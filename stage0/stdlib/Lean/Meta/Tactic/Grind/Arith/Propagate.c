// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.Propagate
// Imports: import Init.Grind import Lean.Meta.Tactic.Grind.Arith.CommRing.RingId import Lean.Meta.Tactic.Grind.Arith.CommRing.NonCommRingM import Lean.Meta.Tactic.Grind.Arith.CommRing.NonCommSemiringM public import Lean.Meta.Tactic.Grind.PropagatorAttr
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
lean_object* lean_array_get_size(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Nat_shiftLeft___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getRevArg_x21(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Meta_Grind_Goal_getRoot(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getNatValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkNatLit(lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommon___redArg(lean_object*, lean_object*);
lean_object* lean_grind_internalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_grind_mk_eq_proof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
extern lean_object* l_Lean_eagerReflBoolTrue;
lean_object* l_Lean_mkApp8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_pushEqCore___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(lean_object*, lean_object*);
lean_object* l_Nat_land___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNonCommRingId_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiring(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_constLevels_x21(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_mkApp5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(lean_object*, lean_object*);
lean_object* l_Nat_lor___boxed(lean_object*, lean_object*);
lean_object* l_Nat_shiftRight___boxed(lean_object*, lean_object*);
lean_object* l_Nat_xor___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_propagateNatBinOp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Nat"};
static const lean_object* l_Lean_Meta_Grind_Arith_propagateNatBinOp___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_propagateNatBinOp___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_propagateNatBinOp___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_propagateNatBinOp___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_object* l_Lean_Meta_Grind_Arith_propagateNatBinOp___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_propagateNatBinOp___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_propagateNatBinOp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_propagateNatBinOp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Nat_land___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__0_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HAnd"};
static const lean_object* l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__1_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hAnd"};
static const lean_object* l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__1_value),LEAN_SCALAR_PTR_LITERAL(222, 205, 8, 181, 48, 134, 168, 175)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__3_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__2_value),LEAN_SCALAR_PTR_LITERAL(54, 171, 107, 112, 94, 43, 106, 200)}};
static const lean_object* l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__3_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__4_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Grind"};
static const lean_object* l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__5_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "and_congr"};
static const lean_object* l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__6_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__7_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__5_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__7_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_propagateNatBinOp___closed__0_value),LEAN_SCALAR_PTR_LITERAL(32, 105, 216, 204, 207, 254, 171, 116)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__7_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__6_value),LEAN_SCALAR_PTR_LITERAL(163, 208, 50, 99, 221, 142, 75, 154)}};
static const lean_object* l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__7 = (const lean_object*)&l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__7_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_propagateNatAnd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_propagateNatAnd___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_propagateNatAnd___regBuiltin_Lean_Meta_Grind_Arith_propagateNatAnd_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_1291761156____hygCtx___hyg_8_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_propagateNatAnd___regBuiltin_Lean_Meta_Grind_Arith_propagateNatAnd_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_1291761156____hygCtx___hyg_8____boxed(lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_Arith_propagateNatOr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Nat_lor___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_propagateNatOr___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_propagateNatOr___closed__0_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_propagateNatOr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "HOr"};
static const lean_object* l_Lean_Meta_Grind_Arith_propagateNatOr___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_propagateNatOr___closed__1_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_propagateNatOr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "hOr"};
static const lean_object* l_Lean_Meta_Grind_Arith_propagateNatOr___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Arith_propagateNatOr___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_propagateNatOr___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_propagateNatOr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(145, 77, 185, 226, 52, 149, 89, 139)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_propagateNatOr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_propagateNatOr___closed__3_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_propagateNatOr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(45, 86, 165, 237, 21, 139, 25, 132)}};
static const lean_object* l_Lean_Meta_Grind_Arith_propagateNatOr___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_Arith_propagateNatOr___closed__3_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_propagateNatOr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "or_congr"};
static const lean_object* l_Lean_Meta_Grind_Arith_propagateNatOr___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_Arith_propagateNatOr___closed__4_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_propagateNatOr___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_propagateNatOr___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_propagateNatOr___closed__5_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__5_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_propagateNatOr___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_propagateNatOr___closed__5_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_propagateNatBinOp___closed__0_value),LEAN_SCALAR_PTR_LITERAL(32, 105, 216, 204, 207, 254, 171, 116)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_propagateNatOr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_propagateNatOr___closed__5_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_Arith_propagateNatOr___closed__4_value),LEAN_SCALAR_PTR_LITERAL(126, 86, 76, 131, 1, 242, 2, 13)}};
static const lean_object* l_Lean_Meta_Grind_Arith_propagateNatOr___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_Arith_propagateNatOr___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_propagateNatOr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_propagateNatOr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_propagateNatOr___regBuiltin_Lean_Meta_Grind_Arith_propagateNatOr_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_2834229635____hygCtx___hyg_8_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_propagateNatOr___regBuiltin_Lean_Meta_Grind_Arith_propagateNatOr_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_2834229635____hygCtx___hyg_8____boxed(lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_Arith_propagateNatXOr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Nat_xor___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_propagateNatXOr___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_propagateNatXOr___closed__0_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_propagateNatXOr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HXor"};
static const lean_object* l_Lean_Meta_Grind_Arith_propagateNatXOr___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_propagateNatXOr___closed__1_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_propagateNatXOr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hXor"};
static const lean_object* l_Lean_Meta_Grind_Arith_propagateNatXOr___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Arith_propagateNatXOr___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_propagateNatXOr___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_propagateNatXOr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(92, 198, 212, 133, 26, 7, 147, 78)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_propagateNatXOr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_propagateNatXOr___closed__3_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_propagateNatXOr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(109, 159, 33, 254, 118, 42, 120, 166)}};
static const lean_object* l_Lean_Meta_Grind_Arith_propagateNatXOr___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_Arith_propagateNatXOr___closed__3_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_propagateNatXOr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "xor_congr"};
static const lean_object* l_Lean_Meta_Grind_Arith_propagateNatXOr___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_Arith_propagateNatXOr___closed__4_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_propagateNatXOr___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_propagateNatXOr___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_propagateNatXOr___closed__5_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__5_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_propagateNatXOr___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_propagateNatXOr___closed__5_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_propagateNatBinOp___closed__0_value),LEAN_SCALAR_PTR_LITERAL(32, 105, 216, 204, 207, 254, 171, 116)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_propagateNatXOr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_propagateNatXOr___closed__5_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_Arith_propagateNatXOr___closed__4_value),LEAN_SCALAR_PTR_LITERAL(166, 201, 140, 62, 184, 193, 191, 77)}};
static const lean_object* l_Lean_Meta_Grind_Arith_propagateNatXOr___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_Arith_propagateNatXOr___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_propagateNatXOr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_propagateNatXOr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_propagateNatXOr___regBuiltin_Lean_Meta_Grind_Arith_propagateNatXOr_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_3633575148____hygCtx___hyg_8_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_propagateNatXOr___regBuiltin_Lean_Meta_Grind_Arith_propagateNatXOr_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_3633575148____hygCtx___hyg_8____boxed(lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_Arith_propagateNatShiftLeft___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Nat_shiftLeft___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_propagateNatShiftLeft___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_propagateNatShiftLeft___closed__0_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_propagateNatShiftLeft___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "HShiftLeft"};
static const lean_object* l_Lean_Meta_Grind_Arith_propagateNatShiftLeft___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_propagateNatShiftLeft___closed__1_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_propagateNatShiftLeft___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "hShiftLeft"};
static const lean_object* l_Lean_Meta_Grind_Arith_propagateNatShiftLeft___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Arith_propagateNatShiftLeft___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_propagateNatShiftLeft___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_propagateNatShiftLeft___closed__1_value),LEAN_SCALAR_PTR_LITERAL(215, 217, 51, 89, 252, 54, 156, 169)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_propagateNatShiftLeft___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_propagateNatShiftLeft___closed__3_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_propagateNatShiftLeft___closed__2_value),LEAN_SCALAR_PTR_LITERAL(181, 245, 218, 3, 224, 235, 179, 59)}};
static const lean_object* l_Lean_Meta_Grind_Arith_propagateNatShiftLeft___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_Arith_propagateNatShiftLeft___closed__3_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_propagateNatShiftLeft___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "shiftLeft_congr"};
static const lean_object* l_Lean_Meta_Grind_Arith_propagateNatShiftLeft___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_Arith_propagateNatShiftLeft___closed__4_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_propagateNatShiftLeft___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_propagateNatShiftLeft___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_propagateNatShiftLeft___closed__5_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__5_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_propagateNatShiftLeft___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_propagateNatShiftLeft___closed__5_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_propagateNatBinOp___closed__0_value),LEAN_SCALAR_PTR_LITERAL(32, 105, 216, 204, 207, 254, 171, 116)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_propagateNatShiftLeft___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_propagateNatShiftLeft___closed__5_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_Arith_propagateNatShiftLeft___closed__4_value),LEAN_SCALAR_PTR_LITERAL(62, 101, 220, 26, 235, 57, 206, 5)}};
static const lean_object* l_Lean_Meta_Grind_Arith_propagateNatShiftLeft___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_Arith_propagateNatShiftLeft___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_propagateNatShiftLeft(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_propagateNatShiftLeft___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_propagateNatShiftLeft___regBuiltin_Lean_Meta_Grind_Arith_propagateNatShiftLeft_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_3253038636____hygCtx___hyg_8_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_propagateNatShiftLeft___regBuiltin_Lean_Meta_Grind_Arith_propagateNatShiftLeft_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_3253038636____hygCtx___hyg_8____boxed(lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_Arith_propagateNatShiftRight___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Nat_shiftRight___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_propagateNatShiftRight___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_propagateNatShiftRight___closed__0_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_propagateNatShiftRight___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "HShiftRight"};
static const lean_object* l_Lean_Meta_Grind_Arith_propagateNatShiftRight___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_propagateNatShiftRight___closed__1_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_propagateNatShiftRight___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "hShiftRight"};
static const lean_object* l_Lean_Meta_Grind_Arith_propagateNatShiftRight___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Arith_propagateNatShiftRight___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_propagateNatShiftRight___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_propagateNatShiftRight___closed__1_value),LEAN_SCALAR_PTR_LITERAL(123, 35, 163, 146, 1, 76, 65, 75)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_propagateNatShiftRight___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_propagateNatShiftRight___closed__3_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_propagateNatShiftRight___closed__2_value),LEAN_SCALAR_PTR_LITERAL(52, 65, 204, 240, 51, 126, 9, 157)}};
static const lean_object* l_Lean_Meta_Grind_Arith_propagateNatShiftRight___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_Arith_propagateNatShiftRight___closed__3_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_propagateNatShiftRight___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "shiftRight_congr"};
static const lean_object* l_Lean_Meta_Grind_Arith_propagateNatShiftRight___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_Arith_propagateNatShiftRight___closed__4_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_propagateNatShiftRight___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_propagateNatShiftRight___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_propagateNatShiftRight___closed__5_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__5_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_propagateNatShiftRight___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_propagateNatShiftRight___closed__5_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_propagateNatBinOp___closed__0_value),LEAN_SCALAR_PTR_LITERAL(32, 105, 216, 204, 207, 254, 171, 116)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_propagateNatShiftRight___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_propagateNatShiftRight___closed__5_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_Arith_propagateNatShiftRight___closed__4_value),LEAN_SCALAR_PTR_LITERAL(199, 140, 245, 152, 31, 217, 19, 125)}};
static const lean_object* l_Lean_Meta_Grind_Arith_propagateNatShiftRight___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_Arith_propagateNatShiftRight___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_propagateNatShiftRight(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_propagateNatShiftRight___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_propagateNatShiftRight___regBuiltin_Lean_Meta_Grind_Arith_propagateNatShiftRight_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_1805815810____hygCtx___hyg_8_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_propagateNatShiftRight___regBuiltin_Lean_Meta_Grind_Arith_propagateNatShiftRight_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_1805815810____hygCtx___hyg_8____boxed(lean_object*);
static lean_once_cell_t l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__1_spec__2_spec__4___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__1_spec__2_spec__4___redArg___closed__0;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__1_spec__2_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__1___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__1(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__0;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__1;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Int"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__2_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__3_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Rat"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__4_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__4_value),LEAN_SCALAR_PTR_LITERAL(231, 55, 105, 214, 206, 30, 120, 51)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__5_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "BitVec"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__6_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__6_value),LEAN_SCALAR_PTR_LITERAL(108, 178, 58, 132, 143, 189, 222, 74)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__7_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "UInt8"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__8_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__8_value),LEAN_SCALAR_PTR_LITERAL(144, 254, 64, 72, 7, 99, 197, 218)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__9_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "UInt16"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__10 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__10_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__10_value),LEAN_SCALAR_PTR_LITERAL(6, 214, 154, 233, 192, 74, 99, 135)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__11 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__11_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "UInt32"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__12 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__12_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__12_value),LEAN_SCALAR_PTR_LITERAL(98, 192, 58, 241, 186, 14, 255, 186)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__13 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__13_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Int64"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__14 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__14_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__14_value),LEAN_SCALAR_PTR_LITERAL(67, 100, 38, 50, 157, 43, 83, 90)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__15 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__15_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Int8"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__16 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__16_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__16_value),LEAN_SCALAR_PTR_LITERAL(17, 171, 155, 218, 43, 77, 1, 67)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__17 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__17_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Int16"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__18 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__18_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__18_value),LEAN_SCALAR_PTR_LITERAL(61, 121, 89, 120, 57, 100, 28, 22)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__19 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__19_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Int32"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__20 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__20_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__20_value),LEAN_SCALAR_PTR_LITERAL(202, 24, 245, 188, 10, 96, 206, 241)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__21 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__21_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__15_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__22 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__22_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__21_value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__22_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__23 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__23_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__19_value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__23_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__24 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__24_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__17_value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__24_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__25 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__25_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__15_value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__25_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__26 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__26_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__13_value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__26_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__27 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__27_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__11_value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__27_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__28 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__28_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__9_value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__28_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__29 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__29_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__7_value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__29_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__30 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__30_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__5_value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__30_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__31 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__31_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__3_value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__31_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__32 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__32_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_propagateNatBinOp___closed__1_value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__32_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__33 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__33_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__34_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__34;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isSupportedSemiringQuick_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isSupportedSemiringQuick_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isSupportedSemiringQuick(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isSupportedSemiringQuick___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isSupportedSemiringQuick_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isSupportedSemiringQuick_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isUnsupportedSemiring_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isUnsupportedSemiring_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isOfNat_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "OfNat"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isOfNat_x3f___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isOfNat_x3f___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isOfNat_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ofNat"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isOfNat_x3f___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isOfNat_x3f___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isOfNat_x3f___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isOfNat_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(135, 241, 166, 108, 243, 216, 193, 244)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isOfNat_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isOfNat_x3f___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isOfNat_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(2, 108, 58, 34, 100, 49, 50, 216)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isOfNat_x3f___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isOfNat_x3f___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isOfNat_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isOfNat_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_propagateMul___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HMul"};
static const lean_object* l_Lean_Meta_Grind_Arith_propagateMul___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_propagateMul___closed__0_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_propagateMul___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hMul"};
static const lean_object* l_Lean_Meta_Grind_Arith_propagateMul___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_propagateMul___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_propagateMul___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_propagateMul___closed__0_value),LEAN_SCALAR_PTR_LITERAL(254, 113, 255, 140, 142, 9, 169, 40)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_propagateMul___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_propagateMul___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_propagateMul___closed__1_value),LEAN_SCALAR_PTR_LITERAL(248, 227, 200, 215, 229, 255, 92, 22)}};
static const lean_object* l_Lean_Meta_Grind_Arith_propagateMul___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Arith_propagateMul___closed__2_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_propagateMul___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Semiring"};
static const lean_object* l_Lean_Meta_Grind_Arith_propagateMul___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_Arith_propagateMul___closed__3_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_propagateMul___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "one_mul_congr"};
static const lean_object* l_Lean_Meta_Grind_Arith_propagateMul___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_Arith_propagateMul___closed__4_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_propagateMul___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_propagateMul___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_propagateMul___closed__5_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__5_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_propagateMul___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_propagateMul___closed__5_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_propagateMul___closed__3_value),LEAN_SCALAR_PTR_LITERAL(246, 150, 10, 46, 185, 54, 59, 167)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_propagateMul___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_propagateMul___closed__5_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_Arith_propagateMul___closed__4_value),LEAN_SCALAR_PTR_LITERAL(179, 16, 35, 35, 145, 96, 68, 63)}};
static const lean_object* l_Lean_Meta_Grind_Arith_propagateMul___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_Arith_propagateMul___closed__5_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_propagateMul___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "zero_mul_congr"};
static const lean_object* l_Lean_Meta_Grind_Arith_propagateMul___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_Arith_propagateMul___closed__6_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_propagateMul___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_propagateMul___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_propagateMul___closed__7_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__5_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_propagateMul___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_propagateMul___closed__7_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_propagateMul___closed__3_value),LEAN_SCALAR_PTR_LITERAL(246, 150, 10, 46, 185, 54, 59, 167)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_propagateMul___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_propagateMul___closed__7_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_Arith_propagateMul___closed__6_value),LEAN_SCALAR_PTR_LITERAL(234, 210, 145, 114, 121, 190, 113, 32)}};
static const lean_object* l_Lean_Meta_Grind_Arith_propagateMul___closed__7 = (const lean_object*)&l_Lean_Meta_Grind_Arith_propagateMul___closed__7_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_propagateMul___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "mul_one_congr"};
static const lean_object* l_Lean_Meta_Grind_Arith_propagateMul___closed__8 = (const lean_object*)&l_Lean_Meta_Grind_Arith_propagateMul___closed__8_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_propagateMul___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_propagateMul___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_propagateMul___closed__9_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__5_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_propagateMul___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_propagateMul___closed__9_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_propagateMul___closed__3_value),LEAN_SCALAR_PTR_LITERAL(246, 150, 10, 46, 185, 54, 59, 167)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_propagateMul___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_propagateMul___closed__9_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_Arith_propagateMul___closed__8_value),LEAN_SCALAR_PTR_LITERAL(118, 239, 67, 209, 31, 66, 10, 36)}};
static const lean_object* l_Lean_Meta_Grind_Arith_propagateMul___closed__9 = (const lean_object*)&l_Lean_Meta_Grind_Arith_propagateMul___closed__9_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_propagateMul___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "mul_zero_congr"};
static const lean_object* l_Lean_Meta_Grind_Arith_propagateMul___closed__10 = (const lean_object*)&l_Lean_Meta_Grind_Arith_propagateMul___closed__10_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_propagateMul___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_propagateMul___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_propagateMul___closed__11_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__5_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_propagateMul___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_propagateMul___closed__11_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_propagateMul___closed__3_value),LEAN_SCALAR_PTR_LITERAL(246, 150, 10, 46, 185, 54, 59, 167)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_propagateMul___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_propagateMul___closed__11_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_Arith_propagateMul___closed__10_value),LEAN_SCALAR_PTR_LITERAL(170, 247, 48, 62, 70, 153, 89, 80)}};
static const lean_object* l_Lean_Meta_Grind_Arith_propagateMul___closed__11 = (const lean_object*)&l_Lean_Meta_Grind_Arith_propagateMul___closed__11_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_propagateMul(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_propagateMul___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_propagateMul___regBuiltin_Lean_Meta_Grind_Arith_propagateMul_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_3131998065____hygCtx___hyg_8_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_propagateMul___regBuiltin_Lean_Meta_Grind_Arith_propagateMul_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_3131998065____hygCtx___hyg_8____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_propagateNatBinOp(lean_object* v_declName_4_, lean_object* v_congrThmName_5_, lean_object* v_op_6_, lean_object* v_e_7_, lean_object* v_a_8_, lean_object* v_a_9_, lean_object* v_a_10_, lean_object* v_a_11_, lean_object* v_a_12_, lean_object* v_a_13_, lean_object* v_a_14_, lean_object* v_a_15_, lean_object* v_a_16_, lean_object* v_a_17_){
_start:
{
lean_object* v_arity_19_; uint8_t v___x_20_; 
v_arity_19_ = lean_unsigned_to_nat(6u);
v___x_20_ = l_Lean_Expr_isAppOfArity(v_e_7_, v_declName_4_, v_arity_19_);
if (v___x_20_ == 0)
{
lean_object* v___x_21_; lean_object* v___x_22_; 
lean_dec_ref(v_e_7_);
lean_dec_ref(v_op_6_);
lean_dec(v_congrThmName_5_);
v___x_21_ = lean_box(0);
v___x_22_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_22_, 0, v___x_21_);
return v___x_22_;
}
else
{
lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___x_26_; lean_object* v___x_27_; uint8_t v___x_28_; 
v___x_23_ = l_Lean_Expr_getAppNumArgs(v_e_7_);
v___x_24_ = lean_unsigned_to_nat(1u);
v___x_25_ = lean_nat_sub(v___x_23_, v___x_24_);
lean_dec(v___x_23_);
lean_inc(v___x_25_);
v___x_26_ = l_Lean_Expr_getRevArg_x21(v_e_7_, v___x_25_);
v___x_27_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_propagateNatBinOp___closed__1));
v___x_28_ = l_Lean_Expr_isConstOf(v___x_26_, v___x_27_);
lean_dec_ref(v___x_26_);
if (v___x_28_ == 0)
{
lean_object* v___x_29_; lean_object* v___x_30_; 
lean_dec(v___x_25_);
lean_dec_ref(v_e_7_);
lean_dec_ref(v_op_6_);
lean_dec(v_congrThmName_5_);
v___x_29_ = lean_box(0);
v___x_30_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_30_, 0, v___x_29_);
return v___x_30_;
}
else
{
lean_object* v___x_31_; lean_object* v___x_32_; uint8_t v___x_33_; 
v___x_31_ = lean_nat_sub(v___x_25_, v___x_24_);
lean_dec(v___x_25_);
v___x_32_ = l_Lean_Expr_getRevArg_x21(v_e_7_, v___x_31_);
v___x_33_ = l_Lean_Expr_isConstOf(v___x_32_, v___x_27_);
lean_dec_ref(v___x_32_);
if (v___x_33_ == 0)
{
lean_object* v___x_34_; lean_object* v___x_35_; 
lean_dec_ref(v_e_7_);
lean_dec_ref(v_op_6_);
lean_dec(v_congrThmName_5_);
v___x_34_ = lean_box(0);
v___x_35_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_35_, 0, v___x_34_);
return v___x_35_;
}
else
{
lean_object* v___x_36_; lean_object* v_a_37_; lean_object* v___x_38_; 
v___x_36_ = lean_st_ref_get(v_a_8_);
v_a_37_ = l_Lean_Expr_getRevArg_x21(v_e_7_, v___x_24_);
lean_inc_ref(v_a_37_);
v___x_38_ = l_Lean_Meta_Grind_Goal_getRoot(v___x_36_, v_a_37_, v_a_14_, v_a_15_, v_a_16_, v_a_17_);
if (lean_obj_tag(v___x_38_) == 0)
{
lean_object* v_a_39_; lean_object* v___x_40_; 
v_a_39_ = lean_ctor_get(v___x_38_, 0);
lean_inc(v_a_39_);
lean_dec_ref(v___x_38_);
v___x_40_ = l_Lean_Meta_getNatValue_x3f(v_a_39_, v_a_14_, v_a_15_, v_a_16_, v_a_17_);
if (lean_obj_tag(v___x_40_) == 0)
{
lean_object* v_a_41_; lean_object* v___x_43_; uint8_t v_isShared_44_; uint8_t v_isSharedCheck_122_; 
v_a_41_ = lean_ctor_get(v___x_40_, 0);
v_isSharedCheck_122_ = !lean_is_exclusive(v___x_40_);
if (v_isSharedCheck_122_ == 0)
{
v___x_43_ = v___x_40_;
v_isShared_44_ = v_isSharedCheck_122_;
goto v_resetjp_42_;
}
else
{
lean_inc(v_a_41_);
lean_dec(v___x_40_);
v___x_43_ = lean_box(0);
v_isShared_44_ = v_isSharedCheck_122_;
goto v_resetjp_42_;
}
v_resetjp_42_:
{
if (lean_obj_tag(v_a_41_) == 1)
{
lean_object* v_val_45_; lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v___x_49_; 
lean_del_object(v___x_43_);
v_val_45_ = lean_ctor_get(v_a_41_, 0);
lean_inc(v_val_45_);
lean_dec_ref(v_a_41_);
v___x_46_ = lean_st_ref_get(v_a_8_);
v___x_47_ = lean_unsigned_to_nat(0u);
v___x_48_ = l_Lean_Expr_getRevArg_x21(v_e_7_, v___x_47_);
lean_inc_ref(v___x_48_);
v___x_49_ = l_Lean_Meta_Grind_Goal_getRoot(v___x_46_, v___x_48_, v_a_14_, v_a_15_, v_a_16_, v_a_17_);
if (lean_obj_tag(v___x_49_) == 0)
{
lean_object* v_a_50_; lean_object* v___x_51_; 
v_a_50_ = lean_ctor_get(v___x_49_, 0);
lean_inc(v_a_50_);
lean_dec_ref(v___x_49_);
v___x_51_ = l_Lean_Meta_getNatValue_x3f(v_a_50_, v_a_14_, v_a_15_, v_a_16_, v_a_17_);
if (lean_obj_tag(v___x_51_) == 0)
{
lean_object* v_a_52_; lean_object* v___x_54_; uint8_t v_isShared_55_; uint8_t v_isSharedCheck_101_; 
v_a_52_ = lean_ctor_get(v___x_51_, 0);
v_isSharedCheck_101_ = !lean_is_exclusive(v___x_51_);
if (v_isSharedCheck_101_ == 0)
{
v___x_54_ = v___x_51_;
v_isShared_55_ = v_isSharedCheck_101_;
goto v_resetjp_53_;
}
else
{
lean_inc(v_a_52_);
lean_dec(v___x_51_);
v___x_54_ = lean_box(0);
v_isShared_55_ = v_isSharedCheck_101_;
goto v_resetjp_53_;
}
v_resetjp_53_:
{
if (lean_obj_tag(v_a_52_) == 1)
{
lean_object* v_val_56_; lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; 
lean_del_object(v___x_54_);
v_val_56_ = lean_ctor_get(v_a_52_, 0);
lean_inc(v_val_56_);
lean_dec_ref(v_a_52_);
v___x_57_ = lean_apply_2(v_op_6_, v_val_45_, v_val_56_);
v___x_58_ = l_Lean_mkNatLit(v___x_57_);
v___x_59_ = l_Lean_Meta_Sym_shareCommon___redArg(v___x_58_, v_a_13_);
if (lean_obj_tag(v___x_59_) == 0)
{
lean_object* v_a_60_; lean_object* v___x_61_; lean_object* v___x_62_; 
v_a_60_ = lean_ctor_get(v___x_59_, 0);
lean_inc_n(v_a_60_, 2);
lean_dec_ref(v___x_59_);
v___x_61_ = lean_box(0);
lean_inc(v_a_17_);
lean_inc_ref(v_a_16_);
lean_inc(v_a_15_);
lean_inc_ref(v_a_14_);
lean_inc(v_a_13_);
lean_inc_ref(v_a_12_);
lean_inc(v_a_11_);
lean_inc_ref(v_a_10_);
lean_inc(v_a_9_);
lean_inc(v_a_8_);
v___x_62_ = lean_grind_internalize(v_a_60_, v___x_47_, v___x_61_, v_a_8_, v_a_9_, v_a_10_, v_a_11_, v_a_12_, v_a_13_, v_a_14_, v_a_15_, v_a_16_, v_a_17_);
if (lean_obj_tag(v___x_62_) == 0)
{
lean_object* v___x_63_; 
lean_dec_ref(v___x_62_);
lean_inc(v_a_17_);
lean_inc_ref(v_a_16_);
lean_inc(v_a_15_);
lean_inc_ref(v_a_14_);
lean_inc(v_a_13_);
lean_inc_ref(v_a_12_);
lean_inc(v_a_11_);
lean_inc_ref(v_a_10_);
lean_inc(v_a_9_);
lean_inc(v_a_8_);
lean_inc(v_a_39_);
lean_inc_ref(v_a_37_);
v___x_63_ = lean_grind_mk_eq_proof(v_a_37_, v_a_39_, v_a_8_, v_a_9_, v_a_10_, v_a_11_, v_a_12_, v_a_13_, v_a_14_, v_a_15_, v_a_16_, v_a_17_);
if (lean_obj_tag(v___x_63_) == 0)
{
lean_object* v_a_64_; lean_object* v___x_65_; 
v_a_64_ = lean_ctor_get(v___x_63_, 0);
lean_inc(v_a_64_);
lean_dec_ref(v___x_63_);
lean_inc(v_a_17_);
lean_inc_ref(v_a_16_);
lean_inc(v_a_15_);
lean_inc_ref(v_a_14_);
lean_inc(v_a_13_);
lean_inc_ref(v_a_12_);
lean_inc(v_a_11_);
lean_inc_ref(v_a_10_);
lean_inc(v_a_9_);
lean_inc(v_a_8_);
lean_inc(v_a_50_);
lean_inc_ref(v___x_48_);
v___x_65_ = lean_grind_mk_eq_proof(v___x_48_, v_a_50_, v_a_8_, v_a_9_, v_a_10_, v_a_11_, v_a_12_, v_a_13_, v_a_14_, v_a_15_, v_a_16_, v_a_17_);
if (lean_obj_tag(v___x_65_) == 0)
{
lean_object* v_a_66_; lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; uint8_t v___x_71_; lean_object* v___x_72_; 
v_a_66_ = lean_ctor_get(v___x_65_, 0);
lean_inc(v_a_66_);
lean_dec_ref(v___x_65_);
v___x_67_ = lean_box(0);
v___x_68_ = l_Lean_mkConst(v_congrThmName_5_, v___x_67_);
v___x_69_ = l_Lean_eagerReflBoolTrue;
lean_inc(v_a_60_);
v___x_70_ = l_Lean_mkApp8(v___x_68_, v_a_37_, v___x_48_, v_a_39_, v_a_50_, v_a_60_, v_a_64_, v_a_66_, v___x_69_);
v___x_71_ = 0;
v___x_72_ = l_Lean_Meta_Grind_pushEqCore___redArg(v_e_7_, v_a_60_, v___x_70_, v___x_71_, v_a_8_, v_a_10_, v_a_14_, v_a_15_, v_a_16_, v_a_17_);
return v___x_72_;
}
else
{
lean_object* v_a_73_; lean_object* v___x_75_; uint8_t v_isShared_76_; uint8_t v_isSharedCheck_80_; 
lean_dec(v_a_64_);
lean_dec(v_a_60_);
lean_dec(v_a_50_);
lean_dec_ref(v___x_48_);
lean_dec(v_a_39_);
lean_dec_ref(v_a_37_);
lean_dec_ref(v_e_7_);
lean_dec(v_congrThmName_5_);
v_a_73_ = lean_ctor_get(v___x_65_, 0);
v_isSharedCheck_80_ = !lean_is_exclusive(v___x_65_);
if (v_isSharedCheck_80_ == 0)
{
v___x_75_ = v___x_65_;
v_isShared_76_ = v_isSharedCheck_80_;
goto v_resetjp_74_;
}
else
{
lean_inc(v_a_73_);
lean_dec(v___x_65_);
v___x_75_ = lean_box(0);
v_isShared_76_ = v_isSharedCheck_80_;
goto v_resetjp_74_;
}
v_resetjp_74_:
{
lean_object* v___x_78_; 
if (v_isShared_76_ == 0)
{
v___x_78_ = v___x_75_;
goto v_reusejp_77_;
}
else
{
lean_object* v_reuseFailAlloc_79_; 
v_reuseFailAlloc_79_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_79_, 0, v_a_73_);
v___x_78_ = v_reuseFailAlloc_79_;
goto v_reusejp_77_;
}
v_reusejp_77_:
{
return v___x_78_;
}
}
}
}
else
{
lean_object* v_a_81_; lean_object* v___x_83_; uint8_t v_isShared_84_; uint8_t v_isSharedCheck_88_; 
lean_dec(v_a_60_);
lean_dec(v_a_50_);
lean_dec_ref(v___x_48_);
lean_dec(v_a_39_);
lean_dec_ref(v_a_37_);
lean_dec_ref(v_e_7_);
lean_dec(v_congrThmName_5_);
v_a_81_ = lean_ctor_get(v___x_63_, 0);
v_isSharedCheck_88_ = !lean_is_exclusive(v___x_63_);
if (v_isSharedCheck_88_ == 0)
{
v___x_83_ = v___x_63_;
v_isShared_84_ = v_isSharedCheck_88_;
goto v_resetjp_82_;
}
else
{
lean_inc(v_a_81_);
lean_dec(v___x_63_);
v___x_83_ = lean_box(0);
v_isShared_84_ = v_isSharedCheck_88_;
goto v_resetjp_82_;
}
v_resetjp_82_:
{
lean_object* v___x_86_; 
if (v_isShared_84_ == 0)
{
v___x_86_ = v___x_83_;
goto v_reusejp_85_;
}
else
{
lean_object* v_reuseFailAlloc_87_; 
v_reuseFailAlloc_87_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_87_, 0, v_a_81_);
v___x_86_ = v_reuseFailAlloc_87_;
goto v_reusejp_85_;
}
v_reusejp_85_:
{
return v___x_86_;
}
}
}
}
else
{
lean_dec(v_a_60_);
lean_dec(v_a_50_);
lean_dec_ref(v___x_48_);
lean_dec(v_a_39_);
lean_dec_ref(v_a_37_);
lean_dec_ref(v_e_7_);
lean_dec(v_congrThmName_5_);
return v___x_62_;
}
}
else
{
lean_object* v_a_89_; lean_object* v___x_91_; uint8_t v_isShared_92_; uint8_t v_isSharedCheck_96_; 
lean_dec(v_a_50_);
lean_dec_ref(v___x_48_);
lean_dec(v_a_39_);
lean_dec_ref(v_a_37_);
lean_dec_ref(v_e_7_);
lean_dec(v_congrThmName_5_);
v_a_89_ = lean_ctor_get(v___x_59_, 0);
v_isSharedCheck_96_ = !lean_is_exclusive(v___x_59_);
if (v_isSharedCheck_96_ == 0)
{
v___x_91_ = v___x_59_;
v_isShared_92_ = v_isSharedCheck_96_;
goto v_resetjp_90_;
}
else
{
lean_inc(v_a_89_);
lean_dec(v___x_59_);
v___x_91_ = lean_box(0);
v_isShared_92_ = v_isSharedCheck_96_;
goto v_resetjp_90_;
}
v_resetjp_90_:
{
lean_object* v___x_94_; 
if (v_isShared_92_ == 0)
{
v___x_94_ = v___x_91_;
goto v_reusejp_93_;
}
else
{
lean_object* v_reuseFailAlloc_95_; 
v_reuseFailAlloc_95_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_95_, 0, v_a_89_);
v___x_94_ = v_reuseFailAlloc_95_;
goto v_reusejp_93_;
}
v_reusejp_93_:
{
return v___x_94_;
}
}
}
}
else
{
lean_object* v___x_97_; lean_object* v___x_99_; 
lean_dec(v_a_52_);
lean_dec(v_a_50_);
lean_dec_ref(v___x_48_);
lean_dec(v_val_45_);
lean_dec(v_a_39_);
lean_dec_ref(v_a_37_);
lean_dec_ref(v_e_7_);
lean_dec_ref(v_op_6_);
lean_dec(v_congrThmName_5_);
v___x_97_ = lean_box(0);
if (v_isShared_55_ == 0)
{
lean_ctor_set(v___x_54_, 0, v___x_97_);
v___x_99_ = v___x_54_;
goto v_reusejp_98_;
}
else
{
lean_object* v_reuseFailAlloc_100_; 
v_reuseFailAlloc_100_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_100_, 0, v___x_97_);
v___x_99_ = v_reuseFailAlloc_100_;
goto v_reusejp_98_;
}
v_reusejp_98_:
{
return v___x_99_;
}
}
}
}
else
{
lean_object* v_a_102_; lean_object* v___x_104_; uint8_t v_isShared_105_; uint8_t v_isSharedCheck_109_; 
lean_dec(v_a_50_);
lean_dec_ref(v___x_48_);
lean_dec(v_val_45_);
lean_dec(v_a_39_);
lean_dec_ref(v_a_37_);
lean_dec_ref(v_e_7_);
lean_dec_ref(v_op_6_);
lean_dec(v_congrThmName_5_);
v_a_102_ = lean_ctor_get(v___x_51_, 0);
v_isSharedCheck_109_ = !lean_is_exclusive(v___x_51_);
if (v_isSharedCheck_109_ == 0)
{
v___x_104_ = v___x_51_;
v_isShared_105_ = v_isSharedCheck_109_;
goto v_resetjp_103_;
}
else
{
lean_inc(v_a_102_);
lean_dec(v___x_51_);
v___x_104_ = lean_box(0);
v_isShared_105_ = v_isSharedCheck_109_;
goto v_resetjp_103_;
}
v_resetjp_103_:
{
lean_object* v___x_107_; 
if (v_isShared_105_ == 0)
{
v___x_107_ = v___x_104_;
goto v_reusejp_106_;
}
else
{
lean_object* v_reuseFailAlloc_108_; 
v_reuseFailAlloc_108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_108_, 0, v_a_102_);
v___x_107_ = v_reuseFailAlloc_108_;
goto v_reusejp_106_;
}
v_reusejp_106_:
{
return v___x_107_;
}
}
}
}
else
{
lean_object* v_a_110_; lean_object* v___x_112_; uint8_t v_isShared_113_; uint8_t v_isSharedCheck_117_; 
lean_dec_ref(v___x_48_);
lean_dec(v_val_45_);
lean_dec(v_a_39_);
lean_dec_ref(v_a_37_);
lean_dec_ref(v_e_7_);
lean_dec_ref(v_op_6_);
lean_dec(v_congrThmName_5_);
v_a_110_ = lean_ctor_get(v___x_49_, 0);
v_isSharedCheck_117_ = !lean_is_exclusive(v___x_49_);
if (v_isSharedCheck_117_ == 0)
{
v___x_112_ = v___x_49_;
v_isShared_113_ = v_isSharedCheck_117_;
goto v_resetjp_111_;
}
else
{
lean_inc(v_a_110_);
lean_dec(v___x_49_);
v___x_112_ = lean_box(0);
v_isShared_113_ = v_isSharedCheck_117_;
goto v_resetjp_111_;
}
v_resetjp_111_:
{
lean_object* v___x_115_; 
if (v_isShared_113_ == 0)
{
v___x_115_ = v___x_112_;
goto v_reusejp_114_;
}
else
{
lean_object* v_reuseFailAlloc_116_; 
v_reuseFailAlloc_116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_116_, 0, v_a_110_);
v___x_115_ = v_reuseFailAlloc_116_;
goto v_reusejp_114_;
}
v_reusejp_114_:
{
return v___x_115_;
}
}
}
}
else
{
lean_object* v___x_118_; lean_object* v___x_120_; 
lean_dec(v_a_41_);
lean_dec(v_a_39_);
lean_dec_ref(v_a_37_);
lean_dec_ref(v_e_7_);
lean_dec_ref(v_op_6_);
lean_dec(v_congrThmName_5_);
v___x_118_ = lean_box(0);
if (v_isShared_44_ == 0)
{
lean_ctor_set(v___x_43_, 0, v___x_118_);
v___x_120_ = v___x_43_;
goto v_reusejp_119_;
}
else
{
lean_object* v_reuseFailAlloc_121_; 
v_reuseFailAlloc_121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_121_, 0, v___x_118_);
v___x_120_ = v_reuseFailAlloc_121_;
goto v_reusejp_119_;
}
v_reusejp_119_:
{
return v___x_120_;
}
}
}
}
else
{
lean_object* v_a_123_; lean_object* v___x_125_; uint8_t v_isShared_126_; uint8_t v_isSharedCheck_130_; 
lean_dec(v_a_39_);
lean_dec_ref(v_a_37_);
lean_dec_ref(v_e_7_);
lean_dec_ref(v_op_6_);
lean_dec(v_congrThmName_5_);
v_a_123_ = lean_ctor_get(v___x_40_, 0);
v_isSharedCheck_130_ = !lean_is_exclusive(v___x_40_);
if (v_isSharedCheck_130_ == 0)
{
v___x_125_ = v___x_40_;
v_isShared_126_ = v_isSharedCheck_130_;
goto v_resetjp_124_;
}
else
{
lean_inc(v_a_123_);
lean_dec(v___x_40_);
v___x_125_ = lean_box(0);
v_isShared_126_ = v_isSharedCheck_130_;
goto v_resetjp_124_;
}
v_resetjp_124_:
{
lean_object* v___x_128_; 
if (v_isShared_126_ == 0)
{
v___x_128_ = v___x_125_;
goto v_reusejp_127_;
}
else
{
lean_object* v_reuseFailAlloc_129_; 
v_reuseFailAlloc_129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_129_, 0, v_a_123_);
v___x_128_ = v_reuseFailAlloc_129_;
goto v_reusejp_127_;
}
v_reusejp_127_:
{
return v___x_128_;
}
}
}
}
else
{
lean_object* v_a_131_; lean_object* v___x_133_; uint8_t v_isShared_134_; uint8_t v_isSharedCheck_138_; 
lean_dec_ref(v_a_37_);
lean_dec_ref(v_e_7_);
lean_dec_ref(v_op_6_);
lean_dec(v_congrThmName_5_);
v_a_131_ = lean_ctor_get(v___x_38_, 0);
v_isSharedCheck_138_ = !lean_is_exclusive(v___x_38_);
if (v_isSharedCheck_138_ == 0)
{
v___x_133_ = v___x_38_;
v_isShared_134_ = v_isSharedCheck_138_;
goto v_resetjp_132_;
}
else
{
lean_inc(v_a_131_);
lean_dec(v___x_38_);
v___x_133_ = lean_box(0);
v_isShared_134_ = v_isSharedCheck_138_;
goto v_resetjp_132_;
}
v_resetjp_132_:
{
lean_object* v___x_136_; 
if (v_isShared_134_ == 0)
{
v___x_136_ = v___x_133_;
goto v_reusejp_135_;
}
else
{
lean_object* v_reuseFailAlloc_137_; 
v_reuseFailAlloc_137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_137_, 0, v_a_131_);
v___x_136_ = v_reuseFailAlloc_137_;
goto v_reusejp_135_;
}
v_reusejp_135_:
{
return v___x_136_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_propagateNatBinOp___boxed(lean_object* v_declName_139_, lean_object* v_congrThmName_140_, lean_object* v_op_141_, lean_object* v_e_142_, lean_object* v_a_143_, lean_object* v_a_144_, lean_object* v_a_145_, lean_object* v_a_146_, lean_object* v_a_147_, lean_object* v_a_148_, lean_object* v_a_149_, lean_object* v_a_150_, lean_object* v_a_151_, lean_object* v_a_152_, lean_object* v_a_153_){
_start:
{
lean_object* v_res_154_; 
v_res_154_ = l_Lean_Meta_Grind_Arith_propagateNatBinOp(v_declName_139_, v_congrThmName_140_, v_op_141_, v_e_142_, v_a_143_, v_a_144_, v_a_145_, v_a_146_, v_a_147_, v_a_148_, v_a_149_, v_a_150_, v_a_151_, v_a_152_);
lean_dec(v_a_152_);
lean_dec_ref(v_a_151_);
lean_dec(v_a_150_);
lean_dec_ref(v_a_149_);
lean_dec(v_a_148_);
lean_dec_ref(v_a_147_);
lean_dec(v_a_146_);
lean_dec_ref(v_a_145_);
lean_dec(v_a_144_);
lean_dec(v_a_143_);
lean_dec(v_declName_139_);
return v_res_154_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_propagateNatAnd(lean_object* v_e_169_, lean_object* v_a_170_, lean_object* v_a_171_, lean_object* v_a_172_, lean_object* v_a_173_, lean_object* v_a_174_, lean_object* v_a_175_, lean_object* v_a_176_, lean_object* v_a_177_, lean_object* v_a_178_, lean_object* v_a_179_){
_start:
{
lean_object* v___f_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; 
v___f_181_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__0));
v___x_182_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__3));
v___x_183_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__7));
v___x_184_ = l_Lean_Meta_Grind_Arith_propagateNatBinOp(v___x_182_, v___x_183_, v___f_181_, v_e_169_, v_a_170_, v_a_171_, v_a_172_, v_a_173_, v_a_174_, v_a_175_, v_a_176_, v_a_177_, v_a_178_, v_a_179_);
return v___x_184_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_propagateNatAnd___boxed(lean_object* v_e_185_, lean_object* v_a_186_, lean_object* v_a_187_, lean_object* v_a_188_, lean_object* v_a_189_, lean_object* v_a_190_, lean_object* v_a_191_, lean_object* v_a_192_, lean_object* v_a_193_, lean_object* v_a_194_, lean_object* v_a_195_, lean_object* v_a_196_){
_start:
{
lean_object* v_res_197_; 
v_res_197_ = l_Lean_Meta_Grind_Arith_propagateNatAnd(v_e_185_, v_a_186_, v_a_187_, v_a_188_, v_a_189_, v_a_190_, v_a_191_, v_a_192_, v_a_193_, v_a_194_, v_a_195_);
lean_dec(v_a_195_);
lean_dec_ref(v_a_194_);
lean_dec(v_a_193_);
lean_dec_ref(v_a_192_);
lean_dec(v_a_191_);
lean_dec_ref(v_a_190_);
lean_dec(v_a_189_);
lean_dec_ref(v_a_188_);
lean_dec(v_a_187_);
lean_dec(v_a_186_);
return v_res_197_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_propagateNatAnd___regBuiltin_Lean_Meta_Grind_Arith_propagateNatAnd_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_1291761156____hygCtx___hyg_8_(){
_start:
{
lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; 
v___x_199_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__3));
v___x_200_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_propagateNatAnd___boxed), 12, 0);
v___x_201_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_199_, v___x_200_);
return v___x_201_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_propagateNatAnd___regBuiltin_Lean_Meta_Grind_Arith_propagateNatAnd_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_1291761156____hygCtx___hyg_8____boxed(lean_object* v_a_202_){
_start:
{
lean_object* v_res_203_; 
v_res_203_ = l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_propagateNatAnd___regBuiltin_Lean_Meta_Grind_Arith_propagateNatAnd_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_1291761156____hygCtx___hyg_8_();
return v_res_203_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_propagateNatOr(lean_object* v_e_216_, lean_object* v_a_217_, lean_object* v_a_218_, lean_object* v_a_219_, lean_object* v_a_220_, lean_object* v_a_221_, lean_object* v_a_222_, lean_object* v_a_223_, lean_object* v_a_224_, lean_object* v_a_225_, lean_object* v_a_226_){
_start:
{
lean_object* v___f_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; 
v___f_228_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_propagateNatOr___closed__0));
v___x_229_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_propagateNatOr___closed__3));
v___x_230_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_propagateNatOr___closed__5));
v___x_231_ = l_Lean_Meta_Grind_Arith_propagateNatBinOp(v___x_229_, v___x_230_, v___f_228_, v_e_216_, v_a_217_, v_a_218_, v_a_219_, v_a_220_, v_a_221_, v_a_222_, v_a_223_, v_a_224_, v_a_225_, v_a_226_);
return v___x_231_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_propagateNatOr___boxed(lean_object* v_e_232_, lean_object* v_a_233_, lean_object* v_a_234_, lean_object* v_a_235_, lean_object* v_a_236_, lean_object* v_a_237_, lean_object* v_a_238_, lean_object* v_a_239_, lean_object* v_a_240_, lean_object* v_a_241_, lean_object* v_a_242_, lean_object* v_a_243_){
_start:
{
lean_object* v_res_244_; 
v_res_244_ = l_Lean_Meta_Grind_Arith_propagateNatOr(v_e_232_, v_a_233_, v_a_234_, v_a_235_, v_a_236_, v_a_237_, v_a_238_, v_a_239_, v_a_240_, v_a_241_, v_a_242_);
lean_dec(v_a_242_);
lean_dec_ref(v_a_241_);
lean_dec(v_a_240_);
lean_dec_ref(v_a_239_);
lean_dec(v_a_238_);
lean_dec_ref(v_a_237_);
lean_dec(v_a_236_);
lean_dec_ref(v_a_235_);
lean_dec(v_a_234_);
lean_dec(v_a_233_);
return v_res_244_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_propagateNatOr___regBuiltin_Lean_Meta_Grind_Arith_propagateNatOr_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_2834229635____hygCtx___hyg_8_(){
_start:
{
lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; 
v___x_246_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_propagateNatOr___closed__3));
v___x_247_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_propagateNatOr___boxed), 12, 0);
v___x_248_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_246_, v___x_247_);
return v___x_248_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_propagateNatOr___regBuiltin_Lean_Meta_Grind_Arith_propagateNatOr_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_2834229635____hygCtx___hyg_8____boxed(lean_object* v_a_249_){
_start:
{
lean_object* v_res_250_; 
v_res_250_ = l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_propagateNatOr___regBuiltin_Lean_Meta_Grind_Arith_propagateNatOr_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_2834229635____hygCtx___hyg_8_();
return v_res_250_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_propagateNatXOr(lean_object* v_e_263_, lean_object* v_a_264_, lean_object* v_a_265_, lean_object* v_a_266_, lean_object* v_a_267_, lean_object* v_a_268_, lean_object* v_a_269_, lean_object* v_a_270_, lean_object* v_a_271_, lean_object* v_a_272_, lean_object* v_a_273_){
_start:
{
lean_object* v___f_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; 
v___f_275_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_propagateNatXOr___closed__0));
v___x_276_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_propagateNatXOr___closed__3));
v___x_277_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_propagateNatXOr___closed__5));
v___x_278_ = l_Lean_Meta_Grind_Arith_propagateNatBinOp(v___x_276_, v___x_277_, v___f_275_, v_e_263_, v_a_264_, v_a_265_, v_a_266_, v_a_267_, v_a_268_, v_a_269_, v_a_270_, v_a_271_, v_a_272_, v_a_273_);
return v___x_278_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_propagateNatXOr___boxed(lean_object* v_e_279_, lean_object* v_a_280_, lean_object* v_a_281_, lean_object* v_a_282_, lean_object* v_a_283_, lean_object* v_a_284_, lean_object* v_a_285_, lean_object* v_a_286_, lean_object* v_a_287_, lean_object* v_a_288_, lean_object* v_a_289_, lean_object* v_a_290_){
_start:
{
lean_object* v_res_291_; 
v_res_291_ = l_Lean_Meta_Grind_Arith_propagateNatXOr(v_e_279_, v_a_280_, v_a_281_, v_a_282_, v_a_283_, v_a_284_, v_a_285_, v_a_286_, v_a_287_, v_a_288_, v_a_289_);
lean_dec(v_a_289_);
lean_dec_ref(v_a_288_);
lean_dec(v_a_287_);
lean_dec_ref(v_a_286_);
lean_dec(v_a_285_);
lean_dec_ref(v_a_284_);
lean_dec(v_a_283_);
lean_dec_ref(v_a_282_);
lean_dec(v_a_281_);
lean_dec(v_a_280_);
return v_res_291_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_propagateNatXOr___regBuiltin_Lean_Meta_Grind_Arith_propagateNatXOr_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_3633575148____hygCtx___hyg_8_(){
_start:
{
lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; 
v___x_293_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_propagateNatXOr___closed__3));
v___x_294_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_propagateNatXOr___boxed), 12, 0);
v___x_295_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_293_, v___x_294_);
return v___x_295_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_propagateNatXOr___regBuiltin_Lean_Meta_Grind_Arith_propagateNatXOr_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_3633575148____hygCtx___hyg_8____boxed(lean_object* v_a_296_){
_start:
{
lean_object* v_res_297_; 
v_res_297_ = l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_propagateNatXOr___regBuiltin_Lean_Meta_Grind_Arith_propagateNatXOr_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_3633575148____hygCtx___hyg_8_();
return v_res_297_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_propagateNatShiftLeft(lean_object* v_e_310_, lean_object* v_a_311_, lean_object* v_a_312_, lean_object* v_a_313_, lean_object* v_a_314_, lean_object* v_a_315_, lean_object* v_a_316_, lean_object* v_a_317_, lean_object* v_a_318_, lean_object* v_a_319_, lean_object* v_a_320_){
_start:
{
lean_object* v___f_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; 
v___f_322_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_propagateNatShiftLeft___closed__0));
v___x_323_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_propagateNatShiftLeft___closed__3));
v___x_324_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_propagateNatShiftLeft___closed__5));
v___x_325_ = l_Lean_Meta_Grind_Arith_propagateNatBinOp(v___x_323_, v___x_324_, v___f_322_, v_e_310_, v_a_311_, v_a_312_, v_a_313_, v_a_314_, v_a_315_, v_a_316_, v_a_317_, v_a_318_, v_a_319_, v_a_320_);
return v___x_325_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_propagateNatShiftLeft___boxed(lean_object* v_e_326_, lean_object* v_a_327_, lean_object* v_a_328_, lean_object* v_a_329_, lean_object* v_a_330_, lean_object* v_a_331_, lean_object* v_a_332_, lean_object* v_a_333_, lean_object* v_a_334_, lean_object* v_a_335_, lean_object* v_a_336_, lean_object* v_a_337_){
_start:
{
lean_object* v_res_338_; 
v_res_338_ = l_Lean_Meta_Grind_Arith_propagateNatShiftLeft(v_e_326_, v_a_327_, v_a_328_, v_a_329_, v_a_330_, v_a_331_, v_a_332_, v_a_333_, v_a_334_, v_a_335_, v_a_336_);
lean_dec(v_a_336_);
lean_dec_ref(v_a_335_);
lean_dec(v_a_334_);
lean_dec_ref(v_a_333_);
lean_dec(v_a_332_);
lean_dec_ref(v_a_331_);
lean_dec(v_a_330_);
lean_dec_ref(v_a_329_);
lean_dec(v_a_328_);
lean_dec(v_a_327_);
return v_res_338_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_propagateNatShiftLeft___regBuiltin_Lean_Meta_Grind_Arith_propagateNatShiftLeft_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_3253038636____hygCtx___hyg_8_(){
_start:
{
lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; 
v___x_340_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_propagateNatShiftLeft___closed__3));
v___x_341_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_propagateNatShiftLeft___boxed), 12, 0);
v___x_342_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_340_, v___x_341_);
return v___x_342_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_propagateNatShiftLeft___regBuiltin_Lean_Meta_Grind_Arith_propagateNatShiftLeft_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_3253038636____hygCtx___hyg_8____boxed(lean_object* v_a_343_){
_start:
{
lean_object* v_res_344_; 
v_res_344_ = l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_propagateNatShiftLeft___regBuiltin_Lean_Meta_Grind_Arith_propagateNatShiftLeft_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_3253038636____hygCtx___hyg_8_();
return v_res_344_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_propagateNatShiftRight(lean_object* v_e_357_, lean_object* v_a_358_, lean_object* v_a_359_, lean_object* v_a_360_, lean_object* v_a_361_, lean_object* v_a_362_, lean_object* v_a_363_, lean_object* v_a_364_, lean_object* v_a_365_, lean_object* v_a_366_, lean_object* v_a_367_){
_start:
{
lean_object* v___f_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; 
v___f_369_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_propagateNatShiftRight___closed__0));
v___x_370_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_propagateNatShiftRight___closed__3));
v___x_371_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_propagateNatShiftRight___closed__5));
v___x_372_ = l_Lean_Meta_Grind_Arith_propagateNatBinOp(v___x_370_, v___x_371_, v___f_369_, v_e_357_, v_a_358_, v_a_359_, v_a_360_, v_a_361_, v_a_362_, v_a_363_, v_a_364_, v_a_365_, v_a_366_, v_a_367_);
return v___x_372_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_propagateNatShiftRight___boxed(lean_object* v_e_373_, lean_object* v_a_374_, lean_object* v_a_375_, lean_object* v_a_376_, lean_object* v_a_377_, lean_object* v_a_378_, lean_object* v_a_379_, lean_object* v_a_380_, lean_object* v_a_381_, lean_object* v_a_382_, lean_object* v_a_383_, lean_object* v_a_384_){
_start:
{
lean_object* v_res_385_; 
v_res_385_ = l_Lean_Meta_Grind_Arith_propagateNatShiftRight(v_e_373_, v_a_374_, v_a_375_, v_a_376_, v_a_377_, v_a_378_, v_a_379_, v_a_380_, v_a_381_, v_a_382_, v_a_383_);
lean_dec(v_a_383_);
lean_dec_ref(v_a_382_);
lean_dec(v_a_381_);
lean_dec_ref(v_a_380_);
lean_dec(v_a_379_);
lean_dec_ref(v_a_378_);
lean_dec(v_a_377_);
lean_dec_ref(v_a_376_);
lean_dec(v_a_375_);
lean_dec(v_a_374_);
return v_res_385_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_propagateNatShiftRight___regBuiltin_Lean_Meta_Grind_Arith_propagateNatShiftRight_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_1805815810____hygCtx___hyg_8_(){
_start:
{
lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; 
v___x_387_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_propagateNatShiftRight___closed__3));
v___x_388_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_propagateNatShiftRight___boxed), 12, 0);
v___x_389_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_387_, v___x_388_);
return v___x_389_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_propagateNatShiftRight___regBuiltin_Lean_Meta_Grind_Arith_propagateNatShiftRight_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_1805815810____hygCtx___hyg_8____boxed(lean_object* v_a_390_){
_start:
{
lean_object* v_res_391_; 
v_res_391_ = l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_propagateNatShiftRight___regBuiltin_Lean_Meta_Grind_Arith_propagateNatShiftRight_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_1805815810____hygCtx___hyg_8_();
return v_res_391_;
}
}
static uint64_t _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__1_spec__2_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_392_; uint64_t v___x_393_; 
v___x_392_ = lean_unsigned_to_nat(1723u);
v___x_393_ = lean_uint64_of_nat(v___x_392_);
return v___x_393_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__1_spec__2_spec__4___redArg(lean_object* v_x_394_, lean_object* v_x_395_){
_start:
{
if (lean_obj_tag(v_x_395_) == 0)
{
return v_x_394_;
}
else
{
lean_object* v_key_396_; lean_object* v_value_397_; lean_object* v_tail_398_; lean_object* v___x_400_; uint8_t v_isShared_401_; uint8_t v_isSharedCheck_424_; 
v_key_396_ = lean_ctor_get(v_x_395_, 0);
v_value_397_ = lean_ctor_get(v_x_395_, 1);
v_tail_398_ = lean_ctor_get(v_x_395_, 2);
v_isSharedCheck_424_ = !lean_is_exclusive(v_x_395_);
if (v_isSharedCheck_424_ == 0)
{
v___x_400_ = v_x_395_;
v_isShared_401_ = v_isSharedCheck_424_;
goto v_resetjp_399_;
}
else
{
lean_inc(v_tail_398_);
lean_inc(v_value_397_);
lean_inc(v_key_396_);
lean_dec(v_x_395_);
v___x_400_ = lean_box(0);
v_isShared_401_ = v_isSharedCheck_424_;
goto v_resetjp_399_;
}
v_resetjp_399_:
{
lean_object* v___x_402_; uint64_t v___y_404_; 
v___x_402_ = lean_array_get_size(v_x_394_);
if (lean_obj_tag(v_key_396_) == 0)
{
uint64_t v___x_422_; 
v___x_422_ = lean_uint64_once(&l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__1_spec__2_spec__4___redArg___closed__0, &l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__1_spec__2_spec__4___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__1_spec__2_spec__4___redArg___closed__0);
v___y_404_ = v___x_422_;
goto v___jp_403_;
}
else
{
uint64_t v_hash_423_; 
v_hash_423_ = lean_ctor_get_uint64(v_key_396_, sizeof(void*)*2);
v___y_404_ = v_hash_423_;
goto v___jp_403_;
}
v___jp_403_:
{
uint64_t v___x_405_; uint64_t v___x_406_; uint64_t v_fold_407_; uint64_t v___x_408_; uint64_t v___x_409_; uint64_t v___x_410_; size_t v___x_411_; size_t v___x_412_; size_t v___x_413_; size_t v___x_414_; size_t v___x_415_; lean_object* v___x_416_; lean_object* v___x_418_; 
v___x_405_ = 32ULL;
v___x_406_ = lean_uint64_shift_right(v___y_404_, v___x_405_);
v_fold_407_ = lean_uint64_xor(v___y_404_, v___x_406_);
v___x_408_ = 16ULL;
v___x_409_ = lean_uint64_shift_right(v_fold_407_, v___x_408_);
v___x_410_ = lean_uint64_xor(v_fold_407_, v___x_409_);
v___x_411_ = lean_uint64_to_usize(v___x_410_);
v___x_412_ = lean_usize_of_nat(v___x_402_);
v___x_413_ = ((size_t)1ULL);
v___x_414_ = lean_usize_sub(v___x_412_, v___x_413_);
v___x_415_ = lean_usize_land(v___x_411_, v___x_414_);
v___x_416_ = lean_array_uget_borrowed(v_x_394_, v___x_415_);
lean_inc(v___x_416_);
if (v_isShared_401_ == 0)
{
lean_ctor_set(v___x_400_, 2, v___x_416_);
v___x_418_ = v___x_400_;
goto v_reusejp_417_;
}
else
{
lean_object* v_reuseFailAlloc_421_; 
v_reuseFailAlloc_421_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_421_, 0, v_key_396_);
lean_ctor_set(v_reuseFailAlloc_421_, 1, v_value_397_);
lean_ctor_set(v_reuseFailAlloc_421_, 2, v___x_416_);
v___x_418_ = v_reuseFailAlloc_421_;
goto v_reusejp_417_;
}
v_reusejp_417_:
{
lean_object* v___x_419_; 
v___x_419_ = lean_array_uset(v_x_394_, v___x_415_, v___x_418_);
v_x_394_ = v___x_419_;
v_x_395_ = v_tail_398_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__1_spec__2___redArg(lean_object* v_i_425_, lean_object* v_source_426_, lean_object* v_target_427_){
_start:
{
lean_object* v___x_428_; uint8_t v___x_429_; 
v___x_428_ = lean_array_get_size(v_source_426_);
v___x_429_ = lean_nat_dec_lt(v_i_425_, v___x_428_);
if (v___x_429_ == 0)
{
lean_dec_ref(v_source_426_);
lean_dec(v_i_425_);
return v_target_427_;
}
else
{
lean_object* v_es_430_; lean_object* v___x_431_; lean_object* v_source_432_; lean_object* v_target_433_; lean_object* v___x_434_; lean_object* v___x_435_; 
v_es_430_ = lean_array_fget(v_source_426_, v_i_425_);
v___x_431_ = lean_box(0);
v_source_432_ = lean_array_fset(v_source_426_, v_i_425_, v___x_431_);
v_target_433_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__1_spec__2_spec__4___redArg(v_target_427_, v_es_430_);
v___x_434_ = lean_unsigned_to_nat(1u);
v___x_435_ = lean_nat_add(v_i_425_, v___x_434_);
lean_dec(v_i_425_);
v_i_425_ = v___x_435_;
v_source_426_ = v_source_432_;
v_target_427_ = v_target_433_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__1___redArg(lean_object* v_data_437_){
_start:
{
lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v_nbuckets_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; 
v___x_438_ = lean_array_get_size(v_data_437_);
v___x_439_ = lean_unsigned_to_nat(2u);
v_nbuckets_440_ = lean_nat_mul(v___x_438_, v___x_439_);
v___x_441_ = lean_unsigned_to_nat(0u);
v___x_442_ = lean_box(0);
v___x_443_ = lean_mk_array(v_nbuckets_440_, v___x_442_);
v___x_444_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__1_spec__2___redArg(v___x_441_, v_data_437_, v___x_443_);
return v___x_444_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__0___redArg(lean_object* v_a_445_, lean_object* v_x_446_){
_start:
{
if (lean_obj_tag(v_x_446_) == 0)
{
uint8_t v___x_447_; 
v___x_447_ = 0;
return v___x_447_;
}
else
{
lean_object* v_key_448_; lean_object* v_tail_449_; uint8_t v___x_450_; 
v_key_448_ = lean_ctor_get(v_x_446_, 0);
v_tail_449_ = lean_ctor_get(v_x_446_, 2);
v___x_450_ = lean_name_eq(v_key_448_, v_a_445_);
if (v___x_450_ == 0)
{
v_x_446_ = v_tail_449_;
goto _start;
}
else
{
return v___x_450_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__0___redArg___boxed(lean_object* v_a_452_, lean_object* v_x_453_){
_start:
{
uint8_t v_res_454_; lean_object* v_r_455_; 
v_res_454_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__0___redArg(v_a_452_, v_x_453_);
lean_dec(v_x_453_);
lean_dec(v_a_452_);
v_r_455_ = lean_box(v_res_454_);
return v_r_455_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0___redArg(lean_object* v_m_456_, lean_object* v_a_457_, lean_object* v_b_458_){
_start:
{
lean_object* v_size_459_; lean_object* v_buckets_460_; lean_object* v___x_461_; uint64_t v___y_463_; 
v_size_459_ = lean_ctor_get(v_m_456_, 0);
v_buckets_460_ = lean_ctor_get(v_m_456_, 1);
v___x_461_ = lean_array_get_size(v_buckets_460_);
if (lean_obj_tag(v_a_457_) == 0)
{
uint64_t v___x_500_; 
v___x_500_ = lean_uint64_once(&l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__1_spec__2_spec__4___redArg___closed__0, &l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__1_spec__2_spec__4___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__1_spec__2_spec__4___redArg___closed__0);
v___y_463_ = v___x_500_;
goto v___jp_462_;
}
else
{
uint64_t v_hash_501_; 
v_hash_501_ = lean_ctor_get_uint64(v_a_457_, sizeof(void*)*2);
v___y_463_ = v_hash_501_;
goto v___jp_462_;
}
v___jp_462_:
{
uint64_t v___x_464_; uint64_t v___x_465_; uint64_t v_fold_466_; uint64_t v___x_467_; uint64_t v___x_468_; uint64_t v___x_469_; size_t v___x_470_; size_t v___x_471_; size_t v___x_472_; size_t v___x_473_; size_t v___x_474_; lean_object* v_bkt_475_; uint8_t v___x_476_; 
v___x_464_ = 32ULL;
v___x_465_ = lean_uint64_shift_right(v___y_463_, v___x_464_);
v_fold_466_ = lean_uint64_xor(v___y_463_, v___x_465_);
v___x_467_ = 16ULL;
v___x_468_ = lean_uint64_shift_right(v_fold_466_, v___x_467_);
v___x_469_ = lean_uint64_xor(v_fold_466_, v___x_468_);
v___x_470_ = lean_uint64_to_usize(v___x_469_);
v___x_471_ = lean_usize_of_nat(v___x_461_);
v___x_472_ = ((size_t)1ULL);
v___x_473_ = lean_usize_sub(v___x_471_, v___x_472_);
v___x_474_ = lean_usize_land(v___x_470_, v___x_473_);
v_bkt_475_ = lean_array_uget_borrowed(v_buckets_460_, v___x_474_);
v___x_476_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__0___redArg(v_a_457_, v_bkt_475_);
if (v___x_476_ == 0)
{
lean_object* v___x_478_; uint8_t v_isShared_479_; uint8_t v_isSharedCheck_497_; 
lean_inc_ref(v_buckets_460_);
lean_inc(v_size_459_);
v_isSharedCheck_497_ = !lean_is_exclusive(v_m_456_);
if (v_isSharedCheck_497_ == 0)
{
lean_object* v_unused_498_; lean_object* v_unused_499_; 
v_unused_498_ = lean_ctor_get(v_m_456_, 1);
lean_dec(v_unused_498_);
v_unused_499_ = lean_ctor_get(v_m_456_, 0);
lean_dec(v_unused_499_);
v___x_478_ = v_m_456_;
v_isShared_479_ = v_isSharedCheck_497_;
goto v_resetjp_477_;
}
else
{
lean_dec(v_m_456_);
v___x_478_ = lean_box(0);
v_isShared_479_ = v_isSharedCheck_497_;
goto v_resetjp_477_;
}
v_resetjp_477_:
{
lean_object* v___x_480_; lean_object* v_size_x27_481_; lean_object* v___x_482_; lean_object* v_buckets_x27_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; uint8_t v___x_489_; 
v___x_480_ = lean_unsigned_to_nat(1u);
v_size_x27_481_ = lean_nat_add(v_size_459_, v___x_480_);
lean_dec(v_size_459_);
lean_inc(v_bkt_475_);
v___x_482_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_482_, 0, v_a_457_);
lean_ctor_set(v___x_482_, 1, v_b_458_);
lean_ctor_set(v___x_482_, 2, v_bkt_475_);
v_buckets_x27_483_ = lean_array_uset(v_buckets_460_, v___x_474_, v___x_482_);
v___x_484_ = lean_unsigned_to_nat(4u);
v___x_485_ = lean_nat_mul(v_size_x27_481_, v___x_484_);
v___x_486_ = lean_unsigned_to_nat(3u);
v___x_487_ = lean_nat_div(v___x_485_, v___x_486_);
lean_dec(v___x_485_);
v___x_488_ = lean_array_get_size(v_buckets_x27_483_);
v___x_489_ = lean_nat_dec_le(v___x_487_, v___x_488_);
lean_dec(v___x_487_);
if (v___x_489_ == 0)
{
lean_object* v_val_490_; lean_object* v___x_492_; 
v_val_490_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__1___redArg(v_buckets_x27_483_);
if (v_isShared_479_ == 0)
{
lean_ctor_set(v___x_478_, 1, v_val_490_);
lean_ctor_set(v___x_478_, 0, v_size_x27_481_);
v___x_492_ = v___x_478_;
goto v_reusejp_491_;
}
else
{
lean_object* v_reuseFailAlloc_493_; 
v_reuseFailAlloc_493_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_493_, 0, v_size_x27_481_);
lean_ctor_set(v_reuseFailAlloc_493_, 1, v_val_490_);
v___x_492_ = v_reuseFailAlloc_493_;
goto v_reusejp_491_;
}
v_reusejp_491_:
{
return v___x_492_;
}
}
else
{
lean_object* v___x_495_; 
if (v_isShared_479_ == 0)
{
lean_ctor_set(v___x_478_, 1, v_buckets_x27_483_);
lean_ctor_set(v___x_478_, 0, v_size_x27_481_);
v___x_495_ = v___x_478_;
goto v_reusejp_494_;
}
else
{
lean_object* v_reuseFailAlloc_496_; 
v_reuseFailAlloc_496_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_496_, 0, v_size_x27_481_);
lean_ctor_set(v_reuseFailAlloc_496_, 1, v_buckets_x27_483_);
v___x_495_ = v_reuseFailAlloc_496_;
goto v_reusejp_494_;
}
v_reusejp_494_:
{
return v___x_495_;
}
}
}
}
else
{
lean_dec(v_b_458_);
lean_dec(v_a_457_);
return v_m_456_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__1(lean_object* v_x_502_, lean_object* v_x_503_){
_start:
{
if (lean_obj_tag(v_x_503_) == 0)
{
return v_x_502_;
}
else
{
lean_object* v_head_504_; lean_object* v_tail_505_; lean_object* v___x_506_; lean_object* v___x_507_; 
v_head_504_ = lean_ctor_get(v_x_503_, 0);
lean_inc(v_head_504_);
v_tail_505_ = lean_ctor_get(v_x_503_, 1);
lean_inc(v_tail_505_);
lean_dec_ref(v_x_503_);
v___x_506_ = lean_box(0);
v___x_507_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0___redArg(v_x_502_, v_head_504_, v___x_506_);
v_x_502_ = v___x_507_;
v_x_503_ = v_tail_505_;
goto _start;
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__0(void){
_start:
{
lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; 
v___x_509_ = lean_box(0);
v___x_510_ = lean_unsigned_to_nat(16u);
v___x_511_ = lean_mk_array(v___x_510_, v___x_509_);
return v___x_511_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__1(void){
_start:
{
lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; 
v___x_512_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__0);
v___x_513_ = lean_unsigned_to_nat(0u);
v___x_514_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_514_, 0, v___x_513_);
lean_ctor_set(v___x_514_, 1, v___x_512_);
return v___x_514_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__34(void){
_start:
{
lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; 
v___x_581_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__33));
v___x_582_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__1, &l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__1);
v___x_583_ = l_List_foldl___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__1(v___x_582_, v___x_581_);
return v___x_583_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring(void){
_start:
{
lean_object* v___x_584_; 
v___x_584_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__34, &l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__34_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__34);
return v___x_584_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0(lean_object* v_00_u03b2_585_, lean_object* v_m_586_, lean_object* v_a_587_, lean_object* v_b_588_){
_start:
{
lean_object* v___x_589_; 
v___x_589_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0___redArg(v_m_586_, v_a_587_, v_b_588_);
return v___x_589_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__0(lean_object* v_00_u03b2_590_, lean_object* v_a_591_, lean_object* v_x_592_){
_start:
{
uint8_t v___x_593_; 
v___x_593_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__0___redArg(v_a_591_, v_x_592_);
return v___x_593_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__0___boxed(lean_object* v_00_u03b2_594_, lean_object* v_a_595_, lean_object* v_x_596_){
_start:
{
uint8_t v_res_597_; lean_object* v_r_598_; 
v_res_597_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__0(v_00_u03b2_594_, v_a_595_, v_x_596_);
lean_dec(v_x_596_);
lean_dec(v_a_595_);
v_r_598_ = lean_box(v_res_597_);
return v_r_598_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__1(lean_object* v_00_u03b2_599_, lean_object* v_data_600_){
_start:
{
lean_object* v___x_601_; 
v___x_601_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__1___redArg(v_data_600_);
return v___x_601_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_602_, lean_object* v_i_603_, lean_object* v_source_604_, lean_object* v_target_605_){
_start:
{
lean_object* v___x_606_; 
v___x_606_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__1_spec__2___redArg(v_i_603_, v_source_604_, v_target_605_);
return v___x_606_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_607_, lean_object* v_x_608_, lean_object* v_x_609_){
_start:
{
lean_object* v___x_610_; 
v___x_610_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__1_spec__2_spec__4___redArg(v_x_608_, v_x_609_);
return v___x_610_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isSupportedSemiringQuick_spec__0___redArg(lean_object* v_m_611_, lean_object* v_a_612_){
_start:
{
lean_object* v_buckets_613_; lean_object* v___x_614_; uint64_t v___y_616_; 
v_buckets_613_ = lean_ctor_get(v_m_611_, 1);
v___x_614_ = lean_array_get_size(v_buckets_613_);
if (lean_obj_tag(v_a_612_) == 0)
{
uint64_t v___x_630_; 
v___x_630_ = lean_uint64_once(&l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__1_spec__2_spec__4___redArg___closed__0, &l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__1_spec__2_spec__4___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__1_spec__2_spec__4___redArg___closed__0);
v___y_616_ = v___x_630_;
goto v___jp_615_;
}
else
{
uint64_t v_hash_631_; 
v_hash_631_ = lean_ctor_get_uint64(v_a_612_, sizeof(void*)*2);
v___y_616_ = v_hash_631_;
goto v___jp_615_;
}
v___jp_615_:
{
uint64_t v___x_617_; uint64_t v___x_618_; uint64_t v_fold_619_; uint64_t v___x_620_; uint64_t v___x_621_; uint64_t v___x_622_; size_t v___x_623_; size_t v___x_624_; size_t v___x_625_; size_t v___x_626_; size_t v___x_627_; lean_object* v___x_628_; uint8_t v___x_629_; 
v___x_617_ = 32ULL;
v___x_618_ = lean_uint64_shift_right(v___y_616_, v___x_617_);
v_fold_619_ = lean_uint64_xor(v___y_616_, v___x_618_);
v___x_620_ = 16ULL;
v___x_621_ = lean_uint64_shift_right(v_fold_619_, v___x_620_);
v___x_622_ = lean_uint64_xor(v_fold_619_, v___x_621_);
v___x_623_ = lean_uint64_to_usize(v___x_622_);
v___x_624_ = lean_usize_of_nat(v___x_614_);
v___x_625_ = ((size_t)1ULL);
v___x_626_ = lean_usize_sub(v___x_624_, v___x_625_);
v___x_627_ = lean_usize_land(v___x_623_, v___x_626_);
v___x_628_ = lean_array_uget_borrowed(v_buckets_613_, v___x_627_);
v___x_629_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__0___redArg(v_a_612_, v___x_628_);
return v___x_629_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isSupportedSemiringQuick_spec__0___redArg___boxed(lean_object* v_m_632_, lean_object* v_a_633_){
_start:
{
uint8_t v_res_634_; lean_object* v_r_635_; 
v_res_634_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isSupportedSemiringQuick_spec__0___redArg(v_m_632_, v_a_633_);
lean_dec(v_a_633_);
lean_dec_ref(v_m_632_);
v_r_635_ = lean_box(v_res_634_);
return v_r_635_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isSupportedSemiringQuick(lean_object* v_type_636_){
_start:
{
lean_object* v___x_637_; 
v___x_637_ = l_Lean_Expr_getAppFn(v_type_636_);
if (lean_obj_tag(v___x_637_) == 4)
{
lean_object* v_declName_638_; lean_object* v___x_639_; uint8_t v___x_640_; 
v_declName_638_ = lean_ctor_get(v___x_637_, 0);
lean_inc(v_declName_638_);
lean_dec_ref(v___x_637_);
v___x_639_ = l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring;
v___x_640_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isSupportedSemiringQuick_spec__0___redArg(v___x_639_, v_declName_638_);
lean_dec(v_declName_638_);
return v___x_640_;
}
else
{
uint8_t v___x_641_; 
lean_dec_ref(v___x_637_);
v___x_641_ = 0;
return v___x_641_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isSupportedSemiringQuick___boxed(lean_object* v_type_642_){
_start:
{
uint8_t v_res_643_; lean_object* v_r_644_; 
v_res_643_ = l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isSupportedSemiringQuick(v_type_642_);
lean_dec_ref(v_type_642_);
v_r_644_ = lean_box(v_res_643_);
return v_r_644_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isSupportedSemiringQuick_spec__0(lean_object* v_00_u03b2_645_, lean_object* v_m_646_, lean_object* v_a_647_){
_start:
{
uint8_t v___x_648_; 
v___x_648_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isSupportedSemiringQuick_spec__0___redArg(v_m_646_, v_a_647_);
return v___x_648_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isSupportedSemiringQuick_spec__0___boxed(lean_object* v_00_u03b2_649_, lean_object* v_m_650_, lean_object* v_a_651_){
_start:
{
uint8_t v_res_652_; lean_object* v_r_653_; 
v_res_652_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isSupportedSemiringQuick_spec__0(v_00_u03b2_649_, v_m_650_, v_a_651_);
lean_dec(v_a_651_);
lean_dec_ref(v_m_650_);
v_r_653_ = lean_box(v_res_652_);
return v_r_653_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isUnsupportedSemiring_x3f(lean_object* v_type_654_, lean_object* v_a_655_, lean_object* v_a_656_, lean_object* v_a_657_, lean_object* v_a_658_, lean_object* v_a_659_, lean_object* v_a_660_, lean_object* v_a_661_, lean_object* v_a_662_, lean_object* v_a_663_, lean_object* v_a_664_){
_start:
{
uint8_t v___x_666_; 
v___x_666_ = l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isSupportedSemiringQuick(v_type_654_);
if (v___x_666_ == 0)
{
lean_object* v___x_667_; 
lean_inc_ref(v_type_654_);
v___x_667_ = l_Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f(v_type_654_, v_a_655_, v_a_656_, v_a_657_, v_a_658_, v_a_659_, v_a_660_, v_a_661_, v_a_662_, v_a_663_, v_a_664_);
if (lean_obj_tag(v___x_667_) == 0)
{
lean_object* v_a_668_; lean_object* v___x_670_; uint8_t v_isShared_671_; uint8_t v_isSharedCheck_794_; 
v_a_668_ = lean_ctor_get(v___x_667_, 0);
v_isSharedCheck_794_ = !lean_is_exclusive(v___x_667_);
if (v_isSharedCheck_794_ == 0)
{
v___x_670_ = v___x_667_;
v_isShared_671_ = v_isSharedCheck_794_;
goto v_resetjp_669_;
}
else
{
lean_inc(v_a_668_);
lean_dec(v___x_667_);
v___x_670_ = lean_box(0);
v_isShared_671_ = v_isSharedCheck_794_;
goto v_resetjp_669_;
}
v_resetjp_669_:
{
if (lean_obj_tag(v_a_668_) == 0)
{
if (v___x_666_ == 0)
{
lean_object* v___x_677_; 
lean_del_object(v___x_670_);
lean_inc_ref(v_type_654_);
v___x_677_ = l_Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f(v_type_654_, v_a_655_, v_a_656_, v_a_657_, v_a_658_, v_a_659_, v_a_660_, v_a_661_, v_a_662_, v_a_663_, v_a_664_);
if (lean_obj_tag(v___x_677_) == 0)
{
lean_object* v_a_678_; 
v_a_678_ = lean_ctor_get(v___x_677_, 0);
lean_inc(v_a_678_);
lean_dec_ref(v___x_677_);
if (lean_obj_tag(v_a_678_) == 1)
{
lean_object* v_val_679_; lean_object* v___x_681_; uint8_t v_isShared_682_; uint8_t v_isSharedCheck_705_; 
lean_dec_ref(v_type_654_);
v_val_679_ = lean_ctor_get(v_a_678_, 0);
v_isSharedCheck_705_ = !lean_is_exclusive(v_a_678_);
if (v_isSharedCheck_705_ == 0)
{
v___x_681_ = v_a_678_;
v_isShared_682_ = v_isSharedCheck_705_;
goto v_resetjp_680_;
}
else
{
lean_inc(v_val_679_);
lean_dec(v_a_678_);
v___x_681_ = lean_box(0);
v_isShared_682_ = v_isSharedCheck_705_;
goto v_resetjp_680_;
}
v_resetjp_680_:
{
lean_object* v___x_683_; 
v___x_683_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring(v_val_679_, v_a_655_, v_a_656_, v_a_657_, v_a_658_, v_a_659_, v_a_660_, v_a_661_, v_a_662_, v_a_663_, v_a_664_);
lean_dec(v_val_679_);
if (lean_obj_tag(v___x_683_) == 0)
{
lean_object* v_a_684_; lean_object* v___x_686_; uint8_t v_isShared_687_; uint8_t v_isSharedCheck_696_; 
v_a_684_ = lean_ctor_get(v___x_683_, 0);
v_isSharedCheck_696_ = !lean_is_exclusive(v___x_683_);
if (v_isSharedCheck_696_ == 0)
{
v___x_686_ = v___x_683_;
v_isShared_687_ = v_isSharedCheck_696_;
goto v_resetjp_685_;
}
else
{
lean_inc(v_a_684_);
lean_dec(v___x_683_);
v___x_686_ = lean_box(0);
v_isShared_687_ = v_isSharedCheck_696_;
goto v_resetjp_685_;
}
v_resetjp_685_:
{
lean_object* v_toSemiring_688_; lean_object* v_semiringInst_689_; lean_object* v___x_691_; 
v_toSemiring_688_ = lean_ctor_get(v_a_684_, 0);
lean_inc_ref(v_toSemiring_688_);
lean_dec(v_a_684_);
v_semiringInst_689_ = lean_ctor_get(v_toSemiring_688_, 3);
lean_inc_ref(v_semiringInst_689_);
lean_dec_ref(v_toSemiring_688_);
if (v_isShared_682_ == 0)
{
lean_ctor_set(v___x_681_, 0, v_semiringInst_689_);
v___x_691_ = v___x_681_;
goto v_reusejp_690_;
}
else
{
lean_object* v_reuseFailAlloc_695_; 
v_reuseFailAlloc_695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_695_, 0, v_semiringInst_689_);
v___x_691_ = v_reuseFailAlloc_695_;
goto v_reusejp_690_;
}
v_reusejp_690_:
{
lean_object* v___x_693_; 
if (v_isShared_687_ == 0)
{
lean_ctor_set(v___x_686_, 0, v___x_691_);
v___x_693_ = v___x_686_;
goto v_reusejp_692_;
}
else
{
lean_object* v_reuseFailAlloc_694_; 
v_reuseFailAlloc_694_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_694_, 0, v___x_691_);
v___x_693_ = v_reuseFailAlloc_694_;
goto v_reusejp_692_;
}
v_reusejp_692_:
{
return v___x_693_;
}
}
}
}
else
{
lean_object* v_a_697_; lean_object* v___x_699_; uint8_t v_isShared_700_; uint8_t v_isSharedCheck_704_; 
lean_del_object(v___x_681_);
v_a_697_ = lean_ctor_get(v___x_683_, 0);
v_isSharedCheck_704_ = !lean_is_exclusive(v___x_683_);
if (v_isSharedCheck_704_ == 0)
{
v___x_699_ = v___x_683_;
v_isShared_700_ = v_isSharedCheck_704_;
goto v_resetjp_698_;
}
else
{
lean_inc(v_a_697_);
lean_dec(v___x_683_);
v___x_699_ = lean_box(0);
v_isShared_700_ = v_isSharedCheck_704_;
goto v_resetjp_698_;
}
v_resetjp_698_:
{
lean_object* v___x_702_; 
if (v_isShared_700_ == 0)
{
v___x_702_ = v___x_699_;
goto v_reusejp_701_;
}
else
{
lean_object* v_reuseFailAlloc_703_; 
v_reuseFailAlloc_703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_703_, 0, v_a_697_);
v___x_702_ = v_reuseFailAlloc_703_;
goto v_reusejp_701_;
}
v_reusejp_701_:
{
return v___x_702_;
}
}
}
}
}
else
{
lean_object* v___x_706_; 
lean_dec(v_a_678_);
lean_inc_ref(v_type_654_);
v___x_706_ = l_Lean_Meta_Grind_Arith_CommRing_getNonCommRingId_x3f(v_type_654_, v_a_655_, v_a_656_, v_a_657_, v_a_658_, v_a_659_, v_a_660_, v_a_661_, v_a_662_, v_a_663_, v_a_664_);
if (lean_obj_tag(v___x_706_) == 0)
{
lean_object* v_a_707_; 
v_a_707_ = lean_ctor_get(v___x_706_, 0);
lean_inc(v_a_707_);
lean_dec_ref(v___x_706_);
if (lean_obj_tag(v_a_707_) == 1)
{
lean_object* v_val_708_; lean_object* v___x_710_; uint8_t v_isShared_711_; uint8_t v_isSharedCheck_733_; 
lean_dec_ref(v_type_654_);
v_val_708_ = lean_ctor_get(v_a_707_, 0);
v_isSharedCheck_733_ = !lean_is_exclusive(v_a_707_);
if (v_isSharedCheck_733_ == 0)
{
v___x_710_ = v_a_707_;
v_isShared_711_ = v_isSharedCheck_733_;
goto v_resetjp_709_;
}
else
{
lean_inc(v_val_708_);
lean_dec(v_a_707_);
v___x_710_ = lean_box(0);
v_isShared_711_ = v_isSharedCheck_733_;
goto v_resetjp_709_;
}
v_resetjp_709_:
{
lean_object* v___x_712_; 
v___x_712_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing(v_val_708_, v_a_655_, v_a_656_, v_a_657_, v_a_658_, v_a_659_, v_a_660_, v_a_661_, v_a_662_, v_a_663_, v_a_664_);
lean_dec(v_val_708_);
if (lean_obj_tag(v___x_712_) == 0)
{
lean_object* v_a_713_; lean_object* v___x_715_; uint8_t v_isShared_716_; uint8_t v_isSharedCheck_724_; 
v_a_713_ = lean_ctor_get(v___x_712_, 0);
v_isSharedCheck_724_ = !lean_is_exclusive(v___x_712_);
if (v_isSharedCheck_724_ == 0)
{
v___x_715_ = v___x_712_;
v_isShared_716_ = v_isSharedCheck_724_;
goto v_resetjp_714_;
}
else
{
lean_inc(v_a_713_);
lean_dec(v___x_712_);
v___x_715_ = lean_box(0);
v_isShared_716_ = v_isSharedCheck_724_;
goto v_resetjp_714_;
}
v_resetjp_714_:
{
lean_object* v_semiringInst_717_; lean_object* v___x_719_; 
v_semiringInst_717_ = lean_ctor_get(v_a_713_, 4);
lean_inc_ref(v_semiringInst_717_);
lean_dec(v_a_713_);
if (v_isShared_711_ == 0)
{
lean_ctor_set(v___x_710_, 0, v_semiringInst_717_);
v___x_719_ = v___x_710_;
goto v_reusejp_718_;
}
else
{
lean_object* v_reuseFailAlloc_723_; 
v_reuseFailAlloc_723_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_723_, 0, v_semiringInst_717_);
v___x_719_ = v_reuseFailAlloc_723_;
goto v_reusejp_718_;
}
v_reusejp_718_:
{
lean_object* v___x_721_; 
if (v_isShared_716_ == 0)
{
lean_ctor_set(v___x_715_, 0, v___x_719_);
v___x_721_ = v___x_715_;
goto v_reusejp_720_;
}
else
{
lean_object* v_reuseFailAlloc_722_; 
v_reuseFailAlloc_722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_722_, 0, v___x_719_);
v___x_721_ = v_reuseFailAlloc_722_;
goto v_reusejp_720_;
}
v_reusejp_720_:
{
return v___x_721_;
}
}
}
}
else
{
lean_object* v_a_725_; lean_object* v___x_727_; uint8_t v_isShared_728_; uint8_t v_isSharedCheck_732_; 
lean_del_object(v___x_710_);
v_a_725_ = lean_ctor_get(v___x_712_, 0);
v_isSharedCheck_732_ = !lean_is_exclusive(v___x_712_);
if (v_isSharedCheck_732_ == 0)
{
v___x_727_ = v___x_712_;
v_isShared_728_ = v_isSharedCheck_732_;
goto v_resetjp_726_;
}
else
{
lean_inc(v_a_725_);
lean_dec(v___x_712_);
v___x_727_ = lean_box(0);
v_isShared_728_ = v_isSharedCheck_732_;
goto v_resetjp_726_;
}
v_resetjp_726_:
{
lean_object* v___x_730_; 
if (v_isShared_728_ == 0)
{
v___x_730_ = v___x_727_;
goto v_reusejp_729_;
}
else
{
lean_object* v_reuseFailAlloc_731_; 
v_reuseFailAlloc_731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_731_, 0, v_a_725_);
v___x_730_ = v_reuseFailAlloc_731_;
goto v_reusejp_729_;
}
v_reusejp_729_:
{
return v___x_730_;
}
}
}
}
}
else
{
lean_object* v___x_734_; 
lean_dec(v_a_707_);
v___x_734_ = l_Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f___redArg(v_type_654_, v_a_655_, v_a_661_, v_a_662_, v_a_663_, v_a_664_);
if (lean_obj_tag(v___x_734_) == 0)
{
lean_object* v_a_735_; lean_object* v___x_737_; uint8_t v_isShared_738_; uint8_t v_isSharedCheck_769_; 
v_a_735_ = lean_ctor_get(v___x_734_, 0);
v_isSharedCheck_769_ = !lean_is_exclusive(v___x_734_);
if (v_isSharedCheck_769_ == 0)
{
v___x_737_ = v___x_734_;
v_isShared_738_ = v_isSharedCheck_769_;
goto v_resetjp_736_;
}
else
{
lean_inc(v_a_735_);
lean_dec(v___x_734_);
v___x_737_ = lean_box(0);
v_isShared_738_ = v_isSharedCheck_769_;
goto v_resetjp_736_;
}
v_resetjp_736_:
{
if (lean_obj_tag(v_a_735_) == 1)
{
lean_object* v_val_739_; lean_object* v___x_741_; uint8_t v_isShared_742_; uint8_t v_isSharedCheck_764_; 
lean_del_object(v___x_737_);
v_val_739_ = lean_ctor_get(v_a_735_, 0);
v_isSharedCheck_764_ = !lean_is_exclusive(v_a_735_);
if (v_isSharedCheck_764_ == 0)
{
v___x_741_ = v_a_735_;
v_isShared_742_ = v_isSharedCheck_764_;
goto v_resetjp_740_;
}
else
{
lean_inc(v_val_739_);
lean_dec(v_a_735_);
v___x_741_ = lean_box(0);
v_isShared_742_ = v_isSharedCheck_764_;
goto v_resetjp_740_;
}
v_resetjp_740_:
{
lean_object* v___x_743_; 
v___x_743_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiring(v_val_739_, v_a_655_, v_a_656_, v_a_657_, v_a_658_, v_a_659_, v_a_660_, v_a_661_, v_a_662_, v_a_663_, v_a_664_);
lean_dec(v_val_739_);
if (lean_obj_tag(v___x_743_) == 0)
{
lean_object* v_a_744_; lean_object* v___x_746_; uint8_t v_isShared_747_; uint8_t v_isSharedCheck_755_; 
v_a_744_ = lean_ctor_get(v___x_743_, 0);
v_isSharedCheck_755_ = !lean_is_exclusive(v___x_743_);
if (v_isSharedCheck_755_ == 0)
{
v___x_746_ = v___x_743_;
v_isShared_747_ = v_isSharedCheck_755_;
goto v_resetjp_745_;
}
else
{
lean_inc(v_a_744_);
lean_dec(v___x_743_);
v___x_746_ = lean_box(0);
v_isShared_747_ = v_isSharedCheck_755_;
goto v_resetjp_745_;
}
v_resetjp_745_:
{
lean_object* v_semiringInst_748_; lean_object* v___x_750_; 
v_semiringInst_748_ = lean_ctor_get(v_a_744_, 3);
lean_inc_ref(v_semiringInst_748_);
lean_dec(v_a_744_);
if (v_isShared_742_ == 0)
{
lean_ctor_set(v___x_741_, 0, v_semiringInst_748_);
v___x_750_ = v___x_741_;
goto v_reusejp_749_;
}
else
{
lean_object* v_reuseFailAlloc_754_; 
v_reuseFailAlloc_754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_754_, 0, v_semiringInst_748_);
v___x_750_ = v_reuseFailAlloc_754_;
goto v_reusejp_749_;
}
v_reusejp_749_:
{
lean_object* v___x_752_; 
if (v_isShared_747_ == 0)
{
lean_ctor_set(v___x_746_, 0, v___x_750_);
v___x_752_ = v___x_746_;
goto v_reusejp_751_;
}
else
{
lean_object* v_reuseFailAlloc_753_; 
v_reuseFailAlloc_753_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_753_, 0, v___x_750_);
v___x_752_ = v_reuseFailAlloc_753_;
goto v_reusejp_751_;
}
v_reusejp_751_:
{
return v___x_752_;
}
}
}
}
else
{
lean_object* v_a_756_; lean_object* v___x_758_; uint8_t v_isShared_759_; uint8_t v_isSharedCheck_763_; 
lean_del_object(v___x_741_);
v_a_756_ = lean_ctor_get(v___x_743_, 0);
v_isSharedCheck_763_ = !lean_is_exclusive(v___x_743_);
if (v_isSharedCheck_763_ == 0)
{
v___x_758_ = v___x_743_;
v_isShared_759_ = v_isSharedCheck_763_;
goto v_resetjp_757_;
}
else
{
lean_inc(v_a_756_);
lean_dec(v___x_743_);
v___x_758_ = lean_box(0);
v_isShared_759_ = v_isSharedCheck_763_;
goto v_resetjp_757_;
}
v_resetjp_757_:
{
lean_object* v___x_761_; 
if (v_isShared_759_ == 0)
{
v___x_761_ = v___x_758_;
goto v_reusejp_760_;
}
else
{
lean_object* v_reuseFailAlloc_762_; 
v_reuseFailAlloc_762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_762_, 0, v_a_756_);
v___x_761_ = v_reuseFailAlloc_762_;
goto v_reusejp_760_;
}
v_reusejp_760_:
{
return v___x_761_;
}
}
}
}
}
else
{
lean_object* v___x_765_; lean_object* v___x_767_; 
lean_dec(v_a_735_);
v___x_765_ = lean_box(0);
if (v_isShared_738_ == 0)
{
lean_ctor_set(v___x_737_, 0, v___x_765_);
v___x_767_ = v___x_737_;
goto v_reusejp_766_;
}
else
{
lean_object* v_reuseFailAlloc_768_; 
v_reuseFailAlloc_768_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_768_, 0, v___x_765_);
v___x_767_ = v_reuseFailAlloc_768_;
goto v_reusejp_766_;
}
v_reusejp_766_:
{
return v___x_767_;
}
}
}
}
else
{
lean_object* v_a_770_; lean_object* v___x_772_; uint8_t v_isShared_773_; uint8_t v_isSharedCheck_777_; 
v_a_770_ = lean_ctor_get(v___x_734_, 0);
v_isSharedCheck_777_ = !lean_is_exclusive(v___x_734_);
if (v_isSharedCheck_777_ == 0)
{
v___x_772_ = v___x_734_;
v_isShared_773_ = v_isSharedCheck_777_;
goto v_resetjp_771_;
}
else
{
lean_inc(v_a_770_);
lean_dec(v___x_734_);
v___x_772_ = lean_box(0);
v_isShared_773_ = v_isSharedCheck_777_;
goto v_resetjp_771_;
}
v_resetjp_771_:
{
lean_object* v___x_775_; 
if (v_isShared_773_ == 0)
{
v___x_775_ = v___x_772_;
goto v_reusejp_774_;
}
else
{
lean_object* v_reuseFailAlloc_776_; 
v_reuseFailAlloc_776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_776_, 0, v_a_770_);
v___x_775_ = v_reuseFailAlloc_776_;
goto v_reusejp_774_;
}
v_reusejp_774_:
{
return v___x_775_;
}
}
}
}
}
else
{
lean_object* v_a_778_; lean_object* v___x_780_; uint8_t v_isShared_781_; uint8_t v_isSharedCheck_785_; 
lean_dec_ref(v_type_654_);
v_a_778_ = lean_ctor_get(v___x_706_, 0);
v_isSharedCheck_785_ = !lean_is_exclusive(v___x_706_);
if (v_isSharedCheck_785_ == 0)
{
v___x_780_ = v___x_706_;
v_isShared_781_ = v_isSharedCheck_785_;
goto v_resetjp_779_;
}
else
{
lean_inc(v_a_778_);
lean_dec(v___x_706_);
v___x_780_ = lean_box(0);
v_isShared_781_ = v_isSharedCheck_785_;
goto v_resetjp_779_;
}
v_resetjp_779_:
{
lean_object* v___x_783_; 
if (v_isShared_781_ == 0)
{
v___x_783_ = v___x_780_;
goto v_reusejp_782_;
}
else
{
lean_object* v_reuseFailAlloc_784_; 
v_reuseFailAlloc_784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_784_, 0, v_a_778_);
v___x_783_ = v_reuseFailAlloc_784_;
goto v_reusejp_782_;
}
v_reusejp_782_:
{
return v___x_783_;
}
}
}
}
}
else
{
lean_object* v_a_786_; lean_object* v___x_788_; uint8_t v_isShared_789_; uint8_t v_isSharedCheck_793_; 
lean_dec_ref(v_type_654_);
v_a_786_ = lean_ctor_get(v___x_677_, 0);
v_isSharedCheck_793_ = !lean_is_exclusive(v___x_677_);
if (v_isSharedCheck_793_ == 0)
{
v___x_788_ = v___x_677_;
v_isShared_789_ = v_isSharedCheck_793_;
goto v_resetjp_787_;
}
else
{
lean_inc(v_a_786_);
lean_dec(v___x_677_);
v___x_788_ = lean_box(0);
v_isShared_789_ = v_isSharedCheck_793_;
goto v_resetjp_787_;
}
v_resetjp_787_:
{
lean_object* v___x_791_; 
if (v_isShared_789_ == 0)
{
v___x_791_ = v___x_788_;
goto v_reusejp_790_;
}
else
{
lean_object* v_reuseFailAlloc_792_; 
v_reuseFailAlloc_792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_792_, 0, v_a_786_);
v___x_791_ = v_reuseFailAlloc_792_;
goto v_reusejp_790_;
}
v_reusejp_790_:
{
return v___x_791_;
}
}
}
}
else
{
lean_dec_ref(v_type_654_);
goto v___jp_672_;
}
}
else
{
lean_dec_ref(v_a_668_);
lean_dec_ref(v_type_654_);
goto v___jp_672_;
}
v___jp_672_:
{
lean_object* v___x_673_; lean_object* v___x_675_; 
v___x_673_ = lean_box(0);
if (v_isShared_671_ == 0)
{
lean_ctor_set(v___x_670_, 0, v___x_673_);
v___x_675_ = v___x_670_;
goto v_reusejp_674_;
}
else
{
lean_object* v_reuseFailAlloc_676_; 
v_reuseFailAlloc_676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_676_, 0, v___x_673_);
v___x_675_ = v_reuseFailAlloc_676_;
goto v_reusejp_674_;
}
v_reusejp_674_:
{
return v___x_675_;
}
}
}
}
else
{
lean_object* v_a_795_; lean_object* v___x_797_; uint8_t v_isShared_798_; uint8_t v_isSharedCheck_802_; 
lean_dec_ref(v_type_654_);
v_a_795_ = lean_ctor_get(v___x_667_, 0);
v_isSharedCheck_802_ = !lean_is_exclusive(v___x_667_);
if (v_isSharedCheck_802_ == 0)
{
v___x_797_ = v___x_667_;
v_isShared_798_ = v_isSharedCheck_802_;
goto v_resetjp_796_;
}
else
{
lean_inc(v_a_795_);
lean_dec(v___x_667_);
v___x_797_ = lean_box(0);
v_isShared_798_ = v_isSharedCheck_802_;
goto v_resetjp_796_;
}
v_resetjp_796_:
{
lean_object* v___x_800_; 
if (v_isShared_798_ == 0)
{
v___x_800_ = v___x_797_;
goto v_reusejp_799_;
}
else
{
lean_object* v_reuseFailAlloc_801_; 
v_reuseFailAlloc_801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_801_, 0, v_a_795_);
v___x_800_ = v_reuseFailAlloc_801_;
goto v_reusejp_799_;
}
v_reusejp_799_:
{
return v___x_800_;
}
}
}
}
else
{
lean_object* v___x_803_; lean_object* v___x_804_; 
lean_dec_ref(v_type_654_);
v___x_803_ = lean_box(0);
v___x_804_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_804_, 0, v___x_803_);
return v___x_804_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isUnsupportedSemiring_x3f___boxed(lean_object* v_type_805_, lean_object* v_a_806_, lean_object* v_a_807_, lean_object* v_a_808_, lean_object* v_a_809_, lean_object* v_a_810_, lean_object* v_a_811_, lean_object* v_a_812_, lean_object* v_a_813_, lean_object* v_a_814_, lean_object* v_a_815_, lean_object* v_a_816_){
_start:
{
lean_object* v_res_817_; 
v_res_817_ = l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isUnsupportedSemiring_x3f(v_type_805_, v_a_806_, v_a_807_, v_a_808_, v_a_809_, v_a_810_, v_a_811_, v_a_812_, v_a_813_, v_a_814_, v_a_815_);
lean_dec(v_a_815_);
lean_dec_ref(v_a_814_);
lean_dec(v_a_813_);
lean_dec_ref(v_a_812_);
lean_dec(v_a_811_);
lean_dec_ref(v_a_810_);
lean_dec(v_a_809_);
lean_dec_ref(v_a_808_);
lean_dec(v_a_807_);
lean_dec(v_a_806_);
return v_res_817_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isOfNat_x3f(lean_object* v_a_823_, lean_object* v_a_824_, lean_object* v_a_825_, lean_object* v_a_826_, lean_object* v_a_827_){
_start:
{
lean_object* v___x_832_; uint8_t v___x_833_; 
v___x_832_ = l_Lean_Expr_cleanupAnnotations(v_a_823_);
v___x_833_ = l_Lean_Expr_isApp(v___x_832_);
if (v___x_833_ == 0)
{
lean_dec_ref(v___x_832_);
goto v___jp_829_;
}
else
{
lean_object* v___x_834_; uint8_t v___x_835_; 
v___x_834_ = l_Lean_Expr_appFnCleanup___redArg(v___x_832_);
v___x_835_ = l_Lean_Expr_isApp(v___x_834_);
if (v___x_835_ == 0)
{
lean_dec_ref(v___x_834_);
goto v___jp_829_;
}
else
{
lean_object* v_arg_836_; lean_object* v___x_837_; uint8_t v___x_838_; 
v_arg_836_ = lean_ctor_get(v___x_834_, 1);
lean_inc_ref(v_arg_836_);
v___x_837_ = l_Lean_Expr_appFnCleanup___redArg(v___x_834_);
v___x_838_ = l_Lean_Expr_isApp(v___x_837_);
if (v___x_838_ == 0)
{
lean_dec_ref(v___x_837_);
lean_dec_ref(v_arg_836_);
goto v___jp_829_;
}
else
{
lean_object* v___x_839_; lean_object* v___x_840_; uint8_t v___x_841_; 
v___x_839_ = l_Lean_Expr_appFnCleanup___redArg(v___x_837_);
v___x_840_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isOfNat_x3f___closed__2));
v___x_841_ = l_Lean_Expr_isConstOf(v___x_839_, v___x_840_);
lean_dec_ref(v___x_839_);
if (v___x_841_ == 0)
{
lean_dec_ref(v_arg_836_);
goto v___jp_829_;
}
else
{
lean_object* v___x_842_; 
v___x_842_ = l_Lean_Meta_getNatValue_x3f(v_arg_836_, v_a_824_, v_a_825_, v_a_826_, v_a_827_);
lean_dec_ref(v_arg_836_);
return v___x_842_;
}
}
}
}
v___jp_829_:
{
lean_object* v___x_830_; lean_object* v___x_831_; 
v___x_830_ = lean_box(0);
v___x_831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_831_, 0, v___x_830_);
return v___x_831_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isOfNat_x3f___boxed(lean_object* v_a_843_, lean_object* v_a_844_, lean_object* v_a_845_, lean_object* v_a_846_, lean_object* v_a_847_, lean_object* v_a_848_){
_start:
{
lean_object* v_res_849_; 
v_res_849_ = l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isOfNat_x3f(v_a_843_, v_a_844_, v_a_845_, v_a_846_, v_a_847_);
lean_dec(v_a_847_);
lean_dec_ref(v_a_846_);
lean_dec(v_a_845_);
lean_dec_ref(v_a_844_);
return v_res_849_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_propagateMul(lean_object* v_e_880_, lean_object* v_a_881_, lean_object* v_a_882_, lean_object* v_a_883_, lean_object* v_a_884_, lean_object* v_a_885_, lean_object* v_a_886_, lean_object* v_a_887_, lean_object* v_a_888_, lean_object* v_a_889_, lean_object* v_a_890_){
_start:
{
lean_object* v___x_895_; uint8_t v___x_896_; 
lean_inc_ref(v_e_880_);
v___x_895_ = l_Lean_Expr_cleanupAnnotations(v_e_880_);
v___x_896_ = l_Lean_Expr_isApp(v___x_895_);
if (v___x_896_ == 0)
{
lean_dec_ref(v___x_895_);
lean_dec_ref(v_e_880_);
goto v___jp_892_;
}
else
{
lean_object* v_arg_897_; lean_object* v___x_898_; uint8_t v___x_899_; 
v_arg_897_ = lean_ctor_get(v___x_895_, 1);
lean_inc_ref(v_arg_897_);
v___x_898_ = l_Lean_Expr_appFnCleanup___redArg(v___x_895_);
v___x_899_ = l_Lean_Expr_isApp(v___x_898_);
if (v___x_899_ == 0)
{
lean_dec_ref(v___x_898_);
lean_dec_ref(v_arg_897_);
lean_dec_ref(v_e_880_);
goto v___jp_892_;
}
else
{
lean_object* v_arg_900_; lean_object* v___x_901_; uint8_t v___x_902_; 
v_arg_900_ = lean_ctor_get(v___x_898_, 1);
lean_inc_ref(v_arg_900_);
v___x_901_ = l_Lean_Expr_appFnCleanup___redArg(v___x_898_);
v___x_902_ = l_Lean_Expr_isApp(v___x_901_);
if (v___x_902_ == 0)
{
lean_dec_ref(v___x_901_);
lean_dec_ref(v_arg_900_);
lean_dec_ref(v_arg_897_);
lean_dec_ref(v_e_880_);
goto v___jp_892_;
}
else
{
lean_object* v___x_903_; uint8_t v___x_904_; 
v___x_903_ = l_Lean_Expr_appFnCleanup___redArg(v___x_901_);
v___x_904_ = l_Lean_Expr_isApp(v___x_903_);
if (v___x_904_ == 0)
{
lean_dec_ref(v___x_903_);
lean_dec_ref(v_arg_900_);
lean_dec_ref(v_arg_897_);
lean_dec_ref(v_e_880_);
goto v___jp_892_;
}
else
{
lean_object* v_arg_905_; lean_object* v___x_906_; uint8_t v___x_907_; 
v_arg_905_ = lean_ctor_get(v___x_903_, 1);
lean_inc_ref(v_arg_905_);
v___x_906_ = l_Lean_Expr_appFnCleanup___redArg(v___x_903_);
v___x_907_ = l_Lean_Expr_isApp(v___x_906_);
if (v___x_907_ == 0)
{
lean_dec_ref(v___x_906_);
lean_dec_ref(v_arg_905_);
lean_dec_ref(v_arg_900_);
lean_dec_ref(v_arg_897_);
lean_dec_ref(v_e_880_);
goto v___jp_892_;
}
else
{
lean_object* v_arg_908_; lean_object* v___x_909_; uint8_t v___x_910_; 
v_arg_908_ = lean_ctor_get(v___x_906_, 1);
lean_inc_ref(v_arg_908_);
v___x_909_ = l_Lean_Expr_appFnCleanup___redArg(v___x_906_);
v___x_910_ = l_Lean_Expr_isApp(v___x_909_);
if (v___x_910_ == 0)
{
lean_dec_ref(v___x_909_);
lean_dec_ref(v_arg_908_);
lean_dec_ref(v_arg_905_);
lean_dec_ref(v_arg_900_);
lean_dec_ref(v_arg_897_);
lean_dec_ref(v_e_880_);
goto v___jp_892_;
}
else
{
lean_object* v_arg_911_; lean_object* v___x_912_; lean_object* v___x_913_; uint8_t v___x_914_; 
v_arg_911_ = lean_ctor_get(v___x_909_, 1);
lean_inc_ref(v_arg_911_);
v___x_912_ = l_Lean_Expr_appFnCleanup___redArg(v___x_909_);
v___x_913_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_propagateMul___closed__2));
v___x_914_ = l_Lean_Expr_isConstOf(v___x_912_, v___x_913_);
if (v___x_914_ == 0)
{
lean_dec_ref(v___x_912_);
lean_dec_ref(v_arg_911_);
lean_dec_ref(v_arg_908_);
lean_dec_ref(v_arg_905_);
lean_dec_ref(v_arg_900_);
lean_dec_ref(v_arg_897_);
lean_dec_ref(v_e_880_);
goto v___jp_892_;
}
else
{
lean_object* v___x_915_; 
lean_inc_ref(v_arg_911_);
v___x_915_ = l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isUnsupportedSemiring_x3f(v_arg_911_, v_a_881_, v_a_882_, v_a_883_, v_a_884_, v_a_885_, v_a_886_, v_a_887_, v_a_888_, v_a_889_, v_a_890_);
if (lean_obj_tag(v___x_915_) == 0)
{
lean_object* v_a_916_; lean_object* v___x_918_; uint8_t v_isShared_919_; uint8_t v_isSharedCheck_1090_; 
v_a_916_ = lean_ctor_get(v___x_915_, 0);
v_isSharedCheck_1090_ = !lean_is_exclusive(v___x_915_);
if (v_isSharedCheck_1090_ == 0)
{
v___x_918_ = v___x_915_;
v_isShared_919_ = v_isSharedCheck_1090_;
goto v_resetjp_917_;
}
else
{
lean_inc(v_a_916_);
lean_dec(v___x_915_);
v___x_918_ = lean_box(0);
v_isShared_919_ = v_isSharedCheck_1090_;
goto v_resetjp_917_;
}
v_resetjp_917_:
{
if (lean_obj_tag(v_a_916_) == 1)
{
lean_object* v_val_920_; uint8_t v___y_922_; uint8_t v___x_1084_; 
v_val_920_ = lean_ctor_get(v_a_916_, 0);
lean_inc(v_val_920_);
lean_dec_ref(v_a_916_);
v___x_1084_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_arg_911_, v_arg_908_);
lean_dec_ref(v_arg_908_);
if (v___x_1084_ == 0)
{
lean_dec_ref(v_arg_905_);
v___y_922_ = v___x_1084_;
goto v___jp_921_;
}
else
{
uint8_t v___x_1085_; 
v___x_1085_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_arg_911_, v_arg_905_);
lean_dec_ref(v_arg_905_);
v___y_922_ = v___x_1085_;
goto v___jp_921_;
}
v___jp_921_:
{
if (v___y_922_ == 0)
{
lean_object* v___x_923_; lean_object* v___x_925_; 
lean_dec(v_val_920_);
lean_dec_ref(v___x_912_);
lean_dec_ref(v_arg_911_);
lean_dec_ref(v_arg_900_);
lean_dec_ref(v_arg_897_);
lean_dec_ref(v_e_880_);
v___x_923_ = lean_box(0);
if (v_isShared_919_ == 0)
{
lean_ctor_set(v___x_918_, 0, v___x_923_);
v___x_925_ = v___x_918_;
goto v_reusejp_924_;
}
else
{
lean_object* v_reuseFailAlloc_926_; 
v_reuseFailAlloc_926_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_926_, 0, v___x_923_);
v___x_925_ = v_reuseFailAlloc_926_;
goto v_reusejp_924_;
}
v_reusejp_924_:
{
return v___x_925_;
}
}
else
{
lean_object* v___x_927_; 
v___x_927_ = l_Lean_Expr_constLevels_x21(v___x_912_);
lean_dec_ref(v___x_912_);
if (lean_obj_tag(v___x_927_) == 1)
{
lean_object* v_head_928_; lean_object* v___x_930_; uint8_t v_isShared_931_; uint8_t v_isSharedCheck_1078_; 
lean_del_object(v___x_918_);
v_head_928_ = lean_ctor_get(v___x_927_, 0);
v_isSharedCheck_1078_ = !lean_is_exclusive(v___x_927_);
if (v_isSharedCheck_1078_ == 0)
{
lean_object* v_unused_1079_; 
v_unused_1079_ = lean_ctor_get(v___x_927_, 1);
lean_dec(v_unused_1079_);
v___x_930_ = v___x_927_;
v_isShared_931_ = v_isSharedCheck_1078_;
goto v_resetjp_929_;
}
else
{
lean_inc(v_head_928_);
lean_dec(v___x_927_);
v___x_930_ = lean_box(0);
v_isShared_931_ = v_isSharedCheck_1078_;
goto v_resetjp_929_;
}
v_resetjp_929_:
{
lean_object* v___x_932_; lean_object* v___x_933_; 
v___x_932_ = lean_st_ref_get(v_a_881_);
lean_inc_ref(v_arg_900_);
v___x_933_ = l_Lean_Meta_Grind_Goal_getRoot(v___x_932_, v_arg_900_, v_a_887_, v_a_888_, v_a_889_, v_a_890_);
if (lean_obj_tag(v___x_933_) == 0)
{
lean_object* v_a_934_; lean_object* v___x_935_; lean_object* v___x_936_; 
v_a_934_ = lean_ctor_get(v___x_933_, 0);
lean_inc(v_a_934_);
lean_dec_ref(v___x_933_);
v___x_935_ = lean_st_ref_get(v_a_881_);
lean_inc_ref(v_arg_897_);
v___x_936_ = l_Lean_Meta_Grind_Goal_getRoot(v___x_935_, v_arg_897_, v_a_887_, v_a_888_, v_a_889_, v_a_890_);
if (lean_obj_tag(v___x_936_) == 0)
{
lean_object* v_a_937_; lean_object* v___x_938_; 
v_a_937_ = lean_ctor_get(v___x_936_, 0);
lean_inc(v_a_937_);
lean_dec_ref(v___x_936_);
lean_inc(v_a_934_);
v___x_938_ = l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isOfNat_x3f(v_a_934_, v_a_887_, v_a_888_, v_a_889_, v_a_890_);
if (lean_obj_tag(v___x_938_) == 0)
{
lean_object* v_a_939_; lean_object* v___x_941_; uint8_t v_isShared_942_; uint8_t v_isSharedCheck_1053_; 
v_a_939_ = lean_ctor_get(v___x_938_, 0);
v_isSharedCheck_1053_ = !lean_is_exclusive(v___x_938_);
if (v_isSharedCheck_1053_ == 0)
{
v___x_941_ = v___x_938_;
v_isShared_942_ = v_isSharedCheck_1053_;
goto v_resetjp_940_;
}
else
{
lean_inc(v_a_939_);
lean_dec(v___x_938_);
v___x_941_ = lean_box(0);
v_isShared_942_ = v_isSharedCheck_1053_;
goto v_resetjp_940_;
}
v_resetjp_940_:
{
if (lean_obj_tag(v_a_939_) == 1)
{
lean_object* v_val_943_; lean_object* v___x_944_; uint8_t v___x_945_; 
lean_dec(v_a_937_);
v_val_943_ = lean_ctor_get(v_a_939_, 0);
lean_inc(v_val_943_);
lean_dec_ref(v_a_939_);
v___x_944_ = lean_unsigned_to_nat(0u);
v___x_945_ = lean_nat_dec_eq(v_val_943_, v___x_944_);
if (v___x_945_ == 0)
{
lean_object* v___x_946_; uint8_t v___x_947_; 
v___x_946_ = lean_unsigned_to_nat(1u);
v___x_947_ = lean_nat_dec_eq(v_val_943_, v___x_946_);
lean_dec(v_val_943_);
if (v___x_947_ == 0)
{
lean_object* v___x_948_; lean_object* v___x_950_; 
lean_dec(v_a_934_);
lean_del_object(v___x_930_);
lean_dec(v_head_928_);
lean_dec(v_val_920_);
lean_dec_ref(v_arg_911_);
lean_dec_ref(v_arg_900_);
lean_dec_ref(v_arg_897_);
lean_dec_ref(v_e_880_);
v___x_948_ = lean_box(0);
if (v_isShared_942_ == 0)
{
lean_ctor_set(v___x_941_, 0, v___x_948_);
v___x_950_ = v___x_941_;
goto v_reusejp_949_;
}
else
{
lean_object* v_reuseFailAlloc_951_; 
v_reuseFailAlloc_951_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_951_, 0, v___x_948_);
v___x_950_ = v_reuseFailAlloc_951_;
goto v_reusejp_949_;
}
v_reusejp_949_:
{
return v___x_950_;
}
}
else
{
lean_object* v___x_952_; 
lean_del_object(v___x_941_);
lean_inc(v_a_890_);
lean_inc_ref(v_a_889_);
lean_inc(v_a_888_);
lean_inc_ref(v_a_887_);
lean_inc(v_a_886_);
lean_inc_ref(v_a_885_);
lean_inc(v_a_884_);
lean_inc_ref(v_a_883_);
lean_inc(v_a_882_);
lean_inc(v_a_881_);
lean_inc_ref(v_arg_900_);
v___x_952_ = lean_grind_mk_eq_proof(v_arg_900_, v_a_934_, v_a_881_, v_a_882_, v_a_883_, v_a_884_, v_a_885_, v_a_886_, v_a_887_, v_a_888_, v_a_889_, v_a_890_);
if (lean_obj_tag(v___x_952_) == 0)
{
lean_object* v_a_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_957_; 
v_a_953_ = lean_ctor_get(v___x_952_, 0);
lean_inc(v_a_953_);
lean_dec_ref(v___x_952_);
v___x_954_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_propagateMul___closed__5));
v___x_955_ = lean_box(0);
if (v_isShared_931_ == 0)
{
lean_ctor_set(v___x_930_, 1, v___x_955_);
v___x_957_ = v___x_930_;
goto v_reusejp_956_;
}
else
{
lean_object* v_reuseFailAlloc_961_; 
v_reuseFailAlloc_961_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_961_, 0, v_head_928_);
lean_ctor_set(v_reuseFailAlloc_961_, 1, v___x_955_);
v___x_957_ = v_reuseFailAlloc_961_;
goto v_reusejp_956_;
}
v_reusejp_956_:
{
lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; 
v___x_958_ = l_Lean_mkConst(v___x_954_, v___x_957_);
lean_inc_ref(v_arg_897_);
v___x_959_ = l_Lean_mkApp5(v___x_958_, v_arg_911_, v_val_920_, v_arg_900_, v_arg_897_, v_a_953_);
v___x_960_ = l_Lean_Meta_Grind_pushEqCore___redArg(v_e_880_, v_arg_897_, v___x_959_, v___x_945_, v_a_881_, v_a_883_, v_a_887_, v_a_888_, v_a_889_, v_a_890_);
return v___x_960_;
}
}
else
{
lean_object* v_a_962_; lean_object* v___x_964_; uint8_t v_isShared_965_; uint8_t v_isSharedCheck_969_; 
lean_del_object(v___x_930_);
lean_dec(v_head_928_);
lean_dec(v_val_920_);
lean_dec_ref(v_arg_911_);
lean_dec_ref(v_arg_900_);
lean_dec_ref(v_arg_897_);
lean_dec_ref(v_e_880_);
v_a_962_ = lean_ctor_get(v___x_952_, 0);
v_isSharedCheck_969_ = !lean_is_exclusive(v___x_952_);
if (v_isSharedCheck_969_ == 0)
{
v___x_964_ = v___x_952_;
v_isShared_965_ = v_isSharedCheck_969_;
goto v_resetjp_963_;
}
else
{
lean_inc(v_a_962_);
lean_dec(v___x_952_);
v___x_964_ = lean_box(0);
v_isShared_965_ = v_isSharedCheck_969_;
goto v_resetjp_963_;
}
v_resetjp_963_:
{
lean_object* v___x_967_; 
if (v_isShared_965_ == 0)
{
v___x_967_ = v___x_964_;
goto v_reusejp_966_;
}
else
{
lean_object* v_reuseFailAlloc_968_; 
v_reuseFailAlloc_968_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_968_, 0, v_a_962_);
v___x_967_ = v_reuseFailAlloc_968_;
goto v_reusejp_966_;
}
v_reusejp_966_:
{
return v___x_967_;
}
}
}
}
}
else
{
lean_object* v___x_970_; 
lean_dec(v_val_943_);
lean_del_object(v___x_941_);
lean_inc(v_a_890_);
lean_inc_ref(v_a_889_);
lean_inc(v_a_888_);
lean_inc_ref(v_a_887_);
lean_inc(v_a_886_);
lean_inc_ref(v_a_885_);
lean_inc(v_a_884_);
lean_inc_ref(v_a_883_);
lean_inc(v_a_882_);
lean_inc(v_a_881_);
lean_inc(v_a_934_);
lean_inc_ref(v_arg_900_);
v___x_970_ = lean_grind_mk_eq_proof(v_arg_900_, v_a_934_, v_a_881_, v_a_882_, v_a_883_, v_a_884_, v_a_885_, v_a_886_, v_a_887_, v_a_888_, v_a_889_, v_a_890_);
if (lean_obj_tag(v___x_970_) == 0)
{
lean_object* v_a_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_975_; 
v_a_971_ = lean_ctor_get(v___x_970_, 0);
lean_inc(v_a_971_);
lean_dec_ref(v___x_970_);
v___x_972_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_propagateMul___closed__7));
v___x_973_ = lean_box(0);
if (v_isShared_931_ == 0)
{
lean_ctor_set(v___x_930_, 1, v___x_973_);
v___x_975_ = v___x_930_;
goto v_reusejp_974_;
}
else
{
lean_object* v_reuseFailAlloc_980_; 
v_reuseFailAlloc_980_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_980_, 0, v_head_928_);
lean_ctor_set(v_reuseFailAlloc_980_, 1, v___x_973_);
v___x_975_ = v_reuseFailAlloc_980_;
goto v_reusejp_974_;
}
v_reusejp_974_:
{
lean_object* v___x_976_; lean_object* v___x_977_; uint8_t v___x_978_; lean_object* v___x_979_; 
v___x_976_ = l_Lean_mkConst(v___x_972_, v___x_975_);
v___x_977_ = l_Lean_mkApp5(v___x_976_, v_arg_911_, v_val_920_, v_arg_900_, v_arg_897_, v_a_971_);
v___x_978_ = 0;
v___x_979_ = l_Lean_Meta_Grind_pushEqCore___redArg(v_e_880_, v_a_934_, v___x_977_, v___x_978_, v_a_881_, v_a_883_, v_a_887_, v_a_888_, v_a_889_, v_a_890_);
return v___x_979_;
}
}
else
{
lean_object* v_a_981_; lean_object* v___x_983_; uint8_t v_isShared_984_; uint8_t v_isSharedCheck_988_; 
lean_dec(v_a_934_);
lean_del_object(v___x_930_);
lean_dec(v_head_928_);
lean_dec(v_val_920_);
lean_dec_ref(v_arg_911_);
lean_dec_ref(v_arg_900_);
lean_dec_ref(v_arg_897_);
lean_dec_ref(v_e_880_);
v_a_981_ = lean_ctor_get(v___x_970_, 0);
v_isSharedCheck_988_ = !lean_is_exclusive(v___x_970_);
if (v_isSharedCheck_988_ == 0)
{
v___x_983_ = v___x_970_;
v_isShared_984_ = v_isSharedCheck_988_;
goto v_resetjp_982_;
}
else
{
lean_inc(v_a_981_);
lean_dec(v___x_970_);
v___x_983_ = lean_box(0);
v_isShared_984_ = v_isSharedCheck_988_;
goto v_resetjp_982_;
}
v_resetjp_982_:
{
lean_object* v___x_986_; 
if (v_isShared_984_ == 0)
{
v___x_986_ = v___x_983_;
goto v_reusejp_985_;
}
else
{
lean_object* v_reuseFailAlloc_987_; 
v_reuseFailAlloc_987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_987_, 0, v_a_981_);
v___x_986_ = v_reuseFailAlloc_987_;
goto v_reusejp_985_;
}
v_reusejp_985_:
{
return v___x_986_;
}
}
}
}
}
else
{
lean_object* v___x_989_; 
lean_del_object(v___x_941_);
lean_dec(v_a_939_);
lean_dec(v_a_934_);
lean_inc(v_a_937_);
v___x_989_ = l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isOfNat_x3f(v_a_937_, v_a_887_, v_a_888_, v_a_889_, v_a_890_);
if (lean_obj_tag(v___x_989_) == 0)
{
lean_object* v_a_990_; lean_object* v___x_992_; uint8_t v_isShared_993_; uint8_t v_isSharedCheck_1044_; 
v_a_990_ = lean_ctor_get(v___x_989_, 0);
v_isSharedCheck_1044_ = !lean_is_exclusive(v___x_989_);
if (v_isSharedCheck_1044_ == 0)
{
v___x_992_ = v___x_989_;
v_isShared_993_ = v_isSharedCheck_1044_;
goto v_resetjp_991_;
}
else
{
lean_inc(v_a_990_);
lean_dec(v___x_989_);
v___x_992_ = lean_box(0);
v_isShared_993_ = v_isSharedCheck_1044_;
goto v_resetjp_991_;
}
v_resetjp_991_:
{
if (lean_obj_tag(v_a_990_) == 1)
{
lean_object* v_val_994_; lean_object* v___x_995_; uint8_t v___x_996_; 
v_val_994_ = lean_ctor_get(v_a_990_, 0);
lean_inc(v_val_994_);
lean_dec_ref(v_a_990_);
v___x_995_ = lean_unsigned_to_nat(0u);
v___x_996_ = lean_nat_dec_eq(v_val_994_, v___x_995_);
if (v___x_996_ == 0)
{
lean_object* v___x_997_; uint8_t v___x_998_; 
v___x_997_ = lean_unsigned_to_nat(1u);
v___x_998_ = lean_nat_dec_eq(v_val_994_, v___x_997_);
lean_dec(v_val_994_);
if (v___x_998_ == 0)
{
lean_object* v___x_999_; lean_object* v___x_1001_; 
lean_dec(v_a_937_);
lean_del_object(v___x_930_);
lean_dec(v_head_928_);
lean_dec(v_val_920_);
lean_dec_ref(v_arg_911_);
lean_dec_ref(v_arg_900_);
lean_dec_ref(v_arg_897_);
lean_dec_ref(v_e_880_);
v___x_999_ = lean_box(0);
if (v_isShared_993_ == 0)
{
lean_ctor_set(v___x_992_, 0, v___x_999_);
v___x_1001_ = v___x_992_;
goto v_reusejp_1000_;
}
else
{
lean_object* v_reuseFailAlloc_1002_; 
v_reuseFailAlloc_1002_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1002_, 0, v___x_999_);
v___x_1001_ = v_reuseFailAlloc_1002_;
goto v_reusejp_1000_;
}
v_reusejp_1000_:
{
return v___x_1001_;
}
}
else
{
lean_object* v___x_1003_; 
lean_del_object(v___x_992_);
lean_inc(v_a_890_);
lean_inc_ref(v_a_889_);
lean_inc(v_a_888_);
lean_inc_ref(v_a_887_);
lean_inc(v_a_886_);
lean_inc_ref(v_a_885_);
lean_inc(v_a_884_);
lean_inc_ref(v_a_883_);
lean_inc(v_a_882_);
lean_inc(v_a_881_);
lean_inc_ref(v_arg_897_);
v___x_1003_ = lean_grind_mk_eq_proof(v_arg_897_, v_a_937_, v_a_881_, v_a_882_, v_a_883_, v_a_884_, v_a_885_, v_a_886_, v_a_887_, v_a_888_, v_a_889_, v_a_890_);
if (lean_obj_tag(v___x_1003_) == 0)
{
lean_object* v_a_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1008_; 
v_a_1004_ = lean_ctor_get(v___x_1003_, 0);
lean_inc(v_a_1004_);
lean_dec_ref(v___x_1003_);
v___x_1005_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_propagateMul___closed__9));
v___x_1006_ = lean_box(0);
if (v_isShared_931_ == 0)
{
lean_ctor_set(v___x_930_, 1, v___x_1006_);
v___x_1008_ = v___x_930_;
goto v_reusejp_1007_;
}
else
{
lean_object* v_reuseFailAlloc_1012_; 
v_reuseFailAlloc_1012_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1012_, 0, v_head_928_);
lean_ctor_set(v_reuseFailAlloc_1012_, 1, v___x_1006_);
v___x_1008_ = v_reuseFailAlloc_1012_;
goto v_reusejp_1007_;
}
v_reusejp_1007_:
{
lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; 
v___x_1009_ = l_Lean_mkConst(v___x_1005_, v___x_1008_);
lean_inc_ref(v_arg_900_);
v___x_1010_ = l_Lean_mkApp5(v___x_1009_, v_arg_911_, v_val_920_, v_arg_900_, v_arg_897_, v_a_1004_);
v___x_1011_ = l_Lean_Meta_Grind_pushEqCore___redArg(v_e_880_, v_arg_900_, v___x_1010_, v___x_996_, v_a_881_, v_a_883_, v_a_887_, v_a_888_, v_a_889_, v_a_890_);
return v___x_1011_;
}
}
else
{
lean_object* v_a_1013_; lean_object* v___x_1015_; uint8_t v_isShared_1016_; uint8_t v_isSharedCheck_1020_; 
lean_del_object(v___x_930_);
lean_dec(v_head_928_);
lean_dec(v_val_920_);
lean_dec_ref(v_arg_911_);
lean_dec_ref(v_arg_900_);
lean_dec_ref(v_arg_897_);
lean_dec_ref(v_e_880_);
v_a_1013_ = lean_ctor_get(v___x_1003_, 0);
v_isSharedCheck_1020_ = !lean_is_exclusive(v___x_1003_);
if (v_isSharedCheck_1020_ == 0)
{
v___x_1015_ = v___x_1003_;
v_isShared_1016_ = v_isSharedCheck_1020_;
goto v_resetjp_1014_;
}
else
{
lean_inc(v_a_1013_);
lean_dec(v___x_1003_);
v___x_1015_ = lean_box(0);
v_isShared_1016_ = v_isSharedCheck_1020_;
goto v_resetjp_1014_;
}
v_resetjp_1014_:
{
lean_object* v___x_1018_; 
if (v_isShared_1016_ == 0)
{
v___x_1018_ = v___x_1015_;
goto v_reusejp_1017_;
}
else
{
lean_object* v_reuseFailAlloc_1019_; 
v_reuseFailAlloc_1019_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1019_, 0, v_a_1013_);
v___x_1018_ = v_reuseFailAlloc_1019_;
goto v_reusejp_1017_;
}
v_reusejp_1017_:
{
return v___x_1018_;
}
}
}
}
}
else
{
lean_object* v___x_1021_; 
lean_dec(v_val_994_);
lean_del_object(v___x_992_);
lean_inc(v_a_890_);
lean_inc_ref(v_a_889_);
lean_inc(v_a_888_);
lean_inc_ref(v_a_887_);
lean_inc(v_a_886_);
lean_inc_ref(v_a_885_);
lean_inc(v_a_884_);
lean_inc_ref(v_a_883_);
lean_inc(v_a_882_);
lean_inc(v_a_881_);
lean_inc(v_a_937_);
lean_inc_ref(v_arg_897_);
v___x_1021_ = lean_grind_mk_eq_proof(v_arg_897_, v_a_937_, v_a_881_, v_a_882_, v_a_883_, v_a_884_, v_a_885_, v_a_886_, v_a_887_, v_a_888_, v_a_889_, v_a_890_);
if (lean_obj_tag(v___x_1021_) == 0)
{
lean_object* v_a_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1026_; 
v_a_1022_ = lean_ctor_get(v___x_1021_, 0);
lean_inc(v_a_1022_);
lean_dec_ref(v___x_1021_);
v___x_1023_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_propagateMul___closed__11));
v___x_1024_ = lean_box(0);
if (v_isShared_931_ == 0)
{
lean_ctor_set(v___x_930_, 1, v___x_1024_);
v___x_1026_ = v___x_930_;
goto v_reusejp_1025_;
}
else
{
lean_object* v_reuseFailAlloc_1031_; 
v_reuseFailAlloc_1031_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1031_, 0, v_head_928_);
lean_ctor_set(v_reuseFailAlloc_1031_, 1, v___x_1024_);
v___x_1026_ = v_reuseFailAlloc_1031_;
goto v_reusejp_1025_;
}
v_reusejp_1025_:
{
lean_object* v___x_1027_; lean_object* v___x_1028_; uint8_t v___x_1029_; lean_object* v___x_1030_; 
v___x_1027_ = l_Lean_mkConst(v___x_1023_, v___x_1026_);
v___x_1028_ = l_Lean_mkApp5(v___x_1027_, v_arg_911_, v_val_920_, v_arg_900_, v_arg_897_, v_a_1022_);
v___x_1029_ = 0;
v___x_1030_ = l_Lean_Meta_Grind_pushEqCore___redArg(v_e_880_, v_a_937_, v___x_1028_, v___x_1029_, v_a_881_, v_a_883_, v_a_887_, v_a_888_, v_a_889_, v_a_890_);
return v___x_1030_;
}
}
else
{
lean_object* v_a_1032_; lean_object* v___x_1034_; uint8_t v_isShared_1035_; uint8_t v_isSharedCheck_1039_; 
lean_dec(v_a_937_);
lean_del_object(v___x_930_);
lean_dec(v_head_928_);
lean_dec(v_val_920_);
lean_dec_ref(v_arg_911_);
lean_dec_ref(v_arg_900_);
lean_dec_ref(v_arg_897_);
lean_dec_ref(v_e_880_);
v_a_1032_ = lean_ctor_get(v___x_1021_, 0);
v_isSharedCheck_1039_ = !lean_is_exclusive(v___x_1021_);
if (v_isSharedCheck_1039_ == 0)
{
v___x_1034_ = v___x_1021_;
v_isShared_1035_ = v_isSharedCheck_1039_;
goto v_resetjp_1033_;
}
else
{
lean_inc(v_a_1032_);
lean_dec(v___x_1021_);
v___x_1034_ = lean_box(0);
v_isShared_1035_ = v_isSharedCheck_1039_;
goto v_resetjp_1033_;
}
v_resetjp_1033_:
{
lean_object* v___x_1037_; 
if (v_isShared_1035_ == 0)
{
v___x_1037_ = v___x_1034_;
goto v_reusejp_1036_;
}
else
{
lean_object* v_reuseFailAlloc_1038_; 
v_reuseFailAlloc_1038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1038_, 0, v_a_1032_);
v___x_1037_ = v_reuseFailAlloc_1038_;
goto v_reusejp_1036_;
}
v_reusejp_1036_:
{
return v___x_1037_;
}
}
}
}
}
else
{
lean_object* v___x_1040_; lean_object* v___x_1042_; 
lean_dec(v_a_990_);
lean_dec(v_a_937_);
lean_del_object(v___x_930_);
lean_dec(v_head_928_);
lean_dec(v_val_920_);
lean_dec_ref(v_arg_911_);
lean_dec_ref(v_arg_900_);
lean_dec_ref(v_arg_897_);
lean_dec_ref(v_e_880_);
v___x_1040_ = lean_box(0);
if (v_isShared_993_ == 0)
{
lean_ctor_set(v___x_992_, 0, v___x_1040_);
v___x_1042_ = v___x_992_;
goto v_reusejp_1041_;
}
else
{
lean_object* v_reuseFailAlloc_1043_; 
v_reuseFailAlloc_1043_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1043_, 0, v___x_1040_);
v___x_1042_ = v_reuseFailAlloc_1043_;
goto v_reusejp_1041_;
}
v_reusejp_1041_:
{
return v___x_1042_;
}
}
}
}
else
{
lean_object* v_a_1045_; lean_object* v___x_1047_; uint8_t v_isShared_1048_; uint8_t v_isSharedCheck_1052_; 
lean_dec(v_a_937_);
lean_del_object(v___x_930_);
lean_dec(v_head_928_);
lean_dec(v_val_920_);
lean_dec_ref(v_arg_911_);
lean_dec_ref(v_arg_900_);
lean_dec_ref(v_arg_897_);
lean_dec_ref(v_e_880_);
v_a_1045_ = lean_ctor_get(v___x_989_, 0);
v_isSharedCheck_1052_ = !lean_is_exclusive(v___x_989_);
if (v_isSharedCheck_1052_ == 0)
{
v___x_1047_ = v___x_989_;
v_isShared_1048_ = v_isSharedCheck_1052_;
goto v_resetjp_1046_;
}
else
{
lean_inc(v_a_1045_);
lean_dec(v___x_989_);
v___x_1047_ = lean_box(0);
v_isShared_1048_ = v_isSharedCheck_1052_;
goto v_resetjp_1046_;
}
v_resetjp_1046_:
{
lean_object* v___x_1050_; 
if (v_isShared_1048_ == 0)
{
v___x_1050_ = v___x_1047_;
goto v_reusejp_1049_;
}
else
{
lean_object* v_reuseFailAlloc_1051_; 
v_reuseFailAlloc_1051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1051_, 0, v_a_1045_);
v___x_1050_ = v_reuseFailAlloc_1051_;
goto v_reusejp_1049_;
}
v_reusejp_1049_:
{
return v___x_1050_;
}
}
}
}
}
}
else
{
lean_object* v_a_1054_; lean_object* v___x_1056_; uint8_t v_isShared_1057_; uint8_t v_isSharedCheck_1061_; 
lean_dec(v_a_937_);
lean_dec(v_a_934_);
lean_del_object(v___x_930_);
lean_dec(v_head_928_);
lean_dec(v_val_920_);
lean_dec_ref(v_arg_911_);
lean_dec_ref(v_arg_900_);
lean_dec_ref(v_arg_897_);
lean_dec_ref(v_e_880_);
v_a_1054_ = lean_ctor_get(v___x_938_, 0);
v_isSharedCheck_1061_ = !lean_is_exclusive(v___x_938_);
if (v_isSharedCheck_1061_ == 0)
{
v___x_1056_ = v___x_938_;
v_isShared_1057_ = v_isSharedCheck_1061_;
goto v_resetjp_1055_;
}
else
{
lean_inc(v_a_1054_);
lean_dec(v___x_938_);
v___x_1056_ = lean_box(0);
v_isShared_1057_ = v_isSharedCheck_1061_;
goto v_resetjp_1055_;
}
v_resetjp_1055_:
{
lean_object* v___x_1059_; 
if (v_isShared_1057_ == 0)
{
v___x_1059_ = v___x_1056_;
goto v_reusejp_1058_;
}
else
{
lean_object* v_reuseFailAlloc_1060_; 
v_reuseFailAlloc_1060_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1060_, 0, v_a_1054_);
v___x_1059_ = v_reuseFailAlloc_1060_;
goto v_reusejp_1058_;
}
v_reusejp_1058_:
{
return v___x_1059_;
}
}
}
}
else
{
lean_object* v_a_1062_; lean_object* v___x_1064_; uint8_t v_isShared_1065_; uint8_t v_isSharedCheck_1069_; 
lean_dec(v_a_934_);
lean_del_object(v___x_930_);
lean_dec(v_head_928_);
lean_dec(v_val_920_);
lean_dec_ref(v_arg_911_);
lean_dec_ref(v_arg_900_);
lean_dec_ref(v_arg_897_);
lean_dec_ref(v_e_880_);
v_a_1062_ = lean_ctor_get(v___x_936_, 0);
v_isSharedCheck_1069_ = !lean_is_exclusive(v___x_936_);
if (v_isSharedCheck_1069_ == 0)
{
v___x_1064_ = v___x_936_;
v_isShared_1065_ = v_isSharedCheck_1069_;
goto v_resetjp_1063_;
}
else
{
lean_inc(v_a_1062_);
lean_dec(v___x_936_);
v___x_1064_ = lean_box(0);
v_isShared_1065_ = v_isSharedCheck_1069_;
goto v_resetjp_1063_;
}
v_resetjp_1063_:
{
lean_object* v___x_1067_; 
if (v_isShared_1065_ == 0)
{
v___x_1067_ = v___x_1064_;
goto v_reusejp_1066_;
}
else
{
lean_object* v_reuseFailAlloc_1068_; 
v_reuseFailAlloc_1068_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1068_, 0, v_a_1062_);
v___x_1067_ = v_reuseFailAlloc_1068_;
goto v_reusejp_1066_;
}
v_reusejp_1066_:
{
return v___x_1067_;
}
}
}
}
else
{
lean_object* v_a_1070_; lean_object* v___x_1072_; uint8_t v_isShared_1073_; uint8_t v_isSharedCheck_1077_; 
lean_del_object(v___x_930_);
lean_dec(v_head_928_);
lean_dec(v_val_920_);
lean_dec_ref(v_arg_911_);
lean_dec_ref(v_arg_900_);
lean_dec_ref(v_arg_897_);
lean_dec_ref(v_e_880_);
v_a_1070_ = lean_ctor_get(v___x_933_, 0);
v_isSharedCheck_1077_ = !lean_is_exclusive(v___x_933_);
if (v_isSharedCheck_1077_ == 0)
{
v___x_1072_ = v___x_933_;
v_isShared_1073_ = v_isSharedCheck_1077_;
goto v_resetjp_1071_;
}
else
{
lean_inc(v_a_1070_);
lean_dec(v___x_933_);
v___x_1072_ = lean_box(0);
v_isShared_1073_ = v_isSharedCheck_1077_;
goto v_resetjp_1071_;
}
v_resetjp_1071_:
{
lean_object* v___x_1075_; 
if (v_isShared_1073_ == 0)
{
v___x_1075_ = v___x_1072_;
goto v_reusejp_1074_;
}
else
{
lean_object* v_reuseFailAlloc_1076_; 
v_reuseFailAlloc_1076_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1076_, 0, v_a_1070_);
v___x_1075_ = v_reuseFailAlloc_1076_;
goto v_reusejp_1074_;
}
v_reusejp_1074_:
{
return v___x_1075_;
}
}
}
}
}
else
{
lean_object* v___x_1080_; lean_object* v___x_1082_; 
lean_dec(v___x_927_);
lean_dec(v_val_920_);
lean_dec_ref(v_arg_911_);
lean_dec_ref(v_arg_900_);
lean_dec_ref(v_arg_897_);
lean_dec_ref(v_e_880_);
v___x_1080_ = lean_box(0);
if (v_isShared_919_ == 0)
{
lean_ctor_set(v___x_918_, 0, v___x_1080_);
v___x_1082_ = v___x_918_;
goto v_reusejp_1081_;
}
else
{
lean_object* v_reuseFailAlloc_1083_; 
v_reuseFailAlloc_1083_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1083_, 0, v___x_1080_);
v___x_1082_ = v_reuseFailAlloc_1083_;
goto v_reusejp_1081_;
}
v_reusejp_1081_:
{
return v___x_1082_;
}
}
}
}
}
else
{
lean_object* v___x_1086_; lean_object* v___x_1088_; 
lean_dec(v_a_916_);
lean_dec_ref(v___x_912_);
lean_dec_ref(v_arg_911_);
lean_dec_ref(v_arg_908_);
lean_dec_ref(v_arg_905_);
lean_dec_ref(v_arg_900_);
lean_dec_ref(v_arg_897_);
lean_dec_ref(v_e_880_);
v___x_1086_ = lean_box(0);
if (v_isShared_919_ == 0)
{
lean_ctor_set(v___x_918_, 0, v___x_1086_);
v___x_1088_ = v___x_918_;
goto v_reusejp_1087_;
}
else
{
lean_object* v_reuseFailAlloc_1089_; 
v_reuseFailAlloc_1089_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1089_, 0, v___x_1086_);
v___x_1088_ = v_reuseFailAlloc_1089_;
goto v_reusejp_1087_;
}
v_reusejp_1087_:
{
return v___x_1088_;
}
}
}
}
else
{
lean_object* v_a_1091_; lean_object* v___x_1093_; uint8_t v_isShared_1094_; uint8_t v_isSharedCheck_1098_; 
lean_dec_ref(v___x_912_);
lean_dec_ref(v_arg_911_);
lean_dec_ref(v_arg_908_);
lean_dec_ref(v_arg_905_);
lean_dec_ref(v_arg_900_);
lean_dec_ref(v_arg_897_);
lean_dec_ref(v_e_880_);
v_a_1091_ = lean_ctor_get(v___x_915_, 0);
v_isSharedCheck_1098_ = !lean_is_exclusive(v___x_915_);
if (v_isSharedCheck_1098_ == 0)
{
v___x_1093_ = v___x_915_;
v_isShared_1094_ = v_isSharedCheck_1098_;
goto v_resetjp_1092_;
}
else
{
lean_inc(v_a_1091_);
lean_dec(v___x_915_);
v___x_1093_ = lean_box(0);
v_isShared_1094_ = v_isSharedCheck_1098_;
goto v_resetjp_1092_;
}
v_resetjp_1092_:
{
lean_object* v___x_1096_; 
if (v_isShared_1094_ == 0)
{
v___x_1096_ = v___x_1093_;
goto v_reusejp_1095_;
}
else
{
lean_object* v_reuseFailAlloc_1097_; 
v_reuseFailAlloc_1097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1097_, 0, v_a_1091_);
v___x_1096_ = v_reuseFailAlloc_1097_;
goto v_reusejp_1095_;
}
v_reusejp_1095_:
{
return v___x_1096_;
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
v___jp_892_:
{
lean_object* v___x_893_; lean_object* v___x_894_; 
v___x_893_ = lean_box(0);
v___x_894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_894_, 0, v___x_893_);
return v___x_894_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_propagateMul___boxed(lean_object* v_e_1099_, lean_object* v_a_1100_, lean_object* v_a_1101_, lean_object* v_a_1102_, lean_object* v_a_1103_, lean_object* v_a_1104_, lean_object* v_a_1105_, lean_object* v_a_1106_, lean_object* v_a_1107_, lean_object* v_a_1108_, lean_object* v_a_1109_, lean_object* v_a_1110_){
_start:
{
lean_object* v_res_1111_; 
v_res_1111_ = l_Lean_Meta_Grind_Arith_propagateMul(v_e_1099_, v_a_1100_, v_a_1101_, v_a_1102_, v_a_1103_, v_a_1104_, v_a_1105_, v_a_1106_, v_a_1107_, v_a_1108_, v_a_1109_);
lean_dec(v_a_1109_);
lean_dec_ref(v_a_1108_);
lean_dec(v_a_1107_);
lean_dec_ref(v_a_1106_);
lean_dec(v_a_1105_);
lean_dec_ref(v_a_1104_);
lean_dec(v_a_1103_);
lean_dec_ref(v_a_1102_);
lean_dec(v_a_1101_);
lean_dec(v_a_1100_);
return v_res_1111_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_propagateMul___regBuiltin_Lean_Meta_Grind_Arith_propagateMul_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_3131998065____hygCtx___hyg_8_(){
_start:
{
lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; 
v___x_1113_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_propagateMul___closed__2));
v___x_1114_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_propagateMul___boxed), 12, 0);
v___x_1115_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_1113_, v___x_1114_);
return v___x_1115_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_propagateMul___regBuiltin_Lean_Meta_Grind_Arith_propagateMul_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_3131998065____hygCtx___hyg_8____boxed(lean_object* v_a_1116_){
_start:
{
lean_object* v_res_1117_; 
v_res_1117_ = l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_propagateMul___regBuiltin_Lean_Meta_Grind_Arith_propagateMul_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_3131998065____hygCtx___hyg_8_();
return v_res_1117_;
}
}
lean_object* runtime_initialize_Init_Grind(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_NonCommRingM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_NonCommSemiringM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_PropagatorAttr(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Propagate(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Grind(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_NonCommRingM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_NonCommSemiringM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_PropagatorAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_propagateNatAnd___regBuiltin_Lean_Meta_Grind_Arith_propagateNatAnd_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_1291761156____hygCtx___hyg_8_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_propagateNatOr___regBuiltin_Lean_Meta_Grind_Arith_propagateNatOr_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_2834229635____hygCtx___hyg_8_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_propagateNatXOr___regBuiltin_Lean_Meta_Grind_Arith_propagateNatXOr_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_3633575148____hygCtx___hyg_8_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_propagateNatShiftLeft___regBuiltin_Lean_Meta_Grind_Arith_propagateNatShiftLeft_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_3253038636____hygCtx___hyg_8_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_propagateNatShiftRight___regBuiltin_Lean_Meta_Grind_Arith_propagateNatShiftRight_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_1805815810____hygCtx___hyg_8_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring);
res = l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_propagateMul___regBuiltin_Lean_Meta_Grind_Arith_propagateMul_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_3131998065____hygCtx___hyg_8_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_Arith_Propagate(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Grind(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_NonCommRingM(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_NonCommSemiringM(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_PropagatorAttr(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Propagate(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Grind(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_NonCommRingM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_NonCommSemiringM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_PropagatorAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Propagate(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_Arith_Propagate(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_Arith_Propagate(builtin);
}
#ifdef __cplusplus
}
#endif
