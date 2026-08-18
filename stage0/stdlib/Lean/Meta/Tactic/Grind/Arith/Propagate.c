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
lean_object* l_Nat_land___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Nat_lor___boxed(lean_object*, lean_object*);
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
lean_object* l_Lean_Meta_Sym_shareCommon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_grind_internalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_grind_mk_eq_proof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
extern lean_object* l_Lean_eagerReflBoolTrue;
lean_object* l_Lean_mkApp8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_pushEqCore___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(lean_object*, lean_object*);
lean_object* l_Nat_shiftRight___boxed(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_noption_is_some(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_noption_get(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
lean_object* l_Nat_shiftLeft___boxed(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Raw_setEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNonCommRingId_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiring(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_constLevels_x21(lean_object*);
lean_object* l_Lean_mkApp5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_propagateNatAnd___regBuiltin_Lean_Meta_Grind_Arith_propagateNatAnd_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_1291761156____hygCtx___hyg_9_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_propagateNatAnd___regBuiltin_Lean_Meta_Grind_Arith_propagateNatAnd_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_1291761156____hygCtx___hyg_9____boxed(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_propagateNatOr___regBuiltin_Lean_Meta_Grind_Arith_propagateNatOr_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_2834229635____hygCtx___hyg_9_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_propagateNatOr___regBuiltin_Lean_Meta_Grind_Arith_propagateNatOr_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_2834229635____hygCtx___hyg_9____boxed(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_propagateNatXOr___regBuiltin_Lean_Meta_Grind_Arith_propagateNatXOr_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_3633575148____hygCtx___hyg_9_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_propagateNatXOr___regBuiltin_Lean_Meta_Grind_Arith_propagateNatXOr_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_3633575148____hygCtx___hyg_9____boxed(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_propagateNatShiftLeft___regBuiltin_Lean_Meta_Grind_Arith_propagateNatShiftLeft_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_3253038636____hygCtx___hyg_9_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_propagateNatShiftLeft___regBuiltin_Lean_Meta_Grind_Arith_propagateNatShiftLeft_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_3253038636____hygCtx___hyg_9____boxed(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_propagateNatShiftRight___regBuiltin_Lean_Meta_Grind_Arith_propagateNatShiftRight_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_1805815810____hygCtx___hyg_9_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_propagateNatShiftRight___regBuiltin_Lean_Meta_Grind_Arith_propagateNatShiftRight_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_1805815810____hygCtx___hyg_9____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__1_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__1___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__2(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__0;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__1;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__2;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Int"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__3_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__3_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__4_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Rat"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__5_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__5_value),LEAN_SCALAR_PTR_LITERAL(231, 55, 105, 214, 206, 30, 120, 51)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__6_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "BitVec"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__7_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__7_value),LEAN_SCALAR_PTR_LITERAL(108, 178, 58, 132, 143, 189, 222, 74)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__8_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "UInt8"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__9_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__9_value),LEAN_SCALAR_PTR_LITERAL(144, 254, 64, 72, 7, 99, 197, 218)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__10 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__10_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "UInt16"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__11 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__11_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__11_value),LEAN_SCALAR_PTR_LITERAL(6, 214, 154, 233, 192, 74, 99, 135)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__12 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__12_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "UInt32"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__13 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__13_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__13_value),LEAN_SCALAR_PTR_LITERAL(98, 192, 58, 241, 186, 14, 255, 186)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__14 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__14_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Int64"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__15 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__15_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__15_value),LEAN_SCALAR_PTR_LITERAL(67, 100, 38, 50, 157, 43, 83, 90)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__16 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__16_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Int8"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__17 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__17_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__17_value),LEAN_SCALAR_PTR_LITERAL(17, 171, 155, 218, 43, 77, 1, 67)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__18 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__18_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Int16"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__19 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__19_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__19_value),LEAN_SCALAR_PTR_LITERAL(61, 121, 89, 120, 57, 100, 28, 22)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__20 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__20_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Int32"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__21 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__21_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__21_value),LEAN_SCALAR_PTR_LITERAL(202, 24, 245, 188, 10, 96, 206, 241)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__22 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__22_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__16_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__23 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__23_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__22_value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__23_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__24 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__24_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__20_value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__24_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__25 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__25_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__18_value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__25_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__26 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__26_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__16_value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__26_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__27 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__27_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__14_value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__27_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__28 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__28_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__12_value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__28_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__29 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__29_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__10_value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__29_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__30 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__30_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__8_value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__30_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__31 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__31_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__6_value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__31_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__32 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__32_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__4_value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__32_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__33 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__33_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_propagateNatBinOp___closed__1_value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__33_value)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__34 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__34_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__35_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__35;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__1_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isSupportedSemiringQuick_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isSupportedSemiringQuick_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isSupportedSemiringQuick_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isSupportedSemiringQuick_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isSupportedSemiringQuick(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isSupportedSemiringQuick___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isSupportedSemiringQuick_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isSupportedSemiringQuick_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isSupportedSemiringQuick_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isSupportedSemiringQuick_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_propagateMul___regBuiltin_Lean_Meta_Grind_Arith_propagateMul_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_3131998065____hygCtx___hyg_9_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_propagateMul___regBuiltin_Lean_Meta_Grind_Arith_propagateMul_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_3131998065____hygCtx___hyg_9____boxed(lean_object*);
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
lean_dec(v___x_36_);
if (lean_obj_tag(v___x_38_) == 0)
{
lean_object* v_a_39_; lean_object* v___x_40_; 
v_a_39_ = lean_ctor_get(v___x_38_, 0);
lean_inc(v_a_39_);
lean_dec_ref_known(v___x_38_, 1);
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
lean_dec_ref_known(v_a_41_, 1);
v___x_46_ = lean_st_ref_get(v_a_8_);
v___x_47_ = lean_unsigned_to_nat(0u);
v___x_48_ = l_Lean_Expr_getRevArg_x21(v_e_7_, v___x_47_);
lean_inc_ref(v___x_48_);
v___x_49_ = l_Lean_Meta_Grind_Goal_getRoot(v___x_46_, v___x_48_, v_a_14_, v_a_15_, v_a_16_, v_a_17_);
lean_dec(v___x_46_);
if (lean_obj_tag(v___x_49_) == 0)
{
lean_object* v_a_50_; lean_object* v___x_51_; 
v_a_50_ = lean_ctor_get(v___x_49_, 0);
lean_inc(v_a_50_);
lean_dec_ref_known(v___x_49_, 1);
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
lean_dec_ref_known(v_a_52_, 1);
v___x_57_ = lean_apply_2(v_op_6_, v_val_45_, v_val_56_);
v___x_58_ = l_Lean_mkNatLit(v___x_57_);
v___x_59_ = l_Lean_Meta_Sym_shareCommon(v___x_58_, v_a_12_, v_a_13_, v_a_14_, v_a_15_, v_a_16_, v_a_17_);
if (lean_obj_tag(v___x_59_) == 0)
{
lean_object* v_a_60_; lean_object* v___x_61_; lean_object* v___x_62_; 
v_a_60_ = lean_ctor_get(v___x_59_, 0);
lean_inc_n(v_a_60_, 2);
lean_dec_ref_known(v___x_59_, 1);
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
lean_dec_ref_known(v___x_62_, 1);
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
lean_dec_ref_known(v___x_63_, 1);
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
lean_dec_ref_known(v___x_65_, 1);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_propagateNatAnd___regBuiltin_Lean_Meta_Grind_Arith_propagateNatAnd_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_1291761156____hygCtx___hyg_9_(){
_start:
{
lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; 
v___x_199_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__3));
v___x_200_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_propagateNatAnd___boxed), 12, 0);
v___x_201_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_199_, v___x_200_);
return v___x_201_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_propagateNatAnd___regBuiltin_Lean_Meta_Grind_Arith_propagateNatAnd_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_1291761156____hygCtx___hyg_9____boxed(lean_object* v_a_202_){
_start:
{
lean_object* v_res_203_; 
v_res_203_ = l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_propagateNatAnd___regBuiltin_Lean_Meta_Grind_Arith_propagateNatAnd_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_1291761156____hygCtx___hyg_9_();
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_propagateNatOr___regBuiltin_Lean_Meta_Grind_Arith_propagateNatOr_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_2834229635____hygCtx___hyg_9_(){
_start:
{
lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; 
v___x_246_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_propagateNatOr___closed__3));
v___x_247_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_propagateNatOr___boxed), 12, 0);
v___x_248_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_246_, v___x_247_);
return v___x_248_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_propagateNatOr___regBuiltin_Lean_Meta_Grind_Arith_propagateNatOr_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_2834229635____hygCtx___hyg_9____boxed(lean_object* v_a_249_){
_start:
{
lean_object* v_res_250_; 
v_res_250_ = l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_propagateNatOr___regBuiltin_Lean_Meta_Grind_Arith_propagateNatOr_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_2834229635____hygCtx___hyg_9_();
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_propagateNatXOr___regBuiltin_Lean_Meta_Grind_Arith_propagateNatXOr_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_3633575148____hygCtx___hyg_9_(){
_start:
{
lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; 
v___x_293_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_propagateNatXOr___closed__3));
v___x_294_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_propagateNatXOr___boxed), 12, 0);
v___x_295_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_293_, v___x_294_);
return v___x_295_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_propagateNatXOr___regBuiltin_Lean_Meta_Grind_Arith_propagateNatXOr_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_3633575148____hygCtx___hyg_9____boxed(lean_object* v_a_296_){
_start:
{
lean_object* v_res_297_; 
v_res_297_ = l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_propagateNatXOr___regBuiltin_Lean_Meta_Grind_Arith_propagateNatXOr_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_3633575148____hygCtx___hyg_9_();
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_propagateNatShiftLeft___regBuiltin_Lean_Meta_Grind_Arith_propagateNatShiftLeft_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_3253038636____hygCtx___hyg_9_(){
_start:
{
lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; 
v___x_340_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_propagateNatShiftLeft___closed__3));
v___x_341_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_propagateNatShiftLeft___boxed), 12, 0);
v___x_342_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_340_, v___x_341_);
return v___x_342_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_propagateNatShiftLeft___regBuiltin_Lean_Meta_Grind_Arith_propagateNatShiftLeft_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_3253038636____hygCtx___hyg_9____boxed(lean_object* v_a_343_){
_start:
{
lean_object* v_res_344_; 
v_res_344_ = l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_propagateNatShiftLeft___regBuiltin_Lean_Meta_Grind_Arith_propagateNatShiftLeft_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_3253038636____hygCtx___hyg_9_();
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_propagateNatShiftRight___regBuiltin_Lean_Meta_Grind_Arith_propagateNatShiftRight_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_1805815810____hygCtx___hyg_9_(){
_start:
{
lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; 
v___x_387_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_propagateNatShiftRight___closed__3));
v___x_388_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_propagateNatShiftRight___boxed), 12, 0);
v___x_389_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_387_, v___x_388_);
return v___x_389_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_propagateNatShiftRight___regBuiltin_Lean_Meta_Grind_Arith_propagateNatShiftRight_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_1805815810____hygCtx___hyg_9____boxed(lean_object* v_a_390_){
_start:
{
lean_object* v_res_391_; 
v_res_391_ = l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_propagateNatShiftRight___regBuiltin_Lean_Meta_Grind_Arith_propagateNatShiftRight_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_1805815810____hygCtx___hyg_9_();
return v_res_391_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__0___redArg(lean_object* v_m_392_, lean_object* v_query_393_, lean_object* v_x_394_, lean_object* v_x_395_, lean_object* v_x_396_){
_start:
{
lean_object* v_zero_397_; uint8_t v_isZero_398_; 
v_zero_397_ = lean_unsigned_to_nat(0u);
v_isZero_398_ = lean_nat_dec_eq(v_x_395_, v_zero_397_);
if (v_isZero_398_ == 1)
{
lean_dec(v_x_396_);
lean_dec(v_x_395_);
if (lean_obj_tag(v_x_394_) == 0)
{
lean_object* v___x_399_; 
v___x_399_ = lean_box(2);
return v___x_399_;
}
else
{
lean_object* v_val_400_; lean_object* v___x_402_; uint8_t v_isShared_403_; uint8_t v_isSharedCheck_407_; 
v_val_400_ = lean_ctor_get(v_x_394_, 0);
v_isSharedCheck_407_ = !lean_is_exclusive(v_x_394_);
if (v_isSharedCheck_407_ == 0)
{
v___x_402_ = v_x_394_;
v_isShared_403_ = v_isSharedCheck_407_;
goto v_resetjp_401_;
}
else
{
lean_inc(v_val_400_);
lean_dec(v_x_394_);
v___x_402_ = lean_box(0);
v_isShared_403_ = v_isSharedCheck_407_;
goto v_resetjp_401_;
}
v_resetjp_401_:
{
lean_object* v___x_405_; 
if (v_isShared_403_ == 0)
{
v___x_405_ = v___x_402_;
goto v_reusejp_404_;
}
else
{
lean_object* v_reuseFailAlloc_406_; 
v_reuseFailAlloc_406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_406_, 0, v_val_400_);
v___x_405_ = v_reuseFailAlloc_406_;
goto v_reusejp_404_;
}
v_reusejp_404_:
{
return v___x_405_;
}
}
}
}
else
{
lean_object* v_keyArray_408_; lean_object* v_valueArray_409_; lean_object* v___x_410_; uint8_t v_isSome_411_; 
v_keyArray_408_ = lean_ctor_get(v_m_392_, 1);
v_valueArray_409_ = lean_ctor_get(v_m_392_, 2);
v___x_410_ = lean_array_fget_borrowed(v_keyArray_408_, v_x_396_);
v_isSome_411_ = lean_noption_is_some(v___x_410_);
if (v_isSome_411_ == 0)
{
lean_dec(v_x_395_);
if (lean_obj_tag(v_x_394_) == 0)
{
lean_object* v___x_412_; 
v___x_412_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_412_, 0, v_x_396_);
return v___x_412_;
}
else
{
lean_object* v_val_413_; lean_object* v___x_415_; uint8_t v_isShared_416_; uint8_t v_isSharedCheck_420_; 
lean_dec(v_x_396_);
v_val_413_ = lean_ctor_get(v_x_394_, 0);
v_isSharedCheck_420_ = !lean_is_exclusive(v_x_394_);
if (v_isSharedCheck_420_ == 0)
{
v___x_415_ = v_x_394_;
v_isShared_416_ = v_isSharedCheck_420_;
goto v_resetjp_414_;
}
else
{
lean_inc(v_val_413_);
lean_dec(v_x_394_);
v___x_415_ = lean_box(0);
v_isShared_416_ = v_isSharedCheck_420_;
goto v_resetjp_414_;
}
v_resetjp_414_:
{
lean_object* v___x_418_; 
if (v_isShared_416_ == 0)
{
v___x_418_ = v___x_415_;
goto v_reusejp_417_;
}
else
{
lean_object* v_reuseFailAlloc_419_; 
v_reuseFailAlloc_419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_419_, 0, v_val_413_);
v___x_418_ = v_reuseFailAlloc_419_;
goto v_reusejp_417_;
}
v_reusejp_417_:
{
return v___x_418_;
}
}
}
}
else
{
lean_object* v_one_421_; lean_object* v_n_422_; lean_object* v___y_424_; 
v_one_421_ = lean_unsigned_to_nat(1u);
v_n_422_ = lean_nat_sub(v_x_395_, v_one_421_);
lean_dec(v_x_395_);
if (v_isSome_411_ == 0)
{
goto v___jp_430_;
}
else
{
lean_object* v___x_432_; uint8_t v_isSome_433_; 
v___x_432_ = lean_array_fget_borrowed(v_valueArray_409_, v_x_396_);
v_isSome_433_ = lean_noption_is_some(v___x_432_);
if (v_isSome_433_ == 0)
{
goto v___jp_430_;
}
else
{
lean_object* v_val_434_; uint8_t v___x_435_; 
lean_inc(v___x_410_);
v_val_434_ = lean_noption_get(v___x_410_);
v___x_435_ = lean_name_eq(v_val_434_, v_query_393_);
if (v___x_435_ == 0)
{
lean_object* v___x_436_; lean_object* v___x_437_; uint8_t v___x_438_; 
lean_dec(v_val_434_);
v___x_436_ = lean_array_get_size(v_keyArray_408_);
v___x_437_ = lean_nat_add(v_x_396_, v_one_421_);
lean_dec(v_x_396_);
v___x_438_ = lean_nat_dec_lt(v___x_437_, v___x_436_);
if (v___x_438_ == 0)
{
lean_dec(v___x_437_);
v_x_395_ = v_n_422_;
v_x_396_ = v_zero_397_;
goto _start;
}
else
{
v_x_395_ = v_n_422_;
v_x_396_ = v___x_437_;
goto _start;
}
}
else
{
lean_object* v_val_441_; lean_object* v___x_442_; 
lean_dec(v_n_422_);
lean_dec(v_x_394_);
lean_inc(v___x_432_);
v_val_441_ = lean_noption_get(v___x_432_);
v___x_442_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_442_, 0, v_x_396_);
lean_ctor_set(v___x_442_, 1, v_val_434_);
lean_ctor_set(v___x_442_, 2, v_val_441_);
return v___x_442_;
}
}
}
v___jp_423_:
{
lean_object* v___x_425_; lean_object* v___x_426_; uint8_t v___x_427_; 
v___x_425_ = lean_array_get_size(v_keyArray_408_);
v___x_426_ = lean_nat_add(v_x_396_, v_one_421_);
lean_dec(v_x_396_);
v___x_427_ = lean_nat_dec_lt(v___x_426_, v___x_425_);
if (v___x_427_ == 0)
{
lean_dec(v___x_426_);
v_x_394_ = v___y_424_;
v_x_395_ = v_n_422_;
v_x_396_ = v_zero_397_;
goto _start;
}
else
{
v_x_394_ = v___y_424_;
v_x_395_ = v_n_422_;
v_x_396_ = v___x_426_;
goto _start;
}
}
v___jp_430_:
{
if (lean_obj_tag(v_x_394_) == 0)
{
lean_object* v___x_431_; 
lean_inc(v_x_396_);
v___x_431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_431_, 0, v_x_396_);
v___y_424_ = v___x_431_;
goto v___jp_423_;
}
else
{
v___y_424_ = v_x_394_;
goto v___jp_423_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__0___redArg___boxed(lean_object* v_m_443_, lean_object* v_query_444_, lean_object* v_x_445_, lean_object* v_x_446_, lean_object* v_x_447_){
_start:
{
lean_object* v_res_448_; 
v_res_448_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__0___redArg(v_m_443_, v_query_444_, v_x_445_, v_x_446_, v_x_447_);
lean_dec(v_query_444_);
lean_dec_ref(v_m_443_);
return v_res_448_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0___redArg(lean_object* v_m_449_, lean_object* v_query_450_){
_start:
{
lean_object* v_keyArray_451_; lean_object* v___x_452_; uint64_t v___y_454_; 
v_keyArray_451_ = lean_ctor_get(v_m_449_, 1);
v___x_452_ = lean_array_get_size(v_keyArray_451_);
if (lean_obj_tag(v_query_450_) == 0)
{
uint64_t v___x_469_; 
v___x_469_ = 1723ULL;
v___y_454_ = v___x_469_;
goto v___jp_453_;
}
else
{
uint64_t v_hash_470_; 
v_hash_470_ = lean_ctor_get_uint64(v_query_450_, sizeof(void*)*2);
v___y_454_ = v_hash_470_;
goto v___jp_453_;
}
v___jp_453_:
{
uint64_t v___x_455_; uint64_t v___x_456_; uint64_t v_fold_457_; uint64_t v___x_458_; uint64_t v___x_459_; uint64_t v___x_460_; size_t v___x_461_; size_t v___x_462_; size_t v___x_463_; size_t v___x_464_; size_t v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; 
v___x_455_ = 32ULL;
v___x_456_ = lean_uint64_shift_right(v___y_454_, v___x_455_);
v_fold_457_ = lean_uint64_xor(v___y_454_, v___x_456_);
v___x_458_ = 16ULL;
v___x_459_ = lean_uint64_shift_right(v_fold_457_, v___x_458_);
v___x_460_ = lean_uint64_xor(v_fold_457_, v___x_459_);
v___x_461_ = lean_uint64_to_usize(v___x_460_);
v___x_462_ = lean_usize_of_nat(v___x_452_);
v___x_463_ = ((size_t)1ULL);
v___x_464_ = lean_usize_sub(v___x_462_, v___x_463_);
v___x_465_ = lean_usize_land(v___x_461_, v___x_464_);
v___x_466_ = lean_usize_to_nat(v___x_465_);
v___x_467_ = lean_box(0);
v___x_468_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__0___redArg(v_m_449_, v_query_450_, v___x_467_, v___x_452_, v___x_466_);
return v___x_468_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0___redArg___boxed(lean_object* v_m_471_, lean_object* v_query_472_){
_start:
{
lean_object* v_res_473_; 
v_res_473_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0___redArg(v_m_471_, v_query_472_);
lean_dec(v_query_472_);
lean_dec_ref(v_m_471_);
return v_res_473_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__1_spec__2_spec__3___redArg(lean_object* v_b_474_, lean_object* v_acc_475_, lean_object* v_i_476_){
_start:
{
lean_object* v___y_478_; lean_object* v_keyArray_486_; lean_object* v_valueArray_487_; lean_object* v___x_488_; uint8_t v___x_489_; 
v_keyArray_486_ = lean_ctor_get(v_b_474_, 1);
v_valueArray_487_ = lean_ctor_get(v_b_474_, 2);
v___x_488_ = lean_array_get_size(v_keyArray_486_);
v___x_489_ = lean_nat_dec_lt(v_i_476_, v___x_488_);
if (v___x_489_ == 0)
{
lean_dec(v_i_476_);
return v_acc_475_;
}
else
{
lean_object* v___x_490_; uint8_t v_isSome_491_; 
v___x_490_ = lean_array_fget_borrowed(v_keyArray_486_, v_i_476_);
v_isSome_491_ = lean_noption_is_some(v___x_490_);
if (v_isSome_491_ == 0)
{
goto v___jp_482_;
}
else
{
lean_object* v___x_492_; uint8_t v_isSome_493_; 
v___x_492_ = lean_array_fget_borrowed(v_valueArray_487_, v_i_476_);
v_isSome_493_ = lean_noption_is_some(v___x_492_);
if (v_isSome_493_ == 0)
{
goto v___jp_482_;
}
else
{
lean_object* v_val_494_; lean_object* v_val_495_; lean_object* v_i_497_; lean_object* v___x_502_; 
lean_inc(v___x_490_);
v_val_494_ = lean_noption_get(v___x_490_);
lean_inc(v___x_492_);
v_val_495_ = lean_noption_get(v___x_492_);
v___x_502_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0___redArg(v_acc_475_, v_val_494_);
switch(lean_obj_tag(v___x_502_))
{
case 0:
{
lean_object* v_index_503_; lean_object* v_size_504_; lean_object* v___x_505_; 
v_index_503_ = lean_ctor_get(v___x_502_, 0);
lean_inc(v_index_503_);
lean_dec_ref_known(v___x_502_, 3);
v_size_504_ = lean_ctor_get(v_acc_475_, 0);
lean_inc(v_size_504_);
v___x_505_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_475_, v_size_504_, v_index_503_, v_val_494_, v_val_495_);
lean_dec(v_index_503_);
v___y_478_ = v___x_505_;
goto v___jp_477_;
}
case 1:
{
lean_object* v_index_506_; 
v_index_506_ = lean_ctor_get(v___x_502_, 0);
lean_inc(v_index_506_);
lean_dec_ref_known(v___x_502_, 1);
v_i_497_ = v_index_506_;
goto v___jp_496_;
}
default: 
{
lean_object* v___x_507_; lean_object* v___x_508_; 
v___x_507_ = lean_unsigned_to_nat(0u);
v___x_508_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v_acc_475_, v___x_507_);
if (lean_obj_tag(v___x_508_) == 0)
{
lean_object* v_index_509_; 
v_index_509_ = lean_ctor_get(v___x_508_, 0);
lean_inc(v_index_509_);
lean_dec_ref_known(v___x_508_, 1);
v_i_497_ = v_index_509_;
goto v___jp_496_;
}
else
{
lean_dec(v_val_495_);
lean_dec(v_val_494_);
v___y_478_ = v_acc_475_;
goto v___jp_477_;
}
}
}
v___jp_496_:
{
lean_object* v_size_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; 
v_size_498_ = lean_ctor_get(v_acc_475_, 0);
v___x_499_ = lean_unsigned_to_nat(1u);
v___x_500_ = lean_nat_add(v_size_498_, v___x_499_);
v___x_501_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_475_, v___x_500_, v_i_497_, v_val_494_, v_val_495_);
lean_dec(v_i_497_);
v___y_478_ = v___x_501_;
goto v___jp_477_;
}
}
}
}
v___jp_477_:
{
lean_object* v___x_479_; lean_object* v___x_480_; 
v___x_479_ = lean_unsigned_to_nat(1u);
v___x_480_ = lean_nat_add(v_i_476_, v___x_479_);
lean_dec(v_i_476_);
v_acc_475_ = v___y_478_;
v_i_476_ = v___x_480_;
goto _start;
}
v___jp_482_:
{
lean_object* v___x_483_; lean_object* v___x_484_; 
v___x_483_ = lean_unsigned_to_nat(1u);
v___x_484_ = lean_nat_add(v_i_476_, v___x_483_);
lean_dec(v_i_476_);
v_i_476_ = v___x_484_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__1_spec__2_spec__3___redArg___boxed(lean_object* v_b_510_, lean_object* v_acc_511_, lean_object* v_i_512_){
_start:
{
lean_object* v_res_513_; 
v_res_513_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__1_spec__2_spec__3___redArg(v_b_510_, v_acc_511_, v_i_512_);
lean_dec_ref(v_b_510_);
return v_res_513_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__1_spec__2___redArg(lean_object* v_init_514_, lean_object* v_b_515_){
_start:
{
lean_object* v___x_516_; lean_object* v___x_517_; 
v___x_516_ = lean_unsigned_to_nat(0u);
v___x_517_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__1_spec__2_spec__3___redArg(v_b_515_, v_init_514_, v___x_516_);
return v___x_517_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__1_spec__2___redArg___boxed(lean_object* v_init_518_, lean_object* v_b_519_){
_start:
{
lean_object* v_res_520_; 
v_res_520_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__1_spec__2___redArg(v_init_518_, v_b_519_);
lean_dec_ref(v_b_519_);
return v_res_520_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__1___redArg(lean_object* v_m_521_){
_start:
{
lean_object* v_keyArray_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v_cellCount_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v_target_529_; lean_object* v___x_530_; 
v_keyArray_522_ = lean_ctor_get(v_m_521_, 1);
v___x_523_ = lean_array_get_size(v_keyArray_522_);
v___x_524_ = lean_unsigned_to_nat(2u);
v_cellCount_525_ = lean_nat_mul(v___x_523_, v___x_524_);
v___x_526_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_525_);
v___x_527_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_525_);
v___x_528_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_525_);
v_target_529_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_target_529_, 0, v___x_526_);
lean_ctor_set(v_target_529_, 1, v___x_527_);
lean_ctor_set(v_target_529_, 2, v___x_528_);
v___x_530_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__1_spec__2___redArg(v_target_529_, v_m_521_);
return v___x_530_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__1___redArg___boxed(lean_object* v_m_531_){
_start:
{
lean_object* v_res_532_; 
v_res_532_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__1___redArg(v_m_531_);
lean_dec_ref(v_m_531_);
return v_res_532_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__2(lean_object* v_x_533_, lean_object* v_x_534_){
_start:
{
if (lean_obj_tag(v_x_534_) == 0)
{
return v_x_533_;
}
else
{
lean_object* v_head_535_; lean_object* v_tail_536_; lean_object* v___x_537_; lean_object* v___y_539_; lean_object* v_i_540_; lean_object* v___y_547_; lean_object* v___y_559_; lean_object* v_i_560_; lean_object* v___x_578_; 
v_head_535_ = lean_ctor_get(v_x_534_, 0);
lean_inc(v_head_535_);
v_tail_536_ = lean_ctor_get(v_x_534_, 1);
lean_inc(v_tail_536_);
lean_dec_ref_known(v_x_534_, 2);
v___x_537_ = lean_box(0);
v___x_578_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0___redArg(v_x_533_, v_head_535_);
switch(lean_obj_tag(v___x_578_))
{
case 0:
{
lean_dec_ref_known(v___x_578_, 3);
lean_dec(v_head_535_);
v_x_534_ = v_tail_536_;
goto _start;
}
case 1:
{
lean_object* v_index_580_; lean_object* v_size_581_; lean_object* v_keyArray_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; uint8_t v___x_586_; 
v_index_580_ = lean_ctor_get(v___x_578_, 0);
lean_inc(v_index_580_);
lean_dec_ref_known(v___x_578_, 1);
v_size_581_ = lean_ctor_get(v_x_533_, 0);
v_keyArray_582_ = lean_ctor_get(v_x_533_, 1);
v___x_583_ = lean_unsigned_to_nat(1u);
v___x_584_ = lean_nat_add(v_size_581_, v___x_583_);
v___x_585_ = lean_array_get_size(v_keyArray_582_);
v___x_586_ = lean_nat_dec_lt(v___x_584_, v___x_585_);
if (v___x_586_ == 0)
{
lean_dec(v___x_584_);
lean_dec(v_index_580_);
goto v___jp_566_;
}
else
{
lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; uint8_t v___x_591_; 
v___x_587_ = lean_unsigned_to_nat(4u);
v___x_588_ = lean_nat_mul(v___x_584_, v___x_587_);
v___x_589_ = lean_unsigned_to_nat(3u);
v___x_590_ = lean_nat_mul(v___x_585_, v___x_589_);
v___x_591_ = lean_nat_dec_le(v___x_588_, v___x_590_);
lean_dec(v___x_590_);
lean_dec(v___x_588_);
if (v___x_591_ == 0)
{
lean_dec(v___x_584_);
lean_dec(v_index_580_);
goto v___jp_566_;
}
else
{
lean_object* v___x_592_; 
v___x_592_ = l_Std_DHashMap_Raw_setEntry___redArg(v_x_533_, v___x_584_, v_index_580_, v_head_535_, v___x_537_);
lean_dec(v_index_580_);
v_x_533_ = v___x_592_;
v_x_534_ = v_tail_536_;
goto _start;
}
}
}
default: 
{
lean_object* v_size_594_; lean_object* v_keyArray_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; uint8_t v___x_599_; 
v_size_594_ = lean_ctor_get(v_x_533_, 0);
v_keyArray_595_ = lean_ctor_get(v_x_533_, 1);
v___x_596_ = lean_unsigned_to_nat(1u);
v___x_597_ = lean_nat_add(v_size_594_, v___x_596_);
v___x_598_ = lean_array_get_size(v_keyArray_595_);
v___x_599_ = lean_nat_dec_lt(v___x_597_, v___x_598_);
if (v___x_599_ == 0)
{
lean_object* v___x_600_; 
lean_dec(v___x_597_);
v___x_600_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__1___redArg(v_x_533_);
lean_dec_ref(v_x_533_);
v___y_547_ = v___x_600_;
goto v___jp_546_;
}
else
{
lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; uint8_t v___x_605_; 
v___x_601_ = lean_unsigned_to_nat(4u);
v___x_602_ = lean_nat_mul(v___x_597_, v___x_601_);
lean_dec(v___x_597_);
v___x_603_ = lean_unsigned_to_nat(3u);
v___x_604_ = lean_nat_mul(v___x_598_, v___x_603_);
v___x_605_ = lean_nat_dec_le(v___x_602_, v___x_604_);
lean_dec(v___x_604_);
lean_dec(v___x_602_);
if (v___x_605_ == 0)
{
lean_object* v___x_606_; 
v___x_606_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__1___redArg(v_x_533_);
lean_dec_ref(v_x_533_);
v___y_547_ = v___x_606_;
goto v___jp_546_;
}
else
{
v___y_547_ = v_x_533_;
goto v___jp_546_;
}
}
}
}
v___jp_538_:
{
lean_object* v_size_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; 
v_size_541_ = lean_ctor_get(v___y_539_, 0);
v___x_542_ = lean_unsigned_to_nat(1u);
v___x_543_ = lean_nat_add(v_size_541_, v___x_542_);
v___x_544_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_539_, v___x_543_, v_i_540_, v_head_535_, v___x_537_);
lean_dec(v_i_540_);
v_x_533_ = v___x_544_;
v_x_534_ = v_tail_536_;
goto _start;
}
v___jp_546_:
{
lean_object* v___x_548_; 
v___x_548_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0___redArg(v___y_547_, v_head_535_);
switch(lean_obj_tag(v___x_548_))
{
case 0:
{
lean_object* v_index_549_; lean_object* v_size_550_; lean_object* v___x_551_; 
v_index_549_ = lean_ctor_get(v___x_548_, 0);
lean_inc(v_index_549_);
lean_dec_ref_known(v___x_548_, 3);
v_size_550_ = lean_ctor_get(v___y_547_, 0);
lean_inc(v_size_550_);
v___x_551_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_547_, v_size_550_, v_index_549_, v_head_535_, v___x_537_);
lean_dec(v_index_549_);
v_x_533_ = v___x_551_;
v_x_534_ = v_tail_536_;
goto _start;
}
case 1:
{
lean_object* v_index_553_; 
v_index_553_ = lean_ctor_get(v___x_548_, 0);
lean_inc(v_index_553_);
lean_dec_ref_known(v___x_548_, 1);
v___y_539_ = v___y_547_;
v_i_540_ = v_index_553_;
goto v___jp_538_;
}
default: 
{
lean_object* v___x_554_; lean_object* v___x_555_; 
v___x_554_ = lean_unsigned_to_nat(0u);
v___x_555_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_547_, v___x_554_);
if (lean_obj_tag(v___x_555_) == 0)
{
lean_object* v_index_556_; 
v_index_556_ = lean_ctor_get(v___x_555_, 0);
lean_inc(v_index_556_);
lean_dec_ref_known(v___x_555_, 1);
v___y_539_ = v___y_547_;
v_i_540_ = v_index_556_;
goto v___jp_538_;
}
else
{
lean_dec(v_head_535_);
v_x_533_ = v___y_547_;
v_x_534_ = v_tail_536_;
goto _start;
}
}
}
}
v___jp_558_:
{
lean_object* v_size_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; 
v_size_561_ = lean_ctor_get(v___y_559_, 0);
v___x_562_ = lean_unsigned_to_nat(1u);
v___x_563_ = lean_nat_add(v_size_561_, v___x_562_);
v___x_564_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_559_, v___x_563_, v_i_560_, v_head_535_, v___x_537_);
lean_dec(v_i_560_);
v_x_533_ = v___x_564_;
v_x_534_ = v_tail_536_;
goto _start;
}
v___jp_566_:
{
lean_object* v___x_567_; lean_object* v___x_568_; 
v___x_567_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__1___redArg(v_x_533_);
lean_dec_ref(v_x_533_);
v___x_568_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0___redArg(v___x_567_, v_head_535_);
switch(lean_obj_tag(v___x_568_))
{
case 0:
{
lean_object* v_index_569_; lean_object* v_size_570_; lean_object* v___x_571_; 
v_index_569_ = lean_ctor_get(v___x_568_, 0);
lean_inc(v_index_569_);
lean_dec_ref_known(v___x_568_, 3);
v_size_570_ = lean_ctor_get(v___x_567_, 0);
lean_inc(v_size_570_);
v___x_571_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_567_, v_size_570_, v_index_569_, v_head_535_, v___x_537_);
lean_dec(v_index_569_);
v_x_533_ = v___x_571_;
v_x_534_ = v_tail_536_;
goto _start;
}
case 1:
{
lean_object* v_index_573_; 
v_index_573_ = lean_ctor_get(v___x_568_, 0);
lean_inc(v_index_573_);
lean_dec_ref_known(v___x_568_, 1);
v___y_559_ = v___x_567_;
v_i_560_ = v_index_573_;
goto v___jp_558_;
}
default: 
{
lean_object* v___x_574_; lean_object* v___x_575_; 
v___x_574_ = lean_unsigned_to_nat(0u);
v___x_575_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_567_, v___x_574_);
if (lean_obj_tag(v___x_575_) == 0)
{
lean_object* v_index_576_; 
v_index_576_ = lean_ctor_get(v___x_575_, 0);
lean_inc(v_index_576_);
lean_dec_ref_known(v___x_575_, 1);
v___y_559_ = v___x_567_;
v_i_560_ = v_index_576_;
goto v___jp_558_;
}
else
{
lean_dec(v_head_535_);
v_x_533_ = v___x_567_;
v_x_534_ = v_tail_536_;
goto _start;
}
}
}
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__0(void){
_start:
{
lean_object* v_cellCount_607_; lean_object* v___x_608_; 
v_cellCount_607_ = lean_unsigned_to_nat(16u);
v___x_608_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_607_);
return v___x_608_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__1(void){
_start:
{
lean_object* v_cellCount_609_; lean_object* v___x_610_; 
v_cellCount_609_ = lean_unsigned_to_nat(16u);
v___x_610_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_609_);
return v___x_610_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__2(void){
_start:
{
lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; 
v___x_611_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__1, &l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__1);
v___x_612_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__0);
v___x_613_ = lean_unsigned_to_nat(0u);
v___x_614_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_614_, 0, v___x_613_);
lean_ctor_set(v___x_614_, 1, v___x_612_);
lean_ctor_set(v___x_614_, 2, v___x_611_);
return v___x_614_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__35(void){
_start:
{
lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; 
v___x_681_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__34));
v___x_682_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__2);
v___x_683_ = l_List_foldl___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__2(v___x_682_, v___x_681_);
return v___x_683_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring(void){
_start:
{
lean_object* v___x_684_; 
v___x_684_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__35, &l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__35_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__35);
return v___x_684_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0(lean_object* v_00_u03b2_685_, lean_object* v_m_686_, lean_object* v_query_687_){
_start:
{
lean_object* v___x_688_; 
v___x_688_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0___redArg(v_m_686_, v_query_687_);
return v___x_688_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0___boxed(lean_object* v_00_u03b2_689_, lean_object* v_m_690_, lean_object* v_query_691_){
_start:
{
lean_object* v_res_692_; 
v_res_692_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0(v_00_u03b2_689_, v_m_690_, v_query_691_);
lean_dec(v_query_691_);
lean_dec_ref(v_m_690_);
return v_res_692_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__1(lean_object* v_00_u03b2_693_, lean_object* v_m_694_){
_start:
{
lean_object* v___x_695_; 
v___x_695_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__1___redArg(v_m_694_);
return v___x_695_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__1___boxed(lean_object* v_00_u03b2_696_, lean_object* v_m_697_){
_start:
{
lean_object* v_res_698_; 
v_res_698_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__1(v_00_u03b2_696_, v_m_697_);
lean_dec_ref(v_m_697_);
return v_res_698_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__0(lean_object* v_00_u03b2_699_, lean_object* v_m_700_, lean_object* v_query_701_, lean_object* v_x_702_, lean_object* v_x_703_, lean_object* v_x_704_, lean_object* v_x_705_){
_start:
{
lean_object* v___x_706_; 
v___x_706_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__0___redArg(v_m_700_, v_query_701_, v_x_702_, v_x_703_, v_x_704_);
return v___x_706_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__0___boxed(lean_object* v_00_u03b2_707_, lean_object* v_m_708_, lean_object* v_query_709_, lean_object* v_x_710_, lean_object* v_x_711_, lean_object* v_x_712_, lean_object* v_x_713_){
_start:
{
lean_object* v_res_714_; 
v_res_714_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__0(v_00_u03b2_707_, v_m_708_, v_query_709_, v_x_710_, v_x_711_, v_x_712_, v_x_713_);
lean_dec(v_query_709_);
lean_dec_ref(v_m_708_);
return v_res_714_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__1_spec__2(lean_object* v_00_u03b2_715_, lean_object* v_init_716_, lean_object* v_b_717_){
_start:
{
lean_object* v___x_718_; 
v___x_718_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__1_spec__2___redArg(v_init_716_, v_b_717_);
return v___x_718_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__1_spec__2___boxed(lean_object* v_00_u03b2_719_, lean_object* v_init_720_, lean_object* v_b_721_){
_start:
{
lean_object* v_res_722_; 
v_res_722_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__1_spec__2(v_00_u03b2_719_, v_init_720_, v_b_721_);
lean_dec_ref(v_b_721_);
return v_res_722_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_723_, lean_object* v_b_724_, lean_object* v_acc_725_, lean_object* v_i_726_){
_start:
{
lean_object* v___x_727_; 
v___x_727_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__1_spec__2_spec__3___redArg(v_b_724_, v_acc_725_, v_i_726_);
return v___x_727_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__1_spec__2_spec__3___boxed(lean_object* v_00_u03b2_728_, lean_object* v_b_729_, lean_object* v_acc_730_, lean_object* v_i_731_){
_start:
{
lean_object* v_res_732_; 
v_res_732_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__1_spec__2_spec__3(v_00_u03b2_728_, v_b_729_, v_acc_730_, v_i_731_);
lean_dec_ref(v_b_729_);
return v_res_732_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isSupportedSemiringQuick_spec__0_spec__0___redArg(lean_object* v_m_733_, lean_object* v_query_734_){
_start:
{
lean_object* v___x_735_; 
v___x_735_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0___redArg(v_m_733_, v_query_734_);
if (lean_obj_tag(v___x_735_) == 0)
{
lean_object* v_index_736_; lean_object* v_key_737_; lean_object* v_value_738_; lean_object* v___x_740_; uint8_t v_isShared_741_; uint8_t v_isSharedCheck_745_; 
v_index_736_ = lean_ctor_get(v___x_735_, 0);
v_key_737_ = lean_ctor_get(v___x_735_, 1);
v_value_738_ = lean_ctor_get(v___x_735_, 2);
v_isSharedCheck_745_ = !lean_is_exclusive(v___x_735_);
if (v_isSharedCheck_745_ == 0)
{
v___x_740_ = v___x_735_;
v_isShared_741_ = v_isSharedCheck_745_;
goto v_resetjp_739_;
}
else
{
lean_inc(v_value_738_);
lean_inc(v_key_737_);
lean_inc(v_index_736_);
lean_dec(v___x_735_);
v___x_740_ = lean_box(0);
v_isShared_741_ = v_isSharedCheck_745_;
goto v_resetjp_739_;
}
v_resetjp_739_:
{
lean_object* v___x_743_; 
if (v_isShared_741_ == 0)
{
v___x_743_ = v___x_740_;
goto v_reusejp_742_;
}
else
{
lean_object* v_reuseFailAlloc_744_; 
v_reuseFailAlloc_744_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_744_, 0, v_index_736_);
lean_ctor_set(v_reuseFailAlloc_744_, 1, v_key_737_);
lean_ctor_set(v_reuseFailAlloc_744_, 2, v_value_738_);
v___x_743_ = v_reuseFailAlloc_744_;
goto v_reusejp_742_;
}
v_reusejp_742_:
{
return v___x_743_;
}
}
}
else
{
lean_object* v___x_746_; 
lean_dec(v___x_735_);
v___x_746_ = lean_box(1);
return v___x_746_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isSupportedSemiringQuick_spec__0_spec__0___redArg___boxed(lean_object* v_m_747_, lean_object* v_query_748_){
_start:
{
lean_object* v_res_749_; 
v_res_749_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isSupportedSemiringQuick_spec__0_spec__0___redArg(v_m_747_, v_query_748_);
lean_dec(v_query_748_);
lean_dec_ref(v_m_747_);
return v_res_749_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isSupportedSemiringQuick_spec__0___redArg(lean_object* v_m_750_, lean_object* v_a_751_){
_start:
{
lean_object* v___x_752_; 
v___x_752_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isSupportedSemiringQuick_spec__0_spec__0___redArg(v_m_750_, v_a_751_);
if (lean_obj_tag(v___x_752_) == 0)
{
uint8_t v___x_753_; 
lean_dec_ref_known(v___x_752_, 3);
v___x_753_ = 1;
return v___x_753_;
}
else
{
uint8_t v___x_754_; 
v___x_754_ = 0;
return v___x_754_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isSupportedSemiringQuick_spec__0___redArg___boxed(lean_object* v_m_755_, lean_object* v_a_756_){
_start:
{
uint8_t v_res_757_; lean_object* v_r_758_; 
v_res_757_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isSupportedSemiringQuick_spec__0___redArg(v_m_755_, v_a_756_);
lean_dec(v_a_756_);
lean_dec_ref(v_m_755_);
v_r_758_ = lean_box(v_res_757_);
return v_r_758_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isSupportedSemiringQuick(lean_object* v_type_759_){
_start:
{
lean_object* v___x_760_; 
v___x_760_ = l_Lean_Expr_getAppFn(v_type_759_);
if (lean_obj_tag(v___x_760_) == 4)
{
lean_object* v_declName_761_; lean_object* v___x_762_; uint8_t v___x_763_; 
v_declName_761_ = lean_ctor_get(v___x_760_, 0);
lean_inc(v_declName_761_);
lean_dec_ref_known(v___x_760_, 2);
v___x_762_ = l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring;
v___x_763_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isSupportedSemiringQuick_spec__0___redArg(v___x_762_, v_declName_761_);
lean_dec(v_declName_761_);
return v___x_763_;
}
else
{
uint8_t v___x_764_; 
lean_dec_ref(v___x_760_);
v___x_764_ = 0;
return v___x_764_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isSupportedSemiringQuick___boxed(lean_object* v_type_765_){
_start:
{
uint8_t v_res_766_; lean_object* v_r_767_; 
v_res_766_ = l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isSupportedSemiringQuick(v_type_765_);
lean_dec_ref(v_type_765_);
v_r_767_ = lean_box(v_res_766_);
return v_r_767_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isSupportedSemiringQuick_spec__0(lean_object* v_00_u03b2_768_, lean_object* v_m_769_, lean_object* v_a_770_){
_start:
{
uint8_t v___x_771_; 
v___x_771_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isSupportedSemiringQuick_spec__0___redArg(v_m_769_, v_a_770_);
return v___x_771_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isSupportedSemiringQuick_spec__0___boxed(lean_object* v_00_u03b2_772_, lean_object* v_m_773_, lean_object* v_a_774_){
_start:
{
uint8_t v_res_775_; lean_object* v_r_776_; 
v_res_775_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isSupportedSemiringQuick_spec__0(v_00_u03b2_772_, v_m_773_, v_a_774_);
lean_dec(v_a_774_);
lean_dec_ref(v_m_773_);
v_r_776_ = lean_box(v_res_775_);
return v_r_776_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isSupportedSemiringQuick_spec__0_spec__0(lean_object* v_00_u03b2_777_, lean_object* v_m_778_, lean_object* v_query_779_){
_start:
{
lean_object* v___x_780_; 
v___x_780_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isSupportedSemiringQuick_spec__0_spec__0___redArg(v_m_778_, v_query_779_);
return v___x_780_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isSupportedSemiringQuick_spec__0_spec__0___boxed(lean_object* v_00_u03b2_781_, lean_object* v_m_782_, lean_object* v_query_783_){
_start:
{
lean_object* v_res_784_; 
v_res_784_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isSupportedSemiringQuick_spec__0_spec__0(v_00_u03b2_781_, v_m_782_, v_query_783_);
lean_dec(v_query_783_);
lean_dec_ref(v_m_782_);
return v_res_784_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isUnsupportedSemiring_x3f(lean_object* v_type_785_, lean_object* v_a_786_, lean_object* v_a_787_, lean_object* v_a_788_, lean_object* v_a_789_, lean_object* v_a_790_, lean_object* v_a_791_, lean_object* v_a_792_, lean_object* v_a_793_, lean_object* v_a_794_, lean_object* v_a_795_){
_start:
{
uint8_t v___x_797_; 
v___x_797_ = l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isSupportedSemiringQuick(v_type_785_);
if (v___x_797_ == 0)
{
lean_object* v___x_798_; 
lean_inc_ref(v_type_785_);
v___x_798_ = l_Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f(v_type_785_, v_a_786_, v_a_787_, v_a_788_, v_a_789_, v_a_790_, v_a_791_, v_a_792_, v_a_793_, v_a_794_, v_a_795_);
if (lean_obj_tag(v___x_798_) == 0)
{
lean_object* v_a_799_; lean_object* v___x_801_; uint8_t v_isShared_802_; uint8_t v_isSharedCheck_925_; 
v_a_799_ = lean_ctor_get(v___x_798_, 0);
v_isSharedCheck_925_ = !lean_is_exclusive(v___x_798_);
if (v_isSharedCheck_925_ == 0)
{
v___x_801_ = v___x_798_;
v_isShared_802_ = v_isSharedCheck_925_;
goto v_resetjp_800_;
}
else
{
lean_inc(v_a_799_);
lean_dec(v___x_798_);
v___x_801_ = lean_box(0);
v_isShared_802_ = v_isSharedCheck_925_;
goto v_resetjp_800_;
}
v_resetjp_800_:
{
if (lean_obj_tag(v_a_799_) == 0)
{
if (v___x_797_ == 0)
{
lean_object* v___x_808_; 
lean_del_object(v___x_801_);
lean_inc_ref(v_type_785_);
v___x_808_ = l_Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f(v_type_785_, v_a_786_, v_a_787_, v_a_788_, v_a_789_, v_a_790_, v_a_791_, v_a_792_, v_a_793_, v_a_794_, v_a_795_);
if (lean_obj_tag(v___x_808_) == 0)
{
lean_object* v_a_809_; 
v_a_809_ = lean_ctor_get(v___x_808_, 0);
lean_inc(v_a_809_);
lean_dec_ref_known(v___x_808_, 1);
if (lean_obj_tag(v_a_809_) == 1)
{
lean_object* v_val_810_; lean_object* v___x_812_; uint8_t v_isShared_813_; uint8_t v_isSharedCheck_836_; 
lean_dec_ref(v_type_785_);
v_val_810_ = lean_ctor_get(v_a_809_, 0);
v_isSharedCheck_836_ = !lean_is_exclusive(v_a_809_);
if (v_isSharedCheck_836_ == 0)
{
v___x_812_ = v_a_809_;
v_isShared_813_ = v_isSharedCheck_836_;
goto v_resetjp_811_;
}
else
{
lean_inc(v_val_810_);
lean_dec(v_a_809_);
v___x_812_ = lean_box(0);
v_isShared_813_ = v_isSharedCheck_836_;
goto v_resetjp_811_;
}
v_resetjp_811_:
{
lean_object* v___x_814_; 
v___x_814_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring(v_val_810_, v_a_786_, v_a_787_, v_a_788_, v_a_789_, v_a_790_, v_a_791_, v_a_792_, v_a_793_, v_a_794_, v_a_795_);
lean_dec(v_val_810_);
if (lean_obj_tag(v___x_814_) == 0)
{
lean_object* v_a_815_; lean_object* v___x_817_; uint8_t v_isShared_818_; uint8_t v_isSharedCheck_827_; 
v_a_815_ = lean_ctor_get(v___x_814_, 0);
v_isSharedCheck_827_ = !lean_is_exclusive(v___x_814_);
if (v_isSharedCheck_827_ == 0)
{
v___x_817_ = v___x_814_;
v_isShared_818_ = v_isSharedCheck_827_;
goto v_resetjp_816_;
}
else
{
lean_inc(v_a_815_);
lean_dec(v___x_814_);
v___x_817_ = lean_box(0);
v_isShared_818_ = v_isSharedCheck_827_;
goto v_resetjp_816_;
}
v_resetjp_816_:
{
lean_object* v_toSemiring_819_; lean_object* v_semiringInst_820_; lean_object* v___x_822_; 
v_toSemiring_819_ = lean_ctor_get(v_a_815_, 0);
lean_inc_ref(v_toSemiring_819_);
lean_dec(v_a_815_);
v_semiringInst_820_ = lean_ctor_get(v_toSemiring_819_, 3);
lean_inc_ref(v_semiringInst_820_);
lean_dec_ref(v_toSemiring_819_);
if (v_isShared_813_ == 0)
{
lean_ctor_set(v___x_812_, 0, v_semiringInst_820_);
v___x_822_ = v___x_812_;
goto v_reusejp_821_;
}
else
{
lean_object* v_reuseFailAlloc_826_; 
v_reuseFailAlloc_826_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_826_, 0, v_semiringInst_820_);
v___x_822_ = v_reuseFailAlloc_826_;
goto v_reusejp_821_;
}
v_reusejp_821_:
{
lean_object* v___x_824_; 
if (v_isShared_818_ == 0)
{
lean_ctor_set(v___x_817_, 0, v___x_822_);
v___x_824_ = v___x_817_;
goto v_reusejp_823_;
}
else
{
lean_object* v_reuseFailAlloc_825_; 
v_reuseFailAlloc_825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_825_, 0, v___x_822_);
v___x_824_ = v_reuseFailAlloc_825_;
goto v_reusejp_823_;
}
v_reusejp_823_:
{
return v___x_824_;
}
}
}
}
else
{
lean_object* v_a_828_; lean_object* v___x_830_; uint8_t v_isShared_831_; uint8_t v_isSharedCheck_835_; 
lean_del_object(v___x_812_);
v_a_828_ = lean_ctor_get(v___x_814_, 0);
v_isSharedCheck_835_ = !lean_is_exclusive(v___x_814_);
if (v_isSharedCheck_835_ == 0)
{
v___x_830_ = v___x_814_;
v_isShared_831_ = v_isSharedCheck_835_;
goto v_resetjp_829_;
}
else
{
lean_inc(v_a_828_);
lean_dec(v___x_814_);
v___x_830_ = lean_box(0);
v_isShared_831_ = v_isSharedCheck_835_;
goto v_resetjp_829_;
}
v_resetjp_829_:
{
lean_object* v___x_833_; 
if (v_isShared_831_ == 0)
{
v___x_833_ = v___x_830_;
goto v_reusejp_832_;
}
else
{
lean_object* v_reuseFailAlloc_834_; 
v_reuseFailAlloc_834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_834_, 0, v_a_828_);
v___x_833_ = v_reuseFailAlloc_834_;
goto v_reusejp_832_;
}
v_reusejp_832_:
{
return v___x_833_;
}
}
}
}
}
else
{
lean_object* v___x_837_; 
lean_dec(v_a_809_);
lean_inc_ref(v_type_785_);
v___x_837_ = l_Lean_Meta_Grind_Arith_CommRing_getNonCommRingId_x3f(v_type_785_, v_a_786_, v_a_787_, v_a_788_, v_a_789_, v_a_790_, v_a_791_, v_a_792_, v_a_793_, v_a_794_, v_a_795_);
if (lean_obj_tag(v___x_837_) == 0)
{
lean_object* v_a_838_; 
v_a_838_ = lean_ctor_get(v___x_837_, 0);
lean_inc(v_a_838_);
lean_dec_ref_known(v___x_837_, 1);
if (lean_obj_tag(v_a_838_) == 1)
{
lean_object* v_val_839_; lean_object* v___x_841_; uint8_t v_isShared_842_; uint8_t v_isSharedCheck_864_; 
lean_dec_ref(v_type_785_);
v_val_839_ = lean_ctor_get(v_a_838_, 0);
v_isSharedCheck_864_ = !lean_is_exclusive(v_a_838_);
if (v_isSharedCheck_864_ == 0)
{
v___x_841_ = v_a_838_;
v_isShared_842_ = v_isSharedCheck_864_;
goto v_resetjp_840_;
}
else
{
lean_inc(v_val_839_);
lean_dec(v_a_838_);
v___x_841_ = lean_box(0);
v_isShared_842_ = v_isSharedCheck_864_;
goto v_resetjp_840_;
}
v_resetjp_840_:
{
lean_object* v___x_843_; 
v___x_843_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing(v_val_839_, v_a_786_, v_a_787_, v_a_788_, v_a_789_, v_a_790_, v_a_791_, v_a_792_, v_a_793_, v_a_794_, v_a_795_);
lean_dec(v_val_839_);
if (lean_obj_tag(v___x_843_) == 0)
{
lean_object* v_a_844_; lean_object* v___x_846_; uint8_t v_isShared_847_; uint8_t v_isSharedCheck_855_; 
v_a_844_ = lean_ctor_get(v___x_843_, 0);
v_isSharedCheck_855_ = !lean_is_exclusive(v___x_843_);
if (v_isSharedCheck_855_ == 0)
{
v___x_846_ = v___x_843_;
v_isShared_847_ = v_isSharedCheck_855_;
goto v_resetjp_845_;
}
else
{
lean_inc(v_a_844_);
lean_dec(v___x_843_);
v___x_846_ = lean_box(0);
v_isShared_847_ = v_isSharedCheck_855_;
goto v_resetjp_845_;
}
v_resetjp_845_:
{
lean_object* v_semiringInst_848_; lean_object* v___x_850_; 
v_semiringInst_848_ = lean_ctor_get(v_a_844_, 4);
lean_inc_ref(v_semiringInst_848_);
lean_dec(v_a_844_);
if (v_isShared_842_ == 0)
{
lean_ctor_set(v___x_841_, 0, v_semiringInst_848_);
v___x_850_ = v___x_841_;
goto v_reusejp_849_;
}
else
{
lean_object* v_reuseFailAlloc_854_; 
v_reuseFailAlloc_854_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_854_, 0, v_semiringInst_848_);
v___x_850_ = v_reuseFailAlloc_854_;
goto v_reusejp_849_;
}
v_reusejp_849_:
{
lean_object* v___x_852_; 
if (v_isShared_847_ == 0)
{
lean_ctor_set(v___x_846_, 0, v___x_850_);
v___x_852_ = v___x_846_;
goto v_reusejp_851_;
}
else
{
lean_object* v_reuseFailAlloc_853_; 
v_reuseFailAlloc_853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_853_, 0, v___x_850_);
v___x_852_ = v_reuseFailAlloc_853_;
goto v_reusejp_851_;
}
v_reusejp_851_:
{
return v___x_852_;
}
}
}
}
else
{
lean_object* v_a_856_; lean_object* v___x_858_; uint8_t v_isShared_859_; uint8_t v_isSharedCheck_863_; 
lean_del_object(v___x_841_);
v_a_856_ = lean_ctor_get(v___x_843_, 0);
v_isSharedCheck_863_ = !lean_is_exclusive(v___x_843_);
if (v_isSharedCheck_863_ == 0)
{
v___x_858_ = v___x_843_;
v_isShared_859_ = v_isSharedCheck_863_;
goto v_resetjp_857_;
}
else
{
lean_inc(v_a_856_);
lean_dec(v___x_843_);
v___x_858_ = lean_box(0);
v_isShared_859_ = v_isSharedCheck_863_;
goto v_resetjp_857_;
}
v_resetjp_857_:
{
lean_object* v___x_861_; 
if (v_isShared_859_ == 0)
{
v___x_861_ = v___x_858_;
goto v_reusejp_860_;
}
else
{
lean_object* v_reuseFailAlloc_862_; 
v_reuseFailAlloc_862_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_862_, 0, v_a_856_);
v___x_861_ = v_reuseFailAlloc_862_;
goto v_reusejp_860_;
}
v_reusejp_860_:
{
return v___x_861_;
}
}
}
}
}
else
{
lean_object* v___x_865_; 
lean_dec(v_a_838_);
v___x_865_ = l_Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f___redArg(v_type_785_, v_a_786_, v_a_791_, v_a_792_, v_a_793_, v_a_794_, v_a_795_);
if (lean_obj_tag(v___x_865_) == 0)
{
lean_object* v_a_866_; lean_object* v___x_868_; uint8_t v_isShared_869_; uint8_t v_isSharedCheck_900_; 
v_a_866_ = lean_ctor_get(v___x_865_, 0);
v_isSharedCheck_900_ = !lean_is_exclusive(v___x_865_);
if (v_isSharedCheck_900_ == 0)
{
v___x_868_ = v___x_865_;
v_isShared_869_ = v_isSharedCheck_900_;
goto v_resetjp_867_;
}
else
{
lean_inc(v_a_866_);
lean_dec(v___x_865_);
v___x_868_ = lean_box(0);
v_isShared_869_ = v_isSharedCheck_900_;
goto v_resetjp_867_;
}
v_resetjp_867_:
{
if (lean_obj_tag(v_a_866_) == 1)
{
lean_object* v_val_870_; lean_object* v___x_872_; uint8_t v_isShared_873_; uint8_t v_isSharedCheck_895_; 
lean_del_object(v___x_868_);
v_val_870_ = lean_ctor_get(v_a_866_, 0);
v_isSharedCheck_895_ = !lean_is_exclusive(v_a_866_);
if (v_isSharedCheck_895_ == 0)
{
v___x_872_ = v_a_866_;
v_isShared_873_ = v_isSharedCheck_895_;
goto v_resetjp_871_;
}
else
{
lean_inc(v_val_870_);
lean_dec(v_a_866_);
v___x_872_ = lean_box(0);
v_isShared_873_ = v_isSharedCheck_895_;
goto v_resetjp_871_;
}
v_resetjp_871_:
{
lean_object* v___x_874_; 
v___x_874_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiring(v_val_870_, v_a_786_, v_a_787_, v_a_788_, v_a_789_, v_a_790_, v_a_791_, v_a_792_, v_a_793_, v_a_794_, v_a_795_);
lean_dec(v_val_870_);
if (lean_obj_tag(v___x_874_) == 0)
{
lean_object* v_a_875_; lean_object* v___x_877_; uint8_t v_isShared_878_; uint8_t v_isSharedCheck_886_; 
v_a_875_ = lean_ctor_get(v___x_874_, 0);
v_isSharedCheck_886_ = !lean_is_exclusive(v___x_874_);
if (v_isSharedCheck_886_ == 0)
{
v___x_877_ = v___x_874_;
v_isShared_878_ = v_isSharedCheck_886_;
goto v_resetjp_876_;
}
else
{
lean_inc(v_a_875_);
lean_dec(v___x_874_);
v___x_877_ = lean_box(0);
v_isShared_878_ = v_isSharedCheck_886_;
goto v_resetjp_876_;
}
v_resetjp_876_:
{
lean_object* v_semiringInst_879_; lean_object* v___x_881_; 
v_semiringInst_879_ = lean_ctor_get(v_a_875_, 3);
lean_inc_ref(v_semiringInst_879_);
lean_dec(v_a_875_);
if (v_isShared_873_ == 0)
{
lean_ctor_set(v___x_872_, 0, v_semiringInst_879_);
v___x_881_ = v___x_872_;
goto v_reusejp_880_;
}
else
{
lean_object* v_reuseFailAlloc_885_; 
v_reuseFailAlloc_885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_885_, 0, v_semiringInst_879_);
v___x_881_ = v_reuseFailAlloc_885_;
goto v_reusejp_880_;
}
v_reusejp_880_:
{
lean_object* v___x_883_; 
if (v_isShared_878_ == 0)
{
lean_ctor_set(v___x_877_, 0, v___x_881_);
v___x_883_ = v___x_877_;
goto v_reusejp_882_;
}
else
{
lean_object* v_reuseFailAlloc_884_; 
v_reuseFailAlloc_884_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_884_, 0, v___x_881_);
v___x_883_ = v_reuseFailAlloc_884_;
goto v_reusejp_882_;
}
v_reusejp_882_:
{
return v___x_883_;
}
}
}
}
else
{
lean_object* v_a_887_; lean_object* v___x_889_; uint8_t v_isShared_890_; uint8_t v_isSharedCheck_894_; 
lean_del_object(v___x_872_);
v_a_887_ = lean_ctor_get(v___x_874_, 0);
v_isSharedCheck_894_ = !lean_is_exclusive(v___x_874_);
if (v_isSharedCheck_894_ == 0)
{
v___x_889_ = v___x_874_;
v_isShared_890_ = v_isSharedCheck_894_;
goto v_resetjp_888_;
}
else
{
lean_inc(v_a_887_);
lean_dec(v___x_874_);
v___x_889_ = lean_box(0);
v_isShared_890_ = v_isSharedCheck_894_;
goto v_resetjp_888_;
}
v_resetjp_888_:
{
lean_object* v___x_892_; 
if (v_isShared_890_ == 0)
{
v___x_892_ = v___x_889_;
goto v_reusejp_891_;
}
else
{
lean_object* v_reuseFailAlloc_893_; 
v_reuseFailAlloc_893_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_893_, 0, v_a_887_);
v___x_892_ = v_reuseFailAlloc_893_;
goto v_reusejp_891_;
}
v_reusejp_891_:
{
return v___x_892_;
}
}
}
}
}
else
{
lean_object* v___x_896_; lean_object* v___x_898_; 
lean_dec(v_a_866_);
v___x_896_ = lean_box(0);
if (v_isShared_869_ == 0)
{
lean_ctor_set(v___x_868_, 0, v___x_896_);
v___x_898_ = v___x_868_;
goto v_reusejp_897_;
}
else
{
lean_object* v_reuseFailAlloc_899_; 
v_reuseFailAlloc_899_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_899_, 0, v___x_896_);
v___x_898_ = v_reuseFailAlloc_899_;
goto v_reusejp_897_;
}
v_reusejp_897_:
{
return v___x_898_;
}
}
}
}
else
{
lean_object* v_a_901_; lean_object* v___x_903_; uint8_t v_isShared_904_; uint8_t v_isSharedCheck_908_; 
v_a_901_ = lean_ctor_get(v___x_865_, 0);
v_isSharedCheck_908_ = !lean_is_exclusive(v___x_865_);
if (v_isSharedCheck_908_ == 0)
{
v___x_903_ = v___x_865_;
v_isShared_904_ = v_isSharedCheck_908_;
goto v_resetjp_902_;
}
else
{
lean_inc(v_a_901_);
lean_dec(v___x_865_);
v___x_903_ = lean_box(0);
v_isShared_904_ = v_isSharedCheck_908_;
goto v_resetjp_902_;
}
v_resetjp_902_:
{
lean_object* v___x_906_; 
if (v_isShared_904_ == 0)
{
v___x_906_ = v___x_903_;
goto v_reusejp_905_;
}
else
{
lean_object* v_reuseFailAlloc_907_; 
v_reuseFailAlloc_907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_907_, 0, v_a_901_);
v___x_906_ = v_reuseFailAlloc_907_;
goto v_reusejp_905_;
}
v_reusejp_905_:
{
return v___x_906_;
}
}
}
}
}
else
{
lean_object* v_a_909_; lean_object* v___x_911_; uint8_t v_isShared_912_; uint8_t v_isSharedCheck_916_; 
lean_dec_ref(v_type_785_);
v_a_909_ = lean_ctor_get(v___x_837_, 0);
v_isSharedCheck_916_ = !lean_is_exclusive(v___x_837_);
if (v_isSharedCheck_916_ == 0)
{
v___x_911_ = v___x_837_;
v_isShared_912_ = v_isSharedCheck_916_;
goto v_resetjp_910_;
}
else
{
lean_inc(v_a_909_);
lean_dec(v___x_837_);
v___x_911_ = lean_box(0);
v_isShared_912_ = v_isSharedCheck_916_;
goto v_resetjp_910_;
}
v_resetjp_910_:
{
lean_object* v___x_914_; 
if (v_isShared_912_ == 0)
{
v___x_914_ = v___x_911_;
goto v_reusejp_913_;
}
else
{
lean_object* v_reuseFailAlloc_915_; 
v_reuseFailAlloc_915_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_915_, 0, v_a_909_);
v___x_914_ = v_reuseFailAlloc_915_;
goto v_reusejp_913_;
}
v_reusejp_913_:
{
return v___x_914_;
}
}
}
}
}
else
{
lean_object* v_a_917_; lean_object* v___x_919_; uint8_t v_isShared_920_; uint8_t v_isSharedCheck_924_; 
lean_dec_ref(v_type_785_);
v_a_917_ = lean_ctor_get(v___x_808_, 0);
v_isSharedCheck_924_ = !lean_is_exclusive(v___x_808_);
if (v_isSharedCheck_924_ == 0)
{
v___x_919_ = v___x_808_;
v_isShared_920_ = v_isSharedCheck_924_;
goto v_resetjp_918_;
}
else
{
lean_inc(v_a_917_);
lean_dec(v___x_808_);
v___x_919_ = lean_box(0);
v_isShared_920_ = v_isSharedCheck_924_;
goto v_resetjp_918_;
}
v_resetjp_918_:
{
lean_object* v___x_922_; 
if (v_isShared_920_ == 0)
{
v___x_922_ = v___x_919_;
goto v_reusejp_921_;
}
else
{
lean_object* v_reuseFailAlloc_923_; 
v_reuseFailAlloc_923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_923_, 0, v_a_917_);
v___x_922_ = v_reuseFailAlloc_923_;
goto v_reusejp_921_;
}
v_reusejp_921_:
{
return v___x_922_;
}
}
}
}
else
{
lean_dec_ref(v_type_785_);
goto v___jp_803_;
}
}
else
{
lean_dec_ref_known(v_a_799_, 1);
lean_dec_ref(v_type_785_);
goto v___jp_803_;
}
v___jp_803_:
{
lean_object* v___x_804_; lean_object* v___x_806_; 
v___x_804_ = lean_box(0);
if (v_isShared_802_ == 0)
{
lean_ctor_set(v___x_801_, 0, v___x_804_);
v___x_806_ = v___x_801_;
goto v_reusejp_805_;
}
else
{
lean_object* v_reuseFailAlloc_807_; 
v_reuseFailAlloc_807_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_807_, 0, v___x_804_);
v___x_806_ = v_reuseFailAlloc_807_;
goto v_reusejp_805_;
}
v_reusejp_805_:
{
return v___x_806_;
}
}
}
}
else
{
lean_object* v_a_926_; lean_object* v___x_928_; uint8_t v_isShared_929_; uint8_t v_isSharedCheck_933_; 
lean_dec_ref(v_type_785_);
v_a_926_ = lean_ctor_get(v___x_798_, 0);
v_isSharedCheck_933_ = !lean_is_exclusive(v___x_798_);
if (v_isSharedCheck_933_ == 0)
{
v___x_928_ = v___x_798_;
v_isShared_929_ = v_isSharedCheck_933_;
goto v_resetjp_927_;
}
else
{
lean_inc(v_a_926_);
lean_dec(v___x_798_);
v___x_928_ = lean_box(0);
v_isShared_929_ = v_isSharedCheck_933_;
goto v_resetjp_927_;
}
v_resetjp_927_:
{
lean_object* v___x_931_; 
if (v_isShared_929_ == 0)
{
v___x_931_ = v___x_928_;
goto v_reusejp_930_;
}
else
{
lean_object* v_reuseFailAlloc_932_; 
v_reuseFailAlloc_932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_932_, 0, v_a_926_);
v___x_931_ = v_reuseFailAlloc_932_;
goto v_reusejp_930_;
}
v_reusejp_930_:
{
return v___x_931_;
}
}
}
}
else
{
lean_object* v___x_934_; lean_object* v___x_935_; 
lean_dec_ref(v_type_785_);
v___x_934_ = lean_box(0);
v___x_935_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_935_, 0, v___x_934_);
return v___x_935_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isUnsupportedSemiring_x3f___boxed(lean_object* v_type_936_, lean_object* v_a_937_, lean_object* v_a_938_, lean_object* v_a_939_, lean_object* v_a_940_, lean_object* v_a_941_, lean_object* v_a_942_, lean_object* v_a_943_, lean_object* v_a_944_, lean_object* v_a_945_, lean_object* v_a_946_, lean_object* v_a_947_){
_start:
{
lean_object* v_res_948_; 
v_res_948_ = l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isUnsupportedSemiring_x3f(v_type_936_, v_a_937_, v_a_938_, v_a_939_, v_a_940_, v_a_941_, v_a_942_, v_a_943_, v_a_944_, v_a_945_, v_a_946_);
lean_dec(v_a_946_);
lean_dec_ref(v_a_945_);
lean_dec(v_a_944_);
lean_dec_ref(v_a_943_);
lean_dec(v_a_942_);
lean_dec_ref(v_a_941_);
lean_dec(v_a_940_);
lean_dec_ref(v_a_939_);
lean_dec(v_a_938_);
lean_dec(v_a_937_);
return v_res_948_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isOfNat_x3f(lean_object* v_a_954_, lean_object* v_a_955_, lean_object* v_a_956_, lean_object* v_a_957_, lean_object* v_a_958_){
_start:
{
lean_object* v___x_963_; uint8_t v___x_964_; 
v___x_963_ = l_Lean_Expr_cleanupAnnotations(v_a_954_);
v___x_964_ = l_Lean_Expr_isApp(v___x_963_);
if (v___x_964_ == 0)
{
lean_dec_ref(v___x_963_);
goto v___jp_960_;
}
else
{
lean_object* v___x_965_; uint8_t v___x_966_; 
v___x_965_ = l_Lean_Expr_appFnCleanup___redArg(v___x_963_);
v___x_966_ = l_Lean_Expr_isApp(v___x_965_);
if (v___x_966_ == 0)
{
lean_dec_ref(v___x_965_);
goto v___jp_960_;
}
else
{
lean_object* v_arg_967_; lean_object* v___x_968_; uint8_t v___x_969_; 
v_arg_967_ = lean_ctor_get(v___x_965_, 1);
lean_inc_ref(v_arg_967_);
v___x_968_ = l_Lean_Expr_appFnCleanup___redArg(v___x_965_);
v___x_969_ = l_Lean_Expr_isApp(v___x_968_);
if (v___x_969_ == 0)
{
lean_dec_ref(v___x_968_);
lean_dec_ref(v_arg_967_);
goto v___jp_960_;
}
else
{
lean_object* v___x_970_; lean_object* v___x_971_; uint8_t v___x_972_; 
v___x_970_ = l_Lean_Expr_appFnCleanup___redArg(v___x_968_);
v___x_971_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isOfNat_x3f___closed__2));
v___x_972_ = l_Lean_Expr_isConstOf(v___x_970_, v___x_971_);
lean_dec_ref(v___x_970_);
if (v___x_972_ == 0)
{
lean_dec_ref(v_arg_967_);
goto v___jp_960_;
}
else
{
lean_object* v___x_973_; 
v___x_973_ = l_Lean_Meta_getNatValue_x3f(v_arg_967_, v_a_955_, v_a_956_, v_a_957_, v_a_958_);
lean_dec_ref(v_arg_967_);
return v___x_973_;
}
}
}
}
v___jp_960_:
{
lean_object* v___x_961_; lean_object* v___x_962_; 
v___x_961_ = lean_box(0);
v___x_962_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_962_, 0, v___x_961_);
return v___x_962_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isOfNat_x3f___boxed(lean_object* v_a_974_, lean_object* v_a_975_, lean_object* v_a_976_, lean_object* v_a_977_, lean_object* v_a_978_, lean_object* v_a_979_){
_start:
{
lean_object* v_res_980_; 
v_res_980_ = l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isOfNat_x3f(v_a_974_, v_a_975_, v_a_976_, v_a_977_, v_a_978_);
lean_dec(v_a_978_);
lean_dec_ref(v_a_977_);
lean_dec(v_a_976_);
lean_dec_ref(v_a_975_);
return v_res_980_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_propagateMul(lean_object* v_e_1011_, lean_object* v_a_1012_, lean_object* v_a_1013_, lean_object* v_a_1014_, lean_object* v_a_1015_, lean_object* v_a_1016_, lean_object* v_a_1017_, lean_object* v_a_1018_, lean_object* v_a_1019_, lean_object* v_a_1020_, lean_object* v_a_1021_){
_start:
{
lean_object* v___x_1026_; uint8_t v___x_1027_; 
lean_inc_ref(v_e_1011_);
v___x_1026_ = l_Lean_Expr_cleanupAnnotations(v_e_1011_);
v___x_1027_ = l_Lean_Expr_isApp(v___x_1026_);
if (v___x_1027_ == 0)
{
lean_dec_ref(v___x_1026_);
lean_dec_ref(v_e_1011_);
goto v___jp_1023_;
}
else
{
lean_object* v_arg_1028_; lean_object* v___x_1029_; uint8_t v___x_1030_; 
v_arg_1028_ = lean_ctor_get(v___x_1026_, 1);
lean_inc_ref(v_arg_1028_);
v___x_1029_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1026_);
v___x_1030_ = l_Lean_Expr_isApp(v___x_1029_);
if (v___x_1030_ == 0)
{
lean_dec_ref(v___x_1029_);
lean_dec_ref(v_arg_1028_);
lean_dec_ref(v_e_1011_);
goto v___jp_1023_;
}
else
{
lean_object* v_arg_1031_; lean_object* v___x_1032_; uint8_t v___x_1033_; 
v_arg_1031_ = lean_ctor_get(v___x_1029_, 1);
lean_inc_ref(v_arg_1031_);
v___x_1032_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1029_);
v___x_1033_ = l_Lean_Expr_isApp(v___x_1032_);
if (v___x_1033_ == 0)
{
lean_dec_ref(v___x_1032_);
lean_dec_ref(v_arg_1031_);
lean_dec_ref(v_arg_1028_);
lean_dec_ref(v_e_1011_);
goto v___jp_1023_;
}
else
{
lean_object* v___x_1034_; uint8_t v___x_1035_; 
v___x_1034_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1032_);
v___x_1035_ = l_Lean_Expr_isApp(v___x_1034_);
if (v___x_1035_ == 0)
{
lean_dec_ref(v___x_1034_);
lean_dec_ref(v_arg_1031_);
lean_dec_ref(v_arg_1028_);
lean_dec_ref(v_e_1011_);
goto v___jp_1023_;
}
else
{
lean_object* v_arg_1036_; lean_object* v___x_1037_; uint8_t v___x_1038_; 
v_arg_1036_ = lean_ctor_get(v___x_1034_, 1);
lean_inc_ref(v_arg_1036_);
v___x_1037_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1034_);
v___x_1038_ = l_Lean_Expr_isApp(v___x_1037_);
if (v___x_1038_ == 0)
{
lean_dec_ref(v___x_1037_);
lean_dec_ref(v_arg_1036_);
lean_dec_ref(v_arg_1031_);
lean_dec_ref(v_arg_1028_);
lean_dec_ref(v_e_1011_);
goto v___jp_1023_;
}
else
{
lean_object* v_arg_1039_; lean_object* v___x_1040_; uint8_t v___x_1041_; 
v_arg_1039_ = lean_ctor_get(v___x_1037_, 1);
lean_inc_ref(v_arg_1039_);
v___x_1040_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1037_);
v___x_1041_ = l_Lean_Expr_isApp(v___x_1040_);
if (v___x_1041_ == 0)
{
lean_dec_ref(v___x_1040_);
lean_dec_ref(v_arg_1039_);
lean_dec_ref(v_arg_1036_);
lean_dec_ref(v_arg_1031_);
lean_dec_ref(v_arg_1028_);
lean_dec_ref(v_e_1011_);
goto v___jp_1023_;
}
else
{
lean_object* v_arg_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; uint8_t v___x_1045_; 
v_arg_1042_ = lean_ctor_get(v___x_1040_, 1);
lean_inc_ref(v_arg_1042_);
v___x_1043_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1040_);
v___x_1044_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_propagateMul___closed__2));
v___x_1045_ = l_Lean_Expr_isConstOf(v___x_1043_, v___x_1044_);
if (v___x_1045_ == 0)
{
lean_dec_ref(v___x_1043_);
lean_dec_ref(v_arg_1042_);
lean_dec_ref(v_arg_1039_);
lean_dec_ref(v_arg_1036_);
lean_dec_ref(v_arg_1031_);
lean_dec_ref(v_arg_1028_);
lean_dec_ref(v_e_1011_);
goto v___jp_1023_;
}
else
{
lean_object* v___x_1046_; 
lean_inc_ref(v_arg_1042_);
v___x_1046_ = l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isUnsupportedSemiring_x3f(v_arg_1042_, v_a_1012_, v_a_1013_, v_a_1014_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_, v_a_1019_, v_a_1020_, v_a_1021_);
if (lean_obj_tag(v___x_1046_) == 0)
{
lean_object* v_a_1047_; lean_object* v___x_1049_; uint8_t v_isShared_1050_; uint8_t v_isSharedCheck_1224_; 
v_a_1047_ = lean_ctor_get(v___x_1046_, 0);
v_isSharedCheck_1224_ = !lean_is_exclusive(v___x_1046_);
if (v_isSharedCheck_1224_ == 0)
{
v___x_1049_ = v___x_1046_;
v_isShared_1050_ = v_isSharedCheck_1224_;
goto v_resetjp_1048_;
}
else
{
lean_inc(v_a_1047_);
lean_dec(v___x_1046_);
v___x_1049_ = lean_box(0);
v_isShared_1050_ = v_isSharedCheck_1224_;
goto v_resetjp_1048_;
}
v_resetjp_1048_:
{
if (lean_obj_tag(v_a_1047_) == 1)
{
lean_object* v_val_1051_; uint8_t v___y_1053_; size_t v___x_1215_; size_t v___x_1216_; uint8_t v___x_1217_; 
v_val_1051_ = lean_ctor_get(v_a_1047_, 0);
lean_inc(v_val_1051_);
lean_dec_ref_known(v_a_1047_, 1);
v___x_1215_ = lean_ptr_addr(v_arg_1042_);
v___x_1216_ = lean_ptr_addr(v_arg_1039_);
lean_dec_ref(v_arg_1039_);
v___x_1217_ = lean_usize_dec_eq(v___x_1215_, v___x_1216_);
if (v___x_1217_ == 0)
{
lean_dec_ref(v_arg_1036_);
v___y_1053_ = v___x_1217_;
goto v___jp_1052_;
}
else
{
size_t v___x_1218_; uint8_t v___x_1219_; 
v___x_1218_ = lean_ptr_addr(v_arg_1036_);
lean_dec_ref(v_arg_1036_);
v___x_1219_ = lean_usize_dec_eq(v___x_1215_, v___x_1218_);
v___y_1053_ = v___x_1219_;
goto v___jp_1052_;
}
v___jp_1052_:
{
if (v___y_1053_ == 0)
{
lean_object* v___x_1054_; lean_object* v___x_1056_; 
lean_dec(v_val_1051_);
lean_dec_ref(v___x_1043_);
lean_dec_ref(v_arg_1042_);
lean_dec_ref(v_arg_1031_);
lean_dec_ref(v_arg_1028_);
lean_dec_ref(v_e_1011_);
v___x_1054_ = lean_box(0);
if (v_isShared_1050_ == 0)
{
lean_ctor_set(v___x_1049_, 0, v___x_1054_);
v___x_1056_ = v___x_1049_;
goto v_reusejp_1055_;
}
else
{
lean_object* v_reuseFailAlloc_1057_; 
v_reuseFailAlloc_1057_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1057_, 0, v___x_1054_);
v___x_1056_ = v_reuseFailAlloc_1057_;
goto v_reusejp_1055_;
}
v_reusejp_1055_:
{
return v___x_1056_;
}
}
else
{
lean_object* v___x_1058_; 
v___x_1058_ = l_Lean_Expr_constLevels_x21(v___x_1043_);
lean_dec_ref(v___x_1043_);
if (lean_obj_tag(v___x_1058_) == 1)
{
lean_object* v_head_1059_; lean_object* v___x_1061_; uint8_t v_isShared_1062_; uint8_t v_isSharedCheck_1209_; 
lean_del_object(v___x_1049_);
v_head_1059_ = lean_ctor_get(v___x_1058_, 0);
v_isSharedCheck_1209_ = !lean_is_exclusive(v___x_1058_);
if (v_isSharedCheck_1209_ == 0)
{
lean_object* v_unused_1210_; 
v_unused_1210_ = lean_ctor_get(v___x_1058_, 1);
lean_dec(v_unused_1210_);
v___x_1061_ = v___x_1058_;
v_isShared_1062_ = v_isSharedCheck_1209_;
goto v_resetjp_1060_;
}
else
{
lean_inc(v_head_1059_);
lean_dec(v___x_1058_);
v___x_1061_ = lean_box(0);
v_isShared_1062_ = v_isSharedCheck_1209_;
goto v_resetjp_1060_;
}
v_resetjp_1060_:
{
lean_object* v___x_1063_; lean_object* v___x_1064_; 
v___x_1063_ = lean_st_ref_get(v_a_1012_);
lean_inc_ref(v_arg_1031_);
v___x_1064_ = l_Lean_Meta_Grind_Goal_getRoot(v___x_1063_, v_arg_1031_, v_a_1018_, v_a_1019_, v_a_1020_, v_a_1021_);
lean_dec(v___x_1063_);
if (lean_obj_tag(v___x_1064_) == 0)
{
lean_object* v_a_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; 
v_a_1065_ = lean_ctor_get(v___x_1064_, 0);
lean_inc(v_a_1065_);
lean_dec_ref_known(v___x_1064_, 1);
v___x_1066_ = lean_st_ref_get(v_a_1012_);
lean_inc_ref(v_arg_1028_);
v___x_1067_ = l_Lean_Meta_Grind_Goal_getRoot(v___x_1066_, v_arg_1028_, v_a_1018_, v_a_1019_, v_a_1020_, v_a_1021_);
lean_dec(v___x_1066_);
if (lean_obj_tag(v___x_1067_) == 0)
{
lean_object* v_a_1068_; lean_object* v___x_1069_; 
v_a_1068_ = lean_ctor_get(v___x_1067_, 0);
lean_inc(v_a_1068_);
lean_dec_ref_known(v___x_1067_, 1);
lean_inc(v_a_1065_);
v___x_1069_ = l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isOfNat_x3f(v_a_1065_, v_a_1018_, v_a_1019_, v_a_1020_, v_a_1021_);
if (lean_obj_tag(v___x_1069_) == 0)
{
lean_object* v_a_1070_; lean_object* v___x_1072_; uint8_t v_isShared_1073_; uint8_t v_isSharedCheck_1184_; 
v_a_1070_ = lean_ctor_get(v___x_1069_, 0);
v_isSharedCheck_1184_ = !lean_is_exclusive(v___x_1069_);
if (v_isSharedCheck_1184_ == 0)
{
v___x_1072_ = v___x_1069_;
v_isShared_1073_ = v_isSharedCheck_1184_;
goto v_resetjp_1071_;
}
else
{
lean_inc(v_a_1070_);
lean_dec(v___x_1069_);
v___x_1072_ = lean_box(0);
v_isShared_1073_ = v_isSharedCheck_1184_;
goto v_resetjp_1071_;
}
v_resetjp_1071_:
{
if (lean_obj_tag(v_a_1070_) == 1)
{
lean_object* v_val_1074_; lean_object* v___x_1075_; uint8_t v___x_1076_; 
lean_dec(v_a_1068_);
v_val_1074_ = lean_ctor_get(v_a_1070_, 0);
lean_inc(v_val_1074_);
lean_dec_ref_known(v_a_1070_, 1);
v___x_1075_ = lean_unsigned_to_nat(0u);
v___x_1076_ = lean_nat_dec_eq(v_val_1074_, v___x_1075_);
if (v___x_1076_ == 0)
{
lean_object* v___x_1077_; uint8_t v___x_1078_; 
v___x_1077_ = lean_unsigned_to_nat(1u);
v___x_1078_ = lean_nat_dec_eq(v_val_1074_, v___x_1077_);
lean_dec(v_val_1074_);
if (v___x_1078_ == 0)
{
lean_object* v___x_1079_; lean_object* v___x_1081_; 
lean_dec(v_a_1065_);
lean_del_object(v___x_1061_);
lean_dec(v_head_1059_);
lean_dec(v_val_1051_);
lean_dec_ref(v_arg_1042_);
lean_dec_ref(v_arg_1031_);
lean_dec_ref(v_arg_1028_);
lean_dec_ref(v_e_1011_);
v___x_1079_ = lean_box(0);
if (v_isShared_1073_ == 0)
{
lean_ctor_set(v___x_1072_, 0, v___x_1079_);
v___x_1081_ = v___x_1072_;
goto v_reusejp_1080_;
}
else
{
lean_object* v_reuseFailAlloc_1082_; 
v_reuseFailAlloc_1082_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1082_, 0, v___x_1079_);
v___x_1081_ = v_reuseFailAlloc_1082_;
goto v_reusejp_1080_;
}
v_reusejp_1080_:
{
return v___x_1081_;
}
}
else
{
lean_object* v___x_1083_; 
lean_del_object(v___x_1072_);
lean_inc(v_a_1021_);
lean_inc_ref(v_a_1020_);
lean_inc(v_a_1019_);
lean_inc_ref(v_a_1018_);
lean_inc(v_a_1017_);
lean_inc_ref(v_a_1016_);
lean_inc(v_a_1015_);
lean_inc_ref(v_a_1014_);
lean_inc(v_a_1013_);
lean_inc(v_a_1012_);
lean_inc_ref(v_arg_1031_);
v___x_1083_ = lean_grind_mk_eq_proof(v_arg_1031_, v_a_1065_, v_a_1012_, v_a_1013_, v_a_1014_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_, v_a_1019_, v_a_1020_, v_a_1021_);
if (lean_obj_tag(v___x_1083_) == 0)
{
lean_object* v_a_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1088_; 
v_a_1084_ = lean_ctor_get(v___x_1083_, 0);
lean_inc(v_a_1084_);
lean_dec_ref_known(v___x_1083_, 1);
v___x_1085_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_propagateMul___closed__5));
v___x_1086_ = lean_box(0);
if (v_isShared_1062_ == 0)
{
lean_ctor_set(v___x_1061_, 1, v___x_1086_);
v___x_1088_ = v___x_1061_;
goto v_reusejp_1087_;
}
else
{
lean_object* v_reuseFailAlloc_1092_; 
v_reuseFailAlloc_1092_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1092_, 0, v_head_1059_);
lean_ctor_set(v_reuseFailAlloc_1092_, 1, v___x_1086_);
v___x_1088_ = v_reuseFailAlloc_1092_;
goto v_reusejp_1087_;
}
v_reusejp_1087_:
{
lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; 
v___x_1089_ = l_Lean_mkConst(v___x_1085_, v___x_1088_);
lean_inc_ref(v_arg_1028_);
v___x_1090_ = l_Lean_mkApp5(v___x_1089_, v_arg_1042_, v_val_1051_, v_arg_1031_, v_arg_1028_, v_a_1084_);
v___x_1091_ = l_Lean_Meta_Grind_pushEqCore___redArg(v_e_1011_, v_arg_1028_, v___x_1090_, v___x_1076_, v_a_1012_, v_a_1014_, v_a_1018_, v_a_1019_, v_a_1020_, v_a_1021_);
return v___x_1091_;
}
}
else
{
lean_object* v_a_1093_; lean_object* v___x_1095_; uint8_t v_isShared_1096_; uint8_t v_isSharedCheck_1100_; 
lean_del_object(v___x_1061_);
lean_dec(v_head_1059_);
lean_dec(v_val_1051_);
lean_dec_ref(v_arg_1042_);
lean_dec_ref(v_arg_1031_);
lean_dec_ref(v_arg_1028_);
lean_dec_ref(v_e_1011_);
v_a_1093_ = lean_ctor_get(v___x_1083_, 0);
v_isSharedCheck_1100_ = !lean_is_exclusive(v___x_1083_);
if (v_isSharedCheck_1100_ == 0)
{
v___x_1095_ = v___x_1083_;
v_isShared_1096_ = v_isSharedCheck_1100_;
goto v_resetjp_1094_;
}
else
{
lean_inc(v_a_1093_);
lean_dec(v___x_1083_);
v___x_1095_ = lean_box(0);
v_isShared_1096_ = v_isSharedCheck_1100_;
goto v_resetjp_1094_;
}
v_resetjp_1094_:
{
lean_object* v___x_1098_; 
if (v_isShared_1096_ == 0)
{
v___x_1098_ = v___x_1095_;
goto v_reusejp_1097_;
}
else
{
lean_object* v_reuseFailAlloc_1099_; 
v_reuseFailAlloc_1099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1099_, 0, v_a_1093_);
v___x_1098_ = v_reuseFailAlloc_1099_;
goto v_reusejp_1097_;
}
v_reusejp_1097_:
{
return v___x_1098_;
}
}
}
}
}
else
{
lean_object* v___x_1101_; 
lean_dec(v_val_1074_);
lean_del_object(v___x_1072_);
lean_inc(v_a_1021_);
lean_inc_ref(v_a_1020_);
lean_inc(v_a_1019_);
lean_inc_ref(v_a_1018_);
lean_inc(v_a_1017_);
lean_inc_ref(v_a_1016_);
lean_inc(v_a_1015_);
lean_inc_ref(v_a_1014_);
lean_inc(v_a_1013_);
lean_inc(v_a_1012_);
lean_inc(v_a_1065_);
lean_inc_ref(v_arg_1031_);
v___x_1101_ = lean_grind_mk_eq_proof(v_arg_1031_, v_a_1065_, v_a_1012_, v_a_1013_, v_a_1014_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_, v_a_1019_, v_a_1020_, v_a_1021_);
if (lean_obj_tag(v___x_1101_) == 0)
{
lean_object* v_a_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1106_; 
v_a_1102_ = lean_ctor_get(v___x_1101_, 0);
lean_inc(v_a_1102_);
lean_dec_ref_known(v___x_1101_, 1);
v___x_1103_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_propagateMul___closed__7));
v___x_1104_ = lean_box(0);
if (v_isShared_1062_ == 0)
{
lean_ctor_set(v___x_1061_, 1, v___x_1104_);
v___x_1106_ = v___x_1061_;
goto v_reusejp_1105_;
}
else
{
lean_object* v_reuseFailAlloc_1111_; 
v_reuseFailAlloc_1111_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1111_, 0, v_head_1059_);
lean_ctor_set(v_reuseFailAlloc_1111_, 1, v___x_1104_);
v___x_1106_ = v_reuseFailAlloc_1111_;
goto v_reusejp_1105_;
}
v_reusejp_1105_:
{
lean_object* v___x_1107_; lean_object* v___x_1108_; uint8_t v___x_1109_; lean_object* v___x_1110_; 
v___x_1107_ = l_Lean_mkConst(v___x_1103_, v___x_1106_);
v___x_1108_ = l_Lean_mkApp5(v___x_1107_, v_arg_1042_, v_val_1051_, v_arg_1031_, v_arg_1028_, v_a_1102_);
v___x_1109_ = 0;
v___x_1110_ = l_Lean_Meta_Grind_pushEqCore___redArg(v_e_1011_, v_a_1065_, v___x_1108_, v___x_1109_, v_a_1012_, v_a_1014_, v_a_1018_, v_a_1019_, v_a_1020_, v_a_1021_);
return v___x_1110_;
}
}
else
{
lean_object* v_a_1112_; lean_object* v___x_1114_; uint8_t v_isShared_1115_; uint8_t v_isSharedCheck_1119_; 
lean_dec(v_a_1065_);
lean_del_object(v___x_1061_);
lean_dec(v_head_1059_);
lean_dec(v_val_1051_);
lean_dec_ref(v_arg_1042_);
lean_dec_ref(v_arg_1031_);
lean_dec_ref(v_arg_1028_);
lean_dec_ref(v_e_1011_);
v_a_1112_ = lean_ctor_get(v___x_1101_, 0);
v_isSharedCheck_1119_ = !lean_is_exclusive(v___x_1101_);
if (v_isSharedCheck_1119_ == 0)
{
v___x_1114_ = v___x_1101_;
v_isShared_1115_ = v_isSharedCheck_1119_;
goto v_resetjp_1113_;
}
else
{
lean_inc(v_a_1112_);
lean_dec(v___x_1101_);
v___x_1114_ = lean_box(0);
v_isShared_1115_ = v_isSharedCheck_1119_;
goto v_resetjp_1113_;
}
v_resetjp_1113_:
{
lean_object* v___x_1117_; 
if (v_isShared_1115_ == 0)
{
v___x_1117_ = v___x_1114_;
goto v_reusejp_1116_;
}
else
{
lean_object* v_reuseFailAlloc_1118_; 
v_reuseFailAlloc_1118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1118_, 0, v_a_1112_);
v___x_1117_ = v_reuseFailAlloc_1118_;
goto v_reusejp_1116_;
}
v_reusejp_1116_:
{
return v___x_1117_;
}
}
}
}
}
else
{
lean_object* v___x_1120_; 
lean_del_object(v___x_1072_);
lean_dec(v_a_1070_);
lean_dec(v_a_1065_);
lean_inc(v_a_1068_);
v___x_1120_ = l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isOfNat_x3f(v_a_1068_, v_a_1018_, v_a_1019_, v_a_1020_, v_a_1021_);
if (lean_obj_tag(v___x_1120_) == 0)
{
lean_object* v_a_1121_; lean_object* v___x_1123_; uint8_t v_isShared_1124_; uint8_t v_isSharedCheck_1175_; 
v_a_1121_ = lean_ctor_get(v___x_1120_, 0);
v_isSharedCheck_1175_ = !lean_is_exclusive(v___x_1120_);
if (v_isSharedCheck_1175_ == 0)
{
v___x_1123_ = v___x_1120_;
v_isShared_1124_ = v_isSharedCheck_1175_;
goto v_resetjp_1122_;
}
else
{
lean_inc(v_a_1121_);
lean_dec(v___x_1120_);
v___x_1123_ = lean_box(0);
v_isShared_1124_ = v_isSharedCheck_1175_;
goto v_resetjp_1122_;
}
v_resetjp_1122_:
{
if (lean_obj_tag(v_a_1121_) == 1)
{
lean_object* v_val_1125_; lean_object* v___x_1126_; uint8_t v___x_1127_; 
v_val_1125_ = lean_ctor_get(v_a_1121_, 0);
lean_inc(v_val_1125_);
lean_dec_ref_known(v_a_1121_, 1);
v___x_1126_ = lean_unsigned_to_nat(0u);
v___x_1127_ = lean_nat_dec_eq(v_val_1125_, v___x_1126_);
if (v___x_1127_ == 0)
{
lean_object* v___x_1128_; uint8_t v___x_1129_; 
v___x_1128_ = lean_unsigned_to_nat(1u);
v___x_1129_ = lean_nat_dec_eq(v_val_1125_, v___x_1128_);
lean_dec(v_val_1125_);
if (v___x_1129_ == 0)
{
lean_object* v___x_1130_; lean_object* v___x_1132_; 
lean_dec(v_a_1068_);
lean_del_object(v___x_1061_);
lean_dec(v_head_1059_);
lean_dec(v_val_1051_);
lean_dec_ref(v_arg_1042_);
lean_dec_ref(v_arg_1031_);
lean_dec_ref(v_arg_1028_);
lean_dec_ref(v_e_1011_);
v___x_1130_ = lean_box(0);
if (v_isShared_1124_ == 0)
{
lean_ctor_set(v___x_1123_, 0, v___x_1130_);
v___x_1132_ = v___x_1123_;
goto v_reusejp_1131_;
}
else
{
lean_object* v_reuseFailAlloc_1133_; 
v_reuseFailAlloc_1133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1133_, 0, v___x_1130_);
v___x_1132_ = v_reuseFailAlloc_1133_;
goto v_reusejp_1131_;
}
v_reusejp_1131_:
{
return v___x_1132_;
}
}
else
{
lean_object* v___x_1134_; 
lean_del_object(v___x_1123_);
lean_inc(v_a_1021_);
lean_inc_ref(v_a_1020_);
lean_inc(v_a_1019_);
lean_inc_ref(v_a_1018_);
lean_inc(v_a_1017_);
lean_inc_ref(v_a_1016_);
lean_inc(v_a_1015_);
lean_inc_ref(v_a_1014_);
lean_inc(v_a_1013_);
lean_inc(v_a_1012_);
lean_inc_ref(v_arg_1028_);
v___x_1134_ = lean_grind_mk_eq_proof(v_arg_1028_, v_a_1068_, v_a_1012_, v_a_1013_, v_a_1014_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_, v_a_1019_, v_a_1020_, v_a_1021_);
if (lean_obj_tag(v___x_1134_) == 0)
{
lean_object* v_a_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1139_; 
v_a_1135_ = lean_ctor_get(v___x_1134_, 0);
lean_inc(v_a_1135_);
lean_dec_ref_known(v___x_1134_, 1);
v___x_1136_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_propagateMul___closed__9));
v___x_1137_ = lean_box(0);
if (v_isShared_1062_ == 0)
{
lean_ctor_set(v___x_1061_, 1, v___x_1137_);
v___x_1139_ = v___x_1061_;
goto v_reusejp_1138_;
}
else
{
lean_object* v_reuseFailAlloc_1143_; 
v_reuseFailAlloc_1143_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1143_, 0, v_head_1059_);
lean_ctor_set(v_reuseFailAlloc_1143_, 1, v___x_1137_);
v___x_1139_ = v_reuseFailAlloc_1143_;
goto v_reusejp_1138_;
}
v_reusejp_1138_:
{
lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; 
v___x_1140_ = l_Lean_mkConst(v___x_1136_, v___x_1139_);
lean_inc_ref(v_arg_1031_);
v___x_1141_ = l_Lean_mkApp5(v___x_1140_, v_arg_1042_, v_val_1051_, v_arg_1031_, v_arg_1028_, v_a_1135_);
v___x_1142_ = l_Lean_Meta_Grind_pushEqCore___redArg(v_e_1011_, v_arg_1031_, v___x_1141_, v___x_1127_, v_a_1012_, v_a_1014_, v_a_1018_, v_a_1019_, v_a_1020_, v_a_1021_);
return v___x_1142_;
}
}
else
{
lean_object* v_a_1144_; lean_object* v___x_1146_; uint8_t v_isShared_1147_; uint8_t v_isSharedCheck_1151_; 
lean_del_object(v___x_1061_);
lean_dec(v_head_1059_);
lean_dec(v_val_1051_);
lean_dec_ref(v_arg_1042_);
lean_dec_ref(v_arg_1031_);
lean_dec_ref(v_arg_1028_);
lean_dec_ref(v_e_1011_);
v_a_1144_ = lean_ctor_get(v___x_1134_, 0);
v_isSharedCheck_1151_ = !lean_is_exclusive(v___x_1134_);
if (v_isSharedCheck_1151_ == 0)
{
v___x_1146_ = v___x_1134_;
v_isShared_1147_ = v_isSharedCheck_1151_;
goto v_resetjp_1145_;
}
else
{
lean_inc(v_a_1144_);
lean_dec(v___x_1134_);
v___x_1146_ = lean_box(0);
v_isShared_1147_ = v_isSharedCheck_1151_;
goto v_resetjp_1145_;
}
v_resetjp_1145_:
{
lean_object* v___x_1149_; 
if (v_isShared_1147_ == 0)
{
v___x_1149_ = v___x_1146_;
goto v_reusejp_1148_;
}
else
{
lean_object* v_reuseFailAlloc_1150_; 
v_reuseFailAlloc_1150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1150_, 0, v_a_1144_);
v___x_1149_ = v_reuseFailAlloc_1150_;
goto v_reusejp_1148_;
}
v_reusejp_1148_:
{
return v___x_1149_;
}
}
}
}
}
else
{
lean_object* v___x_1152_; 
lean_dec(v_val_1125_);
lean_del_object(v___x_1123_);
lean_inc(v_a_1021_);
lean_inc_ref(v_a_1020_);
lean_inc(v_a_1019_);
lean_inc_ref(v_a_1018_);
lean_inc(v_a_1017_);
lean_inc_ref(v_a_1016_);
lean_inc(v_a_1015_);
lean_inc_ref(v_a_1014_);
lean_inc(v_a_1013_);
lean_inc(v_a_1012_);
lean_inc(v_a_1068_);
lean_inc_ref(v_arg_1028_);
v___x_1152_ = lean_grind_mk_eq_proof(v_arg_1028_, v_a_1068_, v_a_1012_, v_a_1013_, v_a_1014_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_, v_a_1019_, v_a_1020_, v_a_1021_);
if (lean_obj_tag(v___x_1152_) == 0)
{
lean_object* v_a_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1157_; 
v_a_1153_ = lean_ctor_get(v___x_1152_, 0);
lean_inc(v_a_1153_);
lean_dec_ref_known(v___x_1152_, 1);
v___x_1154_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_propagateMul___closed__11));
v___x_1155_ = lean_box(0);
if (v_isShared_1062_ == 0)
{
lean_ctor_set(v___x_1061_, 1, v___x_1155_);
v___x_1157_ = v___x_1061_;
goto v_reusejp_1156_;
}
else
{
lean_object* v_reuseFailAlloc_1162_; 
v_reuseFailAlloc_1162_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1162_, 0, v_head_1059_);
lean_ctor_set(v_reuseFailAlloc_1162_, 1, v___x_1155_);
v___x_1157_ = v_reuseFailAlloc_1162_;
goto v_reusejp_1156_;
}
v_reusejp_1156_:
{
lean_object* v___x_1158_; lean_object* v___x_1159_; uint8_t v___x_1160_; lean_object* v___x_1161_; 
v___x_1158_ = l_Lean_mkConst(v___x_1154_, v___x_1157_);
v___x_1159_ = l_Lean_mkApp5(v___x_1158_, v_arg_1042_, v_val_1051_, v_arg_1031_, v_arg_1028_, v_a_1153_);
v___x_1160_ = 0;
v___x_1161_ = l_Lean_Meta_Grind_pushEqCore___redArg(v_e_1011_, v_a_1068_, v___x_1159_, v___x_1160_, v_a_1012_, v_a_1014_, v_a_1018_, v_a_1019_, v_a_1020_, v_a_1021_);
return v___x_1161_;
}
}
else
{
lean_object* v_a_1163_; lean_object* v___x_1165_; uint8_t v_isShared_1166_; uint8_t v_isSharedCheck_1170_; 
lean_dec(v_a_1068_);
lean_del_object(v___x_1061_);
lean_dec(v_head_1059_);
lean_dec(v_val_1051_);
lean_dec_ref(v_arg_1042_);
lean_dec_ref(v_arg_1031_);
lean_dec_ref(v_arg_1028_);
lean_dec_ref(v_e_1011_);
v_a_1163_ = lean_ctor_get(v___x_1152_, 0);
v_isSharedCheck_1170_ = !lean_is_exclusive(v___x_1152_);
if (v_isSharedCheck_1170_ == 0)
{
v___x_1165_ = v___x_1152_;
v_isShared_1166_ = v_isSharedCheck_1170_;
goto v_resetjp_1164_;
}
else
{
lean_inc(v_a_1163_);
lean_dec(v___x_1152_);
v___x_1165_ = lean_box(0);
v_isShared_1166_ = v_isSharedCheck_1170_;
goto v_resetjp_1164_;
}
v_resetjp_1164_:
{
lean_object* v___x_1168_; 
if (v_isShared_1166_ == 0)
{
v___x_1168_ = v___x_1165_;
goto v_reusejp_1167_;
}
else
{
lean_object* v_reuseFailAlloc_1169_; 
v_reuseFailAlloc_1169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1169_, 0, v_a_1163_);
v___x_1168_ = v_reuseFailAlloc_1169_;
goto v_reusejp_1167_;
}
v_reusejp_1167_:
{
return v___x_1168_;
}
}
}
}
}
else
{
lean_object* v___x_1171_; lean_object* v___x_1173_; 
lean_dec(v_a_1121_);
lean_dec(v_a_1068_);
lean_del_object(v___x_1061_);
lean_dec(v_head_1059_);
lean_dec(v_val_1051_);
lean_dec_ref(v_arg_1042_);
lean_dec_ref(v_arg_1031_);
lean_dec_ref(v_arg_1028_);
lean_dec_ref(v_e_1011_);
v___x_1171_ = lean_box(0);
if (v_isShared_1124_ == 0)
{
lean_ctor_set(v___x_1123_, 0, v___x_1171_);
v___x_1173_ = v___x_1123_;
goto v_reusejp_1172_;
}
else
{
lean_object* v_reuseFailAlloc_1174_; 
v_reuseFailAlloc_1174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1174_, 0, v___x_1171_);
v___x_1173_ = v_reuseFailAlloc_1174_;
goto v_reusejp_1172_;
}
v_reusejp_1172_:
{
return v___x_1173_;
}
}
}
}
else
{
lean_object* v_a_1176_; lean_object* v___x_1178_; uint8_t v_isShared_1179_; uint8_t v_isSharedCheck_1183_; 
lean_dec(v_a_1068_);
lean_del_object(v___x_1061_);
lean_dec(v_head_1059_);
lean_dec(v_val_1051_);
lean_dec_ref(v_arg_1042_);
lean_dec_ref(v_arg_1031_);
lean_dec_ref(v_arg_1028_);
lean_dec_ref(v_e_1011_);
v_a_1176_ = lean_ctor_get(v___x_1120_, 0);
v_isSharedCheck_1183_ = !lean_is_exclusive(v___x_1120_);
if (v_isSharedCheck_1183_ == 0)
{
v___x_1178_ = v___x_1120_;
v_isShared_1179_ = v_isSharedCheck_1183_;
goto v_resetjp_1177_;
}
else
{
lean_inc(v_a_1176_);
lean_dec(v___x_1120_);
v___x_1178_ = lean_box(0);
v_isShared_1179_ = v_isSharedCheck_1183_;
goto v_resetjp_1177_;
}
v_resetjp_1177_:
{
lean_object* v___x_1181_; 
if (v_isShared_1179_ == 0)
{
v___x_1181_ = v___x_1178_;
goto v_reusejp_1180_;
}
else
{
lean_object* v_reuseFailAlloc_1182_; 
v_reuseFailAlloc_1182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1182_, 0, v_a_1176_);
v___x_1181_ = v_reuseFailAlloc_1182_;
goto v_reusejp_1180_;
}
v_reusejp_1180_:
{
return v___x_1181_;
}
}
}
}
}
}
else
{
lean_object* v_a_1185_; lean_object* v___x_1187_; uint8_t v_isShared_1188_; uint8_t v_isSharedCheck_1192_; 
lean_dec(v_a_1068_);
lean_dec(v_a_1065_);
lean_del_object(v___x_1061_);
lean_dec(v_head_1059_);
lean_dec(v_val_1051_);
lean_dec_ref(v_arg_1042_);
lean_dec_ref(v_arg_1031_);
lean_dec_ref(v_arg_1028_);
lean_dec_ref(v_e_1011_);
v_a_1185_ = lean_ctor_get(v___x_1069_, 0);
v_isSharedCheck_1192_ = !lean_is_exclusive(v___x_1069_);
if (v_isSharedCheck_1192_ == 0)
{
v___x_1187_ = v___x_1069_;
v_isShared_1188_ = v_isSharedCheck_1192_;
goto v_resetjp_1186_;
}
else
{
lean_inc(v_a_1185_);
lean_dec(v___x_1069_);
v___x_1187_ = lean_box(0);
v_isShared_1188_ = v_isSharedCheck_1192_;
goto v_resetjp_1186_;
}
v_resetjp_1186_:
{
lean_object* v___x_1190_; 
if (v_isShared_1188_ == 0)
{
v___x_1190_ = v___x_1187_;
goto v_reusejp_1189_;
}
else
{
lean_object* v_reuseFailAlloc_1191_; 
v_reuseFailAlloc_1191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1191_, 0, v_a_1185_);
v___x_1190_ = v_reuseFailAlloc_1191_;
goto v_reusejp_1189_;
}
v_reusejp_1189_:
{
return v___x_1190_;
}
}
}
}
else
{
lean_object* v_a_1193_; lean_object* v___x_1195_; uint8_t v_isShared_1196_; uint8_t v_isSharedCheck_1200_; 
lean_dec(v_a_1065_);
lean_del_object(v___x_1061_);
lean_dec(v_head_1059_);
lean_dec(v_val_1051_);
lean_dec_ref(v_arg_1042_);
lean_dec_ref(v_arg_1031_);
lean_dec_ref(v_arg_1028_);
lean_dec_ref(v_e_1011_);
v_a_1193_ = lean_ctor_get(v___x_1067_, 0);
v_isSharedCheck_1200_ = !lean_is_exclusive(v___x_1067_);
if (v_isSharedCheck_1200_ == 0)
{
v___x_1195_ = v___x_1067_;
v_isShared_1196_ = v_isSharedCheck_1200_;
goto v_resetjp_1194_;
}
else
{
lean_inc(v_a_1193_);
lean_dec(v___x_1067_);
v___x_1195_ = lean_box(0);
v_isShared_1196_ = v_isSharedCheck_1200_;
goto v_resetjp_1194_;
}
v_resetjp_1194_:
{
lean_object* v___x_1198_; 
if (v_isShared_1196_ == 0)
{
v___x_1198_ = v___x_1195_;
goto v_reusejp_1197_;
}
else
{
lean_object* v_reuseFailAlloc_1199_; 
v_reuseFailAlloc_1199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1199_, 0, v_a_1193_);
v___x_1198_ = v_reuseFailAlloc_1199_;
goto v_reusejp_1197_;
}
v_reusejp_1197_:
{
return v___x_1198_;
}
}
}
}
else
{
lean_object* v_a_1201_; lean_object* v___x_1203_; uint8_t v_isShared_1204_; uint8_t v_isSharedCheck_1208_; 
lean_del_object(v___x_1061_);
lean_dec(v_head_1059_);
lean_dec(v_val_1051_);
lean_dec_ref(v_arg_1042_);
lean_dec_ref(v_arg_1031_);
lean_dec_ref(v_arg_1028_);
lean_dec_ref(v_e_1011_);
v_a_1201_ = lean_ctor_get(v___x_1064_, 0);
v_isSharedCheck_1208_ = !lean_is_exclusive(v___x_1064_);
if (v_isSharedCheck_1208_ == 0)
{
v___x_1203_ = v___x_1064_;
v_isShared_1204_ = v_isSharedCheck_1208_;
goto v_resetjp_1202_;
}
else
{
lean_inc(v_a_1201_);
lean_dec(v___x_1064_);
v___x_1203_ = lean_box(0);
v_isShared_1204_ = v_isSharedCheck_1208_;
goto v_resetjp_1202_;
}
v_resetjp_1202_:
{
lean_object* v___x_1206_; 
if (v_isShared_1204_ == 0)
{
v___x_1206_ = v___x_1203_;
goto v_reusejp_1205_;
}
else
{
lean_object* v_reuseFailAlloc_1207_; 
v_reuseFailAlloc_1207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1207_, 0, v_a_1201_);
v___x_1206_ = v_reuseFailAlloc_1207_;
goto v_reusejp_1205_;
}
v_reusejp_1205_:
{
return v___x_1206_;
}
}
}
}
}
else
{
lean_object* v___x_1211_; lean_object* v___x_1213_; 
lean_dec(v___x_1058_);
lean_dec(v_val_1051_);
lean_dec_ref(v_arg_1042_);
lean_dec_ref(v_arg_1031_);
lean_dec_ref(v_arg_1028_);
lean_dec_ref(v_e_1011_);
v___x_1211_ = lean_box(0);
if (v_isShared_1050_ == 0)
{
lean_ctor_set(v___x_1049_, 0, v___x_1211_);
v___x_1213_ = v___x_1049_;
goto v_reusejp_1212_;
}
else
{
lean_object* v_reuseFailAlloc_1214_; 
v_reuseFailAlloc_1214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1214_, 0, v___x_1211_);
v___x_1213_ = v_reuseFailAlloc_1214_;
goto v_reusejp_1212_;
}
v_reusejp_1212_:
{
return v___x_1213_;
}
}
}
}
}
else
{
lean_object* v___x_1220_; lean_object* v___x_1222_; 
lean_dec(v_a_1047_);
lean_dec_ref(v___x_1043_);
lean_dec_ref(v_arg_1042_);
lean_dec_ref(v_arg_1039_);
lean_dec_ref(v_arg_1036_);
lean_dec_ref(v_arg_1031_);
lean_dec_ref(v_arg_1028_);
lean_dec_ref(v_e_1011_);
v___x_1220_ = lean_box(0);
if (v_isShared_1050_ == 0)
{
lean_ctor_set(v___x_1049_, 0, v___x_1220_);
v___x_1222_ = v___x_1049_;
goto v_reusejp_1221_;
}
else
{
lean_object* v_reuseFailAlloc_1223_; 
v_reuseFailAlloc_1223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1223_, 0, v___x_1220_);
v___x_1222_ = v_reuseFailAlloc_1223_;
goto v_reusejp_1221_;
}
v_reusejp_1221_:
{
return v___x_1222_;
}
}
}
}
else
{
lean_object* v_a_1225_; lean_object* v___x_1227_; uint8_t v_isShared_1228_; uint8_t v_isSharedCheck_1232_; 
lean_dec_ref(v___x_1043_);
lean_dec_ref(v_arg_1042_);
lean_dec_ref(v_arg_1039_);
lean_dec_ref(v_arg_1036_);
lean_dec_ref(v_arg_1031_);
lean_dec_ref(v_arg_1028_);
lean_dec_ref(v_e_1011_);
v_a_1225_ = lean_ctor_get(v___x_1046_, 0);
v_isSharedCheck_1232_ = !lean_is_exclusive(v___x_1046_);
if (v_isSharedCheck_1232_ == 0)
{
v___x_1227_ = v___x_1046_;
v_isShared_1228_ = v_isSharedCheck_1232_;
goto v_resetjp_1226_;
}
else
{
lean_inc(v_a_1225_);
lean_dec(v___x_1046_);
v___x_1227_ = lean_box(0);
v_isShared_1228_ = v_isSharedCheck_1232_;
goto v_resetjp_1226_;
}
v_resetjp_1226_:
{
lean_object* v___x_1230_; 
if (v_isShared_1228_ == 0)
{
v___x_1230_ = v___x_1227_;
goto v_reusejp_1229_;
}
else
{
lean_object* v_reuseFailAlloc_1231_; 
v_reuseFailAlloc_1231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1231_, 0, v_a_1225_);
v___x_1230_ = v_reuseFailAlloc_1231_;
goto v_reusejp_1229_;
}
v_reusejp_1229_:
{
return v___x_1230_;
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
v___jp_1023_:
{
lean_object* v___x_1024_; lean_object* v___x_1025_; 
v___x_1024_ = lean_box(0);
v___x_1025_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1025_, 0, v___x_1024_);
return v___x_1025_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_propagateMul___boxed(lean_object* v_e_1233_, lean_object* v_a_1234_, lean_object* v_a_1235_, lean_object* v_a_1236_, lean_object* v_a_1237_, lean_object* v_a_1238_, lean_object* v_a_1239_, lean_object* v_a_1240_, lean_object* v_a_1241_, lean_object* v_a_1242_, lean_object* v_a_1243_, lean_object* v_a_1244_){
_start:
{
lean_object* v_res_1245_; 
v_res_1245_ = l_Lean_Meta_Grind_Arith_propagateMul(v_e_1233_, v_a_1234_, v_a_1235_, v_a_1236_, v_a_1237_, v_a_1238_, v_a_1239_, v_a_1240_, v_a_1241_, v_a_1242_, v_a_1243_);
lean_dec(v_a_1243_);
lean_dec_ref(v_a_1242_);
lean_dec(v_a_1241_);
lean_dec_ref(v_a_1240_);
lean_dec(v_a_1239_);
lean_dec_ref(v_a_1238_);
lean_dec(v_a_1237_);
lean_dec_ref(v_a_1236_);
lean_dec(v_a_1235_);
lean_dec(v_a_1234_);
return v_res_1245_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_propagateMul___regBuiltin_Lean_Meta_Grind_Arith_propagateMul_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_3131998065____hygCtx___hyg_9_(){
_start:
{
lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; 
v___x_1247_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_propagateMul___closed__2));
v___x_1248_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_propagateMul___boxed), 12, 0);
v___x_1249_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_1247_, v___x_1248_);
return v___x_1249_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_propagateMul___regBuiltin_Lean_Meta_Grind_Arith_propagateMul_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_3131998065____hygCtx___hyg_9____boxed(lean_object* v_a_1250_){
_start:
{
lean_object* v_res_1251_; 
v_res_1251_ = l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_propagateMul___regBuiltin_Lean_Meta_Grind_Arith_propagateMul_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_3131998065____hygCtx___hyg_9_();
return v_res_1251_;
}
}
lean_object* runtime_initialize_Init_Grind(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_NonCommRingM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_NonCommSemiringM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_PropagatorAttr(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Propagate(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
res = l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_propagateNatAnd___regBuiltin_Lean_Meta_Grind_Arith_propagateNatAnd_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_1291761156____hygCtx___hyg_9_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_propagateNatOr___regBuiltin_Lean_Meta_Grind_Arith_propagateNatOr_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_2834229635____hygCtx___hyg_9_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_propagateNatXOr___regBuiltin_Lean_Meta_Grind_Arith_propagateNatXOr_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_3633575148____hygCtx___hyg_9_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_propagateNatShiftLeft___regBuiltin_Lean_Meta_Grind_Arith_propagateNatShiftLeft_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_3253038636____hygCtx___hyg_9_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_propagateNatShiftRight___regBuiltin_Lean_Meta_Grind_Arith_propagateNatShiftRight_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_1805815810____hygCtx___hyg_9_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring = _init_l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring);
res = l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_propagateMul___regBuiltin_Lean_Meta_Grind_Arith_propagateMul_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_3131998065____hygCtx___hyg_9_();
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
