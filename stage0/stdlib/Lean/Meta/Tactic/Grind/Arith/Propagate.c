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
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Nat_land___boxed(lean_object*, lean_object*);
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
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
lean_object* l_Nat_shiftLeft___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNonCommRingId_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiring(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Expr_constLevels_x21(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_mkApp5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_propagateMul___regBuiltin_Lean_Meta_Grind_Arith_propagateMul_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_3131998065____hygCtx___hyg_9_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_propagateMul___regBuiltin_Lean_Meta_Grind_Arith_propagateMul_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_3131998065____hygCtx___hyg_9____boxed(lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_propagateNatBinOp(lean_object* v_declName_4_, lean_object* v_congrThmName_5_, lean_object* v_op_6_, lean_object* v_e_7_, lean_object* v_a_8_, lean_object* v_a_9_, lean_object* v_a_10_, lean_object* v_a_11_, lean_object* v_a_12_, lean_object* v_a_13_, lean_object* v_a_14_, lean_object* v_a_15_, lean_object* v_a_16_, lean_object* v_a_17_){
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
lean_object* v___x_36_; lean_object* v_a_37_; lean_object* v___x_38_; lean_object* v___x_39_; 
v___x_36_ = lean_unsigned_to_nat(0u);
v_a_37_ = l_Lean_Expr_getRevArg_x21(v_e_7_, v___x_24_);
v___x_38_ = lean_st_ref_get(v_a_8_);
lean_inc_ref(v_a_37_);
v___x_39_ = l_Lean_Meta_Grind_Goal_getRoot(v___x_38_, v_a_37_, v_a_14_, v_a_15_, v_a_16_, v_a_17_);
lean_dec(v___x_38_);
if (lean_obj_tag(v___x_39_) == 0)
{
lean_object* v_a_40_; lean_object* v___x_41_; 
v_a_40_ = lean_ctor_get(v___x_39_, 0);
lean_inc(v_a_40_);
lean_dec_ref_known(v___x_39_, 1);
v___x_41_ = l_Lean_Meta_getNatValue_x3f(v_a_40_, v_a_14_, v_a_15_, v_a_16_, v_a_17_);
if (lean_obj_tag(v___x_41_) == 0)
{
lean_object* v_a_42_; lean_object* v___x_44_; uint8_t v_isShared_45_; uint8_t v_isSharedCheck_122_; 
v_a_42_ = lean_ctor_get(v___x_41_, 0);
v_isSharedCheck_122_ = !lean_is_exclusive(v___x_41_);
if (v_isSharedCheck_122_ == 0)
{
v___x_44_ = v___x_41_;
v_isShared_45_ = v_isSharedCheck_122_;
goto v_resetjp_43_;
}
else
{
lean_inc(v_a_42_);
lean_dec(v___x_41_);
v___x_44_ = lean_box(0);
v_isShared_45_ = v_isSharedCheck_122_;
goto v_resetjp_43_;
}
v_resetjp_43_:
{
if (lean_obj_tag(v_a_42_) == 1)
{
lean_object* v_val_46_; lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v___x_49_; 
lean_del_object(v___x_44_);
v_val_46_ = lean_ctor_get(v_a_42_, 0);
lean_inc(v_val_46_);
lean_dec_ref_known(v_a_42_, 1);
v___x_47_ = l_Lean_Expr_getRevArg_x21(v_e_7_, v___x_36_);
v___x_48_ = lean_st_ref_get(v_a_8_);
lean_inc_ref(v___x_47_);
v___x_49_ = l_Lean_Meta_Grind_Goal_getRoot(v___x_48_, v___x_47_, v_a_14_, v_a_15_, v_a_16_, v_a_17_);
lean_dec(v___x_48_);
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
v___x_57_ = lean_apply_2(v_op_6_, v_val_46_, v_val_56_);
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
v___x_62_ = lean_grind_internalize(v_a_60_, v___x_36_, v___x_61_, v_a_8_, v_a_9_, v_a_10_, v_a_11_, v_a_12_, v_a_13_, v_a_14_, v_a_15_, v_a_16_, v_a_17_);
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
lean_inc(v_a_40_);
lean_inc_ref(v_a_37_);
v___x_63_ = lean_grind_mk_eq_proof(v_a_37_, v_a_40_, v_a_8_, v_a_9_, v_a_10_, v_a_11_, v_a_12_, v_a_13_, v_a_14_, v_a_15_, v_a_16_, v_a_17_);
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
lean_inc_ref(v___x_47_);
v___x_65_ = lean_grind_mk_eq_proof(v___x_47_, v_a_50_, v_a_8_, v_a_9_, v_a_10_, v_a_11_, v_a_12_, v_a_13_, v_a_14_, v_a_15_, v_a_16_, v_a_17_);
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
v___x_70_ = l_Lean_mkApp8(v___x_68_, v_a_37_, v___x_47_, v_a_40_, v_a_50_, v_a_60_, v_a_64_, v_a_66_, v___x_69_);
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
lean_dec_ref(v___x_47_);
lean_dec(v_a_40_);
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
lean_dec_ref(v___x_47_);
lean_dec(v_a_40_);
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
lean_dec_ref(v___x_47_);
lean_dec(v_a_40_);
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
lean_dec_ref(v___x_47_);
lean_dec(v_a_40_);
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
lean_dec_ref(v___x_47_);
lean_dec(v_val_46_);
lean_dec(v_a_40_);
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
lean_dec_ref(v___x_47_);
lean_dec(v_val_46_);
lean_dec(v_a_40_);
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
lean_dec_ref(v___x_47_);
lean_dec(v_val_46_);
lean_dec(v_a_40_);
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
lean_dec(v_a_42_);
lean_dec(v_a_40_);
lean_dec_ref(v_a_37_);
lean_dec_ref(v_e_7_);
lean_dec_ref(v_op_6_);
lean_dec(v_congrThmName_5_);
v___x_118_ = lean_box(0);
if (v_isShared_45_ == 0)
{
lean_ctor_set(v___x_44_, 0, v___x_118_);
v___x_120_ = v___x_44_;
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
lean_dec(v_a_40_);
lean_dec_ref(v_a_37_);
lean_dec_ref(v_e_7_);
lean_dec_ref(v_op_6_);
lean_dec(v_congrThmName_5_);
v_a_123_ = lean_ctor_get(v___x_41_, 0);
v_isSharedCheck_130_ = !lean_is_exclusive(v___x_41_);
if (v_isSharedCheck_130_ == 0)
{
v___x_125_ = v___x_41_;
v_isShared_126_ = v_isSharedCheck_130_;
goto v_resetjp_124_;
}
else
{
lean_inc(v_a_123_);
lean_dec(v___x_41_);
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
v_a_131_ = lean_ctor_get(v___x_39_, 0);
v_isSharedCheck_138_ = !lean_is_exclusive(v___x_39_);
if (v_isSharedCheck_138_ == 0)
{
v___x_133_ = v___x_39_;
v_isShared_134_ = v_isSharedCheck_138_;
goto v_resetjp_132_;
}
else
{
lean_inc(v_a_131_);
lean_dec(v___x_39_);
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
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_propagateNatBinOp_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_4_ = stack[0].m_obj;
lean_object* v_congrThmName_5_ = stack[1].m_obj;
lean_object* v_op_6_ = stack[2].m_obj;
lean_object* v_e_7_ = stack[3].m_obj;
lean_object* v_a_8_ = stack[4].m_obj;
lean_object* v_a_9_ = stack[5].m_obj;
lean_object* v_a_10_ = stack[6].m_obj;
lean_object* v_a_11_ = stack[7].m_obj;
lean_object* v_a_12_ = stack[8].m_obj;
lean_object* v_a_13_ = stack[9].m_obj;
lean_object* v_a_14_ = stack[10].m_obj;
lean_object* v_a_15_ = stack[11].m_obj;
lean_object* v_a_16_ = stack[12].m_obj;
lean_object* v_a_17_ = stack[13].m_obj;
lean_object* v_res_139_;
v_res_139_ = l_Lean_Meta_Grind_Arith_propagateNatBinOp(v_declName_4_, v_congrThmName_5_, v_op_6_, v_e_7_, v_a_8_, v_a_9_, v_a_10_, v_a_11_, v_a_12_, v_a_13_, v_a_14_, v_a_15_, v_a_16_, v_a_17_);
stack->m_obj
 = v_res_139_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_propagateNatBinOp___boxed(lean_object* v_declName_140_, lean_object* v_congrThmName_141_, lean_object* v_op_142_, lean_object* v_e_143_, lean_object* v_a_144_, lean_object* v_a_145_, lean_object* v_a_146_, lean_object* v_a_147_, lean_object* v_a_148_, lean_object* v_a_149_, lean_object* v_a_150_, lean_object* v_a_151_, lean_object* v_a_152_, lean_object* v_a_153_, lean_object* v_a_154_){
_start:
{
lean_object* v_res_155_; 
v_res_155_ = l_Lean_Meta_Grind_Arith_propagateNatBinOp(v_declName_140_, v_congrThmName_141_, v_op_142_, v_e_143_, v_a_144_, v_a_145_, v_a_146_, v_a_147_, v_a_148_, v_a_149_, v_a_150_, v_a_151_, v_a_152_, v_a_153_);
lean_dec(v_a_153_);
lean_dec_ref(v_a_152_);
lean_dec(v_a_151_);
lean_dec_ref(v_a_150_);
lean_dec(v_a_149_);
lean_dec_ref(v_a_148_);
lean_dec(v_a_147_);
lean_dec_ref(v_a_146_);
lean_dec(v_a_145_);
lean_dec(v_a_144_);
lean_dec(v_declName_140_);
return v_res_155_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_propagateNatAnd(lean_object* v_e_170_, lean_object* v_a_171_, lean_object* v_a_172_, lean_object* v_a_173_, lean_object* v_a_174_, lean_object* v_a_175_, lean_object* v_a_176_, lean_object* v_a_177_, lean_object* v_a_178_, lean_object* v_a_179_, lean_object* v_a_180_){
_start:
{
lean_object* v___f_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; 
v___f_182_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__0));
v___x_183_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__3));
v___x_184_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__7));
v___x_185_ = l_Lean_Meta_Grind_Arith_propagateNatBinOp(v___x_183_, v___x_184_, v___f_182_, v_e_170_, v_a_171_, v_a_172_, v_a_173_, v_a_174_, v_a_175_, v_a_176_, v_a_177_, v_a_178_, v_a_179_, v_a_180_);
return v___x_185_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_propagateNatAnd_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_170_ = stack[0].m_obj;
lean_object* v_a_171_ = stack[1].m_obj;
lean_object* v_a_172_ = stack[2].m_obj;
lean_object* v_a_173_ = stack[3].m_obj;
lean_object* v_a_174_ = stack[4].m_obj;
lean_object* v_a_175_ = stack[5].m_obj;
lean_object* v_a_176_ = stack[6].m_obj;
lean_object* v_a_177_ = stack[7].m_obj;
lean_object* v_a_178_ = stack[8].m_obj;
lean_object* v_a_179_ = stack[9].m_obj;
lean_object* v_a_180_ = stack[10].m_obj;
lean_object* v_res_186_;
v_res_186_ = l_Lean_Meta_Grind_Arith_propagateNatAnd(v_e_170_, v_a_171_, v_a_172_, v_a_173_, v_a_174_, v_a_175_, v_a_176_, v_a_177_, v_a_178_, v_a_179_, v_a_180_);
stack->m_obj
 = v_res_186_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_propagateNatAnd___boxed(lean_object* v_e_187_, lean_object* v_a_188_, lean_object* v_a_189_, lean_object* v_a_190_, lean_object* v_a_191_, lean_object* v_a_192_, lean_object* v_a_193_, lean_object* v_a_194_, lean_object* v_a_195_, lean_object* v_a_196_, lean_object* v_a_197_, lean_object* v_a_198_){
_start:
{
lean_object* v_res_199_; 
v_res_199_ = l_Lean_Meta_Grind_Arith_propagateNatAnd(v_e_187_, v_a_188_, v_a_189_, v_a_190_, v_a_191_, v_a_192_, v_a_193_, v_a_194_, v_a_195_, v_a_196_, v_a_197_);
lean_dec(v_a_197_);
lean_dec_ref(v_a_196_);
lean_dec(v_a_195_);
lean_dec_ref(v_a_194_);
lean_dec(v_a_193_);
lean_dec_ref(v_a_192_);
lean_dec(v_a_191_);
lean_dec_ref(v_a_190_);
lean_dec(v_a_189_);
lean_dec(v_a_188_);
return v_res_199_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_propagateNatAnd___regBuiltin_Lean_Meta_Grind_Arith_propagateNatAnd_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_1291761156____hygCtx___hyg_9_(){
_start:
{
lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; 
v___x_201_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_propagateNatAnd___closed__3));
v___x_202_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_propagateNatAnd___boxed), 12, 0);
v___x_203_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_201_, v___x_202_);
return v___x_203_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_propagateNatAnd___regBuiltin_Lean_Meta_Grind_Arith_propagateNatAnd_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_1291761156____hygCtx___hyg_9__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_204_;
v_res_204_ = l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_propagateNatAnd___regBuiltin_Lean_Meta_Grind_Arith_propagateNatAnd_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_1291761156____hygCtx___hyg_9_();
stack->m_obj
 = v_res_204_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_propagateNatAnd___regBuiltin_Lean_Meta_Grind_Arith_propagateNatAnd_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_1291761156____hygCtx___hyg_9____boxed(lean_object* v_a_205_){
_start:
{
lean_object* v_res_206_; 
v_res_206_ = l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_propagateNatAnd___regBuiltin_Lean_Meta_Grind_Arith_propagateNatAnd_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_1291761156____hygCtx___hyg_9_();
return v_res_206_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_propagateNatOr(lean_object* v_e_219_, lean_object* v_a_220_, lean_object* v_a_221_, lean_object* v_a_222_, lean_object* v_a_223_, lean_object* v_a_224_, lean_object* v_a_225_, lean_object* v_a_226_, lean_object* v_a_227_, lean_object* v_a_228_, lean_object* v_a_229_){
_start:
{
lean_object* v___f_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; 
v___f_231_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_propagateNatOr___closed__0));
v___x_232_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_propagateNatOr___closed__3));
v___x_233_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_propagateNatOr___closed__5));
v___x_234_ = l_Lean_Meta_Grind_Arith_propagateNatBinOp(v___x_232_, v___x_233_, v___f_231_, v_e_219_, v_a_220_, v_a_221_, v_a_222_, v_a_223_, v_a_224_, v_a_225_, v_a_226_, v_a_227_, v_a_228_, v_a_229_);
return v___x_234_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_propagateNatOr_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_219_ = stack[0].m_obj;
lean_object* v_a_220_ = stack[1].m_obj;
lean_object* v_a_221_ = stack[2].m_obj;
lean_object* v_a_222_ = stack[3].m_obj;
lean_object* v_a_223_ = stack[4].m_obj;
lean_object* v_a_224_ = stack[5].m_obj;
lean_object* v_a_225_ = stack[6].m_obj;
lean_object* v_a_226_ = stack[7].m_obj;
lean_object* v_a_227_ = stack[8].m_obj;
lean_object* v_a_228_ = stack[9].m_obj;
lean_object* v_a_229_ = stack[10].m_obj;
lean_object* v_res_235_;
v_res_235_ = l_Lean_Meta_Grind_Arith_propagateNatOr(v_e_219_, v_a_220_, v_a_221_, v_a_222_, v_a_223_, v_a_224_, v_a_225_, v_a_226_, v_a_227_, v_a_228_, v_a_229_);
stack->m_obj
 = v_res_235_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_propagateNatOr___boxed(lean_object* v_e_236_, lean_object* v_a_237_, lean_object* v_a_238_, lean_object* v_a_239_, lean_object* v_a_240_, lean_object* v_a_241_, lean_object* v_a_242_, lean_object* v_a_243_, lean_object* v_a_244_, lean_object* v_a_245_, lean_object* v_a_246_, lean_object* v_a_247_){
_start:
{
lean_object* v_res_248_; 
v_res_248_ = l_Lean_Meta_Grind_Arith_propagateNatOr(v_e_236_, v_a_237_, v_a_238_, v_a_239_, v_a_240_, v_a_241_, v_a_242_, v_a_243_, v_a_244_, v_a_245_, v_a_246_);
lean_dec(v_a_246_);
lean_dec_ref(v_a_245_);
lean_dec(v_a_244_);
lean_dec_ref(v_a_243_);
lean_dec(v_a_242_);
lean_dec_ref(v_a_241_);
lean_dec(v_a_240_);
lean_dec_ref(v_a_239_);
lean_dec(v_a_238_);
lean_dec(v_a_237_);
return v_res_248_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_propagateNatOr___regBuiltin_Lean_Meta_Grind_Arith_propagateNatOr_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_2834229635____hygCtx___hyg_9_(){
_start:
{
lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; 
v___x_250_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_propagateNatOr___closed__3));
v___x_251_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_propagateNatOr___boxed), 12, 0);
v___x_252_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_250_, v___x_251_);
return v___x_252_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_propagateNatOr___regBuiltin_Lean_Meta_Grind_Arith_propagateNatOr_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_2834229635____hygCtx___hyg_9__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_253_;
v_res_253_ = l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_propagateNatOr___regBuiltin_Lean_Meta_Grind_Arith_propagateNatOr_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_2834229635____hygCtx___hyg_9_();
stack->m_obj
 = v_res_253_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_propagateNatOr___regBuiltin_Lean_Meta_Grind_Arith_propagateNatOr_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_2834229635____hygCtx___hyg_9____boxed(lean_object* v_a_254_){
_start:
{
lean_object* v_res_255_; 
v_res_255_ = l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_propagateNatOr___regBuiltin_Lean_Meta_Grind_Arith_propagateNatOr_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_2834229635____hygCtx___hyg_9_();
return v_res_255_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_propagateNatXOr(lean_object* v_e_268_, lean_object* v_a_269_, lean_object* v_a_270_, lean_object* v_a_271_, lean_object* v_a_272_, lean_object* v_a_273_, lean_object* v_a_274_, lean_object* v_a_275_, lean_object* v_a_276_, lean_object* v_a_277_, lean_object* v_a_278_){
_start:
{
lean_object* v___f_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; 
v___f_280_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_propagateNatXOr___closed__0));
v___x_281_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_propagateNatXOr___closed__3));
v___x_282_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_propagateNatXOr___closed__5));
v___x_283_ = l_Lean_Meta_Grind_Arith_propagateNatBinOp(v___x_281_, v___x_282_, v___f_280_, v_e_268_, v_a_269_, v_a_270_, v_a_271_, v_a_272_, v_a_273_, v_a_274_, v_a_275_, v_a_276_, v_a_277_, v_a_278_);
return v___x_283_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_propagateNatXOr_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_268_ = stack[0].m_obj;
lean_object* v_a_269_ = stack[1].m_obj;
lean_object* v_a_270_ = stack[2].m_obj;
lean_object* v_a_271_ = stack[3].m_obj;
lean_object* v_a_272_ = stack[4].m_obj;
lean_object* v_a_273_ = stack[5].m_obj;
lean_object* v_a_274_ = stack[6].m_obj;
lean_object* v_a_275_ = stack[7].m_obj;
lean_object* v_a_276_ = stack[8].m_obj;
lean_object* v_a_277_ = stack[9].m_obj;
lean_object* v_a_278_ = stack[10].m_obj;
lean_object* v_res_284_;
v_res_284_ = l_Lean_Meta_Grind_Arith_propagateNatXOr(v_e_268_, v_a_269_, v_a_270_, v_a_271_, v_a_272_, v_a_273_, v_a_274_, v_a_275_, v_a_276_, v_a_277_, v_a_278_);
stack->m_obj
 = v_res_284_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_propagateNatXOr___boxed(lean_object* v_e_285_, lean_object* v_a_286_, lean_object* v_a_287_, lean_object* v_a_288_, lean_object* v_a_289_, lean_object* v_a_290_, lean_object* v_a_291_, lean_object* v_a_292_, lean_object* v_a_293_, lean_object* v_a_294_, lean_object* v_a_295_, lean_object* v_a_296_){
_start:
{
lean_object* v_res_297_; 
v_res_297_ = l_Lean_Meta_Grind_Arith_propagateNatXOr(v_e_285_, v_a_286_, v_a_287_, v_a_288_, v_a_289_, v_a_290_, v_a_291_, v_a_292_, v_a_293_, v_a_294_, v_a_295_);
lean_dec(v_a_295_);
lean_dec_ref(v_a_294_);
lean_dec(v_a_293_);
lean_dec_ref(v_a_292_);
lean_dec(v_a_291_);
lean_dec_ref(v_a_290_);
lean_dec(v_a_289_);
lean_dec_ref(v_a_288_);
lean_dec(v_a_287_);
lean_dec(v_a_286_);
return v_res_297_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_propagateNatXOr___regBuiltin_Lean_Meta_Grind_Arith_propagateNatXOr_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_3633575148____hygCtx___hyg_9_(){
_start:
{
lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; 
v___x_299_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_propagateNatXOr___closed__3));
v___x_300_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_propagateNatXOr___boxed), 12, 0);
v___x_301_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_299_, v___x_300_);
return v___x_301_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_propagateNatXOr___regBuiltin_Lean_Meta_Grind_Arith_propagateNatXOr_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_3633575148____hygCtx___hyg_9__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_302_;
v_res_302_ = l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_propagateNatXOr___regBuiltin_Lean_Meta_Grind_Arith_propagateNatXOr_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_3633575148____hygCtx___hyg_9_();
stack->m_obj
 = v_res_302_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_propagateNatXOr___regBuiltin_Lean_Meta_Grind_Arith_propagateNatXOr_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_3633575148____hygCtx___hyg_9____boxed(lean_object* v_a_303_){
_start:
{
lean_object* v_res_304_; 
v_res_304_ = l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_propagateNatXOr___regBuiltin_Lean_Meta_Grind_Arith_propagateNatXOr_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_3633575148____hygCtx___hyg_9_();
return v_res_304_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_propagateNatShiftLeft(lean_object* v_e_317_, lean_object* v_a_318_, lean_object* v_a_319_, lean_object* v_a_320_, lean_object* v_a_321_, lean_object* v_a_322_, lean_object* v_a_323_, lean_object* v_a_324_, lean_object* v_a_325_, lean_object* v_a_326_, lean_object* v_a_327_){
_start:
{
lean_object* v___f_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; 
v___f_329_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_propagateNatShiftLeft___closed__0));
v___x_330_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_propagateNatShiftLeft___closed__3));
v___x_331_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_propagateNatShiftLeft___closed__5));
v___x_332_ = l_Lean_Meta_Grind_Arith_propagateNatBinOp(v___x_330_, v___x_331_, v___f_329_, v_e_317_, v_a_318_, v_a_319_, v_a_320_, v_a_321_, v_a_322_, v_a_323_, v_a_324_, v_a_325_, v_a_326_, v_a_327_);
return v___x_332_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_propagateNatShiftLeft_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_317_ = stack[0].m_obj;
lean_object* v_a_318_ = stack[1].m_obj;
lean_object* v_a_319_ = stack[2].m_obj;
lean_object* v_a_320_ = stack[3].m_obj;
lean_object* v_a_321_ = stack[4].m_obj;
lean_object* v_a_322_ = stack[5].m_obj;
lean_object* v_a_323_ = stack[6].m_obj;
lean_object* v_a_324_ = stack[7].m_obj;
lean_object* v_a_325_ = stack[8].m_obj;
lean_object* v_a_326_ = stack[9].m_obj;
lean_object* v_a_327_ = stack[10].m_obj;
lean_object* v_res_333_;
v_res_333_ = l_Lean_Meta_Grind_Arith_propagateNatShiftLeft(v_e_317_, v_a_318_, v_a_319_, v_a_320_, v_a_321_, v_a_322_, v_a_323_, v_a_324_, v_a_325_, v_a_326_, v_a_327_);
stack->m_obj
 = v_res_333_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_propagateNatShiftLeft___boxed(lean_object* v_e_334_, lean_object* v_a_335_, lean_object* v_a_336_, lean_object* v_a_337_, lean_object* v_a_338_, lean_object* v_a_339_, lean_object* v_a_340_, lean_object* v_a_341_, lean_object* v_a_342_, lean_object* v_a_343_, lean_object* v_a_344_, lean_object* v_a_345_){
_start:
{
lean_object* v_res_346_; 
v_res_346_ = l_Lean_Meta_Grind_Arith_propagateNatShiftLeft(v_e_334_, v_a_335_, v_a_336_, v_a_337_, v_a_338_, v_a_339_, v_a_340_, v_a_341_, v_a_342_, v_a_343_, v_a_344_);
lean_dec(v_a_344_);
lean_dec_ref(v_a_343_);
lean_dec(v_a_342_);
lean_dec_ref(v_a_341_);
lean_dec(v_a_340_);
lean_dec_ref(v_a_339_);
lean_dec(v_a_338_);
lean_dec_ref(v_a_337_);
lean_dec(v_a_336_);
lean_dec(v_a_335_);
return v_res_346_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_propagateNatShiftLeft___regBuiltin_Lean_Meta_Grind_Arith_propagateNatShiftLeft_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_3253038636____hygCtx___hyg_9_(){
_start:
{
lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; 
v___x_348_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_propagateNatShiftLeft___closed__3));
v___x_349_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_propagateNatShiftLeft___boxed), 12, 0);
v___x_350_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_348_, v___x_349_);
return v___x_350_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_propagateNatShiftLeft___regBuiltin_Lean_Meta_Grind_Arith_propagateNatShiftLeft_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_3253038636____hygCtx___hyg_9__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_351_;
v_res_351_ = l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_propagateNatShiftLeft___regBuiltin_Lean_Meta_Grind_Arith_propagateNatShiftLeft_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_3253038636____hygCtx___hyg_9_();
stack->m_obj
 = v_res_351_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_propagateNatShiftLeft___regBuiltin_Lean_Meta_Grind_Arith_propagateNatShiftLeft_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_3253038636____hygCtx___hyg_9____boxed(lean_object* v_a_352_){
_start:
{
lean_object* v_res_353_; 
v_res_353_ = l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_propagateNatShiftLeft___regBuiltin_Lean_Meta_Grind_Arith_propagateNatShiftLeft_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_3253038636____hygCtx___hyg_9_();
return v_res_353_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_propagateNatShiftRight(lean_object* v_e_366_, lean_object* v_a_367_, lean_object* v_a_368_, lean_object* v_a_369_, lean_object* v_a_370_, lean_object* v_a_371_, lean_object* v_a_372_, lean_object* v_a_373_, lean_object* v_a_374_, lean_object* v_a_375_, lean_object* v_a_376_){
_start:
{
lean_object* v___f_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; 
v___f_378_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_propagateNatShiftRight___closed__0));
v___x_379_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_propagateNatShiftRight___closed__3));
v___x_380_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_propagateNatShiftRight___closed__5));
v___x_381_ = l_Lean_Meta_Grind_Arith_propagateNatBinOp(v___x_379_, v___x_380_, v___f_378_, v_e_366_, v_a_367_, v_a_368_, v_a_369_, v_a_370_, v_a_371_, v_a_372_, v_a_373_, v_a_374_, v_a_375_, v_a_376_);
return v___x_381_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_propagateNatShiftRight_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_366_ = stack[0].m_obj;
lean_object* v_a_367_ = stack[1].m_obj;
lean_object* v_a_368_ = stack[2].m_obj;
lean_object* v_a_369_ = stack[3].m_obj;
lean_object* v_a_370_ = stack[4].m_obj;
lean_object* v_a_371_ = stack[5].m_obj;
lean_object* v_a_372_ = stack[6].m_obj;
lean_object* v_a_373_ = stack[7].m_obj;
lean_object* v_a_374_ = stack[8].m_obj;
lean_object* v_a_375_ = stack[9].m_obj;
lean_object* v_a_376_ = stack[10].m_obj;
lean_object* v_res_382_;
v_res_382_ = l_Lean_Meta_Grind_Arith_propagateNatShiftRight(v_e_366_, v_a_367_, v_a_368_, v_a_369_, v_a_370_, v_a_371_, v_a_372_, v_a_373_, v_a_374_, v_a_375_, v_a_376_);
stack->m_obj
 = v_res_382_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_propagateNatShiftRight___boxed(lean_object* v_e_383_, lean_object* v_a_384_, lean_object* v_a_385_, lean_object* v_a_386_, lean_object* v_a_387_, lean_object* v_a_388_, lean_object* v_a_389_, lean_object* v_a_390_, lean_object* v_a_391_, lean_object* v_a_392_, lean_object* v_a_393_, lean_object* v_a_394_){
_start:
{
lean_object* v_res_395_; 
v_res_395_ = l_Lean_Meta_Grind_Arith_propagateNatShiftRight(v_e_383_, v_a_384_, v_a_385_, v_a_386_, v_a_387_, v_a_388_, v_a_389_, v_a_390_, v_a_391_, v_a_392_, v_a_393_);
lean_dec(v_a_393_);
lean_dec_ref(v_a_392_);
lean_dec(v_a_391_);
lean_dec_ref(v_a_390_);
lean_dec(v_a_389_);
lean_dec_ref(v_a_388_);
lean_dec(v_a_387_);
lean_dec_ref(v_a_386_);
lean_dec(v_a_385_);
lean_dec(v_a_384_);
return v_res_395_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_propagateNatShiftRight___regBuiltin_Lean_Meta_Grind_Arith_propagateNatShiftRight_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_1805815810____hygCtx___hyg_9_(){
_start:
{
lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; 
v___x_397_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_propagateNatShiftRight___closed__3));
v___x_398_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_propagateNatShiftRight___boxed), 12, 0);
v___x_399_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_397_, v___x_398_);
return v___x_399_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_propagateNatShiftRight___regBuiltin_Lean_Meta_Grind_Arith_propagateNatShiftRight_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_1805815810____hygCtx___hyg_9__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_400_;
v_res_400_ = l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_propagateNatShiftRight___regBuiltin_Lean_Meta_Grind_Arith_propagateNatShiftRight_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_1805815810____hygCtx___hyg_9_();
stack->m_obj
 = v_res_400_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_propagateNatShiftRight___regBuiltin_Lean_Meta_Grind_Arith_propagateNatShiftRight_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_1805815810____hygCtx___hyg_9____boxed(lean_object* v_a_401_){
_start:
{
lean_object* v_res_402_; 
v_res_402_ = l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_propagateNatShiftRight___regBuiltin_Lean_Meta_Grind_Arith_propagateNatShiftRight_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_1805815810____hygCtx___hyg_9_();
return v_res_402_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__1_spec__2_spec__4___redArg(lean_object* v_x_403_, lean_object* v_x_404_){
_start:
{
if (lean_obj_tag(v_x_404_) == 0)
{
return v_x_403_;
}
else
{
lean_object* v_key_405_; lean_object* v_value_406_; lean_object* v_tail_407_; lean_object* v___x_409_; uint8_t v_isShared_410_; uint8_t v_isSharedCheck_433_; 
v_key_405_ = lean_ctor_get(v_x_404_, 0);
v_value_406_ = lean_ctor_get(v_x_404_, 1);
v_tail_407_ = lean_ctor_get(v_x_404_, 2);
v_isSharedCheck_433_ = !lean_is_exclusive(v_x_404_);
if (v_isSharedCheck_433_ == 0)
{
v___x_409_ = v_x_404_;
v_isShared_410_ = v_isSharedCheck_433_;
goto v_resetjp_408_;
}
else
{
lean_inc(v_tail_407_);
lean_inc(v_value_406_);
lean_inc(v_key_405_);
lean_dec(v_x_404_);
v___x_409_ = lean_box(0);
v_isShared_410_ = v_isSharedCheck_433_;
goto v_resetjp_408_;
}
v_resetjp_408_:
{
lean_object* v___x_411_; uint64_t v___y_413_; 
v___x_411_ = lean_array_get_size(v_x_403_);
if (lean_obj_tag(v_key_405_) == 0)
{
uint64_t v___x_431_; 
v___x_431_ = 1723ULL;
v___y_413_ = v___x_431_;
goto v___jp_412_;
}
else
{
uint64_t v_hash_432_; 
v_hash_432_ = lean_ctor_get_uint64(v_key_405_, sizeof(void*)*2);
v___y_413_ = v_hash_432_;
goto v___jp_412_;
}
v___jp_412_:
{
uint64_t v___x_414_; uint64_t v___x_415_; uint64_t v_fold_416_; uint64_t v___x_417_; uint64_t v___x_418_; uint64_t v___x_419_; size_t v___x_420_; size_t v___x_421_; size_t v___x_422_; size_t v___x_423_; size_t v___x_424_; lean_object* v___x_425_; lean_object* v___x_427_; 
v___x_414_ = 32ULL;
v___x_415_ = lean_uint64_shift_right(v___y_413_, v___x_414_);
v_fold_416_ = lean_uint64_xor(v___y_413_, v___x_415_);
v___x_417_ = 16ULL;
v___x_418_ = lean_uint64_shift_right(v_fold_416_, v___x_417_);
v___x_419_ = lean_uint64_xor(v_fold_416_, v___x_418_);
v___x_420_ = lean_uint64_to_usize(v___x_419_);
v___x_421_ = lean_usize_of_nat(v___x_411_);
v___x_422_ = ((size_t)1ULL);
v___x_423_ = lean_usize_sub(v___x_421_, v___x_422_);
v___x_424_ = lean_usize_land(v___x_420_, v___x_423_);
v___x_425_ = lean_array_uget_borrowed(v_x_403_, v___x_424_);
lean_inc(v___x_425_);
if (v_isShared_410_ == 0)
{
lean_ctor_set(v___x_409_, 2, v___x_425_);
v___x_427_ = v___x_409_;
goto v_reusejp_426_;
}
else
{
lean_object* v_reuseFailAlloc_430_; 
v_reuseFailAlloc_430_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_430_, 0, v_key_405_);
lean_ctor_set(v_reuseFailAlloc_430_, 1, v_value_406_);
lean_ctor_set(v_reuseFailAlloc_430_, 2, v___x_425_);
v___x_427_ = v_reuseFailAlloc_430_;
goto v_reusejp_426_;
}
v_reusejp_426_:
{
lean_object* v___x_428_; 
v___x_428_ = lean_array_uset(v_x_403_, v___x_424_, v___x_427_);
v_x_403_ = v___x_428_;
v_x_404_ = v_tail_407_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__1_spec__2___redArg(lean_object* v_i_434_, lean_object* v_source_435_, lean_object* v_target_436_){
_start:
{
lean_object* v___x_437_; uint8_t v___x_438_; 
v___x_437_ = lean_array_get_size(v_source_435_);
v___x_438_ = lean_nat_dec_lt(v_i_434_, v___x_437_);
if (v___x_438_ == 0)
{
lean_dec_ref(v_source_435_);
lean_dec(v_i_434_);
return v_target_436_;
}
else
{
lean_object* v_es_439_; lean_object* v___x_440_; lean_object* v_source_441_; lean_object* v_target_442_; lean_object* v___x_443_; lean_object* v___x_444_; 
v_es_439_ = lean_array_fget(v_source_435_, v_i_434_);
v___x_440_ = lean_box(0);
v_source_441_ = lean_array_fset(v_source_435_, v_i_434_, v___x_440_);
v_target_442_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__1_spec__2_spec__4___redArg(v_target_436_, v_es_439_);
v___x_443_ = lean_unsigned_to_nat(1u);
v___x_444_ = lean_nat_add(v_i_434_, v___x_443_);
lean_dec(v_i_434_);
v_i_434_ = v___x_444_;
v_source_435_ = v_source_441_;
v_target_436_ = v_target_442_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__1___redArg(lean_object* v_data_446_){
_start:
{
lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v_nbuckets_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; 
v___x_447_ = lean_array_get_size(v_data_446_);
v___x_448_ = lean_unsigned_to_nat(2u);
v_nbuckets_449_ = lean_nat_mul(v___x_447_, v___x_448_);
v___x_450_ = lean_unsigned_to_nat(0u);
v___x_451_ = lean_box(0);
v___x_452_ = lean_mk_array(v_nbuckets_449_, v___x_451_);
v___x_453_ = lean_array_propagate_mark(v_data_446_, v___x_452_);
v___x_454_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__1_spec__2___redArg(v___x_450_, v_data_446_, v___x_453_);
return v___x_454_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__0___redArg(lean_object* v_a_455_, lean_object* v_x_456_){
_start:
{
if (lean_obj_tag(v_x_456_) == 0)
{
uint8_t v___x_457_; 
v___x_457_ = 0;
return v___x_457_;
}
else
{
lean_object* v_key_458_; lean_object* v_tail_459_; uint8_t v___x_460_; 
v_key_458_ = lean_ctor_get(v_x_456_, 0);
v_tail_459_ = lean_ctor_get(v_x_456_, 2);
v___x_460_ = lean_name_eq(v_key_458_, v_a_455_);
if (v___x_460_ == 0)
{
v_x_456_ = v_tail_459_;
goto _start;
}
else
{
return v___x_460_;
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_455_ = stack[0].m_obj;
lean_object* v_x_456_ = stack[1].m_obj;
uint8_t v_res_462_;
v_res_462_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__0___redArg(v_a_455_, v_x_456_);
stack->m_num = v_res_462_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__0___redArg___boxed(lean_object* v_a_463_, lean_object* v_x_464_){
_start:
{
uint8_t v_res_465_; lean_object* v_r_466_; 
v_res_465_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__0___redArg(v_a_463_, v_x_464_);
lean_dec(v_x_464_);
lean_dec(v_a_463_);
v_r_466_ = lean_box(v_res_465_);
return v_r_466_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0___redArg(lean_object* v_m_467_, lean_object* v_a_468_, lean_object* v_b_469_){
_start:
{
lean_object* v_size_470_; lean_object* v_buckets_471_; lean_object* v___x_472_; uint64_t v___y_474_; 
v_size_470_ = lean_ctor_get(v_m_467_, 0);
v_buckets_471_ = lean_ctor_get(v_m_467_, 1);
v___x_472_ = lean_array_get_size(v_buckets_471_);
if (lean_obj_tag(v_a_468_) == 0)
{
uint64_t v___x_511_; 
v___x_511_ = 1723ULL;
v___y_474_ = v___x_511_;
goto v___jp_473_;
}
else
{
uint64_t v_hash_512_; 
v_hash_512_ = lean_ctor_get_uint64(v_a_468_, sizeof(void*)*2);
v___y_474_ = v_hash_512_;
goto v___jp_473_;
}
v___jp_473_:
{
uint64_t v___x_475_; uint64_t v___x_476_; uint64_t v_fold_477_; uint64_t v___x_478_; uint64_t v___x_479_; uint64_t v___x_480_; size_t v___x_481_; size_t v___x_482_; size_t v___x_483_; size_t v___x_484_; size_t v___x_485_; lean_object* v_bkt_486_; uint8_t v___x_487_; 
v___x_475_ = 32ULL;
v___x_476_ = lean_uint64_shift_right(v___y_474_, v___x_475_);
v_fold_477_ = lean_uint64_xor(v___y_474_, v___x_476_);
v___x_478_ = 16ULL;
v___x_479_ = lean_uint64_shift_right(v_fold_477_, v___x_478_);
v___x_480_ = lean_uint64_xor(v_fold_477_, v___x_479_);
v___x_481_ = lean_uint64_to_usize(v___x_480_);
v___x_482_ = lean_usize_of_nat(v___x_472_);
v___x_483_ = ((size_t)1ULL);
v___x_484_ = lean_usize_sub(v___x_482_, v___x_483_);
v___x_485_ = lean_usize_land(v___x_481_, v___x_484_);
v_bkt_486_ = lean_array_uget_borrowed(v_buckets_471_, v___x_485_);
v___x_487_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__0___redArg(v_a_468_, v_bkt_486_);
if (v___x_487_ == 0)
{
lean_object* v___x_489_; uint8_t v_isShared_490_; uint8_t v_isSharedCheck_508_; 
lean_inc_ref(v_buckets_471_);
lean_inc(v_size_470_);
v_isSharedCheck_508_ = !lean_is_exclusive(v_m_467_);
if (v_isSharedCheck_508_ == 0)
{
lean_object* v_unused_509_; lean_object* v_unused_510_; 
v_unused_509_ = lean_ctor_get(v_m_467_, 1);
lean_dec(v_unused_509_);
v_unused_510_ = lean_ctor_get(v_m_467_, 0);
lean_dec(v_unused_510_);
v___x_489_ = v_m_467_;
v_isShared_490_ = v_isSharedCheck_508_;
goto v_resetjp_488_;
}
else
{
lean_dec(v_m_467_);
v___x_489_ = lean_box(0);
v_isShared_490_ = v_isSharedCheck_508_;
goto v_resetjp_488_;
}
v_resetjp_488_:
{
lean_object* v___x_491_; lean_object* v_size_x27_492_; lean_object* v___x_493_; lean_object* v_buckets_x27_494_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; uint8_t v___x_500_; 
v___x_491_ = lean_unsigned_to_nat(1u);
v_size_x27_492_ = lean_nat_add(v_size_470_, v___x_491_);
lean_dec(v_size_470_);
lean_inc(v_bkt_486_);
v___x_493_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_493_, 0, v_a_468_);
lean_ctor_set(v___x_493_, 1, v_b_469_);
lean_ctor_set(v___x_493_, 2, v_bkt_486_);
v_buckets_x27_494_ = lean_array_uset(v_buckets_471_, v___x_485_, v___x_493_);
v___x_495_ = lean_unsigned_to_nat(4u);
v___x_496_ = lean_nat_mul(v_size_x27_492_, v___x_495_);
v___x_497_ = lean_unsigned_to_nat(3u);
v___x_498_ = lean_nat_div(v___x_496_, v___x_497_);
lean_dec(v___x_496_);
v___x_499_ = lean_array_get_size(v_buckets_x27_494_);
v___x_500_ = lean_nat_dec_le(v___x_498_, v___x_499_);
lean_dec(v___x_498_);
if (v___x_500_ == 0)
{
lean_object* v_val_501_; lean_object* v___x_503_; 
v_val_501_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__1___redArg(v_buckets_x27_494_);
if (v_isShared_490_ == 0)
{
lean_ctor_set(v___x_489_, 1, v_val_501_);
lean_ctor_set(v___x_489_, 0, v_size_x27_492_);
v___x_503_ = v___x_489_;
goto v_reusejp_502_;
}
else
{
lean_object* v_reuseFailAlloc_504_; 
v_reuseFailAlloc_504_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_504_, 0, v_size_x27_492_);
lean_ctor_set(v_reuseFailAlloc_504_, 1, v_val_501_);
v___x_503_ = v_reuseFailAlloc_504_;
goto v_reusejp_502_;
}
v_reusejp_502_:
{
return v___x_503_;
}
}
else
{
lean_object* v___x_506_; 
if (v_isShared_490_ == 0)
{
lean_ctor_set(v___x_489_, 1, v_buckets_x27_494_);
lean_ctor_set(v___x_489_, 0, v_size_x27_492_);
v___x_506_ = v___x_489_;
goto v_reusejp_505_;
}
else
{
lean_object* v_reuseFailAlloc_507_; 
v_reuseFailAlloc_507_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_507_, 0, v_size_x27_492_);
lean_ctor_set(v_reuseFailAlloc_507_, 1, v_buckets_x27_494_);
v___x_506_ = v_reuseFailAlloc_507_;
goto v_reusejp_505_;
}
v_reusejp_505_:
{
return v___x_506_;
}
}
}
}
else
{
lean_dec(v_b_469_);
lean_dec(v_a_468_);
return v_m_467_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__1(lean_object* v_x_513_, lean_object* v_x_514_){
_start:
{
if (lean_obj_tag(v_x_514_) == 0)
{
return v_x_513_;
}
else
{
lean_object* v_head_515_; lean_object* v_tail_516_; lean_object* v___x_517_; lean_object* v___x_518_; 
v_head_515_ = lean_ctor_get(v_x_514_, 0);
lean_inc(v_head_515_);
v_tail_516_ = lean_ctor_get(v_x_514_, 1);
lean_inc(v_tail_516_);
lean_dec_ref_known(v_x_514_, 2);
v___x_517_ = lean_box(0);
v___x_518_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0___redArg(v_x_513_, v_head_515_, v___x_517_);
v_x_513_ = v___x_518_;
v_x_514_ = v_tail_516_;
goto _start;
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__0(void){
_start:
{
lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; 
v___x_520_ = lean_box(0);
v___x_521_ = lean_unsigned_to_nat(16u);
v___x_522_ = lean_mk_array(v___x_521_, v___x_520_);
return v___x_522_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__1(void){
_start:
{
lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; 
v___x_523_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__0);
v___x_524_ = lean_unsigned_to_nat(0u);
v___x_525_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_525_, 0, v___x_524_);
lean_ctor_set(v___x_525_, 1, v___x_523_);
return v___x_525_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__34(void){
_start:
{
lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; 
v___x_592_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__33));
v___x_593_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__1, &l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__1);
v___x_594_ = l_List_foldl___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__1(v___x_593_, v___x_592_);
return v___x_594_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring(void){
_start:
{
lean_object* v___x_595_; 
v___x_595_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__34, &l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__34_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring___closed__34);
return v___x_595_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0(lean_object* v_00_u03b2_596_, lean_object* v_m_597_, lean_object* v_a_598_, lean_object* v_b_599_){
_start:
{
lean_object* v___x_600_; 
v___x_600_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0___redArg(v_m_597_, v_a_598_, v_b_599_);
return v___x_600_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__0(lean_object* v_00_u03b2_601_, lean_object* v_a_602_, lean_object* v_x_603_){
_start:
{
uint8_t v___x_604_; 
v___x_604_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__0___redArg(v_a_602_, v_x_603_);
return v___x_604_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_602_ = stack[1].m_obj;
lean_object* v_x_603_ = stack[2].m_obj;
uint8_t v_res_605_;
v_res_605_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__0(lean_box(0), v_a_602_, v_x_603_);
stack->m_num = v_res_605_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__0___boxed(lean_object* v_00_u03b2_606_, lean_object* v_a_607_, lean_object* v_x_608_){
_start:
{
uint8_t v_res_609_; lean_object* v_r_610_; 
v_res_609_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__0(v_00_u03b2_606_, v_a_607_, v_x_608_);
lean_dec(v_x_608_);
lean_dec(v_a_607_);
v_r_610_ = lean_box(v_res_609_);
return v_r_610_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__1(lean_object* v_00_u03b2_611_, lean_object* v_data_612_){
_start:
{
lean_object* v___x_613_; 
v___x_613_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__1___redArg(v_data_612_);
return v___x_613_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_614_, lean_object* v_i_615_, lean_object* v_source_616_, lean_object* v_target_617_){
_start:
{
lean_object* v___x_618_; 
v___x_618_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__1_spec__2___redArg(v_i_615_, v_source_616_, v_target_617_);
return v___x_618_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_619_, lean_object* v_x_620_, lean_object* v_x_621_){
_start:
{
lean_object* v___x_622_; 
v___x_622_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__1_spec__2_spec__4___redArg(v_x_620_, v_x_621_);
return v___x_622_;
}
}
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isSupportedSemiringQuick_spec__0___redArg(lean_object* v_m_623_, lean_object* v_a_624_){
_start:
{
lean_object* v_buckets_625_; lean_object* v___x_626_; uint64_t v___y_628_; 
v_buckets_625_ = lean_ctor_get(v_m_623_, 1);
v___x_626_ = lean_array_get_size(v_buckets_625_);
if (lean_obj_tag(v_a_624_) == 0)
{
uint64_t v___x_642_; 
v___x_642_ = 1723ULL;
v___y_628_ = v___x_642_;
goto v___jp_627_;
}
else
{
uint64_t v_hash_643_; 
v_hash_643_ = lean_ctor_get_uint64(v_a_624_, sizeof(void*)*2);
v___y_628_ = v_hash_643_;
goto v___jp_627_;
}
v___jp_627_:
{
uint64_t v___x_629_; uint64_t v___x_630_; uint64_t v_fold_631_; uint64_t v___x_632_; uint64_t v___x_633_; uint64_t v___x_634_; size_t v___x_635_; size_t v___x_636_; size_t v___x_637_; size_t v___x_638_; size_t v___x_639_; lean_object* v___x_640_; uint8_t v___x_641_; 
v___x_629_ = 32ULL;
v___x_630_ = lean_uint64_shift_right(v___y_628_, v___x_629_);
v_fold_631_ = lean_uint64_xor(v___y_628_, v___x_630_);
v___x_632_ = 16ULL;
v___x_633_ = lean_uint64_shift_right(v_fold_631_, v___x_632_);
v___x_634_ = lean_uint64_xor(v_fold_631_, v___x_633_);
v___x_635_ = lean_uint64_to_usize(v___x_634_);
v___x_636_ = lean_usize_of_nat(v___x_626_);
v___x_637_ = ((size_t)1ULL);
v___x_638_ = lean_usize_sub(v___x_636_, v___x_637_);
v___x_639_ = lean_usize_land(v___x_635_, v___x_638_);
v___x_640_ = lean_array_uget_borrowed(v_buckets_625_, v___x_639_);
v___x_641_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring_spec__0_spec__0___redArg(v_a_624_, v___x_640_);
return v___x_641_;
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isSupportedSemiringQuick_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_623_ = stack[0].m_obj;
lean_object* v_a_624_ = stack[1].m_obj;
uint8_t v_res_644_;
v_res_644_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isSupportedSemiringQuick_spec__0___redArg(v_m_623_, v_a_624_);
stack->m_num = v_res_644_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isSupportedSemiringQuick_spec__0___redArg___boxed(lean_object* v_m_645_, lean_object* v_a_646_){
_start:
{
uint8_t v_res_647_; lean_object* v_r_648_; 
v_res_647_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isSupportedSemiringQuick_spec__0___redArg(v_m_645_, v_a_646_);
lean_dec(v_a_646_);
lean_dec_ref(v_m_645_);
v_r_648_ = lean_box(v_res_647_);
return v_r_648_;
}
}
uint8_t l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isSupportedSemiringQuick(lean_object* v_type_649_){
_start:
{
lean_object* v___x_650_; 
v___x_650_ = l_Lean_Expr_getAppFn(v_type_649_);
if (lean_obj_tag(v___x_650_) == 4)
{
lean_object* v_declName_651_; lean_object* v___x_652_; uint8_t v___x_653_; 
v_declName_651_ = lean_ctor_get(v___x_650_, 0);
lean_inc(v_declName_651_);
lean_dec_ref_known(v___x_650_, 2);
v___x_652_ = l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_supportedSemiring;
v___x_653_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isSupportedSemiringQuick_spec__0___redArg(v___x_652_, v_declName_651_);
lean_dec(v_declName_651_);
return v___x_653_;
}
else
{
uint8_t v___x_654_; 
lean_dec_ref(v___x_650_);
v___x_654_ = 0;
return v___x_654_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isSupportedSemiringQuick_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_649_ = stack[0].m_obj;
uint8_t v_res_655_;
v_res_655_ = l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isSupportedSemiringQuick(v_type_649_);
stack->m_num = v_res_655_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isSupportedSemiringQuick___boxed(lean_object* v_type_656_){
_start:
{
uint8_t v_res_657_; lean_object* v_r_658_; 
v_res_657_ = l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isSupportedSemiringQuick(v_type_656_);
lean_dec_ref(v_type_656_);
v_r_658_ = lean_box(v_res_657_);
return v_r_658_;
}
}
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isSupportedSemiringQuick_spec__0(lean_object* v_00_u03b2_659_, lean_object* v_m_660_, lean_object* v_a_661_){
_start:
{
uint8_t v___x_662_; 
v___x_662_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isSupportedSemiringQuick_spec__0___redArg(v_m_660_, v_a_661_);
return v___x_662_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isSupportedSemiringQuick_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_660_ = stack[1].m_obj;
lean_object* v_a_661_ = stack[2].m_obj;
uint8_t v_res_663_;
v_res_663_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isSupportedSemiringQuick_spec__0(lean_box(0), v_m_660_, v_a_661_);
stack->m_num = v_res_663_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isSupportedSemiringQuick_spec__0___boxed(lean_object* v_00_u03b2_664_, lean_object* v_m_665_, lean_object* v_a_666_){
_start:
{
uint8_t v_res_667_; lean_object* v_r_668_; 
v_res_667_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isSupportedSemiringQuick_spec__0(v_00_u03b2_664_, v_m_665_, v_a_666_);
lean_dec(v_a_666_);
lean_dec_ref(v_m_665_);
v_r_668_ = lean_box(v_res_667_);
return v_r_668_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isUnsupportedSemiring_x3f(lean_object* v_type_669_, lean_object* v_a_670_, lean_object* v_a_671_, lean_object* v_a_672_, lean_object* v_a_673_, lean_object* v_a_674_, lean_object* v_a_675_, lean_object* v_a_676_, lean_object* v_a_677_, lean_object* v_a_678_, lean_object* v_a_679_){
_start:
{
uint8_t v___x_681_; 
v___x_681_ = l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isSupportedSemiringQuick(v_type_669_);
if (v___x_681_ == 0)
{
lean_object* v___x_682_; 
lean_inc_ref(v_type_669_);
v___x_682_ = l_Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f___redArg(v_type_669_, v_a_674_, v_a_675_, v_a_676_, v_a_677_, v_a_678_, v_a_679_);
if (lean_obj_tag(v___x_682_) == 0)
{
lean_object* v_a_683_; lean_object* v___x_685_; uint8_t v_isShared_686_; uint8_t v_isSharedCheck_809_; 
v_a_683_ = lean_ctor_get(v___x_682_, 0);
v_isSharedCheck_809_ = !lean_is_exclusive(v___x_682_);
if (v_isSharedCheck_809_ == 0)
{
v___x_685_ = v___x_682_;
v_isShared_686_ = v_isSharedCheck_809_;
goto v_resetjp_684_;
}
else
{
lean_inc(v_a_683_);
lean_dec(v___x_682_);
v___x_685_ = lean_box(0);
v_isShared_686_ = v_isSharedCheck_809_;
goto v_resetjp_684_;
}
v_resetjp_684_:
{
if (lean_obj_tag(v_a_683_) == 0)
{
if (v___x_681_ == 0)
{
lean_object* v___x_692_; 
lean_del_object(v___x_685_);
lean_inc_ref(v_type_669_);
v___x_692_ = l_Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f___redArg(v_type_669_, v_a_674_, v_a_675_, v_a_676_, v_a_677_, v_a_678_, v_a_679_);
if (lean_obj_tag(v___x_692_) == 0)
{
lean_object* v_a_693_; 
v_a_693_ = lean_ctor_get(v___x_692_, 0);
lean_inc(v_a_693_);
lean_dec_ref_known(v___x_692_, 1);
if (lean_obj_tag(v_a_693_) == 1)
{
lean_object* v_val_694_; lean_object* v___x_696_; uint8_t v_isShared_697_; uint8_t v_isSharedCheck_720_; 
lean_dec_ref(v_type_669_);
v_val_694_ = lean_ctor_get(v_a_693_, 0);
v_isSharedCheck_720_ = !lean_is_exclusive(v_a_693_);
if (v_isSharedCheck_720_ == 0)
{
v___x_696_ = v_a_693_;
v_isShared_697_ = v_isSharedCheck_720_;
goto v_resetjp_695_;
}
else
{
lean_inc(v_val_694_);
lean_dec(v_a_693_);
v___x_696_ = lean_box(0);
v_isShared_697_ = v_isSharedCheck_720_;
goto v_resetjp_695_;
}
v_resetjp_695_:
{
lean_object* v___x_698_; 
v___x_698_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_getCommSemiring(v_val_694_, v_a_670_, v_a_671_, v_a_672_, v_a_673_, v_a_674_, v_a_675_, v_a_676_, v_a_677_, v_a_678_, v_a_679_);
lean_dec(v_val_694_);
if (lean_obj_tag(v___x_698_) == 0)
{
lean_object* v_a_699_; lean_object* v___x_701_; uint8_t v_isShared_702_; uint8_t v_isSharedCheck_711_; 
v_a_699_ = lean_ctor_get(v___x_698_, 0);
v_isSharedCheck_711_ = !lean_is_exclusive(v___x_698_);
if (v_isSharedCheck_711_ == 0)
{
v___x_701_ = v___x_698_;
v_isShared_702_ = v_isSharedCheck_711_;
goto v_resetjp_700_;
}
else
{
lean_inc(v_a_699_);
lean_dec(v___x_698_);
v___x_701_ = lean_box(0);
v_isShared_702_ = v_isSharedCheck_711_;
goto v_resetjp_700_;
}
v_resetjp_700_:
{
lean_object* v_toSemiring_703_; lean_object* v_semiringInst_704_; lean_object* v___x_706_; 
v_toSemiring_703_ = lean_ctor_get(v_a_699_, 0);
lean_inc_ref(v_toSemiring_703_);
lean_dec(v_a_699_);
v_semiringInst_704_ = lean_ctor_get(v_toSemiring_703_, 3);
lean_inc_ref(v_semiringInst_704_);
lean_dec_ref(v_toSemiring_703_);
if (v_isShared_697_ == 0)
{
lean_ctor_set(v___x_696_, 0, v_semiringInst_704_);
v___x_706_ = v___x_696_;
goto v_reusejp_705_;
}
else
{
lean_object* v_reuseFailAlloc_710_; 
v_reuseFailAlloc_710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_710_, 0, v_semiringInst_704_);
v___x_706_ = v_reuseFailAlloc_710_;
goto v_reusejp_705_;
}
v_reusejp_705_:
{
lean_object* v___x_708_; 
if (v_isShared_702_ == 0)
{
lean_ctor_set(v___x_701_, 0, v___x_706_);
v___x_708_ = v___x_701_;
goto v_reusejp_707_;
}
else
{
lean_object* v_reuseFailAlloc_709_; 
v_reuseFailAlloc_709_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_709_, 0, v___x_706_);
v___x_708_ = v_reuseFailAlloc_709_;
goto v_reusejp_707_;
}
v_reusejp_707_:
{
return v___x_708_;
}
}
}
}
else
{
lean_object* v_a_712_; lean_object* v___x_714_; uint8_t v_isShared_715_; uint8_t v_isSharedCheck_719_; 
lean_del_object(v___x_696_);
v_a_712_ = lean_ctor_get(v___x_698_, 0);
v_isSharedCheck_719_ = !lean_is_exclusive(v___x_698_);
if (v_isSharedCheck_719_ == 0)
{
v___x_714_ = v___x_698_;
v_isShared_715_ = v_isSharedCheck_719_;
goto v_resetjp_713_;
}
else
{
lean_inc(v_a_712_);
lean_dec(v___x_698_);
v___x_714_ = lean_box(0);
v_isShared_715_ = v_isSharedCheck_719_;
goto v_resetjp_713_;
}
v_resetjp_713_:
{
lean_object* v___x_717_; 
if (v_isShared_715_ == 0)
{
v___x_717_ = v___x_714_;
goto v_reusejp_716_;
}
else
{
lean_object* v_reuseFailAlloc_718_; 
v_reuseFailAlloc_718_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_718_, 0, v_a_712_);
v___x_717_ = v_reuseFailAlloc_718_;
goto v_reusejp_716_;
}
v_reusejp_716_:
{
return v___x_717_;
}
}
}
}
}
else
{
lean_object* v___x_721_; 
lean_dec(v_a_693_);
lean_inc_ref(v_type_669_);
v___x_721_ = l_Lean_Meta_Grind_Arith_CommRing_getNonCommRingId_x3f___redArg(v_type_669_, v_a_674_, v_a_675_, v_a_676_, v_a_677_, v_a_678_, v_a_679_);
if (lean_obj_tag(v___x_721_) == 0)
{
lean_object* v_a_722_; 
v_a_722_ = lean_ctor_get(v___x_721_, 0);
lean_inc(v_a_722_);
lean_dec_ref_known(v___x_721_, 1);
if (lean_obj_tag(v_a_722_) == 1)
{
lean_object* v_val_723_; lean_object* v___x_725_; uint8_t v_isShared_726_; uint8_t v_isSharedCheck_748_; 
lean_dec_ref(v_type_669_);
v_val_723_ = lean_ctor_get(v_a_722_, 0);
v_isSharedCheck_748_ = !lean_is_exclusive(v_a_722_);
if (v_isSharedCheck_748_ == 0)
{
v___x_725_ = v_a_722_;
v_isShared_726_ = v_isSharedCheck_748_;
goto v_resetjp_724_;
}
else
{
lean_inc(v_val_723_);
lean_dec(v_a_722_);
v___x_725_ = lean_box(0);
v_isShared_726_ = v_isSharedCheck_748_;
goto v_resetjp_724_;
}
v_resetjp_724_:
{
lean_object* v___x_727_; 
v___x_727_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing(v_val_723_, v_a_670_, v_a_671_, v_a_672_, v_a_673_, v_a_674_, v_a_675_, v_a_676_, v_a_677_, v_a_678_, v_a_679_);
lean_dec(v_val_723_);
if (lean_obj_tag(v___x_727_) == 0)
{
lean_object* v_a_728_; lean_object* v___x_730_; uint8_t v_isShared_731_; uint8_t v_isSharedCheck_739_; 
v_a_728_ = lean_ctor_get(v___x_727_, 0);
v_isSharedCheck_739_ = !lean_is_exclusive(v___x_727_);
if (v_isSharedCheck_739_ == 0)
{
v___x_730_ = v___x_727_;
v_isShared_731_ = v_isSharedCheck_739_;
goto v_resetjp_729_;
}
else
{
lean_inc(v_a_728_);
lean_dec(v___x_727_);
v___x_730_ = lean_box(0);
v_isShared_731_ = v_isSharedCheck_739_;
goto v_resetjp_729_;
}
v_resetjp_729_:
{
lean_object* v_semiringInst_732_; lean_object* v___x_734_; 
v_semiringInst_732_ = lean_ctor_get(v_a_728_, 4);
lean_inc_ref(v_semiringInst_732_);
lean_dec(v_a_728_);
if (v_isShared_726_ == 0)
{
lean_ctor_set(v___x_725_, 0, v_semiringInst_732_);
v___x_734_ = v___x_725_;
goto v_reusejp_733_;
}
else
{
lean_object* v_reuseFailAlloc_738_; 
v_reuseFailAlloc_738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_738_, 0, v_semiringInst_732_);
v___x_734_ = v_reuseFailAlloc_738_;
goto v_reusejp_733_;
}
v_reusejp_733_:
{
lean_object* v___x_736_; 
if (v_isShared_731_ == 0)
{
lean_ctor_set(v___x_730_, 0, v___x_734_);
v___x_736_ = v___x_730_;
goto v_reusejp_735_;
}
else
{
lean_object* v_reuseFailAlloc_737_; 
v_reuseFailAlloc_737_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_737_, 0, v___x_734_);
v___x_736_ = v_reuseFailAlloc_737_;
goto v_reusejp_735_;
}
v_reusejp_735_:
{
return v___x_736_;
}
}
}
}
else
{
lean_object* v_a_740_; lean_object* v___x_742_; uint8_t v_isShared_743_; uint8_t v_isSharedCheck_747_; 
lean_del_object(v___x_725_);
v_a_740_ = lean_ctor_get(v___x_727_, 0);
v_isSharedCheck_747_ = !lean_is_exclusive(v___x_727_);
if (v_isSharedCheck_747_ == 0)
{
v___x_742_ = v___x_727_;
v_isShared_743_ = v_isSharedCheck_747_;
goto v_resetjp_741_;
}
else
{
lean_inc(v_a_740_);
lean_dec(v___x_727_);
v___x_742_ = lean_box(0);
v_isShared_743_ = v_isSharedCheck_747_;
goto v_resetjp_741_;
}
v_resetjp_741_:
{
lean_object* v___x_745_; 
if (v_isShared_743_ == 0)
{
v___x_745_ = v___x_742_;
goto v_reusejp_744_;
}
else
{
lean_object* v_reuseFailAlloc_746_; 
v_reuseFailAlloc_746_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_746_, 0, v_a_740_);
v___x_745_ = v_reuseFailAlloc_746_;
goto v_reusejp_744_;
}
v_reusejp_744_:
{
return v___x_745_;
}
}
}
}
}
else
{
lean_object* v___x_749_; 
lean_dec(v_a_722_);
v___x_749_ = l_Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f___redArg(v_type_669_, v_a_674_, v_a_675_, v_a_676_, v_a_677_, v_a_678_, v_a_679_);
if (lean_obj_tag(v___x_749_) == 0)
{
lean_object* v_a_750_; lean_object* v___x_752_; uint8_t v_isShared_753_; uint8_t v_isSharedCheck_784_; 
v_a_750_ = lean_ctor_get(v___x_749_, 0);
v_isSharedCheck_784_ = !lean_is_exclusive(v___x_749_);
if (v_isSharedCheck_784_ == 0)
{
v___x_752_ = v___x_749_;
v_isShared_753_ = v_isSharedCheck_784_;
goto v_resetjp_751_;
}
else
{
lean_inc(v_a_750_);
lean_dec(v___x_749_);
v___x_752_ = lean_box(0);
v_isShared_753_ = v_isSharedCheck_784_;
goto v_resetjp_751_;
}
v_resetjp_751_:
{
if (lean_obj_tag(v_a_750_) == 1)
{
lean_object* v_val_754_; lean_object* v___x_756_; uint8_t v_isShared_757_; uint8_t v_isSharedCheck_779_; 
lean_del_object(v___x_752_);
v_val_754_ = lean_ctor_get(v_a_750_, 0);
v_isSharedCheck_779_ = !lean_is_exclusive(v_a_750_);
if (v_isSharedCheck_779_ == 0)
{
v___x_756_ = v_a_750_;
v_isShared_757_ = v_isSharedCheck_779_;
goto v_resetjp_755_;
}
else
{
lean_inc(v_val_754_);
lean_dec(v_a_750_);
v___x_756_ = lean_box(0);
v_isShared_757_ = v_isSharedCheck_779_;
goto v_resetjp_755_;
}
v_resetjp_755_:
{
lean_object* v___x_758_; 
v___x_758_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_getSemiring(v_val_754_, v_a_670_, v_a_671_, v_a_672_, v_a_673_, v_a_674_, v_a_675_, v_a_676_, v_a_677_, v_a_678_, v_a_679_);
lean_dec(v_val_754_);
if (lean_obj_tag(v___x_758_) == 0)
{
lean_object* v_a_759_; lean_object* v___x_761_; uint8_t v_isShared_762_; uint8_t v_isSharedCheck_770_; 
v_a_759_ = lean_ctor_get(v___x_758_, 0);
v_isSharedCheck_770_ = !lean_is_exclusive(v___x_758_);
if (v_isSharedCheck_770_ == 0)
{
v___x_761_ = v___x_758_;
v_isShared_762_ = v_isSharedCheck_770_;
goto v_resetjp_760_;
}
else
{
lean_inc(v_a_759_);
lean_dec(v___x_758_);
v___x_761_ = lean_box(0);
v_isShared_762_ = v_isSharedCheck_770_;
goto v_resetjp_760_;
}
v_resetjp_760_:
{
lean_object* v_semiringInst_763_; lean_object* v___x_765_; 
v_semiringInst_763_ = lean_ctor_get(v_a_759_, 3);
lean_inc_ref(v_semiringInst_763_);
lean_dec(v_a_759_);
if (v_isShared_757_ == 0)
{
lean_ctor_set(v___x_756_, 0, v_semiringInst_763_);
v___x_765_ = v___x_756_;
goto v_reusejp_764_;
}
else
{
lean_object* v_reuseFailAlloc_769_; 
v_reuseFailAlloc_769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_769_, 0, v_semiringInst_763_);
v___x_765_ = v_reuseFailAlloc_769_;
goto v_reusejp_764_;
}
v_reusejp_764_:
{
lean_object* v___x_767_; 
if (v_isShared_762_ == 0)
{
lean_ctor_set(v___x_761_, 0, v___x_765_);
v___x_767_ = v___x_761_;
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
lean_object* v_a_771_; lean_object* v___x_773_; uint8_t v_isShared_774_; uint8_t v_isSharedCheck_778_; 
lean_del_object(v___x_756_);
v_a_771_ = lean_ctor_get(v___x_758_, 0);
v_isSharedCheck_778_ = !lean_is_exclusive(v___x_758_);
if (v_isSharedCheck_778_ == 0)
{
v___x_773_ = v___x_758_;
v_isShared_774_ = v_isSharedCheck_778_;
goto v_resetjp_772_;
}
else
{
lean_inc(v_a_771_);
lean_dec(v___x_758_);
v___x_773_ = lean_box(0);
v_isShared_774_ = v_isSharedCheck_778_;
goto v_resetjp_772_;
}
v_resetjp_772_:
{
lean_object* v___x_776_; 
if (v_isShared_774_ == 0)
{
v___x_776_ = v___x_773_;
goto v_reusejp_775_;
}
else
{
lean_object* v_reuseFailAlloc_777_; 
v_reuseFailAlloc_777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_777_, 0, v_a_771_);
v___x_776_ = v_reuseFailAlloc_777_;
goto v_reusejp_775_;
}
v_reusejp_775_:
{
return v___x_776_;
}
}
}
}
}
else
{
lean_object* v___x_780_; lean_object* v___x_782_; 
lean_dec(v_a_750_);
v___x_780_ = lean_box(0);
if (v_isShared_753_ == 0)
{
lean_ctor_set(v___x_752_, 0, v___x_780_);
v___x_782_ = v___x_752_;
goto v_reusejp_781_;
}
else
{
lean_object* v_reuseFailAlloc_783_; 
v_reuseFailAlloc_783_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_783_, 0, v___x_780_);
v___x_782_ = v_reuseFailAlloc_783_;
goto v_reusejp_781_;
}
v_reusejp_781_:
{
return v___x_782_;
}
}
}
}
else
{
lean_object* v_a_785_; lean_object* v___x_787_; uint8_t v_isShared_788_; uint8_t v_isSharedCheck_792_; 
v_a_785_ = lean_ctor_get(v___x_749_, 0);
v_isSharedCheck_792_ = !lean_is_exclusive(v___x_749_);
if (v_isSharedCheck_792_ == 0)
{
v___x_787_ = v___x_749_;
v_isShared_788_ = v_isSharedCheck_792_;
goto v_resetjp_786_;
}
else
{
lean_inc(v_a_785_);
lean_dec(v___x_749_);
v___x_787_ = lean_box(0);
v_isShared_788_ = v_isSharedCheck_792_;
goto v_resetjp_786_;
}
v_resetjp_786_:
{
lean_object* v___x_790_; 
if (v_isShared_788_ == 0)
{
v___x_790_ = v___x_787_;
goto v_reusejp_789_;
}
else
{
lean_object* v_reuseFailAlloc_791_; 
v_reuseFailAlloc_791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_791_, 0, v_a_785_);
v___x_790_ = v_reuseFailAlloc_791_;
goto v_reusejp_789_;
}
v_reusejp_789_:
{
return v___x_790_;
}
}
}
}
}
else
{
lean_object* v_a_793_; lean_object* v___x_795_; uint8_t v_isShared_796_; uint8_t v_isSharedCheck_800_; 
lean_dec_ref(v_type_669_);
v_a_793_ = lean_ctor_get(v___x_721_, 0);
v_isSharedCheck_800_ = !lean_is_exclusive(v___x_721_);
if (v_isSharedCheck_800_ == 0)
{
v___x_795_ = v___x_721_;
v_isShared_796_ = v_isSharedCheck_800_;
goto v_resetjp_794_;
}
else
{
lean_inc(v_a_793_);
lean_dec(v___x_721_);
v___x_795_ = lean_box(0);
v_isShared_796_ = v_isSharedCheck_800_;
goto v_resetjp_794_;
}
v_resetjp_794_:
{
lean_object* v___x_798_; 
if (v_isShared_796_ == 0)
{
v___x_798_ = v___x_795_;
goto v_reusejp_797_;
}
else
{
lean_object* v_reuseFailAlloc_799_; 
v_reuseFailAlloc_799_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_799_, 0, v_a_793_);
v___x_798_ = v_reuseFailAlloc_799_;
goto v_reusejp_797_;
}
v_reusejp_797_:
{
return v___x_798_;
}
}
}
}
}
else
{
lean_object* v_a_801_; lean_object* v___x_803_; uint8_t v_isShared_804_; uint8_t v_isSharedCheck_808_; 
lean_dec_ref(v_type_669_);
v_a_801_ = lean_ctor_get(v___x_692_, 0);
v_isSharedCheck_808_ = !lean_is_exclusive(v___x_692_);
if (v_isSharedCheck_808_ == 0)
{
v___x_803_ = v___x_692_;
v_isShared_804_ = v_isSharedCheck_808_;
goto v_resetjp_802_;
}
else
{
lean_inc(v_a_801_);
lean_dec(v___x_692_);
v___x_803_ = lean_box(0);
v_isShared_804_ = v_isSharedCheck_808_;
goto v_resetjp_802_;
}
v_resetjp_802_:
{
lean_object* v___x_806_; 
if (v_isShared_804_ == 0)
{
v___x_806_ = v___x_803_;
goto v_reusejp_805_;
}
else
{
lean_object* v_reuseFailAlloc_807_; 
v_reuseFailAlloc_807_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_807_, 0, v_a_801_);
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
lean_dec_ref(v_type_669_);
goto v___jp_687_;
}
}
else
{
lean_dec_ref_known(v_a_683_, 1);
lean_dec_ref(v_type_669_);
goto v___jp_687_;
}
v___jp_687_:
{
lean_object* v___x_688_; lean_object* v___x_690_; 
v___x_688_ = lean_box(0);
if (v_isShared_686_ == 0)
{
lean_ctor_set(v___x_685_, 0, v___x_688_);
v___x_690_ = v___x_685_;
goto v_reusejp_689_;
}
else
{
lean_object* v_reuseFailAlloc_691_; 
v_reuseFailAlloc_691_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_691_, 0, v___x_688_);
v___x_690_ = v_reuseFailAlloc_691_;
goto v_reusejp_689_;
}
v_reusejp_689_:
{
return v___x_690_;
}
}
}
}
else
{
lean_object* v_a_810_; lean_object* v___x_812_; uint8_t v_isShared_813_; uint8_t v_isSharedCheck_817_; 
lean_dec_ref(v_type_669_);
v_a_810_ = lean_ctor_get(v___x_682_, 0);
v_isSharedCheck_817_ = !lean_is_exclusive(v___x_682_);
if (v_isSharedCheck_817_ == 0)
{
v___x_812_ = v___x_682_;
v_isShared_813_ = v_isSharedCheck_817_;
goto v_resetjp_811_;
}
else
{
lean_inc(v_a_810_);
lean_dec(v___x_682_);
v___x_812_ = lean_box(0);
v_isShared_813_ = v_isSharedCheck_817_;
goto v_resetjp_811_;
}
v_resetjp_811_:
{
lean_object* v___x_815_; 
if (v_isShared_813_ == 0)
{
v___x_815_ = v___x_812_;
goto v_reusejp_814_;
}
else
{
lean_object* v_reuseFailAlloc_816_; 
v_reuseFailAlloc_816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_816_, 0, v_a_810_);
v___x_815_ = v_reuseFailAlloc_816_;
goto v_reusejp_814_;
}
v_reusejp_814_:
{
return v___x_815_;
}
}
}
}
else
{
lean_object* v___x_818_; lean_object* v___x_819_; 
lean_dec_ref(v_type_669_);
v___x_818_ = lean_box(0);
v___x_819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_819_, 0, v___x_818_);
return v___x_819_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isUnsupportedSemiring_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_669_ = stack[0].m_obj;
lean_object* v_a_670_ = stack[1].m_obj;
lean_object* v_a_671_ = stack[2].m_obj;
lean_object* v_a_672_ = stack[3].m_obj;
lean_object* v_a_673_ = stack[4].m_obj;
lean_object* v_a_674_ = stack[5].m_obj;
lean_object* v_a_675_ = stack[6].m_obj;
lean_object* v_a_676_ = stack[7].m_obj;
lean_object* v_a_677_ = stack[8].m_obj;
lean_object* v_a_678_ = stack[9].m_obj;
lean_object* v_a_679_ = stack[10].m_obj;
lean_object* v_res_820_;
v_res_820_ = l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isUnsupportedSemiring_x3f(v_type_669_, v_a_670_, v_a_671_, v_a_672_, v_a_673_, v_a_674_, v_a_675_, v_a_676_, v_a_677_, v_a_678_, v_a_679_);
stack->m_obj
 = v_res_820_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isUnsupportedSemiring_x3f___boxed(lean_object* v_type_821_, lean_object* v_a_822_, lean_object* v_a_823_, lean_object* v_a_824_, lean_object* v_a_825_, lean_object* v_a_826_, lean_object* v_a_827_, lean_object* v_a_828_, lean_object* v_a_829_, lean_object* v_a_830_, lean_object* v_a_831_, lean_object* v_a_832_){
_start:
{
lean_object* v_res_833_; 
v_res_833_ = l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isUnsupportedSemiring_x3f(v_type_821_, v_a_822_, v_a_823_, v_a_824_, v_a_825_, v_a_826_, v_a_827_, v_a_828_, v_a_829_, v_a_830_, v_a_831_);
lean_dec(v_a_831_);
lean_dec_ref(v_a_830_);
lean_dec(v_a_829_);
lean_dec_ref(v_a_828_);
lean_dec(v_a_827_);
lean_dec_ref(v_a_826_);
lean_dec(v_a_825_);
lean_dec_ref(v_a_824_);
lean_dec(v_a_823_);
lean_dec(v_a_822_);
return v_res_833_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isOfNat_x3f(lean_object* v_a_839_, lean_object* v_a_840_, lean_object* v_a_841_, lean_object* v_a_842_, lean_object* v_a_843_){
_start:
{
lean_object* v___x_848_; uint8_t v___x_849_; 
v___x_848_ = l_Lean_Expr_cleanupAnnotations(v_a_839_);
v___x_849_ = l_Lean_Expr_isApp(v___x_848_);
if (v___x_849_ == 0)
{
lean_dec_ref(v___x_848_);
goto v___jp_845_;
}
else
{
lean_object* v___x_850_; uint8_t v___x_851_; 
v___x_850_ = l_Lean_Expr_appFnCleanup___redArg(v___x_848_);
v___x_851_ = l_Lean_Expr_isApp(v___x_850_);
if (v___x_851_ == 0)
{
lean_dec_ref(v___x_850_);
goto v___jp_845_;
}
else
{
lean_object* v_arg_852_; lean_object* v___x_853_; uint8_t v___x_854_; 
v_arg_852_ = lean_ctor_get(v___x_850_, 1);
lean_inc_ref(v_arg_852_);
v___x_853_ = l_Lean_Expr_appFnCleanup___redArg(v___x_850_);
v___x_854_ = l_Lean_Expr_isApp(v___x_853_);
if (v___x_854_ == 0)
{
lean_dec_ref(v___x_853_);
lean_dec_ref(v_arg_852_);
goto v___jp_845_;
}
else
{
lean_object* v___x_855_; lean_object* v___x_856_; uint8_t v___x_857_; 
v___x_855_ = l_Lean_Expr_appFnCleanup___redArg(v___x_853_);
v___x_856_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isOfNat_x3f___closed__2));
v___x_857_ = l_Lean_Expr_isConstOf(v___x_855_, v___x_856_);
lean_dec_ref(v___x_855_);
if (v___x_857_ == 0)
{
lean_dec_ref(v_arg_852_);
goto v___jp_845_;
}
else
{
lean_object* v___x_858_; 
v___x_858_ = l_Lean_Meta_getNatValue_x3f(v_arg_852_, v_a_840_, v_a_841_, v_a_842_, v_a_843_);
lean_dec_ref(v_arg_852_);
return v___x_858_;
}
}
}
}
v___jp_845_:
{
lean_object* v___x_846_; lean_object* v___x_847_; 
v___x_846_ = lean_box(0);
v___x_847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_847_, 0, v___x_846_);
return v___x_847_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isOfNat_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_839_ = stack[0].m_obj;
lean_object* v_a_840_ = stack[1].m_obj;
lean_object* v_a_841_ = stack[2].m_obj;
lean_object* v_a_842_ = stack[3].m_obj;
lean_object* v_a_843_ = stack[4].m_obj;
lean_object* v_res_859_;
v_res_859_ = l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isOfNat_x3f(v_a_839_, v_a_840_, v_a_841_, v_a_842_, v_a_843_);
stack->m_obj
 = v_res_859_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isOfNat_x3f___boxed(lean_object* v_a_860_, lean_object* v_a_861_, lean_object* v_a_862_, lean_object* v_a_863_, lean_object* v_a_864_, lean_object* v_a_865_){
_start:
{
lean_object* v_res_866_; 
v_res_866_ = l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isOfNat_x3f(v_a_860_, v_a_861_, v_a_862_, v_a_863_, v_a_864_);
lean_dec(v_a_864_);
lean_dec_ref(v_a_863_);
lean_dec(v_a_862_);
lean_dec_ref(v_a_861_);
return v_res_866_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_propagateMul(lean_object* v_e_897_, lean_object* v_a_898_, lean_object* v_a_899_, lean_object* v_a_900_, lean_object* v_a_901_, lean_object* v_a_902_, lean_object* v_a_903_, lean_object* v_a_904_, lean_object* v_a_905_, lean_object* v_a_906_, lean_object* v_a_907_){
_start:
{
lean_object* v___x_912_; uint8_t v___x_913_; 
lean_inc_ref(v_e_897_);
v___x_912_ = l_Lean_Expr_cleanupAnnotations(v_e_897_);
v___x_913_ = l_Lean_Expr_isApp(v___x_912_);
if (v___x_913_ == 0)
{
lean_dec_ref(v___x_912_);
lean_dec_ref(v_e_897_);
goto v___jp_909_;
}
else
{
lean_object* v_arg_914_; lean_object* v___x_915_; uint8_t v___x_916_; 
v_arg_914_ = lean_ctor_get(v___x_912_, 1);
lean_inc_ref(v_arg_914_);
v___x_915_ = l_Lean_Expr_appFnCleanup___redArg(v___x_912_);
v___x_916_ = l_Lean_Expr_isApp(v___x_915_);
if (v___x_916_ == 0)
{
lean_dec_ref(v___x_915_);
lean_dec_ref(v_arg_914_);
lean_dec_ref(v_e_897_);
goto v___jp_909_;
}
else
{
lean_object* v_arg_917_; lean_object* v___x_918_; uint8_t v___x_919_; 
v_arg_917_ = lean_ctor_get(v___x_915_, 1);
lean_inc_ref(v_arg_917_);
v___x_918_ = l_Lean_Expr_appFnCleanup___redArg(v___x_915_);
v___x_919_ = l_Lean_Expr_isApp(v___x_918_);
if (v___x_919_ == 0)
{
lean_dec_ref(v___x_918_);
lean_dec_ref(v_arg_917_);
lean_dec_ref(v_arg_914_);
lean_dec_ref(v_e_897_);
goto v___jp_909_;
}
else
{
lean_object* v___x_920_; uint8_t v___x_921_; 
v___x_920_ = l_Lean_Expr_appFnCleanup___redArg(v___x_918_);
v___x_921_ = l_Lean_Expr_isApp(v___x_920_);
if (v___x_921_ == 0)
{
lean_dec_ref(v___x_920_);
lean_dec_ref(v_arg_917_);
lean_dec_ref(v_arg_914_);
lean_dec_ref(v_e_897_);
goto v___jp_909_;
}
else
{
lean_object* v_arg_922_; lean_object* v___x_923_; uint8_t v___x_924_; 
v_arg_922_ = lean_ctor_get(v___x_920_, 1);
lean_inc_ref(v_arg_922_);
v___x_923_ = l_Lean_Expr_appFnCleanup___redArg(v___x_920_);
v___x_924_ = l_Lean_Expr_isApp(v___x_923_);
if (v___x_924_ == 0)
{
lean_dec_ref(v___x_923_);
lean_dec_ref(v_arg_922_);
lean_dec_ref(v_arg_917_);
lean_dec_ref(v_arg_914_);
lean_dec_ref(v_e_897_);
goto v___jp_909_;
}
else
{
lean_object* v_arg_925_; lean_object* v___x_926_; uint8_t v___x_927_; 
v_arg_925_ = lean_ctor_get(v___x_923_, 1);
lean_inc_ref(v_arg_925_);
v___x_926_ = l_Lean_Expr_appFnCleanup___redArg(v___x_923_);
v___x_927_ = l_Lean_Expr_isApp(v___x_926_);
if (v___x_927_ == 0)
{
lean_dec_ref(v___x_926_);
lean_dec_ref(v_arg_925_);
lean_dec_ref(v_arg_922_);
lean_dec_ref(v_arg_917_);
lean_dec_ref(v_arg_914_);
lean_dec_ref(v_e_897_);
goto v___jp_909_;
}
else
{
lean_object* v_arg_928_; lean_object* v___x_929_; lean_object* v___x_930_; uint8_t v___x_931_; 
v_arg_928_ = lean_ctor_get(v___x_926_, 1);
lean_inc_ref(v_arg_928_);
v___x_929_ = l_Lean_Expr_appFnCleanup___redArg(v___x_926_);
v___x_930_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_propagateMul___closed__2));
v___x_931_ = l_Lean_Expr_isConstOf(v___x_929_, v___x_930_);
if (v___x_931_ == 0)
{
lean_dec_ref(v___x_929_);
lean_dec_ref(v_arg_928_);
lean_dec_ref(v_arg_925_);
lean_dec_ref(v_arg_922_);
lean_dec_ref(v_arg_917_);
lean_dec_ref(v_arg_914_);
lean_dec_ref(v_e_897_);
goto v___jp_909_;
}
else
{
lean_object* v___x_932_; 
lean_inc_ref(v_arg_928_);
v___x_932_ = l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isUnsupportedSemiring_x3f(v_arg_928_, v_a_898_, v_a_899_, v_a_900_, v_a_901_, v_a_902_, v_a_903_, v_a_904_, v_a_905_, v_a_906_, v_a_907_);
if (lean_obj_tag(v___x_932_) == 0)
{
lean_object* v_a_933_; lean_object* v___x_935_; uint8_t v_isShared_936_; uint8_t v_isSharedCheck_1111_; 
v_a_933_ = lean_ctor_get(v___x_932_, 0);
v_isSharedCheck_1111_ = !lean_is_exclusive(v___x_932_);
if (v_isSharedCheck_1111_ == 0)
{
v___x_935_ = v___x_932_;
v_isShared_936_ = v_isSharedCheck_1111_;
goto v_resetjp_934_;
}
else
{
lean_inc(v_a_933_);
lean_dec(v___x_932_);
v___x_935_ = lean_box(0);
v_isShared_936_ = v_isSharedCheck_1111_;
goto v_resetjp_934_;
}
v_resetjp_934_:
{
if (lean_obj_tag(v_a_933_) == 1)
{
lean_object* v_val_942_; lean_object* v___x_944_; uint8_t v_isShared_945_; uint8_t v_isSharedCheck_1108_; 
v_val_942_ = lean_ctor_get(v_a_933_, 0);
v_isSharedCheck_1108_ = !lean_is_exclusive(v_a_933_);
if (v_isSharedCheck_1108_ == 0)
{
v___x_944_ = v_a_933_;
v_isShared_945_ = v_isSharedCheck_1108_;
goto v_resetjp_943_;
}
else
{
lean_inc(v_val_942_);
lean_dec(v_a_933_);
v___x_944_ = lean_box(0);
v_isShared_945_ = v_isSharedCheck_1108_;
goto v_resetjp_943_;
}
v_resetjp_943_:
{
size_t v___x_946_; size_t v___x_947_; uint8_t v___x_948_; 
v___x_946_ = lean_ptr_addr(v_arg_928_);
v___x_947_ = lean_ptr_addr(v_arg_925_);
lean_dec_ref(v_arg_925_);
v___x_948_ = lean_usize_dec_eq(v___x_946_, v___x_947_);
if (v___x_948_ == 0)
{
lean_del_object(v___x_944_);
lean_dec(v_val_942_);
lean_dec_ref(v___x_929_);
lean_dec_ref(v_arg_928_);
lean_dec_ref(v_arg_922_);
lean_dec_ref(v_arg_917_);
lean_dec_ref(v_arg_914_);
lean_dec_ref(v_e_897_);
goto v___jp_937_;
}
else
{
size_t v___x_949_; uint8_t v___x_950_; 
v___x_949_ = lean_ptr_addr(v_arg_922_);
lean_dec_ref(v_arg_922_);
v___x_950_ = lean_usize_dec_eq(v___x_946_, v___x_949_);
if (v___x_950_ == 0)
{
lean_del_object(v___x_944_);
lean_dec(v_val_942_);
lean_dec_ref(v___x_929_);
lean_dec_ref(v_arg_928_);
lean_dec_ref(v_arg_917_);
lean_dec_ref(v_arg_914_);
lean_dec_ref(v_e_897_);
goto v___jp_937_;
}
else
{
lean_object* v___x_951_; 
lean_del_object(v___x_935_);
v___x_951_ = l_Lean_Expr_constLevels_x21(v___x_929_);
lean_dec_ref(v___x_929_);
if (lean_obj_tag(v___x_951_) == 1)
{
lean_object* v_head_952_; lean_object* v___x_954_; uint8_t v_isShared_955_; uint8_t v_isSharedCheck_1102_; 
lean_del_object(v___x_944_);
v_head_952_ = lean_ctor_get(v___x_951_, 0);
v_isSharedCheck_1102_ = !lean_is_exclusive(v___x_951_);
if (v_isSharedCheck_1102_ == 0)
{
lean_object* v_unused_1103_; 
v_unused_1103_ = lean_ctor_get(v___x_951_, 1);
lean_dec(v_unused_1103_);
v___x_954_ = v___x_951_;
v_isShared_955_ = v_isSharedCheck_1102_;
goto v_resetjp_953_;
}
else
{
lean_inc(v_head_952_);
lean_dec(v___x_951_);
v___x_954_ = lean_box(0);
v_isShared_955_ = v_isSharedCheck_1102_;
goto v_resetjp_953_;
}
v_resetjp_953_:
{
lean_object* v___x_956_; lean_object* v___x_957_; 
v___x_956_ = lean_st_ref_get(v_a_898_);
lean_inc_ref(v_arg_917_);
v___x_957_ = l_Lean_Meta_Grind_Goal_getRoot(v___x_956_, v_arg_917_, v_a_904_, v_a_905_, v_a_906_, v_a_907_);
lean_dec(v___x_956_);
if (lean_obj_tag(v___x_957_) == 0)
{
lean_object* v_a_958_; lean_object* v___x_959_; lean_object* v___x_960_; 
v_a_958_ = lean_ctor_get(v___x_957_, 0);
lean_inc(v_a_958_);
lean_dec_ref_known(v___x_957_, 1);
v___x_959_ = lean_st_ref_get(v_a_898_);
lean_inc_ref(v_arg_914_);
v___x_960_ = l_Lean_Meta_Grind_Goal_getRoot(v___x_959_, v_arg_914_, v_a_904_, v_a_905_, v_a_906_, v_a_907_);
lean_dec(v___x_959_);
if (lean_obj_tag(v___x_960_) == 0)
{
lean_object* v_a_961_; lean_object* v___x_962_; 
v_a_961_ = lean_ctor_get(v___x_960_, 0);
lean_inc(v_a_961_);
lean_dec_ref_known(v___x_960_, 1);
lean_inc(v_a_958_);
v___x_962_ = l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isOfNat_x3f(v_a_958_, v_a_904_, v_a_905_, v_a_906_, v_a_907_);
if (lean_obj_tag(v___x_962_) == 0)
{
lean_object* v_a_963_; lean_object* v___x_965_; uint8_t v_isShared_966_; uint8_t v_isSharedCheck_1077_; 
v_a_963_ = lean_ctor_get(v___x_962_, 0);
v_isSharedCheck_1077_ = !lean_is_exclusive(v___x_962_);
if (v_isSharedCheck_1077_ == 0)
{
v___x_965_ = v___x_962_;
v_isShared_966_ = v_isSharedCheck_1077_;
goto v_resetjp_964_;
}
else
{
lean_inc(v_a_963_);
lean_dec(v___x_962_);
v___x_965_ = lean_box(0);
v_isShared_966_ = v_isSharedCheck_1077_;
goto v_resetjp_964_;
}
v_resetjp_964_:
{
if (lean_obj_tag(v_a_963_) == 1)
{
lean_object* v_val_967_; lean_object* v___x_968_; uint8_t v___x_969_; 
lean_dec(v_a_961_);
v_val_967_ = lean_ctor_get(v_a_963_, 0);
lean_inc(v_val_967_);
lean_dec_ref_known(v_a_963_, 1);
v___x_968_ = lean_unsigned_to_nat(0u);
v___x_969_ = lean_nat_dec_eq(v_val_967_, v___x_968_);
if (v___x_969_ == 0)
{
lean_object* v___x_970_; uint8_t v___x_971_; 
v___x_970_ = lean_unsigned_to_nat(1u);
v___x_971_ = lean_nat_dec_eq(v_val_967_, v___x_970_);
lean_dec(v_val_967_);
if (v___x_971_ == 0)
{
lean_object* v___x_972_; lean_object* v___x_974_; 
lean_dec(v_a_958_);
lean_del_object(v___x_954_);
lean_dec(v_head_952_);
lean_dec(v_val_942_);
lean_dec_ref(v_arg_928_);
lean_dec_ref(v_arg_917_);
lean_dec_ref(v_arg_914_);
lean_dec_ref(v_e_897_);
v___x_972_ = lean_box(0);
if (v_isShared_966_ == 0)
{
lean_ctor_set(v___x_965_, 0, v___x_972_);
v___x_974_ = v___x_965_;
goto v_reusejp_973_;
}
else
{
lean_object* v_reuseFailAlloc_975_; 
v_reuseFailAlloc_975_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_975_, 0, v___x_972_);
v___x_974_ = v_reuseFailAlloc_975_;
goto v_reusejp_973_;
}
v_reusejp_973_:
{
return v___x_974_;
}
}
else
{
lean_object* v___x_976_; 
lean_del_object(v___x_965_);
lean_inc(v_a_907_);
lean_inc_ref(v_a_906_);
lean_inc(v_a_905_);
lean_inc_ref(v_a_904_);
lean_inc(v_a_903_);
lean_inc_ref(v_a_902_);
lean_inc(v_a_901_);
lean_inc_ref(v_a_900_);
lean_inc(v_a_899_);
lean_inc(v_a_898_);
lean_inc_ref(v_arg_917_);
v___x_976_ = lean_grind_mk_eq_proof(v_arg_917_, v_a_958_, v_a_898_, v_a_899_, v_a_900_, v_a_901_, v_a_902_, v_a_903_, v_a_904_, v_a_905_, v_a_906_, v_a_907_);
if (lean_obj_tag(v___x_976_) == 0)
{
lean_object* v_a_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_981_; 
v_a_977_ = lean_ctor_get(v___x_976_, 0);
lean_inc(v_a_977_);
lean_dec_ref_known(v___x_976_, 1);
v___x_978_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_propagateMul___closed__5));
v___x_979_ = lean_box(0);
if (v_isShared_955_ == 0)
{
lean_ctor_set(v___x_954_, 1, v___x_979_);
v___x_981_ = v___x_954_;
goto v_reusejp_980_;
}
else
{
lean_object* v_reuseFailAlloc_985_; 
v_reuseFailAlloc_985_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_985_, 0, v_head_952_);
lean_ctor_set(v_reuseFailAlloc_985_, 1, v___x_979_);
v___x_981_ = v_reuseFailAlloc_985_;
goto v_reusejp_980_;
}
v_reusejp_980_:
{
lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; 
v___x_982_ = l_Lean_mkConst(v___x_978_, v___x_981_);
lean_inc_ref(v_arg_914_);
v___x_983_ = l_Lean_mkApp5(v___x_982_, v_arg_928_, v_val_942_, v_arg_917_, v_arg_914_, v_a_977_);
v___x_984_ = l_Lean_Meta_Grind_pushEqCore___redArg(v_e_897_, v_arg_914_, v___x_983_, v___x_969_, v_a_898_, v_a_900_, v_a_904_, v_a_905_, v_a_906_, v_a_907_);
return v___x_984_;
}
}
else
{
lean_object* v_a_986_; lean_object* v___x_988_; uint8_t v_isShared_989_; uint8_t v_isSharedCheck_993_; 
lean_del_object(v___x_954_);
lean_dec(v_head_952_);
lean_dec(v_val_942_);
lean_dec_ref(v_arg_928_);
lean_dec_ref(v_arg_917_);
lean_dec_ref(v_arg_914_);
lean_dec_ref(v_e_897_);
v_a_986_ = lean_ctor_get(v___x_976_, 0);
v_isSharedCheck_993_ = !lean_is_exclusive(v___x_976_);
if (v_isSharedCheck_993_ == 0)
{
v___x_988_ = v___x_976_;
v_isShared_989_ = v_isSharedCheck_993_;
goto v_resetjp_987_;
}
else
{
lean_inc(v_a_986_);
lean_dec(v___x_976_);
v___x_988_ = lean_box(0);
v_isShared_989_ = v_isSharedCheck_993_;
goto v_resetjp_987_;
}
v_resetjp_987_:
{
lean_object* v___x_991_; 
if (v_isShared_989_ == 0)
{
v___x_991_ = v___x_988_;
goto v_reusejp_990_;
}
else
{
lean_object* v_reuseFailAlloc_992_; 
v_reuseFailAlloc_992_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_992_, 0, v_a_986_);
v___x_991_ = v_reuseFailAlloc_992_;
goto v_reusejp_990_;
}
v_reusejp_990_:
{
return v___x_991_;
}
}
}
}
}
else
{
lean_object* v___x_994_; 
lean_dec(v_val_967_);
lean_del_object(v___x_965_);
lean_inc(v_a_907_);
lean_inc_ref(v_a_906_);
lean_inc(v_a_905_);
lean_inc_ref(v_a_904_);
lean_inc(v_a_903_);
lean_inc_ref(v_a_902_);
lean_inc(v_a_901_);
lean_inc_ref(v_a_900_);
lean_inc(v_a_899_);
lean_inc(v_a_898_);
lean_inc(v_a_958_);
lean_inc_ref(v_arg_917_);
v___x_994_ = lean_grind_mk_eq_proof(v_arg_917_, v_a_958_, v_a_898_, v_a_899_, v_a_900_, v_a_901_, v_a_902_, v_a_903_, v_a_904_, v_a_905_, v_a_906_, v_a_907_);
if (lean_obj_tag(v___x_994_) == 0)
{
lean_object* v_a_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_999_; 
v_a_995_ = lean_ctor_get(v___x_994_, 0);
lean_inc(v_a_995_);
lean_dec_ref_known(v___x_994_, 1);
v___x_996_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_propagateMul___closed__7));
v___x_997_ = lean_box(0);
if (v_isShared_955_ == 0)
{
lean_ctor_set(v___x_954_, 1, v___x_997_);
v___x_999_ = v___x_954_;
goto v_reusejp_998_;
}
else
{
lean_object* v_reuseFailAlloc_1004_; 
v_reuseFailAlloc_1004_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1004_, 0, v_head_952_);
lean_ctor_set(v_reuseFailAlloc_1004_, 1, v___x_997_);
v___x_999_ = v_reuseFailAlloc_1004_;
goto v_reusejp_998_;
}
v_reusejp_998_:
{
lean_object* v___x_1000_; lean_object* v___x_1001_; uint8_t v___x_1002_; lean_object* v___x_1003_; 
v___x_1000_ = l_Lean_mkConst(v___x_996_, v___x_999_);
v___x_1001_ = l_Lean_mkApp5(v___x_1000_, v_arg_928_, v_val_942_, v_arg_917_, v_arg_914_, v_a_995_);
v___x_1002_ = 0;
v___x_1003_ = l_Lean_Meta_Grind_pushEqCore___redArg(v_e_897_, v_a_958_, v___x_1001_, v___x_1002_, v_a_898_, v_a_900_, v_a_904_, v_a_905_, v_a_906_, v_a_907_);
return v___x_1003_;
}
}
else
{
lean_object* v_a_1005_; lean_object* v___x_1007_; uint8_t v_isShared_1008_; uint8_t v_isSharedCheck_1012_; 
lean_dec(v_a_958_);
lean_del_object(v___x_954_);
lean_dec(v_head_952_);
lean_dec(v_val_942_);
lean_dec_ref(v_arg_928_);
lean_dec_ref(v_arg_917_);
lean_dec_ref(v_arg_914_);
lean_dec_ref(v_e_897_);
v_a_1005_ = lean_ctor_get(v___x_994_, 0);
v_isSharedCheck_1012_ = !lean_is_exclusive(v___x_994_);
if (v_isSharedCheck_1012_ == 0)
{
v___x_1007_ = v___x_994_;
v_isShared_1008_ = v_isSharedCheck_1012_;
goto v_resetjp_1006_;
}
else
{
lean_inc(v_a_1005_);
lean_dec(v___x_994_);
v___x_1007_ = lean_box(0);
v_isShared_1008_ = v_isSharedCheck_1012_;
goto v_resetjp_1006_;
}
v_resetjp_1006_:
{
lean_object* v___x_1010_; 
if (v_isShared_1008_ == 0)
{
v___x_1010_ = v___x_1007_;
goto v_reusejp_1009_;
}
else
{
lean_object* v_reuseFailAlloc_1011_; 
v_reuseFailAlloc_1011_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1011_, 0, v_a_1005_);
v___x_1010_ = v_reuseFailAlloc_1011_;
goto v_reusejp_1009_;
}
v_reusejp_1009_:
{
return v___x_1010_;
}
}
}
}
}
else
{
lean_object* v___x_1013_; 
lean_del_object(v___x_965_);
lean_dec(v_a_963_);
lean_dec(v_a_958_);
lean_inc(v_a_961_);
v___x_1013_ = l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_isOfNat_x3f(v_a_961_, v_a_904_, v_a_905_, v_a_906_, v_a_907_);
if (lean_obj_tag(v___x_1013_) == 0)
{
lean_object* v_a_1014_; lean_object* v___x_1016_; uint8_t v_isShared_1017_; uint8_t v_isSharedCheck_1068_; 
v_a_1014_ = lean_ctor_get(v___x_1013_, 0);
v_isSharedCheck_1068_ = !lean_is_exclusive(v___x_1013_);
if (v_isSharedCheck_1068_ == 0)
{
v___x_1016_ = v___x_1013_;
v_isShared_1017_ = v_isSharedCheck_1068_;
goto v_resetjp_1015_;
}
else
{
lean_inc(v_a_1014_);
lean_dec(v___x_1013_);
v___x_1016_ = lean_box(0);
v_isShared_1017_ = v_isSharedCheck_1068_;
goto v_resetjp_1015_;
}
v_resetjp_1015_:
{
if (lean_obj_tag(v_a_1014_) == 1)
{
lean_object* v_val_1018_; lean_object* v___x_1019_; uint8_t v___x_1020_; 
v_val_1018_ = lean_ctor_get(v_a_1014_, 0);
lean_inc(v_val_1018_);
lean_dec_ref_known(v_a_1014_, 1);
v___x_1019_ = lean_unsigned_to_nat(0u);
v___x_1020_ = lean_nat_dec_eq(v_val_1018_, v___x_1019_);
if (v___x_1020_ == 0)
{
lean_object* v___x_1021_; uint8_t v___x_1022_; 
v___x_1021_ = lean_unsigned_to_nat(1u);
v___x_1022_ = lean_nat_dec_eq(v_val_1018_, v___x_1021_);
lean_dec(v_val_1018_);
if (v___x_1022_ == 0)
{
lean_object* v___x_1023_; lean_object* v___x_1025_; 
lean_dec(v_a_961_);
lean_del_object(v___x_954_);
lean_dec(v_head_952_);
lean_dec(v_val_942_);
lean_dec_ref(v_arg_928_);
lean_dec_ref(v_arg_917_);
lean_dec_ref(v_arg_914_);
lean_dec_ref(v_e_897_);
v___x_1023_ = lean_box(0);
if (v_isShared_1017_ == 0)
{
lean_ctor_set(v___x_1016_, 0, v___x_1023_);
v___x_1025_ = v___x_1016_;
goto v_reusejp_1024_;
}
else
{
lean_object* v_reuseFailAlloc_1026_; 
v_reuseFailAlloc_1026_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1026_, 0, v___x_1023_);
v___x_1025_ = v_reuseFailAlloc_1026_;
goto v_reusejp_1024_;
}
v_reusejp_1024_:
{
return v___x_1025_;
}
}
else
{
lean_object* v___x_1027_; 
lean_del_object(v___x_1016_);
lean_inc(v_a_907_);
lean_inc_ref(v_a_906_);
lean_inc(v_a_905_);
lean_inc_ref(v_a_904_);
lean_inc(v_a_903_);
lean_inc_ref(v_a_902_);
lean_inc(v_a_901_);
lean_inc_ref(v_a_900_);
lean_inc(v_a_899_);
lean_inc(v_a_898_);
lean_inc_ref(v_arg_914_);
v___x_1027_ = lean_grind_mk_eq_proof(v_arg_914_, v_a_961_, v_a_898_, v_a_899_, v_a_900_, v_a_901_, v_a_902_, v_a_903_, v_a_904_, v_a_905_, v_a_906_, v_a_907_);
if (lean_obj_tag(v___x_1027_) == 0)
{
lean_object* v_a_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1032_; 
v_a_1028_ = lean_ctor_get(v___x_1027_, 0);
lean_inc(v_a_1028_);
lean_dec_ref_known(v___x_1027_, 1);
v___x_1029_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_propagateMul___closed__9));
v___x_1030_ = lean_box(0);
if (v_isShared_955_ == 0)
{
lean_ctor_set(v___x_954_, 1, v___x_1030_);
v___x_1032_ = v___x_954_;
goto v_reusejp_1031_;
}
else
{
lean_object* v_reuseFailAlloc_1036_; 
v_reuseFailAlloc_1036_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1036_, 0, v_head_952_);
lean_ctor_set(v_reuseFailAlloc_1036_, 1, v___x_1030_);
v___x_1032_ = v_reuseFailAlloc_1036_;
goto v_reusejp_1031_;
}
v_reusejp_1031_:
{
lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; 
v___x_1033_ = l_Lean_mkConst(v___x_1029_, v___x_1032_);
lean_inc_ref(v_arg_917_);
v___x_1034_ = l_Lean_mkApp5(v___x_1033_, v_arg_928_, v_val_942_, v_arg_917_, v_arg_914_, v_a_1028_);
v___x_1035_ = l_Lean_Meta_Grind_pushEqCore___redArg(v_e_897_, v_arg_917_, v___x_1034_, v___x_1020_, v_a_898_, v_a_900_, v_a_904_, v_a_905_, v_a_906_, v_a_907_);
return v___x_1035_;
}
}
else
{
lean_object* v_a_1037_; lean_object* v___x_1039_; uint8_t v_isShared_1040_; uint8_t v_isSharedCheck_1044_; 
lean_del_object(v___x_954_);
lean_dec(v_head_952_);
lean_dec(v_val_942_);
lean_dec_ref(v_arg_928_);
lean_dec_ref(v_arg_917_);
lean_dec_ref(v_arg_914_);
lean_dec_ref(v_e_897_);
v_a_1037_ = lean_ctor_get(v___x_1027_, 0);
v_isSharedCheck_1044_ = !lean_is_exclusive(v___x_1027_);
if (v_isSharedCheck_1044_ == 0)
{
v___x_1039_ = v___x_1027_;
v_isShared_1040_ = v_isSharedCheck_1044_;
goto v_resetjp_1038_;
}
else
{
lean_inc(v_a_1037_);
lean_dec(v___x_1027_);
v___x_1039_ = lean_box(0);
v_isShared_1040_ = v_isSharedCheck_1044_;
goto v_resetjp_1038_;
}
v_resetjp_1038_:
{
lean_object* v___x_1042_; 
if (v_isShared_1040_ == 0)
{
v___x_1042_ = v___x_1039_;
goto v_reusejp_1041_;
}
else
{
lean_object* v_reuseFailAlloc_1043_; 
v_reuseFailAlloc_1043_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1043_, 0, v_a_1037_);
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
}
else
{
lean_object* v___x_1045_; 
lean_dec(v_val_1018_);
lean_del_object(v___x_1016_);
lean_inc(v_a_907_);
lean_inc_ref(v_a_906_);
lean_inc(v_a_905_);
lean_inc_ref(v_a_904_);
lean_inc(v_a_903_);
lean_inc_ref(v_a_902_);
lean_inc(v_a_901_);
lean_inc_ref(v_a_900_);
lean_inc(v_a_899_);
lean_inc(v_a_898_);
lean_inc(v_a_961_);
lean_inc_ref(v_arg_914_);
v___x_1045_ = lean_grind_mk_eq_proof(v_arg_914_, v_a_961_, v_a_898_, v_a_899_, v_a_900_, v_a_901_, v_a_902_, v_a_903_, v_a_904_, v_a_905_, v_a_906_, v_a_907_);
if (lean_obj_tag(v___x_1045_) == 0)
{
lean_object* v_a_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1050_; 
v_a_1046_ = lean_ctor_get(v___x_1045_, 0);
lean_inc(v_a_1046_);
lean_dec_ref_known(v___x_1045_, 1);
v___x_1047_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_propagateMul___closed__11));
v___x_1048_ = lean_box(0);
if (v_isShared_955_ == 0)
{
lean_ctor_set(v___x_954_, 1, v___x_1048_);
v___x_1050_ = v___x_954_;
goto v_reusejp_1049_;
}
else
{
lean_object* v_reuseFailAlloc_1055_; 
v_reuseFailAlloc_1055_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1055_, 0, v_head_952_);
lean_ctor_set(v_reuseFailAlloc_1055_, 1, v___x_1048_);
v___x_1050_ = v_reuseFailAlloc_1055_;
goto v_reusejp_1049_;
}
v_reusejp_1049_:
{
lean_object* v___x_1051_; lean_object* v___x_1052_; uint8_t v___x_1053_; lean_object* v___x_1054_; 
v___x_1051_ = l_Lean_mkConst(v___x_1047_, v___x_1050_);
v___x_1052_ = l_Lean_mkApp5(v___x_1051_, v_arg_928_, v_val_942_, v_arg_917_, v_arg_914_, v_a_1046_);
v___x_1053_ = 0;
v___x_1054_ = l_Lean_Meta_Grind_pushEqCore___redArg(v_e_897_, v_a_961_, v___x_1052_, v___x_1053_, v_a_898_, v_a_900_, v_a_904_, v_a_905_, v_a_906_, v_a_907_);
return v___x_1054_;
}
}
else
{
lean_object* v_a_1056_; lean_object* v___x_1058_; uint8_t v_isShared_1059_; uint8_t v_isSharedCheck_1063_; 
lean_dec(v_a_961_);
lean_del_object(v___x_954_);
lean_dec(v_head_952_);
lean_dec(v_val_942_);
lean_dec_ref(v_arg_928_);
lean_dec_ref(v_arg_917_);
lean_dec_ref(v_arg_914_);
lean_dec_ref(v_e_897_);
v_a_1056_ = lean_ctor_get(v___x_1045_, 0);
v_isSharedCheck_1063_ = !lean_is_exclusive(v___x_1045_);
if (v_isSharedCheck_1063_ == 0)
{
v___x_1058_ = v___x_1045_;
v_isShared_1059_ = v_isSharedCheck_1063_;
goto v_resetjp_1057_;
}
else
{
lean_inc(v_a_1056_);
lean_dec(v___x_1045_);
v___x_1058_ = lean_box(0);
v_isShared_1059_ = v_isSharedCheck_1063_;
goto v_resetjp_1057_;
}
v_resetjp_1057_:
{
lean_object* v___x_1061_; 
if (v_isShared_1059_ == 0)
{
v___x_1061_ = v___x_1058_;
goto v_reusejp_1060_;
}
else
{
lean_object* v_reuseFailAlloc_1062_; 
v_reuseFailAlloc_1062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1062_, 0, v_a_1056_);
v___x_1061_ = v_reuseFailAlloc_1062_;
goto v_reusejp_1060_;
}
v_reusejp_1060_:
{
return v___x_1061_;
}
}
}
}
}
else
{
lean_object* v___x_1064_; lean_object* v___x_1066_; 
lean_dec(v_a_1014_);
lean_dec(v_a_961_);
lean_del_object(v___x_954_);
lean_dec(v_head_952_);
lean_dec(v_val_942_);
lean_dec_ref(v_arg_928_);
lean_dec_ref(v_arg_917_);
lean_dec_ref(v_arg_914_);
lean_dec_ref(v_e_897_);
v___x_1064_ = lean_box(0);
if (v_isShared_1017_ == 0)
{
lean_ctor_set(v___x_1016_, 0, v___x_1064_);
v___x_1066_ = v___x_1016_;
goto v_reusejp_1065_;
}
else
{
lean_object* v_reuseFailAlloc_1067_; 
v_reuseFailAlloc_1067_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1067_, 0, v___x_1064_);
v___x_1066_ = v_reuseFailAlloc_1067_;
goto v_reusejp_1065_;
}
v_reusejp_1065_:
{
return v___x_1066_;
}
}
}
}
else
{
lean_object* v_a_1069_; lean_object* v___x_1071_; uint8_t v_isShared_1072_; uint8_t v_isSharedCheck_1076_; 
lean_dec(v_a_961_);
lean_del_object(v___x_954_);
lean_dec(v_head_952_);
lean_dec(v_val_942_);
lean_dec_ref(v_arg_928_);
lean_dec_ref(v_arg_917_);
lean_dec_ref(v_arg_914_);
lean_dec_ref(v_e_897_);
v_a_1069_ = lean_ctor_get(v___x_1013_, 0);
v_isSharedCheck_1076_ = !lean_is_exclusive(v___x_1013_);
if (v_isSharedCheck_1076_ == 0)
{
v___x_1071_ = v___x_1013_;
v_isShared_1072_ = v_isSharedCheck_1076_;
goto v_resetjp_1070_;
}
else
{
lean_inc(v_a_1069_);
lean_dec(v___x_1013_);
v___x_1071_ = lean_box(0);
v_isShared_1072_ = v_isSharedCheck_1076_;
goto v_resetjp_1070_;
}
v_resetjp_1070_:
{
lean_object* v___x_1074_; 
if (v_isShared_1072_ == 0)
{
v___x_1074_ = v___x_1071_;
goto v_reusejp_1073_;
}
else
{
lean_object* v_reuseFailAlloc_1075_; 
v_reuseFailAlloc_1075_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1075_, 0, v_a_1069_);
v___x_1074_ = v_reuseFailAlloc_1075_;
goto v_reusejp_1073_;
}
v_reusejp_1073_:
{
return v___x_1074_;
}
}
}
}
}
}
else
{
lean_object* v_a_1078_; lean_object* v___x_1080_; uint8_t v_isShared_1081_; uint8_t v_isSharedCheck_1085_; 
lean_dec(v_a_961_);
lean_dec(v_a_958_);
lean_del_object(v___x_954_);
lean_dec(v_head_952_);
lean_dec(v_val_942_);
lean_dec_ref(v_arg_928_);
lean_dec_ref(v_arg_917_);
lean_dec_ref(v_arg_914_);
lean_dec_ref(v_e_897_);
v_a_1078_ = lean_ctor_get(v___x_962_, 0);
v_isSharedCheck_1085_ = !lean_is_exclusive(v___x_962_);
if (v_isSharedCheck_1085_ == 0)
{
v___x_1080_ = v___x_962_;
v_isShared_1081_ = v_isSharedCheck_1085_;
goto v_resetjp_1079_;
}
else
{
lean_inc(v_a_1078_);
lean_dec(v___x_962_);
v___x_1080_ = lean_box(0);
v_isShared_1081_ = v_isSharedCheck_1085_;
goto v_resetjp_1079_;
}
v_resetjp_1079_:
{
lean_object* v___x_1083_; 
if (v_isShared_1081_ == 0)
{
v___x_1083_ = v___x_1080_;
goto v_reusejp_1082_;
}
else
{
lean_object* v_reuseFailAlloc_1084_; 
v_reuseFailAlloc_1084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1084_, 0, v_a_1078_);
v___x_1083_ = v_reuseFailAlloc_1084_;
goto v_reusejp_1082_;
}
v_reusejp_1082_:
{
return v___x_1083_;
}
}
}
}
else
{
lean_object* v_a_1086_; lean_object* v___x_1088_; uint8_t v_isShared_1089_; uint8_t v_isSharedCheck_1093_; 
lean_dec(v_a_958_);
lean_del_object(v___x_954_);
lean_dec(v_head_952_);
lean_dec(v_val_942_);
lean_dec_ref(v_arg_928_);
lean_dec_ref(v_arg_917_);
lean_dec_ref(v_arg_914_);
lean_dec_ref(v_e_897_);
v_a_1086_ = lean_ctor_get(v___x_960_, 0);
v_isSharedCheck_1093_ = !lean_is_exclusive(v___x_960_);
if (v_isSharedCheck_1093_ == 0)
{
v___x_1088_ = v___x_960_;
v_isShared_1089_ = v_isSharedCheck_1093_;
goto v_resetjp_1087_;
}
else
{
lean_inc(v_a_1086_);
lean_dec(v___x_960_);
v___x_1088_ = lean_box(0);
v_isShared_1089_ = v_isSharedCheck_1093_;
goto v_resetjp_1087_;
}
v_resetjp_1087_:
{
lean_object* v___x_1091_; 
if (v_isShared_1089_ == 0)
{
v___x_1091_ = v___x_1088_;
goto v_reusejp_1090_;
}
else
{
lean_object* v_reuseFailAlloc_1092_; 
v_reuseFailAlloc_1092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1092_, 0, v_a_1086_);
v___x_1091_ = v_reuseFailAlloc_1092_;
goto v_reusejp_1090_;
}
v_reusejp_1090_:
{
return v___x_1091_;
}
}
}
}
else
{
lean_object* v_a_1094_; lean_object* v___x_1096_; uint8_t v_isShared_1097_; uint8_t v_isSharedCheck_1101_; 
lean_del_object(v___x_954_);
lean_dec(v_head_952_);
lean_dec(v_val_942_);
lean_dec_ref(v_arg_928_);
lean_dec_ref(v_arg_917_);
lean_dec_ref(v_arg_914_);
lean_dec_ref(v_e_897_);
v_a_1094_ = lean_ctor_get(v___x_957_, 0);
v_isSharedCheck_1101_ = !lean_is_exclusive(v___x_957_);
if (v_isSharedCheck_1101_ == 0)
{
v___x_1096_ = v___x_957_;
v_isShared_1097_ = v_isSharedCheck_1101_;
goto v_resetjp_1095_;
}
else
{
lean_inc(v_a_1094_);
lean_dec(v___x_957_);
v___x_1096_ = lean_box(0);
v_isShared_1097_ = v_isSharedCheck_1101_;
goto v_resetjp_1095_;
}
v_resetjp_1095_:
{
lean_object* v___x_1099_; 
if (v_isShared_1097_ == 0)
{
v___x_1099_ = v___x_1096_;
goto v_reusejp_1098_;
}
else
{
lean_object* v_reuseFailAlloc_1100_; 
v_reuseFailAlloc_1100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1100_, 0, v_a_1094_);
v___x_1099_ = v_reuseFailAlloc_1100_;
goto v_reusejp_1098_;
}
v_reusejp_1098_:
{
return v___x_1099_;
}
}
}
}
}
else
{
lean_object* v___x_1104_; lean_object* v___x_1106_; 
lean_dec(v___x_951_);
lean_dec(v_val_942_);
lean_dec_ref(v_arg_928_);
lean_dec_ref(v_arg_917_);
lean_dec_ref(v_arg_914_);
lean_dec_ref(v_e_897_);
v___x_1104_ = lean_box(0);
if (v_isShared_945_ == 0)
{
lean_ctor_set_tag(v___x_944_, 0);
lean_ctor_set(v___x_944_, 0, v___x_1104_);
v___x_1106_ = v___x_944_;
goto v_reusejp_1105_;
}
else
{
lean_object* v_reuseFailAlloc_1107_; 
v_reuseFailAlloc_1107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1107_, 0, v___x_1104_);
v___x_1106_ = v_reuseFailAlloc_1107_;
goto v_reusejp_1105_;
}
v_reusejp_1105_:
{
return v___x_1106_;
}
}
}
}
}
}
else
{
lean_object* v___x_1109_; lean_object* v___x_1110_; 
lean_del_object(v___x_935_);
lean_dec(v_a_933_);
lean_dec_ref(v___x_929_);
lean_dec_ref(v_arg_928_);
lean_dec_ref(v_arg_925_);
lean_dec_ref(v_arg_922_);
lean_dec_ref(v_arg_917_);
lean_dec_ref(v_arg_914_);
lean_dec_ref(v_e_897_);
v___x_1109_ = lean_box(0);
v___x_1110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1110_, 0, v___x_1109_);
return v___x_1110_;
}
v___jp_937_:
{
lean_object* v___x_938_; lean_object* v___x_940_; 
v___x_938_ = lean_box(0);
if (v_isShared_936_ == 0)
{
lean_ctor_set(v___x_935_, 0, v___x_938_);
v___x_940_ = v___x_935_;
goto v_reusejp_939_;
}
else
{
lean_object* v_reuseFailAlloc_941_; 
v_reuseFailAlloc_941_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_941_, 0, v___x_938_);
v___x_940_ = v_reuseFailAlloc_941_;
goto v_reusejp_939_;
}
v_reusejp_939_:
{
return v___x_940_;
}
}
}
}
else
{
lean_object* v_a_1112_; lean_object* v___x_1114_; uint8_t v_isShared_1115_; uint8_t v_isSharedCheck_1119_; 
lean_dec_ref(v___x_929_);
lean_dec_ref(v_arg_928_);
lean_dec_ref(v_arg_925_);
lean_dec_ref(v_arg_922_);
lean_dec_ref(v_arg_917_);
lean_dec_ref(v_arg_914_);
lean_dec_ref(v_e_897_);
v_a_1112_ = lean_ctor_get(v___x_932_, 0);
v_isSharedCheck_1119_ = !lean_is_exclusive(v___x_932_);
if (v_isSharedCheck_1119_ == 0)
{
v___x_1114_ = v___x_932_;
v_isShared_1115_ = v_isSharedCheck_1119_;
goto v_resetjp_1113_;
}
else
{
lean_inc(v_a_1112_);
lean_dec(v___x_932_);
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
}
}
}
}
}
v___jp_909_:
{
lean_object* v___x_910_; lean_object* v___x_911_; 
v___x_910_ = lean_box(0);
v___x_911_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_911_, 0, v___x_910_);
return v___x_911_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_propagateMul_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_897_ = stack[0].m_obj;
lean_object* v_a_898_ = stack[1].m_obj;
lean_object* v_a_899_ = stack[2].m_obj;
lean_object* v_a_900_ = stack[3].m_obj;
lean_object* v_a_901_ = stack[4].m_obj;
lean_object* v_a_902_ = stack[5].m_obj;
lean_object* v_a_903_ = stack[6].m_obj;
lean_object* v_a_904_ = stack[7].m_obj;
lean_object* v_a_905_ = stack[8].m_obj;
lean_object* v_a_906_ = stack[9].m_obj;
lean_object* v_a_907_ = stack[10].m_obj;
lean_object* v_res_1120_;
v_res_1120_ = l_Lean_Meta_Grind_Arith_propagateMul(v_e_897_, v_a_898_, v_a_899_, v_a_900_, v_a_901_, v_a_902_, v_a_903_, v_a_904_, v_a_905_, v_a_906_, v_a_907_);
stack->m_obj
 = v_res_1120_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_propagateMul___boxed(lean_object* v_e_1121_, lean_object* v_a_1122_, lean_object* v_a_1123_, lean_object* v_a_1124_, lean_object* v_a_1125_, lean_object* v_a_1126_, lean_object* v_a_1127_, lean_object* v_a_1128_, lean_object* v_a_1129_, lean_object* v_a_1130_, lean_object* v_a_1131_, lean_object* v_a_1132_){
_start:
{
lean_object* v_res_1133_; 
v_res_1133_ = l_Lean_Meta_Grind_Arith_propagateMul(v_e_1121_, v_a_1122_, v_a_1123_, v_a_1124_, v_a_1125_, v_a_1126_, v_a_1127_, v_a_1128_, v_a_1129_, v_a_1130_, v_a_1131_);
lean_dec(v_a_1131_);
lean_dec_ref(v_a_1130_);
lean_dec(v_a_1129_);
lean_dec_ref(v_a_1128_);
lean_dec(v_a_1127_);
lean_dec_ref(v_a_1126_);
lean_dec(v_a_1125_);
lean_dec_ref(v_a_1124_);
lean_dec(v_a_1123_);
lean_dec(v_a_1122_);
return v_res_1133_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_propagateMul___regBuiltin_Lean_Meta_Grind_Arith_propagateMul_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_3131998065____hygCtx___hyg_9_(){
_start:
{
lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; 
v___x_1135_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_propagateMul___closed__2));
v___x_1136_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_propagateMul___boxed), 12, 0);
v___x_1137_ = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(v___x_1135_, v___x_1136_);
return v___x_1137_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_propagateMul___regBuiltin_Lean_Meta_Grind_Arith_propagateMul_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_3131998065____hygCtx___hyg_9__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1138_;
v_res_1138_ = l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_propagateMul___regBuiltin_Lean_Meta_Grind_Arith_propagateMul_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_3131998065____hygCtx___hyg_9_();
stack->m_obj
 = v_res_1138_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_propagateMul___regBuiltin_Lean_Meta_Grind_Arith_propagateMul_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_3131998065____hygCtx___hyg_9____boxed(lean_object* v_a_1139_){
_start:
{
lean_object* v_res_1140_; 
v_res_1140_ = l___private_Lean_Meta_Tactic_Grind_Arith_Propagate_0__Lean_Meta_Grind_Arith_propagateMul___regBuiltin_Lean_Meta_Grind_Arith_propagateMul_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_3131998065____hygCtx___hyg_9_();
return v_res_1140_;
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
