// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.CommRing.Internalize
// Imports: public import Lean.Meta.Tactic.Grind.Arith.CommRing.RingId import Lean.Meta.Tactic.Grind.Simp import Lean.Meta.Tactic.Grind.Arith.Util import Lean.Meta.Tactic.Grind.Arith.CommRing.Reify import Lean.Meta.Tactic.Grind.Arith.CommRing.DenoteExpr
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
lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_canon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommon___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_synthInstanceMeta_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkInst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
uint8_t l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(lean_object*, lean_object*);
uint64_t l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* l_Lean_Meta_getIntValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getNatValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_nat_abs(lean_object*);
lean_object* l_Lean_mkRawNatLit(lean_object*);
lean_object* l_Lean_Meta_synthInstance_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_pushNewFact(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_hasChar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_getCharInst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_int_emod(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkNatLit(lean_object*);
lean_object* l_Lean_mkIntLit(lean_object*);
extern lean_object* l_Lean_eagerReflBoolTrue;
lean_object* l_Lean_mkApp6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkExpectedPropHint(lean_object*, lean_object*);
lean_object* l_Lean_mkApp5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_pushEqCore___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getConfig___redArg(lean_object*);
uint8_t l_Lean_Meta_Grind_Arith_isIntModuleVirtualParent(lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_reify_x3f(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Grind_Arith_CommRing_ringExt;
lean_object* l_Lean_Meta_Grind_SolverExtension_markTerm___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_updateLastTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_sreify_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNonCommRingId_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_ncreify_x3f(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_modifyRing___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_ncsreify_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_modifySemiring___redArg(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "IntCast"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "intCast"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(63, 186, 193, 83, 149, 255, 18, 69)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(190, 203, 124, 26, 63, 107, 241, 61)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "NatCast"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__3_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "natCast"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__4_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__3_value),LEAN_SCALAR_PTR_LITERAL(65, 128, 63, 191, 243, 154, 52, 80)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__4_value),LEAN_SCALAR_PTR_LITERAL(47, 224, 192, 179, 253, 143, 7, 98)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__5_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "OfNat"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__6_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ofNat"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__7_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__6_value),LEAN_SCALAR_PTR_LITERAL(135, 241, 166, 108, 243, 216, 193, 244)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__8_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__7_value),LEAN_SCALAR_PTR_LITERAL(2, 108, 58, 34, 100, 49, 50, 216)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__8_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Neg"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__9_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "neg"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__10 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__10_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__9_value),LEAN_SCALAR_PTR_LITERAL(94, 4, 109, 108, 64, 81, 153, 133)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__11_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__10_value),LEAN_SCALAR_PTR_LITERAL(105, 26, 70, 221, 245, 238, 127, 238)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__11 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__11_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HPow"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__12 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__12_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hPow"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__13 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__13_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__12_value),LEAN_SCALAR_PTR_LITERAL(155, 188, 136, 200, 106, 253, 76, 178)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__14_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__13_value),LEAN_SCALAR_PTR_LITERAL(32, 63, 208, 57, 56, 184, 164, 144)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__14 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__14_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "HSMul"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__15 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__15_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "hSMul"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__16 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__16_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__15_value),LEAN_SCALAR_PTR_LITERAL(226, 107, 25, 48, 80, 144, 236, 217)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__17_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__16_value),LEAN_SCALAR_PTR_LITERAL(23, 127, 6, 115, 121, 139, 223, 188)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__17 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__17_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HMul"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__18 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__18_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hMul"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__19 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__19_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__20_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__18_value),LEAN_SCALAR_PTR_LITERAL(254, 113, 255, 140, 142, 9, 169, 40)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__20_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__19_value),LEAN_SCALAR_PTR_LITERAL(248, 227, 200, 215, 229, 255, 92, 22)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__20 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__20_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HSub"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__21 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__21_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hSub"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__22 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__22_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__23_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__21_value),LEAN_SCALAR_PTR_LITERAL(121, 130, 45, 212, 110, 237, 236, 233)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__23_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__22_value),LEAN_SCALAR_PTR_LITERAL(231, 253, 204, 163, 168, 77, 27, 58)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__23 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__23_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HAdd"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__24 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__24_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hAdd"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__25 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__25_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__26_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__24_value),LEAN_SCALAR_PTR_LITERAL(221, 239, 47, 196, 170, 166, 59, 144)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__26_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__25_value),LEAN_SCALAR_PTR_LITERAL(134, 172, 115, 219, 189, 252, 56, 148)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__26 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__26_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Int"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__27 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__27_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__27_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__28 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__28_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Nat"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__29 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__29_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__29_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__30 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__30_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isForbiddenParent___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "LE"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isForbiddenParent___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isForbiddenParent___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isForbiddenParent___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "le"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isForbiddenParent___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isForbiddenParent___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isForbiddenParent___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isForbiddenParent___closed__0_value),LEAN_SCALAR_PTR_LITERAL(216, 149, 183, 186, 191, 145, 216, 115)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isForbiddenParent___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isForbiddenParent___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isForbiddenParent___closed__1_value),LEAN_SCALAR_PTR_LITERAL(109, 14, 90, 172, 72, 170, 136, 101)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isForbiddenParent___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isForbiddenParent___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isForbiddenParent___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "LT"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isForbiddenParent___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isForbiddenParent___closed__3_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isForbiddenParent___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "lt"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isForbiddenParent___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isForbiddenParent___closed__4_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isForbiddenParent___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isForbiddenParent___closed__3_value),LEAN_SCALAR_PTR_LITERAL(71, 235, 154, 184, 62, 135, 30, 248)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isForbiddenParent___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isForbiddenParent___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isForbiddenParent___closed__4_value),LEAN_SCALAR_PTR_LITERAL(54, 235, 251, 9, 4, 74, 57, 164)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isForbiddenParent___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isForbiddenParent___closed__5_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isForbiddenParent___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HMod"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isForbiddenParent___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isForbiddenParent___closed__6_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isForbiddenParent___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hMod"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isForbiddenParent___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isForbiddenParent___closed__7_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isForbiddenParent___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isForbiddenParent___closed__6_value),LEAN_SCALAR_PTR_LITERAL(93, 4, 3, 35, 188, 254, 191, 190)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isForbiddenParent___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isForbiddenParent___closed__8_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isForbiddenParent___closed__7_value),LEAN_SCALAR_PTR_LITERAL(120, 199, 142, 238, 9, 44, 94, 134)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isForbiddenParent___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isForbiddenParent___closed__8_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isForbiddenParent___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HDiv"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isForbiddenParent___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isForbiddenParent___closed__9_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isForbiddenParent___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hDiv"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isForbiddenParent___closed__10 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isForbiddenParent___closed__10_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isForbiddenParent___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isForbiddenParent___closed__9_value),LEAN_SCALAR_PTR_LITERAL(74, 223, 78, 88, 255, 236, 144, 164)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isForbiddenParent___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isForbiddenParent___closed__11_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isForbiddenParent___closed__10_value),LEAN_SCALAR_PTR_LITERAL(26, 183, 188, 240, 156, 118, 170, 84)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isForbiddenParent___closed__11 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isForbiddenParent___closed__11_value;
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isForbiddenParent(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isForbiddenParent___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1_spec__5_spec__8_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1_spec__5_spec__8_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1_spec__5_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1_spec__5_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1_spec__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "`grind` failed to find instance"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1_spec__5___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1_spec__5___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1_spec__5___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1_spec__5___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1___boxed(lean_object**);
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0___closed__0_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Grind"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0___closed__1_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Ring"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0___closed__2_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "toNeg"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0___closed__3_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0___closed__4_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0___closed__4_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(196, 225, 111, 69, 82, 38, 249, 149)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0___closed__4_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(100, 233, 103, 154, 53, 22, 86, 139)}};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0___closed__4_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__9_value),LEAN_SCALAR_PTR_LITERAL(94, 4, 109, 108, 64, 81, 153, 133)}};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isIntCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__1_spec__2___lam__0(lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isIntCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__1_spec__2___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isIntCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__1_spec__2___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isIntCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__1_spec__2___closed__0_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isIntCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__1_spec__2___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isIntCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__1_spec__2___closed__0_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(196, 225, 111, 69, 82, 38, 249, 149)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isIntCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__1_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isIntCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__1_spec__2___closed__0_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(1, 189, 244, 99, 68, 50, 19, 202)}};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isIntCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__1_spec__2___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isIntCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__1_spec__2___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isIntCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__1_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(63, 186, 193, 83, 149, 255, 18, 69)}};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isIntCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__1_spec__2___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isIntCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__1_spec__2___closed__1_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isIntCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__1_spec__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "cast"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isIntCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__1_spec__2___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isIntCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__1_spec__2___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isIntCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__1_spec__2___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__27_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isIntCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__1_spec__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isIntCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__1_spec__2___closed__3_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isIntCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__1_spec__2___closed__2_value),LEAN_SCALAR_PTR_LITERAL(181, 4, 252, 84, 28, 16, 24, 6)}};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isIntCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__1_spec__2___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isIntCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__1_spec__2___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isIntCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isIntCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_isIntCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_isIntCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isNatCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__2_spec__4___lam__0(lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_getNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isNatCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__2_spec__4_spec__6___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Semiring"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_getNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isNatCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__2_spec__4_spec__6___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_getNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isNatCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__2_spec__4_spec__6___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_getNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isNatCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__2_spec__4_spec__6___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_getNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isNatCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__2_spec__4_spec__6___redArg___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_getNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isNatCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__2_spec__4_spec__6___redArg___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_getNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isNatCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__2_spec__4_spec__6___redArg___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_getNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isNatCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__2_spec__4_spec__6___redArg___closed__1_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_getNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isNatCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__2_spec__4_spec__6___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(246, 150, 10, 46, 185, 54, 59, 167)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_getNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isNatCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__2_spec__4_spec__6___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_getNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isNatCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__2_spec__4_spec__6___redArg___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__4_value),LEAN_SCALAR_PTR_LITERAL(84, 97, 73, 37, 143, 22, 233, 204)}};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_getNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isNatCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__2_spec__4_spec__6___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_getNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isNatCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__2_spec__4_spec__6___redArg___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_getNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isNatCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__2_spec__4_spec__6___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__3_value),LEAN_SCALAR_PTR_LITERAL(65, 128, 63, 191, 243, 154, 52, 80)}};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_getNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isNatCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__2_spec__4_spec__6___redArg___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_getNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isNatCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__2_spec__4_spec__6___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_getNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isNatCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__2_spec__4_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_getNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isNatCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__2_spec__4_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isNatCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isNatCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_isNatCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_isNatCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_getNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isNatCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__2_spec__4_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_getNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isNatCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__2_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1_spec__5_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1_spec__5_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___lam__0(lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Field"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___closed__0_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "toInv"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___closed__2_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(69, 164, 44, 189, 207, 226, 143, 119)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___closed__2_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(101, 152, 64, 108, 234, 163, 46, 107)}};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___closed__2_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Inv"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___closed__3_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(142, 68, 231, 210, 96, 163, 154, 19)}};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___closed__4_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "inv"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___closed__5_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(142, 68, 231, 210, 96, 163, 154, 19)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___closed__6_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___closed__5_value),LEAN_SCALAR_PTR_LITERAL(63, 31, 248, 222, 13, 64, 40, 141)}};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___closed__6_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 44, .m_capacity = 44, .m_length = 43, .m_data = "`grind` internal error, type is not a field"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___closed__7 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___closed__7_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___closed__8;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0_spec__2_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg___closed__1;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0_spec__3___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___lam__0(lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__6_value),LEAN_SCALAR_PTR_LITERAL(135, 241, 166, 108, 243, 216, 193, 244)}};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__4___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__4___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__4___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__4___closed__1;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__4___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__4___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__4___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__4___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__4___closed__2_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_getNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isNatCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__2_spec__4_spec__6___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(246, 150, 10, 46, 185, 54, 59, 167)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__4___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__4___closed__2_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__7_value),LEAN_SCALAR_PTR_LITERAL(103, 49, 23, 61, 125, 46, 165, 129)}};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__4___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__4___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1_spec__2_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1_spec__2_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1_spec__2___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__3___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__3_spec__5___boxed(lean_object**);
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "instHMul"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__3___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__3___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(177, 107, 107, 59, 202, 230, 169, 251)}};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__3___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__3___closed__1_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "toMul"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__3___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__3___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__3___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__3___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__3___closed__3_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__3___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__3___closed__3_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_getNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isNatCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__2_spec__4_spec__6___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(246, 150, 10, 46, 185, 54, 59, 167)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__3___closed__3_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(232, 23, 103, 115, 5, 120, 143, 98)}};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__3___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__3___closed__3_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__18_value),LEAN_SCALAR_PTR_LITERAL(254, 113, 255, 140, 142, 9, 169, 40)}};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__3___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__3___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "CommRing"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "inv_split"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__0_value),LEAN_SCALAR_PTR_LITERAL(205, 3, 54, 198, 92, 149, 38, 227)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__2_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__1_value),LEAN_SCALAR_PTR_LITERAL(145, 213, 231, 249, 53, 164, 241, 56)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__3;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "inv_int_eqC"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__4_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__5_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__5_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__0_value),LEAN_SCALAR_PTR_LITERAL(205, 3, 54, 198, 92, 149, 38, 227)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__5_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__4_value),LEAN_SCALAR_PTR_LITERAL(153, 82, 86, 32, 91, 2, 111, 119)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__5_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "inv_zero_eqC"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__6_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__7_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__7_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__0_value),LEAN_SCALAR_PTR_LITERAL(205, 3, 54, 198, 92, 149, 38, 227)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__7_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__6_value),LEAN_SCALAR_PTR_LITERAL(59, 171, 80, 119, 126, 116, 37, 65)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__7_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "inv_int_eq"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__8_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__9_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__9_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__0_value),LEAN_SCALAR_PTR_LITERAL(205, 3, 54, 198, 92, 149, 38, 227)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__9_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__8_value),LEAN_SCALAR_PTR_LITERAL(187, 42, 227, 251, 174, 7, 5, 152)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__9_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "inv_zero"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__10 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__10_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__11_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__11_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(69, 164, 44, 189, 207, 226, 143, 119)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__11_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__10_value),LEAN_SCALAR_PTR_LITERAL(103, 152, 135, 191, 44, 26, 55, 129)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__11 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__11_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1_spec__2(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0_spec__3(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1_spec__2_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1_spec__2_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0_spec__2_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeInv(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeInv___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0_spec__1_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0_spec__2___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_internalize___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_internalize___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_internalize___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_internalize___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_internalize___lam__3(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__4___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__4___redArg___closed__0;
static const lean_string_object l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__4___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__4___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__4___redArg___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__4___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__4___redArg___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__4___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "grind"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__0_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "ring"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__1_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "internalize"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__0_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__3_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__1_value),LEAN_SCALAR_PTR_LITERAL(17, 56, 209, 254, 185, 203, 153, 57)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__3_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__2_value),LEAN_SCALAR_PTR_LITERAL(140, 40, 248, 182, 136, 181, 0, 182)}};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__3_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__4_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__4_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__5_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__6;
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__7 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__7_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__8;
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "]: "};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__9 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__9_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__10;
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "semiring ["};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__11 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__11_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__12;
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "(non-comm) ring ["};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__13 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__13_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__14;
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "(non-comm) semiring ["};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__15 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__15_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__16;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_internalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_internalize___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0_spec__2(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0_spec__1_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f(lean_object* v_e_52_){
_start:
{
lean_object* v___x_53_; uint8_t v___x_54_; 
v___x_53_ = l_Lean_Expr_cleanupAnnotations(v_e_52_);
v___x_54_ = l_Lean_Expr_isApp(v___x_53_);
if (v___x_54_ == 0)
{
lean_object* v___x_55_; 
lean_dec_ref(v___x_53_);
v___x_55_ = lean_box(0);
return v___x_55_;
}
else
{
lean_object* v___x_56_; uint8_t v___x_57_; 
v___x_56_ = l_Lean_Expr_appFnCleanup___redArg(v___x_53_);
v___x_57_ = l_Lean_Expr_isApp(v___x_56_);
if (v___x_57_ == 0)
{
lean_object* v___x_58_; 
lean_dec_ref(v___x_56_);
v___x_58_ = lean_box(0);
return v___x_58_;
}
else
{
lean_object* v___x_59_; uint8_t v___x_60_; 
v___x_59_ = l_Lean_Expr_appFnCleanup___redArg(v___x_56_);
v___x_60_ = l_Lean_Expr_isApp(v___x_59_);
if (v___x_60_ == 0)
{
lean_object* v___x_61_; 
lean_dec_ref(v___x_59_);
v___x_61_ = lean_box(0);
return v___x_61_;
}
else
{
lean_object* v_arg_62_; lean_object* v___x_63_; lean_object* v___x_64_; uint8_t v___x_65_; 
v_arg_62_ = lean_ctor_get(v___x_59_, 1);
lean_inc_ref(v_arg_62_);
v___x_63_ = l_Lean_Expr_appFnCleanup___redArg(v___x_59_);
v___x_64_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__2));
v___x_65_ = l_Lean_Expr_isConstOf(v___x_63_, v___x_64_);
if (v___x_65_ == 0)
{
lean_object* v___x_66_; uint8_t v___x_67_; 
v___x_66_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__5));
v___x_67_ = l_Lean_Expr_isConstOf(v___x_63_, v___x_66_);
if (v___x_67_ == 0)
{
lean_object* v___x_68_; uint8_t v___x_69_; 
v___x_68_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__8));
v___x_69_ = l_Lean_Expr_isConstOf(v___x_63_, v___x_68_);
if (v___x_69_ == 0)
{
lean_object* v___x_70_; uint8_t v___x_71_; 
v___x_70_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__11));
v___x_71_ = l_Lean_Expr_isConstOf(v___x_63_, v___x_70_);
if (v___x_71_ == 0)
{
uint8_t v___x_72_; 
lean_dec_ref(v_arg_62_);
v___x_72_ = l_Lean_Expr_isApp(v___x_63_);
if (v___x_72_ == 0)
{
lean_object* v___x_73_; 
lean_dec_ref(v___x_63_);
v___x_73_ = lean_box(0);
return v___x_73_;
}
else
{
lean_object* v___x_74_; uint8_t v___x_75_; 
v___x_74_ = l_Lean_Expr_appFnCleanup___redArg(v___x_63_);
v___x_75_ = l_Lean_Expr_isApp(v___x_74_);
if (v___x_75_ == 0)
{
lean_object* v___x_76_; 
lean_dec_ref(v___x_74_);
v___x_76_ = lean_box(0);
return v___x_76_;
}
else
{
lean_object* v_arg_77_; lean_object* v___x_78_; uint8_t v___x_79_; 
v_arg_77_ = lean_ctor_get(v___x_74_, 1);
lean_inc_ref(v_arg_77_);
v___x_78_ = l_Lean_Expr_appFnCleanup___redArg(v___x_74_);
v___x_79_ = l_Lean_Expr_isApp(v___x_78_);
if (v___x_79_ == 0)
{
lean_object* v___x_80_; 
lean_dec_ref(v___x_78_);
lean_dec_ref(v_arg_77_);
v___x_80_ = lean_box(0);
return v___x_80_;
}
else
{
lean_object* v_arg_81_; lean_object* v___x_82_; lean_object* v___x_83_; uint8_t v___x_84_; 
v_arg_81_ = lean_ctor_get(v___x_78_, 1);
lean_inc_ref(v_arg_81_);
v___x_82_ = l_Lean_Expr_appFnCleanup___redArg(v___x_78_);
v___x_83_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__14));
v___x_84_ = l_Lean_Expr_isConstOf(v___x_82_, v___x_83_);
if (v___x_84_ == 0)
{
lean_object* v___x_85_; uint8_t v___x_86_; 
v___x_85_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__17));
v___x_86_ = l_Lean_Expr_isConstOf(v___x_82_, v___x_85_);
if (v___x_86_ == 0)
{
lean_object* v___x_87_; uint8_t v___x_88_; 
lean_dec_ref(v_arg_77_);
v___x_87_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__20));
v___x_88_ = l_Lean_Expr_isConstOf(v___x_82_, v___x_87_);
if (v___x_88_ == 0)
{
lean_object* v___x_89_; uint8_t v___x_90_; 
v___x_89_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__23));
v___x_90_ = l_Lean_Expr_isConstOf(v___x_82_, v___x_89_);
if (v___x_90_ == 0)
{
lean_object* v___x_91_; uint8_t v___x_92_; 
v___x_91_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__26));
v___x_92_ = l_Lean_Expr_isConstOf(v___x_82_, v___x_91_);
lean_dec_ref(v___x_82_);
if (v___x_92_ == 0)
{
lean_object* v___x_93_; 
lean_dec_ref(v_arg_81_);
v___x_93_ = lean_box(0);
return v___x_93_;
}
else
{
lean_object* v___x_94_; 
v___x_94_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_94_, 0, v_arg_81_);
return v___x_94_;
}
}
else
{
lean_object* v___x_95_; 
lean_dec_ref(v___x_82_);
v___x_95_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_95_, 0, v_arg_81_);
return v___x_95_;
}
}
else
{
lean_object* v___x_96_; 
lean_dec_ref(v___x_82_);
v___x_96_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_96_, 0, v_arg_81_);
return v___x_96_;
}
}
else
{
lean_object* v___x_97_; lean_object* v___x_98_; uint8_t v___x_99_; 
lean_dec_ref(v___x_82_);
v___x_97_ = l_Lean_Expr_cleanupAnnotations(v_arg_81_);
v___x_98_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__28));
v___x_99_ = l_Lean_Expr_isConstOf(v___x_97_, v___x_98_);
if (v___x_99_ == 0)
{
lean_object* v___x_100_; uint8_t v___x_101_; 
v___x_100_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__30));
v___x_101_ = l_Lean_Expr_isConstOf(v___x_97_, v___x_100_);
lean_dec_ref(v___x_97_);
if (v___x_101_ == 0)
{
lean_object* v___x_102_; 
lean_dec_ref(v_arg_77_);
v___x_102_ = lean_box(0);
return v___x_102_;
}
else
{
lean_object* v___x_103_; 
v___x_103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_103_, 0, v_arg_77_);
return v___x_103_;
}
}
else
{
lean_object* v___x_104_; 
lean_dec_ref(v___x_97_);
v___x_104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_104_, 0, v_arg_77_);
return v___x_104_;
}
}
}
else
{
lean_object* v___x_105_; lean_object* v___x_106_; uint8_t v___x_107_; 
lean_dec_ref(v___x_82_);
v___x_105_ = l_Lean_Expr_cleanupAnnotations(v_arg_77_);
v___x_106_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__30));
v___x_107_ = l_Lean_Expr_isConstOf(v___x_105_, v___x_106_);
lean_dec_ref(v___x_105_);
if (v___x_107_ == 0)
{
lean_object* v___x_108_; 
lean_dec_ref(v_arg_81_);
v___x_108_ = lean_box(0);
return v___x_108_;
}
else
{
lean_object* v___x_109_; 
v___x_109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_109_, 0, v_arg_81_);
return v___x_109_;
}
}
}
}
}
}
else
{
lean_object* v___x_110_; 
lean_dec_ref(v___x_63_);
v___x_110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_110_, 0, v_arg_62_);
return v___x_110_;
}
}
else
{
lean_object* v___x_111_; 
lean_dec_ref(v___x_63_);
v___x_111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_111_, 0, v_arg_62_);
return v___x_111_;
}
}
else
{
lean_object* v___x_112_; 
lean_dec_ref(v___x_63_);
v___x_112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_112_, 0, v_arg_62_);
return v___x_112_;
}
}
else
{
lean_object* v___x_113_; 
lean_dec_ref(v___x_63_);
v___x_113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_113_, 0, v_arg_62_);
return v___x_113_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isForbiddenParent(lean_object* v_parent_x3f_134_){
_start:
{
if (lean_obj_tag(v_parent_x3f_134_) == 1)
{
lean_object* v_val_135_; lean_object* v___x_136_; 
v_val_135_ = lean_ctor_get(v_parent_x3f_134_, 0);
lean_inc_n(v_val_135_, 2);
lean_dec_ref(v_parent_x3f_134_);
v___x_136_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f(v_val_135_);
if (lean_obj_tag(v___x_136_) == 0)
{
lean_object* v___x_137_; uint8_t v___x_138_; 
v___x_137_ = l_Lean_Expr_cleanupAnnotations(v_val_135_);
v___x_138_ = l_Lean_Expr_isApp(v___x_137_);
if (v___x_138_ == 0)
{
lean_dec_ref(v___x_137_);
return v___x_138_;
}
else
{
lean_object* v___x_139_; uint8_t v___x_140_; 
v___x_139_ = l_Lean_Expr_appFnCleanup___redArg(v___x_137_);
v___x_140_ = l_Lean_Expr_isApp(v___x_139_);
if (v___x_140_ == 0)
{
lean_dec_ref(v___x_139_);
return v___x_140_;
}
else
{
lean_object* v___x_141_; uint8_t v___x_142_; 
v___x_141_ = l_Lean_Expr_appFnCleanup___redArg(v___x_139_);
v___x_142_ = l_Lean_Expr_isApp(v___x_141_);
if (v___x_142_ == 0)
{
lean_dec_ref(v___x_141_);
return v___x_142_;
}
else
{
lean_object* v___x_143_; uint8_t v___x_144_; 
v___x_143_ = l_Lean_Expr_appFnCleanup___redArg(v___x_141_);
v___x_144_ = l_Lean_Expr_isApp(v___x_143_);
if (v___x_144_ == 0)
{
lean_dec_ref(v___x_143_);
return v___x_144_;
}
else
{
lean_object* v___x_145_; lean_object* v___x_146_; uint8_t v___x_147_; 
v___x_145_ = l_Lean_Expr_appFnCleanup___redArg(v___x_143_);
v___x_146_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isForbiddenParent___closed__2));
v___x_147_ = l_Lean_Expr_isConstOf(v___x_145_, v___x_146_);
if (v___x_147_ == 0)
{
lean_object* v___x_148_; uint8_t v___x_149_; 
v___x_148_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isForbiddenParent___closed__5));
v___x_149_ = l_Lean_Expr_isConstOf(v___x_145_, v___x_148_);
if (v___x_149_ == 0)
{
uint8_t v___x_150_; 
v___x_150_ = l_Lean_Expr_isApp(v___x_145_);
if (v___x_150_ == 0)
{
lean_dec_ref(v___x_145_);
return v___x_150_;
}
else
{
lean_object* v___x_151_; uint8_t v___x_152_; 
v___x_151_ = l_Lean_Expr_appFnCleanup___redArg(v___x_145_);
v___x_152_ = l_Lean_Expr_isApp(v___x_151_);
if (v___x_152_ == 0)
{
lean_dec_ref(v___x_151_);
return v___x_152_;
}
else
{
lean_object* v___x_153_; lean_object* v___x_154_; uint8_t v___x_155_; 
v___x_153_ = l_Lean_Expr_appFnCleanup___redArg(v___x_151_);
v___x_154_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isForbiddenParent___closed__8));
v___x_155_ = l_Lean_Expr_isConstOf(v___x_153_, v___x_154_);
if (v___x_155_ == 0)
{
lean_object* v___x_156_; uint8_t v___x_157_; 
v___x_156_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isForbiddenParent___closed__11));
v___x_157_ = l_Lean_Expr_isConstOf(v___x_153_, v___x_156_);
lean_dec_ref(v___x_153_);
if (v___x_157_ == 0)
{
return v___x_157_;
}
else
{
return v___x_144_;
}
}
else
{
lean_dec_ref(v___x_153_);
return v___x_144_;
}
}
}
}
else
{
lean_dec_ref(v___x_145_);
return v___x_144_;
}
}
else
{
lean_dec_ref(v___x_145_);
return v___x_144_;
}
}
}
}
}
}
else
{
uint8_t v___x_158_; 
lean_dec_ref(v___x_136_);
lean_dec(v_val_135_);
v___x_158_ = 1;
return v___x_158_;
}
}
else
{
uint8_t v___x_159_; 
lean_dec(v_parent_x3f_134_);
v___x_159_ = 0;
return v___x_159_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isForbiddenParent___boxed(lean_object* v_parent_x3f_160_){
_start:
{
uint8_t v_res_161_; lean_object* v_r_162_; 
v_res_161_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isForbiddenParent(v_parent_x3f_160_);
v_r_162_ = lean_box(v_res_161_);
return v_r_162_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0___lam__0(lean_object* v_a_163_, lean_object* v_s_164_){
_start:
{
lean_object* v_toRing_165_; lean_object* v_invFn_x3f_166_; lean_object* v_semiringId_x3f_167_; lean_object* v_commSemiringInst_168_; lean_object* v_commRingInst_169_; lean_object* v_noZeroDivInst_x3f_170_; lean_object* v_fieldInst_x3f_171_; lean_object* v_denoteEntries_172_; lean_object* v_nextId_173_; lean_object* v_steps_174_; lean_object* v_queue_175_; lean_object* v_basis_176_; lean_object* v_diseqs_177_; uint8_t v_recheck_178_; lean_object* v_invSet_179_; lean_object* v_numEq0_x3f_180_; uint8_t v_numEq0Updated_181_; lean_object* v___x_183_; uint8_t v_isShared_184_; uint8_t v_isSharedCheck_213_; 
v_toRing_165_ = lean_ctor_get(v_s_164_, 0);
v_invFn_x3f_166_ = lean_ctor_get(v_s_164_, 1);
v_semiringId_x3f_167_ = lean_ctor_get(v_s_164_, 2);
v_commSemiringInst_168_ = lean_ctor_get(v_s_164_, 3);
v_commRingInst_169_ = lean_ctor_get(v_s_164_, 4);
v_noZeroDivInst_x3f_170_ = lean_ctor_get(v_s_164_, 5);
v_fieldInst_x3f_171_ = lean_ctor_get(v_s_164_, 6);
v_denoteEntries_172_ = lean_ctor_get(v_s_164_, 7);
v_nextId_173_ = lean_ctor_get(v_s_164_, 8);
v_steps_174_ = lean_ctor_get(v_s_164_, 9);
v_queue_175_ = lean_ctor_get(v_s_164_, 10);
v_basis_176_ = lean_ctor_get(v_s_164_, 11);
v_diseqs_177_ = lean_ctor_get(v_s_164_, 12);
v_recheck_178_ = lean_ctor_get_uint8(v_s_164_, sizeof(void*)*15);
v_invSet_179_ = lean_ctor_get(v_s_164_, 13);
v_numEq0_x3f_180_ = lean_ctor_get(v_s_164_, 14);
v_numEq0Updated_181_ = lean_ctor_get_uint8(v_s_164_, sizeof(void*)*15 + 1);
v_isSharedCheck_213_ = !lean_is_exclusive(v_s_164_);
if (v_isSharedCheck_213_ == 0)
{
v___x_183_ = v_s_164_;
v_isShared_184_ = v_isSharedCheck_213_;
goto v_resetjp_182_;
}
else
{
lean_inc(v_numEq0_x3f_180_);
lean_inc(v_invSet_179_);
lean_inc(v_diseqs_177_);
lean_inc(v_basis_176_);
lean_inc(v_queue_175_);
lean_inc(v_steps_174_);
lean_inc(v_nextId_173_);
lean_inc(v_denoteEntries_172_);
lean_inc(v_fieldInst_x3f_171_);
lean_inc(v_noZeroDivInst_x3f_170_);
lean_inc(v_commRingInst_169_);
lean_inc(v_commSemiringInst_168_);
lean_inc(v_semiringId_x3f_167_);
lean_inc(v_invFn_x3f_166_);
lean_inc(v_toRing_165_);
lean_dec(v_s_164_);
v___x_183_ = lean_box(0);
v_isShared_184_ = v_isSharedCheck_213_;
goto v_resetjp_182_;
}
v_resetjp_182_:
{
lean_object* v_id_185_; lean_object* v_type_186_; lean_object* v_u_187_; lean_object* v_ringInst_188_; lean_object* v_semiringInst_189_; lean_object* v_charInst_x3f_190_; lean_object* v_addFn_x3f_191_; lean_object* v_mulFn_x3f_192_; lean_object* v_subFn_x3f_193_; lean_object* v_powFn_x3f_194_; lean_object* v_intCastFn_x3f_195_; lean_object* v_natCastFn_x3f_196_; lean_object* v_one_x3f_197_; lean_object* v_vars_198_; lean_object* v_varMap_199_; lean_object* v_denote_200_; lean_object* v___x_202_; uint8_t v_isShared_203_; uint8_t v_isSharedCheck_211_; 
v_id_185_ = lean_ctor_get(v_toRing_165_, 0);
v_type_186_ = lean_ctor_get(v_toRing_165_, 1);
v_u_187_ = lean_ctor_get(v_toRing_165_, 2);
v_ringInst_188_ = lean_ctor_get(v_toRing_165_, 3);
v_semiringInst_189_ = lean_ctor_get(v_toRing_165_, 4);
v_charInst_x3f_190_ = lean_ctor_get(v_toRing_165_, 5);
v_addFn_x3f_191_ = lean_ctor_get(v_toRing_165_, 6);
v_mulFn_x3f_192_ = lean_ctor_get(v_toRing_165_, 7);
v_subFn_x3f_193_ = lean_ctor_get(v_toRing_165_, 8);
v_powFn_x3f_194_ = lean_ctor_get(v_toRing_165_, 10);
v_intCastFn_x3f_195_ = lean_ctor_get(v_toRing_165_, 11);
v_natCastFn_x3f_196_ = lean_ctor_get(v_toRing_165_, 12);
v_one_x3f_197_ = lean_ctor_get(v_toRing_165_, 13);
v_vars_198_ = lean_ctor_get(v_toRing_165_, 14);
v_varMap_199_ = lean_ctor_get(v_toRing_165_, 15);
v_denote_200_ = lean_ctor_get(v_toRing_165_, 16);
v_isSharedCheck_211_ = !lean_is_exclusive(v_toRing_165_);
if (v_isSharedCheck_211_ == 0)
{
lean_object* v_unused_212_; 
v_unused_212_ = lean_ctor_get(v_toRing_165_, 9);
lean_dec(v_unused_212_);
v___x_202_ = v_toRing_165_;
v_isShared_203_ = v_isSharedCheck_211_;
goto v_resetjp_201_;
}
else
{
lean_inc(v_denote_200_);
lean_inc(v_varMap_199_);
lean_inc(v_vars_198_);
lean_inc(v_one_x3f_197_);
lean_inc(v_natCastFn_x3f_196_);
lean_inc(v_intCastFn_x3f_195_);
lean_inc(v_powFn_x3f_194_);
lean_inc(v_subFn_x3f_193_);
lean_inc(v_mulFn_x3f_192_);
lean_inc(v_addFn_x3f_191_);
lean_inc(v_charInst_x3f_190_);
lean_inc(v_semiringInst_189_);
lean_inc(v_ringInst_188_);
lean_inc(v_u_187_);
lean_inc(v_type_186_);
lean_inc(v_id_185_);
lean_dec(v_toRing_165_);
v___x_202_ = lean_box(0);
v_isShared_203_ = v_isSharedCheck_211_;
goto v_resetjp_201_;
}
v_resetjp_201_:
{
lean_object* v___x_204_; lean_object* v___x_206_; 
v___x_204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_204_, 0, v_a_163_);
if (v_isShared_203_ == 0)
{
lean_ctor_set(v___x_202_, 9, v___x_204_);
v___x_206_ = v___x_202_;
goto v_reusejp_205_;
}
else
{
lean_object* v_reuseFailAlloc_210_; 
v_reuseFailAlloc_210_ = lean_alloc_ctor(0, 17, 0);
lean_ctor_set(v_reuseFailAlloc_210_, 0, v_id_185_);
lean_ctor_set(v_reuseFailAlloc_210_, 1, v_type_186_);
lean_ctor_set(v_reuseFailAlloc_210_, 2, v_u_187_);
lean_ctor_set(v_reuseFailAlloc_210_, 3, v_ringInst_188_);
lean_ctor_set(v_reuseFailAlloc_210_, 4, v_semiringInst_189_);
lean_ctor_set(v_reuseFailAlloc_210_, 5, v_charInst_x3f_190_);
lean_ctor_set(v_reuseFailAlloc_210_, 6, v_addFn_x3f_191_);
lean_ctor_set(v_reuseFailAlloc_210_, 7, v_mulFn_x3f_192_);
lean_ctor_set(v_reuseFailAlloc_210_, 8, v_subFn_x3f_193_);
lean_ctor_set(v_reuseFailAlloc_210_, 9, v___x_204_);
lean_ctor_set(v_reuseFailAlloc_210_, 10, v_powFn_x3f_194_);
lean_ctor_set(v_reuseFailAlloc_210_, 11, v_intCastFn_x3f_195_);
lean_ctor_set(v_reuseFailAlloc_210_, 12, v_natCastFn_x3f_196_);
lean_ctor_set(v_reuseFailAlloc_210_, 13, v_one_x3f_197_);
lean_ctor_set(v_reuseFailAlloc_210_, 14, v_vars_198_);
lean_ctor_set(v_reuseFailAlloc_210_, 15, v_varMap_199_);
lean_ctor_set(v_reuseFailAlloc_210_, 16, v_denote_200_);
v___x_206_ = v_reuseFailAlloc_210_;
goto v_reusejp_205_;
}
v_reusejp_205_:
{
lean_object* v___x_208_; 
if (v_isShared_184_ == 0)
{
lean_ctor_set(v___x_183_, 0, v___x_206_);
v___x_208_ = v___x_183_;
goto v_reusejp_207_;
}
else
{
lean_object* v_reuseFailAlloc_209_; 
v_reuseFailAlloc_209_ = lean_alloc_ctor(0, 15, 2);
lean_ctor_set(v_reuseFailAlloc_209_, 0, v___x_206_);
lean_ctor_set(v_reuseFailAlloc_209_, 1, v_invFn_x3f_166_);
lean_ctor_set(v_reuseFailAlloc_209_, 2, v_semiringId_x3f_167_);
lean_ctor_set(v_reuseFailAlloc_209_, 3, v_commSemiringInst_168_);
lean_ctor_set(v_reuseFailAlloc_209_, 4, v_commRingInst_169_);
lean_ctor_set(v_reuseFailAlloc_209_, 5, v_noZeroDivInst_x3f_170_);
lean_ctor_set(v_reuseFailAlloc_209_, 6, v_fieldInst_x3f_171_);
lean_ctor_set(v_reuseFailAlloc_209_, 7, v_denoteEntries_172_);
lean_ctor_set(v_reuseFailAlloc_209_, 8, v_nextId_173_);
lean_ctor_set(v_reuseFailAlloc_209_, 9, v_steps_174_);
lean_ctor_set(v_reuseFailAlloc_209_, 10, v_queue_175_);
lean_ctor_set(v_reuseFailAlloc_209_, 11, v_basis_176_);
lean_ctor_set(v_reuseFailAlloc_209_, 12, v_diseqs_177_);
lean_ctor_set(v_reuseFailAlloc_209_, 13, v_invSet_179_);
lean_ctor_set(v_reuseFailAlloc_209_, 14, v_numEq0_x3f_180_);
lean_ctor_set_uint8(v_reuseFailAlloc_209_, sizeof(void*)*15, v_recheck_178_);
lean_ctor_set_uint8(v_reuseFailAlloc_209_, sizeof(void*)*15 + 1, v_numEq0Updated_181_);
v___x_208_ = v_reuseFailAlloc_209_;
goto v_reusejp_207_;
}
v_reusejp_207_:
{
return v___x_208_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1_spec__5_spec__8_spec__9(lean_object* v_msgData_214_, lean_object* v___y_215_, lean_object* v___y_216_, lean_object* v___y_217_, lean_object* v___y_218_){
_start:
{
lean_object* v___x_220_; lean_object* v_env_221_; lean_object* v___x_222_; lean_object* v_mctx_223_; lean_object* v_lctx_224_; lean_object* v_options_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; 
v___x_220_ = lean_st_ref_get(v___y_218_);
v_env_221_ = lean_ctor_get(v___x_220_, 0);
lean_inc_ref(v_env_221_);
lean_dec(v___x_220_);
v___x_222_ = lean_st_ref_get(v___y_216_);
v_mctx_223_ = lean_ctor_get(v___x_222_, 0);
lean_inc_ref(v_mctx_223_);
lean_dec(v___x_222_);
v_lctx_224_ = lean_ctor_get(v___y_215_, 2);
v_options_225_ = lean_ctor_get(v___y_217_, 2);
lean_inc_ref(v_options_225_);
lean_inc_ref(v_lctx_224_);
v___x_226_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_226_, 0, v_env_221_);
lean_ctor_set(v___x_226_, 1, v_mctx_223_);
lean_ctor_set(v___x_226_, 2, v_lctx_224_);
lean_ctor_set(v___x_226_, 3, v_options_225_);
v___x_227_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_227_, 0, v___x_226_);
lean_ctor_set(v___x_227_, 1, v_msgData_214_);
v___x_228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_228_, 0, v___x_227_);
return v___x_228_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1_spec__5_spec__8_spec__9___boxed(lean_object* v_msgData_229_, lean_object* v___y_230_, lean_object* v___y_231_, lean_object* v___y_232_, lean_object* v___y_233_, lean_object* v___y_234_){
_start:
{
lean_object* v_res_235_; 
v_res_235_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1_spec__5_spec__8_spec__9(v_msgData_229_, v___y_230_, v___y_231_, v___y_232_, v___y_233_);
lean_dec(v___y_233_);
lean_dec_ref(v___y_232_);
lean_dec(v___y_231_);
lean_dec_ref(v___y_230_);
return v_res_235_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1_spec__5_spec__8___redArg(lean_object* v_msg_236_, lean_object* v___y_237_, lean_object* v___y_238_, lean_object* v___y_239_, lean_object* v___y_240_){
_start:
{
lean_object* v_ref_242_; lean_object* v___x_243_; lean_object* v_a_244_; lean_object* v___x_246_; uint8_t v_isShared_247_; uint8_t v_isSharedCheck_252_; 
v_ref_242_ = lean_ctor_get(v___y_239_, 5);
v___x_243_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1_spec__5_spec__8_spec__9(v_msg_236_, v___y_237_, v___y_238_, v___y_239_, v___y_240_);
v_a_244_ = lean_ctor_get(v___x_243_, 0);
v_isSharedCheck_252_ = !lean_is_exclusive(v___x_243_);
if (v_isSharedCheck_252_ == 0)
{
v___x_246_ = v___x_243_;
v_isShared_247_ = v_isSharedCheck_252_;
goto v_resetjp_245_;
}
else
{
lean_inc(v_a_244_);
lean_dec(v___x_243_);
v___x_246_ = lean_box(0);
v_isShared_247_ = v_isSharedCheck_252_;
goto v_resetjp_245_;
}
v_resetjp_245_:
{
lean_object* v___x_248_; lean_object* v___x_250_; 
lean_inc(v_ref_242_);
v___x_248_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_248_, 0, v_ref_242_);
lean_ctor_set(v___x_248_, 1, v_a_244_);
if (v_isShared_247_ == 0)
{
lean_ctor_set_tag(v___x_246_, 1);
lean_ctor_set(v___x_246_, 0, v___x_248_);
v___x_250_ = v___x_246_;
goto v_reusejp_249_;
}
else
{
lean_object* v_reuseFailAlloc_251_; 
v_reuseFailAlloc_251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_251_, 0, v___x_248_);
v___x_250_ = v_reuseFailAlloc_251_;
goto v_reusejp_249_;
}
v_reusejp_249_:
{
return v___x_250_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1_spec__5_spec__8___redArg___boxed(lean_object* v_msg_253_, lean_object* v___y_254_, lean_object* v___y_255_, lean_object* v___y_256_, lean_object* v___y_257_, lean_object* v___y_258_){
_start:
{
lean_object* v_res_259_; 
v_res_259_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1_spec__5_spec__8___redArg(v_msg_253_, v___y_254_, v___y_255_, v___y_256_, v___y_257_);
lean_dec(v___y_257_);
lean_dec_ref(v___y_256_);
lean_dec(v___y_255_);
lean_dec_ref(v___y_254_);
return v_res_259_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1_spec__5___closed__1(void){
_start:
{
lean_object* v___x_261_; lean_object* v___x_262_; 
v___x_261_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1_spec__5___closed__0));
v___x_262_ = l_Lean_stringToMessageData(v___x_261_);
return v___x_262_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1_spec__5(lean_object* v_type_263_, lean_object* v___y_264_, lean_object* v___y_265_, lean_object* v___y_266_, lean_object* v___y_267_, lean_object* v___y_268_, lean_object* v___y_269_, lean_object* v___y_270_, lean_object* v___y_271_, lean_object* v___y_272_, lean_object* v___y_273_, lean_object* v___y_274_){
_start:
{
lean_object* v___x_276_; 
lean_inc_ref(v_type_263_);
v___x_276_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f(v_type_263_, v___y_271_, v___y_272_, v___y_273_, v___y_274_);
if (lean_obj_tag(v___x_276_) == 0)
{
lean_object* v_a_277_; lean_object* v___x_279_; uint8_t v_isShared_280_; uint8_t v_isSharedCheck_289_; 
v_a_277_ = lean_ctor_get(v___x_276_, 0);
v_isSharedCheck_289_ = !lean_is_exclusive(v___x_276_);
if (v_isSharedCheck_289_ == 0)
{
v___x_279_ = v___x_276_;
v_isShared_280_ = v_isSharedCheck_289_;
goto v_resetjp_278_;
}
else
{
lean_inc(v_a_277_);
lean_dec(v___x_276_);
v___x_279_ = lean_box(0);
v_isShared_280_ = v_isSharedCheck_289_;
goto v_resetjp_278_;
}
v_resetjp_278_:
{
if (lean_obj_tag(v_a_277_) == 1)
{
lean_object* v_val_281_; lean_object* v___x_283_; 
lean_dec_ref(v_type_263_);
v_val_281_ = lean_ctor_get(v_a_277_, 0);
lean_inc(v_val_281_);
lean_dec_ref(v_a_277_);
if (v_isShared_280_ == 0)
{
lean_ctor_set(v___x_279_, 0, v_val_281_);
v___x_283_ = v___x_279_;
goto v_reusejp_282_;
}
else
{
lean_object* v_reuseFailAlloc_284_; 
v_reuseFailAlloc_284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_284_, 0, v_val_281_);
v___x_283_ = v_reuseFailAlloc_284_;
goto v_reusejp_282_;
}
v_reusejp_282_:
{
return v___x_283_;
}
}
else
{
lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; 
lean_del_object(v___x_279_);
lean_dec(v_a_277_);
v___x_285_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1_spec__5___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1_spec__5___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1_spec__5___closed__1);
v___x_286_ = l_Lean_indentExpr(v_type_263_);
v___x_287_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_287_, 0, v___x_285_);
lean_ctor_set(v___x_287_, 1, v___x_286_);
v___x_288_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1_spec__5_spec__8___redArg(v___x_287_, v___y_271_, v___y_272_, v___y_273_, v___y_274_);
return v___x_288_;
}
}
}
else
{
lean_object* v_a_290_; lean_object* v___x_292_; uint8_t v_isShared_293_; uint8_t v_isSharedCheck_297_; 
lean_dec_ref(v_type_263_);
v_a_290_ = lean_ctor_get(v___x_276_, 0);
v_isSharedCheck_297_ = !lean_is_exclusive(v___x_276_);
if (v_isSharedCheck_297_ == 0)
{
v___x_292_ = v___x_276_;
v_isShared_293_ = v_isSharedCheck_297_;
goto v_resetjp_291_;
}
else
{
lean_inc(v_a_290_);
lean_dec(v___x_276_);
v___x_292_ = lean_box(0);
v_isShared_293_ = v_isSharedCheck_297_;
goto v_resetjp_291_;
}
v_resetjp_291_:
{
lean_object* v___x_295_; 
if (v_isShared_293_ == 0)
{
v___x_295_ = v___x_292_;
goto v_reusejp_294_;
}
else
{
lean_object* v_reuseFailAlloc_296_; 
v_reuseFailAlloc_296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_296_, 0, v_a_290_);
v___x_295_ = v_reuseFailAlloc_296_;
goto v_reusejp_294_;
}
v_reusejp_294_:
{
return v___x_295_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1_spec__5___boxed(lean_object* v_type_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_, lean_object* v___y_309_, lean_object* v___y_310_){
_start:
{
lean_object* v_res_311_; 
v_res_311_ = l_Lean_Meta_Grind_Arith_CommRing_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1_spec__5(v_type_298_, v___y_299_, v___y_300_, v___y_301_, v___y_302_, v___y_303_, v___y_304_, v___y_305_, v___y_306_, v___y_307_, v___y_308_, v___y_309_);
lean_dec(v___y_309_);
lean_dec_ref(v___y_308_);
lean_dec(v___y_307_);
lean_dec_ref(v___y_306_);
lean_dec(v___y_305_);
lean_dec_ref(v___y_304_);
lean_dec(v___y_303_);
lean_dec_ref(v___y_302_);
lean_dec(v___y_301_);
lean_dec(v___y_300_);
lean_dec_ref(v___y_299_);
return v_res_311_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1(lean_object* v_type_312_, lean_object* v_u_313_, lean_object* v_instDeclName_314_, lean_object* v_declName_315_, lean_object* v_expectedInst_316_, lean_object* v___y_317_, lean_object* v___y_318_, lean_object* v___y_319_, lean_object* v___y_320_, lean_object* v___y_321_, lean_object* v___y_322_, lean_object* v___y_323_, lean_object* v___y_324_, lean_object* v___y_325_, lean_object* v___y_326_, lean_object* v___y_327_){
_start:
{
lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; 
v___x_329_ = lean_box(0);
v___x_330_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_330_, 0, v_u_313_);
lean_ctor_set(v___x_330_, 1, v___x_329_);
lean_inc_ref(v___x_330_);
v___x_331_ = l_Lean_mkConst(v_instDeclName_314_, v___x_330_);
lean_inc_ref(v_type_312_);
v___x_332_ = l_Lean_Expr_app___override(v___x_331_, v_type_312_);
v___x_333_ = l_Lean_Meta_Grind_Arith_CommRing_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1_spec__5(v___x_332_, v___y_317_, v___y_318_, v___y_319_, v___y_320_, v___y_321_, v___y_322_, v___y_323_, v___y_324_, v___y_325_, v___y_326_, v___y_327_);
if (lean_obj_tag(v___x_333_) == 0)
{
lean_object* v_a_334_; lean_object* v___x_335_; 
v_a_334_ = lean_ctor_get(v___x_333_, 0);
lean_inc_n(v_a_334_, 2);
lean_dec_ref(v___x_333_);
lean_inc(v_declName_315_);
v___x_335_ = l_Lean_Meta_Grind_Arith_CommRing_checkInst(v_declName_315_, v_a_334_, v_expectedInst_316_, v___y_324_, v___y_325_, v___y_326_, v___y_327_);
if (lean_obj_tag(v___x_335_) == 0)
{
lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; 
lean_dec_ref(v___x_335_);
v___x_336_ = l_Lean_mkConst(v_declName_315_, v___x_330_);
v___x_337_ = l_Lean_mkAppB(v___x_336_, v_type_312_, v_a_334_);
v___x_338_ = l_Lean_Meta_Sym_canon(v___x_337_, v___y_322_, v___y_323_, v___y_324_, v___y_325_, v___y_326_, v___y_327_);
if (lean_obj_tag(v___x_338_) == 0)
{
lean_object* v_a_339_; lean_object* v___x_340_; 
v_a_339_ = lean_ctor_get(v___x_338_, 0);
lean_inc(v_a_339_);
lean_dec_ref(v___x_338_);
v___x_340_ = l_Lean_Meta_Sym_shareCommon___redArg(v_a_339_, v___y_323_);
return v___x_340_;
}
else
{
return v___x_338_;
}
}
else
{
lean_object* v_a_341_; lean_object* v___x_343_; uint8_t v_isShared_344_; uint8_t v_isSharedCheck_348_; 
lean_dec(v_a_334_);
lean_dec_ref(v___x_330_);
lean_dec(v_declName_315_);
lean_dec_ref(v_type_312_);
v_a_341_ = lean_ctor_get(v___x_335_, 0);
v_isSharedCheck_348_ = !lean_is_exclusive(v___x_335_);
if (v_isSharedCheck_348_ == 0)
{
v___x_343_ = v___x_335_;
v_isShared_344_ = v_isSharedCheck_348_;
goto v_resetjp_342_;
}
else
{
lean_inc(v_a_341_);
lean_dec(v___x_335_);
v___x_343_ = lean_box(0);
v_isShared_344_ = v_isSharedCheck_348_;
goto v_resetjp_342_;
}
v_resetjp_342_:
{
lean_object* v___x_346_; 
if (v_isShared_344_ == 0)
{
v___x_346_ = v___x_343_;
goto v_reusejp_345_;
}
else
{
lean_object* v_reuseFailAlloc_347_; 
v_reuseFailAlloc_347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_347_, 0, v_a_341_);
v___x_346_ = v_reuseFailAlloc_347_;
goto v_reusejp_345_;
}
v_reusejp_345_:
{
return v___x_346_;
}
}
}
}
else
{
lean_dec_ref(v___x_330_);
lean_dec_ref(v_expectedInst_316_);
lean_dec(v_declName_315_);
lean_dec_ref(v_type_312_);
return v___x_333_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1___boxed(lean_object** _args){
lean_object* v_type_349_ = _args[0];
lean_object* v_u_350_ = _args[1];
lean_object* v_instDeclName_351_ = _args[2];
lean_object* v_declName_352_ = _args[3];
lean_object* v_expectedInst_353_ = _args[4];
lean_object* v___y_354_ = _args[5];
lean_object* v___y_355_ = _args[6];
lean_object* v___y_356_ = _args[7];
lean_object* v___y_357_ = _args[8];
lean_object* v___y_358_ = _args[9];
lean_object* v___y_359_ = _args[10];
lean_object* v___y_360_ = _args[11];
lean_object* v___y_361_ = _args[12];
lean_object* v___y_362_ = _args[13];
lean_object* v___y_363_ = _args[14];
lean_object* v___y_364_ = _args[15];
lean_object* v___y_365_ = _args[16];
_start:
{
lean_object* v_res_366_; 
v_res_366_ = l_Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1(v_type_349_, v_u_350_, v_instDeclName_351_, v_declName_352_, v_expectedInst_353_, v___y_354_, v___y_355_, v___y_356_, v___y_357_, v___y_358_, v___y_359_, v___y_360_, v___y_361_, v___y_362_, v___y_363_, v___y_364_);
lean_dec(v___y_364_);
lean_dec_ref(v___y_363_);
lean_dec(v___y_362_);
lean_dec_ref(v___y_361_);
lean_dec(v___y_360_);
lean_dec_ref(v___y_359_);
lean_dec(v___y_358_);
lean_dec_ref(v___y_357_);
lean_dec(v___y_356_);
lean_dec(v___y_355_);
lean_dec_ref(v___y_354_);
return v_res_366_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0(lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_){
_start:
{
lean_object* v___x_390_; 
v___x_390_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v___y_378_, v___y_379_, v___y_380_, v___y_381_, v___y_382_, v___y_383_, v___y_384_, v___y_385_, v___y_386_, v___y_387_, v___y_388_);
if (lean_obj_tag(v___x_390_) == 0)
{
lean_object* v_a_391_; lean_object* v___x_393_; uint8_t v_isShared_394_; uint8_t v_isSharedCheck_431_; 
v_a_391_ = lean_ctor_get(v___x_390_, 0);
v_isSharedCheck_431_ = !lean_is_exclusive(v___x_390_);
if (v_isSharedCheck_431_ == 0)
{
v___x_393_ = v___x_390_;
v_isShared_394_ = v_isSharedCheck_431_;
goto v_resetjp_392_;
}
else
{
lean_inc(v_a_391_);
lean_dec(v___x_390_);
v___x_393_ = lean_box(0);
v_isShared_394_ = v_isSharedCheck_431_;
goto v_resetjp_392_;
}
v_resetjp_392_:
{
lean_object* v_toRing_395_; lean_object* v_negFn_x3f_396_; 
v_toRing_395_ = lean_ctor_get(v_a_391_, 0);
lean_inc_ref(v_toRing_395_);
lean_dec(v_a_391_);
v_negFn_x3f_396_ = lean_ctor_get(v_toRing_395_, 9);
if (lean_obj_tag(v_negFn_x3f_396_) == 1)
{
lean_object* v_val_397_; lean_object* v___x_399_; 
lean_inc_ref(v_negFn_x3f_396_);
lean_dec_ref(v_toRing_395_);
v_val_397_ = lean_ctor_get(v_negFn_x3f_396_, 0);
lean_inc(v_val_397_);
lean_dec_ref(v_negFn_x3f_396_);
if (v_isShared_394_ == 0)
{
lean_ctor_set(v___x_393_, 0, v_val_397_);
v___x_399_ = v___x_393_;
goto v_reusejp_398_;
}
else
{
lean_object* v_reuseFailAlloc_400_; 
v_reuseFailAlloc_400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_400_, 0, v_val_397_);
v___x_399_ = v_reuseFailAlloc_400_;
goto v_reusejp_398_;
}
v_reusejp_398_:
{
return v___x_399_;
}
}
else
{
lean_object* v_type_401_; lean_object* v_u_402_; lean_object* v_ringInst_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v_expectedInst_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; 
lean_del_object(v___x_393_);
v_type_401_ = lean_ctor_get(v_toRing_395_, 1);
lean_inc_ref_n(v_type_401_, 2);
v_u_402_ = lean_ctor_get(v_toRing_395_, 2);
lean_inc_n(v_u_402_, 2);
v_ringInst_403_ = lean_ctor_get(v_toRing_395_, 3);
lean_inc_ref(v_ringInst_403_);
lean_dec_ref(v_toRing_395_);
v___x_404_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0___closed__4));
v___x_405_ = lean_box(0);
v___x_406_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_406_, 0, v_u_402_);
lean_ctor_set(v___x_406_, 1, v___x_405_);
v___x_407_ = l_Lean_mkConst(v___x_404_, v___x_406_);
v_expectedInst_408_ = l_Lean_mkAppB(v___x_407_, v_type_401_, v_ringInst_403_);
v___x_409_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0___closed__5));
v___x_410_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__11));
v___x_411_ = l_Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1(v_type_401_, v_u_402_, v___x_409_, v___x_410_, v_expectedInst_408_, v___y_378_, v___y_379_, v___y_380_, v___y_381_, v___y_382_, v___y_383_, v___y_384_, v___y_385_, v___y_386_, v___y_387_, v___y_388_);
if (lean_obj_tag(v___x_411_) == 0)
{
lean_object* v_a_412_; lean_object* v___f_413_; lean_object* v___x_414_; 
v_a_412_ = lean_ctor_get(v___x_411_, 0);
lean_inc_n(v_a_412_, 2);
lean_dec_ref(v___x_411_);
v___f_413_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0___lam__0), 2, 1);
lean_closure_set(v___f_413_, 0, v_a_412_);
v___x_414_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(v___f_413_, v___y_378_, v___y_379_);
if (lean_obj_tag(v___x_414_) == 0)
{
lean_object* v___x_416_; uint8_t v_isShared_417_; uint8_t v_isSharedCheck_421_; 
v_isSharedCheck_421_ = !lean_is_exclusive(v___x_414_);
if (v_isSharedCheck_421_ == 0)
{
lean_object* v_unused_422_; 
v_unused_422_ = lean_ctor_get(v___x_414_, 0);
lean_dec(v_unused_422_);
v___x_416_ = v___x_414_;
v_isShared_417_ = v_isSharedCheck_421_;
goto v_resetjp_415_;
}
else
{
lean_dec(v___x_414_);
v___x_416_ = lean_box(0);
v_isShared_417_ = v_isSharedCheck_421_;
goto v_resetjp_415_;
}
v_resetjp_415_:
{
lean_object* v___x_419_; 
if (v_isShared_417_ == 0)
{
lean_ctor_set(v___x_416_, 0, v_a_412_);
v___x_419_ = v___x_416_;
goto v_reusejp_418_;
}
else
{
lean_object* v_reuseFailAlloc_420_; 
v_reuseFailAlloc_420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_420_, 0, v_a_412_);
v___x_419_ = v_reuseFailAlloc_420_;
goto v_reusejp_418_;
}
v_reusejp_418_:
{
return v___x_419_;
}
}
}
else
{
lean_object* v_a_423_; lean_object* v___x_425_; uint8_t v_isShared_426_; uint8_t v_isSharedCheck_430_; 
lean_dec(v_a_412_);
v_a_423_ = lean_ctor_get(v___x_414_, 0);
v_isSharedCheck_430_ = !lean_is_exclusive(v___x_414_);
if (v_isSharedCheck_430_ == 0)
{
v___x_425_ = v___x_414_;
v_isShared_426_ = v_isSharedCheck_430_;
goto v_resetjp_424_;
}
else
{
lean_inc(v_a_423_);
lean_dec(v___x_414_);
v___x_425_ = lean_box(0);
v_isShared_426_ = v_isSharedCheck_430_;
goto v_resetjp_424_;
}
v_resetjp_424_:
{
lean_object* v___x_428_; 
if (v_isShared_426_ == 0)
{
v___x_428_ = v___x_425_;
goto v_reusejp_427_;
}
else
{
lean_object* v_reuseFailAlloc_429_; 
v_reuseFailAlloc_429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_429_, 0, v_a_423_);
v___x_428_ = v_reuseFailAlloc_429_;
goto v_reusejp_427_;
}
v_reusejp_427_:
{
return v___x_428_;
}
}
}
}
else
{
return v___x_411_;
}
}
}
}
else
{
lean_object* v_a_432_; lean_object* v___x_434_; uint8_t v_isShared_435_; uint8_t v_isSharedCheck_439_; 
v_a_432_ = lean_ctor_get(v___x_390_, 0);
v_isSharedCheck_439_ = !lean_is_exclusive(v___x_390_);
if (v_isSharedCheck_439_ == 0)
{
v___x_434_ = v___x_390_;
v_isShared_435_ = v_isSharedCheck_439_;
goto v_resetjp_433_;
}
else
{
lean_inc(v_a_432_);
lean_dec(v___x_390_);
v___x_434_ = lean_box(0);
v_isShared_435_ = v_isSharedCheck_439_;
goto v_resetjp_433_;
}
v_resetjp_433_:
{
lean_object* v___x_437_; 
if (v_isShared_435_ == 0)
{
v___x_437_ = v___x_434_;
goto v_reusejp_436_;
}
else
{
lean_object* v_reuseFailAlloc_438_; 
v_reuseFailAlloc_438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_438_, 0, v_a_432_);
v___x_437_ = v_reuseFailAlloc_438_;
goto v_reusejp_436_;
}
v_reusejp_436_:
{
return v___x_437_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0___boxed(lean_object* v___y_440_, lean_object* v___y_441_, lean_object* v___y_442_, lean_object* v___y_443_, lean_object* v___y_444_, lean_object* v___y_445_, lean_object* v___y_446_, lean_object* v___y_447_, lean_object* v___y_448_, lean_object* v___y_449_, lean_object* v___y_450_, lean_object* v___y_451_){
_start:
{
lean_object* v_res_452_; 
v_res_452_ = l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0(v___y_440_, v___y_441_, v___y_442_, v___y_443_, v___y_444_, v___y_445_, v___y_446_, v___y_447_, v___y_448_, v___y_449_, v___y_450_);
lean_dec(v___y_450_);
lean_dec_ref(v___y_449_);
lean_dec(v___y_448_);
lean_dec_ref(v___y_447_);
lean_dec(v___y_446_);
lean_dec_ref(v___y_445_);
lean_dec(v___y_444_);
lean_dec_ref(v___y_443_);
lean_dec(v___y_442_);
lean_dec(v___y_441_);
lean_dec_ref(v___y_440_);
return v_res_452_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0(lean_object* v_inst_453_, lean_object* v___y_454_, lean_object* v___y_455_, lean_object* v___y_456_, lean_object* v___y_457_, lean_object* v___y_458_, lean_object* v___y_459_, lean_object* v___y_460_, lean_object* v___y_461_, lean_object* v___y_462_, lean_object* v___y_463_, lean_object* v___y_464_){
_start:
{
lean_object* v___x_466_; 
v___x_466_ = l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0(v___y_454_, v___y_455_, v___y_456_, v___y_457_, v___y_458_, v___y_459_, v___y_460_, v___y_461_, v___y_462_, v___y_463_, v___y_464_);
if (lean_obj_tag(v___x_466_) == 0)
{
lean_object* v_a_467_; lean_object* v___x_469_; uint8_t v_isShared_470_; uint8_t v_isSharedCheck_477_; 
v_a_467_ = lean_ctor_get(v___x_466_, 0);
v_isSharedCheck_477_ = !lean_is_exclusive(v___x_466_);
if (v_isSharedCheck_477_ == 0)
{
v___x_469_ = v___x_466_;
v_isShared_470_ = v_isSharedCheck_477_;
goto v_resetjp_468_;
}
else
{
lean_inc(v_a_467_);
lean_dec(v___x_466_);
v___x_469_ = lean_box(0);
v_isShared_470_ = v_isSharedCheck_477_;
goto v_resetjp_468_;
}
v_resetjp_468_:
{
lean_object* v___x_471_; uint8_t v___x_472_; lean_object* v___x_473_; lean_object* v___x_475_; 
v___x_471_ = l_Lean_Expr_appArg_x21(v_a_467_);
lean_dec(v_a_467_);
v___x_472_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v___x_471_, v_inst_453_);
lean_dec_ref(v___x_471_);
v___x_473_ = lean_box(v___x_472_);
if (v_isShared_470_ == 0)
{
lean_ctor_set(v___x_469_, 0, v___x_473_);
v___x_475_ = v___x_469_;
goto v_reusejp_474_;
}
else
{
lean_object* v_reuseFailAlloc_476_; 
v_reuseFailAlloc_476_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_476_, 0, v___x_473_);
v___x_475_ = v_reuseFailAlloc_476_;
goto v_reusejp_474_;
}
v_reusejp_474_:
{
return v___x_475_;
}
}
}
else
{
lean_object* v_a_478_; lean_object* v___x_480_; uint8_t v_isShared_481_; uint8_t v_isSharedCheck_485_; 
v_a_478_ = lean_ctor_get(v___x_466_, 0);
v_isSharedCheck_485_ = !lean_is_exclusive(v___x_466_);
if (v_isSharedCheck_485_ == 0)
{
v___x_480_ = v___x_466_;
v_isShared_481_ = v_isSharedCheck_485_;
goto v_resetjp_479_;
}
else
{
lean_inc(v_a_478_);
lean_dec(v___x_466_);
v___x_480_ = lean_box(0);
v_isShared_481_ = v_isSharedCheck_485_;
goto v_resetjp_479_;
}
v_resetjp_479_:
{
lean_object* v___x_483_; 
if (v_isShared_481_ == 0)
{
v___x_483_ = v___x_480_;
goto v_reusejp_482_;
}
else
{
lean_object* v_reuseFailAlloc_484_; 
v_reuseFailAlloc_484_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_484_, 0, v_a_478_);
v___x_483_ = v_reuseFailAlloc_484_;
goto v_reusejp_482_;
}
v_reusejp_482_:
{
return v___x_483_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0___boxed(lean_object* v_inst_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_, lean_object* v___y_493_, lean_object* v___y_494_, lean_object* v___y_495_, lean_object* v___y_496_, lean_object* v___y_497_, lean_object* v___y_498_){
_start:
{
lean_object* v_res_499_; 
v_res_499_ = l_Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0(v_inst_486_, v___y_487_, v___y_488_, v___y_489_, v___y_490_, v___y_491_, v___y_492_, v___y_493_, v___y_494_, v___y_495_, v___y_496_, v___y_497_);
lean_dec(v___y_497_);
lean_dec_ref(v___y_496_);
lean_dec(v___y_495_);
lean_dec_ref(v___y_494_);
lean_dec(v___y_493_);
lean_dec_ref(v___y_492_);
lean_dec(v___y_491_);
lean_dec_ref(v___y_490_);
lean_dec(v___y_489_);
lean_dec(v___y_488_);
lean_dec_ref(v___y_487_);
lean_dec_ref(v_inst_486_);
return v_res_499_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isIntCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__1_spec__2___lam__0(lean_object* v_a_500_, lean_object* v_s_501_){
_start:
{
lean_object* v_toRing_502_; lean_object* v_invFn_x3f_503_; lean_object* v_semiringId_x3f_504_; lean_object* v_commSemiringInst_505_; lean_object* v_commRingInst_506_; lean_object* v_noZeroDivInst_x3f_507_; lean_object* v_fieldInst_x3f_508_; lean_object* v_denoteEntries_509_; lean_object* v_nextId_510_; lean_object* v_steps_511_; lean_object* v_queue_512_; lean_object* v_basis_513_; lean_object* v_diseqs_514_; uint8_t v_recheck_515_; lean_object* v_invSet_516_; lean_object* v_numEq0_x3f_517_; uint8_t v_numEq0Updated_518_; lean_object* v___x_520_; uint8_t v_isShared_521_; uint8_t v_isSharedCheck_550_; 
v_toRing_502_ = lean_ctor_get(v_s_501_, 0);
v_invFn_x3f_503_ = lean_ctor_get(v_s_501_, 1);
v_semiringId_x3f_504_ = lean_ctor_get(v_s_501_, 2);
v_commSemiringInst_505_ = lean_ctor_get(v_s_501_, 3);
v_commRingInst_506_ = lean_ctor_get(v_s_501_, 4);
v_noZeroDivInst_x3f_507_ = lean_ctor_get(v_s_501_, 5);
v_fieldInst_x3f_508_ = lean_ctor_get(v_s_501_, 6);
v_denoteEntries_509_ = lean_ctor_get(v_s_501_, 7);
v_nextId_510_ = lean_ctor_get(v_s_501_, 8);
v_steps_511_ = lean_ctor_get(v_s_501_, 9);
v_queue_512_ = lean_ctor_get(v_s_501_, 10);
v_basis_513_ = lean_ctor_get(v_s_501_, 11);
v_diseqs_514_ = lean_ctor_get(v_s_501_, 12);
v_recheck_515_ = lean_ctor_get_uint8(v_s_501_, sizeof(void*)*15);
v_invSet_516_ = lean_ctor_get(v_s_501_, 13);
v_numEq0_x3f_517_ = lean_ctor_get(v_s_501_, 14);
v_numEq0Updated_518_ = lean_ctor_get_uint8(v_s_501_, sizeof(void*)*15 + 1);
v_isSharedCheck_550_ = !lean_is_exclusive(v_s_501_);
if (v_isSharedCheck_550_ == 0)
{
v___x_520_ = v_s_501_;
v_isShared_521_ = v_isSharedCheck_550_;
goto v_resetjp_519_;
}
else
{
lean_inc(v_numEq0_x3f_517_);
lean_inc(v_invSet_516_);
lean_inc(v_diseqs_514_);
lean_inc(v_basis_513_);
lean_inc(v_queue_512_);
lean_inc(v_steps_511_);
lean_inc(v_nextId_510_);
lean_inc(v_denoteEntries_509_);
lean_inc(v_fieldInst_x3f_508_);
lean_inc(v_noZeroDivInst_x3f_507_);
lean_inc(v_commRingInst_506_);
lean_inc(v_commSemiringInst_505_);
lean_inc(v_semiringId_x3f_504_);
lean_inc(v_invFn_x3f_503_);
lean_inc(v_toRing_502_);
lean_dec(v_s_501_);
v___x_520_ = lean_box(0);
v_isShared_521_ = v_isSharedCheck_550_;
goto v_resetjp_519_;
}
v_resetjp_519_:
{
lean_object* v_id_522_; lean_object* v_type_523_; lean_object* v_u_524_; lean_object* v_ringInst_525_; lean_object* v_semiringInst_526_; lean_object* v_charInst_x3f_527_; lean_object* v_addFn_x3f_528_; lean_object* v_mulFn_x3f_529_; lean_object* v_subFn_x3f_530_; lean_object* v_negFn_x3f_531_; lean_object* v_powFn_x3f_532_; lean_object* v_natCastFn_x3f_533_; lean_object* v_one_x3f_534_; lean_object* v_vars_535_; lean_object* v_varMap_536_; lean_object* v_denote_537_; lean_object* v___x_539_; uint8_t v_isShared_540_; uint8_t v_isSharedCheck_548_; 
v_id_522_ = lean_ctor_get(v_toRing_502_, 0);
v_type_523_ = lean_ctor_get(v_toRing_502_, 1);
v_u_524_ = lean_ctor_get(v_toRing_502_, 2);
v_ringInst_525_ = lean_ctor_get(v_toRing_502_, 3);
v_semiringInst_526_ = lean_ctor_get(v_toRing_502_, 4);
v_charInst_x3f_527_ = lean_ctor_get(v_toRing_502_, 5);
v_addFn_x3f_528_ = lean_ctor_get(v_toRing_502_, 6);
v_mulFn_x3f_529_ = lean_ctor_get(v_toRing_502_, 7);
v_subFn_x3f_530_ = lean_ctor_get(v_toRing_502_, 8);
v_negFn_x3f_531_ = lean_ctor_get(v_toRing_502_, 9);
v_powFn_x3f_532_ = lean_ctor_get(v_toRing_502_, 10);
v_natCastFn_x3f_533_ = lean_ctor_get(v_toRing_502_, 12);
v_one_x3f_534_ = lean_ctor_get(v_toRing_502_, 13);
v_vars_535_ = lean_ctor_get(v_toRing_502_, 14);
v_varMap_536_ = lean_ctor_get(v_toRing_502_, 15);
v_denote_537_ = lean_ctor_get(v_toRing_502_, 16);
v_isSharedCheck_548_ = !lean_is_exclusive(v_toRing_502_);
if (v_isSharedCheck_548_ == 0)
{
lean_object* v_unused_549_; 
v_unused_549_ = lean_ctor_get(v_toRing_502_, 11);
lean_dec(v_unused_549_);
v___x_539_ = v_toRing_502_;
v_isShared_540_ = v_isSharedCheck_548_;
goto v_resetjp_538_;
}
else
{
lean_inc(v_denote_537_);
lean_inc(v_varMap_536_);
lean_inc(v_vars_535_);
lean_inc(v_one_x3f_534_);
lean_inc(v_natCastFn_x3f_533_);
lean_inc(v_powFn_x3f_532_);
lean_inc(v_negFn_x3f_531_);
lean_inc(v_subFn_x3f_530_);
lean_inc(v_mulFn_x3f_529_);
lean_inc(v_addFn_x3f_528_);
lean_inc(v_charInst_x3f_527_);
lean_inc(v_semiringInst_526_);
lean_inc(v_ringInst_525_);
lean_inc(v_u_524_);
lean_inc(v_type_523_);
lean_inc(v_id_522_);
lean_dec(v_toRing_502_);
v___x_539_ = lean_box(0);
v_isShared_540_ = v_isSharedCheck_548_;
goto v_resetjp_538_;
}
v_resetjp_538_:
{
lean_object* v___x_541_; lean_object* v___x_543_; 
v___x_541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_541_, 0, v_a_500_);
if (v_isShared_540_ == 0)
{
lean_ctor_set(v___x_539_, 11, v___x_541_);
v___x_543_ = v___x_539_;
goto v_reusejp_542_;
}
else
{
lean_object* v_reuseFailAlloc_547_; 
v_reuseFailAlloc_547_ = lean_alloc_ctor(0, 17, 0);
lean_ctor_set(v_reuseFailAlloc_547_, 0, v_id_522_);
lean_ctor_set(v_reuseFailAlloc_547_, 1, v_type_523_);
lean_ctor_set(v_reuseFailAlloc_547_, 2, v_u_524_);
lean_ctor_set(v_reuseFailAlloc_547_, 3, v_ringInst_525_);
lean_ctor_set(v_reuseFailAlloc_547_, 4, v_semiringInst_526_);
lean_ctor_set(v_reuseFailAlloc_547_, 5, v_charInst_x3f_527_);
lean_ctor_set(v_reuseFailAlloc_547_, 6, v_addFn_x3f_528_);
lean_ctor_set(v_reuseFailAlloc_547_, 7, v_mulFn_x3f_529_);
lean_ctor_set(v_reuseFailAlloc_547_, 8, v_subFn_x3f_530_);
lean_ctor_set(v_reuseFailAlloc_547_, 9, v_negFn_x3f_531_);
lean_ctor_set(v_reuseFailAlloc_547_, 10, v_powFn_x3f_532_);
lean_ctor_set(v_reuseFailAlloc_547_, 11, v___x_541_);
lean_ctor_set(v_reuseFailAlloc_547_, 12, v_natCastFn_x3f_533_);
lean_ctor_set(v_reuseFailAlloc_547_, 13, v_one_x3f_534_);
lean_ctor_set(v_reuseFailAlloc_547_, 14, v_vars_535_);
lean_ctor_set(v_reuseFailAlloc_547_, 15, v_varMap_536_);
lean_ctor_set(v_reuseFailAlloc_547_, 16, v_denote_537_);
v___x_543_ = v_reuseFailAlloc_547_;
goto v_reusejp_542_;
}
v_reusejp_542_:
{
lean_object* v___x_545_; 
if (v_isShared_521_ == 0)
{
lean_ctor_set(v___x_520_, 0, v___x_543_);
v___x_545_ = v___x_520_;
goto v_reusejp_544_;
}
else
{
lean_object* v_reuseFailAlloc_546_; 
v_reuseFailAlloc_546_ = lean_alloc_ctor(0, 15, 2);
lean_ctor_set(v_reuseFailAlloc_546_, 0, v___x_543_);
lean_ctor_set(v_reuseFailAlloc_546_, 1, v_invFn_x3f_503_);
lean_ctor_set(v_reuseFailAlloc_546_, 2, v_semiringId_x3f_504_);
lean_ctor_set(v_reuseFailAlloc_546_, 3, v_commSemiringInst_505_);
lean_ctor_set(v_reuseFailAlloc_546_, 4, v_commRingInst_506_);
lean_ctor_set(v_reuseFailAlloc_546_, 5, v_noZeroDivInst_x3f_507_);
lean_ctor_set(v_reuseFailAlloc_546_, 6, v_fieldInst_x3f_508_);
lean_ctor_set(v_reuseFailAlloc_546_, 7, v_denoteEntries_509_);
lean_ctor_set(v_reuseFailAlloc_546_, 8, v_nextId_510_);
lean_ctor_set(v_reuseFailAlloc_546_, 9, v_steps_511_);
lean_ctor_set(v_reuseFailAlloc_546_, 10, v_queue_512_);
lean_ctor_set(v_reuseFailAlloc_546_, 11, v_basis_513_);
lean_ctor_set(v_reuseFailAlloc_546_, 12, v_diseqs_514_);
lean_ctor_set(v_reuseFailAlloc_546_, 13, v_invSet_516_);
lean_ctor_set(v_reuseFailAlloc_546_, 14, v_numEq0_x3f_517_);
lean_ctor_set_uint8(v_reuseFailAlloc_546_, sizeof(void*)*15, v_recheck_515_);
lean_ctor_set_uint8(v_reuseFailAlloc_546_, sizeof(void*)*15 + 1, v_numEq0Updated_518_);
v___x_545_ = v_reuseFailAlloc_546_;
goto v_reusejp_544_;
}
v_reusejp_544_:
{
return v___x_545_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isIntCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__1_spec__2(lean_object* v___y_562_, lean_object* v___y_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_){
_start:
{
lean_object* v___y_575_; lean_object* v___y_576_; lean_object* v___y_577_; lean_object* v___x_597_; 
v___x_597_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v___y_562_, v___y_563_, v___y_564_, v___y_565_, v___y_566_, v___y_567_, v___y_568_, v___y_569_, v___y_570_, v___y_571_, v___y_572_);
if (lean_obj_tag(v___x_597_) == 0)
{
lean_object* v_a_598_; lean_object* v___x_600_; uint8_t v_isShared_601_; uint8_t v_isSharedCheck_656_; 
v_a_598_ = lean_ctor_get(v___x_597_, 0);
v_isSharedCheck_656_ = !lean_is_exclusive(v___x_597_);
if (v_isSharedCheck_656_ == 0)
{
v___x_600_ = v___x_597_;
v_isShared_601_ = v_isSharedCheck_656_;
goto v_resetjp_599_;
}
else
{
lean_inc(v_a_598_);
lean_dec(v___x_597_);
v___x_600_ = lean_box(0);
v_isShared_601_ = v_isSharedCheck_656_;
goto v_resetjp_599_;
}
v_resetjp_599_:
{
lean_object* v_toRing_602_; lean_object* v_intCastFn_x3f_603_; 
v_toRing_602_ = lean_ctor_get(v_a_598_, 0);
lean_inc_ref(v_toRing_602_);
lean_dec(v_a_598_);
v_intCastFn_x3f_603_ = lean_ctor_get(v_toRing_602_, 11);
if (lean_obj_tag(v_intCastFn_x3f_603_) == 1)
{
lean_object* v_val_604_; lean_object* v___x_606_; 
lean_inc_ref(v_intCastFn_x3f_603_);
lean_dec_ref(v_toRing_602_);
v_val_604_ = lean_ctor_get(v_intCastFn_x3f_603_, 0);
lean_inc(v_val_604_);
lean_dec_ref(v_intCastFn_x3f_603_);
if (v_isShared_601_ == 0)
{
lean_ctor_set(v___x_600_, 0, v_val_604_);
v___x_606_ = v___x_600_;
goto v_reusejp_605_;
}
else
{
lean_object* v_reuseFailAlloc_607_; 
v_reuseFailAlloc_607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_607_, 0, v_val_604_);
v___x_606_ = v_reuseFailAlloc_607_;
goto v_reusejp_605_;
}
v_reusejp_605_:
{
return v___x_606_;
}
}
else
{
lean_object* v_type_608_; lean_object* v_u_609_; lean_object* v_ringInst_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v_inst_x27_615_; lean_object* v_inst_617_; lean_object* v___y_618_; lean_object* v___y_619_; lean_object* v___y_620_; lean_object* v___y_621_; lean_object* v___y_622_; lean_object* v___y_623_; lean_object* v___y_624_; lean_object* v___y_625_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v_instType_634_; lean_object* v___x_635_; 
lean_del_object(v___x_600_);
v_type_608_ = lean_ctor_get(v_toRing_602_, 1);
lean_inc_ref_n(v_type_608_, 3);
v_u_609_ = lean_ctor_get(v_toRing_602_, 2);
lean_inc(v_u_609_);
v_ringInst_610_ = lean_ctor_get(v_toRing_602_, 3);
lean_inc_ref(v_ringInst_610_);
lean_dec_ref(v_toRing_602_);
v___x_611_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isIntCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__1_spec__2___closed__0));
v___x_612_ = lean_box(0);
v___x_613_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_613_, 0, v_u_609_);
lean_ctor_set(v___x_613_, 1, v___x_612_);
lean_inc_ref_n(v___x_613_, 2);
v___x_614_ = l_Lean_mkConst(v___x_611_, v___x_613_);
v_inst_x27_615_ = l_Lean_mkAppB(v___x_614_, v_type_608_, v_ringInst_610_);
v___x_632_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isIntCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__1_spec__2___closed__1));
v___x_633_ = l_Lean_mkConst(v___x_632_, v___x_613_);
v_instType_634_ = l_Lean_Expr_app___override(v___x_633_, v_type_608_);
v___x_635_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f(v_instType_634_, v___y_569_, v___y_570_, v___y_571_, v___y_572_);
if (lean_obj_tag(v___x_635_) == 0)
{
lean_object* v_a_636_; 
v_a_636_ = lean_ctor_get(v___x_635_, 0);
lean_inc(v_a_636_);
lean_dec_ref(v___x_635_);
if (lean_obj_tag(v_a_636_) == 0)
{
v_inst_617_ = v_inst_x27_615_;
v___y_618_ = v___y_562_;
v___y_619_ = v___y_563_;
v___y_620_ = v___y_567_;
v___y_621_ = v___y_568_;
v___y_622_ = v___y_569_;
v___y_623_ = v___y_570_;
v___y_624_ = v___y_571_;
v___y_625_ = v___y_572_;
goto v___jp_616_;
}
else
{
lean_object* v_val_637_; lean_object* v___x_638_; lean_object* v___x_639_; 
v_val_637_ = lean_ctor_get(v_a_636_, 0);
lean_inc_n(v_val_637_, 2);
lean_dec_ref(v_a_636_);
v___x_638_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isIntCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__1_spec__2___closed__3));
v___x_639_ = l_Lean_Meta_Grind_Arith_CommRing_checkInst(v___x_638_, v_val_637_, v_inst_x27_615_, v___y_569_, v___y_570_, v___y_571_, v___y_572_);
if (lean_obj_tag(v___x_639_) == 0)
{
lean_dec_ref(v___x_639_);
v_inst_617_ = v_val_637_;
v___y_618_ = v___y_562_;
v___y_619_ = v___y_563_;
v___y_620_ = v___y_567_;
v___y_621_ = v___y_568_;
v___y_622_ = v___y_569_;
v___y_623_ = v___y_570_;
v___y_624_ = v___y_571_;
v___y_625_ = v___y_572_;
goto v___jp_616_;
}
else
{
lean_object* v_a_640_; lean_object* v___x_642_; uint8_t v_isShared_643_; uint8_t v_isSharedCheck_647_; 
lean_dec(v_val_637_);
lean_dec_ref(v___x_613_);
lean_dec_ref(v_type_608_);
v_a_640_ = lean_ctor_get(v___x_639_, 0);
v_isSharedCheck_647_ = !lean_is_exclusive(v___x_639_);
if (v_isSharedCheck_647_ == 0)
{
v___x_642_ = v___x_639_;
v_isShared_643_ = v_isSharedCheck_647_;
goto v_resetjp_641_;
}
else
{
lean_inc(v_a_640_);
lean_dec(v___x_639_);
v___x_642_ = lean_box(0);
v_isShared_643_ = v_isSharedCheck_647_;
goto v_resetjp_641_;
}
v_resetjp_641_:
{
lean_object* v___x_645_; 
if (v_isShared_643_ == 0)
{
v___x_645_ = v___x_642_;
goto v_reusejp_644_;
}
else
{
lean_object* v_reuseFailAlloc_646_; 
v_reuseFailAlloc_646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_646_, 0, v_a_640_);
v___x_645_ = v_reuseFailAlloc_646_;
goto v_reusejp_644_;
}
v_reusejp_644_:
{
return v___x_645_;
}
}
}
}
}
else
{
lean_object* v_a_648_; lean_object* v___x_650_; uint8_t v_isShared_651_; uint8_t v_isSharedCheck_655_; 
lean_dec_ref(v_inst_x27_615_);
lean_dec_ref(v___x_613_);
lean_dec_ref(v_type_608_);
v_a_648_ = lean_ctor_get(v___x_635_, 0);
v_isSharedCheck_655_ = !lean_is_exclusive(v___x_635_);
if (v_isSharedCheck_655_ == 0)
{
v___x_650_ = v___x_635_;
v_isShared_651_ = v_isSharedCheck_655_;
goto v_resetjp_649_;
}
else
{
lean_inc(v_a_648_);
lean_dec(v___x_635_);
v___x_650_ = lean_box(0);
v_isShared_651_ = v_isSharedCheck_655_;
goto v_resetjp_649_;
}
v_resetjp_649_:
{
lean_object* v___x_653_; 
if (v_isShared_651_ == 0)
{
v___x_653_ = v___x_650_;
goto v_reusejp_652_;
}
else
{
lean_object* v_reuseFailAlloc_654_; 
v_reuseFailAlloc_654_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_654_, 0, v_a_648_);
v___x_653_ = v_reuseFailAlloc_654_;
goto v_reusejp_652_;
}
v_reusejp_652_:
{
return v___x_653_;
}
}
}
v___jp_616_:
{
lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; 
v___x_626_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__2));
v___x_627_ = l_Lean_mkConst(v___x_626_, v___x_613_);
v___x_628_ = l_Lean_mkAppB(v___x_627_, v_type_608_, v_inst_617_);
v___x_629_ = l_Lean_Meta_Sym_canon(v___x_628_, v___y_620_, v___y_621_, v___y_622_, v___y_623_, v___y_624_, v___y_625_);
if (lean_obj_tag(v___x_629_) == 0)
{
lean_object* v_a_630_; lean_object* v___x_631_; 
v_a_630_ = lean_ctor_get(v___x_629_, 0);
lean_inc(v_a_630_);
lean_dec_ref(v___x_629_);
v___x_631_ = l_Lean_Meta_Sym_shareCommon___redArg(v_a_630_, v___y_621_);
v___y_575_ = v___y_619_;
v___y_576_ = v___y_618_;
v___y_577_ = v___x_631_;
goto v___jp_574_;
}
else
{
v___y_575_ = v___y_619_;
v___y_576_ = v___y_618_;
v___y_577_ = v___x_629_;
goto v___jp_574_;
}
}
}
}
}
else
{
lean_object* v_a_657_; lean_object* v___x_659_; uint8_t v_isShared_660_; uint8_t v_isSharedCheck_664_; 
v_a_657_ = lean_ctor_get(v___x_597_, 0);
v_isSharedCheck_664_ = !lean_is_exclusive(v___x_597_);
if (v_isSharedCheck_664_ == 0)
{
v___x_659_ = v___x_597_;
v_isShared_660_ = v_isSharedCheck_664_;
goto v_resetjp_658_;
}
else
{
lean_inc(v_a_657_);
lean_dec(v___x_597_);
v___x_659_ = lean_box(0);
v_isShared_660_ = v_isSharedCheck_664_;
goto v_resetjp_658_;
}
v_resetjp_658_:
{
lean_object* v___x_662_; 
if (v_isShared_660_ == 0)
{
v___x_662_ = v___x_659_;
goto v_reusejp_661_;
}
else
{
lean_object* v_reuseFailAlloc_663_; 
v_reuseFailAlloc_663_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_663_, 0, v_a_657_);
v___x_662_ = v_reuseFailAlloc_663_;
goto v_reusejp_661_;
}
v_reusejp_661_:
{
return v___x_662_;
}
}
}
v___jp_574_:
{
if (lean_obj_tag(v___y_577_) == 0)
{
lean_object* v_a_578_; lean_object* v___f_579_; lean_object* v___x_580_; 
v_a_578_ = lean_ctor_get(v___y_577_, 0);
lean_inc_n(v_a_578_, 2);
lean_dec_ref(v___y_577_);
v___f_579_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isIntCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__1_spec__2___lam__0), 2, 1);
lean_closure_set(v___f_579_, 0, v_a_578_);
v___x_580_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(v___f_579_, v___y_576_, v___y_575_);
if (lean_obj_tag(v___x_580_) == 0)
{
lean_object* v___x_582_; uint8_t v_isShared_583_; uint8_t v_isSharedCheck_587_; 
v_isSharedCheck_587_ = !lean_is_exclusive(v___x_580_);
if (v_isSharedCheck_587_ == 0)
{
lean_object* v_unused_588_; 
v_unused_588_ = lean_ctor_get(v___x_580_, 0);
lean_dec(v_unused_588_);
v___x_582_ = v___x_580_;
v_isShared_583_ = v_isSharedCheck_587_;
goto v_resetjp_581_;
}
else
{
lean_dec(v___x_580_);
v___x_582_ = lean_box(0);
v_isShared_583_ = v_isSharedCheck_587_;
goto v_resetjp_581_;
}
v_resetjp_581_:
{
lean_object* v___x_585_; 
if (v_isShared_583_ == 0)
{
lean_ctor_set(v___x_582_, 0, v_a_578_);
v___x_585_ = v___x_582_;
goto v_reusejp_584_;
}
else
{
lean_object* v_reuseFailAlloc_586_; 
v_reuseFailAlloc_586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_586_, 0, v_a_578_);
v___x_585_ = v_reuseFailAlloc_586_;
goto v_reusejp_584_;
}
v_reusejp_584_:
{
return v___x_585_;
}
}
}
else
{
lean_object* v_a_589_; lean_object* v___x_591_; uint8_t v_isShared_592_; uint8_t v_isSharedCheck_596_; 
lean_dec(v_a_578_);
v_a_589_ = lean_ctor_get(v___x_580_, 0);
v_isSharedCheck_596_ = !lean_is_exclusive(v___x_580_);
if (v_isSharedCheck_596_ == 0)
{
v___x_591_ = v___x_580_;
v_isShared_592_ = v_isSharedCheck_596_;
goto v_resetjp_590_;
}
else
{
lean_inc(v_a_589_);
lean_dec(v___x_580_);
v___x_591_ = lean_box(0);
v_isShared_592_ = v_isSharedCheck_596_;
goto v_resetjp_590_;
}
v_resetjp_590_:
{
lean_object* v___x_594_; 
if (v_isShared_592_ == 0)
{
v___x_594_ = v___x_591_;
goto v_reusejp_593_;
}
else
{
lean_object* v_reuseFailAlloc_595_; 
v_reuseFailAlloc_595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_595_, 0, v_a_589_);
v___x_594_ = v_reuseFailAlloc_595_;
goto v_reusejp_593_;
}
v_reusejp_593_:
{
return v___x_594_;
}
}
}
}
else
{
return v___y_577_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isIntCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__1_spec__2___boxed(lean_object* v___y_665_, lean_object* v___y_666_, lean_object* v___y_667_, lean_object* v___y_668_, lean_object* v___y_669_, lean_object* v___y_670_, lean_object* v___y_671_, lean_object* v___y_672_, lean_object* v___y_673_, lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_){
_start:
{
lean_object* v_res_677_; 
v_res_677_ = l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isIntCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__1_spec__2(v___y_665_, v___y_666_, v___y_667_, v___y_668_, v___y_669_, v___y_670_, v___y_671_, v___y_672_, v___y_673_, v___y_674_, v___y_675_);
lean_dec(v___y_675_);
lean_dec_ref(v___y_674_);
lean_dec(v___y_673_);
lean_dec_ref(v___y_672_);
lean_dec(v___y_671_);
lean_dec_ref(v___y_670_);
lean_dec(v___y_669_);
lean_dec_ref(v___y_668_);
lean_dec(v___y_667_);
lean_dec(v___y_666_);
lean_dec_ref(v___y_665_);
return v_res_677_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_isIntCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__1(lean_object* v_inst_678_, lean_object* v___y_679_, lean_object* v___y_680_, lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_, lean_object* v___y_688_, lean_object* v___y_689_){
_start:
{
lean_object* v___x_691_; 
v___x_691_ = l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isIntCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__1_spec__2(v___y_679_, v___y_680_, v___y_681_, v___y_682_, v___y_683_, v___y_684_, v___y_685_, v___y_686_, v___y_687_, v___y_688_, v___y_689_);
if (lean_obj_tag(v___x_691_) == 0)
{
lean_object* v_a_692_; lean_object* v___x_694_; uint8_t v_isShared_695_; uint8_t v_isSharedCheck_702_; 
v_a_692_ = lean_ctor_get(v___x_691_, 0);
v_isSharedCheck_702_ = !lean_is_exclusive(v___x_691_);
if (v_isSharedCheck_702_ == 0)
{
v___x_694_ = v___x_691_;
v_isShared_695_ = v_isSharedCheck_702_;
goto v_resetjp_693_;
}
else
{
lean_inc(v_a_692_);
lean_dec(v___x_691_);
v___x_694_ = lean_box(0);
v_isShared_695_ = v_isSharedCheck_702_;
goto v_resetjp_693_;
}
v_resetjp_693_:
{
lean_object* v___x_696_; uint8_t v___x_697_; lean_object* v___x_698_; lean_object* v___x_700_; 
v___x_696_ = l_Lean_Expr_appArg_x21(v_a_692_);
lean_dec(v_a_692_);
v___x_697_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v___x_696_, v_inst_678_);
lean_dec_ref(v___x_696_);
v___x_698_ = lean_box(v___x_697_);
if (v_isShared_695_ == 0)
{
lean_ctor_set(v___x_694_, 0, v___x_698_);
v___x_700_ = v___x_694_;
goto v_reusejp_699_;
}
else
{
lean_object* v_reuseFailAlloc_701_; 
v_reuseFailAlloc_701_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_701_, 0, v___x_698_);
v___x_700_ = v_reuseFailAlloc_701_;
goto v_reusejp_699_;
}
v_reusejp_699_:
{
return v___x_700_;
}
}
}
else
{
lean_object* v_a_703_; lean_object* v___x_705_; uint8_t v_isShared_706_; uint8_t v_isSharedCheck_710_; 
v_a_703_ = lean_ctor_get(v___x_691_, 0);
v_isSharedCheck_710_ = !lean_is_exclusive(v___x_691_);
if (v_isSharedCheck_710_ == 0)
{
v___x_705_ = v___x_691_;
v_isShared_706_ = v_isSharedCheck_710_;
goto v_resetjp_704_;
}
else
{
lean_inc(v_a_703_);
lean_dec(v___x_691_);
v___x_705_ = lean_box(0);
v_isShared_706_ = v_isSharedCheck_710_;
goto v_resetjp_704_;
}
v_resetjp_704_:
{
lean_object* v___x_708_; 
if (v_isShared_706_ == 0)
{
v___x_708_ = v___x_705_;
goto v_reusejp_707_;
}
else
{
lean_object* v_reuseFailAlloc_709_; 
v_reuseFailAlloc_709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_709_, 0, v_a_703_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_isIntCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__1___boxed(lean_object* v_inst_711_, lean_object* v___y_712_, lean_object* v___y_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_, lean_object* v___y_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_){
_start:
{
lean_object* v_res_724_; 
v_res_724_ = l_Lean_Meta_Grind_Arith_CommRing_isIntCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__1(v_inst_711_, v___y_712_, v___y_713_, v___y_714_, v___y_715_, v___y_716_, v___y_717_, v___y_718_, v___y_719_, v___y_720_, v___y_721_, v___y_722_);
lean_dec(v___y_722_);
lean_dec_ref(v___y_721_);
lean_dec(v___y_720_);
lean_dec_ref(v___y_719_);
lean_dec(v___y_718_);
lean_dec_ref(v___y_717_);
lean_dec(v___y_716_);
lean_dec_ref(v___y_715_);
lean_dec(v___y_714_);
lean_dec(v___y_713_);
lean_dec_ref(v___y_712_);
lean_dec_ref(v_inst_711_);
return v_res_724_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isNatCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__2_spec__4___lam__0(lean_object* v_a_725_, lean_object* v_s_726_){
_start:
{
lean_object* v_toRing_727_; lean_object* v_invFn_x3f_728_; lean_object* v_semiringId_x3f_729_; lean_object* v_commSemiringInst_730_; lean_object* v_commRingInst_731_; lean_object* v_noZeroDivInst_x3f_732_; lean_object* v_fieldInst_x3f_733_; lean_object* v_denoteEntries_734_; lean_object* v_nextId_735_; lean_object* v_steps_736_; lean_object* v_queue_737_; lean_object* v_basis_738_; lean_object* v_diseqs_739_; uint8_t v_recheck_740_; lean_object* v_invSet_741_; lean_object* v_numEq0_x3f_742_; uint8_t v_numEq0Updated_743_; lean_object* v___x_745_; uint8_t v_isShared_746_; uint8_t v_isSharedCheck_775_; 
v_toRing_727_ = lean_ctor_get(v_s_726_, 0);
v_invFn_x3f_728_ = lean_ctor_get(v_s_726_, 1);
v_semiringId_x3f_729_ = lean_ctor_get(v_s_726_, 2);
v_commSemiringInst_730_ = lean_ctor_get(v_s_726_, 3);
v_commRingInst_731_ = lean_ctor_get(v_s_726_, 4);
v_noZeroDivInst_x3f_732_ = lean_ctor_get(v_s_726_, 5);
v_fieldInst_x3f_733_ = lean_ctor_get(v_s_726_, 6);
v_denoteEntries_734_ = lean_ctor_get(v_s_726_, 7);
v_nextId_735_ = lean_ctor_get(v_s_726_, 8);
v_steps_736_ = lean_ctor_get(v_s_726_, 9);
v_queue_737_ = lean_ctor_get(v_s_726_, 10);
v_basis_738_ = lean_ctor_get(v_s_726_, 11);
v_diseqs_739_ = lean_ctor_get(v_s_726_, 12);
v_recheck_740_ = lean_ctor_get_uint8(v_s_726_, sizeof(void*)*15);
v_invSet_741_ = lean_ctor_get(v_s_726_, 13);
v_numEq0_x3f_742_ = lean_ctor_get(v_s_726_, 14);
v_numEq0Updated_743_ = lean_ctor_get_uint8(v_s_726_, sizeof(void*)*15 + 1);
v_isSharedCheck_775_ = !lean_is_exclusive(v_s_726_);
if (v_isSharedCheck_775_ == 0)
{
v___x_745_ = v_s_726_;
v_isShared_746_ = v_isSharedCheck_775_;
goto v_resetjp_744_;
}
else
{
lean_inc(v_numEq0_x3f_742_);
lean_inc(v_invSet_741_);
lean_inc(v_diseqs_739_);
lean_inc(v_basis_738_);
lean_inc(v_queue_737_);
lean_inc(v_steps_736_);
lean_inc(v_nextId_735_);
lean_inc(v_denoteEntries_734_);
lean_inc(v_fieldInst_x3f_733_);
lean_inc(v_noZeroDivInst_x3f_732_);
lean_inc(v_commRingInst_731_);
lean_inc(v_commSemiringInst_730_);
lean_inc(v_semiringId_x3f_729_);
lean_inc(v_invFn_x3f_728_);
lean_inc(v_toRing_727_);
lean_dec(v_s_726_);
v___x_745_ = lean_box(0);
v_isShared_746_ = v_isSharedCheck_775_;
goto v_resetjp_744_;
}
v_resetjp_744_:
{
lean_object* v_id_747_; lean_object* v_type_748_; lean_object* v_u_749_; lean_object* v_ringInst_750_; lean_object* v_semiringInst_751_; lean_object* v_charInst_x3f_752_; lean_object* v_addFn_x3f_753_; lean_object* v_mulFn_x3f_754_; lean_object* v_subFn_x3f_755_; lean_object* v_negFn_x3f_756_; lean_object* v_powFn_x3f_757_; lean_object* v_intCastFn_x3f_758_; lean_object* v_one_x3f_759_; lean_object* v_vars_760_; lean_object* v_varMap_761_; lean_object* v_denote_762_; lean_object* v___x_764_; uint8_t v_isShared_765_; uint8_t v_isSharedCheck_773_; 
v_id_747_ = lean_ctor_get(v_toRing_727_, 0);
v_type_748_ = lean_ctor_get(v_toRing_727_, 1);
v_u_749_ = lean_ctor_get(v_toRing_727_, 2);
v_ringInst_750_ = lean_ctor_get(v_toRing_727_, 3);
v_semiringInst_751_ = lean_ctor_get(v_toRing_727_, 4);
v_charInst_x3f_752_ = lean_ctor_get(v_toRing_727_, 5);
v_addFn_x3f_753_ = lean_ctor_get(v_toRing_727_, 6);
v_mulFn_x3f_754_ = lean_ctor_get(v_toRing_727_, 7);
v_subFn_x3f_755_ = lean_ctor_get(v_toRing_727_, 8);
v_negFn_x3f_756_ = lean_ctor_get(v_toRing_727_, 9);
v_powFn_x3f_757_ = lean_ctor_get(v_toRing_727_, 10);
v_intCastFn_x3f_758_ = lean_ctor_get(v_toRing_727_, 11);
v_one_x3f_759_ = lean_ctor_get(v_toRing_727_, 13);
v_vars_760_ = lean_ctor_get(v_toRing_727_, 14);
v_varMap_761_ = lean_ctor_get(v_toRing_727_, 15);
v_denote_762_ = lean_ctor_get(v_toRing_727_, 16);
v_isSharedCheck_773_ = !lean_is_exclusive(v_toRing_727_);
if (v_isSharedCheck_773_ == 0)
{
lean_object* v_unused_774_; 
v_unused_774_ = lean_ctor_get(v_toRing_727_, 12);
lean_dec(v_unused_774_);
v___x_764_ = v_toRing_727_;
v_isShared_765_ = v_isSharedCheck_773_;
goto v_resetjp_763_;
}
else
{
lean_inc(v_denote_762_);
lean_inc(v_varMap_761_);
lean_inc(v_vars_760_);
lean_inc(v_one_x3f_759_);
lean_inc(v_intCastFn_x3f_758_);
lean_inc(v_powFn_x3f_757_);
lean_inc(v_negFn_x3f_756_);
lean_inc(v_subFn_x3f_755_);
lean_inc(v_mulFn_x3f_754_);
lean_inc(v_addFn_x3f_753_);
lean_inc(v_charInst_x3f_752_);
lean_inc(v_semiringInst_751_);
lean_inc(v_ringInst_750_);
lean_inc(v_u_749_);
lean_inc(v_type_748_);
lean_inc(v_id_747_);
lean_dec(v_toRing_727_);
v___x_764_ = lean_box(0);
v_isShared_765_ = v_isSharedCheck_773_;
goto v_resetjp_763_;
}
v_resetjp_763_:
{
lean_object* v___x_766_; lean_object* v___x_768_; 
v___x_766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_766_, 0, v_a_725_);
if (v_isShared_765_ == 0)
{
lean_ctor_set(v___x_764_, 12, v___x_766_);
v___x_768_ = v___x_764_;
goto v_reusejp_767_;
}
else
{
lean_object* v_reuseFailAlloc_772_; 
v_reuseFailAlloc_772_ = lean_alloc_ctor(0, 17, 0);
lean_ctor_set(v_reuseFailAlloc_772_, 0, v_id_747_);
lean_ctor_set(v_reuseFailAlloc_772_, 1, v_type_748_);
lean_ctor_set(v_reuseFailAlloc_772_, 2, v_u_749_);
lean_ctor_set(v_reuseFailAlloc_772_, 3, v_ringInst_750_);
lean_ctor_set(v_reuseFailAlloc_772_, 4, v_semiringInst_751_);
lean_ctor_set(v_reuseFailAlloc_772_, 5, v_charInst_x3f_752_);
lean_ctor_set(v_reuseFailAlloc_772_, 6, v_addFn_x3f_753_);
lean_ctor_set(v_reuseFailAlloc_772_, 7, v_mulFn_x3f_754_);
lean_ctor_set(v_reuseFailAlloc_772_, 8, v_subFn_x3f_755_);
lean_ctor_set(v_reuseFailAlloc_772_, 9, v_negFn_x3f_756_);
lean_ctor_set(v_reuseFailAlloc_772_, 10, v_powFn_x3f_757_);
lean_ctor_set(v_reuseFailAlloc_772_, 11, v_intCastFn_x3f_758_);
lean_ctor_set(v_reuseFailAlloc_772_, 12, v___x_766_);
lean_ctor_set(v_reuseFailAlloc_772_, 13, v_one_x3f_759_);
lean_ctor_set(v_reuseFailAlloc_772_, 14, v_vars_760_);
lean_ctor_set(v_reuseFailAlloc_772_, 15, v_varMap_761_);
lean_ctor_set(v_reuseFailAlloc_772_, 16, v_denote_762_);
v___x_768_ = v_reuseFailAlloc_772_;
goto v_reusejp_767_;
}
v_reusejp_767_:
{
lean_object* v___x_770_; 
if (v_isShared_746_ == 0)
{
lean_ctor_set(v___x_745_, 0, v___x_768_);
v___x_770_ = v___x_745_;
goto v_reusejp_769_;
}
else
{
lean_object* v_reuseFailAlloc_771_; 
v_reuseFailAlloc_771_ = lean_alloc_ctor(0, 15, 2);
lean_ctor_set(v_reuseFailAlloc_771_, 0, v___x_768_);
lean_ctor_set(v_reuseFailAlloc_771_, 1, v_invFn_x3f_728_);
lean_ctor_set(v_reuseFailAlloc_771_, 2, v_semiringId_x3f_729_);
lean_ctor_set(v_reuseFailAlloc_771_, 3, v_commSemiringInst_730_);
lean_ctor_set(v_reuseFailAlloc_771_, 4, v_commRingInst_731_);
lean_ctor_set(v_reuseFailAlloc_771_, 5, v_noZeroDivInst_x3f_732_);
lean_ctor_set(v_reuseFailAlloc_771_, 6, v_fieldInst_x3f_733_);
lean_ctor_set(v_reuseFailAlloc_771_, 7, v_denoteEntries_734_);
lean_ctor_set(v_reuseFailAlloc_771_, 8, v_nextId_735_);
lean_ctor_set(v_reuseFailAlloc_771_, 9, v_steps_736_);
lean_ctor_set(v_reuseFailAlloc_771_, 10, v_queue_737_);
lean_ctor_set(v_reuseFailAlloc_771_, 11, v_basis_738_);
lean_ctor_set(v_reuseFailAlloc_771_, 12, v_diseqs_739_);
lean_ctor_set(v_reuseFailAlloc_771_, 13, v_invSet_741_);
lean_ctor_set(v_reuseFailAlloc_771_, 14, v_numEq0_x3f_742_);
lean_ctor_set_uint8(v_reuseFailAlloc_771_, sizeof(void*)*15, v_recheck_740_);
lean_ctor_set_uint8(v_reuseFailAlloc_771_, sizeof(void*)*15 + 1, v_numEq0Updated_743_);
v___x_770_ = v_reuseFailAlloc_771_;
goto v_reusejp_769_;
}
v_reusejp_769_:
{
return v___x_770_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_getNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isNatCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__2_spec__4_spec__6___redArg(lean_object* v_u_784_, lean_object* v_type_785_, lean_object* v_semiringInst_786_, lean_object* v___y_787_, lean_object* v___y_788_, lean_object* v___y_789_, lean_object* v___y_790_, lean_object* v___y_791_, lean_object* v___y_792_){
_start:
{
lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v_inst_x27_798_; lean_object* v_inst_800_; lean_object* v___y_801_; lean_object* v___y_802_; lean_object* v___y_803_; lean_object* v___y_804_; lean_object* v___y_805_; lean_object* v___y_806_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v_instType_815_; lean_object* v___x_816_; 
v___x_794_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_getNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isNatCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__2_spec__4_spec__6___redArg___closed__1));
v___x_795_ = lean_box(0);
v___x_796_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_796_, 0, v_u_784_);
lean_ctor_set(v___x_796_, 1, v___x_795_);
lean_inc_ref_n(v___x_796_, 2);
v___x_797_ = l_Lean_mkConst(v___x_794_, v___x_796_);
lean_inc_ref_n(v_type_785_, 2);
v_inst_x27_798_ = l_Lean_mkAppB(v___x_797_, v_type_785_, v_semiringInst_786_);
v___x_813_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_getNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isNatCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__2_spec__4_spec__6___redArg___closed__2));
v___x_814_ = l_Lean_mkConst(v___x_813_, v___x_796_);
v_instType_815_ = l_Lean_Expr_app___override(v___x_814_, v_type_785_);
v___x_816_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f(v_instType_815_, v___y_789_, v___y_790_, v___y_791_, v___y_792_);
if (lean_obj_tag(v___x_816_) == 0)
{
lean_object* v_a_817_; 
v_a_817_ = lean_ctor_get(v___x_816_, 0);
lean_inc(v_a_817_);
lean_dec_ref(v___x_816_);
if (lean_obj_tag(v_a_817_) == 0)
{
v_inst_800_ = v_inst_x27_798_;
v___y_801_ = v___y_787_;
v___y_802_ = v___y_788_;
v___y_803_ = v___y_789_;
v___y_804_ = v___y_790_;
v___y_805_ = v___y_791_;
v___y_806_ = v___y_792_;
goto v___jp_799_;
}
else
{
lean_object* v_val_818_; lean_object* v___x_819_; lean_object* v___x_820_; 
v_val_818_ = lean_ctor_get(v_a_817_, 0);
lean_inc_n(v_val_818_, 2);
lean_dec_ref(v_a_817_);
v___x_819_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__5));
v___x_820_ = l_Lean_Meta_Grind_Arith_CommRing_checkInst(v___x_819_, v_val_818_, v_inst_x27_798_, v___y_789_, v___y_790_, v___y_791_, v___y_792_);
if (lean_obj_tag(v___x_820_) == 0)
{
lean_dec_ref(v___x_820_);
v_inst_800_ = v_val_818_;
v___y_801_ = v___y_787_;
v___y_802_ = v___y_788_;
v___y_803_ = v___y_789_;
v___y_804_ = v___y_790_;
v___y_805_ = v___y_791_;
v___y_806_ = v___y_792_;
goto v___jp_799_;
}
else
{
lean_object* v_a_821_; lean_object* v___x_823_; uint8_t v_isShared_824_; uint8_t v_isSharedCheck_828_; 
lean_dec(v_val_818_);
lean_dec_ref(v___x_796_);
lean_dec_ref(v_type_785_);
v_a_821_ = lean_ctor_get(v___x_820_, 0);
v_isSharedCheck_828_ = !lean_is_exclusive(v___x_820_);
if (v_isSharedCheck_828_ == 0)
{
v___x_823_ = v___x_820_;
v_isShared_824_ = v_isSharedCheck_828_;
goto v_resetjp_822_;
}
else
{
lean_inc(v_a_821_);
lean_dec(v___x_820_);
v___x_823_ = lean_box(0);
v_isShared_824_ = v_isSharedCheck_828_;
goto v_resetjp_822_;
}
v_resetjp_822_:
{
lean_object* v___x_826_; 
if (v_isShared_824_ == 0)
{
v___x_826_ = v___x_823_;
goto v_reusejp_825_;
}
else
{
lean_object* v_reuseFailAlloc_827_; 
v_reuseFailAlloc_827_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_827_, 0, v_a_821_);
v___x_826_ = v_reuseFailAlloc_827_;
goto v_reusejp_825_;
}
v_reusejp_825_:
{
return v___x_826_;
}
}
}
}
}
else
{
lean_object* v_a_829_; lean_object* v___x_831_; uint8_t v_isShared_832_; uint8_t v_isSharedCheck_836_; 
lean_dec_ref(v_inst_x27_798_);
lean_dec_ref(v___x_796_);
lean_dec_ref(v_type_785_);
v_a_829_ = lean_ctor_get(v___x_816_, 0);
v_isSharedCheck_836_ = !lean_is_exclusive(v___x_816_);
if (v_isSharedCheck_836_ == 0)
{
v___x_831_ = v___x_816_;
v_isShared_832_ = v_isSharedCheck_836_;
goto v_resetjp_830_;
}
else
{
lean_inc(v_a_829_);
lean_dec(v___x_816_);
v___x_831_ = lean_box(0);
v_isShared_832_ = v_isSharedCheck_836_;
goto v_resetjp_830_;
}
v_resetjp_830_:
{
lean_object* v___x_834_; 
if (v_isShared_832_ == 0)
{
v___x_834_ = v___x_831_;
goto v_reusejp_833_;
}
else
{
lean_object* v_reuseFailAlloc_835_; 
v_reuseFailAlloc_835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_835_, 0, v_a_829_);
v___x_834_ = v_reuseFailAlloc_835_;
goto v_reusejp_833_;
}
v_reusejp_833_:
{
return v___x_834_;
}
}
}
v___jp_799_:
{
lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; 
v___x_807_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__5));
v___x_808_ = l_Lean_mkConst(v___x_807_, v___x_796_);
v___x_809_ = l_Lean_mkAppB(v___x_808_, v_type_785_, v_inst_800_);
v___x_810_ = l_Lean_Meta_Sym_canon(v___x_809_, v___y_801_, v___y_802_, v___y_803_, v___y_804_, v___y_805_, v___y_806_);
if (lean_obj_tag(v___x_810_) == 0)
{
lean_object* v_a_811_; lean_object* v___x_812_; 
v_a_811_ = lean_ctor_get(v___x_810_, 0);
lean_inc(v_a_811_);
lean_dec_ref(v___x_810_);
v___x_812_ = l_Lean_Meta_Sym_shareCommon___redArg(v_a_811_, v___y_802_);
return v___x_812_;
}
else
{
return v___x_810_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_getNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isNatCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__2_spec__4_spec__6___redArg___boxed(lean_object* v_u_837_, lean_object* v_type_838_, lean_object* v_semiringInst_839_, lean_object* v___y_840_, lean_object* v___y_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_){
_start:
{
lean_object* v_res_847_; 
v_res_847_ = l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_getNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isNatCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__2_spec__4_spec__6___redArg(v_u_837_, v_type_838_, v_semiringInst_839_, v___y_840_, v___y_841_, v___y_842_, v___y_843_, v___y_844_, v___y_845_);
lean_dec(v___y_845_);
lean_dec_ref(v___y_844_);
lean_dec(v___y_843_);
lean_dec_ref(v___y_842_);
lean_dec(v___y_841_);
lean_dec_ref(v___y_840_);
return v_res_847_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isNatCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__2_spec__4(lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_, lean_object* v___y_852_, lean_object* v___y_853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_, lean_object* v___y_857_, lean_object* v___y_858_){
_start:
{
lean_object* v___x_860_; 
v___x_860_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v___y_848_, v___y_849_, v___y_850_, v___y_851_, v___y_852_, v___y_853_, v___y_854_, v___y_855_, v___y_856_, v___y_857_, v___y_858_);
if (lean_obj_tag(v___x_860_) == 0)
{
lean_object* v_a_861_; lean_object* v___x_863_; uint8_t v_isShared_864_; uint8_t v_isSharedCheck_894_; 
v_a_861_ = lean_ctor_get(v___x_860_, 0);
v_isSharedCheck_894_ = !lean_is_exclusive(v___x_860_);
if (v_isSharedCheck_894_ == 0)
{
v___x_863_ = v___x_860_;
v_isShared_864_ = v_isSharedCheck_894_;
goto v_resetjp_862_;
}
else
{
lean_inc(v_a_861_);
lean_dec(v___x_860_);
v___x_863_ = lean_box(0);
v_isShared_864_ = v_isSharedCheck_894_;
goto v_resetjp_862_;
}
v_resetjp_862_:
{
lean_object* v_toRing_865_; lean_object* v_natCastFn_x3f_866_; 
v_toRing_865_ = lean_ctor_get(v_a_861_, 0);
lean_inc_ref(v_toRing_865_);
lean_dec(v_a_861_);
v_natCastFn_x3f_866_ = lean_ctor_get(v_toRing_865_, 12);
if (lean_obj_tag(v_natCastFn_x3f_866_) == 1)
{
lean_object* v_val_867_; lean_object* v___x_869_; 
lean_inc_ref(v_natCastFn_x3f_866_);
lean_dec_ref(v_toRing_865_);
v_val_867_ = lean_ctor_get(v_natCastFn_x3f_866_, 0);
lean_inc(v_val_867_);
lean_dec_ref(v_natCastFn_x3f_866_);
if (v_isShared_864_ == 0)
{
lean_ctor_set(v___x_863_, 0, v_val_867_);
v___x_869_ = v___x_863_;
goto v_reusejp_868_;
}
else
{
lean_object* v_reuseFailAlloc_870_; 
v_reuseFailAlloc_870_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_870_, 0, v_val_867_);
v___x_869_ = v_reuseFailAlloc_870_;
goto v_reusejp_868_;
}
v_reusejp_868_:
{
return v___x_869_;
}
}
else
{
lean_object* v_type_871_; lean_object* v_u_872_; lean_object* v_semiringInst_873_; lean_object* v___x_874_; 
lean_del_object(v___x_863_);
v_type_871_ = lean_ctor_get(v_toRing_865_, 1);
lean_inc_ref(v_type_871_);
v_u_872_ = lean_ctor_get(v_toRing_865_, 2);
lean_inc(v_u_872_);
v_semiringInst_873_ = lean_ctor_get(v_toRing_865_, 4);
lean_inc_ref(v_semiringInst_873_);
lean_dec_ref(v_toRing_865_);
v___x_874_ = l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_getNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isNatCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__2_spec__4_spec__6___redArg(v_u_872_, v_type_871_, v_semiringInst_873_, v___y_853_, v___y_854_, v___y_855_, v___y_856_, v___y_857_, v___y_858_);
if (lean_obj_tag(v___x_874_) == 0)
{
lean_object* v_a_875_; lean_object* v___f_876_; lean_object* v___x_877_; 
v_a_875_ = lean_ctor_get(v___x_874_, 0);
lean_inc_n(v_a_875_, 2);
lean_dec_ref(v___x_874_);
v___f_876_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isNatCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__2_spec__4___lam__0), 2, 1);
lean_closure_set(v___f_876_, 0, v_a_875_);
v___x_877_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(v___f_876_, v___y_848_, v___y_849_);
if (lean_obj_tag(v___x_877_) == 0)
{
lean_object* v___x_879_; uint8_t v_isShared_880_; uint8_t v_isSharedCheck_884_; 
v_isSharedCheck_884_ = !lean_is_exclusive(v___x_877_);
if (v_isSharedCheck_884_ == 0)
{
lean_object* v_unused_885_; 
v_unused_885_ = lean_ctor_get(v___x_877_, 0);
lean_dec(v_unused_885_);
v___x_879_ = v___x_877_;
v_isShared_880_ = v_isSharedCheck_884_;
goto v_resetjp_878_;
}
else
{
lean_dec(v___x_877_);
v___x_879_ = lean_box(0);
v_isShared_880_ = v_isSharedCheck_884_;
goto v_resetjp_878_;
}
v_resetjp_878_:
{
lean_object* v___x_882_; 
if (v_isShared_880_ == 0)
{
lean_ctor_set(v___x_879_, 0, v_a_875_);
v___x_882_ = v___x_879_;
goto v_reusejp_881_;
}
else
{
lean_object* v_reuseFailAlloc_883_; 
v_reuseFailAlloc_883_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_883_, 0, v_a_875_);
v___x_882_ = v_reuseFailAlloc_883_;
goto v_reusejp_881_;
}
v_reusejp_881_:
{
return v___x_882_;
}
}
}
else
{
lean_object* v_a_886_; lean_object* v___x_888_; uint8_t v_isShared_889_; uint8_t v_isSharedCheck_893_; 
lean_dec(v_a_875_);
v_a_886_ = lean_ctor_get(v___x_877_, 0);
v_isSharedCheck_893_ = !lean_is_exclusive(v___x_877_);
if (v_isSharedCheck_893_ == 0)
{
v___x_888_ = v___x_877_;
v_isShared_889_ = v_isSharedCheck_893_;
goto v_resetjp_887_;
}
else
{
lean_inc(v_a_886_);
lean_dec(v___x_877_);
v___x_888_ = lean_box(0);
v_isShared_889_ = v_isSharedCheck_893_;
goto v_resetjp_887_;
}
v_resetjp_887_:
{
lean_object* v___x_891_; 
if (v_isShared_889_ == 0)
{
v___x_891_ = v___x_888_;
goto v_reusejp_890_;
}
else
{
lean_object* v_reuseFailAlloc_892_; 
v_reuseFailAlloc_892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_892_, 0, v_a_886_);
v___x_891_ = v_reuseFailAlloc_892_;
goto v_reusejp_890_;
}
v_reusejp_890_:
{
return v___x_891_;
}
}
}
}
else
{
return v___x_874_;
}
}
}
}
else
{
lean_object* v_a_895_; lean_object* v___x_897_; uint8_t v_isShared_898_; uint8_t v_isSharedCheck_902_; 
v_a_895_ = lean_ctor_get(v___x_860_, 0);
v_isSharedCheck_902_ = !lean_is_exclusive(v___x_860_);
if (v_isSharedCheck_902_ == 0)
{
v___x_897_ = v___x_860_;
v_isShared_898_ = v_isSharedCheck_902_;
goto v_resetjp_896_;
}
else
{
lean_inc(v_a_895_);
lean_dec(v___x_860_);
v___x_897_ = lean_box(0);
v_isShared_898_ = v_isSharedCheck_902_;
goto v_resetjp_896_;
}
v_resetjp_896_:
{
lean_object* v___x_900_; 
if (v_isShared_898_ == 0)
{
v___x_900_ = v___x_897_;
goto v_reusejp_899_;
}
else
{
lean_object* v_reuseFailAlloc_901_; 
v_reuseFailAlloc_901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_901_, 0, v_a_895_);
v___x_900_ = v_reuseFailAlloc_901_;
goto v_reusejp_899_;
}
v_reusejp_899_:
{
return v___x_900_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isNatCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__2_spec__4___boxed(lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_, lean_object* v___y_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_){
_start:
{
lean_object* v_res_915_; 
v_res_915_ = l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isNatCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__2_spec__4(v___y_903_, v___y_904_, v___y_905_, v___y_906_, v___y_907_, v___y_908_, v___y_909_, v___y_910_, v___y_911_, v___y_912_, v___y_913_);
lean_dec(v___y_913_);
lean_dec_ref(v___y_912_);
lean_dec(v___y_911_);
lean_dec_ref(v___y_910_);
lean_dec(v___y_909_);
lean_dec_ref(v___y_908_);
lean_dec(v___y_907_);
lean_dec_ref(v___y_906_);
lean_dec(v___y_905_);
lean_dec(v___y_904_);
lean_dec_ref(v___y_903_);
return v_res_915_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_isNatCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__2(lean_object* v_inst_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_){
_start:
{
lean_object* v___x_929_; 
v___x_929_ = l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isNatCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__2_spec__4(v___y_917_, v___y_918_, v___y_919_, v___y_920_, v___y_921_, v___y_922_, v___y_923_, v___y_924_, v___y_925_, v___y_926_, v___y_927_);
if (lean_obj_tag(v___x_929_) == 0)
{
lean_object* v_a_930_; lean_object* v___x_932_; uint8_t v_isShared_933_; uint8_t v_isSharedCheck_940_; 
v_a_930_ = lean_ctor_get(v___x_929_, 0);
v_isSharedCheck_940_ = !lean_is_exclusive(v___x_929_);
if (v_isSharedCheck_940_ == 0)
{
v___x_932_ = v___x_929_;
v_isShared_933_ = v_isSharedCheck_940_;
goto v_resetjp_931_;
}
else
{
lean_inc(v_a_930_);
lean_dec(v___x_929_);
v___x_932_ = lean_box(0);
v_isShared_933_ = v_isSharedCheck_940_;
goto v_resetjp_931_;
}
v_resetjp_931_:
{
lean_object* v___x_934_; uint8_t v___x_935_; lean_object* v___x_936_; lean_object* v___x_938_; 
v___x_934_ = l_Lean_Expr_appArg_x21(v_a_930_);
lean_dec(v_a_930_);
v___x_935_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v___x_934_, v_inst_916_);
lean_dec_ref(v___x_934_);
v___x_936_ = lean_box(v___x_935_);
if (v_isShared_933_ == 0)
{
lean_ctor_set(v___x_932_, 0, v___x_936_);
v___x_938_ = v___x_932_;
goto v_reusejp_937_;
}
else
{
lean_object* v_reuseFailAlloc_939_; 
v_reuseFailAlloc_939_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_939_, 0, v___x_936_);
v___x_938_ = v_reuseFailAlloc_939_;
goto v_reusejp_937_;
}
v_reusejp_937_:
{
return v___x_938_;
}
}
}
else
{
lean_object* v_a_941_; lean_object* v___x_943_; uint8_t v_isShared_944_; uint8_t v_isSharedCheck_948_; 
v_a_941_ = lean_ctor_get(v___x_929_, 0);
v_isSharedCheck_948_ = !lean_is_exclusive(v___x_929_);
if (v_isSharedCheck_948_ == 0)
{
v___x_943_ = v___x_929_;
v_isShared_944_ = v_isSharedCheck_948_;
goto v_resetjp_942_;
}
else
{
lean_inc(v_a_941_);
lean_dec(v___x_929_);
v___x_943_ = lean_box(0);
v_isShared_944_ = v_isSharedCheck_948_;
goto v_resetjp_942_;
}
v_resetjp_942_:
{
lean_object* v___x_946_; 
if (v_isShared_944_ == 0)
{
v___x_946_ = v___x_943_;
goto v_reusejp_945_;
}
else
{
lean_object* v_reuseFailAlloc_947_; 
v_reuseFailAlloc_947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_947_, 0, v_a_941_);
v___x_946_ = v_reuseFailAlloc_947_;
goto v_reusejp_945_;
}
v_reusejp_945_:
{
return v___x_946_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_isNatCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__2___boxed(lean_object* v_inst_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_){
_start:
{
lean_object* v_res_962_; 
v_res_962_ = l_Lean_Meta_Grind_Arith_CommRing_isNatCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__2(v_inst_949_, v___y_950_, v___y_951_, v___y_952_, v___y_953_, v___y_954_, v___y_955_, v___y_956_, v___y_957_, v___y_958_, v___y_959_, v___y_960_);
lean_dec(v___y_960_);
lean_dec_ref(v___y_959_);
lean_dec(v___y_958_);
lean_dec_ref(v___y_957_);
lean_dec(v___y_956_);
lean_dec_ref(v___y_955_);
lean_dec(v___y_954_);
lean_dec_ref(v___y_953_);
lean_dec(v___y_952_);
lean_dec(v___y_951_);
lean_dec_ref(v___y_950_);
lean_dec_ref(v_inst_949_);
return v_res_962_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f(lean_object* v_e_963_, lean_object* v_a_964_, lean_object* v_a_965_, lean_object* v_a_966_, lean_object* v_a_967_, lean_object* v_a_968_, lean_object* v_a_969_, lean_object* v_a_970_, lean_object* v_a_971_, lean_object* v_a_972_, lean_object* v_a_973_, lean_object* v_a_974_){
_start:
{
lean_object* v___x_976_; 
v___x_976_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_963_, v_a_972_);
if (lean_obj_tag(v___x_976_) == 0)
{
lean_object* v_a_977_; lean_object* v___x_979_; uint8_t v_isShared_980_; uint8_t v_isSharedCheck_1140_; 
v_a_977_ = lean_ctor_get(v___x_976_, 0);
v_isSharedCheck_1140_ = !lean_is_exclusive(v___x_976_);
if (v_isSharedCheck_1140_ == 0)
{
v___x_979_ = v___x_976_;
v_isShared_980_ = v_isSharedCheck_1140_;
goto v_resetjp_978_;
}
else
{
lean_inc(v_a_977_);
lean_dec(v___x_976_);
v___x_979_ = lean_box(0);
v_isShared_980_ = v_isSharedCheck_1140_;
goto v_resetjp_978_;
}
v_resetjp_978_:
{
lean_object* v___x_986_; uint8_t v___x_987_; 
v___x_986_ = l_Lean_Expr_cleanupAnnotations(v_a_977_);
v___x_987_ = l_Lean_Expr_isApp(v___x_986_);
if (v___x_987_ == 0)
{
lean_dec_ref(v___x_986_);
goto v___jp_981_;
}
else
{
lean_object* v_arg_988_; lean_object* v___x_989_; uint8_t v___x_990_; 
v_arg_988_ = lean_ctor_get(v___x_986_, 1);
lean_inc_ref(v_arg_988_);
v___x_989_ = l_Lean_Expr_appFnCleanup___redArg(v___x_986_);
v___x_990_ = l_Lean_Expr_isApp(v___x_989_);
if (v___x_990_ == 0)
{
lean_dec_ref(v___x_989_);
lean_dec_ref(v_arg_988_);
goto v___jp_981_;
}
else
{
lean_object* v_arg_991_; lean_object* v___x_992_; uint8_t v___x_993_; 
v_arg_991_ = lean_ctor_get(v___x_989_, 1);
lean_inc_ref(v_arg_991_);
v___x_992_ = l_Lean_Expr_appFnCleanup___redArg(v___x_989_);
v___x_993_ = l_Lean_Expr_isApp(v___x_992_);
if (v___x_993_ == 0)
{
lean_dec_ref(v___x_992_);
lean_dec_ref(v_arg_991_);
lean_dec_ref(v_arg_988_);
goto v___jp_981_;
}
else
{
lean_object* v___x_994_; lean_object* v___x_995_; uint8_t v___x_996_; 
v___x_994_ = l_Lean_Expr_appFnCleanup___redArg(v___x_992_);
v___x_995_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__8));
v___x_996_ = l_Lean_Expr_isConstOf(v___x_994_, v___x_995_);
if (v___x_996_ == 0)
{
lean_object* v___x_997_; uint8_t v___x_998_; 
v___x_997_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__5));
v___x_998_ = l_Lean_Expr_isConstOf(v___x_994_, v___x_997_);
if (v___x_998_ == 0)
{
lean_object* v___x_999_; uint8_t v___x_1000_; 
v___x_999_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__2));
v___x_1000_ = l_Lean_Expr_isConstOf(v___x_994_, v___x_999_);
if (v___x_1000_ == 0)
{
lean_object* v___x_1001_; uint8_t v___x_1002_; 
v___x_1001_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__11));
v___x_1002_ = l_Lean_Expr_isConstOf(v___x_994_, v___x_1001_);
lean_dec_ref(v___x_994_);
if (v___x_1002_ == 0)
{
lean_dec_ref(v_arg_991_);
lean_dec_ref(v_arg_988_);
goto v___jp_981_;
}
else
{
lean_object* v___x_1003_; 
lean_del_object(v___x_979_);
v___x_1003_ = l_Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0(v_arg_991_, v_a_964_, v_a_965_, v_a_966_, v_a_967_, v_a_968_, v_a_969_, v_a_970_, v_a_971_, v_a_972_, v_a_973_, v_a_974_);
lean_dec_ref(v_arg_991_);
if (lean_obj_tag(v___x_1003_) == 0)
{
lean_object* v_a_1004_; lean_object* v___x_1006_; uint8_t v_isShared_1007_; uint8_t v_isSharedCheck_1032_; 
v_a_1004_ = lean_ctor_get(v___x_1003_, 0);
v_isSharedCheck_1032_ = !lean_is_exclusive(v___x_1003_);
if (v_isSharedCheck_1032_ == 0)
{
v___x_1006_ = v___x_1003_;
v_isShared_1007_ = v_isSharedCheck_1032_;
goto v_resetjp_1005_;
}
else
{
lean_inc(v_a_1004_);
lean_dec(v___x_1003_);
v___x_1006_ = lean_box(0);
v_isShared_1007_ = v_isSharedCheck_1032_;
goto v_resetjp_1005_;
}
v_resetjp_1005_:
{
uint8_t v___x_1008_; 
v___x_1008_ = lean_unbox(v_a_1004_);
lean_dec(v_a_1004_);
if (v___x_1008_ == 0)
{
lean_object* v___x_1009_; lean_object* v___x_1011_; 
lean_dec_ref(v_arg_988_);
v___x_1009_ = lean_box(0);
if (v_isShared_1007_ == 0)
{
lean_ctor_set(v___x_1006_, 0, v___x_1009_);
v___x_1011_ = v___x_1006_;
goto v_reusejp_1010_;
}
else
{
lean_object* v_reuseFailAlloc_1012_; 
v_reuseFailAlloc_1012_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1012_, 0, v___x_1009_);
v___x_1011_ = v_reuseFailAlloc_1012_;
goto v_reusejp_1010_;
}
v_reusejp_1010_:
{
return v___x_1011_;
}
}
else
{
lean_object* v___x_1013_; 
lean_del_object(v___x_1006_);
v___x_1013_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f(v_arg_988_, v_a_964_, v_a_965_, v_a_966_, v_a_967_, v_a_968_, v_a_969_, v_a_970_, v_a_971_, v_a_972_, v_a_973_, v_a_974_);
if (lean_obj_tag(v___x_1013_) == 0)
{
lean_object* v_a_1014_; 
v_a_1014_ = lean_ctor_get(v___x_1013_, 0);
lean_inc(v_a_1014_);
if (lean_obj_tag(v_a_1014_) == 0)
{
return v___x_1013_;
}
else
{
lean_object* v___x_1016_; uint8_t v_isShared_1017_; uint8_t v_isSharedCheck_1030_; 
v_isSharedCheck_1030_ = !lean_is_exclusive(v___x_1013_);
if (v_isSharedCheck_1030_ == 0)
{
lean_object* v_unused_1031_; 
v_unused_1031_ = lean_ctor_get(v___x_1013_, 0);
lean_dec(v_unused_1031_);
v___x_1016_ = v___x_1013_;
v_isShared_1017_ = v_isSharedCheck_1030_;
goto v_resetjp_1015_;
}
else
{
lean_dec(v___x_1013_);
v___x_1016_ = lean_box(0);
v_isShared_1017_ = v_isSharedCheck_1030_;
goto v_resetjp_1015_;
}
v_resetjp_1015_:
{
lean_object* v_val_1018_; lean_object* v___x_1020_; uint8_t v_isShared_1021_; uint8_t v_isSharedCheck_1029_; 
v_val_1018_ = lean_ctor_get(v_a_1014_, 0);
v_isSharedCheck_1029_ = !lean_is_exclusive(v_a_1014_);
if (v_isSharedCheck_1029_ == 0)
{
v___x_1020_ = v_a_1014_;
v_isShared_1021_ = v_isSharedCheck_1029_;
goto v_resetjp_1019_;
}
else
{
lean_inc(v_val_1018_);
lean_dec(v_a_1014_);
v___x_1020_ = lean_box(0);
v_isShared_1021_ = v_isSharedCheck_1029_;
goto v_resetjp_1019_;
}
v_resetjp_1019_:
{
lean_object* v___x_1022_; lean_object* v___x_1024_; 
v___x_1022_ = lean_int_neg(v_val_1018_);
lean_dec(v_val_1018_);
if (v_isShared_1021_ == 0)
{
lean_ctor_set(v___x_1020_, 0, v___x_1022_);
v___x_1024_ = v___x_1020_;
goto v_reusejp_1023_;
}
else
{
lean_object* v_reuseFailAlloc_1028_; 
v_reuseFailAlloc_1028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1028_, 0, v___x_1022_);
v___x_1024_ = v_reuseFailAlloc_1028_;
goto v_reusejp_1023_;
}
v_reusejp_1023_:
{
lean_object* v___x_1026_; 
if (v_isShared_1017_ == 0)
{
lean_ctor_set(v___x_1016_, 0, v___x_1024_);
v___x_1026_ = v___x_1016_;
goto v_reusejp_1025_;
}
else
{
lean_object* v_reuseFailAlloc_1027_; 
v_reuseFailAlloc_1027_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1027_, 0, v___x_1024_);
v___x_1026_ = v_reuseFailAlloc_1027_;
goto v_reusejp_1025_;
}
v_reusejp_1025_:
{
return v___x_1026_;
}
}
}
}
}
}
else
{
return v___x_1013_;
}
}
}
}
else
{
lean_object* v_a_1033_; lean_object* v___x_1035_; uint8_t v_isShared_1036_; uint8_t v_isSharedCheck_1040_; 
lean_dec_ref(v_arg_988_);
v_a_1033_ = lean_ctor_get(v___x_1003_, 0);
v_isSharedCheck_1040_ = !lean_is_exclusive(v___x_1003_);
if (v_isSharedCheck_1040_ == 0)
{
v___x_1035_ = v___x_1003_;
v_isShared_1036_ = v_isSharedCheck_1040_;
goto v_resetjp_1034_;
}
else
{
lean_inc(v_a_1033_);
lean_dec(v___x_1003_);
v___x_1035_ = lean_box(0);
v_isShared_1036_ = v_isSharedCheck_1040_;
goto v_resetjp_1034_;
}
v_resetjp_1034_:
{
lean_object* v___x_1038_; 
if (v_isShared_1036_ == 0)
{
v___x_1038_ = v___x_1035_;
goto v_reusejp_1037_;
}
else
{
lean_object* v_reuseFailAlloc_1039_; 
v_reuseFailAlloc_1039_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1039_, 0, v_a_1033_);
v___x_1038_ = v_reuseFailAlloc_1039_;
goto v_reusejp_1037_;
}
v_reusejp_1037_:
{
return v___x_1038_;
}
}
}
}
}
else
{
lean_object* v___x_1041_; 
lean_dec_ref(v___x_994_);
lean_del_object(v___x_979_);
v___x_1041_ = l_Lean_Meta_Grind_Arith_CommRing_isIntCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__1(v_arg_991_, v_a_964_, v_a_965_, v_a_966_, v_a_967_, v_a_968_, v_a_969_, v_a_970_, v_a_971_, v_a_972_, v_a_973_, v_a_974_);
lean_dec_ref(v_arg_991_);
if (lean_obj_tag(v___x_1041_) == 0)
{
lean_object* v_a_1042_; lean_object* v___x_1044_; uint8_t v_isShared_1045_; uint8_t v_isSharedCheck_1052_; 
v_a_1042_ = lean_ctor_get(v___x_1041_, 0);
v_isSharedCheck_1052_ = !lean_is_exclusive(v___x_1041_);
if (v_isSharedCheck_1052_ == 0)
{
v___x_1044_ = v___x_1041_;
v_isShared_1045_ = v_isSharedCheck_1052_;
goto v_resetjp_1043_;
}
else
{
lean_inc(v_a_1042_);
lean_dec(v___x_1041_);
v___x_1044_ = lean_box(0);
v_isShared_1045_ = v_isSharedCheck_1052_;
goto v_resetjp_1043_;
}
v_resetjp_1043_:
{
uint8_t v___x_1046_; 
v___x_1046_ = lean_unbox(v_a_1042_);
lean_dec(v_a_1042_);
if (v___x_1046_ == 0)
{
lean_object* v___x_1047_; lean_object* v___x_1049_; 
lean_dec_ref(v_arg_988_);
v___x_1047_ = lean_box(0);
if (v_isShared_1045_ == 0)
{
lean_ctor_set(v___x_1044_, 0, v___x_1047_);
v___x_1049_ = v___x_1044_;
goto v_reusejp_1048_;
}
else
{
lean_object* v_reuseFailAlloc_1050_; 
v_reuseFailAlloc_1050_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1050_, 0, v___x_1047_);
v___x_1049_ = v_reuseFailAlloc_1050_;
goto v_reusejp_1048_;
}
v_reusejp_1048_:
{
return v___x_1049_;
}
}
else
{
lean_object* v___x_1051_; 
lean_del_object(v___x_1044_);
v___x_1051_ = l_Lean_Meta_getIntValue_x3f(v_arg_988_, v_a_971_, v_a_972_, v_a_973_, v_a_974_);
return v___x_1051_;
}
}
}
else
{
lean_object* v_a_1053_; lean_object* v___x_1055_; uint8_t v_isShared_1056_; uint8_t v_isSharedCheck_1060_; 
lean_dec_ref(v_arg_988_);
v_a_1053_ = lean_ctor_get(v___x_1041_, 0);
v_isSharedCheck_1060_ = !lean_is_exclusive(v___x_1041_);
if (v_isSharedCheck_1060_ == 0)
{
v___x_1055_ = v___x_1041_;
v_isShared_1056_ = v_isSharedCheck_1060_;
goto v_resetjp_1054_;
}
else
{
lean_inc(v_a_1053_);
lean_dec(v___x_1041_);
v___x_1055_ = lean_box(0);
v_isShared_1056_ = v_isSharedCheck_1060_;
goto v_resetjp_1054_;
}
v_resetjp_1054_:
{
lean_object* v___x_1058_; 
if (v_isShared_1056_ == 0)
{
v___x_1058_ = v___x_1055_;
goto v_reusejp_1057_;
}
else
{
lean_object* v_reuseFailAlloc_1059_; 
v_reuseFailAlloc_1059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1059_, 0, v_a_1053_);
v___x_1058_ = v_reuseFailAlloc_1059_;
goto v_reusejp_1057_;
}
v_reusejp_1057_:
{
return v___x_1058_;
}
}
}
}
}
else
{
lean_object* v___x_1061_; 
lean_dec_ref(v___x_994_);
lean_del_object(v___x_979_);
v___x_1061_ = l_Lean_Meta_Grind_Arith_CommRing_isNatCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__2(v_arg_991_, v_a_964_, v_a_965_, v_a_966_, v_a_967_, v_a_968_, v_a_969_, v_a_970_, v_a_971_, v_a_972_, v_a_973_, v_a_974_);
lean_dec_ref(v_arg_991_);
if (lean_obj_tag(v___x_1061_) == 0)
{
lean_object* v_a_1062_; lean_object* v___x_1064_; uint8_t v_isShared_1065_; uint8_t v_isSharedCheck_1101_; 
v_a_1062_ = lean_ctor_get(v___x_1061_, 0);
v_isSharedCheck_1101_ = !lean_is_exclusive(v___x_1061_);
if (v_isSharedCheck_1101_ == 0)
{
v___x_1064_ = v___x_1061_;
v_isShared_1065_ = v_isSharedCheck_1101_;
goto v_resetjp_1063_;
}
else
{
lean_inc(v_a_1062_);
lean_dec(v___x_1061_);
v___x_1064_ = lean_box(0);
v_isShared_1065_ = v_isSharedCheck_1101_;
goto v_resetjp_1063_;
}
v_resetjp_1063_:
{
uint8_t v___x_1066_; 
v___x_1066_ = lean_unbox(v_a_1062_);
lean_dec(v_a_1062_);
if (v___x_1066_ == 0)
{
lean_object* v___x_1067_; lean_object* v___x_1069_; 
lean_dec_ref(v_arg_988_);
v___x_1067_ = lean_box(0);
if (v_isShared_1065_ == 0)
{
lean_ctor_set(v___x_1064_, 0, v___x_1067_);
v___x_1069_ = v___x_1064_;
goto v_reusejp_1068_;
}
else
{
lean_object* v_reuseFailAlloc_1070_; 
v_reuseFailAlloc_1070_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1070_, 0, v___x_1067_);
v___x_1069_ = v_reuseFailAlloc_1070_;
goto v_reusejp_1068_;
}
v_reusejp_1068_:
{
return v___x_1069_;
}
}
else
{
lean_object* v___x_1071_; 
lean_del_object(v___x_1064_);
v___x_1071_ = l_Lean_Meta_getNatValue_x3f(v_arg_988_, v_a_971_, v_a_972_, v_a_973_, v_a_974_);
lean_dec_ref(v_arg_988_);
if (lean_obj_tag(v___x_1071_) == 0)
{
lean_object* v_a_1072_; lean_object* v___x_1074_; uint8_t v_isShared_1075_; uint8_t v_isSharedCheck_1092_; 
v_a_1072_ = lean_ctor_get(v___x_1071_, 0);
v_isSharedCheck_1092_ = !lean_is_exclusive(v___x_1071_);
if (v_isSharedCheck_1092_ == 0)
{
v___x_1074_ = v___x_1071_;
v_isShared_1075_ = v_isSharedCheck_1092_;
goto v_resetjp_1073_;
}
else
{
lean_inc(v_a_1072_);
lean_dec(v___x_1071_);
v___x_1074_ = lean_box(0);
v_isShared_1075_ = v_isSharedCheck_1092_;
goto v_resetjp_1073_;
}
v_resetjp_1073_:
{
if (lean_obj_tag(v_a_1072_) == 1)
{
lean_object* v_val_1076_; lean_object* v___x_1078_; uint8_t v_isShared_1079_; uint8_t v_isSharedCheck_1087_; 
v_val_1076_ = lean_ctor_get(v_a_1072_, 0);
v_isSharedCheck_1087_ = !lean_is_exclusive(v_a_1072_);
if (v_isSharedCheck_1087_ == 0)
{
v___x_1078_ = v_a_1072_;
v_isShared_1079_ = v_isSharedCheck_1087_;
goto v_resetjp_1077_;
}
else
{
lean_inc(v_val_1076_);
lean_dec(v_a_1072_);
v___x_1078_ = lean_box(0);
v_isShared_1079_ = v_isSharedCheck_1087_;
goto v_resetjp_1077_;
}
v_resetjp_1077_:
{
lean_object* v___x_1080_; lean_object* v___x_1082_; 
v___x_1080_ = lean_nat_to_int(v_val_1076_);
if (v_isShared_1079_ == 0)
{
lean_ctor_set(v___x_1078_, 0, v___x_1080_);
v___x_1082_ = v___x_1078_;
goto v_reusejp_1081_;
}
else
{
lean_object* v_reuseFailAlloc_1086_; 
v_reuseFailAlloc_1086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1086_, 0, v___x_1080_);
v___x_1082_ = v_reuseFailAlloc_1086_;
goto v_reusejp_1081_;
}
v_reusejp_1081_:
{
lean_object* v___x_1084_; 
if (v_isShared_1075_ == 0)
{
lean_ctor_set(v___x_1074_, 0, v___x_1082_);
v___x_1084_ = v___x_1074_;
goto v_reusejp_1083_;
}
else
{
lean_object* v_reuseFailAlloc_1085_; 
v_reuseFailAlloc_1085_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1085_, 0, v___x_1082_);
v___x_1084_ = v_reuseFailAlloc_1085_;
goto v_reusejp_1083_;
}
v_reusejp_1083_:
{
return v___x_1084_;
}
}
}
}
else
{
lean_object* v___x_1088_; lean_object* v___x_1090_; 
lean_dec(v_a_1072_);
v___x_1088_ = lean_box(0);
if (v_isShared_1075_ == 0)
{
lean_ctor_set(v___x_1074_, 0, v___x_1088_);
v___x_1090_ = v___x_1074_;
goto v_reusejp_1089_;
}
else
{
lean_object* v_reuseFailAlloc_1091_; 
v_reuseFailAlloc_1091_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1091_, 0, v___x_1088_);
v___x_1090_ = v_reuseFailAlloc_1091_;
goto v_reusejp_1089_;
}
v_reusejp_1089_:
{
return v___x_1090_;
}
}
}
}
else
{
lean_object* v_a_1093_; lean_object* v___x_1095_; uint8_t v_isShared_1096_; uint8_t v_isSharedCheck_1100_; 
v_a_1093_ = lean_ctor_get(v___x_1071_, 0);
v_isSharedCheck_1100_ = !lean_is_exclusive(v___x_1071_);
if (v_isSharedCheck_1100_ == 0)
{
v___x_1095_ = v___x_1071_;
v_isShared_1096_ = v_isSharedCheck_1100_;
goto v_resetjp_1094_;
}
else
{
lean_inc(v_a_1093_);
lean_dec(v___x_1071_);
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
}
else
{
lean_object* v_a_1102_; lean_object* v___x_1104_; uint8_t v_isShared_1105_; uint8_t v_isSharedCheck_1109_; 
lean_dec_ref(v_arg_988_);
v_a_1102_ = lean_ctor_get(v___x_1061_, 0);
v_isSharedCheck_1109_ = !lean_is_exclusive(v___x_1061_);
if (v_isSharedCheck_1109_ == 0)
{
v___x_1104_ = v___x_1061_;
v_isShared_1105_ = v_isSharedCheck_1109_;
goto v_resetjp_1103_;
}
else
{
lean_inc(v_a_1102_);
lean_dec(v___x_1061_);
v___x_1104_ = lean_box(0);
v_isShared_1105_ = v_isSharedCheck_1109_;
goto v_resetjp_1103_;
}
v_resetjp_1103_:
{
lean_object* v___x_1107_; 
if (v_isShared_1105_ == 0)
{
v___x_1107_ = v___x_1104_;
goto v_reusejp_1106_;
}
else
{
lean_object* v_reuseFailAlloc_1108_; 
v_reuseFailAlloc_1108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1108_, 0, v_a_1102_);
v___x_1107_ = v_reuseFailAlloc_1108_;
goto v_reusejp_1106_;
}
v_reusejp_1106_:
{
return v___x_1107_;
}
}
}
}
}
else
{
lean_object* v___x_1110_; 
lean_dec_ref(v___x_994_);
lean_dec_ref(v_arg_988_);
lean_del_object(v___x_979_);
v___x_1110_ = l_Lean_Meta_getNatValue_x3f(v_arg_991_, v_a_971_, v_a_972_, v_a_973_, v_a_974_);
lean_dec_ref(v_arg_991_);
if (lean_obj_tag(v___x_1110_) == 0)
{
lean_object* v_a_1111_; lean_object* v___x_1113_; uint8_t v_isShared_1114_; uint8_t v_isSharedCheck_1131_; 
v_a_1111_ = lean_ctor_get(v___x_1110_, 0);
v_isSharedCheck_1131_ = !lean_is_exclusive(v___x_1110_);
if (v_isSharedCheck_1131_ == 0)
{
v___x_1113_ = v___x_1110_;
v_isShared_1114_ = v_isSharedCheck_1131_;
goto v_resetjp_1112_;
}
else
{
lean_inc(v_a_1111_);
lean_dec(v___x_1110_);
v___x_1113_ = lean_box(0);
v_isShared_1114_ = v_isSharedCheck_1131_;
goto v_resetjp_1112_;
}
v_resetjp_1112_:
{
if (lean_obj_tag(v_a_1111_) == 1)
{
lean_object* v_val_1115_; lean_object* v___x_1117_; uint8_t v_isShared_1118_; uint8_t v_isSharedCheck_1126_; 
v_val_1115_ = lean_ctor_get(v_a_1111_, 0);
v_isSharedCheck_1126_ = !lean_is_exclusive(v_a_1111_);
if (v_isSharedCheck_1126_ == 0)
{
v___x_1117_ = v_a_1111_;
v_isShared_1118_ = v_isSharedCheck_1126_;
goto v_resetjp_1116_;
}
else
{
lean_inc(v_val_1115_);
lean_dec(v_a_1111_);
v___x_1117_ = lean_box(0);
v_isShared_1118_ = v_isSharedCheck_1126_;
goto v_resetjp_1116_;
}
v_resetjp_1116_:
{
lean_object* v___x_1119_; lean_object* v___x_1121_; 
v___x_1119_ = lean_nat_to_int(v_val_1115_);
if (v_isShared_1118_ == 0)
{
lean_ctor_set(v___x_1117_, 0, v___x_1119_);
v___x_1121_ = v___x_1117_;
goto v_reusejp_1120_;
}
else
{
lean_object* v_reuseFailAlloc_1125_; 
v_reuseFailAlloc_1125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1125_, 0, v___x_1119_);
v___x_1121_ = v_reuseFailAlloc_1125_;
goto v_reusejp_1120_;
}
v_reusejp_1120_:
{
lean_object* v___x_1123_; 
if (v_isShared_1114_ == 0)
{
lean_ctor_set(v___x_1113_, 0, v___x_1121_);
v___x_1123_ = v___x_1113_;
goto v_reusejp_1122_;
}
else
{
lean_object* v_reuseFailAlloc_1124_; 
v_reuseFailAlloc_1124_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1124_, 0, v___x_1121_);
v___x_1123_ = v_reuseFailAlloc_1124_;
goto v_reusejp_1122_;
}
v_reusejp_1122_:
{
return v___x_1123_;
}
}
}
}
else
{
lean_object* v___x_1127_; lean_object* v___x_1129_; 
lean_dec(v_a_1111_);
v___x_1127_ = lean_box(0);
if (v_isShared_1114_ == 0)
{
lean_ctor_set(v___x_1113_, 0, v___x_1127_);
v___x_1129_ = v___x_1113_;
goto v_reusejp_1128_;
}
else
{
lean_object* v_reuseFailAlloc_1130_; 
v_reuseFailAlloc_1130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1130_, 0, v___x_1127_);
v___x_1129_ = v_reuseFailAlloc_1130_;
goto v_reusejp_1128_;
}
v_reusejp_1128_:
{
return v___x_1129_;
}
}
}
}
else
{
lean_object* v_a_1132_; lean_object* v___x_1134_; uint8_t v_isShared_1135_; uint8_t v_isSharedCheck_1139_; 
v_a_1132_ = lean_ctor_get(v___x_1110_, 0);
v_isSharedCheck_1139_ = !lean_is_exclusive(v___x_1110_);
if (v_isSharedCheck_1139_ == 0)
{
v___x_1134_ = v___x_1110_;
v_isShared_1135_ = v_isSharedCheck_1139_;
goto v_resetjp_1133_;
}
else
{
lean_inc(v_a_1132_);
lean_dec(v___x_1110_);
v___x_1134_ = lean_box(0);
v_isShared_1135_ = v_isSharedCheck_1139_;
goto v_resetjp_1133_;
}
v_resetjp_1133_:
{
lean_object* v___x_1137_; 
if (v_isShared_1135_ == 0)
{
v___x_1137_ = v___x_1134_;
goto v_reusejp_1136_;
}
else
{
lean_object* v_reuseFailAlloc_1138_; 
v_reuseFailAlloc_1138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1138_, 0, v_a_1132_);
v___x_1137_ = v_reuseFailAlloc_1138_;
goto v_reusejp_1136_;
}
v_reusejp_1136_:
{
return v___x_1137_;
}
}
}
}
}
}
}
v___jp_981_:
{
lean_object* v___x_982_; lean_object* v___x_984_; 
v___x_982_ = lean_box(0);
if (v_isShared_980_ == 0)
{
lean_ctor_set(v___x_979_, 0, v___x_982_);
v___x_984_ = v___x_979_;
goto v_reusejp_983_;
}
else
{
lean_object* v_reuseFailAlloc_985_; 
v_reuseFailAlloc_985_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_985_, 0, v___x_982_);
v___x_984_ = v_reuseFailAlloc_985_;
goto v_reusejp_983_;
}
v_reusejp_983_:
{
return v___x_984_;
}
}
}
}
else
{
lean_object* v_a_1141_; lean_object* v___x_1143_; uint8_t v_isShared_1144_; uint8_t v_isSharedCheck_1148_; 
v_a_1141_ = lean_ctor_get(v___x_976_, 0);
v_isSharedCheck_1148_ = !lean_is_exclusive(v___x_976_);
if (v_isSharedCheck_1148_ == 0)
{
v___x_1143_ = v___x_976_;
v_isShared_1144_ = v_isSharedCheck_1148_;
goto v_resetjp_1142_;
}
else
{
lean_inc(v_a_1141_);
lean_dec(v___x_976_);
v___x_1143_ = lean_box(0);
v_isShared_1144_ = v_isSharedCheck_1148_;
goto v_resetjp_1142_;
}
v_resetjp_1142_:
{
lean_object* v___x_1146_; 
if (v_isShared_1144_ == 0)
{
v___x_1146_ = v___x_1143_;
goto v_reusejp_1145_;
}
else
{
lean_object* v_reuseFailAlloc_1147_; 
v_reuseFailAlloc_1147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1147_, 0, v_a_1141_);
v___x_1146_ = v_reuseFailAlloc_1147_;
goto v_reusejp_1145_;
}
v_reusejp_1145_:
{
return v___x_1146_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f___boxed(lean_object* v_e_1149_, lean_object* v_a_1150_, lean_object* v_a_1151_, lean_object* v_a_1152_, lean_object* v_a_1153_, lean_object* v_a_1154_, lean_object* v_a_1155_, lean_object* v_a_1156_, lean_object* v_a_1157_, lean_object* v_a_1158_, lean_object* v_a_1159_, lean_object* v_a_1160_, lean_object* v_a_1161_){
_start:
{
lean_object* v_res_1162_; 
v_res_1162_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f(v_e_1149_, v_a_1150_, v_a_1151_, v_a_1152_, v_a_1153_, v_a_1154_, v_a_1155_, v_a_1156_, v_a_1157_, v_a_1158_, v_a_1159_, v_a_1160_);
lean_dec(v_a_1160_);
lean_dec_ref(v_a_1159_);
lean_dec(v_a_1158_);
lean_dec_ref(v_a_1157_);
lean_dec(v_a_1156_);
lean_dec_ref(v_a_1155_);
lean_dec(v_a_1154_);
lean_dec_ref(v_a_1153_);
lean_dec(v_a_1152_);
lean_dec(v_a_1151_);
lean_dec_ref(v_a_1150_);
return v_res_1162_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_getNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isNatCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__2_spec__4_spec__6(lean_object* v_u_1163_, lean_object* v_type_1164_, lean_object* v_semiringInst_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_){
_start:
{
lean_object* v___x_1178_; 
v___x_1178_ = l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_getNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isNatCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__2_spec__4_spec__6___redArg(v_u_1163_, v_type_1164_, v_semiringInst_1165_, v___y_1171_, v___y_1172_, v___y_1173_, v___y_1174_, v___y_1175_, v___y_1176_);
return v___x_1178_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_getNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isNatCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__2_spec__4_spec__6___boxed(lean_object* v_u_1179_, lean_object* v_type_1180_, lean_object* v_semiringInst_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_){
_start:
{
lean_object* v_res_1194_; 
v_res_1194_ = l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_getNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isNatCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__2_spec__4_spec__6(v_u_1179_, v_type_1180_, v_semiringInst_1181_, v___y_1182_, v___y_1183_, v___y_1184_, v___y_1185_, v___y_1186_, v___y_1187_, v___y_1188_, v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_);
lean_dec(v___y_1192_);
lean_dec_ref(v___y_1191_);
lean_dec(v___y_1190_);
lean_dec_ref(v___y_1189_);
lean_dec(v___y_1188_);
lean_dec_ref(v___y_1187_);
lean_dec(v___y_1186_);
lean_dec_ref(v___y_1185_);
lean_dec(v___y_1184_);
lean_dec(v___y_1183_);
lean_dec_ref(v___y_1182_);
return v_res_1194_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1_spec__5_spec__8(lean_object* v_00_u03b1_1195_, lean_object* v_msg_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_){
_start:
{
lean_object* v___x_1209_; 
v___x_1209_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1_spec__5_spec__8___redArg(v_msg_1196_, v___y_1204_, v___y_1205_, v___y_1206_, v___y_1207_);
return v___x_1209_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1_spec__5_spec__8___boxed(lean_object* v_00_u03b1_1210_, lean_object* v_msg_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_){
_start:
{
lean_object* v_res_1224_; 
v_res_1224_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1_spec__5_spec__8(v_00_u03b1_1210_, v_msg_1211_, v___y_1212_, v___y_1213_, v___y_1214_, v___y_1215_, v___y_1216_, v___y_1217_, v___y_1218_, v___y_1219_, v___y_1220_, v___y_1221_, v___y_1222_);
lean_dec(v___y_1222_);
lean_dec_ref(v___y_1221_);
lean_dec(v___y_1220_);
lean_dec_ref(v___y_1219_);
lean_dec(v___y_1218_);
lean_dec_ref(v___y_1217_);
lean_dec(v___y_1216_);
lean_dec_ref(v___y_1215_);
lean_dec(v___y_1214_);
lean_dec(v___y_1213_);
lean_dec_ref(v___y_1212_);
return v_res_1224_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___lam__0(lean_object* v_a_1225_, lean_object* v_s_1226_){
_start:
{
lean_object* v_toRing_1227_; lean_object* v_semiringId_x3f_1228_; lean_object* v_commSemiringInst_1229_; lean_object* v_commRingInst_1230_; lean_object* v_noZeroDivInst_x3f_1231_; lean_object* v_fieldInst_x3f_1232_; lean_object* v_denoteEntries_1233_; lean_object* v_nextId_1234_; lean_object* v_steps_1235_; lean_object* v_queue_1236_; lean_object* v_basis_1237_; lean_object* v_diseqs_1238_; uint8_t v_recheck_1239_; lean_object* v_invSet_1240_; lean_object* v_numEq0_x3f_1241_; uint8_t v_numEq0Updated_1242_; lean_object* v___x_1244_; uint8_t v_isShared_1245_; uint8_t v_isSharedCheck_1250_; 
v_toRing_1227_ = lean_ctor_get(v_s_1226_, 0);
v_semiringId_x3f_1228_ = lean_ctor_get(v_s_1226_, 2);
v_commSemiringInst_1229_ = lean_ctor_get(v_s_1226_, 3);
v_commRingInst_1230_ = lean_ctor_get(v_s_1226_, 4);
v_noZeroDivInst_x3f_1231_ = lean_ctor_get(v_s_1226_, 5);
v_fieldInst_x3f_1232_ = lean_ctor_get(v_s_1226_, 6);
v_denoteEntries_1233_ = lean_ctor_get(v_s_1226_, 7);
v_nextId_1234_ = lean_ctor_get(v_s_1226_, 8);
v_steps_1235_ = lean_ctor_get(v_s_1226_, 9);
v_queue_1236_ = lean_ctor_get(v_s_1226_, 10);
v_basis_1237_ = lean_ctor_get(v_s_1226_, 11);
v_diseqs_1238_ = lean_ctor_get(v_s_1226_, 12);
v_recheck_1239_ = lean_ctor_get_uint8(v_s_1226_, sizeof(void*)*15);
v_invSet_1240_ = lean_ctor_get(v_s_1226_, 13);
v_numEq0_x3f_1241_ = lean_ctor_get(v_s_1226_, 14);
v_numEq0Updated_1242_ = lean_ctor_get_uint8(v_s_1226_, sizeof(void*)*15 + 1);
v_isSharedCheck_1250_ = !lean_is_exclusive(v_s_1226_);
if (v_isSharedCheck_1250_ == 0)
{
lean_object* v_unused_1251_; 
v_unused_1251_ = lean_ctor_get(v_s_1226_, 1);
lean_dec(v_unused_1251_);
v___x_1244_ = v_s_1226_;
v_isShared_1245_ = v_isSharedCheck_1250_;
goto v_resetjp_1243_;
}
else
{
lean_inc(v_numEq0_x3f_1241_);
lean_inc(v_invSet_1240_);
lean_inc(v_diseqs_1238_);
lean_inc(v_basis_1237_);
lean_inc(v_queue_1236_);
lean_inc(v_steps_1235_);
lean_inc(v_nextId_1234_);
lean_inc(v_denoteEntries_1233_);
lean_inc(v_fieldInst_x3f_1232_);
lean_inc(v_noZeroDivInst_x3f_1231_);
lean_inc(v_commRingInst_1230_);
lean_inc(v_commSemiringInst_1229_);
lean_inc(v_semiringId_x3f_1228_);
lean_inc(v_toRing_1227_);
lean_dec(v_s_1226_);
v___x_1244_ = lean_box(0);
v_isShared_1245_ = v_isSharedCheck_1250_;
goto v_resetjp_1243_;
}
v_resetjp_1243_:
{
lean_object* v___x_1246_; lean_object* v___x_1248_; 
v___x_1246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1246_, 0, v_a_1225_);
if (v_isShared_1245_ == 0)
{
lean_ctor_set(v___x_1244_, 1, v___x_1246_);
v___x_1248_ = v___x_1244_;
goto v_reusejp_1247_;
}
else
{
lean_object* v_reuseFailAlloc_1249_; 
v_reuseFailAlloc_1249_ = lean_alloc_ctor(0, 15, 2);
lean_ctor_set(v_reuseFailAlloc_1249_, 0, v_toRing_1227_);
lean_ctor_set(v_reuseFailAlloc_1249_, 1, v___x_1246_);
lean_ctor_set(v_reuseFailAlloc_1249_, 2, v_semiringId_x3f_1228_);
lean_ctor_set(v_reuseFailAlloc_1249_, 3, v_commSemiringInst_1229_);
lean_ctor_set(v_reuseFailAlloc_1249_, 4, v_commRingInst_1230_);
lean_ctor_set(v_reuseFailAlloc_1249_, 5, v_noZeroDivInst_x3f_1231_);
lean_ctor_set(v_reuseFailAlloc_1249_, 6, v_fieldInst_x3f_1232_);
lean_ctor_set(v_reuseFailAlloc_1249_, 7, v_denoteEntries_1233_);
lean_ctor_set(v_reuseFailAlloc_1249_, 8, v_nextId_1234_);
lean_ctor_set(v_reuseFailAlloc_1249_, 9, v_steps_1235_);
lean_ctor_set(v_reuseFailAlloc_1249_, 10, v_queue_1236_);
lean_ctor_set(v_reuseFailAlloc_1249_, 11, v_basis_1237_);
lean_ctor_set(v_reuseFailAlloc_1249_, 12, v_diseqs_1238_);
lean_ctor_set(v_reuseFailAlloc_1249_, 13, v_invSet_1240_);
lean_ctor_set(v_reuseFailAlloc_1249_, 14, v_numEq0_x3f_1241_);
lean_ctor_set_uint8(v_reuseFailAlloc_1249_, sizeof(void*)*15, v_recheck_1239_);
lean_ctor_set_uint8(v_reuseFailAlloc_1249_, sizeof(void*)*15 + 1, v_numEq0Updated_1242_);
v___x_1248_ = v_reuseFailAlloc_1249_;
goto v_reusejp_1247_;
}
v_reusejp_1247_:
{
return v___x_1248_;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___closed__8(void){
_start:
{
lean_object* v___x_1267_; lean_object* v___x_1268_; 
v___x_1267_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___closed__7));
v___x_1268_ = l_Lean_stringToMessageData(v___x_1267_);
return v___x_1268_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0(lean_object* v___y_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_){
_start:
{
lean_object* v___x_1281_; 
v___x_1281_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v___y_1269_, v___y_1270_, v___y_1271_, v___y_1272_, v___y_1273_, v___y_1274_, v___y_1275_, v___y_1276_, v___y_1277_, v___y_1278_, v___y_1279_);
if (lean_obj_tag(v___x_1281_) == 0)
{
lean_object* v_a_1282_; lean_object* v___x_1284_; uint8_t v_isShared_1285_; uint8_t v_isSharedCheck_1329_; 
v_a_1282_ = lean_ctor_get(v___x_1281_, 0);
v_isSharedCheck_1329_ = !lean_is_exclusive(v___x_1281_);
if (v_isSharedCheck_1329_ == 0)
{
v___x_1284_ = v___x_1281_;
v_isShared_1285_ = v_isSharedCheck_1329_;
goto v_resetjp_1283_;
}
else
{
lean_inc(v_a_1282_);
lean_dec(v___x_1281_);
v___x_1284_ = lean_box(0);
v_isShared_1285_ = v_isSharedCheck_1329_;
goto v_resetjp_1283_;
}
v_resetjp_1283_:
{
lean_object* v_fieldInst_x3f_1286_; 
v_fieldInst_x3f_1286_ = lean_ctor_get(v_a_1282_, 6);
if (lean_obj_tag(v_fieldInst_x3f_1286_) == 1)
{
lean_object* v_invFn_x3f_1287_; 
lean_inc_ref(v_fieldInst_x3f_1286_);
v_invFn_x3f_1287_ = lean_ctor_get(v_a_1282_, 1);
if (lean_obj_tag(v_invFn_x3f_1287_) == 1)
{
lean_object* v_val_1288_; lean_object* v___x_1290_; 
lean_inc_ref(v_invFn_x3f_1287_);
lean_dec_ref(v_fieldInst_x3f_1286_);
lean_dec(v_a_1282_);
v_val_1288_ = lean_ctor_get(v_invFn_x3f_1287_, 0);
lean_inc(v_val_1288_);
lean_dec_ref(v_invFn_x3f_1287_);
if (v_isShared_1285_ == 0)
{
lean_ctor_set(v___x_1284_, 0, v_val_1288_);
v___x_1290_ = v___x_1284_;
goto v_reusejp_1289_;
}
else
{
lean_object* v_reuseFailAlloc_1291_; 
v_reuseFailAlloc_1291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1291_, 0, v_val_1288_);
v___x_1290_ = v_reuseFailAlloc_1291_;
goto v_reusejp_1289_;
}
v_reusejp_1289_:
{
return v___x_1290_;
}
}
else
{
lean_object* v_toRing_1292_; lean_object* v_val_1293_; lean_object* v_type_1294_; lean_object* v_u_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v_expectedInst_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; 
lean_del_object(v___x_1284_);
v_toRing_1292_ = lean_ctor_get(v_a_1282_, 0);
lean_inc_ref(v_toRing_1292_);
lean_dec(v_a_1282_);
v_val_1293_ = lean_ctor_get(v_fieldInst_x3f_1286_, 0);
lean_inc(v_val_1293_);
lean_dec_ref(v_fieldInst_x3f_1286_);
v_type_1294_ = lean_ctor_get(v_toRing_1292_, 1);
lean_inc_ref_n(v_type_1294_, 2);
v_u_1295_ = lean_ctor_get(v_toRing_1292_, 2);
lean_inc_n(v_u_1295_, 2);
lean_dec_ref(v_toRing_1292_);
v___x_1296_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___closed__2));
v___x_1297_ = lean_box(0);
v___x_1298_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1298_, 0, v_u_1295_);
lean_ctor_set(v___x_1298_, 1, v___x_1297_);
v___x_1299_ = l_Lean_mkConst(v___x_1296_, v___x_1298_);
v_expectedInst_1300_ = l_Lean_mkAppB(v___x_1299_, v_type_1294_, v_val_1293_);
v___x_1301_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___closed__4));
v___x_1302_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___closed__6));
v___x_1303_ = l_Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1(v_type_1294_, v_u_1295_, v___x_1301_, v___x_1302_, v_expectedInst_1300_, v___y_1269_, v___y_1270_, v___y_1271_, v___y_1272_, v___y_1273_, v___y_1274_, v___y_1275_, v___y_1276_, v___y_1277_, v___y_1278_, v___y_1279_);
if (lean_obj_tag(v___x_1303_) == 0)
{
lean_object* v_a_1304_; lean_object* v___f_1305_; lean_object* v___x_1306_; 
v_a_1304_ = lean_ctor_get(v___x_1303_, 0);
lean_inc_n(v_a_1304_, 2);
lean_dec_ref(v___x_1303_);
v___f_1305_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___lam__0), 2, 1);
lean_closure_set(v___f_1305_, 0, v_a_1304_);
v___x_1306_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(v___f_1305_, v___y_1269_, v___y_1270_);
if (lean_obj_tag(v___x_1306_) == 0)
{
lean_object* v___x_1308_; uint8_t v_isShared_1309_; uint8_t v_isSharedCheck_1313_; 
v_isSharedCheck_1313_ = !lean_is_exclusive(v___x_1306_);
if (v_isSharedCheck_1313_ == 0)
{
lean_object* v_unused_1314_; 
v_unused_1314_ = lean_ctor_get(v___x_1306_, 0);
lean_dec(v_unused_1314_);
v___x_1308_ = v___x_1306_;
v_isShared_1309_ = v_isSharedCheck_1313_;
goto v_resetjp_1307_;
}
else
{
lean_dec(v___x_1306_);
v___x_1308_ = lean_box(0);
v_isShared_1309_ = v_isSharedCheck_1313_;
goto v_resetjp_1307_;
}
v_resetjp_1307_:
{
lean_object* v___x_1311_; 
if (v_isShared_1309_ == 0)
{
lean_ctor_set(v___x_1308_, 0, v_a_1304_);
v___x_1311_ = v___x_1308_;
goto v_reusejp_1310_;
}
else
{
lean_object* v_reuseFailAlloc_1312_; 
v_reuseFailAlloc_1312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1312_, 0, v_a_1304_);
v___x_1311_ = v_reuseFailAlloc_1312_;
goto v_reusejp_1310_;
}
v_reusejp_1310_:
{
return v___x_1311_;
}
}
}
else
{
lean_object* v_a_1315_; lean_object* v___x_1317_; uint8_t v_isShared_1318_; uint8_t v_isSharedCheck_1322_; 
lean_dec(v_a_1304_);
v_a_1315_ = lean_ctor_get(v___x_1306_, 0);
v_isSharedCheck_1322_ = !lean_is_exclusive(v___x_1306_);
if (v_isSharedCheck_1322_ == 0)
{
v___x_1317_ = v___x_1306_;
v_isShared_1318_ = v_isSharedCheck_1322_;
goto v_resetjp_1316_;
}
else
{
lean_inc(v_a_1315_);
lean_dec(v___x_1306_);
v___x_1317_ = lean_box(0);
v_isShared_1318_ = v_isSharedCheck_1322_;
goto v_resetjp_1316_;
}
v_resetjp_1316_:
{
lean_object* v___x_1320_; 
if (v_isShared_1318_ == 0)
{
v___x_1320_ = v___x_1317_;
goto v_reusejp_1319_;
}
else
{
lean_object* v_reuseFailAlloc_1321_; 
v_reuseFailAlloc_1321_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1321_, 0, v_a_1315_);
v___x_1320_ = v_reuseFailAlloc_1321_;
goto v_reusejp_1319_;
}
v_reusejp_1319_:
{
return v___x_1320_;
}
}
}
}
else
{
return v___x_1303_;
}
}
}
else
{
lean_object* v_toRing_1323_; lean_object* v_type_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; 
lean_del_object(v___x_1284_);
v_toRing_1323_ = lean_ctor_get(v_a_1282_, 0);
lean_inc_ref(v_toRing_1323_);
lean_dec(v_a_1282_);
v_type_1324_ = lean_ctor_get(v_toRing_1323_, 1);
lean_inc_ref(v_type_1324_);
lean_dec_ref(v_toRing_1323_);
v___x_1325_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___closed__8, &l_Lean_Meta_Grind_Arith_CommRing_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___closed__8_once, _init_l_Lean_Meta_Grind_Arith_CommRing_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___closed__8);
v___x_1326_ = l_Lean_indentExpr(v_type_1324_);
v___x_1327_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1327_, 0, v___x_1325_);
lean_ctor_set(v___x_1327_, 1, v___x_1326_);
v___x_1328_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1_spec__5_spec__8___redArg(v___x_1327_, v___y_1276_, v___y_1277_, v___y_1278_, v___y_1279_);
return v___x_1328_;
}
}
}
else
{
lean_object* v_a_1330_; lean_object* v___x_1332_; uint8_t v_isShared_1333_; uint8_t v_isSharedCheck_1337_; 
v_a_1330_ = lean_ctor_get(v___x_1281_, 0);
v_isSharedCheck_1337_ = !lean_is_exclusive(v___x_1281_);
if (v_isSharedCheck_1337_ == 0)
{
v___x_1332_ = v___x_1281_;
v_isShared_1333_ = v_isSharedCheck_1337_;
goto v_resetjp_1331_;
}
else
{
lean_inc(v_a_1330_);
lean_dec(v___x_1281_);
v___x_1332_ = lean_box(0);
v_isShared_1333_ = v_isSharedCheck_1337_;
goto v_resetjp_1331_;
}
v_resetjp_1331_:
{
lean_object* v___x_1335_; 
if (v_isShared_1333_ == 0)
{
v___x_1335_ = v___x_1332_;
goto v_reusejp_1334_;
}
else
{
lean_object* v_reuseFailAlloc_1336_; 
v_reuseFailAlloc_1336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1336_, 0, v_a_1330_);
v___x_1335_ = v_reuseFailAlloc_1336_;
goto v_reusejp_1334_;
}
v_reusejp_1334_:
{
return v___x_1335_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___boxed(lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_){
_start:
{
lean_object* v_res_1350_; 
v_res_1350_ = l_Lean_Meta_Grind_Arith_CommRing_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0(v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_, v___y_1342_, v___y_1343_, v___y_1344_, v___y_1345_, v___y_1346_, v___y_1347_, v___y_1348_);
lean_dec(v___y_1348_);
lean_dec_ref(v___y_1347_);
lean_dec(v___y_1346_);
lean_dec_ref(v___y_1345_);
lean_dec(v___y_1344_);
lean_dec_ref(v___y_1343_);
lean_dec(v___y_1342_);
lean_dec_ref(v___y_1341_);
lean_dec(v___y_1340_);
lean_dec(v___y_1339_);
lean_dec_ref(v___y_1338_);
return v_res_1350_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst(lean_object* v_inst_1351_, lean_object* v_a_1352_, lean_object* v_a_1353_, lean_object* v_a_1354_, lean_object* v_a_1355_, lean_object* v_a_1356_, lean_object* v_a_1357_, lean_object* v_a_1358_, lean_object* v_a_1359_, lean_object* v_a_1360_, lean_object* v_a_1361_, lean_object* v_a_1362_){
_start:
{
lean_object* v___x_1364_; 
v___x_1364_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v_a_1352_, v_a_1353_, v_a_1354_, v_a_1355_, v_a_1356_, v_a_1357_, v_a_1358_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_);
if (lean_obj_tag(v___x_1364_) == 0)
{
lean_object* v_a_1365_; lean_object* v___x_1367_; uint8_t v_isShared_1368_; uint8_t v_isSharedCheck_1395_; 
v_a_1365_ = lean_ctor_get(v___x_1364_, 0);
v_isSharedCheck_1395_ = !lean_is_exclusive(v___x_1364_);
if (v_isSharedCheck_1395_ == 0)
{
v___x_1367_ = v___x_1364_;
v_isShared_1368_ = v_isSharedCheck_1395_;
goto v_resetjp_1366_;
}
else
{
lean_inc(v_a_1365_);
lean_dec(v___x_1364_);
v___x_1367_ = lean_box(0);
v_isShared_1368_ = v_isSharedCheck_1395_;
goto v_resetjp_1366_;
}
v_resetjp_1366_:
{
lean_object* v_fieldInst_x3f_1369_; 
v_fieldInst_x3f_1369_ = lean_ctor_get(v_a_1365_, 6);
lean_inc(v_fieldInst_x3f_1369_);
lean_dec(v_a_1365_);
if (lean_obj_tag(v_fieldInst_x3f_1369_) == 0)
{
uint8_t v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1373_; 
v___x_1370_ = 0;
v___x_1371_ = lean_box(v___x_1370_);
if (v_isShared_1368_ == 0)
{
lean_ctor_set(v___x_1367_, 0, v___x_1371_);
v___x_1373_ = v___x_1367_;
goto v_reusejp_1372_;
}
else
{
lean_object* v_reuseFailAlloc_1374_; 
v_reuseFailAlloc_1374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1374_, 0, v___x_1371_);
v___x_1373_ = v_reuseFailAlloc_1374_;
goto v_reusejp_1372_;
}
v_reusejp_1372_:
{
return v___x_1373_;
}
}
else
{
lean_object* v___x_1375_; 
lean_dec_ref(v_fieldInst_x3f_1369_);
lean_del_object(v___x_1367_);
v___x_1375_ = l_Lean_Meta_Grind_Arith_CommRing_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0(v_a_1352_, v_a_1353_, v_a_1354_, v_a_1355_, v_a_1356_, v_a_1357_, v_a_1358_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_);
if (lean_obj_tag(v___x_1375_) == 0)
{
lean_object* v_a_1376_; lean_object* v___x_1378_; uint8_t v_isShared_1379_; uint8_t v_isSharedCheck_1386_; 
v_a_1376_ = lean_ctor_get(v___x_1375_, 0);
v_isSharedCheck_1386_ = !lean_is_exclusive(v___x_1375_);
if (v_isSharedCheck_1386_ == 0)
{
v___x_1378_ = v___x_1375_;
v_isShared_1379_ = v_isSharedCheck_1386_;
goto v_resetjp_1377_;
}
else
{
lean_inc(v_a_1376_);
lean_dec(v___x_1375_);
v___x_1378_ = lean_box(0);
v_isShared_1379_ = v_isSharedCheck_1386_;
goto v_resetjp_1377_;
}
v_resetjp_1377_:
{
lean_object* v___x_1380_; uint8_t v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1384_; 
v___x_1380_ = l_Lean_Expr_appArg_x21(v_a_1376_);
lean_dec(v_a_1376_);
v___x_1381_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v___x_1380_, v_inst_1351_);
lean_dec_ref(v___x_1380_);
v___x_1382_ = lean_box(v___x_1381_);
if (v_isShared_1379_ == 0)
{
lean_ctor_set(v___x_1378_, 0, v___x_1382_);
v___x_1384_ = v___x_1378_;
goto v_reusejp_1383_;
}
else
{
lean_object* v_reuseFailAlloc_1385_; 
v_reuseFailAlloc_1385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1385_, 0, v___x_1382_);
v___x_1384_ = v_reuseFailAlloc_1385_;
goto v_reusejp_1383_;
}
v_reusejp_1383_:
{
return v___x_1384_;
}
}
}
else
{
lean_object* v_a_1387_; lean_object* v___x_1389_; uint8_t v_isShared_1390_; uint8_t v_isSharedCheck_1394_; 
v_a_1387_ = lean_ctor_get(v___x_1375_, 0);
v_isSharedCheck_1394_ = !lean_is_exclusive(v___x_1375_);
if (v_isSharedCheck_1394_ == 0)
{
v___x_1389_ = v___x_1375_;
v_isShared_1390_ = v_isSharedCheck_1394_;
goto v_resetjp_1388_;
}
else
{
lean_inc(v_a_1387_);
lean_dec(v___x_1375_);
v___x_1389_ = lean_box(0);
v_isShared_1390_ = v_isSharedCheck_1394_;
goto v_resetjp_1388_;
}
v_resetjp_1388_:
{
lean_object* v___x_1392_; 
if (v_isShared_1390_ == 0)
{
v___x_1392_ = v___x_1389_;
goto v_reusejp_1391_;
}
else
{
lean_object* v_reuseFailAlloc_1393_; 
v_reuseFailAlloc_1393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1393_, 0, v_a_1387_);
v___x_1392_ = v_reuseFailAlloc_1393_;
goto v_reusejp_1391_;
}
v_reusejp_1391_:
{
return v___x_1392_;
}
}
}
}
}
}
else
{
lean_object* v_a_1396_; lean_object* v___x_1398_; uint8_t v_isShared_1399_; uint8_t v_isSharedCheck_1403_; 
v_a_1396_ = lean_ctor_get(v___x_1364_, 0);
v_isSharedCheck_1403_ = !lean_is_exclusive(v___x_1364_);
if (v_isSharedCheck_1403_ == 0)
{
v___x_1398_ = v___x_1364_;
v_isShared_1399_ = v_isSharedCheck_1403_;
goto v_resetjp_1397_;
}
else
{
lean_inc(v_a_1396_);
lean_dec(v___x_1364_);
v___x_1398_ = lean_box(0);
v_isShared_1399_ = v_isSharedCheck_1403_;
goto v_resetjp_1397_;
}
v_resetjp_1397_:
{
lean_object* v___x_1401_; 
if (v_isShared_1399_ == 0)
{
v___x_1401_ = v___x_1398_;
goto v_reusejp_1400_;
}
else
{
lean_object* v_reuseFailAlloc_1402_; 
v_reuseFailAlloc_1402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1402_, 0, v_a_1396_);
v___x_1401_ = v_reuseFailAlloc_1402_;
goto v_reusejp_1400_;
}
v_reusejp_1400_:
{
return v___x_1401_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst___boxed(lean_object* v_inst_1404_, lean_object* v_a_1405_, lean_object* v_a_1406_, lean_object* v_a_1407_, lean_object* v_a_1408_, lean_object* v_a_1409_, lean_object* v_a_1410_, lean_object* v_a_1411_, lean_object* v_a_1412_, lean_object* v_a_1413_, lean_object* v_a_1414_, lean_object* v_a_1415_, lean_object* v_a_1416_){
_start:
{
lean_object* v_res_1417_; 
v_res_1417_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst(v_inst_1404_, v_a_1405_, v_a_1406_, v_a_1407_, v_a_1408_, v_a_1409_, v_a_1410_, v_a_1411_, v_a_1412_, v_a_1413_, v_a_1414_, v_a_1415_);
lean_dec(v_a_1415_);
lean_dec_ref(v_a_1414_);
lean_dec(v_a_1413_);
lean_dec_ref(v_a_1412_);
lean_dec(v_a_1411_);
lean_dec_ref(v_a_1410_);
lean_dec(v_a_1409_);
lean_dec_ref(v_a_1408_);
lean_dec(v_a_1407_);
lean_dec(v_a_1406_);
lean_dec_ref(v_a_1405_);
lean_dec_ref(v_inst_1404_);
return v_res_1417_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__2(lean_object* v_a_1418_){
_start:
{
lean_object* v___x_1419_; 
v___x_1419_ = lean_nat_to_int(v_a_1418_);
return v___x_1419_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0_spec__2_spec__6___redArg(lean_object* v_x_1420_, lean_object* v_x_1421_, lean_object* v_x_1422_, lean_object* v_x_1423_){
_start:
{
lean_object* v_ks_1424_; lean_object* v_vs_1425_; lean_object* v___x_1427_; uint8_t v_isShared_1428_; uint8_t v_isSharedCheck_1449_; 
v_ks_1424_ = lean_ctor_get(v_x_1420_, 0);
v_vs_1425_ = lean_ctor_get(v_x_1420_, 1);
v_isSharedCheck_1449_ = !lean_is_exclusive(v_x_1420_);
if (v_isSharedCheck_1449_ == 0)
{
v___x_1427_ = v_x_1420_;
v_isShared_1428_ = v_isSharedCheck_1449_;
goto v_resetjp_1426_;
}
else
{
lean_inc(v_vs_1425_);
lean_inc(v_ks_1424_);
lean_dec(v_x_1420_);
v___x_1427_ = lean_box(0);
v_isShared_1428_ = v_isSharedCheck_1449_;
goto v_resetjp_1426_;
}
v_resetjp_1426_:
{
lean_object* v___x_1429_; uint8_t v___x_1430_; 
v___x_1429_ = lean_array_get_size(v_ks_1424_);
v___x_1430_ = lean_nat_dec_lt(v_x_1421_, v___x_1429_);
if (v___x_1430_ == 0)
{
lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1434_; 
lean_dec(v_x_1421_);
v___x_1431_ = lean_array_push(v_ks_1424_, v_x_1422_);
v___x_1432_ = lean_array_push(v_vs_1425_, v_x_1423_);
if (v_isShared_1428_ == 0)
{
lean_ctor_set(v___x_1427_, 1, v___x_1432_);
lean_ctor_set(v___x_1427_, 0, v___x_1431_);
v___x_1434_ = v___x_1427_;
goto v_reusejp_1433_;
}
else
{
lean_object* v_reuseFailAlloc_1435_; 
v_reuseFailAlloc_1435_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1435_, 0, v___x_1431_);
lean_ctor_set(v_reuseFailAlloc_1435_, 1, v___x_1432_);
v___x_1434_ = v_reuseFailAlloc_1435_;
goto v_reusejp_1433_;
}
v_reusejp_1433_:
{
return v___x_1434_;
}
}
else
{
lean_object* v_k_x27_1436_; uint8_t v___x_1437_; 
v_k_x27_1436_ = lean_array_fget_borrowed(v_ks_1424_, v_x_1421_);
v___x_1437_ = lean_expr_eqv(v_x_1422_, v_k_x27_1436_);
if (v___x_1437_ == 0)
{
lean_object* v___x_1439_; 
if (v_isShared_1428_ == 0)
{
v___x_1439_ = v___x_1427_;
goto v_reusejp_1438_;
}
else
{
lean_object* v_reuseFailAlloc_1443_; 
v_reuseFailAlloc_1443_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1443_, 0, v_ks_1424_);
lean_ctor_set(v_reuseFailAlloc_1443_, 1, v_vs_1425_);
v___x_1439_ = v_reuseFailAlloc_1443_;
goto v_reusejp_1438_;
}
v_reusejp_1438_:
{
lean_object* v___x_1440_; lean_object* v___x_1441_; 
v___x_1440_ = lean_unsigned_to_nat(1u);
v___x_1441_ = lean_nat_add(v_x_1421_, v___x_1440_);
lean_dec(v_x_1421_);
v_x_1420_ = v___x_1439_;
v_x_1421_ = v___x_1441_;
goto _start;
}
}
else
{
lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1447_; 
v___x_1444_ = lean_array_fset(v_ks_1424_, v_x_1421_, v_x_1422_);
v___x_1445_ = lean_array_fset(v_vs_1425_, v_x_1421_, v_x_1423_);
lean_dec(v_x_1421_);
if (v_isShared_1428_ == 0)
{
lean_ctor_set(v___x_1427_, 1, v___x_1445_);
lean_ctor_set(v___x_1427_, 0, v___x_1444_);
v___x_1447_ = v___x_1427_;
goto v_reusejp_1446_;
}
else
{
lean_object* v_reuseFailAlloc_1448_; 
v_reuseFailAlloc_1448_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1448_, 0, v___x_1444_);
lean_ctor_set(v_reuseFailAlloc_1448_, 1, v___x_1445_);
v___x_1447_ = v_reuseFailAlloc_1448_;
goto v_reusejp_1446_;
}
v_reusejp_1446_:
{
return v___x_1447_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0_spec__2___redArg(lean_object* v_n_1450_, lean_object* v_k_1451_, lean_object* v_v_1452_){
_start:
{
lean_object* v___x_1453_; lean_object* v___x_1454_; 
v___x_1453_ = lean_unsigned_to_nat(0u);
v___x_1454_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0_spec__2_spec__6___redArg(v_n_1450_, v___x_1453_, v_k_1451_, v_v_1452_);
return v___x_1454_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg___closed__0(void){
_start:
{
size_t v___x_1455_; size_t v___x_1456_; size_t v___x_1457_; 
v___x_1455_ = ((size_t)5ULL);
v___x_1456_ = ((size_t)1ULL);
v___x_1457_ = lean_usize_shift_left(v___x_1456_, v___x_1455_);
return v___x_1457_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_1458_; size_t v___x_1459_; size_t v___x_1460_; 
v___x_1458_ = ((size_t)1ULL);
v___x_1459_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg___closed__0);
v___x_1460_ = lean_usize_sub(v___x_1459_, v___x_1458_);
return v___x_1460_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_1461_; 
v___x_1461_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1461_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg(lean_object* v_x_1462_, size_t v_x_1463_, size_t v_x_1464_, lean_object* v_x_1465_, lean_object* v_x_1466_){
_start:
{
if (lean_obj_tag(v_x_1462_) == 0)
{
lean_object* v_es_1467_; size_t v___x_1468_; size_t v___x_1469_; size_t v___x_1470_; size_t v___x_1471_; lean_object* v_j_1472_; lean_object* v___x_1473_; uint8_t v___x_1474_; 
v_es_1467_ = lean_ctor_get(v_x_1462_, 0);
v___x_1468_ = ((size_t)5ULL);
v___x_1469_ = ((size_t)1ULL);
v___x_1470_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg___closed__1);
v___x_1471_ = lean_usize_land(v_x_1463_, v___x_1470_);
v_j_1472_ = lean_usize_to_nat(v___x_1471_);
v___x_1473_ = lean_array_get_size(v_es_1467_);
v___x_1474_ = lean_nat_dec_lt(v_j_1472_, v___x_1473_);
if (v___x_1474_ == 0)
{
lean_dec(v_j_1472_);
lean_dec(v_x_1466_);
lean_dec_ref(v_x_1465_);
return v_x_1462_;
}
else
{
lean_object* v___x_1476_; uint8_t v_isShared_1477_; uint8_t v_isSharedCheck_1511_; 
lean_inc_ref(v_es_1467_);
v_isSharedCheck_1511_ = !lean_is_exclusive(v_x_1462_);
if (v_isSharedCheck_1511_ == 0)
{
lean_object* v_unused_1512_; 
v_unused_1512_ = lean_ctor_get(v_x_1462_, 0);
lean_dec(v_unused_1512_);
v___x_1476_ = v_x_1462_;
v_isShared_1477_ = v_isSharedCheck_1511_;
goto v_resetjp_1475_;
}
else
{
lean_dec(v_x_1462_);
v___x_1476_ = lean_box(0);
v_isShared_1477_ = v_isSharedCheck_1511_;
goto v_resetjp_1475_;
}
v_resetjp_1475_:
{
lean_object* v_v_1478_; lean_object* v___x_1479_; lean_object* v_xs_x27_1480_; lean_object* v___y_1482_; 
v_v_1478_ = lean_array_fget(v_es_1467_, v_j_1472_);
v___x_1479_ = lean_box(0);
v_xs_x27_1480_ = lean_array_fset(v_es_1467_, v_j_1472_, v___x_1479_);
switch(lean_obj_tag(v_v_1478_))
{
case 0:
{
lean_object* v_key_1487_; lean_object* v_val_1488_; lean_object* v___x_1490_; uint8_t v_isShared_1491_; uint8_t v_isSharedCheck_1498_; 
v_key_1487_ = lean_ctor_get(v_v_1478_, 0);
v_val_1488_ = lean_ctor_get(v_v_1478_, 1);
v_isSharedCheck_1498_ = !lean_is_exclusive(v_v_1478_);
if (v_isSharedCheck_1498_ == 0)
{
v___x_1490_ = v_v_1478_;
v_isShared_1491_ = v_isSharedCheck_1498_;
goto v_resetjp_1489_;
}
else
{
lean_inc(v_val_1488_);
lean_inc(v_key_1487_);
lean_dec(v_v_1478_);
v___x_1490_ = lean_box(0);
v_isShared_1491_ = v_isSharedCheck_1498_;
goto v_resetjp_1489_;
}
v_resetjp_1489_:
{
uint8_t v___x_1492_; 
v___x_1492_ = lean_expr_eqv(v_x_1465_, v_key_1487_);
if (v___x_1492_ == 0)
{
lean_object* v___x_1493_; lean_object* v___x_1494_; 
lean_del_object(v___x_1490_);
v___x_1493_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1487_, v_val_1488_, v_x_1465_, v_x_1466_);
v___x_1494_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1494_, 0, v___x_1493_);
v___y_1482_ = v___x_1494_;
goto v___jp_1481_;
}
else
{
lean_object* v___x_1496_; 
lean_dec(v_val_1488_);
lean_dec(v_key_1487_);
if (v_isShared_1491_ == 0)
{
lean_ctor_set(v___x_1490_, 1, v_x_1466_);
lean_ctor_set(v___x_1490_, 0, v_x_1465_);
v___x_1496_ = v___x_1490_;
goto v_reusejp_1495_;
}
else
{
lean_object* v_reuseFailAlloc_1497_; 
v_reuseFailAlloc_1497_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1497_, 0, v_x_1465_);
lean_ctor_set(v_reuseFailAlloc_1497_, 1, v_x_1466_);
v___x_1496_ = v_reuseFailAlloc_1497_;
goto v_reusejp_1495_;
}
v_reusejp_1495_:
{
v___y_1482_ = v___x_1496_;
goto v___jp_1481_;
}
}
}
}
case 1:
{
lean_object* v_node_1499_; lean_object* v___x_1501_; uint8_t v_isShared_1502_; uint8_t v_isSharedCheck_1509_; 
v_node_1499_ = lean_ctor_get(v_v_1478_, 0);
v_isSharedCheck_1509_ = !lean_is_exclusive(v_v_1478_);
if (v_isSharedCheck_1509_ == 0)
{
v___x_1501_ = v_v_1478_;
v_isShared_1502_ = v_isSharedCheck_1509_;
goto v_resetjp_1500_;
}
else
{
lean_inc(v_node_1499_);
lean_dec(v_v_1478_);
v___x_1501_ = lean_box(0);
v_isShared_1502_ = v_isSharedCheck_1509_;
goto v_resetjp_1500_;
}
v_resetjp_1500_:
{
size_t v___x_1503_; size_t v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1507_; 
v___x_1503_ = lean_usize_shift_right(v_x_1463_, v___x_1468_);
v___x_1504_ = lean_usize_add(v_x_1464_, v___x_1469_);
v___x_1505_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg(v_node_1499_, v___x_1503_, v___x_1504_, v_x_1465_, v_x_1466_);
if (v_isShared_1502_ == 0)
{
lean_ctor_set(v___x_1501_, 0, v___x_1505_);
v___x_1507_ = v___x_1501_;
goto v_reusejp_1506_;
}
else
{
lean_object* v_reuseFailAlloc_1508_; 
v_reuseFailAlloc_1508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1508_, 0, v___x_1505_);
v___x_1507_ = v_reuseFailAlloc_1508_;
goto v_reusejp_1506_;
}
v_reusejp_1506_:
{
v___y_1482_ = v___x_1507_;
goto v___jp_1481_;
}
}
}
default: 
{
lean_object* v___x_1510_; 
v___x_1510_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1510_, 0, v_x_1465_);
lean_ctor_set(v___x_1510_, 1, v_x_1466_);
v___y_1482_ = v___x_1510_;
goto v___jp_1481_;
}
}
v___jp_1481_:
{
lean_object* v___x_1483_; lean_object* v___x_1485_; 
v___x_1483_ = lean_array_fset(v_xs_x27_1480_, v_j_1472_, v___y_1482_);
lean_dec(v_j_1472_);
if (v_isShared_1477_ == 0)
{
lean_ctor_set(v___x_1476_, 0, v___x_1483_);
v___x_1485_ = v___x_1476_;
goto v_reusejp_1484_;
}
else
{
lean_object* v_reuseFailAlloc_1486_; 
v_reuseFailAlloc_1486_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1486_, 0, v___x_1483_);
v___x_1485_ = v_reuseFailAlloc_1486_;
goto v_reusejp_1484_;
}
v_reusejp_1484_:
{
return v___x_1485_;
}
}
}
}
}
else
{
lean_object* v_ks_1513_; lean_object* v_vs_1514_; lean_object* v___x_1516_; uint8_t v_isShared_1517_; uint8_t v_isSharedCheck_1534_; 
v_ks_1513_ = lean_ctor_get(v_x_1462_, 0);
v_vs_1514_ = lean_ctor_get(v_x_1462_, 1);
v_isSharedCheck_1534_ = !lean_is_exclusive(v_x_1462_);
if (v_isSharedCheck_1534_ == 0)
{
v___x_1516_ = v_x_1462_;
v_isShared_1517_ = v_isSharedCheck_1534_;
goto v_resetjp_1515_;
}
else
{
lean_inc(v_vs_1514_);
lean_inc(v_ks_1513_);
lean_dec(v_x_1462_);
v___x_1516_ = lean_box(0);
v_isShared_1517_ = v_isSharedCheck_1534_;
goto v_resetjp_1515_;
}
v_resetjp_1515_:
{
lean_object* v___x_1519_; 
if (v_isShared_1517_ == 0)
{
v___x_1519_ = v___x_1516_;
goto v_reusejp_1518_;
}
else
{
lean_object* v_reuseFailAlloc_1533_; 
v_reuseFailAlloc_1533_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1533_, 0, v_ks_1513_);
lean_ctor_set(v_reuseFailAlloc_1533_, 1, v_vs_1514_);
v___x_1519_ = v_reuseFailAlloc_1533_;
goto v_reusejp_1518_;
}
v_reusejp_1518_:
{
lean_object* v_newNode_1520_; uint8_t v___y_1522_; size_t v___x_1528_; uint8_t v___x_1529_; 
v_newNode_1520_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0_spec__2___redArg(v___x_1519_, v_x_1465_, v_x_1466_);
v___x_1528_ = ((size_t)7ULL);
v___x_1529_ = lean_usize_dec_le(v___x_1528_, v_x_1464_);
if (v___x_1529_ == 0)
{
lean_object* v___x_1530_; lean_object* v___x_1531_; uint8_t v___x_1532_; 
v___x_1530_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1520_);
v___x_1531_ = lean_unsigned_to_nat(4u);
v___x_1532_ = lean_nat_dec_lt(v___x_1530_, v___x_1531_);
lean_dec(v___x_1530_);
v___y_1522_ = v___x_1532_;
goto v___jp_1521_;
}
else
{
v___y_1522_ = v___x_1529_;
goto v___jp_1521_;
}
v___jp_1521_:
{
if (v___y_1522_ == 0)
{
lean_object* v_ks_1523_; lean_object* v_vs_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; 
v_ks_1523_ = lean_ctor_get(v_newNode_1520_, 0);
lean_inc_ref(v_ks_1523_);
v_vs_1524_ = lean_ctor_get(v_newNode_1520_, 1);
lean_inc_ref(v_vs_1524_);
lean_dec_ref(v_newNode_1520_);
v___x_1525_ = lean_unsigned_to_nat(0u);
v___x_1526_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg___closed__2);
v___x_1527_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0_spec__3___redArg(v_x_1464_, v_ks_1523_, v_vs_1524_, v___x_1525_, v___x_1526_);
lean_dec_ref(v_vs_1524_);
lean_dec_ref(v_ks_1523_);
return v___x_1527_;
}
else
{
return v_newNode_1520_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0_spec__3___redArg(size_t v_depth_1535_, lean_object* v_keys_1536_, lean_object* v_vals_1537_, lean_object* v_i_1538_, lean_object* v_entries_1539_){
_start:
{
lean_object* v___x_1540_; uint8_t v___x_1541_; 
v___x_1540_ = lean_array_get_size(v_keys_1536_);
v___x_1541_ = lean_nat_dec_lt(v_i_1538_, v___x_1540_);
if (v___x_1541_ == 0)
{
lean_dec(v_i_1538_);
return v_entries_1539_;
}
else
{
lean_object* v_k_1542_; lean_object* v_v_1543_; uint64_t v___x_1544_; size_t v_h_1545_; size_t v___x_1546_; lean_object* v___x_1547_; size_t v___x_1548_; size_t v___x_1549_; size_t v___x_1550_; size_t v_h_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; 
v_k_1542_ = lean_array_fget_borrowed(v_keys_1536_, v_i_1538_);
v_v_1543_ = lean_array_fget_borrowed(v_vals_1537_, v_i_1538_);
v___x_1544_ = l_Lean_Expr_hash(v_k_1542_);
v_h_1545_ = lean_uint64_to_usize(v___x_1544_);
v___x_1546_ = ((size_t)5ULL);
v___x_1547_ = lean_unsigned_to_nat(1u);
v___x_1548_ = ((size_t)1ULL);
v___x_1549_ = lean_usize_sub(v_depth_1535_, v___x_1548_);
v___x_1550_ = lean_usize_mul(v___x_1546_, v___x_1549_);
v_h_1551_ = lean_usize_shift_right(v_h_1545_, v___x_1550_);
v___x_1552_ = lean_nat_add(v_i_1538_, v___x_1547_);
lean_dec(v_i_1538_);
lean_inc(v_v_1543_);
lean_inc(v_k_1542_);
v___x_1553_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg(v_entries_1539_, v_h_1551_, v_depth_1535_, v_k_1542_, v_v_1543_);
v_i_1538_ = v___x_1552_;
v_entries_1539_ = v___x_1553_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_depth_1555_, lean_object* v_keys_1556_, lean_object* v_vals_1557_, lean_object* v_i_1558_, lean_object* v_entries_1559_){
_start:
{
size_t v_depth_boxed_1560_; lean_object* v_res_1561_; 
v_depth_boxed_1560_ = lean_unbox_usize(v_depth_1555_);
lean_dec(v_depth_1555_);
v_res_1561_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0_spec__3___redArg(v_depth_boxed_1560_, v_keys_1556_, v_vals_1557_, v_i_1558_, v_entries_1559_);
lean_dec_ref(v_vals_1557_);
lean_dec_ref(v_keys_1556_);
return v_res_1561_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg___boxed(lean_object* v_x_1562_, lean_object* v_x_1563_, lean_object* v_x_1564_, lean_object* v_x_1565_, lean_object* v_x_1566_){
_start:
{
size_t v_x_140288__boxed_1567_; size_t v_x_140289__boxed_1568_; lean_object* v_res_1569_; 
v_x_140288__boxed_1567_ = lean_unbox_usize(v_x_1563_);
lean_dec(v_x_1563_);
v_x_140289__boxed_1568_ = lean_unbox_usize(v_x_1564_);
lean_dec(v_x_1564_);
v_res_1569_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg(v_x_1562_, v_x_140288__boxed_1567_, v_x_140289__boxed_1568_, v_x_1565_, v_x_1566_);
return v_res_1569_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0___redArg(lean_object* v_x_1570_, lean_object* v_x_1571_, lean_object* v_x_1572_){
_start:
{
uint64_t v___x_1573_; size_t v___x_1574_; size_t v___x_1575_; lean_object* v___x_1576_; 
v___x_1573_ = l_Lean_Expr_hash(v_x_1571_);
v___x_1574_ = lean_uint64_to_usize(v___x_1573_);
v___x_1575_ = ((size_t)1ULL);
v___x_1576_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg(v_x_1570_, v___x_1574_, v___x_1575_, v_x_1571_, v_x_1572_);
return v___x_1576_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___lam__0(lean_object* v_a_1577_, lean_object* v_s_1578_){
_start:
{
lean_object* v_toRing_1579_; lean_object* v_invFn_x3f_1580_; lean_object* v_semiringId_x3f_1581_; lean_object* v_commSemiringInst_1582_; lean_object* v_commRingInst_1583_; lean_object* v_noZeroDivInst_x3f_1584_; lean_object* v_fieldInst_x3f_1585_; lean_object* v_denoteEntries_1586_; lean_object* v_nextId_1587_; lean_object* v_steps_1588_; lean_object* v_queue_1589_; lean_object* v_basis_1590_; lean_object* v_diseqs_1591_; uint8_t v_recheck_1592_; lean_object* v_invSet_1593_; lean_object* v_numEq0_x3f_1594_; uint8_t v_numEq0Updated_1595_; lean_object* v___x_1597_; uint8_t v_isShared_1598_; uint8_t v_isSharedCheck_1604_; 
v_toRing_1579_ = lean_ctor_get(v_s_1578_, 0);
v_invFn_x3f_1580_ = lean_ctor_get(v_s_1578_, 1);
v_semiringId_x3f_1581_ = lean_ctor_get(v_s_1578_, 2);
v_commSemiringInst_1582_ = lean_ctor_get(v_s_1578_, 3);
v_commRingInst_1583_ = lean_ctor_get(v_s_1578_, 4);
v_noZeroDivInst_x3f_1584_ = lean_ctor_get(v_s_1578_, 5);
v_fieldInst_x3f_1585_ = lean_ctor_get(v_s_1578_, 6);
v_denoteEntries_1586_ = lean_ctor_get(v_s_1578_, 7);
v_nextId_1587_ = lean_ctor_get(v_s_1578_, 8);
v_steps_1588_ = lean_ctor_get(v_s_1578_, 9);
v_queue_1589_ = lean_ctor_get(v_s_1578_, 10);
v_basis_1590_ = lean_ctor_get(v_s_1578_, 11);
v_diseqs_1591_ = lean_ctor_get(v_s_1578_, 12);
v_recheck_1592_ = lean_ctor_get_uint8(v_s_1578_, sizeof(void*)*15);
v_invSet_1593_ = lean_ctor_get(v_s_1578_, 13);
v_numEq0_x3f_1594_ = lean_ctor_get(v_s_1578_, 14);
v_numEq0Updated_1595_ = lean_ctor_get_uint8(v_s_1578_, sizeof(void*)*15 + 1);
v_isSharedCheck_1604_ = !lean_is_exclusive(v_s_1578_);
if (v_isSharedCheck_1604_ == 0)
{
v___x_1597_ = v_s_1578_;
v_isShared_1598_ = v_isSharedCheck_1604_;
goto v_resetjp_1596_;
}
else
{
lean_inc(v_numEq0_x3f_1594_);
lean_inc(v_invSet_1593_);
lean_inc(v_diseqs_1591_);
lean_inc(v_basis_1590_);
lean_inc(v_queue_1589_);
lean_inc(v_steps_1588_);
lean_inc(v_nextId_1587_);
lean_inc(v_denoteEntries_1586_);
lean_inc(v_fieldInst_x3f_1585_);
lean_inc(v_noZeroDivInst_x3f_1584_);
lean_inc(v_commRingInst_1583_);
lean_inc(v_commSemiringInst_1582_);
lean_inc(v_semiringId_x3f_1581_);
lean_inc(v_invFn_x3f_1580_);
lean_inc(v_toRing_1579_);
lean_dec(v_s_1578_);
v___x_1597_ = lean_box(0);
v_isShared_1598_ = v_isSharedCheck_1604_;
goto v_resetjp_1596_;
}
v_resetjp_1596_:
{
lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1602_; 
v___x_1599_ = lean_box(0);
v___x_1600_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0___redArg(v_invSet_1593_, v_a_1577_, v___x_1599_);
if (v_isShared_1598_ == 0)
{
lean_ctor_set(v___x_1597_, 13, v___x_1600_);
v___x_1602_ = v___x_1597_;
goto v_reusejp_1601_;
}
else
{
lean_object* v_reuseFailAlloc_1603_; 
v_reuseFailAlloc_1603_ = lean_alloc_ctor(0, 15, 2);
lean_ctor_set(v_reuseFailAlloc_1603_, 0, v_toRing_1579_);
lean_ctor_set(v_reuseFailAlloc_1603_, 1, v_invFn_x3f_1580_);
lean_ctor_set(v_reuseFailAlloc_1603_, 2, v_semiringId_x3f_1581_);
lean_ctor_set(v_reuseFailAlloc_1603_, 3, v_commSemiringInst_1582_);
lean_ctor_set(v_reuseFailAlloc_1603_, 4, v_commRingInst_1583_);
lean_ctor_set(v_reuseFailAlloc_1603_, 5, v_noZeroDivInst_x3f_1584_);
lean_ctor_set(v_reuseFailAlloc_1603_, 6, v_fieldInst_x3f_1585_);
lean_ctor_set(v_reuseFailAlloc_1603_, 7, v_denoteEntries_1586_);
lean_ctor_set(v_reuseFailAlloc_1603_, 8, v_nextId_1587_);
lean_ctor_set(v_reuseFailAlloc_1603_, 9, v_steps_1588_);
lean_ctor_set(v_reuseFailAlloc_1603_, 10, v_queue_1589_);
lean_ctor_set(v_reuseFailAlloc_1603_, 11, v_basis_1590_);
lean_ctor_set(v_reuseFailAlloc_1603_, 12, v_diseqs_1591_);
lean_ctor_set(v_reuseFailAlloc_1603_, 13, v___x_1600_);
lean_ctor_set(v_reuseFailAlloc_1603_, 14, v_numEq0_x3f_1594_);
lean_ctor_set_uint8(v_reuseFailAlloc_1603_, sizeof(void*)*15, v_recheck_1592_);
lean_ctor_set_uint8(v_reuseFailAlloc_1603_, sizeof(void*)*15 + 1, v_numEq0Updated_1595_);
v___x_1602_ = v_reuseFailAlloc_1603_;
goto v_reusejp_1601_;
}
v_reusejp_1601_:
{
return v___x_1602_;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__4___closed__1(void){
_start:
{
lean_object* v___x_1607_; lean_object* v___x_1608_; 
v___x_1607_ = lean_unsigned_to_nat(0u);
v___x_1608_ = lean_nat_to_int(v___x_1607_);
return v___x_1608_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__4(lean_object* v_k_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_){
_start:
{
lean_object* v___x_1627_; 
v___x_1627_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v___y_1615_, v___y_1616_, v___y_1617_, v___y_1618_, v___y_1619_, v___y_1620_, v___y_1621_, v___y_1622_, v___y_1623_, v___y_1624_, v___y_1625_);
if (lean_obj_tag(v___x_1627_) == 0)
{
lean_object* v_a_1628_; lean_object* v_toRing_1629_; lean_object* v_type_1630_; lean_object* v_u_1631_; lean_object* v_semiringInst_1632_; lean_object* v___x_1633_; lean_object* v_n_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; 
v_a_1628_ = lean_ctor_get(v___x_1627_, 0);
lean_inc(v_a_1628_);
lean_dec_ref(v___x_1627_);
v_toRing_1629_ = lean_ctor_get(v_a_1628_, 0);
lean_inc_ref(v_toRing_1629_);
lean_dec(v_a_1628_);
v_type_1630_ = lean_ctor_get(v_toRing_1629_, 1);
lean_inc_ref_n(v_type_1630_, 2);
v_u_1631_ = lean_ctor_get(v_toRing_1629_, 2);
lean_inc(v_u_1631_);
v_semiringInst_1632_ = lean_ctor_get(v_toRing_1629_, 4);
lean_inc_ref(v_semiringInst_1632_);
lean_dec_ref(v_toRing_1629_);
v___x_1633_ = lean_nat_abs(v_k_1614_);
v_n_1634_ = l_Lean_mkRawNatLit(v___x_1633_);
v___x_1635_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__4___closed__0));
v___x_1636_ = lean_box(0);
v___x_1637_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1637_, 0, v_u_1631_);
lean_ctor_set(v___x_1637_, 1, v___x_1636_);
lean_inc_ref(v___x_1637_);
v___x_1638_ = l_Lean_mkConst(v___x_1635_, v___x_1637_);
lean_inc_ref(v_n_1634_);
v___x_1639_ = l_Lean_mkAppB(v___x_1638_, v_type_1630_, v_n_1634_);
v___x_1640_ = lean_box(0);
v___x_1641_ = l_Lean_Meta_synthInstance_x3f(v___x_1639_, v___x_1640_, v___y_1622_, v___y_1623_, v___y_1624_, v___y_1625_);
if (lean_obj_tag(v___x_1641_) == 0)
{
lean_object* v_a_1642_; lean_object* v___x_1644_; uint8_t v_isShared_1645_; uint8_t v_isSharedCheck_1681_; 
v_a_1642_ = lean_ctor_get(v___x_1641_, 0);
v_isSharedCheck_1681_ = !lean_is_exclusive(v___x_1641_);
if (v_isSharedCheck_1681_ == 0)
{
v___x_1644_ = v___x_1641_;
v_isShared_1645_ = v_isSharedCheck_1681_;
goto v_resetjp_1643_;
}
else
{
lean_inc(v_a_1642_);
lean_dec(v___x_1641_);
v___x_1644_ = lean_box(0);
v_isShared_1645_ = v_isSharedCheck_1681_;
goto v_resetjp_1643_;
}
v_resetjp_1643_:
{
lean_object* v_ofNatInst_1647_; lean_object* v___y_1648_; lean_object* v___y_1649_; lean_object* v___y_1650_; lean_object* v___y_1651_; lean_object* v___y_1652_; lean_object* v___y_1653_; lean_object* v___y_1654_; lean_object* v___y_1655_; lean_object* v___y_1656_; lean_object* v___y_1657_; lean_object* v___y_1658_; 
if (lean_obj_tag(v_a_1642_) == 1)
{
lean_object* v_val_1677_; 
lean_dec_ref(v_semiringInst_1632_);
v_val_1677_ = lean_ctor_get(v_a_1642_, 0);
lean_inc(v_val_1677_);
lean_dec_ref(v_a_1642_);
v_ofNatInst_1647_ = v_val_1677_;
v___y_1648_ = v___y_1615_;
v___y_1649_ = v___y_1616_;
v___y_1650_ = v___y_1617_;
v___y_1651_ = v___y_1618_;
v___y_1652_ = v___y_1619_;
v___y_1653_ = v___y_1620_;
v___y_1654_ = v___y_1621_;
v___y_1655_ = v___y_1622_;
v___y_1656_ = v___y_1623_;
v___y_1657_ = v___y_1624_;
v___y_1658_ = v___y_1625_;
goto v___jp_1646_;
}
else
{
lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; 
lean_dec(v_a_1642_);
v___x_1678_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__4___closed__2));
lean_inc_ref(v___x_1637_);
v___x_1679_ = l_Lean_mkConst(v___x_1678_, v___x_1637_);
lean_inc_ref(v_n_1634_);
lean_inc_ref(v_type_1630_);
v___x_1680_ = l_Lean_mkApp3(v___x_1679_, v_type_1630_, v_semiringInst_1632_, v_n_1634_);
v_ofNatInst_1647_ = v___x_1680_;
v___y_1648_ = v___y_1615_;
v___y_1649_ = v___y_1616_;
v___y_1650_ = v___y_1617_;
v___y_1651_ = v___y_1618_;
v___y_1652_ = v___y_1619_;
v___y_1653_ = v___y_1620_;
v___y_1654_ = v___y_1621_;
v___y_1655_ = v___y_1622_;
v___y_1656_ = v___y_1623_;
v___y_1657_ = v___y_1624_;
v___y_1658_ = v___y_1625_;
goto v___jp_1646_;
}
v___jp_1646_:
{
lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v_n_1661_; lean_object* v___x_1662_; uint8_t v___x_1663_; 
v___x_1659_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__8));
v___x_1660_ = l_Lean_mkConst(v___x_1659_, v___x_1637_);
v_n_1661_ = l_Lean_mkApp3(v___x_1660_, v_type_1630_, v_n_1634_, v_ofNatInst_1647_);
v___x_1662_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__4___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__4___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__4___closed__1);
v___x_1663_ = lean_int_dec_lt(v_k_1614_, v___x_1662_);
if (v___x_1663_ == 0)
{
lean_object* v___x_1665_; 
if (v_isShared_1645_ == 0)
{
lean_ctor_set(v___x_1644_, 0, v_n_1661_);
v___x_1665_ = v___x_1644_;
goto v_reusejp_1664_;
}
else
{
lean_object* v_reuseFailAlloc_1666_; 
v_reuseFailAlloc_1666_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1666_, 0, v_n_1661_);
v___x_1665_ = v_reuseFailAlloc_1666_;
goto v_reusejp_1664_;
}
v_reusejp_1664_:
{
return v___x_1665_;
}
}
else
{
lean_object* v___x_1667_; 
lean_del_object(v___x_1644_);
v___x_1667_ = l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0(v___y_1648_, v___y_1649_, v___y_1650_, v___y_1651_, v___y_1652_, v___y_1653_, v___y_1654_, v___y_1655_, v___y_1656_, v___y_1657_, v___y_1658_);
if (lean_obj_tag(v___x_1667_) == 0)
{
lean_object* v_a_1668_; lean_object* v___x_1670_; uint8_t v_isShared_1671_; uint8_t v_isSharedCheck_1676_; 
v_a_1668_ = lean_ctor_get(v___x_1667_, 0);
v_isSharedCheck_1676_ = !lean_is_exclusive(v___x_1667_);
if (v_isSharedCheck_1676_ == 0)
{
v___x_1670_ = v___x_1667_;
v_isShared_1671_ = v_isSharedCheck_1676_;
goto v_resetjp_1669_;
}
else
{
lean_inc(v_a_1668_);
lean_dec(v___x_1667_);
v___x_1670_ = lean_box(0);
v_isShared_1671_ = v_isSharedCheck_1676_;
goto v_resetjp_1669_;
}
v_resetjp_1669_:
{
lean_object* v___x_1672_; lean_object* v___x_1674_; 
v___x_1672_ = l_Lean_Expr_app___override(v_a_1668_, v_n_1661_);
if (v_isShared_1671_ == 0)
{
lean_ctor_set(v___x_1670_, 0, v___x_1672_);
v___x_1674_ = v___x_1670_;
goto v_reusejp_1673_;
}
else
{
lean_object* v_reuseFailAlloc_1675_; 
v_reuseFailAlloc_1675_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1675_, 0, v___x_1672_);
v___x_1674_ = v_reuseFailAlloc_1675_;
goto v_reusejp_1673_;
}
v_reusejp_1673_:
{
return v___x_1674_;
}
}
}
else
{
lean_dec_ref(v_n_1661_);
return v___x_1667_;
}
}
}
}
}
else
{
lean_object* v_a_1682_; lean_object* v___x_1684_; uint8_t v_isShared_1685_; uint8_t v_isSharedCheck_1689_; 
lean_dec_ref(v___x_1637_);
lean_dec_ref(v_n_1634_);
lean_dec_ref(v_semiringInst_1632_);
lean_dec_ref(v_type_1630_);
v_a_1682_ = lean_ctor_get(v___x_1641_, 0);
v_isSharedCheck_1689_ = !lean_is_exclusive(v___x_1641_);
if (v_isSharedCheck_1689_ == 0)
{
v___x_1684_ = v___x_1641_;
v_isShared_1685_ = v_isSharedCheck_1689_;
goto v_resetjp_1683_;
}
else
{
lean_inc(v_a_1682_);
lean_dec(v___x_1641_);
v___x_1684_ = lean_box(0);
v_isShared_1685_ = v_isSharedCheck_1689_;
goto v_resetjp_1683_;
}
v_resetjp_1683_:
{
lean_object* v___x_1687_; 
if (v_isShared_1685_ == 0)
{
v___x_1687_ = v___x_1684_;
goto v_reusejp_1686_;
}
else
{
lean_object* v_reuseFailAlloc_1688_; 
v_reuseFailAlloc_1688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1688_, 0, v_a_1682_);
v___x_1687_ = v_reuseFailAlloc_1688_;
goto v_reusejp_1686_;
}
v_reusejp_1686_:
{
return v___x_1687_;
}
}
}
}
else
{
lean_object* v_a_1690_; lean_object* v___x_1692_; uint8_t v_isShared_1693_; uint8_t v_isSharedCheck_1697_; 
v_a_1690_ = lean_ctor_get(v___x_1627_, 0);
v_isSharedCheck_1697_ = !lean_is_exclusive(v___x_1627_);
if (v_isSharedCheck_1697_ == 0)
{
v___x_1692_ = v___x_1627_;
v_isShared_1693_ = v_isSharedCheck_1697_;
goto v_resetjp_1691_;
}
else
{
lean_inc(v_a_1690_);
lean_dec(v___x_1627_);
v___x_1692_ = lean_box(0);
v_isShared_1693_ = v_isSharedCheck_1697_;
goto v_resetjp_1691_;
}
v_resetjp_1691_:
{
lean_object* v___x_1695_; 
if (v_isShared_1693_ == 0)
{
v___x_1695_ = v___x_1692_;
goto v_reusejp_1694_;
}
else
{
lean_object* v_reuseFailAlloc_1696_; 
v_reuseFailAlloc_1696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1696_, 0, v_a_1690_);
v___x_1695_ = v_reuseFailAlloc_1696_;
goto v_reusejp_1694_;
}
v_reusejp_1694_:
{
return v___x_1695_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__4___boxed(lean_object* v_k_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_){
_start:
{
lean_object* v_res_1711_; 
v_res_1711_ = l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__4(v_k_1698_, v___y_1699_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_, v___y_1706_, v___y_1707_, v___y_1708_, v___y_1709_);
lean_dec(v___y_1709_);
lean_dec_ref(v___y_1708_);
lean_dec(v___y_1707_);
lean_dec_ref(v___y_1706_);
lean_dec(v___y_1705_);
lean_dec_ref(v___y_1704_);
lean_dec(v___y_1703_);
lean_dec_ref(v___y_1702_);
lean_dec(v___y_1701_);
lean_dec(v___y_1700_);
lean_dec_ref(v___y_1699_);
lean_dec(v_k_1698_);
return v_res_1711_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1_spec__2_spec__6___redArg(lean_object* v_keys_1712_, lean_object* v_i_1713_, lean_object* v_k_1714_){
_start:
{
lean_object* v___x_1715_; uint8_t v___x_1716_; 
v___x_1715_ = lean_array_get_size(v_keys_1712_);
v___x_1716_ = lean_nat_dec_lt(v_i_1713_, v___x_1715_);
if (v___x_1716_ == 0)
{
lean_dec(v_i_1713_);
return v___x_1716_;
}
else
{
lean_object* v_k_x27_1717_; uint8_t v___x_1718_; 
v_k_x27_1717_ = lean_array_fget_borrowed(v_keys_1712_, v_i_1713_);
v___x_1718_ = lean_expr_eqv(v_k_1714_, v_k_x27_1717_);
if (v___x_1718_ == 0)
{
lean_object* v___x_1719_; lean_object* v___x_1720_; 
v___x_1719_ = lean_unsigned_to_nat(1u);
v___x_1720_ = lean_nat_add(v_i_1713_, v___x_1719_);
lean_dec(v_i_1713_);
v_i_1713_ = v___x_1720_;
goto _start;
}
else
{
lean_dec(v_i_1713_);
return v___x_1718_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1_spec__2_spec__6___redArg___boxed(lean_object* v_keys_1722_, lean_object* v_i_1723_, lean_object* v_k_1724_){
_start:
{
uint8_t v_res_1725_; lean_object* v_r_1726_; 
v_res_1725_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1_spec__2_spec__6___redArg(v_keys_1722_, v_i_1723_, v_k_1724_);
lean_dec_ref(v_k_1724_);
lean_dec_ref(v_keys_1722_);
v_r_1726_ = lean_box(v_res_1725_);
return v_r_1726_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1_spec__2___redArg(lean_object* v_x_1727_, size_t v_x_1728_, lean_object* v_x_1729_){
_start:
{
if (lean_obj_tag(v_x_1727_) == 0)
{
lean_object* v_es_1730_; lean_object* v___x_1731_; size_t v___x_1732_; size_t v___x_1733_; size_t v___x_1734_; lean_object* v_j_1735_; lean_object* v___x_1736_; 
v_es_1730_ = lean_ctor_get(v_x_1727_, 0);
v___x_1731_ = lean_box(2);
v___x_1732_ = ((size_t)5ULL);
v___x_1733_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg___closed__1);
v___x_1734_ = lean_usize_land(v_x_1728_, v___x_1733_);
v_j_1735_ = lean_usize_to_nat(v___x_1734_);
v___x_1736_ = lean_array_get_borrowed(v___x_1731_, v_es_1730_, v_j_1735_);
lean_dec(v_j_1735_);
switch(lean_obj_tag(v___x_1736_))
{
case 0:
{
lean_object* v_key_1737_; uint8_t v___x_1738_; 
v_key_1737_ = lean_ctor_get(v___x_1736_, 0);
v___x_1738_ = lean_expr_eqv(v_x_1729_, v_key_1737_);
return v___x_1738_;
}
case 1:
{
lean_object* v_node_1739_; size_t v___x_1740_; 
v_node_1739_ = lean_ctor_get(v___x_1736_, 0);
v___x_1740_ = lean_usize_shift_right(v_x_1728_, v___x_1732_);
v_x_1727_ = v_node_1739_;
v_x_1728_ = v___x_1740_;
goto _start;
}
default: 
{
uint8_t v___x_1742_; 
v___x_1742_ = 0;
return v___x_1742_;
}
}
}
else
{
lean_object* v_ks_1743_; lean_object* v___x_1744_; uint8_t v___x_1745_; 
v_ks_1743_ = lean_ctor_get(v_x_1727_, 0);
v___x_1744_ = lean_unsigned_to_nat(0u);
v___x_1745_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1_spec__2_spec__6___redArg(v_ks_1743_, v___x_1744_, v_x_1729_);
return v___x_1745_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1_spec__2___redArg___boxed(lean_object* v_x_1746_, lean_object* v_x_1747_, lean_object* v_x_1748_){
_start:
{
size_t v_x_140701__boxed_1749_; uint8_t v_res_1750_; lean_object* v_r_1751_; 
v_x_140701__boxed_1749_ = lean_unbox_usize(v_x_1747_);
lean_dec(v_x_1747_);
v_res_1750_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1_spec__2___redArg(v_x_1746_, v_x_140701__boxed_1749_, v_x_1748_);
lean_dec_ref(v_x_1748_);
lean_dec_ref(v_x_1746_);
v_r_1751_ = lean_box(v_res_1750_);
return v_r_1751_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1___redArg(lean_object* v_x_1752_, lean_object* v_x_1753_){
_start:
{
uint64_t v___x_1754_; size_t v___x_1755_; uint8_t v___x_1756_; 
v___x_1754_ = l_Lean_Expr_hash(v_x_1753_);
v___x_1755_ = lean_uint64_to_usize(v___x_1754_);
v___x_1756_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1_spec__2___redArg(v_x_1752_, v___x_1755_, v_x_1753_);
return v___x_1756_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1___redArg___boxed(lean_object* v_x_1757_, lean_object* v_x_1758_){
_start:
{
uint8_t v_res_1759_; lean_object* v_r_1760_; 
v_res_1759_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1___redArg(v_x_1757_, v_x_1758_);
lean_dec_ref(v_x_1758_);
lean_dec_ref(v_x_1757_);
v_r_1760_ = lean_box(v_res_1759_);
return v_r_1760_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__3___lam__0(lean_object* v_a_1761_, lean_object* v_s_1762_){
_start:
{
lean_object* v_toRing_1763_; lean_object* v_invFn_x3f_1764_; lean_object* v_semiringId_x3f_1765_; lean_object* v_commSemiringInst_1766_; lean_object* v_commRingInst_1767_; lean_object* v_noZeroDivInst_x3f_1768_; lean_object* v_fieldInst_x3f_1769_; lean_object* v_denoteEntries_1770_; lean_object* v_nextId_1771_; lean_object* v_steps_1772_; lean_object* v_queue_1773_; lean_object* v_basis_1774_; lean_object* v_diseqs_1775_; uint8_t v_recheck_1776_; lean_object* v_invSet_1777_; lean_object* v_numEq0_x3f_1778_; uint8_t v_numEq0Updated_1779_; lean_object* v___x_1781_; uint8_t v_isShared_1782_; uint8_t v_isSharedCheck_1811_; 
v_toRing_1763_ = lean_ctor_get(v_s_1762_, 0);
v_invFn_x3f_1764_ = lean_ctor_get(v_s_1762_, 1);
v_semiringId_x3f_1765_ = lean_ctor_get(v_s_1762_, 2);
v_commSemiringInst_1766_ = lean_ctor_get(v_s_1762_, 3);
v_commRingInst_1767_ = lean_ctor_get(v_s_1762_, 4);
v_noZeroDivInst_x3f_1768_ = lean_ctor_get(v_s_1762_, 5);
v_fieldInst_x3f_1769_ = lean_ctor_get(v_s_1762_, 6);
v_denoteEntries_1770_ = lean_ctor_get(v_s_1762_, 7);
v_nextId_1771_ = lean_ctor_get(v_s_1762_, 8);
v_steps_1772_ = lean_ctor_get(v_s_1762_, 9);
v_queue_1773_ = lean_ctor_get(v_s_1762_, 10);
v_basis_1774_ = lean_ctor_get(v_s_1762_, 11);
v_diseqs_1775_ = lean_ctor_get(v_s_1762_, 12);
v_recheck_1776_ = lean_ctor_get_uint8(v_s_1762_, sizeof(void*)*15);
v_invSet_1777_ = lean_ctor_get(v_s_1762_, 13);
v_numEq0_x3f_1778_ = lean_ctor_get(v_s_1762_, 14);
v_numEq0Updated_1779_ = lean_ctor_get_uint8(v_s_1762_, sizeof(void*)*15 + 1);
v_isSharedCheck_1811_ = !lean_is_exclusive(v_s_1762_);
if (v_isSharedCheck_1811_ == 0)
{
v___x_1781_ = v_s_1762_;
v_isShared_1782_ = v_isSharedCheck_1811_;
goto v_resetjp_1780_;
}
else
{
lean_inc(v_numEq0_x3f_1778_);
lean_inc(v_invSet_1777_);
lean_inc(v_diseqs_1775_);
lean_inc(v_basis_1774_);
lean_inc(v_queue_1773_);
lean_inc(v_steps_1772_);
lean_inc(v_nextId_1771_);
lean_inc(v_denoteEntries_1770_);
lean_inc(v_fieldInst_x3f_1769_);
lean_inc(v_noZeroDivInst_x3f_1768_);
lean_inc(v_commRingInst_1767_);
lean_inc(v_commSemiringInst_1766_);
lean_inc(v_semiringId_x3f_1765_);
lean_inc(v_invFn_x3f_1764_);
lean_inc(v_toRing_1763_);
lean_dec(v_s_1762_);
v___x_1781_ = lean_box(0);
v_isShared_1782_ = v_isSharedCheck_1811_;
goto v_resetjp_1780_;
}
v_resetjp_1780_:
{
lean_object* v_id_1783_; lean_object* v_type_1784_; lean_object* v_u_1785_; lean_object* v_ringInst_1786_; lean_object* v_semiringInst_1787_; lean_object* v_charInst_x3f_1788_; lean_object* v_addFn_x3f_1789_; lean_object* v_subFn_x3f_1790_; lean_object* v_negFn_x3f_1791_; lean_object* v_powFn_x3f_1792_; lean_object* v_intCastFn_x3f_1793_; lean_object* v_natCastFn_x3f_1794_; lean_object* v_one_x3f_1795_; lean_object* v_vars_1796_; lean_object* v_varMap_1797_; lean_object* v_denote_1798_; lean_object* v___x_1800_; uint8_t v_isShared_1801_; uint8_t v_isSharedCheck_1809_; 
v_id_1783_ = lean_ctor_get(v_toRing_1763_, 0);
v_type_1784_ = lean_ctor_get(v_toRing_1763_, 1);
v_u_1785_ = lean_ctor_get(v_toRing_1763_, 2);
v_ringInst_1786_ = lean_ctor_get(v_toRing_1763_, 3);
v_semiringInst_1787_ = lean_ctor_get(v_toRing_1763_, 4);
v_charInst_x3f_1788_ = lean_ctor_get(v_toRing_1763_, 5);
v_addFn_x3f_1789_ = lean_ctor_get(v_toRing_1763_, 6);
v_subFn_x3f_1790_ = lean_ctor_get(v_toRing_1763_, 8);
v_negFn_x3f_1791_ = lean_ctor_get(v_toRing_1763_, 9);
v_powFn_x3f_1792_ = lean_ctor_get(v_toRing_1763_, 10);
v_intCastFn_x3f_1793_ = lean_ctor_get(v_toRing_1763_, 11);
v_natCastFn_x3f_1794_ = lean_ctor_get(v_toRing_1763_, 12);
v_one_x3f_1795_ = lean_ctor_get(v_toRing_1763_, 13);
v_vars_1796_ = lean_ctor_get(v_toRing_1763_, 14);
v_varMap_1797_ = lean_ctor_get(v_toRing_1763_, 15);
v_denote_1798_ = lean_ctor_get(v_toRing_1763_, 16);
v_isSharedCheck_1809_ = !lean_is_exclusive(v_toRing_1763_);
if (v_isSharedCheck_1809_ == 0)
{
lean_object* v_unused_1810_; 
v_unused_1810_ = lean_ctor_get(v_toRing_1763_, 7);
lean_dec(v_unused_1810_);
v___x_1800_ = v_toRing_1763_;
v_isShared_1801_ = v_isSharedCheck_1809_;
goto v_resetjp_1799_;
}
else
{
lean_inc(v_denote_1798_);
lean_inc(v_varMap_1797_);
lean_inc(v_vars_1796_);
lean_inc(v_one_x3f_1795_);
lean_inc(v_natCastFn_x3f_1794_);
lean_inc(v_intCastFn_x3f_1793_);
lean_inc(v_powFn_x3f_1792_);
lean_inc(v_negFn_x3f_1791_);
lean_inc(v_subFn_x3f_1790_);
lean_inc(v_addFn_x3f_1789_);
lean_inc(v_charInst_x3f_1788_);
lean_inc(v_semiringInst_1787_);
lean_inc(v_ringInst_1786_);
lean_inc(v_u_1785_);
lean_inc(v_type_1784_);
lean_inc(v_id_1783_);
lean_dec(v_toRing_1763_);
v___x_1800_ = lean_box(0);
v_isShared_1801_ = v_isSharedCheck_1809_;
goto v_resetjp_1799_;
}
v_resetjp_1799_:
{
lean_object* v___x_1802_; lean_object* v___x_1804_; 
v___x_1802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1802_, 0, v_a_1761_);
if (v_isShared_1801_ == 0)
{
lean_ctor_set(v___x_1800_, 7, v___x_1802_);
v___x_1804_ = v___x_1800_;
goto v_reusejp_1803_;
}
else
{
lean_object* v_reuseFailAlloc_1808_; 
v_reuseFailAlloc_1808_ = lean_alloc_ctor(0, 17, 0);
lean_ctor_set(v_reuseFailAlloc_1808_, 0, v_id_1783_);
lean_ctor_set(v_reuseFailAlloc_1808_, 1, v_type_1784_);
lean_ctor_set(v_reuseFailAlloc_1808_, 2, v_u_1785_);
lean_ctor_set(v_reuseFailAlloc_1808_, 3, v_ringInst_1786_);
lean_ctor_set(v_reuseFailAlloc_1808_, 4, v_semiringInst_1787_);
lean_ctor_set(v_reuseFailAlloc_1808_, 5, v_charInst_x3f_1788_);
lean_ctor_set(v_reuseFailAlloc_1808_, 6, v_addFn_x3f_1789_);
lean_ctor_set(v_reuseFailAlloc_1808_, 7, v___x_1802_);
lean_ctor_set(v_reuseFailAlloc_1808_, 8, v_subFn_x3f_1790_);
lean_ctor_set(v_reuseFailAlloc_1808_, 9, v_negFn_x3f_1791_);
lean_ctor_set(v_reuseFailAlloc_1808_, 10, v_powFn_x3f_1792_);
lean_ctor_set(v_reuseFailAlloc_1808_, 11, v_intCastFn_x3f_1793_);
lean_ctor_set(v_reuseFailAlloc_1808_, 12, v_natCastFn_x3f_1794_);
lean_ctor_set(v_reuseFailAlloc_1808_, 13, v_one_x3f_1795_);
lean_ctor_set(v_reuseFailAlloc_1808_, 14, v_vars_1796_);
lean_ctor_set(v_reuseFailAlloc_1808_, 15, v_varMap_1797_);
lean_ctor_set(v_reuseFailAlloc_1808_, 16, v_denote_1798_);
v___x_1804_ = v_reuseFailAlloc_1808_;
goto v_reusejp_1803_;
}
v_reusejp_1803_:
{
lean_object* v___x_1806_; 
if (v_isShared_1782_ == 0)
{
lean_ctor_set(v___x_1781_, 0, v___x_1804_);
v___x_1806_ = v___x_1781_;
goto v_reusejp_1805_;
}
else
{
lean_object* v_reuseFailAlloc_1807_; 
v_reuseFailAlloc_1807_ = lean_alloc_ctor(0, 15, 2);
lean_ctor_set(v_reuseFailAlloc_1807_, 0, v___x_1804_);
lean_ctor_set(v_reuseFailAlloc_1807_, 1, v_invFn_x3f_1764_);
lean_ctor_set(v_reuseFailAlloc_1807_, 2, v_semiringId_x3f_1765_);
lean_ctor_set(v_reuseFailAlloc_1807_, 3, v_commSemiringInst_1766_);
lean_ctor_set(v_reuseFailAlloc_1807_, 4, v_commRingInst_1767_);
lean_ctor_set(v_reuseFailAlloc_1807_, 5, v_noZeroDivInst_x3f_1768_);
lean_ctor_set(v_reuseFailAlloc_1807_, 6, v_fieldInst_x3f_1769_);
lean_ctor_set(v_reuseFailAlloc_1807_, 7, v_denoteEntries_1770_);
lean_ctor_set(v_reuseFailAlloc_1807_, 8, v_nextId_1771_);
lean_ctor_set(v_reuseFailAlloc_1807_, 9, v_steps_1772_);
lean_ctor_set(v_reuseFailAlloc_1807_, 10, v_queue_1773_);
lean_ctor_set(v_reuseFailAlloc_1807_, 11, v_basis_1774_);
lean_ctor_set(v_reuseFailAlloc_1807_, 12, v_diseqs_1775_);
lean_ctor_set(v_reuseFailAlloc_1807_, 13, v_invSet_1777_);
lean_ctor_set(v_reuseFailAlloc_1807_, 14, v_numEq0_x3f_1778_);
lean_ctor_set_uint8(v_reuseFailAlloc_1807_, sizeof(void*)*15, v_recheck_1776_);
lean_ctor_set_uint8(v_reuseFailAlloc_1807_, sizeof(void*)*15 + 1, v_numEq0Updated_1779_);
v___x_1806_ = v_reuseFailAlloc_1807_;
goto v_reusejp_1805_;
}
v_reusejp_1805_:
{
return v___x_1806_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__3_spec__5(lean_object* v_type_1812_, lean_object* v_u_1813_, lean_object* v_instDeclName_1814_, lean_object* v_declName_1815_, lean_object* v_expectedInst_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_){
_start:
{
lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; 
v___x_1829_ = lean_box(0);
lean_inc_n(v_u_1813_, 2);
v___x_1830_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1830_, 0, v_u_1813_);
lean_ctor_set(v___x_1830_, 1, v___x_1829_);
v___x_1831_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1831_, 0, v_u_1813_);
lean_ctor_set(v___x_1831_, 1, v___x_1830_);
v___x_1832_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1832_, 0, v_u_1813_);
lean_ctor_set(v___x_1832_, 1, v___x_1831_);
lean_inc_ref(v___x_1832_);
v___x_1833_ = l_Lean_mkConst(v_instDeclName_1814_, v___x_1832_);
lean_inc_ref_n(v_type_1812_, 3);
v___x_1834_ = l_Lean_mkApp3(v___x_1833_, v_type_1812_, v_type_1812_, v_type_1812_);
v___x_1835_ = l_Lean_Meta_Grind_Arith_CommRing_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1_spec__5(v___x_1834_, v___y_1817_, v___y_1818_, v___y_1819_, v___y_1820_, v___y_1821_, v___y_1822_, v___y_1823_, v___y_1824_, v___y_1825_, v___y_1826_, v___y_1827_);
if (lean_obj_tag(v___x_1835_) == 0)
{
lean_object* v_a_1836_; lean_object* v___x_1837_; 
v_a_1836_ = lean_ctor_get(v___x_1835_, 0);
lean_inc_n(v_a_1836_, 2);
lean_dec_ref(v___x_1835_);
lean_inc(v_declName_1815_);
v___x_1837_ = l_Lean_Meta_Grind_Arith_CommRing_checkInst(v_declName_1815_, v_a_1836_, v_expectedInst_1816_, v___y_1824_, v___y_1825_, v___y_1826_, v___y_1827_);
if (lean_obj_tag(v___x_1837_) == 0)
{
lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; 
lean_dec_ref(v___x_1837_);
v___x_1838_ = l_Lean_mkConst(v_declName_1815_, v___x_1832_);
lean_inc_ref_n(v_type_1812_, 2);
v___x_1839_ = l_Lean_mkApp4(v___x_1838_, v_type_1812_, v_type_1812_, v_type_1812_, v_a_1836_);
v___x_1840_ = l_Lean_Meta_Sym_canon(v___x_1839_, v___y_1822_, v___y_1823_, v___y_1824_, v___y_1825_, v___y_1826_, v___y_1827_);
if (lean_obj_tag(v___x_1840_) == 0)
{
lean_object* v_a_1841_; lean_object* v___x_1842_; 
v_a_1841_ = lean_ctor_get(v___x_1840_, 0);
lean_inc(v_a_1841_);
lean_dec_ref(v___x_1840_);
v___x_1842_ = l_Lean_Meta_Sym_shareCommon___redArg(v_a_1841_, v___y_1823_);
return v___x_1842_;
}
else
{
return v___x_1840_;
}
}
else
{
lean_object* v_a_1843_; lean_object* v___x_1845_; uint8_t v_isShared_1846_; uint8_t v_isSharedCheck_1850_; 
lean_dec(v_a_1836_);
lean_dec_ref(v___x_1832_);
lean_dec(v_declName_1815_);
lean_dec_ref(v_type_1812_);
v_a_1843_ = lean_ctor_get(v___x_1837_, 0);
v_isSharedCheck_1850_ = !lean_is_exclusive(v___x_1837_);
if (v_isSharedCheck_1850_ == 0)
{
v___x_1845_ = v___x_1837_;
v_isShared_1846_ = v_isSharedCheck_1850_;
goto v_resetjp_1844_;
}
else
{
lean_inc(v_a_1843_);
lean_dec(v___x_1837_);
v___x_1845_ = lean_box(0);
v_isShared_1846_ = v_isSharedCheck_1850_;
goto v_resetjp_1844_;
}
v_resetjp_1844_:
{
lean_object* v___x_1848_; 
if (v_isShared_1846_ == 0)
{
v___x_1848_ = v___x_1845_;
goto v_reusejp_1847_;
}
else
{
lean_object* v_reuseFailAlloc_1849_; 
v_reuseFailAlloc_1849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1849_, 0, v_a_1843_);
v___x_1848_ = v_reuseFailAlloc_1849_;
goto v_reusejp_1847_;
}
v_reusejp_1847_:
{
return v___x_1848_;
}
}
}
}
else
{
lean_dec_ref(v___x_1832_);
lean_dec_ref(v_expectedInst_1816_);
lean_dec(v_declName_1815_);
lean_dec_ref(v_type_1812_);
return v___x_1835_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__3_spec__5___boxed(lean_object** _args){
lean_object* v_type_1851_ = _args[0];
lean_object* v_u_1852_ = _args[1];
lean_object* v_instDeclName_1853_ = _args[2];
lean_object* v_declName_1854_ = _args[3];
lean_object* v_expectedInst_1855_ = _args[4];
lean_object* v___y_1856_ = _args[5];
lean_object* v___y_1857_ = _args[6];
lean_object* v___y_1858_ = _args[7];
lean_object* v___y_1859_ = _args[8];
lean_object* v___y_1860_ = _args[9];
lean_object* v___y_1861_ = _args[10];
lean_object* v___y_1862_ = _args[11];
lean_object* v___y_1863_ = _args[12];
lean_object* v___y_1864_ = _args[13];
lean_object* v___y_1865_ = _args[14];
lean_object* v___y_1866_ = _args[15];
lean_object* v___y_1867_ = _args[16];
_start:
{
lean_object* v_res_1868_; 
v_res_1868_ = l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__3_spec__5(v_type_1851_, v_u_1852_, v_instDeclName_1853_, v_declName_1854_, v_expectedInst_1855_, v___y_1856_, v___y_1857_, v___y_1858_, v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_, v___y_1863_, v___y_1864_, v___y_1865_, v___y_1866_);
lean_dec(v___y_1866_);
lean_dec_ref(v___y_1865_);
lean_dec(v___y_1864_);
lean_dec_ref(v___y_1863_);
lean_dec(v___y_1862_);
lean_dec_ref(v___y_1861_);
lean_dec(v___y_1860_);
lean_dec_ref(v___y_1859_);
lean_dec(v___y_1858_);
lean_dec(v___y_1857_);
lean_dec_ref(v___y_1856_);
return v_res_1868_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__3(lean_object* v___y_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_){
_start:
{
lean_object* v___x_1892_; 
v___x_1892_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v___y_1880_, v___y_1881_, v___y_1882_, v___y_1883_, v___y_1884_, v___y_1885_, v___y_1886_, v___y_1887_, v___y_1888_, v___y_1889_, v___y_1890_);
if (lean_obj_tag(v___x_1892_) == 0)
{
lean_object* v_a_1893_; lean_object* v___x_1895_; uint8_t v_isShared_1896_; uint8_t v_isSharedCheck_1936_; 
v_a_1893_ = lean_ctor_get(v___x_1892_, 0);
v_isSharedCheck_1936_ = !lean_is_exclusive(v___x_1892_);
if (v_isSharedCheck_1936_ == 0)
{
v___x_1895_ = v___x_1892_;
v_isShared_1896_ = v_isSharedCheck_1936_;
goto v_resetjp_1894_;
}
else
{
lean_inc(v_a_1893_);
lean_dec(v___x_1892_);
v___x_1895_ = lean_box(0);
v_isShared_1896_ = v_isSharedCheck_1936_;
goto v_resetjp_1894_;
}
v_resetjp_1894_:
{
lean_object* v_toRing_1897_; lean_object* v_mulFn_x3f_1898_; 
v_toRing_1897_ = lean_ctor_get(v_a_1893_, 0);
lean_inc_ref(v_toRing_1897_);
lean_dec(v_a_1893_);
v_mulFn_x3f_1898_ = lean_ctor_get(v_toRing_1897_, 7);
if (lean_obj_tag(v_mulFn_x3f_1898_) == 1)
{
lean_object* v_val_1899_; lean_object* v___x_1901_; 
lean_inc_ref(v_mulFn_x3f_1898_);
lean_dec_ref(v_toRing_1897_);
v_val_1899_ = lean_ctor_get(v_mulFn_x3f_1898_, 0);
lean_inc(v_val_1899_);
lean_dec_ref(v_mulFn_x3f_1898_);
if (v_isShared_1896_ == 0)
{
lean_ctor_set(v___x_1895_, 0, v_val_1899_);
v___x_1901_ = v___x_1895_;
goto v_reusejp_1900_;
}
else
{
lean_object* v_reuseFailAlloc_1902_; 
v_reuseFailAlloc_1902_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1902_, 0, v_val_1899_);
v___x_1901_ = v_reuseFailAlloc_1902_;
goto v_reusejp_1900_;
}
v_reusejp_1900_:
{
return v___x_1901_;
}
}
else
{
lean_object* v_type_1903_; lean_object* v_u_1904_; lean_object* v_semiringInst_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v_expectedInst_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; 
lean_del_object(v___x_1895_);
v_type_1903_ = lean_ctor_get(v_toRing_1897_, 1);
lean_inc_ref_n(v_type_1903_, 3);
v_u_1904_ = lean_ctor_get(v_toRing_1897_, 2);
lean_inc_n(v_u_1904_, 2);
v_semiringInst_1905_ = lean_ctor_get(v_toRing_1897_, 4);
lean_inc_ref(v_semiringInst_1905_);
lean_dec_ref(v_toRing_1897_);
v___x_1906_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__3___closed__1));
v___x_1907_ = lean_box(0);
v___x_1908_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1908_, 0, v_u_1904_);
lean_ctor_set(v___x_1908_, 1, v___x_1907_);
lean_inc_ref(v___x_1908_);
v___x_1909_ = l_Lean_mkConst(v___x_1906_, v___x_1908_);
v___x_1910_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__3___closed__3));
v___x_1911_ = l_Lean_mkConst(v___x_1910_, v___x_1908_);
v___x_1912_ = l_Lean_mkAppB(v___x_1911_, v_type_1903_, v_semiringInst_1905_);
v_expectedInst_1913_ = l_Lean_mkAppB(v___x_1909_, v_type_1903_, v___x_1912_);
v___x_1914_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__3___closed__4));
v___x_1915_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__20));
v___x_1916_ = l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__3_spec__5(v_type_1903_, v_u_1904_, v___x_1914_, v___x_1915_, v_expectedInst_1913_, v___y_1880_, v___y_1881_, v___y_1882_, v___y_1883_, v___y_1884_, v___y_1885_, v___y_1886_, v___y_1887_, v___y_1888_, v___y_1889_, v___y_1890_);
if (lean_obj_tag(v___x_1916_) == 0)
{
lean_object* v_a_1917_; lean_object* v___f_1918_; lean_object* v___x_1919_; 
v_a_1917_ = lean_ctor_get(v___x_1916_, 0);
lean_inc_n(v_a_1917_, 2);
lean_dec_ref(v___x_1916_);
v___f_1918_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__3___lam__0), 2, 1);
lean_closure_set(v___f_1918_, 0, v_a_1917_);
v___x_1919_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(v___f_1918_, v___y_1880_, v___y_1881_);
if (lean_obj_tag(v___x_1919_) == 0)
{
lean_object* v___x_1921_; uint8_t v_isShared_1922_; uint8_t v_isSharedCheck_1926_; 
v_isSharedCheck_1926_ = !lean_is_exclusive(v___x_1919_);
if (v_isSharedCheck_1926_ == 0)
{
lean_object* v_unused_1927_; 
v_unused_1927_ = lean_ctor_get(v___x_1919_, 0);
lean_dec(v_unused_1927_);
v___x_1921_ = v___x_1919_;
v_isShared_1922_ = v_isSharedCheck_1926_;
goto v_resetjp_1920_;
}
else
{
lean_dec(v___x_1919_);
v___x_1921_ = lean_box(0);
v_isShared_1922_ = v_isSharedCheck_1926_;
goto v_resetjp_1920_;
}
v_resetjp_1920_:
{
lean_object* v___x_1924_; 
if (v_isShared_1922_ == 0)
{
lean_ctor_set(v___x_1921_, 0, v_a_1917_);
v___x_1924_ = v___x_1921_;
goto v_reusejp_1923_;
}
else
{
lean_object* v_reuseFailAlloc_1925_; 
v_reuseFailAlloc_1925_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1925_, 0, v_a_1917_);
v___x_1924_ = v_reuseFailAlloc_1925_;
goto v_reusejp_1923_;
}
v_reusejp_1923_:
{
return v___x_1924_;
}
}
}
else
{
lean_object* v_a_1928_; lean_object* v___x_1930_; uint8_t v_isShared_1931_; uint8_t v_isSharedCheck_1935_; 
lean_dec(v_a_1917_);
v_a_1928_ = lean_ctor_get(v___x_1919_, 0);
v_isSharedCheck_1935_ = !lean_is_exclusive(v___x_1919_);
if (v_isSharedCheck_1935_ == 0)
{
v___x_1930_ = v___x_1919_;
v_isShared_1931_ = v_isSharedCheck_1935_;
goto v_resetjp_1929_;
}
else
{
lean_inc(v_a_1928_);
lean_dec(v___x_1919_);
v___x_1930_ = lean_box(0);
v_isShared_1931_ = v_isSharedCheck_1935_;
goto v_resetjp_1929_;
}
v_resetjp_1929_:
{
lean_object* v___x_1933_; 
if (v_isShared_1931_ == 0)
{
v___x_1933_ = v___x_1930_;
goto v_reusejp_1932_;
}
else
{
lean_object* v_reuseFailAlloc_1934_; 
v_reuseFailAlloc_1934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1934_, 0, v_a_1928_);
v___x_1933_ = v_reuseFailAlloc_1934_;
goto v_reusejp_1932_;
}
v_reusejp_1932_:
{
return v___x_1933_;
}
}
}
}
else
{
return v___x_1916_;
}
}
}
}
else
{
lean_object* v_a_1937_; lean_object* v___x_1939_; uint8_t v_isShared_1940_; uint8_t v_isSharedCheck_1944_; 
v_a_1937_ = lean_ctor_get(v___x_1892_, 0);
v_isSharedCheck_1944_ = !lean_is_exclusive(v___x_1892_);
if (v_isSharedCheck_1944_ == 0)
{
v___x_1939_ = v___x_1892_;
v_isShared_1940_ = v_isSharedCheck_1944_;
goto v_resetjp_1938_;
}
else
{
lean_inc(v_a_1937_);
lean_dec(v___x_1892_);
v___x_1939_ = lean_box(0);
v_isShared_1940_ = v_isSharedCheck_1944_;
goto v_resetjp_1938_;
}
v_resetjp_1938_:
{
lean_object* v___x_1942_; 
if (v_isShared_1940_ == 0)
{
v___x_1942_ = v___x_1939_;
goto v_reusejp_1941_;
}
else
{
lean_object* v_reuseFailAlloc_1943_; 
v_reuseFailAlloc_1943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1943_, 0, v_a_1937_);
v___x_1942_ = v_reuseFailAlloc_1943_;
goto v_reusejp_1941_;
}
v_reusejp_1941_:
{
return v___x_1942_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__3___boxed(lean_object* v___y_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_){
_start:
{
lean_object* v_res_1957_; 
v_res_1957_ = l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__3(v___y_1945_, v___y_1946_, v___y_1947_, v___y_1948_, v___y_1949_, v___y_1950_, v___y_1951_, v___y_1952_, v___y_1953_, v___y_1954_, v___y_1955_);
lean_dec(v___y_1955_);
lean_dec_ref(v___y_1954_);
lean_dec(v___y_1953_);
lean_dec_ref(v___y_1952_);
lean_dec(v___y_1951_);
lean_dec_ref(v___y_1950_);
lean_dec(v___y_1949_);
lean_dec_ref(v___y_1948_);
lean_dec(v___y_1947_);
lean_dec(v___y_1946_);
lean_dec_ref(v___y_1945_);
return v_res_1957_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__3(void){
_start:
{
lean_object* v___x_1965_; lean_object* v___x_1966_; 
v___x_1965_ = lean_unsigned_to_nat(1u);
v___x_1966_ = lean_nat_to_int(v___x_1965_);
return v___x_1966_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv(lean_object* v_e_1991_, lean_object* v_inst_1992_, lean_object* v_a_1993_, lean_object* v_a_1994_, lean_object* v_a_1995_, lean_object* v_a_1996_, lean_object* v_a_1997_, lean_object* v_a_1998_, lean_object* v_a_1999_, lean_object* v_a_2000_, lean_object* v_a_2001_, lean_object* v_a_2002_, lean_object* v_a_2003_, lean_object* v_a_2004_){
_start:
{
lean_object* v___x_2009_; 
v___x_2009_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst(v_inst_1992_, v_a_1994_, v_a_1995_, v_a_1996_, v_a_1997_, v_a_1998_, v_a_1999_, v_a_2000_, v_a_2001_, v_a_2002_, v_a_2003_, v_a_2004_);
if (lean_obj_tag(v___x_2009_) == 0)
{
lean_object* v_a_2010_; lean_object* v___x_2012_; uint8_t v_isShared_2013_; uint8_t v_isSharedCheck_2269_; 
v_a_2010_ = lean_ctor_get(v___x_2009_, 0);
v_isSharedCheck_2269_ = !lean_is_exclusive(v___x_2009_);
if (v_isSharedCheck_2269_ == 0)
{
v___x_2012_ = v___x_2009_;
v_isShared_2013_ = v_isSharedCheck_2269_;
goto v_resetjp_2011_;
}
else
{
lean_inc(v_a_2010_);
lean_dec(v___x_2009_);
v___x_2012_ = lean_box(0);
v_isShared_2013_ = v_isSharedCheck_2269_;
goto v_resetjp_2011_;
}
v_resetjp_2011_:
{
uint8_t v___x_2014_; 
v___x_2014_ = lean_unbox(v_a_2010_);
lean_dec(v_a_2010_);
if (v___x_2014_ == 0)
{
lean_object* v___x_2015_; lean_object* v___x_2017_; 
lean_dec_ref(v_a_1993_);
lean_dec_ref(v_e_1991_);
v___x_2015_ = lean_box(0);
if (v_isShared_2013_ == 0)
{
lean_ctor_set(v___x_2012_, 0, v___x_2015_);
v___x_2017_ = v___x_2012_;
goto v_reusejp_2016_;
}
else
{
lean_object* v_reuseFailAlloc_2018_; 
v_reuseFailAlloc_2018_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2018_, 0, v___x_2015_);
v___x_2017_ = v_reuseFailAlloc_2018_;
goto v_reusejp_2016_;
}
v_reusejp_2016_:
{
return v___x_2017_;
}
}
else
{
lean_object* v___x_2019_; 
lean_del_object(v___x_2012_);
v___x_2019_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v_a_1994_, v_a_1995_, v_a_1996_, v_a_1997_, v_a_1998_, v_a_1999_, v_a_2000_, v_a_2001_, v_a_2002_, v_a_2003_, v_a_2004_);
if (lean_obj_tag(v___x_2019_) == 0)
{
lean_object* v_a_2020_; lean_object* v___x_2022_; uint8_t v_isShared_2023_; uint8_t v_isSharedCheck_2260_; 
v_a_2020_ = lean_ctor_get(v___x_2019_, 0);
v_isSharedCheck_2260_ = !lean_is_exclusive(v___x_2019_);
if (v_isSharedCheck_2260_ == 0)
{
v___x_2022_ = v___x_2019_;
v_isShared_2023_ = v_isSharedCheck_2260_;
goto v_resetjp_2021_;
}
else
{
lean_inc(v_a_2020_);
lean_dec(v___x_2019_);
v___x_2022_ = lean_box(0);
v_isShared_2023_ = v_isSharedCheck_2260_;
goto v_resetjp_2021_;
}
v_resetjp_2021_:
{
lean_object* v_fieldInst_x3f_2024_; 
v_fieldInst_x3f_2024_ = lean_ctor_get(v_a_2020_, 6);
lean_inc(v_fieldInst_x3f_2024_);
if (lean_obj_tag(v_fieldInst_x3f_2024_) == 1)
{
lean_object* v_toRing_2025_; lean_object* v_val_2026_; lean_object* v___y_2028_; lean_object* v___y_2029_; lean_object* v___y_2030_; lean_object* v___y_2031_; lean_object* v___y_2032_; lean_object* v___y_2033_; lean_object* v___y_2034_; lean_object* v___y_2035_; lean_object* v___y_2036_; lean_object* v___y_2037_; lean_object* v___x_2047_; 
lean_del_object(v___x_2022_);
v_toRing_2025_ = lean_ctor_get(v_a_2020_, 0);
lean_inc_ref(v_toRing_2025_);
lean_dec(v_a_2020_);
v_val_2026_ = lean_ctor_get(v_fieldInst_x3f_2024_, 0);
lean_inc(v_val_2026_);
lean_dec_ref(v_fieldInst_x3f_2024_);
v___x_2047_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v_a_1994_, v_a_1995_, v_a_1996_, v_a_1997_, v_a_1998_, v_a_1999_, v_a_2000_, v_a_2001_, v_a_2002_, v_a_2003_, v_a_2004_);
if (lean_obj_tag(v___x_2047_) == 0)
{
lean_object* v_a_2048_; lean_object* v___x_2050_; uint8_t v_isShared_2051_; uint8_t v_isSharedCheck_2247_; 
v_a_2048_ = lean_ctor_get(v___x_2047_, 0);
v_isSharedCheck_2247_ = !lean_is_exclusive(v___x_2047_);
if (v_isSharedCheck_2247_ == 0)
{
v___x_2050_ = v___x_2047_;
v_isShared_2051_ = v_isSharedCheck_2247_;
goto v_resetjp_2049_;
}
else
{
lean_inc(v_a_2048_);
lean_dec(v___x_2047_);
v___x_2050_ = lean_box(0);
v_isShared_2051_ = v_isSharedCheck_2247_;
goto v_resetjp_2049_;
}
v_resetjp_2049_:
{
lean_object* v_invSet_2052_; uint8_t v___x_2053_; 
v_invSet_2052_ = lean_ctor_get(v_a_2048_, 13);
lean_inc_ref(v_invSet_2052_);
lean_dec(v_a_2048_);
v___x_2053_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1___redArg(v_invSet_2052_, v_a_1993_);
lean_dec_ref(v_invSet_2052_);
if (v___x_2053_ == 0)
{
lean_object* v___f_2054_; lean_object* v___x_2055_; 
lean_del_object(v___x_2050_);
lean_inc_ref(v_a_1993_);
v___f_2054_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___lam__0), 2, 1);
lean_closure_set(v___f_2054_, 0, v_a_1993_);
v___x_2055_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(v___f_2054_, v_a_1994_, v_a_1995_);
if (lean_obj_tag(v___x_2055_) == 0)
{
lean_object* v___x_2056_; 
lean_dec_ref(v___x_2055_);
lean_inc_ref(v_a_1993_);
v___x_2056_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f(v_a_1993_, v_a_1994_, v_a_1995_, v_a_1996_, v_a_1997_, v_a_1998_, v_a_1999_, v_a_2000_, v_a_2001_, v_a_2002_, v_a_2003_, v_a_2004_);
if (lean_obj_tag(v___x_2056_) == 0)
{
lean_object* v_a_2057_; 
v_a_2057_ = lean_ctor_get(v___x_2056_, 0);
lean_inc(v_a_2057_);
lean_dec_ref(v___x_2056_);
if (lean_obj_tag(v_a_2057_) == 1)
{
lean_object* v_val_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; uint8_t v___x_2061_; 
v_val_2058_ = lean_ctor_get(v_a_2057_, 0);
lean_inc(v_val_2058_);
lean_dec_ref(v_a_2057_);
v___x_2059_ = lean_unsigned_to_nat(0u);
v___x_2060_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__4___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__4___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__4___closed__1);
v___x_2061_ = lean_int_dec_eq(v_val_2058_, v___x_2060_);
if (v___x_2061_ == 0)
{
lean_object* v___x_2062_; 
v___x_2062_ = l_Lean_Meta_Grind_Arith_CommRing_hasChar(v_a_1994_, v_a_1995_, v_a_1996_, v_a_1997_, v_a_1998_, v_a_1999_, v_a_2000_, v_a_2001_, v_a_2002_, v_a_2003_, v_a_2004_);
if (lean_obj_tag(v___x_2062_) == 0)
{
lean_object* v_a_2063_; uint8_t v___x_2064_; 
v_a_2063_ = lean_ctor_get(v___x_2062_, 0);
lean_inc(v_a_2063_);
lean_dec_ref(v___x_2062_);
v___x_2064_ = lean_unbox(v_a_2063_);
lean_dec(v_a_2063_);
if (v___x_2064_ == 0)
{
lean_dec(v_val_2058_);
lean_dec_ref(v_e_1991_);
v___y_2028_ = v_a_1995_;
v___y_2029_ = v_a_1996_;
v___y_2030_ = v_a_1997_;
v___y_2031_ = v_a_1998_;
v___y_2032_ = v_a_1999_;
v___y_2033_ = v_a_2000_;
v___y_2034_ = v_a_2001_;
v___y_2035_ = v_a_2002_;
v___y_2036_ = v_a_2003_;
v___y_2037_ = v_a_2004_;
goto v___jp_2027_;
}
else
{
lean_object* v___x_2065_; 
v___x_2065_ = l_Lean_Meta_Grind_Arith_CommRing_getCharInst(v_a_1994_, v_a_1995_, v_a_1996_, v_a_1997_, v_a_1998_, v_a_1999_, v_a_2000_, v_a_2001_, v_a_2002_, v_a_2003_, v_a_2004_);
if (lean_obj_tag(v___x_2065_) == 0)
{
lean_object* v_a_2066_; lean_object* v_fst_2067_; lean_object* v_snd_2068_; lean_object* v___x_2070_; uint8_t v_isShared_2071_; uint8_t v_isSharedCheck_2201_; 
v_a_2066_ = lean_ctor_get(v___x_2065_, 0);
lean_inc(v_a_2066_);
lean_dec_ref(v___x_2065_);
v_fst_2067_ = lean_ctor_get(v_a_2066_, 0);
v_snd_2068_ = lean_ctor_get(v_a_2066_, 1);
v_isSharedCheck_2201_ = !lean_is_exclusive(v_a_2066_);
if (v_isSharedCheck_2201_ == 0)
{
v___x_2070_ = v_a_2066_;
v_isShared_2071_ = v_isSharedCheck_2201_;
goto v_resetjp_2069_;
}
else
{
lean_inc(v_snd_2068_);
lean_inc(v_fst_2067_);
lean_dec(v_a_2066_);
v___x_2070_ = lean_box(0);
v_isShared_2071_ = v_isSharedCheck_2201_;
goto v_resetjp_2069_;
}
v_resetjp_2069_:
{
uint8_t v___x_2072_; 
v___x_2072_ = lean_nat_dec_eq(v_snd_2068_, v___x_2059_);
if (v___x_2072_ == 0)
{
lean_object* v___x_2073_; lean_object* v___x_2074_; uint8_t v___x_2075_; 
lean_inc(v_snd_2068_);
v___x_2073_ = lean_nat_to_int(v_snd_2068_);
v___x_2074_ = lean_int_emod(v_val_2058_, v___x_2073_);
lean_dec(v___x_2073_);
v___x_2075_ = lean_int_dec_eq(v___x_2074_, v___x_2060_);
lean_dec(v___x_2074_);
if (v___x_2075_ == 0)
{
lean_object* v___x_2076_; 
v___x_2076_ = l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__3(v_a_1994_, v_a_1995_, v_a_1996_, v_a_1997_, v_a_1998_, v_a_1999_, v_a_2000_, v_a_2001_, v_a_2002_, v_a_2003_, v_a_2004_);
if (lean_obj_tag(v___x_2076_) == 0)
{
lean_object* v_a_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; 
v_a_2077_ = lean_ctor_get(v___x_2076_, 0);
lean_inc(v_a_2077_);
lean_dec_ref(v___x_2076_);
v___x_2078_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__3, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__3);
v___x_2079_ = l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__4(v___x_2078_, v_a_1994_, v_a_1995_, v_a_1996_, v_a_1997_, v_a_1998_, v_a_1999_, v_a_2000_, v_a_2001_, v_a_2002_, v_a_2003_, v_a_2004_);
if (lean_obj_tag(v___x_2079_) == 0)
{
lean_object* v_a_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; 
v_a_2080_ = lean_ctor_get(v___x_2079_, 0);
lean_inc(v_a_2080_);
lean_dec_ref(v___x_2079_);
v___x_2081_ = l_Lean_mkAppB(v_a_2077_, v_a_1993_, v_e_1991_);
v___x_2082_ = l_Lean_Meta_mkEq(v___x_2081_, v_a_2080_, v_a_2001_, v_a_2002_, v_a_2003_, v_a_2004_);
if (lean_obj_tag(v___x_2082_) == 0)
{
lean_object* v_a_2083_; lean_object* v_type_2084_; lean_object* v_u_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2089_; 
v_a_2083_ = lean_ctor_get(v___x_2082_, 0);
lean_inc(v_a_2083_);
lean_dec_ref(v___x_2082_);
v_type_2084_ = lean_ctor_get(v_toRing_2025_, 1);
lean_inc_ref(v_type_2084_);
v_u_2085_ = lean_ctor_get(v_toRing_2025_, 2);
lean_inc(v_u_2085_);
lean_dec_ref(v_toRing_2025_);
v___x_2086_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__5));
v___x_2087_ = lean_box(0);
if (v_isShared_2071_ == 0)
{
lean_ctor_set_tag(v___x_2070_, 1);
lean_ctor_set(v___x_2070_, 1, v___x_2087_);
lean_ctor_set(v___x_2070_, 0, v_u_2085_);
v___x_2089_ = v___x_2070_;
goto v_reusejp_2088_;
}
else
{
lean_object* v_reuseFailAlloc_2097_; 
v_reuseFailAlloc_2097_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2097_, 0, v_u_2085_);
lean_ctor_set(v_reuseFailAlloc_2097_, 1, v___x_2087_);
v___x_2089_ = v_reuseFailAlloc_2097_;
goto v_reusejp_2088_;
}
v_reusejp_2088_:
{
lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; 
v___x_2090_ = l_Lean_mkConst(v___x_2086_, v___x_2089_);
v___x_2091_ = l_Lean_mkNatLit(v_snd_2068_);
v___x_2092_ = l_Lean_mkIntLit(v_val_2058_);
lean_dec(v_val_2058_);
v___x_2093_ = l_Lean_eagerReflBoolTrue;
v___x_2094_ = l_Lean_mkApp6(v___x_2090_, v_type_2084_, v___x_2091_, v_val_2026_, v_fst_2067_, v___x_2092_, v___x_2093_);
v___x_2095_ = l_Lean_Meta_mkExpectedPropHint(v___x_2094_, v_a_2083_);
v___x_2096_ = l_Lean_Meta_Grind_pushNewFact(v___x_2095_, v___x_2059_, v_a_1995_, v_a_1996_, v_a_1997_, v_a_1998_, v_a_1999_, v_a_2000_, v_a_2001_, v_a_2002_, v_a_2003_, v_a_2004_);
if (lean_obj_tag(v___x_2096_) == 0)
{
lean_dec_ref(v___x_2096_);
goto v___jp_2006_;
}
else
{
return v___x_2096_;
}
}
}
else
{
lean_object* v_a_2098_; lean_object* v___x_2100_; uint8_t v_isShared_2101_; uint8_t v_isSharedCheck_2105_; 
lean_del_object(v___x_2070_);
lean_dec(v_snd_2068_);
lean_dec(v_fst_2067_);
lean_dec(v_val_2058_);
lean_dec(v_val_2026_);
lean_dec_ref(v_toRing_2025_);
v_a_2098_ = lean_ctor_get(v___x_2082_, 0);
v_isSharedCheck_2105_ = !lean_is_exclusive(v___x_2082_);
if (v_isSharedCheck_2105_ == 0)
{
v___x_2100_ = v___x_2082_;
v_isShared_2101_ = v_isSharedCheck_2105_;
goto v_resetjp_2099_;
}
else
{
lean_inc(v_a_2098_);
lean_dec(v___x_2082_);
v___x_2100_ = lean_box(0);
v_isShared_2101_ = v_isSharedCheck_2105_;
goto v_resetjp_2099_;
}
v_resetjp_2099_:
{
lean_object* v___x_2103_; 
if (v_isShared_2101_ == 0)
{
v___x_2103_ = v___x_2100_;
goto v_reusejp_2102_;
}
else
{
lean_object* v_reuseFailAlloc_2104_; 
v_reuseFailAlloc_2104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2104_, 0, v_a_2098_);
v___x_2103_ = v_reuseFailAlloc_2104_;
goto v_reusejp_2102_;
}
v_reusejp_2102_:
{
return v___x_2103_;
}
}
}
}
else
{
lean_object* v_a_2106_; lean_object* v___x_2108_; uint8_t v_isShared_2109_; uint8_t v_isSharedCheck_2113_; 
lean_dec(v_a_2077_);
lean_del_object(v___x_2070_);
lean_dec(v_snd_2068_);
lean_dec(v_fst_2067_);
lean_dec(v_val_2058_);
lean_dec(v_val_2026_);
lean_dec_ref(v_toRing_2025_);
lean_dec_ref(v_a_1993_);
lean_dec_ref(v_e_1991_);
v_a_2106_ = lean_ctor_get(v___x_2079_, 0);
v_isSharedCheck_2113_ = !lean_is_exclusive(v___x_2079_);
if (v_isSharedCheck_2113_ == 0)
{
v___x_2108_ = v___x_2079_;
v_isShared_2109_ = v_isSharedCheck_2113_;
goto v_resetjp_2107_;
}
else
{
lean_inc(v_a_2106_);
lean_dec(v___x_2079_);
v___x_2108_ = lean_box(0);
v_isShared_2109_ = v_isSharedCheck_2113_;
goto v_resetjp_2107_;
}
v_resetjp_2107_:
{
lean_object* v___x_2111_; 
if (v_isShared_2109_ == 0)
{
v___x_2111_ = v___x_2108_;
goto v_reusejp_2110_;
}
else
{
lean_object* v_reuseFailAlloc_2112_; 
v_reuseFailAlloc_2112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2112_, 0, v_a_2106_);
v___x_2111_ = v_reuseFailAlloc_2112_;
goto v_reusejp_2110_;
}
v_reusejp_2110_:
{
return v___x_2111_;
}
}
}
}
else
{
lean_object* v_a_2114_; lean_object* v___x_2116_; uint8_t v_isShared_2117_; uint8_t v_isSharedCheck_2121_; 
lean_del_object(v___x_2070_);
lean_dec(v_snd_2068_);
lean_dec(v_fst_2067_);
lean_dec(v_val_2058_);
lean_dec(v_val_2026_);
lean_dec_ref(v_toRing_2025_);
lean_dec_ref(v_a_1993_);
lean_dec_ref(v_e_1991_);
v_a_2114_ = lean_ctor_get(v___x_2076_, 0);
v_isSharedCheck_2121_ = !lean_is_exclusive(v___x_2076_);
if (v_isSharedCheck_2121_ == 0)
{
v___x_2116_ = v___x_2076_;
v_isShared_2117_ = v_isSharedCheck_2121_;
goto v_resetjp_2115_;
}
else
{
lean_inc(v_a_2114_);
lean_dec(v___x_2076_);
v___x_2116_ = lean_box(0);
v_isShared_2117_ = v_isSharedCheck_2121_;
goto v_resetjp_2115_;
}
v_resetjp_2115_:
{
lean_object* v___x_2119_; 
if (v_isShared_2117_ == 0)
{
v___x_2119_ = v___x_2116_;
goto v_reusejp_2118_;
}
else
{
lean_object* v_reuseFailAlloc_2120_; 
v_reuseFailAlloc_2120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2120_, 0, v_a_2114_);
v___x_2119_ = v_reuseFailAlloc_2120_;
goto v_reusejp_2118_;
}
v_reusejp_2118_:
{
return v___x_2119_;
}
}
}
}
else
{
lean_object* v___x_2122_; 
lean_dec_ref(v_a_1993_);
v___x_2122_ = l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__4(v___x_2060_, v_a_1994_, v_a_1995_, v_a_1996_, v_a_1997_, v_a_1998_, v_a_1999_, v_a_2000_, v_a_2001_, v_a_2002_, v_a_2003_, v_a_2004_);
if (lean_obj_tag(v___x_2122_) == 0)
{
lean_object* v_a_2123_; lean_object* v___x_2124_; 
v_a_2123_ = lean_ctor_get(v___x_2122_, 0);
lean_inc(v_a_2123_);
lean_dec_ref(v___x_2122_);
v___x_2124_ = l_Lean_Meta_mkEq(v_e_1991_, v_a_2123_, v_a_2001_, v_a_2002_, v_a_2003_, v_a_2004_);
if (lean_obj_tag(v___x_2124_) == 0)
{
lean_object* v_a_2125_; lean_object* v_type_2126_; lean_object* v_u_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2131_; 
v_a_2125_ = lean_ctor_get(v___x_2124_, 0);
lean_inc(v_a_2125_);
lean_dec_ref(v___x_2124_);
v_type_2126_ = lean_ctor_get(v_toRing_2025_, 1);
lean_inc_ref(v_type_2126_);
v_u_2127_ = lean_ctor_get(v_toRing_2025_, 2);
lean_inc(v_u_2127_);
lean_dec_ref(v_toRing_2025_);
v___x_2128_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__7));
v___x_2129_ = lean_box(0);
if (v_isShared_2071_ == 0)
{
lean_ctor_set_tag(v___x_2070_, 1);
lean_ctor_set(v___x_2070_, 1, v___x_2129_);
lean_ctor_set(v___x_2070_, 0, v_u_2127_);
v___x_2131_ = v___x_2070_;
goto v_reusejp_2130_;
}
else
{
lean_object* v_reuseFailAlloc_2139_; 
v_reuseFailAlloc_2139_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2139_, 0, v_u_2127_);
lean_ctor_set(v_reuseFailAlloc_2139_, 1, v___x_2129_);
v___x_2131_ = v_reuseFailAlloc_2139_;
goto v_reusejp_2130_;
}
v_reusejp_2130_:
{
lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; 
v___x_2132_ = l_Lean_mkConst(v___x_2128_, v___x_2131_);
v___x_2133_ = l_Lean_mkNatLit(v_snd_2068_);
v___x_2134_ = l_Lean_mkIntLit(v_val_2058_);
lean_dec(v_val_2058_);
v___x_2135_ = l_Lean_eagerReflBoolTrue;
v___x_2136_ = l_Lean_mkApp6(v___x_2132_, v_type_2126_, v___x_2133_, v_val_2026_, v_fst_2067_, v___x_2134_, v___x_2135_);
v___x_2137_ = l_Lean_Meta_mkExpectedPropHint(v___x_2136_, v_a_2125_);
v___x_2138_ = l_Lean_Meta_Grind_pushNewFact(v___x_2137_, v___x_2059_, v_a_1995_, v_a_1996_, v_a_1997_, v_a_1998_, v_a_1999_, v_a_2000_, v_a_2001_, v_a_2002_, v_a_2003_, v_a_2004_);
if (lean_obj_tag(v___x_2138_) == 0)
{
lean_dec_ref(v___x_2138_);
goto v___jp_2006_;
}
else
{
return v___x_2138_;
}
}
}
else
{
lean_object* v_a_2140_; lean_object* v___x_2142_; uint8_t v_isShared_2143_; uint8_t v_isSharedCheck_2147_; 
lean_del_object(v___x_2070_);
lean_dec(v_snd_2068_);
lean_dec(v_fst_2067_);
lean_dec(v_val_2058_);
lean_dec(v_val_2026_);
lean_dec_ref(v_toRing_2025_);
v_a_2140_ = lean_ctor_get(v___x_2124_, 0);
v_isSharedCheck_2147_ = !lean_is_exclusive(v___x_2124_);
if (v_isSharedCheck_2147_ == 0)
{
v___x_2142_ = v___x_2124_;
v_isShared_2143_ = v_isSharedCheck_2147_;
goto v_resetjp_2141_;
}
else
{
lean_inc(v_a_2140_);
lean_dec(v___x_2124_);
v___x_2142_ = lean_box(0);
v_isShared_2143_ = v_isSharedCheck_2147_;
goto v_resetjp_2141_;
}
v_resetjp_2141_:
{
lean_object* v___x_2145_; 
if (v_isShared_2143_ == 0)
{
v___x_2145_ = v___x_2142_;
goto v_reusejp_2144_;
}
else
{
lean_object* v_reuseFailAlloc_2146_; 
v_reuseFailAlloc_2146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2146_, 0, v_a_2140_);
v___x_2145_ = v_reuseFailAlloc_2146_;
goto v_reusejp_2144_;
}
v_reusejp_2144_:
{
return v___x_2145_;
}
}
}
}
else
{
lean_object* v_a_2148_; lean_object* v___x_2150_; uint8_t v_isShared_2151_; uint8_t v_isSharedCheck_2155_; 
lean_del_object(v___x_2070_);
lean_dec(v_snd_2068_);
lean_dec(v_fst_2067_);
lean_dec(v_val_2058_);
lean_dec(v_val_2026_);
lean_dec_ref(v_toRing_2025_);
lean_dec_ref(v_e_1991_);
v_a_2148_ = lean_ctor_get(v___x_2122_, 0);
v_isSharedCheck_2155_ = !lean_is_exclusive(v___x_2122_);
if (v_isSharedCheck_2155_ == 0)
{
v___x_2150_ = v___x_2122_;
v_isShared_2151_ = v_isSharedCheck_2155_;
goto v_resetjp_2149_;
}
else
{
lean_inc(v_a_2148_);
lean_dec(v___x_2122_);
v___x_2150_ = lean_box(0);
v_isShared_2151_ = v_isSharedCheck_2155_;
goto v_resetjp_2149_;
}
v_resetjp_2149_:
{
lean_object* v___x_2153_; 
if (v_isShared_2151_ == 0)
{
v___x_2153_ = v___x_2150_;
goto v_reusejp_2152_;
}
else
{
lean_object* v_reuseFailAlloc_2154_; 
v_reuseFailAlloc_2154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2154_, 0, v_a_2148_);
v___x_2153_ = v_reuseFailAlloc_2154_;
goto v_reusejp_2152_;
}
v_reusejp_2152_:
{
return v___x_2153_;
}
}
}
}
}
else
{
lean_object* v___x_2156_; 
lean_dec(v_snd_2068_);
v___x_2156_ = l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__3(v_a_1994_, v_a_1995_, v_a_1996_, v_a_1997_, v_a_1998_, v_a_1999_, v_a_2000_, v_a_2001_, v_a_2002_, v_a_2003_, v_a_2004_);
if (lean_obj_tag(v___x_2156_) == 0)
{
lean_object* v_a_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; 
v_a_2157_ = lean_ctor_get(v___x_2156_, 0);
lean_inc(v_a_2157_);
lean_dec_ref(v___x_2156_);
v___x_2158_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__3, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__3);
v___x_2159_ = l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__4(v___x_2158_, v_a_1994_, v_a_1995_, v_a_1996_, v_a_1997_, v_a_1998_, v_a_1999_, v_a_2000_, v_a_2001_, v_a_2002_, v_a_2003_, v_a_2004_);
if (lean_obj_tag(v___x_2159_) == 0)
{
lean_object* v_a_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; 
v_a_2160_ = lean_ctor_get(v___x_2159_, 0);
lean_inc(v_a_2160_);
lean_dec_ref(v___x_2159_);
v___x_2161_ = l_Lean_mkAppB(v_a_2157_, v_a_1993_, v_e_1991_);
v___x_2162_ = l_Lean_Meta_mkEq(v___x_2161_, v_a_2160_, v_a_2001_, v_a_2002_, v_a_2003_, v_a_2004_);
if (lean_obj_tag(v___x_2162_) == 0)
{
lean_object* v_a_2163_; lean_object* v_type_2164_; lean_object* v_u_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2169_; 
v_a_2163_ = lean_ctor_get(v___x_2162_, 0);
lean_inc(v_a_2163_);
lean_dec_ref(v___x_2162_);
v_type_2164_ = lean_ctor_get(v_toRing_2025_, 1);
lean_inc_ref(v_type_2164_);
v_u_2165_ = lean_ctor_get(v_toRing_2025_, 2);
lean_inc(v_u_2165_);
lean_dec_ref(v_toRing_2025_);
v___x_2166_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__9));
v___x_2167_ = lean_box(0);
if (v_isShared_2071_ == 0)
{
lean_ctor_set_tag(v___x_2070_, 1);
lean_ctor_set(v___x_2070_, 1, v___x_2167_);
lean_ctor_set(v___x_2070_, 0, v_u_2165_);
v___x_2169_ = v___x_2070_;
goto v_reusejp_2168_;
}
else
{
lean_object* v_reuseFailAlloc_2176_; 
v_reuseFailAlloc_2176_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2176_, 0, v_u_2165_);
lean_ctor_set(v_reuseFailAlloc_2176_, 1, v___x_2167_);
v___x_2169_ = v_reuseFailAlloc_2176_;
goto v_reusejp_2168_;
}
v_reusejp_2168_:
{
lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; 
v___x_2170_ = l_Lean_mkConst(v___x_2166_, v___x_2169_);
v___x_2171_ = l_Lean_mkIntLit(v_val_2058_);
lean_dec(v_val_2058_);
v___x_2172_ = l_Lean_eagerReflBoolTrue;
v___x_2173_ = l_Lean_mkApp5(v___x_2170_, v_type_2164_, v_val_2026_, v_fst_2067_, v___x_2171_, v___x_2172_);
v___x_2174_ = l_Lean_Meta_mkExpectedPropHint(v___x_2173_, v_a_2163_);
v___x_2175_ = l_Lean_Meta_Grind_pushNewFact(v___x_2174_, v___x_2059_, v_a_1995_, v_a_1996_, v_a_1997_, v_a_1998_, v_a_1999_, v_a_2000_, v_a_2001_, v_a_2002_, v_a_2003_, v_a_2004_);
if (lean_obj_tag(v___x_2175_) == 0)
{
lean_dec_ref(v___x_2175_);
goto v___jp_2006_;
}
else
{
return v___x_2175_;
}
}
}
else
{
lean_object* v_a_2177_; lean_object* v___x_2179_; uint8_t v_isShared_2180_; uint8_t v_isSharedCheck_2184_; 
lean_del_object(v___x_2070_);
lean_dec(v_fst_2067_);
lean_dec(v_val_2058_);
lean_dec(v_val_2026_);
lean_dec_ref(v_toRing_2025_);
v_a_2177_ = lean_ctor_get(v___x_2162_, 0);
v_isSharedCheck_2184_ = !lean_is_exclusive(v___x_2162_);
if (v_isSharedCheck_2184_ == 0)
{
v___x_2179_ = v___x_2162_;
v_isShared_2180_ = v_isSharedCheck_2184_;
goto v_resetjp_2178_;
}
else
{
lean_inc(v_a_2177_);
lean_dec(v___x_2162_);
v___x_2179_ = lean_box(0);
v_isShared_2180_ = v_isSharedCheck_2184_;
goto v_resetjp_2178_;
}
v_resetjp_2178_:
{
lean_object* v___x_2182_; 
if (v_isShared_2180_ == 0)
{
v___x_2182_ = v___x_2179_;
goto v_reusejp_2181_;
}
else
{
lean_object* v_reuseFailAlloc_2183_; 
v_reuseFailAlloc_2183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2183_, 0, v_a_2177_);
v___x_2182_ = v_reuseFailAlloc_2183_;
goto v_reusejp_2181_;
}
v_reusejp_2181_:
{
return v___x_2182_;
}
}
}
}
else
{
lean_object* v_a_2185_; lean_object* v___x_2187_; uint8_t v_isShared_2188_; uint8_t v_isSharedCheck_2192_; 
lean_dec(v_a_2157_);
lean_del_object(v___x_2070_);
lean_dec(v_fst_2067_);
lean_dec(v_val_2058_);
lean_dec(v_val_2026_);
lean_dec_ref(v_toRing_2025_);
lean_dec_ref(v_a_1993_);
lean_dec_ref(v_e_1991_);
v_a_2185_ = lean_ctor_get(v___x_2159_, 0);
v_isSharedCheck_2192_ = !lean_is_exclusive(v___x_2159_);
if (v_isSharedCheck_2192_ == 0)
{
v___x_2187_ = v___x_2159_;
v_isShared_2188_ = v_isSharedCheck_2192_;
goto v_resetjp_2186_;
}
else
{
lean_inc(v_a_2185_);
lean_dec(v___x_2159_);
v___x_2187_ = lean_box(0);
v_isShared_2188_ = v_isSharedCheck_2192_;
goto v_resetjp_2186_;
}
v_resetjp_2186_:
{
lean_object* v___x_2190_; 
if (v_isShared_2188_ == 0)
{
v___x_2190_ = v___x_2187_;
goto v_reusejp_2189_;
}
else
{
lean_object* v_reuseFailAlloc_2191_; 
v_reuseFailAlloc_2191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2191_, 0, v_a_2185_);
v___x_2190_ = v_reuseFailAlloc_2191_;
goto v_reusejp_2189_;
}
v_reusejp_2189_:
{
return v___x_2190_;
}
}
}
}
else
{
lean_object* v_a_2193_; lean_object* v___x_2195_; uint8_t v_isShared_2196_; uint8_t v_isSharedCheck_2200_; 
lean_del_object(v___x_2070_);
lean_dec(v_fst_2067_);
lean_dec(v_val_2058_);
lean_dec(v_val_2026_);
lean_dec_ref(v_toRing_2025_);
lean_dec_ref(v_a_1993_);
lean_dec_ref(v_e_1991_);
v_a_2193_ = lean_ctor_get(v___x_2156_, 0);
v_isSharedCheck_2200_ = !lean_is_exclusive(v___x_2156_);
if (v_isSharedCheck_2200_ == 0)
{
v___x_2195_ = v___x_2156_;
v_isShared_2196_ = v_isSharedCheck_2200_;
goto v_resetjp_2194_;
}
else
{
lean_inc(v_a_2193_);
lean_dec(v___x_2156_);
v___x_2195_ = lean_box(0);
v_isShared_2196_ = v_isSharedCheck_2200_;
goto v_resetjp_2194_;
}
v_resetjp_2194_:
{
lean_object* v___x_2198_; 
if (v_isShared_2196_ == 0)
{
v___x_2198_ = v___x_2195_;
goto v_reusejp_2197_;
}
else
{
lean_object* v_reuseFailAlloc_2199_; 
v_reuseFailAlloc_2199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2199_, 0, v_a_2193_);
v___x_2198_ = v_reuseFailAlloc_2199_;
goto v_reusejp_2197_;
}
v_reusejp_2197_:
{
return v___x_2198_;
}
}
}
}
}
}
else
{
lean_object* v_a_2202_; lean_object* v___x_2204_; uint8_t v_isShared_2205_; uint8_t v_isSharedCheck_2209_; 
lean_dec(v_val_2058_);
lean_dec(v_val_2026_);
lean_dec_ref(v_toRing_2025_);
lean_dec_ref(v_a_1993_);
lean_dec_ref(v_e_1991_);
v_a_2202_ = lean_ctor_get(v___x_2065_, 0);
v_isSharedCheck_2209_ = !lean_is_exclusive(v___x_2065_);
if (v_isSharedCheck_2209_ == 0)
{
v___x_2204_ = v___x_2065_;
v_isShared_2205_ = v_isSharedCheck_2209_;
goto v_resetjp_2203_;
}
else
{
lean_inc(v_a_2202_);
lean_dec(v___x_2065_);
v___x_2204_ = lean_box(0);
v_isShared_2205_ = v_isSharedCheck_2209_;
goto v_resetjp_2203_;
}
v_resetjp_2203_:
{
lean_object* v___x_2207_; 
if (v_isShared_2205_ == 0)
{
v___x_2207_ = v___x_2204_;
goto v_reusejp_2206_;
}
else
{
lean_object* v_reuseFailAlloc_2208_; 
v_reuseFailAlloc_2208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2208_, 0, v_a_2202_);
v___x_2207_ = v_reuseFailAlloc_2208_;
goto v_reusejp_2206_;
}
v_reusejp_2206_:
{
return v___x_2207_;
}
}
}
}
}
else
{
lean_object* v_a_2210_; lean_object* v___x_2212_; uint8_t v_isShared_2213_; uint8_t v_isSharedCheck_2217_; 
lean_dec(v_val_2058_);
lean_dec(v_val_2026_);
lean_dec_ref(v_toRing_2025_);
lean_dec_ref(v_a_1993_);
lean_dec_ref(v_e_1991_);
v_a_2210_ = lean_ctor_get(v___x_2062_, 0);
v_isSharedCheck_2217_ = !lean_is_exclusive(v___x_2062_);
if (v_isSharedCheck_2217_ == 0)
{
v___x_2212_ = v___x_2062_;
v_isShared_2213_ = v_isSharedCheck_2217_;
goto v_resetjp_2211_;
}
else
{
lean_inc(v_a_2210_);
lean_dec(v___x_2062_);
v___x_2212_ = lean_box(0);
v_isShared_2213_ = v_isSharedCheck_2217_;
goto v_resetjp_2211_;
}
v_resetjp_2211_:
{
lean_object* v___x_2215_; 
if (v_isShared_2213_ == 0)
{
v___x_2215_ = v___x_2212_;
goto v_reusejp_2214_;
}
else
{
lean_object* v_reuseFailAlloc_2216_; 
v_reuseFailAlloc_2216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2216_, 0, v_a_2210_);
v___x_2215_ = v_reuseFailAlloc_2216_;
goto v_reusejp_2214_;
}
v_reusejp_2214_:
{
return v___x_2215_;
}
}
}
}
else
{
lean_object* v_type_2218_; lean_object* v_u_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; 
lean_dec(v_val_2058_);
v_type_2218_ = lean_ctor_get(v_toRing_2025_, 1);
lean_inc_ref(v_type_2218_);
v_u_2219_ = lean_ctor_get(v_toRing_2025_, 2);
lean_inc(v_u_2219_);
lean_dec_ref(v_toRing_2025_);
v___x_2220_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__11));
v___x_2221_ = lean_box(0);
v___x_2222_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2222_, 0, v_u_2219_);
lean_ctor_set(v___x_2222_, 1, v___x_2221_);
v___x_2223_ = l_Lean_mkConst(v___x_2220_, v___x_2222_);
v___x_2224_ = l_Lean_mkAppB(v___x_2223_, v_type_2218_, v_val_2026_);
v___x_2225_ = l_Lean_Meta_Grind_pushEqCore___redArg(v_e_1991_, v_a_1993_, v___x_2224_, v___x_2053_, v_a_1995_, v_a_1997_, v_a_2001_, v_a_2002_, v_a_2003_, v_a_2004_);
if (lean_obj_tag(v___x_2225_) == 0)
{
lean_object* v___x_2227_; uint8_t v_isShared_2228_; uint8_t v_isSharedCheck_2233_; 
v_isSharedCheck_2233_ = !lean_is_exclusive(v___x_2225_);
if (v_isSharedCheck_2233_ == 0)
{
lean_object* v_unused_2234_; 
v_unused_2234_ = lean_ctor_get(v___x_2225_, 0);
lean_dec(v_unused_2234_);
v___x_2227_ = v___x_2225_;
v_isShared_2228_ = v_isSharedCheck_2233_;
goto v_resetjp_2226_;
}
else
{
lean_dec(v___x_2225_);
v___x_2227_ = lean_box(0);
v_isShared_2228_ = v_isSharedCheck_2233_;
goto v_resetjp_2226_;
}
v_resetjp_2226_:
{
lean_object* v___x_2229_; lean_object* v___x_2231_; 
v___x_2229_ = lean_box(0);
if (v_isShared_2228_ == 0)
{
lean_ctor_set(v___x_2227_, 0, v___x_2229_);
v___x_2231_ = v___x_2227_;
goto v_reusejp_2230_;
}
else
{
lean_object* v_reuseFailAlloc_2232_; 
v_reuseFailAlloc_2232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2232_, 0, v___x_2229_);
v___x_2231_ = v_reuseFailAlloc_2232_;
goto v_reusejp_2230_;
}
v_reusejp_2230_:
{
return v___x_2231_;
}
}
}
else
{
return v___x_2225_;
}
}
}
else
{
lean_dec(v_a_2057_);
lean_dec_ref(v_e_1991_);
v___y_2028_ = v_a_1995_;
v___y_2029_ = v_a_1996_;
v___y_2030_ = v_a_1997_;
v___y_2031_ = v_a_1998_;
v___y_2032_ = v_a_1999_;
v___y_2033_ = v_a_2000_;
v___y_2034_ = v_a_2001_;
v___y_2035_ = v_a_2002_;
v___y_2036_ = v_a_2003_;
v___y_2037_ = v_a_2004_;
goto v___jp_2027_;
}
}
else
{
lean_object* v_a_2235_; lean_object* v___x_2237_; uint8_t v_isShared_2238_; uint8_t v_isSharedCheck_2242_; 
lean_dec(v_val_2026_);
lean_dec_ref(v_toRing_2025_);
lean_dec_ref(v_a_1993_);
lean_dec_ref(v_e_1991_);
v_a_2235_ = lean_ctor_get(v___x_2056_, 0);
v_isSharedCheck_2242_ = !lean_is_exclusive(v___x_2056_);
if (v_isSharedCheck_2242_ == 0)
{
v___x_2237_ = v___x_2056_;
v_isShared_2238_ = v_isSharedCheck_2242_;
goto v_resetjp_2236_;
}
else
{
lean_inc(v_a_2235_);
lean_dec(v___x_2056_);
v___x_2237_ = lean_box(0);
v_isShared_2238_ = v_isSharedCheck_2242_;
goto v_resetjp_2236_;
}
v_resetjp_2236_:
{
lean_object* v___x_2240_; 
if (v_isShared_2238_ == 0)
{
v___x_2240_ = v___x_2237_;
goto v_reusejp_2239_;
}
else
{
lean_object* v_reuseFailAlloc_2241_; 
v_reuseFailAlloc_2241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2241_, 0, v_a_2235_);
v___x_2240_ = v_reuseFailAlloc_2241_;
goto v_reusejp_2239_;
}
v_reusejp_2239_:
{
return v___x_2240_;
}
}
}
}
else
{
lean_dec(v_val_2026_);
lean_dec_ref(v_toRing_2025_);
lean_dec_ref(v_a_1993_);
lean_dec_ref(v_e_1991_);
return v___x_2055_;
}
}
else
{
lean_object* v___x_2243_; lean_object* v___x_2245_; 
lean_dec(v_val_2026_);
lean_dec_ref(v_toRing_2025_);
lean_dec_ref(v_a_1993_);
lean_dec_ref(v_e_1991_);
v___x_2243_ = lean_box(0);
if (v_isShared_2051_ == 0)
{
lean_ctor_set(v___x_2050_, 0, v___x_2243_);
v___x_2245_ = v___x_2050_;
goto v_reusejp_2244_;
}
else
{
lean_object* v_reuseFailAlloc_2246_; 
v_reuseFailAlloc_2246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2246_, 0, v___x_2243_);
v___x_2245_ = v_reuseFailAlloc_2246_;
goto v_reusejp_2244_;
}
v_reusejp_2244_:
{
return v___x_2245_;
}
}
}
}
else
{
lean_object* v_a_2248_; lean_object* v___x_2250_; uint8_t v_isShared_2251_; uint8_t v_isSharedCheck_2255_; 
lean_dec(v_val_2026_);
lean_dec_ref(v_toRing_2025_);
lean_dec_ref(v_a_1993_);
lean_dec_ref(v_e_1991_);
v_a_2248_ = lean_ctor_get(v___x_2047_, 0);
v_isSharedCheck_2255_ = !lean_is_exclusive(v___x_2047_);
if (v_isSharedCheck_2255_ == 0)
{
v___x_2250_ = v___x_2047_;
v_isShared_2251_ = v_isSharedCheck_2255_;
goto v_resetjp_2249_;
}
else
{
lean_inc(v_a_2248_);
lean_dec(v___x_2047_);
v___x_2250_ = lean_box(0);
v_isShared_2251_ = v_isSharedCheck_2255_;
goto v_resetjp_2249_;
}
v_resetjp_2249_:
{
lean_object* v___x_2253_; 
if (v_isShared_2251_ == 0)
{
v___x_2253_ = v___x_2250_;
goto v_reusejp_2252_;
}
else
{
lean_object* v_reuseFailAlloc_2254_; 
v_reuseFailAlloc_2254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2254_, 0, v_a_2248_);
v___x_2253_ = v_reuseFailAlloc_2254_;
goto v_reusejp_2252_;
}
v_reusejp_2252_:
{
return v___x_2253_;
}
}
}
v___jp_2027_:
{
lean_object* v_type_2038_; lean_object* v_u_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; 
v_type_2038_ = lean_ctor_get(v_toRing_2025_, 1);
lean_inc_ref(v_type_2038_);
v_u_2039_ = lean_ctor_get(v_toRing_2025_, 2);
lean_inc(v_u_2039_);
lean_dec_ref(v_toRing_2025_);
v___x_2040_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__2));
v___x_2041_ = lean_box(0);
v___x_2042_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2042_, 0, v_u_2039_);
lean_ctor_set(v___x_2042_, 1, v___x_2041_);
v___x_2043_ = l_Lean_mkConst(v___x_2040_, v___x_2042_);
v___x_2044_ = l_Lean_mkApp3(v___x_2043_, v_type_2038_, v_val_2026_, v_a_1993_);
v___x_2045_ = lean_unsigned_to_nat(0u);
v___x_2046_ = l_Lean_Meta_Grind_pushNewFact(v___x_2044_, v___x_2045_, v___y_2028_, v___y_2029_, v___y_2030_, v___y_2031_, v___y_2032_, v___y_2033_, v___y_2034_, v___y_2035_, v___y_2036_, v___y_2037_);
return v___x_2046_;
}
}
else
{
lean_object* v___x_2256_; lean_object* v___x_2258_; 
lean_dec(v_fieldInst_x3f_2024_);
lean_dec(v_a_2020_);
lean_dec_ref(v_a_1993_);
lean_dec_ref(v_e_1991_);
v___x_2256_ = lean_box(0);
if (v_isShared_2023_ == 0)
{
lean_ctor_set(v___x_2022_, 0, v___x_2256_);
v___x_2258_ = v___x_2022_;
goto v_reusejp_2257_;
}
else
{
lean_object* v_reuseFailAlloc_2259_; 
v_reuseFailAlloc_2259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2259_, 0, v___x_2256_);
v___x_2258_ = v_reuseFailAlloc_2259_;
goto v_reusejp_2257_;
}
v_reusejp_2257_:
{
return v___x_2258_;
}
}
}
}
else
{
lean_object* v_a_2261_; lean_object* v___x_2263_; uint8_t v_isShared_2264_; uint8_t v_isSharedCheck_2268_; 
lean_dec_ref(v_a_1993_);
lean_dec_ref(v_e_1991_);
v_a_2261_ = lean_ctor_get(v___x_2019_, 0);
v_isSharedCheck_2268_ = !lean_is_exclusive(v___x_2019_);
if (v_isSharedCheck_2268_ == 0)
{
v___x_2263_ = v___x_2019_;
v_isShared_2264_ = v_isSharedCheck_2268_;
goto v_resetjp_2262_;
}
else
{
lean_inc(v_a_2261_);
lean_dec(v___x_2019_);
v___x_2263_ = lean_box(0);
v_isShared_2264_ = v_isSharedCheck_2268_;
goto v_resetjp_2262_;
}
v_resetjp_2262_:
{
lean_object* v___x_2266_; 
if (v_isShared_2264_ == 0)
{
v___x_2266_ = v___x_2263_;
goto v_reusejp_2265_;
}
else
{
lean_object* v_reuseFailAlloc_2267_; 
v_reuseFailAlloc_2267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2267_, 0, v_a_2261_);
v___x_2266_ = v_reuseFailAlloc_2267_;
goto v_reusejp_2265_;
}
v_reusejp_2265_:
{
return v___x_2266_;
}
}
}
}
}
}
else
{
lean_object* v_a_2270_; lean_object* v___x_2272_; uint8_t v_isShared_2273_; uint8_t v_isSharedCheck_2277_; 
lean_dec_ref(v_a_1993_);
lean_dec_ref(v_e_1991_);
v_a_2270_ = lean_ctor_get(v___x_2009_, 0);
v_isSharedCheck_2277_ = !lean_is_exclusive(v___x_2009_);
if (v_isSharedCheck_2277_ == 0)
{
v___x_2272_ = v___x_2009_;
v_isShared_2273_ = v_isSharedCheck_2277_;
goto v_resetjp_2271_;
}
else
{
lean_inc(v_a_2270_);
lean_dec(v___x_2009_);
v___x_2272_ = lean_box(0);
v_isShared_2273_ = v_isSharedCheck_2277_;
goto v_resetjp_2271_;
}
v_resetjp_2271_:
{
lean_object* v___x_2275_; 
if (v_isShared_2273_ == 0)
{
v___x_2275_ = v___x_2272_;
goto v_reusejp_2274_;
}
else
{
lean_object* v_reuseFailAlloc_2276_; 
v_reuseFailAlloc_2276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2276_, 0, v_a_2270_);
v___x_2275_ = v_reuseFailAlloc_2276_;
goto v_reusejp_2274_;
}
v_reusejp_2274_:
{
return v___x_2275_;
}
}
}
v___jp_2006_:
{
lean_object* v___x_2007_; lean_object* v___x_2008_; 
v___x_2007_ = lean_box(0);
v___x_2008_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2008_, 0, v___x_2007_);
return v___x_2008_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___boxed(lean_object* v_e_2278_, lean_object* v_inst_2279_, lean_object* v_a_2280_, lean_object* v_a_2281_, lean_object* v_a_2282_, lean_object* v_a_2283_, lean_object* v_a_2284_, lean_object* v_a_2285_, lean_object* v_a_2286_, lean_object* v_a_2287_, lean_object* v_a_2288_, lean_object* v_a_2289_, lean_object* v_a_2290_, lean_object* v_a_2291_, lean_object* v_a_2292_){
_start:
{
lean_object* v_res_2293_; 
v_res_2293_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv(v_e_2278_, v_inst_2279_, v_a_2280_, v_a_2281_, v_a_2282_, v_a_2283_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_, v_a_2288_, v_a_2289_, v_a_2290_, v_a_2291_);
lean_dec(v_a_2291_);
lean_dec_ref(v_a_2290_);
lean_dec(v_a_2289_);
lean_dec_ref(v_a_2288_);
lean_dec(v_a_2287_);
lean_dec_ref(v_a_2286_);
lean_dec(v_a_2285_);
lean_dec_ref(v_a_2284_);
lean_dec(v_a_2283_);
lean_dec(v_a_2282_);
lean_dec_ref(v_a_2281_);
lean_dec_ref(v_inst_2279_);
return v_res_2293_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0(lean_object* v_00_u03b2_2294_, lean_object* v_x_2295_, lean_object* v_x_2296_, lean_object* v_x_2297_){
_start:
{
lean_object* v___x_2298_; 
v___x_2298_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0___redArg(v_x_2295_, v_x_2296_, v_x_2297_);
return v___x_2298_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1(lean_object* v_00_u03b2_2299_, lean_object* v_x_2300_, lean_object* v_x_2301_){
_start:
{
uint8_t v___x_2302_; 
v___x_2302_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1___redArg(v_x_2300_, v_x_2301_);
return v___x_2302_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1___boxed(lean_object* v_00_u03b2_2303_, lean_object* v_x_2304_, lean_object* v_x_2305_){
_start:
{
uint8_t v_res_2306_; lean_object* v_r_2307_; 
v_res_2306_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1(v_00_u03b2_2303_, v_x_2304_, v_x_2305_);
lean_dec_ref(v_x_2305_);
lean_dec_ref(v_x_2304_);
v_r_2307_ = lean_box(v_res_2306_);
return v_r_2307_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0(lean_object* v_00_u03b2_2308_, lean_object* v_x_2309_, size_t v_x_2310_, size_t v_x_2311_, lean_object* v_x_2312_, lean_object* v_x_2313_){
_start:
{
lean_object* v___x_2314_; 
v___x_2314_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg(v_x_2309_, v_x_2310_, v_x_2311_, v_x_2312_, v_x_2313_);
return v___x_2314_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2315_, lean_object* v_x_2316_, lean_object* v_x_2317_, lean_object* v_x_2318_, lean_object* v_x_2319_, lean_object* v_x_2320_){
_start:
{
size_t v_x_141710__boxed_2321_; size_t v_x_141711__boxed_2322_; lean_object* v_res_2323_; 
v_x_141710__boxed_2321_ = lean_unbox_usize(v_x_2317_);
lean_dec(v_x_2317_);
v_x_141711__boxed_2322_ = lean_unbox_usize(v_x_2318_);
lean_dec(v_x_2318_);
v_res_2323_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0(v_00_u03b2_2315_, v_x_2316_, v_x_141710__boxed_2321_, v_x_141711__boxed_2322_, v_x_2319_, v_x_2320_);
return v_res_2323_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1_spec__2(lean_object* v_00_u03b2_2324_, lean_object* v_x_2325_, size_t v_x_2326_, lean_object* v_x_2327_){
_start:
{
uint8_t v___x_2328_; 
v___x_2328_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1_spec__2___redArg(v_x_2325_, v_x_2326_, v_x_2327_);
return v___x_2328_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1_spec__2___boxed(lean_object* v_00_u03b2_2329_, lean_object* v_x_2330_, lean_object* v_x_2331_, lean_object* v_x_2332_){
_start:
{
size_t v_x_141727__boxed_2333_; uint8_t v_res_2334_; lean_object* v_r_2335_; 
v_x_141727__boxed_2333_ = lean_unbox_usize(v_x_2331_);
lean_dec(v_x_2331_);
v_res_2334_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1_spec__2(v_00_u03b2_2329_, v_x_2330_, v_x_141727__boxed_2333_, v_x_2332_);
lean_dec_ref(v_x_2332_);
lean_dec_ref(v_x_2330_);
v_r_2335_ = lean_box(v_res_2334_);
return v_r_2335_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_2336_, lean_object* v_n_2337_, lean_object* v_k_2338_, lean_object* v_v_2339_){
_start:
{
lean_object* v___x_2340_; 
v___x_2340_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0_spec__2___redArg(v_n_2337_, v_k_2338_, v_v_2339_);
return v___x_2340_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_2341_, size_t v_depth_2342_, lean_object* v_keys_2343_, lean_object* v_vals_2344_, lean_object* v_heq_2345_, lean_object* v_i_2346_, lean_object* v_entries_2347_){
_start:
{
lean_object* v___x_2348_; 
v___x_2348_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0_spec__3___redArg(v_depth_2342_, v_keys_2343_, v_vals_2344_, v_i_2346_, v_entries_2347_);
return v___x_2348_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b2_2349_, lean_object* v_depth_2350_, lean_object* v_keys_2351_, lean_object* v_vals_2352_, lean_object* v_heq_2353_, lean_object* v_i_2354_, lean_object* v_entries_2355_){
_start:
{
size_t v_depth_boxed_2356_; lean_object* v_res_2357_; 
v_depth_boxed_2356_ = lean_unbox_usize(v_depth_2350_);
lean_dec(v_depth_2350_);
v_res_2357_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0_spec__3(v_00_u03b2_2349_, v_depth_boxed_2356_, v_keys_2351_, v_vals_2352_, v_heq_2353_, v_i_2354_, v_entries_2355_);
lean_dec_ref(v_vals_2352_);
lean_dec_ref(v_keys_2351_);
return v_res_2357_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1_spec__2_spec__6(lean_object* v_00_u03b2_2358_, lean_object* v_keys_2359_, lean_object* v_vals_2360_, lean_object* v_heq_2361_, lean_object* v_i_2362_, lean_object* v_k_2363_){
_start:
{
uint8_t v___x_2364_; 
v___x_2364_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1_spec__2_spec__6___redArg(v_keys_2359_, v_i_2362_, v_k_2363_);
return v___x_2364_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1_spec__2_spec__6___boxed(lean_object* v_00_u03b2_2365_, lean_object* v_keys_2366_, lean_object* v_vals_2367_, lean_object* v_heq_2368_, lean_object* v_i_2369_, lean_object* v_k_2370_){
_start:
{
uint8_t v_res_2371_; lean_object* v_r_2372_; 
v_res_2371_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1_spec__2_spec__6(v_00_u03b2_2365_, v_keys_2366_, v_vals_2367_, v_heq_2368_, v_i_2369_, v_k_2370_);
lean_dec_ref(v_k_2370_);
lean_dec_ref(v_vals_2367_);
lean_dec_ref(v_keys_2366_);
v_r_2372_ = lean_box(v_res_2371_);
return v_r_2372_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0_spec__2_spec__6(lean_object* v_00_u03b2_2373_, lean_object* v_x_2374_, lean_object* v_x_2375_, lean_object* v_x_2376_, lean_object* v_x_2377_){
_start:
{
lean_object* v___x_2378_; 
v___x_2378_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0_spec__2_spec__6___redArg(v_x_2374_, v_x_2375_, v_x_2376_, v_x_2377_);
return v___x_2378_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeInv(lean_object* v_e_2379_, lean_object* v_a_2380_, lean_object* v_a_2381_, lean_object* v_a_2382_, lean_object* v_a_2383_, lean_object* v_a_2384_, lean_object* v_a_2385_, lean_object* v_a_2386_, lean_object* v_a_2387_, lean_object* v_a_2388_, lean_object* v_a_2389_){
_start:
{
lean_object* v___x_2391_; 
lean_inc_ref(v_e_2379_);
v___x_2391_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_2379_, v_a_2387_);
if (lean_obj_tag(v___x_2391_) == 0)
{
lean_object* v_a_2392_; lean_object* v___x_2394_; uint8_t v_isShared_2395_; uint8_t v_isSharedCheck_2453_; 
v_a_2392_ = lean_ctor_get(v___x_2391_, 0);
v_isSharedCheck_2453_ = !lean_is_exclusive(v___x_2391_);
if (v_isSharedCheck_2453_ == 0)
{
v___x_2394_ = v___x_2391_;
v_isShared_2395_ = v_isSharedCheck_2453_;
goto v_resetjp_2393_;
}
else
{
lean_inc(v_a_2392_);
lean_dec(v___x_2391_);
v___x_2394_ = lean_box(0);
v_isShared_2395_ = v_isSharedCheck_2453_;
goto v_resetjp_2393_;
}
v_resetjp_2393_:
{
lean_object* v___x_2402_; uint8_t v___x_2403_; 
v___x_2402_ = l_Lean_Expr_cleanupAnnotations(v_a_2392_);
v___x_2403_ = l_Lean_Expr_isApp(v___x_2402_);
if (v___x_2403_ == 0)
{
lean_dec_ref(v___x_2402_);
lean_dec_ref(v_e_2379_);
goto v___jp_2396_;
}
else
{
lean_object* v_arg_2404_; lean_object* v___x_2405_; uint8_t v___x_2406_; 
v_arg_2404_ = lean_ctor_get(v___x_2402_, 1);
lean_inc_ref(v_arg_2404_);
v___x_2405_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2402_);
v___x_2406_ = l_Lean_Expr_isApp(v___x_2405_);
if (v___x_2406_ == 0)
{
lean_dec_ref(v___x_2405_);
lean_dec_ref(v_arg_2404_);
lean_dec_ref(v_e_2379_);
goto v___jp_2396_;
}
else
{
lean_object* v_arg_2407_; lean_object* v___x_2408_; uint8_t v___x_2409_; 
v_arg_2407_ = lean_ctor_get(v___x_2405_, 1);
lean_inc_ref(v_arg_2407_);
v___x_2408_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2405_);
v___x_2409_ = l_Lean_Expr_isApp(v___x_2408_);
if (v___x_2409_ == 0)
{
lean_dec_ref(v___x_2408_);
lean_dec_ref(v_arg_2407_);
lean_dec_ref(v_arg_2404_);
lean_dec_ref(v_e_2379_);
goto v___jp_2396_;
}
else
{
lean_object* v_arg_2410_; lean_object* v___x_2411_; lean_object* v___x_2412_; uint8_t v___x_2413_; 
v_arg_2410_ = lean_ctor_get(v___x_2408_, 1);
lean_inc_ref(v_arg_2410_);
v___x_2411_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2408_);
v___x_2412_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___closed__6));
v___x_2413_ = l_Lean_Expr_isConstOf(v___x_2411_, v___x_2412_);
lean_dec_ref(v___x_2411_);
if (v___x_2413_ == 0)
{
lean_dec_ref(v_arg_2410_);
lean_dec_ref(v_arg_2407_);
lean_dec_ref(v_arg_2404_);
lean_dec_ref(v_e_2379_);
goto v___jp_2396_;
}
else
{
lean_object* v___x_2414_; 
lean_del_object(v___x_2394_);
v___x_2414_ = l_Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f(v_arg_2410_, v_a_2380_, v_a_2381_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_, v_a_2387_, v_a_2388_, v_a_2389_);
if (lean_obj_tag(v___x_2414_) == 0)
{
lean_object* v_a_2415_; lean_object* v___x_2417_; uint8_t v_isShared_2418_; uint8_t v_isSharedCheck_2444_; 
v_a_2415_ = lean_ctor_get(v___x_2414_, 0);
v_isSharedCheck_2444_ = !lean_is_exclusive(v___x_2414_);
if (v_isSharedCheck_2444_ == 0)
{
v___x_2417_ = v___x_2414_;
v_isShared_2418_ = v_isSharedCheck_2444_;
goto v_resetjp_2416_;
}
else
{
lean_inc(v_a_2415_);
lean_dec(v___x_2414_);
v___x_2417_ = lean_box(0);
v_isShared_2418_ = v_isSharedCheck_2444_;
goto v_resetjp_2416_;
}
v_resetjp_2416_:
{
if (lean_obj_tag(v_a_2415_) == 1)
{
lean_object* v_val_2419_; uint8_t v___x_2420_; lean_object* v___x_2421_; lean_object* v___x_2422_; 
lean_del_object(v___x_2417_);
v_val_2419_ = lean_ctor_get(v_a_2415_, 0);
lean_inc(v_val_2419_);
lean_dec_ref(v_a_2415_);
v___x_2420_ = 0;
v___x_2421_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2421_, 0, v_val_2419_);
lean_ctor_set_uint8(v___x_2421_, sizeof(void*)*1, v___x_2420_);
v___x_2422_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv(v_e_2379_, v_arg_2407_, v_arg_2404_, v___x_2421_, v_a_2380_, v_a_2381_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_, v_a_2387_, v_a_2388_, v_a_2389_);
lean_dec_ref(v___x_2421_);
lean_dec_ref(v_arg_2407_);
if (lean_obj_tag(v___x_2422_) == 0)
{
lean_object* v___x_2424_; uint8_t v_isShared_2425_; uint8_t v_isSharedCheck_2430_; 
v_isSharedCheck_2430_ = !lean_is_exclusive(v___x_2422_);
if (v_isSharedCheck_2430_ == 0)
{
lean_object* v_unused_2431_; 
v_unused_2431_ = lean_ctor_get(v___x_2422_, 0);
lean_dec(v_unused_2431_);
v___x_2424_ = v___x_2422_;
v_isShared_2425_ = v_isSharedCheck_2430_;
goto v_resetjp_2423_;
}
else
{
lean_dec(v___x_2422_);
v___x_2424_ = lean_box(0);
v_isShared_2425_ = v_isSharedCheck_2430_;
goto v_resetjp_2423_;
}
v_resetjp_2423_:
{
lean_object* v___x_2426_; lean_object* v___x_2428_; 
v___x_2426_ = lean_box(v___x_2413_);
if (v_isShared_2425_ == 0)
{
lean_ctor_set(v___x_2424_, 0, v___x_2426_);
v___x_2428_ = v___x_2424_;
goto v_reusejp_2427_;
}
else
{
lean_object* v_reuseFailAlloc_2429_; 
v_reuseFailAlloc_2429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2429_, 0, v___x_2426_);
v___x_2428_ = v_reuseFailAlloc_2429_;
goto v_reusejp_2427_;
}
v_reusejp_2427_:
{
return v___x_2428_;
}
}
}
else
{
lean_object* v_a_2432_; lean_object* v___x_2434_; uint8_t v_isShared_2435_; uint8_t v_isSharedCheck_2439_; 
v_a_2432_ = lean_ctor_get(v___x_2422_, 0);
v_isSharedCheck_2439_ = !lean_is_exclusive(v___x_2422_);
if (v_isSharedCheck_2439_ == 0)
{
v___x_2434_ = v___x_2422_;
v_isShared_2435_ = v_isSharedCheck_2439_;
goto v_resetjp_2433_;
}
else
{
lean_inc(v_a_2432_);
lean_dec(v___x_2422_);
v___x_2434_ = lean_box(0);
v_isShared_2435_ = v_isSharedCheck_2439_;
goto v_resetjp_2433_;
}
v_resetjp_2433_:
{
lean_object* v___x_2437_; 
if (v_isShared_2435_ == 0)
{
v___x_2437_ = v___x_2434_;
goto v_reusejp_2436_;
}
else
{
lean_object* v_reuseFailAlloc_2438_; 
v_reuseFailAlloc_2438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2438_, 0, v_a_2432_);
v___x_2437_ = v_reuseFailAlloc_2438_;
goto v_reusejp_2436_;
}
v_reusejp_2436_:
{
return v___x_2437_;
}
}
}
}
else
{
lean_object* v___x_2440_; lean_object* v___x_2442_; 
lean_dec(v_a_2415_);
lean_dec_ref(v_arg_2407_);
lean_dec_ref(v_arg_2404_);
lean_dec_ref(v_e_2379_);
v___x_2440_ = lean_box(v___x_2413_);
if (v_isShared_2418_ == 0)
{
lean_ctor_set(v___x_2417_, 0, v___x_2440_);
v___x_2442_ = v___x_2417_;
goto v_reusejp_2441_;
}
else
{
lean_object* v_reuseFailAlloc_2443_; 
v_reuseFailAlloc_2443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2443_, 0, v___x_2440_);
v___x_2442_ = v_reuseFailAlloc_2443_;
goto v_reusejp_2441_;
}
v_reusejp_2441_:
{
return v___x_2442_;
}
}
}
}
else
{
lean_object* v_a_2445_; lean_object* v___x_2447_; uint8_t v_isShared_2448_; uint8_t v_isSharedCheck_2452_; 
lean_dec_ref(v_arg_2407_);
lean_dec_ref(v_arg_2404_);
lean_dec_ref(v_e_2379_);
v_a_2445_ = lean_ctor_get(v___x_2414_, 0);
v_isSharedCheck_2452_ = !lean_is_exclusive(v___x_2414_);
if (v_isSharedCheck_2452_ == 0)
{
v___x_2447_ = v___x_2414_;
v_isShared_2448_ = v_isSharedCheck_2452_;
goto v_resetjp_2446_;
}
else
{
lean_inc(v_a_2445_);
lean_dec(v___x_2414_);
v___x_2447_ = lean_box(0);
v_isShared_2448_ = v_isSharedCheck_2452_;
goto v_resetjp_2446_;
}
v_resetjp_2446_:
{
lean_object* v___x_2450_; 
if (v_isShared_2448_ == 0)
{
v___x_2450_ = v___x_2447_;
goto v_reusejp_2449_;
}
else
{
lean_object* v_reuseFailAlloc_2451_; 
v_reuseFailAlloc_2451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2451_, 0, v_a_2445_);
v___x_2450_ = v_reuseFailAlloc_2451_;
goto v_reusejp_2449_;
}
v_reusejp_2449_:
{
return v___x_2450_;
}
}
}
}
}
}
}
v___jp_2396_:
{
uint8_t v___x_2397_; lean_object* v___x_2398_; lean_object* v___x_2400_; 
v___x_2397_ = 0;
v___x_2398_ = lean_box(v___x_2397_);
if (v_isShared_2395_ == 0)
{
lean_ctor_set(v___x_2394_, 0, v___x_2398_);
v___x_2400_ = v___x_2394_;
goto v_reusejp_2399_;
}
else
{
lean_object* v_reuseFailAlloc_2401_; 
v_reuseFailAlloc_2401_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2401_, 0, v___x_2398_);
v___x_2400_ = v_reuseFailAlloc_2401_;
goto v_reusejp_2399_;
}
v_reusejp_2399_:
{
return v___x_2400_;
}
}
}
}
else
{
lean_object* v_a_2454_; lean_object* v___x_2456_; uint8_t v_isShared_2457_; uint8_t v_isSharedCheck_2461_; 
lean_dec_ref(v_e_2379_);
v_a_2454_ = lean_ctor_get(v___x_2391_, 0);
v_isSharedCheck_2461_ = !lean_is_exclusive(v___x_2391_);
if (v_isSharedCheck_2461_ == 0)
{
v___x_2456_ = v___x_2391_;
v_isShared_2457_ = v_isSharedCheck_2461_;
goto v_resetjp_2455_;
}
else
{
lean_inc(v_a_2454_);
lean_dec(v___x_2391_);
v___x_2456_ = lean_box(0);
v_isShared_2457_ = v_isSharedCheck_2461_;
goto v_resetjp_2455_;
}
v_resetjp_2455_:
{
lean_object* v___x_2459_; 
if (v_isShared_2457_ == 0)
{
v___x_2459_ = v___x_2456_;
goto v_reusejp_2458_;
}
else
{
lean_object* v_reuseFailAlloc_2460_; 
v_reuseFailAlloc_2460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2460_, 0, v_a_2454_);
v___x_2459_ = v_reuseFailAlloc_2460_;
goto v_reusejp_2458_;
}
v_reusejp_2458_:
{
return v___x_2459_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeInv___boxed(lean_object* v_e_2462_, lean_object* v_a_2463_, lean_object* v_a_2464_, lean_object* v_a_2465_, lean_object* v_a_2466_, lean_object* v_a_2467_, lean_object* v_a_2468_, lean_object* v_a_2469_, lean_object* v_a_2470_, lean_object* v_a_2471_, lean_object* v_a_2472_, lean_object* v_a_2473_){
_start:
{
lean_object* v_res_2474_; 
v_res_2474_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeInv(v_e_2462_, v_a_2463_, v_a_2464_, v_a_2465_, v_a_2466_, v_a_2467_, v_a_2468_, v_a_2469_, v_a_2470_, v_a_2471_, v_a_2472_);
lean_dec(v_a_2472_);
lean_dec_ref(v_a_2471_);
lean_dec(v_a_2470_);
lean_dec_ref(v_a_2469_);
lean_dec(v_a_2468_);
lean_dec_ref(v_a_2467_);
lean_dec(v_a_2466_);
lean_dec_ref(v_a_2465_);
lean_dec(v_a_2464_);
lean_dec(v_a_2463_);
return v_res_2474_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0_spec__1_spec__6___redArg(lean_object* v_x_2475_, lean_object* v_x_2476_, lean_object* v_x_2477_, lean_object* v_x_2478_){
_start:
{
lean_object* v_ks_2479_; lean_object* v_vs_2480_; lean_object* v___x_2482_; uint8_t v_isShared_2483_; uint8_t v_isSharedCheck_2504_; 
v_ks_2479_ = lean_ctor_get(v_x_2475_, 0);
v_vs_2480_ = lean_ctor_get(v_x_2475_, 1);
v_isSharedCheck_2504_ = !lean_is_exclusive(v_x_2475_);
if (v_isSharedCheck_2504_ == 0)
{
v___x_2482_ = v_x_2475_;
v_isShared_2483_ = v_isSharedCheck_2504_;
goto v_resetjp_2481_;
}
else
{
lean_inc(v_vs_2480_);
lean_inc(v_ks_2479_);
lean_dec(v_x_2475_);
v___x_2482_ = lean_box(0);
v_isShared_2483_ = v_isSharedCheck_2504_;
goto v_resetjp_2481_;
}
v_resetjp_2481_:
{
lean_object* v___x_2484_; uint8_t v___x_2485_; 
v___x_2484_ = lean_array_get_size(v_ks_2479_);
v___x_2485_ = lean_nat_dec_lt(v_x_2476_, v___x_2484_);
if (v___x_2485_ == 0)
{
lean_object* v___x_2486_; lean_object* v___x_2487_; lean_object* v___x_2489_; 
lean_dec(v_x_2476_);
v___x_2486_ = lean_array_push(v_ks_2479_, v_x_2477_);
v___x_2487_ = lean_array_push(v_vs_2480_, v_x_2478_);
if (v_isShared_2483_ == 0)
{
lean_ctor_set(v___x_2482_, 1, v___x_2487_);
lean_ctor_set(v___x_2482_, 0, v___x_2486_);
v___x_2489_ = v___x_2482_;
goto v_reusejp_2488_;
}
else
{
lean_object* v_reuseFailAlloc_2490_; 
v_reuseFailAlloc_2490_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2490_, 0, v___x_2486_);
lean_ctor_set(v_reuseFailAlloc_2490_, 1, v___x_2487_);
v___x_2489_ = v_reuseFailAlloc_2490_;
goto v_reusejp_2488_;
}
v_reusejp_2488_:
{
return v___x_2489_;
}
}
else
{
lean_object* v_k_x27_2491_; uint8_t v___x_2492_; 
v_k_x27_2491_ = lean_array_fget_borrowed(v_ks_2479_, v_x_2476_);
v___x_2492_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_2477_, v_k_x27_2491_);
if (v___x_2492_ == 0)
{
lean_object* v___x_2494_; 
if (v_isShared_2483_ == 0)
{
v___x_2494_ = v___x_2482_;
goto v_reusejp_2493_;
}
else
{
lean_object* v_reuseFailAlloc_2498_; 
v_reuseFailAlloc_2498_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2498_, 0, v_ks_2479_);
lean_ctor_set(v_reuseFailAlloc_2498_, 1, v_vs_2480_);
v___x_2494_ = v_reuseFailAlloc_2498_;
goto v_reusejp_2493_;
}
v_reusejp_2493_:
{
lean_object* v___x_2495_; lean_object* v___x_2496_; 
v___x_2495_ = lean_unsigned_to_nat(1u);
v___x_2496_ = lean_nat_add(v_x_2476_, v___x_2495_);
lean_dec(v_x_2476_);
v_x_2475_ = v___x_2494_;
v_x_2476_ = v___x_2496_;
goto _start;
}
}
else
{
lean_object* v___x_2499_; lean_object* v___x_2500_; lean_object* v___x_2502_; 
v___x_2499_ = lean_array_fset(v_ks_2479_, v_x_2476_, v_x_2477_);
v___x_2500_ = lean_array_fset(v_vs_2480_, v_x_2476_, v_x_2478_);
lean_dec(v_x_2476_);
if (v_isShared_2483_ == 0)
{
lean_ctor_set(v___x_2482_, 1, v___x_2500_);
lean_ctor_set(v___x_2482_, 0, v___x_2499_);
v___x_2502_ = v___x_2482_;
goto v_reusejp_2501_;
}
else
{
lean_object* v_reuseFailAlloc_2503_; 
v_reuseFailAlloc_2503_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2503_, 0, v___x_2499_);
lean_ctor_set(v_reuseFailAlloc_2503_, 1, v___x_2500_);
v___x_2502_ = v_reuseFailAlloc_2503_;
goto v_reusejp_2501_;
}
v_reusejp_2501_:
{
return v___x_2502_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0_spec__1___redArg(lean_object* v_n_2505_, lean_object* v_k_2506_, lean_object* v_v_2507_){
_start:
{
lean_object* v___x_2508_; lean_object* v___x_2509_; 
v___x_2508_ = lean_unsigned_to_nat(0u);
v___x_2509_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0_spec__1_spec__6___redArg(v_n_2505_, v___x_2508_, v_k_2506_, v_v_2507_);
return v___x_2509_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0___redArg(lean_object* v_x_2510_, size_t v_x_2511_, size_t v_x_2512_, lean_object* v_x_2513_, lean_object* v_x_2514_){
_start:
{
if (lean_obj_tag(v_x_2510_) == 0)
{
lean_object* v_es_2515_; size_t v___x_2516_; size_t v___x_2517_; size_t v___x_2518_; size_t v___x_2519_; lean_object* v_j_2520_; lean_object* v___x_2521_; uint8_t v___x_2522_; 
v_es_2515_ = lean_ctor_get(v_x_2510_, 0);
v___x_2516_ = ((size_t)5ULL);
v___x_2517_ = ((size_t)1ULL);
v___x_2518_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg___closed__1);
v___x_2519_ = lean_usize_land(v_x_2511_, v___x_2518_);
v_j_2520_ = lean_usize_to_nat(v___x_2519_);
v___x_2521_ = lean_array_get_size(v_es_2515_);
v___x_2522_ = lean_nat_dec_lt(v_j_2520_, v___x_2521_);
if (v___x_2522_ == 0)
{
lean_dec(v_j_2520_);
lean_dec(v_x_2514_);
lean_dec_ref(v_x_2513_);
return v_x_2510_;
}
else
{
lean_object* v___x_2524_; uint8_t v_isShared_2525_; uint8_t v_isSharedCheck_2559_; 
lean_inc_ref(v_es_2515_);
v_isSharedCheck_2559_ = !lean_is_exclusive(v_x_2510_);
if (v_isSharedCheck_2559_ == 0)
{
lean_object* v_unused_2560_; 
v_unused_2560_ = lean_ctor_get(v_x_2510_, 0);
lean_dec(v_unused_2560_);
v___x_2524_ = v_x_2510_;
v_isShared_2525_ = v_isSharedCheck_2559_;
goto v_resetjp_2523_;
}
else
{
lean_dec(v_x_2510_);
v___x_2524_ = lean_box(0);
v_isShared_2525_ = v_isSharedCheck_2559_;
goto v_resetjp_2523_;
}
v_resetjp_2523_:
{
lean_object* v_v_2526_; lean_object* v___x_2527_; lean_object* v_xs_x27_2528_; lean_object* v___y_2530_; 
v_v_2526_ = lean_array_fget(v_es_2515_, v_j_2520_);
v___x_2527_ = lean_box(0);
v_xs_x27_2528_ = lean_array_fset(v_es_2515_, v_j_2520_, v___x_2527_);
switch(lean_obj_tag(v_v_2526_))
{
case 0:
{
lean_object* v_key_2535_; lean_object* v_val_2536_; lean_object* v___x_2538_; uint8_t v_isShared_2539_; uint8_t v_isSharedCheck_2546_; 
v_key_2535_ = lean_ctor_get(v_v_2526_, 0);
v_val_2536_ = lean_ctor_get(v_v_2526_, 1);
v_isSharedCheck_2546_ = !lean_is_exclusive(v_v_2526_);
if (v_isSharedCheck_2546_ == 0)
{
v___x_2538_ = v_v_2526_;
v_isShared_2539_ = v_isSharedCheck_2546_;
goto v_resetjp_2537_;
}
else
{
lean_inc(v_val_2536_);
lean_inc(v_key_2535_);
lean_dec(v_v_2526_);
v___x_2538_ = lean_box(0);
v_isShared_2539_ = v_isSharedCheck_2546_;
goto v_resetjp_2537_;
}
v_resetjp_2537_:
{
uint8_t v___x_2540_; 
v___x_2540_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_2513_, v_key_2535_);
if (v___x_2540_ == 0)
{
lean_object* v___x_2541_; lean_object* v___x_2542_; 
lean_del_object(v___x_2538_);
v___x_2541_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_2535_, v_val_2536_, v_x_2513_, v_x_2514_);
v___x_2542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2542_, 0, v___x_2541_);
v___y_2530_ = v___x_2542_;
goto v___jp_2529_;
}
else
{
lean_object* v___x_2544_; 
lean_dec(v_val_2536_);
lean_dec(v_key_2535_);
if (v_isShared_2539_ == 0)
{
lean_ctor_set(v___x_2538_, 1, v_x_2514_);
lean_ctor_set(v___x_2538_, 0, v_x_2513_);
v___x_2544_ = v___x_2538_;
goto v_reusejp_2543_;
}
else
{
lean_object* v_reuseFailAlloc_2545_; 
v_reuseFailAlloc_2545_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2545_, 0, v_x_2513_);
lean_ctor_set(v_reuseFailAlloc_2545_, 1, v_x_2514_);
v___x_2544_ = v_reuseFailAlloc_2545_;
goto v_reusejp_2543_;
}
v_reusejp_2543_:
{
v___y_2530_ = v___x_2544_;
goto v___jp_2529_;
}
}
}
}
case 1:
{
lean_object* v_node_2547_; lean_object* v___x_2549_; uint8_t v_isShared_2550_; uint8_t v_isSharedCheck_2557_; 
v_node_2547_ = lean_ctor_get(v_v_2526_, 0);
v_isSharedCheck_2557_ = !lean_is_exclusive(v_v_2526_);
if (v_isSharedCheck_2557_ == 0)
{
v___x_2549_ = v_v_2526_;
v_isShared_2550_ = v_isSharedCheck_2557_;
goto v_resetjp_2548_;
}
else
{
lean_inc(v_node_2547_);
lean_dec(v_v_2526_);
v___x_2549_ = lean_box(0);
v_isShared_2550_ = v_isSharedCheck_2557_;
goto v_resetjp_2548_;
}
v_resetjp_2548_:
{
size_t v___x_2551_; size_t v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2555_; 
v___x_2551_ = lean_usize_shift_right(v_x_2511_, v___x_2516_);
v___x_2552_ = lean_usize_add(v_x_2512_, v___x_2517_);
v___x_2553_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0___redArg(v_node_2547_, v___x_2551_, v___x_2552_, v_x_2513_, v_x_2514_);
if (v_isShared_2550_ == 0)
{
lean_ctor_set(v___x_2549_, 0, v___x_2553_);
v___x_2555_ = v___x_2549_;
goto v_reusejp_2554_;
}
else
{
lean_object* v_reuseFailAlloc_2556_; 
v_reuseFailAlloc_2556_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2556_, 0, v___x_2553_);
v___x_2555_ = v_reuseFailAlloc_2556_;
goto v_reusejp_2554_;
}
v_reusejp_2554_:
{
v___y_2530_ = v___x_2555_;
goto v___jp_2529_;
}
}
}
default: 
{
lean_object* v___x_2558_; 
v___x_2558_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2558_, 0, v_x_2513_);
lean_ctor_set(v___x_2558_, 1, v_x_2514_);
v___y_2530_ = v___x_2558_;
goto v___jp_2529_;
}
}
v___jp_2529_:
{
lean_object* v___x_2531_; lean_object* v___x_2533_; 
v___x_2531_ = lean_array_fset(v_xs_x27_2528_, v_j_2520_, v___y_2530_);
lean_dec(v_j_2520_);
if (v_isShared_2525_ == 0)
{
lean_ctor_set(v___x_2524_, 0, v___x_2531_);
v___x_2533_ = v___x_2524_;
goto v_reusejp_2532_;
}
else
{
lean_object* v_reuseFailAlloc_2534_; 
v_reuseFailAlloc_2534_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2534_, 0, v___x_2531_);
v___x_2533_ = v_reuseFailAlloc_2534_;
goto v_reusejp_2532_;
}
v_reusejp_2532_:
{
return v___x_2533_;
}
}
}
}
}
else
{
lean_object* v_ks_2561_; lean_object* v_vs_2562_; lean_object* v___x_2564_; uint8_t v_isShared_2565_; uint8_t v_isSharedCheck_2582_; 
v_ks_2561_ = lean_ctor_get(v_x_2510_, 0);
v_vs_2562_ = lean_ctor_get(v_x_2510_, 1);
v_isSharedCheck_2582_ = !lean_is_exclusive(v_x_2510_);
if (v_isSharedCheck_2582_ == 0)
{
v___x_2564_ = v_x_2510_;
v_isShared_2565_ = v_isSharedCheck_2582_;
goto v_resetjp_2563_;
}
else
{
lean_inc(v_vs_2562_);
lean_inc(v_ks_2561_);
lean_dec(v_x_2510_);
v___x_2564_ = lean_box(0);
v_isShared_2565_ = v_isSharedCheck_2582_;
goto v_resetjp_2563_;
}
v_resetjp_2563_:
{
lean_object* v___x_2567_; 
if (v_isShared_2565_ == 0)
{
v___x_2567_ = v___x_2564_;
goto v_reusejp_2566_;
}
else
{
lean_object* v_reuseFailAlloc_2581_; 
v_reuseFailAlloc_2581_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2581_, 0, v_ks_2561_);
lean_ctor_set(v_reuseFailAlloc_2581_, 1, v_vs_2562_);
v___x_2567_ = v_reuseFailAlloc_2581_;
goto v_reusejp_2566_;
}
v_reusejp_2566_:
{
lean_object* v_newNode_2568_; uint8_t v___y_2570_; size_t v___x_2576_; uint8_t v___x_2577_; 
v_newNode_2568_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0_spec__1___redArg(v___x_2567_, v_x_2513_, v_x_2514_);
v___x_2576_ = ((size_t)7ULL);
v___x_2577_ = lean_usize_dec_le(v___x_2576_, v_x_2512_);
if (v___x_2577_ == 0)
{
lean_object* v___x_2578_; lean_object* v___x_2579_; uint8_t v___x_2580_; 
v___x_2578_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2568_);
v___x_2579_ = lean_unsigned_to_nat(4u);
v___x_2580_ = lean_nat_dec_lt(v___x_2578_, v___x_2579_);
lean_dec(v___x_2578_);
v___y_2570_ = v___x_2580_;
goto v___jp_2569_;
}
else
{
v___y_2570_ = v___x_2577_;
goto v___jp_2569_;
}
v___jp_2569_:
{
if (v___y_2570_ == 0)
{
lean_object* v_ks_2571_; lean_object* v_vs_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; 
v_ks_2571_ = lean_ctor_get(v_newNode_2568_, 0);
lean_inc_ref(v_ks_2571_);
v_vs_2572_ = lean_ctor_get(v_newNode_2568_, 1);
lean_inc_ref(v_vs_2572_);
lean_dec_ref(v_newNode_2568_);
v___x_2573_ = lean_unsigned_to_nat(0u);
v___x_2574_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg___closed__2);
v___x_2575_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0_spec__2___redArg(v_x_2512_, v_ks_2571_, v_vs_2572_, v___x_2573_, v___x_2574_);
lean_dec_ref(v_vs_2572_);
lean_dec_ref(v_ks_2571_);
return v___x_2575_;
}
else
{
return v_newNode_2568_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0_spec__2___redArg(size_t v_depth_2583_, lean_object* v_keys_2584_, lean_object* v_vals_2585_, lean_object* v_i_2586_, lean_object* v_entries_2587_){
_start:
{
lean_object* v___x_2588_; uint8_t v___x_2589_; 
v___x_2588_ = lean_array_get_size(v_keys_2584_);
v___x_2589_ = lean_nat_dec_lt(v_i_2586_, v___x_2588_);
if (v___x_2589_ == 0)
{
lean_dec(v_i_2586_);
return v_entries_2587_;
}
else
{
lean_object* v_k_2590_; lean_object* v_v_2591_; uint64_t v___x_2592_; size_t v_h_2593_; size_t v___x_2594_; lean_object* v___x_2595_; size_t v___x_2596_; size_t v___x_2597_; size_t v___x_2598_; size_t v_h_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; 
v_k_2590_ = lean_array_fget_borrowed(v_keys_2584_, v_i_2586_);
v_v_2591_ = lean_array_fget_borrowed(v_vals_2585_, v_i_2586_);
v___x_2592_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_k_2590_);
v_h_2593_ = lean_uint64_to_usize(v___x_2592_);
v___x_2594_ = ((size_t)5ULL);
v___x_2595_ = lean_unsigned_to_nat(1u);
v___x_2596_ = ((size_t)1ULL);
v___x_2597_ = lean_usize_sub(v_depth_2583_, v___x_2596_);
v___x_2598_ = lean_usize_mul(v___x_2594_, v___x_2597_);
v_h_2599_ = lean_usize_shift_right(v_h_2593_, v___x_2598_);
v___x_2600_ = lean_nat_add(v_i_2586_, v___x_2595_);
lean_dec(v_i_2586_);
lean_inc(v_v_2591_);
lean_inc(v_k_2590_);
v___x_2601_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0___redArg(v_entries_2587_, v_h_2599_, v_depth_2583_, v_k_2590_, v_v_2591_);
v_i_2586_ = v___x_2600_;
v_entries_2587_ = v___x_2601_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_2603_, lean_object* v_keys_2604_, lean_object* v_vals_2605_, lean_object* v_i_2606_, lean_object* v_entries_2607_){
_start:
{
size_t v_depth_boxed_2608_; lean_object* v_res_2609_; 
v_depth_boxed_2608_ = lean_unbox_usize(v_depth_2603_);
lean_dec(v_depth_2603_);
v_res_2609_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0_spec__2___redArg(v_depth_boxed_2608_, v_keys_2604_, v_vals_2605_, v_i_2606_, v_entries_2607_);
lean_dec_ref(v_vals_2605_);
lean_dec_ref(v_keys_2604_);
return v_res_2609_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0___redArg___boxed(lean_object* v_x_2610_, lean_object* v_x_2611_, lean_object* v_x_2612_, lean_object* v_x_2613_, lean_object* v_x_2614_){
_start:
{
size_t v_x_213035__boxed_2615_; size_t v_x_213036__boxed_2616_; lean_object* v_res_2617_; 
v_x_213035__boxed_2615_ = lean_unbox_usize(v_x_2611_);
lean_dec(v_x_2611_);
v_x_213036__boxed_2616_ = lean_unbox_usize(v_x_2612_);
lean_dec(v_x_2612_);
v_res_2617_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0___redArg(v_x_2610_, v_x_213035__boxed_2615_, v_x_213036__boxed_2616_, v_x_2613_, v_x_2614_);
return v_res_2617_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0___redArg(lean_object* v_x_2618_, lean_object* v_x_2619_, lean_object* v_x_2620_){
_start:
{
uint64_t v___x_2621_; size_t v___x_2622_; size_t v___x_2623_; lean_object* v___x_2624_; 
v___x_2621_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_2619_);
v___x_2622_ = lean_uint64_to_usize(v___x_2621_);
v___x_2623_ = ((size_t)1ULL);
v___x_2624_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0___redArg(v_x_2618_, v___x_2622_, v___x_2623_, v_x_2619_, v_x_2620_);
return v___x_2624_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_internalize___lam__0(lean_object* v_e_2625_, lean_object* v_val_2626_, lean_object* v_s_2627_){
_start:
{
lean_object* v_toRing_2628_; lean_object* v_invFn_x3f_2629_; lean_object* v_semiringId_x3f_2630_; lean_object* v_commSemiringInst_2631_; lean_object* v_commRingInst_2632_; lean_object* v_noZeroDivInst_x3f_2633_; lean_object* v_fieldInst_x3f_2634_; lean_object* v_denoteEntries_2635_; lean_object* v_nextId_2636_; lean_object* v_steps_2637_; lean_object* v_queue_2638_; lean_object* v_basis_2639_; lean_object* v_diseqs_2640_; uint8_t v_recheck_2641_; lean_object* v_invSet_2642_; lean_object* v_numEq0_x3f_2643_; uint8_t v_numEq0Updated_2644_; lean_object* v___x_2646_; uint8_t v_isShared_2647_; uint8_t v_isSharedCheck_2678_; 
v_toRing_2628_ = lean_ctor_get(v_s_2627_, 0);
v_invFn_x3f_2629_ = lean_ctor_get(v_s_2627_, 1);
v_semiringId_x3f_2630_ = lean_ctor_get(v_s_2627_, 2);
v_commSemiringInst_2631_ = lean_ctor_get(v_s_2627_, 3);
v_commRingInst_2632_ = lean_ctor_get(v_s_2627_, 4);
v_noZeroDivInst_x3f_2633_ = lean_ctor_get(v_s_2627_, 5);
v_fieldInst_x3f_2634_ = lean_ctor_get(v_s_2627_, 6);
v_denoteEntries_2635_ = lean_ctor_get(v_s_2627_, 7);
v_nextId_2636_ = lean_ctor_get(v_s_2627_, 8);
v_steps_2637_ = lean_ctor_get(v_s_2627_, 9);
v_queue_2638_ = lean_ctor_get(v_s_2627_, 10);
v_basis_2639_ = lean_ctor_get(v_s_2627_, 11);
v_diseqs_2640_ = lean_ctor_get(v_s_2627_, 12);
v_recheck_2641_ = lean_ctor_get_uint8(v_s_2627_, sizeof(void*)*15);
v_invSet_2642_ = lean_ctor_get(v_s_2627_, 13);
v_numEq0_x3f_2643_ = lean_ctor_get(v_s_2627_, 14);
v_numEq0Updated_2644_ = lean_ctor_get_uint8(v_s_2627_, sizeof(void*)*15 + 1);
v_isSharedCheck_2678_ = !lean_is_exclusive(v_s_2627_);
if (v_isSharedCheck_2678_ == 0)
{
v___x_2646_ = v_s_2627_;
v_isShared_2647_ = v_isSharedCheck_2678_;
goto v_resetjp_2645_;
}
else
{
lean_inc(v_numEq0_x3f_2643_);
lean_inc(v_invSet_2642_);
lean_inc(v_diseqs_2640_);
lean_inc(v_basis_2639_);
lean_inc(v_queue_2638_);
lean_inc(v_steps_2637_);
lean_inc(v_nextId_2636_);
lean_inc(v_denoteEntries_2635_);
lean_inc(v_fieldInst_x3f_2634_);
lean_inc(v_noZeroDivInst_x3f_2633_);
lean_inc(v_commRingInst_2632_);
lean_inc(v_commSemiringInst_2631_);
lean_inc(v_semiringId_x3f_2630_);
lean_inc(v_invFn_x3f_2629_);
lean_inc(v_toRing_2628_);
lean_dec(v_s_2627_);
v___x_2646_ = lean_box(0);
v_isShared_2647_ = v_isSharedCheck_2678_;
goto v_resetjp_2645_;
}
v_resetjp_2645_:
{
lean_object* v_id_2648_; lean_object* v_type_2649_; lean_object* v_u_2650_; lean_object* v_ringInst_2651_; lean_object* v_semiringInst_2652_; lean_object* v_charInst_x3f_2653_; lean_object* v_addFn_x3f_2654_; lean_object* v_mulFn_x3f_2655_; lean_object* v_subFn_x3f_2656_; lean_object* v_negFn_x3f_2657_; lean_object* v_powFn_x3f_2658_; lean_object* v_intCastFn_x3f_2659_; lean_object* v_natCastFn_x3f_2660_; lean_object* v_one_x3f_2661_; lean_object* v_vars_2662_; lean_object* v_varMap_2663_; lean_object* v_denote_2664_; lean_object* v___x_2666_; uint8_t v_isShared_2667_; uint8_t v_isSharedCheck_2677_; 
v_id_2648_ = lean_ctor_get(v_toRing_2628_, 0);
v_type_2649_ = lean_ctor_get(v_toRing_2628_, 1);
v_u_2650_ = lean_ctor_get(v_toRing_2628_, 2);
v_ringInst_2651_ = lean_ctor_get(v_toRing_2628_, 3);
v_semiringInst_2652_ = lean_ctor_get(v_toRing_2628_, 4);
v_charInst_x3f_2653_ = lean_ctor_get(v_toRing_2628_, 5);
v_addFn_x3f_2654_ = lean_ctor_get(v_toRing_2628_, 6);
v_mulFn_x3f_2655_ = lean_ctor_get(v_toRing_2628_, 7);
v_subFn_x3f_2656_ = lean_ctor_get(v_toRing_2628_, 8);
v_negFn_x3f_2657_ = lean_ctor_get(v_toRing_2628_, 9);
v_powFn_x3f_2658_ = lean_ctor_get(v_toRing_2628_, 10);
v_intCastFn_x3f_2659_ = lean_ctor_get(v_toRing_2628_, 11);
v_natCastFn_x3f_2660_ = lean_ctor_get(v_toRing_2628_, 12);
v_one_x3f_2661_ = lean_ctor_get(v_toRing_2628_, 13);
v_vars_2662_ = lean_ctor_get(v_toRing_2628_, 14);
v_varMap_2663_ = lean_ctor_get(v_toRing_2628_, 15);
v_denote_2664_ = lean_ctor_get(v_toRing_2628_, 16);
v_isSharedCheck_2677_ = !lean_is_exclusive(v_toRing_2628_);
if (v_isSharedCheck_2677_ == 0)
{
v___x_2666_ = v_toRing_2628_;
v_isShared_2667_ = v_isSharedCheck_2677_;
goto v_resetjp_2665_;
}
else
{
lean_inc(v_denote_2664_);
lean_inc(v_varMap_2663_);
lean_inc(v_vars_2662_);
lean_inc(v_one_x3f_2661_);
lean_inc(v_natCastFn_x3f_2660_);
lean_inc(v_intCastFn_x3f_2659_);
lean_inc(v_powFn_x3f_2658_);
lean_inc(v_negFn_x3f_2657_);
lean_inc(v_subFn_x3f_2656_);
lean_inc(v_mulFn_x3f_2655_);
lean_inc(v_addFn_x3f_2654_);
lean_inc(v_charInst_x3f_2653_);
lean_inc(v_semiringInst_2652_);
lean_inc(v_ringInst_2651_);
lean_inc(v_u_2650_);
lean_inc(v_type_2649_);
lean_inc(v_id_2648_);
lean_dec(v_toRing_2628_);
v___x_2666_ = lean_box(0);
v_isShared_2667_ = v_isSharedCheck_2677_;
goto v_resetjp_2665_;
}
v_resetjp_2665_:
{
lean_object* v___x_2668_; lean_object* v___x_2670_; 
lean_inc_ref(v_val_2626_);
lean_inc_ref(v_e_2625_);
v___x_2668_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0___redArg(v_denote_2664_, v_e_2625_, v_val_2626_);
if (v_isShared_2667_ == 0)
{
lean_ctor_set(v___x_2666_, 16, v___x_2668_);
v___x_2670_ = v___x_2666_;
goto v_reusejp_2669_;
}
else
{
lean_object* v_reuseFailAlloc_2676_; 
v_reuseFailAlloc_2676_ = lean_alloc_ctor(0, 17, 0);
lean_ctor_set(v_reuseFailAlloc_2676_, 0, v_id_2648_);
lean_ctor_set(v_reuseFailAlloc_2676_, 1, v_type_2649_);
lean_ctor_set(v_reuseFailAlloc_2676_, 2, v_u_2650_);
lean_ctor_set(v_reuseFailAlloc_2676_, 3, v_ringInst_2651_);
lean_ctor_set(v_reuseFailAlloc_2676_, 4, v_semiringInst_2652_);
lean_ctor_set(v_reuseFailAlloc_2676_, 5, v_charInst_x3f_2653_);
lean_ctor_set(v_reuseFailAlloc_2676_, 6, v_addFn_x3f_2654_);
lean_ctor_set(v_reuseFailAlloc_2676_, 7, v_mulFn_x3f_2655_);
lean_ctor_set(v_reuseFailAlloc_2676_, 8, v_subFn_x3f_2656_);
lean_ctor_set(v_reuseFailAlloc_2676_, 9, v_negFn_x3f_2657_);
lean_ctor_set(v_reuseFailAlloc_2676_, 10, v_powFn_x3f_2658_);
lean_ctor_set(v_reuseFailAlloc_2676_, 11, v_intCastFn_x3f_2659_);
lean_ctor_set(v_reuseFailAlloc_2676_, 12, v_natCastFn_x3f_2660_);
lean_ctor_set(v_reuseFailAlloc_2676_, 13, v_one_x3f_2661_);
lean_ctor_set(v_reuseFailAlloc_2676_, 14, v_vars_2662_);
lean_ctor_set(v_reuseFailAlloc_2676_, 15, v_varMap_2663_);
lean_ctor_set(v_reuseFailAlloc_2676_, 16, v___x_2668_);
v___x_2670_ = v_reuseFailAlloc_2676_;
goto v_reusejp_2669_;
}
v_reusejp_2669_:
{
lean_object* v___x_2671_; lean_object* v___x_2672_; lean_object* v___x_2674_; 
v___x_2671_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2671_, 0, v_e_2625_);
lean_ctor_set(v___x_2671_, 1, v_val_2626_);
v___x_2672_ = l_Lean_PersistentArray_push___redArg(v_denoteEntries_2635_, v___x_2671_);
if (v_isShared_2647_ == 0)
{
lean_ctor_set(v___x_2646_, 7, v___x_2672_);
lean_ctor_set(v___x_2646_, 0, v___x_2670_);
v___x_2674_ = v___x_2646_;
goto v_reusejp_2673_;
}
else
{
lean_object* v_reuseFailAlloc_2675_; 
v_reuseFailAlloc_2675_ = lean_alloc_ctor(0, 15, 2);
lean_ctor_set(v_reuseFailAlloc_2675_, 0, v___x_2670_);
lean_ctor_set(v_reuseFailAlloc_2675_, 1, v_invFn_x3f_2629_);
lean_ctor_set(v_reuseFailAlloc_2675_, 2, v_semiringId_x3f_2630_);
lean_ctor_set(v_reuseFailAlloc_2675_, 3, v_commSemiringInst_2631_);
lean_ctor_set(v_reuseFailAlloc_2675_, 4, v_commRingInst_2632_);
lean_ctor_set(v_reuseFailAlloc_2675_, 5, v_noZeroDivInst_x3f_2633_);
lean_ctor_set(v_reuseFailAlloc_2675_, 6, v_fieldInst_x3f_2634_);
lean_ctor_set(v_reuseFailAlloc_2675_, 7, v___x_2672_);
lean_ctor_set(v_reuseFailAlloc_2675_, 8, v_nextId_2636_);
lean_ctor_set(v_reuseFailAlloc_2675_, 9, v_steps_2637_);
lean_ctor_set(v_reuseFailAlloc_2675_, 10, v_queue_2638_);
lean_ctor_set(v_reuseFailAlloc_2675_, 11, v_basis_2639_);
lean_ctor_set(v_reuseFailAlloc_2675_, 12, v_diseqs_2640_);
lean_ctor_set(v_reuseFailAlloc_2675_, 13, v_invSet_2642_);
lean_ctor_set(v_reuseFailAlloc_2675_, 14, v_numEq0_x3f_2643_);
lean_ctor_set_uint8(v_reuseFailAlloc_2675_, sizeof(void*)*15, v_recheck_2641_);
lean_ctor_set_uint8(v_reuseFailAlloc_2675_, sizeof(void*)*15 + 1, v_numEq0Updated_2644_);
v___x_2674_ = v_reuseFailAlloc_2675_;
goto v_reusejp_2673_;
}
v_reusejp_2673_:
{
return v___x_2674_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_internalize___lam__1(lean_object* v___y_2679_, lean_object* v_e_2680_, lean_object* v_val_2681_, lean_object* v_s_2682_){
_start:
{
lean_object* v_rings_2683_; lean_object* v_typeIdOf_2684_; lean_object* v_exprToRingId_2685_; lean_object* v_semirings_2686_; lean_object* v_stypeIdOf_2687_; lean_object* v_exprToSemiringId_2688_; lean_object* v_ncRings_2689_; lean_object* v_exprToNCRingId_2690_; lean_object* v_nctypeIdOf_2691_; lean_object* v_ncSemirings_2692_; lean_object* v_exprToNCSemiringId_2693_; lean_object* v_ncstypeIdOf_2694_; lean_object* v_steps_2695_; lean_object* v___x_2696_; uint8_t v___x_2697_; 
v_rings_2683_ = lean_ctor_get(v_s_2682_, 0);
v_typeIdOf_2684_ = lean_ctor_get(v_s_2682_, 1);
v_exprToRingId_2685_ = lean_ctor_get(v_s_2682_, 2);
v_semirings_2686_ = lean_ctor_get(v_s_2682_, 3);
v_stypeIdOf_2687_ = lean_ctor_get(v_s_2682_, 4);
v_exprToSemiringId_2688_ = lean_ctor_get(v_s_2682_, 5);
v_ncRings_2689_ = lean_ctor_get(v_s_2682_, 6);
v_exprToNCRingId_2690_ = lean_ctor_get(v_s_2682_, 7);
v_nctypeIdOf_2691_ = lean_ctor_get(v_s_2682_, 8);
v_ncSemirings_2692_ = lean_ctor_get(v_s_2682_, 9);
v_exprToNCSemiringId_2693_ = lean_ctor_get(v_s_2682_, 10);
v_ncstypeIdOf_2694_ = lean_ctor_get(v_s_2682_, 11);
v_steps_2695_ = lean_ctor_get(v_s_2682_, 12);
v___x_2696_ = lean_array_get_size(v_semirings_2686_);
v___x_2697_ = lean_nat_dec_lt(v___y_2679_, v___x_2696_);
if (v___x_2697_ == 0)
{
lean_dec_ref(v_val_2681_);
lean_dec_ref(v_e_2680_);
return v_s_2682_;
}
else
{
lean_object* v___x_2699_; uint8_t v_isShared_2700_; uint8_t v_isSharedCheck_2739_; 
lean_inc(v_steps_2695_);
lean_inc_ref(v_ncstypeIdOf_2694_);
lean_inc_ref(v_exprToNCSemiringId_2693_);
lean_inc_ref(v_ncSemirings_2692_);
lean_inc_ref(v_nctypeIdOf_2691_);
lean_inc_ref(v_exprToNCRingId_2690_);
lean_inc_ref(v_ncRings_2689_);
lean_inc_ref(v_exprToSemiringId_2688_);
lean_inc_ref(v_stypeIdOf_2687_);
lean_inc_ref(v_semirings_2686_);
lean_inc_ref(v_exprToRingId_2685_);
lean_inc_ref(v_typeIdOf_2684_);
lean_inc_ref(v_rings_2683_);
v_isSharedCheck_2739_ = !lean_is_exclusive(v_s_2682_);
if (v_isSharedCheck_2739_ == 0)
{
lean_object* v_unused_2740_; lean_object* v_unused_2741_; lean_object* v_unused_2742_; lean_object* v_unused_2743_; lean_object* v_unused_2744_; lean_object* v_unused_2745_; lean_object* v_unused_2746_; lean_object* v_unused_2747_; lean_object* v_unused_2748_; lean_object* v_unused_2749_; lean_object* v_unused_2750_; lean_object* v_unused_2751_; lean_object* v_unused_2752_; 
v_unused_2740_ = lean_ctor_get(v_s_2682_, 12);
lean_dec(v_unused_2740_);
v_unused_2741_ = lean_ctor_get(v_s_2682_, 11);
lean_dec(v_unused_2741_);
v_unused_2742_ = lean_ctor_get(v_s_2682_, 10);
lean_dec(v_unused_2742_);
v_unused_2743_ = lean_ctor_get(v_s_2682_, 9);
lean_dec(v_unused_2743_);
v_unused_2744_ = lean_ctor_get(v_s_2682_, 8);
lean_dec(v_unused_2744_);
v_unused_2745_ = lean_ctor_get(v_s_2682_, 7);
lean_dec(v_unused_2745_);
v_unused_2746_ = lean_ctor_get(v_s_2682_, 6);
lean_dec(v_unused_2746_);
v_unused_2747_ = lean_ctor_get(v_s_2682_, 5);
lean_dec(v_unused_2747_);
v_unused_2748_ = lean_ctor_get(v_s_2682_, 4);
lean_dec(v_unused_2748_);
v_unused_2749_ = lean_ctor_get(v_s_2682_, 3);
lean_dec(v_unused_2749_);
v_unused_2750_ = lean_ctor_get(v_s_2682_, 2);
lean_dec(v_unused_2750_);
v_unused_2751_ = lean_ctor_get(v_s_2682_, 1);
lean_dec(v_unused_2751_);
v_unused_2752_ = lean_ctor_get(v_s_2682_, 0);
lean_dec(v_unused_2752_);
v___x_2699_ = v_s_2682_;
v_isShared_2700_ = v_isSharedCheck_2739_;
goto v_resetjp_2698_;
}
else
{
lean_dec(v_s_2682_);
v___x_2699_ = lean_box(0);
v_isShared_2700_ = v_isSharedCheck_2739_;
goto v_resetjp_2698_;
}
v_resetjp_2698_:
{
lean_object* v_v_2701_; lean_object* v_toSemiring_2702_; lean_object* v_ringId_2703_; lean_object* v_commSemiringInst_2704_; lean_object* v_addRightCancelInst_x3f_2705_; lean_object* v_toQFn_x3f_2706_; lean_object* v___x_2708_; uint8_t v_isShared_2709_; uint8_t v_isSharedCheck_2738_; 
v_v_2701_ = lean_array_fget(v_semirings_2686_, v___y_2679_);
v_toSemiring_2702_ = lean_ctor_get(v_v_2701_, 0);
v_ringId_2703_ = lean_ctor_get(v_v_2701_, 1);
v_commSemiringInst_2704_ = lean_ctor_get(v_v_2701_, 2);
v_addRightCancelInst_x3f_2705_ = lean_ctor_get(v_v_2701_, 3);
v_toQFn_x3f_2706_ = lean_ctor_get(v_v_2701_, 4);
v_isSharedCheck_2738_ = !lean_is_exclusive(v_v_2701_);
if (v_isSharedCheck_2738_ == 0)
{
v___x_2708_ = v_v_2701_;
v_isShared_2709_ = v_isSharedCheck_2738_;
goto v_resetjp_2707_;
}
else
{
lean_inc(v_toQFn_x3f_2706_);
lean_inc(v_addRightCancelInst_x3f_2705_);
lean_inc(v_commSemiringInst_2704_);
lean_inc(v_ringId_2703_);
lean_inc(v_toSemiring_2702_);
lean_dec(v_v_2701_);
v___x_2708_ = lean_box(0);
v_isShared_2709_ = v_isSharedCheck_2738_;
goto v_resetjp_2707_;
}
v_resetjp_2707_:
{
lean_object* v_id_2710_; lean_object* v_type_2711_; lean_object* v_u_2712_; lean_object* v_semiringInst_2713_; lean_object* v_addFn_x3f_2714_; lean_object* v_mulFn_x3f_2715_; lean_object* v_powFn_x3f_2716_; lean_object* v_natCastFn_x3f_2717_; lean_object* v_denote_2718_; lean_object* v_vars_2719_; lean_object* v_varMap_2720_; lean_object* v___x_2722_; uint8_t v_isShared_2723_; uint8_t v_isSharedCheck_2737_; 
v_id_2710_ = lean_ctor_get(v_toSemiring_2702_, 0);
v_type_2711_ = lean_ctor_get(v_toSemiring_2702_, 1);
v_u_2712_ = lean_ctor_get(v_toSemiring_2702_, 2);
v_semiringInst_2713_ = lean_ctor_get(v_toSemiring_2702_, 3);
v_addFn_x3f_2714_ = lean_ctor_get(v_toSemiring_2702_, 4);
v_mulFn_x3f_2715_ = lean_ctor_get(v_toSemiring_2702_, 5);
v_powFn_x3f_2716_ = lean_ctor_get(v_toSemiring_2702_, 6);
v_natCastFn_x3f_2717_ = lean_ctor_get(v_toSemiring_2702_, 7);
v_denote_2718_ = lean_ctor_get(v_toSemiring_2702_, 8);
v_vars_2719_ = lean_ctor_get(v_toSemiring_2702_, 9);
v_varMap_2720_ = lean_ctor_get(v_toSemiring_2702_, 10);
v_isSharedCheck_2737_ = !lean_is_exclusive(v_toSemiring_2702_);
if (v_isSharedCheck_2737_ == 0)
{
v___x_2722_ = v_toSemiring_2702_;
v_isShared_2723_ = v_isSharedCheck_2737_;
goto v_resetjp_2721_;
}
else
{
lean_inc(v_varMap_2720_);
lean_inc(v_vars_2719_);
lean_inc(v_denote_2718_);
lean_inc(v_natCastFn_x3f_2717_);
lean_inc(v_powFn_x3f_2716_);
lean_inc(v_mulFn_x3f_2715_);
lean_inc(v_addFn_x3f_2714_);
lean_inc(v_semiringInst_2713_);
lean_inc(v_u_2712_);
lean_inc(v_type_2711_);
lean_inc(v_id_2710_);
lean_dec(v_toSemiring_2702_);
v___x_2722_ = lean_box(0);
v_isShared_2723_ = v_isSharedCheck_2737_;
goto v_resetjp_2721_;
}
v_resetjp_2721_:
{
lean_object* v___x_2724_; lean_object* v_xs_x27_2725_; lean_object* v___x_2726_; lean_object* v___x_2728_; 
v___x_2724_ = lean_box(0);
v_xs_x27_2725_ = lean_array_fset(v_semirings_2686_, v___y_2679_, v___x_2724_);
v___x_2726_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0___redArg(v_denote_2718_, v_e_2680_, v_val_2681_);
if (v_isShared_2723_ == 0)
{
lean_ctor_set(v___x_2722_, 8, v___x_2726_);
v___x_2728_ = v___x_2722_;
goto v_reusejp_2727_;
}
else
{
lean_object* v_reuseFailAlloc_2736_; 
v_reuseFailAlloc_2736_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_2736_, 0, v_id_2710_);
lean_ctor_set(v_reuseFailAlloc_2736_, 1, v_type_2711_);
lean_ctor_set(v_reuseFailAlloc_2736_, 2, v_u_2712_);
lean_ctor_set(v_reuseFailAlloc_2736_, 3, v_semiringInst_2713_);
lean_ctor_set(v_reuseFailAlloc_2736_, 4, v_addFn_x3f_2714_);
lean_ctor_set(v_reuseFailAlloc_2736_, 5, v_mulFn_x3f_2715_);
lean_ctor_set(v_reuseFailAlloc_2736_, 6, v_powFn_x3f_2716_);
lean_ctor_set(v_reuseFailAlloc_2736_, 7, v_natCastFn_x3f_2717_);
lean_ctor_set(v_reuseFailAlloc_2736_, 8, v___x_2726_);
lean_ctor_set(v_reuseFailAlloc_2736_, 9, v_vars_2719_);
lean_ctor_set(v_reuseFailAlloc_2736_, 10, v_varMap_2720_);
v___x_2728_ = v_reuseFailAlloc_2736_;
goto v_reusejp_2727_;
}
v_reusejp_2727_:
{
lean_object* v___x_2730_; 
if (v_isShared_2709_ == 0)
{
lean_ctor_set(v___x_2708_, 0, v___x_2728_);
v___x_2730_ = v___x_2708_;
goto v_reusejp_2729_;
}
else
{
lean_object* v_reuseFailAlloc_2735_; 
v_reuseFailAlloc_2735_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2735_, 0, v___x_2728_);
lean_ctor_set(v_reuseFailAlloc_2735_, 1, v_ringId_2703_);
lean_ctor_set(v_reuseFailAlloc_2735_, 2, v_commSemiringInst_2704_);
lean_ctor_set(v_reuseFailAlloc_2735_, 3, v_addRightCancelInst_x3f_2705_);
lean_ctor_set(v_reuseFailAlloc_2735_, 4, v_toQFn_x3f_2706_);
v___x_2730_ = v_reuseFailAlloc_2735_;
goto v_reusejp_2729_;
}
v_reusejp_2729_:
{
lean_object* v___x_2731_; lean_object* v___x_2733_; 
v___x_2731_ = lean_array_fset(v_xs_x27_2725_, v___y_2679_, v___x_2730_);
if (v_isShared_2700_ == 0)
{
lean_ctor_set(v___x_2699_, 3, v___x_2731_);
v___x_2733_ = v___x_2699_;
goto v_reusejp_2732_;
}
else
{
lean_object* v_reuseFailAlloc_2734_; 
v_reuseFailAlloc_2734_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_2734_, 0, v_rings_2683_);
lean_ctor_set(v_reuseFailAlloc_2734_, 1, v_typeIdOf_2684_);
lean_ctor_set(v_reuseFailAlloc_2734_, 2, v_exprToRingId_2685_);
lean_ctor_set(v_reuseFailAlloc_2734_, 3, v___x_2731_);
lean_ctor_set(v_reuseFailAlloc_2734_, 4, v_stypeIdOf_2687_);
lean_ctor_set(v_reuseFailAlloc_2734_, 5, v_exprToSemiringId_2688_);
lean_ctor_set(v_reuseFailAlloc_2734_, 6, v_ncRings_2689_);
lean_ctor_set(v_reuseFailAlloc_2734_, 7, v_exprToNCRingId_2690_);
lean_ctor_set(v_reuseFailAlloc_2734_, 8, v_nctypeIdOf_2691_);
lean_ctor_set(v_reuseFailAlloc_2734_, 9, v_ncSemirings_2692_);
lean_ctor_set(v_reuseFailAlloc_2734_, 10, v_exprToNCSemiringId_2693_);
lean_ctor_set(v_reuseFailAlloc_2734_, 11, v_ncstypeIdOf_2694_);
lean_ctor_set(v_reuseFailAlloc_2734_, 12, v_steps_2695_);
v___x_2733_ = v_reuseFailAlloc_2734_;
goto v_reusejp_2732_;
}
v_reusejp_2732_:
{
return v___x_2733_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_internalize___lam__1___boxed(lean_object* v___y_2753_, lean_object* v_e_2754_, lean_object* v_val_2755_, lean_object* v_s_2756_){
_start:
{
lean_object* v_res_2757_; 
v_res_2757_ = l_Lean_Meta_Grind_Arith_CommRing_internalize___lam__1(v___y_2753_, v_e_2754_, v_val_2755_, v_s_2756_);
lean_dec(v___y_2753_);
return v_res_2757_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_internalize___lam__2(lean_object* v_e_2758_, lean_object* v_val_2759_, lean_object* v_s_2760_){
_start:
{
lean_object* v_id_2761_; lean_object* v_type_2762_; lean_object* v_u_2763_; lean_object* v_ringInst_2764_; lean_object* v_semiringInst_2765_; lean_object* v_charInst_x3f_2766_; lean_object* v_addFn_x3f_2767_; lean_object* v_mulFn_x3f_2768_; lean_object* v_subFn_x3f_2769_; lean_object* v_negFn_x3f_2770_; lean_object* v_powFn_x3f_2771_; lean_object* v_intCastFn_x3f_2772_; lean_object* v_natCastFn_x3f_2773_; lean_object* v_one_x3f_2774_; lean_object* v_vars_2775_; lean_object* v_varMap_2776_; lean_object* v_denote_2777_; lean_object* v___x_2779_; uint8_t v_isShared_2780_; uint8_t v_isSharedCheck_2785_; 
v_id_2761_ = lean_ctor_get(v_s_2760_, 0);
v_type_2762_ = lean_ctor_get(v_s_2760_, 1);
v_u_2763_ = lean_ctor_get(v_s_2760_, 2);
v_ringInst_2764_ = lean_ctor_get(v_s_2760_, 3);
v_semiringInst_2765_ = lean_ctor_get(v_s_2760_, 4);
v_charInst_x3f_2766_ = lean_ctor_get(v_s_2760_, 5);
v_addFn_x3f_2767_ = lean_ctor_get(v_s_2760_, 6);
v_mulFn_x3f_2768_ = lean_ctor_get(v_s_2760_, 7);
v_subFn_x3f_2769_ = lean_ctor_get(v_s_2760_, 8);
v_negFn_x3f_2770_ = lean_ctor_get(v_s_2760_, 9);
v_powFn_x3f_2771_ = lean_ctor_get(v_s_2760_, 10);
v_intCastFn_x3f_2772_ = lean_ctor_get(v_s_2760_, 11);
v_natCastFn_x3f_2773_ = lean_ctor_get(v_s_2760_, 12);
v_one_x3f_2774_ = lean_ctor_get(v_s_2760_, 13);
v_vars_2775_ = lean_ctor_get(v_s_2760_, 14);
v_varMap_2776_ = lean_ctor_get(v_s_2760_, 15);
v_denote_2777_ = lean_ctor_get(v_s_2760_, 16);
v_isSharedCheck_2785_ = !lean_is_exclusive(v_s_2760_);
if (v_isSharedCheck_2785_ == 0)
{
v___x_2779_ = v_s_2760_;
v_isShared_2780_ = v_isSharedCheck_2785_;
goto v_resetjp_2778_;
}
else
{
lean_inc(v_denote_2777_);
lean_inc(v_varMap_2776_);
lean_inc(v_vars_2775_);
lean_inc(v_one_x3f_2774_);
lean_inc(v_natCastFn_x3f_2773_);
lean_inc(v_intCastFn_x3f_2772_);
lean_inc(v_powFn_x3f_2771_);
lean_inc(v_negFn_x3f_2770_);
lean_inc(v_subFn_x3f_2769_);
lean_inc(v_mulFn_x3f_2768_);
lean_inc(v_addFn_x3f_2767_);
lean_inc(v_charInst_x3f_2766_);
lean_inc(v_semiringInst_2765_);
lean_inc(v_ringInst_2764_);
lean_inc(v_u_2763_);
lean_inc(v_type_2762_);
lean_inc(v_id_2761_);
lean_dec(v_s_2760_);
v___x_2779_ = lean_box(0);
v_isShared_2780_ = v_isSharedCheck_2785_;
goto v_resetjp_2778_;
}
v_resetjp_2778_:
{
lean_object* v___x_2781_; lean_object* v___x_2783_; 
v___x_2781_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0___redArg(v_denote_2777_, v_e_2758_, v_val_2759_);
if (v_isShared_2780_ == 0)
{
lean_ctor_set(v___x_2779_, 16, v___x_2781_);
v___x_2783_ = v___x_2779_;
goto v_reusejp_2782_;
}
else
{
lean_object* v_reuseFailAlloc_2784_; 
v_reuseFailAlloc_2784_ = lean_alloc_ctor(0, 17, 0);
lean_ctor_set(v_reuseFailAlloc_2784_, 0, v_id_2761_);
lean_ctor_set(v_reuseFailAlloc_2784_, 1, v_type_2762_);
lean_ctor_set(v_reuseFailAlloc_2784_, 2, v_u_2763_);
lean_ctor_set(v_reuseFailAlloc_2784_, 3, v_ringInst_2764_);
lean_ctor_set(v_reuseFailAlloc_2784_, 4, v_semiringInst_2765_);
lean_ctor_set(v_reuseFailAlloc_2784_, 5, v_charInst_x3f_2766_);
lean_ctor_set(v_reuseFailAlloc_2784_, 6, v_addFn_x3f_2767_);
lean_ctor_set(v_reuseFailAlloc_2784_, 7, v_mulFn_x3f_2768_);
lean_ctor_set(v_reuseFailAlloc_2784_, 8, v_subFn_x3f_2769_);
lean_ctor_set(v_reuseFailAlloc_2784_, 9, v_negFn_x3f_2770_);
lean_ctor_set(v_reuseFailAlloc_2784_, 10, v_powFn_x3f_2771_);
lean_ctor_set(v_reuseFailAlloc_2784_, 11, v_intCastFn_x3f_2772_);
lean_ctor_set(v_reuseFailAlloc_2784_, 12, v_natCastFn_x3f_2773_);
lean_ctor_set(v_reuseFailAlloc_2784_, 13, v_one_x3f_2774_);
lean_ctor_set(v_reuseFailAlloc_2784_, 14, v_vars_2775_);
lean_ctor_set(v_reuseFailAlloc_2784_, 15, v_varMap_2776_);
lean_ctor_set(v_reuseFailAlloc_2784_, 16, v___x_2781_);
v___x_2783_ = v_reuseFailAlloc_2784_;
goto v_reusejp_2782_;
}
v_reusejp_2782_:
{
return v___x_2783_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_internalize___lam__3(lean_object* v_e_2786_, lean_object* v_val_2787_, lean_object* v_s_2788_){
_start:
{
lean_object* v_id_2789_; lean_object* v_type_2790_; lean_object* v_u_2791_; lean_object* v_semiringInst_2792_; lean_object* v_addFn_x3f_2793_; lean_object* v_mulFn_x3f_2794_; lean_object* v_powFn_x3f_2795_; lean_object* v_natCastFn_x3f_2796_; lean_object* v_denote_2797_; lean_object* v_vars_2798_; lean_object* v_varMap_2799_; lean_object* v___x_2801_; uint8_t v_isShared_2802_; uint8_t v_isSharedCheck_2807_; 
v_id_2789_ = lean_ctor_get(v_s_2788_, 0);
v_type_2790_ = lean_ctor_get(v_s_2788_, 1);
v_u_2791_ = lean_ctor_get(v_s_2788_, 2);
v_semiringInst_2792_ = lean_ctor_get(v_s_2788_, 3);
v_addFn_x3f_2793_ = lean_ctor_get(v_s_2788_, 4);
v_mulFn_x3f_2794_ = lean_ctor_get(v_s_2788_, 5);
v_powFn_x3f_2795_ = lean_ctor_get(v_s_2788_, 6);
v_natCastFn_x3f_2796_ = lean_ctor_get(v_s_2788_, 7);
v_denote_2797_ = lean_ctor_get(v_s_2788_, 8);
v_vars_2798_ = lean_ctor_get(v_s_2788_, 9);
v_varMap_2799_ = lean_ctor_get(v_s_2788_, 10);
v_isSharedCheck_2807_ = !lean_is_exclusive(v_s_2788_);
if (v_isSharedCheck_2807_ == 0)
{
v___x_2801_ = v_s_2788_;
v_isShared_2802_ = v_isSharedCheck_2807_;
goto v_resetjp_2800_;
}
else
{
lean_inc(v_varMap_2799_);
lean_inc(v_vars_2798_);
lean_inc(v_denote_2797_);
lean_inc(v_natCastFn_x3f_2796_);
lean_inc(v_powFn_x3f_2795_);
lean_inc(v_mulFn_x3f_2794_);
lean_inc(v_addFn_x3f_2793_);
lean_inc(v_semiringInst_2792_);
lean_inc(v_u_2791_);
lean_inc(v_type_2790_);
lean_inc(v_id_2789_);
lean_dec(v_s_2788_);
v___x_2801_ = lean_box(0);
v_isShared_2802_ = v_isSharedCheck_2807_;
goto v_resetjp_2800_;
}
v_resetjp_2800_:
{
lean_object* v___x_2803_; lean_object* v___x_2805_; 
v___x_2803_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0___redArg(v_denote_2797_, v_e_2786_, v_val_2787_);
if (v_isShared_2802_ == 0)
{
lean_ctor_set(v___x_2801_, 8, v___x_2803_);
v___x_2805_ = v___x_2801_;
goto v_reusejp_2804_;
}
else
{
lean_object* v_reuseFailAlloc_2806_; 
v_reuseFailAlloc_2806_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_2806_, 0, v_id_2789_);
lean_ctor_set(v_reuseFailAlloc_2806_, 1, v_type_2790_);
lean_ctor_set(v_reuseFailAlloc_2806_, 2, v_u_2791_);
lean_ctor_set(v_reuseFailAlloc_2806_, 3, v_semiringInst_2792_);
lean_ctor_set(v_reuseFailAlloc_2806_, 4, v_addFn_x3f_2793_);
lean_ctor_set(v_reuseFailAlloc_2806_, 5, v_mulFn_x3f_2794_);
lean_ctor_set(v_reuseFailAlloc_2806_, 6, v_powFn_x3f_2795_);
lean_ctor_set(v_reuseFailAlloc_2806_, 7, v_natCastFn_x3f_2796_);
lean_ctor_set(v_reuseFailAlloc_2806_, 8, v___x_2803_);
lean_ctor_set(v_reuseFailAlloc_2806_, 9, v_vars_2798_);
lean_ctor_set(v_reuseFailAlloc_2806_, 10, v_varMap_2799_);
v___x_2805_ = v_reuseFailAlloc_2806_;
goto v_reusejp_2804_;
}
v_reusejp_2804_:
{
return v___x_2805_;
}
}
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_2808_; double v___x_2809_; 
v___x_2808_ = lean_unsigned_to_nat(0u);
v___x_2809_ = lean_float_of_nat(v___x_2808_);
return v___x_2809_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__4___redArg(lean_object* v_cls_2813_, lean_object* v_msg_2814_, lean_object* v___y_2815_, lean_object* v___y_2816_, lean_object* v___y_2817_, lean_object* v___y_2818_){
_start:
{
lean_object* v_ref_2820_; lean_object* v___x_2821_; lean_object* v_a_2822_; lean_object* v___x_2824_; uint8_t v_isShared_2825_; uint8_t v_isSharedCheck_2866_; 
v_ref_2820_ = lean_ctor_get(v___y_2817_, 5);
v___x_2821_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1_spec__5_spec__8_spec__9(v_msg_2814_, v___y_2815_, v___y_2816_, v___y_2817_, v___y_2818_);
v_a_2822_ = lean_ctor_get(v___x_2821_, 0);
v_isSharedCheck_2866_ = !lean_is_exclusive(v___x_2821_);
if (v_isSharedCheck_2866_ == 0)
{
v___x_2824_ = v___x_2821_;
v_isShared_2825_ = v_isSharedCheck_2866_;
goto v_resetjp_2823_;
}
else
{
lean_inc(v_a_2822_);
lean_dec(v___x_2821_);
v___x_2824_ = lean_box(0);
v_isShared_2825_ = v_isSharedCheck_2866_;
goto v_resetjp_2823_;
}
v_resetjp_2823_:
{
lean_object* v___x_2826_; lean_object* v_traceState_2827_; lean_object* v_env_2828_; lean_object* v_nextMacroScope_2829_; lean_object* v_ngen_2830_; lean_object* v_auxDeclNGen_2831_; lean_object* v_cache_2832_; lean_object* v_messages_2833_; lean_object* v_infoState_2834_; lean_object* v_snapshotTasks_2835_; lean_object* v___x_2837_; uint8_t v_isShared_2838_; uint8_t v_isSharedCheck_2865_; 
v___x_2826_ = lean_st_ref_take(v___y_2818_);
v_traceState_2827_ = lean_ctor_get(v___x_2826_, 4);
v_env_2828_ = lean_ctor_get(v___x_2826_, 0);
v_nextMacroScope_2829_ = lean_ctor_get(v___x_2826_, 1);
v_ngen_2830_ = lean_ctor_get(v___x_2826_, 2);
v_auxDeclNGen_2831_ = lean_ctor_get(v___x_2826_, 3);
v_cache_2832_ = lean_ctor_get(v___x_2826_, 5);
v_messages_2833_ = lean_ctor_get(v___x_2826_, 6);
v_infoState_2834_ = lean_ctor_get(v___x_2826_, 7);
v_snapshotTasks_2835_ = lean_ctor_get(v___x_2826_, 8);
v_isSharedCheck_2865_ = !lean_is_exclusive(v___x_2826_);
if (v_isSharedCheck_2865_ == 0)
{
v___x_2837_ = v___x_2826_;
v_isShared_2838_ = v_isSharedCheck_2865_;
goto v_resetjp_2836_;
}
else
{
lean_inc(v_snapshotTasks_2835_);
lean_inc(v_infoState_2834_);
lean_inc(v_messages_2833_);
lean_inc(v_cache_2832_);
lean_inc(v_traceState_2827_);
lean_inc(v_auxDeclNGen_2831_);
lean_inc(v_ngen_2830_);
lean_inc(v_nextMacroScope_2829_);
lean_inc(v_env_2828_);
lean_dec(v___x_2826_);
v___x_2837_ = lean_box(0);
v_isShared_2838_ = v_isSharedCheck_2865_;
goto v_resetjp_2836_;
}
v_resetjp_2836_:
{
uint64_t v_tid_2839_; lean_object* v_traces_2840_; lean_object* v___x_2842_; uint8_t v_isShared_2843_; uint8_t v_isSharedCheck_2864_; 
v_tid_2839_ = lean_ctor_get_uint64(v_traceState_2827_, sizeof(void*)*1);
v_traces_2840_ = lean_ctor_get(v_traceState_2827_, 0);
v_isSharedCheck_2864_ = !lean_is_exclusive(v_traceState_2827_);
if (v_isSharedCheck_2864_ == 0)
{
v___x_2842_ = v_traceState_2827_;
v_isShared_2843_ = v_isSharedCheck_2864_;
goto v_resetjp_2841_;
}
else
{
lean_inc(v_traces_2840_);
lean_dec(v_traceState_2827_);
v___x_2842_ = lean_box(0);
v_isShared_2843_ = v_isSharedCheck_2864_;
goto v_resetjp_2841_;
}
v_resetjp_2841_:
{
lean_object* v___x_2844_; double v___x_2845_; uint8_t v___x_2846_; lean_object* v___x_2847_; lean_object* v___x_2848_; lean_object* v___x_2849_; lean_object* v___x_2850_; lean_object* v___x_2851_; lean_object* v___x_2852_; lean_object* v___x_2854_; 
v___x_2844_ = lean_box(0);
v___x_2845_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__4___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__4___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__4___redArg___closed__0);
v___x_2846_ = 0;
v___x_2847_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__4___redArg___closed__1));
v___x_2848_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2848_, 0, v_cls_2813_);
lean_ctor_set(v___x_2848_, 1, v___x_2844_);
lean_ctor_set(v___x_2848_, 2, v___x_2847_);
lean_ctor_set_float(v___x_2848_, sizeof(void*)*3, v___x_2845_);
lean_ctor_set_float(v___x_2848_, sizeof(void*)*3 + 8, v___x_2845_);
lean_ctor_set_uint8(v___x_2848_, sizeof(void*)*3 + 16, v___x_2846_);
v___x_2849_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__4___redArg___closed__2));
v___x_2850_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2850_, 0, v___x_2848_);
lean_ctor_set(v___x_2850_, 1, v_a_2822_);
lean_ctor_set(v___x_2850_, 2, v___x_2849_);
lean_inc(v_ref_2820_);
v___x_2851_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2851_, 0, v_ref_2820_);
lean_ctor_set(v___x_2851_, 1, v___x_2850_);
v___x_2852_ = l_Lean_PersistentArray_push___redArg(v_traces_2840_, v___x_2851_);
if (v_isShared_2843_ == 0)
{
lean_ctor_set(v___x_2842_, 0, v___x_2852_);
v___x_2854_ = v___x_2842_;
goto v_reusejp_2853_;
}
else
{
lean_object* v_reuseFailAlloc_2863_; 
v_reuseFailAlloc_2863_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2863_, 0, v___x_2852_);
lean_ctor_set_uint64(v_reuseFailAlloc_2863_, sizeof(void*)*1, v_tid_2839_);
v___x_2854_ = v_reuseFailAlloc_2863_;
goto v_reusejp_2853_;
}
v_reusejp_2853_:
{
lean_object* v___x_2856_; 
if (v_isShared_2838_ == 0)
{
lean_ctor_set(v___x_2837_, 4, v___x_2854_);
v___x_2856_ = v___x_2837_;
goto v_reusejp_2855_;
}
else
{
lean_object* v_reuseFailAlloc_2862_; 
v_reuseFailAlloc_2862_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2862_, 0, v_env_2828_);
lean_ctor_set(v_reuseFailAlloc_2862_, 1, v_nextMacroScope_2829_);
lean_ctor_set(v_reuseFailAlloc_2862_, 2, v_ngen_2830_);
lean_ctor_set(v_reuseFailAlloc_2862_, 3, v_auxDeclNGen_2831_);
lean_ctor_set(v_reuseFailAlloc_2862_, 4, v___x_2854_);
lean_ctor_set(v_reuseFailAlloc_2862_, 5, v_cache_2832_);
lean_ctor_set(v_reuseFailAlloc_2862_, 6, v_messages_2833_);
lean_ctor_set(v_reuseFailAlloc_2862_, 7, v_infoState_2834_);
lean_ctor_set(v_reuseFailAlloc_2862_, 8, v_snapshotTasks_2835_);
v___x_2856_ = v_reuseFailAlloc_2862_;
goto v_reusejp_2855_;
}
v_reusejp_2855_:
{
lean_object* v___x_2857_; lean_object* v___x_2858_; lean_object* v___x_2860_; 
v___x_2857_ = lean_st_ref_set(v___y_2818_, v___x_2856_);
v___x_2858_ = lean_box(0);
if (v_isShared_2825_ == 0)
{
lean_ctor_set(v___x_2824_, 0, v___x_2858_);
v___x_2860_ = v___x_2824_;
goto v_reusejp_2859_;
}
else
{
lean_object* v_reuseFailAlloc_2861_; 
v_reuseFailAlloc_2861_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2861_, 0, v___x_2858_);
v___x_2860_ = v_reuseFailAlloc_2861_;
goto v_reusejp_2859_;
}
v_reusejp_2859_:
{
return v___x_2860_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__4___redArg___boxed(lean_object* v_cls_2867_, lean_object* v_msg_2868_, lean_object* v___y_2869_, lean_object* v___y_2870_, lean_object* v___y_2871_, lean_object* v___y_2872_, lean_object* v___y_2873_){
_start:
{
lean_object* v_res_2874_; 
v_res_2874_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__4___redArg(v_cls_2867_, v_msg_2868_, v___y_2869_, v___y_2870_, v___y_2871_, v___y_2872_);
lean_dec(v___y_2872_);
lean_dec_ref(v___y_2871_);
lean_dec(v___y_2870_);
lean_dec_ref(v___y_2869_);
return v_res_2874_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__1___redArg(lean_object* v_cls_2875_, lean_object* v_msg_2876_, lean_object* v___y_2877_, lean_object* v___y_2878_, lean_object* v___y_2879_, lean_object* v___y_2880_){
_start:
{
lean_object* v_ref_2882_; lean_object* v___x_2883_; lean_object* v_a_2884_; lean_object* v___x_2886_; uint8_t v_isShared_2887_; uint8_t v_isSharedCheck_2928_; 
v_ref_2882_ = lean_ctor_get(v___y_2879_, 5);
v___x_2883_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1_spec__5_spec__8_spec__9(v_msg_2876_, v___y_2877_, v___y_2878_, v___y_2879_, v___y_2880_);
v_a_2884_ = lean_ctor_get(v___x_2883_, 0);
v_isSharedCheck_2928_ = !lean_is_exclusive(v___x_2883_);
if (v_isSharedCheck_2928_ == 0)
{
v___x_2886_ = v___x_2883_;
v_isShared_2887_ = v_isSharedCheck_2928_;
goto v_resetjp_2885_;
}
else
{
lean_inc(v_a_2884_);
lean_dec(v___x_2883_);
v___x_2886_ = lean_box(0);
v_isShared_2887_ = v_isSharedCheck_2928_;
goto v_resetjp_2885_;
}
v_resetjp_2885_:
{
lean_object* v___x_2888_; lean_object* v_traceState_2889_; lean_object* v_env_2890_; lean_object* v_nextMacroScope_2891_; lean_object* v_ngen_2892_; lean_object* v_auxDeclNGen_2893_; lean_object* v_cache_2894_; lean_object* v_messages_2895_; lean_object* v_infoState_2896_; lean_object* v_snapshotTasks_2897_; lean_object* v___x_2899_; uint8_t v_isShared_2900_; uint8_t v_isSharedCheck_2927_; 
v___x_2888_ = lean_st_ref_take(v___y_2880_);
v_traceState_2889_ = lean_ctor_get(v___x_2888_, 4);
v_env_2890_ = lean_ctor_get(v___x_2888_, 0);
v_nextMacroScope_2891_ = lean_ctor_get(v___x_2888_, 1);
v_ngen_2892_ = lean_ctor_get(v___x_2888_, 2);
v_auxDeclNGen_2893_ = lean_ctor_get(v___x_2888_, 3);
v_cache_2894_ = lean_ctor_get(v___x_2888_, 5);
v_messages_2895_ = lean_ctor_get(v___x_2888_, 6);
v_infoState_2896_ = lean_ctor_get(v___x_2888_, 7);
v_snapshotTasks_2897_ = lean_ctor_get(v___x_2888_, 8);
v_isSharedCheck_2927_ = !lean_is_exclusive(v___x_2888_);
if (v_isSharedCheck_2927_ == 0)
{
v___x_2899_ = v___x_2888_;
v_isShared_2900_ = v_isSharedCheck_2927_;
goto v_resetjp_2898_;
}
else
{
lean_inc(v_snapshotTasks_2897_);
lean_inc(v_infoState_2896_);
lean_inc(v_messages_2895_);
lean_inc(v_cache_2894_);
lean_inc(v_traceState_2889_);
lean_inc(v_auxDeclNGen_2893_);
lean_inc(v_ngen_2892_);
lean_inc(v_nextMacroScope_2891_);
lean_inc(v_env_2890_);
lean_dec(v___x_2888_);
v___x_2899_ = lean_box(0);
v_isShared_2900_ = v_isSharedCheck_2927_;
goto v_resetjp_2898_;
}
v_resetjp_2898_:
{
uint64_t v_tid_2901_; lean_object* v_traces_2902_; lean_object* v___x_2904_; uint8_t v_isShared_2905_; uint8_t v_isSharedCheck_2926_; 
v_tid_2901_ = lean_ctor_get_uint64(v_traceState_2889_, sizeof(void*)*1);
v_traces_2902_ = lean_ctor_get(v_traceState_2889_, 0);
v_isSharedCheck_2926_ = !lean_is_exclusive(v_traceState_2889_);
if (v_isSharedCheck_2926_ == 0)
{
v___x_2904_ = v_traceState_2889_;
v_isShared_2905_ = v_isSharedCheck_2926_;
goto v_resetjp_2903_;
}
else
{
lean_inc(v_traces_2902_);
lean_dec(v_traceState_2889_);
v___x_2904_ = lean_box(0);
v_isShared_2905_ = v_isSharedCheck_2926_;
goto v_resetjp_2903_;
}
v_resetjp_2903_:
{
lean_object* v___x_2906_; double v___x_2907_; uint8_t v___x_2908_; lean_object* v___x_2909_; lean_object* v___x_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; lean_object* v___x_2913_; lean_object* v___x_2914_; lean_object* v___x_2916_; 
v___x_2906_ = lean_box(0);
v___x_2907_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__4___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__4___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__4___redArg___closed__0);
v___x_2908_ = 0;
v___x_2909_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__4___redArg___closed__1));
v___x_2910_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2910_, 0, v_cls_2875_);
lean_ctor_set(v___x_2910_, 1, v___x_2906_);
lean_ctor_set(v___x_2910_, 2, v___x_2909_);
lean_ctor_set_float(v___x_2910_, sizeof(void*)*3, v___x_2907_);
lean_ctor_set_float(v___x_2910_, sizeof(void*)*3 + 8, v___x_2907_);
lean_ctor_set_uint8(v___x_2910_, sizeof(void*)*3 + 16, v___x_2908_);
v___x_2911_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__4___redArg___closed__2));
v___x_2912_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2912_, 0, v___x_2910_);
lean_ctor_set(v___x_2912_, 1, v_a_2884_);
lean_ctor_set(v___x_2912_, 2, v___x_2911_);
lean_inc(v_ref_2882_);
v___x_2913_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2913_, 0, v_ref_2882_);
lean_ctor_set(v___x_2913_, 1, v___x_2912_);
v___x_2914_ = l_Lean_PersistentArray_push___redArg(v_traces_2902_, v___x_2913_);
if (v_isShared_2905_ == 0)
{
lean_ctor_set(v___x_2904_, 0, v___x_2914_);
v___x_2916_ = v___x_2904_;
goto v_reusejp_2915_;
}
else
{
lean_object* v_reuseFailAlloc_2925_; 
v_reuseFailAlloc_2925_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2925_, 0, v___x_2914_);
lean_ctor_set_uint64(v_reuseFailAlloc_2925_, sizeof(void*)*1, v_tid_2901_);
v___x_2916_ = v_reuseFailAlloc_2925_;
goto v_reusejp_2915_;
}
v_reusejp_2915_:
{
lean_object* v___x_2918_; 
if (v_isShared_2900_ == 0)
{
lean_ctor_set(v___x_2899_, 4, v___x_2916_);
v___x_2918_ = v___x_2899_;
goto v_reusejp_2917_;
}
else
{
lean_object* v_reuseFailAlloc_2924_; 
v_reuseFailAlloc_2924_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2924_, 0, v_env_2890_);
lean_ctor_set(v_reuseFailAlloc_2924_, 1, v_nextMacroScope_2891_);
lean_ctor_set(v_reuseFailAlloc_2924_, 2, v_ngen_2892_);
lean_ctor_set(v_reuseFailAlloc_2924_, 3, v_auxDeclNGen_2893_);
lean_ctor_set(v_reuseFailAlloc_2924_, 4, v___x_2916_);
lean_ctor_set(v_reuseFailAlloc_2924_, 5, v_cache_2894_);
lean_ctor_set(v_reuseFailAlloc_2924_, 6, v_messages_2895_);
lean_ctor_set(v_reuseFailAlloc_2924_, 7, v_infoState_2896_);
lean_ctor_set(v_reuseFailAlloc_2924_, 8, v_snapshotTasks_2897_);
v___x_2918_ = v_reuseFailAlloc_2924_;
goto v_reusejp_2917_;
}
v_reusejp_2917_:
{
lean_object* v___x_2919_; lean_object* v___x_2920_; lean_object* v___x_2922_; 
v___x_2919_ = lean_st_ref_set(v___y_2880_, v___x_2918_);
v___x_2920_ = lean_box(0);
if (v_isShared_2887_ == 0)
{
lean_ctor_set(v___x_2886_, 0, v___x_2920_);
v___x_2922_ = v___x_2886_;
goto v_reusejp_2921_;
}
else
{
lean_object* v_reuseFailAlloc_2923_; 
v_reuseFailAlloc_2923_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2923_, 0, v___x_2920_);
v___x_2922_ = v_reuseFailAlloc_2923_;
goto v_reusejp_2921_;
}
v_reusejp_2921_:
{
return v___x_2922_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__1___redArg___boxed(lean_object* v_cls_2929_, lean_object* v_msg_2930_, lean_object* v___y_2931_, lean_object* v___y_2932_, lean_object* v___y_2933_, lean_object* v___y_2934_, lean_object* v___y_2935_){
_start:
{
lean_object* v_res_2936_; 
v_res_2936_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__1___redArg(v_cls_2929_, v_msg_2930_, v___y_2931_, v___y_2932_, v___y_2933_, v___y_2934_);
lean_dec(v___y_2934_);
lean_dec_ref(v___y_2933_);
lean_dec(v___y_2932_);
lean_dec_ref(v___y_2931_);
return v_res_2936_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__2___redArg(lean_object* v_cls_2937_, lean_object* v_msg_2938_, lean_object* v___y_2939_, lean_object* v___y_2940_, lean_object* v___y_2941_, lean_object* v___y_2942_){
_start:
{
lean_object* v_ref_2944_; lean_object* v___x_2945_; lean_object* v_a_2946_; lean_object* v___x_2948_; uint8_t v_isShared_2949_; uint8_t v_isSharedCheck_2990_; 
v_ref_2944_ = lean_ctor_get(v___y_2941_, 5);
v___x_2945_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1_spec__5_spec__8_spec__9(v_msg_2938_, v___y_2939_, v___y_2940_, v___y_2941_, v___y_2942_);
v_a_2946_ = lean_ctor_get(v___x_2945_, 0);
v_isSharedCheck_2990_ = !lean_is_exclusive(v___x_2945_);
if (v_isSharedCheck_2990_ == 0)
{
v___x_2948_ = v___x_2945_;
v_isShared_2949_ = v_isSharedCheck_2990_;
goto v_resetjp_2947_;
}
else
{
lean_inc(v_a_2946_);
lean_dec(v___x_2945_);
v___x_2948_ = lean_box(0);
v_isShared_2949_ = v_isSharedCheck_2990_;
goto v_resetjp_2947_;
}
v_resetjp_2947_:
{
lean_object* v___x_2950_; lean_object* v_traceState_2951_; lean_object* v_env_2952_; lean_object* v_nextMacroScope_2953_; lean_object* v_ngen_2954_; lean_object* v_auxDeclNGen_2955_; lean_object* v_cache_2956_; lean_object* v_messages_2957_; lean_object* v_infoState_2958_; lean_object* v_snapshotTasks_2959_; lean_object* v___x_2961_; uint8_t v_isShared_2962_; uint8_t v_isSharedCheck_2989_; 
v___x_2950_ = lean_st_ref_take(v___y_2942_);
v_traceState_2951_ = lean_ctor_get(v___x_2950_, 4);
v_env_2952_ = lean_ctor_get(v___x_2950_, 0);
v_nextMacroScope_2953_ = lean_ctor_get(v___x_2950_, 1);
v_ngen_2954_ = lean_ctor_get(v___x_2950_, 2);
v_auxDeclNGen_2955_ = lean_ctor_get(v___x_2950_, 3);
v_cache_2956_ = lean_ctor_get(v___x_2950_, 5);
v_messages_2957_ = lean_ctor_get(v___x_2950_, 6);
v_infoState_2958_ = lean_ctor_get(v___x_2950_, 7);
v_snapshotTasks_2959_ = lean_ctor_get(v___x_2950_, 8);
v_isSharedCheck_2989_ = !lean_is_exclusive(v___x_2950_);
if (v_isSharedCheck_2989_ == 0)
{
v___x_2961_ = v___x_2950_;
v_isShared_2962_ = v_isSharedCheck_2989_;
goto v_resetjp_2960_;
}
else
{
lean_inc(v_snapshotTasks_2959_);
lean_inc(v_infoState_2958_);
lean_inc(v_messages_2957_);
lean_inc(v_cache_2956_);
lean_inc(v_traceState_2951_);
lean_inc(v_auxDeclNGen_2955_);
lean_inc(v_ngen_2954_);
lean_inc(v_nextMacroScope_2953_);
lean_inc(v_env_2952_);
lean_dec(v___x_2950_);
v___x_2961_ = lean_box(0);
v_isShared_2962_ = v_isSharedCheck_2989_;
goto v_resetjp_2960_;
}
v_resetjp_2960_:
{
uint64_t v_tid_2963_; lean_object* v_traces_2964_; lean_object* v___x_2966_; uint8_t v_isShared_2967_; uint8_t v_isSharedCheck_2988_; 
v_tid_2963_ = lean_ctor_get_uint64(v_traceState_2951_, sizeof(void*)*1);
v_traces_2964_ = lean_ctor_get(v_traceState_2951_, 0);
v_isSharedCheck_2988_ = !lean_is_exclusive(v_traceState_2951_);
if (v_isSharedCheck_2988_ == 0)
{
v___x_2966_ = v_traceState_2951_;
v_isShared_2967_ = v_isSharedCheck_2988_;
goto v_resetjp_2965_;
}
else
{
lean_inc(v_traces_2964_);
lean_dec(v_traceState_2951_);
v___x_2966_ = lean_box(0);
v_isShared_2967_ = v_isSharedCheck_2988_;
goto v_resetjp_2965_;
}
v_resetjp_2965_:
{
lean_object* v___x_2968_; double v___x_2969_; uint8_t v___x_2970_; lean_object* v___x_2971_; lean_object* v___x_2972_; lean_object* v___x_2973_; lean_object* v___x_2974_; lean_object* v___x_2975_; lean_object* v___x_2976_; lean_object* v___x_2978_; 
v___x_2968_ = lean_box(0);
v___x_2969_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__4___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__4___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__4___redArg___closed__0);
v___x_2970_ = 0;
v___x_2971_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__4___redArg___closed__1));
v___x_2972_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2972_, 0, v_cls_2937_);
lean_ctor_set(v___x_2972_, 1, v___x_2968_);
lean_ctor_set(v___x_2972_, 2, v___x_2971_);
lean_ctor_set_float(v___x_2972_, sizeof(void*)*3, v___x_2969_);
lean_ctor_set_float(v___x_2972_, sizeof(void*)*3 + 8, v___x_2969_);
lean_ctor_set_uint8(v___x_2972_, sizeof(void*)*3 + 16, v___x_2970_);
v___x_2973_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__4___redArg___closed__2));
v___x_2974_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2974_, 0, v___x_2972_);
lean_ctor_set(v___x_2974_, 1, v_a_2946_);
lean_ctor_set(v___x_2974_, 2, v___x_2973_);
lean_inc(v_ref_2944_);
v___x_2975_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2975_, 0, v_ref_2944_);
lean_ctor_set(v___x_2975_, 1, v___x_2974_);
v___x_2976_ = l_Lean_PersistentArray_push___redArg(v_traces_2964_, v___x_2975_);
if (v_isShared_2967_ == 0)
{
lean_ctor_set(v___x_2966_, 0, v___x_2976_);
v___x_2978_ = v___x_2966_;
goto v_reusejp_2977_;
}
else
{
lean_object* v_reuseFailAlloc_2987_; 
v_reuseFailAlloc_2987_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2987_, 0, v___x_2976_);
lean_ctor_set_uint64(v_reuseFailAlloc_2987_, sizeof(void*)*1, v_tid_2963_);
v___x_2978_ = v_reuseFailAlloc_2987_;
goto v_reusejp_2977_;
}
v_reusejp_2977_:
{
lean_object* v___x_2980_; 
if (v_isShared_2962_ == 0)
{
lean_ctor_set(v___x_2961_, 4, v___x_2978_);
v___x_2980_ = v___x_2961_;
goto v_reusejp_2979_;
}
else
{
lean_object* v_reuseFailAlloc_2986_; 
v_reuseFailAlloc_2986_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2986_, 0, v_env_2952_);
lean_ctor_set(v_reuseFailAlloc_2986_, 1, v_nextMacroScope_2953_);
lean_ctor_set(v_reuseFailAlloc_2986_, 2, v_ngen_2954_);
lean_ctor_set(v_reuseFailAlloc_2986_, 3, v_auxDeclNGen_2955_);
lean_ctor_set(v_reuseFailAlloc_2986_, 4, v___x_2978_);
lean_ctor_set(v_reuseFailAlloc_2986_, 5, v_cache_2956_);
lean_ctor_set(v_reuseFailAlloc_2986_, 6, v_messages_2957_);
lean_ctor_set(v_reuseFailAlloc_2986_, 7, v_infoState_2958_);
lean_ctor_set(v_reuseFailAlloc_2986_, 8, v_snapshotTasks_2959_);
v___x_2980_ = v_reuseFailAlloc_2986_;
goto v_reusejp_2979_;
}
v_reusejp_2979_:
{
lean_object* v___x_2981_; lean_object* v___x_2982_; lean_object* v___x_2984_; 
v___x_2981_ = lean_st_ref_set(v___y_2942_, v___x_2980_);
v___x_2982_ = lean_box(0);
if (v_isShared_2949_ == 0)
{
lean_ctor_set(v___x_2948_, 0, v___x_2982_);
v___x_2984_ = v___x_2948_;
goto v_reusejp_2983_;
}
else
{
lean_object* v_reuseFailAlloc_2985_; 
v_reuseFailAlloc_2985_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2985_, 0, v___x_2982_);
v___x_2984_ = v_reuseFailAlloc_2985_;
goto v_reusejp_2983_;
}
v_reusejp_2983_:
{
return v___x_2984_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__2___redArg___boxed(lean_object* v_cls_2991_, lean_object* v_msg_2992_, lean_object* v___y_2993_, lean_object* v___y_2994_, lean_object* v___y_2995_, lean_object* v___y_2996_, lean_object* v___y_2997_){
_start:
{
lean_object* v_res_2998_; 
v_res_2998_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__2___redArg(v_cls_2991_, v_msg_2992_, v___y_2993_, v___y_2994_, v___y_2995_, v___y_2996_);
lean_dec(v___y_2996_);
lean_dec_ref(v___y_2995_);
lean_dec(v___y_2994_);
lean_dec_ref(v___y_2993_);
return v_res_2998_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__3___redArg(lean_object* v_cls_2999_, lean_object* v_msg_3000_, lean_object* v___y_3001_, lean_object* v___y_3002_, lean_object* v___y_3003_, lean_object* v___y_3004_){
_start:
{
lean_object* v_ref_3006_; lean_object* v___x_3007_; lean_object* v_a_3008_; lean_object* v___x_3010_; uint8_t v_isShared_3011_; uint8_t v_isSharedCheck_3052_; 
v_ref_3006_ = lean_ctor_get(v___y_3003_, 5);
v___x_3007_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1_spec__5_spec__8_spec__9(v_msg_3000_, v___y_3001_, v___y_3002_, v___y_3003_, v___y_3004_);
v_a_3008_ = lean_ctor_get(v___x_3007_, 0);
v_isSharedCheck_3052_ = !lean_is_exclusive(v___x_3007_);
if (v_isSharedCheck_3052_ == 0)
{
v___x_3010_ = v___x_3007_;
v_isShared_3011_ = v_isSharedCheck_3052_;
goto v_resetjp_3009_;
}
else
{
lean_inc(v_a_3008_);
lean_dec(v___x_3007_);
v___x_3010_ = lean_box(0);
v_isShared_3011_ = v_isSharedCheck_3052_;
goto v_resetjp_3009_;
}
v_resetjp_3009_:
{
lean_object* v___x_3012_; lean_object* v_traceState_3013_; lean_object* v_env_3014_; lean_object* v_nextMacroScope_3015_; lean_object* v_ngen_3016_; lean_object* v_auxDeclNGen_3017_; lean_object* v_cache_3018_; lean_object* v_messages_3019_; lean_object* v_infoState_3020_; lean_object* v_snapshotTasks_3021_; lean_object* v___x_3023_; uint8_t v_isShared_3024_; uint8_t v_isSharedCheck_3051_; 
v___x_3012_ = lean_st_ref_take(v___y_3004_);
v_traceState_3013_ = lean_ctor_get(v___x_3012_, 4);
v_env_3014_ = lean_ctor_get(v___x_3012_, 0);
v_nextMacroScope_3015_ = lean_ctor_get(v___x_3012_, 1);
v_ngen_3016_ = lean_ctor_get(v___x_3012_, 2);
v_auxDeclNGen_3017_ = lean_ctor_get(v___x_3012_, 3);
v_cache_3018_ = lean_ctor_get(v___x_3012_, 5);
v_messages_3019_ = lean_ctor_get(v___x_3012_, 6);
v_infoState_3020_ = lean_ctor_get(v___x_3012_, 7);
v_snapshotTasks_3021_ = lean_ctor_get(v___x_3012_, 8);
v_isSharedCheck_3051_ = !lean_is_exclusive(v___x_3012_);
if (v_isSharedCheck_3051_ == 0)
{
v___x_3023_ = v___x_3012_;
v_isShared_3024_ = v_isSharedCheck_3051_;
goto v_resetjp_3022_;
}
else
{
lean_inc(v_snapshotTasks_3021_);
lean_inc(v_infoState_3020_);
lean_inc(v_messages_3019_);
lean_inc(v_cache_3018_);
lean_inc(v_traceState_3013_);
lean_inc(v_auxDeclNGen_3017_);
lean_inc(v_ngen_3016_);
lean_inc(v_nextMacroScope_3015_);
lean_inc(v_env_3014_);
lean_dec(v___x_3012_);
v___x_3023_ = lean_box(0);
v_isShared_3024_ = v_isSharedCheck_3051_;
goto v_resetjp_3022_;
}
v_resetjp_3022_:
{
uint64_t v_tid_3025_; lean_object* v_traces_3026_; lean_object* v___x_3028_; uint8_t v_isShared_3029_; uint8_t v_isSharedCheck_3050_; 
v_tid_3025_ = lean_ctor_get_uint64(v_traceState_3013_, sizeof(void*)*1);
v_traces_3026_ = lean_ctor_get(v_traceState_3013_, 0);
v_isSharedCheck_3050_ = !lean_is_exclusive(v_traceState_3013_);
if (v_isSharedCheck_3050_ == 0)
{
v___x_3028_ = v_traceState_3013_;
v_isShared_3029_ = v_isSharedCheck_3050_;
goto v_resetjp_3027_;
}
else
{
lean_inc(v_traces_3026_);
lean_dec(v_traceState_3013_);
v___x_3028_ = lean_box(0);
v_isShared_3029_ = v_isSharedCheck_3050_;
goto v_resetjp_3027_;
}
v_resetjp_3027_:
{
lean_object* v___x_3030_; double v___x_3031_; uint8_t v___x_3032_; lean_object* v___x_3033_; lean_object* v___x_3034_; lean_object* v___x_3035_; lean_object* v___x_3036_; lean_object* v___x_3037_; lean_object* v___x_3038_; lean_object* v___x_3040_; 
v___x_3030_ = lean_box(0);
v___x_3031_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__4___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__4___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__4___redArg___closed__0);
v___x_3032_ = 0;
v___x_3033_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__4___redArg___closed__1));
v___x_3034_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3034_, 0, v_cls_2999_);
lean_ctor_set(v___x_3034_, 1, v___x_3030_);
lean_ctor_set(v___x_3034_, 2, v___x_3033_);
lean_ctor_set_float(v___x_3034_, sizeof(void*)*3, v___x_3031_);
lean_ctor_set_float(v___x_3034_, sizeof(void*)*3 + 8, v___x_3031_);
lean_ctor_set_uint8(v___x_3034_, sizeof(void*)*3 + 16, v___x_3032_);
v___x_3035_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__4___redArg___closed__2));
v___x_3036_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3036_, 0, v___x_3034_);
lean_ctor_set(v___x_3036_, 1, v_a_3008_);
lean_ctor_set(v___x_3036_, 2, v___x_3035_);
lean_inc(v_ref_3006_);
v___x_3037_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3037_, 0, v_ref_3006_);
lean_ctor_set(v___x_3037_, 1, v___x_3036_);
v___x_3038_ = l_Lean_PersistentArray_push___redArg(v_traces_3026_, v___x_3037_);
if (v_isShared_3029_ == 0)
{
lean_ctor_set(v___x_3028_, 0, v___x_3038_);
v___x_3040_ = v___x_3028_;
goto v_reusejp_3039_;
}
else
{
lean_object* v_reuseFailAlloc_3049_; 
v_reuseFailAlloc_3049_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3049_, 0, v___x_3038_);
lean_ctor_set_uint64(v_reuseFailAlloc_3049_, sizeof(void*)*1, v_tid_3025_);
v___x_3040_ = v_reuseFailAlloc_3049_;
goto v_reusejp_3039_;
}
v_reusejp_3039_:
{
lean_object* v___x_3042_; 
if (v_isShared_3024_ == 0)
{
lean_ctor_set(v___x_3023_, 4, v___x_3040_);
v___x_3042_ = v___x_3023_;
goto v_reusejp_3041_;
}
else
{
lean_object* v_reuseFailAlloc_3048_; 
v_reuseFailAlloc_3048_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3048_, 0, v_env_3014_);
lean_ctor_set(v_reuseFailAlloc_3048_, 1, v_nextMacroScope_3015_);
lean_ctor_set(v_reuseFailAlloc_3048_, 2, v_ngen_3016_);
lean_ctor_set(v_reuseFailAlloc_3048_, 3, v_auxDeclNGen_3017_);
lean_ctor_set(v_reuseFailAlloc_3048_, 4, v___x_3040_);
lean_ctor_set(v_reuseFailAlloc_3048_, 5, v_cache_3018_);
lean_ctor_set(v_reuseFailAlloc_3048_, 6, v_messages_3019_);
lean_ctor_set(v_reuseFailAlloc_3048_, 7, v_infoState_3020_);
lean_ctor_set(v_reuseFailAlloc_3048_, 8, v_snapshotTasks_3021_);
v___x_3042_ = v_reuseFailAlloc_3048_;
goto v_reusejp_3041_;
}
v_reusejp_3041_:
{
lean_object* v___x_3043_; lean_object* v___x_3044_; lean_object* v___x_3046_; 
v___x_3043_ = lean_st_ref_set(v___y_3004_, v___x_3042_);
v___x_3044_ = lean_box(0);
if (v_isShared_3011_ == 0)
{
lean_ctor_set(v___x_3010_, 0, v___x_3044_);
v___x_3046_ = v___x_3010_;
goto v_reusejp_3045_;
}
else
{
lean_object* v_reuseFailAlloc_3047_; 
v_reuseFailAlloc_3047_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3047_, 0, v___x_3044_);
v___x_3046_ = v_reuseFailAlloc_3047_;
goto v_reusejp_3045_;
}
v_reusejp_3045_:
{
return v___x_3046_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__3___redArg___boxed(lean_object* v_cls_3053_, lean_object* v_msg_3054_, lean_object* v___y_3055_, lean_object* v___y_3056_, lean_object* v___y_3057_, lean_object* v___y_3058_, lean_object* v___y_3059_){
_start:
{
lean_object* v_res_3060_; 
v_res_3060_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__3___redArg(v_cls_3053_, v_msg_3054_, v___y_3055_, v___y_3056_, v___y_3057_, v___y_3058_);
lean_dec(v___y_3058_);
lean_dec_ref(v___y_3057_);
lean_dec(v___y_3056_);
lean_dec_ref(v___y_3055_);
return v_res_3060_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__6(void){
_start:
{
lean_object* v___x_3071_; lean_object* v___x_3072_; lean_object* v___x_3073_; 
v___x_3071_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__3));
v___x_3072_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__5));
v___x_3073_ = l_Lean_Name_append(v___x_3072_, v___x_3071_);
return v___x_3073_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__8(void){
_start:
{
lean_object* v___x_3075_; lean_object* v___x_3076_; 
v___x_3075_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__7));
v___x_3076_ = l_Lean_stringToMessageData(v___x_3075_);
return v___x_3076_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__10(void){
_start:
{
lean_object* v___x_3078_; lean_object* v___x_3079_; 
v___x_3078_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__9));
v___x_3079_ = l_Lean_stringToMessageData(v___x_3078_);
return v___x_3079_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__12(void){
_start:
{
lean_object* v___x_3081_; lean_object* v___x_3082_; 
v___x_3081_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__11));
v___x_3082_ = l_Lean_stringToMessageData(v___x_3081_);
return v___x_3082_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__14(void){
_start:
{
lean_object* v___x_3084_; lean_object* v___x_3085_; 
v___x_3084_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__13));
v___x_3085_ = l_Lean_stringToMessageData(v___x_3084_);
return v___x_3085_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__16(void){
_start:
{
lean_object* v___x_3087_; lean_object* v___x_3088_; 
v___x_3087_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__15));
v___x_3088_ = l_Lean_stringToMessageData(v___x_3087_);
return v___x_3088_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_internalize(lean_object* v_e_3089_, lean_object* v_parent_x3f_3090_, lean_object* v_a_3091_, lean_object* v_a_3092_, lean_object* v_a_3093_, lean_object* v_a_3094_, lean_object* v_a_3095_, lean_object* v_a_3096_, lean_object* v_a_3097_, lean_object* v_a_3098_, lean_object* v_a_3099_, lean_object* v_a_3100_){
_start:
{
lean_object* v___x_3102_; 
v___x_3102_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_3093_);
if (lean_obj_tag(v___x_3102_) == 0)
{
lean_object* v_a_3103_; lean_object* v___x_3105_; uint8_t v_isShared_3106_; uint8_t v_isSharedCheck_3442_; 
v_a_3103_ = lean_ctor_get(v___x_3102_, 0);
v_isSharedCheck_3442_ = !lean_is_exclusive(v___x_3102_);
if (v_isSharedCheck_3442_ == 0)
{
v___x_3105_ = v___x_3102_;
v_isShared_3106_ = v_isSharedCheck_3442_;
goto v_resetjp_3104_;
}
else
{
lean_inc(v_a_3103_);
lean_dec(v___x_3102_);
v___x_3105_ = lean_box(0);
v_isShared_3106_ = v_isSharedCheck_3442_;
goto v_resetjp_3104_;
}
v_resetjp_3104_:
{
uint8_t v_ring_3107_; 
v_ring_3107_ = lean_ctor_get_uint8(v_a_3103_, sizeof(void*)*11 + 21);
lean_dec(v_a_3103_);
if (v_ring_3107_ == 0)
{
lean_object* v___x_3108_; lean_object* v___x_3110_; 
lean_dec(v_parent_x3f_3090_);
lean_dec_ref(v_e_3089_);
v___x_3108_ = lean_box(0);
if (v_isShared_3106_ == 0)
{
lean_ctor_set(v___x_3105_, 0, v___x_3108_);
v___x_3110_ = v___x_3105_;
goto v_reusejp_3109_;
}
else
{
lean_object* v_reuseFailAlloc_3111_; 
v_reuseFailAlloc_3111_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3111_, 0, v___x_3108_);
v___x_3110_ = v_reuseFailAlloc_3111_;
goto v_reusejp_3109_;
}
v_reusejp_3109_:
{
return v___x_3110_;
}
}
else
{
uint8_t v___x_3112_; 
v___x_3112_ = l_Lean_Meta_Grind_Arith_isIntModuleVirtualParent(v_parent_x3f_3090_);
if (v___x_3112_ == 0)
{
lean_object* v___x_3113_; 
lean_del_object(v___x_3105_);
lean_inc_ref(v_e_3089_);
v___x_3113_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeInv(v_e_3089_, v_a_3091_, v_a_3092_, v_a_3093_, v_a_3094_, v_a_3095_, v_a_3096_, v_a_3097_, v_a_3098_, v_a_3099_, v_a_3100_);
if (lean_obj_tag(v___x_3113_) == 0)
{
lean_object* v_a_3114_; lean_object* v___x_3116_; uint8_t v_isShared_3117_; uint8_t v_isSharedCheck_3429_; 
v_a_3114_ = lean_ctor_get(v___x_3113_, 0);
v_isSharedCheck_3429_ = !lean_is_exclusive(v___x_3113_);
if (v_isSharedCheck_3429_ == 0)
{
v___x_3116_ = v___x_3113_;
v_isShared_3117_ = v_isSharedCheck_3429_;
goto v_resetjp_3115_;
}
else
{
lean_inc(v_a_3114_);
lean_dec(v___x_3113_);
v___x_3116_ = lean_box(0);
v_isShared_3117_ = v_isSharedCheck_3429_;
goto v_resetjp_3115_;
}
v_resetjp_3115_:
{
uint8_t v___x_3118_; 
v___x_3118_ = lean_unbox(v_a_3114_);
lean_dec(v_a_3114_);
if (v___x_3118_ == 0)
{
lean_object* v___x_3119_; 
lean_inc_ref(v_e_3089_);
v___x_3119_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f(v_e_3089_);
if (lean_obj_tag(v___x_3119_) == 1)
{
lean_object* v_val_3120_; uint8_t v___x_3121_; 
v_val_3120_ = lean_ctor_get(v___x_3119_, 0);
lean_inc(v_val_3120_);
lean_dec_ref(v___x_3119_);
v___x_3121_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isForbiddenParent(v_parent_x3f_3090_);
if (v___x_3121_ == 0)
{
lean_object* v___x_3122_; 
lean_del_object(v___x_3116_);
lean_inc(v_val_3120_);
v___x_3122_ = l_Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f(v_val_3120_, v_a_3091_, v_a_3092_, v_a_3093_, v_a_3094_, v_a_3095_, v_a_3096_, v_a_3097_, v_a_3098_, v_a_3099_, v_a_3100_);
if (lean_obj_tag(v___x_3122_) == 0)
{
lean_object* v_a_3123_; 
v_a_3123_ = lean_ctor_get(v___x_3122_, 0);
lean_inc(v_a_3123_);
lean_dec_ref(v___x_3122_);
if (lean_obj_tag(v_a_3123_) == 1)
{
lean_object* v_val_3124_; lean_object* v___x_3125_; lean_object* v___x_3126_; lean_object* v___x_3127_; 
lean_dec(v_val_3120_);
v_val_3124_ = lean_ctor_get(v_a_3123_, 0);
lean_inc_n(v_val_3124_, 2);
lean_dec_ref(v_a_3123_);
v___x_3125_ = lean_unsigned_to_nat(0u);
v___x_3126_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3126_, 0, v_val_3124_);
lean_ctor_set_uint8(v___x_3126_, sizeof(void*)*1, v___x_3121_);
lean_inc_ref(v_e_3089_);
v___x_3127_ = l_Lean_Meta_Grind_Arith_CommRing_reify_x3f(v_e_3089_, v_ring_3107_, v___x_3125_, v___x_3126_, v_a_3091_, v_a_3092_, v_a_3093_, v_a_3094_, v_a_3095_, v_a_3096_, v_a_3097_, v_a_3098_, v_a_3099_, v_a_3100_);
if (lean_obj_tag(v___x_3127_) == 0)
{
lean_object* v_a_3128_; lean_object* v___x_3130_; uint8_t v_isShared_3131_; uint8_t v_isSharedCheck_3178_; 
v_a_3128_ = lean_ctor_get(v___x_3127_, 0);
v_isSharedCheck_3178_ = !lean_is_exclusive(v___x_3127_);
if (v_isSharedCheck_3178_ == 0)
{
v___x_3130_ = v___x_3127_;
v_isShared_3131_ = v_isSharedCheck_3178_;
goto v_resetjp_3129_;
}
else
{
lean_inc(v_a_3128_);
lean_dec(v___x_3127_);
v___x_3130_ = lean_box(0);
v_isShared_3131_ = v_isSharedCheck_3178_;
goto v_resetjp_3129_;
}
v_resetjp_3129_:
{
if (lean_obj_tag(v_a_3128_) == 1)
{
lean_object* v_options_3132_; lean_object* v_val_3133_; lean_object* v_inheritedTraceOptions_3134_; uint8_t v_hasTrace_3135_; lean_object* v___f_3136_; lean_object* v___y_3138_; lean_object* v___y_3139_; lean_object* v___y_3140_; lean_object* v___y_3141_; lean_object* v___y_3142_; lean_object* v___y_3143_; lean_object* v___y_3144_; lean_object* v___y_3145_; lean_object* v___y_3146_; lean_object* v___y_3147_; lean_object* v___y_3148_; 
lean_del_object(v___x_3130_);
v_options_3132_ = lean_ctor_get(v_a_3099_, 2);
v_val_3133_ = lean_ctor_get(v_a_3128_, 0);
lean_inc(v_val_3133_);
lean_dec_ref(v_a_3128_);
v_inheritedTraceOptions_3134_ = lean_ctor_get(v_a_3099_, 13);
v_hasTrace_3135_ = lean_ctor_get_uint8(v_options_3132_, sizeof(void*)*1);
lean_inc_ref(v_e_3089_);
v___f_3136_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_internalize___lam__0), 3, 2);
lean_closure_set(v___f_3136_, 0, v_e_3089_);
lean_closure_set(v___f_3136_, 1, v_val_3133_);
if (v_hasTrace_3135_ == 0)
{
lean_dec(v_val_3124_);
v___y_3138_ = v___x_3126_;
v___y_3139_ = v_a_3091_;
v___y_3140_ = v_a_3092_;
v___y_3141_ = v_a_3093_;
v___y_3142_ = v_a_3094_;
v___y_3143_ = v_a_3095_;
v___y_3144_ = v_a_3096_;
v___y_3145_ = v_a_3097_;
v___y_3146_ = v_a_3098_;
v___y_3147_ = v_a_3099_;
v___y_3148_ = v_a_3100_;
goto v___jp_3137_;
}
else
{
lean_object* v___x_3153_; lean_object* v___x_3154_; uint8_t v___x_3155_; 
v___x_3153_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__3));
v___x_3154_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__6, &l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__6_once, _init_l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__6);
v___x_3155_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3134_, v_options_3132_, v___x_3154_);
if (v___x_3155_ == 0)
{
lean_dec(v_val_3124_);
v___y_3138_ = v___x_3126_;
v___y_3139_ = v_a_3091_;
v___y_3140_ = v_a_3092_;
v___y_3141_ = v_a_3093_;
v___y_3142_ = v_a_3094_;
v___y_3143_ = v_a_3095_;
v___y_3144_ = v_a_3096_;
v___y_3145_ = v_a_3097_;
v___y_3146_ = v_a_3098_;
v___y_3147_ = v_a_3099_;
v___y_3148_ = v_a_3100_;
goto v___jp_3137_;
}
else
{
lean_object* v___x_3156_; 
v___x_3156_ = l_Lean_Meta_Grind_updateLastTag(v_a_3091_, v_a_3092_, v_a_3093_, v_a_3094_, v_a_3095_, v_a_3096_, v_a_3097_, v_a_3098_, v_a_3099_, v_a_3100_);
if (lean_obj_tag(v___x_3156_) == 0)
{
lean_object* v___x_3158_; uint8_t v_isShared_3159_; uint8_t v_isSharedCheck_3172_; 
v_isSharedCheck_3172_ = !lean_is_exclusive(v___x_3156_);
if (v_isSharedCheck_3172_ == 0)
{
lean_object* v_unused_3173_; 
v_unused_3173_ = lean_ctor_get(v___x_3156_, 0);
lean_dec(v_unused_3173_);
v___x_3158_ = v___x_3156_;
v_isShared_3159_ = v_isSharedCheck_3172_;
goto v_resetjp_3157_;
}
else
{
lean_dec(v___x_3156_);
v___x_3158_ = lean_box(0);
v_isShared_3159_ = v_isSharedCheck_3172_;
goto v_resetjp_3157_;
}
v_resetjp_3157_:
{
lean_object* v___x_3160_; lean_object* v___x_3161_; lean_object* v___x_3163_; 
v___x_3160_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__8, &l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__8_once, _init_l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__8);
v___x_3161_ = l_Nat_reprFast(v_val_3124_);
if (v_isShared_3159_ == 0)
{
lean_ctor_set_tag(v___x_3158_, 3);
lean_ctor_set(v___x_3158_, 0, v___x_3161_);
v___x_3163_ = v___x_3158_;
goto v_reusejp_3162_;
}
else
{
lean_object* v_reuseFailAlloc_3171_; 
v_reuseFailAlloc_3171_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3171_, 0, v___x_3161_);
v___x_3163_ = v_reuseFailAlloc_3171_;
goto v_reusejp_3162_;
}
v_reusejp_3162_:
{
lean_object* v___x_3164_; lean_object* v___x_3165_; lean_object* v___x_3166_; lean_object* v___x_3167_; lean_object* v___x_3168_; lean_object* v___x_3169_; lean_object* v___x_3170_; 
v___x_3164_ = l_Lean_MessageData_ofFormat(v___x_3163_);
v___x_3165_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3165_, 0, v___x_3160_);
lean_ctor_set(v___x_3165_, 1, v___x_3164_);
v___x_3166_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__10, &l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__10_once, _init_l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__10);
v___x_3167_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3167_, 0, v___x_3165_);
lean_ctor_set(v___x_3167_, 1, v___x_3166_);
lean_inc_ref(v_e_3089_);
v___x_3168_ = l_Lean_MessageData_ofExpr(v_e_3089_);
v___x_3169_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3169_, 0, v___x_3167_);
lean_ctor_set(v___x_3169_, 1, v___x_3168_);
v___x_3170_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__1___redArg(v___x_3153_, v___x_3169_, v_a_3097_, v_a_3098_, v_a_3099_, v_a_3100_);
if (lean_obj_tag(v___x_3170_) == 0)
{
lean_dec_ref(v___x_3170_);
v___y_3138_ = v___x_3126_;
v___y_3139_ = v_a_3091_;
v___y_3140_ = v_a_3092_;
v___y_3141_ = v_a_3093_;
v___y_3142_ = v_a_3094_;
v___y_3143_ = v_a_3095_;
v___y_3144_ = v_a_3096_;
v___y_3145_ = v_a_3097_;
v___y_3146_ = v_a_3098_;
v___y_3147_ = v_a_3099_;
v___y_3148_ = v_a_3100_;
goto v___jp_3137_;
}
else
{
lean_dec_ref(v___f_3136_);
lean_dec_ref(v___x_3126_);
lean_dec_ref(v_e_3089_);
return v___x_3170_;
}
}
}
}
else
{
lean_dec_ref(v___f_3136_);
lean_dec_ref(v___x_3126_);
lean_dec(v_val_3124_);
lean_dec_ref(v_e_3089_);
return v___x_3156_;
}
}
}
v___jp_3137_:
{
lean_object* v___x_3149_; 
lean_inc_ref(v_e_3089_);
v___x_3149_ = l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg(v_e_3089_, v___y_3138_, v___y_3139_, v___y_3143_, v___y_3144_, v___y_3145_, v___y_3146_, v___y_3147_, v___y_3148_);
if (lean_obj_tag(v___x_3149_) == 0)
{
lean_object* v___x_3150_; lean_object* v___x_3151_; 
lean_dec_ref(v___x_3149_);
v___x_3150_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_3151_ = l_Lean_Meta_Grind_SolverExtension_markTerm___redArg(v___x_3150_, v_e_3089_, v___y_3139_, v___y_3140_, v___y_3141_, v___y_3142_, v___y_3143_, v___y_3144_, v___y_3145_, v___y_3146_, v___y_3147_, v___y_3148_);
if (lean_obj_tag(v___x_3151_) == 0)
{
lean_object* v___x_3152_; 
lean_dec_ref(v___x_3151_);
v___x_3152_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(v___f_3136_, v___y_3138_, v___y_3139_);
lean_dec_ref(v___y_3138_);
return v___x_3152_;
}
else
{
lean_dec_ref(v___y_3138_);
lean_dec_ref(v___f_3136_);
return v___x_3151_;
}
}
else
{
lean_dec_ref(v___y_3138_);
lean_dec_ref(v___f_3136_);
lean_dec_ref(v_e_3089_);
return v___x_3149_;
}
}
}
else
{
lean_object* v___x_3174_; lean_object* v___x_3176_; 
lean_dec(v_a_3128_);
lean_dec_ref(v___x_3126_);
lean_dec(v_val_3124_);
lean_dec_ref(v_e_3089_);
v___x_3174_ = lean_box(0);
if (v_isShared_3131_ == 0)
{
lean_ctor_set(v___x_3130_, 0, v___x_3174_);
v___x_3176_ = v___x_3130_;
goto v_reusejp_3175_;
}
else
{
lean_object* v_reuseFailAlloc_3177_; 
v_reuseFailAlloc_3177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3177_, 0, v___x_3174_);
v___x_3176_ = v_reuseFailAlloc_3177_;
goto v_reusejp_3175_;
}
v_reusejp_3175_:
{
return v___x_3176_;
}
}
}
}
else
{
lean_object* v_a_3179_; lean_object* v___x_3181_; uint8_t v_isShared_3182_; uint8_t v_isSharedCheck_3186_; 
lean_dec_ref(v___x_3126_);
lean_dec(v_val_3124_);
lean_dec_ref(v_e_3089_);
v_a_3179_ = lean_ctor_get(v___x_3127_, 0);
v_isSharedCheck_3186_ = !lean_is_exclusive(v___x_3127_);
if (v_isSharedCheck_3186_ == 0)
{
v___x_3181_ = v___x_3127_;
v_isShared_3182_ = v_isSharedCheck_3186_;
goto v_resetjp_3180_;
}
else
{
lean_inc(v_a_3179_);
lean_dec(v___x_3127_);
v___x_3181_ = lean_box(0);
v_isShared_3182_ = v_isSharedCheck_3186_;
goto v_resetjp_3180_;
}
v_resetjp_3180_:
{
lean_object* v___x_3184_; 
if (v_isShared_3182_ == 0)
{
v___x_3184_ = v___x_3181_;
goto v_reusejp_3183_;
}
else
{
lean_object* v_reuseFailAlloc_3185_; 
v_reuseFailAlloc_3185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3185_, 0, v_a_3179_);
v___x_3184_ = v_reuseFailAlloc_3185_;
goto v_reusejp_3183_;
}
v_reusejp_3183_:
{
return v___x_3184_;
}
}
}
}
else
{
lean_object* v___x_3187_; 
lean_dec(v_a_3123_);
lean_inc(v_val_3120_);
v___x_3187_ = l_Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f(v_val_3120_, v_a_3091_, v_a_3092_, v_a_3093_, v_a_3094_, v_a_3095_, v_a_3096_, v_a_3097_, v_a_3098_, v_a_3099_, v_a_3100_);
if (lean_obj_tag(v___x_3187_) == 0)
{
lean_object* v_a_3188_; 
v_a_3188_ = lean_ctor_get(v___x_3187_, 0);
lean_inc(v_a_3188_);
lean_dec_ref(v___x_3187_);
if (lean_obj_tag(v_a_3188_) == 1)
{
lean_object* v_val_3189_; lean_object* v___x_3190_; 
lean_dec(v_val_3120_);
v_val_3189_ = lean_ctor_get(v_a_3188_, 0);
lean_inc(v_val_3189_);
lean_dec_ref(v_a_3188_);
lean_inc_ref(v_e_3089_);
v___x_3190_ = l_Lean_Meta_Grind_Arith_CommRing_sreify_x3f(v_e_3089_, v_val_3189_, v_a_3091_, v_a_3092_, v_a_3093_, v_a_3094_, v_a_3095_, v_a_3096_, v_a_3097_, v_a_3098_, v_a_3099_, v_a_3100_);
if (lean_obj_tag(v___x_3190_) == 0)
{
lean_object* v_a_3191_; lean_object* v___x_3193_; uint8_t v_isShared_3194_; uint8_t v_isSharedCheck_3241_; 
v_a_3191_ = lean_ctor_get(v___x_3190_, 0);
v_isSharedCheck_3241_ = !lean_is_exclusive(v___x_3190_);
if (v_isSharedCheck_3241_ == 0)
{
v___x_3193_ = v___x_3190_;
v_isShared_3194_ = v_isSharedCheck_3241_;
goto v_resetjp_3192_;
}
else
{
lean_inc(v_a_3191_);
lean_dec(v___x_3190_);
v___x_3193_ = lean_box(0);
v_isShared_3194_ = v_isSharedCheck_3241_;
goto v_resetjp_3192_;
}
v_resetjp_3192_:
{
if (lean_obj_tag(v_a_3191_) == 1)
{
lean_object* v_val_3195_; lean_object* v___y_3197_; lean_object* v___y_3198_; lean_object* v___y_3199_; lean_object* v___y_3200_; lean_object* v___y_3201_; lean_object* v___y_3202_; lean_object* v___y_3203_; lean_object* v___y_3204_; lean_object* v___y_3205_; lean_object* v___y_3206_; lean_object* v___y_3207_; lean_object* v_options_3213_; uint8_t v_hasTrace_3214_; 
lean_del_object(v___x_3193_);
v_val_3195_ = lean_ctor_get(v_a_3191_, 0);
lean_inc(v_val_3195_);
lean_dec_ref(v_a_3191_);
v_options_3213_ = lean_ctor_get(v_a_3099_, 2);
v_hasTrace_3214_ = lean_ctor_get_uint8(v_options_3213_, sizeof(void*)*1);
if (v_hasTrace_3214_ == 0)
{
v___y_3197_ = v_val_3189_;
v___y_3198_ = v_a_3091_;
v___y_3199_ = v_a_3092_;
v___y_3200_ = v_a_3093_;
v___y_3201_ = v_a_3094_;
v___y_3202_ = v_a_3095_;
v___y_3203_ = v_a_3096_;
v___y_3204_ = v_a_3097_;
v___y_3205_ = v_a_3098_;
v___y_3206_ = v_a_3099_;
v___y_3207_ = v_a_3100_;
goto v___jp_3196_;
}
else
{
lean_object* v_inheritedTraceOptions_3215_; lean_object* v___x_3216_; lean_object* v___x_3217_; uint8_t v___x_3218_; 
v_inheritedTraceOptions_3215_ = lean_ctor_get(v_a_3099_, 13);
v___x_3216_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__3));
v___x_3217_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__6, &l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__6_once, _init_l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__6);
v___x_3218_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3215_, v_options_3213_, v___x_3217_);
if (v___x_3218_ == 0)
{
v___y_3197_ = v_val_3189_;
v___y_3198_ = v_a_3091_;
v___y_3199_ = v_a_3092_;
v___y_3200_ = v_a_3093_;
v___y_3201_ = v_a_3094_;
v___y_3202_ = v_a_3095_;
v___y_3203_ = v_a_3096_;
v___y_3204_ = v_a_3097_;
v___y_3205_ = v_a_3098_;
v___y_3206_ = v_a_3099_;
v___y_3207_ = v_a_3100_;
goto v___jp_3196_;
}
else
{
lean_object* v___x_3219_; 
v___x_3219_ = l_Lean_Meta_Grind_updateLastTag(v_a_3091_, v_a_3092_, v_a_3093_, v_a_3094_, v_a_3095_, v_a_3096_, v_a_3097_, v_a_3098_, v_a_3099_, v_a_3100_);
if (lean_obj_tag(v___x_3219_) == 0)
{
lean_object* v___x_3221_; uint8_t v_isShared_3222_; uint8_t v_isSharedCheck_3235_; 
v_isSharedCheck_3235_ = !lean_is_exclusive(v___x_3219_);
if (v_isSharedCheck_3235_ == 0)
{
lean_object* v_unused_3236_; 
v_unused_3236_ = lean_ctor_get(v___x_3219_, 0);
lean_dec(v_unused_3236_);
v___x_3221_ = v___x_3219_;
v_isShared_3222_ = v_isSharedCheck_3235_;
goto v_resetjp_3220_;
}
else
{
lean_dec(v___x_3219_);
v___x_3221_ = lean_box(0);
v_isShared_3222_ = v_isSharedCheck_3235_;
goto v_resetjp_3220_;
}
v_resetjp_3220_:
{
lean_object* v___x_3223_; lean_object* v___x_3224_; lean_object* v___x_3226_; 
v___x_3223_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__12, &l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__12_once, _init_l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__12);
lean_inc(v_val_3189_);
v___x_3224_ = l_Nat_reprFast(v_val_3189_);
if (v_isShared_3222_ == 0)
{
lean_ctor_set_tag(v___x_3221_, 3);
lean_ctor_set(v___x_3221_, 0, v___x_3224_);
v___x_3226_ = v___x_3221_;
goto v_reusejp_3225_;
}
else
{
lean_object* v_reuseFailAlloc_3234_; 
v_reuseFailAlloc_3234_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3234_, 0, v___x_3224_);
v___x_3226_ = v_reuseFailAlloc_3234_;
goto v_reusejp_3225_;
}
v_reusejp_3225_:
{
lean_object* v___x_3227_; lean_object* v___x_3228_; lean_object* v___x_3229_; lean_object* v___x_3230_; lean_object* v___x_3231_; lean_object* v___x_3232_; lean_object* v___x_3233_; 
v___x_3227_ = l_Lean_MessageData_ofFormat(v___x_3226_);
v___x_3228_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3228_, 0, v___x_3223_);
lean_ctor_set(v___x_3228_, 1, v___x_3227_);
v___x_3229_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__10, &l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__10_once, _init_l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__10);
v___x_3230_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3230_, 0, v___x_3228_);
lean_ctor_set(v___x_3230_, 1, v___x_3229_);
lean_inc_ref(v_e_3089_);
v___x_3231_ = l_Lean_MessageData_ofExpr(v_e_3089_);
v___x_3232_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3232_, 0, v___x_3230_);
lean_ctor_set(v___x_3232_, 1, v___x_3231_);
v___x_3233_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__2___redArg(v___x_3216_, v___x_3232_, v_a_3097_, v_a_3098_, v_a_3099_, v_a_3100_);
if (lean_obj_tag(v___x_3233_) == 0)
{
lean_dec_ref(v___x_3233_);
v___y_3197_ = v_val_3189_;
v___y_3198_ = v_a_3091_;
v___y_3199_ = v_a_3092_;
v___y_3200_ = v_a_3093_;
v___y_3201_ = v_a_3094_;
v___y_3202_ = v_a_3095_;
v___y_3203_ = v_a_3096_;
v___y_3204_ = v_a_3097_;
v___y_3205_ = v_a_3098_;
v___y_3206_ = v_a_3099_;
v___y_3207_ = v_a_3100_;
goto v___jp_3196_;
}
else
{
lean_dec(v_val_3195_);
lean_dec(v_val_3189_);
lean_dec_ref(v_e_3089_);
return v___x_3233_;
}
}
}
}
else
{
lean_dec(v_val_3195_);
lean_dec(v_val_3189_);
lean_dec_ref(v_e_3089_);
return v___x_3219_;
}
}
}
v___jp_3196_:
{
lean_object* v___x_3208_; 
lean_inc_ref(v_e_3089_);
v___x_3208_ = l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg(v_e_3089_, v___y_3197_, v___y_3198_, v___y_3202_, v___y_3203_, v___y_3204_, v___y_3205_, v___y_3206_, v___y_3207_);
if (lean_obj_tag(v___x_3208_) == 0)
{
lean_object* v___x_3209_; lean_object* v___x_3210_; 
lean_dec_ref(v___x_3208_);
v___x_3209_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
lean_inc_ref(v_e_3089_);
v___x_3210_ = l_Lean_Meta_Grind_SolverExtension_markTerm___redArg(v___x_3209_, v_e_3089_, v___y_3198_, v___y_3199_, v___y_3200_, v___y_3201_, v___y_3202_, v___y_3203_, v___y_3204_, v___y_3205_, v___y_3206_, v___y_3207_);
if (lean_obj_tag(v___x_3210_) == 0)
{
lean_object* v___f_3211_; lean_object* v___x_3212_; 
lean_dec_ref(v___x_3210_);
v___f_3211_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_internalize___lam__1___boxed), 4, 3);
lean_closure_set(v___f_3211_, 0, v___y_3197_);
lean_closure_set(v___f_3211_, 1, v_e_3089_);
lean_closure_set(v___f_3211_, 2, v_val_3195_);
v___x_3212_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_3209_, v___f_3211_, v___y_3198_);
return v___x_3212_;
}
else
{
lean_dec(v___y_3197_);
lean_dec(v_val_3195_);
lean_dec_ref(v_e_3089_);
return v___x_3210_;
}
}
else
{
lean_dec(v___y_3197_);
lean_dec(v_val_3195_);
lean_dec_ref(v_e_3089_);
return v___x_3208_;
}
}
}
else
{
lean_object* v___x_3237_; lean_object* v___x_3239_; 
lean_dec(v_a_3191_);
lean_dec(v_val_3189_);
lean_dec_ref(v_e_3089_);
v___x_3237_ = lean_box(0);
if (v_isShared_3194_ == 0)
{
lean_ctor_set(v___x_3193_, 0, v___x_3237_);
v___x_3239_ = v___x_3193_;
goto v_reusejp_3238_;
}
else
{
lean_object* v_reuseFailAlloc_3240_; 
v_reuseFailAlloc_3240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3240_, 0, v___x_3237_);
v___x_3239_ = v_reuseFailAlloc_3240_;
goto v_reusejp_3238_;
}
v_reusejp_3238_:
{
return v___x_3239_;
}
}
}
}
else
{
lean_object* v_a_3242_; lean_object* v___x_3244_; uint8_t v_isShared_3245_; uint8_t v_isSharedCheck_3249_; 
lean_dec(v_val_3189_);
lean_dec_ref(v_e_3089_);
v_a_3242_ = lean_ctor_get(v___x_3190_, 0);
v_isSharedCheck_3249_ = !lean_is_exclusive(v___x_3190_);
if (v_isSharedCheck_3249_ == 0)
{
v___x_3244_ = v___x_3190_;
v_isShared_3245_ = v_isSharedCheck_3249_;
goto v_resetjp_3243_;
}
else
{
lean_inc(v_a_3242_);
lean_dec(v___x_3190_);
v___x_3244_ = lean_box(0);
v_isShared_3245_ = v_isSharedCheck_3249_;
goto v_resetjp_3243_;
}
v_resetjp_3243_:
{
lean_object* v___x_3247_; 
if (v_isShared_3245_ == 0)
{
v___x_3247_ = v___x_3244_;
goto v_reusejp_3246_;
}
else
{
lean_object* v_reuseFailAlloc_3248_; 
v_reuseFailAlloc_3248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3248_, 0, v_a_3242_);
v___x_3247_ = v_reuseFailAlloc_3248_;
goto v_reusejp_3246_;
}
v_reusejp_3246_:
{
return v___x_3247_;
}
}
}
}
else
{
lean_object* v___x_3250_; 
lean_dec(v_a_3188_);
lean_inc(v_val_3120_);
v___x_3250_ = l_Lean_Meta_Grind_Arith_CommRing_getNonCommRingId_x3f(v_val_3120_, v_a_3091_, v_a_3092_, v_a_3093_, v_a_3094_, v_a_3095_, v_a_3096_, v_a_3097_, v_a_3098_, v_a_3099_, v_a_3100_);
if (lean_obj_tag(v___x_3250_) == 0)
{
lean_object* v_a_3251_; 
v_a_3251_ = lean_ctor_get(v___x_3250_, 0);
lean_inc(v_a_3251_);
lean_dec_ref(v___x_3250_);
if (lean_obj_tag(v_a_3251_) == 1)
{
lean_object* v_val_3252_; lean_object* v___x_3253_; lean_object* v___x_3254_; 
lean_dec(v_val_3120_);
v_val_3252_ = lean_ctor_get(v_a_3251_, 0);
lean_inc(v_val_3252_);
lean_dec_ref(v_a_3251_);
v___x_3253_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_e_3089_);
v___x_3254_ = l_Lean_Meta_Grind_Arith_CommRing_ncreify_x3f(v_e_3089_, v_ring_3107_, v___x_3253_, v_val_3252_, v_a_3091_, v_a_3092_, v_a_3093_, v_a_3094_, v_a_3095_, v_a_3096_, v_a_3097_, v_a_3098_, v_a_3099_, v_a_3100_);
if (lean_obj_tag(v___x_3254_) == 0)
{
lean_object* v_a_3255_; lean_object* v___x_3257_; uint8_t v_isShared_3258_; uint8_t v_isSharedCheck_3305_; 
v_a_3255_ = lean_ctor_get(v___x_3254_, 0);
v_isSharedCheck_3305_ = !lean_is_exclusive(v___x_3254_);
if (v_isSharedCheck_3305_ == 0)
{
v___x_3257_ = v___x_3254_;
v_isShared_3258_ = v_isSharedCheck_3305_;
goto v_resetjp_3256_;
}
else
{
lean_inc(v_a_3255_);
lean_dec(v___x_3254_);
v___x_3257_ = lean_box(0);
v_isShared_3258_ = v_isSharedCheck_3305_;
goto v_resetjp_3256_;
}
v_resetjp_3256_:
{
if (lean_obj_tag(v_a_3255_) == 1)
{
lean_object* v_options_3259_; lean_object* v_val_3260_; lean_object* v_inheritedTraceOptions_3261_; uint8_t v_hasTrace_3262_; lean_object* v___f_3263_; lean_object* v___y_3265_; lean_object* v___y_3266_; lean_object* v___y_3267_; lean_object* v___y_3268_; lean_object* v___y_3269_; lean_object* v___y_3270_; lean_object* v___y_3271_; lean_object* v___y_3272_; lean_object* v___y_3273_; lean_object* v___y_3274_; lean_object* v___y_3275_; 
lean_del_object(v___x_3257_);
v_options_3259_ = lean_ctor_get(v_a_3099_, 2);
v_val_3260_ = lean_ctor_get(v_a_3255_, 0);
lean_inc(v_val_3260_);
lean_dec_ref(v_a_3255_);
v_inheritedTraceOptions_3261_ = lean_ctor_get(v_a_3099_, 13);
v_hasTrace_3262_ = lean_ctor_get_uint8(v_options_3259_, sizeof(void*)*1);
lean_inc_ref(v_e_3089_);
v___f_3263_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_internalize___lam__2), 3, 2);
lean_closure_set(v___f_3263_, 0, v_e_3089_);
lean_closure_set(v___f_3263_, 1, v_val_3260_);
if (v_hasTrace_3262_ == 0)
{
v___y_3265_ = v_val_3252_;
v___y_3266_ = v_a_3091_;
v___y_3267_ = v_a_3092_;
v___y_3268_ = v_a_3093_;
v___y_3269_ = v_a_3094_;
v___y_3270_ = v_a_3095_;
v___y_3271_ = v_a_3096_;
v___y_3272_ = v_a_3097_;
v___y_3273_ = v_a_3098_;
v___y_3274_ = v_a_3099_;
v___y_3275_ = v_a_3100_;
goto v___jp_3264_;
}
else
{
lean_object* v___x_3280_; lean_object* v___x_3281_; uint8_t v___x_3282_; 
v___x_3280_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__3));
v___x_3281_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__6, &l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__6_once, _init_l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__6);
v___x_3282_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3261_, v_options_3259_, v___x_3281_);
if (v___x_3282_ == 0)
{
v___y_3265_ = v_val_3252_;
v___y_3266_ = v_a_3091_;
v___y_3267_ = v_a_3092_;
v___y_3268_ = v_a_3093_;
v___y_3269_ = v_a_3094_;
v___y_3270_ = v_a_3095_;
v___y_3271_ = v_a_3096_;
v___y_3272_ = v_a_3097_;
v___y_3273_ = v_a_3098_;
v___y_3274_ = v_a_3099_;
v___y_3275_ = v_a_3100_;
goto v___jp_3264_;
}
else
{
lean_object* v___x_3283_; 
v___x_3283_ = l_Lean_Meta_Grind_updateLastTag(v_a_3091_, v_a_3092_, v_a_3093_, v_a_3094_, v_a_3095_, v_a_3096_, v_a_3097_, v_a_3098_, v_a_3099_, v_a_3100_);
if (lean_obj_tag(v___x_3283_) == 0)
{
lean_object* v___x_3285_; uint8_t v_isShared_3286_; uint8_t v_isSharedCheck_3299_; 
v_isSharedCheck_3299_ = !lean_is_exclusive(v___x_3283_);
if (v_isSharedCheck_3299_ == 0)
{
lean_object* v_unused_3300_; 
v_unused_3300_ = lean_ctor_get(v___x_3283_, 0);
lean_dec(v_unused_3300_);
v___x_3285_ = v___x_3283_;
v_isShared_3286_ = v_isSharedCheck_3299_;
goto v_resetjp_3284_;
}
else
{
lean_dec(v___x_3283_);
v___x_3285_ = lean_box(0);
v_isShared_3286_ = v_isSharedCheck_3299_;
goto v_resetjp_3284_;
}
v_resetjp_3284_:
{
lean_object* v___x_3287_; lean_object* v___x_3288_; lean_object* v___x_3290_; 
v___x_3287_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__14, &l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__14_once, _init_l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__14);
lean_inc(v_val_3252_);
v___x_3288_ = l_Nat_reprFast(v_val_3252_);
if (v_isShared_3286_ == 0)
{
lean_ctor_set_tag(v___x_3285_, 3);
lean_ctor_set(v___x_3285_, 0, v___x_3288_);
v___x_3290_ = v___x_3285_;
goto v_reusejp_3289_;
}
else
{
lean_object* v_reuseFailAlloc_3298_; 
v_reuseFailAlloc_3298_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3298_, 0, v___x_3288_);
v___x_3290_ = v_reuseFailAlloc_3298_;
goto v_reusejp_3289_;
}
v_reusejp_3289_:
{
lean_object* v___x_3291_; lean_object* v___x_3292_; lean_object* v___x_3293_; lean_object* v___x_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; lean_object* v___x_3297_; 
v___x_3291_ = l_Lean_MessageData_ofFormat(v___x_3290_);
v___x_3292_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3292_, 0, v___x_3287_);
lean_ctor_set(v___x_3292_, 1, v___x_3291_);
v___x_3293_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__10, &l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__10_once, _init_l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__10);
v___x_3294_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3294_, 0, v___x_3292_);
lean_ctor_set(v___x_3294_, 1, v___x_3293_);
lean_inc_ref(v_e_3089_);
v___x_3295_ = l_Lean_MessageData_ofExpr(v_e_3089_);
v___x_3296_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3296_, 0, v___x_3294_);
lean_ctor_set(v___x_3296_, 1, v___x_3295_);
v___x_3297_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__3___redArg(v___x_3280_, v___x_3296_, v_a_3097_, v_a_3098_, v_a_3099_, v_a_3100_);
if (lean_obj_tag(v___x_3297_) == 0)
{
lean_dec_ref(v___x_3297_);
v___y_3265_ = v_val_3252_;
v___y_3266_ = v_a_3091_;
v___y_3267_ = v_a_3092_;
v___y_3268_ = v_a_3093_;
v___y_3269_ = v_a_3094_;
v___y_3270_ = v_a_3095_;
v___y_3271_ = v_a_3096_;
v___y_3272_ = v_a_3097_;
v___y_3273_ = v_a_3098_;
v___y_3274_ = v_a_3099_;
v___y_3275_ = v_a_3100_;
goto v___jp_3264_;
}
else
{
lean_dec_ref(v___f_3263_);
lean_dec(v_val_3252_);
lean_dec_ref(v_e_3089_);
return v___x_3297_;
}
}
}
}
else
{
lean_dec_ref(v___f_3263_);
lean_dec(v_val_3252_);
lean_dec_ref(v_e_3089_);
return v___x_3283_;
}
}
}
v___jp_3264_:
{
lean_object* v___x_3276_; 
lean_inc_ref(v_e_3089_);
v___x_3276_ = l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId___redArg(v_e_3089_, v___y_3265_, v___y_3266_, v___y_3270_, v___y_3271_, v___y_3272_, v___y_3273_, v___y_3274_, v___y_3275_);
if (lean_obj_tag(v___x_3276_) == 0)
{
lean_object* v___x_3277_; lean_object* v___x_3278_; 
lean_dec_ref(v___x_3276_);
v___x_3277_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_3278_ = l_Lean_Meta_Grind_SolverExtension_markTerm___redArg(v___x_3277_, v_e_3089_, v___y_3266_, v___y_3267_, v___y_3268_, v___y_3269_, v___y_3270_, v___y_3271_, v___y_3272_, v___y_3273_, v___y_3274_, v___y_3275_);
if (lean_obj_tag(v___x_3278_) == 0)
{
lean_object* v___x_3279_; 
lean_dec_ref(v___x_3278_);
v___x_3279_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_modifyRing___redArg(v___f_3263_, v___y_3265_, v___y_3266_);
lean_dec(v___y_3265_);
return v___x_3279_;
}
else
{
lean_dec(v___y_3265_);
lean_dec_ref(v___f_3263_);
return v___x_3278_;
}
}
else
{
lean_dec(v___y_3265_);
lean_dec_ref(v___f_3263_);
lean_dec_ref(v_e_3089_);
return v___x_3276_;
}
}
}
else
{
lean_object* v___x_3301_; lean_object* v___x_3303_; 
lean_dec(v_a_3255_);
lean_dec(v_val_3252_);
lean_dec_ref(v_e_3089_);
v___x_3301_ = lean_box(0);
if (v_isShared_3258_ == 0)
{
lean_ctor_set(v___x_3257_, 0, v___x_3301_);
v___x_3303_ = v___x_3257_;
goto v_reusejp_3302_;
}
else
{
lean_object* v_reuseFailAlloc_3304_; 
v_reuseFailAlloc_3304_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3304_, 0, v___x_3301_);
v___x_3303_ = v_reuseFailAlloc_3304_;
goto v_reusejp_3302_;
}
v_reusejp_3302_:
{
return v___x_3303_;
}
}
}
}
else
{
lean_object* v_a_3306_; lean_object* v___x_3308_; uint8_t v_isShared_3309_; uint8_t v_isSharedCheck_3313_; 
lean_dec(v_val_3252_);
lean_dec_ref(v_e_3089_);
v_a_3306_ = lean_ctor_get(v___x_3254_, 0);
v_isSharedCheck_3313_ = !lean_is_exclusive(v___x_3254_);
if (v_isSharedCheck_3313_ == 0)
{
v___x_3308_ = v___x_3254_;
v_isShared_3309_ = v_isSharedCheck_3313_;
goto v_resetjp_3307_;
}
else
{
lean_inc(v_a_3306_);
lean_dec(v___x_3254_);
v___x_3308_ = lean_box(0);
v_isShared_3309_ = v_isSharedCheck_3313_;
goto v_resetjp_3307_;
}
v_resetjp_3307_:
{
lean_object* v___x_3311_; 
if (v_isShared_3309_ == 0)
{
v___x_3311_ = v___x_3308_;
goto v_reusejp_3310_;
}
else
{
lean_object* v_reuseFailAlloc_3312_; 
v_reuseFailAlloc_3312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3312_, 0, v_a_3306_);
v___x_3311_ = v_reuseFailAlloc_3312_;
goto v_reusejp_3310_;
}
v_reusejp_3310_:
{
return v___x_3311_;
}
}
}
}
else
{
lean_object* v___x_3314_; 
lean_dec(v_a_3251_);
v___x_3314_ = l_Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f___redArg(v_val_3120_, v_a_3091_, v_a_3097_, v_a_3098_, v_a_3099_, v_a_3100_);
if (lean_obj_tag(v___x_3314_) == 0)
{
lean_object* v_a_3315_; lean_object* v___x_3317_; uint8_t v_isShared_3318_; uint8_t v_isSharedCheck_3384_; 
v_a_3315_ = lean_ctor_get(v___x_3314_, 0);
v_isSharedCheck_3384_ = !lean_is_exclusive(v___x_3314_);
if (v_isSharedCheck_3384_ == 0)
{
v___x_3317_ = v___x_3314_;
v_isShared_3318_ = v_isSharedCheck_3384_;
goto v_resetjp_3316_;
}
else
{
lean_inc(v_a_3315_);
lean_dec(v___x_3314_);
v___x_3317_ = lean_box(0);
v_isShared_3318_ = v_isSharedCheck_3384_;
goto v_resetjp_3316_;
}
v_resetjp_3316_:
{
if (lean_obj_tag(v_a_3315_) == 1)
{
lean_object* v_val_3319_; lean_object* v___x_3320_; 
lean_del_object(v___x_3317_);
v_val_3319_ = lean_ctor_get(v_a_3315_, 0);
lean_inc(v_val_3319_);
lean_dec_ref(v_a_3315_);
lean_inc_ref(v_e_3089_);
v___x_3320_ = l_Lean_Meta_Grind_Arith_CommRing_ncsreify_x3f(v_e_3089_, v_val_3319_, v_a_3091_, v_a_3092_, v_a_3093_, v_a_3094_, v_a_3095_, v_a_3096_, v_a_3097_, v_a_3098_, v_a_3099_, v_a_3100_);
if (lean_obj_tag(v___x_3320_) == 0)
{
lean_object* v_a_3321_; lean_object* v___x_3323_; uint8_t v_isShared_3324_; uint8_t v_isSharedCheck_3371_; 
v_a_3321_ = lean_ctor_get(v___x_3320_, 0);
v_isSharedCheck_3371_ = !lean_is_exclusive(v___x_3320_);
if (v_isSharedCheck_3371_ == 0)
{
v___x_3323_ = v___x_3320_;
v_isShared_3324_ = v_isSharedCheck_3371_;
goto v_resetjp_3322_;
}
else
{
lean_inc(v_a_3321_);
lean_dec(v___x_3320_);
v___x_3323_ = lean_box(0);
v_isShared_3324_ = v_isSharedCheck_3371_;
goto v_resetjp_3322_;
}
v_resetjp_3322_:
{
if (lean_obj_tag(v_a_3321_) == 1)
{
lean_object* v_options_3325_; lean_object* v_val_3326_; lean_object* v_inheritedTraceOptions_3327_; uint8_t v_hasTrace_3328_; lean_object* v___f_3329_; lean_object* v___y_3331_; lean_object* v___y_3332_; lean_object* v___y_3333_; lean_object* v___y_3334_; lean_object* v___y_3335_; lean_object* v___y_3336_; lean_object* v___y_3337_; lean_object* v___y_3338_; lean_object* v___y_3339_; lean_object* v___y_3340_; lean_object* v___y_3341_; 
lean_del_object(v___x_3323_);
v_options_3325_ = lean_ctor_get(v_a_3099_, 2);
v_val_3326_ = lean_ctor_get(v_a_3321_, 0);
lean_inc(v_val_3326_);
lean_dec_ref(v_a_3321_);
v_inheritedTraceOptions_3327_ = lean_ctor_get(v_a_3099_, 13);
v_hasTrace_3328_ = lean_ctor_get_uint8(v_options_3325_, sizeof(void*)*1);
lean_inc_ref(v_e_3089_);
v___f_3329_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_internalize___lam__3), 3, 2);
lean_closure_set(v___f_3329_, 0, v_e_3089_);
lean_closure_set(v___f_3329_, 1, v_val_3326_);
if (v_hasTrace_3328_ == 0)
{
v___y_3331_ = v_val_3319_;
v___y_3332_ = v_a_3091_;
v___y_3333_ = v_a_3092_;
v___y_3334_ = v_a_3093_;
v___y_3335_ = v_a_3094_;
v___y_3336_ = v_a_3095_;
v___y_3337_ = v_a_3096_;
v___y_3338_ = v_a_3097_;
v___y_3339_ = v_a_3098_;
v___y_3340_ = v_a_3099_;
v___y_3341_ = v_a_3100_;
goto v___jp_3330_;
}
else
{
lean_object* v___x_3346_; lean_object* v___x_3347_; uint8_t v___x_3348_; 
v___x_3346_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__3));
v___x_3347_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__6, &l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__6_once, _init_l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__6);
v___x_3348_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3327_, v_options_3325_, v___x_3347_);
if (v___x_3348_ == 0)
{
v___y_3331_ = v_val_3319_;
v___y_3332_ = v_a_3091_;
v___y_3333_ = v_a_3092_;
v___y_3334_ = v_a_3093_;
v___y_3335_ = v_a_3094_;
v___y_3336_ = v_a_3095_;
v___y_3337_ = v_a_3096_;
v___y_3338_ = v_a_3097_;
v___y_3339_ = v_a_3098_;
v___y_3340_ = v_a_3099_;
v___y_3341_ = v_a_3100_;
goto v___jp_3330_;
}
else
{
lean_object* v___x_3349_; 
v___x_3349_ = l_Lean_Meta_Grind_updateLastTag(v_a_3091_, v_a_3092_, v_a_3093_, v_a_3094_, v_a_3095_, v_a_3096_, v_a_3097_, v_a_3098_, v_a_3099_, v_a_3100_);
if (lean_obj_tag(v___x_3349_) == 0)
{
lean_object* v___x_3351_; uint8_t v_isShared_3352_; uint8_t v_isSharedCheck_3365_; 
v_isSharedCheck_3365_ = !lean_is_exclusive(v___x_3349_);
if (v_isSharedCheck_3365_ == 0)
{
lean_object* v_unused_3366_; 
v_unused_3366_ = lean_ctor_get(v___x_3349_, 0);
lean_dec(v_unused_3366_);
v___x_3351_ = v___x_3349_;
v_isShared_3352_ = v_isSharedCheck_3365_;
goto v_resetjp_3350_;
}
else
{
lean_dec(v___x_3349_);
v___x_3351_ = lean_box(0);
v_isShared_3352_ = v_isSharedCheck_3365_;
goto v_resetjp_3350_;
}
v_resetjp_3350_:
{
lean_object* v___x_3353_; lean_object* v___x_3354_; lean_object* v___x_3356_; 
v___x_3353_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__16, &l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__16_once, _init_l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__16);
lean_inc(v_val_3319_);
v___x_3354_ = l_Nat_reprFast(v_val_3319_);
if (v_isShared_3352_ == 0)
{
lean_ctor_set_tag(v___x_3351_, 3);
lean_ctor_set(v___x_3351_, 0, v___x_3354_);
v___x_3356_ = v___x_3351_;
goto v_reusejp_3355_;
}
else
{
lean_object* v_reuseFailAlloc_3364_; 
v_reuseFailAlloc_3364_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3364_, 0, v___x_3354_);
v___x_3356_ = v_reuseFailAlloc_3364_;
goto v_reusejp_3355_;
}
v_reusejp_3355_:
{
lean_object* v___x_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; 
v___x_3357_ = l_Lean_MessageData_ofFormat(v___x_3356_);
v___x_3358_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3358_, 0, v___x_3353_);
lean_ctor_set(v___x_3358_, 1, v___x_3357_);
v___x_3359_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__10, &l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__10_once, _init_l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__10);
v___x_3360_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3360_, 0, v___x_3358_);
lean_ctor_set(v___x_3360_, 1, v___x_3359_);
lean_inc_ref(v_e_3089_);
v___x_3361_ = l_Lean_MessageData_ofExpr(v_e_3089_);
v___x_3362_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3362_, 0, v___x_3360_);
lean_ctor_set(v___x_3362_, 1, v___x_3361_);
v___x_3363_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__4___redArg(v___x_3346_, v___x_3362_, v_a_3097_, v_a_3098_, v_a_3099_, v_a_3100_);
if (lean_obj_tag(v___x_3363_) == 0)
{
lean_dec_ref(v___x_3363_);
v___y_3331_ = v_val_3319_;
v___y_3332_ = v_a_3091_;
v___y_3333_ = v_a_3092_;
v___y_3334_ = v_a_3093_;
v___y_3335_ = v_a_3094_;
v___y_3336_ = v_a_3095_;
v___y_3337_ = v_a_3096_;
v___y_3338_ = v_a_3097_;
v___y_3339_ = v_a_3098_;
v___y_3340_ = v_a_3099_;
v___y_3341_ = v_a_3100_;
goto v___jp_3330_;
}
else
{
lean_dec_ref(v___f_3329_);
lean_dec(v_val_3319_);
lean_dec_ref(v_e_3089_);
return v___x_3363_;
}
}
}
}
else
{
lean_dec_ref(v___f_3329_);
lean_dec(v_val_3319_);
lean_dec_ref(v_e_3089_);
return v___x_3349_;
}
}
}
v___jp_3330_:
{
lean_object* v___x_3342_; 
lean_inc_ref(v_e_3089_);
v___x_3342_ = l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId___redArg(v_e_3089_, v___y_3331_, v___y_3332_, v___y_3336_, v___y_3337_, v___y_3338_, v___y_3339_, v___y_3340_, v___y_3341_);
if (lean_obj_tag(v___x_3342_) == 0)
{
lean_object* v___x_3343_; lean_object* v___x_3344_; 
lean_dec_ref(v___x_3342_);
v___x_3343_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_3344_ = l_Lean_Meta_Grind_SolverExtension_markTerm___redArg(v___x_3343_, v_e_3089_, v___y_3332_, v___y_3333_, v___y_3334_, v___y_3335_, v___y_3336_, v___y_3337_, v___y_3338_, v___y_3339_, v___y_3340_, v___y_3341_);
if (lean_obj_tag(v___x_3344_) == 0)
{
lean_object* v___x_3345_; 
lean_dec_ref(v___x_3344_);
v___x_3345_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_modifySemiring___redArg(v___f_3329_, v___y_3331_, v___y_3332_);
lean_dec(v___y_3331_);
return v___x_3345_;
}
else
{
lean_dec(v___y_3331_);
lean_dec_ref(v___f_3329_);
return v___x_3344_;
}
}
else
{
lean_dec(v___y_3331_);
lean_dec_ref(v___f_3329_);
lean_dec_ref(v_e_3089_);
return v___x_3342_;
}
}
}
else
{
lean_object* v___x_3367_; lean_object* v___x_3369_; 
lean_dec(v_a_3321_);
lean_dec(v_val_3319_);
lean_dec_ref(v_e_3089_);
v___x_3367_ = lean_box(0);
if (v_isShared_3324_ == 0)
{
lean_ctor_set(v___x_3323_, 0, v___x_3367_);
v___x_3369_ = v___x_3323_;
goto v_reusejp_3368_;
}
else
{
lean_object* v_reuseFailAlloc_3370_; 
v_reuseFailAlloc_3370_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3370_, 0, v___x_3367_);
v___x_3369_ = v_reuseFailAlloc_3370_;
goto v_reusejp_3368_;
}
v_reusejp_3368_:
{
return v___x_3369_;
}
}
}
}
else
{
lean_object* v_a_3372_; lean_object* v___x_3374_; uint8_t v_isShared_3375_; uint8_t v_isSharedCheck_3379_; 
lean_dec(v_val_3319_);
lean_dec_ref(v_e_3089_);
v_a_3372_ = lean_ctor_get(v___x_3320_, 0);
v_isSharedCheck_3379_ = !lean_is_exclusive(v___x_3320_);
if (v_isSharedCheck_3379_ == 0)
{
v___x_3374_ = v___x_3320_;
v_isShared_3375_ = v_isSharedCheck_3379_;
goto v_resetjp_3373_;
}
else
{
lean_inc(v_a_3372_);
lean_dec(v___x_3320_);
v___x_3374_ = lean_box(0);
v_isShared_3375_ = v_isSharedCheck_3379_;
goto v_resetjp_3373_;
}
v_resetjp_3373_:
{
lean_object* v___x_3377_; 
if (v_isShared_3375_ == 0)
{
v___x_3377_ = v___x_3374_;
goto v_reusejp_3376_;
}
else
{
lean_object* v_reuseFailAlloc_3378_; 
v_reuseFailAlloc_3378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3378_, 0, v_a_3372_);
v___x_3377_ = v_reuseFailAlloc_3378_;
goto v_reusejp_3376_;
}
v_reusejp_3376_:
{
return v___x_3377_;
}
}
}
}
else
{
lean_object* v___x_3380_; lean_object* v___x_3382_; 
lean_dec(v_a_3315_);
lean_dec_ref(v_e_3089_);
v___x_3380_ = lean_box(0);
if (v_isShared_3318_ == 0)
{
lean_ctor_set(v___x_3317_, 0, v___x_3380_);
v___x_3382_ = v___x_3317_;
goto v_reusejp_3381_;
}
else
{
lean_object* v_reuseFailAlloc_3383_; 
v_reuseFailAlloc_3383_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3383_, 0, v___x_3380_);
v___x_3382_ = v_reuseFailAlloc_3383_;
goto v_reusejp_3381_;
}
v_reusejp_3381_:
{
return v___x_3382_;
}
}
}
}
else
{
lean_object* v_a_3385_; lean_object* v___x_3387_; uint8_t v_isShared_3388_; uint8_t v_isSharedCheck_3392_; 
lean_dec_ref(v_e_3089_);
v_a_3385_ = lean_ctor_get(v___x_3314_, 0);
v_isSharedCheck_3392_ = !lean_is_exclusive(v___x_3314_);
if (v_isSharedCheck_3392_ == 0)
{
v___x_3387_ = v___x_3314_;
v_isShared_3388_ = v_isSharedCheck_3392_;
goto v_resetjp_3386_;
}
else
{
lean_inc(v_a_3385_);
lean_dec(v___x_3314_);
v___x_3387_ = lean_box(0);
v_isShared_3388_ = v_isSharedCheck_3392_;
goto v_resetjp_3386_;
}
v_resetjp_3386_:
{
lean_object* v___x_3390_; 
if (v_isShared_3388_ == 0)
{
v___x_3390_ = v___x_3387_;
goto v_reusejp_3389_;
}
else
{
lean_object* v_reuseFailAlloc_3391_; 
v_reuseFailAlloc_3391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3391_, 0, v_a_3385_);
v___x_3390_ = v_reuseFailAlloc_3391_;
goto v_reusejp_3389_;
}
v_reusejp_3389_:
{
return v___x_3390_;
}
}
}
}
}
else
{
lean_object* v_a_3393_; lean_object* v___x_3395_; uint8_t v_isShared_3396_; uint8_t v_isSharedCheck_3400_; 
lean_dec(v_val_3120_);
lean_dec_ref(v_e_3089_);
v_a_3393_ = lean_ctor_get(v___x_3250_, 0);
v_isSharedCheck_3400_ = !lean_is_exclusive(v___x_3250_);
if (v_isSharedCheck_3400_ == 0)
{
v___x_3395_ = v___x_3250_;
v_isShared_3396_ = v_isSharedCheck_3400_;
goto v_resetjp_3394_;
}
else
{
lean_inc(v_a_3393_);
lean_dec(v___x_3250_);
v___x_3395_ = lean_box(0);
v_isShared_3396_ = v_isSharedCheck_3400_;
goto v_resetjp_3394_;
}
v_resetjp_3394_:
{
lean_object* v___x_3398_; 
if (v_isShared_3396_ == 0)
{
v___x_3398_ = v___x_3395_;
goto v_reusejp_3397_;
}
else
{
lean_object* v_reuseFailAlloc_3399_; 
v_reuseFailAlloc_3399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3399_, 0, v_a_3393_);
v___x_3398_ = v_reuseFailAlloc_3399_;
goto v_reusejp_3397_;
}
v_reusejp_3397_:
{
return v___x_3398_;
}
}
}
}
}
else
{
lean_object* v_a_3401_; lean_object* v___x_3403_; uint8_t v_isShared_3404_; uint8_t v_isSharedCheck_3408_; 
lean_dec(v_val_3120_);
lean_dec_ref(v_e_3089_);
v_a_3401_ = lean_ctor_get(v___x_3187_, 0);
v_isSharedCheck_3408_ = !lean_is_exclusive(v___x_3187_);
if (v_isSharedCheck_3408_ == 0)
{
v___x_3403_ = v___x_3187_;
v_isShared_3404_ = v_isSharedCheck_3408_;
goto v_resetjp_3402_;
}
else
{
lean_inc(v_a_3401_);
lean_dec(v___x_3187_);
v___x_3403_ = lean_box(0);
v_isShared_3404_ = v_isSharedCheck_3408_;
goto v_resetjp_3402_;
}
v_resetjp_3402_:
{
lean_object* v___x_3406_; 
if (v_isShared_3404_ == 0)
{
v___x_3406_ = v___x_3403_;
goto v_reusejp_3405_;
}
else
{
lean_object* v_reuseFailAlloc_3407_; 
v_reuseFailAlloc_3407_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3407_, 0, v_a_3401_);
v___x_3406_ = v_reuseFailAlloc_3407_;
goto v_reusejp_3405_;
}
v_reusejp_3405_:
{
return v___x_3406_;
}
}
}
}
}
else
{
lean_object* v_a_3409_; lean_object* v___x_3411_; uint8_t v_isShared_3412_; uint8_t v_isSharedCheck_3416_; 
lean_dec(v_val_3120_);
lean_dec_ref(v_e_3089_);
v_a_3409_ = lean_ctor_get(v___x_3122_, 0);
v_isSharedCheck_3416_ = !lean_is_exclusive(v___x_3122_);
if (v_isSharedCheck_3416_ == 0)
{
v___x_3411_ = v___x_3122_;
v_isShared_3412_ = v_isSharedCheck_3416_;
goto v_resetjp_3410_;
}
else
{
lean_inc(v_a_3409_);
lean_dec(v___x_3122_);
v___x_3411_ = lean_box(0);
v_isShared_3412_ = v_isSharedCheck_3416_;
goto v_resetjp_3410_;
}
v_resetjp_3410_:
{
lean_object* v___x_3414_; 
if (v_isShared_3412_ == 0)
{
v___x_3414_ = v___x_3411_;
goto v_reusejp_3413_;
}
else
{
lean_object* v_reuseFailAlloc_3415_; 
v_reuseFailAlloc_3415_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3415_, 0, v_a_3409_);
v___x_3414_ = v_reuseFailAlloc_3415_;
goto v_reusejp_3413_;
}
v_reusejp_3413_:
{
return v___x_3414_;
}
}
}
}
else
{
lean_object* v___x_3417_; lean_object* v___x_3419_; 
lean_dec(v_val_3120_);
lean_dec_ref(v_e_3089_);
v___x_3417_ = lean_box(0);
if (v_isShared_3117_ == 0)
{
lean_ctor_set(v___x_3116_, 0, v___x_3417_);
v___x_3419_ = v___x_3116_;
goto v_reusejp_3418_;
}
else
{
lean_object* v_reuseFailAlloc_3420_; 
v_reuseFailAlloc_3420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3420_, 0, v___x_3417_);
v___x_3419_ = v_reuseFailAlloc_3420_;
goto v_reusejp_3418_;
}
v_reusejp_3418_:
{
return v___x_3419_;
}
}
}
else
{
lean_object* v___x_3421_; lean_object* v___x_3423_; 
lean_dec(v___x_3119_);
lean_dec(v_parent_x3f_3090_);
lean_dec_ref(v_e_3089_);
v___x_3421_ = lean_box(0);
if (v_isShared_3117_ == 0)
{
lean_ctor_set(v___x_3116_, 0, v___x_3421_);
v___x_3423_ = v___x_3116_;
goto v_reusejp_3422_;
}
else
{
lean_object* v_reuseFailAlloc_3424_; 
v_reuseFailAlloc_3424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3424_, 0, v___x_3421_);
v___x_3423_ = v_reuseFailAlloc_3424_;
goto v_reusejp_3422_;
}
v_reusejp_3422_:
{
return v___x_3423_;
}
}
}
else
{
lean_object* v___x_3425_; lean_object* v___x_3427_; 
lean_dec(v_parent_x3f_3090_);
lean_dec_ref(v_e_3089_);
v___x_3425_ = lean_box(0);
if (v_isShared_3117_ == 0)
{
lean_ctor_set(v___x_3116_, 0, v___x_3425_);
v___x_3427_ = v___x_3116_;
goto v_reusejp_3426_;
}
else
{
lean_object* v_reuseFailAlloc_3428_; 
v_reuseFailAlloc_3428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3428_, 0, v___x_3425_);
v___x_3427_ = v_reuseFailAlloc_3428_;
goto v_reusejp_3426_;
}
v_reusejp_3426_:
{
return v___x_3427_;
}
}
}
}
else
{
lean_object* v_a_3430_; lean_object* v___x_3432_; uint8_t v_isShared_3433_; uint8_t v_isSharedCheck_3437_; 
lean_dec(v_parent_x3f_3090_);
lean_dec_ref(v_e_3089_);
v_a_3430_ = lean_ctor_get(v___x_3113_, 0);
v_isSharedCheck_3437_ = !lean_is_exclusive(v___x_3113_);
if (v_isSharedCheck_3437_ == 0)
{
v___x_3432_ = v___x_3113_;
v_isShared_3433_ = v_isSharedCheck_3437_;
goto v_resetjp_3431_;
}
else
{
lean_inc(v_a_3430_);
lean_dec(v___x_3113_);
v___x_3432_ = lean_box(0);
v_isShared_3433_ = v_isSharedCheck_3437_;
goto v_resetjp_3431_;
}
v_resetjp_3431_:
{
lean_object* v___x_3435_; 
if (v_isShared_3433_ == 0)
{
v___x_3435_ = v___x_3432_;
goto v_reusejp_3434_;
}
else
{
lean_object* v_reuseFailAlloc_3436_; 
v_reuseFailAlloc_3436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3436_, 0, v_a_3430_);
v___x_3435_ = v_reuseFailAlloc_3436_;
goto v_reusejp_3434_;
}
v_reusejp_3434_:
{
return v___x_3435_;
}
}
}
}
else
{
lean_object* v___x_3438_; lean_object* v___x_3440_; 
lean_dec(v_parent_x3f_3090_);
lean_dec_ref(v_e_3089_);
v___x_3438_ = lean_box(0);
if (v_isShared_3106_ == 0)
{
lean_ctor_set(v___x_3105_, 0, v___x_3438_);
v___x_3440_ = v___x_3105_;
goto v_reusejp_3439_;
}
else
{
lean_object* v_reuseFailAlloc_3441_; 
v_reuseFailAlloc_3441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3441_, 0, v___x_3438_);
v___x_3440_ = v_reuseFailAlloc_3441_;
goto v_reusejp_3439_;
}
v_reusejp_3439_:
{
return v___x_3440_;
}
}
}
}
}
else
{
lean_object* v_a_3443_; lean_object* v___x_3445_; uint8_t v_isShared_3446_; uint8_t v_isSharedCheck_3450_; 
lean_dec(v_parent_x3f_3090_);
lean_dec_ref(v_e_3089_);
v_a_3443_ = lean_ctor_get(v___x_3102_, 0);
v_isSharedCheck_3450_ = !lean_is_exclusive(v___x_3102_);
if (v_isSharedCheck_3450_ == 0)
{
v___x_3445_ = v___x_3102_;
v_isShared_3446_ = v_isSharedCheck_3450_;
goto v_resetjp_3444_;
}
else
{
lean_inc(v_a_3443_);
lean_dec(v___x_3102_);
v___x_3445_ = lean_box(0);
v_isShared_3446_ = v_isSharedCheck_3450_;
goto v_resetjp_3444_;
}
v_resetjp_3444_:
{
lean_object* v___x_3448_; 
if (v_isShared_3446_ == 0)
{
v___x_3448_ = v___x_3445_;
goto v_reusejp_3447_;
}
else
{
lean_object* v_reuseFailAlloc_3449_; 
v_reuseFailAlloc_3449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3449_, 0, v_a_3443_);
v___x_3448_ = v_reuseFailAlloc_3449_;
goto v_reusejp_3447_;
}
v_reusejp_3447_:
{
return v___x_3448_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_internalize___boxed(lean_object* v_e_3451_, lean_object* v_parent_x3f_3452_, lean_object* v_a_3453_, lean_object* v_a_3454_, lean_object* v_a_3455_, lean_object* v_a_3456_, lean_object* v_a_3457_, lean_object* v_a_3458_, lean_object* v_a_3459_, lean_object* v_a_3460_, lean_object* v_a_3461_, lean_object* v_a_3462_, lean_object* v_a_3463_){
_start:
{
lean_object* v_res_3464_; 
v_res_3464_ = l_Lean_Meta_Grind_Arith_CommRing_internalize(v_e_3451_, v_parent_x3f_3452_, v_a_3453_, v_a_3454_, v_a_3455_, v_a_3456_, v_a_3457_, v_a_3458_, v_a_3459_, v_a_3460_, v_a_3461_, v_a_3462_);
lean_dec(v_a_3462_);
lean_dec_ref(v_a_3461_);
lean_dec(v_a_3460_);
lean_dec_ref(v_a_3459_);
lean_dec(v_a_3458_);
lean_dec_ref(v_a_3457_);
lean_dec(v_a_3456_);
lean_dec_ref(v_a_3455_);
lean_dec(v_a_3454_);
lean_dec(v_a_3453_);
return v_res_3464_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0(lean_object* v_00_u03b2_3465_, lean_object* v_x_3466_, lean_object* v_x_3467_, lean_object* v_x_3468_){
_start:
{
lean_object* v___x_3469_; 
v___x_3469_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0___redArg(v_x_3466_, v_x_3467_, v_x_3468_);
return v___x_3469_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__1(lean_object* v_cls_3470_, lean_object* v_msg_3471_, lean_object* v___y_3472_, lean_object* v___y_3473_, lean_object* v___y_3474_, lean_object* v___y_3475_, lean_object* v___y_3476_, lean_object* v___y_3477_, lean_object* v___y_3478_, lean_object* v___y_3479_, lean_object* v___y_3480_, lean_object* v___y_3481_, lean_object* v___y_3482_){
_start:
{
lean_object* v___x_3484_; 
v___x_3484_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__1___redArg(v_cls_3470_, v_msg_3471_, v___y_3479_, v___y_3480_, v___y_3481_, v___y_3482_);
return v___x_3484_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__1___boxed(lean_object* v_cls_3485_, lean_object* v_msg_3486_, lean_object* v___y_3487_, lean_object* v___y_3488_, lean_object* v___y_3489_, lean_object* v___y_3490_, lean_object* v___y_3491_, lean_object* v___y_3492_, lean_object* v___y_3493_, lean_object* v___y_3494_, lean_object* v___y_3495_, lean_object* v___y_3496_, lean_object* v___y_3497_, lean_object* v___y_3498_){
_start:
{
lean_object* v_res_3499_; 
v_res_3499_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__1(v_cls_3485_, v_msg_3486_, v___y_3487_, v___y_3488_, v___y_3489_, v___y_3490_, v___y_3491_, v___y_3492_, v___y_3493_, v___y_3494_, v___y_3495_, v___y_3496_, v___y_3497_);
lean_dec(v___y_3497_);
lean_dec_ref(v___y_3496_);
lean_dec(v___y_3495_);
lean_dec_ref(v___y_3494_);
lean_dec(v___y_3493_);
lean_dec_ref(v___y_3492_);
lean_dec(v___y_3491_);
lean_dec_ref(v___y_3490_);
lean_dec(v___y_3489_);
lean_dec(v___y_3488_);
lean_dec_ref(v___y_3487_);
return v_res_3499_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__2(lean_object* v_cls_3500_, lean_object* v_msg_3501_, lean_object* v___y_3502_, lean_object* v___y_3503_, lean_object* v___y_3504_, lean_object* v___y_3505_, lean_object* v___y_3506_, lean_object* v___y_3507_, lean_object* v___y_3508_, lean_object* v___y_3509_, lean_object* v___y_3510_, lean_object* v___y_3511_, lean_object* v___y_3512_){
_start:
{
lean_object* v___x_3514_; 
v___x_3514_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__2___redArg(v_cls_3500_, v_msg_3501_, v___y_3509_, v___y_3510_, v___y_3511_, v___y_3512_);
return v___x_3514_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__2___boxed(lean_object* v_cls_3515_, lean_object* v_msg_3516_, lean_object* v___y_3517_, lean_object* v___y_3518_, lean_object* v___y_3519_, lean_object* v___y_3520_, lean_object* v___y_3521_, lean_object* v___y_3522_, lean_object* v___y_3523_, lean_object* v___y_3524_, lean_object* v___y_3525_, lean_object* v___y_3526_, lean_object* v___y_3527_, lean_object* v___y_3528_){
_start:
{
lean_object* v_res_3529_; 
v_res_3529_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__2(v_cls_3515_, v_msg_3516_, v___y_3517_, v___y_3518_, v___y_3519_, v___y_3520_, v___y_3521_, v___y_3522_, v___y_3523_, v___y_3524_, v___y_3525_, v___y_3526_, v___y_3527_);
lean_dec(v___y_3527_);
lean_dec_ref(v___y_3526_);
lean_dec(v___y_3525_);
lean_dec_ref(v___y_3524_);
lean_dec(v___y_3523_);
lean_dec_ref(v___y_3522_);
lean_dec(v___y_3521_);
lean_dec_ref(v___y_3520_);
lean_dec(v___y_3519_);
lean_dec(v___y_3518_);
lean_dec(v___y_3517_);
return v_res_3529_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__3(lean_object* v_cls_3530_, lean_object* v_msg_3531_, lean_object* v___y_3532_, lean_object* v___y_3533_, lean_object* v___y_3534_, lean_object* v___y_3535_, lean_object* v___y_3536_, lean_object* v___y_3537_, lean_object* v___y_3538_, lean_object* v___y_3539_, lean_object* v___y_3540_, lean_object* v___y_3541_, lean_object* v___y_3542_){
_start:
{
lean_object* v___x_3544_; 
v___x_3544_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__3___redArg(v_cls_3530_, v_msg_3531_, v___y_3539_, v___y_3540_, v___y_3541_, v___y_3542_);
return v___x_3544_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__3___boxed(lean_object* v_cls_3545_, lean_object* v_msg_3546_, lean_object* v___y_3547_, lean_object* v___y_3548_, lean_object* v___y_3549_, lean_object* v___y_3550_, lean_object* v___y_3551_, lean_object* v___y_3552_, lean_object* v___y_3553_, lean_object* v___y_3554_, lean_object* v___y_3555_, lean_object* v___y_3556_, lean_object* v___y_3557_, lean_object* v___y_3558_){
_start:
{
lean_object* v_res_3559_; 
v_res_3559_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__3(v_cls_3545_, v_msg_3546_, v___y_3547_, v___y_3548_, v___y_3549_, v___y_3550_, v___y_3551_, v___y_3552_, v___y_3553_, v___y_3554_, v___y_3555_, v___y_3556_, v___y_3557_);
lean_dec(v___y_3557_);
lean_dec_ref(v___y_3556_);
lean_dec(v___y_3555_);
lean_dec_ref(v___y_3554_);
lean_dec(v___y_3553_);
lean_dec_ref(v___y_3552_);
lean_dec(v___y_3551_);
lean_dec_ref(v___y_3550_);
lean_dec(v___y_3549_);
lean_dec(v___y_3548_);
lean_dec(v___y_3547_);
return v_res_3559_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__4(lean_object* v_cls_3560_, lean_object* v_msg_3561_, lean_object* v___y_3562_, lean_object* v___y_3563_, lean_object* v___y_3564_, lean_object* v___y_3565_, lean_object* v___y_3566_, lean_object* v___y_3567_, lean_object* v___y_3568_, lean_object* v___y_3569_, lean_object* v___y_3570_, lean_object* v___y_3571_, lean_object* v___y_3572_){
_start:
{
lean_object* v___x_3574_; 
v___x_3574_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__4___redArg(v_cls_3560_, v_msg_3561_, v___y_3569_, v___y_3570_, v___y_3571_, v___y_3572_);
return v___x_3574_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__4___boxed(lean_object* v_cls_3575_, lean_object* v_msg_3576_, lean_object* v___y_3577_, lean_object* v___y_3578_, lean_object* v___y_3579_, lean_object* v___y_3580_, lean_object* v___y_3581_, lean_object* v___y_3582_, lean_object* v___y_3583_, lean_object* v___y_3584_, lean_object* v___y_3585_, lean_object* v___y_3586_, lean_object* v___y_3587_, lean_object* v___y_3588_){
_start:
{
lean_object* v_res_3589_; 
v_res_3589_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__4(v_cls_3575_, v_msg_3576_, v___y_3577_, v___y_3578_, v___y_3579_, v___y_3580_, v___y_3581_, v___y_3582_, v___y_3583_, v___y_3584_, v___y_3585_, v___y_3586_, v___y_3587_);
lean_dec(v___y_3587_);
lean_dec_ref(v___y_3586_);
lean_dec(v___y_3585_);
lean_dec_ref(v___y_3584_);
lean_dec(v___y_3583_);
lean_dec_ref(v___y_3582_);
lean_dec(v___y_3581_);
lean_dec_ref(v___y_3580_);
lean_dec(v___y_3579_);
lean_dec(v___y_3578_);
lean_dec(v___y_3577_);
return v_res_3589_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0(lean_object* v_00_u03b2_3590_, lean_object* v_x_3591_, size_t v_x_3592_, size_t v_x_3593_, lean_object* v_x_3594_, lean_object* v_x_3595_){
_start:
{
lean_object* v___x_3596_; 
v___x_3596_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0___redArg(v_x_3591_, v_x_3592_, v_x_3593_, v_x_3594_, v_x_3595_);
return v___x_3596_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3597_, lean_object* v_x_3598_, lean_object* v_x_3599_, lean_object* v_x_3600_, lean_object* v_x_3601_, lean_object* v_x_3602_){
_start:
{
size_t v_x_214737__boxed_3603_; size_t v_x_214738__boxed_3604_; lean_object* v_res_3605_; 
v_x_214737__boxed_3603_ = lean_unbox_usize(v_x_3599_);
lean_dec(v_x_3599_);
v_x_214738__boxed_3604_ = lean_unbox_usize(v_x_3600_);
lean_dec(v_x_3600_);
v_res_3605_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0(v_00_u03b2_3597_, v_x_3598_, v_x_214737__boxed_3603_, v_x_214738__boxed_3604_, v_x_3601_, v_x_3602_);
return v_res_3605_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_3606_, lean_object* v_n_3607_, lean_object* v_k_3608_, lean_object* v_v_3609_){
_start:
{
lean_object* v___x_3610_; 
v___x_3610_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0_spec__1___redArg(v_n_3607_, v_k_3608_, v_v_3609_);
return v___x_3610_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_3611_, size_t v_depth_3612_, lean_object* v_keys_3613_, lean_object* v_vals_3614_, lean_object* v_heq_3615_, lean_object* v_i_3616_, lean_object* v_entries_3617_){
_start:
{
lean_object* v___x_3618_; 
v___x_3618_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0_spec__2___redArg(v_depth_3612_, v_keys_3613_, v_vals_3614_, v_i_3616_, v_entries_3617_);
return v___x_3618_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_3619_, lean_object* v_depth_3620_, lean_object* v_keys_3621_, lean_object* v_vals_3622_, lean_object* v_heq_3623_, lean_object* v_i_3624_, lean_object* v_entries_3625_){
_start:
{
size_t v_depth_boxed_3626_; lean_object* v_res_3627_; 
v_depth_boxed_3626_ = lean_unbox_usize(v_depth_3620_);
lean_dec(v_depth_3620_);
v_res_3627_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0_spec__2(v_00_u03b2_3619_, v_depth_boxed_3626_, v_keys_3621_, v_vals_3622_, v_heq_3623_, v_i_3624_, v_entries_3625_);
lean_dec_ref(v_vals_3622_);
lean_dec_ref(v_keys_3621_);
return v_res_3627_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0_spec__1_spec__6(lean_object* v_00_u03b2_3628_, lean_object* v_x_3629_, lean_object* v_x_3630_, lean_object* v_x_3631_, lean_object* v_x_3632_){
_start:
{
lean_object* v___x_3633_; 
v___x_3633_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0_spec__1_spec__6___redArg(v_x_3629_, v_x_3630_, v_x_3631_, v_x_3632_);
return v___x_3633_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Simp(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Util(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Reify(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Simp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Reify(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Simp(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Util(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Reify(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Simp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Reify(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize(builtin);
}
#ifdef __cplusplus
}
#endif
