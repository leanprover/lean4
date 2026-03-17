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
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint64_t l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* lean_grind_canon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommon___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_synthInstanceMeta_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkInst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
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
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Meta_Grind_getConfig___redArg(lean_object*);
uint8_t l_Lean_Meta_Grind_Arith_isIntModuleVirtualParent(lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_reify_x3f(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermRingId(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Grind_Arith_CommRing_ringExt;
lean_object* l_Lean_Meta_Grind_SolverExtension_markTerm___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_updateLastTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_sreify_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNonCommRingId_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_ncreify_x3f(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_modifyRing___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_ncsreify_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_getNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isNatCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__2_spec__4_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_getNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isNatCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__2_spec__4_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__1___redArg___closed__0 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__1___redArg___closed__0_value;
static const lean_ctor_object l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__1___redArg___closed__1 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__1___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__7___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0_spec__5_spec__10___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0_spec__6___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__4_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__5;
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "]: "};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__6_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__7;
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "semiring ["};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__8 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__8_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__9;
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "(non-comm) ring ["};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__10 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__10_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__11;
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "(non-comm) semiring ["};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__12 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__12_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__13;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_internalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_internalize___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0_spec__6(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0_spec__5_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_inc(v_val_135_);
lean_dec_ref(v_parent_x3f_134_);
lean_inc(v_val_135_);
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
lean_inc(v___y_274_);
lean_inc_ref(v___y_273_);
lean_inc(v___y_272_);
lean_inc_ref(v___y_271_);
lean_inc_ref(v_type_263_);
v___x_276_ = l_Lean_Meta_Grind_synthInstanceMeta_x3f(v_type_263_, v___y_271_, v___y_272_, v___y_273_, v___y_274_);
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
lean_dec(v___y_274_);
lean_dec_ref(v___y_273_);
lean_dec(v___y_272_);
lean_dec_ref(v___y_271_);
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
lean_dec(v___y_274_);
lean_dec_ref(v___y_273_);
lean_dec(v___y_272_);
lean_dec_ref(v___y_271_);
return v___x_288_;
}
}
}
else
{
lean_object* v_a_290_; lean_object* v___x_292_; uint8_t v_isShared_293_; uint8_t v_isSharedCheck_297_; 
lean_dec(v___y_274_);
lean_dec_ref(v___y_273_);
lean_dec(v___y_272_);
lean_dec_ref(v___y_271_);
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
lean_inc(v___y_327_);
lean_inc_ref(v___y_326_);
lean_inc(v___y_325_);
lean_inc_ref(v___y_324_);
v___x_333_ = l_Lean_Meta_Grind_Arith_CommRing_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1_spec__5(v___x_332_, v___y_317_, v___y_318_, v___y_319_, v___y_320_, v___y_321_, v___y_322_, v___y_323_, v___y_324_, v___y_325_, v___y_326_, v___y_327_);
if (lean_obj_tag(v___x_333_) == 0)
{
lean_object* v_a_334_; lean_object* v___x_335_; 
v_a_334_ = lean_ctor_get(v___x_333_, 0);
lean_inc(v_a_334_);
lean_dec_ref(v___x_333_);
lean_inc(v___y_327_);
lean_inc_ref(v___y_326_);
lean_inc(v___y_325_);
lean_inc_ref(v___y_324_);
lean_inc(v_a_334_);
lean_inc(v_declName_315_);
v___x_335_ = l_Lean_Meta_Grind_Arith_CommRing_checkInst(v_declName_315_, v_a_334_, v_expectedInst_316_, v___y_324_, v___y_325_, v___y_326_, v___y_327_);
if (lean_obj_tag(v___x_335_) == 0)
{
lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; 
lean_dec_ref(v___x_335_);
v___x_336_ = l_Lean_mkConst(v_declName_315_, v___x_330_);
v___x_337_ = l_Lean_mkAppB(v___x_336_, v_type_312_, v_a_334_);
lean_inc(v___y_323_);
v___x_338_ = lean_grind_canon(v___x_337_, v___y_318_, v___y_319_, v___y_320_, v___y_321_, v___y_322_, v___y_323_, v___y_324_, v___y_325_, v___y_326_, v___y_327_);
if (lean_obj_tag(v___x_338_) == 0)
{
lean_object* v_a_339_; lean_object* v___x_340_; 
v_a_339_ = lean_ctor_get(v___x_338_, 0);
lean_inc(v_a_339_);
lean_dec_ref(v___x_338_);
v___x_340_ = l_Lean_Meta_Sym_shareCommon___redArg(v_a_339_, v___y_323_);
lean_dec(v___y_323_);
return v___x_340_;
}
else
{
lean_dec(v___y_323_);
return v___x_338_;
}
}
else
{
lean_object* v_a_341_; lean_object* v___x_343_; uint8_t v_isShared_344_; uint8_t v_isSharedCheck_348_; 
lean_dec(v_a_334_);
lean_dec_ref(v___x_330_);
lean_dec(v___y_327_);
lean_dec_ref(v___y_326_);
lean_dec(v___y_325_);
lean_dec_ref(v___y_324_);
lean_dec(v___y_323_);
lean_dec_ref(v___y_322_);
lean_dec(v___y_321_);
lean_dec_ref(v___y_320_);
lean_dec(v___y_319_);
lean_dec(v___y_318_);
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
lean_dec(v___y_327_);
lean_dec_ref(v___y_326_);
lean_dec(v___y_325_);
lean_dec_ref(v___y_324_);
lean_dec(v___y_323_);
lean_dec_ref(v___y_322_);
lean_dec(v___y_321_);
lean_dec_ref(v___y_320_);
lean_dec(v___y_319_);
lean_dec(v___y_318_);
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
lean_dec(v___y_388_);
lean_dec_ref(v___y_387_);
lean_dec(v___y_386_);
lean_dec_ref(v___y_385_);
lean_dec(v___y_384_);
lean_dec_ref(v___y_383_);
lean_dec(v___y_382_);
lean_dec_ref(v___y_381_);
lean_dec(v___y_380_);
lean_dec(v___y_379_);
lean_dec_ref(v___y_378_);
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
lean_inc_ref(v_type_401_);
v_u_402_ = lean_ctor_get(v_toRing_395_, 2);
lean_inc(v_u_402_);
v_ringInst_403_ = lean_ctor_get(v_toRing_395_, 3);
lean_inc_ref(v_ringInst_403_);
lean_dec_ref(v_toRing_395_);
v___x_404_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0___closed__4));
v___x_405_ = lean_box(0);
lean_inc(v_u_402_);
v___x_406_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_406_, 0, v_u_402_);
lean_ctor_set(v___x_406_, 1, v___x_405_);
v___x_407_ = l_Lean_mkConst(v___x_404_, v___x_406_);
lean_inc_ref(v_type_401_);
v_expectedInst_408_ = l_Lean_mkAppB(v___x_407_, v_type_401_, v_ringInst_403_);
v___x_409_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0___closed__5));
v___x_410_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__11));
lean_inc(v___y_379_);
v___x_411_ = l_Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1(v_type_401_, v_u_402_, v___x_409_, v___x_410_, v_expectedInst_408_, v___y_378_, v___y_379_, v___y_380_, v___y_381_, v___y_382_, v___y_383_, v___y_384_, v___y_385_, v___y_386_, v___y_387_, v___y_388_);
if (lean_obj_tag(v___x_411_) == 0)
{
lean_object* v_a_412_; lean_object* v___f_413_; lean_object* v___x_414_; 
v_a_412_ = lean_ctor_get(v___x_411_, 0);
lean_inc(v_a_412_);
lean_dec_ref(v___x_411_);
lean_inc(v_a_412_);
v___f_413_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0___lam__0), 2, 1);
lean_closure_set(v___f_413_, 0, v_a_412_);
v___x_414_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(v___f_413_, v___y_378_, v___y_379_);
lean_dec(v___y_379_);
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
lean_dec(v___y_379_);
lean_dec_ref(v___y_378_);
return v___x_411_;
}
}
}
}
else
{
lean_object* v_a_432_; lean_object* v___x_434_; uint8_t v_isShared_435_; uint8_t v_isSharedCheck_439_; 
lean_dec(v___y_388_);
lean_dec_ref(v___y_387_);
lean_dec(v___y_386_);
lean_dec_ref(v___y_385_);
lean_dec(v___y_384_);
lean_dec_ref(v___y_383_);
lean_dec(v___y_382_);
lean_dec_ref(v___y_381_);
lean_dec(v___y_380_);
lean_dec(v___y_379_);
lean_dec_ref(v___y_378_);
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
lean_object* v_a_598_; lean_object* v___x_600_; uint8_t v_isShared_601_; uint8_t v_isSharedCheck_659_; 
v_a_598_ = lean_ctor_get(v___x_597_, 0);
v_isSharedCheck_659_ = !lean_is_exclusive(v___x_597_);
if (v_isSharedCheck_659_ == 0)
{
v___x_600_ = v___x_597_;
v_isShared_601_ = v_isSharedCheck_659_;
goto v_resetjp_599_;
}
else
{
lean_inc(v_a_598_);
lean_dec(v___x_597_);
v___x_600_ = lean_box(0);
v_isShared_601_ = v_isSharedCheck_659_;
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
lean_dec(v___y_572_);
lean_dec_ref(v___y_571_);
lean_dec(v___y_570_);
lean_dec_ref(v___y_569_);
lean_dec(v___y_568_);
lean_dec_ref(v___y_567_);
lean_dec(v___y_566_);
lean_dec_ref(v___y_565_);
lean_dec(v___y_564_);
lean_dec(v___y_563_);
lean_dec_ref(v___y_562_);
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
lean_object* v_type_608_; lean_object* v_u_609_; lean_object* v_ringInst_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v_inst_x27_615_; lean_object* v_inst_617_; lean_object* v___y_618_; lean_object* v___y_619_; lean_object* v___y_620_; lean_object* v___y_621_; lean_object* v___y_622_; lean_object* v___y_623_; lean_object* v___y_624_; lean_object* v___y_625_; lean_object* v___y_626_; lean_object* v___y_627_; lean_object* v___y_628_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v_instType_637_; lean_object* v___x_638_; 
lean_del_object(v___x_600_);
v_type_608_ = lean_ctor_get(v_toRing_602_, 1);
lean_inc_ref(v_type_608_);
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
lean_inc_ref(v___x_613_);
v___x_614_ = l_Lean_mkConst(v___x_611_, v___x_613_);
lean_inc_ref(v_type_608_);
v_inst_x27_615_ = l_Lean_mkAppB(v___x_614_, v_type_608_, v_ringInst_610_);
v___x_635_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isIntCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__1_spec__2___closed__1));
lean_inc_ref(v___x_613_);
v___x_636_ = l_Lean_mkConst(v___x_635_, v___x_613_);
lean_inc_ref(v_type_608_);
v_instType_637_ = l_Lean_Expr_app___override(v___x_636_, v_type_608_);
lean_inc(v___y_572_);
lean_inc_ref(v___y_571_);
lean_inc(v___y_570_);
lean_inc_ref(v___y_569_);
v___x_638_ = l_Lean_Meta_Grind_synthInstanceMeta_x3f(v_instType_637_, v___y_569_, v___y_570_, v___y_571_, v___y_572_);
if (lean_obj_tag(v___x_638_) == 0)
{
lean_object* v_a_639_; 
v_a_639_ = lean_ctor_get(v___x_638_, 0);
lean_inc(v_a_639_);
lean_dec_ref(v___x_638_);
if (lean_obj_tag(v_a_639_) == 0)
{
v_inst_617_ = v_inst_x27_615_;
v___y_618_ = v___y_562_;
v___y_619_ = v___y_563_;
v___y_620_ = v___y_564_;
v___y_621_ = v___y_565_;
v___y_622_ = v___y_566_;
v___y_623_ = v___y_567_;
v___y_624_ = v___y_568_;
v___y_625_ = v___y_569_;
v___y_626_ = v___y_570_;
v___y_627_ = v___y_571_;
v___y_628_ = v___y_572_;
goto v___jp_616_;
}
else
{
lean_object* v_val_640_; lean_object* v___x_641_; lean_object* v___x_642_; 
v_val_640_ = lean_ctor_get(v_a_639_, 0);
lean_inc(v_val_640_);
lean_dec_ref(v_a_639_);
v___x_641_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isIntCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__1_spec__2___closed__3));
lean_inc(v___y_572_);
lean_inc_ref(v___y_571_);
lean_inc(v___y_570_);
lean_inc_ref(v___y_569_);
lean_inc(v_val_640_);
v___x_642_ = l_Lean_Meta_Grind_Arith_CommRing_checkInst(v___x_641_, v_val_640_, v_inst_x27_615_, v___y_569_, v___y_570_, v___y_571_, v___y_572_);
if (lean_obj_tag(v___x_642_) == 0)
{
lean_dec_ref(v___x_642_);
v_inst_617_ = v_val_640_;
v___y_618_ = v___y_562_;
v___y_619_ = v___y_563_;
v___y_620_ = v___y_564_;
v___y_621_ = v___y_565_;
v___y_622_ = v___y_566_;
v___y_623_ = v___y_567_;
v___y_624_ = v___y_568_;
v___y_625_ = v___y_569_;
v___y_626_ = v___y_570_;
v___y_627_ = v___y_571_;
v___y_628_ = v___y_572_;
goto v___jp_616_;
}
else
{
lean_object* v_a_643_; lean_object* v___x_645_; uint8_t v_isShared_646_; uint8_t v_isSharedCheck_650_; 
lean_dec(v_val_640_);
lean_dec_ref(v___x_613_);
lean_dec_ref(v_type_608_);
lean_dec(v___y_572_);
lean_dec_ref(v___y_571_);
lean_dec(v___y_570_);
lean_dec_ref(v___y_569_);
lean_dec(v___y_568_);
lean_dec_ref(v___y_567_);
lean_dec(v___y_566_);
lean_dec_ref(v___y_565_);
lean_dec(v___y_564_);
lean_dec(v___y_563_);
lean_dec_ref(v___y_562_);
v_a_643_ = lean_ctor_get(v___x_642_, 0);
v_isSharedCheck_650_ = !lean_is_exclusive(v___x_642_);
if (v_isSharedCheck_650_ == 0)
{
v___x_645_ = v___x_642_;
v_isShared_646_ = v_isSharedCheck_650_;
goto v_resetjp_644_;
}
else
{
lean_inc(v_a_643_);
lean_dec(v___x_642_);
v___x_645_ = lean_box(0);
v_isShared_646_ = v_isSharedCheck_650_;
goto v_resetjp_644_;
}
v_resetjp_644_:
{
lean_object* v___x_648_; 
if (v_isShared_646_ == 0)
{
v___x_648_ = v___x_645_;
goto v_reusejp_647_;
}
else
{
lean_object* v_reuseFailAlloc_649_; 
v_reuseFailAlloc_649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_649_, 0, v_a_643_);
v___x_648_ = v_reuseFailAlloc_649_;
goto v_reusejp_647_;
}
v_reusejp_647_:
{
return v___x_648_;
}
}
}
}
}
else
{
lean_object* v_a_651_; lean_object* v___x_653_; uint8_t v_isShared_654_; uint8_t v_isSharedCheck_658_; 
lean_dec_ref(v_inst_x27_615_);
lean_dec_ref(v___x_613_);
lean_dec_ref(v_type_608_);
lean_dec(v___y_572_);
lean_dec_ref(v___y_571_);
lean_dec(v___y_570_);
lean_dec_ref(v___y_569_);
lean_dec(v___y_568_);
lean_dec_ref(v___y_567_);
lean_dec(v___y_566_);
lean_dec_ref(v___y_565_);
lean_dec(v___y_564_);
lean_dec(v___y_563_);
lean_dec_ref(v___y_562_);
v_a_651_ = lean_ctor_get(v___x_638_, 0);
v_isSharedCheck_658_ = !lean_is_exclusive(v___x_638_);
if (v_isSharedCheck_658_ == 0)
{
v___x_653_ = v___x_638_;
v_isShared_654_ = v_isSharedCheck_658_;
goto v_resetjp_652_;
}
else
{
lean_inc(v_a_651_);
lean_dec(v___x_638_);
v___x_653_ = lean_box(0);
v_isShared_654_ = v_isSharedCheck_658_;
goto v_resetjp_652_;
}
v_resetjp_652_:
{
lean_object* v___x_656_; 
if (v_isShared_654_ == 0)
{
v___x_656_ = v___x_653_;
goto v_reusejp_655_;
}
else
{
lean_object* v_reuseFailAlloc_657_; 
v_reuseFailAlloc_657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_657_, 0, v_a_651_);
v___x_656_ = v_reuseFailAlloc_657_;
goto v_reusejp_655_;
}
v_reusejp_655_:
{
return v___x_656_;
}
}
}
v___jp_616_:
{
lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; 
v___x_629_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__2));
v___x_630_ = l_Lean_mkConst(v___x_629_, v___x_613_);
v___x_631_ = l_Lean_mkAppB(v___x_630_, v_type_608_, v_inst_617_);
lean_inc(v___y_624_);
lean_inc(v___y_619_);
v___x_632_ = lean_grind_canon(v___x_631_, v___y_619_, v___y_620_, v___y_621_, v___y_622_, v___y_623_, v___y_624_, v___y_625_, v___y_626_, v___y_627_, v___y_628_);
if (lean_obj_tag(v___x_632_) == 0)
{
lean_object* v_a_633_; lean_object* v___x_634_; 
v_a_633_ = lean_ctor_get(v___x_632_, 0);
lean_inc(v_a_633_);
lean_dec_ref(v___x_632_);
v___x_634_ = l_Lean_Meta_Sym_shareCommon___redArg(v_a_633_, v___y_624_);
lean_dec(v___y_624_);
v___y_575_ = v___y_618_;
v___y_576_ = v___y_619_;
v___y_577_ = v___x_634_;
goto v___jp_574_;
}
else
{
lean_dec(v___y_624_);
v___y_575_ = v___y_618_;
v___y_576_ = v___y_619_;
v___y_577_ = v___x_632_;
goto v___jp_574_;
}
}
}
}
}
else
{
lean_object* v_a_660_; lean_object* v___x_662_; uint8_t v_isShared_663_; uint8_t v_isSharedCheck_667_; 
lean_dec(v___y_572_);
lean_dec_ref(v___y_571_);
lean_dec(v___y_570_);
lean_dec_ref(v___y_569_);
lean_dec(v___y_568_);
lean_dec_ref(v___y_567_);
lean_dec(v___y_566_);
lean_dec_ref(v___y_565_);
lean_dec(v___y_564_);
lean_dec(v___y_563_);
lean_dec_ref(v___y_562_);
v_a_660_ = lean_ctor_get(v___x_597_, 0);
v_isSharedCheck_667_ = !lean_is_exclusive(v___x_597_);
if (v_isSharedCheck_667_ == 0)
{
v___x_662_ = v___x_597_;
v_isShared_663_ = v_isSharedCheck_667_;
goto v_resetjp_661_;
}
else
{
lean_inc(v_a_660_);
lean_dec(v___x_597_);
v___x_662_ = lean_box(0);
v_isShared_663_ = v_isSharedCheck_667_;
goto v_resetjp_661_;
}
v_resetjp_661_:
{
lean_object* v___x_665_; 
if (v_isShared_663_ == 0)
{
v___x_665_ = v___x_662_;
goto v_reusejp_664_;
}
else
{
lean_object* v_reuseFailAlloc_666_; 
v_reuseFailAlloc_666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_666_, 0, v_a_660_);
v___x_665_ = v_reuseFailAlloc_666_;
goto v_reusejp_664_;
}
v_reusejp_664_:
{
return v___x_665_;
}
}
}
v___jp_574_:
{
if (lean_obj_tag(v___y_577_) == 0)
{
lean_object* v_a_578_; lean_object* v___f_579_; lean_object* v___x_580_; 
v_a_578_ = lean_ctor_get(v___y_577_, 0);
lean_inc(v_a_578_);
lean_dec_ref(v___y_577_);
lean_inc(v_a_578_);
v___f_579_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isIntCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__1_spec__2___lam__0), 2, 1);
lean_closure_set(v___f_579_, 0, v_a_578_);
v___x_580_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(v___f_579_, v___y_575_, v___y_576_);
lean_dec(v___y_576_);
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
lean_dec(v___y_576_);
lean_dec_ref(v___y_575_);
return v___y_577_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isIntCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__1_spec__2___boxed(lean_object* v___y_668_, lean_object* v___y_669_, lean_object* v___y_670_, lean_object* v___y_671_, lean_object* v___y_672_, lean_object* v___y_673_, lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_, lean_object* v___y_677_, lean_object* v___y_678_, lean_object* v___y_679_){
_start:
{
lean_object* v_res_680_; 
v_res_680_ = l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isIntCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__1_spec__2(v___y_668_, v___y_669_, v___y_670_, v___y_671_, v___y_672_, v___y_673_, v___y_674_, v___y_675_, v___y_676_, v___y_677_, v___y_678_);
return v_res_680_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_isIntCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__1(lean_object* v_inst_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_, lean_object* v___y_688_, lean_object* v___y_689_, lean_object* v___y_690_, lean_object* v___y_691_, lean_object* v___y_692_){
_start:
{
lean_object* v___x_694_; 
v___x_694_ = l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isIntCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__1_spec__2(v___y_682_, v___y_683_, v___y_684_, v___y_685_, v___y_686_, v___y_687_, v___y_688_, v___y_689_, v___y_690_, v___y_691_, v___y_692_);
if (lean_obj_tag(v___x_694_) == 0)
{
lean_object* v_a_695_; lean_object* v___x_697_; uint8_t v_isShared_698_; uint8_t v_isSharedCheck_705_; 
v_a_695_ = lean_ctor_get(v___x_694_, 0);
v_isSharedCheck_705_ = !lean_is_exclusive(v___x_694_);
if (v_isSharedCheck_705_ == 0)
{
v___x_697_ = v___x_694_;
v_isShared_698_ = v_isSharedCheck_705_;
goto v_resetjp_696_;
}
else
{
lean_inc(v_a_695_);
lean_dec(v___x_694_);
v___x_697_ = lean_box(0);
v_isShared_698_ = v_isSharedCheck_705_;
goto v_resetjp_696_;
}
v_resetjp_696_:
{
lean_object* v___x_699_; uint8_t v___x_700_; lean_object* v___x_701_; lean_object* v___x_703_; 
v___x_699_ = l_Lean_Expr_appArg_x21(v_a_695_);
lean_dec(v_a_695_);
v___x_700_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v___x_699_, v_inst_681_);
lean_dec_ref(v___x_699_);
v___x_701_ = lean_box(v___x_700_);
if (v_isShared_698_ == 0)
{
lean_ctor_set(v___x_697_, 0, v___x_701_);
v___x_703_ = v___x_697_;
goto v_reusejp_702_;
}
else
{
lean_object* v_reuseFailAlloc_704_; 
v_reuseFailAlloc_704_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_704_, 0, v___x_701_);
v___x_703_ = v_reuseFailAlloc_704_;
goto v_reusejp_702_;
}
v_reusejp_702_:
{
return v___x_703_;
}
}
}
else
{
lean_object* v_a_706_; lean_object* v___x_708_; uint8_t v_isShared_709_; uint8_t v_isSharedCheck_713_; 
v_a_706_ = lean_ctor_get(v___x_694_, 0);
v_isSharedCheck_713_ = !lean_is_exclusive(v___x_694_);
if (v_isSharedCheck_713_ == 0)
{
v___x_708_ = v___x_694_;
v_isShared_709_ = v_isSharedCheck_713_;
goto v_resetjp_707_;
}
else
{
lean_inc(v_a_706_);
lean_dec(v___x_694_);
v___x_708_ = lean_box(0);
v_isShared_709_ = v_isSharedCheck_713_;
goto v_resetjp_707_;
}
v_resetjp_707_:
{
lean_object* v___x_711_; 
if (v_isShared_709_ == 0)
{
v___x_711_ = v___x_708_;
goto v_reusejp_710_;
}
else
{
lean_object* v_reuseFailAlloc_712_; 
v_reuseFailAlloc_712_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_712_, 0, v_a_706_);
v___x_711_ = v_reuseFailAlloc_712_;
goto v_reusejp_710_;
}
v_reusejp_710_:
{
return v___x_711_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_isIntCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__1___boxed(lean_object* v_inst_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_, lean_object* v___y_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_, lean_object* v___y_724_, lean_object* v___y_725_, lean_object* v___y_726_){
_start:
{
lean_object* v_res_727_; 
v_res_727_ = l_Lean_Meta_Grind_Arith_CommRing_isIntCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__1(v_inst_714_, v___y_715_, v___y_716_, v___y_717_, v___y_718_, v___y_719_, v___y_720_, v___y_721_, v___y_722_, v___y_723_, v___y_724_, v___y_725_);
lean_dec_ref(v_inst_714_);
return v_res_727_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isNatCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__2_spec__4___lam__0(lean_object* v_a_728_, lean_object* v_s_729_){
_start:
{
lean_object* v_toRing_730_; lean_object* v_invFn_x3f_731_; lean_object* v_semiringId_x3f_732_; lean_object* v_commSemiringInst_733_; lean_object* v_commRingInst_734_; lean_object* v_noZeroDivInst_x3f_735_; lean_object* v_fieldInst_x3f_736_; lean_object* v_denoteEntries_737_; lean_object* v_nextId_738_; lean_object* v_steps_739_; lean_object* v_queue_740_; lean_object* v_basis_741_; lean_object* v_diseqs_742_; uint8_t v_recheck_743_; lean_object* v_invSet_744_; lean_object* v_numEq0_x3f_745_; uint8_t v_numEq0Updated_746_; lean_object* v___x_748_; uint8_t v_isShared_749_; uint8_t v_isSharedCheck_778_; 
v_toRing_730_ = lean_ctor_get(v_s_729_, 0);
v_invFn_x3f_731_ = lean_ctor_get(v_s_729_, 1);
v_semiringId_x3f_732_ = lean_ctor_get(v_s_729_, 2);
v_commSemiringInst_733_ = lean_ctor_get(v_s_729_, 3);
v_commRingInst_734_ = lean_ctor_get(v_s_729_, 4);
v_noZeroDivInst_x3f_735_ = lean_ctor_get(v_s_729_, 5);
v_fieldInst_x3f_736_ = lean_ctor_get(v_s_729_, 6);
v_denoteEntries_737_ = lean_ctor_get(v_s_729_, 7);
v_nextId_738_ = lean_ctor_get(v_s_729_, 8);
v_steps_739_ = lean_ctor_get(v_s_729_, 9);
v_queue_740_ = lean_ctor_get(v_s_729_, 10);
v_basis_741_ = lean_ctor_get(v_s_729_, 11);
v_diseqs_742_ = lean_ctor_get(v_s_729_, 12);
v_recheck_743_ = lean_ctor_get_uint8(v_s_729_, sizeof(void*)*15);
v_invSet_744_ = lean_ctor_get(v_s_729_, 13);
v_numEq0_x3f_745_ = lean_ctor_get(v_s_729_, 14);
v_numEq0Updated_746_ = lean_ctor_get_uint8(v_s_729_, sizeof(void*)*15 + 1);
v_isSharedCheck_778_ = !lean_is_exclusive(v_s_729_);
if (v_isSharedCheck_778_ == 0)
{
v___x_748_ = v_s_729_;
v_isShared_749_ = v_isSharedCheck_778_;
goto v_resetjp_747_;
}
else
{
lean_inc(v_numEq0_x3f_745_);
lean_inc(v_invSet_744_);
lean_inc(v_diseqs_742_);
lean_inc(v_basis_741_);
lean_inc(v_queue_740_);
lean_inc(v_steps_739_);
lean_inc(v_nextId_738_);
lean_inc(v_denoteEntries_737_);
lean_inc(v_fieldInst_x3f_736_);
lean_inc(v_noZeroDivInst_x3f_735_);
lean_inc(v_commRingInst_734_);
lean_inc(v_commSemiringInst_733_);
lean_inc(v_semiringId_x3f_732_);
lean_inc(v_invFn_x3f_731_);
lean_inc(v_toRing_730_);
lean_dec(v_s_729_);
v___x_748_ = lean_box(0);
v_isShared_749_ = v_isSharedCheck_778_;
goto v_resetjp_747_;
}
v_resetjp_747_:
{
lean_object* v_id_750_; lean_object* v_type_751_; lean_object* v_u_752_; lean_object* v_ringInst_753_; lean_object* v_semiringInst_754_; lean_object* v_charInst_x3f_755_; lean_object* v_addFn_x3f_756_; lean_object* v_mulFn_x3f_757_; lean_object* v_subFn_x3f_758_; lean_object* v_negFn_x3f_759_; lean_object* v_powFn_x3f_760_; lean_object* v_intCastFn_x3f_761_; lean_object* v_one_x3f_762_; lean_object* v_vars_763_; lean_object* v_varMap_764_; lean_object* v_denote_765_; lean_object* v___x_767_; uint8_t v_isShared_768_; uint8_t v_isSharedCheck_776_; 
v_id_750_ = lean_ctor_get(v_toRing_730_, 0);
v_type_751_ = lean_ctor_get(v_toRing_730_, 1);
v_u_752_ = lean_ctor_get(v_toRing_730_, 2);
v_ringInst_753_ = lean_ctor_get(v_toRing_730_, 3);
v_semiringInst_754_ = lean_ctor_get(v_toRing_730_, 4);
v_charInst_x3f_755_ = lean_ctor_get(v_toRing_730_, 5);
v_addFn_x3f_756_ = lean_ctor_get(v_toRing_730_, 6);
v_mulFn_x3f_757_ = lean_ctor_get(v_toRing_730_, 7);
v_subFn_x3f_758_ = lean_ctor_get(v_toRing_730_, 8);
v_negFn_x3f_759_ = lean_ctor_get(v_toRing_730_, 9);
v_powFn_x3f_760_ = lean_ctor_get(v_toRing_730_, 10);
v_intCastFn_x3f_761_ = lean_ctor_get(v_toRing_730_, 11);
v_one_x3f_762_ = lean_ctor_get(v_toRing_730_, 13);
v_vars_763_ = lean_ctor_get(v_toRing_730_, 14);
v_varMap_764_ = lean_ctor_get(v_toRing_730_, 15);
v_denote_765_ = lean_ctor_get(v_toRing_730_, 16);
v_isSharedCheck_776_ = !lean_is_exclusive(v_toRing_730_);
if (v_isSharedCheck_776_ == 0)
{
lean_object* v_unused_777_; 
v_unused_777_ = lean_ctor_get(v_toRing_730_, 12);
lean_dec(v_unused_777_);
v___x_767_ = v_toRing_730_;
v_isShared_768_ = v_isSharedCheck_776_;
goto v_resetjp_766_;
}
else
{
lean_inc(v_denote_765_);
lean_inc(v_varMap_764_);
lean_inc(v_vars_763_);
lean_inc(v_one_x3f_762_);
lean_inc(v_intCastFn_x3f_761_);
lean_inc(v_powFn_x3f_760_);
lean_inc(v_negFn_x3f_759_);
lean_inc(v_subFn_x3f_758_);
lean_inc(v_mulFn_x3f_757_);
lean_inc(v_addFn_x3f_756_);
lean_inc(v_charInst_x3f_755_);
lean_inc(v_semiringInst_754_);
lean_inc(v_ringInst_753_);
lean_inc(v_u_752_);
lean_inc(v_type_751_);
lean_inc(v_id_750_);
lean_dec(v_toRing_730_);
v___x_767_ = lean_box(0);
v_isShared_768_ = v_isSharedCheck_776_;
goto v_resetjp_766_;
}
v_resetjp_766_:
{
lean_object* v___x_769_; lean_object* v___x_771_; 
v___x_769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_769_, 0, v_a_728_);
if (v_isShared_768_ == 0)
{
lean_ctor_set(v___x_767_, 12, v___x_769_);
v___x_771_ = v___x_767_;
goto v_reusejp_770_;
}
else
{
lean_object* v_reuseFailAlloc_775_; 
v_reuseFailAlloc_775_ = lean_alloc_ctor(0, 17, 0);
lean_ctor_set(v_reuseFailAlloc_775_, 0, v_id_750_);
lean_ctor_set(v_reuseFailAlloc_775_, 1, v_type_751_);
lean_ctor_set(v_reuseFailAlloc_775_, 2, v_u_752_);
lean_ctor_set(v_reuseFailAlloc_775_, 3, v_ringInst_753_);
lean_ctor_set(v_reuseFailAlloc_775_, 4, v_semiringInst_754_);
lean_ctor_set(v_reuseFailAlloc_775_, 5, v_charInst_x3f_755_);
lean_ctor_set(v_reuseFailAlloc_775_, 6, v_addFn_x3f_756_);
lean_ctor_set(v_reuseFailAlloc_775_, 7, v_mulFn_x3f_757_);
lean_ctor_set(v_reuseFailAlloc_775_, 8, v_subFn_x3f_758_);
lean_ctor_set(v_reuseFailAlloc_775_, 9, v_negFn_x3f_759_);
lean_ctor_set(v_reuseFailAlloc_775_, 10, v_powFn_x3f_760_);
lean_ctor_set(v_reuseFailAlloc_775_, 11, v_intCastFn_x3f_761_);
lean_ctor_set(v_reuseFailAlloc_775_, 12, v___x_769_);
lean_ctor_set(v_reuseFailAlloc_775_, 13, v_one_x3f_762_);
lean_ctor_set(v_reuseFailAlloc_775_, 14, v_vars_763_);
lean_ctor_set(v_reuseFailAlloc_775_, 15, v_varMap_764_);
lean_ctor_set(v_reuseFailAlloc_775_, 16, v_denote_765_);
v___x_771_ = v_reuseFailAlloc_775_;
goto v_reusejp_770_;
}
v_reusejp_770_:
{
lean_object* v___x_773_; 
if (v_isShared_749_ == 0)
{
lean_ctor_set(v___x_748_, 0, v___x_771_);
v___x_773_ = v___x_748_;
goto v_reusejp_772_;
}
else
{
lean_object* v_reuseFailAlloc_774_; 
v_reuseFailAlloc_774_ = lean_alloc_ctor(0, 15, 2);
lean_ctor_set(v_reuseFailAlloc_774_, 0, v___x_771_);
lean_ctor_set(v_reuseFailAlloc_774_, 1, v_invFn_x3f_731_);
lean_ctor_set(v_reuseFailAlloc_774_, 2, v_semiringId_x3f_732_);
lean_ctor_set(v_reuseFailAlloc_774_, 3, v_commSemiringInst_733_);
lean_ctor_set(v_reuseFailAlloc_774_, 4, v_commRingInst_734_);
lean_ctor_set(v_reuseFailAlloc_774_, 5, v_noZeroDivInst_x3f_735_);
lean_ctor_set(v_reuseFailAlloc_774_, 6, v_fieldInst_x3f_736_);
lean_ctor_set(v_reuseFailAlloc_774_, 7, v_denoteEntries_737_);
lean_ctor_set(v_reuseFailAlloc_774_, 8, v_nextId_738_);
lean_ctor_set(v_reuseFailAlloc_774_, 9, v_steps_739_);
lean_ctor_set(v_reuseFailAlloc_774_, 10, v_queue_740_);
lean_ctor_set(v_reuseFailAlloc_774_, 11, v_basis_741_);
lean_ctor_set(v_reuseFailAlloc_774_, 12, v_diseqs_742_);
lean_ctor_set(v_reuseFailAlloc_774_, 13, v_invSet_744_);
lean_ctor_set(v_reuseFailAlloc_774_, 14, v_numEq0_x3f_745_);
lean_ctor_set_uint8(v_reuseFailAlloc_774_, sizeof(void*)*15, v_recheck_743_);
lean_ctor_set_uint8(v_reuseFailAlloc_774_, sizeof(void*)*15 + 1, v_numEq0Updated_746_);
v___x_773_ = v_reuseFailAlloc_774_;
goto v_reusejp_772_;
}
v_reusejp_772_:
{
return v___x_773_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_getNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isNatCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__2_spec__4_spec__6___redArg(lean_object* v_u_787_, lean_object* v_type_788_, lean_object* v_semiringInst_789_, lean_object* v___y_790_, lean_object* v___y_791_, lean_object* v___y_792_, lean_object* v___y_793_, lean_object* v___y_794_, lean_object* v___y_795_, lean_object* v___y_796_, lean_object* v___y_797_, lean_object* v___y_798_, lean_object* v___y_799_){
_start:
{
lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v_inst_x27_805_; lean_object* v_inst_807_; lean_object* v___y_808_; lean_object* v___y_809_; lean_object* v___y_810_; lean_object* v___y_811_; lean_object* v___y_812_; lean_object* v___y_813_; lean_object* v___y_814_; lean_object* v___y_815_; lean_object* v___y_816_; lean_object* v___y_817_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v_instType_826_; lean_object* v___x_827_; 
v___x_801_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_getNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isNatCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__2_spec__4_spec__6___redArg___closed__1));
v___x_802_ = lean_box(0);
v___x_803_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_803_, 0, v_u_787_);
lean_ctor_set(v___x_803_, 1, v___x_802_);
lean_inc_ref(v___x_803_);
v___x_804_ = l_Lean_mkConst(v___x_801_, v___x_803_);
lean_inc_ref(v_type_788_);
v_inst_x27_805_ = l_Lean_mkAppB(v___x_804_, v_type_788_, v_semiringInst_789_);
v___x_824_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_getNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isNatCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__2_spec__4_spec__6___redArg___closed__2));
lean_inc_ref(v___x_803_);
v___x_825_ = l_Lean_mkConst(v___x_824_, v___x_803_);
lean_inc_ref(v_type_788_);
v_instType_826_ = l_Lean_Expr_app___override(v___x_825_, v_type_788_);
lean_inc(v___y_799_);
lean_inc_ref(v___y_798_);
lean_inc(v___y_797_);
lean_inc_ref(v___y_796_);
v___x_827_ = l_Lean_Meta_Grind_synthInstanceMeta_x3f(v_instType_826_, v___y_796_, v___y_797_, v___y_798_, v___y_799_);
if (lean_obj_tag(v___x_827_) == 0)
{
lean_object* v_a_828_; 
v_a_828_ = lean_ctor_get(v___x_827_, 0);
lean_inc(v_a_828_);
lean_dec_ref(v___x_827_);
if (lean_obj_tag(v_a_828_) == 0)
{
v_inst_807_ = v_inst_x27_805_;
v___y_808_ = v___y_790_;
v___y_809_ = v___y_791_;
v___y_810_ = v___y_792_;
v___y_811_ = v___y_793_;
v___y_812_ = v___y_794_;
v___y_813_ = v___y_795_;
v___y_814_ = v___y_796_;
v___y_815_ = v___y_797_;
v___y_816_ = v___y_798_;
v___y_817_ = v___y_799_;
goto v___jp_806_;
}
else
{
lean_object* v_val_829_; lean_object* v___x_830_; lean_object* v___x_831_; 
v_val_829_ = lean_ctor_get(v_a_828_, 0);
lean_inc(v_val_829_);
lean_dec_ref(v_a_828_);
v___x_830_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__5));
lean_inc(v___y_799_);
lean_inc_ref(v___y_798_);
lean_inc(v___y_797_);
lean_inc_ref(v___y_796_);
lean_inc(v_val_829_);
v___x_831_ = l_Lean_Meta_Grind_Arith_CommRing_checkInst(v___x_830_, v_val_829_, v_inst_x27_805_, v___y_796_, v___y_797_, v___y_798_, v___y_799_);
if (lean_obj_tag(v___x_831_) == 0)
{
lean_dec_ref(v___x_831_);
v_inst_807_ = v_val_829_;
v___y_808_ = v___y_790_;
v___y_809_ = v___y_791_;
v___y_810_ = v___y_792_;
v___y_811_ = v___y_793_;
v___y_812_ = v___y_794_;
v___y_813_ = v___y_795_;
v___y_814_ = v___y_796_;
v___y_815_ = v___y_797_;
v___y_816_ = v___y_798_;
v___y_817_ = v___y_799_;
goto v___jp_806_;
}
else
{
lean_object* v_a_832_; lean_object* v___x_834_; uint8_t v_isShared_835_; uint8_t v_isSharedCheck_839_; 
lean_dec(v_val_829_);
lean_dec_ref(v___x_803_);
lean_dec(v___y_799_);
lean_dec_ref(v___y_798_);
lean_dec(v___y_797_);
lean_dec_ref(v___y_796_);
lean_dec(v___y_795_);
lean_dec_ref(v___y_794_);
lean_dec(v___y_793_);
lean_dec_ref(v___y_792_);
lean_dec(v___y_791_);
lean_dec(v___y_790_);
lean_dec_ref(v_type_788_);
v_a_832_ = lean_ctor_get(v___x_831_, 0);
v_isSharedCheck_839_ = !lean_is_exclusive(v___x_831_);
if (v_isSharedCheck_839_ == 0)
{
v___x_834_ = v___x_831_;
v_isShared_835_ = v_isSharedCheck_839_;
goto v_resetjp_833_;
}
else
{
lean_inc(v_a_832_);
lean_dec(v___x_831_);
v___x_834_ = lean_box(0);
v_isShared_835_ = v_isSharedCheck_839_;
goto v_resetjp_833_;
}
v_resetjp_833_:
{
lean_object* v___x_837_; 
if (v_isShared_835_ == 0)
{
v___x_837_ = v___x_834_;
goto v_reusejp_836_;
}
else
{
lean_object* v_reuseFailAlloc_838_; 
v_reuseFailAlloc_838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_838_, 0, v_a_832_);
v___x_837_ = v_reuseFailAlloc_838_;
goto v_reusejp_836_;
}
v_reusejp_836_:
{
return v___x_837_;
}
}
}
}
}
else
{
lean_object* v_a_840_; lean_object* v___x_842_; uint8_t v_isShared_843_; uint8_t v_isSharedCheck_847_; 
lean_dec_ref(v_inst_x27_805_);
lean_dec_ref(v___x_803_);
lean_dec(v___y_799_);
lean_dec_ref(v___y_798_);
lean_dec(v___y_797_);
lean_dec_ref(v___y_796_);
lean_dec(v___y_795_);
lean_dec_ref(v___y_794_);
lean_dec(v___y_793_);
lean_dec_ref(v___y_792_);
lean_dec(v___y_791_);
lean_dec(v___y_790_);
lean_dec_ref(v_type_788_);
v_a_840_ = lean_ctor_get(v___x_827_, 0);
v_isSharedCheck_847_ = !lean_is_exclusive(v___x_827_);
if (v_isSharedCheck_847_ == 0)
{
v___x_842_ = v___x_827_;
v_isShared_843_ = v_isSharedCheck_847_;
goto v_resetjp_841_;
}
else
{
lean_inc(v_a_840_);
lean_dec(v___x_827_);
v___x_842_ = lean_box(0);
v_isShared_843_ = v_isSharedCheck_847_;
goto v_resetjp_841_;
}
v_resetjp_841_:
{
lean_object* v___x_845_; 
if (v_isShared_843_ == 0)
{
v___x_845_ = v___x_842_;
goto v_reusejp_844_;
}
else
{
lean_object* v_reuseFailAlloc_846_; 
v_reuseFailAlloc_846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_846_, 0, v_a_840_);
v___x_845_ = v_reuseFailAlloc_846_;
goto v_reusejp_844_;
}
v_reusejp_844_:
{
return v___x_845_;
}
}
}
v___jp_806_:
{
lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; 
v___x_818_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__5));
v___x_819_ = l_Lean_mkConst(v___x_818_, v___x_803_);
v___x_820_ = l_Lean_mkAppB(v___x_819_, v_type_788_, v_inst_807_);
lean_inc(v___y_813_);
v___x_821_ = lean_grind_canon(v___x_820_, v___y_808_, v___y_809_, v___y_810_, v___y_811_, v___y_812_, v___y_813_, v___y_814_, v___y_815_, v___y_816_, v___y_817_);
if (lean_obj_tag(v___x_821_) == 0)
{
lean_object* v_a_822_; lean_object* v___x_823_; 
v_a_822_ = lean_ctor_get(v___x_821_, 0);
lean_inc(v_a_822_);
lean_dec_ref(v___x_821_);
v___x_823_ = l_Lean_Meta_Sym_shareCommon___redArg(v_a_822_, v___y_813_);
lean_dec(v___y_813_);
return v___x_823_;
}
else
{
lean_dec(v___y_813_);
return v___x_821_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_getNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isNatCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__2_spec__4_spec__6___redArg___boxed(lean_object* v_u_848_, lean_object* v_type_849_, lean_object* v_semiringInst_850_, lean_object* v___y_851_, lean_object* v___y_852_, lean_object* v___y_853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_, lean_object* v___y_857_, lean_object* v___y_858_, lean_object* v___y_859_, lean_object* v___y_860_, lean_object* v___y_861_){
_start:
{
lean_object* v_res_862_; 
v_res_862_ = l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_getNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isNatCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__2_spec__4_spec__6___redArg(v_u_848_, v_type_849_, v_semiringInst_850_, v___y_851_, v___y_852_, v___y_853_, v___y_854_, v___y_855_, v___y_856_, v___y_857_, v___y_858_, v___y_859_, v___y_860_);
return v_res_862_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isNatCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__2_spec__4(lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_, lean_object* v___y_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_, lean_object* v___y_870_, lean_object* v___y_871_, lean_object* v___y_872_, lean_object* v___y_873_){
_start:
{
lean_object* v___x_875_; 
v___x_875_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v___y_863_, v___y_864_, v___y_865_, v___y_866_, v___y_867_, v___y_868_, v___y_869_, v___y_870_, v___y_871_, v___y_872_, v___y_873_);
if (lean_obj_tag(v___x_875_) == 0)
{
lean_object* v_a_876_; lean_object* v___x_878_; uint8_t v_isShared_879_; uint8_t v_isSharedCheck_909_; 
v_a_876_ = lean_ctor_get(v___x_875_, 0);
v_isSharedCheck_909_ = !lean_is_exclusive(v___x_875_);
if (v_isSharedCheck_909_ == 0)
{
v___x_878_ = v___x_875_;
v_isShared_879_ = v_isSharedCheck_909_;
goto v_resetjp_877_;
}
else
{
lean_inc(v_a_876_);
lean_dec(v___x_875_);
v___x_878_ = lean_box(0);
v_isShared_879_ = v_isSharedCheck_909_;
goto v_resetjp_877_;
}
v_resetjp_877_:
{
lean_object* v_toRing_880_; lean_object* v_natCastFn_x3f_881_; 
v_toRing_880_ = lean_ctor_get(v_a_876_, 0);
lean_inc_ref(v_toRing_880_);
lean_dec(v_a_876_);
v_natCastFn_x3f_881_ = lean_ctor_get(v_toRing_880_, 12);
if (lean_obj_tag(v_natCastFn_x3f_881_) == 1)
{
lean_object* v_val_882_; lean_object* v___x_884_; 
lean_inc_ref(v_natCastFn_x3f_881_);
lean_dec_ref(v_toRing_880_);
lean_dec(v___y_873_);
lean_dec_ref(v___y_872_);
lean_dec(v___y_871_);
lean_dec_ref(v___y_870_);
lean_dec(v___y_869_);
lean_dec_ref(v___y_868_);
lean_dec(v___y_867_);
lean_dec_ref(v___y_866_);
lean_dec(v___y_865_);
lean_dec(v___y_864_);
lean_dec_ref(v___y_863_);
v_val_882_ = lean_ctor_get(v_natCastFn_x3f_881_, 0);
lean_inc(v_val_882_);
lean_dec_ref(v_natCastFn_x3f_881_);
if (v_isShared_879_ == 0)
{
lean_ctor_set(v___x_878_, 0, v_val_882_);
v___x_884_ = v___x_878_;
goto v_reusejp_883_;
}
else
{
lean_object* v_reuseFailAlloc_885_; 
v_reuseFailAlloc_885_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_885_, 0, v_val_882_);
v___x_884_ = v_reuseFailAlloc_885_;
goto v_reusejp_883_;
}
v_reusejp_883_:
{
return v___x_884_;
}
}
else
{
lean_object* v_type_886_; lean_object* v_u_887_; lean_object* v_semiringInst_888_; lean_object* v___x_889_; 
lean_del_object(v___x_878_);
v_type_886_ = lean_ctor_get(v_toRing_880_, 1);
lean_inc_ref(v_type_886_);
v_u_887_ = lean_ctor_get(v_toRing_880_, 2);
lean_inc(v_u_887_);
v_semiringInst_888_ = lean_ctor_get(v_toRing_880_, 4);
lean_inc_ref(v_semiringInst_888_);
lean_dec_ref(v_toRing_880_);
lean_inc(v___y_864_);
v___x_889_ = l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_getNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isNatCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__2_spec__4_spec__6___redArg(v_u_887_, v_type_886_, v_semiringInst_888_, v___y_864_, v___y_865_, v___y_866_, v___y_867_, v___y_868_, v___y_869_, v___y_870_, v___y_871_, v___y_872_, v___y_873_);
if (lean_obj_tag(v___x_889_) == 0)
{
lean_object* v_a_890_; lean_object* v___f_891_; lean_object* v___x_892_; 
v_a_890_ = lean_ctor_get(v___x_889_, 0);
lean_inc(v_a_890_);
lean_dec_ref(v___x_889_);
lean_inc(v_a_890_);
v___f_891_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isNatCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__2_spec__4___lam__0), 2, 1);
lean_closure_set(v___f_891_, 0, v_a_890_);
v___x_892_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(v___f_891_, v___y_863_, v___y_864_);
lean_dec(v___y_864_);
if (lean_obj_tag(v___x_892_) == 0)
{
lean_object* v___x_894_; uint8_t v_isShared_895_; uint8_t v_isSharedCheck_899_; 
v_isSharedCheck_899_ = !lean_is_exclusive(v___x_892_);
if (v_isSharedCheck_899_ == 0)
{
lean_object* v_unused_900_; 
v_unused_900_ = lean_ctor_get(v___x_892_, 0);
lean_dec(v_unused_900_);
v___x_894_ = v___x_892_;
v_isShared_895_ = v_isSharedCheck_899_;
goto v_resetjp_893_;
}
else
{
lean_dec(v___x_892_);
v___x_894_ = lean_box(0);
v_isShared_895_ = v_isSharedCheck_899_;
goto v_resetjp_893_;
}
v_resetjp_893_:
{
lean_object* v___x_897_; 
if (v_isShared_895_ == 0)
{
lean_ctor_set(v___x_894_, 0, v_a_890_);
v___x_897_ = v___x_894_;
goto v_reusejp_896_;
}
else
{
lean_object* v_reuseFailAlloc_898_; 
v_reuseFailAlloc_898_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_898_, 0, v_a_890_);
v___x_897_ = v_reuseFailAlloc_898_;
goto v_reusejp_896_;
}
v_reusejp_896_:
{
return v___x_897_;
}
}
}
else
{
lean_object* v_a_901_; lean_object* v___x_903_; uint8_t v_isShared_904_; uint8_t v_isSharedCheck_908_; 
lean_dec(v_a_890_);
v_a_901_ = lean_ctor_get(v___x_892_, 0);
v_isSharedCheck_908_ = !lean_is_exclusive(v___x_892_);
if (v_isSharedCheck_908_ == 0)
{
v___x_903_ = v___x_892_;
v_isShared_904_ = v_isSharedCheck_908_;
goto v_resetjp_902_;
}
else
{
lean_inc(v_a_901_);
lean_dec(v___x_892_);
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
else
{
lean_dec(v___y_864_);
lean_dec_ref(v___y_863_);
return v___x_889_;
}
}
}
}
else
{
lean_object* v_a_910_; lean_object* v___x_912_; uint8_t v_isShared_913_; uint8_t v_isSharedCheck_917_; 
lean_dec(v___y_873_);
lean_dec_ref(v___y_872_);
lean_dec(v___y_871_);
lean_dec_ref(v___y_870_);
lean_dec(v___y_869_);
lean_dec_ref(v___y_868_);
lean_dec(v___y_867_);
lean_dec_ref(v___y_866_);
lean_dec(v___y_865_);
lean_dec(v___y_864_);
lean_dec_ref(v___y_863_);
v_a_910_ = lean_ctor_get(v___x_875_, 0);
v_isSharedCheck_917_ = !lean_is_exclusive(v___x_875_);
if (v_isSharedCheck_917_ == 0)
{
v___x_912_ = v___x_875_;
v_isShared_913_ = v_isSharedCheck_917_;
goto v_resetjp_911_;
}
else
{
lean_inc(v_a_910_);
lean_dec(v___x_875_);
v___x_912_ = lean_box(0);
v_isShared_913_ = v_isSharedCheck_917_;
goto v_resetjp_911_;
}
v_resetjp_911_:
{
lean_object* v___x_915_; 
if (v_isShared_913_ == 0)
{
v___x_915_ = v___x_912_;
goto v_reusejp_914_;
}
else
{
lean_object* v_reuseFailAlloc_916_; 
v_reuseFailAlloc_916_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_916_, 0, v_a_910_);
v___x_915_ = v_reuseFailAlloc_916_;
goto v_reusejp_914_;
}
v_reusejp_914_:
{
return v___x_915_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isNatCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__2_spec__4___boxed(lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_){
_start:
{
lean_object* v_res_930_; 
v_res_930_ = l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isNatCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__2_spec__4(v___y_918_, v___y_919_, v___y_920_, v___y_921_, v___y_922_, v___y_923_, v___y_924_, v___y_925_, v___y_926_, v___y_927_, v___y_928_);
return v_res_930_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_isNatCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__2(lean_object* v_inst_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_){
_start:
{
lean_object* v___x_944_; 
v___x_944_ = l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isNatCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__2_spec__4(v___y_932_, v___y_933_, v___y_934_, v___y_935_, v___y_936_, v___y_937_, v___y_938_, v___y_939_, v___y_940_, v___y_941_, v___y_942_);
if (lean_obj_tag(v___x_944_) == 0)
{
lean_object* v_a_945_; lean_object* v___x_947_; uint8_t v_isShared_948_; uint8_t v_isSharedCheck_955_; 
v_a_945_ = lean_ctor_get(v___x_944_, 0);
v_isSharedCheck_955_ = !lean_is_exclusive(v___x_944_);
if (v_isSharedCheck_955_ == 0)
{
v___x_947_ = v___x_944_;
v_isShared_948_ = v_isSharedCheck_955_;
goto v_resetjp_946_;
}
else
{
lean_inc(v_a_945_);
lean_dec(v___x_944_);
v___x_947_ = lean_box(0);
v_isShared_948_ = v_isSharedCheck_955_;
goto v_resetjp_946_;
}
v_resetjp_946_:
{
lean_object* v___x_949_; uint8_t v___x_950_; lean_object* v___x_951_; lean_object* v___x_953_; 
v___x_949_ = l_Lean_Expr_appArg_x21(v_a_945_);
lean_dec(v_a_945_);
v___x_950_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v___x_949_, v_inst_931_);
lean_dec_ref(v___x_949_);
v___x_951_ = lean_box(v___x_950_);
if (v_isShared_948_ == 0)
{
lean_ctor_set(v___x_947_, 0, v___x_951_);
v___x_953_ = v___x_947_;
goto v_reusejp_952_;
}
else
{
lean_object* v_reuseFailAlloc_954_; 
v_reuseFailAlloc_954_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_954_, 0, v___x_951_);
v___x_953_ = v_reuseFailAlloc_954_;
goto v_reusejp_952_;
}
v_reusejp_952_:
{
return v___x_953_;
}
}
}
else
{
lean_object* v_a_956_; lean_object* v___x_958_; uint8_t v_isShared_959_; uint8_t v_isSharedCheck_963_; 
v_a_956_ = lean_ctor_get(v___x_944_, 0);
v_isSharedCheck_963_ = !lean_is_exclusive(v___x_944_);
if (v_isSharedCheck_963_ == 0)
{
v___x_958_ = v___x_944_;
v_isShared_959_ = v_isSharedCheck_963_;
goto v_resetjp_957_;
}
else
{
lean_inc(v_a_956_);
lean_dec(v___x_944_);
v___x_958_ = lean_box(0);
v_isShared_959_ = v_isSharedCheck_963_;
goto v_resetjp_957_;
}
v_resetjp_957_:
{
lean_object* v___x_961_; 
if (v_isShared_959_ == 0)
{
v___x_961_ = v___x_958_;
goto v_reusejp_960_;
}
else
{
lean_object* v_reuseFailAlloc_962_; 
v_reuseFailAlloc_962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_962_, 0, v_a_956_);
v___x_961_ = v_reuseFailAlloc_962_;
goto v_reusejp_960_;
}
v_reusejp_960_:
{
return v___x_961_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_isNatCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__2___boxed(lean_object* v_inst_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_, lean_object* v___y_976_){
_start:
{
lean_object* v_res_977_; 
v_res_977_ = l_Lean_Meta_Grind_Arith_CommRing_isNatCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__2(v_inst_964_, v___y_965_, v___y_966_, v___y_967_, v___y_968_, v___y_969_, v___y_970_, v___y_971_, v___y_972_, v___y_973_, v___y_974_, v___y_975_);
lean_dec_ref(v_inst_964_);
return v_res_977_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f(lean_object* v_e_978_, lean_object* v_a_979_, lean_object* v_a_980_, lean_object* v_a_981_, lean_object* v_a_982_, lean_object* v_a_983_, lean_object* v_a_984_, lean_object* v_a_985_, lean_object* v_a_986_, lean_object* v_a_987_, lean_object* v_a_988_, lean_object* v_a_989_){
_start:
{
lean_object* v___x_991_; 
v___x_991_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_978_, v_a_987_);
if (lean_obj_tag(v___x_991_) == 0)
{
lean_object* v_a_992_; lean_object* v___x_994_; uint8_t v_isShared_995_; uint8_t v_isSharedCheck_1155_; 
v_a_992_ = lean_ctor_get(v___x_991_, 0);
v_isSharedCheck_1155_ = !lean_is_exclusive(v___x_991_);
if (v_isSharedCheck_1155_ == 0)
{
v___x_994_ = v___x_991_;
v_isShared_995_ = v_isSharedCheck_1155_;
goto v_resetjp_993_;
}
else
{
lean_inc(v_a_992_);
lean_dec(v___x_991_);
v___x_994_ = lean_box(0);
v_isShared_995_ = v_isSharedCheck_1155_;
goto v_resetjp_993_;
}
v_resetjp_993_:
{
lean_object* v___x_1001_; uint8_t v___x_1002_; 
v___x_1001_ = l_Lean_Expr_cleanupAnnotations(v_a_992_);
v___x_1002_ = l_Lean_Expr_isApp(v___x_1001_);
if (v___x_1002_ == 0)
{
lean_dec_ref(v___x_1001_);
lean_dec(v_a_989_);
lean_dec_ref(v_a_988_);
lean_dec(v_a_987_);
lean_dec_ref(v_a_986_);
lean_dec(v_a_985_);
lean_dec_ref(v_a_984_);
lean_dec(v_a_983_);
lean_dec_ref(v_a_982_);
lean_dec(v_a_981_);
lean_dec(v_a_980_);
lean_dec_ref(v_a_979_);
goto v___jp_996_;
}
else
{
lean_object* v_arg_1003_; lean_object* v___x_1004_; uint8_t v___x_1005_; 
v_arg_1003_ = lean_ctor_get(v___x_1001_, 1);
lean_inc_ref(v_arg_1003_);
v___x_1004_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1001_);
v___x_1005_ = l_Lean_Expr_isApp(v___x_1004_);
if (v___x_1005_ == 0)
{
lean_dec_ref(v___x_1004_);
lean_dec_ref(v_arg_1003_);
lean_dec(v_a_989_);
lean_dec_ref(v_a_988_);
lean_dec(v_a_987_);
lean_dec_ref(v_a_986_);
lean_dec(v_a_985_);
lean_dec_ref(v_a_984_);
lean_dec(v_a_983_);
lean_dec_ref(v_a_982_);
lean_dec(v_a_981_);
lean_dec(v_a_980_);
lean_dec_ref(v_a_979_);
goto v___jp_996_;
}
else
{
lean_object* v_arg_1006_; lean_object* v___x_1007_; uint8_t v___x_1008_; 
v_arg_1006_ = lean_ctor_get(v___x_1004_, 1);
lean_inc_ref(v_arg_1006_);
v___x_1007_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1004_);
v___x_1008_ = l_Lean_Expr_isApp(v___x_1007_);
if (v___x_1008_ == 0)
{
lean_dec_ref(v___x_1007_);
lean_dec_ref(v_arg_1006_);
lean_dec_ref(v_arg_1003_);
lean_dec(v_a_989_);
lean_dec_ref(v_a_988_);
lean_dec(v_a_987_);
lean_dec_ref(v_a_986_);
lean_dec(v_a_985_);
lean_dec_ref(v_a_984_);
lean_dec(v_a_983_);
lean_dec_ref(v_a_982_);
lean_dec(v_a_981_);
lean_dec(v_a_980_);
lean_dec_ref(v_a_979_);
goto v___jp_996_;
}
else
{
lean_object* v___x_1009_; lean_object* v___x_1010_; uint8_t v___x_1011_; 
v___x_1009_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1007_);
v___x_1010_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__8));
v___x_1011_ = l_Lean_Expr_isConstOf(v___x_1009_, v___x_1010_);
if (v___x_1011_ == 0)
{
lean_object* v___x_1012_; uint8_t v___x_1013_; 
v___x_1012_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__5));
v___x_1013_ = l_Lean_Expr_isConstOf(v___x_1009_, v___x_1012_);
if (v___x_1013_ == 0)
{
lean_object* v___x_1014_; uint8_t v___x_1015_; 
v___x_1014_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__2));
v___x_1015_ = l_Lean_Expr_isConstOf(v___x_1009_, v___x_1014_);
if (v___x_1015_ == 0)
{
lean_object* v___x_1016_; uint8_t v___x_1017_; 
v___x_1016_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__11));
v___x_1017_ = l_Lean_Expr_isConstOf(v___x_1009_, v___x_1016_);
lean_dec_ref(v___x_1009_);
if (v___x_1017_ == 0)
{
lean_dec_ref(v_arg_1006_);
lean_dec_ref(v_arg_1003_);
lean_dec(v_a_989_);
lean_dec_ref(v_a_988_);
lean_dec(v_a_987_);
lean_dec_ref(v_a_986_);
lean_dec(v_a_985_);
lean_dec_ref(v_a_984_);
lean_dec(v_a_983_);
lean_dec_ref(v_a_982_);
lean_dec(v_a_981_);
lean_dec(v_a_980_);
lean_dec_ref(v_a_979_);
goto v___jp_996_;
}
else
{
lean_object* v___x_1018_; 
lean_del_object(v___x_994_);
lean_inc(v_a_989_);
lean_inc_ref(v_a_988_);
lean_inc(v_a_987_);
lean_inc_ref(v_a_986_);
lean_inc(v_a_985_);
lean_inc_ref(v_a_984_);
lean_inc(v_a_983_);
lean_inc_ref(v_a_982_);
lean_inc(v_a_981_);
lean_inc(v_a_980_);
lean_inc_ref(v_a_979_);
v___x_1018_ = l_Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0(v_arg_1006_, v_a_979_, v_a_980_, v_a_981_, v_a_982_, v_a_983_, v_a_984_, v_a_985_, v_a_986_, v_a_987_, v_a_988_, v_a_989_);
lean_dec_ref(v_arg_1006_);
if (lean_obj_tag(v___x_1018_) == 0)
{
lean_object* v_a_1019_; lean_object* v___x_1021_; uint8_t v_isShared_1022_; uint8_t v_isSharedCheck_1047_; 
v_a_1019_ = lean_ctor_get(v___x_1018_, 0);
v_isSharedCheck_1047_ = !lean_is_exclusive(v___x_1018_);
if (v_isSharedCheck_1047_ == 0)
{
v___x_1021_ = v___x_1018_;
v_isShared_1022_ = v_isSharedCheck_1047_;
goto v_resetjp_1020_;
}
else
{
lean_inc(v_a_1019_);
lean_dec(v___x_1018_);
v___x_1021_ = lean_box(0);
v_isShared_1022_ = v_isSharedCheck_1047_;
goto v_resetjp_1020_;
}
v_resetjp_1020_:
{
uint8_t v___x_1023_; 
v___x_1023_ = lean_unbox(v_a_1019_);
lean_dec(v_a_1019_);
if (v___x_1023_ == 0)
{
lean_object* v___x_1024_; lean_object* v___x_1026_; 
lean_dec_ref(v_arg_1003_);
lean_dec(v_a_989_);
lean_dec_ref(v_a_988_);
lean_dec(v_a_987_);
lean_dec_ref(v_a_986_);
lean_dec(v_a_985_);
lean_dec_ref(v_a_984_);
lean_dec(v_a_983_);
lean_dec_ref(v_a_982_);
lean_dec(v_a_981_);
lean_dec(v_a_980_);
lean_dec_ref(v_a_979_);
v___x_1024_ = lean_box(0);
if (v_isShared_1022_ == 0)
{
lean_ctor_set(v___x_1021_, 0, v___x_1024_);
v___x_1026_ = v___x_1021_;
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
else
{
lean_object* v___x_1028_; 
lean_del_object(v___x_1021_);
v___x_1028_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f(v_arg_1003_, v_a_979_, v_a_980_, v_a_981_, v_a_982_, v_a_983_, v_a_984_, v_a_985_, v_a_986_, v_a_987_, v_a_988_, v_a_989_);
if (lean_obj_tag(v___x_1028_) == 0)
{
lean_object* v_a_1029_; 
v_a_1029_ = lean_ctor_get(v___x_1028_, 0);
lean_inc(v_a_1029_);
if (lean_obj_tag(v_a_1029_) == 0)
{
return v___x_1028_;
}
else
{
lean_object* v___x_1031_; uint8_t v_isShared_1032_; uint8_t v_isSharedCheck_1045_; 
v_isSharedCheck_1045_ = !lean_is_exclusive(v___x_1028_);
if (v_isSharedCheck_1045_ == 0)
{
lean_object* v_unused_1046_; 
v_unused_1046_ = lean_ctor_get(v___x_1028_, 0);
lean_dec(v_unused_1046_);
v___x_1031_ = v___x_1028_;
v_isShared_1032_ = v_isSharedCheck_1045_;
goto v_resetjp_1030_;
}
else
{
lean_dec(v___x_1028_);
v___x_1031_ = lean_box(0);
v_isShared_1032_ = v_isSharedCheck_1045_;
goto v_resetjp_1030_;
}
v_resetjp_1030_:
{
lean_object* v_val_1033_; lean_object* v___x_1035_; uint8_t v_isShared_1036_; uint8_t v_isSharedCheck_1044_; 
v_val_1033_ = lean_ctor_get(v_a_1029_, 0);
v_isSharedCheck_1044_ = !lean_is_exclusive(v_a_1029_);
if (v_isSharedCheck_1044_ == 0)
{
v___x_1035_ = v_a_1029_;
v_isShared_1036_ = v_isSharedCheck_1044_;
goto v_resetjp_1034_;
}
else
{
lean_inc(v_val_1033_);
lean_dec(v_a_1029_);
v___x_1035_ = lean_box(0);
v_isShared_1036_ = v_isSharedCheck_1044_;
goto v_resetjp_1034_;
}
v_resetjp_1034_:
{
lean_object* v___x_1037_; lean_object* v___x_1039_; 
v___x_1037_ = lean_int_neg(v_val_1033_);
lean_dec(v_val_1033_);
if (v_isShared_1036_ == 0)
{
lean_ctor_set(v___x_1035_, 0, v___x_1037_);
v___x_1039_ = v___x_1035_;
goto v_reusejp_1038_;
}
else
{
lean_object* v_reuseFailAlloc_1043_; 
v_reuseFailAlloc_1043_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1043_, 0, v___x_1037_);
v___x_1039_ = v_reuseFailAlloc_1043_;
goto v_reusejp_1038_;
}
v_reusejp_1038_:
{
lean_object* v___x_1041_; 
if (v_isShared_1032_ == 0)
{
lean_ctor_set(v___x_1031_, 0, v___x_1039_);
v___x_1041_ = v___x_1031_;
goto v_reusejp_1040_;
}
else
{
lean_object* v_reuseFailAlloc_1042_; 
v_reuseFailAlloc_1042_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1042_, 0, v___x_1039_);
v___x_1041_ = v_reuseFailAlloc_1042_;
goto v_reusejp_1040_;
}
v_reusejp_1040_:
{
return v___x_1041_;
}
}
}
}
}
}
else
{
return v___x_1028_;
}
}
}
}
else
{
lean_object* v_a_1048_; lean_object* v___x_1050_; uint8_t v_isShared_1051_; uint8_t v_isSharedCheck_1055_; 
lean_dec_ref(v_arg_1003_);
lean_dec(v_a_989_);
lean_dec_ref(v_a_988_);
lean_dec(v_a_987_);
lean_dec_ref(v_a_986_);
lean_dec(v_a_985_);
lean_dec_ref(v_a_984_);
lean_dec(v_a_983_);
lean_dec_ref(v_a_982_);
lean_dec(v_a_981_);
lean_dec(v_a_980_);
lean_dec_ref(v_a_979_);
v_a_1048_ = lean_ctor_get(v___x_1018_, 0);
v_isSharedCheck_1055_ = !lean_is_exclusive(v___x_1018_);
if (v_isSharedCheck_1055_ == 0)
{
v___x_1050_ = v___x_1018_;
v_isShared_1051_ = v_isSharedCheck_1055_;
goto v_resetjp_1049_;
}
else
{
lean_inc(v_a_1048_);
lean_dec(v___x_1018_);
v___x_1050_ = lean_box(0);
v_isShared_1051_ = v_isSharedCheck_1055_;
goto v_resetjp_1049_;
}
v_resetjp_1049_:
{
lean_object* v___x_1053_; 
if (v_isShared_1051_ == 0)
{
v___x_1053_ = v___x_1050_;
goto v_reusejp_1052_;
}
else
{
lean_object* v_reuseFailAlloc_1054_; 
v_reuseFailAlloc_1054_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1054_, 0, v_a_1048_);
v___x_1053_ = v_reuseFailAlloc_1054_;
goto v_reusejp_1052_;
}
v_reusejp_1052_:
{
return v___x_1053_;
}
}
}
}
}
else
{
lean_object* v___x_1056_; 
lean_dec_ref(v___x_1009_);
lean_del_object(v___x_994_);
lean_inc(v_a_989_);
lean_inc_ref(v_a_988_);
lean_inc(v_a_987_);
lean_inc_ref(v_a_986_);
v___x_1056_ = l_Lean_Meta_Grind_Arith_CommRing_isIntCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__1(v_arg_1006_, v_a_979_, v_a_980_, v_a_981_, v_a_982_, v_a_983_, v_a_984_, v_a_985_, v_a_986_, v_a_987_, v_a_988_, v_a_989_);
lean_dec_ref(v_arg_1006_);
if (lean_obj_tag(v___x_1056_) == 0)
{
lean_object* v_a_1057_; lean_object* v___x_1059_; uint8_t v_isShared_1060_; uint8_t v_isSharedCheck_1067_; 
v_a_1057_ = lean_ctor_get(v___x_1056_, 0);
v_isSharedCheck_1067_ = !lean_is_exclusive(v___x_1056_);
if (v_isSharedCheck_1067_ == 0)
{
v___x_1059_ = v___x_1056_;
v_isShared_1060_ = v_isSharedCheck_1067_;
goto v_resetjp_1058_;
}
else
{
lean_inc(v_a_1057_);
lean_dec(v___x_1056_);
v___x_1059_ = lean_box(0);
v_isShared_1060_ = v_isSharedCheck_1067_;
goto v_resetjp_1058_;
}
v_resetjp_1058_:
{
uint8_t v___x_1061_; 
v___x_1061_ = lean_unbox(v_a_1057_);
lean_dec(v_a_1057_);
if (v___x_1061_ == 0)
{
lean_object* v___x_1062_; lean_object* v___x_1064_; 
lean_dec_ref(v_arg_1003_);
lean_dec(v_a_989_);
lean_dec_ref(v_a_988_);
lean_dec(v_a_987_);
lean_dec_ref(v_a_986_);
v___x_1062_ = lean_box(0);
if (v_isShared_1060_ == 0)
{
lean_ctor_set(v___x_1059_, 0, v___x_1062_);
v___x_1064_ = v___x_1059_;
goto v_reusejp_1063_;
}
else
{
lean_object* v_reuseFailAlloc_1065_; 
v_reuseFailAlloc_1065_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1065_, 0, v___x_1062_);
v___x_1064_ = v_reuseFailAlloc_1065_;
goto v_reusejp_1063_;
}
v_reusejp_1063_:
{
return v___x_1064_;
}
}
else
{
lean_object* v___x_1066_; 
lean_del_object(v___x_1059_);
v___x_1066_ = l_Lean_Meta_getIntValue_x3f(v_arg_1003_, v_a_986_, v_a_987_, v_a_988_, v_a_989_);
return v___x_1066_;
}
}
}
else
{
lean_object* v_a_1068_; lean_object* v___x_1070_; uint8_t v_isShared_1071_; uint8_t v_isSharedCheck_1075_; 
lean_dec_ref(v_arg_1003_);
lean_dec(v_a_989_);
lean_dec_ref(v_a_988_);
lean_dec(v_a_987_);
lean_dec_ref(v_a_986_);
v_a_1068_ = lean_ctor_get(v___x_1056_, 0);
v_isSharedCheck_1075_ = !lean_is_exclusive(v___x_1056_);
if (v_isSharedCheck_1075_ == 0)
{
v___x_1070_ = v___x_1056_;
v_isShared_1071_ = v_isSharedCheck_1075_;
goto v_resetjp_1069_;
}
else
{
lean_inc(v_a_1068_);
lean_dec(v___x_1056_);
v___x_1070_ = lean_box(0);
v_isShared_1071_ = v_isSharedCheck_1075_;
goto v_resetjp_1069_;
}
v_resetjp_1069_:
{
lean_object* v___x_1073_; 
if (v_isShared_1071_ == 0)
{
v___x_1073_ = v___x_1070_;
goto v_reusejp_1072_;
}
else
{
lean_object* v_reuseFailAlloc_1074_; 
v_reuseFailAlloc_1074_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1074_, 0, v_a_1068_);
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
else
{
lean_object* v___x_1076_; 
lean_dec_ref(v___x_1009_);
lean_del_object(v___x_994_);
lean_inc(v_a_989_);
lean_inc_ref(v_a_988_);
lean_inc(v_a_987_);
lean_inc_ref(v_a_986_);
v___x_1076_ = l_Lean_Meta_Grind_Arith_CommRing_isNatCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__2(v_arg_1006_, v_a_979_, v_a_980_, v_a_981_, v_a_982_, v_a_983_, v_a_984_, v_a_985_, v_a_986_, v_a_987_, v_a_988_, v_a_989_);
lean_dec_ref(v_arg_1006_);
if (lean_obj_tag(v___x_1076_) == 0)
{
lean_object* v_a_1077_; lean_object* v___x_1079_; uint8_t v_isShared_1080_; uint8_t v_isSharedCheck_1116_; 
v_a_1077_ = lean_ctor_get(v___x_1076_, 0);
v_isSharedCheck_1116_ = !lean_is_exclusive(v___x_1076_);
if (v_isSharedCheck_1116_ == 0)
{
v___x_1079_ = v___x_1076_;
v_isShared_1080_ = v_isSharedCheck_1116_;
goto v_resetjp_1078_;
}
else
{
lean_inc(v_a_1077_);
lean_dec(v___x_1076_);
v___x_1079_ = lean_box(0);
v_isShared_1080_ = v_isSharedCheck_1116_;
goto v_resetjp_1078_;
}
v_resetjp_1078_:
{
uint8_t v___x_1081_; 
v___x_1081_ = lean_unbox(v_a_1077_);
lean_dec(v_a_1077_);
if (v___x_1081_ == 0)
{
lean_object* v___x_1082_; lean_object* v___x_1084_; 
lean_dec_ref(v_arg_1003_);
lean_dec(v_a_989_);
lean_dec_ref(v_a_988_);
lean_dec(v_a_987_);
lean_dec_ref(v_a_986_);
v___x_1082_ = lean_box(0);
if (v_isShared_1080_ == 0)
{
lean_ctor_set(v___x_1079_, 0, v___x_1082_);
v___x_1084_ = v___x_1079_;
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
else
{
lean_object* v___x_1086_; 
lean_del_object(v___x_1079_);
v___x_1086_ = l_Lean_Meta_getNatValue_x3f(v_arg_1003_, v_a_986_, v_a_987_, v_a_988_, v_a_989_);
lean_dec_ref(v_arg_1003_);
if (lean_obj_tag(v___x_1086_) == 0)
{
lean_object* v_a_1087_; lean_object* v___x_1089_; uint8_t v_isShared_1090_; uint8_t v_isSharedCheck_1107_; 
v_a_1087_ = lean_ctor_get(v___x_1086_, 0);
v_isSharedCheck_1107_ = !lean_is_exclusive(v___x_1086_);
if (v_isSharedCheck_1107_ == 0)
{
v___x_1089_ = v___x_1086_;
v_isShared_1090_ = v_isSharedCheck_1107_;
goto v_resetjp_1088_;
}
else
{
lean_inc(v_a_1087_);
lean_dec(v___x_1086_);
v___x_1089_ = lean_box(0);
v_isShared_1090_ = v_isSharedCheck_1107_;
goto v_resetjp_1088_;
}
v_resetjp_1088_:
{
if (lean_obj_tag(v_a_1087_) == 1)
{
lean_object* v_val_1091_; lean_object* v___x_1093_; uint8_t v_isShared_1094_; uint8_t v_isSharedCheck_1102_; 
v_val_1091_ = lean_ctor_get(v_a_1087_, 0);
v_isSharedCheck_1102_ = !lean_is_exclusive(v_a_1087_);
if (v_isSharedCheck_1102_ == 0)
{
v___x_1093_ = v_a_1087_;
v_isShared_1094_ = v_isSharedCheck_1102_;
goto v_resetjp_1092_;
}
else
{
lean_inc(v_val_1091_);
lean_dec(v_a_1087_);
v___x_1093_ = lean_box(0);
v_isShared_1094_ = v_isSharedCheck_1102_;
goto v_resetjp_1092_;
}
v_resetjp_1092_:
{
lean_object* v___x_1095_; lean_object* v___x_1097_; 
v___x_1095_ = lean_nat_to_int(v_val_1091_);
if (v_isShared_1094_ == 0)
{
lean_ctor_set(v___x_1093_, 0, v___x_1095_);
v___x_1097_ = v___x_1093_;
goto v_reusejp_1096_;
}
else
{
lean_object* v_reuseFailAlloc_1101_; 
v_reuseFailAlloc_1101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1101_, 0, v___x_1095_);
v___x_1097_ = v_reuseFailAlloc_1101_;
goto v_reusejp_1096_;
}
v_reusejp_1096_:
{
lean_object* v___x_1099_; 
if (v_isShared_1090_ == 0)
{
lean_ctor_set(v___x_1089_, 0, v___x_1097_);
v___x_1099_ = v___x_1089_;
goto v_reusejp_1098_;
}
else
{
lean_object* v_reuseFailAlloc_1100_; 
v_reuseFailAlloc_1100_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1100_, 0, v___x_1097_);
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
else
{
lean_object* v___x_1103_; lean_object* v___x_1105_; 
lean_dec(v_a_1087_);
v___x_1103_ = lean_box(0);
if (v_isShared_1090_ == 0)
{
lean_ctor_set(v___x_1089_, 0, v___x_1103_);
v___x_1105_ = v___x_1089_;
goto v_reusejp_1104_;
}
else
{
lean_object* v_reuseFailAlloc_1106_; 
v_reuseFailAlloc_1106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1106_, 0, v___x_1103_);
v___x_1105_ = v_reuseFailAlloc_1106_;
goto v_reusejp_1104_;
}
v_reusejp_1104_:
{
return v___x_1105_;
}
}
}
}
else
{
lean_object* v_a_1108_; lean_object* v___x_1110_; uint8_t v_isShared_1111_; uint8_t v_isSharedCheck_1115_; 
v_a_1108_ = lean_ctor_get(v___x_1086_, 0);
v_isSharedCheck_1115_ = !lean_is_exclusive(v___x_1086_);
if (v_isSharedCheck_1115_ == 0)
{
v___x_1110_ = v___x_1086_;
v_isShared_1111_ = v_isSharedCheck_1115_;
goto v_resetjp_1109_;
}
else
{
lean_inc(v_a_1108_);
lean_dec(v___x_1086_);
v___x_1110_ = lean_box(0);
v_isShared_1111_ = v_isSharedCheck_1115_;
goto v_resetjp_1109_;
}
v_resetjp_1109_:
{
lean_object* v___x_1113_; 
if (v_isShared_1111_ == 0)
{
v___x_1113_ = v___x_1110_;
goto v_reusejp_1112_;
}
else
{
lean_object* v_reuseFailAlloc_1114_; 
v_reuseFailAlloc_1114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1114_, 0, v_a_1108_);
v___x_1113_ = v_reuseFailAlloc_1114_;
goto v_reusejp_1112_;
}
v_reusejp_1112_:
{
return v___x_1113_;
}
}
}
}
}
}
else
{
lean_object* v_a_1117_; lean_object* v___x_1119_; uint8_t v_isShared_1120_; uint8_t v_isSharedCheck_1124_; 
lean_dec_ref(v_arg_1003_);
lean_dec(v_a_989_);
lean_dec_ref(v_a_988_);
lean_dec(v_a_987_);
lean_dec_ref(v_a_986_);
v_a_1117_ = lean_ctor_get(v___x_1076_, 0);
v_isSharedCheck_1124_ = !lean_is_exclusive(v___x_1076_);
if (v_isSharedCheck_1124_ == 0)
{
v___x_1119_ = v___x_1076_;
v_isShared_1120_ = v_isSharedCheck_1124_;
goto v_resetjp_1118_;
}
else
{
lean_inc(v_a_1117_);
lean_dec(v___x_1076_);
v___x_1119_ = lean_box(0);
v_isShared_1120_ = v_isSharedCheck_1124_;
goto v_resetjp_1118_;
}
v_resetjp_1118_:
{
lean_object* v___x_1122_; 
if (v_isShared_1120_ == 0)
{
v___x_1122_ = v___x_1119_;
goto v_reusejp_1121_;
}
else
{
lean_object* v_reuseFailAlloc_1123_; 
v_reuseFailAlloc_1123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1123_, 0, v_a_1117_);
v___x_1122_ = v_reuseFailAlloc_1123_;
goto v_reusejp_1121_;
}
v_reusejp_1121_:
{
return v___x_1122_;
}
}
}
}
}
else
{
lean_object* v___x_1125_; 
lean_dec_ref(v___x_1009_);
lean_dec_ref(v_arg_1003_);
lean_del_object(v___x_994_);
lean_dec(v_a_985_);
lean_dec_ref(v_a_984_);
lean_dec(v_a_983_);
lean_dec_ref(v_a_982_);
lean_dec(v_a_981_);
lean_dec(v_a_980_);
lean_dec_ref(v_a_979_);
v___x_1125_ = l_Lean_Meta_getNatValue_x3f(v_arg_1006_, v_a_986_, v_a_987_, v_a_988_, v_a_989_);
lean_dec_ref(v_arg_1006_);
if (lean_obj_tag(v___x_1125_) == 0)
{
lean_object* v_a_1126_; lean_object* v___x_1128_; uint8_t v_isShared_1129_; uint8_t v_isSharedCheck_1146_; 
v_a_1126_ = lean_ctor_get(v___x_1125_, 0);
v_isSharedCheck_1146_ = !lean_is_exclusive(v___x_1125_);
if (v_isSharedCheck_1146_ == 0)
{
v___x_1128_ = v___x_1125_;
v_isShared_1129_ = v_isSharedCheck_1146_;
goto v_resetjp_1127_;
}
else
{
lean_inc(v_a_1126_);
lean_dec(v___x_1125_);
v___x_1128_ = lean_box(0);
v_isShared_1129_ = v_isSharedCheck_1146_;
goto v_resetjp_1127_;
}
v_resetjp_1127_:
{
if (lean_obj_tag(v_a_1126_) == 1)
{
lean_object* v_val_1130_; lean_object* v___x_1132_; uint8_t v_isShared_1133_; uint8_t v_isSharedCheck_1141_; 
v_val_1130_ = lean_ctor_get(v_a_1126_, 0);
v_isSharedCheck_1141_ = !lean_is_exclusive(v_a_1126_);
if (v_isSharedCheck_1141_ == 0)
{
v___x_1132_ = v_a_1126_;
v_isShared_1133_ = v_isSharedCheck_1141_;
goto v_resetjp_1131_;
}
else
{
lean_inc(v_val_1130_);
lean_dec(v_a_1126_);
v___x_1132_ = lean_box(0);
v_isShared_1133_ = v_isSharedCheck_1141_;
goto v_resetjp_1131_;
}
v_resetjp_1131_:
{
lean_object* v___x_1134_; lean_object* v___x_1136_; 
v___x_1134_ = lean_nat_to_int(v_val_1130_);
if (v_isShared_1133_ == 0)
{
lean_ctor_set(v___x_1132_, 0, v___x_1134_);
v___x_1136_ = v___x_1132_;
goto v_reusejp_1135_;
}
else
{
lean_object* v_reuseFailAlloc_1140_; 
v_reuseFailAlloc_1140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1140_, 0, v___x_1134_);
v___x_1136_ = v_reuseFailAlloc_1140_;
goto v_reusejp_1135_;
}
v_reusejp_1135_:
{
lean_object* v___x_1138_; 
if (v_isShared_1129_ == 0)
{
lean_ctor_set(v___x_1128_, 0, v___x_1136_);
v___x_1138_ = v___x_1128_;
goto v_reusejp_1137_;
}
else
{
lean_object* v_reuseFailAlloc_1139_; 
v_reuseFailAlloc_1139_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1139_, 0, v___x_1136_);
v___x_1138_ = v_reuseFailAlloc_1139_;
goto v_reusejp_1137_;
}
v_reusejp_1137_:
{
return v___x_1138_;
}
}
}
}
else
{
lean_object* v___x_1142_; lean_object* v___x_1144_; 
lean_dec(v_a_1126_);
v___x_1142_ = lean_box(0);
if (v_isShared_1129_ == 0)
{
lean_ctor_set(v___x_1128_, 0, v___x_1142_);
v___x_1144_ = v___x_1128_;
goto v_reusejp_1143_;
}
else
{
lean_object* v_reuseFailAlloc_1145_; 
v_reuseFailAlloc_1145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1145_, 0, v___x_1142_);
v___x_1144_ = v_reuseFailAlloc_1145_;
goto v_reusejp_1143_;
}
v_reusejp_1143_:
{
return v___x_1144_;
}
}
}
}
else
{
lean_object* v_a_1147_; lean_object* v___x_1149_; uint8_t v_isShared_1150_; uint8_t v_isSharedCheck_1154_; 
v_a_1147_ = lean_ctor_get(v___x_1125_, 0);
v_isSharedCheck_1154_ = !lean_is_exclusive(v___x_1125_);
if (v_isSharedCheck_1154_ == 0)
{
v___x_1149_ = v___x_1125_;
v_isShared_1150_ = v_isSharedCheck_1154_;
goto v_resetjp_1148_;
}
else
{
lean_inc(v_a_1147_);
lean_dec(v___x_1125_);
v___x_1149_ = lean_box(0);
v_isShared_1150_ = v_isSharedCheck_1154_;
goto v_resetjp_1148_;
}
v_resetjp_1148_:
{
lean_object* v___x_1152_; 
if (v_isShared_1150_ == 0)
{
v___x_1152_ = v___x_1149_;
goto v_reusejp_1151_;
}
else
{
lean_object* v_reuseFailAlloc_1153_; 
v_reuseFailAlloc_1153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1153_, 0, v_a_1147_);
v___x_1152_ = v_reuseFailAlloc_1153_;
goto v_reusejp_1151_;
}
v_reusejp_1151_:
{
return v___x_1152_;
}
}
}
}
}
}
}
v___jp_996_:
{
lean_object* v___x_997_; lean_object* v___x_999_; 
v___x_997_ = lean_box(0);
if (v_isShared_995_ == 0)
{
lean_ctor_set(v___x_994_, 0, v___x_997_);
v___x_999_ = v___x_994_;
goto v_reusejp_998_;
}
else
{
lean_object* v_reuseFailAlloc_1000_; 
v_reuseFailAlloc_1000_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1000_, 0, v___x_997_);
v___x_999_ = v_reuseFailAlloc_1000_;
goto v_reusejp_998_;
}
v_reusejp_998_:
{
return v___x_999_;
}
}
}
}
else
{
lean_object* v_a_1156_; lean_object* v___x_1158_; uint8_t v_isShared_1159_; uint8_t v_isSharedCheck_1163_; 
lean_dec(v_a_989_);
lean_dec_ref(v_a_988_);
lean_dec(v_a_987_);
lean_dec_ref(v_a_986_);
lean_dec(v_a_985_);
lean_dec_ref(v_a_984_);
lean_dec(v_a_983_);
lean_dec_ref(v_a_982_);
lean_dec(v_a_981_);
lean_dec(v_a_980_);
lean_dec_ref(v_a_979_);
v_a_1156_ = lean_ctor_get(v___x_991_, 0);
v_isSharedCheck_1163_ = !lean_is_exclusive(v___x_991_);
if (v_isSharedCheck_1163_ == 0)
{
v___x_1158_ = v___x_991_;
v_isShared_1159_ = v_isSharedCheck_1163_;
goto v_resetjp_1157_;
}
else
{
lean_inc(v_a_1156_);
lean_dec(v___x_991_);
v___x_1158_ = lean_box(0);
v_isShared_1159_ = v_isSharedCheck_1163_;
goto v_resetjp_1157_;
}
v_resetjp_1157_:
{
lean_object* v___x_1161_; 
if (v_isShared_1159_ == 0)
{
v___x_1161_ = v___x_1158_;
goto v_reusejp_1160_;
}
else
{
lean_object* v_reuseFailAlloc_1162_; 
v_reuseFailAlloc_1162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1162_, 0, v_a_1156_);
v___x_1161_ = v_reuseFailAlloc_1162_;
goto v_reusejp_1160_;
}
v_reusejp_1160_:
{
return v___x_1161_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f___boxed(lean_object* v_e_1164_, lean_object* v_a_1165_, lean_object* v_a_1166_, lean_object* v_a_1167_, lean_object* v_a_1168_, lean_object* v_a_1169_, lean_object* v_a_1170_, lean_object* v_a_1171_, lean_object* v_a_1172_, lean_object* v_a_1173_, lean_object* v_a_1174_, lean_object* v_a_1175_, lean_object* v_a_1176_){
_start:
{
lean_object* v_res_1177_; 
v_res_1177_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f(v_e_1164_, v_a_1165_, v_a_1166_, v_a_1167_, v_a_1168_, v_a_1169_, v_a_1170_, v_a_1171_, v_a_1172_, v_a_1173_, v_a_1174_, v_a_1175_);
return v_res_1177_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_getNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isNatCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__2_spec__4_spec__6(lean_object* v_u_1178_, lean_object* v_type_1179_, lean_object* v_semiringInst_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_){
_start:
{
lean_object* v___x_1193_; 
v___x_1193_ = l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_getNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isNatCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__2_spec__4_spec__6___redArg(v_u_1178_, v_type_1179_, v_semiringInst_1180_, v___y_1182_, v___y_1183_, v___y_1184_, v___y_1185_, v___y_1186_, v___y_1187_, v___y_1188_, v___y_1189_, v___y_1190_, v___y_1191_);
return v___x_1193_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_getNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isNatCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__2_spec__4_spec__6___boxed(lean_object* v_u_1194_, lean_object* v_type_1195_, lean_object* v_semiringInst_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_){
_start:
{
lean_object* v_res_1209_; 
v_res_1209_ = l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_getNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isNatCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__2_spec__4_spec__6(v_u_1194_, v_type_1195_, v_semiringInst_1196_, v___y_1197_, v___y_1198_, v___y_1199_, v___y_1200_, v___y_1201_, v___y_1202_, v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_, v___y_1207_);
lean_dec_ref(v___y_1197_);
return v_res_1209_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1_spec__5_spec__8(lean_object* v_00_u03b1_1210_, lean_object* v_msg_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_){
_start:
{
lean_object* v___x_1224_; 
v___x_1224_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1_spec__5_spec__8___redArg(v_msg_1211_, v___y_1219_, v___y_1220_, v___y_1221_, v___y_1222_);
return v___x_1224_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1_spec__5_spec__8___boxed(lean_object* v_00_u03b1_1225_, lean_object* v_msg_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_){
_start:
{
lean_object* v_res_1239_; 
v_res_1239_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1_spec__5_spec__8(v_00_u03b1_1225_, v_msg_1226_, v___y_1227_, v___y_1228_, v___y_1229_, v___y_1230_, v___y_1231_, v___y_1232_, v___y_1233_, v___y_1234_, v___y_1235_, v___y_1236_, v___y_1237_);
lean_dec(v___y_1237_);
lean_dec_ref(v___y_1236_);
lean_dec(v___y_1235_);
lean_dec_ref(v___y_1234_);
lean_dec(v___y_1233_);
lean_dec_ref(v___y_1232_);
lean_dec(v___y_1231_);
lean_dec_ref(v___y_1230_);
lean_dec(v___y_1229_);
lean_dec(v___y_1228_);
lean_dec_ref(v___y_1227_);
return v_res_1239_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___lam__0(lean_object* v_a_1240_, lean_object* v_s_1241_){
_start:
{
lean_object* v_toRing_1242_; lean_object* v_semiringId_x3f_1243_; lean_object* v_commSemiringInst_1244_; lean_object* v_commRingInst_1245_; lean_object* v_noZeroDivInst_x3f_1246_; lean_object* v_fieldInst_x3f_1247_; lean_object* v_denoteEntries_1248_; lean_object* v_nextId_1249_; lean_object* v_steps_1250_; lean_object* v_queue_1251_; lean_object* v_basis_1252_; lean_object* v_diseqs_1253_; uint8_t v_recheck_1254_; lean_object* v_invSet_1255_; lean_object* v_numEq0_x3f_1256_; uint8_t v_numEq0Updated_1257_; lean_object* v___x_1259_; uint8_t v_isShared_1260_; uint8_t v_isSharedCheck_1265_; 
v_toRing_1242_ = lean_ctor_get(v_s_1241_, 0);
v_semiringId_x3f_1243_ = lean_ctor_get(v_s_1241_, 2);
v_commSemiringInst_1244_ = lean_ctor_get(v_s_1241_, 3);
v_commRingInst_1245_ = lean_ctor_get(v_s_1241_, 4);
v_noZeroDivInst_x3f_1246_ = lean_ctor_get(v_s_1241_, 5);
v_fieldInst_x3f_1247_ = lean_ctor_get(v_s_1241_, 6);
v_denoteEntries_1248_ = lean_ctor_get(v_s_1241_, 7);
v_nextId_1249_ = lean_ctor_get(v_s_1241_, 8);
v_steps_1250_ = lean_ctor_get(v_s_1241_, 9);
v_queue_1251_ = lean_ctor_get(v_s_1241_, 10);
v_basis_1252_ = lean_ctor_get(v_s_1241_, 11);
v_diseqs_1253_ = lean_ctor_get(v_s_1241_, 12);
v_recheck_1254_ = lean_ctor_get_uint8(v_s_1241_, sizeof(void*)*15);
v_invSet_1255_ = lean_ctor_get(v_s_1241_, 13);
v_numEq0_x3f_1256_ = lean_ctor_get(v_s_1241_, 14);
v_numEq0Updated_1257_ = lean_ctor_get_uint8(v_s_1241_, sizeof(void*)*15 + 1);
v_isSharedCheck_1265_ = !lean_is_exclusive(v_s_1241_);
if (v_isSharedCheck_1265_ == 0)
{
lean_object* v_unused_1266_; 
v_unused_1266_ = lean_ctor_get(v_s_1241_, 1);
lean_dec(v_unused_1266_);
v___x_1259_ = v_s_1241_;
v_isShared_1260_ = v_isSharedCheck_1265_;
goto v_resetjp_1258_;
}
else
{
lean_inc(v_numEq0_x3f_1256_);
lean_inc(v_invSet_1255_);
lean_inc(v_diseqs_1253_);
lean_inc(v_basis_1252_);
lean_inc(v_queue_1251_);
lean_inc(v_steps_1250_);
lean_inc(v_nextId_1249_);
lean_inc(v_denoteEntries_1248_);
lean_inc(v_fieldInst_x3f_1247_);
lean_inc(v_noZeroDivInst_x3f_1246_);
lean_inc(v_commRingInst_1245_);
lean_inc(v_commSemiringInst_1244_);
lean_inc(v_semiringId_x3f_1243_);
lean_inc(v_toRing_1242_);
lean_dec(v_s_1241_);
v___x_1259_ = lean_box(0);
v_isShared_1260_ = v_isSharedCheck_1265_;
goto v_resetjp_1258_;
}
v_resetjp_1258_:
{
lean_object* v___x_1261_; lean_object* v___x_1263_; 
v___x_1261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1261_, 0, v_a_1240_);
if (v_isShared_1260_ == 0)
{
lean_ctor_set(v___x_1259_, 1, v___x_1261_);
v___x_1263_ = v___x_1259_;
goto v_reusejp_1262_;
}
else
{
lean_object* v_reuseFailAlloc_1264_; 
v_reuseFailAlloc_1264_ = lean_alloc_ctor(0, 15, 2);
lean_ctor_set(v_reuseFailAlloc_1264_, 0, v_toRing_1242_);
lean_ctor_set(v_reuseFailAlloc_1264_, 1, v___x_1261_);
lean_ctor_set(v_reuseFailAlloc_1264_, 2, v_semiringId_x3f_1243_);
lean_ctor_set(v_reuseFailAlloc_1264_, 3, v_commSemiringInst_1244_);
lean_ctor_set(v_reuseFailAlloc_1264_, 4, v_commRingInst_1245_);
lean_ctor_set(v_reuseFailAlloc_1264_, 5, v_noZeroDivInst_x3f_1246_);
lean_ctor_set(v_reuseFailAlloc_1264_, 6, v_fieldInst_x3f_1247_);
lean_ctor_set(v_reuseFailAlloc_1264_, 7, v_denoteEntries_1248_);
lean_ctor_set(v_reuseFailAlloc_1264_, 8, v_nextId_1249_);
lean_ctor_set(v_reuseFailAlloc_1264_, 9, v_steps_1250_);
lean_ctor_set(v_reuseFailAlloc_1264_, 10, v_queue_1251_);
lean_ctor_set(v_reuseFailAlloc_1264_, 11, v_basis_1252_);
lean_ctor_set(v_reuseFailAlloc_1264_, 12, v_diseqs_1253_);
lean_ctor_set(v_reuseFailAlloc_1264_, 13, v_invSet_1255_);
lean_ctor_set(v_reuseFailAlloc_1264_, 14, v_numEq0_x3f_1256_);
lean_ctor_set_uint8(v_reuseFailAlloc_1264_, sizeof(void*)*15, v_recheck_1254_);
lean_ctor_set_uint8(v_reuseFailAlloc_1264_, sizeof(void*)*15 + 1, v_numEq0Updated_1257_);
v___x_1263_ = v_reuseFailAlloc_1264_;
goto v_reusejp_1262_;
}
v_reusejp_1262_:
{
return v___x_1263_;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___closed__8(void){
_start:
{
lean_object* v___x_1282_; lean_object* v___x_1283_; 
v___x_1282_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___closed__7));
v___x_1283_ = l_Lean_stringToMessageData(v___x_1282_);
return v___x_1283_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0(lean_object* v___y_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_){
_start:
{
lean_object* v___x_1296_; 
v___x_1296_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v___y_1284_, v___y_1285_, v___y_1286_, v___y_1287_, v___y_1288_, v___y_1289_, v___y_1290_, v___y_1291_, v___y_1292_, v___y_1293_, v___y_1294_);
if (lean_obj_tag(v___x_1296_) == 0)
{
lean_object* v_a_1297_; lean_object* v___x_1299_; uint8_t v_isShared_1300_; uint8_t v_isSharedCheck_1344_; 
v_a_1297_ = lean_ctor_get(v___x_1296_, 0);
v_isSharedCheck_1344_ = !lean_is_exclusive(v___x_1296_);
if (v_isSharedCheck_1344_ == 0)
{
v___x_1299_ = v___x_1296_;
v_isShared_1300_ = v_isSharedCheck_1344_;
goto v_resetjp_1298_;
}
else
{
lean_inc(v_a_1297_);
lean_dec(v___x_1296_);
v___x_1299_ = lean_box(0);
v_isShared_1300_ = v_isSharedCheck_1344_;
goto v_resetjp_1298_;
}
v_resetjp_1298_:
{
lean_object* v_fieldInst_x3f_1301_; 
v_fieldInst_x3f_1301_ = lean_ctor_get(v_a_1297_, 6);
if (lean_obj_tag(v_fieldInst_x3f_1301_) == 1)
{
lean_object* v_invFn_x3f_1302_; 
lean_inc_ref(v_fieldInst_x3f_1301_);
v_invFn_x3f_1302_ = lean_ctor_get(v_a_1297_, 1);
if (lean_obj_tag(v_invFn_x3f_1302_) == 1)
{
lean_object* v_val_1303_; lean_object* v___x_1305_; 
lean_inc_ref(v_invFn_x3f_1302_);
lean_dec_ref(v_fieldInst_x3f_1301_);
lean_dec(v_a_1297_);
lean_dec(v___y_1294_);
lean_dec_ref(v___y_1293_);
lean_dec(v___y_1292_);
lean_dec_ref(v___y_1291_);
lean_dec(v___y_1290_);
lean_dec_ref(v___y_1289_);
lean_dec(v___y_1288_);
lean_dec_ref(v___y_1287_);
lean_dec(v___y_1286_);
lean_dec(v___y_1285_);
lean_dec_ref(v___y_1284_);
v_val_1303_ = lean_ctor_get(v_invFn_x3f_1302_, 0);
lean_inc(v_val_1303_);
lean_dec_ref(v_invFn_x3f_1302_);
if (v_isShared_1300_ == 0)
{
lean_ctor_set(v___x_1299_, 0, v_val_1303_);
v___x_1305_ = v___x_1299_;
goto v_reusejp_1304_;
}
else
{
lean_object* v_reuseFailAlloc_1306_; 
v_reuseFailAlloc_1306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1306_, 0, v_val_1303_);
v___x_1305_ = v_reuseFailAlloc_1306_;
goto v_reusejp_1304_;
}
v_reusejp_1304_:
{
return v___x_1305_;
}
}
else
{
lean_object* v_toRing_1307_; lean_object* v_val_1308_; lean_object* v_type_1309_; lean_object* v_u_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v_expectedInst_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; 
lean_del_object(v___x_1299_);
v_toRing_1307_ = lean_ctor_get(v_a_1297_, 0);
lean_inc_ref(v_toRing_1307_);
lean_dec(v_a_1297_);
v_val_1308_ = lean_ctor_get(v_fieldInst_x3f_1301_, 0);
lean_inc(v_val_1308_);
lean_dec_ref(v_fieldInst_x3f_1301_);
v_type_1309_ = lean_ctor_get(v_toRing_1307_, 1);
lean_inc_ref(v_type_1309_);
v_u_1310_ = lean_ctor_get(v_toRing_1307_, 2);
lean_inc(v_u_1310_);
lean_dec_ref(v_toRing_1307_);
v___x_1311_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___closed__2));
v___x_1312_ = lean_box(0);
lean_inc(v_u_1310_);
v___x_1313_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1313_, 0, v_u_1310_);
lean_ctor_set(v___x_1313_, 1, v___x_1312_);
v___x_1314_ = l_Lean_mkConst(v___x_1311_, v___x_1313_);
lean_inc_ref(v_type_1309_);
v_expectedInst_1315_ = l_Lean_mkAppB(v___x_1314_, v_type_1309_, v_val_1308_);
v___x_1316_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___closed__4));
v___x_1317_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___closed__6));
lean_inc(v___y_1285_);
v___x_1318_ = l_Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1(v_type_1309_, v_u_1310_, v___x_1316_, v___x_1317_, v_expectedInst_1315_, v___y_1284_, v___y_1285_, v___y_1286_, v___y_1287_, v___y_1288_, v___y_1289_, v___y_1290_, v___y_1291_, v___y_1292_, v___y_1293_, v___y_1294_);
if (lean_obj_tag(v___x_1318_) == 0)
{
lean_object* v_a_1319_; lean_object* v___f_1320_; lean_object* v___x_1321_; 
v_a_1319_ = lean_ctor_get(v___x_1318_, 0);
lean_inc(v_a_1319_);
lean_dec_ref(v___x_1318_);
lean_inc(v_a_1319_);
v___f_1320_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___lam__0), 2, 1);
lean_closure_set(v___f_1320_, 0, v_a_1319_);
v___x_1321_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(v___f_1320_, v___y_1284_, v___y_1285_);
lean_dec(v___y_1285_);
if (lean_obj_tag(v___x_1321_) == 0)
{
lean_object* v___x_1323_; uint8_t v_isShared_1324_; uint8_t v_isSharedCheck_1328_; 
v_isSharedCheck_1328_ = !lean_is_exclusive(v___x_1321_);
if (v_isSharedCheck_1328_ == 0)
{
lean_object* v_unused_1329_; 
v_unused_1329_ = lean_ctor_get(v___x_1321_, 0);
lean_dec(v_unused_1329_);
v___x_1323_ = v___x_1321_;
v_isShared_1324_ = v_isSharedCheck_1328_;
goto v_resetjp_1322_;
}
else
{
lean_dec(v___x_1321_);
v___x_1323_ = lean_box(0);
v_isShared_1324_ = v_isSharedCheck_1328_;
goto v_resetjp_1322_;
}
v_resetjp_1322_:
{
lean_object* v___x_1326_; 
if (v_isShared_1324_ == 0)
{
lean_ctor_set(v___x_1323_, 0, v_a_1319_);
v___x_1326_ = v___x_1323_;
goto v_reusejp_1325_;
}
else
{
lean_object* v_reuseFailAlloc_1327_; 
v_reuseFailAlloc_1327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1327_, 0, v_a_1319_);
v___x_1326_ = v_reuseFailAlloc_1327_;
goto v_reusejp_1325_;
}
v_reusejp_1325_:
{
return v___x_1326_;
}
}
}
else
{
lean_object* v_a_1330_; lean_object* v___x_1332_; uint8_t v_isShared_1333_; uint8_t v_isSharedCheck_1337_; 
lean_dec(v_a_1319_);
v_a_1330_ = lean_ctor_get(v___x_1321_, 0);
v_isSharedCheck_1337_ = !lean_is_exclusive(v___x_1321_);
if (v_isSharedCheck_1337_ == 0)
{
v___x_1332_ = v___x_1321_;
v_isShared_1333_ = v_isSharedCheck_1337_;
goto v_resetjp_1331_;
}
else
{
lean_inc(v_a_1330_);
lean_dec(v___x_1321_);
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
else
{
lean_dec(v___y_1285_);
lean_dec_ref(v___y_1284_);
return v___x_1318_;
}
}
}
else
{
lean_object* v_toRing_1338_; lean_object* v_type_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; 
lean_del_object(v___x_1299_);
lean_dec(v___y_1290_);
lean_dec_ref(v___y_1289_);
lean_dec(v___y_1288_);
lean_dec_ref(v___y_1287_);
lean_dec(v___y_1286_);
lean_dec(v___y_1285_);
lean_dec_ref(v___y_1284_);
v_toRing_1338_ = lean_ctor_get(v_a_1297_, 0);
lean_inc_ref(v_toRing_1338_);
lean_dec(v_a_1297_);
v_type_1339_ = lean_ctor_get(v_toRing_1338_, 1);
lean_inc_ref(v_type_1339_);
lean_dec_ref(v_toRing_1338_);
v___x_1340_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___closed__8, &l_Lean_Meta_Grind_Arith_CommRing_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___closed__8_once, _init_l_Lean_Meta_Grind_Arith_CommRing_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___closed__8);
v___x_1341_ = l_Lean_indentExpr(v_type_1339_);
v___x_1342_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1342_, 0, v___x_1340_);
lean_ctor_set(v___x_1342_, 1, v___x_1341_);
v___x_1343_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1_spec__5_spec__8___redArg(v___x_1342_, v___y_1291_, v___y_1292_, v___y_1293_, v___y_1294_);
lean_dec(v___y_1294_);
lean_dec_ref(v___y_1293_);
lean_dec(v___y_1292_);
lean_dec_ref(v___y_1291_);
return v___x_1343_;
}
}
}
else
{
lean_object* v_a_1345_; lean_object* v___x_1347_; uint8_t v_isShared_1348_; uint8_t v_isSharedCheck_1352_; 
lean_dec(v___y_1294_);
lean_dec_ref(v___y_1293_);
lean_dec(v___y_1292_);
lean_dec_ref(v___y_1291_);
lean_dec(v___y_1290_);
lean_dec_ref(v___y_1289_);
lean_dec(v___y_1288_);
lean_dec_ref(v___y_1287_);
lean_dec(v___y_1286_);
lean_dec(v___y_1285_);
lean_dec_ref(v___y_1284_);
v_a_1345_ = lean_ctor_get(v___x_1296_, 0);
v_isSharedCheck_1352_ = !lean_is_exclusive(v___x_1296_);
if (v_isSharedCheck_1352_ == 0)
{
v___x_1347_ = v___x_1296_;
v_isShared_1348_ = v_isSharedCheck_1352_;
goto v_resetjp_1346_;
}
else
{
lean_inc(v_a_1345_);
lean_dec(v___x_1296_);
v___x_1347_ = lean_box(0);
v_isShared_1348_ = v_isSharedCheck_1352_;
goto v_resetjp_1346_;
}
v_resetjp_1346_:
{
lean_object* v___x_1350_; 
if (v_isShared_1348_ == 0)
{
v___x_1350_ = v___x_1347_;
goto v_reusejp_1349_;
}
else
{
lean_object* v_reuseFailAlloc_1351_; 
v_reuseFailAlloc_1351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1351_, 0, v_a_1345_);
v___x_1350_ = v_reuseFailAlloc_1351_;
goto v_reusejp_1349_;
}
v_reusejp_1349_:
{
return v___x_1350_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___boxed(lean_object* v___y_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_){
_start:
{
lean_object* v_res_1365_; 
v_res_1365_ = l_Lean_Meta_Grind_Arith_CommRing_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0(v___y_1353_, v___y_1354_, v___y_1355_, v___y_1356_, v___y_1357_, v___y_1358_, v___y_1359_, v___y_1360_, v___y_1361_, v___y_1362_, v___y_1363_);
return v_res_1365_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst(lean_object* v_inst_1366_, lean_object* v_a_1367_, lean_object* v_a_1368_, lean_object* v_a_1369_, lean_object* v_a_1370_, lean_object* v_a_1371_, lean_object* v_a_1372_, lean_object* v_a_1373_, lean_object* v_a_1374_, lean_object* v_a_1375_, lean_object* v_a_1376_, lean_object* v_a_1377_){
_start:
{
lean_object* v___x_1379_; 
v___x_1379_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v_a_1367_, v_a_1368_, v_a_1369_, v_a_1370_, v_a_1371_, v_a_1372_, v_a_1373_, v_a_1374_, v_a_1375_, v_a_1376_, v_a_1377_);
if (lean_obj_tag(v___x_1379_) == 0)
{
lean_object* v_a_1380_; lean_object* v___x_1382_; uint8_t v_isShared_1383_; uint8_t v_isSharedCheck_1410_; 
v_a_1380_ = lean_ctor_get(v___x_1379_, 0);
v_isSharedCheck_1410_ = !lean_is_exclusive(v___x_1379_);
if (v_isSharedCheck_1410_ == 0)
{
v___x_1382_ = v___x_1379_;
v_isShared_1383_ = v_isSharedCheck_1410_;
goto v_resetjp_1381_;
}
else
{
lean_inc(v_a_1380_);
lean_dec(v___x_1379_);
v___x_1382_ = lean_box(0);
v_isShared_1383_ = v_isSharedCheck_1410_;
goto v_resetjp_1381_;
}
v_resetjp_1381_:
{
lean_object* v_fieldInst_x3f_1384_; 
v_fieldInst_x3f_1384_ = lean_ctor_get(v_a_1380_, 6);
lean_inc(v_fieldInst_x3f_1384_);
lean_dec(v_a_1380_);
if (lean_obj_tag(v_fieldInst_x3f_1384_) == 0)
{
uint8_t v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1388_; 
lean_dec(v_a_1377_);
lean_dec_ref(v_a_1376_);
lean_dec(v_a_1375_);
lean_dec_ref(v_a_1374_);
lean_dec(v_a_1373_);
lean_dec_ref(v_a_1372_);
lean_dec(v_a_1371_);
lean_dec_ref(v_a_1370_);
lean_dec(v_a_1369_);
lean_dec(v_a_1368_);
lean_dec_ref(v_a_1367_);
v___x_1385_ = 0;
v___x_1386_ = lean_box(v___x_1385_);
if (v_isShared_1383_ == 0)
{
lean_ctor_set(v___x_1382_, 0, v___x_1386_);
v___x_1388_ = v___x_1382_;
goto v_reusejp_1387_;
}
else
{
lean_object* v_reuseFailAlloc_1389_; 
v_reuseFailAlloc_1389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1389_, 0, v___x_1386_);
v___x_1388_ = v_reuseFailAlloc_1389_;
goto v_reusejp_1387_;
}
v_reusejp_1387_:
{
return v___x_1388_;
}
}
else
{
lean_object* v___x_1390_; 
lean_dec_ref(v_fieldInst_x3f_1384_);
lean_del_object(v___x_1382_);
v___x_1390_ = l_Lean_Meta_Grind_Arith_CommRing_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0(v_a_1367_, v_a_1368_, v_a_1369_, v_a_1370_, v_a_1371_, v_a_1372_, v_a_1373_, v_a_1374_, v_a_1375_, v_a_1376_, v_a_1377_);
if (lean_obj_tag(v___x_1390_) == 0)
{
lean_object* v_a_1391_; lean_object* v___x_1393_; uint8_t v_isShared_1394_; uint8_t v_isSharedCheck_1401_; 
v_a_1391_ = lean_ctor_get(v___x_1390_, 0);
v_isSharedCheck_1401_ = !lean_is_exclusive(v___x_1390_);
if (v_isSharedCheck_1401_ == 0)
{
v___x_1393_ = v___x_1390_;
v_isShared_1394_ = v_isSharedCheck_1401_;
goto v_resetjp_1392_;
}
else
{
lean_inc(v_a_1391_);
lean_dec(v___x_1390_);
v___x_1393_ = lean_box(0);
v_isShared_1394_ = v_isSharedCheck_1401_;
goto v_resetjp_1392_;
}
v_resetjp_1392_:
{
lean_object* v___x_1395_; uint8_t v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1399_; 
v___x_1395_ = l_Lean_Expr_appArg_x21(v_a_1391_);
lean_dec(v_a_1391_);
v___x_1396_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v___x_1395_, v_inst_1366_);
lean_dec_ref(v___x_1395_);
v___x_1397_ = lean_box(v___x_1396_);
if (v_isShared_1394_ == 0)
{
lean_ctor_set(v___x_1393_, 0, v___x_1397_);
v___x_1399_ = v___x_1393_;
goto v_reusejp_1398_;
}
else
{
lean_object* v_reuseFailAlloc_1400_; 
v_reuseFailAlloc_1400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1400_, 0, v___x_1397_);
v___x_1399_ = v_reuseFailAlloc_1400_;
goto v_reusejp_1398_;
}
v_reusejp_1398_:
{
return v___x_1399_;
}
}
}
else
{
lean_object* v_a_1402_; lean_object* v___x_1404_; uint8_t v_isShared_1405_; uint8_t v_isSharedCheck_1409_; 
v_a_1402_ = lean_ctor_get(v___x_1390_, 0);
v_isSharedCheck_1409_ = !lean_is_exclusive(v___x_1390_);
if (v_isSharedCheck_1409_ == 0)
{
v___x_1404_ = v___x_1390_;
v_isShared_1405_ = v_isSharedCheck_1409_;
goto v_resetjp_1403_;
}
else
{
lean_inc(v_a_1402_);
lean_dec(v___x_1390_);
v___x_1404_ = lean_box(0);
v_isShared_1405_ = v_isSharedCheck_1409_;
goto v_resetjp_1403_;
}
v_resetjp_1403_:
{
lean_object* v___x_1407_; 
if (v_isShared_1405_ == 0)
{
v___x_1407_ = v___x_1404_;
goto v_reusejp_1406_;
}
else
{
lean_object* v_reuseFailAlloc_1408_; 
v_reuseFailAlloc_1408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1408_, 0, v_a_1402_);
v___x_1407_ = v_reuseFailAlloc_1408_;
goto v_reusejp_1406_;
}
v_reusejp_1406_:
{
return v___x_1407_;
}
}
}
}
}
}
else
{
lean_object* v_a_1411_; lean_object* v___x_1413_; uint8_t v_isShared_1414_; uint8_t v_isSharedCheck_1418_; 
lean_dec(v_a_1377_);
lean_dec_ref(v_a_1376_);
lean_dec(v_a_1375_);
lean_dec_ref(v_a_1374_);
lean_dec(v_a_1373_);
lean_dec_ref(v_a_1372_);
lean_dec(v_a_1371_);
lean_dec_ref(v_a_1370_);
lean_dec(v_a_1369_);
lean_dec(v_a_1368_);
lean_dec_ref(v_a_1367_);
v_a_1411_ = lean_ctor_get(v___x_1379_, 0);
v_isSharedCheck_1418_ = !lean_is_exclusive(v___x_1379_);
if (v_isSharedCheck_1418_ == 0)
{
v___x_1413_ = v___x_1379_;
v_isShared_1414_ = v_isSharedCheck_1418_;
goto v_resetjp_1412_;
}
else
{
lean_inc(v_a_1411_);
lean_dec(v___x_1379_);
v___x_1413_ = lean_box(0);
v_isShared_1414_ = v_isSharedCheck_1418_;
goto v_resetjp_1412_;
}
v_resetjp_1412_:
{
lean_object* v___x_1416_; 
if (v_isShared_1414_ == 0)
{
v___x_1416_ = v___x_1413_;
goto v_reusejp_1415_;
}
else
{
lean_object* v_reuseFailAlloc_1417_; 
v_reuseFailAlloc_1417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1417_, 0, v_a_1411_);
v___x_1416_ = v_reuseFailAlloc_1417_;
goto v_reusejp_1415_;
}
v_reusejp_1415_:
{
return v___x_1416_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst___boxed(lean_object* v_inst_1419_, lean_object* v_a_1420_, lean_object* v_a_1421_, lean_object* v_a_1422_, lean_object* v_a_1423_, lean_object* v_a_1424_, lean_object* v_a_1425_, lean_object* v_a_1426_, lean_object* v_a_1427_, lean_object* v_a_1428_, lean_object* v_a_1429_, lean_object* v_a_1430_, lean_object* v_a_1431_){
_start:
{
lean_object* v_res_1432_; 
v_res_1432_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst(v_inst_1419_, v_a_1420_, v_a_1421_, v_a_1422_, v_a_1423_, v_a_1424_, v_a_1425_, v_a_1426_, v_a_1427_, v_a_1428_, v_a_1429_, v_a_1430_);
lean_dec_ref(v_inst_1419_);
return v_res_1432_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__2(lean_object* v_a_1433_){
_start:
{
lean_object* v___x_1434_; 
v___x_1434_ = lean_nat_to_int(v_a_1433_);
return v___x_1434_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0_spec__2_spec__6___redArg(lean_object* v_x_1435_, lean_object* v_x_1436_, lean_object* v_x_1437_, lean_object* v_x_1438_){
_start:
{
lean_object* v_ks_1439_; lean_object* v_vs_1440_; lean_object* v___x_1442_; uint8_t v_isShared_1443_; uint8_t v_isSharedCheck_1464_; 
v_ks_1439_ = lean_ctor_get(v_x_1435_, 0);
v_vs_1440_ = lean_ctor_get(v_x_1435_, 1);
v_isSharedCheck_1464_ = !lean_is_exclusive(v_x_1435_);
if (v_isSharedCheck_1464_ == 0)
{
v___x_1442_ = v_x_1435_;
v_isShared_1443_ = v_isSharedCheck_1464_;
goto v_resetjp_1441_;
}
else
{
lean_inc(v_vs_1440_);
lean_inc(v_ks_1439_);
lean_dec(v_x_1435_);
v___x_1442_ = lean_box(0);
v_isShared_1443_ = v_isSharedCheck_1464_;
goto v_resetjp_1441_;
}
v_resetjp_1441_:
{
lean_object* v___x_1444_; uint8_t v___x_1445_; 
v___x_1444_ = lean_array_get_size(v_ks_1439_);
v___x_1445_ = lean_nat_dec_lt(v_x_1436_, v___x_1444_);
if (v___x_1445_ == 0)
{
lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1449_; 
lean_dec(v_x_1436_);
v___x_1446_ = lean_array_push(v_ks_1439_, v_x_1437_);
v___x_1447_ = lean_array_push(v_vs_1440_, v_x_1438_);
if (v_isShared_1443_ == 0)
{
lean_ctor_set(v___x_1442_, 1, v___x_1447_);
lean_ctor_set(v___x_1442_, 0, v___x_1446_);
v___x_1449_ = v___x_1442_;
goto v_reusejp_1448_;
}
else
{
lean_object* v_reuseFailAlloc_1450_; 
v_reuseFailAlloc_1450_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1450_, 0, v___x_1446_);
lean_ctor_set(v_reuseFailAlloc_1450_, 1, v___x_1447_);
v___x_1449_ = v_reuseFailAlloc_1450_;
goto v_reusejp_1448_;
}
v_reusejp_1448_:
{
return v___x_1449_;
}
}
else
{
lean_object* v_k_x27_1451_; uint8_t v___x_1452_; 
v_k_x27_1451_ = lean_array_fget_borrowed(v_ks_1439_, v_x_1436_);
v___x_1452_ = lean_expr_eqv(v_x_1437_, v_k_x27_1451_);
if (v___x_1452_ == 0)
{
lean_object* v___x_1454_; 
if (v_isShared_1443_ == 0)
{
v___x_1454_ = v___x_1442_;
goto v_reusejp_1453_;
}
else
{
lean_object* v_reuseFailAlloc_1458_; 
v_reuseFailAlloc_1458_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1458_, 0, v_ks_1439_);
lean_ctor_set(v_reuseFailAlloc_1458_, 1, v_vs_1440_);
v___x_1454_ = v_reuseFailAlloc_1458_;
goto v_reusejp_1453_;
}
v_reusejp_1453_:
{
lean_object* v___x_1455_; lean_object* v___x_1456_; 
v___x_1455_ = lean_unsigned_to_nat(1u);
v___x_1456_ = lean_nat_add(v_x_1436_, v___x_1455_);
lean_dec(v_x_1436_);
v_x_1435_ = v___x_1454_;
v_x_1436_ = v___x_1456_;
goto _start;
}
}
else
{
lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1462_; 
v___x_1459_ = lean_array_fset(v_ks_1439_, v_x_1436_, v_x_1437_);
v___x_1460_ = lean_array_fset(v_vs_1440_, v_x_1436_, v_x_1438_);
lean_dec(v_x_1436_);
if (v_isShared_1443_ == 0)
{
lean_ctor_set(v___x_1442_, 1, v___x_1460_);
lean_ctor_set(v___x_1442_, 0, v___x_1459_);
v___x_1462_ = v___x_1442_;
goto v_reusejp_1461_;
}
else
{
lean_object* v_reuseFailAlloc_1463_; 
v_reuseFailAlloc_1463_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1463_, 0, v___x_1459_);
lean_ctor_set(v_reuseFailAlloc_1463_, 1, v___x_1460_);
v___x_1462_ = v_reuseFailAlloc_1463_;
goto v_reusejp_1461_;
}
v_reusejp_1461_:
{
return v___x_1462_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0_spec__2___redArg(lean_object* v_n_1465_, lean_object* v_k_1466_, lean_object* v_v_1467_){
_start:
{
lean_object* v___x_1468_; lean_object* v___x_1469_; 
v___x_1468_ = lean_unsigned_to_nat(0u);
v___x_1469_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0_spec__2_spec__6___redArg(v_n_1465_, v___x_1468_, v_k_1466_, v_v_1467_);
return v___x_1469_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg___closed__0(void){
_start:
{
size_t v___x_1470_; size_t v___x_1471_; size_t v___x_1472_; 
v___x_1470_ = ((size_t)5ULL);
v___x_1471_ = ((size_t)1ULL);
v___x_1472_ = lean_usize_shift_left(v___x_1471_, v___x_1470_);
return v___x_1472_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_1473_; size_t v___x_1474_; size_t v___x_1475_; 
v___x_1473_ = ((size_t)1ULL);
v___x_1474_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg___closed__0);
v___x_1475_ = lean_usize_sub(v___x_1474_, v___x_1473_);
return v___x_1475_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_1476_; 
v___x_1476_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1476_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg(lean_object* v_x_1477_, size_t v_x_1478_, size_t v_x_1479_, lean_object* v_x_1480_, lean_object* v_x_1481_){
_start:
{
if (lean_obj_tag(v_x_1477_) == 0)
{
lean_object* v_es_1482_; size_t v___x_1483_; size_t v___x_1484_; size_t v___x_1485_; size_t v___x_1486_; lean_object* v_j_1487_; lean_object* v___x_1488_; uint8_t v___x_1489_; 
v_es_1482_ = lean_ctor_get(v_x_1477_, 0);
v___x_1483_ = ((size_t)5ULL);
v___x_1484_ = ((size_t)1ULL);
v___x_1485_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg___closed__1);
v___x_1486_ = lean_usize_land(v_x_1478_, v___x_1485_);
v_j_1487_ = lean_usize_to_nat(v___x_1486_);
v___x_1488_ = lean_array_get_size(v_es_1482_);
v___x_1489_ = lean_nat_dec_lt(v_j_1487_, v___x_1488_);
if (v___x_1489_ == 0)
{
lean_dec(v_j_1487_);
lean_dec(v_x_1481_);
lean_dec_ref(v_x_1480_);
return v_x_1477_;
}
else
{
lean_object* v___x_1491_; uint8_t v_isShared_1492_; uint8_t v_isSharedCheck_1526_; 
lean_inc_ref(v_es_1482_);
v_isSharedCheck_1526_ = !lean_is_exclusive(v_x_1477_);
if (v_isSharedCheck_1526_ == 0)
{
lean_object* v_unused_1527_; 
v_unused_1527_ = lean_ctor_get(v_x_1477_, 0);
lean_dec(v_unused_1527_);
v___x_1491_ = v_x_1477_;
v_isShared_1492_ = v_isSharedCheck_1526_;
goto v_resetjp_1490_;
}
else
{
lean_dec(v_x_1477_);
v___x_1491_ = lean_box(0);
v_isShared_1492_ = v_isSharedCheck_1526_;
goto v_resetjp_1490_;
}
v_resetjp_1490_:
{
lean_object* v_v_1493_; lean_object* v___x_1494_; lean_object* v_xs_x27_1495_; lean_object* v___y_1497_; 
v_v_1493_ = lean_array_fget(v_es_1482_, v_j_1487_);
v___x_1494_ = lean_box(0);
v_xs_x27_1495_ = lean_array_fset(v_es_1482_, v_j_1487_, v___x_1494_);
switch(lean_obj_tag(v_v_1493_))
{
case 0:
{
lean_object* v_key_1502_; lean_object* v_val_1503_; lean_object* v___x_1505_; uint8_t v_isShared_1506_; uint8_t v_isSharedCheck_1513_; 
v_key_1502_ = lean_ctor_get(v_v_1493_, 0);
v_val_1503_ = lean_ctor_get(v_v_1493_, 1);
v_isSharedCheck_1513_ = !lean_is_exclusive(v_v_1493_);
if (v_isSharedCheck_1513_ == 0)
{
v___x_1505_ = v_v_1493_;
v_isShared_1506_ = v_isSharedCheck_1513_;
goto v_resetjp_1504_;
}
else
{
lean_inc(v_val_1503_);
lean_inc(v_key_1502_);
lean_dec(v_v_1493_);
v___x_1505_ = lean_box(0);
v_isShared_1506_ = v_isSharedCheck_1513_;
goto v_resetjp_1504_;
}
v_resetjp_1504_:
{
uint8_t v___x_1507_; 
v___x_1507_ = lean_expr_eqv(v_x_1480_, v_key_1502_);
if (v___x_1507_ == 0)
{
lean_object* v___x_1508_; lean_object* v___x_1509_; 
lean_del_object(v___x_1505_);
v___x_1508_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1502_, v_val_1503_, v_x_1480_, v_x_1481_);
v___x_1509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1509_, 0, v___x_1508_);
v___y_1497_ = v___x_1509_;
goto v___jp_1496_;
}
else
{
lean_object* v___x_1511_; 
lean_dec(v_val_1503_);
lean_dec(v_key_1502_);
if (v_isShared_1506_ == 0)
{
lean_ctor_set(v___x_1505_, 1, v_x_1481_);
lean_ctor_set(v___x_1505_, 0, v_x_1480_);
v___x_1511_ = v___x_1505_;
goto v_reusejp_1510_;
}
else
{
lean_object* v_reuseFailAlloc_1512_; 
v_reuseFailAlloc_1512_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1512_, 0, v_x_1480_);
lean_ctor_set(v_reuseFailAlloc_1512_, 1, v_x_1481_);
v___x_1511_ = v_reuseFailAlloc_1512_;
goto v_reusejp_1510_;
}
v_reusejp_1510_:
{
v___y_1497_ = v___x_1511_;
goto v___jp_1496_;
}
}
}
}
case 1:
{
lean_object* v_node_1514_; lean_object* v___x_1516_; uint8_t v_isShared_1517_; uint8_t v_isSharedCheck_1524_; 
v_node_1514_ = lean_ctor_get(v_v_1493_, 0);
v_isSharedCheck_1524_ = !lean_is_exclusive(v_v_1493_);
if (v_isSharedCheck_1524_ == 0)
{
v___x_1516_ = v_v_1493_;
v_isShared_1517_ = v_isSharedCheck_1524_;
goto v_resetjp_1515_;
}
else
{
lean_inc(v_node_1514_);
lean_dec(v_v_1493_);
v___x_1516_ = lean_box(0);
v_isShared_1517_ = v_isSharedCheck_1524_;
goto v_resetjp_1515_;
}
v_resetjp_1515_:
{
size_t v___x_1518_; size_t v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1522_; 
v___x_1518_ = lean_usize_shift_right(v_x_1478_, v___x_1483_);
v___x_1519_ = lean_usize_add(v_x_1479_, v___x_1484_);
v___x_1520_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg(v_node_1514_, v___x_1518_, v___x_1519_, v_x_1480_, v_x_1481_);
if (v_isShared_1517_ == 0)
{
lean_ctor_set(v___x_1516_, 0, v___x_1520_);
v___x_1522_ = v___x_1516_;
goto v_reusejp_1521_;
}
else
{
lean_object* v_reuseFailAlloc_1523_; 
v_reuseFailAlloc_1523_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1523_, 0, v___x_1520_);
v___x_1522_ = v_reuseFailAlloc_1523_;
goto v_reusejp_1521_;
}
v_reusejp_1521_:
{
v___y_1497_ = v___x_1522_;
goto v___jp_1496_;
}
}
}
default: 
{
lean_object* v___x_1525_; 
v___x_1525_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1525_, 0, v_x_1480_);
lean_ctor_set(v___x_1525_, 1, v_x_1481_);
v___y_1497_ = v___x_1525_;
goto v___jp_1496_;
}
}
v___jp_1496_:
{
lean_object* v___x_1498_; lean_object* v___x_1500_; 
v___x_1498_ = lean_array_fset(v_xs_x27_1495_, v_j_1487_, v___y_1497_);
lean_dec(v_j_1487_);
if (v_isShared_1492_ == 0)
{
lean_ctor_set(v___x_1491_, 0, v___x_1498_);
v___x_1500_ = v___x_1491_;
goto v_reusejp_1499_;
}
else
{
lean_object* v_reuseFailAlloc_1501_; 
v_reuseFailAlloc_1501_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1501_, 0, v___x_1498_);
v___x_1500_ = v_reuseFailAlloc_1501_;
goto v_reusejp_1499_;
}
v_reusejp_1499_:
{
return v___x_1500_;
}
}
}
}
}
else
{
lean_object* v_ks_1528_; lean_object* v_vs_1529_; lean_object* v___x_1531_; uint8_t v_isShared_1532_; uint8_t v_isSharedCheck_1549_; 
v_ks_1528_ = lean_ctor_get(v_x_1477_, 0);
v_vs_1529_ = lean_ctor_get(v_x_1477_, 1);
v_isSharedCheck_1549_ = !lean_is_exclusive(v_x_1477_);
if (v_isSharedCheck_1549_ == 0)
{
v___x_1531_ = v_x_1477_;
v_isShared_1532_ = v_isSharedCheck_1549_;
goto v_resetjp_1530_;
}
else
{
lean_inc(v_vs_1529_);
lean_inc(v_ks_1528_);
lean_dec(v_x_1477_);
v___x_1531_ = lean_box(0);
v_isShared_1532_ = v_isSharedCheck_1549_;
goto v_resetjp_1530_;
}
v_resetjp_1530_:
{
lean_object* v___x_1534_; 
if (v_isShared_1532_ == 0)
{
v___x_1534_ = v___x_1531_;
goto v_reusejp_1533_;
}
else
{
lean_object* v_reuseFailAlloc_1548_; 
v_reuseFailAlloc_1548_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1548_, 0, v_ks_1528_);
lean_ctor_set(v_reuseFailAlloc_1548_, 1, v_vs_1529_);
v___x_1534_ = v_reuseFailAlloc_1548_;
goto v_reusejp_1533_;
}
v_reusejp_1533_:
{
lean_object* v_newNode_1535_; uint8_t v___y_1537_; size_t v___x_1543_; uint8_t v___x_1544_; 
v_newNode_1535_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0_spec__2___redArg(v___x_1534_, v_x_1480_, v_x_1481_);
v___x_1543_ = ((size_t)7ULL);
v___x_1544_ = lean_usize_dec_le(v___x_1543_, v_x_1479_);
if (v___x_1544_ == 0)
{
lean_object* v___x_1545_; lean_object* v___x_1546_; uint8_t v___x_1547_; 
v___x_1545_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1535_);
v___x_1546_ = lean_unsigned_to_nat(4u);
v___x_1547_ = lean_nat_dec_lt(v___x_1545_, v___x_1546_);
lean_dec(v___x_1545_);
v___y_1537_ = v___x_1547_;
goto v___jp_1536_;
}
else
{
v___y_1537_ = v___x_1544_;
goto v___jp_1536_;
}
v___jp_1536_:
{
if (v___y_1537_ == 0)
{
lean_object* v_ks_1538_; lean_object* v_vs_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; 
v_ks_1538_ = lean_ctor_get(v_newNode_1535_, 0);
lean_inc_ref(v_ks_1538_);
v_vs_1539_ = lean_ctor_get(v_newNode_1535_, 1);
lean_inc_ref(v_vs_1539_);
lean_dec_ref(v_newNode_1535_);
v___x_1540_ = lean_unsigned_to_nat(0u);
v___x_1541_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg___closed__2);
v___x_1542_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0_spec__3___redArg(v_x_1479_, v_ks_1538_, v_vs_1539_, v___x_1540_, v___x_1541_);
lean_dec_ref(v_vs_1539_);
lean_dec_ref(v_ks_1538_);
return v___x_1542_;
}
else
{
return v_newNode_1535_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0_spec__3___redArg(size_t v_depth_1550_, lean_object* v_keys_1551_, lean_object* v_vals_1552_, lean_object* v_i_1553_, lean_object* v_entries_1554_){
_start:
{
lean_object* v___x_1555_; uint8_t v___x_1556_; 
v___x_1555_ = lean_array_get_size(v_keys_1551_);
v___x_1556_ = lean_nat_dec_lt(v_i_1553_, v___x_1555_);
if (v___x_1556_ == 0)
{
lean_dec(v_i_1553_);
return v_entries_1554_;
}
else
{
lean_object* v_k_1557_; lean_object* v_v_1558_; uint64_t v___x_1559_; size_t v_h_1560_; size_t v___x_1561_; lean_object* v___x_1562_; size_t v___x_1563_; size_t v___x_1564_; size_t v___x_1565_; size_t v_h_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; 
v_k_1557_ = lean_array_fget_borrowed(v_keys_1551_, v_i_1553_);
v_v_1558_ = lean_array_fget_borrowed(v_vals_1552_, v_i_1553_);
v___x_1559_ = l_Lean_Expr_hash(v_k_1557_);
v_h_1560_ = lean_uint64_to_usize(v___x_1559_);
v___x_1561_ = ((size_t)5ULL);
v___x_1562_ = lean_unsigned_to_nat(1u);
v___x_1563_ = ((size_t)1ULL);
v___x_1564_ = lean_usize_sub(v_depth_1550_, v___x_1563_);
v___x_1565_ = lean_usize_mul(v___x_1561_, v___x_1564_);
v_h_1566_ = lean_usize_shift_right(v_h_1560_, v___x_1565_);
v___x_1567_ = lean_nat_add(v_i_1553_, v___x_1562_);
lean_dec(v_i_1553_);
lean_inc(v_v_1558_);
lean_inc(v_k_1557_);
v___x_1568_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg(v_entries_1554_, v_h_1566_, v_depth_1550_, v_k_1557_, v_v_1558_);
v_i_1553_ = v___x_1567_;
v_entries_1554_ = v___x_1568_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_depth_1570_, lean_object* v_keys_1571_, lean_object* v_vals_1572_, lean_object* v_i_1573_, lean_object* v_entries_1574_){
_start:
{
size_t v_depth_boxed_1575_; lean_object* v_res_1576_; 
v_depth_boxed_1575_ = lean_unbox_usize(v_depth_1570_);
lean_dec(v_depth_1570_);
v_res_1576_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0_spec__3___redArg(v_depth_boxed_1575_, v_keys_1571_, v_vals_1572_, v_i_1573_, v_entries_1574_);
lean_dec_ref(v_vals_1572_);
lean_dec_ref(v_keys_1571_);
return v_res_1576_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg___boxed(lean_object* v_x_1577_, lean_object* v_x_1578_, lean_object* v_x_1579_, lean_object* v_x_1580_, lean_object* v_x_1581_){
_start:
{
size_t v_x_140378__boxed_1582_; size_t v_x_140379__boxed_1583_; lean_object* v_res_1584_; 
v_x_140378__boxed_1582_ = lean_unbox_usize(v_x_1578_);
lean_dec(v_x_1578_);
v_x_140379__boxed_1583_ = lean_unbox_usize(v_x_1579_);
lean_dec(v_x_1579_);
v_res_1584_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg(v_x_1577_, v_x_140378__boxed_1582_, v_x_140379__boxed_1583_, v_x_1580_, v_x_1581_);
return v_res_1584_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0___redArg(lean_object* v_x_1585_, lean_object* v_x_1586_, lean_object* v_x_1587_){
_start:
{
uint64_t v___x_1588_; size_t v___x_1589_; size_t v___x_1590_; lean_object* v___x_1591_; 
v___x_1588_ = l_Lean_Expr_hash(v_x_1586_);
v___x_1589_ = lean_uint64_to_usize(v___x_1588_);
v___x_1590_ = ((size_t)1ULL);
v___x_1591_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg(v_x_1585_, v___x_1589_, v___x_1590_, v_x_1586_, v_x_1587_);
return v___x_1591_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___lam__0(lean_object* v_a_1592_, lean_object* v_s_1593_){
_start:
{
lean_object* v_toRing_1594_; lean_object* v_invFn_x3f_1595_; lean_object* v_semiringId_x3f_1596_; lean_object* v_commSemiringInst_1597_; lean_object* v_commRingInst_1598_; lean_object* v_noZeroDivInst_x3f_1599_; lean_object* v_fieldInst_x3f_1600_; lean_object* v_denoteEntries_1601_; lean_object* v_nextId_1602_; lean_object* v_steps_1603_; lean_object* v_queue_1604_; lean_object* v_basis_1605_; lean_object* v_diseqs_1606_; uint8_t v_recheck_1607_; lean_object* v_invSet_1608_; lean_object* v_numEq0_x3f_1609_; uint8_t v_numEq0Updated_1610_; lean_object* v___x_1612_; uint8_t v_isShared_1613_; uint8_t v_isSharedCheck_1619_; 
v_toRing_1594_ = lean_ctor_get(v_s_1593_, 0);
v_invFn_x3f_1595_ = lean_ctor_get(v_s_1593_, 1);
v_semiringId_x3f_1596_ = lean_ctor_get(v_s_1593_, 2);
v_commSemiringInst_1597_ = lean_ctor_get(v_s_1593_, 3);
v_commRingInst_1598_ = lean_ctor_get(v_s_1593_, 4);
v_noZeroDivInst_x3f_1599_ = lean_ctor_get(v_s_1593_, 5);
v_fieldInst_x3f_1600_ = lean_ctor_get(v_s_1593_, 6);
v_denoteEntries_1601_ = lean_ctor_get(v_s_1593_, 7);
v_nextId_1602_ = lean_ctor_get(v_s_1593_, 8);
v_steps_1603_ = lean_ctor_get(v_s_1593_, 9);
v_queue_1604_ = lean_ctor_get(v_s_1593_, 10);
v_basis_1605_ = lean_ctor_get(v_s_1593_, 11);
v_diseqs_1606_ = lean_ctor_get(v_s_1593_, 12);
v_recheck_1607_ = lean_ctor_get_uint8(v_s_1593_, sizeof(void*)*15);
v_invSet_1608_ = lean_ctor_get(v_s_1593_, 13);
v_numEq0_x3f_1609_ = lean_ctor_get(v_s_1593_, 14);
v_numEq0Updated_1610_ = lean_ctor_get_uint8(v_s_1593_, sizeof(void*)*15 + 1);
v_isSharedCheck_1619_ = !lean_is_exclusive(v_s_1593_);
if (v_isSharedCheck_1619_ == 0)
{
v___x_1612_ = v_s_1593_;
v_isShared_1613_ = v_isSharedCheck_1619_;
goto v_resetjp_1611_;
}
else
{
lean_inc(v_numEq0_x3f_1609_);
lean_inc(v_invSet_1608_);
lean_inc(v_diseqs_1606_);
lean_inc(v_basis_1605_);
lean_inc(v_queue_1604_);
lean_inc(v_steps_1603_);
lean_inc(v_nextId_1602_);
lean_inc(v_denoteEntries_1601_);
lean_inc(v_fieldInst_x3f_1600_);
lean_inc(v_noZeroDivInst_x3f_1599_);
lean_inc(v_commRingInst_1598_);
lean_inc(v_commSemiringInst_1597_);
lean_inc(v_semiringId_x3f_1596_);
lean_inc(v_invFn_x3f_1595_);
lean_inc(v_toRing_1594_);
lean_dec(v_s_1593_);
v___x_1612_ = lean_box(0);
v_isShared_1613_ = v_isSharedCheck_1619_;
goto v_resetjp_1611_;
}
v_resetjp_1611_:
{
lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1617_; 
v___x_1614_ = lean_box(0);
v___x_1615_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0___redArg(v_invSet_1608_, v_a_1592_, v___x_1614_);
if (v_isShared_1613_ == 0)
{
lean_ctor_set(v___x_1612_, 13, v___x_1615_);
v___x_1617_ = v___x_1612_;
goto v_reusejp_1616_;
}
else
{
lean_object* v_reuseFailAlloc_1618_; 
v_reuseFailAlloc_1618_ = lean_alloc_ctor(0, 15, 2);
lean_ctor_set(v_reuseFailAlloc_1618_, 0, v_toRing_1594_);
lean_ctor_set(v_reuseFailAlloc_1618_, 1, v_invFn_x3f_1595_);
lean_ctor_set(v_reuseFailAlloc_1618_, 2, v_semiringId_x3f_1596_);
lean_ctor_set(v_reuseFailAlloc_1618_, 3, v_commSemiringInst_1597_);
lean_ctor_set(v_reuseFailAlloc_1618_, 4, v_commRingInst_1598_);
lean_ctor_set(v_reuseFailAlloc_1618_, 5, v_noZeroDivInst_x3f_1599_);
lean_ctor_set(v_reuseFailAlloc_1618_, 6, v_fieldInst_x3f_1600_);
lean_ctor_set(v_reuseFailAlloc_1618_, 7, v_denoteEntries_1601_);
lean_ctor_set(v_reuseFailAlloc_1618_, 8, v_nextId_1602_);
lean_ctor_set(v_reuseFailAlloc_1618_, 9, v_steps_1603_);
lean_ctor_set(v_reuseFailAlloc_1618_, 10, v_queue_1604_);
lean_ctor_set(v_reuseFailAlloc_1618_, 11, v_basis_1605_);
lean_ctor_set(v_reuseFailAlloc_1618_, 12, v_diseqs_1606_);
lean_ctor_set(v_reuseFailAlloc_1618_, 13, v___x_1615_);
lean_ctor_set(v_reuseFailAlloc_1618_, 14, v_numEq0_x3f_1609_);
lean_ctor_set_uint8(v_reuseFailAlloc_1618_, sizeof(void*)*15, v_recheck_1607_);
lean_ctor_set_uint8(v_reuseFailAlloc_1618_, sizeof(void*)*15 + 1, v_numEq0Updated_1610_);
v___x_1617_ = v_reuseFailAlloc_1618_;
goto v_reusejp_1616_;
}
v_reusejp_1616_:
{
return v___x_1617_;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__4___closed__1(void){
_start:
{
lean_object* v___x_1622_; lean_object* v___x_1623_; 
v___x_1622_ = lean_unsigned_to_nat(0u);
v___x_1623_ = lean_nat_to_int(v___x_1622_);
return v___x_1623_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__4(lean_object* v_k_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_){
_start:
{
lean_object* v___x_1642_; 
v___x_1642_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_, v___y_1637_, v___y_1638_, v___y_1639_, v___y_1640_);
if (lean_obj_tag(v___x_1642_) == 0)
{
lean_object* v_a_1643_; lean_object* v_toRing_1644_; lean_object* v_type_1645_; lean_object* v_u_1646_; lean_object* v_semiringInst_1647_; lean_object* v___x_1648_; lean_object* v_n_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; 
v_a_1643_ = lean_ctor_get(v___x_1642_, 0);
lean_inc(v_a_1643_);
lean_dec_ref(v___x_1642_);
v_toRing_1644_ = lean_ctor_get(v_a_1643_, 0);
lean_inc_ref(v_toRing_1644_);
lean_dec(v_a_1643_);
v_type_1645_ = lean_ctor_get(v_toRing_1644_, 1);
lean_inc_ref(v_type_1645_);
v_u_1646_ = lean_ctor_get(v_toRing_1644_, 2);
lean_inc(v_u_1646_);
v_semiringInst_1647_ = lean_ctor_get(v_toRing_1644_, 4);
lean_inc_ref(v_semiringInst_1647_);
lean_dec_ref(v_toRing_1644_);
v___x_1648_ = lean_nat_abs(v_k_1629_);
v_n_1649_ = l_Lean_mkRawNatLit(v___x_1648_);
v___x_1650_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__4___closed__0));
v___x_1651_ = lean_box(0);
v___x_1652_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1652_, 0, v_u_1646_);
lean_ctor_set(v___x_1652_, 1, v___x_1651_);
lean_inc_ref(v___x_1652_);
v___x_1653_ = l_Lean_mkConst(v___x_1650_, v___x_1652_);
lean_inc_ref(v_n_1649_);
lean_inc_ref(v_type_1645_);
v___x_1654_ = l_Lean_mkAppB(v___x_1653_, v_type_1645_, v_n_1649_);
v___x_1655_ = lean_box(0);
lean_inc(v___y_1640_);
lean_inc_ref(v___y_1639_);
lean_inc(v___y_1638_);
lean_inc_ref(v___y_1637_);
v___x_1656_ = l_Lean_Meta_synthInstance_x3f(v___x_1654_, v___x_1655_, v___y_1637_, v___y_1638_, v___y_1639_, v___y_1640_);
if (lean_obj_tag(v___x_1656_) == 0)
{
lean_object* v_a_1657_; lean_object* v___x_1659_; uint8_t v_isShared_1660_; uint8_t v_isSharedCheck_1696_; 
v_a_1657_ = lean_ctor_get(v___x_1656_, 0);
v_isSharedCheck_1696_ = !lean_is_exclusive(v___x_1656_);
if (v_isSharedCheck_1696_ == 0)
{
v___x_1659_ = v___x_1656_;
v_isShared_1660_ = v_isSharedCheck_1696_;
goto v_resetjp_1658_;
}
else
{
lean_inc(v_a_1657_);
lean_dec(v___x_1656_);
v___x_1659_ = lean_box(0);
v_isShared_1660_ = v_isSharedCheck_1696_;
goto v_resetjp_1658_;
}
v_resetjp_1658_:
{
lean_object* v_ofNatInst_1662_; lean_object* v___y_1663_; lean_object* v___y_1664_; lean_object* v___y_1665_; lean_object* v___y_1666_; lean_object* v___y_1667_; lean_object* v___y_1668_; lean_object* v___y_1669_; lean_object* v___y_1670_; lean_object* v___y_1671_; lean_object* v___y_1672_; lean_object* v___y_1673_; 
if (lean_obj_tag(v_a_1657_) == 1)
{
lean_object* v_val_1692_; 
lean_dec_ref(v_semiringInst_1647_);
v_val_1692_ = lean_ctor_get(v_a_1657_, 0);
lean_inc(v_val_1692_);
lean_dec_ref(v_a_1657_);
v_ofNatInst_1662_ = v_val_1692_;
v___y_1663_ = v___y_1630_;
v___y_1664_ = v___y_1631_;
v___y_1665_ = v___y_1632_;
v___y_1666_ = v___y_1633_;
v___y_1667_ = v___y_1634_;
v___y_1668_ = v___y_1635_;
v___y_1669_ = v___y_1636_;
v___y_1670_ = v___y_1637_;
v___y_1671_ = v___y_1638_;
v___y_1672_ = v___y_1639_;
v___y_1673_ = v___y_1640_;
goto v___jp_1661_;
}
else
{
lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; 
lean_dec(v_a_1657_);
v___x_1693_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__4___closed__2));
lean_inc_ref(v___x_1652_);
v___x_1694_ = l_Lean_mkConst(v___x_1693_, v___x_1652_);
lean_inc_ref(v_n_1649_);
lean_inc_ref(v_type_1645_);
v___x_1695_ = l_Lean_mkApp3(v___x_1694_, v_type_1645_, v_semiringInst_1647_, v_n_1649_);
v_ofNatInst_1662_ = v___x_1695_;
v___y_1663_ = v___y_1630_;
v___y_1664_ = v___y_1631_;
v___y_1665_ = v___y_1632_;
v___y_1666_ = v___y_1633_;
v___y_1667_ = v___y_1634_;
v___y_1668_ = v___y_1635_;
v___y_1669_ = v___y_1636_;
v___y_1670_ = v___y_1637_;
v___y_1671_ = v___y_1638_;
v___y_1672_ = v___y_1639_;
v___y_1673_ = v___y_1640_;
goto v___jp_1661_;
}
v___jp_1661_:
{
lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v_n_1676_; lean_object* v___x_1677_; uint8_t v___x_1678_; 
v___x_1674_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__8));
v___x_1675_ = l_Lean_mkConst(v___x_1674_, v___x_1652_);
v_n_1676_ = l_Lean_mkApp3(v___x_1675_, v_type_1645_, v_n_1649_, v_ofNatInst_1662_);
v___x_1677_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__4___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__4___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__4___closed__1);
v___x_1678_ = lean_int_dec_lt(v_k_1629_, v___x_1677_);
if (v___x_1678_ == 0)
{
lean_object* v___x_1680_; 
lean_dec(v___y_1673_);
lean_dec_ref(v___y_1672_);
lean_dec(v___y_1671_);
lean_dec_ref(v___y_1670_);
lean_dec(v___y_1669_);
lean_dec_ref(v___y_1668_);
lean_dec(v___y_1667_);
lean_dec_ref(v___y_1666_);
lean_dec(v___y_1665_);
lean_dec(v___y_1664_);
lean_dec_ref(v___y_1663_);
if (v_isShared_1660_ == 0)
{
lean_ctor_set(v___x_1659_, 0, v_n_1676_);
v___x_1680_ = v___x_1659_;
goto v_reusejp_1679_;
}
else
{
lean_object* v_reuseFailAlloc_1681_; 
v_reuseFailAlloc_1681_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1681_, 0, v_n_1676_);
v___x_1680_ = v_reuseFailAlloc_1681_;
goto v_reusejp_1679_;
}
v_reusejp_1679_:
{
return v___x_1680_;
}
}
else
{
lean_object* v___x_1682_; 
lean_del_object(v___x_1659_);
v___x_1682_ = l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0(v___y_1663_, v___y_1664_, v___y_1665_, v___y_1666_, v___y_1667_, v___y_1668_, v___y_1669_, v___y_1670_, v___y_1671_, v___y_1672_, v___y_1673_);
if (lean_obj_tag(v___x_1682_) == 0)
{
lean_object* v_a_1683_; lean_object* v___x_1685_; uint8_t v_isShared_1686_; uint8_t v_isSharedCheck_1691_; 
v_a_1683_ = lean_ctor_get(v___x_1682_, 0);
v_isSharedCheck_1691_ = !lean_is_exclusive(v___x_1682_);
if (v_isSharedCheck_1691_ == 0)
{
v___x_1685_ = v___x_1682_;
v_isShared_1686_ = v_isSharedCheck_1691_;
goto v_resetjp_1684_;
}
else
{
lean_inc(v_a_1683_);
lean_dec(v___x_1682_);
v___x_1685_ = lean_box(0);
v_isShared_1686_ = v_isSharedCheck_1691_;
goto v_resetjp_1684_;
}
v_resetjp_1684_:
{
lean_object* v___x_1687_; lean_object* v___x_1689_; 
v___x_1687_ = l_Lean_Expr_app___override(v_a_1683_, v_n_1676_);
if (v_isShared_1686_ == 0)
{
lean_ctor_set(v___x_1685_, 0, v___x_1687_);
v___x_1689_ = v___x_1685_;
goto v_reusejp_1688_;
}
else
{
lean_object* v_reuseFailAlloc_1690_; 
v_reuseFailAlloc_1690_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1690_, 0, v___x_1687_);
v___x_1689_ = v_reuseFailAlloc_1690_;
goto v_reusejp_1688_;
}
v_reusejp_1688_:
{
return v___x_1689_;
}
}
}
else
{
lean_dec_ref(v_n_1676_);
return v___x_1682_;
}
}
}
}
}
else
{
lean_object* v_a_1697_; lean_object* v___x_1699_; uint8_t v_isShared_1700_; uint8_t v_isSharedCheck_1704_; 
lean_dec_ref(v___x_1652_);
lean_dec_ref(v_n_1649_);
lean_dec_ref(v_semiringInst_1647_);
lean_dec_ref(v_type_1645_);
lean_dec(v___y_1640_);
lean_dec_ref(v___y_1639_);
lean_dec(v___y_1638_);
lean_dec_ref(v___y_1637_);
lean_dec(v___y_1636_);
lean_dec_ref(v___y_1635_);
lean_dec(v___y_1634_);
lean_dec_ref(v___y_1633_);
lean_dec(v___y_1632_);
lean_dec(v___y_1631_);
lean_dec_ref(v___y_1630_);
v_a_1697_ = lean_ctor_get(v___x_1656_, 0);
v_isSharedCheck_1704_ = !lean_is_exclusive(v___x_1656_);
if (v_isSharedCheck_1704_ == 0)
{
v___x_1699_ = v___x_1656_;
v_isShared_1700_ = v_isSharedCheck_1704_;
goto v_resetjp_1698_;
}
else
{
lean_inc(v_a_1697_);
lean_dec(v___x_1656_);
v___x_1699_ = lean_box(0);
v_isShared_1700_ = v_isSharedCheck_1704_;
goto v_resetjp_1698_;
}
v_resetjp_1698_:
{
lean_object* v___x_1702_; 
if (v_isShared_1700_ == 0)
{
v___x_1702_ = v___x_1699_;
goto v_reusejp_1701_;
}
else
{
lean_object* v_reuseFailAlloc_1703_; 
v_reuseFailAlloc_1703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1703_, 0, v_a_1697_);
v___x_1702_ = v_reuseFailAlloc_1703_;
goto v_reusejp_1701_;
}
v_reusejp_1701_:
{
return v___x_1702_;
}
}
}
}
else
{
lean_object* v_a_1705_; lean_object* v___x_1707_; uint8_t v_isShared_1708_; uint8_t v_isSharedCheck_1712_; 
lean_dec(v___y_1640_);
lean_dec_ref(v___y_1639_);
lean_dec(v___y_1638_);
lean_dec_ref(v___y_1637_);
lean_dec(v___y_1636_);
lean_dec_ref(v___y_1635_);
lean_dec(v___y_1634_);
lean_dec_ref(v___y_1633_);
lean_dec(v___y_1632_);
lean_dec(v___y_1631_);
lean_dec_ref(v___y_1630_);
v_a_1705_ = lean_ctor_get(v___x_1642_, 0);
v_isSharedCheck_1712_ = !lean_is_exclusive(v___x_1642_);
if (v_isSharedCheck_1712_ == 0)
{
v___x_1707_ = v___x_1642_;
v_isShared_1708_ = v_isSharedCheck_1712_;
goto v_resetjp_1706_;
}
else
{
lean_inc(v_a_1705_);
lean_dec(v___x_1642_);
v___x_1707_ = lean_box(0);
v_isShared_1708_ = v_isSharedCheck_1712_;
goto v_resetjp_1706_;
}
v_resetjp_1706_:
{
lean_object* v___x_1710_; 
if (v_isShared_1708_ == 0)
{
v___x_1710_ = v___x_1707_;
goto v_reusejp_1709_;
}
else
{
lean_object* v_reuseFailAlloc_1711_; 
v_reuseFailAlloc_1711_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1711_, 0, v_a_1705_);
v___x_1710_ = v_reuseFailAlloc_1711_;
goto v_reusejp_1709_;
}
v_reusejp_1709_:
{
return v___x_1710_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__4___boxed(lean_object* v_k_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_){
_start:
{
lean_object* v_res_1726_; 
v_res_1726_ = l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__4(v_k_1713_, v___y_1714_, v___y_1715_, v___y_1716_, v___y_1717_, v___y_1718_, v___y_1719_, v___y_1720_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_);
lean_dec(v_k_1713_);
return v_res_1726_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1_spec__2_spec__6___redArg(lean_object* v_keys_1727_, lean_object* v_i_1728_, lean_object* v_k_1729_){
_start:
{
lean_object* v___x_1730_; uint8_t v___x_1731_; 
v___x_1730_ = lean_array_get_size(v_keys_1727_);
v___x_1731_ = lean_nat_dec_lt(v_i_1728_, v___x_1730_);
if (v___x_1731_ == 0)
{
lean_dec(v_i_1728_);
return v___x_1731_;
}
else
{
lean_object* v_k_x27_1732_; uint8_t v___x_1733_; 
v_k_x27_1732_ = lean_array_fget_borrowed(v_keys_1727_, v_i_1728_);
v___x_1733_ = lean_expr_eqv(v_k_1729_, v_k_x27_1732_);
if (v___x_1733_ == 0)
{
lean_object* v___x_1734_; lean_object* v___x_1735_; 
v___x_1734_ = lean_unsigned_to_nat(1u);
v___x_1735_ = lean_nat_add(v_i_1728_, v___x_1734_);
lean_dec(v_i_1728_);
v_i_1728_ = v___x_1735_;
goto _start;
}
else
{
lean_dec(v_i_1728_);
return v___x_1733_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1_spec__2_spec__6___redArg___boxed(lean_object* v_keys_1737_, lean_object* v_i_1738_, lean_object* v_k_1739_){
_start:
{
uint8_t v_res_1740_; lean_object* v_r_1741_; 
v_res_1740_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1_spec__2_spec__6___redArg(v_keys_1737_, v_i_1738_, v_k_1739_);
lean_dec_ref(v_k_1739_);
lean_dec_ref(v_keys_1737_);
v_r_1741_ = lean_box(v_res_1740_);
return v_r_1741_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1_spec__2___redArg(lean_object* v_x_1742_, size_t v_x_1743_, lean_object* v_x_1744_){
_start:
{
if (lean_obj_tag(v_x_1742_) == 0)
{
lean_object* v_es_1745_; lean_object* v___x_1746_; size_t v___x_1747_; size_t v___x_1748_; size_t v___x_1749_; lean_object* v_j_1750_; lean_object* v___x_1751_; 
v_es_1745_ = lean_ctor_get(v_x_1742_, 0);
lean_inc_ref(v_es_1745_);
lean_dec_ref(v_x_1742_);
v___x_1746_ = lean_box(2);
v___x_1747_ = ((size_t)5ULL);
v___x_1748_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg___closed__1);
v___x_1749_ = lean_usize_land(v_x_1743_, v___x_1748_);
v_j_1750_ = lean_usize_to_nat(v___x_1749_);
v___x_1751_ = lean_array_get(v___x_1746_, v_es_1745_, v_j_1750_);
lean_dec(v_j_1750_);
lean_dec_ref(v_es_1745_);
switch(lean_obj_tag(v___x_1751_))
{
case 0:
{
lean_object* v_key_1752_; uint8_t v___x_1753_; 
v_key_1752_ = lean_ctor_get(v___x_1751_, 0);
lean_inc(v_key_1752_);
lean_dec_ref(v___x_1751_);
v___x_1753_ = lean_expr_eqv(v_x_1744_, v_key_1752_);
lean_dec(v_key_1752_);
return v___x_1753_;
}
case 1:
{
lean_object* v_node_1754_; size_t v___x_1755_; 
v_node_1754_ = lean_ctor_get(v___x_1751_, 0);
lean_inc(v_node_1754_);
lean_dec_ref(v___x_1751_);
v___x_1755_ = lean_usize_shift_right(v_x_1743_, v___x_1747_);
v_x_1742_ = v_node_1754_;
v_x_1743_ = v___x_1755_;
goto _start;
}
default: 
{
uint8_t v___x_1757_; 
v___x_1757_ = 0;
return v___x_1757_;
}
}
}
else
{
lean_object* v_ks_1758_; lean_object* v___x_1759_; uint8_t v___x_1760_; 
v_ks_1758_ = lean_ctor_get(v_x_1742_, 0);
lean_inc_ref(v_ks_1758_);
lean_dec_ref(v_x_1742_);
v___x_1759_ = lean_unsigned_to_nat(0u);
v___x_1760_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1_spec__2_spec__6___redArg(v_ks_1758_, v___x_1759_, v_x_1744_);
lean_dec_ref(v_ks_1758_);
return v___x_1760_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1_spec__2___redArg___boxed(lean_object* v_x_1761_, lean_object* v_x_1762_, lean_object* v_x_1763_){
_start:
{
size_t v_x_140791__boxed_1764_; uint8_t v_res_1765_; lean_object* v_r_1766_; 
v_x_140791__boxed_1764_ = lean_unbox_usize(v_x_1762_);
lean_dec(v_x_1762_);
v_res_1765_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1_spec__2___redArg(v_x_1761_, v_x_140791__boxed_1764_, v_x_1763_);
lean_dec_ref(v_x_1763_);
v_r_1766_ = lean_box(v_res_1765_);
return v_r_1766_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1___redArg(lean_object* v_x_1767_, lean_object* v_x_1768_){
_start:
{
uint64_t v___x_1769_; size_t v___x_1770_; uint8_t v___x_1771_; 
v___x_1769_ = l_Lean_Expr_hash(v_x_1768_);
v___x_1770_ = lean_uint64_to_usize(v___x_1769_);
v___x_1771_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1_spec__2___redArg(v_x_1767_, v___x_1770_, v_x_1768_);
return v___x_1771_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1___redArg___boxed(lean_object* v_x_1772_, lean_object* v_x_1773_){
_start:
{
uint8_t v_res_1774_; lean_object* v_r_1775_; 
v_res_1774_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1___redArg(v_x_1772_, v_x_1773_);
lean_dec_ref(v_x_1773_);
v_r_1775_ = lean_box(v_res_1774_);
return v_r_1775_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__3___lam__0(lean_object* v_a_1776_, lean_object* v_s_1777_){
_start:
{
lean_object* v_toRing_1778_; lean_object* v_invFn_x3f_1779_; lean_object* v_semiringId_x3f_1780_; lean_object* v_commSemiringInst_1781_; lean_object* v_commRingInst_1782_; lean_object* v_noZeroDivInst_x3f_1783_; lean_object* v_fieldInst_x3f_1784_; lean_object* v_denoteEntries_1785_; lean_object* v_nextId_1786_; lean_object* v_steps_1787_; lean_object* v_queue_1788_; lean_object* v_basis_1789_; lean_object* v_diseqs_1790_; uint8_t v_recheck_1791_; lean_object* v_invSet_1792_; lean_object* v_numEq0_x3f_1793_; uint8_t v_numEq0Updated_1794_; lean_object* v___x_1796_; uint8_t v_isShared_1797_; uint8_t v_isSharedCheck_1826_; 
v_toRing_1778_ = lean_ctor_get(v_s_1777_, 0);
v_invFn_x3f_1779_ = lean_ctor_get(v_s_1777_, 1);
v_semiringId_x3f_1780_ = lean_ctor_get(v_s_1777_, 2);
v_commSemiringInst_1781_ = lean_ctor_get(v_s_1777_, 3);
v_commRingInst_1782_ = lean_ctor_get(v_s_1777_, 4);
v_noZeroDivInst_x3f_1783_ = lean_ctor_get(v_s_1777_, 5);
v_fieldInst_x3f_1784_ = lean_ctor_get(v_s_1777_, 6);
v_denoteEntries_1785_ = lean_ctor_get(v_s_1777_, 7);
v_nextId_1786_ = lean_ctor_get(v_s_1777_, 8);
v_steps_1787_ = lean_ctor_get(v_s_1777_, 9);
v_queue_1788_ = lean_ctor_get(v_s_1777_, 10);
v_basis_1789_ = lean_ctor_get(v_s_1777_, 11);
v_diseqs_1790_ = lean_ctor_get(v_s_1777_, 12);
v_recheck_1791_ = lean_ctor_get_uint8(v_s_1777_, sizeof(void*)*15);
v_invSet_1792_ = lean_ctor_get(v_s_1777_, 13);
v_numEq0_x3f_1793_ = lean_ctor_get(v_s_1777_, 14);
v_numEq0Updated_1794_ = lean_ctor_get_uint8(v_s_1777_, sizeof(void*)*15 + 1);
v_isSharedCheck_1826_ = !lean_is_exclusive(v_s_1777_);
if (v_isSharedCheck_1826_ == 0)
{
v___x_1796_ = v_s_1777_;
v_isShared_1797_ = v_isSharedCheck_1826_;
goto v_resetjp_1795_;
}
else
{
lean_inc(v_numEq0_x3f_1793_);
lean_inc(v_invSet_1792_);
lean_inc(v_diseqs_1790_);
lean_inc(v_basis_1789_);
lean_inc(v_queue_1788_);
lean_inc(v_steps_1787_);
lean_inc(v_nextId_1786_);
lean_inc(v_denoteEntries_1785_);
lean_inc(v_fieldInst_x3f_1784_);
lean_inc(v_noZeroDivInst_x3f_1783_);
lean_inc(v_commRingInst_1782_);
lean_inc(v_commSemiringInst_1781_);
lean_inc(v_semiringId_x3f_1780_);
lean_inc(v_invFn_x3f_1779_);
lean_inc(v_toRing_1778_);
lean_dec(v_s_1777_);
v___x_1796_ = lean_box(0);
v_isShared_1797_ = v_isSharedCheck_1826_;
goto v_resetjp_1795_;
}
v_resetjp_1795_:
{
lean_object* v_id_1798_; lean_object* v_type_1799_; lean_object* v_u_1800_; lean_object* v_ringInst_1801_; lean_object* v_semiringInst_1802_; lean_object* v_charInst_x3f_1803_; lean_object* v_addFn_x3f_1804_; lean_object* v_subFn_x3f_1805_; lean_object* v_negFn_x3f_1806_; lean_object* v_powFn_x3f_1807_; lean_object* v_intCastFn_x3f_1808_; lean_object* v_natCastFn_x3f_1809_; lean_object* v_one_x3f_1810_; lean_object* v_vars_1811_; lean_object* v_varMap_1812_; lean_object* v_denote_1813_; lean_object* v___x_1815_; uint8_t v_isShared_1816_; uint8_t v_isSharedCheck_1824_; 
v_id_1798_ = lean_ctor_get(v_toRing_1778_, 0);
v_type_1799_ = lean_ctor_get(v_toRing_1778_, 1);
v_u_1800_ = lean_ctor_get(v_toRing_1778_, 2);
v_ringInst_1801_ = lean_ctor_get(v_toRing_1778_, 3);
v_semiringInst_1802_ = lean_ctor_get(v_toRing_1778_, 4);
v_charInst_x3f_1803_ = lean_ctor_get(v_toRing_1778_, 5);
v_addFn_x3f_1804_ = lean_ctor_get(v_toRing_1778_, 6);
v_subFn_x3f_1805_ = lean_ctor_get(v_toRing_1778_, 8);
v_negFn_x3f_1806_ = lean_ctor_get(v_toRing_1778_, 9);
v_powFn_x3f_1807_ = lean_ctor_get(v_toRing_1778_, 10);
v_intCastFn_x3f_1808_ = lean_ctor_get(v_toRing_1778_, 11);
v_natCastFn_x3f_1809_ = lean_ctor_get(v_toRing_1778_, 12);
v_one_x3f_1810_ = lean_ctor_get(v_toRing_1778_, 13);
v_vars_1811_ = lean_ctor_get(v_toRing_1778_, 14);
v_varMap_1812_ = lean_ctor_get(v_toRing_1778_, 15);
v_denote_1813_ = lean_ctor_get(v_toRing_1778_, 16);
v_isSharedCheck_1824_ = !lean_is_exclusive(v_toRing_1778_);
if (v_isSharedCheck_1824_ == 0)
{
lean_object* v_unused_1825_; 
v_unused_1825_ = lean_ctor_get(v_toRing_1778_, 7);
lean_dec(v_unused_1825_);
v___x_1815_ = v_toRing_1778_;
v_isShared_1816_ = v_isSharedCheck_1824_;
goto v_resetjp_1814_;
}
else
{
lean_inc(v_denote_1813_);
lean_inc(v_varMap_1812_);
lean_inc(v_vars_1811_);
lean_inc(v_one_x3f_1810_);
lean_inc(v_natCastFn_x3f_1809_);
lean_inc(v_intCastFn_x3f_1808_);
lean_inc(v_powFn_x3f_1807_);
lean_inc(v_negFn_x3f_1806_);
lean_inc(v_subFn_x3f_1805_);
lean_inc(v_addFn_x3f_1804_);
lean_inc(v_charInst_x3f_1803_);
lean_inc(v_semiringInst_1802_);
lean_inc(v_ringInst_1801_);
lean_inc(v_u_1800_);
lean_inc(v_type_1799_);
lean_inc(v_id_1798_);
lean_dec(v_toRing_1778_);
v___x_1815_ = lean_box(0);
v_isShared_1816_ = v_isSharedCheck_1824_;
goto v_resetjp_1814_;
}
v_resetjp_1814_:
{
lean_object* v___x_1817_; lean_object* v___x_1819_; 
v___x_1817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1817_, 0, v_a_1776_);
if (v_isShared_1816_ == 0)
{
lean_ctor_set(v___x_1815_, 7, v___x_1817_);
v___x_1819_ = v___x_1815_;
goto v_reusejp_1818_;
}
else
{
lean_object* v_reuseFailAlloc_1823_; 
v_reuseFailAlloc_1823_ = lean_alloc_ctor(0, 17, 0);
lean_ctor_set(v_reuseFailAlloc_1823_, 0, v_id_1798_);
lean_ctor_set(v_reuseFailAlloc_1823_, 1, v_type_1799_);
lean_ctor_set(v_reuseFailAlloc_1823_, 2, v_u_1800_);
lean_ctor_set(v_reuseFailAlloc_1823_, 3, v_ringInst_1801_);
lean_ctor_set(v_reuseFailAlloc_1823_, 4, v_semiringInst_1802_);
lean_ctor_set(v_reuseFailAlloc_1823_, 5, v_charInst_x3f_1803_);
lean_ctor_set(v_reuseFailAlloc_1823_, 6, v_addFn_x3f_1804_);
lean_ctor_set(v_reuseFailAlloc_1823_, 7, v___x_1817_);
lean_ctor_set(v_reuseFailAlloc_1823_, 8, v_subFn_x3f_1805_);
lean_ctor_set(v_reuseFailAlloc_1823_, 9, v_negFn_x3f_1806_);
lean_ctor_set(v_reuseFailAlloc_1823_, 10, v_powFn_x3f_1807_);
lean_ctor_set(v_reuseFailAlloc_1823_, 11, v_intCastFn_x3f_1808_);
lean_ctor_set(v_reuseFailAlloc_1823_, 12, v_natCastFn_x3f_1809_);
lean_ctor_set(v_reuseFailAlloc_1823_, 13, v_one_x3f_1810_);
lean_ctor_set(v_reuseFailAlloc_1823_, 14, v_vars_1811_);
lean_ctor_set(v_reuseFailAlloc_1823_, 15, v_varMap_1812_);
lean_ctor_set(v_reuseFailAlloc_1823_, 16, v_denote_1813_);
v___x_1819_ = v_reuseFailAlloc_1823_;
goto v_reusejp_1818_;
}
v_reusejp_1818_:
{
lean_object* v___x_1821_; 
if (v_isShared_1797_ == 0)
{
lean_ctor_set(v___x_1796_, 0, v___x_1819_);
v___x_1821_ = v___x_1796_;
goto v_reusejp_1820_;
}
else
{
lean_object* v_reuseFailAlloc_1822_; 
v_reuseFailAlloc_1822_ = lean_alloc_ctor(0, 15, 2);
lean_ctor_set(v_reuseFailAlloc_1822_, 0, v___x_1819_);
lean_ctor_set(v_reuseFailAlloc_1822_, 1, v_invFn_x3f_1779_);
lean_ctor_set(v_reuseFailAlloc_1822_, 2, v_semiringId_x3f_1780_);
lean_ctor_set(v_reuseFailAlloc_1822_, 3, v_commSemiringInst_1781_);
lean_ctor_set(v_reuseFailAlloc_1822_, 4, v_commRingInst_1782_);
lean_ctor_set(v_reuseFailAlloc_1822_, 5, v_noZeroDivInst_x3f_1783_);
lean_ctor_set(v_reuseFailAlloc_1822_, 6, v_fieldInst_x3f_1784_);
lean_ctor_set(v_reuseFailAlloc_1822_, 7, v_denoteEntries_1785_);
lean_ctor_set(v_reuseFailAlloc_1822_, 8, v_nextId_1786_);
lean_ctor_set(v_reuseFailAlloc_1822_, 9, v_steps_1787_);
lean_ctor_set(v_reuseFailAlloc_1822_, 10, v_queue_1788_);
lean_ctor_set(v_reuseFailAlloc_1822_, 11, v_basis_1789_);
lean_ctor_set(v_reuseFailAlloc_1822_, 12, v_diseqs_1790_);
lean_ctor_set(v_reuseFailAlloc_1822_, 13, v_invSet_1792_);
lean_ctor_set(v_reuseFailAlloc_1822_, 14, v_numEq0_x3f_1793_);
lean_ctor_set_uint8(v_reuseFailAlloc_1822_, sizeof(void*)*15, v_recheck_1791_);
lean_ctor_set_uint8(v_reuseFailAlloc_1822_, sizeof(void*)*15 + 1, v_numEq0Updated_1794_);
v___x_1821_ = v_reuseFailAlloc_1822_;
goto v_reusejp_1820_;
}
v_reusejp_1820_:
{
return v___x_1821_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__3_spec__5(lean_object* v_type_1827_, lean_object* v_u_1828_, lean_object* v_instDeclName_1829_, lean_object* v_declName_1830_, lean_object* v_expectedInst_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_){
_start:
{
lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; 
v___x_1844_ = lean_box(0);
lean_inc(v_u_1828_);
v___x_1845_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1845_, 0, v_u_1828_);
lean_ctor_set(v___x_1845_, 1, v___x_1844_);
lean_inc(v_u_1828_);
v___x_1846_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1846_, 0, v_u_1828_);
lean_ctor_set(v___x_1846_, 1, v___x_1845_);
v___x_1847_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1847_, 0, v_u_1828_);
lean_ctor_set(v___x_1847_, 1, v___x_1846_);
lean_inc_ref(v___x_1847_);
v___x_1848_ = l_Lean_mkConst(v_instDeclName_1829_, v___x_1847_);
lean_inc_ref_n(v_type_1827_, 3);
v___x_1849_ = l_Lean_mkApp3(v___x_1848_, v_type_1827_, v_type_1827_, v_type_1827_);
lean_inc(v___y_1842_);
lean_inc_ref(v___y_1841_);
lean_inc(v___y_1840_);
lean_inc_ref(v___y_1839_);
v___x_1850_ = l_Lean_Meta_Grind_Arith_CommRing_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1_spec__5(v___x_1849_, v___y_1832_, v___y_1833_, v___y_1834_, v___y_1835_, v___y_1836_, v___y_1837_, v___y_1838_, v___y_1839_, v___y_1840_, v___y_1841_, v___y_1842_);
if (lean_obj_tag(v___x_1850_) == 0)
{
lean_object* v_a_1851_; lean_object* v___x_1852_; 
v_a_1851_ = lean_ctor_get(v___x_1850_, 0);
lean_inc(v_a_1851_);
lean_dec_ref(v___x_1850_);
lean_inc(v___y_1842_);
lean_inc_ref(v___y_1841_);
lean_inc(v___y_1840_);
lean_inc_ref(v___y_1839_);
lean_inc(v_a_1851_);
lean_inc(v_declName_1830_);
v___x_1852_ = l_Lean_Meta_Grind_Arith_CommRing_checkInst(v_declName_1830_, v_a_1851_, v_expectedInst_1831_, v___y_1839_, v___y_1840_, v___y_1841_, v___y_1842_);
if (lean_obj_tag(v___x_1852_) == 0)
{
lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; 
lean_dec_ref(v___x_1852_);
v___x_1853_ = l_Lean_mkConst(v_declName_1830_, v___x_1847_);
lean_inc_ref_n(v_type_1827_, 2);
v___x_1854_ = l_Lean_mkApp4(v___x_1853_, v_type_1827_, v_type_1827_, v_type_1827_, v_a_1851_);
lean_inc(v___y_1838_);
v___x_1855_ = lean_grind_canon(v___x_1854_, v___y_1833_, v___y_1834_, v___y_1835_, v___y_1836_, v___y_1837_, v___y_1838_, v___y_1839_, v___y_1840_, v___y_1841_, v___y_1842_);
if (lean_obj_tag(v___x_1855_) == 0)
{
lean_object* v_a_1856_; lean_object* v___x_1857_; 
v_a_1856_ = lean_ctor_get(v___x_1855_, 0);
lean_inc(v_a_1856_);
lean_dec_ref(v___x_1855_);
v___x_1857_ = l_Lean_Meta_Sym_shareCommon___redArg(v_a_1856_, v___y_1838_);
lean_dec(v___y_1838_);
return v___x_1857_;
}
else
{
lean_dec(v___y_1838_);
return v___x_1855_;
}
}
else
{
lean_object* v_a_1858_; lean_object* v___x_1860_; uint8_t v_isShared_1861_; uint8_t v_isSharedCheck_1865_; 
lean_dec(v_a_1851_);
lean_dec_ref(v___x_1847_);
lean_dec(v___y_1842_);
lean_dec_ref(v___y_1841_);
lean_dec(v___y_1840_);
lean_dec_ref(v___y_1839_);
lean_dec(v___y_1838_);
lean_dec_ref(v___y_1837_);
lean_dec(v___y_1836_);
lean_dec_ref(v___y_1835_);
lean_dec(v___y_1834_);
lean_dec(v___y_1833_);
lean_dec(v_declName_1830_);
lean_dec_ref(v_type_1827_);
v_a_1858_ = lean_ctor_get(v___x_1852_, 0);
v_isSharedCheck_1865_ = !lean_is_exclusive(v___x_1852_);
if (v_isSharedCheck_1865_ == 0)
{
v___x_1860_ = v___x_1852_;
v_isShared_1861_ = v_isSharedCheck_1865_;
goto v_resetjp_1859_;
}
else
{
lean_inc(v_a_1858_);
lean_dec(v___x_1852_);
v___x_1860_ = lean_box(0);
v_isShared_1861_ = v_isSharedCheck_1865_;
goto v_resetjp_1859_;
}
v_resetjp_1859_:
{
lean_object* v___x_1863_; 
if (v_isShared_1861_ == 0)
{
v___x_1863_ = v___x_1860_;
goto v_reusejp_1862_;
}
else
{
lean_object* v_reuseFailAlloc_1864_; 
v_reuseFailAlloc_1864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1864_, 0, v_a_1858_);
v___x_1863_ = v_reuseFailAlloc_1864_;
goto v_reusejp_1862_;
}
v_reusejp_1862_:
{
return v___x_1863_;
}
}
}
}
else
{
lean_dec_ref(v___x_1847_);
lean_dec(v___y_1842_);
lean_dec_ref(v___y_1841_);
lean_dec(v___y_1840_);
lean_dec_ref(v___y_1839_);
lean_dec(v___y_1838_);
lean_dec_ref(v___y_1837_);
lean_dec(v___y_1836_);
lean_dec_ref(v___y_1835_);
lean_dec(v___y_1834_);
lean_dec(v___y_1833_);
lean_dec_ref(v_expectedInst_1831_);
lean_dec(v_declName_1830_);
lean_dec_ref(v_type_1827_);
return v___x_1850_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__3_spec__5___boxed(lean_object** _args){
lean_object* v_type_1866_ = _args[0];
lean_object* v_u_1867_ = _args[1];
lean_object* v_instDeclName_1868_ = _args[2];
lean_object* v_declName_1869_ = _args[3];
lean_object* v_expectedInst_1870_ = _args[4];
lean_object* v___y_1871_ = _args[5];
lean_object* v___y_1872_ = _args[6];
lean_object* v___y_1873_ = _args[7];
lean_object* v___y_1874_ = _args[8];
lean_object* v___y_1875_ = _args[9];
lean_object* v___y_1876_ = _args[10];
lean_object* v___y_1877_ = _args[11];
lean_object* v___y_1878_ = _args[12];
lean_object* v___y_1879_ = _args[13];
lean_object* v___y_1880_ = _args[14];
lean_object* v___y_1881_ = _args[15];
lean_object* v___y_1882_ = _args[16];
_start:
{
lean_object* v_res_1883_; 
v_res_1883_ = l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__3_spec__5(v_type_1866_, v_u_1867_, v_instDeclName_1868_, v_declName_1869_, v_expectedInst_1870_, v___y_1871_, v___y_1872_, v___y_1873_, v___y_1874_, v___y_1875_, v___y_1876_, v___y_1877_, v___y_1878_, v___y_1879_, v___y_1880_, v___y_1881_);
lean_dec_ref(v___y_1871_);
return v_res_1883_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__3(lean_object* v___y_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_){
_start:
{
lean_object* v___x_1907_; 
v___x_1907_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v___y_1895_, v___y_1896_, v___y_1897_, v___y_1898_, v___y_1899_, v___y_1900_, v___y_1901_, v___y_1902_, v___y_1903_, v___y_1904_, v___y_1905_);
if (lean_obj_tag(v___x_1907_) == 0)
{
lean_object* v_a_1908_; lean_object* v___x_1910_; uint8_t v_isShared_1911_; uint8_t v_isSharedCheck_1951_; 
v_a_1908_ = lean_ctor_get(v___x_1907_, 0);
v_isSharedCheck_1951_ = !lean_is_exclusive(v___x_1907_);
if (v_isSharedCheck_1951_ == 0)
{
v___x_1910_ = v___x_1907_;
v_isShared_1911_ = v_isSharedCheck_1951_;
goto v_resetjp_1909_;
}
else
{
lean_inc(v_a_1908_);
lean_dec(v___x_1907_);
v___x_1910_ = lean_box(0);
v_isShared_1911_ = v_isSharedCheck_1951_;
goto v_resetjp_1909_;
}
v_resetjp_1909_:
{
lean_object* v_toRing_1912_; lean_object* v_mulFn_x3f_1913_; 
v_toRing_1912_ = lean_ctor_get(v_a_1908_, 0);
lean_inc_ref(v_toRing_1912_);
lean_dec(v_a_1908_);
v_mulFn_x3f_1913_ = lean_ctor_get(v_toRing_1912_, 7);
if (lean_obj_tag(v_mulFn_x3f_1913_) == 1)
{
lean_object* v_val_1914_; lean_object* v___x_1916_; 
lean_inc_ref(v_mulFn_x3f_1913_);
lean_dec_ref(v_toRing_1912_);
lean_dec(v___y_1905_);
lean_dec_ref(v___y_1904_);
lean_dec(v___y_1903_);
lean_dec_ref(v___y_1902_);
lean_dec(v___y_1901_);
lean_dec_ref(v___y_1900_);
lean_dec(v___y_1899_);
lean_dec_ref(v___y_1898_);
lean_dec(v___y_1897_);
lean_dec(v___y_1896_);
lean_dec_ref(v___y_1895_);
v_val_1914_ = lean_ctor_get(v_mulFn_x3f_1913_, 0);
lean_inc(v_val_1914_);
lean_dec_ref(v_mulFn_x3f_1913_);
if (v_isShared_1911_ == 0)
{
lean_ctor_set(v___x_1910_, 0, v_val_1914_);
v___x_1916_ = v___x_1910_;
goto v_reusejp_1915_;
}
else
{
lean_object* v_reuseFailAlloc_1917_; 
v_reuseFailAlloc_1917_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1917_, 0, v_val_1914_);
v___x_1916_ = v_reuseFailAlloc_1917_;
goto v_reusejp_1915_;
}
v_reusejp_1915_:
{
return v___x_1916_;
}
}
else
{
lean_object* v_type_1918_; lean_object* v_u_1919_; lean_object* v_semiringInst_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v_expectedInst_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; 
lean_del_object(v___x_1910_);
v_type_1918_ = lean_ctor_get(v_toRing_1912_, 1);
lean_inc_ref(v_type_1918_);
v_u_1919_ = lean_ctor_get(v_toRing_1912_, 2);
lean_inc(v_u_1919_);
v_semiringInst_1920_ = lean_ctor_get(v_toRing_1912_, 4);
lean_inc_ref(v_semiringInst_1920_);
lean_dec_ref(v_toRing_1912_);
v___x_1921_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__3___closed__1));
v___x_1922_ = lean_box(0);
lean_inc(v_u_1919_);
v___x_1923_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1923_, 0, v_u_1919_);
lean_ctor_set(v___x_1923_, 1, v___x_1922_);
lean_inc_ref(v___x_1923_);
v___x_1924_ = l_Lean_mkConst(v___x_1921_, v___x_1923_);
v___x_1925_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__3___closed__3));
v___x_1926_ = l_Lean_mkConst(v___x_1925_, v___x_1923_);
lean_inc_ref(v_type_1918_);
v___x_1927_ = l_Lean_mkAppB(v___x_1926_, v_type_1918_, v_semiringInst_1920_);
lean_inc_ref(v_type_1918_);
v_expectedInst_1928_ = l_Lean_mkAppB(v___x_1924_, v_type_1918_, v___x_1927_);
v___x_1929_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__3___closed__4));
v___x_1930_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__20));
lean_inc(v___y_1896_);
v___x_1931_ = l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__3_spec__5(v_type_1918_, v_u_1919_, v___x_1929_, v___x_1930_, v_expectedInst_1928_, v___y_1895_, v___y_1896_, v___y_1897_, v___y_1898_, v___y_1899_, v___y_1900_, v___y_1901_, v___y_1902_, v___y_1903_, v___y_1904_, v___y_1905_);
if (lean_obj_tag(v___x_1931_) == 0)
{
lean_object* v_a_1932_; lean_object* v___f_1933_; lean_object* v___x_1934_; 
v_a_1932_ = lean_ctor_get(v___x_1931_, 0);
lean_inc(v_a_1932_);
lean_dec_ref(v___x_1931_);
lean_inc(v_a_1932_);
v___f_1933_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__3___lam__0), 2, 1);
lean_closure_set(v___f_1933_, 0, v_a_1932_);
v___x_1934_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(v___f_1933_, v___y_1895_, v___y_1896_);
lean_dec(v___y_1896_);
if (lean_obj_tag(v___x_1934_) == 0)
{
lean_object* v___x_1936_; uint8_t v_isShared_1937_; uint8_t v_isSharedCheck_1941_; 
v_isSharedCheck_1941_ = !lean_is_exclusive(v___x_1934_);
if (v_isSharedCheck_1941_ == 0)
{
lean_object* v_unused_1942_; 
v_unused_1942_ = lean_ctor_get(v___x_1934_, 0);
lean_dec(v_unused_1942_);
v___x_1936_ = v___x_1934_;
v_isShared_1937_ = v_isSharedCheck_1941_;
goto v_resetjp_1935_;
}
else
{
lean_dec(v___x_1934_);
v___x_1936_ = lean_box(0);
v_isShared_1937_ = v_isSharedCheck_1941_;
goto v_resetjp_1935_;
}
v_resetjp_1935_:
{
lean_object* v___x_1939_; 
if (v_isShared_1937_ == 0)
{
lean_ctor_set(v___x_1936_, 0, v_a_1932_);
v___x_1939_ = v___x_1936_;
goto v_reusejp_1938_;
}
else
{
lean_object* v_reuseFailAlloc_1940_; 
v_reuseFailAlloc_1940_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1940_, 0, v_a_1932_);
v___x_1939_ = v_reuseFailAlloc_1940_;
goto v_reusejp_1938_;
}
v_reusejp_1938_:
{
return v___x_1939_;
}
}
}
else
{
lean_object* v_a_1943_; lean_object* v___x_1945_; uint8_t v_isShared_1946_; uint8_t v_isSharedCheck_1950_; 
lean_dec(v_a_1932_);
v_a_1943_ = lean_ctor_get(v___x_1934_, 0);
v_isSharedCheck_1950_ = !lean_is_exclusive(v___x_1934_);
if (v_isSharedCheck_1950_ == 0)
{
v___x_1945_ = v___x_1934_;
v_isShared_1946_ = v_isSharedCheck_1950_;
goto v_resetjp_1944_;
}
else
{
lean_inc(v_a_1943_);
lean_dec(v___x_1934_);
v___x_1945_ = lean_box(0);
v_isShared_1946_ = v_isSharedCheck_1950_;
goto v_resetjp_1944_;
}
v_resetjp_1944_:
{
lean_object* v___x_1948_; 
if (v_isShared_1946_ == 0)
{
v___x_1948_ = v___x_1945_;
goto v_reusejp_1947_;
}
else
{
lean_object* v_reuseFailAlloc_1949_; 
v_reuseFailAlloc_1949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1949_, 0, v_a_1943_);
v___x_1948_ = v_reuseFailAlloc_1949_;
goto v_reusejp_1947_;
}
v_reusejp_1947_:
{
return v___x_1948_;
}
}
}
}
else
{
lean_dec(v___y_1896_);
lean_dec_ref(v___y_1895_);
return v___x_1931_;
}
}
}
}
else
{
lean_object* v_a_1952_; lean_object* v___x_1954_; uint8_t v_isShared_1955_; uint8_t v_isSharedCheck_1959_; 
lean_dec(v___y_1905_);
lean_dec_ref(v___y_1904_);
lean_dec(v___y_1903_);
lean_dec_ref(v___y_1902_);
lean_dec(v___y_1901_);
lean_dec_ref(v___y_1900_);
lean_dec(v___y_1899_);
lean_dec_ref(v___y_1898_);
lean_dec(v___y_1897_);
lean_dec(v___y_1896_);
lean_dec_ref(v___y_1895_);
v_a_1952_ = lean_ctor_get(v___x_1907_, 0);
v_isSharedCheck_1959_ = !lean_is_exclusive(v___x_1907_);
if (v_isSharedCheck_1959_ == 0)
{
v___x_1954_ = v___x_1907_;
v_isShared_1955_ = v_isSharedCheck_1959_;
goto v_resetjp_1953_;
}
else
{
lean_inc(v_a_1952_);
lean_dec(v___x_1907_);
v___x_1954_ = lean_box(0);
v_isShared_1955_ = v_isSharedCheck_1959_;
goto v_resetjp_1953_;
}
v_resetjp_1953_:
{
lean_object* v___x_1957_; 
if (v_isShared_1955_ == 0)
{
v___x_1957_ = v___x_1954_;
goto v_reusejp_1956_;
}
else
{
lean_object* v_reuseFailAlloc_1958_; 
v_reuseFailAlloc_1958_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1958_, 0, v_a_1952_);
v___x_1957_ = v_reuseFailAlloc_1958_;
goto v_reusejp_1956_;
}
v_reusejp_1956_:
{
return v___x_1957_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__3___boxed(lean_object* v___y_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_){
_start:
{
lean_object* v_res_1972_; 
v_res_1972_ = l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__3(v___y_1960_, v___y_1961_, v___y_1962_, v___y_1963_, v___y_1964_, v___y_1965_, v___y_1966_, v___y_1967_, v___y_1968_, v___y_1969_, v___y_1970_);
return v_res_1972_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__3(void){
_start:
{
lean_object* v___x_1980_; lean_object* v___x_1981_; 
v___x_1980_ = lean_unsigned_to_nat(1u);
v___x_1981_ = lean_nat_to_int(v___x_1980_);
return v___x_1981_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv(lean_object* v_e_2006_, lean_object* v_inst_2007_, lean_object* v_a_2008_, lean_object* v_a_2009_, lean_object* v_a_2010_, lean_object* v_a_2011_, lean_object* v_a_2012_, lean_object* v_a_2013_, lean_object* v_a_2014_, lean_object* v_a_2015_, lean_object* v_a_2016_, lean_object* v_a_2017_, lean_object* v_a_2018_, lean_object* v_a_2019_){
_start:
{
lean_object* v___x_2024_; 
lean_inc(v_a_2019_);
lean_inc_ref(v_a_2018_);
lean_inc(v_a_2017_);
lean_inc_ref(v_a_2016_);
lean_inc(v_a_2015_);
lean_inc_ref(v_a_2014_);
lean_inc(v_a_2013_);
lean_inc_ref(v_a_2012_);
lean_inc(v_a_2011_);
lean_inc(v_a_2010_);
lean_inc_ref(v_a_2009_);
v___x_2024_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst(v_inst_2007_, v_a_2009_, v_a_2010_, v_a_2011_, v_a_2012_, v_a_2013_, v_a_2014_, v_a_2015_, v_a_2016_, v_a_2017_, v_a_2018_, v_a_2019_);
if (lean_obj_tag(v___x_2024_) == 0)
{
lean_object* v_a_2025_; lean_object* v___x_2027_; uint8_t v_isShared_2028_; uint8_t v_isSharedCheck_2284_; 
v_a_2025_ = lean_ctor_get(v___x_2024_, 0);
v_isSharedCheck_2284_ = !lean_is_exclusive(v___x_2024_);
if (v_isSharedCheck_2284_ == 0)
{
v___x_2027_ = v___x_2024_;
v_isShared_2028_ = v_isSharedCheck_2284_;
goto v_resetjp_2026_;
}
else
{
lean_inc(v_a_2025_);
lean_dec(v___x_2024_);
v___x_2027_ = lean_box(0);
v_isShared_2028_ = v_isSharedCheck_2284_;
goto v_resetjp_2026_;
}
v_resetjp_2026_:
{
uint8_t v___x_2029_; 
v___x_2029_ = lean_unbox(v_a_2025_);
lean_dec(v_a_2025_);
if (v___x_2029_ == 0)
{
lean_object* v___x_2030_; lean_object* v___x_2032_; 
lean_dec(v_a_2019_);
lean_dec_ref(v_a_2018_);
lean_dec(v_a_2017_);
lean_dec_ref(v_a_2016_);
lean_dec(v_a_2015_);
lean_dec_ref(v_a_2014_);
lean_dec(v_a_2013_);
lean_dec_ref(v_a_2012_);
lean_dec(v_a_2011_);
lean_dec(v_a_2010_);
lean_dec_ref(v_a_2009_);
lean_dec_ref(v_a_2008_);
lean_dec_ref(v_e_2006_);
v___x_2030_ = lean_box(0);
if (v_isShared_2028_ == 0)
{
lean_ctor_set(v___x_2027_, 0, v___x_2030_);
v___x_2032_ = v___x_2027_;
goto v_reusejp_2031_;
}
else
{
lean_object* v_reuseFailAlloc_2033_; 
v_reuseFailAlloc_2033_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2033_, 0, v___x_2030_);
v___x_2032_ = v_reuseFailAlloc_2033_;
goto v_reusejp_2031_;
}
v_reusejp_2031_:
{
return v___x_2032_;
}
}
else
{
lean_object* v___x_2034_; 
lean_del_object(v___x_2027_);
v___x_2034_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v_a_2009_, v_a_2010_, v_a_2011_, v_a_2012_, v_a_2013_, v_a_2014_, v_a_2015_, v_a_2016_, v_a_2017_, v_a_2018_, v_a_2019_);
if (lean_obj_tag(v___x_2034_) == 0)
{
lean_object* v_a_2035_; lean_object* v___x_2037_; uint8_t v_isShared_2038_; uint8_t v_isSharedCheck_2275_; 
v_a_2035_ = lean_ctor_get(v___x_2034_, 0);
v_isSharedCheck_2275_ = !lean_is_exclusive(v___x_2034_);
if (v_isSharedCheck_2275_ == 0)
{
v___x_2037_ = v___x_2034_;
v_isShared_2038_ = v_isSharedCheck_2275_;
goto v_resetjp_2036_;
}
else
{
lean_inc(v_a_2035_);
lean_dec(v___x_2034_);
v___x_2037_ = lean_box(0);
v_isShared_2038_ = v_isSharedCheck_2275_;
goto v_resetjp_2036_;
}
v_resetjp_2036_:
{
lean_object* v_fieldInst_x3f_2039_; 
v_fieldInst_x3f_2039_ = lean_ctor_get(v_a_2035_, 6);
lean_inc(v_fieldInst_x3f_2039_);
if (lean_obj_tag(v_fieldInst_x3f_2039_) == 1)
{
lean_object* v_toRing_2040_; lean_object* v_val_2041_; lean_object* v___y_2043_; lean_object* v___y_2044_; lean_object* v___y_2045_; lean_object* v___y_2046_; lean_object* v___y_2047_; lean_object* v___y_2048_; lean_object* v___y_2049_; lean_object* v___y_2050_; lean_object* v___y_2051_; lean_object* v___y_2052_; lean_object* v___x_2062_; 
lean_del_object(v___x_2037_);
v_toRing_2040_ = lean_ctor_get(v_a_2035_, 0);
lean_inc_ref(v_toRing_2040_);
lean_dec(v_a_2035_);
v_val_2041_ = lean_ctor_get(v_fieldInst_x3f_2039_, 0);
lean_inc(v_val_2041_);
lean_dec_ref(v_fieldInst_x3f_2039_);
v___x_2062_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v_a_2009_, v_a_2010_, v_a_2011_, v_a_2012_, v_a_2013_, v_a_2014_, v_a_2015_, v_a_2016_, v_a_2017_, v_a_2018_, v_a_2019_);
if (lean_obj_tag(v___x_2062_) == 0)
{
lean_object* v_a_2063_; lean_object* v___x_2065_; uint8_t v_isShared_2066_; uint8_t v_isSharedCheck_2262_; 
v_a_2063_ = lean_ctor_get(v___x_2062_, 0);
v_isSharedCheck_2262_ = !lean_is_exclusive(v___x_2062_);
if (v_isSharedCheck_2262_ == 0)
{
v___x_2065_ = v___x_2062_;
v_isShared_2066_ = v_isSharedCheck_2262_;
goto v_resetjp_2064_;
}
else
{
lean_inc(v_a_2063_);
lean_dec(v___x_2062_);
v___x_2065_ = lean_box(0);
v_isShared_2066_ = v_isSharedCheck_2262_;
goto v_resetjp_2064_;
}
v_resetjp_2064_:
{
lean_object* v_invSet_2067_; uint8_t v___x_2068_; 
v_invSet_2067_ = lean_ctor_get(v_a_2063_, 13);
lean_inc_ref(v_invSet_2067_);
lean_dec(v_a_2063_);
v___x_2068_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1___redArg(v_invSet_2067_, v_a_2008_);
if (v___x_2068_ == 0)
{
lean_object* v___f_2069_; lean_object* v___x_2070_; 
lean_del_object(v___x_2065_);
lean_inc_ref(v_a_2008_);
v___f_2069_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___lam__0), 2, 1);
lean_closure_set(v___f_2069_, 0, v_a_2008_);
lean_inc_ref(v_a_2009_);
v___x_2070_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(v___f_2069_, v_a_2009_, v_a_2010_);
if (lean_obj_tag(v___x_2070_) == 0)
{
lean_object* v___x_2071_; 
lean_dec_ref(v___x_2070_);
lean_inc(v_a_2019_);
lean_inc_ref(v_a_2018_);
lean_inc(v_a_2017_);
lean_inc_ref(v_a_2016_);
lean_inc(v_a_2015_);
lean_inc_ref(v_a_2014_);
lean_inc(v_a_2013_);
lean_inc_ref(v_a_2012_);
lean_inc(v_a_2011_);
lean_inc(v_a_2010_);
lean_inc_ref(v_a_2009_);
lean_inc_ref(v_a_2008_);
v___x_2071_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f(v_a_2008_, v_a_2009_, v_a_2010_, v_a_2011_, v_a_2012_, v_a_2013_, v_a_2014_, v_a_2015_, v_a_2016_, v_a_2017_, v_a_2018_, v_a_2019_);
if (lean_obj_tag(v___x_2071_) == 0)
{
lean_object* v_a_2072_; 
v_a_2072_ = lean_ctor_get(v___x_2071_, 0);
lean_inc(v_a_2072_);
lean_dec_ref(v___x_2071_);
if (lean_obj_tag(v_a_2072_) == 1)
{
lean_object* v_val_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; uint8_t v___x_2076_; 
v_val_2073_ = lean_ctor_get(v_a_2072_, 0);
lean_inc(v_val_2073_);
lean_dec_ref(v_a_2072_);
v___x_2074_ = lean_unsigned_to_nat(0u);
v___x_2075_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__4___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__4___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__4___closed__1);
v___x_2076_ = lean_int_dec_eq(v_val_2073_, v___x_2075_);
if (v___x_2076_ == 0)
{
lean_object* v___x_2077_; 
v___x_2077_ = l_Lean_Meta_Grind_Arith_CommRing_hasChar(v_a_2009_, v_a_2010_, v_a_2011_, v_a_2012_, v_a_2013_, v_a_2014_, v_a_2015_, v_a_2016_, v_a_2017_, v_a_2018_, v_a_2019_);
if (lean_obj_tag(v___x_2077_) == 0)
{
lean_object* v_a_2078_; uint8_t v___x_2079_; 
v_a_2078_ = lean_ctor_get(v___x_2077_, 0);
lean_inc(v_a_2078_);
lean_dec_ref(v___x_2077_);
v___x_2079_ = lean_unbox(v_a_2078_);
lean_dec(v_a_2078_);
if (v___x_2079_ == 0)
{
lean_dec(v_val_2073_);
lean_dec_ref(v_a_2009_);
lean_dec_ref(v_e_2006_);
v___y_2043_ = v_a_2010_;
v___y_2044_ = v_a_2011_;
v___y_2045_ = v_a_2012_;
v___y_2046_ = v_a_2013_;
v___y_2047_ = v_a_2014_;
v___y_2048_ = v_a_2015_;
v___y_2049_ = v_a_2016_;
v___y_2050_ = v_a_2017_;
v___y_2051_ = v_a_2018_;
v___y_2052_ = v_a_2019_;
goto v___jp_2042_;
}
else
{
lean_object* v___x_2080_; 
v___x_2080_ = l_Lean_Meta_Grind_Arith_CommRing_getCharInst(v_a_2009_, v_a_2010_, v_a_2011_, v_a_2012_, v_a_2013_, v_a_2014_, v_a_2015_, v_a_2016_, v_a_2017_, v_a_2018_, v_a_2019_);
if (lean_obj_tag(v___x_2080_) == 0)
{
lean_object* v_a_2081_; lean_object* v_fst_2082_; lean_object* v_snd_2083_; lean_object* v___x_2085_; uint8_t v_isShared_2086_; uint8_t v_isSharedCheck_2216_; 
v_a_2081_ = lean_ctor_get(v___x_2080_, 0);
lean_inc(v_a_2081_);
lean_dec_ref(v___x_2080_);
v_fst_2082_ = lean_ctor_get(v_a_2081_, 0);
v_snd_2083_ = lean_ctor_get(v_a_2081_, 1);
v_isSharedCheck_2216_ = !lean_is_exclusive(v_a_2081_);
if (v_isSharedCheck_2216_ == 0)
{
v___x_2085_ = v_a_2081_;
v_isShared_2086_ = v_isSharedCheck_2216_;
goto v_resetjp_2084_;
}
else
{
lean_inc(v_snd_2083_);
lean_inc(v_fst_2082_);
lean_dec(v_a_2081_);
v___x_2085_ = lean_box(0);
v_isShared_2086_ = v_isSharedCheck_2216_;
goto v_resetjp_2084_;
}
v_resetjp_2084_:
{
uint8_t v___x_2087_; 
v___x_2087_ = lean_nat_dec_eq(v_snd_2083_, v___x_2074_);
if (v___x_2087_ == 0)
{
lean_object* v___x_2088_; lean_object* v___x_2089_; uint8_t v___x_2090_; 
lean_inc(v_snd_2083_);
v___x_2088_ = lean_nat_to_int(v_snd_2083_);
v___x_2089_ = lean_int_emod(v_val_2073_, v___x_2088_);
lean_dec(v___x_2088_);
v___x_2090_ = lean_int_dec_eq(v___x_2089_, v___x_2075_);
lean_dec(v___x_2089_);
if (v___x_2090_ == 0)
{
lean_object* v___x_2091_; 
lean_inc(v_a_2019_);
lean_inc_ref(v_a_2018_);
lean_inc(v_a_2017_);
lean_inc_ref(v_a_2016_);
lean_inc(v_a_2015_);
lean_inc_ref(v_a_2014_);
lean_inc(v_a_2013_);
lean_inc_ref(v_a_2012_);
lean_inc(v_a_2011_);
lean_inc(v_a_2010_);
lean_inc_ref(v_a_2009_);
v___x_2091_ = l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__3(v_a_2009_, v_a_2010_, v_a_2011_, v_a_2012_, v_a_2013_, v_a_2014_, v_a_2015_, v_a_2016_, v_a_2017_, v_a_2018_, v_a_2019_);
if (lean_obj_tag(v___x_2091_) == 0)
{
lean_object* v_a_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; 
v_a_2092_ = lean_ctor_get(v___x_2091_, 0);
lean_inc(v_a_2092_);
lean_dec_ref(v___x_2091_);
v___x_2093_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__3, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__3);
lean_inc(v_a_2019_);
lean_inc_ref(v_a_2018_);
lean_inc(v_a_2017_);
lean_inc_ref(v_a_2016_);
lean_inc(v_a_2015_);
lean_inc_ref(v_a_2014_);
lean_inc(v_a_2013_);
lean_inc_ref(v_a_2012_);
lean_inc(v_a_2011_);
lean_inc(v_a_2010_);
v___x_2094_ = l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__4(v___x_2093_, v_a_2009_, v_a_2010_, v_a_2011_, v_a_2012_, v_a_2013_, v_a_2014_, v_a_2015_, v_a_2016_, v_a_2017_, v_a_2018_, v_a_2019_);
if (lean_obj_tag(v___x_2094_) == 0)
{
lean_object* v_a_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; 
v_a_2095_ = lean_ctor_get(v___x_2094_, 0);
lean_inc(v_a_2095_);
lean_dec_ref(v___x_2094_);
v___x_2096_ = l_Lean_mkAppB(v_a_2092_, v_a_2008_, v_e_2006_);
lean_inc(v_a_2019_);
lean_inc_ref(v_a_2018_);
lean_inc(v_a_2017_);
lean_inc_ref(v_a_2016_);
v___x_2097_ = l_Lean_Meta_mkEq(v___x_2096_, v_a_2095_, v_a_2016_, v_a_2017_, v_a_2018_, v_a_2019_);
if (lean_obj_tag(v___x_2097_) == 0)
{
lean_object* v_a_2098_; lean_object* v_type_2099_; lean_object* v_u_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; lean_object* v___x_2104_; 
v_a_2098_ = lean_ctor_get(v___x_2097_, 0);
lean_inc(v_a_2098_);
lean_dec_ref(v___x_2097_);
v_type_2099_ = lean_ctor_get(v_toRing_2040_, 1);
lean_inc_ref(v_type_2099_);
v_u_2100_ = lean_ctor_get(v_toRing_2040_, 2);
lean_inc(v_u_2100_);
lean_dec_ref(v_toRing_2040_);
v___x_2101_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__5));
v___x_2102_ = lean_box(0);
if (v_isShared_2086_ == 0)
{
lean_ctor_set_tag(v___x_2085_, 1);
lean_ctor_set(v___x_2085_, 1, v___x_2102_);
lean_ctor_set(v___x_2085_, 0, v_u_2100_);
v___x_2104_ = v___x_2085_;
goto v_reusejp_2103_;
}
else
{
lean_object* v_reuseFailAlloc_2112_; 
v_reuseFailAlloc_2112_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2112_, 0, v_u_2100_);
lean_ctor_set(v_reuseFailAlloc_2112_, 1, v___x_2102_);
v___x_2104_ = v_reuseFailAlloc_2112_;
goto v_reusejp_2103_;
}
v_reusejp_2103_:
{
lean_object* v___x_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; 
v___x_2105_ = l_Lean_mkConst(v___x_2101_, v___x_2104_);
v___x_2106_ = l_Lean_mkNatLit(v_snd_2083_);
v___x_2107_ = l_Lean_mkIntLit(v_val_2073_);
lean_dec(v_val_2073_);
v___x_2108_ = l_Lean_eagerReflBoolTrue;
v___x_2109_ = l_Lean_mkApp6(v___x_2105_, v_type_2099_, v___x_2106_, v_val_2041_, v_fst_2082_, v___x_2107_, v___x_2108_);
v___x_2110_ = l_Lean_Meta_mkExpectedPropHint(v___x_2109_, v_a_2098_);
v___x_2111_ = l_Lean_Meta_Grind_pushNewFact(v___x_2110_, v___x_2074_, v_a_2010_, v_a_2011_, v_a_2012_, v_a_2013_, v_a_2014_, v_a_2015_, v_a_2016_, v_a_2017_, v_a_2018_, v_a_2019_);
if (lean_obj_tag(v___x_2111_) == 0)
{
lean_dec_ref(v___x_2111_);
goto v___jp_2021_;
}
else
{
return v___x_2111_;
}
}
}
else
{
lean_object* v_a_2113_; lean_object* v___x_2115_; uint8_t v_isShared_2116_; uint8_t v_isSharedCheck_2120_; 
lean_del_object(v___x_2085_);
lean_dec(v_snd_2083_);
lean_dec(v_fst_2082_);
lean_dec(v_val_2073_);
lean_dec(v_val_2041_);
lean_dec_ref(v_toRing_2040_);
lean_dec(v_a_2019_);
lean_dec_ref(v_a_2018_);
lean_dec(v_a_2017_);
lean_dec_ref(v_a_2016_);
lean_dec(v_a_2015_);
lean_dec_ref(v_a_2014_);
lean_dec(v_a_2013_);
lean_dec_ref(v_a_2012_);
lean_dec(v_a_2011_);
lean_dec(v_a_2010_);
v_a_2113_ = lean_ctor_get(v___x_2097_, 0);
v_isSharedCheck_2120_ = !lean_is_exclusive(v___x_2097_);
if (v_isSharedCheck_2120_ == 0)
{
v___x_2115_ = v___x_2097_;
v_isShared_2116_ = v_isSharedCheck_2120_;
goto v_resetjp_2114_;
}
else
{
lean_inc(v_a_2113_);
lean_dec(v___x_2097_);
v___x_2115_ = lean_box(0);
v_isShared_2116_ = v_isSharedCheck_2120_;
goto v_resetjp_2114_;
}
v_resetjp_2114_:
{
lean_object* v___x_2118_; 
if (v_isShared_2116_ == 0)
{
v___x_2118_ = v___x_2115_;
goto v_reusejp_2117_;
}
else
{
lean_object* v_reuseFailAlloc_2119_; 
v_reuseFailAlloc_2119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2119_, 0, v_a_2113_);
v___x_2118_ = v_reuseFailAlloc_2119_;
goto v_reusejp_2117_;
}
v_reusejp_2117_:
{
return v___x_2118_;
}
}
}
}
else
{
lean_object* v_a_2121_; lean_object* v___x_2123_; uint8_t v_isShared_2124_; uint8_t v_isSharedCheck_2128_; 
lean_dec(v_a_2092_);
lean_del_object(v___x_2085_);
lean_dec(v_snd_2083_);
lean_dec(v_fst_2082_);
lean_dec(v_val_2073_);
lean_dec(v_val_2041_);
lean_dec_ref(v_toRing_2040_);
lean_dec(v_a_2019_);
lean_dec_ref(v_a_2018_);
lean_dec(v_a_2017_);
lean_dec_ref(v_a_2016_);
lean_dec(v_a_2015_);
lean_dec_ref(v_a_2014_);
lean_dec(v_a_2013_);
lean_dec_ref(v_a_2012_);
lean_dec(v_a_2011_);
lean_dec(v_a_2010_);
lean_dec_ref(v_a_2008_);
lean_dec_ref(v_e_2006_);
v_a_2121_ = lean_ctor_get(v___x_2094_, 0);
v_isSharedCheck_2128_ = !lean_is_exclusive(v___x_2094_);
if (v_isSharedCheck_2128_ == 0)
{
v___x_2123_ = v___x_2094_;
v_isShared_2124_ = v_isSharedCheck_2128_;
goto v_resetjp_2122_;
}
else
{
lean_inc(v_a_2121_);
lean_dec(v___x_2094_);
v___x_2123_ = lean_box(0);
v_isShared_2124_ = v_isSharedCheck_2128_;
goto v_resetjp_2122_;
}
v_resetjp_2122_:
{
lean_object* v___x_2126_; 
if (v_isShared_2124_ == 0)
{
v___x_2126_ = v___x_2123_;
goto v_reusejp_2125_;
}
else
{
lean_object* v_reuseFailAlloc_2127_; 
v_reuseFailAlloc_2127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2127_, 0, v_a_2121_);
v___x_2126_ = v_reuseFailAlloc_2127_;
goto v_reusejp_2125_;
}
v_reusejp_2125_:
{
return v___x_2126_;
}
}
}
}
else
{
lean_object* v_a_2129_; lean_object* v___x_2131_; uint8_t v_isShared_2132_; uint8_t v_isSharedCheck_2136_; 
lean_del_object(v___x_2085_);
lean_dec(v_snd_2083_);
lean_dec(v_fst_2082_);
lean_dec(v_val_2073_);
lean_dec(v_val_2041_);
lean_dec_ref(v_toRing_2040_);
lean_dec(v_a_2019_);
lean_dec_ref(v_a_2018_);
lean_dec(v_a_2017_);
lean_dec_ref(v_a_2016_);
lean_dec(v_a_2015_);
lean_dec_ref(v_a_2014_);
lean_dec(v_a_2013_);
lean_dec_ref(v_a_2012_);
lean_dec(v_a_2011_);
lean_dec(v_a_2010_);
lean_dec_ref(v_a_2009_);
lean_dec_ref(v_a_2008_);
lean_dec_ref(v_e_2006_);
v_a_2129_ = lean_ctor_get(v___x_2091_, 0);
v_isSharedCheck_2136_ = !lean_is_exclusive(v___x_2091_);
if (v_isSharedCheck_2136_ == 0)
{
v___x_2131_ = v___x_2091_;
v_isShared_2132_ = v_isSharedCheck_2136_;
goto v_resetjp_2130_;
}
else
{
lean_inc(v_a_2129_);
lean_dec(v___x_2091_);
v___x_2131_ = lean_box(0);
v_isShared_2132_ = v_isSharedCheck_2136_;
goto v_resetjp_2130_;
}
v_resetjp_2130_:
{
lean_object* v___x_2134_; 
if (v_isShared_2132_ == 0)
{
v___x_2134_ = v___x_2131_;
goto v_reusejp_2133_;
}
else
{
lean_object* v_reuseFailAlloc_2135_; 
v_reuseFailAlloc_2135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2135_, 0, v_a_2129_);
v___x_2134_ = v_reuseFailAlloc_2135_;
goto v_reusejp_2133_;
}
v_reusejp_2133_:
{
return v___x_2134_;
}
}
}
}
else
{
lean_object* v___x_2137_; 
lean_dec_ref(v_a_2008_);
lean_inc(v_a_2019_);
lean_inc_ref(v_a_2018_);
lean_inc(v_a_2017_);
lean_inc_ref(v_a_2016_);
lean_inc(v_a_2015_);
lean_inc_ref(v_a_2014_);
lean_inc(v_a_2013_);
lean_inc_ref(v_a_2012_);
lean_inc(v_a_2011_);
lean_inc(v_a_2010_);
v___x_2137_ = l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__4(v___x_2075_, v_a_2009_, v_a_2010_, v_a_2011_, v_a_2012_, v_a_2013_, v_a_2014_, v_a_2015_, v_a_2016_, v_a_2017_, v_a_2018_, v_a_2019_);
if (lean_obj_tag(v___x_2137_) == 0)
{
lean_object* v_a_2138_; lean_object* v___x_2139_; 
v_a_2138_ = lean_ctor_get(v___x_2137_, 0);
lean_inc(v_a_2138_);
lean_dec_ref(v___x_2137_);
lean_inc(v_a_2019_);
lean_inc_ref(v_a_2018_);
lean_inc(v_a_2017_);
lean_inc_ref(v_a_2016_);
v___x_2139_ = l_Lean_Meta_mkEq(v_e_2006_, v_a_2138_, v_a_2016_, v_a_2017_, v_a_2018_, v_a_2019_);
if (lean_obj_tag(v___x_2139_) == 0)
{
lean_object* v_a_2140_; lean_object* v_type_2141_; lean_object* v_u_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2146_; 
v_a_2140_ = lean_ctor_get(v___x_2139_, 0);
lean_inc(v_a_2140_);
lean_dec_ref(v___x_2139_);
v_type_2141_ = lean_ctor_get(v_toRing_2040_, 1);
lean_inc_ref(v_type_2141_);
v_u_2142_ = lean_ctor_get(v_toRing_2040_, 2);
lean_inc(v_u_2142_);
lean_dec_ref(v_toRing_2040_);
v___x_2143_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__7));
v___x_2144_ = lean_box(0);
if (v_isShared_2086_ == 0)
{
lean_ctor_set_tag(v___x_2085_, 1);
lean_ctor_set(v___x_2085_, 1, v___x_2144_);
lean_ctor_set(v___x_2085_, 0, v_u_2142_);
v___x_2146_ = v___x_2085_;
goto v_reusejp_2145_;
}
else
{
lean_object* v_reuseFailAlloc_2154_; 
v_reuseFailAlloc_2154_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2154_, 0, v_u_2142_);
lean_ctor_set(v_reuseFailAlloc_2154_, 1, v___x_2144_);
v___x_2146_ = v_reuseFailAlloc_2154_;
goto v_reusejp_2145_;
}
v_reusejp_2145_:
{
lean_object* v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; 
v___x_2147_ = l_Lean_mkConst(v___x_2143_, v___x_2146_);
v___x_2148_ = l_Lean_mkNatLit(v_snd_2083_);
v___x_2149_ = l_Lean_mkIntLit(v_val_2073_);
lean_dec(v_val_2073_);
v___x_2150_ = l_Lean_eagerReflBoolTrue;
v___x_2151_ = l_Lean_mkApp6(v___x_2147_, v_type_2141_, v___x_2148_, v_val_2041_, v_fst_2082_, v___x_2149_, v___x_2150_);
v___x_2152_ = l_Lean_Meta_mkExpectedPropHint(v___x_2151_, v_a_2140_);
v___x_2153_ = l_Lean_Meta_Grind_pushNewFact(v___x_2152_, v___x_2074_, v_a_2010_, v_a_2011_, v_a_2012_, v_a_2013_, v_a_2014_, v_a_2015_, v_a_2016_, v_a_2017_, v_a_2018_, v_a_2019_);
if (lean_obj_tag(v___x_2153_) == 0)
{
lean_dec_ref(v___x_2153_);
goto v___jp_2021_;
}
else
{
return v___x_2153_;
}
}
}
else
{
lean_object* v_a_2155_; lean_object* v___x_2157_; uint8_t v_isShared_2158_; uint8_t v_isSharedCheck_2162_; 
lean_del_object(v___x_2085_);
lean_dec(v_snd_2083_);
lean_dec(v_fst_2082_);
lean_dec(v_val_2073_);
lean_dec(v_val_2041_);
lean_dec_ref(v_toRing_2040_);
lean_dec(v_a_2019_);
lean_dec_ref(v_a_2018_);
lean_dec(v_a_2017_);
lean_dec_ref(v_a_2016_);
lean_dec(v_a_2015_);
lean_dec_ref(v_a_2014_);
lean_dec(v_a_2013_);
lean_dec_ref(v_a_2012_);
lean_dec(v_a_2011_);
lean_dec(v_a_2010_);
v_a_2155_ = lean_ctor_get(v___x_2139_, 0);
v_isSharedCheck_2162_ = !lean_is_exclusive(v___x_2139_);
if (v_isSharedCheck_2162_ == 0)
{
v___x_2157_ = v___x_2139_;
v_isShared_2158_ = v_isSharedCheck_2162_;
goto v_resetjp_2156_;
}
else
{
lean_inc(v_a_2155_);
lean_dec(v___x_2139_);
v___x_2157_ = lean_box(0);
v_isShared_2158_ = v_isSharedCheck_2162_;
goto v_resetjp_2156_;
}
v_resetjp_2156_:
{
lean_object* v___x_2160_; 
if (v_isShared_2158_ == 0)
{
v___x_2160_ = v___x_2157_;
goto v_reusejp_2159_;
}
else
{
lean_object* v_reuseFailAlloc_2161_; 
v_reuseFailAlloc_2161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2161_, 0, v_a_2155_);
v___x_2160_ = v_reuseFailAlloc_2161_;
goto v_reusejp_2159_;
}
v_reusejp_2159_:
{
return v___x_2160_;
}
}
}
}
else
{
lean_object* v_a_2163_; lean_object* v___x_2165_; uint8_t v_isShared_2166_; uint8_t v_isSharedCheck_2170_; 
lean_del_object(v___x_2085_);
lean_dec(v_snd_2083_);
lean_dec(v_fst_2082_);
lean_dec(v_val_2073_);
lean_dec(v_val_2041_);
lean_dec_ref(v_toRing_2040_);
lean_dec(v_a_2019_);
lean_dec_ref(v_a_2018_);
lean_dec(v_a_2017_);
lean_dec_ref(v_a_2016_);
lean_dec(v_a_2015_);
lean_dec_ref(v_a_2014_);
lean_dec(v_a_2013_);
lean_dec_ref(v_a_2012_);
lean_dec(v_a_2011_);
lean_dec(v_a_2010_);
lean_dec_ref(v_e_2006_);
v_a_2163_ = lean_ctor_get(v___x_2137_, 0);
v_isSharedCheck_2170_ = !lean_is_exclusive(v___x_2137_);
if (v_isSharedCheck_2170_ == 0)
{
v___x_2165_ = v___x_2137_;
v_isShared_2166_ = v_isSharedCheck_2170_;
goto v_resetjp_2164_;
}
else
{
lean_inc(v_a_2163_);
lean_dec(v___x_2137_);
v___x_2165_ = lean_box(0);
v_isShared_2166_ = v_isSharedCheck_2170_;
goto v_resetjp_2164_;
}
v_resetjp_2164_:
{
lean_object* v___x_2168_; 
if (v_isShared_2166_ == 0)
{
v___x_2168_ = v___x_2165_;
goto v_reusejp_2167_;
}
else
{
lean_object* v_reuseFailAlloc_2169_; 
v_reuseFailAlloc_2169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2169_, 0, v_a_2163_);
v___x_2168_ = v_reuseFailAlloc_2169_;
goto v_reusejp_2167_;
}
v_reusejp_2167_:
{
return v___x_2168_;
}
}
}
}
}
else
{
lean_object* v___x_2171_; 
lean_dec(v_snd_2083_);
lean_inc(v_a_2019_);
lean_inc_ref(v_a_2018_);
lean_inc(v_a_2017_);
lean_inc_ref(v_a_2016_);
lean_inc(v_a_2015_);
lean_inc_ref(v_a_2014_);
lean_inc(v_a_2013_);
lean_inc_ref(v_a_2012_);
lean_inc(v_a_2011_);
lean_inc(v_a_2010_);
lean_inc_ref(v_a_2009_);
v___x_2171_ = l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__3(v_a_2009_, v_a_2010_, v_a_2011_, v_a_2012_, v_a_2013_, v_a_2014_, v_a_2015_, v_a_2016_, v_a_2017_, v_a_2018_, v_a_2019_);
if (lean_obj_tag(v___x_2171_) == 0)
{
lean_object* v_a_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; 
v_a_2172_ = lean_ctor_get(v___x_2171_, 0);
lean_inc(v_a_2172_);
lean_dec_ref(v___x_2171_);
v___x_2173_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__3, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__3);
lean_inc(v_a_2019_);
lean_inc_ref(v_a_2018_);
lean_inc(v_a_2017_);
lean_inc_ref(v_a_2016_);
lean_inc(v_a_2015_);
lean_inc_ref(v_a_2014_);
lean_inc(v_a_2013_);
lean_inc_ref(v_a_2012_);
lean_inc(v_a_2011_);
lean_inc(v_a_2010_);
v___x_2174_ = l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__4(v___x_2173_, v_a_2009_, v_a_2010_, v_a_2011_, v_a_2012_, v_a_2013_, v_a_2014_, v_a_2015_, v_a_2016_, v_a_2017_, v_a_2018_, v_a_2019_);
if (lean_obj_tag(v___x_2174_) == 0)
{
lean_object* v_a_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; 
v_a_2175_ = lean_ctor_get(v___x_2174_, 0);
lean_inc(v_a_2175_);
lean_dec_ref(v___x_2174_);
v___x_2176_ = l_Lean_mkAppB(v_a_2172_, v_a_2008_, v_e_2006_);
lean_inc(v_a_2019_);
lean_inc_ref(v_a_2018_);
lean_inc(v_a_2017_);
lean_inc_ref(v_a_2016_);
v___x_2177_ = l_Lean_Meta_mkEq(v___x_2176_, v_a_2175_, v_a_2016_, v_a_2017_, v_a_2018_, v_a_2019_);
if (lean_obj_tag(v___x_2177_) == 0)
{
lean_object* v_a_2178_; lean_object* v_type_2179_; lean_object* v_u_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2184_; 
v_a_2178_ = lean_ctor_get(v___x_2177_, 0);
lean_inc(v_a_2178_);
lean_dec_ref(v___x_2177_);
v_type_2179_ = lean_ctor_get(v_toRing_2040_, 1);
lean_inc_ref(v_type_2179_);
v_u_2180_ = lean_ctor_get(v_toRing_2040_, 2);
lean_inc(v_u_2180_);
lean_dec_ref(v_toRing_2040_);
v___x_2181_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__9));
v___x_2182_ = lean_box(0);
if (v_isShared_2086_ == 0)
{
lean_ctor_set_tag(v___x_2085_, 1);
lean_ctor_set(v___x_2085_, 1, v___x_2182_);
lean_ctor_set(v___x_2085_, 0, v_u_2180_);
v___x_2184_ = v___x_2085_;
goto v_reusejp_2183_;
}
else
{
lean_object* v_reuseFailAlloc_2191_; 
v_reuseFailAlloc_2191_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2191_, 0, v_u_2180_);
lean_ctor_set(v_reuseFailAlloc_2191_, 1, v___x_2182_);
v___x_2184_ = v_reuseFailAlloc_2191_;
goto v_reusejp_2183_;
}
v_reusejp_2183_:
{
lean_object* v___x_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; 
v___x_2185_ = l_Lean_mkConst(v___x_2181_, v___x_2184_);
v___x_2186_ = l_Lean_mkIntLit(v_val_2073_);
lean_dec(v_val_2073_);
v___x_2187_ = l_Lean_eagerReflBoolTrue;
v___x_2188_ = l_Lean_mkApp5(v___x_2185_, v_type_2179_, v_val_2041_, v_fst_2082_, v___x_2186_, v___x_2187_);
v___x_2189_ = l_Lean_Meta_mkExpectedPropHint(v___x_2188_, v_a_2178_);
v___x_2190_ = l_Lean_Meta_Grind_pushNewFact(v___x_2189_, v___x_2074_, v_a_2010_, v_a_2011_, v_a_2012_, v_a_2013_, v_a_2014_, v_a_2015_, v_a_2016_, v_a_2017_, v_a_2018_, v_a_2019_);
if (lean_obj_tag(v___x_2190_) == 0)
{
lean_dec_ref(v___x_2190_);
goto v___jp_2021_;
}
else
{
return v___x_2190_;
}
}
}
else
{
lean_object* v_a_2192_; lean_object* v___x_2194_; uint8_t v_isShared_2195_; uint8_t v_isSharedCheck_2199_; 
lean_del_object(v___x_2085_);
lean_dec(v_fst_2082_);
lean_dec(v_val_2073_);
lean_dec(v_val_2041_);
lean_dec_ref(v_toRing_2040_);
lean_dec(v_a_2019_);
lean_dec_ref(v_a_2018_);
lean_dec(v_a_2017_);
lean_dec_ref(v_a_2016_);
lean_dec(v_a_2015_);
lean_dec_ref(v_a_2014_);
lean_dec(v_a_2013_);
lean_dec_ref(v_a_2012_);
lean_dec(v_a_2011_);
lean_dec(v_a_2010_);
v_a_2192_ = lean_ctor_get(v___x_2177_, 0);
v_isSharedCheck_2199_ = !lean_is_exclusive(v___x_2177_);
if (v_isSharedCheck_2199_ == 0)
{
v___x_2194_ = v___x_2177_;
v_isShared_2195_ = v_isSharedCheck_2199_;
goto v_resetjp_2193_;
}
else
{
lean_inc(v_a_2192_);
lean_dec(v___x_2177_);
v___x_2194_ = lean_box(0);
v_isShared_2195_ = v_isSharedCheck_2199_;
goto v_resetjp_2193_;
}
v_resetjp_2193_:
{
lean_object* v___x_2197_; 
if (v_isShared_2195_ == 0)
{
v___x_2197_ = v___x_2194_;
goto v_reusejp_2196_;
}
else
{
lean_object* v_reuseFailAlloc_2198_; 
v_reuseFailAlloc_2198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2198_, 0, v_a_2192_);
v___x_2197_ = v_reuseFailAlloc_2198_;
goto v_reusejp_2196_;
}
v_reusejp_2196_:
{
return v___x_2197_;
}
}
}
}
else
{
lean_object* v_a_2200_; lean_object* v___x_2202_; uint8_t v_isShared_2203_; uint8_t v_isSharedCheck_2207_; 
lean_dec(v_a_2172_);
lean_del_object(v___x_2085_);
lean_dec(v_fst_2082_);
lean_dec(v_val_2073_);
lean_dec(v_val_2041_);
lean_dec_ref(v_toRing_2040_);
lean_dec(v_a_2019_);
lean_dec_ref(v_a_2018_);
lean_dec(v_a_2017_);
lean_dec_ref(v_a_2016_);
lean_dec(v_a_2015_);
lean_dec_ref(v_a_2014_);
lean_dec(v_a_2013_);
lean_dec_ref(v_a_2012_);
lean_dec(v_a_2011_);
lean_dec(v_a_2010_);
lean_dec_ref(v_a_2008_);
lean_dec_ref(v_e_2006_);
v_a_2200_ = lean_ctor_get(v___x_2174_, 0);
v_isSharedCheck_2207_ = !lean_is_exclusive(v___x_2174_);
if (v_isSharedCheck_2207_ == 0)
{
v___x_2202_ = v___x_2174_;
v_isShared_2203_ = v_isSharedCheck_2207_;
goto v_resetjp_2201_;
}
else
{
lean_inc(v_a_2200_);
lean_dec(v___x_2174_);
v___x_2202_ = lean_box(0);
v_isShared_2203_ = v_isSharedCheck_2207_;
goto v_resetjp_2201_;
}
v_resetjp_2201_:
{
lean_object* v___x_2205_; 
if (v_isShared_2203_ == 0)
{
v___x_2205_ = v___x_2202_;
goto v_reusejp_2204_;
}
else
{
lean_object* v_reuseFailAlloc_2206_; 
v_reuseFailAlloc_2206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2206_, 0, v_a_2200_);
v___x_2205_ = v_reuseFailAlloc_2206_;
goto v_reusejp_2204_;
}
v_reusejp_2204_:
{
return v___x_2205_;
}
}
}
}
else
{
lean_object* v_a_2208_; lean_object* v___x_2210_; uint8_t v_isShared_2211_; uint8_t v_isSharedCheck_2215_; 
lean_del_object(v___x_2085_);
lean_dec(v_fst_2082_);
lean_dec(v_val_2073_);
lean_dec(v_val_2041_);
lean_dec_ref(v_toRing_2040_);
lean_dec(v_a_2019_);
lean_dec_ref(v_a_2018_);
lean_dec(v_a_2017_);
lean_dec_ref(v_a_2016_);
lean_dec(v_a_2015_);
lean_dec_ref(v_a_2014_);
lean_dec(v_a_2013_);
lean_dec_ref(v_a_2012_);
lean_dec(v_a_2011_);
lean_dec(v_a_2010_);
lean_dec_ref(v_a_2009_);
lean_dec_ref(v_a_2008_);
lean_dec_ref(v_e_2006_);
v_a_2208_ = lean_ctor_get(v___x_2171_, 0);
v_isSharedCheck_2215_ = !lean_is_exclusive(v___x_2171_);
if (v_isSharedCheck_2215_ == 0)
{
v___x_2210_ = v___x_2171_;
v_isShared_2211_ = v_isSharedCheck_2215_;
goto v_resetjp_2209_;
}
else
{
lean_inc(v_a_2208_);
lean_dec(v___x_2171_);
v___x_2210_ = lean_box(0);
v_isShared_2211_ = v_isSharedCheck_2215_;
goto v_resetjp_2209_;
}
v_resetjp_2209_:
{
lean_object* v___x_2213_; 
if (v_isShared_2211_ == 0)
{
v___x_2213_ = v___x_2210_;
goto v_reusejp_2212_;
}
else
{
lean_object* v_reuseFailAlloc_2214_; 
v_reuseFailAlloc_2214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2214_, 0, v_a_2208_);
v___x_2213_ = v_reuseFailAlloc_2214_;
goto v_reusejp_2212_;
}
v_reusejp_2212_:
{
return v___x_2213_;
}
}
}
}
}
}
else
{
lean_object* v_a_2217_; lean_object* v___x_2219_; uint8_t v_isShared_2220_; uint8_t v_isSharedCheck_2224_; 
lean_dec(v_val_2073_);
lean_dec(v_val_2041_);
lean_dec_ref(v_toRing_2040_);
lean_dec(v_a_2019_);
lean_dec_ref(v_a_2018_);
lean_dec(v_a_2017_);
lean_dec_ref(v_a_2016_);
lean_dec(v_a_2015_);
lean_dec_ref(v_a_2014_);
lean_dec(v_a_2013_);
lean_dec_ref(v_a_2012_);
lean_dec(v_a_2011_);
lean_dec(v_a_2010_);
lean_dec_ref(v_a_2009_);
lean_dec_ref(v_a_2008_);
lean_dec_ref(v_e_2006_);
v_a_2217_ = lean_ctor_get(v___x_2080_, 0);
v_isSharedCheck_2224_ = !lean_is_exclusive(v___x_2080_);
if (v_isSharedCheck_2224_ == 0)
{
v___x_2219_ = v___x_2080_;
v_isShared_2220_ = v_isSharedCheck_2224_;
goto v_resetjp_2218_;
}
else
{
lean_inc(v_a_2217_);
lean_dec(v___x_2080_);
v___x_2219_ = lean_box(0);
v_isShared_2220_ = v_isSharedCheck_2224_;
goto v_resetjp_2218_;
}
v_resetjp_2218_:
{
lean_object* v___x_2222_; 
if (v_isShared_2220_ == 0)
{
v___x_2222_ = v___x_2219_;
goto v_reusejp_2221_;
}
else
{
lean_object* v_reuseFailAlloc_2223_; 
v_reuseFailAlloc_2223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2223_, 0, v_a_2217_);
v___x_2222_ = v_reuseFailAlloc_2223_;
goto v_reusejp_2221_;
}
v_reusejp_2221_:
{
return v___x_2222_;
}
}
}
}
}
else
{
lean_object* v_a_2225_; lean_object* v___x_2227_; uint8_t v_isShared_2228_; uint8_t v_isSharedCheck_2232_; 
lean_dec(v_val_2073_);
lean_dec(v_val_2041_);
lean_dec_ref(v_toRing_2040_);
lean_dec(v_a_2019_);
lean_dec_ref(v_a_2018_);
lean_dec(v_a_2017_);
lean_dec_ref(v_a_2016_);
lean_dec(v_a_2015_);
lean_dec_ref(v_a_2014_);
lean_dec(v_a_2013_);
lean_dec_ref(v_a_2012_);
lean_dec(v_a_2011_);
lean_dec(v_a_2010_);
lean_dec_ref(v_a_2009_);
lean_dec_ref(v_a_2008_);
lean_dec_ref(v_e_2006_);
v_a_2225_ = lean_ctor_get(v___x_2077_, 0);
v_isSharedCheck_2232_ = !lean_is_exclusive(v___x_2077_);
if (v_isSharedCheck_2232_ == 0)
{
v___x_2227_ = v___x_2077_;
v_isShared_2228_ = v_isSharedCheck_2232_;
goto v_resetjp_2226_;
}
else
{
lean_inc(v_a_2225_);
lean_dec(v___x_2077_);
v___x_2227_ = lean_box(0);
v_isShared_2228_ = v_isSharedCheck_2232_;
goto v_resetjp_2226_;
}
v_resetjp_2226_:
{
lean_object* v___x_2230_; 
if (v_isShared_2228_ == 0)
{
v___x_2230_ = v___x_2227_;
goto v_reusejp_2229_;
}
else
{
lean_object* v_reuseFailAlloc_2231_; 
v_reuseFailAlloc_2231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2231_, 0, v_a_2225_);
v___x_2230_ = v_reuseFailAlloc_2231_;
goto v_reusejp_2229_;
}
v_reusejp_2229_:
{
return v___x_2230_;
}
}
}
}
else
{
lean_object* v_type_2233_; lean_object* v_u_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; 
lean_dec(v_val_2073_);
lean_dec(v_a_2015_);
lean_dec_ref(v_a_2014_);
lean_dec(v_a_2013_);
lean_dec(v_a_2011_);
lean_dec_ref(v_a_2009_);
v_type_2233_ = lean_ctor_get(v_toRing_2040_, 1);
lean_inc_ref(v_type_2233_);
v_u_2234_ = lean_ctor_get(v_toRing_2040_, 2);
lean_inc(v_u_2234_);
lean_dec_ref(v_toRing_2040_);
v___x_2235_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__11));
v___x_2236_ = lean_box(0);
v___x_2237_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2237_, 0, v_u_2234_);
lean_ctor_set(v___x_2237_, 1, v___x_2236_);
v___x_2238_ = l_Lean_mkConst(v___x_2235_, v___x_2237_);
v___x_2239_ = l_Lean_mkAppB(v___x_2238_, v_type_2233_, v_val_2041_);
v___x_2240_ = l_Lean_Meta_Grind_pushEqCore___redArg(v_e_2006_, v_a_2008_, v___x_2239_, v___x_2068_, v_a_2010_, v_a_2012_, v_a_2016_, v_a_2017_, v_a_2018_, v_a_2019_);
lean_dec_ref(v_a_2012_);
lean_dec(v_a_2010_);
if (lean_obj_tag(v___x_2240_) == 0)
{
lean_object* v___x_2242_; uint8_t v_isShared_2243_; uint8_t v_isSharedCheck_2248_; 
v_isSharedCheck_2248_ = !lean_is_exclusive(v___x_2240_);
if (v_isSharedCheck_2248_ == 0)
{
lean_object* v_unused_2249_; 
v_unused_2249_ = lean_ctor_get(v___x_2240_, 0);
lean_dec(v_unused_2249_);
v___x_2242_ = v___x_2240_;
v_isShared_2243_ = v_isSharedCheck_2248_;
goto v_resetjp_2241_;
}
else
{
lean_dec(v___x_2240_);
v___x_2242_ = lean_box(0);
v_isShared_2243_ = v_isSharedCheck_2248_;
goto v_resetjp_2241_;
}
v_resetjp_2241_:
{
lean_object* v___x_2244_; lean_object* v___x_2246_; 
v___x_2244_ = lean_box(0);
if (v_isShared_2243_ == 0)
{
lean_ctor_set(v___x_2242_, 0, v___x_2244_);
v___x_2246_ = v___x_2242_;
goto v_reusejp_2245_;
}
else
{
lean_object* v_reuseFailAlloc_2247_; 
v_reuseFailAlloc_2247_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2247_, 0, v___x_2244_);
v___x_2246_ = v_reuseFailAlloc_2247_;
goto v_reusejp_2245_;
}
v_reusejp_2245_:
{
return v___x_2246_;
}
}
}
else
{
return v___x_2240_;
}
}
}
else
{
lean_dec(v_a_2072_);
lean_dec_ref(v_a_2009_);
lean_dec_ref(v_e_2006_);
v___y_2043_ = v_a_2010_;
v___y_2044_ = v_a_2011_;
v___y_2045_ = v_a_2012_;
v___y_2046_ = v_a_2013_;
v___y_2047_ = v_a_2014_;
v___y_2048_ = v_a_2015_;
v___y_2049_ = v_a_2016_;
v___y_2050_ = v_a_2017_;
v___y_2051_ = v_a_2018_;
v___y_2052_ = v_a_2019_;
goto v___jp_2042_;
}
}
else
{
lean_object* v_a_2250_; lean_object* v___x_2252_; uint8_t v_isShared_2253_; uint8_t v_isSharedCheck_2257_; 
lean_dec(v_val_2041_);
lean_dec_ref(v_toRing_2040_);
lean_dec(v_a_2019_);
lean_dec_ref(v_a_2018_);
lean_dec(v_a_2017_);
lean_dec_ref(v_a_2016_);
lean_dec(v_a_2015_);
lean_dec_ref(v_a_2014_);
lean_dec(v_a_2013_);
lean_dec_ref(v_a_2012_);
lean_dec(v_a_2011_);
lean_dec(v_a_2010_);
lean_dec_ref(v_a_2009_);
lean_dec_ref(v_a_2008_);
lean_dec_ref(v_e_2006_);
v_a_2250_ = lean_ctor_get(v___x_2071_, 0);
v_isSharedCheck_2257_ = !lean_is_exclusive(v___x_2071_);
if (v_isSharedCheck_2257_ == 0)
{
v___x_2252_ = v___x_2071_;
v_isShared_2253_ = v_isSharedCheck_2257_;
goto v_resetjp_2251_;
}
else
{
lean_inc(v_a_2250_);
lean_dec(v___x_2071_);
v___x_2252_ = lean_box(0);
v_isShared_2253_ = v_isSharedCheck_2257_;
goto v_resetjp_2251_;
}
v_resetjp_2251_:
{
lean_object* v___x_2255_; 
if (v_isShared_2253_ == 0)
{
v___x_2255_ = v___x_2252_;
goto v_reusejp_2254_;
}
else
{
lean_object* v_reuseFailAlloc_2256_; 
v_reuseFailAlloc_2256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2256_, 0, v_a_2250_);
v___x_2255_ = v_reuseFailAlloc_2256_;
goto v_reusejp_2254_;
}
v_reusejp_2254_:
{
return v___x_2255_;
}
}
}
}
else
{
lean_dec(v_val_2041_);
lean_dec_ref(v_toRing_2040_);
lean_dec(v_a_2019_);
lean_dec_ref(v_a_2018_);
lean_dec(v_a_2017_);
lean_dec_ref(v_a_2016_);
lean_dec(v_a_2015_);
lean_dec_ref(v_a_2014_);
lean_dec(v_a_2013_);
lean_dec_ref(v_a_2012_);
lean_dec(v_a_2011_);
lean_dec(v_a_2010_);
lean_dec_ref(v_a_2009_);
lean_dec_ref(v_a_2008_);
lean_dec_ref(v_e_2006_);
return v___x_2070_;
}
}
else
{
lean_object* v___x_2258_; lean_object* v___x_2260_; 
lean_dec(v_val_2041_);
lean_dec_ref(v_toRing_2040_);
lean_dec(v_a_2019_);
lean_dec_ref(v_a_2018_);
lean_dec(v_a_2017_);
lean_dec_ref(v_a_2016_);
lean_dec(v_a_2015_);
lean_dec_ref(v_a_2014_);
lean_dec(v_a_2013_);
lean_dec_ref(v_a_2012_);
lean_dec(v_a_2011_);
lean_dec(v_a_2010_);
lean_dec_ref(v_a_2009_);
lean_dec_ref(v_a_2008_);
lean_dec_ref(v_e_2006_);
v___x_2258_ = lean_box(0);
if (v_isShared_2066_ == 0)
{
lean_ctor_set(v___x_2065_, 0, v___x_2258_);
v___x_2260_ = v___x_2065_;
goto v_reusejp_2259_;
}
else
{
lean_object* v_reuseFailAlloc_2261_; 
v_reuseFailAlloc_2261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2261_, 0, v___x_2258_);
v___x_2260_ = v_reuseFailAlloc_2261_;
goto v_reusejp_2259_;
}
v_reusejp_2259_:
{
return v___x_2260_;
}
}
}
}
else
{
lean_object* v_a_2263_; lean_object* v___x_2265_; uint8_t v_isShared_2266_; uint8_t v_isSharedCheck_2270_; 
lean_dec(v_val_2041_);
lean_dec_ref(v_toRing_2040_);
lean_dec(v_a_2019_);
lean_dec_ref(v_a_2018_);
lean_dec(v_a_2017_);
lean_dec_ref(v_a_2016_);
lean_dec(v_a_2015_);
lean_dec_ref(v_a_2014_);
lean_dec(v_a_2013_);
lean_dec_ref(v_a_2012_);
lean_dec(v_a_2011_);
lean_dec(v_a_2010_);
lean_dec_ref(v_a_2009_);
lean_dec_ref(v_a_2008_);
lean_dec_ref(v_e_2006_);
v_a_2263_ = lean_ctor_get(v___x_2062_, 0);
v_isSharedCheck_2270_ = !lean_is_exclusive(v___x_2062_);
if (v_isSharedCheck_2270_ == 0)
{
v___x_2265_ = v___x_2062_;
v_isShared_2266_ = v_isSharedCheck_2270_;
goto v_resetjp_2264_;
}
else
{
lean_inc(v_a_2263_);
lean_dec(v___x_2062_);
v___x_2265_ = lean_box(0);
v_isShared_2266_ = v_isSharedCheck_2270_;
goto v_resetjp_2264_;
}
v_resetjp_2264_:
{
lean_object* v___x_2268_; 
if (v_isShared_2266_ == 0)
{
v___x_2268_ = v___x_2265_;
goto v_reusejp_2267_;
}
else
{
lean_object* v_reuseFailAlloc_2269_; 
v_reuseFailAlloc_2269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2269_, 0, v_a_2263_);
v___x_2268_ = v_reuseFailAlloc_2269_;
goto v_reusejp_2267_;
}
v_reusejp_2267_:
{
return v___x_2268_;
}
}
}
v___jp_2042_:
{
lean_object* v_type_2053_; lean_object* v_u_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; 
v_type_2053_ = lean_ctor_get(v_toRing_2040_, 1);
lean_inc_ref(v_type_2053_);
v_u_2054_ = lean_ctor_get(v_toRing_2040_, 2);
lean_inc(v_u_2054_);
lean_dec_ref(v_toRing_2040_);
v___x_2055_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__2));
v___x_2056_ = lean_box(0);
v___x_2057_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2057_, 0, v_u_2054_);
lean_ctor_set(v___x_2057_, 1, v___x_2056_);
v___x_2058_ = l_Lean_mkConst(v___x_2055_, v___x_2057_);
v___x_2059_ = l_Lean_mkApp3(v___x_2058_, v_type_2053_, v_val_2041_, v_a_2008_);
v___x_2060_ = lean_unsigned_to_nat(0u);
v___x_2061_ = l_Lean_Meta_Grind_pushNewFact(v___x_2059_, v___x_2060_, v___y_2043_, v___y_2044_, v___y_2045_, v___y_2046_, v___y_2047_, v___y_2048_, v___y_2049_, v___y_2050_, v___y_2051_, v___y_2052_);
return v___x_2061_;
}
}
else
{
lean_object* v___x_2271_; lean_object* v___x_2273_; 
lean_dec(v_fieldInst_x3f_2039_);
lean_dec(v_a_2035_);
lean_dec(v_a_2019_);
lean_dec_ref(v_a_2018_);
lean_dec(v_a_2017_);
lean_dec_ref(v_a_2016_);
lean_dec(v_a_2015_);
lean_dec_ref(v_a_2014_);
lean_dec(v_a_2013_);
lean_dec_ref(v_a_2012_);
lean_dec(v_a_2011_);
lean_dec(v_a_2010_);
lean_dec_ref(v_a_2009_);
lean_dec_ref(v_a_2008_);
lean_dec_ref(v_e_2006_);
v___x_2271_ = lean_box(0);
if (v_isShared_2038_ == 0)
{
lean_ctor_set(v___x_2037_, 0, v___x_2271_);
v___x_2273_ = v___x_2037_;
goto v_reusejp_2272_;
}
else
{
lean_object* v_reuseFailAlloc_2274_; 
v_reuseFailAlloc_2274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2274_, 0, v___x_2271_);
v___x_2273_ = v_reuseFailAlloc_2274_;
goto v_reusejp_2272_;
}
v_reusejp_2272_:
{
return v___x_2273_;
}
}
}
}
else
{
lean_object* v_a_2276_; lean_object* v___x_2278_; uint8_t v_isShared_2279_; uint8_t v_isSharedCheck_2283_; 
lean_dec(v_a_2019_);
lean_dec_ref(v_a_2018_);
lean_dec(v_a_2017_);
lean_dec_ref(v_a_2016_);
lean_dec(v_a_2015_);
lean_dec_ref(v_a_2014_);
lean_dec(v_a_2013_);
lean_dec_ref(v_a_2012_);
lean_dec(v_a_2011_);
lean_dec(v_a_2010_);
lean_dec_ref(v_a_2009_);
lean_dec_ref(v_a_2008_);
lean_dec_ref(v_e_2006_);
v_a_2276_ = lean_ctor_get(v___x_2034_, 0);
v_isSharedCheck_2283_ = !lean_is_exclusive(v___x_2034_);
if (v_isSharedCheck_2283_ == 0)
{
v___x_2278_ = v___x_2034_;
v_isShared_2279_ = v_isSharedCheck_2283_;
goto v_resetjp_2277_;
}
else
{
lean_inc(v_a_2276_);
lean_dec(v___x_2034_);
v___x_2278_ = lean_box(0);
v_isShared_2279_ = v_isSharedCheck_2283_;
goto v_resetjp_2277_;
}
v_resetjp_2277_:
{
lean_object* v___x_2281_; 
if (v_isShared_2279_ == 0)
{
v___x_2281_ = v___x_2278_;
goto v_reusejp_2280_;
}
else
{
lean_object* v_reuseFailAlloc_2282_; 
v_reuseFailAlloc_2282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2282_, 0, v_a_2276_);
v___x_2281_ = v_reuseFailAlloc_2282_;
goto v_reusejp_2280_;
}
v_reusejp_2280_:
{
return v___x_2281_;
}
}
}
}
}
}
else
{
lean_object* v_a_2285_; lean_object* v___x_2287_; uint8_t v_isShared_2288_; uint8_t v_isSharedCheck_2292_; 
lean_dec(v_a_2019_);
lean_dec_ref(v_a_2018_);
lean_dec(v_a_2017_);
lean_dec_ref(v_a_2016_);
lean_dec(v_a_2015_);
lean_dec_ref(v_a_2014_);
lean_dec(v_a_2013_);
lean_dec_ref(v_a_2012_);
lean_dec(v_a_2011_);
lean_dec(v_a_2010_);
lean_dec_ref(v_a_2009_);
lean_dec_ref(v_a_2008_);
lean_dec_ref(v_e_2006_);
v_a_2285_ = lean_ctor_get(v___x_2024_, 0);
v_isSharedCheck_2292_ = !lean_is_exclusive(v___x_2024_);
if (v_isSharedCheck_2292_ == 0)
{
v___x_2287_ = v___x_2024_;
v_isShared_2288_ = v_isSharedCheck_2292_;
goto v_resetjp_2286_;
}
else
{
lean_inc(v_a_2285_);
lean_dec(v___x_2024_);
v___x_2287_ = lean_box(0);
v_isShared_2288_ = v_isSharedCheck_2292_;
goto v_resetjp_2286_;
}
v_resetjp_2286_:
{
lean_object* v___x_2290_; 
if (v_isShared_2288_ == 0)
{
v___x_2290_ = v___x_2287_;
goto v_reusejp_2289_;
}
else
{
lean_object* v_reuseFailAlloc_2291_; 
v_reuseFailAlloc_2291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2291_, 0, v_a_2285_);
v___x_2290_ = v_reuseFailAlloc_2291_;
goto v_reusejp_2289_;
}
v_reusejp_2289_:
{
return v___x_2290_;
}
}
}
v___jp_2021_:
{
lean_object* v___x_2022_; lean_object* v___x_2023_; 
v___x_2022_ = lean_box(0);
v___x_2023_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2023_, 0, v___x_2022_);
return v___x_2023_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___boxed(lean_object* v_e_2293_, lean_object* v_inst_2294_, lean_object* v_a_2295_, lean_object* v_a_2296_, lean_object* v_a_2297_, lean_object* v_a_2298_, lean_object* v_a_2299_, lean_object* v_a_2300_, lean_object* v_a_2301_, lean_object* v_a_2302_, lean_object* v_a_2303_, lean_object* v_a_2304_, lean_object* v_a_2305_, lean_object* v_a_2306_, lean_object* v_a_2307_){
_start:
{
lean_object* v_res_2308_; 
v_res_2308_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv(v_e_2293_, v_inst_2294_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_, v_a_2301_, v_a_2302_, v_a_2303_, v_a_2304_, v_a_2305_, v_a_2306_);
lean_dec_ref(v_inst_2294_);
return v_res_2308_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0(lean_object* v_00_u03b2_2309_, lean_object* v_x_2310_, lean_object* v_x_2311_, lean_object* v_x_2312_){
_start:
{
lean_object* v___x_2313_; 
v___x_2313_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0___redArg(v_x_2310_, v_x_2311_, v_x_2312_);
return v___x_2313_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1(lean_object* v_00_u03b2_2314_, lean_object* v_x_2315_, lean_object* v_x_2316_){
_start:
{
uint8_t v___x_2317_; 
v___x_2317_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1___redArg(v_x_2315_, v_x_2316_);
return v___x_2317_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1___boxed(lean_object* v_00_u03b2_2318_, lean_object* v_x_2319_, lean_object* v_x_2320_){
_start:
{
uint8_t v_res_2321_; lean_object* v_r_2322_; 
v_res_2321_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1(v_00_u03b2_2318_, v_x_2319_, v_x_2320_);
lean_dec_ref(v_x_2320_);
v_r_2322_ = lean_box(v_res_2321_);
return v_r_2322_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0(lean_object* v_00_u03b2_2323_, lean_object* v_x_2324_, size_t v_x_2325_, size_t v_x_2326_, lean_object* v_x_2327_, lean_object* v_x_2328_){
_start:
{
lean_object* v___x_2329_; 
v___x_2329_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg(v_x_2324_, v_x_2325_, v_x_2326_, v_x_2327_, v_x_2328_);
return v___x_2329_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2330_, lean_object* v_x_2331_, lean_object* v_x_2332_, lean_object* v_x_2333_, lean_object* v_x_2334_, lean_object* v_x_2335_){
_start:
{
size_t v_x_141833__boxed_2336_; size_t v_x_141834__boxed_2337_; lean_object* v_res_2338_; 
v_x_141833__boxed_2336_ = lean_unbox_usize(v_x_2332_);
lean_dec(v_x_2332_);
v_x_141834__boxed_2337_ = lean_unbox_usize(v_x_2333_);
lean_dec(v_x_2333_);
v_res_2338_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0(v_00_u03b2_2330_, v_x_2331_, v_x_141833__boxed_2336_, v_x_141834__boxed_2337_, v_x_2334_, v_x_2335_);
return v_res_2338_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1_spec__2(lean_object* v_00_u03b2_2339_, lean_object* v_x_2340_, size_t v_x_2341_, lean_object* v_x_2342_){
_start:
{
uint8_t v___x_2343_; 
v___x_2343_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1_spec__2___redArg(v_x_2340_, v_x_2341_, v_x_2342_);
return v___x_2343_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1_spec__2___boxed(lean_object* v_00_u03b2_2344_, lean_object* v_x_2345_, lean_object* v_x_2346_, lean_object* v_x_2347_){
_start:
{
size_t v_x_141850__boxed_2348_; uint8_t v_res_2349_; lean_object* v_r_2350_; 
v_x_141850__boxed_2348_ = lean_unbox_usize(v_x_2346_);
lean_dec(v_x_2346_);
v_res_2349_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1_spec__2(v_00_u03b2_2344_, v_x_2345_, v_x_141850__boxed_2348_, v_x_2347_);
lean_dec_ref(v_x_2347_);
v_r_2350_ = lean_box(v_res_2349_);
return v_r_2350_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_2351_, lean_object* v_n_2352_, lean_object* v_k_2353_, lean_object* v_v_2354_){
_start:
{
lean_object* v___x_2355_; 
v___x_2355_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0_spec__2___redArg(v_n_2352_, v_k_2353_, v_v_2354_);
return v___x_2355_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_2356_, size_t v_depth_2357_, lean_object* v_keys_2358_, lean_object* v_vals_2359_, lean_object* v_heq_2360_, lean_object* v_i_2361_, lean_object* v_entries_2362_){
_start:
{
lean_object* v___x_2363_; 
v___x_2363_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0_spec__3___redArg(v_depth_2357_, v_keys_2358_, v_vals_2359_, v_i_2361_, v_entries_2362_);
return v___x_2363_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b2_2364_, lean_object* v_depth_2365_, lean_object* v_keys_2366_, lean_object* v_vals_2367_, lean_object* v_heq_2368_, lean_object* v_i_2369_, lean_object* v_entries_2370_){
_start:
{
size_t v_depth_boxed_2371_; lean_object* v_res_2372_; 
v_depth_boxed_2371_ = lean_unbox_usize(v_depth_2365_);
lean_dec(v_depth_2365_);
v_res_2372_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0_spec__3(v_00_u03b2_2364_, v_depth_boxed_2371_, v_keys_2366_, v_vals_2367_, v_heq_2368_, v_i_2369_, v_entries_2370_);
lean_dec_ref(v_vals_2367_);
lean_dec_ref(v_keys_2366_);
return v_res_2372_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1_spec__2_spec__6(lean_object* v_00_u03b2_2373_, lean_object* v_keys_2374_, lean_object* v_vals_2375_, lean_object* v_heq_2376_, lean_object* v_i_2377_, lean_object* v_k_2378_){
_start:
{
uint8_t v___x_2379_; 
v___x_2379_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1_spec__2_spec__6___redArg(v_keys_2374_, v_i_2377_, v_k_2378_);
return v___x_2379_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1_spec__2_spec__6___boxed(lean_object* v_00_u03b2_2380_, lean_object* v_keys_2381_, lean_object* v_vals_2382_, lean_object* v_heq_2383_, lean_object* v_i_2384_, lean_object* v_k_2385_){
_start:
{
uint8_t v_res_2386_; lean_object* v_r_2387_; 
v_res_2386_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1_spec__2_spec__6(v_00_u03b2_2380_, v_keys_2381_, v_vals_2382_, v_heq_2383_, v_i_2384_, v_k_2385_);
lean_dec_ref(v_k_2385_);
lean_dec_ref(v_vals_2382_);
lean_dec_ref(v_keys_2381_);
v_r_2387_ = lean_box(v_res_2386_);
return v_r_2387_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0_spec__2_spec__6(lean_object* v_00_u03b2_2388_, lean_object* v_x_2389_, lean_object* v_x_2390_, lean_object* v_x_2391_, lean_object* v_x_2392_){
_start:
{
lean_object* v___x_2393_; 
v___x_2393_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0_spec__2_spec__6___redArg(v_x_2389_, v_x_2390_, v_x_2391_, v_x_2392_);
return v___x_2393_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeInv(lean_object* v_e_2394_, lean_object* v_a_2395_, lean_object* v_a_2396_, lean_object* v_a_2397_, lean_object* v_a_2398_, lean_object* v_a_2399_, lean_object* v_a_2400_, lean_object* v_a_2401_, lean_object* v_a_2402_, lean_object* v_a_2403_, lean_object* v_a_2404_){
_start:
{
lean_object* v___x_2406_; 
lean_inc_ref(v_e_2394_);
v___x_2406_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_2394_, v_a_2402_);
if (lean_obj_tag(v___x_2406_) == 0)
{
lean_object* v_a_2407_; lean_object* v___x_2409_; uint8_t v_isShared_2410_; uint8_t v_isSharedCheck_2468_; 
v_a_2407_ = lean_ctor_get(v___x_2406_, 0);
v_isSharedCheck_2468_ = !lean_is_exclusive(v___x_2406_);
if (v_isSharedCheck_2468_ == 0)
{
v___x_2409_ = v___x_2406_;
v_isShared_2410_ = v_isSharedCheck_2468_;
goto v_resetjp_2408_;
}
else
{
lean_inc(v_a_2407_);
lean_dec(v___x_2406_);
v___x_2409_ = lean_box(0);
v_isShared_2410_ = v_isSharedCheck_2468_;
goto v_resetjp_2408_;
}
v_resetjp_2408_:
{
lean_object* v___x_2417_; uint8_t v___x_2418_; 
v___x_2417_ = l_Lean_Expr_cleanupAnnotations(v_a_2407_);
v___x_2418_ = l_Lean_Expr_isApp(v___x_2417_);
if (v___x_2418_ == 0)
{
lean_dec_ref(v___x_2417_);
lean_dec(v_a_2404_);
lean_dec_ref(v_a_2403_);
lean_dec(v_a_2402_);
lean_dec_ref(v_a_2401_);
lean_dec(v_a_2400_);
lean_dec_ref(v_a_2399_);
lean_dec(v_a_2398_);
lean_dec_ref(v_a_2397_);
lean_dec(v_a_2396_);
lean_dec(v_a_2395_);
lean_dec_ref(v_e_2394_);
goto v___jp_2411_;
}
else
{
lean_object* v_arg_2419_; lean_object* v___x_2420_; uint8_t v___x_2421_; 
v_arg_2419_ = lean_ctor_get(v___x_2417_, 1);
lean_inc_ref(v_arg_2419_);
v___x_2420_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2417_);
v___x_2421_ = l_Lean_Expr_isApp(v___x_2420_);
if (v___x_2421_ == 0)
{
lean_dec_ref(v___x_2420_);
lean_dec_ref(v_arg_2419_);
lean_dec(v_a_2404_);
lean_dec_ref(v_a_2403_);
lean_dec(v_a_2402_);
lean_dec_ref(v_a_2401_);
lean_dec(v_a_2400_);
lean_dec_ref(v_a_2399_);
lean_dec(v_a_2398_);
lean_dec_ref(v_a_2397_);
lean_dec(v_a_2396_);
lean_dec(v_a_2395_);
lean_dec_ref(v_e_2394_);
goto v___jp_2411_;
}
else
{
lean_object* v_arg_2422_; lean_object* v___x_2423_; uint8_t v___x_2424_; 
v_arg_2422_ = lean_ctor_get(v___x_2420_, 1);
lean_inc_ref(v_arg_2422_);
v___x_2423_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2420_);
v___x_2424_ = l_Lean_Expr_isApp(v___x_2423_);
if (v___x_2424_ == 0)
{
lean_dec_ref(v___x_2423_);
lean_dec_ref(v_arg_2422_);
lean_dec_ref(v_arg_2419_);
lean_dec(v_a_2404_);
lean_dec_ref(v_a_2403_);
lean_dec(v_a_2402_);
lean_dec_ref(v_a_2401_);
lean_dec(v_a_2400_);
lean_dec_ref(v_a_2399_);
lean_dec(v_a_2398_);
lean_dec_ref(v_a_2397_);
lean_dec(v_a_2396_);
lean_dec(v_a_2395_);
lean_dec_ref(v_e_2394_);
goto v___jp_2411_;
}
else
{
lean_object* v_arg_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; uint8_t v___x_2428_; 
v_arg_2425_ = lean_ctor_get(v___x_2423_, 1);
lean_inc_ref(v_arg_2425_);
v___x_2426_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2423_);
v___x_2427_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___closed__6));
v___x_2428_ = l_Lean_Expr_isConstOf(v___x_2426_, v___x_2427_);
lean_dec_ref(v___x_2426_);
if (v___x_2428_ == 0)
{
lean_dec_ref(v_arg_2425_);
lean_dec_ref(v_arg_2422_);
lean_dec_ref(v_arg_2419_);
lean_dec(v_a_2404_);
lean_dec_ref(v_a_2403_);
lean_dec(v_a_2402_);
lean_dec_ref(v_a_2401_);
lean_dec(v_a_2400_);
lean_dec_ref(v_a_2399_);
lean_dec(v_a_2398_);
lean_dec_ref(v_a_2397_);
lean_dec(v_a_2396_);
lean_dec(v_a_2395_);
lean_dec_ref(v_e_2394_);
goto v___jp_2411_;
}
else
{
lean_object* v___x_2429_; 
lean_del_object(v___x_2409_);
lean_inc(v_a_2404_);
lean_inc_ref(v_a_2403_);
lean_inc(v_a_2402_);
lean_inc_ref(v_a_2401_);
lean_inc(v_a_2400_);
lean_inc_ref(v_a_2399_);
lean_inc(v_a_2398_);
lean_inc_ref(v_a_2397_);
lean_inc(v_a_2396_);
lean_inc(v_a_2395_);
v___x_2429_ = l_Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f(v_arg_2425_, v_a_2395_, v_a_2396_, v_a_2397_, v_a_2398_, v_a_2399_, v_a_2400_, v_a_2401_, v_a_2402_, v_a_2403_, v_a_2404_);
if (lean_obj_tag(v___x_2429_) == 0)
{
lean_object* v_a_2430_; lean_object* v___x_2432_; uint8_t v_isShared_2433_; uint8_t v_isSharedCheck_2459_; 
v_a_2430_ = lean_ctor_get(v___x_2429_, 0);
v_isSharedCheck_2459_ = !lean_is_exclusive(v___x_2429_);
if (v_isSharedCheck_2459_ == 0)
{
v___x_2432_ = v___x_2429_;
v_isShared_2433_ = v_isSharedCheck_2459_;
goto v_resetjp_2431_;
}
else
{
lean_inc(v_a_2430_);
lean_dec(v___x_2429_);
v___x_2432_ = lean_box(0);
v_isShared_2433_ = v_isSharedCheck_2459_;
goto v_resetjp_2431_;
}
v_resetjp_2431_:
{
if (lean_obj_tag(v_a_2430_) == 1)
{
lean_object* v_val_2434_; uint8_t v___x_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; 
lean_del_object(v___x_2432_);
v_val_2434_ = lean_ctor_get(v_a_2430_, 0);
lean_inc(v_val_2434_);
lean_dec_ref(v_a_2430_);
v___x_2435_ = 0;
v___x_2436_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2436_, 0, v_val_2434_);
lean_ctor_set_uint8(v___x_2436_, sizeof(void*)*1, v___x_2435_);
v___x_2437_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv(v_e_2394_, v_arg_2422_, v_arg_2419_, v___x_2436_, v_a_2395_, v_a_2396_, v_a_2397_, v_a_2398_, v_a_2399_, v_a_2400_, v_a_2401_, v_a_2402_, v_a_2403_, v_a_2404_);
lean_dec_ref(v_arg_2422_);
if (lean_obj_tag(v___x_2437_) == 0)
{
lean_object* v___x_2439_; uint8_t v_isShared_2440_; uint8_t v_isSharedCheck_2445_; 
v_isSharedCheck_2445_ = !lean_is_exclusive(v___x_2437_);
if (v_isSharedCheck_2445_ == 0)
{
lean_object* v_unused_2446_; 
v_unused_2446_ = lean_ctor_get(v___x_2437_, 0);
lean_dec(v_unused_2446_);
v___x_2439_ = v___x_2437_;
v_isShared_2440_ = v_isSharedCheck_2445_;
goto v_resetjp_2438_;
}
else
{
lean_dec(v___x_2437_);
v___x_2439_ = lean_box(0);
v_isShared_2440_ = v_isSharedCheck_2445_;
goto v_resetjp_2438_;
}
v_resetjp_2438_:
{
lean_object* v___x_2441_; lean_object* v___x_2443_; 
v___x_2441_ = lean_box(v___x_2428_);
if (v_isShared_2440_ == 0)
{
lean_ctor_set(v___x_2439_, 0, v___x_2441_);
v___x_2443_ = v___x_2439_;
goto v_reusejp_2442_;
}
else
{
lean_object* v_reuseFailAlloc_2444_; 
v_reuseFailAlloc_2444_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2444_, 0, v___x_2441_);
v___x_2443_ = v_reuseFailAlloc_2444_;
goto v_reusejp_2442_;
}
v_reusejp_2442_:
{
return v___x_2443_;
}
}
}
else
{
lean_object* v_a_2447_; lean_object* v___x_2449_; uint8_t v_isShared_2450_; uint8_t v_isSharedCheck_2454_; 
v_a_2447_ = lean_ctor_get(v___x_2437_, 0);
v_isSharedCheck_2454_ = !lean_is_exclusive(v___x_2437_);
if (v_isSharedCheck_2454_ == 0)
{
v___x_2449_ = v___x_2437_;
v_isShared_2450_ = v_isSharedCheck_2454_;
goto v_resetjp_2448_;
}
else
{
lean_inc(v_a_2447_);
lean_dec(v___x_2437_);
v___x_2449_ = lean_box(0);
v_isShared_2450_ = v_isSharedCheck_2454_;
goto v_resetjp_2448_;
}
v_resetjp_2448_:
{
lean_object* v___x_2452_; 
if (v_isShared_2450_ == 0)
{
v___x_2452_ = v___x_2449_;
goto v_reusejp_2451_;
}
else
{
lean_object* v_reuseFailAlloc_2453_; 
v_reuseFailAlloc_2453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2453_, 0, v_a_2447_);
v___x_2452_ = v_reuseFailAlloc_2453_;
goto v_reusejp_2451_;
}
v_reusejp_2451_:
{
return v___x_2452_;
}
}
}
}
else
{
lean_object* v___x_2455_; lean_object* v___x_2457_; 
lean_dec(v_a_2430_);
lean_dec_ref(v_arg_2422_);
lean_dec_ref(v_arg_2419_);
lean_dec(v_a_2404_);
lean_dec_ref(v_a_2403_);
lean_dec(v_a_2402_);
lean_dec_ref(v_a_2401_);
lean_dec(v_a_2400_);
lean_dec_ref(v_a_2399_);
lean_dec(v_a_2398_);
lean_dec_ref(v_a_2397_);
lean_dec(v_a_2396_);
lean_dec(v_a_2395_);
lean_dec_ref(v_e_2394_);
v___x_2455_ = lean_box(v___x_2428_);
if (v_isShared_2433_ == 0)
{
lean_ctor_set(v___x_2432_, 0, v___x_2455_);
v___x_2457_ = v___x_2432_;
goto v_reusejp_2456_;
}
else
{
lean_object* v_reuseFailAlloc_2458_; 
v_reuseFailAlloc_2458_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2458_, 0, v___x_2455_);
v___x_2457_ = v_reuseFailAlloc_2458_;
goto v_reusejp_2456_;
}
v_reusejp_2456_:
{
return v___x_2457_;
}
}
}
}
else
{
lean_object* v_a_2460_; lean_object* v___x_2462_; uint8_t v_isShared_2463_; uint8_t v_isSharedCheck_2467_; 
lean_dec_ref(v_arg_2422_);
lean_dec_ref(v_arg_2419_);
lean_dec(v_a_2404_);
lean_dec_ref(v_a_2403_);
lean_dec(v_a_2402_);
lean_dec_ref(v_a_2401_);
lean_dec(v_a_2400_);
lean_dec_ref(v_a_2399_);
lean_dec(v_a_2398_);
lean_dec_ref(v_a_2397_);
lean_dec(v_a_2396_);
lean_dec(v_a_2395_);
lean_dec_ref(v_e_2394_);
v_a_2460_ = lean_ctor_get(v___x_2429_, 0);
v_isSharedCheck_2467_ = !lean_is_exclusive(v___x_2429_);
if (v_isSharedCheck_2467_ == 0)
{
v___x_2462_ = v___x_2429_;
v_isShared_2463_ = v_isSharedCheck_2467_;
goto v_resetjp_2461_;
}
else
{
lean_inc(v_a_2460_);
lean_dec(v___x_2429_);
v___x_2462_ = lean_box(0);
v_isShared_2463_ = v_isSharedCheck_2467_;
goto v_resetjp_2461_;
}
v_resetjp_2461_:
{
lean_object* v___x_2465_; 
if (v_isShared_2463_ == 0)
{
v___x_2465_ = v___x_2462_;
goto v_reusejp_2464_;
}
else
{
lean_object* v_reuseFailAlloc_2466_; 
v_reuseFailAlloc_2466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2466_, 0, v_a_2460_);
v___x_2465_ = v_reuseFailAlloc_2466_;
goto v_reusejp_2464_;
}
v_reusejp_2464_:
{
return v___x_2465_;
}
}
}
}
}
}
}
v___jp_2411_:
{
uint8_t v___x_2412_; lean_object* v___x_2413_; lean_object* v___x_2415_; 
v___x_2412_ = 0;
v___x_2413_ = lean_box(v___x_2412_);
if (v_isShared_2410_ == 0)
{
lean_ctor_set(v___x_2409_, 0, v___x_2413_);
v___x_2415_ = v___x_2409_;
goto v_reusejp_2414_;
}
else
{
lean_object* v_reuseFailAlloc_2416_; 
v_reuseFailAlloc_2416_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2416_, 0, v___x_2413_);
v___x_2415_ = v_reuseFailAlloc_2416_;
goto v_reusejp_2414_;
}
v_reusejp_2414_:
{
return v___x_2415_;
}
}
}
}
else
{
lean_object* v_a_2469_; lean_object* v___x_2471_; uint8_t v_isShared_2472_; uint8_t v_isSharedCheck_2476_; 
lean_dec(v_a_2404_);
lean_dec_ref(v_a_2403_);
lean_dec(v_a_2402_);
lean_dec_ref(v_a_2401_);
lean_dec(v_a_2400_);
lean_dec_ref(v_a_2399_);
lean_dec(v_a_2398_);
lean_dec_ref(v_a_2397_);
lean_dec(v_a_2396_);
lean_dec(v_a_2395_);
lean_dec_ref(v_e_2394_);
v_a_2469_ = lean_ctor_get(v___x_2406_, 0);
v_isSharedCheck_2476_ = !lean_is_exclusive(v___x_2406_);
if (v_isSharedCheck_2476_ == 0)
{
v___x_2471_ = v___x_2406_;
v_isShared_2472_ = v_isSharedCheck_2476_;
goto v_resetjp_2470_;
}
else
{
lean_inc(v_a_2469_);
lean_dec(v___x_2406_);
v___x_2471_ = lean_box(0);
v_isShared_2472_ = v_isSharedCheck_2476_;
goto v_resetjp_2470_;
}
v_resetjp_2470_:
{
lean_object* v___x_2474_; 
if (v_isShared_2472_ == 0)
{
v___x_2474_ = v___x_2471_;
goto v_reusejp_2473_;
}
else
{
lean_object* v_reuseFailAlloc_2475_; 
v_reuseFailAlloc_2475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2475_, 0, v_a_2469_);
v___x_2474_ = v_reuseFailAlloc_2475_;
goto v_reusejp_2473_;
}
v_reusejp_2473_:
{
return v___x_2474_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeInv___boxed(lean_object* v_e_2477_, lean_object* v_a_2478_, lean_object* v_a_2479_, lean_object* v_a_2480_, lean_object* v_a_2481_, lean_object* v_a_2482_, lean_object* v_a_2483_, lean_object* v_a_2484_, lean_object* v_a_2485_, lean_object* v_a_2486_, lean_object* v_a_2487_, lean_object* v_a_2488_){
_start:
{
lean_object* v_res_2489_; 
v_res_2489_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeInv(v_e_2477_, v_a_2478_, v_a_2479_, v_a_2480_, v_a_2481_, v_a_2482_, v_a_2483_, v_a_2484_, v_a_2485_, v_a_2486_, v_a_2487_);
return v_res_2489_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__1___redArg(lean_object* v_cls_2493_, lean_object* v___y_2494_){
_start:
{
lean_object* v_options_2496_; uint8_t v_hasTrace_2497_; 
v_options_2496_ = lean_ctor_get(v___y_2494_, 2);
v_hasTrace_2497_ = lean_ctor_get_uint8(v_options_2496_, sizeof(void*)*1);
if (v_hasTrace_2497_ == 0)
{
lean_object* v___x_2498_; lean_object* v___x_2499_; 
lean_dec(v_cls_2493_);
v___x_2498_ = lean_box(v_hasTrace_2497_);
v___x_2499_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2499_, 0, v___x_2498_);
return v___x_2499_;
}
else
{
lean_object* v_inheritedTraceOptions_2500_; lean_object* v___x_2501_; lean_object* v___x_2502_; uint8_t v___x_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; 
v_inheritedTraceOptions_2500_ = lean_ctor_get(v___y_2494_, 13);
v___x_2501_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__1___redArg___closed__1));
v___x_2502_ = l_Lean_Name_append(v___x_2501_, v_cls_2493_);
v___x_2503_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2500_, v_options_2496_, v___x_2502_);
lean_dec(v___x_2502_);
v___x_2504_ = lean_box(v___x_2503_);
v___x_2505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2505_, 0, v___x_2504_);
return v___x_2505_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__1___redArg___boxed(lean_object* v_cls_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_){
_start:
{
lean_object* v_res_2509_; 
v_res_2509_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__1___redArg(v_cls_2506_, v___y_2507_);
lean_dec_ref(v___y_2507_);
return v_res_2509_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__1(lean_object* v_cls_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_, lean_object* v___y_2513_, lean_object* v___y_2514_, lean_object* v___y_2515_, lean_object* v___y_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_){
_start:
{
lean_object* v___x_2523_; 
v___x_2523_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__1___redArg(v_cls_2510_, v___y_2520_);
return v___x_2523_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__1___boxed(lean_object* v_cls_2524_, lean_object* v___y_2525_, lean_object* v___y_2526_, lean_object* v___y_2527_, lean_object* v___y_2528_, lean_object* v___y_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_, lean_object* v___y_2532_, lean_object* v___y_2533_, lean_object* v___y_2534_, lean_object* v___y_2535_, lean_object* v___y_2536_){
_start:
{
lean_object* v_res_2537_; 
v_res_2537_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__1(v_cls_2524_, v___y_2525_, v___y_2526_, v___y_2527_, v___y_2528_, v___y_2529_, v___y_2530_, v___y_2531_, v___y_2532_, v___y_2533_, v___y_2534_, v___y_2535_);
lean_dec(v___y_2535_);
lean_dec_ref(v___y_2534_);
lean_dec(v___y_2533_);
lean_dec_ref(v___y_2532_);
lean_dec(v___y_2531_);
lean_dec_ref(v___y_2530_);
lean_dec(v___y_2529_);
lean_dec_ref(v___y_2528_);
lean_dec(v___y_2527_);
lean_dec(v___y_2526_);
lean_dec_ref(v___y_2525_);
return v_res_2537_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__3___redArg(lean_object* v_cls_2538_, lean_object* v___y_2539_){
_start:
{
lean_object* v_options_2541_; uint8_t v_hasTrace_2542_; 
v_options_2541_ = lean_ctor_get(v___y_2539_, 2);
v_hasTrace_2542_ = lean_ctor_get_uint8(v_options_2541_, sizeof(void*)*1);
if (v_hasTrace_2542_ == 0)
{
lean_object* v___x_2543_; lean_object* v___x_2544_; 
lean_dec(v_cls_2538_);
v___x_2543_ = lean_box(v_hasTrace_2542_);
v___x_2544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2544_, 0, v___x_2543_);
return v___x_2544_;
}
else
{
lean_object* v_inheritedTraceOptions_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; uint8_t v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; 
v_inheritedTraceOptions_2545_ = lean_ctor_get(v___y_2539_, 13);
v___x_2546_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__1___redArg___closed__1));
v___x_2547_ = l_Lean_Name_append(v___x_2546_, v_cls_2538_);
v___x_2548_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2545_, v_options_2541_, v___x_2547_);
lean_dec(v___x_2547_);
v___x_2549_ = lean_box(v___x_2548_);
v___x_2550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2550_, 0, v___x_2549_);
return v___x_2550_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__3___redArg___boxed(lean_object* v_cls_2551_, lean_object* v___y_2552_, lean_object* v___y_2553_){
_start:
{
lean_object* v_res_2554_; 
v_res_2554_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__3___redArg(v_cls_2551_, v___y_2552_);
lean_dec_ref(v___y_2552_);
return v_res_2554_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__3(lean_object* v_cls_2555_, lean_object* v___y_2556_, lean_object* v___y_2557_, lean_object* v___y_2558_, lean_object* v___y_2559_, lean_object* v___y_2560_, lean_object* v___y_2561_, lean_object* v___y_2562_, lean_object* v___y_2563_, lean_object* v___y_2564_, lean_object* v___y_2565_, lean_object* v___y_2566_){
_start:
{
lean_object* v___x_2568_; 
v___x_2568_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__3___redArg(v_cls_2555_, v___y_2565_);
return v___x_2568_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__3___boxed(lean_object* v_cls_2569_, lean_object* v___y_2570_, lean_object* v___y_2571_, lean_object* v___y_2572_, lean_object* v___y_2573_, lean_object* v___y_2574_, lean_object* v___y_2575_, lean_object* v___y_2576_, lean_object* v___y_2577_, lean_object* v___y_2578_, lean_object* v___y_2579_, lean_object* v___y_2580_, lean_object* v___y_2581_){
_start:
{
lean_object* v_res_2582_; 
v_res_2582_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__3(v_cls_2569_, v___y_2570_, v___y_2571_, v___y_2572_, v___y_2573_, v___y_2574_, v___y_2575_, v___y_2576_, v___y_2577_, v___y_2578_, v___y_2579_, v___y_2580_);
lean_dec(v___y_2580_);
lean_dec_ref(v___y_2579_);
lean_dec(v___y_2578_);
lean_dec_ref(v___y_2577_);
lean_dec(v___y_2576_);
lean_dec_ref(v___y_2575_);
lean_dec(v___y_2574_);
lean_dec_ref(v___y_2573_);
lean_dec(v___y_2572_);
lean_dec(v___y_2571_);
lean_dec(v___y_2570_);
return v_res_2582_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__5___redArg(lean_object* v_cls_2583_, lean_object* v___y_2584_){
_start:
{
lean_object* v_options_2586_; uint8_t v_hasTrace_2587_; 
v_options_2586_ = lean_ctor_get(v___y_2584_, 2);
v_hasTrace_2587_ = lean_ctor_get_uint8(v_options_2586_, sizeof(void*)*1);
if (v_hasTrace_2587_ == 0)
{
lean_object* v___x_2588_; lean_object* v___x_2589_; 
lean_dec(v_cls_2583_);
v___x_2588_ = lean_box(v_hasTrace_2587_);
v___x_2589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2589_, 0, v___x_2588_);
return v___x_2589_;
}
else
{
lean_object* v_inheritedTraceOptions_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; uint8_t v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; 
v_inheritedTraceOptions_2590_ = lean_ctor_get(v___y_2584_, 13);
v___x_2591_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__1___redArg___closed__1));
v___x_2592_ = l_Lean_Name_append(v___x_2591_, v_cls_2583_);
v___x_2593_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2590_, v_options_2586_, v___x_2592_);
lean_dec(v___x_2592_);
v___x_2594_ = lean_box(v___x_2593_);
v___x_2595_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2595_, 0, v___x_2594_);
return v___x_2595_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__5___redArg___boxed(lean_object* v_cls_2596_, lean_object* v___y_2597_, lean_object* v___y_2598_){
_start:
{
lean_object* v_res_2599_; 
v_res_2599_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__5___redArg(v_cls_2596_, v___y_2597_);
lean_dec_ref(v___y_2597_);
return v_res_2599_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__5(lean_object* v_cls_2600_, lean_object* v___y_2601_, lean_object* v___y_2602_, lean_object* v___y_2603_, lean_object* v___y_2604_, lean_object* v___y_2605_, lean_object* v___y_2606_, lean_object* v___y_2607_, lean_object* v___y_2608_, lean_object* v___y_2609_, lean_object* v___y_2610_, lean_object* v___y_2611_){
_start:
{
lean_object* v___x_2613_; 
v___x_2613_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__5___redArg(v_cls_2600_, v___y_2610_);
return v___x_2613_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__5___boxed(lean_object* v_cls_2614_, lean_object* v___y_2615_, lean_object* v___y_2616_, lean_object* v___y_2617_, lean_object* v___y_2618_, lean_object* v___y_2619_, lean_object* v___y_2620_, lean_object* v___y_2621_, lean_object* v___y_2622_, lean_object* v___y_2623_, lean_object* v___y_2624_, lean_object* v___y_2625_, lean_object* v___y_2626_){
_start:
{
lean_object* v_res_2627_; 
v_res_2627_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__5(v_cls_2614_, v___y_2615_, v___y_2616_, v___y_2617_, v___y_2618_, v___y_2619_, v___y_2620_, v___y_2621_, v___y_2622_, v___y_2623_, v___y_2624_, v___y_2625_);
lean_dec(v___y_2625_);
lean_dec_ref(v___y_2624_);
lean_dec(v___y_2623_);
lean_dec_ref(v___y_2622_);
lean_dec(v___y_2621_);
lean_dec_ref(v___y_2620_);
lean_dec(v___y_2619_);
lean_dec_ref(v___y_2618_);
lean_dec(v___y_2617_);
lean_dec(v___y_2616_);
lean_dec(v___y_2615_);
return v_res_2627_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__7___redArg(lean_object* v_cls_2628_, lean_object* v___y_2629_){
_start:
{
lean_object* v_options_2631_; uint8_t v_hasTrace_2632_; 
v_options_2631_ = lean_ctor_get(v___y_2629_, 2);
v_hasTrace_2632_ = lean_ctor_get_uint8(v_options_2631_, sizeof(void*)*1);
if (v_hasTrace_2632_ == 0)
{
lean_object* v___x_2633_; lean_object* v___x_2634_; 
lean_dec(v_cls_2628_);
v___x_2633_ = lean_box(v_hasTrace_2632_);
v___x_2634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2634_, 0, v___x_2633_);
return v___x_2634_;
}
else
{
lean_object* v_inheritedTraceOptions_2635_; lean_object* v___x_2636_; lean_object* v___x_2637_; uint8_t v___x_2638_; lean_object* v___x_2639_; lean_object* v___x_2640_; 
v_inheritedTraceOptions_2635_ = lean_ctor_get(v___y_2629_, 13);
v___x_2636_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__1___redArg___closed__1));
v___x_2637_ = l_Lean_Name_append(v___x_2636_, v_cls_2628_);
v___x_2638_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2635_, v_options_2631_, v___x_2637_);
lean_dec(v___x_2637_);
v___x_2639_ = lean_box(v___x_2638_);
v___x_2640_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2640_, 0, v___x_2639_);
return v___x_2640_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__7___redArg___boxed(lean_object* v_cls_2641_, lean_object* v___y_2642_, lean_object* v___y_2643_){
_start:
{
lean_object* v_res_2644_; 
v_res_2644_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__7___redArg(v_cls_2641_, v___y_2642_);
lean_dec_ref(v___y_2642_);
return v_res_2644_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__7(lean_object* v_cls_2645_, lean_object* v___y_2646_, lean_object* v___y_2647_, lean_object* v___y_2648_, lean_object* v___y_2649_, lean_object* v___y_2650_, lean_object* v___y_2651_, lean_object* v___y_2652_, lean_object* v___y_2653_, lean_object* v___y_2654_, lean_object* v___y_2655_, lean_object* v___y_2656_){
_start:
{
lean_object* v___x_2658_; 
v___x_2658_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__7___redArg(v_cls_2645_, v___y_2655_);
return v___x_2658_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__7___boxed(lean_object* v_cls_2659_, lean_object* v___y_2660_, lean_object* v___y_2661_, lean_object* v___y_2662_, lean_object* v___y_2663_, lean_object* v___y_2664_, lean_object* v___y_2665_, lean_object* v___y_2666_, lean_object* v___y_2667_, lean_object* v___y_2668_, lean_object* v___y_2669_, lean_object* v___y_2670_, lean_object* v___y_2671_){
_start:
{
lean_object* v_res_2672_; 
v_res_2672_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__7(v_cls_2659_, v___y_2660_, v___y_2661_, v___y_2662_, v___y_2663_, v___y_2664_, v___y_2665_, v___y_2666_, v___y_2667_, v___y_2668_, v___y_2669_, v___y_2670_);
lean_dec(v___y_2670_);
lean_dec_ref(v___y_2669_);
lean_dec(v___y_2668_);
lean_dec_ref(v___y_2667_);
lean_dec(v___y_2666_);
lean_dec_ref(v___y_2665_);
lean_dec(v___y_2664_);
lean_dec_ref(v___y_2663_);
lean_dec(v___y_2662_);
lean_dec(v___y_2661_);
lean_dec(v___y_2660_);
return v_res_2672_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0_spec__5_spec__10___redArg(lean_object* v_x_2673_, lean_object* v_x_2674_, lean_object* v_x_2675_, lean_object* v_x_2676_){
_start:
{
lean_object* v_ks_2677_; lean_object* v_vs_2678_; lean_object* v___x_2680_; uint8_t v_isShared_2681_; uint8_t v_isSharedCheck_2702_; 
v_ks_2677_ = lean_ctor_get(v_x_2673_, 0);
v_vs_2678_ = lean_ctor_get(v_x_2673_, 1);
v_isSharedCheck_2702_ = !lean_is_exclusive(v_x_2673_);
if (v_isSharedCheck_2702_ == 0)
{
v___x_2680_ = v_x_2673_;
v_isShared_2681_ = v_isSharedCheck_2702_;
goto v_resetjp_2679_;
}
else
{
lean_inc(v_vs_2678_);
lean_inc(v_ks_2677_);
lean_dec(v_x_2673_);
v___x_2680_ = lean_box(0);
v_isShared_2681_ = v_isSharedCheck_2702_;
goto v_resetjp_2679_;
}
v_resetjp_2679_:
{
lean_object* v___x_2682_; uint8_t v___x_2683_; 
v___x_2682_ = lean_array_get_size(v_ks_2677_);
v___x_2683_ = lean_nat_dec_lt(v_x_2674_, v___x_2682_);
if (v___x_2683_ == 0)
{
lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2687_; 
lean_dec(v_x_2674_);
v___x_2684_ = lean_array_push(v_ks_2677_, v_x_2675_);
v___x_2685_ = lean_array_push(v_vs_2678_, v_x_2676_);
if (v_isShared_2681_ == 0)
{
lean_ctor_set(v___x_2680_, 1, v___x_2685_);
lean_ctor_set(v___x_2680_, 0, v___x_2684_);
v___x_2687_ = v___x_2680_;
goto v_reusejp_2686_;
}
else
{
lean_object* v_reuseFailAlloc_2688_; 
v_reuseFailAlloc_2688_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2688_, 0, v___x_2684_);
lean_ctor_set(v_reuseFailAlloc_2688_, 1, v___x_2685_);
v___x_2687_ = v_reuseFailAlloc_2688_;
goto v_reusejp_2686_;
}
v_reusejp_2686_:
{
return v___x_2687_;
}
}
else
{
lean_object* v_k_x27_2689_; uint8_t v___x_2690_; 
v_k_x27_2689_ = lean_array_fget_borrowed(v_ks_2677_, v_x_2674_);
v___x_2690_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_2675_, v_k_x27_2689_);
if (v___x_2690_ == 0)
{
lean_object* v___x_2692_; 
if (v_isShared_2681_ == 0)
{
v___x_2692_ = v___x_2680_;
goto v_reusejp_2691_;
}
else
{
lean_object* v_reuseFailAlloc_2696_; 
v_reuseFailAlloc_2696_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2696_, 0, v_ks_2677_);
lean_ctor_set(v_reuseFailAlloc_2696_, 1, v_vs_2678_);
v___x_2692_ = v_reuseFailAlloc_2696_;
goto v_reusejp_2691_;
}
v_reusejp_2691_:
{
lean_object* v___x_2693_; lean_object* v___x_2694_; 
v___x_2693_ = lean_unsigned_to_nat(1u);
v___x_2694_ = lean_nat_add(v_x_2674_, v___x_2693_);
lean_dec(v_x_2674_);
v_x_2673_ = v___x_2692_;
v_x_2674_ = v___x_2694_;
goto _start;
}
}
else
{
lean_object* v___x_2697_; lean_object* v___x_2698_; lean_object* v___x_2700_; 
v___x_2697_ = lean_array_fset(v_ks_2677_, v_x_2674_, v_x_2675_);
v___x_2698_ = lean_array_fset(v_vs_2678_, v_x_2674_, v_x_2676_);
lean_dec(v_x_2674_);
if (v_isShared_2681_ == 0)
{
lean_ctor_set(v___x_2680_, 1, v___x_2698_);
lean_ctor_set(v___x_2680_, 0, v___x_2697_);
v___x_2700_ = v___x_2680_;
goto v_reusejp_2699_;
}
else
{
lean_object* v_reuseFailAlloc_2701_; 
v_reuseFailAlloc_2701_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2701_, 0, v___x_2697_);
lean_ctor_set(v_reuseFailAlloc_2701_, 1, v___x_2698_);
v___x_2700_ = v_reuseFailAlloc_2701_;
goto v_reusejp_2699_;
}
v_reusejp_2699_:
{
return v___x_2700_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0_spec__5___redArg(lean_object* v_n_2703_, lean_object* v_k_2704_, lean_object* v_v_2705_){
_start:
{
lean_object* v___x_2706_; lean_object* v___x_2707_; 
v___x_2706_ = lean_unsigned_to_nat(0u);
v___x_2707_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0_spec__5_spec__10___redArg(v_n_2703_, v___x_2706_, v_k_2704_, v_v_2705_);
return v___x_2707_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0___redArg(lean_object* v_x_2708_, size_t v_x_2709_, size_t v_x_2710_, lean_object* v_x_2711_, lean_object* v_x_2712_){
_start:
{
if (lean_obj_tag(v_x_2708_) == 0)
{
lean_object* v_es_2713_; size_t v___x_2714_; size_t v___x_2715_; size_t v___x_2716_; size_t v___x_2717_; lean_object* v_j_2718_; lean_object* v___x_2719_; uint8_t v___x_2720_; 
v_es_2713_ = lean_ctor_get(v_x_2708_, 0);
v___x_2714_ = ((size_t)5ULL);
v___x_2715_ = ((size_t)1ULL);
v___x_2716_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg___closed__1);
v___x_2717_ = lean_usize_land(v_x_2709_, v___x_2716_);
v_j_2718_ = lean_usize_to_nat(v___x_2717_);
v___x_2719_ = lean_array_get_size(v_es_2713_);
v___x_2720_ = lean_nat_dec_lt(v_j_2718_, v___x_2719_);
if (v___x_2720_ == 0)
{
lean_dec(v_j_2718_);
lean_dec(v_x_2712_);
lean_dec_ref(v_x_2711_);
return v_x_2708_;
}
else
{
lean_object* v___x_2722_; uint8_t v_isShared_2723_; uint8_t v_isSharedCheck_2757_; 
lean_inc_ref(v_es_2713_);
v_isSharedCheck_2757_ = !lean_is_exclusive(v_x_2708_);
if (v_isSharedCheck_2757_ == 0)
{
lean_object* v_unused_2758_; 
v_unused_2758_ = lean_ctor_get(v_x_2708_, 0);
lean_dec(v_unused_2758_);
v___x_2722_ = v_x_2708_;
v_isShared_2723_ = v_isSharedCheck_2757_;
goto v_resetjp_2721_;
}
else
{
lean_dec(v_x_2708_);
v___x_2722_ = lean_box(0);
v_isShared_2723_ = v_isSharedCheck_2757_;
goto v_resetjp_2721_;
}
v_resetjp_2721_:
{
lean_object* v_v_2724_; lean_object* v___x_2725_; lean_object* v_xs_x27_2726_; lean_object* v___y_2728_; 
v_v_2724_ = lean_array_fget(v_es_2713_, v_j_2718_);
v___x_2725_ = lean_box(0);
v_xs_x27_2726_ = lean_array_fset(v_es_2713_, v_j_2718_, v___x_2725_);
switch(lean_obj_tag(v_v_2724_))
{
case 0:
{
lean_object* v_key_2733_; lean_object* v_val_2734_; lean_object* v___x_2736_; uint8_t v_isShared_2737_; uint8_t v_isSharedCheck_2744_; 
v_key_2733_ = lean_ctor_get(v_v_2724_, 0);
v_val_2734_ = lean_ctor_get(v_v_2724_, 1);
v_isSharedCheck_2744_ = !lean_is_exclusive(v_v_2724_);
if (v_isSharedCheck_2744_ == 0)
{
v___x_2736_ = v_v_2724_;
v_isShared_2737_ = v_isSharedCheck_2744_;
goto v_resetjp_2735_;
}
else
{
lean_inc(v_val_2734_);
lean_inc(v_key_2733_);
lean_dec(v_v_2724_);
v___x_2736_ = lean_box(0);
v_isShared_2737_ = v_isSharedCheck_2744_;
goto v_resetjp_2735_;
}
v_resetjp_2735_:
{
uint8_t v___x_2738_; 
v___x_2738_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_2711_, v_key_2733_);
if (v___x_2738_ == 0)
{
lean_object* v___x_2739_; lean_object* v___x_2740_; 
lean_del_object(v___x_2736_);
v___x_2739_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_2733_, v_val_2734_, v_x_2711_, v_x_2712_);
v___x_2740_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2740_, 0, v___x_2739_);
v___y_2728_ = v___x_2740_;
goto v___jp_2727_;
}
else
{
lean_object* v___x_2742_; 
lean_dec(v_val_2734_);
lean_dec(v_key_2733_);
if (v_isShared_2737_ == 0)
{
lean_ctor_set(v___x_2736_, 1, v_x_2712_);
lean_ctor_set(v___x_2736_, 0, v_x_2711_);
v___x_2742_ = v___x_2736_;
goto v_reusejp_2741_;
}
else
{
lean_object* v_reuseFailAlloc_2743_; 
v_reuseFailAlloc_2743_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2743_, 0, v_x_2711_);
lean_ctor_set(v_reuseFailAlloc_2743_, 1, v_x_2712_);
v___x_2742_ = v_reuseFailAlloc_2743_;
goto v_reusejp_2741_;
}
v_reusejp_2741_:
{
v___y_2728_ = v___x_2742_;
goto v___jp_2727_;
}
}
}
}
case 1:
{
lean_object* v_node_2745_; lean_object* v___x_2747_; uint8_t v_isShared_2748_; uint8_t v_isSharedCheck_2755_; 
v_node_2745_ = lean_ctor_get(v_v_2724_, 0);
v_isSharedCheck_2755_ = !lean_is_exclusive(v_v_2724_);
if (v_isSharedCheck_2755_ == 0)
{
v___x_2747_ = v_v_2724_;
v_isShared_2748_ = v_isSharedCheck_2755_;
goto v_resetjp_2746_;
}
else
{
lean_inc(v_node_2745_);
lean_dec(v_v_2724_);
v___x_2747_ = lean_box(0);
v_isShared_2748_ = v_isSharedCheck_2755_;
goto v_resetjp_2746_;
}
v_resetjp_2746_:
{
size_t v___x_2749_; size_t v___x_2750_; lean_object* v___x_2751_; lean_object* v___x_2753_; 
v___x_2749_ = lean_usize_shift_right(v_x_2709_, v___x_2714_);
v___x_2750_ = lean_usize_add(v_x_2710_, v___x_2715_);
v___x_2751_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0___redArg(v_node_2745_, v___x_2749_, v___x_2750_, v_x_2711_, v_x_2712_);
if (v_isShared_2748_ == 0)
{
lean_ctor_set(v___x_2747_, 0, v___x_2751_);
v___x_2753_ = v___x_2747_;
goto v_reusejp_2752_;
}
else
{
lean_object* v_reuseFailAlloc_2754_; 
v_reuseFailAlloc_2754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2754_, 0, v___x_2751_);
v___x_2753_ = v_reuseFailAlloc_2754_;
goto v_reusejp_2752_;
}
v_reusejp_2752_:
{
v___y_2728_ = v___x_2753_;
goto v___jp_2727_;
}
}
}
default: 
{
lean_object* v___x_2756_; 
v___x_2756_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2756_, 0, v_x_2711_);
lean_ctor_set(v___x_2756_, 1, v_x_2712_);
v___y_2728_ = v___x_2756_;
goto v___jp_2727_;
}
}
v___jp_2727_:
{
lean_object* v___x_2729_; lean_object* v___x_2731_; 
v___x_2729_ = lean_array_fset(v_xs_x27_2726_, v_j_2718_, v___y_2728_);
lean_dec(v_j_2718_);
if (v_isShared_2723_ == 0)
{
lean_ctor_set(v___x_2722_, 0, v___x_2729_);
v___x_2731_ = v___x_2722_;
goto v_reusejp_2730_;
}
else
{
lean_object* v_reuseFailAlloc_2732_; 
v_reuseFailAlloc_2732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2732_, 0, v___x_2729_);
v___x_2731_ = v_reuseFailAlloc_2732_;
goto v_reusejp_2730_;
}
v_reusejp_2730_:
{
return v___x_2731_;
}
}
}
}
}
else
{
lean_object* v_ks_2759_; lean_object* v_vs_2760_; lean_object* v___x_2762_; uint8_t v_isShared_2763_; uint8_t v_isSharedCheck_2780_; 
v_ks_2759_ = lean_ctor_get(v_x_2708_, 0);
v_vs_2760_ = lean_ctor_get(v_x_2708_, 1);
v_isSharedCheck_2780_ = !lean_is_exclusive(v_x_2708_);
if (v_isSharedCheck_2780_ == 0)
{
v___x_2762_ = v_x_2708_;
v_isShared_2763_ = v_isSharedCheck_2780_;
goto v_resetjp_2761_;
}
else
{
lean_inc(v_vs_2760_);
lean_inc(v_ks_2759_);
lean_dec(v_x_2708_);
v___x_2762_ = lean_box(0);
v_isShared_2763_ = v_isSharedCheck_2780_;
goto v_resetjp_2761_;
}
v_resetjp_2761_:
{
lean_object* v___x_2765_; 
if (v_isShared_2763_ == 0)
{
v___x_2765_ = v___x_2762_;
goto v_reusejp_2764_;
}
else
{
lean_object* v_reuseFailAlloc_2779_; 
v_reuseFailAlloc_2779_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2779_, 0, v_ks_2759_);
lean_ctor_set(v_reuseFailAlloc_2779_, 1, v_vs_2760_);
v___x_2765_ = v_reuseFailAlloc_2779_;
goto v_reusejp_2764_;
}
v_reusejp_2764_:
{
lean_object* v_newNode_2766_; uint8_t v___y_2768_; size_t v___x_2774_; uint8_t v___x_2775_; 
v_newNode_2766_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0_spec__5___redArg(v___x_2765_, v_x_2711_, v_x_2712_);
v___x_2774_ = ((size_t)7ULL);
v___x_2775_ = lean_usize_dec_le(v___x_2774_, v_x_2710_);
if (v___x_2775_ == 0)
{
lean_object* v___x_2776_; lean_object* v___x_2777_; uint8_t v___x_2778_; 
v___x_2776_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2766_);
v___x_2777_ = lean_unsigned_to_nat(4u);
v___x_2778_ = lean_nat_dec_lt(v___x_2776_, v___x_2777_);
lean_dec(v___x_2776_);
v___y_2768_ = v___x_2778_;
goto v___jp_2767_;
}
else
{
v___y_2768_ = v___x_2775_;
goto v___jp_2767_;
}
v___jp_2767_:
{
if (v___y_2768_ == 0)
{
lean_object* v_ks_2769_; lean_object* v_vs_2770_; lean_object* v___x_2771_; lean_object* v___x_2772_; lean_object* v___x_2773_; 
v_ks_2769_ = lean_ctor_get(v_newNode_2766_, 0);
lean_inc_ref(v_ks_2769_);
v_vs_2770_ = lean_ctor_get(v_newNode_2766_, 1);
lean_inc_ref(v_vs_2770_);
lean_dec_ref(v_newNode_2766_);
v___x_2771_ = lean_unsigned_to_nat(0u);
v___x_2772_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg___closed__2);
v___x_2773_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0_spec__6___redArg(v_x_2710_, v_ks_2769_, v_vs_2770_, v___x_2771_, v___x_2772_);
lean_dec_ref(v_vs_2770_);
lean_dec_ref(v_ks_2769_);
return v___x_2773_;
}
else
{
return v_newNode_2766_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0_spec__6___redArg(size_t v_depth_2781_, lean_object* v_keys_2782_, lean_object* v_vals_2783_, lean_object* v_i_2784_, lean_object* v_entries_2785_){
_start:
{
lean_object* v___x_2786_; uint8_t v___x_2787_; 
v___x_2786_ = lean_array_get_size(v_keys_2782_);
v___x_2787_ = lean_nat_dec_lt(v_i_2784_, v___x_2786_);
if (v___x_2787_ == 0)
{
lean_dec(v_i_2784_);
return v_entries_2785_;
}
else
{
lean_object* v_k_2788_; lean_object* v_v_2789_; uint64_t v___x_2790_; size_t v_h_2791_; size_t v___x_2792_; lean_object* v___x_2793_; size_t v___x_2794_; size_t v___x_2795_; size_t v___x_2796_; size_t v_h_2797_; lean_object* v___x_2798_; lean_object* v___x_2799_; 
v_k_2788_ = lean_array_fget_borrowed(v_keys_2782_, v_i_2784_);
v_v_2789_ = lean_array_fget_borrowed(v_vals_2783_, v_i_2784_);
v___x_2790_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_k_2788_);
v_h_2791_ = lean_uint64_to_usize(v___x_2790_);
v___x_2792_ = ((size_t)5ULL);
v___x_2793_ = lean_unsigned_to_nat(1u);
v___x_2794_ = ((size_t)1ULL);
v___x_2795_ = lean_usize_sub(v_depth_2781_, v___x_2794_);
v___x_2796_ = lean_usize_mul(v___x_2792_, v___x_2795_);
v_h_2797_ = lean_usize_shift_right(v_h_2791_, v___x_2796_);
v___x_2798_ = lean_nat_add(v_i_2784_, v___x_2793_);
lean_dec(v_i_2784_);
lean_inc(v_v_2789_);
lean_inc(v_k_2788_);
v___x_2799_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0___redArg(v_entries_2785_, v_h_2797_, v_depth_2781_, v_k_2788_, v_v_2789_);
v_i_2784_ = v___x_2798_;
v_entries_2785_ = v___x_2799_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0_spec__6___redArg___boxed(lean_object* v_depth_2801_, lean_object* v_keys_2802_, lean_object* v_vals_2803_, lean_object* v_i_2804_, lean_object* v_entries_2805_){
_start:
{
size_t v_depth_boxed_2806_; lean_object* v_res_2807_; 
v_depth_boxed_2806_ = lean_unbox_usize(v_depth_2801_);
lean_dec(v_depth_2801_);
v_res_2807_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0_spec__6___redArg(v_depth_boxed_2806_, v_keys_2802_, v_vals_2803_, v_i_2804_, v_entries_2805_);
lean_dec_ref(v_vals_2803_);
lean_dec_ref(v_keys_2802_);
return v_res_2807_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0___redArg___boxed(lean_object* v_x_2808_, lean_object* v_x_2809_, lean_object* v_x_2810_, lean_object* v_x_2811_, lean_object* v_x_2812_){
_start:
{
size_t v_x_204459__boxed_2813_; size_t v_x_204460__boxed_2814_; lean_object* v_res_2815_; 
v_x_204459__boxed_2813_ = lean_unbox_usize(v_x_2809_);
lean_dec(v_x_2809_);
v_x_204460__boxed_2814_ = lean_unbox_usize(v_x_2810_);
lean_dec(v_x_2810_);
v_res_2815_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0___redArg(v_x_2808_, v_x_204459__boxed_2813_, v_x_204460__boxed_2814_, v_x_2811_, v_x_2812_);
return v_res_2815_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0___redArg(lean_object* v_x_2816_, lean_object* v_x_2817_, lean_object* v_x_2818_){
_start:
{
uint64_t v___x_2819_; size_t v___x_2820_; size_t v___x_2821_; lean_object* v___x_2822_; 
v___x_2819_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_2817_);
v___x_2820_ = lean_uint64_to_usize(v___x_2819_);
v___x_2821_ = ((size_t)1ULL);
v___x_2822_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0___redArg(v_x_2816_, v___x_2820_, v___x_2821_, v_x_2817_, v_x_2818_);
return v___x_2822_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_internalize___lam__0(lean_object* v_e_2823_, lean_object* v_val_2824_, lean_object* v_s_2825_){
_start:
{
lean_object* v_toRing_2826_; lean_object* v_invFn_x3f_2827_; lean_object* v_semiringId_x3f_2828_; lean_object* v_commSemiringInst_2829_; lean_object* v_commRingInst_2830_; lean_object* v_noZeroDivInst_x3f_2831_; lean_object* v_fieldInst_x3f_2832_; lean_object* v_denoteEntries_2833_; lean_object* v_nextId_2834_; lean_object* v_steps_2835_; lean_object* v_queue_2836_; lean_object* v_basis_2837_; lean_object* v_diseqs_2838_; uint8_t v_recheck_2839_; lean_object* v_invSet_2840_; lean_object* v_numEq0_x3f_2841_; uint8_t v_numEq0Updated_2842_; lean_object* v___x_2844_; uint8_t v_isShared_2845_; uint8_t v_isSharedCheck_2876_; 
v_toRing_2826_ = lean_ctor_get(v_s_2825_, 0);
v_invFn_x3f_2827_ = lean_ctor_get(v_s_2825_, 1);
v_semiringId_x3f_2828_ = lean_ctor_get(v_s_2825_, 2);
v_commSemiringInst_2829_ = lean_ctor_get(v_s_2825_, 3);
v_commRingInst_2830_ = lean_ctor_get(v_s_2825_, 4);
v_noZeroDivInst_x3f_2831_ = lean_ctor_get(v_s_2825_, 5);
v_fieldInst_x3f_2832_ = lean_ctor_get(v_s_2825_, 6);
v_denoteEntries_2833_ = lean_ctor_get(v_s_2825_, 7);
v_nextId_2834_ = lean_ctor_get(v_s_2825_, 8);
v_steps_2835_ = lean_ctor_get(v_s_2825_, 9);
v_queue_2836_ = lean_ctor_get(v_s_2825_, 10);
v_basis_2837_ = lean_ctor_get(v_s_2825_, 11);
v_diseqs_2838_ = lean_ctor_get(v_s_2825_, 12);
v_recheck_2839_ = lean_ctor_get_uint8(v_s_2825_, sizeof(void*)*15);
v_invSet_2840_ = lean_ctor_get(v_s_2825_, 13);
v_numEq0_x3f_2841_ = lean_ctor_get(v_s_2825_, 14);
v_numEq0Updated_2842_ = lean_ctor_get_uint8(v_s_2825_, sizeof(void*)*15 + 1);
v_isSharedCheck_2876_ = !lean_is_exclusive(v_s_2825_);
if (v_isSharedCheck_2876_ == 0)
{
v___x_2844_ = v_s_2825_;
v_isShared_2845_ = v_isSharedCheck_2876_;
goto v_resetjp_2843_;
}
else
{
lean_inc(v_numEq0_x3f_2841_);
lean_inc(v_invSet_2840_);
lean_inc(v_diseqs_2838_);
lean_inc(v_basis_2837_);
lean_inc(v_queue_2836_);
lean_inc(v_steps_2835_);
lean_inc(v_nextId_2834_);
lean_inc(v_denoteEntries_2833_);
lean_inc(v_fieldInst_x3f_2832_);
lean_inc(v_noZeroDivInst_x3f_2831_);
lean_inc(v_commRingInst_2830_);
lean_inc(v_commSemiringInst_2829_);
lean_inc(v_semiringId_x3f_2828_);
lean_inc(v_invFn_x3f_2827_);
lean_inc(v_toRing_2826_);
lean_dec(v_s_2825_);
v___x_2844_ = lean_box(0);
v_isShared_2845_ = v_isSharedCheck_2876_;
goto v_resetjp_2843_;
}
v_resetjp_2843_:
{
lean_object* v_id_2846_; lean_object* v_type_2847_; lean_object* v_u_2848_; lean_object* v_ringInst_2849_; lean_object* v_semiringInst_2850_; lean_object* v_charInst_x3f_2851_; lean_object* v_addFn_x3f_2852_; lean_object* v_mulFn_x3f_2853_; lean_object* v_subFn_x3f_2854_; lean_object* v_negFn_x3f_2855_; lean_object* v_powFn_x3f_2856_; lean_object* v_intCastFn_x3f_2857_; lean_object* v_natCastFn_x3f_2858_; lean_object* v_one_x3f_2859_; lean_object* v_vars_2860_; lean_object* v_varMap_2861_; lean_object* v_denote_2862_; lean_object* v___x_2864_; uint8_t v_isShared_2865_; uint8_t v_isSharedCheck_2875_; 
v_id_2846_ = lean_ctor_get(v_toRing_2826_, 0);
v_type_2847_ = lean_ctor_get(v_toRing_2826_, 1);
v_u_2848_ = lean_ctor_get(v_toRing_2826_, 2);
v_ringInst_2849_ = lean_ctor_get(v_toRing_2826_, 3);
v_semiringInst_2850_ = lean_ctor_get(v_toRing_2826_, 4);
v_charInst_x3f_2851_ = lean_ctor_get(v_toRing_2826_, 5);
v_addFn_x3f_2852_ = lean_ctor_get(v_toRing_2826_, 6);
v_mulFn_x3f_2853_ = lean_ctor_get(v_toRing_2826_, 7);
v_subFn_x3f_2854_ = lean_ctor_get(v_toRing_2826_, 8);
v_negFn_x3f_2855_ = lean_ctor_get(v_toRing_2826_, 9);
v_powFn_x3f_2856_ = lean_ctor_get(v_toRing_2826_, 10);
v_intCastFn_x3f_2857_ = lean_ctor_get(v_toRing_2826_, 11);
v_natCastFn_x3f_2858_ = lean_ctor_get(v_toRing_2826_, 12);
v_one_x3f_2859_ = lean_ctor_get(v_toRing_2826_, 13);
v_vars_2860_ = lean_ctor_get(v_toRing_2826_, 14);
v_varMap_2861_ = lean_ctor_get(v_toRing_2826_, 15);
v_denote_2862_ = lean_ctor_get(v_toRing_2826_, 16);
v_isSharedCheck_2875_ = !lean_is_exclusive(v_toRing_2826_);
if (v_isSharedCheck_2875_ == 0)
{
v___x_2864_ = v_toRing_2826_;
v_isShared_2865_ = v_isSharedCheck_2875_;
goto v_resetjp_2863_;
}
else
{
lean_inc(v_denote_2862_);
lean_inc(v_varMap_2861_);
lean_inc(v_vars_2860_);
lean_inc(v_one_x3f_2859_);
lean_inc(v_natCastFn_x3f_2858_);
lean_inc(v_intCastFn_x3f_2857_);
lean_inc(v_powFn_x3f_2856_);
lean_inc(v_negFn_x3f_2855_);
lean_inc(v_subFn_x3f_2854_);
lean_inc(v_mulFn_x3f_2853_);
lean_inc(v_addFn_x3f_2852_);
lean_inc(v_charInst_x3f_2851_);
lean_inc(v_semiringInst_2850_);
lean_inc(v_ringInst_2849_);
lean_inc(v_u_2848_);
lean_inc(v_type_2847_);
lean_inc(v_id_2846_);
lean_dec(v_toRing_2826_);
v___x_2864_ = lean_box(0);
v_isShared_2865_ = v_isSharedCheck_2875_;
goto v_resetjp_2863_;
}
v_resetjp_2863_:
{
lean_object* v___x_2866_; lean_object* v___x_2868_; 
lean_inc_ref(v_val_2824_);
lean_inc_ref(v_e_2823_);
v___x_2866_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0___redArg(v_denote_2862_, v_e_2823_, v_val_2824_);
if (v_isShared_2865_ == 0)
{
lean_ctor_set(v___x_2864_, 16, v___x_2866_);
v___x_2868_ = v___x_2864_;
goto v_reusejp_2867_;
}
else
{
lean_object* v_reuseFailAlloc_2874_; 
v_reuseFailAlloc_2874_ = lean_alloc_ctor(0, 17, 0);
lean_ctor_set(v_reuseFailAlloc_2874_, 0, v_id_2846_);
lean_ctor_set(v_reuseFailAlloc_2874_, 1, v_type_2847_);
lean_ctor_set(v_reuseFailAlloc_2874_, 2, v_u_2848_);
lean_ctor_set(v_reuseFailAlloc_2874_, 3, v_ringInst_2849_);
lean_ctor_set(v_reuseFailAlloc_2874_, 4, v_semiringInst_2850_);
lean_ctor_set(v_reuseFailAlloc_2874_, 5, v_charInst_x3f_2851_);
lean_ctor_set(v_reuseFailAlloc_2874_, 6, v_addFn_x3f_2852_);
lean_ctor_set(v_reuseFailAlloc_2874_, 7, v_mulFn_x3f_2853_);
lean_ctor_set(v_reuseFailAlloc_2874_, 8, v_subFn_x3f_2854_);
lean_ctor_set(v_reuseFailAlloc_2874_, 9, v_negFn_x3f_2855_);
lean_ctor_set(v_reuseFailAlloc_2874_, 10, v_powFn_x3f_2856_);
lean_ctor_set(v_reuseFailAlloc_2874_, 11, v_intCastFn_x3f_2857_);
lean_ctor_set(v_reuseFailAlloc_2874_, 12, v_natCastFn_x3f_2858_);
lean_ctor_set(v_reuseFailAlloc_2874_, 13, v_one_x3f_2859_);
lean_ctor_set(v_reuseFailAlloc_2874_, 14, v_vars_2860_);
lean_ctor_set(v_reuseFailAlloc_2874_, 15, v_varMap_2861_);
lean_ctor_set(v_reuseFailAlloc_2874_, 16, v___x_2866_);
v___x_2868_ = v_reuseFailAlloc_2874_;
goto v_reusejp_2867_;
}
v_reusejp_2867_:
{
lean_object* v___x_2869_; lean_object* v___x_2870_; lean_object* v___x_2872_; 
v___x_2869_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2869_, 0, v_e_2823_);
lean_ctor_set(v___x_2869_, 1, v_val_2824_);
v___x_2870_ = l_Lean_PersistentArray_push___redArg(v_denoteEntries_2833_, v___x_2869_);
if (v_isShared_2845_ == 0)
{
lean_ctor_set(v___x_2844_, 7, v___x_2870_);
lean_ctor_set(v___x_2844_, 0, v___x_2868_);
v___x_2872_ = v___x_2844_;
goto v_reusejp_2871_;
}
else
{
lean_object* v_reuseFailAlloc_2873_; 
v_reuseFailAlloc_2873_ = lean_alloc_ctor(0, 15, 2);
lean_ctor_set(v_reuseFailAlloc_2873_, 0, v___x_2868_);
lean_ctor_set(v_reuseFailAlloc_2873_, 1, v_invFn_x3f_2827_);
lean_ctor_set(v_reuseFailAlloc_2873_, 2, v_semiringId_x3f_2828_);
lean_ctor_set(v_reuseFailAlloc_2873_, 3, v_commSemiringInst_2829_);
lean_ctor_set(v_reuseFailAlloc_2873_, 4, v_commRingInst_2830_);
lean_ctor_set(v_reuseFailAlloc_2873_, 5, v_noZeroDivInst_x3f_2831_);
lean_ctor_set(v_reuseFailAlloc_2873_, 6, v_fieldInst_x3f_2832_);
lean_ctor_set(v_reuseFailAlloc_2873_, 7, v___x_2870_);
lean_ctor_set(v_reuseFailAlloc_2873_, 8, v_nextId_2834_);
lean_ctor_set(v_reuseFailAlloc_2873_, 9, v_steps_2835_);
lean_ctor_set(v_reuseFailAlloc_2873_, 10, v_queue_2836_);
lean_ctor_set(v_reuseFailAlloc_2873_, 11, v_basis_2837_);
lean_ctor_set(v_reuseFailAlloc_2873_, 12, v_diseqs_2838_);
lean_ctor_set(v_reuseFailAlloc_2873_, 13, v_invSet_2840_);
lean_ctor_set(v_reuseFailAlloc_2873_, 14, v_numEq0_x3f_2841_);
lean_ctor_set_uint8(v_reuseFailAlloc_2873_, sizeof(void*)*15, v_recheck_2839_);
lean_ctor_set_uint8(v_reuseFailAlloc_2873_, sizeof(void*)*15 + 1, v_numEq0Updated_2842_);
v___x_2872_ = v_reuseFailAlloc_2873_;
goto v_reusejp_2871_;
}
v_reusejp_2871_:
{
return v___x_2872_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_internalize___lam__1(lean_object* v___y_2877_, lean_object* v_e_2878_, lean_object* v_val_2879_, lean_object* v_s_2880_){
_start:
{
lean_object* v_rings_2881_; lean_object* v_typeIdOf_2882_; lean_object* v_exprToRingId_2883_; lean_object* v_semirings_2884_; lean_object* v_stypeIdOf_2885_; lean_object* v_exprToSemiringId_2886_; lean_object* v_ncRings_2887_; lean_object* v_exprToNCRingId_2888_; lean_object* v_nctypeIdOf_2889_; lean_object* v_ncSemirings_2890_; lean_object* v_exprToNCSemiringId_2891_; lean_object* v_ncstypeIdOf_2892_; lean_object* v_steps_2893_; lean_object* v___x_2894_; uint8_t v___x_2895_; 
v_rings_2881_ = lean_ctor_get(v_s_2880_, 0);
v_typeIdOf_2882_ = lean_ctor_get(v_s_2880_, 1);
v_exprToRingId_2883_ = lean_ctor_get(v_s_2880_, 2);
v_semirings_2884_ = lean_ctor_get(v_s_2880_, 3);
v_stypeIdOf_2885_ = lean_ctor_get(v_s_2880_, 4);
v_exprToSemiringId_2886_ = lean_ctor_get(v_s_2880_, 5);
v_ncRings_2887_ = lean_ctor_get(v_s_2880_, 6);
v_exprToNCRingId_2888_ = lean_ctor_get(v_s_2880_, 7);
v_nctypeIdOf_2889_ = lean_ctor_get(v_s_2880_, 8);
v_ncSemirings_2890_ = lean_ctor_get(v_s_2880_, 9);
v_exprToNCSemiringId_2891_ = lean_ctor_get(v_s_2880_, 10);
v_ncstypeIdOf_2892_ = lean_ctor_get(v_s_2880_, 11);
v_steps_2893_ = lean_ctor_get(v_s_2880_, 12);
v___x_2894_ = lean_array_get_size(v_semirings_2884_);
v___x_2895_ = lean_nat_dec_lt(v___y_2877_, v___x_2894_);
if (v___x_2895_ == 0)
{
lean_dec_ref(v_val_2879_);
lean_dec_ref(v_e_2878_);
return v_s_2880_;
}
else
{
lean_object* v___x_2897_; uint8_t v_isShared_2898_; uint8_t v_isSharedCheck_2937_; 
lean_inc(v_steps_2893_);
lean_inc_ref(v_ncstypeIdOf_2892_);
lean_inc_ref(v_exprToNCSemiringId_2891_);
lean_inc_ref(v_ncSemirings_2890_);
lean_inc_ref(v_nctypeIdOf_2889_);
lean_inc_ref(v_exprToNCRingId_2888_);
lean_inc_ref(v_ncRings_2887_);
lean_inc_ref(v_exprToSemiringId_2886_);
lean_inc_ref(v_stypeIdOf_2885_);
lean_inc_ref(v_semirings_2884_);
lean_inc_ref(v_exprToRingId_2883_);
lean_inc_ref(v_typeIdOf_2882_);
lean_inc_ref(v_rings_2881_);
v_isSharedCheck_2937_ = !lean_is_exclusive(v_s_2880_);
if (v_isSharedCheck_2937_ == 0)
{
lean_object* v_unused_2938_; lean_object* v_unused_2939_; lean_object* v_unused_2940_; lean_object* v_unused_2941_; lean_object* v_unused_2942_; lean_object* v_unused_2943_; lean_object* v_unused_2944_; lean_object* v_unused_2945_; lean_object* v_unused_2946_; lean_object* v_unused_2947_; lean_object* v_unused_2948_; lean_object* v_unused_2949_; lean_object* v_unused_2950_; 
v_unused_2938_ = lean_ctor_get(v_s_2880_, 12);
lean_dec(v_unused_2938_);
v_unused_2939_ = lean_ctor_get(v_s_2880_, 11);
lean_dec(v_unused_2939_);
v_unused_2940_ = lean_ctor_get(v_s_2880_, 10);
lean_dec(v_unused_2940_);
v_unused_2941_ = lean_ctor_get(v_s_2880_, 9);
lean_dec(v_unused_2941_);
v_unused_2942_ = lean_ctor_get(v_s_2880_, 8);
lean_dec(v_unused_2942_);
v_unused_2943_ = lean_ctor_get(v_s_2880_, 7);
lean_dec(v_unused_2943_);
v_unused_2944_ = lean_ctor_get(v_s_2880_, 6);
lean_dec(v_unused_2944_);
v_unused_2945_ = lean_ctor_get(v_s_2880_, 5);
lean_dec(v_unused_2945_);
v_unused_2946_ = lean_ctor_get(v_s_2880_, 4);
lean_dec(v_unused_2946_);
v_unused_2947_ = lean_ctor_get(v_s_2880_, 3);
lean_dec(v_unused_2947_);
v_unused_2948_ = lean_ctor_get(v_s_2880_, 2);
lean_dec(v_unused_2948_);
v_unused_2949_ = lean_ctor_get(v_s_2880_, 1);
lean_dec(v_unused_2949_);
v_unused_2950_ = lean_ctor_get(v_s_2880_, 0);
lean_dec(v_unused_2950_);
v___x_2897_ = v_s_2880_;
v_isShared_2898_ = v_isSharedCheck_2937_;
goto v_resetjp_2896_;
}
else
{
lean_dec(v_s_2880_);
v___x_2897_ = lean_box(0);
v_isShared_2898_ = v_isSharedCheck_2937_;
goto v_resetjp_2896_;
}
v_resetjp_2896_:
{
lean_object* v_v_2899_; lean_object* v_toSemiring_2900_; lean_object* v_ringId_2901_; lean_object* v_commSemiringInst_2902_; lean_object* v_addRightCancelInst_x3f_2903_; lean_object* v_toQFn_x3f_2904_; lean_object* v___x_2906_; uint8_t v_isShared_2907_; uint8_t v_isSharedCheck_2936_; 
v_v_2899_ = lean_array_fget(v_semirings_2884_, v___y_2877_);
v_toSemiring_2900_ = lean_ctor_get(v_v_2899_, 0);
v_ringId_2901_ = lean_ctor_get(v_v_2899_, 1);
v_commSemiringInst_2902_ = lean_ctor_get(v_v_2899_, 2);
v_addRightCancelInst_x3f_2903_ = lean_ctor_get(v_v_2899_, 3);
v_toQFn_x3f_2904_ = lean_ctor_get(v_v_2899_, 4);
v_isSharedCheck_2936_ = !lean_is_exclusive(v_v_2899_);
if (v_isSharedCheck_2936_ == 0)
{
v___x_2906_ = v_v_2899_;
v_isShared_2907_ = v_isSharedCheck_2936_;
goto v_resetjp_2905_;
}
else
{
lean_inc(v_toQFn_x3f_2904_);
lean_inc(v_addRightCancelInst_x3f_2903_);
lean_inc(v_commSemiringInst_2902_);
lean_inc(v_ringId_2901_);
lean_inc(v_toSemiring_2900_);
lean_dec(v_v_2899_);
v___x_2906_ = lean_box(0);
v_isShared_2907_ = v_isSharedCheck_2936_;
goto v_resetjp_2905_;
}
v_resetjp_2905_:
{
lean_object* v_id_2908_; lean_object* v_type_2909_; lean_object* v_u_2910_; lean_object* v_semiringInst_2911_; lean_object* v_addFn_x3f_2912_; lean_object* v_mulFn_x3f_2913_; lean_object* v_powFn_x3f_2914_; lean_object* v_natCastFn_x3f_2915_; lean_object* v_denote_2916_; lean_object* v_vars_2917_; lean_object* v_varMap_2918_; lean_object* v___x_2920_; uint8_t v_isShared_2921_; uint8_t v_isSharedCheck_2935_; 
v_id_2908_ = lean_ctor_get(v_toSemiring_2900_, 0);
v_type_2909_ = lean_ctor_get(v_toSemiring_2900_, 1);
v_u_2910_ = lean_ctor_get(v_toSemiring_2900_, 2);
v_semiringInst_2911_ = lean_ctor_get(v_toSemiring_2900_, 3);
v_addFn_x3f_2912_ = lean_ctor_get(v_toSemiring_2900_, 4);
v_mulFn_x3f_2913_ = lean_ctor_get(v_toSemiring_2900_, 5);
v_powFn_x3f_2914_ = lean_ctor_get(v_toSemiring_2900_, 6);
v_natCastFn_x3f_2915_ = lean_ctor_get(v_toSemiring_2900_, 7);
v_denote_2916_ = lean_ctor_get(v_toSemiring_2900_, 8);
v_vars_2917_ = lean_ctor_get(v_toSemiring_2900_, 9);
v_varMap_2918_ = lean_ctor_get(v_toSemiring_2900_, 10);
v_isSharedCheck_2935_ = !lean_is_exclusive(v_toSemiring_2900_);
if (v_isSharedCheck_2935_ == 0)
{
v___x_2920_ = v_toSemiring_2900_;
v_isShared_2921_ = v_isSharedCheck_2935_;
goto v_resetjp_2919_;
}
else
{
lean_inc(v_varMap_2918_);
lean_inc(v_vars_2917_);
lean_inc(v_denote_2916_);
lean_inc(v_natCastFn_x3f_2915_);
lean_inc(v_powFn_x3f_2914_);
lean_inc(v_mulFn_x3f_2913_);
lean_inc(v_addFn_x3f_2912_);
lean_inc(v_semiringInst_2911_);
lean_inc(v_u_2910_);
lean_inc(v_type_2909_);
lean_inc(v_id_2908_);
lean_dec(v_toSemiring_2900_);
v___x_2920_ = lean_box(0);
v_isShared_2921_ = v_isSharedCheck_2935_;
goto v_resetjp_2919_;
}
v_resetjp_2919_:
{
lean_object* v___x_2922_; lean_object* v_xs_x27_2923_; lean_object* v___x_2924_; lean_object* v___x_2926_; 
v___x_2922_ = lean_box(0);
v_xs_x27_2923_ = lean_array_fset(v_semirings_2884_, v___y_2877_, v___x_2922_);
v___x_2924_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0___redArg(v_denote_2916_, v_e_2878_, v_val_2879_);
if (v_isShared_2921_ == 0)
{
lean_ctor_set(v___x_2920_, 8, v___x_2924_);
v___x_2926_ = v___x_2920_;
goto v_reusejp_2925_;
}
else
{
lean_object* v_reuseFailAlloc_2934_; 
v_reuseFailAlloc_2934_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_2934_, 0, v_id_2908_);
lean_ctor_set(v_reuseFailAlloc_2934_, 1, v_type_2909_);
lean_ctor_set(v_reuseFailAlloc_2934_, 2, v_u_2910_);
lean_ctor_set(v_reuseFailAlloc_2934_, 3, v_semiringInst_2911_);
lean_ctor_set(v_reuseFailAlloc_2934_, 4, v_addFn_x3f_2912_);
lean_ctor_set(v_reuseFailAlloc_2934_, 5, v_mulFn_x3f_2913_);
lean_ctor_set(v_reuseFailAlloc_2934_, 6, v_powFn_x3f_2914_);
lean_ctor_set(v_reuseFailAlloc_2934_, 7, v_natCastFn_x3f_2915_);
lean_ctor_set(v_reuseFailAlloc_2934_, 8, v___x_2924_);
lean_ctor_set(v_reuseFailAlloc_2934_, 9, v_vars_2917_);
lean_ctor_set(v_reuseFailAlloc_2934_, 10, v_varMap_2918_);
v___x_2926_ = v_reuseFailAlloc_2934_;
goto v_reusejp_2925_;
}
v_reusejp_2925_:
{
lean_object* v___x_2928_; 
if (v_isShared_2907_ == 0)
{
lean_ctor_set(v___x_2906_, 0, v___x_2926_);
v___x_2928_ = v___x_2906_;
goto v_reusejp_2927_;
}
else
{
lean_object* v_reuseFailAlloc_2933_; 
v_reuseFailAlloc_2933_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2933_, 0, v___x_2926_);
lean_ctor_set(v_reuseFailAlloc_2933_, 1, v_ringId_2901_);
lean_ctor_set(v_reuseFailAlloc_2933_, 2, v_commSemiringInst_2902_);
lean_ctor_set(v_reuseFailAlloc_2933_, 3, v_addRightCancelInst_x3f_2903_);
lean_ctor_set(v_reuseFailAlloc_2933_, 4, v_toQFn_x3f_2904_);
v___x_2928_ = v_reuseFailAlloc_2933_;
goto v_reusejp_2927_;
}
v_reusejp_2927_:
{
lean_object* v___x_2929_; lean_object* v___x_2931_; 
v___x_2929_ = lean_array_fset(v_xs_x27_2923_, v___y_2877_, v___x_2928_);
if (v_isShared_2898_ == 0)
{
lean_ctor_set(v___x_2897_, 3, v___x_2929_);
v___x_2931_ = v___x_2897_;
goto v_reusejp_2930_;
}
else
{
lean_object* v_reuseFailAlloc_2932_; 
v_reuseFailAlloc_2932_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_2932_, 0, v_rings_2881_);
lean_ctor_set(v_reuseFailAlloc_2932_, 1, v_typeIdOf_2882_);
lean_ctor_set(v_reuseFailAlloc_2932_, 2, v_exprToRingId_2883_);
lean_ctor_set(v_reuseFailAlloc_2932_, 3, v___x_2929_);
lean_ctor_set(v_reuseFailAlloc_2932_, 4, v_stypeIdOf_2885_);
lean_ctor_set(v_reuseFailAlloc_2932_, 5, v_exprToSemiringId_2886_);
lean_ctor_set(v_reuseFailAlloc_2932_, 6, v_ncRings_2887_);
lean_ctor_set(v_reuseFailAlloc_2932_, 7, v_exprToNCRingId_2888_);
lean_ctor_set(v_reuseFailAlloc_2932_, 8, v_nctypeIdOf_2889_);
lean_ctor_set(v_reuseFailAlloc_2932_, 9, v_ncSemirings_2890_);
lean_ctor_set(v_reuseFailAlloc_2932_, 10, v_exprToNCSemiringId_2891_);
lean_ctor_set(v_reuseFailAlloc_2932_, 11, v_ncstypeIdOf_2892_);
lean_ctor_set(v_reuseFailAlloc_2932_, 12, v_steps_2893_);
v___x_2931_ = v_reuseFailAlloc_2932_;
goto v_reusejp_2930_;
}
v_reusejp_2930_:
{
return v___x_2931_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_internalize___lam__1___boxed(lean_object* v___y_2951_, lean_object* v_e_2952_, lean_object* v_val_2953_, lean_object* v_s_2954_){
_start:
{
lean_object* v_res_2955_; 
v_res_2955_ = l_Lean_Meta_Grind_Arith_CommRing_internalize___lam__1(v___y_2951_, v_e_2952_, v_val_2953_, v_s_2954_);
lean_dec(v___y_2951_);
return v_res_2955_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_internalize___lam__2(lean_object* v_e_2956_, lean_object* v_val_2957_, lean_object* v_s_2958_){
_start:
{
lean_object* v_id_2959_; lean_object* v_type_2960_; lean_object* v_u_2961_; lean_object* v_ringInst_2962_; lean_object* v_semiringInst_2963_; lean_object* v_charInst_x3f_2964_; lean_object* v_addFn_x3f_2965_; lean_object* v_mulFn_x3f_2966_; lean_object* v_subFn_x3f_2967_; lean_object* v_negFn_x3f_2968_; lean_object* v_powFn_x3f_2969_; lean_object* v_intCastFn_x3f_2970_; lean_object* v_natCastFn_x3f_2971_; lean_object* v_one_x3f_2972_; lean_object* v_vars_2973_; lean_object* v_varMap_2974_; lean_object* v_denote_2975_; lean_object* v___x_2977_; uint8_t v_isShared_2978_; uint8_t v_isSharedCheck_2983_; 
v_id_2959_ = lean_ctor_get(v_s_2958_, 0);
v_type_2960_ = lean_ctor_get(v_s_2958_, 1);
v_u_2961_ = lean_ctor_get(v_s_2958_, 2);
v_ringInst_2962_ = lean_ctor_get(v_s_2958_, 3);
v_semiringInst_2963_ = lean_ctor_get(v_s_2958_, 4);
v_charInst_x3f_2964_ = lean_ctor_get(v_s_2958_, 5);
v_addFn_x3f_2965_ = lean_ctor_get(v_s_2958_, 6);
v_mulFn_x3f_2966_ = lean_ctor_get(v_s_2958_, 7);
v_subFn_x3f_2967_ = lean_ctor_get(v_s_2958_, 8);
v_negFn_x3f_2968_ = lean_ctor_get(v_s_2958_, 9);
v_powFn_x3f_2969_ = lean_ctor_get(v_s_2958_, 10);
v_intCastFn_x3f_2970_ = lean_ctor_get(v_s_2958_, 11);
v_natCastFn_x3f_2971_ = lean_ctor_get(v_s_2958_, 12);
v_one_x3f_2972_ = lean_ctor_get(v_s_2958_, 13);
v_vars_2973_ = lean_ctor_get(v_s_2958_, 14);
v_varMap_2974_ = lean_ctor_get(v_s_2958_, 15);
v_denote_2975_ = lean_ctor_get(v_s_2958_, 16);
v_isSharedCheck_2983_ = !lean_is_exclusive(v_s_2958_);
if (v_isSharedCheck_2983_ == 0)
{
v___x_2977_ = v_s_2958_;
v_isShared_2978_ = v_isSharedCheck_2983_;
goto v_resetjp_2976_;
}
else
{
lean_inc(v_denote_2975_);
lean_inc(v_varMap_2974_);
lean_inc(v_vars_2973_);
lean_inc(v_one_x3f_2972_);
lean_inc(v_natCastFn_x3f_2971_);
lean_inc(v_intCastFn_x3f_2970_);
lean_inc(v_powFn_x3f_2969_);
lean_inc(v_negFn_x3f_2968_);
lean_inc(v_subFn_x3f_2967_);
lean_inc(v_mulFn_x3f_2966_);
lean_inc(v_addFn_x3f_2965_);
lean_inc(v_charInst_x3f_2964_);
lean_inc(v_semiringInst_2963_);
lean_inc(v_ringInst_2962_);
lean_inc(v_u_2961_);
lean_inc(v_type_2960_);
lean_inc(v_id_2959_);
lean_dec(v_s_2958_);
v___x_2977_ = lean_box(0);
v_isShared_2978_ = v_isSharedCheck_2983_;
goto v_resetjp_2976_;
}
v_resetjp_2976_:
{
lean_object* v___x_2979_; lean_object* v___x_2981_; 
v___x_2979_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0___redArg(v_denote_2975_, v_e_2956_, v_val_2957_);
if (v_isShared_2978_ == 0)
{
lean_ctor_set(v___x_2977_, 16, v___x_2979_);
v___x_2981_ = v___x_2977_;
goto v_reusejp_2980_;
}
else
{
lean_object* v_reuseFailAlloc_2982_; 
v_reuseFailAlloc_2982_ = lean_alloc_ctor(0, 17, 0);
lean_ctor_set(v_reuseFailAlloc_2982_, 0, v_id_2959_);
lean_ctor_set(v_reuseFailAlloc_2982_, 1, v_type_2960_);
lean_ctor_set(v_reuseFailAlloc_2982_, 2, v_u_2961_);
lean_ctor_set(v_reuseFailAlloc_2982_, 3, v_ringInst_2962_);
lean_ctor_set(v_reuseFailAlloc_2982_, 4, v_semiringInst_2963_);
lean_ctor_set(v_reuseFailAlloc_2982_, 5, v_charInst_x3f_2964_);
lean_ctor_set(v_reuseFailAlloc_2982_, 6, v_addFn_x3f_2965_);
lean_ctor_set(v_reuseFailAlloc_2982_, 7, v_mulFn_x3f_2966_);
lean_ctor_set(v_reuseFailAlloc_2982_, 8, v_subFn_x3f_2967_);
lean_ctor_set(v_reuseFailAlloc_2982_, 9, v_negFn_x3f_2968_);
lean_ctor_set(v_reuseFailAlloc_2982_, 10, v_powFn_x3f_2969_);
lean_ctor_set(v_reuseFailAlloc_2982_, 11, v_intCastFn_x3f_2970_);
lean_ctor_set(v_reuseFailAlloc_2982_, 12, v_natCastFn_x3f_2971_);
lean_ctor_set(v_reuseFailAlloc_2982_, 13, v_one_x3f_2972_);
lean_ctor_set(v_reuseFailAlloc_2982_, 14, v_vars_2973_);
lean_ctor_set(v_reuseFailAlloc_2982_, 15, v_varMap_2974_);
lean_ctor_set(v_reuseFailAlloc_2982_, 16, v___x_2979_);
v___x_2981_ = v_reuseFailAlloc_2982_;
goto v_reusejp_2980_;
}
v_reusejp_2980_:
{
return v___x_2981_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_internalize___lam__3(lean_object* v_e_2984_, lean_object* v_val_2985_, lean_object* v_s_2986_){
_start:
{
lean_object* v_id_2987_; lean_object* v_type_2988_; lean_object* v_u_2989_; lean_object* v_semiringInst_2990_; lean_object* v_addFn_x3f_2991_; lean_object* v_mulFn_x3f_2992_; lean_object* v_powFn_x3f_2993_; lean_object* v_natCastFn_x3f_2994_; lean_object* v_denote_2995_; lean_object* v_vars_2996_; lean_object* v_varMap_2997_; lean_object* v___x_2999_; uint8_t v_isShared_3000_; uint8_t v_isSharedCheck_3005_; 
v_id_2987_ = lean_ctor_get(v_s_2986_, 0);
v_type_2988_ = lean_ctor_get(v_s_2986_, 1);
v_u_2989_ = lean_ctor_get(v_s_2986_, 2);
v_semiringInst_2990_ = lean_ctor_get(v_s_2986_, 3);
v_addFn_x3f_2991_ = lean_ctor_get(v_s_2986_, 4);
v_mulFn_x3f_2992_ = lean_ctor_get(v_s_2986_, 5);
v_powFn_x3f_2993_ = lean_ctor_get(v_s_2986_, 6);
v_natCastFn_x3f_2994_ = lean_ctor_get(v_s_2986_, 7);
v_denote_2995_ = lean_ctor_get(v_s_2986_, 8);
v_vars_2996_ = lean_ctor_get(v_s_2986_, 9);
v_varMap_2997_ = lean_ctor_get(v_s_2986_, 10);
v_isSharedCheck_3005_ = !lean_is_exclusive(v_s_2986_);
if (v_isSharedCheck_3005_ == 0)
{
v___x_2999_ = v_s_2986_;
v_isShared_3000_ = v_isSharedCheck_3005_;
goto v_resetjp_2998_;
}
else
{
lean_inc(v_varMap_2997_);
lean_inc(v_vars_2996_);
lean_inc(v_denote_2995_);
lean_inc(v_natCastFn_x3f_2994_);
lean_inc(v_powFn_x3f_2993_);
lean_inc(v_mulFn_x3f_2992_);
lean_inc(v_addFn_x3f_2991_);
lean_inc(v_semiringInst_2990_);
lean_inc(v_u_2989_);
lean_inc(v_type_2988_);
lean_inc(v_id_2987_);
lean_dec(v_s_2986_);
v___x_2999_ = lean_box(0);
v_isShared_3000_ = v_isSharedCheck_3005_;
goto v_resetjp_2998_;
}
v_resetjp_2998_:
{
lean_object* v___x_3001_; lean_object* v___x_3003_; 
v___x_3001_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0___redArg(v_denote_2995_, v_e_2984_, v_val_2985_);
if (v_isShared_3000_ == 0)
{
lean_ctor_set(v___x_2999_, 8, v___x_3001_);
v___x_3003_ = v___x_2999_;
goto v_reusejp_3002_;
}
else
{
lean_object* v_reuseFailAlloc_3004_; 
v_reuseFailAlloc_3004_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_3004_, 0, v_id_2987_);
lean_ctor_set(v_reuseFailAlloc_3004_, 1, v_type_2988_);
lean_ctor_set(v_reuseFailAlloc_3004_, 2, v_u_2989_);
lean_ctor_set(v_reuseFailAlloc_3004_, 3, v_semiringInst_2990_);
lean_ctor_set(v_reuseFailAlloc_3004_, 4, v_addFn_x3f_2991_);
lean_ctor_set(v_reuseFailAlloc_3004_, 5, v_mulFn_x3f_2992_);
lean_ctor_set(v_reuseFailAlloc_3004_, 6, v_powFn_x3f_2993_);
lean_ctor_set(v_reuseFailAlloc_3004_, 7, v_natCastFn_x3f_2994_);
lean_ctor_set(v_reuseFailAlloc_3004_, 8, v___x_3001_);
lean_ctor_set(v_reuseFailAlloc_3004_, 9, v_vars_2996_);
lean_ctor_set(v_reuseFailAlloc_3004_, 10, v_varMap_2997_);
v___x_3003_ = v_reuseFailAlloc_3004_;
goto v_reusejp_3002_;
}
v_reusejp_3002_:
{
return v___x_3003_;
}
}
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_3006_; double v___x_3007_; 
v___x_3006_ = lean_unsigned_to_nat(0u);
v___x_3007_ = lean_float_of_nat(v___x_3006_);
return v___x_3007_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__4___redArg(lean_object* v_cls_3011_, lean_object* v_msg_3012_, lean_object* v___y_3013_, lean_object* v___y_3014_, lean_object* v___y_3015_, lean_object* v___y_3016_){
_start:
{
lean_object* v_ref_3018_; lean_object* v___x_3019_; lean_object* v_a_3020_; lean_object* v___x_3022_; uint8_t v_isShared_3023_; uint8_t v_isSharedCheck_3064_; 
v_ref_3018_ = lean_ctor_get(v___y_3015_, 5);
v___x_3019_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1_spec__5_spec__8_spec__9(v_msg_3012_, v___y_3013_, v___y_3014_, v___y_3015_, v___y_3016_);
v_a_3020_ = lean_ctor_get(v___x_3019_, 0);
v_isSharedCheck_3064_ = !lean_is_exclusive(v___x_3019_);
if (v_isSharedCheck_3064_ == 0)
{
v___x_3022_ = v___x_3019_;
v_isShared_3023_ = v_isSharedCheck_3064_;
goto v_resetjp_3021_;
}
else
{
lean_inc(v_a_3020_);
lean_dec(v___x_3019_);
v___x_3022_ = lean_box(0);
v_isShared_3023_ = v_isSharedCheck_3064_;
goto v_resetjp_3021_;
}
v_resetjp_3021_:
{
lean_object* v___x_3024_; lean_object* v_traceState_3025_; lean_object* v_env_3026_; lean_object* v_nextMacroScope_3027_; lean_object* v_ngen_3028_; lean_object* v_auxDeclNGen_3029_; lean_object* v_cache_3030_; lean_object* v_messages_3031_; lean_object* v_infoState_3032_; lean_object* v_snapshotTasks_3033_; lean_object* v___x_3035_; uint8_t v_isShared_3036_; uint8_t v_isSharedCheck_3063_; 
v___x_3024_ = lean_st_ref_take(v___y_3016_);
v_traceState_3025_ = lean_ctor_get(v___x_3024_, 4);
v_env_3026_ = lean_ctor_get(v___x_3024_, 0);
v_nextMacroScope_3027_ = lean_ctor_get(v___x_3024_, 1);
v_ngen_3028_ = lean_ctor_get(v___x_3024_, 2);
v_auxDeclNGen_3029_ = lean_ctor_get(v___x_3024_, 3);
v_cache_3030_ = lean_ctor_get(v___x_3024_, 5);
v_messages_3031_ = lean_ctor_get(v___x_3024_, 6);
v_infoState_3032_ = lean_ctor_get(v___x_3024_, 7);
v_snapshotTasks_3033_ = lean_ctor_get(v___x_3024_, 8);
v_isSharedCheck_3063_ = !lean_is_exclusive(v___x_3024_);
if (v_isSharedCheck_3063_ == 0)
{
v___x_3035_ = v___x_3024_;
v_isShared_3036_ = v_isSharedCheck_3063_;
goto v_resetjp_3034_;
}
else
{
lean_inc(v_snapshotTasks_3033_);
lean_inc(v_infoState_3032_);
lean_inc(v_messages_3031_);
lean_inc(v_cache_3030_);
lean_inc(v_traceState_3025_);
lean_inc(v_auxDeclNGen_3029_);
lean_inc(v_ngen_3028_);
lean_inc(v_nextMacroScope_3027_);
lean_inc(v_env_3026_);
lean_dec(v___x_3024_);
v___x_3035_ = lean_box(0);
v_isShared_3036_ = v_isSharedCheck_3063_;
goto v_resetjp_3034_;
}
v_resetjp_3034_:
{
uint64_t v_tid_3037_; lean_object* v_traces_3038_; lean_object* v___x_3040_; uint8_t v_isShared_3041_; uint8_t v_isSharedCheck_3062_; 
v_tid_3037_ = lean_ctor_get_uint64(v_traceState_3025_, sizeof(void*)*1);
v_traces_3038_ = lean_ctor_get(v_traceState_3025_, 0);
v_isSharedCheck_3062_ = !lean_is_exclusive(v_traceState_3025_);
if (v_isSharedCheck_3062_ == 0)
{
v___x_3040_ = v_traceState_3025_;
v_isShared_3041_ = v_isSharedCheck_3062_;
goto v_resetjp_3039_;
}
else
{
lean_inc(v_traces_3038_);
lean_dec(v_traceState_3025_);
v___x_3040_ = lean_box(0);
v_isShared_3041_ = v_isSharedCheck_3062_;
goto v_resetjp_3039_;
}
v_resetjp_3039_:
{
lean_object* v___x_3042_; double v___x_3043_; uint8_t v___x_3044_; lean_object* v___x_3045_; lean_object* v___x_3046_; lean_object* v___x_3047_; lean_object* v___x_3048_; lean_object* v___x_3049_; lean_object* v___x_3050_; lean_object* v___x_3052_; 
v___x_3042_ = lean_box(0);
v___x_3043_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__4___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__4___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__4___redArg___closed__0);
v___x_3044_ = 0;
v___x_3045_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__4___redArg___closed__1));
v___x_3046_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3046_, 0, v_cls_3011_);
lean_ctor_set(v___x_3046_, 1, v___x_3042_);
lean_ctor_set(v___x_3046_, 2, v___x_3045_);
lean_ctor_set_float(v___x_3046_, sizeof(void*)*3, v___x_3043_);
lean_ctor_set_float(v___x_3046_, sizeof(void*)*3 + 8, v___x_3043_);
lean_ctor_set_uint8(v___x_3046_, sizeof(void*)*3 + 16, v___x_3044_);
v___x_3047_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__4___redArg___closed__2));
v___x_3048_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3048_, 0, v___x_3046_);
lean_ctor_set(v___x_3048_, 1, v_a_3020_);
lean_ctor_set(v___x_3048_, 2, v___x_3047_);
lean_inc(v_ref_3018_);
v___x_3049_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3049_, 0, v_ref_3018_);
lean_ctor_set(v___x_3049_, 1, v___x_3048_);
v___x_3050_ = l_Lean_PersistentArray_push___redArg(v_traces_3038_, v___x_3049_);
if (v_isShared_3041_ == 0)
{
lean_ctor_set(v___x_3040_, 0, v___x_3050_);
v___x_3052_ = v___x_3040_;
goto v_reusejp_3051_;
}
else
{
lean_object* v_reuseFailAlloc_3061_; 
v_reuseFailAlloc_3061_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3061_, 0, v___x_3050_);
lean_ctor_set_uint64(v_reuseFailAlloc_3061_, sizeof(void*)*1, v_tid_3037_);
v___x_3052_ = v_reuseFailAlloc_3061_;
goto v_reusejp_3051_;
}
v_reusejp_3051_:
{
lean_object* v___x_3054_; 
if (v_isShared_3036_ == 0)
{
lean_ctor_set(v___x_3035_, 4, v___x_3052_);
v___x_3054_ = v___x_3035_;
goto v_reusejp_3053_;
}
else
{
lean_object* v_reuseFailAlloc_3060_; 
v_reuseFailAlloc_3060_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3060_, 0, v_env_3026_);
lean_ctor_set(v_reuseFailAlloc_3060_, 1, v_nextMacroScope_3027_);
lean_ctor_set(v_reuseFailAlloc_3060_, 2, v_ngen_3028_);
lean_ctor_set(v_reuseFailAlloc_3060_, 3, v_auxDeclNGen_3029_);
lean_ctor_set(v_reuseFailAlloc_3060_, 4, v___x_3052_);
lean_ctor_set(v_reuseFailAlloc_3060_, 5, v_cache_3030_);
lean_ctor_set(v_reuseFailAlloc_3060_, 6, v_messages_3031_);
lean_ctor_set(v_reuseFailAlloc_3060_, 7, v_infoState_3032_);
lean_ctor_set(v_reuseFailAlloc_3060_, 8, v_snapshotTasks_3033_);
v___x_3054_ = v_reuseFailAlloc_3060_;
goto v_reusejp_3053_;
}
v_reusejp_3053_:
{
lean_object* v___x_3055_; lean_object* v___x_3056_; lean_object* v___x_3058_; 
v___x_3055_ = lean_st_ref_set(v___y_3016_, v___x_3054_);
v___x_3056_ = lean_box(0);
if (v_isShared_3023_ == 0)
{
lean_ctor_set(v___x_3022_, 0, v___x_3056_);
v___x_3058_ = v___x_3022_;
goto v_reusejp_3057_;
}
else
{
lean_object* v_reuseFailAlloc_3059_; 
v_reuseFailAlloc_3059_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3059_, 0, v___x_3056_);
v___x_3058_ = v_reuseFailAlloc_3059_;
goto v_reusejp_3057_;
}
v_reusejp_3057_:
{
return v___x_3058_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__4___redArg___boxed(lean_object* v_cls_3065_, lean_object* v_msg_3066_, lean_object* v___y_3067_, lean_object* v___y_3068_, lean_object* v___y_3069_, lean_object* v___y_3070_, lean_object* v___y_3071_){
_start:
{
lean_object* v_res_3072_; 
v_res_3072_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__4___redArg(v_cls_3065_, v_msg_3066_, v___y_3067_, v___y_3068_, v___y_3069_, v___y_3070_);
lean_dec(v___y_3070_);
lean_dec_ref(v___y_3069_);
lean_dec(v___y_3068_);
lean_dec_ref(v___y_3067_);
return v_res_3072_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__6___redArg(lean_object* v_cls_3073_, lean_object* v_msg_3074_, lean_object* v___y_3075_, lean_object* v___y_3076_, lean_object* v___y_3077_, lean_object* v___y_3078_){
_start:
{
lean_object* v_ref_3080_; lean_object* v___x_3081_; lean_object* v_a_3082_; lean_object* v___x_3084_; uint8_t v_isShared_3085_; uint8_t v_isSharedCheck_3126_; 
v_ref_3080_ = lean_ctor_get(v___y_3077_, 5);
v___x_3081_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1_spec__5_spec__8_spec__9(v_msg_3074_, v___y_3075_, v___y_3076_, v___y_3077_, v___y_3078_);
v_a_3082_ = lean_ctor_get(v___x_3081_, 0);
v_isSharedCheck_3126_ = !lean_is_exclusive(v___x_3081_);
if (v_isSharedCheck_3126_ == 0)
{
v___x_3084_ = v___x_3081_;
v_isShared_3085_ = v_isSharedCheck_3126_;
goto v_resetjp_3083_;
}
else
{
lean_inc(v_a_3082_);
lean_dec(v___x_3081_);
v___x_3084_ = lean_box(0);
v_isShared_3085_ = v_isSharedCheck_3126_;
goto v_resetjp_3083_;
}
v_resetjp_3083_:
{
lean_object* v___x_3086_; lean_object* v_traceState_3087_; lean_object* v_env_3088_; lean_object* v_nextMacroScope_3089_; lean_object* v_ngen_3090_; lean_object* v_auxDeclNGen_3091_; lean_object* v_cache_3092_; lean_object* v_messages_3093_; lean_object* v_infoState_3094_; lean_object* v_snapshotTasks_3095_; lean_object* v___x_3097_; uint8_t v_isShared_3098_; uint8_t v_isSharedCheck_3125_; 
v___x_3086_ = lean_st_ref_take(v___y_3078_);
v_traceState_3087_ = lean_ctor_get(v___x_3086_, 4);
v_env_3088_ = lean_ctor_get(v___x_3086_, 0);
v_nextMacroScope_3089_ = lean_ctor_get(v___x_3086_, 1);
v_ngen_3090_ = lean_ctor_get(v___x_3086_, 2);
v_auxDeclNGen_3091_ = lean_ctor_get(v___x_3086_, 3);
v_cache_3092_ = lean_ctor_get(v___x_3086_, 5);
v_messages_3093_ = lean_ctor_get(v___x_3086_, 6);
v_infoState_3094_ = lean_ctor_get(v___x_3086_, 7);
v_snapshotTasks_3095_ = lean_ctor_get(v___x_3086_, 8);
v_isSharedCheck_3125_ = !lean_is_exclusive(v___x_3086_);
if (v_isSharedCheck_3125_ == 0)
{
v___x_3097_ = v___x_3086_;
v_isShared_3098_ = v_isSharedCheck_3125_;
goto v_resetjp_3096_;
}
else
{
lean_inc(v_snapshotTasks_3095_);
lean_inc(v_infoState_3094_);
lean_inc(v_messages_3093_);
lean_inc(v_cache_3092_);
lean_inc(v_traceState_3087_);
lean_inc(v_auxDeclNGen_3091_);
lean_inc(v_ngen_3090_);
lean_inc(v_nextMacroScope_3089_);
lean_inc(v_env_3088_);
lean_dec(v___x_3086_);
v___x_3097_ = lean_box(0);
v_isShared_3098_ = v_isSharedCheck_3125_;
goto v_resetjp_3096_;
}
v_resetjp_3096_:
{
uint64_t v_tid_3099_; lean_object* v_traces_3100_; lean_object* v___x_3102_; uint8_t v_isShared_3103_; uint8_t v_isSharedCheck_3124_; 
v_tid_3099_ = lean_ctor_get_uint64(v_traceState_3087_, sizeof(void*)*1);
v_traces_3100_ = lean_ctor_get(v_traceState_3087_, 0);
v_isSharedCheck_3124_ = !lean_is_exclusive(v_traceState_3087_);
if (v_isSharedCheck_3124_ == 0)
{
v___x_3102_ = v_traceState_3087_;
v_isShared_3103_ = v_isSharedCheck_3124_;
goto v_resetjp_3101_;
}
else
{
lean_inc(v_traces_3100_);
lean_dec(v_traceState_3087_);
v___x_3102_ = lean_box(0);
v_isShared_3103_ = v_isSharedCheck_3124_;
goto v_resetjp_3101_;
}
v_resetjp_3101_:
{
lean_object* v___x_3104_; double v___x_3105_; uint8_t v___x_3106_; lean_object* v___x_3107_; lean_object* v___x_3108_; lean_object* v___x_3109_; lean_object* v___x_3110_; lean_object* v___x_3111_; lean_object* v___x_3112_; lean_object* v___x_3114_; 
v___x_3104_ = lean_box(0);
v___x_3105_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__4___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__4___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__4___redArg___closed__0);
v___x_3106_ = 0;
v___x_3107_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__4___redArg___closed__1));
v___x_3108_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3108_, 0, v_cls_3073_);
lean_ctor_set(v___x_3108_, 1, v___x_3104_);
lean_ctor_set(v___x_3108_, 2, v___x_3107_);
lean_ctor_set_float(v___x_3108_, sizeof(void*)*3, v___x_3105_);
lean_ctor_set_float(v___x_3108_, sizeof(void*)*3 + 8, v___x_3105_);
lean_ctor_set_uint8(v___x_3108_, sizeof(void*)*3 + 16, v___x_3106_);
v___x_3109_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__4___redArg___closed__2));
v___x_3110_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3110_, 0, v___x_3108_);
lean_ctor_set(v___x_3110_, 1, v_a_3082_);
lean_ctor_set(v___x_3110_, 2, v___x_3109_);
lean_inc(v_ref_3080_);
v___x_3111_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3111_, 0, v_ref_3080_);
lean_ctor_set(v___x_3111_, 1, v___x_3110_);
v___x_3112_ = l_Lean_PersistentArray_push___redArg(v_traces_3100_, v___x_3111_);
if (v_isShared_3103_ == 0)
{
lean_ctor_set(v___x_3102_, 0, v___x_3112_);
v___x_3114_ = v___x_3102_;
goto v_reusejp_3113_;
}
else
{
lean_object* v_reuseFailAlloc_3123_; 
v_reuseFailAlloc_3123_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3123_, 0, v___x_3112_);
lean_ctor_set_uint64(v_reuseFailAlloc_3123_, sizeof(void*)*1, v_tid_3099_);
v___x_3114_ = v_reuseFailAlloc_3123_;
goto v_reusejp_3113_;
}
v_reusejp_3113_:
{
lean_object* v___x_3116_; 
if (v_isShared_3098_ == 0)
{
lean_ctor_set(v___x_3097_, 4, v___x_3114_);
v___x_3116_ = v___x_3097_;
goto v_reusejp_3115_;
}
else
{
lean_object* v_reuseFailAlloc_3122_; 
v_reuseFailAlloc_3122_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3122_, 0, v_env_3088_);
lean_ctor_set(v_reuseFailAlloc_3122_, 1, v_nextMacroScope_3089_);
lean_ctor_set(v_reuseFailAlloc_3122_, 2, v_ngen_3090_);
lean_ctor_set(v_reuseFailAlloc_3122_, 3, v_auxDeclNGen_3091_);
lean_ctor_set(v_reuseFailAlloc_3122_, 4, v___x_3114_);
lean_ctor_set(v_reuseFailAlloc_3122_, 5, v_cache_3092_);
lean_ctor_set(v_reuseFailAlloc_3122_, 6, v_messages_3093_);
lean_ctor_set(v_reuseFailAlloc_3122_, 7, v_infoState_3094_);
lean_ctor_set(v_reuseFailAlloc_3122_, 8, v_snapshotTasks_3095_);
v___x_3116_ = v_reuseFailAlloc_3122_;
goto v_reusejp_3115_;
}
v_reusejp_3115_:
{
lean_object* v___x_3117_; lean_object* v___x_3118_; lean_object* v___x_3120_; 
v___x_3117_ = lean_st_ref_set(v___y_3078_, v___x_3116_);
v___x_3118_ = lean_box(0);
if (v_isShared_3085_ == 0)
{
lean_ctor_set(v___x_3084_, 0, v___x_3118_);
v___x_3120_ = v___x_3084_;
goto v_reusejp_3119_;
}
else
{
lean_object* v_reuseFailAlloc_3121_; 
v_reuseFailAlloc_3121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3121_, 0, v___x_3118_);
v___x_3120_ = v_reuseFailAlloc_3121_;
goto v_reusejp_3119_;
}
v_reusejp_3119_:
{
return v___x_3120_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__6___redArg___boxed(lean_object* v_cls_3127_, lean_object* v_msg_3128_, lean_object* v___y_3129_, lean_object* v___y_3130_, lean_object* v___y_3131_, lean_object* v___y_3132_, lean_object* v___y_3133_){
_start:
{
lean_object* v_res_3134_; 
v_res_3134_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__6___redArg(v_cls_3127_, v_msg_3128_, v___y_3129_, v___y_3130_, v___y_3131_, v___y_3132_);
lean_dec(v___y_3132_);
lean_dec_ref(v___y_3131_);
lean_dec(v___y_3130_);
lean_dec_ref(v___y_3129_);
return v_res_3134_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__2___redArg(lean_object* v_cls_3135_, lean_object* v_msg_3136_, lean_object* v___y_3137_, lean_object* v___y_3138_, lean_object* v___y_3139_, lean_object* v___y_3140_){
_start:
{
lean_object* v_ref_3142_; lean_object* v___x_3143_; lean_object* v_a_3144_; lean_object* v___x_3146_; uint8_t v_isShared_3147_; uint8_t v_isSharedCheck_3188_; 
v_ref_3142_ = lean_ctor_get(v___y_3139_, 5);
v___x_3143_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1_spec__5_spec__8_spec__9(v_msg_3136_, v___y_3137_, v___y_3138_, v___y_3139_, v___y_3140_);
v_a_3144_ = lean_ctor_get(v___x_3143_, 0);
v_isSharedCheck_3188_ = !lean_is_exclusive(v___x_3143_);
if (v_isSharedCheck_3188_ == 0)
{
v___x_3146_ = v___x_3143_;
v_isShared_3147_ = v_isSharedCheck_3188_;
goto v_resetjp_3145_;
}
else
{
lean_inc(v_a_3144_);
lean_dec(v___x_3143_);
v___x_3146_ = lean_box(0);
v_isShared_3147_ = v_isSharedCheck_3188_;
goto v_resetjp_3145_;
}
v_resetjp_3145_:
{
lean_object* v___x_3148_; lean_object* v_traceState_3149_; lean_object* v_env_3150_; lean_object* v_nextMacroScope_3151_; lean_object* v_ngen_3152_; lean_object* v_auxDeclNGen_3153_; lean_object* v_cache_3154_; lean_object* v_messages_3155_; lean_object* v_infoState_3156_; lean_object* v_snapshotTasks_3157_; lean_object* v___x_3159_; uint8_t v_isShared_3160_; uint8_t v_isSharedCheck_3187_; 
v___x_3148_ = lean_st_ref_take(v___y_3140_);
v_traceState_3149_ = lean_ctor_get(v___x_3148_, 4);
v_env_3150_ = lean_ctor_get(v___x_3148_, 0);
v_nextMacroScope_3151_ = lean_ctor_get(v___x_3148_, 1);
v_ngen_3152_ = lean_ctor_get(v___x_3148_, 2);
v_auxDeclNGen_3153_ = lean_ctor_get(v___x_3148_, 3);
v_cache_3154_ = lean_ctor_get(v___x_3148_, 5);
v_messages_3155_ = lean_ctor_get(v___x_3148_, 6);
v_infoState_3156_ = lean_ctor_get(v___x_3148_, 7);
v_snapshotTasks_3157_ = lean_ctor_get(v___x_3148_, 8);
v_isSharedCheck_3187_ = !lean_is_exclusive(v___x_3148_);
if (v_isSharedCheck_3187_ == 0)
{
v___x_3159_ = v___x_3148_;
v_isShared_3160_ = v_isSharedCheck_3187_;
goto v_resetjp_3158_;
}
else
{
lean_inc(v_snapshotTasks_3157_);
lean_inc(v_infoState_3156_);
lean_inc(v_messages_3155_);
lean_inc(v_cache_3154_);
lean_inc(v_traceState_3149_);
lean_inc(v_auxDeclNGen_3153_);
lean_inc(v_ngen_3152_);
lean_inc(v_nextMacroScope_3151_);
lean_inc(v_env_3150_);
lean_dec(v___x_3148_);
v___x_3159_ = lean_box(0);
v_isShared_3160_ = v_isSharedCheck_3187_;
goto v_resetjp_3158_;
}
v_resetjp_3158_:
{
uint64_t v_tid_3161_; lean_object* v_traces_3162_; lean_object* v___x_3164_; uint8_t v_isShared_3165_; uint8_t v_isSharedCheck_3186_; 
v_tid_3161_ = lean_ctor_get_uint64(v_traceState_3149_, sizeof(void*)*1);
v_traces_3162_ = lean_ctor_get(v_traceState_3149_, 0);
v_isSharedCheck_3186_ = !lean_is_exclusive(v_traceState_3149_);
if (v_isSharedCheck_3186_ == 0)
{
v___x_3164_ = v_traceState_3149_;
v_isShared_3165_ = v_isSharedCheck_3186_;
goto v_resetjp_3163_;
}
else
{
lean_inc(v_traces_3162_);
lean_dec(v_traceState_3149_);
v___x_3164_ = lean_box(0);
v_isShared_3165_ = v_isSharedCheck_3186_;
goto v_resetjp_3163_;
}
v_resetjp_3163_:
{
lean_object* v___x_3166_; double v___x_3167_; uint8_t v___x_3168_; lean_object* v___x_3169_; lean_object* v___x_3170_; lean_object* v___x_3171_; lean_object* v___x_3172_; lean_object* v___x_3173_; lean_object* v___x_3174_; lean_object* v___x_3176_; 
v___x_3166_ = lean_box(0);
v___x_3167_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__4___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__4___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__4___redArg___closed__0);
v___x_3168_ = 0;
v___x_3169_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__4___redArg___closed__1));
v___x_3170_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3170_, 0, v_cls_3135_);
lean_ctor_set(v___x_3170_, 1, v___x_3166_);
lean_ctor_set(v___x_3170_, 2, v___x_3169_);
lean_ctor_set_float(v___x_3170_, sizeof(void*)*3, v___x_3167_);
lean_ctor_set_float(v___x_3170_, sizeof(void*)*3 + 8, v___x_3167_);
lean_ctor_set_uint8(v___x_3170_, sizeof(void*)*3 + 16, v___x_3168_);
v___x_3171_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__4___redArg___closed__2));
v___x_3172_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3172_, 0, v___x_3170_);
lean_ctor_set(v___x_3172_, 1, v_a_3144_);
lean_ctor_set(v___x_3172_, 2, v___x_3171_);
lean_inc(v_ref_3142_);
v___x_3173_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3173_, 0, v_ref_3142_);
lean_ctor_set(v___x_3173_, 1, v___x_3172_);
v___x_3174_ = l_Lean_PersistentArray_push___redArg(v_traces_3162_, v___x_3173_);
if (v_isShared_3165_ == 0)
{
lean_ctor_set(v___x_3164_, 0, v___x_3174_);
v___x_3176_ = v___x_3164_;
goto v_reusejp_3175_;
}
else
{
lean_object* v_reuseFailAlloc_3185_; 
v_reuseFailAlloc_3185_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3185_, 0, v___x_3174_);
lean_ctor_set_uint64(v_reuseFailAlloc_3185_, sizeof(void*)*1, v_tid_3161_);
v___x_3176_ = v_reuseFailAlloc_3185_;
goto v_reusejp_3175_;
}
v_reusejp_3175_:
{
lean_object* v___x_3178_; 
if (v_isShared_3160_ == 0)
{
lean_ctor_set(v___x_3159_, 4, v___x_3176_);
v___x_3178_ = v___x_3159_;
goto v_reusejp_3177_;
}
else
{
lean_object* v_reuseFailAlloc_3184_; 
v_reuseFailAlloc_3184_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3184_, 0, v_env_3150_);
lean_ctor_set(v_reuseFailAlloc_3184_, 1, v_nextMacroScope_3151_);
lean_ctor_set(v_reuseFailAlloc_3184_, 2, v_ngen_3152_);
lean_ctor_set(v_reuseFailAlloc_3184_, 3, v_auxDeclNGen_3153_);
lean_ctor_set(v_reuseFailAlloc_3184_, 4, v___x_3176_);
lean_ctor_set(v_reuseFailAlloc_3184_, 5, v_cache_3154_);
lean_ctor_set(v_reuseFailAlloc_3184_, 6, v_messages_3155_);
lean_ctor_set(v_reuseFailAlloc_3184_, 7, v_infoState_3156_);
lean_ctor_set(v_reuseFailAlloc_3184_, 8, v_snapshotTasks_3157_);
v___x_3178_ = v_reuseFailAlloc_3184_;
goto v_reusejp_3177_;
}
v_reusejp_3177_:
{
lean_object* v___x_3179_; lean_object* v___x_3180_; lean_object* v___x_3182_; 
v___x_3179_ = lean_st_ref_set(v___y_3140_, v___x_3178_);
v___x_3180_ = lean_box(0);
if (v_isShared_3147_ == 0)
{
lean_ctor_set(v___x_3146_, 0, v___x_3180_);
v___x_3182_ = v___x_3146_;
goto v_reusejp_3181_;
}
else
{
lean_object* v_reuseFailAlloc_3183_; 
v_reuseFailAlloc_3183_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3183_, 0, v___x_3180_);
v___x_3182_ = v_reuseFailAlloc_3183_;
goto v_reusejp_3181_;
}
v_reusejp_3181_:
{
return v___x_3182_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__2___redArg___boxed(lean_object* v_cls_3189_, lean_object* v_msg_3190_, lean_object* v___y_3191_, lean_object* v___y_3192_, lean_object* v___y_3193_, lean_object* v___y_3194_, lean_object* v___y_3195_){
_start:
{
lean_object* v_res_3196_; 
v_res_3196_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__2___redArg(v_cls_3189_, v_msg_3190_, v___y_3191_, v___y_3192_, v___y_3193_, v___y_3194_);
lean_dec(v___y_3194_);
lean_dec_ref(v___y_3193_);
lean_dec(v___y_3192_);
lean_dec_ref(v___y_3191_);
return v_res_3196_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__8___redArg(lean_object* v_cls_3197_, lean_object* v_msg_3198_, lean_object* v___y_3199_, lean_object* v___y_3200_, lean_object* v___y_3201_, lean_object* v___y_3202_){
_start:
{
lean_object* v_ref_3204_; lean_object* v___x_3205_; lean_object* v_a_3206_; lean_object* v___x_3208_; uint8_t v_isShared_3209_; uint8_t v_isSharedCheck_3250_; 
v_ref_3204_ = lean_ctor_get(v___y_3201_, 5);
v___x_3205_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1_spec__5_spec__8_spec__9(v_msg_3198_, v___y_3199_, v___y_3200_, v___y_3201_, v___y_3202_);
v_a_3206_ = lean_ctor_get(v___x_3205_, 0);
v_isSharedCheck_3250_ = !lean_is_exclusive(v___x_3205_);
if (v_isSharedCheck_3250_ == 0)
{
v___x_3208_ = v___x_3205_;
v_isShared_3209_ = v_isSharedCheck_3250_;
goto v_resetjp_3207_;
}
else
{
lean_inc(v_a_3206_);
lean_dec(v___x_3205_);
v___x_3208_ = lean_box(0);
v_isShared_3209_ = v_isSharedCheck_3250_;
goto v_resetjp_3207_;
}
v_resetjp_3207_:
{
lean_object* v___x_3210_; lean_object* v_traceState_3211_; lean_object* v_env_3212_; lean_object* v_nextMacroScope_3213_; lean_object* v_ngen_3214_; lean_object* v_auxDeclNGen_3215_; lean_object* v_cache_3216_; lean_object* v_messages_3217_; lean_object* v_infoState_3218_; lean_object* v_snapshotTasks_3219_; lean_object* v___x_3221_; uint8_t v_isShared_3222_; uint8_t v_isSharedCheck_3249_; 
v___x_3210_ = lean_st_ref_take(v___y_3202_);
v_traceState_3211_ = lean_ctor_get(v___x_3210_, 4);
v_env_3212_ = lean_ctor_get(v___x_3210_, 0);
v_nextMacroScope_3213_ = lean_ctor_get(v___x_3210_, 1);
v_ngen_3214_ = lean_ctor_get(v___x_3210_, 2);
v_auxDeclNGen_3215_ = lean_ctor_get(v___x_3210_, 3);
v_cache_3216_ = lean_ctor_get(v___x_3210_, 5);
v_messages_3217_ = lean_ctor_get(v___x_3210_, 6);
v_infoState_3218_ = lean_ctor_get(v___x_3210_, 7);
v_snapshotTasks_3219_ = lean_ctor_get(v___x_3210_, 8);
v_isSharedCheck_3249_ = !lean_is_exclusive(v___x_3210_);
if (v_isSharedCheck_3249_ == 0)
{
v___x_3221_ = v___x_3210_;
v_isShared_3222_ = v_isSharedCheck_3249_;
goto v_resetjp_3220_;
}
else
{
lean_inc(v_snapshotTasks_3219_);
lean_inc(v_infoState_3218_);
lean_inc(v_messages_3217_);
lean_inc(v_cache_3216_);
lean_inc(v_traceState_3211_);
lean_inc(v_auxDeclNGen_3215_);
lean_inc(v_ngen_3214_);
lean_inc(v_nextMacroScope_3213_);
lean_inc(v_env_3212_);
lean_dec(v___x_3210_);
v___x_3221_ = lean_box(0);
v_isShared_3222_ = v_isSharedCheck_3249_;
goto v_resetjp_3220_;
}
v_resetjp_3220_:
{
uint64_t v_tid_3223_; lean_object* v_traces_3224_; lean_object* v___x_3226_; uint8_t v_isShared_3227_; uint8_t v_isSharedCheck_3248_; 
v_tid_3223_ = lean_ctor_get_uint64(v_traceState_3211_, sizeof(void*)*1);
v_traces_3224_ = lean_ctor_get(v_traceState_3211_, 0);
v_isSharedCheck_3248_ = !lean_is_exclusive(v_traceState_3211_);
if (v_isSharedCheck_3248_ == 0)
{
v___x_3226_ = v_traceState_3211_;
v_isShared_3227_ = v_isSharedCheck_3248_;
goto v_resetjp_3225_;
}
else
{
lean_inc(v_traces_3224_);
lean_dec(v_traceState_3211_);
v___x_3226_ = lean_box(0);
v_isShared_3227_ = v_isSharedCheck_3248_;
goto v_resetjp_3225_;
}
v_resetjp_3225_:
{
lean_object* v___x_3228_; double v___x_3229_; uint8_t v___x_3230_; lean_object* v___x_3231_; lean_object* v___x_3232_; lean_object* v___x_3233_; lean_object* v___x_3234_; lean_object* v___x_3235_; lean_object* v___x_3236_; lean_object* v___x_3238_; 
v___x_3228_ = lean_box(0);
v___x_3229_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__4___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__4___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__4___redArg___closed__0);
v___x_3230_ = 0;
v___x_3231_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__4___redArg___closed__1));
v___x_3232_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3232_, 0, v_cls_3197_);
lean_ctor_set(v___x_3232_, 1, v___x_3228_);
lean_ctor_set(v___x_3232_, 2, v___x_3231_);
lean_ctor_set_float(v___x_3232_, sizeof(void*)*3, v___x_3229_);
lean_ctor_set_float(v___x_3232_, sizeof(void*)*3 + 8, v___x_3229_);
lean_ctor_set_uint8(v___x_3232_, sizeof(void*)*3 + 16, v___x_3230_);
v___x_3233_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__4___redArg___closed__2));
v___x_3234_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3234_, 0, v___x_3232_);
lean_ctor_set(v___x_3234_, 1, v_a_3206_);
lean_ctor_set(v___x_3234_, 2, v___x_3233_);
lean_inc(v_ref_3204_);
v___x_3235_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3235_, 0, v_ref_3204_);
lean_ctor_set(v___x_3235_, 1, v___x_3234_);
v___x_3236_ = l_Lean_PersistentArray_push___redArg(v_traces_3224_, v___x_3235_);
if (v_isShared_3227_ == 0)
{
lean_ctor_set(v___x_3226_, 0, v___x_3236_);
v___x_3238_ = v___x_3226_;
goto v_reusejp_3237_;
}
else
{
lean_object* v_reuseFailAlloc_3247_; 
v_reuseFailAlloc_3247_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3247_, 0, v___x_3236_);
lean_ctor_set_uint64(v_reuseFailAlloc_3247_, sizeof(void*)*1, v_tid_3223_);
v___x_3238_ = v_reuseFailAlloc_3247_;
goto v_reusejp_3237_;
}
v_reusejp_3237_:
{
lean_object* v___x_3240_; 
if (v_isShared_3222_ == 0)
{
lean_ctor_set(v___x_3221_, 4, v___x_3238_);
v___x_3240_ = v___x_3221_;
goto v_reusejp_3239_;
}
else
{
lean_object* v_reuseFailAlloc_3246_; 
v_reuseFailAlloc_3246_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3246_, 0, v_env_3212_);
lean_ctor_set(v_reuseFailAlloc_3246_, 1, v_nextMacroScope_3213_);
lean_ctor_set(v_reuseFailAlloc_3246_, 2, v_ngen_3214_);
lean_ctor_set(v_reuseFailAlloc_3246_, 3, v_auxDeclNGen_3215_);
lean_ctor_set(v_reuseFailAlloc_3246_, 4, v___x_3238_);
lean_ctor_set(v_reuseFailAlloc_3246_, 5, v_cache_3216_);
lean_ctor_set(v_reuseFailAlloc_3246_, 6, v_messages_3217_);
lean_ctor_set(v_reuseFailAlloc_3246_, 7, v_infoState_3218_);
lean_ctor_set(v_reuseFailAlloc_3246_, 8, v_snapshotTasks_3219_);
v___x_3240_ = v_reuseFailAlloc_3246_;
goto v_reusejp_3239_;
}
v_reusejp_3239_:
{
lean_object* v___x_3241_; lean_object* v___x_3242_; lean_object* v___x_3244_; 
v___x_3241_ = lean_st_ref_set(v___y_3202_, v___x_3240_);
v___x_3242_ = lean_box(0);
if (v_isShared_3209_ == 0)
{
lean_ctor_set(v___x_3208_, 0, v___x_3242_);
v___x_3244_ = v___x_3208_;
goto v_reusejp_3243_;
}
else
{
lean_object* v_reuseFailAlloc_3245_; 
v_reuseFailAlloc_3245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3245_, 0, v___x_3242_);
v___x_3244_ = v_reuseFailAlloc_3245_;
goto v_reusejp_3243_;
}
v_reusejp_3243_:
{
return v___x_3244_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__8___redArg___boxed(lean_object* v_cls_3251_, lean_object* v_msg_3252_, lean_object* v___y_3253_, lean_object* v___y_3254_, lean_object* v___y_3255_, lean_object* v___y_3256_, lean_object* v___y_3257_){
_start:
{
lean_object* v_res_3258_; 
v_res_3258_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__8___redArg(v_cls_3251_, v_msg_3252_, v___y_3253_, v___y_3254_, v___y_3255_, v___y_3256_);
lean_dec(v___y_3256_);
lean_dec_ref(v___y_3255_);
lean_dec(v___y_3254_);
lean_dec_ref(v___y_3253_);
return v_res_3258_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__5(void){
_start:
{
lean_object* v___x_3267_; lean_object* v___x_3268_; 
v___x_3267_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__4));
v___x_3268_ = l_Lean_stringToMessageData(v___x_3267_);
return v___x_3268_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__7(void){
_start:
{
lean_object* v___x_3270_; lean_object* v___x_3271_; 
v___x_3270_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__6));
v___x_3271_ = l_Lean_stringToMessageData(v___x_3270_);
return v___x_3271_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__9(void){
_start:
{
lean_object* v___x_3273_; lean_object* v___x_3274_; 
v___x_3273_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__8));
v___x_3274_ = l_Lean_stringToMessageData(v___x_3273_);
return v___x_3274_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__11(void){
_start:
{
lean_object* v___x_3276_; lean_object* v___x_3277_; 
v___x_3276_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__10));
v___x_3277_ = l_Lean_stringToMessageData(v___x_3276_);
return v___x_3277_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__13(void){
_start:
{
lean_object* v___x_3279_; lean_object* v___x_3280_; 
v___x_3279_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__12));
v___x_3280_ = l_Lean_stringToMessageData(v___x_3279_);
return v___x_3280_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_internalize(lean_object* v_e_3281_, lean_object* v_parent_x3f_3282_, lean_object* v_a_3283_, lean_object* v_a_3284_, lean_object* v_a_3285_, lean_object* v_a_3286_, lean_object* v_a_3287_, lean_object* v_a_3288_, lean_object* v_a_3289_, lean_object* v_a_3290_, lean_object* v_a_3291_, lean_object* v_a_3292_){
_start:
{
lean_object* v___x_3294_; 
v___x_3294_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_3285_);
if (lean_obj_tag(v___x_3294_) == 0)
{
lean_object* v_a_3295_; lean_object* v___x_3297_; uint8_t v_isShared_3298_; uint8_t v_isSharedCheck_3626_; 
v_a_3295_ = lean_ctor_get(v___x_3294_, 0);
v_isSharedCheck_3626_ = !lean_is_exclusive(v___x_3294_);
if (v_isSharedCheck_3626_ == 0)
{
v___x_3297_ = v___x_3294_;
v_isShared_3298_ = v_isSharedCheck_3626_;
goto v_resetjp_3296_;
}
else
{
lean_inc(v_a_3295_);
lean_dec(v___x_3294_);
v___x_3297_ = lean_box(0);
v_isShared_3298_ = v_isSharedCheck_3626_;
goto v_resetjp_3296_;
}
v_resetjp_3296_:
{
uint8_t v_ring_3299_; 
v_ring_3299_ = lean_ctor_get_uint8(v_a_3295_, sizeof(void*)*11 + 21);
lean_dec(v_a_3295_);
if (v_ring_3299_ == 0)
{
lean_object* v___x_3300_; lean_object* v___x_3302_; 
lean_dec(v_a_3292_);
lean_dec_ref(v_a_3291_);
lean_dec(v_a_3290_);
lean_dec_ref(v_a_3289_);
lean_dec(v_a_3288_);
lean_dec_ref(v_a_3287_);
lean_dec(v_a_3286_);
lean_dec_ref(v_a_3285_);
lean_dec(v_a_3284_);
lean_dec(v_a_3283_);
lean_dec(v_parent_x3f_3282_);
lean_dec_ref(v_e_3281_);
v___x_3300_ = lean_box(0);
if (v_isShared_3298_ == 0)
{
lean_ctor_set(v___x_3297_, 0, v___x_3300_);
v___x_3302_ = v___x_3297_;
goto v_reusejp_3301_;
}
else
{
lean_object* v_reuseFailAlloc_3303_; 
v_reuseFailAlloc_3303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3303_, 0, v___x_3300_);
v___x_3302_ = v_reuseFailAlloc_3303_;
goto v_reusejp_3301_;
}
v_reusejp_3301_:
{
return v___x_3302_;
}
}
else
{
uint8_t v___x_3304_; 
v___x_3304_ = l_Lean_Meta_Grind_Arith_isIntModuleVirtualParent(v_parent_x3f_3282_);
if (v___x_3304_ == 0)
{
lean_object* v___x_3305_; 
lean_del_object(v___x_3297_);
lean_inc(v_a_3292_);
lean_inc_ref(v_a_3291_);
lean_inc(v_a_3290_);
lean_inc_ref(v_a_3289_);
lean_inc(v_a_3288_);
lean_inc_ref(v_a_3287_);
lean_inc(v_a_3286_);
lean_inc_ref(v_a_3285_);
lean_inc(v_a_3284_);
lean_inc(v_a_3283_);
lean_inc_ref(v_e_3281_);
v___x_3305_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeInv(v_e_3281_, v_a_3283_, v_a_3284_, v_a_3285_, v_a_3286_, v_a_3287_, v_a_3288_, v_a_3289_, v_a_3290_, v_a_3291_, v_a_3292_);
if (lean_obj_tag(v___x_3305_) == 0)
{
lean_object* v_a_3306_; lean_object* v___x_3308_; uint8_t v_isShared_3309_; uint8_t v_isSharedCheck_3613_; 
v_a_3306_ = lean_ctor_get(v___x_3305_, 0);
v_isSharedCheck_3613_ = !lean_is_exclusive(v___x_3305_);
if (v_isSharedCheck_3613_ == 0)
{
v___x_3308_ = v___x_3305_;
v_isShared_3309_ = v_isSharedCheck_3613_;
goto v_resetjp_3307_;
}
else
{
lean_inc(v_a_3306_);
lean_dec(v___x_3305_);
v___x_3308_ = lean_box(0);
v_isShared_3309_ = v_isSharedCheck_3613_;
goto v_resetjp_3307_;
}
v_resetjp_3307_:
{
uint8_t v___x_3310_; 
v___x_3310_ = lean_unbox(v_a_3306_);
lean_dec(v_a_3306_);
if (v___x_3310_ == 0)
{
lean_object* v___x_3311_; 
lean_inc_ref(v_e_3281_);
v___x_3311_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f(v_e_3281_);
if (lean_obj_tag(v___x_3311_) == 1)
{
lean_object* v_val_3312_; uint8_t v___x_3313_; 
v_val_3312_ = lean_ctor_get(v___x_3311_, 0);
lean_inc(v_val_3312_);
lean_dec_ref(v___x_3311_);
v___x_3313_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isForbiddenParent(v_parent_x3f_3282_);
if (v___x_3313_ == 0)
{
lean_object* v___x_3314_; 
lean_del_object(v___x_3308_);
lean_inc(v_a_3292_);
lean_inc_ref(v_a_3291_);
lean_inc(v_a_3290_);
lean_inc_ref(v_a_3289_);
lean_inc(v_a_3288_);
lean_inc_ref(v_a_3287_);
lean_inc(v_a_3286_);
lean_inc_ref(v_a_3285_);
lean_inc(v_a_3284_);
lean_inc(v_a_3283_);
lean_inc(v_val_3312_);
v___x_3314_ = l_Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f(v_val_3312_, v_a_3283_, v_a_3284_, v_a_3285_, v_a_3286_, v_a_3287_, v_a_3288_, v_a_3289_, v_a_3290_, v_a_3291_, v_a_3292_);
if (lean_obj_tag(v___x_3314_) == 0)
{
lean_object* v_a_3315_; 
v_a_3315_ = lean_ctor_get(v___x_3314_, 0);
lean_inc(v_a_3315_);
lean_dec_ref(v___x_3314_);
if (lean_obj_tag(v_a_3315_) == 1)
{
lean_object* v_val_3316_; lean_object* v___x_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; 
lean_dec(v_val_3312_);
v_val_3316_ = lean_ctor_get(v_a_3315_, 0);
lean_inc(v_val_3316_);
lean_dec_ref(v_a_3315_);
v___x_3317_ = lean_unsigned_to_nat(0u);
lean_inc(v_val_3316_);
v___x_3318_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3318_, 0, v_val_3316_);
lean_ctor_set_uint8(v___x_3318_, sizeof(void*)*1, v___x_3313_);
lean_inc(v_a_3292_);
lean_inc_ref(v_a_3291_);
lean_inc(v_a_3290_);
lean_inc_ref(v_a_3289_);
lean_inc(v_a_3288_);
lean_inc_ref(v_a_3287_);
lean_inc(v_a_3286_);
lean_inc_ref(v_a_3285_);
lean_inc(v_a_3284_);
lean_inc(v_a_3283_);
lean_inc_ref(v___x_3318_);
lean_inc_ref(v_e_3281_);
v___x_3319_ = l_Lean_Meta_Grind_Arith_CommRing_reify_x3f(v_e_3281_, v_ring_3299_, v___x_3317_, v___x_3318_, v_a_3283_, v_a_3284_, v_a_3285_, v_a_3286_, v_a_3287_, v_a_3288_, v_a_3289_, v_a_3290_, v_a_3291_, v_a_3292_);
if (lean_obj_tag(v___x_3319_) == 0)
{
lean_object* v_a_3320_; lean_object* v___x_3322_; uint8_t v_isShared_3323_; uint8_t v_isSharedCheck_3368_; 
v_a_3320_ = lean_ctor_get(v___x_3319_, 0);
v_isSharedCheck_3368_ = !lean_is_exclusive(v___x_3319_);
if (v_isSharedCheck_3368_ == 0)
{
v___x_3322_ = v___x_3319_;
v_isShared_3323_ = v_isSharedCheck_3368_;
goto v_resetjp_3321_;
}
else
{
lean_inc(v_a_3320_);
lean_dec(v___x_3319_);
v___x_3322_ = lean_box(0);
v_isShared_3323_ = v_isSharedCheck_3368_;
goto v_resetjp_3321_;
}
v_resetjp_3321_:
{
if (lean_obj_tag(v_a_3320_) == 1)
{
lean_object* v_val_3324_; lean_object* v___x_3325_; lean_object* v___x_3326_; lean_object* v_a_3327_; lean_object* v___f_3328_; lean_object* v___y_3330_; lean_object* v___y_3331_; lean_object* v___y_3332_; lean_object* v___y_3333_; lean_object* v___y_3334_; lean_object* v___y_3335_; lean_object* v___y_3336_; lean_object* v___y_3337_; lean_object* v___y_3338_; lean_object* v___y_3339_; lean_object* v___y_3340_; uint8_t v___x_3345_; 
lean_del_object(v___x_3322_);
v_val_3324_ = lean_ctor_get(v_a_3320_, 0);
lean_inc(v_val_3324_);
lean_dec_ref(v_a_3320_);
v___x_3325_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__3));
v___x_3326_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__1___redArg(v___x_3325_, v_a_3291_);
v_a_3327_ = lean_ctor_get(v___x_3326_, 0);
lean_inc(v_a_3327_);
lean_dec_ref(v___x_3326_);
lean_inc_ref(v_e_3281_);
v___f_3328_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_internalize___lam__0), 3, 2);
lean_closure_set(v___f_3328_, 0, v_e_3281_);
lean_closure_set(v___f_3328_, 1, v_val_3324_);
v___x_3345_ = lean_unbox(v_a_3327_);
lean_dec(v_a_3327_);
if (v___x_3345_ == 0)
{
lean_dec(v_val_3316_);
v___y_3330_ = v___x_3318_;
v___y_3331_ = v_a_3283_;
v___y_3332_ = v_a_3284_;
v___y_3333_ = v_a_3285_;
v___y_3334_ = v_a_3286_;
v___y_3335_ = v_a_3287_;
v___y_3336_ = v_a_3288_;
v___y_3337_ = v_a_3289_;
v___y_3338_ = v_a_3290_;
v___y_3339_ = v_a_3291_;
v___y_3340_ = v_a_3292_;
goto v___jp_3329_;
}
else
{
lean_object* v___x_3346_; 
v___x_3346_ = l_Lean_Meta_Grind_updateLastTag(v_a_3283_, v_a_3284_, v_a_3285_, v_a_3286_, v_a_3287_, v_a_3288_, v_a_3289_, v_a_3290_, v_a_3291_, v_a_3292_);
if (lean_obj_tag(v___x_3346_) == 0)
{
lean_object* v___x_3348_; uint8_t v_isShared_3349_; uint8_t v_isSharedCheck_3362_; 
v_isSharedCheck_3362_ = !lean_is_exclusive(v___x_3346_);
if (v_isSharedCheck_3362_ == 0)
{
lean_object* v_unused_3363_; 
v_unused_3363_ = lean_ctor_get(v___x_3346_, 0);
lean_dec(v_unused_3363_);
v___x_3348_ = v___x_3346_;
v_isShared_3349_ = v_isSharedCheck_3362_;
goto v_resetjp_3347_;
}
else
{
lean_dec(v___x_3346_);
v___x_3348_ = lean_box(0);
v_isShared_3349_ = v_isSharedCheck_3362_;
goto v_resetjp_3347_;
}
v_resetjp_3347_:
{
lean_object* v___x_3350_; lean_object* v___x_3351_; lean_object* v___x_3353_; 
v___x_3350_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__5, &l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__5_once, _init_l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__5);
v___x_3351_ = l_Nat_reprFast(v_val_3316_);
if (v_isShared_3349_ == 0)
{
lean_ctor_set_tag(v___x_3348_, 3);
lean_ctor_set(v___x_3348_, 0, v___x_3351_);
v___x_3353_ = v___x_3348_;
goto v_reusejp_3352_;
}
else
{
lean_object* v_reuseFailAlloc_3361_; 
v_reuseFailAlloc_3361_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3361_, 0, v___x_3351_);
v___x_3353_ = v_reuseFailAlloc_3361_;
goto v_reusejp_3352_;
}
v_reusejp_3352_:
{
lean_object* v___x_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; 
v___x_3354_ = l_Lean_MessageData_ofFormat(v___x_3353_);
v___x_3355_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3355_, 0, v___x_3350_);
lean_ctor_set(v___x_3355_, 1, v___x_3354_);
v___x_3356_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__7, &l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__7_once, _init_l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__7);
v___x_3357_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3357_, 0, v___x_3355_);
lean_ctor_set(v___x_3357_, 1, v___x_3356_);
lean_inc_ref(v_e_3281_);
v___x_3358_ = l_Lean_MessageData_ofExpr(v_e_3281_);
v___x_3359_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3359_, 0, v___x_3357_);
lean_ctor_set(v___x_3359_, 1, v___x_3358_);
v___x_3360_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__2___redArg(v___x_3325_, v___x_3359_, v_a_3289_, v_a_3290_, v_a_3291_, v_a_3292_);
if (lean_obj_tag(v___x_3360_) == 0)
{
lean_dec_ref(v___x_3360_);
v___y_3330_ = v___x_3318_;
v___y_3331_ = v_a_3283_;
v___y_3332_ = v_a_3284_;
v___y_3333_ = v_a_3285_;
v___y_3334_ = v_a_3286_;
v___y_3335_ = v_a_3287_;
v___y_3336_ = v_a_3288_;
v___y_3337_ = v_a_3289_;
v___y_3338_ = v_a_3290_;
v___y_3339_ = v_a_3291_;
v___y_3340_ = v_a_3292_;
goto v___jp_3329_;
}
else
{
lean_dec_ref(v___f_3328_);
lean_dec_ref(v___x_3318_);
lean_dec(v_a_3292_);
lean_dec_ref(v_a_3291_);
lean_dec(v_a_3290_);
lean_dec_ref(v_a_3289_);
lean_dec(v_a_3288_);
lean_dec_ref(v_a_3287_);
lean_dec(v_a_3286_);
lean_dec_ref(v_a_3285_);
lean_dec(v_a_3284_);
lean_dec(v_a_3283_);
lean_dec_ref(v_e_3281_);
return v___x_3360_;
}
}
}
}
else
{
lean_dec_ref(v___f_3328_);
lean_dec_ref(v___x_3318_);
lean_dec(v_val_3316_);
lean_dec(v_a_3292_);
lean_dec_ref(v_a_3291_);
lean_dec(v_a_3290_);
lean_dec_ref(v_a_3289_);
lean_dec(v_a_3288_);
lean_dec_ref(v_a_3287_);
lean_dec(v_a_3286_);
lean_dec_ref(v_a_3285_);
lean_dec(v_a_3284_);
lean_dec(v_a_3283_);
lean_dec_ref(v_e_3281_);
return v___x_3346_;
}
}
v___jp_3329_:
{
lean_object* v___x_3341_; 
lean_inc_ref(v___y_3330_);
lean_inc_ref(v_e_3281_);
v___x_3341_ = l_Lean_Meta_Grind_Arith_CommRing_setTermRingId(v_e_3281_, v___y_3330_, v___y_3331_, v___y_3332_, v___y_3333_, v___y_3334_, v___y_3335_, v___y_3336_, v___y_3337_, v___y_3338_, v___y_3339_, v___y_3340_);
if (lean_obj_tag(v___x_3341_) == 0)
{
lean_object* v___x_3342_; lean_object* v___x_3343_; 
lean_dec_ref(v___x_3341_);
v___x_3342_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
lean_inc(v___y_3331_);
v___x_3343_ = l_Lean_Meta_Grind_SolverExtension_markTerm___redArg(v___x_3342_, v_e_3281_, v___y_3331_, v___y_3332_, v___y_3333_, v___y_3334_, v___y_3335_, v___y_3336_, v___y_3337_, v___y_3338_, v___y_3339_, v___y_3340_);
if (lean_obj_tag(v___x_3343_) == 0)
{
lean_object* v___x_3344_; 
lean_dec_ref(v___x_3343_);
v___x_3344_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(v___f_3328_, v___y_3330_, v___y_3331_);
lean_dec(v___y_3331_);
return v___x_3344_;
}
else
{
lean_dec(v___y_3331_);
lean_dec_ref(v___y_3330_);
lean_dec_ref(v___f_3328_);
return v___x_3343_;
}
}
else
{
lean_dec(v___y_3340_);
lean_dec_ref(v___y_3339_);
lean_dec(v___y_3338_);
lean_dec_ref(v___y_3337_);
lean_dec(v___y_3336_);
lean_dec_ref(v___y_3335_);
lean_dec(v___y_3334_);
lean_dec_ref(v___y_3333_);
lean_dec(v___y_3332_);
lean_dec(v___y_3331_);
lean_dec_ref(v___y_3330_);
lean_dec_ref(v___f_3328_);
lean_dec_ref(v_e_3281_);
return v___x_3341_;
}
}
}
else
{
lean_object* v___x_3364_; lean_object* v___x_3366_; 
lean_dec(v_a_3320_);
lean_dec_ref(v___x_3318_);
lean_dec(v_val_3316_);
lean_dec(v_a_3292_);
lean_dec_ref(v_a_3291_);
lean_dec(v_a_3290_);
lean_dec_ref(v_a_3289_);
lean_dec(v_a_3288_);
lean_dec_ref(v_a_3287_);
lean_dec(v_a_3286_);
lean_dec_ref(v_a_3285_);
lean_dec(v_a_3284_);
lean_dec(v_a_3283_);
lean_dec_ref(v_e_3281_);
v___x_3364_ = lean_box(0);
if (v_isShared_3323_ == 0)
{
lean_ctor_set(v___x_3322_, 0, v___x_3364_);
v___x_3366_ = v___x_3322_;
goto v_reusejp_3365_;
}
else
{
lean_object* v_reuseFailAlloc_3367_; 
v_reuseFailAlloc_3367_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3367_, 0, v___x_3364_);
v___x_3366_ = v_reuseFailAlloc_3367_;
goto v_reusejp_3365_;
}
v_reusejp_3365_:
{
return v___x_3366_;
}
}
}
}
else
{
lean_object* v_a_3369_; lean_object* v___x_3371_; uint8_t v_isShared_3372_; uint8_t v_isSharedCheck_3376_; 
lean_dec_ref(v___x_3318_);
lean_dec(v_val_3316_);
lean_dec(v_a_3292_);
lean_dec_ref(v_a_3291_);
lean_dec(v_a_3290_);
lean_dec_ref(v_a_3289_);
lean_dec(v_a_3288_);
lean_dec_ref(v_a_3287_);
lean_dec(v_a_3286_);
lean_dec_ref(v_a_3285_);
lean_dec(v_a_3284_);
lean_dec(v_a_3283_);
lean_dec_ref(v_e_3281_);
v_a_3369_ = lean_ctor_get(v___x_3319_, 0);
v_isSharedCheck_3376_ = !lean_is_exclusive(v___x_3319_);
if (v_isSharedCheck_3376_ == 0)
{
v___x_3371_ = v___x_3319_;
v_isShared_3372_ = v_isSharedCheck_3376_;
goto v_resetjp_3370_;
}
else
{
lean_inc(v_a_3369_);
lean_dec(v___x_3319_);
v___x_3371_ = lean_box(0);
v_isShared_3372_ = v_isSharedCheck_3376_;
goto v_resetjp_3370_;
}
v_resetjp_3370_:
{
lean_object* v___x_3374_; 
if (v_isShared_3372_ == 0)
{
v___x_3374_ = v___x_3371_;
goto v_reusejp_3373_;
}
else
{
lean_object* v_reuseFailAlloc_3375_; 
v_reuseFailAlloc_3375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3375_, 0, v_a_3369_);
v___x_3374_ = v_reuseFailAlloc_3375_;
goto v_reusejp_3373_;
}
v_reusejp_3373_:
{
return v___x_3374_;
}
}
}
}
else
{
lean_object* v___x_3377_; 
lean_dec(v_a_3315_);
lean_inc(v_a_3292_);
lean_inc_ref(v_a_3291_);
lean_inc(v_a_3290_);
lean_inc_ref(v_a_3289_);
lean_inc(v_a_3288_);
lean_inc_ref(v_a_3287_);
lean_inc(v_a_3286_);
lean_inc_ref(v_a_3285_);
lean_inc(v_a_3284_);
lean_inc(v_a_3283_);
lean_inc(v_val_3312_);
v___x_3377_ = l_Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f(v_val_3312_, v_a_3283_, v_a_3284_, v_a_3285_, v_a_3286_, v_a_3287_, v_a_3288_, v_a_3289_, v_a_3290_, v_a_3291_, v_a_3292_);
if (lean_obj_tag(v___x_3377_) == 0)
{
lean_object* v_a_3378_; 
v_a_3378_ = lean_ctor_get(v___x_3377_, 0);
lean_inc(v_a_3378_);
lean_dec_ref(v___x_3377_);
if (lean_obj_tag(v_a_3378_) == 1)
{
lean_object* v_val_3379_; lean_object* v___x_3380_; 
lean_dec(v_val_3312_);
v_val_3379_ = lean_ctor_get(v_a_3378_, 0);
lean_inc(v_val_3379_);
lean_dec_ref(v_a_3378_);
lean_inc(v_a_3292_);
lean_inc_ref(v_a_3291_);
lean_inc(v_a_3290_);
lean_inc_ref(v_a_3289_);
lean_inc(v_a_3288_);
lean_inc_ref(v_a_3287_);
lean_inc(v_a_3286_);
lean_inc_ref(v_a_3285_);
lean_inc(v_a_3284_);
lean_inc(v_a_3283_);
lean_inc(v_val_3379_);
lean_inc_ref(v_e_3281_);
v___x_3380_ = l_Lean_Meta_Grind_Arith_CommRing_sreify_x3f(v_e_3281_, v_val_3379_, v_a_3283_, v_a_3284_, v_a_3285_, v_a_3286_, v_a_3287_, v_a_3288_, v_a_3289_, v_a_3290_, v_a_3291_, v_a_3292_);
if (lean_obj_tag(v___x_3380_) == 0)
{
lean_object* v_a_3381_; lean_object* v___x_3383_; uint8_t v_isShared_3384_; uint8_t v_isSharedCheck_3429_; 
v_a_3381_ = lean_ctor_get(v___x_3380_, 0);
v_isSharedCheck_3429_ = !lean_is_exclusive(v___x_3380_);
if (v_isSharedCheck_3429_ == 0)
{
v___x_3383_ = v___x_3380_;
v_isShared_3384_ = v_isSharedCheck_3429_;
goto v_resetjp_3382_;
}
else
{
lean_inc(v_a_3381_);
lean_dec(v___x_3380_);
v___x_3383_ = lean_box(0);
v_isShared_3384_ = v_isSharedCheck_3429_;
goto v_resetjp_3382_;
}
v_resetjp_3382_:
{
if (lean_obj_tag(v_a_3381_) == 1)
{
lean_object* v_val_3385_; lean_object* v___y_3387_; lean_object* v___y_3388_; lean_object* v___y_3389_; lean_object* v___y_3390_; lean_object* v___y_3391_; lean_object* v___y_3392_; lean_object* v___y_3393_; lean_object* v___y_3394_; lean_object* v___y_3395_; lean_object* v___y_3396_; lean_object* v___y_3397_; lean_object* v___x_3403_; lean_object* v___x_3404_; lean_object* v_a_3405_; uint8_t v___x_3406_; 
lean_del_object(v___x_3383_);
v_val_3385_ = lean_ctor_get(v_a_3381_, 0);
lean_inc(v_val_3385_);
lean_dec_ref(v_a_3381_);
v___x_3403_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__3));
v___x_3404_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__3___redArg(v___x_3403_, v_a_3291_);
v_a_3405_ = lean_ctor_get(v___x_3404_, 0);
lean_inc(v_a_3405_);
lean_dec_ref(v___x_3404_);
v___x_3406_ = lean_unbox(v_a_3405_);
lean_dec(v_a_3405_);
if (v___x_3406_ == 0)
{
v___y_3387_ = v_val_3379_;
v___y_3388_ = v_a_3283_;
v___y_3389_ = v_a_3284_;
v___y_3390_ = v_a_3285_;
v___y_3391_ = v_a_3286_;
v___y_3392_ = v_a_3287_;
v___y_3393_ = v_a_3288_;
v___y_3394_ = v_a_3289_;
v___y_3395_ = v_a_3290_;
v___y_3396_ = v_a_3291_;
v___y_3397_ = v_a_3292_;
goto v___jp_3386_;
}
else
{
lean_object* v___x_3407_; 
v___x_3407_ = l_Lean_Meta_Grind_updateLastTag(v_a_3283_, v_a_3284_, v_a_3285_, v_a_3286_, v_a_3287_, v_a_3288_, v_a_3289_, v_a_3290_, v_a_3291_, v_a_3292_);
if (lean_obj_tag(v___x_3407_) == 0)
{
lean_object* v___x_3409_; uint8_t v_isShared_3410_; uint8_t v_isSharedCheck_3423_; 
v_isSharedCheck_3423_ = !lean_is_exclusive(v___x_3407_);
if (v_isSharedCheck_3423_ == 0)
{
lean_object* v_unused_3424_; 
v_unused_3424_ = lean_ctor_get(v___x_3407_, 0);
lean_dec(v_unused_3424_);
v___x_3409_ = v___x_3407_;
v_isShared_3410_ = v_isSharedCheck_3423_;
goto v_resetjp_3408_;
}
else
{
lean_dec(v___x_3407_);
v___x_3409_ = lean_box(0);
v_isShared_3410_ = v_isSharedCheck_3423_;
goto v_resetjp_3408_;
}
v_resetjp_3408_:
{
lean_object* v___x_3411_; lean_object* v___x_3412_; lean_object* v___x_3414_; 
v___x_3411_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__9, &l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__9_once, _init_l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__9);
lean_inc(v_val_3379_);
v___x_3412_ = l_Nat_reprFast(v_val_3379_);
if (v_isShared_3410_ == 0)
{
lean_ctor_set_tag(v___x_3409_, 3);
lean_ctor_set(v___x_3409_, 0, v___x_3412_);
v___x_3414_ = v___x_3409_;
goto v_reusejp_3413_;
}
else
{
lean_object* v_reuseFailAlloc_3422_; 
v_reuseFailAlloc_3422_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3422_, 0, v___x_3412_);
v___x_3414_ = v_reuseFailAlloc_3422_;
goto v_reusejp_3413_;
}
v_reusejp_3413_:
{
lean_object* v___x_3415_; lean_object* v___x_3416_; lean_object* v___x_3417_; lean_object* v___x_3418_; lean_object* v___x_3419_; lean_object* v___x_3420_; lean_object* v___x_3421_; 
v___x_3415_ = l_Lean_MessageData_ofFormat(v___x_3414_);
v___x_3416_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3416_, 0, v___x_3411_);
lean_ctor_set(v___x_3416_, 1, v___x_3415_);
v___x_3417_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__7, &l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__7_once, _init_l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__7);
v___x_3418_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3418_, 0, v___x_3416_);
lean_ctor_set(v___x_3418_, 1, v___x_3417_);
lean_inc_ref(v_e_3281_);
v___x_3419_ = l_Lean_MessageData_ofExpr(v_e_3281_);
v___x_3420_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3420_, 0, v___x_3418_);
lean_ctor_set(v___x_3420_, 1, v___x_3419_);
v___x_3421_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__4___redArg(v___x_3403_, v___x_3420_, v_a_3289_, v_a_3290_, v_a_3291_, v_a_3292_);
if (lean_obj_tag(v___x_3421_) == 0)
{
lean_dec_ref(v___x_3421_);
v___y_3387_ = v_val_3379_;
v___y_3388_ = v_a_3283_;
v___y_3389_ = v_a_3284_;
v___y_3390_ = v_a_3285_;
v___y_3391_ = v_a_3286_;
v___y_3392_ = v_a_3287_;
v___y_3393_ = v_a_3288_;
v___y_3394_ = v_a_3289_;
v___y_3395_ = v_a_3290_;
v___y_3396_ = v_a_3291_;
v___y_3397_ = v_a_3292_;
goto v___jp_3386_;
}
else
{
lean_dec(v_val_3385_);
lean_dec(v_val_3379_);
lean_dec(v_a_3292_);
lean_dec_ref(v_a_3291_);
lean_dec(v_a_3290_);
lean_dec_ref(v_a_3289_);
lean_dec(v_a_3288_);
lean_dec_ref(v_a_3287_);
lean_dec(v_a_3286_);
lean_dec_ref(v_a_3285_);
lean_dec(v_a_3284_);
lean_dec(v_a_3283_);
lean_dec_ref(v_e_3281_);
return v___x_3421_;
}
}
}
}
else
{
lean_dec(v_val_3385_);
lean_dec(v_val_3379_);
lean_dec(v_a_3292_);
lean_dec_ref(v_a_3291_);
lean_dec(v_a_3290_);
lean_dec_ref(v_a_3289_);
lean_dec(v_a_3288_);
lean_dec_ref(v_a_3287_);
lean_dec(v_a_3286_);
lean_dec_ref(v_a_3285_);
lean_dec(v_a_3284_);
lean_dec(v_a_3283_);
lean_dec_ref(v_e_3281_);
return v___x_3407_;
}
}
v___jp_3386_:
{
lean_object* v___x_3398_; 
lean_inc(v___y_3387_);
lean_inc_ref(v_e_3281_);
v___x_3398_ = l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId(v_e_3281_, v___y_3387_, v___y_3388_, v___y_3389_, v___y_3390_, v___y_3391_, v___y_3392_, v___y_3393_, v___y_3394_, v___y_3395_, v___y_3396_, v___y_3397_);
if (lean_obj_tag(v___x_3398_) == 0)
{
lean_object* v___x_3399_; lean_object* v___x_3400_; 
lean_dec_ref(v___x_3398_);
v___x_3399_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
lean_inc(v___y_3388_);
lean_inc_ref(v_e_3281_);
v___x_3400_ = l_Lean_Meta_Grind_SolverExtension_markTerm___redArg(v___x_3399_, v_e_3281_, v___y_3388_, v___y_3389_, v___y_3390_, v___y_3391_, v___y_3392_, v___y_3393_, v___y_3394_, v___y_3395_, v___y_3396_, v___y_3397_);
if (lean_obj_tag(v___x_3400_) == 0)
{
lean_object* v___f_3401_; lean_object* v___x_3402_; 
lean_dec_ref(v___x_3400_);
v___f_3401_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_internalize___lam__1___boxed), 4, 3);
lean_closure_set(v___f_3401_, 0, v___y_3387_);
lean_closure_set(v___f_3401_, 1, v_e_3281_);
lean_closure_set(v___f_3401_, 2, v_val_3385_);
v___x_3402_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_3399_, v___f_3401_, v___y_3388_);
lean_dec(v___y_3388_);
return v___x_3402_;
}
else
{
lean_dec(v___y_3388_);
lean_dec(v___y_3387_);
lean_dec(v_val_3385_);
lean_dec_ref(v_e_3281_);
return v___x_3400_;
}
}
else
{
lean_dec(v___y_3397_);
lean_dec_ref(v___y_3396_);
lean_dec(v___y_3395_);
lean_dec_ref(v___y_3394_);
lean_dec(v___y_3393_);
lean_dec_ref(v___y_3392_);
lean_dec(v___y_3391_);
lean_dec_ref(v___y_3390_);
lean_dec(v___y_3389_);
lean_dec(v___y_3388_);
lean_dec(v___y_3387_);
lean_dec(v_val_3385_);
lean_dec_ref(v_e_3281_);
return v___x_3398_;
}
}
}
else
{
lean_object* v___x_3425_; lean_object* v___x_3427_; 
lean_dec(v_a_3381_);
lean_dec(v_val_3379_);
lean_dec(v_a_3292_);
lean_dec_ref(v_a_3291_);
lean_dec(v_a_3290_);
lean_dec_ref(v_a_3289_);
lean_dec(v_a_3288_);
lean_dec_ref(v_a_3287_);
lean_dec(v_a_3286_);
lean_dec_ref(v_a_3285_);
lean_dec(v_a_3284_);
lean_dec(v_a_3283_);
lean_dec_ref(v_e_3281_);
v___x_3425_ = lean_box(0);
if (v_isShared_3384_ == 0)
{
lean_ctor_set(v___x_3383_, 0, v___x_3425_);
v___x_3427_ = v___x_3383_;
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
lean_dec(v_val_3379_);
lean_dec(v_a_3292_);
lean_dec_ref(v_a_3291_);
lean_dec(v_a_3290_);
lean_dec_ref(v_a_3289_);
lean_dec(v_a_3288_);
lean_dec_ref(v_a_3287_);
lean_dec(v_a_3286_);
lean_dec_ref(v_a_3285_);
lean_dec(v_a_3284_);
lean_dec(v_a_3283_);
lean_dec_ref(v_e_3281_);
v_a_3430_ = lean_ctor_get(v___x_3380_, 0);
v_isSharedCheck_3437_ = !lean_is_exclusive(v___x_3380_);
if (v_isSharedCheck_3437_ == 0)
{
v___x_3432_ = v___x_3380_;
v_isShared_3433_ = v_isSharedCheck_3437_;
goto v_resetjp_3431_;
}
else
{
lean_inc(v_a_3430_);
lean_dec(v___x_3380_);
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
lean_object* v___x_3438_; 
lean_dec(v_a_3378_);
lean_inc(v_a_3292_);
lean_inc_ref(v_a_3291_);
lean_inc(v_a_3290_);
lean_inc_ref(v_a_3289_);
lean_inc(v_a_3288_);
lean_inc_ref(v_a_3287_);
lean_inc(v_a_3286_);
lean_inc_ref(v_a_3285_);
lean_inc(v_a_3284_);
lean_inc(v_a_3283_);
lean_inc(v_val_3312_);
v___x_3438_ = l_Lean_Meta_Grind_Arith_CommRing_getNonCommRingId_x3f(v_val_3312_, v_a_3283_, v_a_3284_, v_a_3285_, v_a_3286_, v_a_3287_, v_a_3288_, v_a_3289_, v_a_3290_, v_a_3291_, v_a_3292_);
if (lean_obj_tag(v___x_3438_) == 0)
{
lean_object* v_a_3439_; 
v_a_3439_ = lean_ctor_get(v___x_3438_, 0);
lean_inc(v_a_3439_);
lean_dec_ref(v___x_3438_);
if (lean_obj_tag(v_a_3439_) == 1)
{
lean_object* v_val_3440_; lean_object* v___x_3441_; lean_object* v___x_3442_; 
lean_dec(v_val_3312_);
v_val_3440_ = lean_ctor_get(v_a_3439_, 0);
lean_inc(v_val_3440_);
lean_dec_ref(v_a_3439_);
v___x_3441_ = lean_unsigned_to_nat(0u);
lean_inc(v_a_3292_);
lean_inc_ref(v_a_3291_);
lean_inc(v_a_3290_);
lean_inc_ref(v_a_3289_);
lean_inc(v_a_3288_);
lean_inc_ref(v_a_3287_);
lean_inc(v_a_3286_);
lean_inc_ref(v_a_3285_);
lean_inc(v_a_3284_);
lean_inc(v_a_3283_);
lean_inc(v_val_3440_);
lean_inc_ref(v_e_3281_);
v___x_3442_ = l_Lean_Meta_Grind_Arith_CommRing_ncreify_x3f(v_e_3281_, v_ring_3299_, v___x_3441_, v_val_3440_, v_a_3283_, v_a_3284_, v_a_3285_, v_a_3286_, v_a_3287_, v_a_3288_, v_a_3289_, v_a_3290_, v_a_3291_, v_a_3292_);
if (lean_obj_tag(v___x_3442_) == 0)
{
lean_object* v_a_3443_; lean_object* v___x_3445_; uint8_t v_isShared_3446_; uint8_t v_isSharedCheck_3491_; 
v_a_3443_ = lean_ctor_get(v___x_3442_, 0);
v_isSharedCheck_3491_ = !lean_is_exclusive(v___x_3442_);
if (v_isSharedCheck_3491_ == 0)
{
v___x_3445_ = v___x_3442_;
v_isShared_3446_ = v_isSharedCheck_3491_;
goto v_resetjp_3444_;
}
else
{
lean_inc(v_a_3443_);
lean_dec(v___x_3442_);
v___x_3445_ = lean_box(0);
v_isShared_3446_ = v_isSharedCheck_3491_;
goto v_resetjp_3444_;
}
v_resetjp_3444_:
{
if (lean_obj_tag(v_a_3443_) == 1)
{
lean_object* v_val_3447_; lean_object* v___x_3448_; lean_object* v___x_3449_; lean_object* v_a_3450_; lean_object* v___f_3451_; lean_object* v___y_3453_; lean_object* v___y_3454_; lean_object* v___y_3455_; lean_object* v___y_3456_; lean_object* v___y_3457_; lean_object* v___y_3458_; lean_object* v___y_3459_; lean_object* v___y_3460_; lean_object* v___y_3461_; lean_object* v___y_3462_; lean_object* v___y_3463_; uint8_t v___x_3468_; 
lean_del_object(v___x_3445_);
v_val_3447_ = lean_ctor_get(v_a_3443_, 0);
lean_inc(v_val_3447_);
lean_dec_ref(v_a_3443_);
v___x_3448_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__3));
v___x_3449_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__5___redArg(v___x_3448_, v_a_3291_);
v_a_3450_ = lean_ctor_get(v___x_3449_, 0);
lean_inc(v_a_3450_);
lean_dec_ref(v___x_3449_);
lean_inc_ref(v_e_3281_);
v___f_3451_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_internalize___lam__2), 3, 2);
lean_closure_set(v___f_3451_, 0, v_e_3281_);
lean_closure_set(v___f_3451_, 1, v_val_3447_);
v___x_3468_ = lean_unbox(v_a_3450_);
lean_dec(v_a_3450_);
if (v___x_3468_ == 0)
{
v___y_3453_ = v_val_3440_;
v___y_3454_ = v_a_3283_;
v___y_3455_ = v_a_3284_;
v___y_3456_ = v_a_3285_;
v___y_3457_ = v_a_3286_;
v___y_3458_ = v_a_3287_;
v___y_3459_ = v_a_3288_;
v___y_3460_ = v_a_3289_;
v___y_3461_ = v_a_3290_;
v___y_3462_ = v_a_3291_;
v___y_3463_ = v_a_3292_;
goto v___jp_3452_;
}
else
{
lean_object* v___x_3469_; 
v___x_3469_ = l_Lean_Meta_Grind_updateLastTag(v_a_3283_, v_a_3284_, v_a_3285_, v_a_3286_, v_a_3287_, v_a_3288_, v_a_3289_, v_a_3290_, v_a_3291_, v_a_3292_);
if (lean_obj_tag(v___x_3469_) == 0)
{
lean_object* v___x_3471_; uint8_t v_isShared_3472_; uint8_t v_isSharedCheck_3485_; 
v_isSharedCheck_3485_ = !lean_is_exclusive(v___x_3469_);
if (v_isSharedCheck_3485_ == 0)
{
lean_object* v_unused_3486_; 
v_unused_3486_ = lean_ctor_get(v___x_3469_, 0);
lean_dec(v_unused_3486_);
v___x_3471_ = v___x_3469_;
v_isShared_3472_ = v_isSharedCheck_3485_;
goto v_resetjp_3470_;
}
else
{
lean_dec(v___x_3469_);
v___x_3471_ = lean_box(0);
v_isShared_3472_ = v_isSharedCheck_3485_;
goto v_resetjp_3470_;
}
v_resetjp_3470_:
{
lean_object* v___x_3473_; lean_object* v___x_3474_; lean_object* v___x_3476_; 
v___x_3473_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__11, &l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__11_once, _init_l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__11);
lean_inc(v_val_3440_);
v___x_3474_ = l_Nat_reprFast(v_val_3440_);
if (v_isShared_3472_ == 0)
{
lean_ctor_set_tag(v___x_3471_, 3);
lean_ctor_set(v___x_3471_, 0, v___x_3474_);
v___x_3476_ = v___x_3471_;
goto v_reusejp_3475_;
}
else
{
lean_object* v_reuseFailAlloc_3484_; 
v_reuseFailAlloc_3484_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3484_, 0, v___x_3474_);
v___x_3476_ = v_reuseFailAlloc_3484_;
goto v_reusejp_3475_;
}
v_reusejp_3475_:
{
lean_object* v___x_3477_; lean_object* v___x_3478_; lean_object* v___x_3479_; lean_object* v___x_3480_; lean_object* v___x_3481_; lean_object* v___x_3482_; lean_object* v___x_3483_; 
v___x_3477_ = l_Lean_MessageData_ofFormat(v___x_3476_);
v___x_3478_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3478_, 0, v___x_3473_);
lean_ctor_set(v___x_3478_, 1, v___x_3477_);
v___x_3479_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__7, &l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__7_once, _init_l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__7);
v___x_3480_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3480_, 0, v___x_3478_);
lean_ctor_set(v___x_3480_, 1, v___x_3479_);
lean_inc_ref(v_e_3281_);
v___x_3481_ = l_Lean_MessageData_ofExpr(v_e_3281_);
v___x_3482_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3482_, 0, v___x_3480_);
lean_ctor_set(v___x_3482_, 1, v___x_3481_);
v___x_3483_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__6___redArg(v___x_3448_, v___x_3482_, v_a_3289_, v_a_3290_, v_a_3291_, v_a_3292_);
if (lean_obj_tag(v___x_3483_) == 0)
{
lean_dec_ref(v___x_3483_);
v___y_3453_ = v_val_3440_;
v___y_3454_ = v_a_3283_;
v___y_3455_ = v_a_3284_;
v___y_3456_ = v_a_3285_;
v___y_3457_ = v_a_3286_;
v___y_3458_ = v_a_3287_;
v___y_3459_ = v_a_3288_;
v___y_3460_ = v_a_3289_;
v___y_3461_ = v_a_3290_;
v___y_3462_ = v_a_3291_;
v___y_3463_ = v_a_3292_;
goto v___jp_3452_;
}
else
{
lean_dec_ref(v___f_3451_);
lean_dec(v_val_3440_);
lean_dec(v_a_3292_);
lean_dec_ref(v_a_3291_);
lean_dec(v_a_3290_);
lean_dec_ref(v_a_3289_);
lean_dec(v_a_3288_);
lean_dec_ref(v_a_3287_);
lean_dec(v_a_3286_);
lean_dec_ref(v_a_3285_);
lean_dec(v_a_3284_);
lean_dec(v_a_3283_);
lean_dec_ref(v_e_3281_);
return v___x_3483_;
}
}
}
}
else
{
lean_dec_ref(v___f_3451_);
lean_dec(v_val_3440_);
lean_dec(v_a_3292_);
lean_dec_ref(v_a_3291_);
lean_dec(v_a_3290_);
lean_dec_ref(v_a_3289_);
lean_dec(v_a_3288_);
lean_dec_ref(v_a_3287_);
lean_dec(v_a_3286_);
lean_dec_ref(v_a_3285_);
lean_dec(v_a_3284_);
lean_dec(v_a_3283_);
lean_dec_ref(v_e_3281_);
return v___x_3469_;
}
}
v___jp_3452_:
{
lean_object* v___x_3464_; 
lean_inc(v___y_3453_);
lean_inc_ref(v_e_3281_);
v___x_3464_ = l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId(v_e_3281_, v___y_3453_, v___y_3454_, v___y_3455_, v___y_3456_, v___y_3457_, v___y_3458_, v___y_3459_, v___y_3460_, v___y_3461_, v___y_3462_, v___y_3463_);
if (lean_obj_tag(v___x_3464_) == 0)
{
lean_object* v___x_3465_; lean_object* v___x_3466_; 
lean_dec_ref(v___x_3464_);
v___x_3465_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
lean_inc(v___y_3454_);
v___x_3466_ = l_Lean_Meta_Grind_SolverExtension_markTerm___redArg(v___x_3465_, v_e_3281_, v___y_3454_, v___y_3455_, v___y_3456_, v___y_3457_, v___y_3458_, v___y_3459_, v___y_3460_, v___y_3461_, v___y_3462_, v___y_3463_);
if (lean_obj_tag(v___x_3466_) == 0)
{
lean_object* v___x_3467_; 
lean_dec_ref(v___x_3466_);
v___x_3467_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_modifyRing___redArg(v___f_3451_, v___y_3453_, v___y_3454_);
lean_dec(v___y_3454_);
return v___x_3467_;
}
else
{
lean_dec(v___y_3454_);
lean_dec(v___y_3453_);
lean_dec_ref(v___f_3451_);
return v___x_3466_;
}
}
else
{
lean_dec(v___y_3463_);
lean_dec_ref(v___y_3462_);
lean_dec(v___y_3461_);
lean_dec_ref(v___y_3460_);
lean_dec(v___y_3459_);
lean_dec_ref(v___y_3458_);
lean_dec(v___y_3457_);
lean_dec_ref(v___y_3456_);
lean_dec(v___y_3455_);
lean_dec(v___y_3454_);
lean_dec(v___y_3453_);
lean_dec_ref(v___f_3451_);
lean_dec_ref(v_e_3281_);
return v___x_3464_;
}
}
}
else
{
lean_object* v___x_3487_; lean_object* v___x_3489_; 
lean_dec(v_a_3443_);
lean_dec(v_val_3440_);
lean_dec(v_a_3292_);
lean_dec_ref(v_a_3291_);
lean_dec(v_a_3290_);
lean_dec_ref(v_a_3289_);
lean_dec(v_a_3288_);
lean_dec_ref(v_a_3287_);
lean_dec(v_a_3286_);
lean_dec_ref(v_a_3285_);
lean_dec(v_a_3284_);
lean_dec(v_a_3283_);
lean_dec_ref(v_e_3281_);
v___x_3487_ = lean_box(0);
if (v_isShared_3446_ == 0)
{
lean_ctor_set(v___x_3445_, 0, v___x_3487_);
v___x_3489_ = v___x_3445_;
goto v_reusejp_3488_;
}
else
{
lean_object* v_reuseFailAlloc_3490_; 
v_reuseFailAlloc_3490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3490_, 0, v___x_3487_);
v___x_3489_ = v_reuseFailAlloc_3490_;
goto v_reusejp_3488_;
}
v_reusejp_3488_:
{
return v___x_3489_;
}
}
}
}
else
{
lean_object* v_a_3492_; lean_object* v___x_3494_; uint8_t v_isShared_3495_; uint8_t v_isSharedCheck_3499_; 
lean_dec(v_val_3440_);
lean_dec(v_a_3292_);
lean_dec_ref(v_a_3291_);
lean_dec(v_a_3290_);
lean_dec_ref(v_a_3289_);
lean_dec(v_a_3288_);
lean_dec_ref(v_a_3287_);
lean_dec(v_a_3286_);
lean_dec_ref(v_a_3285_);
lean_dec(v_a_3284_);
lean_dec(v_a_3283_);
lean_dec_ref(v_e_3281_);
v_a_3492_ = lean_ctor_get(v___x_3442_, 0);
v_isSharedCheck_3499_ = !lean_is_exclusive(v___x_3442_);
if (v_isSharedCheck_3499_ == 0)
{
v___x_3494_ = v___x_3442_;
v_isShared_3495_ = v_isSharedCheck_3499_;
goto v_resetjp_3493_;
}
else
{
lean_inc(v_a_3492_);
lean_dec(v___x_3442_);
v___x_3494_ = lean_box(0);
v_isShared_3495_ = v_isSharedCheck_3499_;
goto v_resetjp_3493_;
}
v_resetjp_3493_:
{
lean_object* v___x_3497_; 
if (v_isShared_3495_ == 0)
{
v___x_3497_ = v___x_3494_;
goto v_reusejp_3496_;
}
else
{
lean_object* v_reuseFailAlloc_3498_; 
v_reuseFailAlloc_3498_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3498_, 0, v_a_3492_);
v___x_3497_ = v_reuseFailAlloc_3498_;
goto v_reusejp_3496_;
}
v_reusejp_3496_:
{
return v___x_3497_;
}
}
}
}
else
{
lean_object* v___x_3500_; 
lean_dec(v_a_3439_);
lean_inc(v_a_3292_);
lean_inc_ref(v_a_3291_);
lean_inc(v_a_3290_);
lean_inc_ref(v_a_3289_);
v___x_3500_ = l_Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f___redArg(v_val_3312_, v_a_3283_, v_a_3289_, v_a_3290_, v_a_3291_, v_a_3292_);
if (lean_obj_tag(v___x_3500_) == 0)
{
lean_object* v_a_3501_; lean_object* v___x_3503_; uint8_t v_isShared_3504_; uint8_t v_isSharedCheck_3568_; 
v_a_3501_ = lean_ctor_get(v___x_3500_, 0);
v_isSharedCheck_3568_ = !lean_is_exclusive(v___x_3500_);
if (v_isSharedCheck_3568_ == 0)
{
v___x_3503_ = v___x_3500_;
v_isShared_3504_ = v_isSharedCheck_3568_;
goto v_resetjp_3502_;
}
else
{
lean_inc(v_a_3501_);
lean_dec(v___x_3500_);
v___x_3503_ = lean_box(0);
v_isShared_3504_ = v_isSharedCheck_3568_;
goto v_resetjp_3502_;
}
v_resetjp_3502_:
{
if (lean_obj_tag(v_a_3501_) == 1)
{
lean_object* v_val_3505_; lean_object* v___x_3506_; 
lean_del_object(v___x_3503_);
v_val_3505_ = lean_ctor_get(v_a_3501_, 0);
lean_inc(v_val_3505_);
lean_dec_ref(v_a_3501_);
lean_inc(v_a_3292_);
lean_inc_ref(v_a_3291_);
lean_inc(v_a_3290_);
lean_inc_ref(v_a_3289_);
lean_inc(v_a_3288_);
lean_inc_ref(v_a_3287_);
lean_inc(v_a_3286_);
lean_inc_ref(v_a_3285_);
lean_inc(v_a_3284_);
lean_inc(v_a_3283_);
lean_inc(v_val_3505_);
lean_inc_ref(v_e_3281_);
v___x_3506_ = l_Lean_Meta_Grind_Arith_CommRing_ncsreify_x3f(v_e_3281_, v_val_3505_, v_a_3283_, v_a_3284_, v_a_3285_, v_a_3286_, v_a_3287_, v_a_3288_, v_a_3289_, v_a_3290_, v_a_3291_, v_a_3292_);
if (lean_obj_tag(v___x_3506_) == 0)
{
lean_object* v_a_3507_; lean_object* v___x_3509_; uint8_t v_isShared_3510_; uint8_t v_isSharedCheck_3555_; 
v_a_3507_ = lean_ctor_get(v___x_3506_, 0);
v_isSharedCheck_3555_ = !lean_is_exclusive(v___x_3506_);
if (v_isSharedCheck_3555_ == 0)
{
v___x_3509_ = v___x_3506_;
v_isShared_3510_ = v_isSharedCheck_3555_;
goto v_resetjp_3508_;
}
else
{
lean_inc(v_a_3507_);
lean_dec(v___x_3506_);
v___x_3509_ = lean_box(0);
v_isShared_3510_ = v_isSharedCheck_3555_;
goto v_resetjp_3508_;
}
v_resetjp_3508_:
{
if (lean_obj_tag(v_a_3507_) == 1)
{
lean_object* v_val_3511_; lean_object* v___x_3512_; lean_object* v___x_3513_; lean_object* v_a_3514_; lean_object* v___f_3515_; lean_object* v___y_3517_; lean_object* v___y_3518_; lean_object* v___y_3519_; lean_object* v___y_3520_; lean_object* v___y_3521_; lean_object* v___y_3522_; lean_object* v___y_3523_; lean_object* v___y_3524_; lean_object* v___y_3525_; lean_object* v___y_3526_; lean_object* v___y_3527_; uint8_t v___x_3532_; 
lean_del_object(v___x_3509_);
v_val_3511_ = lean_ctor_get(v_a_3507_, 0);
lean_inc(v_val_3511_);
lean_dec_ref(v_a_3507_);
v___x_3512_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__3));
v___x_3513_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__7___redArg(v___x_3512_, v_a_3291_);
v_a_3514_ = lean_ctor_get(v___x_3513_, 0);
lean_inc(v_a_3514_);
lean_dec_ref(v___x_3513_);
lean_inc_ref(v_e_3281_);
v___f_3515_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_internalize___lam__3), 3, 2);
lean_closure_set(v___f_3515_, 0, v_e_3281_);
lean_closure_set(v___f_3515_, 1, v_val_3511_);
v___x_3532_ = lean_unbox(v_a_3514_);
lean_dec(v_a_3514_);
if (v___x_3532_ == 0)
{
v___y_3517_ = v_val_3505_;
v___y_3518_ = v_a_3283_;
v___y_3519_ = v_a_3284_;
v___y_3520_ = v_a_3285_;
v___y_3521_ = v_a_3286_;
v___y_3522_ = v_a_3287_;
v___y_3523_ = v_a_3288_;
v___y_3524_ = v_a_3289_;
v___y_3525_ = v_a_3290_;
v___y_3526_ = v_a_3291_;
v___y_3527_ = v_a_3292_;
goto v___jp_3516_;
}
else
{
lean_object* v___x_3533_; 
v___x_3533_ = l_Lean_Meta_Grind_updateLastTag(v_a_3283_, v_a_3284_, v_a_3285_, v_a_3286_, v_a_3287_, v_a_3288_, v_a_3289_, v_a_3290_, v_a_3291_, v_a_3292_);
if (lean_obj_tag(v___x_3533_) == 0)
{
lean_object* v___x_3535_; uint8_t v_isShared_3536_; uint8_t v_isSharedCheck_3549_; 
v_isSharedCheck_3549_ = !lean_is_exclusive(v___x_3533_);
if (v_isSharedCheck_3549_ == 0)
{
lean_object* v_unused_3550_; 
v_unused_3550_ = lean_ctor_get(v___x_3533_, 0);
lean_dec(v_unused_3550_);
v___x_3535_ = v___x_3533_;
v_isShared_3536_ = v_isSharedCheck_3549_;
goto v_resetjp_3534_;
}
else
{
lean_dec(v___x_3533_);
v___x_3535_ = lean_box(0);
v_isShared_3536_ = v_isSharedCheck_3549_;
goto v_resetjp_3534_;
}
v_resetjp_3534_:
{
lean_object* v___x_3537_; lean_object* v___x_3538_; lean_object* v___x_3540_; 
v___x_3537_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__13, &l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__13_once, _init_l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__13);
lean_inc(v_val_3505_);
v___x_3538_ = l_Nat_reprFast(v_val_3505_);
if (v_isShared_3536_ == 0)
{
lean_ctor_set_tag(v___x_3535_, 3);
lean_ctor_set(v___x_3535_, 0, v___x_3538_);
v___x_3540_ = v___x_3535_;
goto v_reusejp_3539_;
}
else
{
lean_object* v_reuseFailAlloc_3548_; 
v_reuseFailAlloc_3548_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3548_, 0, v___x_3538_);
v___x_3540_ = v_reuseFailAlloc_3548_;
goto v_reusejp_3539_;
}
v_reusejp_3539_:
{
lean_object* v___x_3541_; lean_object* v___x_3542_; lean_object* v___x_3543_; lean_object* v___x_3544_; lean_object* v___x_3545_; lean_object* v___x_3546_; lean_object* v___x_3547_; 
v___x_3541_ = l_Lean_MessageData_ofFormat(v___x_3540_);
v___x_3542_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3542_, 0, v___x_3537_);
lean_ctor_set(v___x_3542_, 1, v___x_3541_);
v___x_3543_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__7, &l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__7_once, _init_l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__7);
v___x_3544_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3544_, 0, v___x_3542_);
lean_ctor_set(v___x_3544_, 1, v___x_3543_);
lean_inc_ref(v_e_3281_);
v___x_3545_ = l_Lean_MessageData_ofExpr(v_e_3281_);
v___x_3546_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3546_, 0, v___x_3544_);
lean_ctor_set(v___x_3546_, 1, v___x_3545_);
v___x_3547_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__8___redArg(v___x_3512_, v___x_3546_, v_a_3289_, v_a_3290_, v_a_3291_, v_a_3292_);
if (lean_obj_tag(v___x_3547_) == 0)
{
lean_dec_ref(v___x_3547_);
v___y_3517_ = v_val_3505_;
v___y_3518_ = v_a_3283_;
v___y_3519_ = v_a_3284_;
v___y_3520_ = v_a_3285_;
v___y_3521_ = v_a_3286_;
v___y_3522_ = v_a_3287_;
v___y_3523_ = v_a_3288_;
v___y_3524_ = v_a_3289_;
v___y_3525_ = v_a_3290_;
v___y_3526_ = v_a_3291_;
v___y_3527_ = v_a_3292_;
goto v___jp_3516_;
}
else
{
lean_dec_ref(v___f_3515_);
lean_dec(v_val_3505_);
lean_dec(v_a_3292_);
lean_dec_ref(v_a_3291_);
lean_dec(v_a_3290_);
lean_dec_ref(v_a_3289_);
lean_dec(v_a_3288_);
lean_dec_ref(v_a_3287_);
lean_dec(v_a_3286_);
lean_dec_ref(v_a_3285_);
lean_dec(v_a_3284_);
lean_dec(v_a_3283_);
lean_dec_ref(v_e_3281_);
return v___x_3547_;
}
}
}
}
else
{
lean_dec_ref(v___f_3515_);
lean_dec(v_val_3505_);
lean_dec(v_a_3292_);
lean_dec_ref(v_a_3291_);
lean_dec(v_a_3290_);
lean_dec_ref(v_a_3289_);
lean_dec(v_a_3288_);
lean_dec_ref(v_a_3287_);
lean_dec(v_a_3286_);
lean_dec_ref(v_a_3285_);
lean_dec(v_a_3284_);
lean_dec(v_a_3283_);
lean_dec_ref(v_e_3281_);
return v___x_3533_;
}
}
v___jp_3516_:
{
lean_object* v___x_3528_; 
lean_inc(v___y_3517_);
lean_inc_ref(v_e_3281_);
v___x_3528_ = l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId(v_e_3281_, v___y_3517_, v___y_3518_, v___y_3519_, v___y_3520_, v___y_3521_, v___y_3522_, v___y_3523_, v___y_3524_, v___y_3525_, v___y_3526_, v___y_3527_);
if (lean_obj_tag(v___x_3528_) == 0)
{
lean_object* v___x_3529_; lean_object* v___x_3530_; 
lean_dec_ref(v___x_3528_);
v___x_3529_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
lean_inc(v___y_3518_);
v___x_3530_ = l_Lean_Meta_Grind_SolverExtension_markTerm___redArg(v___x_3529_, v_e_3281_, v___y_3518_, v___y_3519_, v___y_3520_, v___y_3521_, v___y_3522_, v___y_3523_, v___y_3524_, v___y_3525_, v___y_3526_, v___y_3527_);
if (lean_obj_tag(v___x_3530_) == 0)
{
lean_object* v___x_3531_; 
lean_dec_ref(v___x_3530_);
v___x_3531_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_modifySemiring___redArg(v___f_3515_, v___y_3517_, v___y_3518_);
lean_dec(v___y_3518_);
return v___x_3531_;
}
else
{
lean_dec(v___y_3518_);
lean_dec(v___y_3517_);
lean_dec_ref(v___f_3515_);
return v___x_3530_;
}
}
else
{
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
lean_dec_ref(v___f_3515_);
lean_dec_ref(v_e_3281_);
return v___x_3528_;
}
}
}
else
{
lean_object* v___x_3551_; lean_object* v___x_3553_; 
lean_dec(v_a_3507_);
lean_dec(v_val_3505_);
lean_dec(v_a_3292_);
lean_dec_ref(v_a_3291_);
lean_dec(v_a_3290_);
lean_dec_ref(v_a_3289_);
lean_dec(v_a_3288_);
lean_dec_ref(v_a_3287_);
lean_dec(v_a_3286_);
lean_dec_ref(v_a_3285_);
lean_dec(v_a_3284_);
lean_dec(v_a_3283_);
lean_dec_ref(v_e_3281_);
v___x_3551_ = lean_box(0);
if (v_isShared_3510_ == 0)
{
lean_ctor_set(v___x_3509_, 0, v___x_3551_);
v___x_3553_ = v___x_3509_;
goto v_reusejp_3552_;
}
else
{
lean_object* v_reuseFailAlloc_3554_; 
v_reuseFailAlloc_3554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3554_, 0, v___x_3551_);
v___x_3553_ = v_reuseFailAlloc_3554_;
goto v_reusejp_3552_;
}
v_reusejp_3552_:
{
return v___x_3553_;
}
}
}
}
else
{
lean_object* v_a_3556_; lean_object* v___x_3558_; uint8_t v_isShared_3559_; uint8_t v_isSharedCheck_3563_; 
lean_dec(v_val_3505_);
lean_dec(v_a_3292_);
lean_dec_ref(v_a_3291_);
lean_dec(v_a_3290_);
lean_dec_ref(v_a_3289_);
lean_dec(v_a_3288_);
lean_dec_ref(v_a_3287_);
lean_dec(v_a_3286_);
lean_dec_ref(v_a_3285_);
lean_dec(v_a_3284_);
lean_dec(v_a_3283_);
lean_dec_ref(v_e_3281_);
v_a_3556_ = lean_ctor_get(v___x_3506_, 0);
v_isSharedCheck_3563_ = !lean_is_exclusive(v___x_3506_);
if (v_isSharedCheck_3563_ == 0)
{
v___x_3558_ = v___x_3506_;
v_isShared_3559_ = v_isSharedCheck_3563_;
goto v_resetjp_3557_;
}
else
{
lean_inc(v_a_3556_);
lean_dec(v___x_3506_);
v___x_3558_ = lean_box(0);
v_isShared_3559_ = v_isSharedCheck_3563_;
goto v_resetjp_3557_;
}
v_resetjp_3557_:
{
lean_object* v___x_3561_; 
if (v_isShared_3559_ == 0)
{
v___x_3561_ = v___x_3558_;
goto v_reusejp_3560_;
}
else
{
lean_object* v_reuseFailAlloc_3562_; 
v_reuseFailAlloc_3562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3562_, 0, v_a_3556_);
v___x_3561_ = v_reuseFailAlloc_3562_;
goto v_reusejp_3560_;
}
v_reusejp_3560_:
{
return v___x_3561_;
}
}
}
}
else
{
lean_object* v___x_3564_; lean_object* v___x_3566_; 
lean_dec(v_a_3501_);
lean_dec(v_a_3292_);
lean_dec_ref(v_a_3291_);
lean_dec(v_a_3290_);
lean_dec_ref(v_a_3289_);
lean_dec(v_a_3288_);
lean_dec_ref(v_a_3287_);
lean_dec(v_a_3286_);
lean_dec_ref(v_a_3285_);
lean_dec(v_a_3284_);
lean_dec(v_a_3283_);
lean_dec_ref(v_e_3281_);
v___x_3564_ = lean_box(0);
if (v_isShared_3504_ == 0)
{
lean_ctor_set(v___x_3503_, 0, v___x_3564_);
v___x_3566_ = v___x_3503_;
goto v_reusejp_3565_;
}
else
{
lean_object* v_reuseFailAlloc_3567_; 
v_reuseFailAlloc_3567_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3567_, 0, v___x_3564_);
v___x_3566_ = v_reuseFailAlloc_3567_;
goto v_reusejp_3565_;
}
v_reusejp_3565_:
{
return v___x_3566_;
}
}
}
}
else
{
lean_object* v_a_3569_; lean_object* v___x_3571_; uint8_t v_isShared_3572_; uint8_t v_isSharedCheck_3576_; 
lean_dec(v_a_3292_);
lean_dec_ref(v_a_3291_);
lean_dec(v_a_3290_);
lean_dec_ref(v_a_3289_);
lean_dec(v_a_3288_);
lean_dec_ref(v_a_3287_);
lean_dec(v_a_3286_);
lean_dec_ref(v_a_3285_);
lean_dec(v_a_3284_);
lean_dec(v_a_3283_);
lean_dec_ref(v_e_3281_);
v_a_3569_ = lean_ctor_get(v___x_3500_, 0);
v_isSharedCheck_3576_ = !lean_is_exclusive(v___x_3500_);
if (v_isSharedCheck_3576_ == 0)
{
v___x_3571_ = v___x_3500_;
v_isShared_3572_ = v_isSharedCheck_3576_;
goto v_resetjp_3570_;
}
else
{
lean_inc(v_a_3569_);
lean_dec(v___x_3500_);
v___x_3571_ = lean_box(0);
v_isShared_3572_ = v_isSharedCheck_3576_;
goto v_resetjp_3570_;
}
v_resetjp_3570_:
{
lean_object* v___x_3574_; 
if (v_isShared_3572_ == 0)
{
v___x_3574_ = v___x_3571_;
goto v_reusejp_3573_;
}
else
{
lean_object* v_reuseFailAlloc_3575_; 
v_reuseFailAlloc_3575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3575_, 0, v_a_3569_);
v___x_3574_ = v_reuseFailAlloc_3575_;
goto v_reusejp_3573_;
}
v_reusejp_3573_:
{
return v___x_3574_;
}
}
}
}
}
else
{
lean_object* v_a_3577_; lean_object* v___x_3579_; uint8_t v_isShared_3580_; uint8_t v_isSharedCheck_3584_; 
lean_dec(v_val_3312_);
lean_dec(v_a_3292_);
lean_dec_ref(v_a_3291_);
lean_dec(v_a_3290_);
lean_dec_ref(v_a_3289_);
lean_dec(v_a_3288_);
lean_dec_ref(v_a_3287_);
lean_dec(v_a_3286_);
lean_dec_ref(v_a_3285_);
lean_dec(v_a_3284_);
lean_dec(v_a_3283_);
lean_dec_ref(v_e_3281_);
v_a_3577_ = lean_ctor_get(v___x_3438_, 0);
v_isSharedCheck_3584_ = !lean_is_exclusive(v___x_3438_);
if (v_isSharedCheck_3584_ == 0)
{
v___x_3579_ = v___x_3438_;
v_isShared_3580_ = v_isSharedCheck_3584_;
goto v_resetjp_3578_;
}
else
{
lean_inc(v_a_3577_);
lean_dec(v___x_3438_);
v___x_3579_ = lean_box(0);
v_isShared_3580_ = v_isSharedCheck_3584_;
goto v_resetjp_3578_;
}
v_resetjp_3578_:
{
lean_object* v___x_3582_; 
if (v_isShared_3580_ == 0)
{
v___x_3582_ = v___x_3579_;
goto v_reusejp_3581_;
}
else
{
lean_object* v_reuseFailAlloc_3583_; 
v_reuseFailAlloc_3583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3583_, 0, v_a_3577_);
v___x_3582_ = v_reuseFailAlloc_3583_;
goto v_reusejp_3581_;
}
v_reusejp_3581_:
{
return v___x_3582_;
}
}
}
}
}
else
{
lean_object* v_a_3585_; lean_object* v___x_3587_; uint8_t v_isShared_3588_; uint8_t v_isSharedCheck_3592_; 
lean_dec(v_val_3312_);
lean_dec(v_a_3292_);
lean_dec_ref(v_a_3291_);
lean_dec(v_a_3290_);
lean_dec_ref(v_a_3289_);
lean_dec(v_a_3288_);
lean_dec_ref(v_a_3287_);
lean_dec(v_a_3286_);
lean_dec_ref(v_a_3285_);
lean_dec(v_a_3284_);
lean_dec(v_a_3283_);
lean_dec_ref(v_e_3281_);
v_a_3585_ = lean_ctor_get(v___x_3377_, 0);
v_isSharedCheck_3592_ = !lean_is_exclusive(v___x_3377_);
if (v_isSharedCheck_3592_ == 0)
{
v___x_3587_ = v___x_3377_;
v_isShared_3588_ = v_isSharedCheck_3592_;
goto v_resetjp_3586_;
}
else
{
lean_inc(v_a_3585_);
lean_dec(v___x_3377_);
v___x_3587_ = lean_box(0);
v_isShared_3588_ = v_isSharedCheck_3592_;
goto v_resetjp_3586_;
}
v_resetjp_3586_:
{
lean_object* v___x_3590_; 
if (v_isShared_3588_ == 0)
{
v___x_3590_ = v___x_3587_;
goto v_reusejp_3589_;
}
else
{
lean_object* v_reuseFailAlloc_3591_; 
v_reuseFailAlloc_3591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3591_, 0, v_a_3585_);
v___x_3590_ = v_reuseFailAlloc_3591_;
goto v_reusejp_3589_;
}
v_reusejp_3589_:
{
return v___x_3590_;
}
}
}
}
}
else
{
lean_object* v_a_3593_; lean_object* v___x_3595_; uint8_t v_isShared_3596_; uint8_t v_isSharedCheck_3600_; 
lean_dec(v_val_3312_);
lean_dec(v_a_3292_);
lean_dec_ref(v_a_3291_);
lean_dec(v_a_3290_);
lean_dec_ref(v_a_3289_);
lean_dec(v_a_3288_);
lean_dec_ref(v_a_3287_);
lean_dec(v_a_3286_);
lean_dec_ref(v_a_3285_);
lean_dec(v_a_3284_);
lean_dec(v_a_3283_);
lean_dec_ref(v_e_3281_);
v_a_3593_ = lean_ctor_get(v___x_3314_, 0);
v_isSharedCheck_3600_ = !lean_is_exclusive(v___x_3314_);
if (v_isSharedCheck_3600_ == 0)
{
v___x_3595_ = v___x_3314_;
v_isShared_3596_ = v_isSharedCheck_3600_;
goto v_resetjp_3594_;
}
else
{
lean_inc(v_a_3593_);
lean_dec(v___x_3314_);
v___x_3595_ = lean_box(0);
v_isShared_3596_ = v_isSharedCheck_3600_;
goto v_resetjp_3594_;
}
v_resetjp_3594_:
{
lean_object* v___x_3598_; 
if (v_isShared_3596_ == 0)
{
v___x_3598_ = v___x_3595_;
goto v_reusejp_3597_;
}
else
{
lean_object* v_reuseFailAlloc_3599_; 
v_reuseFailAlloc_3599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3599_, 0, v_a_3593_);
v___x_3598_ = v_reuseFailAlloc_3599_;
goto v_reusejp_3597_;
}
v_reusejp_3597_:
{
return v___x_3598_;
}
}
}
}
else
{
lean_object* v___x_3601_; lean_object* v___x_3603_; 
lean_dec(v_val_3312_);
lean_dec(v_a_3292_);
lean_dec_ref(v_a_3291_);
lean_dec(v_a_3290_);
lean_dec_ref(v_a_3289_);
lean_dec(v_a_3288_);
lean_dec_ref(v_a_3287_);
lean_dec(v_a_3286_);
lean_dec_ref(v_a_3285_);
lean_dec(v_a_3284_);
lean_dec(v_a_3283_);
lean_dec_ref(v_e_3281_);
v___x_3601_ = lean_box(0);
if (v_isShared_3309_ == 0)
{
lean_ctor_set(v___x_3308_, 0, v___x_3601_);
v___x_3603_ = v___x_3308_;
goto v_reusejp_3602_;
}
else
{
lean_object* v_reuseFailAlloc_3604_; 
v_reuseFailAlloc_3604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3604_, 0, v___x_3601_);
v___x_3603_ = v_reuseFailAlloc_3604_;
goto v_reusejp_3602_;
}
v_reusejp_3602_:
{
return v___x_3603_;
}
}
}
else
{
lean_object* v___x_3605_; lean_object* v___x_3607_; 
lean_dec(v___x_3311_);
lean_dec(v_a_3292_);
lean_dec_ref(v_a_3291_);
lean_dec(v_a_3290_);
lean_dec_ref(v_a_3289_);
lean_dec(v_a_3288_);
lean_dec_ref(v_a_3287_);
lean_dec(v_a_3286_);
lean_dec_ref(v_a_3285_);
lean_dec(v_a_3284_);
lean_dec(v_a_3283_);
lean_dec(v_parent_x3f_3282_);
lean_dec_ref(v_e_3281_);
v___x_3605_ = lean_box(0);
if (v_isShared_3309_ == 0)
{
lean_ctor_set(v___x_3308_, 0, v___x_3605_);
v___x_3607_ = v___x_3308_;
goto v_reusejp_3606_;
}
else
{
lean_object* v_reuseFailAlloc_3608_; 
v_reuseFailAlloc_3608_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3608_, 0, v___x_3605_);
v___x_3607_ = v_reuseFailAlloc_3608_;
goto v_reusejp_3606_;
}
v_reusejp_3606_:
{
return v___x_3607_;
}
}
}
else
{
lean_object* v___x_3609_; lean_object* v___x_3611_; 
lean_dec(v_a_3292_);
lean_dec_ref(v_a_3291_);
lean_dec(v_a_3290_);
lean_dec_ref(v_a_3289_);
lean_dec(v_a_3288_);
lean_dec_ref(v_a_3287_);
lean_dec(v_a_3286_);
lean_dec_ref(v_a_3285_);
lean_dec(v_a_3284_);
lean_dec(v_a_3283_);
lean_dec(v_parent_x3f_3282_);
lean_dec_ref(v_e_3281_);
v___x_3609_ = lean_box(0);
if (v_isShared_3309_ == 0)
{
lean_ctor_set(v___x_3308_, 0, v___x_3609_);
v___x_3611_ = v___x_3308_;
goto v_reusejp_3610_;
}
else
{
lean_object* v_reuseFailAlloc_3612_; 
v_reuseFailAlloc_3612_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3612_, 0, v___x_3609_);
v___x_3611_ = v_reuseFailAlloc_3612_;
goto v_reusejp_3610_;
}
v_reusejp_3610_:
{
return v___x_3611_;
}
}
}
}
else
{
lean_object* v_a_3614_; lean_object* v___x_3616_; uint8_t v_isShared_3617_; uint8_t v_isSharedCheck_3621_; 
lean_dec(v_a_3292_);
lean_dec_ref(v_a_3291_);
lean_dec(v_a_3290_);
lean_dec_ref(v_a_3289_);
lean_dec(v_a_3288_);
lean_dec_ref(v_a_3287_);
lean_dec(v_a_3286_);
lean_dec_ref(v_a_3285_);
lean_dec(v_a_3284_);
lean_dec(v_a_3283_);
lean_dec(v_parent_x3f_3282_);
lean_dec_ref(v_e_3281_);
v_a_3614_ = lean_ctor_get(v___x_3305_, 0);
v_isSharedCheck_3621_ = !lean_is_exclusive(v___x_3305_);
if (v_isSharedCheck_3621_ == 0)
{
v___x_3616_ = v___x_3305_;
v_isShared_3617_ = v_isSharedCheck_3621_;
goto v_resetjp_3615_;
}
else
{
lean_inc(v_a_3614_);
lean_dec(v___x_3305_);
v___x_3616_ = lean_box(0);
v_isShared_3617_ = v_isSharedCheck_3621_;
goto v_resetjp_3615_;
}
v_resetjp_3615_:
{
lean_object* v___x_3619_; 
if (v_isShared_3617_ == 0)
{
v___x_3619_ = v___x_3616_;
goto v_reusejp_3618_;
}
else
{
lean_object* v_reuseFailAlloc_3620_; 
v_reuseFailAlloc_3620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3620_, 0, v_a_3614_);
v___x_3619_ = v_reuseFailAlloc_3620_;
goto v_reusejp_3618_;
}
v_reusejp_3618_:
{
return v___x_3619_;
}
}
}
}
else
{
lean_object* v___x_3622_; lean_object* v___x_3624_; 
lean_dec(v_a_3292_);
lean_dec_ref(v_a_3291_);
lean_dec(v_a_3290_);
lean_dec_ref(v_a_3289_);
lean_dec(v_a_3288_);
lean_dec_ref(v_a_3287_);
lean_dec(v_a_3286_);
lean_dec_ref(v_a_3285_);
lean_dec(v_a_3284_);
lean_dec(v_a_3283_);
lean_dec(v_parent_x3f_3282_);
lean_dec_ref(v_e_3281_);
v___x_3622_ = lean_box(0);
if (v_isShared_3298_ == 0)
{
lean_ctor_set(v___x_3297_, 0, v___x_3622_);
v___x_3624_ = v___x_3297_;
goto v_reusejp_3623_;
}
else
{
lean_object* v_reuseFailAlloc_3625_; 
v_reuseFailAlloc_3625_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3625_, 0, v___x_3622_);
v___x_3624_ = v_reuseFailAlloc_3625_;
goto v_reusejp_3623_;
}
v_reusejp_3623_:
{
return v___x_3624_;
}
}
}
}
}
else
{
lean_object* v_a_3627_; lean_object* v___x_3629_; uint8_t v_isShared_3630_; uint8_t v_isSharedCheck_3634_; 
lean_dec(v_a_3292_);
lean_dec_ref(v_a_3291_);
lean_dec(v_a_3290_);
lean_dec_ref(v_a_3289_);
lean_dec(v_a_3288_);
lean_dec_ref(v_a_3287_);
lean_dec(v_a_3286_);
lean_dec_ref(v_a_3285_);
lean_dec(v_a_3284_);
lean_dec(v_a_3283_);
lean_dec(v_parent_x3f_3282_);
lean_dec_ref(v_e_3281_);
v_a_3627_ = lean_ctor_get(v___x_3294_, 0);
v_isSharedCheck_3634_ = !lean_is_exclusive(v___x_3294_);
if (v_isSharedCheck_3634_ == 0)
{
v___x_3629_ = v___x_3294_;
v_isShared_3630_ = v_isSharedCheck_3634_;
goto v_resetjp_3628_;
}
else
{
lean_inc(v_a_3627_);
lean_dec(v___x_3294_);
v___x_3629_ = lean_box(0);
v_isShared_3630_ = v_isSharedCheck_3634_;
goto v_resetjp_3628_;
}
v_resetjp_3628_:
{
lean_object* v___x_3632_; 
if (v_isShared_3630_ == 0)
{
v___x_3632_ = v___x_3629_;
goto v_reusejp_3631_;
}
else
{
lean_object* v_reuseFailAlloc_3633_; 
v_reuseFailAlloc_3633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3633_, 0, v_a_3627_);
v___x_3632_ = v_reuseFailAlloc_3633_;
goto v_reusejp_3631_;
}
v_reusejp_3631_:
{
return v___x_3632_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_internalize___boxed(lean_object* v_e_3635_, lean_object* v_parent_x3f_3636_, lean_object* v_a_3637_, lean_object* v_a_3638_, lean_object* v_a_3639_, lean_object* v_a_3640_, lean_object* v_a_3641_, lean_object* v_a_3642_, lean_object* v_a_3643_, lean_object* v_a_3644_, lean_object* v_a_3645_, lean_object* v_a_3646_, lean_object* v_a_3647_){
_start:
{
lean_object* v_res_3648_; 
v_res_3648_ = l_Lean_Meta_Grind_Arith_CommRing_internalize(v_e_3635_, v_parent_x3f_3636_, v_a_3637_, v_a_3638_, v_a_3639_, v_a_3640_, v_a_3641_, v_a_3642_, v_a_3643_, v_a_3644_, v_a_3645_, v_a_3646_);
return v_res_3648_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0(lean_object* v_00_u03b2_3649_, lean_object* v_x_3650_, lean_object* v_x_3651_, lean_object* v_x_3652_){
_start:
{
lean_object* v___x_3653_; 
v___x_3653_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0___redArg(v_x_3650_, v_x_3651_, v_x_3652_);
return v___x_3653_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__2(lean_object* v_cls_3654_, lean_object* v_msg_3655_, lean_object* v___y_3656_, lean_object* v___y_3657_, lean_object* v___y_3658_, lean_object* v___y_3659_, lean_object* v___y_3660_, lean_object* v___y_3661_, lean_object* v___y_3662_, lean_object* v___y_3663_, lean_object* v___y_3664_, lean_object* v___y_3665_, lean_object* v___y_3666_){
_start:
{
lean_object* v___x_3668_; 
v___x_3668_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__2___redArg(v_cls_3654_, v_msg_3655_, v___y_3663_, v___y_3664_, v___y_3665_, v___y_3666_);
return v___x_3668_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__2___boxed(lean_object* v_cls_3669_, lean_object* v_msg_3670_, lean_object* v___y_3671_, lean_object* v___y_3672_, lean_object* v___y_3673_, lean_object* v___y_3674_, lean_object* v___y_3675_, lean_object* v___y_3676_, lean_object* v___y_3677_, lean_object* v___y_3678_, lean_object* v___y_3679_, lean_object* v___y_3680_, lean_object* v___y_3681_, lean_object* v___y_3682_){
_start:
{
lean_object* v_res_3683_; 
v_res_3683_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__2(v_cls_3669_, v_msg_3670_, v___y_3671_, v___y_3672_, v___y_3673_, v___y_3674_, v___y_3675_, v___y_3676_, v___y_3677_, v___y_3678_, v___y_3679_, v___y_3680_, v___y_3681_);
lean_dec(v___y_3681_);
lean_dec_ref(v___y_3680_);
lean_dec(v___y_3679_);
lean_dec_ref(v___y_3678_);
lean_dec(v___y_3677_);
lean_dec_ref(v___y_3676_);
lean_dec(v___y_3675_);
lean_dec_ref(v___y_3674_);
lean_dec(v___y_3673_);
lean_dec(v___y_3672_);
lean_dec_ref(v___y_3671_);
return v_res_3683_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__4(lean_object* v_cls_3684_, lean_object* v_msg_3685_, lean_object* v___y_3686_, lean_object* v___y_3687_, lean_object* v___y_3688_, lean_object* v___y_3689_, lean_object* v___y_3690_, lean_object* v___y_3691_, lean_object* v___y_3692_, lean_object* v___y_3693_, lean_object* v___y_3694_, lean_object* v___y_3695_, lean_object* v___y_3696_){
_start:
{
lean_object* v___x_3698_; 
v___x_3698_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__4___redArg(v_cls_3684_, v_msg_3685_, v___y_3693_, v___y_3694_, v___y_3695_, v___y_3696_);
return v___x_3698_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__4___boxed(lean_object* v_cls_3699_, lean_object* v_msg_3700_, lean_object* v___y_3701_, lean_object* v___y_3702_, lean_object* v___y_3703_, lean_object* v___y_3704_, lean_object* v___y_3705_, lean_object* v___y_3706_, lean_object* v___y_3707_, lean_object* v___y_3708_, lean_object* v___y_3709_, lean_object* v___y_3710_, lean_object* v___y_3711_, lean_object* v___y_3712_){
_start:
{
lean_object* v_res_3713_; 
v_res_3713_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__4(v_cls_3699_, v_msg_3700_, v___y_3701_, v___y_3702_, v___y_3703_, v___y_3704_, v___y_3705_, v___y_3706_, v___y_3707_, v___y_3708_, v___y_3709_, v___y_3710_, v___y_3711_);
lean_dec(v___y_3711_);
lean_dec_ref(v___y_3710_);
lean_dec(v___y_3709_);
lean_dec_ref(v___y_3708_);
lean_dec(v___y_3707_);
lean_dec_ref(v___y_3706_);
lean_dec(v___y_3705_);
lean_dec_ref(v___y_3704_);
lean_dec(v___y_3703_);
lean_dec(v___y_3702_);
lean_dec(v___y_3701_);
return v_res_3713_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__6(lean_object* v_cls_3714_, lean_object* v_msg_3715_, lean_object* v___y_3716_, lean_object* v___y_3717_, lean_object* v___y_3718_, lean_object* v___y_3719_, lean_object* v___y_3720_, lean_object* v___y_3721_, lean_object* v___y_3722_, lean_object* v___y_3723_, lean_object* v___y_3724_, lean_object* v___y_3725_, lean_object* v___y_3726_){
_start:
{
lean_object* v___x_3728_; 
v___x_3728_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__6___redArg(v_cls_3714_, v_msg_3715_, v___y_3723_, v___y_3724_, v___y_3725_, v___y_3726_);
return v___x_3728_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__6___boxed(lean_object* v_cls_3729_, lean_object* v_msg_3730_, lean_object* v___y_3731_, lean_object* v___y_3732_, lean_object* v___y_3733_, lean_object* v___y_3734_, lean_object* v___y_3735_, lean_object* v___y_3736_, lean_object* v___y_3737_, lean_object* v___y_3738_, lean_object* v___y_3739_, lean_object* v___y_3740_, lean_object* v___y_3741_, lean_object* v___y_3742_){
_start:
{
lean_object* v_res_3743_; 
v_res_3743_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__6(v_cls_3729_, v_msg_3730_, v___y_3731_, v___y_3732_, v___y_3733_, v___y_3734_, v___y_3735_, v___y_3736_, v___y_3737_, v___y_3738_, v___y_3739_, v___y_3740_, v___y_3741_);
lean_dec(v___y_3741_);
lean_dec_ref(v___y_3740_);
lean_dec(v___y_3739_);
lean_dec_ref(v___y_3738_);
lean_dec(v___y_3737_);
lean_dec_ref(v___y_3736_);
lean_dec(v___y_3735_);
lean_dec_ref(v___y_3734_);
lean_dec(v___y_3733_);
lean_dec(v___y_3732_);
lean_dec(v___y_3731_);
return v_res_3743_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__8(lean_object* v_cls_3744_, lean_object* v_msg_3745_, lean_object* v___y_3746_, lean_object* v___y_3747_, lean_object* v___y_3748_, lean_object* v___y_3749_, lean_object* v___y_3750_, lean_object* v___y_3751_, lean_object* v___y_3752_, lean_object* v___y_3753_, lean_object* v___y_3754_, lean_object* v___y_3755_, lean_object* v___y_3756_){
_start:
{
lean_object* v___x_3758_; 
v___x_3758_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__8___redArg(v_cls_3744_, v_msg_3745_, v___y_3753_, v___y_3754_, v___y_3755_, v___y_3756_);
return v___x_3758_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__8___boxed(lean_object* v_cls_3759_, lean_object* v_msg_3760_, lean_object* v___y_3761_, lean_object* v___y_3762_, lean_object* v___y_3763_, lean_object* v___y_3764_, lean_object* v___y_3765_, lean_object* v___y_3766_, lean_object* v___y_3767_, lean_object* v___y_3768_, lean_object* v___y_3769_, lean_object* v___y_3770_, lean_object* v___y_3771_, lean_object* v___y_3772_){
_start:
{
lean_object* v_res_3773_; 
v_res_3773_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__8(v_cls_3759_, v_msg_3760_, v___y_3761_, v___y_3762_, v___y_3763_, v___y_3764_, v___y_3765_, v___y_3766_, v___y_3767_, v___y_3768_, v___y_3769_, v___y_3770_, v___y_3771_);
lean_dec(v___y_3771_);
lean_dec_ref(v___y_3770_);
lean_dec(v___y_3769_);
lean_dec_ref(v___y_3768_);
lean_dec(v___y_3767_);
lean_dec_ref(v___y_3766_);
lean_dec(v___y_3765_);
lean_dec_ref(v___y_3764_);
lean_dec(v___y_3763_);
lean_dec(v___y_3762_);
lean_dec(v___y_3761_);
return v_res_3773_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0(lean_object* v_00_u03b2_3774_, lean_object* v_x_3775_, size_t v_x_3776_, size_t v_x_3777_, lean_object* v_x_3778_, lean_object* v_x_3779_){
_start:
{
lean_object* v___x_3780_; 
v___x_3780_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0___redArg(v_x_3775_, v_x_3776_, v_x_3777_, v_x_3778_, v_x_3779_);
return v___x_3780_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3781_, lean_object* v_x_3782_, lean_object* v_x_3783_, lean_object* v_x_3784_, lean_object* v_x_3785_, lean_object* v_x_3786_){
_start:
{
size_t v_x_206167__boxed_3787_; size_t v_x_206168__boxed_3788_; lean_object* v_res_3789_; 
v_x_206167__boxed_3787_ = lean_unbox_usize(v_x_3783_);
lean_dec(v_x_3783_);
v_x_206168__boxed_3788_ = lean_unbox_usize(v_x_3784_);
lean_dec(v_x_3784_);
v_res_3789_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0(v_00_u03b2_3781_, v_x_3782_, v_x_206167__boxed_3787_, v_x_206168__boxed_3788_, v_x_3785_, v_x_3786_);
return v_res_3789_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0_spec__5(lean_object* v_00_u03b2_3790_, lean_object* v_n_3791_, lean_object* v_k_3792_, lean_object* v_v_3793_){
_start:
{
lean_object* v___x_3794_; 
v___x_3794_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0_spec__5___redArg(v_n_3791_, v_k_3792_, v_v_3793_);
return v___x_3794_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0_spec__6(lean_object* v_00_u03b2_3795_, size_t v_depth_3796_, lean_object* v_keys_3797_, lean_object* v_vals_3798_, lean_object* v_heq_3799_, lean_object* v_i_3800_, lean_object* v_entries_3801_){
_start:
{
lean_object* v___x_3802_; 
v___x_3802_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0_spec__6___redArg(v_depth_3796_, v_keys_3797_, v_vals_3798_, v_i_3800_, v_entries_3801_);
return v___x_3802_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0_spec__6___boxed(lean_object* v_00_u03b2_3803_, lean_object* v_depth_3804_, lean_object* v_keys_3805_, lean_object* v_vals_3806_, lean_object* v_heq_3807_, lean_object* v_i_3808_, lean_object* v_entries_3809_){
_start:
{
size_t v_depth_boxed_3810_; lean_object* v_res_3811_; 
v_depth_boxed_3810_ = lean_unbox_usize(v_depth_3804_);
lean_dec(v_depth_3804_);
v_res_3811_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0_spec__6(v_00_u03b2_3803_, v_depth_boxed_3810_, v_keys_3805_, v_vals_3806_, v_heq_3807_, v_i_3808_, v_entries_3809_);
lean_dec_ref(v_vals_3806_);
lean_dec_ref(v_keys_3805_);
return v_res_3811_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0_spec__5_spec__10(lean_object* v_00_u03b2_3812_, lean_object* v_x_3813_, lean_object* v_x_3814_, lean_object* v_x_3815_, lean_object* v_x_3816_){
_start:
{
lean_object* v___x_3817_; 
v___x_3817_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0_spec__5_spec__10___redArg(v_x_3813_, v_x_3814_, v_x_3815_, v_x_3816_);
return v___x_3817_;
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
