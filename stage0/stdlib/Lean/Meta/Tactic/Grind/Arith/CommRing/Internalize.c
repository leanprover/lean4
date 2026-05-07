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
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
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
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getConfig___redArg(lean_object*);
uint8_t l_Lean_Meta_Grind_Arith_isIntModuleVirtualParent(lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_reify_x3f(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Grind_Arith_CommRing_ringExt;
lean_object* l_Lean_Meta_Grind_SolverExtension_markTerm___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_updateLastTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_outOfBounds___redArg(lean_object*);
lean_object* l_Lean_PersistentArray_get_x21___redArg(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1_spec__5_spec__8_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1_spec__5_spec__8_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1_spec__5_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1_spec__5_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1_spec__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "failed to find instance"};
static const lean_object* l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1_spec__5___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1_spec__5___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1_spec__5___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1_spec__5___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1_spec__5_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1_spec__5_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars___lam__0(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg___closed__0;
static const lean_string_object l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "PowIdentity"};
static const lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__0_value;
static const lean_string_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "pow_eq"};
static const lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__1 = (const lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__1_value;
static const lean_ctor_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__2_value_aux_1),((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(169, 166, 196, 137, 32, 118, 33, 172)}};
static const lean_ctor_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__2_value_aux_2),((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(235, 179, 238, 185, 247, 4, 37, 103)}};
static const lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__2 = (const lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__2_value;
static const lean_string_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "grind"};
static const lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__3 = (const lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__3_value;
static const lean_string_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "ring"};
static const lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__4 = (const lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__4_value;
static const lean_ctor_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__5_value_aux_0),((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(17, 56, 209, 254, 185, 203, 153, 57)}};
static const lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__5 = (const lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__5_value;
static const lean_string_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__6 = (const lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__6_value;
static const lean_ctor_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__6_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__7 = (const lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__7_value;
static lean_once_cell_t l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__8;
static const lean_string_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "PowIdentity: pushing x^"};
static const lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__9 = (const lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__9_value;
static lean_once_cell_t l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__10;
static const lean_string_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = " = x for "};
static const lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__11 = (const lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__11_value;
static lean_once_cell_t l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__12;
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeInv(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeInv___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0_spec__1_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "internalize"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__1_value_aux_0),((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(17, 56, 209, 254, 185, 203, 153, 57)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__1_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__0_value),LEAN_SCALAR_PTR_LITERAL(140, 40, 248, 182, 136, 181, 0, 182)}};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__2;
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__3_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__4;
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "]: "};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__5_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__6;
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "semiring ["};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__7 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__7_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__8;
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "(non-comm) ring ["};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__9 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__9_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__10;
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "(non-comm) semiring ["};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__11 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__11_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__12;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_internalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_internalize___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0_spec__2(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0_spec__1_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v_toRing_165_; lean_object* v_invFn_x3f_166_; lean_object* v_semiringId_x3f_167_; lean_object* v_commSemiringInst_168_; lean_object* v_commRingInst_169_; lean_object* v_noZeroDivInst_x3f_170_; lean_object* v_fieldInst_x3f_171_; lean_object* v_powIdentityInst_x3f_172_; lean_object* v_denoteEntries_173_; lean_object* v_nextId_174_; lean_object* v_steps_175_; lean_object* v_queue_176_; lean_object* v_basis_177_; lean_object* v_diseqs_178_; uint8_t v_recheck_179_; lean_object* v_invSet_180_; lean_object* v_powIdentityVarCount_181_; lean_object* v_numEq0_x3f_182_; uint8_t v_numEq0Updated_183_; lean_object* v___x_185_; uint8_t v_isShared_186_; uint8_t v_isSharedCheck_215_; 
v_toRing_165_ = lean_ctor_get(v_s_164_, 0);
v_invFn_x3f_166_ = lean_ctor_get(v_s_164_, 1);
v_semiringId_x3f_167_ = lean_ctor_get(v_s_164_, 2);
v_commSemiringInst_168_ = lean_ctor_get(v_s_164_, 3);
v_commRingInst_169_ = lean_ctor_get(v_s_164_, 4);
v_noZeroDivInst_x3f_170_ = lean_ctor_get(v_s_164_, 5);
v_fieldInst_x3f_171_ = lean_ctor_get(v_s_164_, 6);
v_powIdentityInst_x3f_172_ = lean_ctor_get(v_s_164_, 7);
v_denoteEntries_173_ = lean_ctor_get(v_s_164_, 8);
v_nextId_174_ = lean_ctor_get(v_s_164_, 9);
v_steps_175_ = lean_ctor_get(v_s_164_, 10);
v_queue_176_ = lean_ctor_get(v_s_164_, 11);
v_basis_177_ = lean_ctor_get(v_s_164_, 12);
v_diseqs_178_ = lean_ctor_get(v_s_164_, 13);
v_recheck_179_ = lean_ctor_get_uint8(v_s_164_, sizeof(void*)*17);
v_invSet_180_ = lean_ctor_get(v_s_164_, 14);
v_powIdentityVarCount_181_ = lean_ctor_get(v_s_164_, 15);
v_numEq0_x3f_182_ = lean_ctor_get(v_s_164_, 16);
v_numEq0Updated_183_ = lean_ctor_get_uint8(v_s_164_, sizeof(void*)*17 + 1);
v_isSharedCheck_215_ = !lean_is_exclusive(v_s_164_);
if (v_isSharedCheck_215_ == 0)
{
v___x_185_ = v_s_164_;
v_isShared_186_ = v_isSharedCheck_215_;
goto v_resetjp_184_;
}
else
{
lean_inc(v_numEq0_x3f_182_);
lean_inc(v_powIdentityVarCount_181_);
lean_inc(v_invSet_180_);
lean_inc(v_diseqs_178_);
lean_inc(v_basis_177_);
lean_inc(v_queue_176_);
lean_inc(v_steps_175_);
lean_inc(v_nextId_174_);
lean_inc(v_denoteEntries_173_);
lean_inc(v_powIdentityInst_x3f_172_);
lean_inc(v_fieldInst_x3f_171_);
lean_inc(v_noZeroDivInst_x3f_170_);
lean_inc(v_commRingInst_169_);
lean_inc(v_commSemiringInst_168_);
lean_inc(v_semiringId_x3f_167_);
lean_inc(v_invFn_x3f_166_);
lean_inc(v_toRing_165_);
lean_dec(v_s_164_);
v___x_185_ = lean_box(0);
v_isShared_186_ = v_isSharedCheck_215_;
goto v_resetjp_184_;
}
v_resetjp_184_:
{
lean_object* v_id_187_; lean_object* v_type_188_; lean_object* v_u_189_; lean_object* v_ringInst_190_; lean_object* v_semiringInst_191_; lean_object* v_charInst_x3f_192_; lean_object* v_addFn_x3f_193_; lean_object* v_mulFn_x3f_194_; lean_object* v_subFn_x3f_195_; lean_object* v_powFn_x3f_196_; lean_object* v_intCastFn_x3f_197_; lean_object* v_natCastFn_x3f_198_; lean_object* v_one_x3f_199_; lean_object* v_vars_200_; lean_object* v_varMap_201_; lean_object* v_denote_202_; lean_object* v___x_204_; uint8_t v_isShared_205_; uint8_t v_isSharedCheck_213_; 
v_id_187_ = lean_ctor_get(v_toRing_165_, 0);
v_type_188_ = lean_ctor_get(v_toRing_165_, 1);
v_u_189_ = lean_ctor_get(v_toRing_165_, 2);
v_ringInst_190_ = lean_ctor_get(v_toRing_165_, 3);
v_semiringInst_191_ = lean_ctor_get(v_toRing_165_, 4);
v_charInst_x3f_192_ = lean_ctor_get(v_toRing_165_, 5);
v_addFn_x3f_193_ = lean_ctor_get(v_toRing_165_, 6);
v_mulFn_x3f_194_ = lean_ctor_get(v_toRing_165_, 7);
v_subFn_x3f_195_ = lean_ctor_get(v_toRing_165_, 8);
v_powFn_x3f_196_ = lean_ctor_get(v_toRing_165_, 10);
v_intCastFn_x3f_197_ = lean_ctor_get(v_toRing_165_, 11);
v_natCastFn_x3f_198_ = lean_ctor_get(v_toRing_165_, 12);
v_one_x3f_199_ = lean_ctor_get(v_toRing_165_, 13);
v_vars_200_ = lean_ctor_get(v_toRing_165_, 14);
v_varMap_201_ = lean_ctor_get(v_toRing_165_, 15);
v_denote_202_ = lean_ctor_get(v_toRing_165_, 16);
v_isSharedCheck_213_ = !lean_is_exclusive(v_toRing_165_);
if (v_isSharedCheck_213_ == 0)
{
lean_object* v_unused_214_; 
v_unused_214_ = lean_ctor_get(v_toRing_165_, 9);
lean_dec(v_unused_214_);
v___x_204_ = v_toRing_165_;
v_isShared_205_ = v_isSharedCheck_213_;
goto v_resetjp_203_;
}
else
{
lean_inc(v_denote_202_);
lean_inc(v_varMap_201_);
lean_inc(v_vars_200_);
lean_inc(v_one_x3f_199_);
lean_inc(v_natCastFn_x3f_198_);
lean_inc(v_intCastFn_x3f_197_);
lean_inc(v_powFn_x3f_196_);
lean_inc(v_subFn_x3f_195_);
lean_inc(v_mulFn_x3f_194_);
lean_inc(v_addFn_x3f_193_);
lean_inc(v_charInst_x3f_192_);
lean_inc(v_semiringInst_191_);
lean_inc(v_ringInst_190_);
lean_inc(v_u_189_);
lean_inc(v_type_188_);
lean_inc(v_id_187_);
lean_dec(v_toRing_165_);
v___x_204_ = lean_box(0);
v_isShared_205_ = v_isSharedCheck_213_;
goto v_resetjp_203_;
}
v_resetjp_203_:
{
lean_object* v___x_206_; lean_object* v___x_208_; 
v___x_206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_206_, 0, v_a_163_);
if (v_isShared_205_ == 0)
{
lean_ctor_set(v___x_204_, 9, v___x_206_);
v___x_208_ = v___x_204_;
goto v_reusejp_207_;
}
else
{
lean_object* v_reuseFailAlloc_212_; 
v_reuseFailAlloc_212_ = lean_alloc_ctor(0, 17, 0);
lean_ctor_set(v_reuseFailAlloc_212_, 0, v_id_187_);
lean_ctor_set(v_reuseFailAlloc_212_, 1, v_type_188_);
lean_ctor_set(v_reuseFailAlloc_212_, 2, v_u_189_);
lean_ctor_set(v_reuseFailAlloc_212_, 3, v_ringInst_190_);
lean_ctor_set(v_reuseFailAlloc_212_, 4, v_semiringInst_191_);
lean_ctor_set(v_reuseFailAlloc_212_, 5, v_charInst_x3f_192_);
lean_ctor_set(v_reuseFailAlloc_212_, 6, v_addFn_x3f_193_);
lean_ctor_set(v_reuseFailAlloc_212_, 7, v_mulFn_x3f_194_);
lean_ctor_set(v_reuseFailAlloc_212_, 8, v_subFn_x3f_195_);
lean_ctor_set(v_reuseFailAlloc_212_, 9, v___x_206_);
lean_ctor_set(v_reuseFailAlloc_212_, 10, v_powFn_x3f_196_);
lean_ctor_set(v_reuseFailAlloc_212_, 11, v_intCastFn_x3f_197_);
lean_ctor_set(v_reuseFailAlloc_212_, 12, v_natCastFn_x3f_198_);
lean_ctor_set(v_reuseFailAlloc_212_, 13, v_one_x3f_199_);
lean_ctor_set(v_reuseFailAlloc_212_, 14, v_vars_200_);
lean_ctor_set(v_reuseFailAlloc_212_, 15, v_varMap_201_);
lean_ctor_set(v_reuseFailAlloc_212_, 16, v_denote_202_);
v___x_208_ = v_reuseFailAlloc_212_;
goto v_reusejp_207_;
}
v_reusejp_207_:
{
lean_object* v___x_210_; 
if (v_isShared_186_ == 0)
{
lean_ctor_set(v___x_185_, 0, v___x_208_);
v___x_210_ = v___x_185_;
goto v_reusejp_209_;
}
else
{
lean_object* v_reuseFailAlloc_211_; 
v_reuseFailAlloc_211_ = lean_alloc_ctor(0, 17, 2);
lean_ctor_set(v_reuseFailAlloc_211_, 0, v___x_208_);
lean_ctor_set(v_reuseFailAlloc_211_, 1, v_invFn_x3f_166_);
lean_ctor_set(v_reuseFailAlloc_211_, 2, v_semiringId_x3f_167_);
lean_ctor_set(v_reuseFailAlloc_211_, 3, v_commSemiringInst_168_);
lean_ctor_set(v_reuseFailAlloc_211_, 4, v_commRingInst_169_);
lean_ctor_set(v_reuseFailAlloc_211_, 5, v_noZeroDivInst_x3f_170_);
lean_ctor_set(v_reuseFailAlloc_211_, 6, v_fieldInst_x3f_171_);
lean_ctor_set(v_reuseFailAlloc_211_, 7, v_powIdentityInst_x3f_172_);
lean_ctor_set(v_reuseFailAlloc_211_, 8, v_denoteEntries_173_);
lean_ctor_set(v_reuseFailAlloc_211_, 9, v_nextId_174_);
lean_ctor_set(v_reuseFailAlloc_211_, 10, v_steps_175_);
lean_ctor_set(v_reuseFailAlloc_211_, 11, v_queue_176_);
lean_ctor_set(v_reuseFailAlloc_211_, 12, v_basis_177_);
lean_ctor_set(v_reuseFailAlloc_211_, 13, v_diseqs_178_);
lean_ctor_set(v_reuseFailAlloc_211_, 14, v_invSet_180_);
lean_ctor_set(v_reuseFailAlloc_211_, 15, v_powIdentityVarCount_181_);
lean_ctor_set(v_reuseFailAlloc_211_, 16, v_numEq0_x3f_182_);
lean_ctor_set_uint8(v_reuseFailAlloc_211_, sizeof(void*)*17, v_recheck_179_);
lean_ctor_set_uint8(v_reuseFailAlloc_211_, sizeof(void*)*17 + 1, v_numEq0Updated_183_);
v___x_210_ = v_reuseFailAlloc_211_;
goto v_reusejp_209_;
}
v_reusejp_209_:
{
return v___x_210_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1_spec__5_spec__8_spec__9(lean_object* v_msgData_216_, lean_object* v___y_217_, lean_object* v___y_218_, lean_object* v___y_219_, lean_object* v___y_220_){
_start:
{
lean_object* v___x_222_; lean_object* v_env_223_; lean_object* v___x_224_; lean_object* v_mctx_225_; lean_object* v_lctx_226_; lean_object* v_options_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; 
v___x_222_ = lean_st_ref_get(v___y_220_);
v_env_223_ = lean_ctor_get(v___x_222_, 0);
lean_inc_ref(v_env_223_);
lean_dec(v___x_222_);
v___x_224_ = lean_st_ref_get(v___y_218_);
v_mctx_225_ = lean_ctor_get(v___x_224_, 0);
lean_inc_ref(v_mctx_225_);
lean_dec(v___x_224_);
v_lctx_226_ = lean_ctor_get(v___y_217_, 2);
v_options_227_ = lean_ctor_get(v___y_219_, 2);
lean_inc_ref(v_options_227_);
lean_inc_ref(v_lctx_226_);
v___x_228_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_228_, 0, v_env_223_);
lean_ctor_set(v___x_228_, 1, v_mctx_225_);
lean_ctor_set(v___x_228_, 2, v_lctx_226_);
lean_ctor_set(v___x_228_, 3, v_options_227_);
v___x_229_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_229_, 0, v___x_228_);
lean_ctor_set(v___x_229_, 1, v_msgData_216_);
v___x_230_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_230_, 0, v___x_229_);
return v___x_230_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1_spec__5_spec__8_spec__9___boxed(lean_object* v_msgData_231_, lean_object* v___y_232_, lean_object* v___y_233_, lean_object* v___y_234_, lean_object* v___y_235_, lean_object* v___y_236_){
_start:
{
lean_object* v_res_237_; 
v_res_237_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1_spec__5_spec__8_spec__9(v_msgData_231_, v___y_232_, v___y_233_, v___y_234_, v___y_235_);
lean_dec(v___y_235_);
lean_dec_ref(v___y_234_);
lean_dec(v___y_233_);
lean_dec_ref(v___y_232_);
return v_res_237_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1_spec__5_spec__8___redArg(lean_object* v_msg_238_, lean_object* v___y_239_, lean_object* v___y_240_, lean_object* v___y_241_, lean_object* v___y_242_){
_start:
{
lean_object* v_ref_244_; lean_object* v___x_245_; lean_object* v_a_246_; lean_object* v___x_248_; uint8_t v_isShared_249_; uint8_t v_isSharedCheck_254_; 
v_ref_244_ = lean_ctor_get(v___y_241_, 5);
v___x_245_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1_spec__5_spec__8_spec__9(v_msg_238_, v___y_239_, v___y_240_, v___y_241_, v___y_242_);
v_a_246_ = lean_ctor_get(v___x_245_, 0);
v_isSharedCheck_254_ = !lean_is_exclusive(v___x_245_);
if (v_isSharedCheck_254_ == 0)
{
v___x_248_ = v___x_245_;
v_isShared_249_ = v_isSharedCheck_254_;
goto v_resetjp_247_;
}
else
{
lean_inc(v_a_246_);
lean_dec(v___x_245_);
v___x_248_ = lean_box(0);
v_isShared_249_ = v_isSharedCheck_254_;
goto v_resetjp_247_;
}
v_resetjp_247_:
{
lean_object* v___x_250_; lean_object* v___x_252_; 
lean_inc(v_ref_244_);
v___x_250_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_250_, 0, v_ref_244_);
lean_ctor_set(v___x_250_, 1, v_a_246_);
if (v_isShared_249_ == 0)
{
lean_ctor_set_tag(v___x_248_, 1);
lean_ctor_set(v___x_248_, 0, v___x_250_);
v___x_252_ = v___x_248_;
goto v_reusejp_251_;
}
else
{
lean_object* v_reuseFailAlloc_253_; 
v_reuseFailAlloc_253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_253_, 0, v___x_250_);
v___x_252_ = v_reuseFailAlloc_253_;
goto v_reusejp_251_;
}
v_reusejp_251_:
{
return v___x_252_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1_spec__5_spec__8___redArg___boxed(lean_object* v_msg_255_, lean_object* v___y_256_, lean_object* v___y_257_, lean_object* v___y_258_, lean_object* v___y_259_, lean_object* v___y_260_){
_start:
{
lean_object* v_res_261_; 
v_res_261_ = l_Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1_spec__5_spec__8___redArg(v_msg_255_, v___y_256_, v___y_257_, v___y_258_, v___y_259_);
lean_dec(v___y_259_);
lean_dec_ref(v___y_258_);
lean_dec(v___y_257_);
lean_dec_ref(v___y_256_);
return v_res_261_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1_spec__5___closed__1(void){
_start:
{
lean_object* v___x_263_; lean_object* v___x_264_; 
v___x_263_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1_spec__5___closed__0));
v___x_264_ = l_Lean_stringToMessageData(v___x_263_);
return v___x_264_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1_spec__5(lean_object* v_type_265_, lean_object* v___y_266_, lean_object* v___y_267_, lean_object* v___y_268_, lean_object* v___y_269_, lean_object* v___y_270_, lean_object* v___y_271_, lean_object* v___y_272_, lean_object* v___y_273_, lean_object* v___y_274_, lean_object* v___y_275_, lean_object* v___y_276_){
_start:
{
lean_object* v___x_278_; 
lean_inc_ref(v_type_265_);
v___x_278_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f(v_type_265_, v___y_273_, v___y_274_, v___y_275_, v___y_276_);
if (lean_obj_tag(v___x_278_) == 0)
{
lean_object* v_a_279_; lean_object* v___x_281_; uint8_t v_isShared_282_; uint8_t v_isSharedCheck_291_; 
v_a_279_ = lean_ctor_get(v___x_278_, 0);
v_isSharedCheck_291_ = !lean_is_exclusive(v___x_278_);
if (v_isSharedCheck_291_ == 0)
{
v___x_281_ = v___x_278_;
v_isShared_282_ = v_isSharedCheck_291_;
goto v_resetjp_280_;
}
else
{
lean_inc(v_a_279_);
lean_dec(v___x_278_);
v___x_281_ = lean_box(0);
v_isShared_282_ = v_isSharedCheck_291_;
goto v_resetjp_280_;
}
v_resetjp_280_:
{
if (lean_obj_tag(v_a_279_) == 1)
{
lean_object* v_val_283_; lean_object* v___x_285_; 
lean_dec_ref(v_type_265_);
v_val_283_ = lean_ctor_get(v_a_279_, 0);
lean_inc(v_val_283_);
lean_dec_ref(v_a_279_);
if (v_isShared_282_ == 0)
{
lean_ctor_set(v___x_281_, 0, v_val_283_);
v___x_285_ = v___x_281_;
goto v_reusejp_284_;
}
else
{
lean_object* v_reuseFailAlloc_286_; 
v_reuseFailAlloc_286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_286_, 0, v_val_283_);
v___x_285_ = v_reuseFailAlloc_286_;
goto v_reusejp_284_;
}
v_reusejp_284_:
{
return v___x_285_;
}
}
else
{
lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; 
lean_del_object(v___x_281_);
lean_dec(v_a_279_);
v___x_287_ = lean_obj_once(&l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1_spec__5___closed__1, &l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1_spec__5___closed__1_once, _init_l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1_spec__5___closed__1);
v___x_288_ = l_Lean_indentExpr(v_type_265_);
v___x_289_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_289_, 0, v___x_287_);
lean_ctor_set(v___x_289_, 1, v___x_288_);
v___x_290_ = l_Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1_spec__5_spec__8___redArg(v___x_289_, v___y_273_, v___y_274_, v___y_275_, v___y_276_);
return v___x_290_;
}
}
}
else
{
lean_object* v_a_292_; lean_object* v___x_294_; uint8_t v_isShared_295_; uint8_t v_isSharedCheck_299_; 
lean_dec_ref(v_type_265_);
v_a_292_ = lean_ctor_get(v___x_278_, 0);
v_isSharedCheck_299_ = !lean_is_exclusive(v___x_278_);
if (v_isSharedCheck_299_ == 0)
{
v___x_294_ = v___x_278_;
v_isShared_295_ = v_isSharedCheck_299_;
goto v_resetjp_293_;
}
else
{
lean_inc(v_a_292_);
lean_dec(v___x_278_);
v___x_294_ = lean_box(0);
v_isShared_295_ = v_isSharedCheck_299_;
goto v_resetjp_293_;
}
v_resetjp_293_:
{
lean_object* v___x_297_; 
if (v_isShared_295_ == 0)
{
v___x_297_ = v___x_294_;
goto v_reusejp_296_;
}
else
{
lean_object* v_reuseFailAlloc_298_; 
v_reuseFailAlloc_298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_298_, 0, v_a_292_);
v___x_297_ = v_reuseFailAlloc_298_;
goto v_reusejp_296_;
}
v_reusejp_296_:
{
return v___x_297_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1_spec__5___boxed(lean_object* v_type_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_, lean_object* v___y_309_, lean_object* v___y_310_, lean_object* v___y_311_, lean_object* v___y_312_){
_start:
{
lean_object* v_res_313_; 
v_res_313_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1_spec__5(v_type_300_, v___y_301_, v___y_302_, v___y_303_, v___y_304_, v___y_305_, v___y_306_, v___y_307_, v___y_308_, v___y_309_, v___y_310_, v___y_311_);
lean_dec(v___y_311_);
lean_dec_ref(v___y_310_);
lean_dec(v___y_309_);
lean_dec_ref(v___y_308_);
lean_dec(v___y_307_);
lean_dec_ref(v___y_306_);
lean_dec(v___y_305_);
lean_dec_ref(v___y_304_);
lean_dec(v___y_303_);
lean_dec(v___y_302_);
lean_dec_ref(v___y_301_);
return v_res_313_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1(lean_object* v_type_314_, lean_object* v_u_315_, lean_object* v_instDeclName_316_, lean_object* v_declName_317_, lean_object* v_expectedInst_318_, lean_object* v___y_319_, lean_object* v___y_320_, lean_object* v___y_321_, lean_object* v___y_322_, lean_object* v___y_323_, lean_object* v___y_324_, lean_object* v___y_325_, lean_object* v___y_326_, lean_object* v___y_327_, lean_object* v___y_328_, lean_object* v___y_329_){
_start:
{
lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; 
v___x_331_ = lean_box(0);
v___x_332_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_332_, 0, v_u_315_);
lean_ctor_set(v___x_332_, 1, v___x_331_);
lean_inc_ref(v___x_332_);
v___x_333_ = l_Lean_mkConst(v_instDeclName_316_, v___x_332_);
lean_inc_ref(v_type_314_);
v___x_334_ = l_Lean_Expr_app___override(v___x_333_, v_type_314_);
v___x_335_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1_spec__5(v___x_334_, v___y_319_, v___y_320_, v___y_321_, v___y_322_, v___y_323_, v___y_324_, v___y_325_, v___y_326_, v___y_327_, v___y_328_, v___y_329_);
if (lean_obj_tag(v___x_335_) == 0)
{
lean_object* v_a_336_; lean_object* v___x_337_; 
v_a_336_ = lean_ctor_get(v___x_335_, 0);
lean_inc_n(v_a_336_, 2);
lean_dec_ref(v___x_335_);
lean_inc(v_declName_317_);
v___x_337_ = l_Lean_Meta_Grind_Arith_CommRing_checkInst(v_declName_317_, v_a_336_, v_expectedInst_318_, v___y_326_, v___y_327_, v___y_328_, v___y_329_);
if (lean_obj_tag(v___x_337_) == 0)
{
lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; 
lean_dec_ref(v___x_337_);
v___x_338_ = l_Lean_mkConst(v_declName_317_, v___x_332_);
v___x_339_ = l_Lean_mkAppB(v___x_338_, v_type_314_, v_a_336_);
v___x_340_ = l_Lean_Meta_Sym_canon(v___x_339_, v___y_324_, v___y_325_, v___y_326_, v___y_327_, v___y_328_, v___y_329_);
if (lean_obj_tag(v___x_340_) == 0)
{
lean_object* v_a_341_; lean_object* v___x_342_; 
v_a_341_ = lean_ctor_get(v___x_340_, 0);
lean_inc(v_a_341_);
lean_dec_ref(v___x_340_);
v___x_342_ = l_Lean_Meta_Sym_shareCommon___redArg(v_a_341_, v___y_325_);
return v___x_342_;
}
else
{
return v___x_340_;
}
}
else
{
lean_object* v_a_343_; lean_object* v___x_345_; uint8_t v_isShared_346_; uint8_t v_isSharedCheck_350_; 
lean_dec(v_a_336_);
lean_dec_ref(v___x_332_);
lean_dec(v_declName_317_);
lean_dec_ref(v_type_314_);
v_a_343_ = lean_ctor_get(v___x_337_, 0);
v_isSharedCheck_350_ = !lean_is_exclusive(v___x_337_);
if (v_isSharedCheck_350_ == 0)
{
v___x_345_ = v___x_337_;
v_isShared_346_ = v_isSharedCheck_350_;
goto v_resetjp_344_;
}
else
{
lean_inc(v_a_343_);
lean_dec(v___x_337_);
v___x_345_ = lean_box(0);
v_isShared_346_ = v_isSharedCheck_350_;
goto v_resetjp_344_;
}
v_resetjp_344_:
{
lean_object* v___x_348_; 
if (v_isShared_346_ == 0)
{
v___x_348_ = v___x_345_;
goto v_reusejp_347_;
}
else
{
lean_object* v_reuseFailAlloc_349_; 
v_reuseFailAlloc_349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_349_, 0, v_a_343_);
v___x_348_ = v_reuseFailAlloc_349_;
goto v_reusejp_347_;
}
v_reusejp_347_:
{
return v___x_348_;
}
}
}
}
else
{
lean_dec_ref(v___x_332_);
lean_dec_ref(v_expectedInst_318_);
lean_dec(v_declName_317_);
lean_dec_ref(v_type_314_);
return v___x_335_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1___boxed(lean_object** _args){
lean_object* v_type_351_ = _args[0];
lean_object* v_u_352_ = _args[1];
lean_object* v_instDeclName_353_ = _args[2];
lean_object* v_declName_354_ = _args[3];
lean_object* v_expectedInst_355_ = _args[4];
lean_object* v___y_356_ = _args[5];
lean_object* v___y_357_ = _args[6];
lean_object* v___y_358_ = _args[7];
lean_object* v___y_359_ = _args[8];
lean_object* v___y_360_ = _args[9];
lean_object* v___y_361_ = _args[10];
lean_object* v___y_362_ = _args[11];
lean_object* v___y_363_ = _args[12];
lean_object* v___y_364_ = _args[13];
lean_object* v___y_365_ = _args[14];
lean_object* v___y_366_ = _args[15];
lean_object* v___y_367_ = _args[16];
_start:
{
lean_object* v_res_368_; 
v_res_368_ = l_Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1(v_type_351_, v_u_352_, v_instDeclName_353_, v_declName_354_, v_expectedInst_355_, v___y_356_, v___y_357_, v___y_358_, v___y_359_, v___y_360_, v___y_361_, v___y_362_, v___y_363_, v___y_364_, v___y_365_, v___y_366_);
lean_dec(v___y_366_);
lean_dec_ref(v___y_365_);
lean_dec(v___y_364_);
lean_dec_ref(v___y_363_);
lean_dec(v___y_362_);
lean_dec_ref(v___y_361_);
lean_dec(v___y_360_);
lean_dec_ref(v___y_359_);
lean_dec(v___y_358_);
lean_dec(v___y_357_);
lean_dec_ref(v___y_356_);
return v_res_368_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0(lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_){
_start:
{
lean_object* v___x_392_; 
v___x_392_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v___y_380_, v___y_381_, v___y_382_, v___y_383_, v___y_384_, v___y_385_, v___y_386_, v___y_387_, v___y_388_, v___y_389_, v___y_390_);
if (lean_obj_tag(v___x_392_) == 0)
{
lean_object* v_a_393_; lean_object* v___x_395_; uint8_t v_isShared_396_; uint8_t v_isSharedCheck_433_; 
v_a_393_ = lean_ctor_get(v___x_392_, 0);
v_isSharedCheck_433_ = !lean_is_exclusive(v___x_392_);
if (v_isSharedCheck_433_ == 0)
{
v___x_395_ = v___x_392_;
v_isShared_396_ = v_isSharedCheck_433_;
goto v_resetjp_394_;
}
else
{
lean_inc(v_a_393_);
lean_dec(v___x_392_);
v___x_395_ = lean_box(0);
v_isShared_396_ = v_isSharedCheck_433_;
goto v_resetjp_394_;
}
v_resetjp_394_:
{
lean_object* v_toRing_397_; lean_object* v_negFn_x3f_398_; 
v_toRing_397_ = lean_ctor_get(v_a_393_, 0);
lean_inc_ref(v_toRing_397_);
lean_dec(v_a_393_);
v_negFn_x3f_398_ = lean_ctor_get(v_toRing_397_, 9);
if (lean_obj_tag(v_negFn_x3f_398_) == 1)
{
lean_object* v_val_399_; lean_object* v___x_401_; 
lean_inc_ref(v_negFn_x3f_398_);
lean_dec_ref(v_toRing_397_);
v_val_399_ = lean_ctor_get(v_negFn_x3f_398_, 0);
lean_inc(v_val_399_);
lean_dec_ref(v_negFn_x3f_398_);
if (v_isShared_396_ == 0)
{
lean_ctor_set(v___x_395_, 0, v_val_399_);
v___x_401_ = v___x_395_;
goto v_reusejp_400_;
}
else
{
lean_object* v_reuseFailAlloc_402_; 
v_reuseFailAlloc_402_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_402_, 0, v_val_399_);
v___x_401_ = v_reuseFailAlloc_402_;
goto v_reusejp_400_;
}
v_reusejp_400_:
{
return v___x_401_;
}
}
else
{
lean_object* v_type_403_; lean_object* v_u_404_; lean_object* v_ringInst_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v_expectedInst_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; 
lean_del_object(v___x_395_);
v_type_403_ = lean_ctor_get(v_toRing_397_, 1);
lean_inc_ref_n(v_type_403_, 2);
v_u_404_ = lean_ctor_get(v_toRing_397_, 2);
lean_inc_n(v_u_404_, 2);
v_ringInst_405_ = lean_ctor_get(v_toRing_397_, 3);
lean_inc_ref(v_ringInst_405_);
lean_dec_ref(v_toRing_397_);
v___x_406_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0___closed__4));
v___x_407_ = lean_box(0);
v___x_408_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_408_, 0, v_u_404_);
lean_ctor_set(v___x_408_, 1, v___x_407_);
v___x_409_ = l_Lean_mkConst(v___x_406_, v___x_408_);
v_expectedInst_410_ = l_Lean_mkAppB(v___x_409_, v_type_403_, v_ringInst_405_);
v___x_411_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0___closed__5));
v___x_412_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__11));
v___x_413_ = l_Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1(v_type_403_, v_u_404_, v___x_411_, v___x_412_, v_expectedInst_410_, v___y_380_, v___y_381_, v___y_382_, v___y_383_, v___y_384_, v___y_385_, v___y_386_, v___y_387_, v___y_388_, v___y_389_, v___y_390_);
if (lean_obj_tag(v___x_413_) == 0)
{
lean_object* v_a_414_; lean_object* v___f_415_; lean_object* v___x_416_; 
v_a_414_ = lean_ctor_get(v___x_413_, 0);
lean_inc_n(v_a_414_, 2);
lean_dec_ref(v___x_413_);
v___f_415_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0___lam__0), 2, 1);
lean_closure_set(v___f_415_, 0, v_a_414_);
v___x_416_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(v___f_415_, v___y_380_, v___y_381_);
if (lean_obj_tag(v___x_416_) == 0)
{
lean_object* v___x_418_; uint8_t v_isShared_419_; uint8_t v_isSharedCheck_423_; 
v_isSharedCheck_423_ = !lean_is_exclusive(v___x_416_);
if (v_isSharedCheck_423_ == 0)
{
lean_object* v_unused_424_; 
v_unused_424_ = lean_ctor_get(v___x_416_, 0);
lean_dec(v_unused_424_);
v___x_418_ = v___x_416_;
v_isShared_419_ = v_isSharedCheck_423_;
goto v_resetjp_417_;
}
else
{
lean_dec(v___x_416_);
v___x_418_ = lean_box(0);
v_isShared_419_ = v_isSharedCheck_423_;
goto v_resetjp_417_;
}
v_resetjp_417_:
{
lean_object* v___x_421_; 
if (v_isShared_419_ == 0)
{
lean_ctor_set(v___x_418_, 0, v_a_414_);
v___x_421_ = v___x_418_;
goto v_reusejp_420_;
}
else
{
lean_object* v_reuseFailAlloc_422_; 
v_reuseFailAlloc_422_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_422_, 0, v_a_414_);
v___x_421_ = v_reuseFailAlloc_422_;
goto v_reusejp_420_;
}
v_reusejp_420_:
{
return v___x_421_;
}
}
}
else
{
lean_object* v_a_425_; lean_object* v___x_427_; uint8_t v_isShared_428_; uint8_t v_isSharedCheck_432_; 
lean_dec(v_a_414_);
v_a_425_ = lean_ctor_get(v___x_416_, 0);
v_isSharedCheck_432_ = !lean_is_exclusive(v___x_416_);
if (v_isSharedCheck_432_ == 0)
{
v___x_427_ = v___x_416_;
v_isShared_428_ = v_isSharedCheck_432_;
goto v_resetjp_426_;
}
else
{
lean_inc(v_a_425_);
lean_dec(v___x_416_);
v___x_427_ = lean_box(0);
v_isShared_428_ = v_isSharedCheck_432_;
goto v_resetjp_426_;
}
v_resetjp_426_:
{
lean_object* v___x_430_; 
if (v_isShared_428_ == 0)
{
v___x_430_ = v___x_427_;
goto v_reusejp_429_;
}
else
{
lean_object* v_reuseFailAlloc_431_; 
v_reuseFailAlloc_431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_431_, 0, v_a_425_);
v___x_430_ = v_reuseFailAlloc_431_;
goto v_reusejp_429_;
}
v_reusejp_429_:
{
return v___x_430_;
}
}
}
}
else
{
return v___x_413_;
}
}
}
}
else
{
lean_object* v_a_434_; lean_object* v___x_436_; uint8_t v_isShared_437_; uint8_t v_isSharedCheck_441_; 
v_a_434_ = lean_ctor_get(v___x_392_, 0);
v_isSharedCheck_441_ = !lean_is_exclusive(v___x_392_);
if (v_isSharedCheck_441_ == 0)
{
v___x_436_ = v___x_392_;
v_isShared_437_ = v_isSharedCheck_441_;
goto v_resetjp_435_;
}
else
{
lean_inc(v_a_434_);
lean_dec(v___x_392_);
v___x_436_ = lean_box(0);
v_isShared_437_ = v_isSharedCheck_441_;
goto v_resetjp_435_;
}
v_resetjp_435_:
{
lean_object* v___x_439_; 
if (v_isShared_437_ == 0)
{
v___x_439_ = v___x_436_;
goto v_reusejp_438_;
}
else
{
lean_object* v_reuseFailAlloc_440_; 
v_reuseFailAlloc_440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_440_, 0, v_a_434_);
v___x_439_ = v_reuseFailAlloc_440_;
goto v_reusejp_438_;
}
v_reusejp_438_:
{
return v___x_439_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0___boxed(lean_object* v___y_442_, lean_object* v___y_443_, lean_object* v___y_444_, lean_object* v___y_445_, lean_object* v___y_446_, lean_object* v___y_447_, lean_object* v___y_448_, lean_object* v___y_449_, lean_object* v___y_450_, lean_object* v___y_451_, lean_object* v___y_452_, lean_object* v___y_453_){
_start:
{
lean_object* v_res_454_; 
v_res_454_ = l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0(v___y_442_, v___y_443_, v___y_444_, v___y_445_, v___y_446_, v___y_447_, v___y_448_, v___y_449_, v___y_450_, v___y_451_, v___y_452_);
lean_dec(v___y_452_);
lean_dec_ref(v___y_451_);
lean_dec(v___y_450_);
lean_dec_ref(v___y_449_);
lean_dec(v___y_448_);
lean_dec_ref(v___y_447_);
lean_dec(v___y_446_);
lean_dec_ref(v___y_445_);
lean_dec(v___y_444_);
lean_dec(v___y_443_);
lean_dec_ref(v___y_442_);
return v_res_454_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0(lean_object* v_inst_455_, lean_object* v___y_456_, lean_object* v___y_457_, lean_object* v___y_458_, lean_object* v___y_459_, lean_object* v___y_460_, lean_object* v___y_461_, lean_object* v___y_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_){
_start:
{
lean_object* v___x_468_; 
v___x_468_ = l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0(v___y_456_, v___y_457_, v___y_458_, v___y_459_, v___y_460_, v___y_461_, v___y_462_, v___y_463_, v___y_464_, v___y_465_, v___y_466_);
if (lean_obj_tag(v___x_468_) == 0)
{
lean_object* v_a_469_; lean_object* v___x_471_; uint8_t v_isShared_472_; uint8_t v_isSharedCheck_479_; 
v_a_469_ = lean_ctor_get(v___x_468_, 0);
v_isSharedCheck_479_ = !lean_is_exclusive(v___x_468_);
if (v_isSharedCheck_479_ == 0)
{
v___x_471_ = v___x_468_;
v_isShared_472_ = v_isSharedCheck_479_;
goto v_resetjp_470_;
}
else
{
lean_inc(v_a_469_);
lean_dec(v___x_468_);
v___x_471_ = lean_box(0);
v_isShared_472_ = v_isSharedCheck_479_;
goto v_resetjp_470_;
}
v_resetjp_470_:
{
lean_object* v___x_473_; uint8_t v___x_474_; lean_object* v___x_475_; lean_object* v___x_477_; 
v___x_473_ = l_Lean_Expr_appArg_x21(v_a_469_);
lean_dec(v_a_469_);
v___x_474_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v___x_473_, v_inst_455_);
lean_dec_ref(v___x_473_);
v___x_475_ = lean_box(v___x_474_);
if (v_isShared_472_ == 0)
{
lean_ctor_set(v___x_471_, 0, v___x_475_);
v___x_477_ = v___x_471_;
goto v_reusejp_476_;
}
else
{
lean_object* v_reuseFailAlloc_478_; 
v_reuseFailAlloc_478_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_478_, 0, v___x_475_);
v___x_477_ = v_reuseFailAlloc_478_;
goto v_reusejp_476_;
}
v_reusejp_476_:
{
return v___x_477_;
}
}
}
else
{
lean_object* v_a_480_; lean_object* v___x_482_; uint8_t v_isShared_483_; uint8_t v_isSharedCheck_487_; 
v_a_480_ = lean_ctor_get(v___x_468_, 0);
v_isSharedCheck_487_ = !lean_is_exclusive(v___x_468_);
if (v_isSharedCheck_487_ == 0)
{
v___x_482_ = v___x_468_;
v_isShared_483_ = v_isSharedCheck_487_;
goto v_resetjp_481_;
}
else
{
lean_inc(v_a_480_);
lean_dec(v___x_468_);
v___x_482_ = lean_box(0);
v_isShared_483_ = v_isSharedCheck_487_;
goto v_resetjp_481_;
}
v_resetjp_481_:
{
lean_object* v___x_485_; 
if (v_isShared_483_ == 0)
{
v___x_485_ = v___x_482_;
goto v_reusejp_484_;
}
else
{
lean_object* v_reuseFailAlloc_486_; 
v_reuseFailAlloc_486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_486_, 0, v_a_480_);
v___x_485_ = v_reuseFailAlloc_486_;
goto v_reusejp_484_;
}
v_reusejp_484_:
{
return v___x_485_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0___boxed(lean_object* v_inst_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_, lean_object* v___y_493_, lean_object* v___y_494_, lean_object* v___y_495_, lean_object* v___y_496_, lean_object* v___y_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_){
_start:
{
lean_object* v_res_501_; 
v_res_501_ = l_Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0(v_inst_488_, v___y_489_, v___y_490_, v___y_491_, v___y_492_, v___y_493_, v___y_494_, v___y_495_, v___y_496_, v___y_497_, v___y_498_, v___y_499_);
lean_dec(v___y_499_);
lean_dec_ref(v___y_498_);
lean_dec(v___y_497_);
lean_dec_ref(v___y_496_);
lean_dec(v___y_495_);
lean_dec_ref(v___y_494_);
lean_dec(v___y_493_);
lean_dec_ref(v___y_492_);
lean_dec(v___y_491_);
lean_dec(v___y_490_);
lean_dec_ref(v___y_489_);
lean_dec_ref(v_inst_488_);
return v_res_501_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isIntCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__1_spec__2___lam__0(lean_object* v_a_502_, lean_object* v_s_503_){
_start:
{
lean_object* v_toRing_504_; lean_object* v_invFn_x3f_505_; lean_object* v_semiringId_x3f_506_; lean_object* v_commSemiringInst_507_; lean_object* v_commRingInst_508_; lean_object* v_noZeroDivInst_x3f_509_; lean_object* v_fieldInst_x3f_510_; lean_object* v_powIdentityInst_x3f_511_; lean_object* v_denoteEntries_512_; lean_object* v_nextId_513_; lean_object* v_steps_514_; lean_object* v_queue_515_; lean_object* v_basis_516_; lean_object* v_diseqs_517_; uint8_t v_recheck_518_; lean_object* v_invSet_519_; lean_object* v_powIdentityVarCount_520_; lean_object* v_numEq0_x3f_521_; uint8_t v_numEq0Updated_522_; lean_object* v___x_524_; uint8_t v_isShared_525_; uint8_t v_isSharedCheck_554_; 
v_toRing_504_ = lean_ctor_get(v_s_503_, 0);
v_invFn_x3f_505_ = lean_ctor_get(v_s_503_, 1);
v_semiringId_x3f_506_ = lean_ctor_get(v_s_503_, 2);
v_commSemiringInst_507_ = lean_ctor_get(v_s_503_, 3);
v_commRingInst_508_ = lean_ctor_get(v_s_503_, 4);
v_noZeroDivInst_x3f_509_ = lean_ctor_get(v_s_503_, 5);
v_fieldInst_x3f_510_ = lean_ctor_get(v_s_503_, 6);
v_powIdentityInst_x3f_511_ = lean_ctor_get(v_s_503_, 7);
v_denoteEntries_512_ = lean_ctor_get(v_s_503_, 8);
v_nextId_513_ = lean_ctor_get(v_s_503_, 9);
v_steps_514_ = lean_ctor_get(v_s_503_, 10);
v_queue_515_ = lean_ctor_get(v_s_503_, 11);
v_basis_516_ = lean_ctor_get(v_s_503_, 12);
v_diseqs_517_ = lean_ctor_get(v_s_503_, 13);
v_recheck_518_ = lean_ctor_get_uint8(v_s_503_, sizeof(void*)*17);
v_invSet_519_ = lean_ctor_get(v_s_503_, 14);
v_powIdentityVarCount_520_ = lean_ctor_get(v_s_503_, 15);
v_numEq0_x3f_521_ = lean_ctor_get(v_s_503_, 16);
v_numEq0Updated_522_ = lean_ctor_get_uint8(v_s_503_, sizeof(void*)*17 + 1);
v_isSharedCheck_554_ = !lean_is_exclusive(v_s_503_);
if (v_isSharedCheck_554_ == 0)
{
v___x_524_ = v_s_503_;
v_isShared_525_ = v_isSharedCheck_554_;
goto v_resetjp_523_;
}
else
{
lean_inc(v_numEq0_x3f_521_);
lean_inc(v_powIdentityVarCount_520_);
lean_inc(v_invSet_519_);
lean_inc(v_diseqs_517_);
lean_inc(v_basis_516_);
lean_inc(v_queue_515_);
lean_inc(v_steps_514_);
lean_inc(v_nextId_513_);
lean_inc(v_denoteEntries_512_);
lean_inc(v_powIdentityInst_x3f_511_);
lean_inc(v_fieldInst_x3f_510_);
lean_inc(v_noZeroDivInst_x3f_509_);
lean_inc(v_commRingInst_508_);
lean_inc(v_commSemiringInst_507_);
lean_inc(v_semiringId_x3f_506_);
lean_inc(v_invFn_x3f_505_);
lean_inc(v_toRing_504_);
lean_dec(v_s_503_);
v___x_524_ = lean_box(0);
v_isShared_525_ = v_isSharedCheck_554_;
goto v_resetjp_523_;
}
v_resetjp_523_:
{
lean_object* v_id_526_; lean_object* v_type_527_; lean_object* v_u_528_; lean_object* v_ringInst_529_; lean_object* v_semiringInst_530_; lean_object* v_charInst_x3f_531_; lean_object* v_addFn_x3f_532_; lean_object* v_mulFn_x3f_533_; lean_object* v_subFn_x3f_534_; lean_object* v_negFn_x3f_535_; lean_object* v_powFn_x3f_536_; lean_object* v_natCastFn_x3f_537_; lean_object* v_one_x3f_538_; lean_object* v_vars_539_; lean_object* v_varMap_540_; lean_object* v_denote_541_; lean_object* v___x_543_; uint8_t v_isShared_544_; uint8_t v_isSharedCheck_552_; 
v_id_526_ = lean_ctor_get(v_toRing_504_, 0);
v_type_527_ = lean_ctor_get(v_toRing_504_, 1);
v_u_528_ = lean_ctor_get(v_toRing_504_, 2);
v_ringInst_529_ = lean_ctor_get(v_toRing_504_, 3);
v_semiringInst_530_ = lean_ctor_get(v_toRing_504_, 4);
v_charInst_x3f_531_ = lean_ctor_get(v_toRing_504_, 5);
v_addFn_x3f_532_ = lean_ctor_get(v_toRing_504_, 6);
v_mulFn_x3f_533_ = lean_ctor_get(v_toRing_504_, 7);
v_subFn_x3f_534_ = lean_ctor_get(v_toRing_504_, 8);
v_negFn_x3f_535_ = lean_ctor_get(v_toRing_504_, 9);
v_powFn_x3f_536_ = lean_ctor_get(v_toRing_504_, 10);
v_natCastFn_x3f_537_ = lean_ctor_get(v_toRing_504_, 12);
v_one_x3f_538_ = lean_ctor_get(v_toRing_504_, 13);
v_vars_539_ = lean_ctor_get(v_toRing_504_, 14);
v_varMap_540_ = lean_ctor_get(v_toRing_504_, 15);
v_denote_541_ = lean_ctor_get(v_toRing_504_, 16);
v_isSharedCheck_552_ = !lean_is_exclusive(v_toRing_504_);
if (v_isSharedCheck_552_ == 0)
{
lean_object* v_unused_553_; 
v_unused_553_ = lean_ctor_get(v_toRing_504_, 11);
lean_dec(v_unused_553_);
v___x_543_ = v_toRing_504_;
v_isShared_544_ = v_isSharedCheck_552_;
goto v_resetjp_542_;
}
else
{
lean_inc(v_denote_541_);
lean_inc(v_varMap_540_);
lean_inc(v_vars_539_);
lean_inc(v_one_x3f_538_);
lean_inc(v_natCastFn_x3f_537_);
lean_inc(v_powFn_x3f_536_);
lean_inc(v_negFn_x3f_535_);
lean_inc(v_subFn_x3f_534_);
lean_inc(v_mulFn_x3f_533_);
lean_inc(v_addFn_x3f_532_);
lean_inc(v_charInst_x3f_531_);
lean_inc(v_semiringInst_530_);
lean_inc(v_ringInst_529_);
lean_inc(v_u_528_);
lean_inc(v_type_527_);
lean_inc(v_id_526_);
lean_dec(v_toRing_504_);
v___x_543_ = lean_box(0);
v_isShared_544_ = v_isSharedCheck_552_;
goto v_resetjp_542_;
}
v_resetjp_542_:
{
lean_object* v___x_545_; lean_object* v___x_547_; 
v___x_545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_545_, 0, v_a_502_);
if (v_isShared_544_ == 0)
{
lean_ctor_set(v___x_543_, 11, v___x_545_);
v___x_547_ = v___x_543_;
goto v_reusejp_546_;
}
else
{
lean_object* v_reuseFailAlloc_551_; 
v_reuseFailAlloc_551_ = lean_alloc_ctor(0, 17, 0);
lean_ctor_set(v_reuseFailAlloc_551_, 0, v_id_526_);
lean_ctor_set(v_reuseFailAlloc_551_, 1, v_type_527_);
lean_ctor_set(v_reuseFailAlloc_551_, 2, v_u_528_);
lean_ctor_set(v_reuseFailAlloc_551_, 3, v_ringInst_529_);
lean_ctor_set(v_reuseFailAlloc_551_, 4, v_semiringInst_530_);
lean_ctor_set(v_reuseFailAlloc_551_, 5, v_charInst_x3f_531_);
lean_ctor_set(v_reuseFailAlloc_551_, 6, v_addFn_x3f_532_);
lean_ctor_set(v_reuseFailAlloc_551_, 7, v_mulFn_x3f_533_);
lean_ctor_set(v_reuseFailAlloc_551_, 8, v_subFn_x3f_534_);
lean_ctor_set(v_reuseFailAlloc_551_, 9, v_negFn_x3f_535_);
lean_ctor_set(v_reuseFailAlloc_551_, 10, v_powFn_x3f_536_);
lean_ctor_set(v_reuseFailAlloc_551_, 11, v___x_545_);
lean_ctor_set(v_reuseFailAlloc_551_, 12, v_natCastFn_x3f_537_);
lean_ctor_set(v_reuseFailAlloc_551_, 13, v_one_x3f_538_);
lean_ctor_set(v_reuseFailAlloc_551_, 14, v_vars_539_);
lean_ctor_set(v_reuseFailAlloc_551_, 15, v_varMap_540_);
lean_ctor_set(v_reuseFailAlloc_551_, 16, v_denote_541_);
v___x_547_ = v_reuseFailAlloc_551_;
goto v_reusejp_546_;
}
v_reusejp_546_:
{
lean_object* v___x_549_; 
if (v_isShared_525_ == 0)
{
lean_ctor_set(v___x_524_, 0, v___x_547_);
v___x_549_ = v___x_524_;
goto v_reusejp_548_;
}
else
{
lean_object* v_reuseFailAlloc_550_; 
v_reuseFailAlloc_550_ = lean_alloc_ctor(0, 17, 2);
lean_ctor_set(v_reuseFailAlloc_550_, 0, v___x_547_);
lean_ctor_set(v_reuseFailAlloc_550_, 1, v_invFn_x3f_505_);
lean_ctor_set(v_reuseFailAlloc_550_, 2, v_semiringId_x3f_506_);
lean_ctor_set(v_reuseFailAlloc_550_, 3, v_commSemiringInst_507_);
lean_ctor_set(v_reuseFailAlloc_550_, 4, v_commRingInst_508_);
lean_ctor_set(v_reuseFailAlloc_550_, 5, v_noZeroDivInst_x3f_509_);
lean_ctor_set(v_reuseFailAlloc_550_, 6, v_fieldInst_x3f_510_);
lean_ctor_set(v_reuseFailAlloc_550_, 7, v_powIdentityInst_x3f_511_);
lean_ctor_set(v_reuseFailAlloc_550_, 8, v_denoteEntries_512_);
lean_ctor_set(v_reuseFailAlloc_550_, 9, v_nextId_513_);
lean_ctor_set(v_reuseFailAlloc_550_, 10, v_steps_514_);
lean_ctor_set(v_reuseFailAlloc_550_, 11, v_queue_515_);
lean_ctor_set(v_reuseFailAlloc_550_, 12, v_basis_516_);
lean_ctor_set(v_reuseFailAlloc_550_, 13, v_diseqs_517_);
lean_ctor_set(v_reuseFailAlloc_550_, 14, v_invSet_519_);
lean_ctor_set(v_reuseFailAlloc_550_, 15, v_powIdentityVarCount_520_);
lean_ctor_set(v_reuseFailAlloc_550_, 16, v_numEq0_x3f_521_);
lean_ctor_set_uint8(v_reuseFailAlloc_550_, sizeof(void*)*17, v_recheck_518_);
lean_ctor_set_uint8(v_reuseFailAlloc_550_, sizeof(void*)*17 + 1, v_numEq0Updated_522_);
v___x_549_ = v_reuseFailAlloc_550_;
goto v_reusejp_548_;
}
v_reusejp_548_:
{
return v___x_549_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isIntCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__1_spec__2(lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_){
_start:
{
lean_object* v___y_579_; lean_object* v___y_580_; lean_object* v___y_581_; lean_object* v___x_601_; 
v___x_601_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v___y_566_, v___y_567_, v___y_568_, v___y_569_, v___y_570_, v___y_571_, v___y_572_, v___y_573_, v___y_574_, v___y_575_, v___y_576_);
if (lean_obj_tag(v___x_601_) == 0)
{
lean_object* v_a_602_; lean_object* v___x_604_; uint8_t v_isShared_605_; uint8_t v_isSharedCheck_660_; 
v_a_602_ = lean_ctor_get(v___x_601_, 0);
v_isSharedCheck_660_ = !lean_is_exclusive(v___x_601_);
if (v_isSharedCheck_660_ == 0)
{
v___x_604_ = v___x_601_;
v_isShared_605_ = v_isSharedCheck_660_;
goto v_resetjp_603_;
}
else
{
lean_inc(v_a_602_);
lean_dec(v___x_601_);
v___x_604_ = lean_box(0);
v_isShared_605_ = v_isSharedCheck_660_;
goto v_resetjp_603_;
}
v_resetjp_603_:
{
lean_object* v_toRing_606_; lean_object* v_intCastFn_x3f_607_; 
v_toRing_606_ = lean_ctor_get(v_a_602_, 0);
lean_inc_ref(v_toRing_606_);
lean_dec(v_a_602_);
v_intCastFn_x3f_607_ = lean_ctor_get(v_toRing_606_, 11);
if (lean_obj_tag(v_intCastFn_x3f_607_) == 1)
{
lean_object* v_val_608_; lean_object* v___x_610_; 
lean_inc_ref(v_intCastFn_x3f_607_);
lean_dec_ref(v_toRing_606_);
v_val_608_ = lean_ctor_get(v_intCastFn_x3f_607_, 0);
lean_inc(v_val_608_);
lean_dec_ref(v_intCastFn_x3f_607_);
if (v_isShared_605_ == 0)
{
lean_ctor_set(v___x_604_, 0, v_val_608_);
v___x_610_ = v___x_604_;
goto v_reusejp_609_;
}
else
{
lean_object* v_reuseFailAlloc_611_; 
v_reuseFailAlloc_611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_611_, 0, v_val_608_);
v___x_610_ = v_reuseFailAlloc_611_;
goto v_reusejp_609_;
}
v_reusejp_609_:
{
return v___x_610_;
}
}
else
{
lean_object* v_type_612_; lean_object* v_u_613_; lean_object* v_ringInst_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v_inst_x27_619_; lean_object* v_inst_621_; lean_object* v___y_622_; lean_object* v___y_623_; lean_object* v___y_624_; lean_object* v___y_625_; lean_object* v___y_626_; lean_object* v___y_627_; lean_object* v___y_628_; lean_object* v___y_629_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v_instType_638_; lean_object* v___x_639_; 
lean_del_object(v___x_604_);
v_type_612_ = lean_ctor_get(v_toRing_606_, 1);
lean_inc_ref_n(v_type_612_, 3);
v_u_613_ = lean_ctor_get(v_toRing_606_, 2);
lean_inc(v_u_613_);
v_ringInst_614_ = lean_ctor_get(v_toRing_606_, 3);
lean_inc_ref(v_ringInst_614_);
lean_dec_ref(v_toRing_606_);
v___x_615_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isIntCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__1_spec__2___closed__0));
v___x_616_ = lean_box(0);
v___x_617_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_617_, 0, v_u_613_);
lean_ctor_set(v___x_617_, 1, v___x_616_);
lean_inc_ref_n(v___x_617_, 2);
v___x_618_ = l_Lean_mkConst(v___x_615_, v___x_617_);
v_inst_x27_619_ = l_Lean_mkAppB(v___x_618_, v_type_612_, v_ringInst_614_);
v___x_636_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isIntCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__1_spec__2___closed__1));
v___x_637_ = l_Lean_mkConst(v___x_636_, v___x_617_);
v_instType_638_ = l_Lean_Expr_app___override(v___x_637_, v_type_612_);
v___x_639_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f(v_instType_638_, v___y_573_, v___y_574_, v___y_575_, v___y_576_);
if (lean_obj_tag(v___x_639_) == 0)
{
lean_object* v_a_640_; 
v_a_640_ = lean_ctor_get(v___x_639_, 0);
lean_inc(v_a_640_);
lean_dec_ref(v___x_639_);
if (lean_obj_tag(v_a_640_) == 0)
{
v_inst_621_ = v_inst_x27_619_;
v___y_622_ = v___y_566_;
v___y_623_ = v___y_567_;
v___y_624_ = v___y_571_;
v___y_625_ = v___y_572_;
v___y_626_ = v___y_573_;
v___y_627_ = v___y_574_;
v___y_628_ = v___y_575_;
v___y_629_ = v___y_576_;
goto v___jp_620_;
}
else
{
lean_object* v_val_641_; lean_object* v___x_642_; lean_object* v___x_643_; 
v_val_641_ = lean_ctor_get(v_a_640_, 0);
lean_inc_n(v_val_641_, 2);
lean_dec_ref(v_a_640_);
v___x_642_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isIntCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__1_spec__2___closed__3));
v___x_643_ = l_Lean_Meta_Grind_Arith_CommRing_checkInst(v___x_642_, v_val_641_, v_inst_x27_619_, v___y_573_, v___y_574_, v___y_575_, v___y_576_);
if (lean_obj_tag(v___x_643_) == 0)
{
lean_dec_ref(v___x_643_);
v_inst_621_ = v_val_641_;
v___y_622_ = v___y_566_;
v___y_623_ = v___y_567_;
v___y_624_ = v___y_571_;
v___y_625_ = v___y_572_;
v___y_626_ = v___y_573_;
v___y_627_ = v___y_574_;
v___y_628_ = v___y_575_;
v___y_629_ = v___y_576_;
goto v___jp_620_;
}
else
{
lean_object* v_a_644_; lean_object* v___x_646_; uint8_t v_isShared_647_; uint8_t v_isSharedCheck_651_; 
lean_dec(v_val_641_);
lean_dec_ref(v___x_617_);
lean_dec_ref(v_type_612_);
v_a_644_ = lean_ctor_get(v___x_643_, 0);
v_isSharedCheck_651_ = !lean_is_exclusive(v___x_643_);
if (v_isSharedCheck_651_ == 0)
{
v___x_646_ = v___x_643_;
v_isShared_647_ = v_isSharedCheck_651_;
goto v_resetjp_645_;
}
else
{
lean_inc(v_a_644_);
lean_dec(v___x_643_);
v___x_646_ = lean_box(0);
v_isShared_647_ = v_isSharedCheck_651_;
goto v_resetjp_645_;
}
v_resetjp_645_:
{
lean_object* v___x_649_; 
if (v_isShared_647_ == 0)
{
v___x_649_ = v___x_646_;
goto v_reusejp_648_;
}
else
{
lean_object* v_reuseFailAlloc_650_; 
v_reuseFailAlloc_650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_650_, 0, v_a_644_);
v___x_649_ = v_reuseFailAlloc_650_;
goto v_reusejp_648_;
}
v_reusejp_648_:
{
return v___x_649_;
}
}
}
}
}
else
{
lean_object* v_a_652_; lean_object* v___x_654_; uint8_t v_isShared_655_; uint8_t v_isSharedCheck_659_; 
lean_dec_ref(v_inst_x27_619_);
lean_dec_ref(v___x_617_);
lean_dec_ref(v_type_612_);
v_a_652_ = lean_ctor_get(v___x_639_, 0);
v_isSharedCheck_659_ = !lean_is_exclusive(v___x_639_);
if (v_isSharedCheck_659_ == 0)
{
v___x_654_ = v___x_639_;
v_isShared_655_ = v_isSharedCheck_659_;
goto v_resetjp_653_;
}
else
{
lean_inc(v_a_652_);
lean_dec(v___x_639_);
v___x_654_ = lean_box(0);
v_isShared_655_ = v_isSharedCheck_659_;
goto v_resetjp_653_;
}
v_resetjp_653_:
{
lean_object* v___x_657_; 
if (v_isShared_655_ == 0)
{
v___x_657_ = v___x_654_;
goto v_reusejp_656_;
}
else
{
lean_object* v_reuseFailAlloc_658_; 
v_reuseFailAlloc_658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_658_, 0, v_a_652_);
v___x_657_ = v_reuseFailAlloc_658_;
goto v_reusejp_656_;
}
v_reusejp_656_:
{
return v___x_657_;
}
}
}
v___jp_620_:
{
lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; 
v___x_630_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__2));
v___x_631_ = l_Lean_mkConst(v___x_630_, v___x_617_);
v___x_632_ = l_Lean_mkAppB(v___x_631_, v_type_612_, v_inst_621_);
v___x_633_ = l_Lean_Meta_Sym_canon(v___x_632_, v___y_624_, v___y_625_, v___y_626_, v___y_627_, v___y_628_, v___y_629_);
if (lean_obj_tag(v___x_633_) == 0)
{
lean_object* v_a_634_; lean_object* v___x_635_; 
v_a_634_ = lean_ctor_get(v___x_633_, 0);
lean_inc(v_a_634_);
lean_dec_ref(v___x_633_);
v___x_635_ = l_Lean_Meta_Sym_shareCommon___redArg(v_a_634_, v___y_625_);
v___y_579_ = v___y_623_;
v___y_580_ = v___y_622_;
v___y_581_ = v___x_635_;
goto v___jp_578_;
}
else
{
v___y_579_ = v___y_623_;
v___y_580_ = v___y_622_;
v___y_581_ = v___x_633_;
goto v___jp_578_;
}
}
}
}
}
else
{
lean_object* v_a_661_; lean_object* v___x_663_; uint8_t v_isShared_664_; uint8_t v_isSharedCheck_668_; 
v_a_661_ = lean_ctor_get(v___x_601_, 0);
v_isSharedCheck_668_ = !lean_is_exclusive(v___x_601_);
if (v_isSharedCheck_668_ == 0)
{
v___x_663_ = v___x_601_;
v_isShared_664_ = v_isSharedCheck_668_;
goto v_resetjp_662_;
}
else
{
lean_inc(v_a_661_);
lean_dec(v___x_601_);
v___x_663_ = lean_box(0);
v_isShared_664_ = v_isSharedCheck_668_;
goto v_resetjp_662_;
}
v_resetjp_662_:
{
lean_object* v___x_666_; 
if (v_isShared_664_ == 0)
{
v___x_666_ = v___x_663_;
goto v_reusejp_665_;
}
else
{
lean_object* v_reuseFailAlloc_667_; 
v_reuseFailAlloc_667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_667_, 0, v_a_661_);
v___x_666_ = v_reuseFailAlloc_667_;
goto v_reusejp_665_;
}
v_reusejp_665_:
{
return v___x_666_;
}
}
}
v___jp_578_:
{
if (lean_obj_tag(v___y_581_) == 0)
{
lean_object* v_a_582_; lean_object* v___f_583_; lean_object* v___x_584_; 
v_a_582_ = lean_ctor_get(v___y_581_, 0);
lean_inc_n(v_a_582_, 2);
lean_dec_ref(v___y_581_);
v___f_583_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isIntCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__1_spec__2___lam__0), 2, 1);
lean_closure_set(v___f_583_, 0, v_a_582_);
v___x_584_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(v___f_583_, v___y_580_, v___y_579_);
if (lean_obj_tag(v___x_584_) == 0)
{
lean_object* v___x_586_; uint8_t v_isShared_587_; uint8_t v_isSharedCheck_591_; 
v_isSharedCheck_591_ = !lean_is_exclusive(v___x_584_);
if (v_isSharedCheck_591_ == 0)
{
lean_object* v_unused_592_; 
v_unused_592_ = lean_ctor_get(v___x_584_, 0);
lean_dec(v_unused_592_);
v___x_586_ = v___x_584_;
v_isShared_587_ = v_isSharedCheck_591_;
goto v_resetjp_585_;
}
else
{
lean_dec(v___x_584_);
v___x_586_ = lean_box(0);
v_isShared_587_ = v_isSharedCheck_591_;
goto v_resetjp_585_;
}
v_resetjp_585_:
{
lean_object* v___x_589_; 
if (v_isShared_587_ == 0)
{
lean_ctor_set(v___x_586_, 0, v_a_582_);
v___x_589_ = v___x_586_;
goto v_reusejp_588_;
}
else
{
lean_object* v_reuseFailAlloc_590_; 
v_reuseFailAlloc_590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_590_, 0, v_a_582_);
v___x_589_ = v_reuseFailAlloc_590_;
goto v_reusejp_588_;
}
v_reusejp_588_:
{
return v___x_589_;
}
}
}
else
{
lean_object* v_a_593_; lean_object* v___x_595_; uint8_t v_isShared_596_; uint8_t v_isSharedCheck_600_; 
lean_dec(v_a_582_);
v_a_593_ = lean_ctor_get(v___x_584_, 0);
v_isSharedCheck_600_ = !lean_is_exclusive(v___x_584_);
if (v_isSharedCheck_600_ == 0)
{
v___x_595_ = v___x_584_;
v_isShared_596_ = v_isSharedCheck_600_;
goto v_resetjp_594_;
}
else
{
lean_inc(v_a_593_);
lean_dec(v___x_584_);
v___x_595_ = lean_box(0);
v_isShared_596_ = v_isSharedCheck_600_;
goto v_resetjp_594_;
}
v_resetjp_594_:
{
lean_object* v___x_598_; 
if (v_isShared_596_ == 0)
{
v___x_598_ = v___x_595_;
goto v_reusejp_597_;
}
else
{
lean_object* v_reuseFailAlloc_599_; 
v_reuseFailAlloc_599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_599_, 0, v_a_593_);
v___x_598_ = v_reuseFailAlloc_599_;
goto v_reusejp_597_;
}
v_reusejp_597_:
{
return v___x_598_;
}
}
}
}
else
{
return v___y_581_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isIntCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__1_spec__2___boxed(lean_object* v___y_669_, lean_object* v___y_670_, lean_object* v___y_671_, lean_object* v___y_672_, lean_object* v___y_673_, lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_, lean_object* v___y_677_, lean_object* v___y_678_, lean_object* v___y_679_, lean_object* v___y_680_){
_start:
{
lean_object* v_res_681_; 
v_res_681_ = l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isIntCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__1_spec__2(v___y_669_, v___y_670_, v___y_671_, v___y_672_, v___y_673_, v___y_674_, v___y_675_, v___y_676_, v___y_677_, v___y_678_, v___y_679_);
lean_dec(v___y_679_);
lean_dec_ref(v___y_678_);
lean_dec(v___y_677_);
lean_dec_ref(v___y_676_);
lean_dec(v___y_675_);
lean_dec_ref(v___y_674_);
lean_dec(v___y_673_);
lean_dec_ref(v___y_672_);
lean_dec(v___y_671_);
lean_dec(v___y_670_);
lean_dec_ref(v___y_669_);
return v_res_681_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_isIntCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__1(lean_object* v_inst_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_, lean_object* v___y_688_, lean_object* v___y_689_, lean_object* v___y_690_, lean_object* v___y_691_, lean_object* v___y_692_, lean_object* v___y_693_){
_start:
{
lean_object* v___x_695_; 
v___x_695_ = l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isIntCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__1_spec__2(v___y_683_, v___y_684_, v___y_685_, v___y_686_, v___y_687_, v___y_688_, v___y_689_, v___y_690_, v___y_691_, v___y_692_, v___y_693_);
if (lean_obj_tag(v___x_695_) == 0)
{
lean_object* v_a_696_; lean_object* v___x_698_; uint8_t v_isShared_699_; uint8_t v_isSharedCheck_706_; 
v_a_696_ = lean_ctor_get(v___x_695_, 0);
v_isSharedCheck_706_ = !lean_is_exclusive(v___x_695_);
if (v_isSharedCheck_706_ == 0)
{
v___x_698_ = v___x_695_;
v_isShared_699_ = v_isSharedCheck_706_;
goto v_resetjp_697_;
}
else
{
lean_inc(v_a_696_);
lean_dec(v___x_695_);
v___x_698_ = lean_box(0);
v_isShared_699_ = v_isSharedCheck_706_;
goto v_resetjp_697_;
}
v_resetjp_697_:
{
lean_object* v___x_700_; uint8_t v___x_701_; lean_object* v___x_702_; lean_object* v___x_704_; 
v___x_700_ = l_Lean_Expr_appArg_x21(v_a_696_);
lean_dec(v_a_696_);
v___x_701_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v___x_700_, v_inst_682_);
lean_dec_ref(v___x_700_);
v___x_702_ = lean_box(v___x_701_);
if (v_isShared_699_ == 0)
{
lean_ctor_set(v___x_698_, 0, v___x_702_);
v___x_704_ = v___x_698_;
goto v_reusejp_703_;
}
else
{
lean_object* v_reuseFailAlloc_705_; 
v_reuseFailAlloc_705_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_705_, 0, v___x_702_);
v___x_704_ = v_reuseFailAlloc_705_;
goto v_reusejp_703_;
}
v_reusejp_703_:
{
return v___x_704_;
}
}
}
else
{
lean_object* v_a_707_; lean_object* v___x_709_; uint8_t v_isShared_710_; uint8_t v_isSharedCheck_714_; 
v_a_707_ = lean_ctor_get(v___x_695_, 0);
v_isSharedCheck_714_ = !lean_is_exclusive(v___x_695_);
if (v_isSharedCheck_714_ == 0)
{
v___x_709_ = v___x_695_;
v_isShared_710_ = v_isSharedCheck_714_;
goto v_resetjp_708_;
}
else
{
lean_inc(v_a_707_);
lean_dec(v___x_695_);
v___x_709_ = lean_box(0);
v_isShared_710_ = v_isSharedCheck_714_;
goto v_resetjp_708_;
}
v_resetjp_708_:
{
lean_object* v___x_712_; 
if (v_isShared_710_ == 0)
{
v___x_712_ = v___x_709_;
goto v_reusejp_711_;
}
else
{
lean_object* v_reuseFailAlloc_713_; 
v_reuseFailAlloc_713_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_713_, 0, v_a_707_);
v___x_712_ = v_reuseFailAlloc_713_;
goto v_reusejp_711_;
}
v_reusejp_711_:
{
return v___x_712_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_isIntCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__1___boxed(lean_object* v_inst_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_, lean_object* v___y_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_, lean_object* v___y_724_, lean_object* v___y_725_, lean_object* v___y_726_, lean_object* v___y_727_){
_start:
{
lean_object* v_res_728_; 
v_res_728_ = l_Lean_Meta_Grind_Arith_CommRing_isIntCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__1(v_inst_715_, v___y_716_, v___y_717_, v___y_718_, v___y_719_, v___y_720_, v___y_721_, v___y_722_, v___y_723_, v___y_724_, v___y_725_, v___y_726_);
lean_dec(v___y_726_);
lean_dec_ref(v___y_725_);
lean_dec(v___y_724_);
lean_dec_ref(v___y_723_);
lean_dec(v___y_722_);
lean_dec_ref(v___y_721_);
lean_dec(v___y_720_);
lean_dec_ref(v___y_719_);
lean_dec(v___y_718_);
lean_dec(v___y_717_);
lean_dec_ref(v___y_716_);
lean_dec_ref(v_inst_715_);
return v_res_728_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isNatCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__2_spec__4___lam__0(lean_object* v_a_729_, lean_object* v_s_730_){
_start:
{
lean_object* v_toRing_731_; lean_object* v_invFn_x3f_732_; lean_object* v_semiringId_x3f_733_; lean_object* v_commSemiringInst_734_; lean_object* v_commRingInst_735_; lean_object* v_noZeroDivInst_x3f_736_; lean_object* v_fieldInst_x3f_737_; lean_object* v_powIdentityInst_x3f_738_; lean_object* v_denoteEntries_739_; lean_object* v_nextId_740_; lean_object* v_steps_741_; lean_object* v_queue_742_; lean_object* v_basis_743_; lean_object* v_diseqs_744_; uint8_t v_recheck_745_; lean_object* v_invSet_746_; lean_object* v_powIdentityVarCount_747_; lean_object* v_numEq0_x3f_748_; uint8_t v_numEq0Updated_749_; lean_object* v___x_751_; uint8_t v_isShared_752_; uint8_t v_isSharedCheck_781_; 
v_toRing_731_ = lean_ctor_get(v_s_730_, 0);
v_invFn_x3f_732_ = lean_ctor_get(v_s_730_, 1);
v_semiringId_x3f_733_ = lean_ctor_get(v_s_730_, 2);
v_commSemiringInst_734_ = lean_ctor_get(v_s_730_, 3);
v_commRingInst_735_ = lean_ctor_get(v_s_730_, 4);
v_noZeroDivInst_x3f_736_ = lean_ctor_get(v_s_730_, 5);
v_fieldInst_x3f_737_ = lean_ctor_get(v_s_730_, 6);
v_powIdentityInst_x3f_738_ = lean_ctor_get(v_s_730_, 7);
v_denoteEntries_739_ = lean_ctor_get(v_s_730_, 8);
v_nextId_740_ = lean_ctor_get(v_s_730_, 9);
v_steps_741_ = lean_ctor_get(v_s_730_, 10);
v_queue_742_ = lean_ctor_get(v_s_730_, 11);
v_basis_743_ = lean_ctor_get(v_s_730_, 12);
v_diseqs_744_ = lean_ctor_get(v_s_730_, 13);
v_recheck_745_ = lean_ctor_get_uint8(v_s_730_, sizeof(void*)*17);
v_invSet_746_ = lean_ctor_get(v_s_730_, 14);
v_powIdentityVarCount_747_ = lean_ctor_get(v_s_730_, 15);
v_numEq0_x3f_748_ = lean_ctor_get(v_s_730_, 16);
v_numEq0Updated_749_ = lean_ctor_get_uint8(v_s_730_, sizeof(void*)*17 + 1);
v_isSharedCheck_781_ = !lean_is_exclusive(v_s_730_);
if (v_isSharedCheck_781_ == 0)
{
v___x_751_ = v_s_730_;
v_isShared_752_ = v_isSharedCheck_781_;
goto v_resetjp_750_;
}
else
{
lean_inc(v_numEq0_x3f_748_);
lean_inc(v_powIdentityVarCount_747_);
lean_inc(v_invSet_746_);
lean_inc(v_diseqs_744_);
lean_inc(v_basis_743_);
lean_inc(v_queue_742_);
lean_inc(v_steps_741_);
lean_inc(v_nextId_740_);
lean_inc(v_denoteEntries_739_);
lean_inc(v_powIdentityInst_x3f_738_);
lean_inc(v_fieldInst_x3f_737_);
lean_inc(v_noZeroDivInst_x3f_736_);
lean_inc(v_commRingInst_735_);
lean_inc(v_commSemiringInst_734_);
lean_inc(v_semiringId_x3f_733_);
lean_inc(v_invFn_x3f_732_);
lean_inc(v_toRing_731_);
lean_dec(v_s_730_);
v___x_751_ = lean_box(0);
v_isShared_752_ = v_isSharedCheck_781_;
goto v_resetjp_750_;
}
v_resetjp_750_:
{
lean_object* v_id_753_; lean_object* v_type_754_; lean_object* v_u_755_; lean_object* v_ringInst_756_; lean_object* v_semiringInst_757_; lean_object* v_charInst_x3f_758_; lean_object* v_addFn_x3f_759_; lean_object* v_mulFn_x3f_760_; lean_object* v_subFn_x3f_761_; lean_object* v_negFn_x3f_762_; lean_object* v_powFn_x3f_763_; lean_object* v_intCastFn_x3f_764_; lean_object* v_one_x3f_765_; lean_object* v_vars_766_; lean_object* v_varMap_767_; lean_object* v_denote_768_; lean_object* v___x_770_; uint8_t v_isShared_771_; uint8_t v_isSharedCheck_779_; 
v_id_753_ = lean_ctor_get(v_toRing_731_, 0);
v_type_754_ = lean_ctor_get(v_toRing_731_, 1);
v_u_755_ = lean_ctor_get(v_toRing_731_, 2);
v_ringInst_756_ = lean_ctor_get(v_toRing_731_, 3);
v_semiringInst_757_ = lean_ctor_get(v_toRing_731_, 4);
v_charInst_x3f_758_ = lean_ctor_get(v_toRing_731_, 5);
v_addFn_x3f_759_ = lean_ctor_get(v_toRing_731_, 6);
v_mulFn_x3f_760_ = lean_ctor_get(v_toRing_731_, 7);
v_subFn_x3f_761_ = lean_ctor_get(v_toRing_731_, 8);
v_negFn_x3f_762_ = lean_ctor_get(v_toRing_731_, 9);
v_powFn_x3f_763_ = lean_ctor_get(v_toRing_731_, 10);
v_intCastFn_x3f_764_ = lean_ctor_get(v_toRing_731_, 11);
v_one_x3f_765_ = lean_ctor_get(v_toRing_731_, 13);
v_vars_766_ = lean_ctor_get(v_toRing_731_, 14);
v_varMap_767_ = lean_ctor_get(v_toRing_731_, 15);
v_denote_768_ = lean_ctor_get(v_toRing_731_, 16);
v_isSharedCheck_779_ = !lean_is_exclusive(v_toRing_731_);
if (v_isSharedCheck_779_ == 0)
{
lean_object* v_unused_780_; 
v_unused_780_ = lean_ctor_get(v_toRing_731_, 12);
lean_dec(v_unused_780_);
v___x_770_ = v_toRing_731_;
v_isShared_771_ = v_isSharedCheck_779_;
goto v_resetjp_769_;
}
else
{
lean_inc(v_denote_768_);
lean_inc(v_varMap_767_);
lean_inc(v_vars_766_);
lean_inc(v_one_x3f_765_);
lean_inc(v_intCastFn_x3f_764_);
lean_inc(v_powFn_x3f_763_);
lean_inc(v_negFn_x3f_762_);
lean_inc(v_subFn_x3f_761_);
lean_inc(v_mulFn_x3f_760_);
lean_inc(v_addFn_x3f_759_);
lean_inc(v_charInst_x3f_758_);
lean_inc(v_semiringInst_757_);
lean_inc(v_ringInst_756_);
lean_inc(v_u_755_);
lean_inc(v_type_754_);
lean_inc(v_id_753_);
lean_dec(v_toRing_731_);
v___x_770_ = lean_box(0);
v_isShared_771_ = v_isSharedCheck_779_;
goto v_resetjp_769_;
}
v_resetjp_769_:
{
lean_object* v___x_772_; lean_object* v___x_774_; 
v___x_772_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_772_, 0, v_a_729_);
if (v_isShared_771_ == 0)
{
lean_ctor_set(v___x_770_, 12, v___x_772_);
v___x_774_ = v___x_770_;
goto v_reusejp_773_;
}
else
{
lean_object* v_reuseFailAlloc_778_; 
v_reuseFailAlloc_778_ = lean_alloc_ctor(0, 17, 0);
lean_ctor_set(v_reuseFailAlloc_778_, 0, v_id_753_);
lean_ctor_set(v_reuseFailAlloc_778_, 1, v_type_754_);
lean_ctor_set(v_reuseFailAlloc_778_, 2, v_u_755_);
lean_ctor_set(v_reuseFailAlloc_778_, 3, v_ringInst_756_);
lean_ctor_set(v_reuseFailAlloc_778_, 4, v_semiringInst_757_);
lean_ctor_set(v_reuseFailAlloc_778_, 5, v_charInst_x3f_758_);
lean_ctor_set(v_reuseFailAlloc_778_, 6, v_addFn_x3f_759_);
lean_ctor_set(v_reuseFailAlloc_778_, 7, v_mulFn_x3f_760_);
lean_ctor_set(v_reuseFailAlloc_778_, 8, v_subFn_x3f_761_);
lean_ctor_set(v_reuseFailAlloc_778_, 9, v_negFn_x3f_762_);
lean_ctor_set(v_reuseFailAlloc_778_, 10, v_powFn_x3f_763_);
lean_ctor_set(v_reuseFailAlloc_778_, 11, v_intCastFn_x3f_764_);
lean_ctor_set(v_reuseFailAlloc_778_, 12, v___x_772_);
lean_ctor_set(v_reuseFailAlloc_778_, 13, v_one_x3f_765_);
lean_ctor_set(v_reuseFailAlloc_778_, 14, v_vars_766_);
lean_ctor_set(v_reuseFailAlloc_778_, 15, v_varMap_767_);
lean_ctor_set(v_reuseFailAlloc_778_, 16, v_denote_768_);
v___x_774_ = v_reuseFailAlloc_778_;
goto v_reusejp_773_;
}
v_reusejp_773_:
{
lean_object* v___x_776_; 
if (v_isShared_752_ == 0)
{
lean_ctor_set(v___x_751_, 0, v___x_774_);
v___x_776_ = v___x_751_;
goto v_reusejp_775_;
}
else
{
lean_object* v_reuseFailAlloc_777_; 
v_reuseFailAlloc_777_ = lean_alloc_ctor(0, 17, 2);
lean_ctor_set(v_reuseFailAlloc_777_, 0, v___x_774_);
lean_ctor_set(v_reuseFailAlloc_777_, 1, v_invFn_x3f_732_);
lean_ctor_set(v_reuseFailAlloc_777_, 2, v_semiringId_x3f_733_);
lean_ctor_set(v_reuseFailAlloc_777_, 3, v_commSemiringInst_734_);
lean_ctor_set(v_reuseFailAlloc_777_, 4, v_commRingInst_735_);
lean_ctor_set(v_reuseFailAlloc_777_, 5, v_noZeroDivInst_x3f_736_);
lean_ctor_set(v_reuseFailAlloc_777_, 6, v_fieldInst_x3f_737_);
lean_ctor_set(v_reuseFailAlloc_777_, 7, v_powIdentityInst_x3f_738_);
lean_ctor_set(v_reuseFailAlloc_777_, 8, v_denoteEntries_739_);
lean_ctor_set(v_reuseFailAlloc_777_, 9, v_nextId_740_);
lean_ctor_set(v_reuseFailAlloc_777_, 10, v_steps_741_);
lean_ctor_set(v_reuseFailAlloc_777_, 11, v_queue_742_);
lean_ctor_set(v_reuseFailAlloc_777_, 12, v_basis_743_);
lean_ctor_set(v_reuseFailAlloc_777_, 13, v_diseqs_744_);
lean_ctor_set(v_reuseFailAlloc_777_, 14, v_invSet_746_);
lean_ctor_set(v_reuseFailAlloc_777_, 15, v_powIdentityVarCount_747_);
lean_ctor_set(v_reuseFailAlloc_777_, 16, v_numEq0_x3f_748_);
lean_ctor_set_uint8(v_reuseFailAlloc_777_, sizeof(void*)*17, v_recheck_745_);
lean_ctor_set_uint8(v_reuseFailAlloc_777_, sizeof(void*)*17 + 1, v_numEq0Updated_749_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_getNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isNatCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__2_spec__4_spec__6___redArg(lean_object* v_u_790_, lean_object* v_type_791_, lean_object* v_semiringInst_792_, lean_object* v___y_793_, lean_object* v___y_794_, lean_object* v___y_795_, lean_object* v___y_796_, lean_object* v___y_797_, lean_object* v___y_798_){
_start:
{
lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v_inst_x27_804_; lean_object* v_inst_806_; lean_object* v___y_807_; lean_object* v___y_808_; lean_object* v___y_809_; lean_object* v___y_810_; lean_object* v___y_811_; lean_object* v___y_812_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v_instType_821_; lean_object* v___x_822_; 
v___x_800_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_getNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isNatCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__2_spec__4_spec__6___redArg___closed__1));
v___x_801_ = lean_box(0);
v___x_802_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_802_, 0, v_u_790_);
lean_ctor_set(v___x_802_, 1, v___x_801_);
lean_inc_ref_n(v___x_802_, 2);
v___x_803_ = l_Lean_mkConst(v___x_800_, v___x_802_);
lean_inc_ref_n(v_type_791_, 2);
v_inst_x27_804_ = l_Lean_mkAppB(v___x_803_, v_type_791_, v_semiringInst_792_);
v___x_819_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_getNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isNatCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__2_spec__4_spec__6___redArg___closed__2));
v___x_820_ = l_Lean_mkConst(v___x_819_, v___x_802_);
v_instType_821_ = l_Lean_Expr_app___override(v___x_820_, v_type_791_);
v___x_822_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f(v_instType_821_, v___y_795_, v___y_796_, v___y_797_, v___y_798_);
if (lean_obj_tag(v___x_822_) == 0)
{
lean_object* v_a_823_; 
v_a_823_ = lean_ctor_get(v___x_822_, 0);
lean_inc(v_a_823_);
lean_dec_ref(v___x_822_);
if (lean_obj_tag(v_a_823_) == 0)
{
v_inst_806_ = v_inst_x27_804_;
v___y_807_ = v___y_793_;
v___y_808_ = v___y_794_;
v___y_809_ = v___y_795_;
v___y_810_ = v___y_796_;
v___y_811_ = v___y_797_;
v___y_812_ = v___y_798_;
goto v___jp_805_;
}
else
{
lean_object* v_val_824_; lean_object* v___x_825_; lean_object* v___x_826_; 
v_val_824_ = lean_ctor_get(v_a_823_, 0);
lean_inc_n(v_val_824_, 2);
lean_dec_ref(v_a_823_);
v___x_825_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__5));
v___x_826_ = l_Lean_Meta_Grind_Arith_CommRing_checkInst(v___x_825_, v_val_824_, v_inst_x27_804_, v___y_795_, v___y_796_, v___y_797_, v___y_798_);
if (lean_obj_tag(v___x_826_) == 0)
{
lean_dec_ref(v___x_826_);
v_inst_806_ = v_val_824_;
v___y_807_ = v___y_793_;
v___y_808_ = v___y_794_;
v___y_809_ = v___y_795_;
v___y_810_ = v___y_796_;
v___y_811_ = v___y_797_;
v___y_812_ = v___y_798_;
goto v___jp_805_;
}
else
{
lean_object* v_a_827_; lean_object* v___x_829_; uint8_t v_isShared_830_; uint8_t v_isSharedCheck_834_; 
lean_dec(v_val_824_);
lean_dec_ref(v___x_802_);
lean_dec_ref(v_type_791_);
v_a_827_ = lean_ctor_get(v___x_826_, 0);
v_isSharedCheck_834_ = !lean_is_exclusive(v___x_826_);
if (v_isSharedCheck_834_ == 0)
{
v___x_829_ = v___x_826_;
v_isShared_830_ = v_isSharedCheck_834_;
goto v_resetjp_828_;
}
else
{
lean_inc(v_a_827_);
lean_dec(v___x_826_);
v___x_829_ = lean_box(0);
v_isShared_830_ = v_isSharedCheck_834_;
goto v_resetjp_828_;
}
v_resetjp_828_:
{
lean_object* v___x_832_; 
if (v_isShared_830_ == 0)
{
v___x_832_ = v___x_829_;
goto v_reusejp_831_;
}
else
{
lean_object* v_reuseFailAlloc_833_; 
v_reuseFailAlloc_833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_833_, 0, v_a_827_);
v___x_832_ = v_reuseFailAlloc_833_;
goto v_reusejp_831_;
}
v_reusejp_831_:
{
return v___x_832_;
}
}
}
}
}
else
{
lean_object* v_a_835_; lean_object* v___x_837_; uint8_t v_isShared_838_; uint8_t v_isSharedCheck_842_; 
lean_dec_ref(v_inst_x27_804_);
lean_dec_ref(v___x_802_);
lean_dec_ref(v_type_791_);
v_a_835_ = lean_ctor_get(v___x_822_, 0);
v_isSharedCheck_842_ = !lean_is_exclusive(v___x_822_);
if (v_isSharedCheck_842_ == 0)
{
v___x_837_ = v___x_822_;
v_isShared_838_ = v_isSharedCheck_842_;
goto v_resetjp_836_;
}
else
{
lean_inc(v_a_835_);
lean_dec(v___x_822_);
v___x_837_ = lean_box(0);
v_isShared_838_ = v_isSharedCheck_842_;
goto v_resetjp_836_;
}
v_resetjp_836_:
{
lean_object* v___x_840_; 
if (v_isShared_838_ == 0)
{
v___x_840_ = v___x_837_;
goto v_reusejp_839_;
}
else
{
lean_object* v_reuseFailAlloc_841_; 
v_reuseFailAlloc_841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_841_, 0, v_a_835_);
v___x_840_ = v_reuseFailAlloc_841_;
goto v_reusejp_839_;
}
v_reusejp_839_:
{
return v___x_840_;
}
}
}
v___jp_805_:
{
lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; 
v___x_813_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__5));
v___x_814_ = l_Lean_mkConst(v___x_813_, v___x_802_);
v___x_815_ = l_Lean_mkAppB(v___x_814_, v_type_791_, v_inst_806_);
v___x_816_ = l_Lean_Meta_Sym_canon(v___x_815_, v___y_807_, v___y_808_, v___y_809_, v___y_810_, v___y_811_, v___y_812_);
if (lean_obj_tag(v___x_816_) == 0)
{
lean_object* v_a_817_; lean_object* v___x_818_; 
v_a_817_ = lean_ctor_get(v___x_816_, 0);
lean_inc(v_a_817_);
lean_dec_ref(v___x_816_);
v___x_818_ = l_Lean_Meta_Sym_shareCommon___redArg(v_a_817_, v___y_808_);
return v___x_818_;
}
else
{
return v___x_816_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_getNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isNatCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__2_spec__4_spec__6___redArg___boxed(lean_object* v_u_843_, lean_object* v_type_844_, lean_object* v_semiringInst_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_, lean_object* v___y_852_){
_start:
{
lean_object* v_res_853_; 
v_res_853_ = l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_getNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isNatCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__2_spec__4_spec__6___redArg(v_u_843_, v_type_844_, v_semiringInst_845_, v___y_846_, v___y_847_, v___y_848_, v___y_849_, v___y_850_, v___y_851_);
lean_dec(v___y_851_);
lean_dec_ref(v___y_850_);
lean_dec(v___y_849_);
lean_dec_ref(v___y_848_);
lean_dec(v___y_847_);
lean_dec_ref(v___y_846_);
return v_res_853_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isNatCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__2_spec__4(lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_, lean_object* v___y_857_, lean_object* v___y_858_, lean_object* v___y_859_, lean_object* v___y_860_, lean_object* v___y_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_){
_start:
{
lean_object* v___x_866_; 
v___x_866_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v___y_854_, v___y_855_, v___y_856_, v___y_857_, v___y_858_, v___y_859_, v___y_860_, v___y_861_, v___y_862_, v___y_863_, v___y_864_);
if (lean_obj_tag(v___x_866_) == 0)
{
lean_object* v_a_867_; lean_object* v___x_869_; uint8_t v_isShared_870_; uint8_t v_isSharedCheck_900_; 
v_a_867_ = lean_ctor_get(v___x_866_, 0);
v_isSharedCheck_900_ = !lean_is_exclusive(v___x_866_);
if (v_isSharedCheck_900_ == 0)
{
v___x_869_ = v___x_866_;
v_isShared_870_ = v_isSharedCheck_900_;
goto v_resetjp_868_;
}
else
{
lean_inc(v_a_867_);
lean_dec(v___x_866_);
v___x_869_ = lean_box(0);
v_isShared_870_ = v_isSharedCheck_900_;
goto v_resetjp_868_;
}
v_resetjp_868_:
{
lean_object* v_toRing_871_; lean_object* v_natCastFn_x3f_872_; 
v_toRing_871_ = lean_ctor_get(v_a_867_, 0);
lean_inc_ref(v_toRing_871_);
lean_dec(v_a_867_);
v_natCastFn_x3f_872_ = lean_ctor_get(v_toRing_871_, 12);
if (lean_obj_tag(v_natCastFn_x3f_872_) == 1)
{
lean_object* v_val_873_; lean_object* v___x_875_; 
lean_inc_ref(v_natCastFn_x3f_872_);
lean_dec_ref(v_toRing_871_);
v_val_873_ = lean_ctor_get(v_natCastFn_x3f_872_, 0);
lean_inc(v_val_873_);
lean_dec_ref(v_natCastFn_x3f_872_);
if (v_isShared_870_ == 0)
{
lean_ctor_set(v___x_869_, 0, v_val_873_);
v___x_875_ = v___x_869_;
goto v_reusejp_874_;
}
else
{
lean_object* v_reuseFailAlloc_876_; 
v_reuseFailAlloc_876_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_876_, 0, v_val_873_);
v___x_875_ = v_reuseFailAlloc_876_;
goto v_reusejp_874_;
}
v_reusejp_874_:
{
return v___x_875_;
}
}
else
{
lean_object* v_type_877_; lean_object* v_u_878_; lean_object* v_semiringInst_879_; lean_object* v___x_880_; 
lean_del_object(v___x_869_);
v_type_877_ = lean_ctor_get(v_toRing_871_, 1);
lean_inc_ref(v_type_877_);
v_u_878_ = lean_ctor_get(v_toRing_871_, 2);
lean_inc(v_u_878_);
v_semiringInst_879_ = lean_ctor_get(v_toRing_871_, 4);
lean_inc_ref(v_semiringInst_879_);
lean_dec_ref(v_toRing_871_);
v___x_880_ = l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_getNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isNatCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__2_spec__4_spec__6___redArg(v_u_878_, v_type_877_, v_semiringInst_879_, v___y_859_, v___y_860_, v___y_861_, v___y_862_, v___y_863_, v___y_864_);
if (lean_obj_tag(v___x_880_) == 0)
{
lean_object* v_a_881_; lean_object* v___f_882_; lean_object* v___x_883_; 
v_a_881_ = lean_ctor_get(v___x_880_, 0);
lean_inc_n(v_a_881_, 2);
lean_dec_ref(v___x_880_);
v___f_882_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isNatCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__2_spec__4___lam__0), 2, 1);
lean_closure_set(v___f_882_, 0, v_a_881_);
v___x_883_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(v___f_882_, v___y_854_, v___y_855_);
if (lean_obj_tag(v___x_883_) == 0)
{
lean_object* v___x_885_; uint8_t v_isShared_886_; uint8_t v_isSharedCheck_890_; 
v_isSharedCheck_890_ = !lean_is_exclusive(v___x_883_);
if (v_isSharedCheck_890_ == 0)
{
lean_object* v_unused_891_; 
v_unused_891_ = lean_ctor_get(v___x_883_, 0);
lean_dec(v_unused_891_);
v___x_885_ = v___x_883_;
v_isShared_886_ = v_isSharedCheck_890_;
goto v_resetjp_884_;
}
else
{
lean_dec(v___x_883_);
v___x_885_ = lean_box(0);
v_isShared_886_ = v_isSharedCheck_890_;
goto v_resetjp_884_;
}
v_resetjp_884_:
{
lean_object* v___x_888_; 
if (v_isShared_886_ == 0)
{
lean_ctor_set(v___x_885_, 0, v_a_881_);
v___x_888_ = v___x_885_;
goto v_reusejp_887_;
}
else
{
lean_object* v_reuseFailAlloc_889_; 
v_reuseFailAlloc_889_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_889_, 0, v_a_881_);
v___x_888_ = v_reuseFailAlloc_889_;
goto v_reusejp_887_;
}
v_reusejp_887_:
{
return v___x_888_;
}
}
}
else
{
lean_object* v_a_892_; lean_object* v___x_894_; uint8_t v_isShared_895_; uint8_t v_isSharedCheck_899_; 
lean_dec(v_a_881_);
v_a_892_ = lean_ctor_get(v___x_883_, 0);
v_isSharedCheck_899_ = !lean_is_exclusive(v___x_883_);
if (v_isSharedCheck_899_ == 0)
{
v___x_894_ = v___x_883_;
v_isShared_895_ = v_isSharedCheck_899_;
goto v_resetjp_893_;
}
else
{
lean_inc(v_a_892_);
lean_dec(v___x_883_);
v___x_894_ = lean_box(0);
v_isShared_895_ = v_isSharedCheck_899_;
goto v_resetjp_893_;
}
v_resetjp_893_:
{
lean_object* v___x_897_; 
if (v_isShared_895_ == 0)
{
v___x_897_ = v___x_894_;
goto v_reusejp_896_;
}
else
{
lean_object* v_reuseFailAlloc_898_; 
v_reuseFailAlloc_898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_898_, 0, v_a_892_);
v___x_897_ = v_reuseFailAlloc_898_;
goto v_reusejp_896_;
}
v_reusejp_896_:
{
return v___x_897_;
}
}
}
}
else
{
return v___x_880_;
}
}
}
}
else
{
lean_object* v_a_901_; lean_object* v___x_903_; uint8_t v_isShared_904_; uint8_t v_isSharedCheck_908_; 
v_a_901_ = lean_ctor_get(v___x_866_, 0);
v_isSharedCheck_908_ = !lean_is_exclusive(v___x_866_);
if (v_isSharedCheck_908_ == 0)
{
v___x_903_ = v___x_866_;
v_isShared_904_ = v_isSharedCheck_908_;
goto v_resetjp_902_;
}
else
{
lean_inc(v_a_901_);
lean_dec(v___x_866_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isNatCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__2_spec__4___boxed(lean_object* v___y_909_, lean_object* v___y_910_, lean_object* v___y_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_){
_start:
{
lean_object* v_res_921_; 
v_res_921_ = l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isNatCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__2_spec__4(v___y_909_, v___y_910_, v___y_911_, v___y_912_, v___y_913_, v___y_914_, v___y_915_, v___y_916_, v___y_917_, v___y_918_, v___y_919_);
lean_dec(v___y_919_);
lean_dec_ref(v___y_918_);
lean_dec(v___y_917_);
lean_dec_ref(v___y_916_);
lean_dec(v___y_915_);
lean_dec_ref(v___y_914_);
lean_dec(v___y_913_);
lean_dec_ref(v___y_912_);
lean_dec(v___y_911_);
lean_dec(v___y_910_);
lean_dec_ref(v___y_909_);
return v_res_921_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_isNatCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__2(lean_object* v_inst_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_, lean_object* v___y_933_){
_start:
{
lean_object* v___x_935_; 
v___x_935_ = l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isNatCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__2_spec__4(v___y_923_, v___y_924_, v___y_925_, v___y_926_, v___y_927_, v___y_928_, v___y_929_, v___y_930_, v___y_931_, v___y_932_, v___y_933_);
if (lean_obj_tag(v___x_935_) == 0)
{
lean_object* v_a_936_; lean_object* v___x_938_; uint8_t v_isShared_939_; uint8_t v_isSharedCheck_946_; 
v_a_936_ = lean_ctor_get(v___x_935_, 0);
v_isSharedCheck_946_ = !lean_is_exclusive(v___x_935_);
if (v_isSharedCheck_946_ == 0)
{
v___x_938_ = v___x_935_;
v_isShared_939_ = v_isSharedCheck_946_;
goto v_resetjp_937_;
}
else
{
lean_inc(v_a_936_);
lean_dec(v___x_935_);
v___x_938_ = lean_box(0);
v_isShared_939_ = v_isSharedCheck_946_;
goto v_resetjp_937_;
}
v_resetjp_937_:
{
lean_object* v___x_940_; uint8_t v___x_941_; lean_object* v___x_942_; lean_object* v___x_944_; 
v___x_940_ = l_Lean_Expr_appArg_x21(v_a_936_);
lean_dec(v_a_936_);
v___x_941_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v___x_940_, v_inst_922_);
lean_dec_ref(v___x_940_);
v___x_942_ = lean_box(v___x_941_);
if (v_isShared_939_ == 0)
{
lean_ctor_set(v___x_938_, 0, v___x_942_);
v___x_944_ = v___x_938_;
goto v_reusejp_943_;
}
else
{
lean_object* v_reuseFailAlloc_945_; 
v_reuseFailAlloc_945_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_945_, 0, v___x_942_);
v___x_944_ = v_reuseFailAlloc_945_;
goto v_reusejp_943_;
}
v_reusejp_943_:
{
return v___x_944_;
}
}
}
else
{
lean_object* v_a_947_; lean_object* v___x_949_; uint8_t v_isShared_950_; uint8_t v_isSharedCheck_954_; 
v_a_947_ = lean_ctor_get(v___x_935_, 0);
v_isSharedCheck_954_ = !lean_is_exclusive(v___x_935_);
if (v_isSharedCheck_954_ == 0)
{
v___x_949_ = v___x_935_;
v_isShared_950_ = v_isSharedCheck_954_;
goto v_resetjp_948_;
}
else
{
lean_inc(v_a_947_);
lean_dec(v___x_935_);
v___x_949_ = lean_box(0);
v_isShared_950_ = v_isSharedCheck_954_;
goto v_resetjp_948_;
}
v_resetjp_948_:
{
lean_object* v___x_952_; 
if (v_isShared_950_ == 0)
{
v___x_952_ = v___x_949_;
goto v_reusejp_951_;
}
else
{
lean_object* v_reuseFailAlloc_953_; 
v_reuseFailAlloc_953_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_953_, 0, v_a_947_);
v___x_952_ = v_reuseFailAlloc_953_;
goto v_reusejp_951_;
}
v_reusejp_951_:
{
return v___x_952_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_isNatCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__2___boxed(lean_object* v_inst_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_){
_start:
{
lean_object* v_res_968_; 
v_res_968_ = l_Lean_Meta_Grind_Arith_CommRing_isNatCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__2(v_inst_955_, v___y_956_, v___y_957_, v___y_958_, v___y_959_, v___y_960_, v___y_961_, v___y_962_, v___y_963_, v___y_964_, v___y_965_, v___y_966_);
lean_dec(v___y_966_);
lean_dec_ref(v___y_965_);
lean_dec(v___y_964_);
lean_dec_ref(v___y_963_);
lean_dec(v___y_962_);
lean_dec_ref(v___y_961_);
lean_dec(v___y_960_);
lean_dec_ref(v___y_959_);
lean_dec(v___y_958_);
lean_dec(v___y_957_);
lean_dec_ref(v___y_956_);
lean_dec_ref(v_inst_955_);
return v_res_968_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f(lean_object* v_e_969_, lean_object* v_a_970_, lean_object* v_a_971_, lean_object* v_a_972_, lean_object* v_a_973_, lean_object* v_a_974_, lean_object* v_a_975_, lean_object* v_a_976_, lean_object* v_a_977_, lean_object* v_a_978_, lean_object* v_a_979_, lean_object* v_a_980_){
_start:
{
lean_object* v___x_982_; 
v___x_982_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_969_, v_a_978_);
if (lean_obj_tag(v___x_982_) == 0)
{
lean_object* v_a_983_; lean_object* v___x_985_; uint8_t v_isShared_986_; uint8_t v_isSharedCheck_1146_; 
v_a_983_ = lean_ctor_get(v___x_982_, 0);
v_isSharedCheck_1146_ = !lean_is_exclusive(v___x_982_);
if (v_isSharedCheck_1146_ == 0)
{
v___x_985_ = v___x_982_;
v_isShared_986_ = v_isSharedCheck_1146_;
goto v_resetjp_984_;
}
else
{
lean_inc(v_a_983_);
lean_dec(v___x_982_);
v___x_985_ = lean_box(0);
v_isShared_986_ = v_isSharedCheck_1146_;
goto v_resetjp_984_;
}
v_resetjp_984_:
{
lean_object* v___x_992_; uint8_t v___x_993_; 
v___x_992_ = l_Lean_Expr_cleanupAnnotations(v_a_983_);
v___x_993_ = l_Lean_Expr_isApp(v___x_992_);
if (v___x_993_ == 0)
{
lean_dec_ref(v___x_992_);
goto v___jp_987_;
}
else
{
lean_object* v_arg_994_; lean_object* v___x_995_; uint8_t v___x_996_; 
v_arg_994_ = lean_ctor_get(v___x_992_, 1);
lean_inc_ref(v_arg_994_);
v___x_995_ = l_Lean_Expr_appFnCleanup___redArg(v___x_992_);
v___x_996_ = l_Lean_Expr_isApp(v___x_995_);
if (v___x_996_ == 0)
{
lean_dec_ref(v___x_995_);
lean_dec_ref(v_arg_994_);
goto v___jp_987_;
}
else
{
lean_object* v_arg_997_; lean_object* v___x_998_; uint8_t v___x_999_; 
v_arg_997_ = lean_ctor_get(v___x_995_, 1);
lean_inc_ref(v_arg_997_);
v___x_998_ = l_Lean_Expr_appFnCleanup___redArg(v___x_995_);
v___x_999_ = l_Lean_Expr_isApp(v___x_998_);
if (v___x_999_ == 0)
{
lean_dec_ref(v___x_998_);
lean_dec_ref(v_arg_997_);
lean_dec_ref(v_arg_994_);
goto v___jp_987_;
}
else
{
lean_object* v___x_1000_; lean_object* v___x_1001_; uint8_t v___x_1002_; 
v___x_1000_ = l_Lean_Expr_appFnCleanup___redArg(v___x_998_);
v___x_1001_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__8));
v___x_1002_ = l_Lean_Expr_isConstOf(v___x_1000_, v___x_1001_);
if (v___x_1002_ == 0)
{
lean_object* v___x_1003_; uint8_t v___x_1004_; 
v___x_1003_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__5));
v___x_1004_ = l_Lean_Expr_isConstOf(v___x_1000_, v___x_1003_);
if (v___x_1004_ == 0)
{
lean_object* v___x_1005_; uint8_t v___x_1006_; 
v___x_1005_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__2));
v___x_1006_ = l_Lean_Expr_isConstOf(v___x_1000_, v___x_1005_);
if (v___x_1006_ == 0)
{
lean_object* v___x_1007_; uint8_t v___x_1008_; 
v___x_1007_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__11));
v___x_1008_ = l_Lean_Expr_isConstOf(v___x_1000_, v___x_1007_);
lean_dec_ref(v___x_1000_);
if (v___x_1008_ == 0)
{
lean_dec_ref(v_arg_997_);
lean_dec_ref(v_arg_994_);
goto v___jp_987_;
}
else
{
lean_object* v___x_1009_; 
lean_del_object(v___x_985_);
v___x_1009_ = l_Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0(v_arg_997_, v_a_970_, v_a_971_, v_a_972_, v_a_973_, v_a_974_, v_a_975_, v_a_976_, v_a_977_, v_a_978_, v_a_979_, v_a_980_);
lean_dec_ref(v_arg_997_);
if (lean_obj_tag(v___x_1009_) == 0)
{
lean_object* v_a_1010_; lean_object* v___x_1012_; uint8_t v_isShared_1013_; uint8_t v_isSharedCheck_1038_; 
v_a_1010_ = lean_ctor_get(v___x_1009_, 0);
v_isSharedCheck_1038_ = !lean_is_exclusive(v___x_1009_);
if (v_isSharedCheck_1038_ == 0)
{
v___x_1012_ = v___x_1009_;
v_isShared_1013_ = v_isSharedCheck_1038_;
goto v_resetjp_1011_;
}
else
{
lean_inc(v_a_1010_);
lean_dec(v___x_1009_);
v___x_1012_ = lean_box(0);
v_isShared_1013_ = v_isSharedCheck_1038_;
goto v_resetjp_1011_;
}
v_resetjp_1011_:
{
uint8_t v___x_1014_; 
v___x_1014_ = lean_unbox(v_a_1010_);
lean_dec(v_a_1010_);
if (v___x_1014_ == 0)
{
lean_object* v___x_1015_; lean_object* v___x_1017_; 
lean_dec_ref(v_arg_994_);
v___x_1015_ = lean_box(0);
if (v_isShared_1013_ == 0)
{
lean_ctor_set(v___x_1012_, 0, v___x_1015_);
v___x_1017_ = v___x_1012_;
goto v_reusejp_1016_;
}
else
{
lean_object* v_reuseFailAlloc_1018_; 
v_reuseFailAlloc_1018_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1018_, 0, v___x_1015_);
v___x_1017_ = v_reuseFailAlloc_1018_;
goto v_reusejp_1016_;
}
v_reusejp_1016_:
{
return v___x_1017_;
}
}
else
{
lean_object* v___x_1019_; 
lean_del_object(v___x_1012_);
v___x_1019_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f(v_arg_994_, v_a_970_, v_a_971_, v_a_972_, v_a_973_, v_a_974_, v_a_975_, v_a_976_, v_a_977_, v_a_978_, v_a_979_, v_a_980_);
if (lean_obj_tag(v___x_1019_) == 0)
{
lean_object* v_a_1020_; 
v_a_1020_ = lean_ctor_get(v___x_1019_, 0);
lean_inc(v_a_1020_);
if (lean_obj_tag(v_a_1020_) == 0)
{
return v___x_1019_;
}
else
{
lean_object* v___x_1022_; uint8_t v_isShared_1023_; uint8_t v_isSharedCheck_1036_; 
v_isSharedCheck_1036_ = !lean_is_exclusive(v___x_1019_);
if (v_isSharedCheck_1036_ == 0)
{
lean_object* v_unused_1037_; 
v_unused_1037_ = lean_ctor_get(v___x_1019_, 0);
lean_dec(v_unused_1037_);
v___x_1022_ = v___x_1019_;
v_isShared_1023_ = v_isSharedCheck_1036_;
goto v_resetjp_1021_;
}
else
{
lean_dec(v___x_1019_);
v___x_1022_ = lean_box(0);
v_isShared_1023_ = v_isSharedCheck_1036_;
goto v_resetjp_1021_;
}
v_resetjp_1021_:
{
lean_object* v_val_1024_; lean_object* v___x_1026_; uint8_t v_isShared_1027_; uint8_t v_isSharedCheck_1035_; 
v_val_1024_ = lean_ctor_get(v_a_1020_, 0);
v_isSharedCheck_1035_ = !lean_is_exclusive(v_a_1020_);
if (v_isSharedCheck_1035_ == 0)
{
v___x_1026_ = v_a_1020_;
v_isShared_1027_ = v_isSharedCheck_1035_;
goto v_resetjp_1025_;
}
else
{
lean_inc(v_val_1024_);
lean_dec(v_a_1020_);
v___x_1026_ = lean_box(0);
v_isShared_1027_ = v_isSharedCheck_1035_;
goto v_resetjp_1025_;
}
v_resetjp_1025_:
{
lean_object* v___x_1028_; lean_object* v___x_1030_; 
v___x_1028_ = lean_int_neg(v_val_1024_);
lean_dec(v_val_1024_);
if (v_isShared_1027_ == 0)
{
lean_ctor_set(v___x_1026_, 0, v___x_1028_);
v___x_1030_ = v___x_1026_;
goto v_reusejp_1029_;
}
else
{
lean_object* v_reuseFailAlloc_1034_; 
v_reuseFailAlloc_1034_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1034_, 0, v___x_1028_);
v___x_1030_ = v_reuseFailAlloc_1034_;
goto v_reusejp_1029_;
}
v_reusejp_1029_:
{
lean_object* v___x_1032_; 
if (v_isShared_1023_ == 0)
{
lean_ctor_set(v___x_1022_, 0, v___x_1030_);
v___x_1032_ = v___x_1022_;
goto v_reusejp_1031_;
}
else
{
lean_object* v_reuseFailAlloc_1033_; 
v_reuseFailAlloc_1033_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1033_, 0, v___x_1030_);
v___x_1032_ = v_reuseFailAlloc_1033_;
goto v_reusejp_1031_;
}
v_reusejp_1031_:
{
return v___x_1032_;
}
}
}
}
}
}
else
{
return v___x_1019_;
}
}
}
}
else
{
lean_object* v_a_1039_; lean_object* v___x_1041_; uint8_t v_isShared_1042_; uint8_t v_isSharedCheck_1046_; 
lean_dec_ref(v_arg_994_);
v_a_1039_ = lean_ctor_get(v___x_1009_, 0);
v_isSharedCheck_1046_ = !lean_is_exclusive(v___x_1009_);
if (v_isSharedCheck_1046_ == 0)
{
v___x_1041_ = v___x_1009_;
v_isShared_1042_ = v_isSharedCheck_1046_;
goto v_resetjp_1040_;
}
else
{
lean_inc(v_a_1039_);
lean_dec(v___x_1009_);
v___x_1041_ = lean_box(0);
v_isShared_1042_ = v_isSharedCheck_1046_;
goto v_resetjp_1040_;
}
v_resetjp_1040_:
{
lean_object* v___x_1044_; 
if (v_isShared_1042_ == 0)
{
v___x_1044_ = v___x_1041_;
goto v_reusejp_1043_;
}
else
{
lean_object* v_reuseFailAlloc_1045_; 
v_reuseFailAlloc_1045_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1045_, 0, v_a_1039_);
v___x_1044_ = v_reuseFailAlloc_1045_;
goto v_reusejp_1043_;
}
v_reusejp_1043_:
{
return v___x_1044_;
}
}
}
}
}
else
{
lean_object* v___x_1047_; 
lean_dec_ref(v___x_1000_);
lean_del_object(v___x_985_);
v___x_1047_ = l_Lean_Meta_Grind_Arith_CommRing_isIntCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__1(v_arg_997_, v_a_970_, v_a_971_, v_a_972_, v_a_973_, v_a_974_, v_a_975_, v_a_976_, v_a_977_, v_a_978_, v_a_979_, v_a_980_);
lean_dec_ref(v_arg_997_);
if (lean_obj_tag(v___x_1047_) == 0)
{
lean_object* v_a_1048_; lean_object* v___x_1050_; uint8_t v_isShared_1051_; uint8_t v_isSharedCheck_1058_; 
v_a_1048_ = lean_ctor_get(v___x_1047_, 0);
v_isSharedCheck_1058_ = !lean_is_exclusive(v___x_1047_);
if (v_isSharedCheck_1058_ == 0)
{
v___x_1050_ = v___x_1047_;
v_isShared_1051_ = v_isSharedCheck_1058_;
goto v_resetjp_1049_;
}
else
{
lean_inc(v_a_1048_);
lean_dec(v___x_1047_);
v___x_1050_ = lean_box(0);
v_isShared_1051_ = v_isSharedCheck_1058_;
goto v_resetjp_1049_;
}
v_resetjp_1049_:
{
uint8_t v___x_1052_; 
v___x_1052_ = lean_unbox(v_a_1048_);
lean_dec(v_a_1048_);
if (v___x_1052_ == 0)
{
lean_object* v___x_1053_; lean_object* v___x_1055_; 
lean_dec_ref(v_arg_994_);
v___x_1053_ = lean_box(0);
if (v_isShared_1051_ == 0)
{
lean_ctor_set(v___x_1050_, 0, v___x_1053_);
v___x_1055_ = v___x_1050_;
goto v_reusejp_1054_;
}
else
{
lean_object* v_reuseFailAlloc_1056_; 
v_reuseFailAlloc_1056_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1056_, 0, v___x_1053_);
v___x_1055_ = v_reuseFailAlloc_1056_;
goto v_reusejp_1054_;
}
v_reusejp_1054_:
{
return v___x_1055_;
}
}
else
{
lean_object* v___x_1057_; 
lean_del_object(v___x_1050_);
v___x_1057_ = l_Lean_Meta_getIntValue_x3f(v_arg_994_, v_a_977_, v_a_978_, v_a_979_, v_a_980_);
return v___x_1057_;
}
}
}
else
{
lean_object* v_a_1059_; lean_object* v___x_1061_; uint8_t v_isShared_1062_; uint8_t v_isSharedCheck_1066_; 
lean_dec_ref(v_arg_994_);
v_a_1059_ = lean_ctor_get(v___x_1047_, 0);
v_isSharedCheck_1066_ = !lean_is_exclusive(v___x_1047_);
if (v_isSharedCheck_1066_ == 0)
{
v___x_1061_ = v___x_1047_;
v_isShared_1062_ = v_isSharedCheck_1066_;
goto v_resetjp_1060_;
}
else
{
lean_inc(v_a_1059_);
lean_dec(v___x_1047_);
v___x_1061_ = lean_box(0);
v_isShared_1062_ = v_isSharedCheck_1066_;
goto v_resetjp_1060_;
}
v_resetjp_1060_:
{
lean_object* v___x_1064_; 
if (v_isShared_1062_ == 0)
{
v___x_1064_ = v___x_1061_;
goto v_reusejp_1063_;
}
else
{
lean_object* v_reuseFailAlloc_1065_; 
v_reuseFailAlloc_1065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1065_, 0, v_a_1059_);
v___x_1064_ = v_reuseFailAlloc_1065_;
goto v_reusejp_1063_;
}
v_reusejp_1063_:
{
return v___x_1064_;
}
}
}
}
}
else
{
lean_object* v___x_1067_; 
lean_dec_ref(v___x_1000_);
lean_del_object(v___x_985_);
v___x_1067_ = l_Lean_Meta_Grind_Arith_CommRing_isNatCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__2(v_arg_997_, v_a_970_, v_a_971_, v_a_972_, v_a_973_, v_a_974_, v_a_975_, v_a_976_, v_a_977_, v_a_978_, v_a_979_, v_a_980_);
lean_dec_ref(v_arg_997_);
if (lean_obj_tag(v___x_1067_) == 0)
{
lean_object* v_a_1068_; lean_object* v___x_1070_; uint8_t v_isShared_1071_; uint8_t v_isSharedCheck_1107_; 
v_a_1068_ = lean_ctor_get(v___x_1067_, 0);
v_isSharedCheck_1107_ = !lean_is_exclusive(v___x_1067_);
if (v_isSharedCheck_1107_ == 0)
{
v___x_1070_ = v___x_1067_;
v_isShared_1071_ = v_isSharedCheck_1107_;
goto v_resetjp_1069_;
}
else
{
lean_inc(v_a_1068_);
lean_dec(v___x_1067_);
v___x_1070_ = lean_box(0);
v_isShared_1071_ = v_isSharedCheck_1107_;
goto v_resetjp_1069_;
}
v_resetjp_1069_:
{
uint8_t v___x_1072_; 
v___x_1072_ = lean_unbox(v_a_1068_);
lean_dec(v_a_1068_);
if (v___x_1072_ == 0)
{
lean_object* v___x_1073_; lean_object* v___x_1075_; 
lean_dec_ref(v_arg_994_);
v___x_1073_ = lean_box(0);
if (v_isShared_1071_ == 0)
{
lean_ctor_set(v___x_1070_, 0, v___x_1073_);
v___x_1075_ = v___x_1070_;
goto v_reusejp_1074_;
}
else
{
lean_object* v_reuseFailAlloc_1076_; 
v_reuseFailAlloc_1076_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1076_, 0, v___x_1073_);
v___x_1075_ = v_reuseFailAlloc_1076_;
goto v_reusejp_1074_;
}
v_reusejp_1074_:
{
return v___x_1075_;
}
}
else
{
lean_object* v___x_1077_; 
lean_del_object(v___x_1070_);
v___x_1077_ = l_Lean_Meta_getNatValue_x3f(v_arg_994_, v_a_977_, v_a_978_, v_a_979_, v_a_980_);
lean_dec_ref(v_arg_994_);
if (lean_obj_tag(v___x_1077_) == 0)
{
lean_object* v_a_1078_; lean_object* v___x_1080_; uint8_t v_isShared_1081_; uint8_t v_isSharedCheck_1098_; 
v_a_1078_ = lean_ctor_get(v___x_1077_, 0);
v_isSharedCheck_1098_ = !lean_is_exclusive(v___x_1077_);
if (v_isSharedCheck_1098_ == 0)
{
v___x_1080_ = v___x_1077_;
v_isShared_1081_ = v_isSharedCheck_1098_;
goto v_resetjp_1079_;
}
else
{
lean_inc(v_a_1078_);
lean_dec(v___x_1077_);
v___x_1080_ = lean_box(0);
v_isShared_1081_ = v_isSharedCheck_1098_;
goto v_resetjp_1079_;
}
v_resetjp_1079_:
{
if (lean_obj_tag(v_a_1078_) == 1)
{
lean_object* v_val_1082_; lean_object* v___x_1084_; uint8_t v_isShared_1085_; uint8_t v_isSharedCheck_1093_; 
v_val_1082_ = lean_ctor_get(v_a_1078_, 0);
v_isSharedCheck_1093_ = !lean_is_exclusive(v_a_1078_);
if (v_isSharedCheck_1093_ == 0)
{
v___x_1084_ = v_a_1078_;
v_isShared_1085_ = v_isSharedCheck_1093_;
goto v_resetjp_1083_;
}
else
{
lean_inc(v_val_1082_);
lean_dec(v_a_1078_);
v___x_1084_ = lean_box(0);
v_isShared_1085_ = v_isSharedCheck_1093_;
goto v_resetjp_1083_;
}
v_resetjp_1083_:
{
lean_object* v___x_1086_; lean_object* v___x_1088_; 
v___x_1086_ = lean_nat_to_int(v_val_1082_);
if (v_isShared_1085_ == 0)
{
lean_ctor_set(v___x_1084_, 0, v___x_1086_);
v___x_1088_ = v___x_1084_;
goto v_reusejp_1087_;
}
else
{
lean_object* v_reuseFailAlloc_1092_; 
v_reuseFailAlloc_1092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1092_, 0, v___x_1086_);
v___x_1088_ = v_reuseFailAlloc_1092_;
goto v_reusejp_1087_;
}
v_reusejp_1087_:
{
lean_object* v___x_1090_; 
if (v_isShared_1081_ == 0)
{
lean_ctor_set(v___x_1080_, 0, v___x_1088_);
v___x_1090_ = v___x_1080_;
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
lean_object* v___x_1094_; lean_object* v___x_1096_; 
lean_dec(v_a_1078_);
v___x_1094_ = lean_box(0);
if (v_isShared_1081_ == 0)
{
lean_ctor_set(v___x_1080_, 0, v___x_1094_);
v___x_1096_ = v___x_1080_;
goto v_reusejp_1095_;
}
else
{
lean_object* v_reuseFailAlloc_1097_; 
v_reuseFailAlloc_1097_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1097_, 0, v___x_1094_);
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
else
{
lean_object* v_a_1099_; lean_object* v___x_1101_; uint8_t v_isShared_1102_; uint8_t v_isSharedCheck_1106_; 
v_a_1099_ = lean_ctor_get(v___x_1077_, 0);
v_isSharedCheck_1106_ = !lean_is_exclusive(v___x_1077_);
if (v_isSharedCheck_1106_ == 0)
{
v___x_1101_ = v___x_1077_;
v_isShared_1102_ = v_isSharedCheck_1106_;
goto v_resetjp_1100_;
}
else
{
lean_inc(v_a_1099_);
lean_dec(v___x_1077_);
v___x_1101_ = lean_box(0);
v_isShared_1102_ = v_isSharedCheck_1106_;
goto v_resetjp_1100_;
}
v_resetjp_1100_:
{
lean_object* v___x_1104_; 
if (v_isShared_1102_ == 0)
{
v___x_1104_ = v___x_1101_;
goto v_reusejp_1103_;
}
else
{
lean_object* v_reuseFailAlloc_1105_; 
v_reuseFailAlloc_1105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1105_, 0, v_a_1099_);
v___x_1104_ = v_reuseFailAlloc_1105_;
goto v_reusejp_1103_;
}
v_reusejp_1103_:
{
return v___x_1104_;
}
}
}
}
}
}
else
{
lean_object* v_a_1108_; lean_object* v___x_1110_; uint8_t v_isShared_1111_; uint8_t v_isSharedCheck_1115_; 
lean_dec_ref(v_arg_994_);
v_a_1108_ = lean_ctor_get(v___x_1067_, 0);
v_isSharedCheck_1115_ = !lean_is_exclusive(v___x_1067_);
if (v_isSharedCheck_1115_ == 0)
{
v___x_1110_ = v___x_1067_;
v_isShared_1111_ = v_isSharedCheck_1115_;
goto v_resetjp_1109_;
}
else
{
lean_inc(v_a_1108_);
lean_dec(v___x_1067_);
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
else
{
lean_object* v___x_1116_; 
lean_dec_ref(v___x_1000_);
lean_dec_ref(v_arg_994_);
lean_del_object(v___x_985_);
v___x_1116_ = l_Lean_Meta_getNatValue_x3f(v_arg_997_, v_a_977_, v_a_978_, v_a_979_, v_a_980_);
lean_dec_ref(v_arg_997_);
if (lean_obj_tag(v___x_1116_) == 0)
{
lean_object* v_a_1117_; lean_object* v___x_1119_; uint8_t v_isShared_1120_; uint8_t v_isSharedCheck_1137_; 
v_a_1117_ = lean_ctor_get(v___x_1116_, 0);
v_isSharedCheck_1137_ = !lean_is_exclusive(v___x_1116_);
if (v_isSharedCheck_1137_ == 0)
{
v___x_1119_ = v___x_1116_;
v_isShared_1120_ = v_isSharedCheck_1137_;
goto v_resetjp_1118_;
}
else
{
lean_inc(v_a_1117_);
lean_dec(v___x_1116_);
v___x_1119_ = lean_box(0);
v_isShared_1120_ = v_isSharedCheck_1137_;
goto v_resetjp_1118_;
}
v_resetjp_1118_:
{
if (lean_obj_tag(v_a_1117_) == 1)
{
lean_object* v_val_1121_; lean_object* v___x_1123_; uint8_t v_isShared_1124_; uint8_t v_isSharedCheck_1132_; 
v_val_1121_ = lean_ctor_get(v_a_1117_, 0);
v_isSharedCheck_1132_ = !lean_is_exclusive(v_a_1117_);
if (v_isSharedCheck_1132_ == 0)
{
v___x_1123_ = v_a_1117_;
v_isShared_1124_ = v_isSharedCheck_1132_;
goto v_resetjp_1122_;
}
else
{
lean_inc(v_val_1121_);
lean_dec(v_a_1117_);
v___x_1123_ = lean_box(0);
v_isShared_1124_ = v_isSharedCheck_1132_;
goto v_resetjp_1122_;
}
v_resetjp_1122_:
{
lean_object* v___x_1125_; lean_object* v___x_1127_; 
v___x_1125_ = lean_nat_to_int(v_val_1121_);
if (v_isShared_1124_ == 0)
{
lean_ctor_set(v___x_1123_, 0, v___x_1125_);
v___x_1127_ = v___x_1123_;
goto v_reusejp_1126_;
}
else
{
lean_object* v_reuseFailAlloc_1131_; 
v_reuseFailAlloc_1131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1131_, 0, v___x_1125_);
v___x_1127_ = v_reuseFailAlloc_1131_;
goto v_reusejp_1126_;
}
v_reusejp_1126_:
{
lean_object* v___x_1129_; 
if (v_isShared_1120_ == 0)
{
lean_ctor_set(v___x_1119_, 0, v___x_1127_);
v___x_1129_ = v___x_1119_;
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
lean_object* v___x_1133_; lean_object* v___x_1135_; 
lean_dec(v_a_1117_);
v___x_1133_ = lean_box(0);
if (v_isShared_1120_ == 0)
{
lean_ctor_set(v___x_1119_, 0, v___x_1133_);
v___x_1135_ = v___x_1119_;
goto v_reusejp_1134_;
}
else
{
lean_object* v_reuseFailAlloc_1136_; 
v_reuseFailAlloc_1136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1136_, 0, v___x_1133_);
v___x_1135_ = v_reuseFailAlloc_1136_;
goto v_reusejp_1134_;
}
v_reusejp_1134_:
{
return v___x_1135_;
}
}
}
}
else
{
lean_object* v_a_1138_; lean_object* v___x_1140_; uint8_t v_isShared_1141_; uint8_t v_isSharedCheck_1145_; 
v_a_1138_ = lean_ctor_get(v___x_1116_, 0);
v_isSharedCheck_1145_ = !lean_is_exclusive(v___x_1116_);
if (v_isSharedCheck_1145_ == 0)
{
v___x_1140_ = v___x_1116_;
v_isShared_1141_ = v_isSharedCheck_1145_;
goto v_resetjp_1139_;
}
else
{
lean_inc(v_a_1138_);
lean_dec(v___x_1116_);
v___x_1140_ = lean_box(0);
v_isShared_1141_ = v_isSharedCheck_1145_;
goto v_resetjp_1139_;
}
v_resetjp_1139_:
{
lean_object* v___x_1143_; 
if (v_isShared_1141_ == 0)
{
v___x_1143_ = v___x_1140_;
goto v_reusejp_1142_;
}
else
{
lean_object* v_reuseFailAlloc_1144_; 
v_reuseFailAlloc_1144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1144_, 0, v_a_1138_);
v___x_1143_ = v_reuseFailAlloc_1144_;
goto v_reusejp_1142_;
}
v_reusejp_1142_:
{
return v___x_1143_;
}
}
}
}
}
}
}
v___jp_987_:
{
lean_object* v___x_988_; lean_object* v___x_990_; 
v___x_988_ = lean_box(0);
if (v_isShared_986_ == 0)
{
lean_ctor_set(v___x_985_, 0, v___x_988_);
v___x_990_ = v___x_985_;
goto v_reusejp_989_;
}
else
{
lean_object* v_reuseFailAlloc_991_; 
v_reuseFailAlloc_991_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_991_, 0, v___x_988_);
v___x_990_ = v_reuseFailAlloc_991_;
goto v_reusejp_989_;
}
v_reusejp_989_:
{
return v___x_990_;
}
}
}
}
else
{
lean_object* v_a_1147_; lean_object* v___x_1149_; uint8_t v_isShared_1150_; uint8_t v_isSharedCheck_1154_; 
v_a_1147_ = lean_ctor_get(v___x_982_, 0);
v_isSharedCheck_1154_ = !lean_is_exclusive(v___x_982_);
if (v_isSharedCheck_1154_ == 0)
{
v___x_1149_ = v___x_982_;
v_isShared_1150_ = v_isSharedCheck_1154_;
goto v_resetjp_1148_;
}
else
{
lean_inc(v_a_1147_);
lean_dec(v___x_982_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f___boxed(lean_object* v_e_1155_, lean_object* v_a_1156_, lean_object* v_a_1157_, lean_object* v_a_1158_, lean_object* v_a_1159_, lean_object* v_a_1160_, lean_object* v_a_1161_, lean_object* v_a_1162_, lean_object* v_a_1163_, lean_object* v_a_1164_, lean_object* v_a_1165_, lean_object* v_a_1166_, lean_object* v_a_1167_){
_start:
{
lean_object* v_res_1168_; 
v_res_1168_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f(v_e_1155_, v_a_1156_, v_a_1157_, v_a_1158_, v_a_1159_, v_a_1160_, v_a_1161_, v_a_1162_, v_a_1163_, v_a_1164_, v_a_1165_, v_a_1166_);
lean_dec(v_a_1166_);
lean_dec_ref(v_a_1165_);
lean_dec(v_a_1164_);
lean_dec_ref(v_a_1163_);
lean_dec(v_a_1162_);
lean_dec_ref(v_a_1161_);
lean_dec(v_a_1160_);
lean_dec_ref(v_a_1159_);
lean_dec(v_a_1158_);
lean_dec(v_a_1157_);
lean_dec_ref(v_a_1156_);
return v_res_1168_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_getNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isNatCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__2_spec__4_spec__6(lean_object* v_u_1169_, lean_object* v_type_1170_, lean_object* v_semiringInst_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_){
_start:
{
lean_object* v___x_1184_; 
v___x_1184_ = l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_getNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isNatCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__2_spec__4_spec__6___redArg(v_u_1169_, v_type_1170_, v_semiringInst_1171_, v___y_1177_, v___y_1178_, v___y_1179_, v___y_1180_, v___y_1181_, v___y_1182_);
return v___x_1184_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_getNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isNatCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__2_spec__4_spec__6___boxed(lean_object* v_u_1185_, lean_object* v_type_1186_, lean_object* v_semiringInst_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_){
_start:
{
lean_object* v_res_1200_; 
v_res_1200_ = l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_getNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isNatCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__2_spec__4_spec__6(v_u_1185_, v_type_1186_, v_semiringInst_1187_, v___y_1188_, v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_, v___y_1193_, v___y_1194_, v___y_1195_, v___y_1196_, v___y_1197_, v___y_1198_);
lean_dec(v___y_1198_);
lean_dec_ref(v___y_1197_);
lean_dec(v___y_1196_);
lean_dec_ref(v___y_1195_);
lean_dec(v___y_1194_);
lean_dec_ref(v___y_1193_);
lean_dec(v___y_1192_);
lean_dec_ref(v___y_1191_);
lean_dec(v___y_1190_);
lean_dec(v___y_1189_);
lean_dec_ref(v___y_1188_);
return v_res_1200_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1_spec__5_spec__8(lean_object* v_00_u03b1_1201_, lean_object* v_msg_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_){
_start:
{
lean_object* v___x_1215_; 
v___x_1215_ = l_Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1_spec__5_spec__8___redArg(v_msg_1202_, v___y_1210_, v___y_1211_, v___y_1212_, v___y_1213_);
return v___x_1215_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1_spec__5_spec__8___boxed(lean_object* v_00_u03b1_1216_, lean_object* v_msg_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_){
_start:
{
lean_object* v_res_1230_; 
v_res_1230_ = l_Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1_spec__5_spec__8(v_00_u03b1_1216_, v_msg_1217_, v___y_1218_, v___y_1219_, v___y_1220_, v___y_1221_, v___y_1222_, v___y_1223_, v___y_1224_, v___y_1225_, v___y_1226_, v___y_1227_, v___y_1228_);
lean_dec(v___y_1228_);
lean_dec_ref(v___y_1227_);
lean_dec(v___y_1226_);
lean_dec_ref(v___y_1225_);
lean_dec(v___y_1224_);
lean_dec_ref(v___y_1223_);
lean_dec(v___y_1222_);
lean_dec_ref(v___y_1221_);
lean_dec(v___y_1220_);
lean_dec(v___y_1219_);
lean_dec_ref(v___y_1218_);
return v_res_1230_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___lam__0(lean_object* v_a_1231_, lean_object* v_s_1232_){
_start:
{
lean_object* v_toRing_1233_; lean_object* v_semiringId_x3f_1234_; lean_object* v_commSemiringInst_1235_; lean_object* v_commRingInst_1236_; lean_object* v_noZeroDivInst_x3f_1237_; lean_object* v_fieldInst_x3f_1238_; lean_object* v_powIdentityInst_x3f_1239_; lean_object* v_denoteEntries_1240_; lean_object* v_nextId_1241_; lean_object* v_steps_1242_; lean_object* v_queue_1243_; lean_object* v_basis_1244_; lean_object* v_diseqs_1245_; uint8_t v_recheck_1246_; lean_object* v_invSet_1247_; lean_object* v_powIdentityVarCount_1248_; lean_object* v_numEq0_x3f_1249_; uint8_t v_numEq0Updated_1250_; lean_object* v___x_1252_; uint8_t v_isShared_1253_; uint8_t v_isSharedCheck_1258_; 
v_toRing_1233_ = lean_ctor_get(v_s_1232_, 0);
v_semiringId_x3f_1234_ = lean_ctor_get(v_s_1232_, 2);
v_commSemiringInst_1235_ = lean_ctor_get(v_s_1232_, 3);
v_commRingInst_1236_ = lean_ctor_get(v_s_1232_, 4);
v_noZeroDivInst_x3f_1237_ = lean_ctor_get(v_s_1232_, 5);
v_fieldInst_x3f_1238_ = lean_ctor_get(v_s_1232_, 6);
v_powIdentityInst_x3f_1239_ = lean_ctor_get(v_s_1232_, 7);
v_denoteEntries_1240_ = lean_ctor_get(v_s_1232_, 8);
v_nextId_1241_ = lean_ctor_get(v_s_1232_, 9);
v_steps_1242_ = lean_ctor_get(v_s_1232_, 10);
v_queue_1243_ = lean_ctor_get(v_s_1232_, 11);
v_basis_1244_ = lean_ctor_get(v_s_1232_, 12);
v_diseqs_1245_ = lean_ctor_get(v_s_1232_, 13);
v_recheck_1246_ = lean_ctor_get_uint8(v_s_1232_, sizeof(void*)*17);
v_invSet_1247_ = lean_ctor_get(v_s_1232_, 14);
v_powIdentityVarCount_1248_ = lean_ctor_get(v_s_1232_, 15);
v_numEq0_x3f_1249_ = lean_ctor_get(v_s_1232_, 16);
v_numEq0Updated_1250_ = lean_ctor_get_uint8(v_s_1232_, sizeof(void*)*17 + 1);
v_isSharedCheck_1258_ = !lean_is_exclusive(v_s_1232_);
if (v_isSharedCheck_1258_ == 0)
{
lean_object* v_unused_1259_; 
v_unused_1259_ = lean_ctor_get(v_s_1232_, 1);
lean_dec(v_unused_1259_);
v___x_1252_ = v_s_1232_;
v_isShared_1253_ = v_isSharedCheck_1258_;
goto v_resetjp_1251_;
}
else
{
lean_inc(v_numEq0_x3f_1249_);
lean_inc(v_powIdentityVarCount_1248_);
lean_inc(v_invSet_1247_);
lean_inc(v_diseqs_1245_);
lean_inc(v_basis_1244_);
lean_inc(v_queue_1243_);
lean_inc(v_steps_1242_);
lean_inc(v_nextId_1241_);
lean_inc(v_denoteEntries_1240_);
lean_inc(v_powIdentityInst_x3f_1239_);
lean_inc(v_fieldInst_x3f_1238_);
lean_inc(v_noZeroDivInst_x3f_1237_);
lean_inc(v_commRingInst_1236_);
lean_inc(v_commSemiringInst_1235_);
lean_inc(v_semiringId_x3f_1234_);
lean_inc(v_toRing_1233_);
lean_dec(v_s_1232_);
v___x_1252_ = lean_box(0);
v_isShared_1253_ = v_isSharedCheck_1258_;
goto v_resetjp_1251_;
}
v_resetjp_1251_:
{
lean_object* v___x_1254_; lean_object* v___x_1256_; 
v___x_1254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1254_, 0, v_a_1231_);
if (v_isShared_1253_ == 0)
{
lean_ctor_set(v___x_1252_, 1, v___x_1254_);
v___x_1256_ = v___x_1252_;
goto v_reusejp_1255_;
}
else
{
lean_object* v_reuseFailAlloc_1257_; 
v_reuseFailAlloc_1257_ = lean_alloc_ctor(0, 17, 2);
lean_ctor_set(v_reuseFailAlloc_1257_, 0, v_toRing_1233_);
lean_ctor_set(v_reuseFailAlloc_1257_, 1, v___x_1254_);
lean_ctor_set(v_reuseFailAlloc_1257_, 2, v_semiringId_x3f_1234_);
lean_ctor_set(v_reuseFailAlloc_1257_, 3, v_commSemiringInst_1235_);
lean_ctor_set(v_reuseFailAlloc_1257_, 4, v_commRingInst_1236_);
lean_ctor_set(v_reuseFailAlloc_1257_, 5, v_noZeroDivInst_x3f_1237_);
lean_ctor_set(v_reuseFailAlloc_1257_, 6, v_fieldInst_x3f_1238_);
lean_ctor_set(v_reuseFailAlloc_1257_, 7, v_powIdentityInst_x3f_1239_);
lean_ctor_set(v_reuseFailAlloc_1257_, 8, v_denoteEntries_1240_);
lean_ctor_set(v_reuseFailAlloc_1257_, 9, v_nextId_1241_);
lean_ctor_set(v_reuseFailAlloc_1257_, 10, v_steps_1242_);
lean_ctor_set(v_reuseFailAlloc_1257_, 11, v_queue_1243_);
lean_ctor_set(v_reuseFailAlloc_1257_, 12, v_basis_1244_);
lean_ctor_set(v_reuseFailAlloc_1257_, 13, v_diseqs_1245_);
lean_ctor_set(v_reuseFailAlloc_1257_, 14, v_invSet_1247_);
lean_ctor_set(v_reuseFailAlloc_1257_, 15, v_powIdentityVarCount_1248_);
lean_ctor_set(v_reuseFailAlloc_1257_, 16, v_numEq0_x3f_1249_);
lean_ctor_set_uint8(v_reuseFailAlloc_1257_, sizeof(void*)*17, v_recheck_1246_);
lean_ctor_set_uint8(v_reuseFailAlloc_1257_, sizeof(void*)*17 + 1, v_numEq0Updated_1250_);
v___x_1256_ = v_reuseFailAlloc_1257_;
goto v_reusejp_1255_;
}
v_reusejp_1255_:
{
return v___x_1256_;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___closed__8(void){
_start:
{
lean_object* v___x_1275_; lean_object* v___x_1276_; 
v___x_1275_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___closed__7));
v___x_1276_ = l_Lean_stringToMessageData(v___x_1275_);
return v___x_1276_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0(lean_object* v___y_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_){
_start:
{
lean_object* v___x_1289_; 
v___x_1289_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v___y_1277_, v___y_1278_, v___y_1279_, v___y_1280_, v___y_1281_, v___y_1282_, v___y_1283_, v___y_1284_, v___y_1285_, v___y_1286_, v___y_1287_);
if (lean_obj_tag(v___x_1289_) == 0)
{
lean_object* v_a_1290_; lean_object* v___x_1292_; uint8_t v_isShared_1293_; uint8_t v_isSharedCheck_1337_; 
v_a_1290_ = lean_ctor_get(v___x_1289_, 0);
v_isSharedCheck_1337_ = !lean_is_exclusive(v___x_1289_);
if (v_isSharedCheck_1337_ == 0)
{
v___x_1292_ = v___x_1289_;
v_isShared_1293_ = v_isSharedCheck_1337_;
goto v_resetjp_1291_;
}
else
{
lean_inc(v_a_1290_);
lean_dec(v___x_1289_);
v___x_1292_ = lean_box(0);
v_isShared_1293_ = v_isSharedCheck_1337_;
goto v_resetjp_1291_;
}
v_resetjp_1291_:
{
lean_object* v_fieldInst_x3f_1294_; 
v_fieldInst_x3f_1294_ = lean_ctor_get(v_a_1290_, 6);
if (lean_obj_tag(v_fieldInst_x3f_1294_) == 1)
{
lean_object* v_invFn_x3f_1295_; 
lean_inc_ref(v_fieldInst_x3f_1294_);
v_invFn_x3f_1295_ = lean_ctor_get(v_a_1290_, 1);
if (lean_obj_tag(v_invFn_x3f_1295_) == 1)
{
lean_object* v_val_1296_; lean_object* v___x_1298_; 
lean_inc_ref(v_invFn_x3f_1295_);
lean_dec_ref(v_fieldInst_x3f_1294_);
lean_dec(v_a_1290_);
v_val_1296_ = lean_ctor_get(v_invFn_x3f_1295_, 0);
lean_inc(v_val_1296_);
lean_dec_ref(v_invFn_x3f_1295_);
if (v_isShared_1293_ == 0)
{
lean_ctor_set(v___x_1292_, 0, v_val_1296_);
v___x_1298_ = v___x_1292_;
goto v_reusejp_1297_;
}
else
{
lean_object* v_reuseFailAlloc_1299_; 
v_reuseFailAlloc_1299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1299_, 0, v_val_1296_);
v___x_1298_ = v_reuseFailAlloc_1299_;
goto v_reusejp_1297_;
}
v_reusejp_1297_:
{
return v___x_1298_;
}
}
else
{
lean_object* v_toRing_1300_; lean_object* v_val_1301_; lean_object* v_type_1302_; lean_object* v_u_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v_expectedInst_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; 
lean_del_object(v___x_1292_);
v_toRing_1300_ = lean_ctor_get(v_a_1290_, 0);
lean_inc_ref(v_toRing_1300_);
lean_dec(v_a_1290_);
v_val_1301_ = lean_ctor_get(v_fieldInst_x3f_1294_, 0);
lean_inc(v_val_1301_);
lean_dec_ref(v_fieldInst_x3f_1294_);
v_type_1302_ = lean_ctor_get(v_toRing_1300_, 1);
lean_inc_ref_n(v_type_1302_, 2);
v_u_1303_ = lean_ctor_get(v_toRing_1300_, 2);
lean_inc_n(v_u_1303_, 2);
lean_dec_ref(v_toRing_1300_);
v___x_1304_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___closed__2));
v___x_1305_ = lean_box(0);
v___x_1306_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1306_, 0, v_u_1303_);
lean_ctor_set(v___x_1306_, 1, v___x_1305_);
v___x_1307_ = l_Lean_mkConst(v___x_1304_, v___x_1306_);
v_expectedInst_1308_ = l_Lean_mkAppB(v___x_1307_, v_type_1302_, v_val_1301_);
v___x_1309_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___closed__4));
v___x_1310_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___closed__6));
v___x_1311_ = l_Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1(v_type_1302_, v_u_1303_, v___x_1309_, v___x_1310_, v_expectedInst_1308_, v___y_1277_, v___y_1278_, v___y_1279_, v___y_1280_, v___y_1281_, v___y_1282_, v___y_1283_, v___y_1284_, v___y_1285_, v___y_1286_, v___y_1287_);
if (lean_obj_tag(v___x_1311_) == 0)
{
lean_object* v_a_1312_; lean_object* v___f_1313_; lean_object* v___x_1314_; 
v_a_1312_ = lean_ctor_get(v___x_1311_, 0);
lean_inc_n(v_a_1312_, 2);
lean_dec_ref(v___x_1311_);
v___f_1313_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___lam__0), 2, 1);
lean_closure_set(v___f_1313_, 0, v_a_1312_);
v___x_1314_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(v___f_1313_, v___y_1277_, v___y_1278_);
if (lean_obj_tag(v___x_1314_) == 0)
{
lean_object* v___x_1316_; uint8_t v_isShared_1317_; uint8_t v_isSharedCheck_1321_; 
v_isSharedCheck_1321_ = !lean_is_exclusive(v___x_1314_);
if (v_isSharedCheck_1321_ == 0)
{
lean_object* v_unused_1322_; 
v_unused_1322_ = lean_ctor_get(v___x_1314_, 0);
lean_dec(v_unused_1322_);
v___x_1316_ = v___x_1314_;
v_isShared_1317_ = v_isSharedCheck_1321_;
goto v_resetjp_1315_;
}
else
{
lean_dec(v___x_1314_);
v___x_1316_ = lean_box(0);
v_isShared_1317_ = v_isSharedCheck_1321_;
goto v_resetjp_1315_;
}
v_resetjp_1315_:
{
lean_object* v___x_1319_; 
if (v_isShared_1317_ == 0)
{
lean_ctor_set(v___x_1316_, 0, v_a_1312_);
v___x_1319_ = v___x_1316_;
goto v_reusejp_1318_;
}
else
{
lean_object* v_reuseFailAlloc_1320_; 
v_reuseFailAlloc_1320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1320_, 0, v_a_1312_);
v___x_1319_ = v_reuseFailAlloc_1320_;
goto v_reusejp_1318_;
}
v_reusejp_1318_:
{
return v___x_1319_;
}
}
}
else
{
lean_object* v_a_1323_; lean_object* v___x_1325_; uint8_t v_isShared_1326_; uint8_t v_isSharedCheck_1330_; 
lean_dec(v_a_1312_);
v_a_1323_ = lean_ctor_get(v___x_1314_, 0);
v_isSharedCheck_1330_ = !lean_is_exclusive(v___x_1314_);
if (v_isSharedCheck_1330_ == 0)
{
v___x_1325_ = v___x_1314_;
v_isShared_1326_ = v_isSharedCheck_1330_;
goto v_resetjp_1324_;
}
else
{
lean_inc(v_a_1323_);
lean_dec(v___x_1314_);
v___x_1325_ = lean_box(0);
v_isShared_1326_ = v_isSharedCheck_1330_;
goto v_resetjp_1324_;
}
v_resetjp_1324_:
{
lean_object* v___x_1328_; 
if (v_isShared_1326_ == 0)
{
v___x_1328_ = v___x_1325_;
goto v_reusejp_1327_;
}
else
{
lean_object* v_reuseFailAlloc_1329_; 
v_reuseFailAlloc_1329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1329_, 0, v_a_1323_);
v___x_1328_ = v_reuseFailAlloc_1329_;
goto v_reusejp_1327_;
}
v_reusejp_1327_:
{
return v___x_1328_;
}
}
}
}
else
{
return v___x_1311_;
}
}
}
else
{
lean_object* v_toRing_1331_; lean_object* v_type_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; 
lean_del_object(v___x_1292_);
v_toRing_1331_ = lean_ctor_get(v_a_1290_, 0);
lean_inc_ref(v_toRing_1331_);
lean_dec(v_a_1290_);
v_type_1332_ = lean_ctor_get(v_toRing_1331_, 1);
lean_inc_ref(v_type_1332_);
lean_dec_ref(v_toRing_1331_);
v___x_1333_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___closed__8, &l_Lean_Meta_Grind_Arith_CommRing_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___closed__8_once, _init_l_Lean_Meta_Grind_Arith_CommRing_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___closed__8);
v___x_1334_ = l_Lean_indentExpr(v_type_1332_);
v___x_1335_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1335_, 0, v___x_1333_);
lean_ctor_set(v___x_1335_, 1, v___x_1334_);
v___x_1336_ = l_Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1_spec__5_spec__8___redArg(v___x_1335_, v___y_1284_, v___y_1285_, v___y_1286_, v___y_1287_);
return v___x_1336_;
}
}
}
else
{
lean_object* v_a_1338_; lean_object* v___x_1340_; uint8_t v_isShared_1341_; uint8_t v_isSharedCheck_1345_; 
v_a_1338_ = lean_ctor_get(v___x_1289_, 0);
v_isSharedCheck_1345_ = !lean_is_exclusive(v___x_1289_);
if (v_isSharedCheck_1345_ == 0)
{
v___x_1340_ = v___x_1289_;
v_isShared_1341_ = v_isSharedCheck_1345_;
goto v_resetjp_1339_;
}
else
{
lean_inc(v_a_1338_);
lean_dec(v___x_1289_);
v___x_1340_ = lean_box(0);
v_isShared_1341_ = v_isSharedCheck_1345_;
goto v_resetjp_1339_;
}
v_resetjp_1339_:
{
lean_object* v___x_1343_; 
if (v_isShared_1341_ == 0)
{
v___x_1343_ = v___x_1340_;
goto v_reusejp_1342_;
}
else
{
lean_object* v_reuseFailAlloc_1344_; 
v_reuseFailAlloc_1344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1344_, 0, v_a_1338_);
v___x_1343_ = v_reuseFailAlloc_1344_;
goto v_reusejp_1342_;
}
v_reusejp_1342_:
{
return v___x_1343_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___boxed(lean_object* v___y_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_){
_start:
{
lean_object* v_res_1358_; 
v_res_1358_ = l_Lean_Meta_Grind_Arith_CommRing_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0(v___y_1346_, v___y_1347_, v___y_1348_, v___y_1349_, v___y_1350_, v___y_1351_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_, v___y_1356_);
lean_dec(v___y_1356_);
lean_dec_ref(v___y_1355_);
lean_dec(v___y_1354_);
lean_dec_ref(v___y_1353_);
lean_dec(v___y_1352_);
lean_dec_ref(v___y_1351_);
lean_dec(v___y_1350_);
lean_dec_ref(v___y_1349_);
lean_dec(v___y_1348_);
lean_dec(v___y_1347_);
lean_dec_ref(v___y_1346_);
return v_res_1358_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst(lean_object* v_inst_1359_, lean_object* v_a_1360_, lean_object* v_a_1361_, lean_object* v_a_1362_, lean_object* v_a_1363_, lean_object* v_a_1364_, lean_object* v_a_1365_, lean_object* v_a_1366_, lean_object* v_a_1367_, lean_object* v_a_1368_, lean_object* v_a_1369_, lean_object* v_a_1370_){
_start:
{
lean_object* v___x_1372_; 
v___x_1372_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v_a_1360_, v_a_1361_, v_a_1362_, v_a_1363_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_, v_a_1368_, v_a_1369_, v_a_1370_);
if (lean_obj_tag(v___x_1372_) == 0)
{
lean_object* v_a_1373_; lean_object* v___x_1375_; uint8_t v_isShared_1376_; uint8_t v_isSharedCheck_1403_; 
v_a_1373_ = lean_ctor_get(v___x_1372_, 0);
v_isSharedCheck_1403_ = !lean_is_exclusive(v___x_1372_);
if (v_isSharedCheck_1403_ == 0)
{
v___x_1375_ = v___x_1372_;
v_isShared_1376_ = v_isSharedCheck_1403_;
goto v_resetjp_1374_;
}
else
{
lean_inc(v_a_1373_);
lean_dec(v___x_1372_);
v___x_1375_ = lean_box(0);
v_isShared_1376_ = v_isSharedCheck_1403_;
goto v_resetjp_1374_;
}
v_resetjp_1374_:
{
lean_object* v_fieldInst_x3f_1377_; 
v_fieldInst_x3f_1377_ = lean_ctor_get(v_a_1373_, 6);
lean_inc(v_fieldInst_x3f_1377_);
lean_dec(v_a_1373_);
if (lean_obj_tag(v_fieldInst_x3f_1377_) == 0)
{
uint8_t v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1381_; 
v___x_1378_ = 0;
v___x_1379_ = lean_box(v___x_1378_);
if (v_isShared_1376_ == 0)
{
lean_ctor_set(v___x_1375_, 0, v___x_1379_);
v___x_1381_ = v___x_1375_;
goto v_reusejp_1380_;
}
else
{
lean_object* v_reuseFailAlloc_1382_; 
v_reuseFailAlloc_1382_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1382_, 0, v___x_1379_);
v___x_1381_ = v_reuseFailAlloc_1382_;
goto v_reusejp_1380_;
}
v_reusejp_1380_:
{
return v___x_1381_;
}
}
else
{
lean_object* v___x_1383_; 
lean_dec_ref(v_fieldInst_x3f_1377_);
lean_del_object(v___x_1375_);
v___x_1383_ = l_Lean_Meta_Grind_Arith_CommRing_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0(v_a_1360_, v_a_1361_, v_a_1362_, v_a_1363_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_, v_a_1368_, v_a_1369_, v_a_1370_);
if (lean_obj_tag(v___x_1383_) == 0)
{
lean_object* v_a_1384_; lean_object* v___x_1386_; uint8_t v_isShared_1387_; uint8_t v_isSharedCheck_1394_; 
v_a_1384_ = lean_ctor_get(v___x_1383_, 0);
v_isSharedCheck_1394_ = !lean_is_exclusive(v___x_1383_);
if (v_isSharedCheck_1394_ == 0)
{
v___x_1386_ = v___x_1383_;
v_isShared_1387_ = v_isSharedCheck_1394_;
goto v_resetjp_1385_;
}
else
{
lean_inc(v_a_1384_);
lean_dec(v___x_1383_);
v___x_1386_ = lean_box(0);
v_isShared_1387_ = v_isSharedCheck_1394_;
goto v_resetjp_1385_;
}
v_resetjp_1385_:
{
lean_object* v___x_1388_; uint8_t v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1392_; 
v___x_1388_ = l_Lean_Expr_appArg_x21(v_a_1384_);
lean_dec(v_a_1384_);
v___x_1389_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v___x_1388_, v_inst_1359_);
lean_dec_ref(v___x_1388_);
v___x_1390_ = lean_box(v___x_1389_);
if (v_isShared_1387_ == 0)
{
lean_ctor_set(v___x_1386_, 0, v___x_1390_);
v___x_1392_ = v___x_1386_;
goto v_reusejp_1391_;
}
else
{
lean_object* v_reuseFailAlloc_1393_; 
v_reuseFailAlloc_1393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1393_, 0, v___x_1390_);
v___x_1392_ = v_reuseFailAlloc_1393_;
goto v_reusejp_1391_;
}
v_reusejp_1391_:
{
return v___x_1392_;
}
}
}
else
{
lean_object* v_a_1395_; lean_object* v___x_1397_; uint8_t v_isShared_1398_; uint8_t v_isSharedCheck_1402_; 
v_a_1395_ = lean_ctor_get(v___x_1383_, 0);
v_isSharedCheck_1402_ = !lean_is_exclusive(v___x_1383_);
if (v_isSharedCheck_1402_ == 0)
{
v___x_1397_ = v___x_1383_;
v_isShared_1398_ = v_isSharedCheck_1402_;
goto v_resetjp_1396_;
}
else
{
lean_inc(v_a_1395_);
lean_dec(v___x_1383_);
v___x_1397_ = lean_box(0);
v_isShared_1398_ = v_isSharedCheck_1402_;
goto v_resetjp_1396_;
}
v_resetjp_1396_:
{
lean_object* v___x_1400_; 
if (v_isShared_1398_ == 0)
{
v___x_1400_ = v___x_1397_;
goto v_reusejp_1399_;
}
else
{
lean_object* v_reuseFailAlloc_1401_; 
v_reuseFailAlloc_1401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1401_, 0, v_a_1395_);
v___x_1400_ = v_reuseFailAlloc_1401_;
goto v_reusejp_1399_;
}
v_reusejp_1399_:
{
return v___x_1400_;
}
}
}
}
}
}
else
{
lean_object* v_a_1404_; lean_object* v___x_1406_; uint8_t v_isShared_1407_; uint8_t v_isSharedCheck_1411_; 
v_a_1404_ = lean_ctor_get(v___x_1372_, 0);
v_isSharedCheck_1411_ = !lean_is_exclusive(v___x_1372_);
if (v_isSharedCheck_1411_ == 0)
{
v___x_1406_ = v___x_1372_;
v_isShared_1407_ = v_isSharedCheck_1411_;
goto v_resetjp_1405_;
}
else
{
lean_inc(v_a_1404_);
lean_dec(v___x_1372_);
v___x_1406_ = lean_box(0);
v_isShared_1407_ = v_isSharedCheck_1411_;
goto v_resetjp_1405_;
}
v_resetjp_1405_:
{
lean_object* v___x_1409_; 
if (v_isShared_1407_ == 0)
{
v___x_1409_ = v___x_1406_;
goto v_reusejp_1408_;
}
else
{
lean_object* v_reuseFailAlloc_1410_; 
v_reuseFailAlloc_1410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1410_, 0, v_a_1404_);
v___x_1409_ = v_reuseFailAlloc_1410_;
goto v_reusejp_1408_;
}
v_reusejp_1408_:
{
return v___x_1409_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst___boxed(lean_object* v_inst_1412_, lean_object* v_a_1413_, lean_object* v_a_1414_, lean_object* v_a_1415_, lean_object* v_a_1416_, lean_object* v_a_1417_, lean_object* v_a_1418_, lean_object* v_a_1419_, lean_object* v_a_1420_, lean_object* v_a_1421_, lean_object* v_a_1422_, lean_object* v_a_1423_, lean_object* v_a_1424_){
_start:
{
lean_object* v_res_1425_; 
v_res_1425_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst(v_inst_1412_, v_a_1413_, v_a_1414_, v_a_1415_, v_a_1416_, v_a_1417_, v_a_1418_, v_a_1419_, v_a_1420_, v_a_1421_, v_a_1422_, v_a_1423_);
lean_dec(v_a_1423_);
lean_dec_ref(v_a_1422_);
lean_dec(v_a_1421_);
lean_dec_ref(v_a_1420_);
lean_dec(v_a_1419_);
lean_dec_ref(v_a_1418_);
lean_dec(v_a_1417_);
lean_dec_ref(v_a_1416_);
lean_dec(v_a_1415_);
lean_dec(v_a_1414_);
lean_dec_ref(v_a_1413_);
lean_dec_ref(v_inst_1412_);
return v_res_1425_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__2(lean_object* v_a_1426_){
_start:
{
lean_object* v___x_1427_; 
v___x_1427_ = lean_nat_to_int(v_a_1426_);
return v___x_1427_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0_spec__2_spec__6___redArg(lean_object* v_x_1428_, lean_object* v_x_1429_, lean_object* v_x_1430_, lean_object* v_x_1431_){
_start:
{
lean_object* v_ks_1432_; lean_object* v_vs_1433_; lean_object* v___x_1435_; uint8_t v_isShared_1436_; uint8_t v_isSharedCheck_1457_; 
v_ks_1432_ = lean_ctor_get(v_x_1428_, 0);
v_vs_1433_ = lean_ctor_get(v_x_1428_, 1);
v_isSharedCheck_1457_ = !lean_is_exclusive(v_x_1428_);
if (v_isSharedCheck_1457_ == 0)
{
v___x_1435_ = v_x_1428_;
v_isShared_1436_ = v_isSharedCheck_1457_;
goto v_resetjp_1434_;
}
else
{
lean_inc(v_vs_1433_);
lean_inc(v_ks_1432_);
lean_dec(v_x_1428_);
v___x_1435_ = lean_box(0);
v_isShared_1436_ = v_isSharedCheck_1457_;
goto v_resetjp_1434_;
}
v_resetjp_1434_:
{
lean_object* v___x_1437_; uint8_t v___x_1438_; 
v___x_1437_ = lean_array_get_size(v_ks_1432_);
v___x_1438_ = lean_nat_dec_lt(v_x_1429_, v___x_1437_);
if (v___x_1438_ == 0)
{
lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1442_; 
lean_dec(v_x_1429_);
v___x_1439_ = lean_array_push(v_ks_1432_, v_x_1430_);
v___x_1440_ = lean_array_push(v_vs_1433_, v_x_1431_);
if (v_isShared_1436_ == 0)
{
lean_ctor_set(v___x_1435_, 1, v___x_1440_);
lean_ctor_set(v___x_1435_, 0, v___x_1439_);
v___x_1442_ = v___x_1435_;
goto v_reusejp_1441_;
}
else
{
lean_object* v_reuseFailAlloc_1443_; 
v_reuseFailAlloc_1443_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1443_, 0, v___x_1439_);
lean_ctor_set(v_reuseFailAlloc_1443_, 1, v___x_1440_);
v___x_1442_ = v_reuseFailAlloc_1443_;
goto v_reusejp_1441_;
}
v_reusejp_1441_:
{
return v___x_1442_;
}
}
else
{
lean_object* v_k_x27_1444_; uint8_t v___x_1445_; 
v_k_x27_1444_ = lean_array_fget_borrowed(v_ks_1432_, v_x_1429_);
v___x_1445_ = lean_expr_eqv(v_x_1430_, v_k_x27_1444_);
if (v___x_1445_ == 0)
{
lean_object* v___x_1447_; 
if (v_isShared_1436_ == 0)
{
v___x_1447_ = v___x_1435_;
goto v_reusejp_1446_;
}
else
{
lean_object* v_reuseFailAlloc_1451_; 
v_reuseFailAlloc_1451_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1451_, 0, v_ks_1432_);
lean_ctor_set(v_reuseFailAlloc_1451_, 1, v_vs_1433_);
v___x_1447_ = v_reuseFailAlloc_1451_;
goto v_reusejp_1446_;
}
v_reusejp_1446_:
{
lean_object* v___x_1448_; lean_object* v___x_1449_; 
v___x_1448_ = lean_unsigned_to_nat(1u);
v___x_1449_ = lean_nat_add(v_x_1429_, v___x_1448_);
lean_dec(v_x_1429_);
v_x_1428_ = v___x_1447_;
v_x_1429_ = v___x_1449_;
goto _start;
}
}
else
{
lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1455_; 
v___x_1452_ = lean_array_fset(v_ks_1432_, v_x_1429_, v_x_1430_);
v___x_1453_ = lean_array_fset(v_vs_1433_, v_x_1429_, v_x_1431_);
lean_dec(v_x_1429_);
if (v_isShared_1436_ == 0)
{
lean_ctor_set(v___x_1435_, 1, v___x_1453_);
lean_ctor_set(v___x_1435_, 0, v___x_1452_);
v___x_1455_ = v___x_1435_;
goto v_reusejp_1454_;
}
else
{
lean_object* v_reuseFailAlloc_1456_; 
v_reuseFailAlloc_1456_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1456_, 0, v___x_1452_);
lean_ctor_set(v_reuseFailAlloc_1456_, 1, v___x_1453_);
v___x_1455_ = v_reuseFailAlloc_1456_;
goto v_reusejp_1454_;
}
v_reusejp_1454_:
{
return v___x_1455_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0_spec__2___redArg(lean_object* v_n_1458_, lean_object* v_k_1459_, lean_object* v_v_1460_){
_start:
{
lean_object* v___x_1461_; lean_object* v___x_1462_; 
v___x_1461_ = lean_unsigned_to_nat(0u);
v___x_1462_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0_spec__2_spec__6___redArg(v_n_1458_, v___x_1461_, v_k_1459_, v_v_1460_);
return v___x_1462_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg___closed__0(void){
_start:
{
size_t v___x_1463_; size_t v___x_1464_; size_t v___x_1465_; 
v___x_1463_ = ((size_t)5ULL);
v___x_1464_ = ((size_t)1ULL);
v___x_1465_ = lean_usize_shift_left(v___x_1464_, v___x_1463_);
return v___x_1465_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_1466_; size_t v___x_1467_; size_t v___x_1468_; 
v___x_1466_ = ((size_t)1ULL);
v___x_1467_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg___closed__0);
v___x_1468_ = lean_usize_sub(v___x_1467_, v___x_1466_);
return v___x_1468_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_1469_; 
v___x_1469_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1469_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg(lean_object* v_x_1470_, size_t v_x_1471_, size_t v_x_1472_, lean_object* v_x_1473_, lean_object* v_x_1474_){
_start:
{
if (lean_obj_tag(v_x_1470_) == 0)
{
lean_object* v_es_1475_; size_t v___x_1476_; size_t v___x_1477_; size_t v___x_1478_; size_t v___x_1479_; lean_object* v_j_1480_; lean_object* v___x_1481_; uint8_t v___x_1482_; 
v_es_1475_ = lean_ctor_get(v_x_1470_, 0);
v___x_1476_ = ((size_t)5ULL);
v___x_1477_ = ((size_t)1ULL);
v___x_1478_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg___closed__1);
v___x_1479_ = lean_usize_land(v_x_1471_, v___x_1478_);
v_j_1480_ = lean_usize_to_nat(v___x_1479_);
v___x_1481_ = lean_array_get_size(v_es_1475_);
v___x_1482_ = lean_nat_dec_lt(v_j_1480_, v___x_1481_);
if (v___x_1482_ == 0)
{
lean_dec(v_j_1480_);
lean_dec(v_x_1474_);
lean_dec_ref(v_x_1473_);
return v_x_1470_;
}
else
{
lean_object* v___x_1484_; uint8_t v_isShared_1485_; uint8_t v_isSharedCheck_1519_; 
lean_inc_ref(v_es_1475_);
v_isSharedCheck_1519_ = !lean_is_exclusive(v_x_1470_);
if (v_isSharedCheck_1519_ == 0)
{
lean_object* v_unused_1520_; 
v_unused_1520_ = lean_ctor_get(v_x_1470_, 0);
lean_dec(v_unused_1520_);
v___x_1484_ = v_x_1470_;
v_isShared_1485_ = v_isSharedCheck_1519_;
goto v_resetjp_1483_;
}
else
{
lean_dec(v_x_1470_);
v___x_1484_ = lean_box(0);
v_isShared_1485_ = v_isSharedCheck_1519_;
goto v_resetjp_1483_;
}
v_resetjp_1483_:
{
lean_object* v_v_1486_; lean_object* v___x_1487_; lean_object* v_xs_x27_1488_; lean_object* v___y_1490_; 
v_v_1486_ = lean_array_fget(v_es_1475_, v_j_1480_);
v___x_1487_ = lean_box(0);
v_xs_x27_1488_ = lean_array_fset(v_es_1475_, v_j_1480_, v___x_1487_);
switch(lean_obj_tag(v_v_1486_))
{
case 0:
{
lean_object* v_key_1495_; lean_object* v_val_1496_; lean_object* v___x_1498_; uint8_t v_isShared_1499_; uint8_t v_isSharedCheck_1506_; 
v_key_1495_ = lean_ctor_get(v_v_1486_, 0);
v_val_1496_ = lean_ctor_get(v_v_1486_, 1);
v_isSharedCheck_1506_ = !lean_is_exclusive(v_v_1486_);
if (v_isSharedCheck_1506_ == 0)
{
v___x_1498_ = v_v_1486_;
v_isShared_1499_ = v_isSharedCheck_1506_;
goto v_resetjp_1497_;
}
else
{
lean_inc(v_val_1496_);
lean_inc(v_key_1495_);
lean_dec(v_v_1486_);
v___x_1498_ = lean_box(0);
v_isShared_1499_ = v_isSharedCheck_1506_;
goto v_resetjp_1497_;
}
v_resetjp_1497_:
{
uint8_t v___x_1500_; 
v___x_1500_ = lean_expr_eqv(v_x_1473_, v_key_1495_);
if (v___x_1500_ == 0)
{
lean_object* v___x_1501_; lean_object* v___x_1502_; 
lean_del_object(v___x_1498_);
v___x_1501_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1495_, v_val_1496_, v_x_1473_, v_x_1474_);
v___x_1502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1502_, 0, v___x_1501_);
v___y_1490_ = v___x_1502_;
goto v___jp_1489_;
}
else
{
lean_object* v___x_1504_; 
lean_dec(v_val_1496_);
lean_dec(v_key_1495_);
if (v_isShared_1499_ == 0)
{
lean_ctor_set(v___x_1498_, 1, v_x_1474_);
lean_ctor_set(v___x_1498_, 0, v_x_1473_);
v___x_1504_ = v___x_1498_;
goto v_reusejp_1503_;
}
else
{
lean_object* v_reuseFailAlloc_1505_; 
v_reuseFailAlloc_1505_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1505_, 0, v_x_1473_);
lean_ctor_set(v_reuseFailAlloc_1505_, 1, v_x_1474_);
v___x_1504_ = v_reuseFailAlloc_1505_;
goto v_reusejp_1503_;
}
v_reusejp_1503_:
{
v___y_1490_ = v___x_1504_;
goto v___jp_1489_;
}
}
}
}
case 1:
{
lean_object* v_node_1507_; lean_object* v___x_1509_; uint8_t v_isShared_1510_; uint8_t v_isSharedCheck_1517_; 
v_node_1507_ = lean_ctor_get(v_v_1486_, 0);
v_isSharedCheck_1517_ = !lean_is_exclusive(v_v_1486_);
if (v_isSharedCheck_1517_ == 0)
{
v___x_1509_ = v_v_1486_;
v_isShared_1510_ = v_isSharedCheck_1517_;
goto v_resetjp_1508_;
}
else
{
lean_inc(v_node_1507_);
lean_dec(v_v_1486_);
v___x_1509_ = lean_box(0);
v_isShared_1510_ = v_isSharedCheck_1517_;
goto v_resetjp_1508_;
}
v_resetjp_1508_:
{
size_t v___x_1511_; size_t v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1515_; 
v___x_1511_ = lean_usize_shift_right(v_x_1471_, v___x_1476_);
v___x_1512_ = lean_usize_add(v_x_1472_, v___x_1477_);
v___x_1513_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg(v_node_1507_, v___x_1511_, v___x_1512_, v_x_1473_, v_x_1474_);
if (v_isShared_1510_ == 0)
{
lean_ctor_set(v___x_1509_, 0, v___x_1513_);
v___x_1515_ = v___x_1509_;
goto v_reusejp_1514_;
}
else
{
lean_object* v_reuseFailAlloc_1516_; 
v_reuseFailAlloc_1516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1516_, 0, v___x_1513_);
v___x_1515_ = v_reuseFailAlloc_1516_;
goto v_reusejp_1514_;
}
v_reusejp_1514_:
{
v___y_1490_ = v___x_1515_;
goto v___jp_1489_;
}
}
}
default: 
{
lean_object* v___x_1518_; 
v___x_1518_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1518_, 0, v_x_1473_);
lean_ctor_set(v___x_1518_, 1, v_x_1474_);
v___y_1490_ = v___x_1518_;
goto v___jp_1489_;
}
}
v___jp_1489_:
{
lean_object* v___x_1491_; lean_object* v___x_1493_; 
v___x_1491_ = lean_array_fset(v_xs_x27_1488_, v_j_1480_, v___y_1490_);
lean_dec(v_j_1480_);
if (v_isShared_1485_ == 0)
{
lean_ctor_set(v___x_1484_, 0, v___x_1491_);
v___x_1493_ = v___x_1484_;
goto v_reusejp_1492_;
}
else
{
lean_object* v_reuseFailAlloc_1494_; 
v_reuseFailAlloc_1494_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1494_, 0, v___x_1491_);
v___x_1493_ = v_reuseFailAlloc_1494_;
goto v_reusejp_1492_;
}
v_reusejp_1492_:
{
return v___x_1493_;
}
}
}
}
}
else
{
lean_object* v_ks_1521_; lean_object* v_vs_1522_; lean_object* v___x_1524_; uint8_t v_isShared_1525_; uint8_t v_isSharedCheck_1542_; 
v_ks_1521_ = lean_ctor_get(v_x_1470_, 0);
v_vs_1522_ = lean_ctor_get(v_x_1470_, 1);
v_isSharedCheck_1542_ = !lean_is_exclusive(v_x_1470_);
if (v_isSharedCheck_1542_ == 0)
{
v___x_1524_ = v_x_1470_;
v_isShared_1525_ = v_isSharedCheck_1542_;
goto v_resetjp_1523_;
}
else
{
lean_inc(v_vs_1522_);
lean_inc(v_ks_1521_);
lean_dec(v_x_1470_);
v___x_1524_ = lean_box(0);
v_isShared_1525_ = v_isSharedCheck_1542_;
goto v_resetjp_1523_;
}
v_resetjp_1523_:
{
lean_object* v___x_1527_; 
if (v_isShared_1525_ == 0)
{
v___x_1527_ = v___x_1524_;
goto v_reusejp_1526_;
}
else
{
lean_object* v_reuseFailAlloc_1541_; 
v_reuseFailAlloc_1541_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1541_, 0, v_ks_1521_);
lean_ctor_set(v_reuseFailAlloc_1541_, 1, v_vs_1522_);
v___x_1527_ = v_reuseFailAlloc_1541_;
goto v_reusejp_1526_;
}
v_reusejp_1526_:
{
lean_object* v_newNode_1528_; uint8_t v___y_1530_; size_t v___x_1536_; uint8_t v___x_1537_; 
v_newNode_1528_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0_spec__2___redArg(v___x_1527_, v_x_1473_, v_x_1474_);
v___x_1536_ = ((size_t)7ULL);
v___x_1537_ = lean_usize_dec_le(v___x_1536_, v_x_1472_);
if (v___x_1537_ == 0)
{
lean_object* v___x_1538_; lean_object* v___x_1539_; uint8_t v___x_1540_; 
v___x_1538_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1528_);
v___x_1539_ = lean_unsigned_to_nat(4u);
v___x_1540_ = lean_nat_dec_lt(v___x_1538_, v___x_1539_);
lean_dec(v___x_1538_);
v___y_1530_ = v___x_1540_;
goto v___jp_1529_;
}
else
{
v___y_1530_ = v___x_1537_;
goto v___jp_1529_;
}
v___jp_1529_:
{
if (v___y_1530_ == 0)
{
lean_object* v_ks_1531_; lean_object* v_vs_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; 
v_ks_1531_ = lean_ctor_get(v_newNode_1528_, 0);
lean_inc_ref(v_ks_1531_);
v_vs_1532_ = lean_ctor_get(v_newNode_1528_, 1);
lean_inc_ref(v_vs_1532_);
lean_dec_ref(v_newNode_1528_);
v___x_1533_ = lean_unsigned_to_nat(0u);
v___x_1534_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg___closed__2);
v___x_1535_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0_spec__3___redArg(v_x_1472_, v_ks_1531_, v_vs_1532_, v___x_1533_, v___x_1534_);
lean_dec_ref(v_vs_1532_);
lean_dec_ref(v_ks_1531_);
return v___x_1535_;
}
else
{
return v_newNode_1528_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0_spec__3___redArg(size_t v_depth_1543_, lean_object* v_keys_1544_, lean_object* v_vals_1545_, lean_object* v_i_1546_, lean_object* v_entries_1547_){
_start:
{
lean_object* v___x_1548_; uint8_t v___x_1549_; 
v___x_1548_ = lean_array_get_size(v_keys_1544_);
v___x_1549_ = lean_nat_dec_lt(v_i_1546_, v___x_1548_);
if (v___x_1549_ == 0)
{
lean_dec(v_i_1546_);
return v_entries_1547_;
}
else
{
lean_object* v_k_1550_; lean_object* v_v_1551_; uint64_t v___x_1552_; size_t v_h_1553_; size_t v___x_1554_; lean_object* v___x_1555_; size_t v___x_1556_; size_t v___x_1557_; size_t v___x_1558_; size_t v_h_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; 
v_k_1550_ = lean_array_fget_borrowed(v_keys_1544_, v_i_1546_);
v_v_1551_ = lean_array_fget_borrowed(v_vals_1545_, v_i_1546_);
v___x_1552_ = l_Lean_Expr_hash(v_k_1550_);
v_h_1553_ = lean_uint64_to_usize(v___x_1552_);
v___x_1554_ = ((size_t)5ULL);
v___x_1555_ = lean_unsigned_to_nat(1u);
v___x_1556_ = ((size_t)1ULL);
v___x_1557_ = lean_usize_sub(v_depth_1543_, v___x_1556_);
v___x_1558_ = lean_usize_mul(v___x_1554_, v___x_1557_);
v_h_1559_ = lean_usize_shift_right(v_h_1553_, v___x_1558_);
v___x_1560_ = lean_nat_add(v_i_1546_, v___x_1555_);
lean_dec(v_i_1546_);
lean_inc(v_v_1551_);
lean_inc(v_k_1550_);
v___x_1561_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg(v_entries_1547_, v_h_1559_, v_depth_1543_, v_k_1550_, v_v_1551_);
v_i_1546_ = v___x_1560_;
v_entries_1547_ = v___x_1561_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_depth_1563_, lean_object* v_keys_1564_, lean_object* v_vals_1565_, lean_object* v_i_1566_, lean_object* v_entries_1567_){
_start:
{
size_t v_depth_boxed_1568_; lean_object* v_res_1569_; 
v_depth_boxed_1568_ = lean_unbox_usize(v_depth_1563_);
lean_dec(v_depth_1563_);
v_res_1569_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0_spec__3___redArg(v_depth_boxed_1568_, v_keys_1564_, v_vals_1565_, v_i_1566_, v_entries_1567_);
lean_dec_ref(v_vals_1565_);
lean_dec_ref(v_keys_1564_);
return v_res_1569_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg___boxed(lean_object* v_x_1570_, lean_object* v_x_1571_, lean_object* v_x_1572_, lean_object* v_x_1573_, lean_object* v_x_1574_){
_start:
{
size_t v_x_140604__boxed_1575_; size_t v_x_140605__boxed_1576_; lean_object* v_res_1577_; 
v_x_140604__boxed_1575_ = lean_unbox_usize(v_x_1571_);
lean_dec(v_x_1571_);
v_x_140605__boxed_1576_ = lean_unbox_usize(v_x_1572_);
lean_dec(v_x_1572_);
v_res_1577_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg(v_x_1570_, v_x_140604__boxed_1575_, v_x_140605__boxed_1576_, v_x_1573_, v_x_1574_);
return v_res_1577_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0___redArg(lean_object* v_x_1578_, lean_object* v_x_1579_, lean_object* v_x_1580_){
_start:
{
uint64_t v___x_1581_; size_t v___x_1582_; size_t v___x_1583_; lean_object* v___x_1584_; 
v___x_1581_ = l_Lean_Expr_hash(v_x_1579_);
v___x_1582_ = lean_uint64_to_usize(v___x_1581_);
v___x_1583_ = ((size_t)1ULL);
v___x_1584_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg(v_x_1578_, v___x_1582_, v___x_1583_, v_x_1579_, v_x_1580_);
return v___x_1584_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___lam__0(lean_object* v_a_1585_, lean_object* v_s_1586_){
_start:
{
lean_object* v_toRing_1587_; lean_object* v_invFn_x3f_1588_; lean_object* v_semiringId_x3f_1589_; lean_object* v_commSemiringInst_1590_; lean_object* v_commRingInst_1591_; lean_object* v_noZeroDivInst_x3f_1592_; lean_object* v_fieldInst_x3f_1593_; lean_object* v_powIdentityInst_x3f_1594_; lean_object* v_denoteEntries_1595_; lean_object* v_nextId_1596_; lean_object* v_steps_1597_; lean_object* v_queue_1598_; lean_object* v_basis_1599_; lean_object* v_diseqs_1600_; uint8_t v_recheck_1601_; lean_object* v_invSet_1602_; lean_object* v_powIdentityVarCount_1603_; lean_object* v_numEq0_x3f_1604_; uint8_t v_numEq0Updated_1605_; lean_object* v___x_1607_; uint8_t v_isShared_1608_; uint8_t v_isSharedCheck_1614_; 
v_toRing_1587_ = lean_ctor_get(v_s_1586_, 0);
v_invFn_x3f_1588_ = lean_ctor_get(v_s_1586_, 1);
v_semiringId_x3f_1589_ = lean_ctor_get(v_s_1586_, 2);
v_commSemiringInst_1590_ = lean_ctor_get(v_s_1586_, 3);
v_commRingInst_1591_ = lean_ctor_get(v_s_1586_, 4);
v_noZeroDivInst_x3f_1592_ = lean_ctor_get(v_s_1586_, 5);
v_fieldInst_x3f_1593_ = lean_ctor_get(v_s_1586_, 6);
v_powIdentityInst_x3f_1594_ = lean_ctor_get(v_s_1586_, 7);
v_denoteEntries_1595_ = lean_ctor_get(v_s_1586_, 8);
v_nextId_1596_ = lean_ctor_get(v_s_1586_, 9);
v_steps_1597_ = lean_ctor_get(v_s_1586_, 10);
v_queue_1598_ = lean_ctor_get(v_s_1586_, 11);
v_basis_1599_ = lean_ctor_get(v_s_1586_, 12);
v_diseqs_1600_ = lean_ctor_get(v_s_1586_, 13);
v_recheck_1601_ = lean_ctor_get_uint8(v_s_1586_, sizeof(void*)*17);
v_invSet_1602_ = lean_ctor_get(v_s_1586_, 14);
v_powIdentityVarCount_1603_ = lean_ctor_get(v_s_1586_, 15);
v_numEq0_x3f_1604_ = lean_ctor_get(v_s_1586_, 16);
v_numEq0Updated_1605_ = lean_ctor_get_uint8(v_s_1586_, sizeof(void*)*17 + 1);
v_isSharedCheck_1614_ = !lean_is_exclusive(v_s_1586_);
if (v_isSharedCheck_1614_ == 0)
{
v___x_1607_ = v_s_1586_;
v_isShared_1608_ = v_isSharedCheck_1614_;
goto v_resetjp_1606_;
}
else
{
lean_inc(v_numEq0_x3f_1604_);
lean_inc(v_powIdentityVarCount_1603_);
lean_inc(v_invSet_1602_);
lean_inc(v_diseqs_1600_);
lean_inc(v_basis_1599_);
lean_inc(v_queue_1598_);
lean_inc(v_steps_1597_);
lean_inc(v_nextId_1596_);
lean_inc(v_denoteEntries_1595_);
lean_inc(v_powIdentityInst_x3f_1594_);
lean_inc(v_fieldInst_x3f_1593_);
lean_inc(v_noZeroDivInst_x3f_1592_);
lean_inc(v_commRingInst_1591_);
lean_inc(v_commSemiringInst_1590_);
lean_inc(v_semiringId_x3f_1589_);
lean_inc(v_invFn_x3f_1588_);
lean_inc(v_toRing_1587_);
lean_dec(v_s_1586_);
v___x_1607_ = lean_box(0);
v_isShared_1608_ = v_isSharedCheck_1614_;
goto v_resetjp_1606_;
}
v_resetjp_1606_:
{
lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1612_; 
v___x_1609_ = lean_box(0);
v___x_1610_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0___redArg(v_invSet_1602_, v_a_1585_, v___x_1609_);
if (v_isShared_1608_ == 0)
{
lean_ctor_set(v___x_1607_, 14, v___x_1610_);
v___x_1612_ = v___x_1607_;
goto v_reusejp_1611_;
}
else
{
lean_object* v_reuseFailAlloc_1613_; 
v_reuseFailAlloc_1613_ = lean_alloc_ctor(0, 17, 2);
lean_ctor_set(v_reuseFailAlloc_1613_, 0, v_toRing_1587_);
lean_ctor_set(v_reuseFailAlloc_1613_, 1, v_invFn_x3f_1588_);
lean_ctor_set(v_reuseFailAlloc_1613_, 2, v_semiringId_x3f_1589_);
lean_ctor_set(v_reuseFailAlloc_1613_, 3, v_commSemiringInst_1590_);
lean_ctor_set(v_reuseFailAlloc_1613_, 4, v_commRingInst_1591_);
lean_ctor_set(v_reuseFailAlloc_1613_, 5, v_noZeroDivInst_x3f_1592_);
lean_ctor_set(v_reuseFailAlloc_1613_, 6, v_fieldInst_x3f_1593_);
lean_ctor_set(v_reuseFailAlloc_1613_, 7, v_powIdentityInst_x3f_1594_);
lean_ctor_set(v_reuseFailAlloc_1613_, 8, v_denoteEntries_1595_);
lean_ctor_set(v_reuseFailAlloc_1613_, 9, v_nextId_1596_);
lean_ctor_set(v_reuseFailAlloc_1613_, 10, v_steps_1597_);
lean_ctor_set(v_reuseFailAlloc_1613_, 11, v_queue_1598_);
lean_ctor_set(v_reuseFailAlloc_1613_, 12, v_basis_1599_);
lean_ctor_set(v_reuseFailAlloc_1613_, 13, v_diseqs_1600_);
lean_ctor_set(v_reuseFailAlloc_1613_, 14, v___x_1610_);
lean_ctor_set(v_reuseFailAlloc_1613_, 15, v_powIdentityVarCount_1603_);
lean_ctor_set(v_reuseFailAlloc_1613_, 16, v_numEq0_x3f_1604_);
lean_ctor_set_uint8(v_reuseFailAlloc_1613_, sizeof(void*)*17, v_recheck_1601_);
lean_ctor_set_uint8(v_reuseFailAlloc_1613_, sizeof(void*)*17 + 1, v_numEq0Updated_1605_);
v___x_1612_ = v_reuseFailAlloc_1613_;
goto v_reusejp_1611_;
}
v_reusejp_1611_:
{
return v___x_1612_;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__4___closed__1(void){
_start:
{
lean_object* v___x_1617_; lean_object* v___x_1618_; 
v___x_1617_ = lean_unsigned_to_nat(0u);
v___x_1618_ = lean_nat_to_int(v___x_1617_);
return v___x_1618_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__4(lean_object* v_k_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_){
_start:
{
lean_object* v___x_1637_; 
v___x_1637_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v___y_1625_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_, v___y_1635_);
if (lean_obj_tag(v___x_1637_) == 0)
{
lean_object* v_a_1638_; lean_object* v_toRing_1639_; lean_object* v_type_1640_; lean_object* v_u_1641_; lean_object* v_semiringInst_1642_; lean_object* v___x_1643_; lean_object* v_n_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; 
v_a_1638_ = lean_ctor_get(v___x_1637_, 0);
lean_inc(v_a_1638_);
lean_dec_ref(v___x_1637_);
v_toRing_1639_ = lean_ctor_get(v_a_1638_, 0);
lean_inc_ref(v_toRing_1639_);
lean_dec(v_a_1638_);
v_type_1640_ = lean_ctor_get(v_toRing_1639_, 1);
lean_inc_ref_n(v_type_1640_, 2);
v_u_1641_ = lean_ctor_get(v_toRing_1639_, 2);
lean_inc(v_u_1641_);
v_semiringInst_1642_ = lean_ctor_get(v_toRing_1639_, 4);
lean_inc_ref(v_semiringInst_1642_);
lean_dec_ref(v_toRing_1639_);
v___x_1643_ = lean_nat_abs(v_k_1624_);
v_n_1644_ = l_Lean_mkRawNatLit(v___x_1643_);
v___x_1645_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__4___closed__0));
v___x_1646_ = lean_box(0);
v___x_1647_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1647_, 0, v_u_1641_);
lean_ctor_set(v___x_1647_, 1, v___x_1646_);
lean_inc_ref(v___x_1647_);
v___x_1648_ = l_Lean_mkConst(v___x_1645_, v___x_1647_);
lean_inc_ref(v_n_1644_);
v___x_1649_ = l_Lean_mkAppB(v___x_1648_, v_type_1640_, v_n_1644_);
v___x_1650_ = lean_box(0);
v___x_1651_ = l_Lean_Meta_synthInstance_x3f(v___x_1649_, v___x_1650_, v___y_1632_, v___y_1633_, v___y_1634_, v___y_1635_);
if (lean_obj_tag(v___x_1651_) == 0)
{
lean_object* v_a_1652_; lean_object* v___x_1654_; uint8_t v_isShared_1655_; uint8_t v_isSharedCheck_1691_; 
v_a_1652_ = lean_ctor_get(v___x_1651_, 0);
v_isSharedCheck_1691_ = !lean_is_exclusive(v___x_1651_);
if (v_isSharedCheck_1691_ == 0)
{
v___x_1654_ = v___x_1651_;
v_isShared_1655_ = v_isSharedCheck_1691_;
goto v_resetjp_1653_;
}
else
{
lean_inc(v_a_1652_);
lean_dec(v___x_1651_);
v___x_1654_ = lean_box(0);
v_isShared_1655_ = v_isSharedCheck_1691_;
goto v_resetjp_1653_;
}
v_resetjp_1653_:
{
lean_object* v_ofNatInst_1657_; lean_object* v___y_1658_; lean_object* v___y_1659_; lean_object* v___y_1660_; lean_object* v___y_1661_; lean_object* v___y_1662_; lean_object* v___y_1663_; lean_object* v___y_1664_; lean_object* v___y_1665_; lean_object* v___y_1666_; lean_object* v___y_1667_; lean_object* v___y_1668_; 
if (lean_obj_tag(v_a_1652_) == 1)
{
lean_object* v_val_1687_; 
lean_dec_ref(v_semiringInst_1642_);
v_val_1687_ = lean_ctor_get(v_a_1652_, 0);
lean_inc(v_val_1687_);
lean_dec_ref(v_a_1652_);
v_ofNatInst_1657_ = v_val_1687_;
v___y_1658_ = v___y_1625_;
v___y_1659_ = v___y_1626_;
v___y_1660_ = v___y_1627_;
v___y_1661_ = v___y_1628_;
v___y_1662_ = v___y_1629_;
v___y_1663_ = v___y_1630_;
v___y_1664_ = v___y_1631_;
v___y_1665_ = v___y_1632_;
v___y_1666_ = v___y_1633_;
v___y_1667_ = v___y_1634_;
v___y_1668_ = v___y_1635_;
goto v___jp_1656_;
}
else
{
lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; 
lean_dec(v_a_1652_);
v___x_1688_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__4___closed__2));
lean_inc_ref(v___x_1647_);
v___x_1689_ = l_Lean_mkConst(v___x_1688_, v___x_1647_);
lean_inc_ref(v_n_1644_);
lean_inc_ref(v_type_1640_);
v___x_1690_ = l_Lean_mkApp3(v___x_1689_, v_type_1640_, v_semiringInst_1642_, v_n_1644_);
v_ofNatInst_1657_ = v___x_1690_;
v___y_1658_ = v___y_1625_;
v___y_1659_ = v___y_1626_;
v___y_1660_ = v___y_1627_;
v___y_1661_ = v___y_1628_;
v___y_1662_ = v___y_1629_;
v___y_1663_ = v___y_1630_;
v___y_1664_ = v___y_1631_;
v___y_1665_ = v___y_1632_;
v___y_1666_ = v___y_1633_;
v___y_1667_ = v___y_1634_;
v___y_1668_ = v___y_1635_;
goto v___jp_1656_;
}
v___jp_1656_:
{
lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v_n_1671_; lean_object* v___x_1672_; uint8_t v___x_1673_; 
v___x_1669_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__8));
v___x_1670_ = l_Lean_mkConst(v___x_1669_, v___x_1647_);
v_n_1671_ = l_Lean_mkApp3(v___x_1670_, v_type_1640_, v_n_1644_, v_ofNatInst_1657_);
v___x_1672_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__4___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__4___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__4___closed__1);
v___x_1673_ = lean_int_dec_lt(v_k_1624_, v___x_1672_);
if (v___x_1673_ == 0)
{
lean_object* v___x_1675_; 
if (v_isShared_1655_ == 0)
{
lean_ctor_set(v___x_1654_, 0, v_n_1671_);
v___x_1675_ = v___x_1654_;
goto v_reusejp_1674_;
}
else
{
lean_object* v_reuseFailAlloc_1676_; 
v_reuseFailAlloc_1676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1676_, 0, v_n_1671_);
v___x_1675_ = v_reuseFailAlloc_1676_;
goto v_reusejp_1674_;
}
v_reusejp_1674_:
{
return v___x_1675_;
}
}
else
{
lean_object* v___x_1677_; 
lean_del_object(v___x_1654_);
v___x_1677_ = l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0(v___y_1658_, v___y_1659_, v___y_1660_, v___y_1661_, v___y_1662_, v___y_1663_, v___y_1664_, v___y_1665_, v___y_1666_, v___y_1667_, v___y_1668_);
if (lean_obj_tag(v___x_1677_) == 0)
{
lean_object* v_a_1678_; lean_object* v___x_1680_; uint8_t v_isShared_1681_; uint8_t v_isSharedCheck_1686_; 
v_a_1678_ = lean_ctor_get(v___x_1677_, 0);
v_isSharedCheck_1686_ = !lean_is_exclusive(v___x_1677_);
if (v_isSharedCheck_1686_ == 0)
{
v___x_1680_ = v___x_1677_;
v_isShared_1681_ = v_isSharedCheck_1686_;
goto v_resetjp_1679_;
}
else
{
lean_inc(v_a_1678_);
lean_dec(v___x_1677_);
v___x_1680_ = lean_box(0);
v_isShared_1681_ = v_isSharedCheck_1686_;
goto v_resetjp_1679_;
}
v_resetjp_1679_:
{
lean_object* v___x_1682_; lean_object* v___x_1684_; 
v___x_1682_ = l_Lean_Expr_app___override(v_a_1678_, v_n_1671_);
if (v_isShared_1681_ == 0)
{
lean_ctor_set(v___x_1680_, 0, v___x_1682_);
v___x_1684_ = v___x_1680_;
goto v_reusejp_1683_;
}
else
{
lean_object* v_reuseFailAlloc_1685_; 
v_reuseFailAlloc_1685_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1685_, 0, v___x_1682_);
v___x_1684_ = v_reuseFailAlloc_1685_;
goto v_reusejp_1683_;
}
v_reusejp_1683_:
{
return v___x_1684_;
}
}
}
else
{
lean_dec_ref(v_n_1671_);
return v___x_1677_;
}
}
}
}
}
else
{
lean_object* v_a_1692_; lean_object* v___x_1694_; uint8_t v_isShared_1695_; uint8_t v_isSharedCheck_1699_; 
lean_dec_ref(v___x_1647_);
lean_dec_ref(v_n_1644_);
lean_dec_ref(v_semiringInst_1642_);
lean_dec_ref(v_type_1640_);
v_a_1692_ = lean_ctor_get(v___x_1651_, 0);
v_isSharedCheck_1699_ = !lean_is_exclusive(v___x_1651_);
if (v_isSharedCheck_1699_ == 0)
{
v___x_1694_ = v___x_1651_;
v_isShared_1695_ = v_isSharedCheck_1699_;
goto v_resetjp_1693_;
}
else
{
lean_inc(v_a_1692_);
lean_dec(v___x_1651_);
v___x_1694_ = lean_box(0);
v_isShared_1695_ = v_isSharedCheck_1699_;
goto v_resetjp_1693_;
}
v_resetjp_1693_:
{
lean_object* v___x_1697_; 
if (v_isShared_1695_ == 0)
{
v___x_1697_ = v___x_1694_;
goto v_reusejp_1696_;
}
else
{
lean_object* v_reuseFailAlloc_1698_; 
v_reuseFailAlloc_1698_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1698_, 0, v_a_1692_);
v___x_1697_ = v_reuseFailAlloc_1698_;
goto v_reusejp_1696_;
}
v_reusejp_1696_:
{
return v___x_1697_;
}
}
}
}
else
{
lean_object* v_a_1700_; lean_object* v___x_1702_; uint8_t v_isShared_1703_; uint8_t v_isSharedCheck_1707_; 
v_a_1700_ = lean_ctor_get(v___x_1637_, 0);
v_isSharedCheck_1707_ = !lean_is_exclusive(v___x_1637_);
if (v_isSharedCheck_1707_ == 0)
{
v___x_1702_ = v___x_1637_;
v_isShared_1703_ = v_isSharedCheck_1707_;
goto v_resetjp_1701_;
}
else
{
lean_inc(v_a_1700_);
lean_dec(v___x_1637_);
v___x_1702_ = lean_box(0);
v_isShared_1703_ = v_isSharedCheck_1707_;
goto v_resetjp_1701_;
}
v_resetjp_1701_:
{
lean_object* v___x_1705_; 
if (v_isShared_1703_ == 0)
{
v___x_1705_ = v___x_1702_;
goto v_reusejp_1704_;
}
else
{
lean_object* v_reuseFailAlloc_1706_; 
v_reuseFailAlloc_1706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1706_, 0, v_a_1700_);
v___x_1705_ = v_reuseFailAlloc_1706_;
goto v_reusejp_1704_;
}
v_reusejp_1704_:
{
return v___x_1705_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__4___boxed(lean_object* v_k_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_){
_start:
{
lean_object* v_res_1721_; 
v_res_1721_ = l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__4(v_k_1708_, v___y_1709_, v___y_1710_, v___y_1711_, v___y_1712_, v___y_1713_, v___y_1714_, v___y_1715_, v___y_1716_, v___y_1717_, v___y_1718_, v___y_1719_);
lean_dec(v___y_1719_);
lean_dec_ref(v___y_1718_);
lean_dec(v___y_1717_);
lean_dec_ref(v___y_1716_);
lean_dec(v___y_1715_);
lean_dec_ref(v___y_1714_);
lean_dec(v___y_1713_);
lean_dec_ref(v___y_1712_);
lean_dec(v___y_1711_);
lean_dec(v___y_1710_);
lean_dec_ref(v___y_1709_);
lean_dec(v_k_1708_);
return v_res_1721_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1_spec__2_spec__6___redArg(lean_object* v_keys_1722_, lean_object* v_i_1723_, lean_object* v_k_1724_){
_start:
{
lean_object* v___x_1725_; uint8_t v___x_1726_; 
v___x_1725_ = lean_array_get_size(v_keys_1722_);
v___x_1726_ = lean_nat_dec_lt(v_i_1723_, v___x_1725_);
if (v___x_1726_ == 0)
{
lean_dec(v_i_1723_);
return v___x_1726_;
}
else
{
lean_object* v_k_x27_1727_; uint8_t v___x_1728_; 
v_k_x27_1727_ = lean_array_fget_borrowed(v_keys_1722_, v_i_1723_);
v___x_1728_ = lean_expr_eqv(v_k_1724_, v_k_x27_1727_);
if (v___x_1728_ == 0)
{
lean_object* v___x_1729_; lean_object* v___x_1730_; 
v___x_1729_ = lean_unsigned_to_nat(1u);
v___x_1730_ = lean_nat_add(v_i_1723_, v___x_1729_);
lean_dec(v_i_1723_);
v_i_1723_ = v___x_1730_;
goto _start;
}
else
{
lean_dec(v_i_1723_);
return v___x_1728_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1_spec__2_spec__6___redArg___boxed(lean_object* v_keys_1732_, lean_object* v_i_1733_, lean_object* v_k_1734_){
_start:
{
uint8_t v_res_1735_; lean_object* v_r_1736_; 
v_res_1735_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1_spec__2_spec__6___redArg(v_keys_1732_, v_i_1733_, v_k_1734_);
lean_dec_ref(v_k_1734_);
lean_dec_ref(v_keys_1732_);
v_r_1736_ = lean_box(v_res_1735_);
return v_r_1736_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1_spec__2___redArg(lean_object* v_x_1737_, size_t v_x_1738_, lean_object* v_x_1739_){
_start:
{
if (lean_obj_tag(v_x_1737_) == 0)
{
lean_object* v_es_1740_; lean_object* v___x_1741_; size_t v___x_1742_; size_t v___x_1743_; size_t v___x_1744_; lean_object* v_j_1745_; lean_object* v___x_1746_; 
v_es_1740_ = lean_ctor_get(v_x_1737_, 0);
v___x_1741_ = lean_box(2);
v___x_1742_ = ((size_t)5ULL);
v___x_1743_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg___closed__1);
v___x_1744_ = lean_usize_land(v_x_1738_, v___x_1743_);
v_j_1745_ = lean_usize_to_nat(v___x_1744_);
v___x_1746_ = lean_array_get_borrowed(v___x_1741_, v_es_1740_, v_j_1745_);
lean_dec(v_j_1745_);
switch(lean_obj_tag(v___x_1746_))
{
case 0:
{
lean_object* v_key_1747_; uint8_t v___x_1748_; 
v_key_1747_ = lean_ctor_get(v___x_1746_, 0);
v___x_1748_ = lean_expr_eqv(v_x_1739_, v_key_1747_);
return v___x_1748_;
}
case 1:
{
lean_object* v_node_1749_; size_t v___x_1750_; 
v_node_1749_ = lean_ctor_get(v___x_1746_, 0);
v___x_1750_ = lean_usize_shift_right(v_x_1738_, v___x_1742_);
v_x_1737_ = v_node_1749_;
v_x_1738_ = v___x_1750_;
goto _start;
}
default: 
{
uint8_t v___x_1752_; 
v___x_1752_ = 0;
return v___x_1752_;
}
}
}
else
{
lean_object* v_ks_1753_; lean_object* v___x_1754_; uint8_t v___x_1755_; 
v_ks_1753_ = lean_ctor_get(v_x_1737_, 0);
v___x_1754_ = lean_unsigned_to_nat(0u);
v___x_1755_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1_spec__2_spec__6___redArg(v_ks_1753_, v___x_1754_, v_x_1739_);
return v___x_1755_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1_spec__2___redArg___boxed(lean_object* v_x_1756_, lean_object* v_x_1757_, lean_object* v_x_1758_){
_start:
{
size_t v_x_141017__boxed_1759_; uint8_t v_res_1760_; lean_object* v_r_1761_; 
v_x_141017__boxed_1759_ = lean_unbox_usize(v_x_1757_);
lean_dec(v_x_1757_);
v_res_1760_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1_spec__2___redArg(v_x_1756_, v_x_141017__boxed_1759_, v_x_1758_);
lean_dec_ref(v_x_1758_);
lean_dec_ref(v_x_1756_);
v_r_1761_ = lean_box(v_res_1760_);
return v_r_1761_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1___redArg(lean_object* v_x_1762_, lean_object* v_x_1763_){
_start:
{
uint64_t v___x_1764_; size_t v___x_1765_; uint8_t v___x_1766_; 
v___x_1764_ = l_Lean_Expr_hash(v_x_1763_);
v___x_1765_ = lean_uint64_to_usize(v___x_1764_);
v___x_1766_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1_spec__2___redArg(v_x_1762_, v___x_1765_, v_x_1763_);
return v___x_1766_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1___redArg___boxed(lean_object* v_x_1767_, lean_object* v_x_1768_){
_start:
{
uint8_t v_res_1769_; lean_object* v_r_1770_; 
v_res_1769_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1___redArg(v_x_1767_, v_x_1768_);
lean_dec_ref(v_x_1768_);
lean_dec_ref(v_x_1767_);
v_r_1770_ = lean_box(v_res_1769_);
return v_r_1770_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__3___lam__0(lean_object* v_a_1771_, lean_object* v_s_1772_){
_start:
{
lean_object* v_toRing_1773_; lean_object* v_invFn_x3f_1774_; lean_object* v_semiringId_x3f_1775_; lean_object* v_commSemiringInst_1776_; lean_object* v_commRingInst_1777_; lean_object* v_noZeroDivInst_x3f_1778_; lean_object* v_fieldInst_x3f_1779_; lean_object* v_powIdentityInst_x3f_1780_; lean_object* v_denoteEntries_1781_; lean_object* v_nextId_1782_; lean_object* v_steps_1783_; lean_object* v_queue_1784_; lean_object* v_basis_1785_; lean_object* v_diseqs_1786_; uint8_t v_recheck_1787_; lean_object* v_invSet_1788_; lean_object* v_powIdentityVarCount_1789_; lean_object* v_numEq0_x3f_1790_; uint8_t v_numEq0Updated_1791_; lean_object* v___x_1793_; uint8_t v_isShared_1794_; uint8_t v_isSharedCheck_1823_; 
v_toRing_1773_ = lean_ctor_get(v_s_1772_, 0);
v_invFn_x3f_1774_ = lean_ctor_get(v_s_1772_, 1);
v_semiringId_x3f_1775_ = lean_ctor_get(v_s_1772_, 2);
v_commSemiringInst_1776_ = lean_ctor_get(v_s_1772_, 3);
v_commRingInst_1777_ = lean_ctor_get(v_s_1772_, 4);
v_noZeroDivInst_x3f_1778_ = lean_ctor_get(v_s_1772_, 5);
v_fieldInst_x3f_1779_ = lean_ctor_get(v_s_1772_, 6);
v_powIdentityInst_x3f_1780_ = lean_ctor_get(v_s_1772_, 7);
v_denoteEntries_1781_ = lean_ctor_get(v_s_1772_, 8);
v_nextId_1782_ = lean_ctor_get(v_s_1772_, 9);
v_steps_1783_ = lean_ctor_get(v_s_1772_, 10);
v_queue_1784_ = lean_ctor_get(v_s_1772_, 11);
v_basis_1785_ = lean_ctor_get(v_s_1772_, 12);
v_diseqs_1786_ = lean_ctor_get(v_s_1772_, 13);
v_recheck_1787_ = lean_ctor_get_uint8(v_s_1772_, sizeof(void*)*17);
v_invSet_1788_ = lean_ctor_get(v_s_1772_, 14);
v_powIdentityVarCount_1789_ = lean_ctor_get(v_s_1772_, 15);
v_numEq0_x3f_1790_ = lean_ctor_get(v_s_1772_, 16);
v_numEq0Updated_1791_ = lean_ctor_get_uint8(v_s_1772_, sizeof(void*)*17 + 1);
v_isSharedCheck_1823_ = !lean_is_exclusive(v_s_1772_);
if (v_isSharedCheck_1823_ == 0)
{
v___x_1793_ = v_s_1772_;
v_isShared_1794_ = v_isSharedCheck_1823_;
goto v_resetjp_1792_;
}
else
{
lean_inc(v_numEq0_x3f_1790_);
lean_inc(v_powIdentityVarCount_1789_);
lean_inc(v_invSet_1788_);
lean_inc(v_diseqs_1786_);
lean_inc(v_basis_1785_);
lean_inc(v_queue_1784_);
lean_inc(v_steps_1783_);
lean_inc(v_nextId_1782_);
lean_inc(v_denoteEntries_1781_);
lean_inc(v_powIdentityInst_x3f_1780_);
lean_inc(v_fieldInst_x3f_1779_);
lean_inc(v_noZeroDivInst_x3f_1778_);
lean_inc(v_commRingInst_1777_);
lean_inc(v_commSemiringInst_1776_);
lean_inc(v_semiringId_x3f_1775_);
lean_inc(v_invFn_x3f_1774_);
lean_inc(v_toRing_1773_);
lean_dec(v_s_1772_);
v___x_1793_ = lean_box(0);
v_isShared_1794_ = v_isSharedCheck_1823_;
goto v_resetjp_1792_;
}
v_resetjp_1792_:
{
lean_object* v_id_1795_; lean_object* v_type_1796_; lean_object* v_u_1797_; lean_object* v_ringInst_1798_; lean_object* v_semiringInst_1799_; lean_object* v_charInst_x3f_1800_; lean_object* v_addFn_x3f_1801_; lean_object* v_subFn_x3f_1802_; lean_object* v_negFn_x3f_1803_; lean_object* v_powFn_x3f_1804_; lean_object* v_intCastFn_x3f_1805_; lean_object* v_natCastFn_x3f_1806_; lean_object* v_one_x3f_1807_; lean_object* v_vars_1808_; lean_object* v_varMap_1809_; lean_object* v_denote_1810_; lean_object* v___x_1812_; uint8_t v_isShared_1813_; uint8_t v_isSharedCheck_1821_; 
v_id_1795_ = lean_ctor_get(v_toRing_1773_, 0);
v_type_1796_ = lean_ctor_get(v_toRing_1773_, 1);
v_u_1797_ = lean_ctor_get(v_toRing_1773_, 2);
v_ringInst_1798_ = lean_ctor_get(v_toRing_1773_, 3);
v_semiringInst_1799_ = lean_ctor_get(v_toRing_1773_, 4);
v_charInst_x3f_1800_ = lean_ctor_get(v_toRing_1773_, 5);
v_addFn_x3f_1801_ = lean_ctor_get(v_toRing_1773_, 6);
v_subFn_x3f_1802_ = lean_ctor_get(v_toRing_1773_, 8);
v_negFn_x3f_1803_ = lean_ctor_get(v_toRing_1773_, 9);
v_powFn_x3f_1804_ = lean_ctor_get(v_toRing_1773_, 10);
v_intCastFn_x3f_1805_ = lean_ctor_get(v_toRing_1773_, 11);
v_natCastFn_x3f_1806_ = lean_ctor_get(v_toRing_1773_, 12);
v_one_x3f_1807_ = lean_ctor_get(v_toRing_1773_, 13);
v_vars_1808_ = lean_ctor_get(v_toRing_1773_, 14);
v_varMap_1809_ = lean_ctor_get(v_toRing_1773_, 15);
v_denote_1810_ = lean_ctor_get(v_toRing_1773_, 16);
v_isSharedCheck_1821_ = !lean_is_exclusive(v_toRing_1773_);
if (v_isSharedCheck_1821_ == 0)
{
lean_object* v_unused_1822_; 
v_unused_1822_ = lean_ctor_get(v_toRing_1773_, 7);
lean_dec(v_unused_1822_);
v___x_1812_ = v_toRing_1773_;
v_isShared_1813_ = v_isSharedCheck_1821_;
goto v_resetjp_1811_;
}
else
{
lean_inc(v_denote_1810_);
lean_inc(v_varMap_1809_);
lean_inc(v_vars_1808_);
lean_inc(v_one_x3f_1807_);
lean_inc(v_natCastFn_x3f_1806_);
lean_inc(v_intCastFn_x3f_1805_);
lean_inc(v_powFn_x3f_1804_);
lean_inc(v_negFn_x3f_1803_);
lean_inc(v_subFn_x3f_1802_);
lean_inc(v_addFn_x3f_1801_);
lean_inc(v_charInst_x3f_1800_);
lean_inc(v_semiringInst_1799_);
lean_inc(v_ringInst_1798_);
lean_inc(v_u_1797_);
lean_inc(v_type_1796_);
lean_inc(v_id_1795_);
lean_dec(v_toRing_1773_);
v___x_1812_ = lean_box(0);
v_isShared_1813_ = v_isSharedCheck_1821_;
goto v_resetjp_1811_;
}
v_resetjp_1811_:
{
lean_object* v___x_1814_; lean_object* v___x_1816_; 
v___x_1814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1814_, 0, v_a_1771_);
if (v_isShared_1813_ == 0)
{
lean_ctor_set(v___x_1812_, 7, v___x_1814_);
v___x_1816_ = v___x_1812_;
goto v_reusejp_1815_;
}
else
{
lean_object* v_reuseFailAlloc_1820_; 
v_reuseFailAlloc_1820_ = lean_alloc_ctor(0, 17, 0);
lean_ctor_set(v_reuseFailAlloc_1820_, 0, v_id_1795_);
lean_ctor_set(v_reuseFailAlloc_1820_, 1, v_type_1796_);
lean_ctor_set(v_reuseFailAlloc_1820_, 2, v_u_1797_);
lean_ctor_set(v_reuseFailAlloc_1820_, 3, v_ringInst_1798_);
lean_ctor_set(v_reuseFailAlloc_1820_, 4, v_semiringInst_1799_);
lean_ctor_set(v_reuseFailAlloc_1820_, 5, v_charInst_x3f_1800_);
lean_ctor_set(v_reuseFailAlloc_1820_, 6, v_addFn_x3f_1801_);
lean_ctor_set(v_reuseFailAlloc_1820_, 7, v___x_1814_);
lean_ctor_set(v_reuseFailAlloc_1820_, 8, v_subFn_x3f_1802_);
lean_ctor_set(v_reuseFailAlloc_1820_, 9, v_negFn_x3f_1803_);
lean_ctor_set(v_reuseFailAlloc_1820_, 10, v_powFn_x3f_1804_);
lean_ctor_set(v_reuseFailAlloc_1820_, 11, v_intCastFn_x3f_1805_);
lean_ctor_set(v_reuseFailAlloc_1820_, 12, v_natCastFn_x3f_1806_);
lean_ctor_set(v_reuseFailAlloc_1820_, 13, v_one_x3f_1807_);
lean_ctor_set(v_reuseFailAlloc_1820_, 14, v_vars_1808_);
lean_ctor_set(v_reuseFailAlloc_1820_, 15, v_varMap_1809_);
lean_ctor_set(v_reuseFailAlloc_1820_, 16, v_denote_1810_);
v___x_1816_ = v_reuseFailAlloc_1820_;
goto v_reusejp_1815_;
}
v_reusejp_1815_:
{
lean_object* v___x_1818_; 
if (v_isShared_1794_ == 0)
{
lean_ctor_set(v___x_1793_, 0, v___x_1816_);
v___x_1818_ = v___x_1793_;
goto v_reusejp_1817_;
}
else
{
lean_object* v_reuseFailAlloc_1819_; 
v_reuseFailAlloc_1819_ = lean_alloc_ctor(0, 17, 2);
lean_ctor_set(v_reuseFailAlloc_1819_, 0, v___x_1816_);
lean_ctor_set(v_reuseFailAlloc_1819_, 1, v_invFn_x3f_1774_);
lean_ctor_set(v_reuseFailAlloc_1819_, 2, v_semiringId_x3f_1775_);
lean_ctor_set(v_reuseFailAlloc_1819_, 3, v_commSemiringInst_1776_);
lean_ctor_set(v_reuseFailAlloc_1819_, 4, v_commRingInst_1777_);
lean_ctor_set(v_reuseFailAlloc_1819_, 5, v_noZeroDivInst_x3f_1778_);
lean_ctor_set(v_reuseFailAlloc_1819_, 6, v_fieldInst_x3f_1779_);
lean_ctor_set(v_reuseFailAlloc_1819_, 7, v_powIdentityInst_x3f_1780_);
lean_ctor_set(v_reuseFailAlloc_1819_, 8, v_denoteEntries_1781_);
lean_ctor_set(v_reuseFailAlloc_1819_, 9, v_nextId_1782_);
lean_ctor_set(v_reuseFailAlloc_1819_, 10, v_steps_1783_);
lean_ctor_set(v_reuseFailAlloc_1819_, 11, v_queue_1784_);
lean_ctor_set(v_reuseFailAlloc_1819_, 12, v_basis_1785_);
lean_ctor_set(v_reuseFailAlloc_1819_, 13, v_diseqs_1786_);
lean_ctor_set(v_reuseFailAlloc_1819_, 14, v_invSet_1788_);
lean_ctor_set(v_reuseFailAlloc_1819_, 15, v_powIdentityVarCount_1789_);
lean_ctor_set(v_reuseFailAlloc_1819_, 16, v_numEq0_x3f_1790_);
lean_ctor_set_uint8(v_reuseFailAlloc_1819_, sizeof(void*)*17, v_recheck_1787_);
lean_ctor_set_uint8(v_reuseFailAlloc_1819_, sizeof(void*)*17 + 1, v_numEq0Updated_1791_);
v___x_1818_ = v_reuseFailAlloc_1819_;
goto v_reusejp_1817_;
}
v_reusejp_1817_:
{
return v___x_1818_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__3_spec__5(lean_object* v_type_1824_, lean_object* v_u_1825_, lean_object* v_instDeclName_1826_, lean_object* v_declName_1827_, lean_object* v_expectedInst_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_){
_start:
{
lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; 
v___x_1841_ = lean_box(0);
lean_inc_n(v_u_1825_, 2);
v___x_1842_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1842_, 0, v_u_1825_);
lean_ctor_set(v___x_1842_, 1, v___x_1841_);
v___x_1843_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1843_, 0, v_u_1825_);
lean_ctor_set(v___x_1843_, 1, v___x_1842_);
v___x_1844_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1844_, 0, v_u_1825_);
lean_ctor_set(v___x_1844_, 1, v___x_1843_);
lean_inc_ref(v___x_1844_);
v___x_1845_ = l_Lean_mkConst(v_instDeclName_1826_, v___x_1844_);
lean_inc_ref_n(v_type_1824_, 3);
v___x_1846_ = l_Lean_mkApp3(v___x_1845_, v_type_1824_, v_type_1824_, v_type_1824_);
v___x_1847_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1_spec__5(v___x_1846_, v___y_1829_, v___y_1830_, v___y_1831_, v___y_1832_, v___y_1833_, v___y_1834_, v___y_1835_, v___y_1836_, v___y_1837_, v___y_1838_, v___y_1839_);
if (lean_obj_tag(v___x_1847_) == 0)
{
lean_object* v_a_1848_; lean_object* v___x_1849_; 
v_a_1848_ = lean_ctor_get(v___x_1847_, 0);
lean_inc_n(v_a_1848_, 2);
lean_dec_ref(v___x_1847_);
lean_inc(v_declName_1827_);
v___x_1849_ = l_Lean_Meta_Grind_Arith_CommRing_checkInst(v_declName_1827_, v_a_1848_, v_expectedInst_1828_, v___y_1836_, v___y_1837_, v___y_1838_, v___y_1839_);
if (lean_obj_tag(v___x_1849_) == 0)
{
lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; 
lean_dec_ref(v___x_1849_);
v___x_1850_ = l_Lean_mkConst(v_declName_1827_, v___x_1844_);
lean_inc_ref_n(v_type_1824_, 2);
v___x_1851_ = l_Lean_mkApp4(v___x_1850_, v_type_1824_, v_type_1824_, v_type_1824_, v_a_1848_);
v___x_1852_ = l_Lean_Meta_Sym_canon(v___x_1851_, v___y_1834_, v___y_1835_, v___y_1836_, v___y_1837_, v___y_1838_, v___y_1839_);
if (lean_obj_tag(v___x_1852_) == 0)
{
lean_object* v_a_1853_; lean_object* v___x_1854_; 
v_a_1853_ = lean_ctor_get(v___x_1852_, 0);
lean_inc(v_a_1853_);
lean_dec_ref(v___x_1852_);
v___x_1854_ = l_Lean_Meta_Sym_shareCommon___redArg(v_a_1853_, v___y_1835_);
return v___x_1854_;
}
else
{
return v___x_1852_;
}
}
else
{
lean_object* v_a_1855_; lean_object* v___x_1857_; uint8_t v_isShared_1858_; uint8_t v_isSharedCheck_1862_; 
lean_dec(v_a_1848_);
lean_dec_ref(v___x_1844_);
lean_dec(v_declName_1827_);
lean_dec_ref(v_type_1824_);
v_a_1855_ = lean_ctor_get(v___x_1849_, 0);
v_isSharedCheck_1862_ = !lean_is_exclusive(v___x_1849_);
if (v_isSharedCheck_1862_ == 0)
{
v___x_1857_ = v___x_1849_;
v_isShared_1858_ = v_isSharedCheck_1862_;
goto v_resetjp_1856_;
}
else
{
lean_inc(v_a_1855_);
lean_dec(v___x_1849_);
v___x_1857_ = lean_box(0);
v_isShared_1858_ = v_isSharedCheck_1862_;
goto v_resetjp_1856_;
}
v_resetjp_1856_:
{
lean_object* v___x_1860_; 
if (v_isShared_1858_ == 0)
{
v___x_1860_ = v___x_1857_;
goto v_reusejp_1859_;
}
else
{
lean_object* v_reuseFailAlloc_1861_; 
v_reuseFailAlloc_1861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1861_, 0, v_a_1855_);
v___x_1860_ = v_reuseFailAlloc_1861_;
goto v_reusejp_1859_;
}
v_reusejp_1859_:
{
return v___x_1860_;
}
}
}
}
else
{
lean_dec_ref(v___x_1844_);
lean_dec_ref(v_expectedInst_1828_);
lean_dec(v_declName_1827_);
lean_dec_ref(v_type_1824_);
return v___x_1847_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__3_spec__5___boxed(lean_object** _args){
lean_object* v_type_1863_ = _args[0];
lean_object* v_u_1864_ = _args[1];
lean_object* v_instDeclName_1865_ = _args[2];
lean_object* v_declName_1866_ = _args[3];
lean_object* v_expectedInst_1867_ = _args[4];
lean_object* v___y_1868_ = _args[5];
lean_object* v___y_1869_ = _args[6];
lean_object* v___y_1870_ = _args[7];
lean_object* v___y_1871_ = _args[8];
lean_object* v___y_1872_ = _args[9];
lean_object* v___y_1873_ = _args[10];
lean_object* v___y_1874_ = _args[11];
lean_object* v___y_1875_ = _args[12];
lean_object* v___y_1876_ = _args[13];
lean_object* v___y_1877_ = _args[14];
lean_object* v___y_1878_ = _args[15];
lean_object* v___y_1879_ = _args[16];
_start:
{
lean_object* v_res_1880_; 
v_res_1880_ = l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__3_spec__5(v_type_1863_, v_u_1864_, v_instDeclName_1865_, v_declName_1866_, v_expectedInst_1867_, v___y_1868_, v___y_1869_, v___y_1870_, v___y_1871_, v___y_1872_, v___y_1873_, v___y_1874_, v___y_1875_, v___y_1876_, v___y_1877_, v___y_1878_);
lean_dec(v___y_1878_);
lean_dec_ref(v___y_1877_);
lean_dec(v___y_1876_);
lean_dec_ref(v___y_1875_);
lean_dec(v___y_1874_);
lean_dec_ref(v___y_1873_);
lean_dec(v___y_1872_);
lean_dec_ref(v___y_1871_);
lean_dec(v___y_1870_);
lean_dec(v___y_1869_);
lean_dec_ref(v___y_1868_);
return v_res_1880_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__3(lean_object* v___y_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_){
_start:
{
lean_object* v___x_1904_; 
v___x_1904_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v___y_1892_, v___y_1893_, v___y_1894_, v___y_1895_, v___y_1896_, v___y_1897_, v___y_1898_, v___y_1899_, v___y_1900_, v___y_1901_, v___y_1902_);
if (lean_obj_tag(v___x_1904_) == 0)
{
lean_object* v_a_1905_; lean_object* v___x_1907_; uint8_t v_isShared_1908_; uint8_t v_isSharedCheck_1948_; 
v_a_1905_ = lean_ctor_get(v___x_1904_, 0);
v_isSharedCheck_1948_ = !lean_is_exclusive(v___x_1904_);
if (v_isSharedCheck_1948_ == 0)
{
v___x_1907_ = v___x_1904_;
v_isShared_1908_ = v_isSharedCheck_1948_;
goto v_resetjp_1906_;
}
else
{
lean_inc(v_a_1905_);
lean_dec(v___x_1904_);
v___x_1907_ = lean_box(0);
v_isShared_1908_ = v_isSharedCheck_1948_;
goto v_resetjp_1906_;
}
v_resetjp_1906_:
{
lean_object* v_toRing_1909_; lean_object* v_mulFn_x3f_1910_; 
v_toRing_1909_ = lean_ctor_get(v_a_1905_, 0);
lean_inc_ref(v_toRing_1909_);
lean_dec(v_a_1905_);
v_mulFn_x3f_1910_ = lean_ctor_get(v_toRing_1909_, 7);
if (lean_obj_tag(v_mulFn_x3f_1910_) == 1)
{
lean_object* v_val_1911_; lean_object* v___x_1913_; 
lean_inc_ref(v_mulFn_x3f_1910_);
lean_dec_ref(v_toRing_1909_);
v_val_1911_ = lean_ctor_get(v_mulFn_x3f_1910_, 0);
lean_inc(v_val_1911_);
lean_dec_ref(v_mulFn_x3f_1910_);
if (v_isShared_1908_ == 0)
{
lean_ctor_set(v___x_1907_, 0, v_val_1911_);
v___x_1913_ = v___x_1907_;
goto v_reusejp_1912_;
}
else
{
lean_object* v_reuseFailAlloc_1914_; 
v_reuseFailAlloc_1914_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1914_, 0, v_val_1911_);
v___x_1913_ = v_reuseFailAlloc_1914_;
goto v_reusejp_1912_;
}
v_reusejp_1912_:
{
return v___x_1913_;
}
}
else
{
lean_object* v_type_1915_; lean_object* v_u_1916_; lean_object* v_semiringInst_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v_expectedInst_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; 
lean_del_object(v___x_1907_);
v_type_1915_ = lean_ctor_get(v_toRing_1909_, 1);
lean_inc_ref_n(v_type_1915_, 3);
v_u_1916_ = lean_ctor_get(v_toRing_1909_, 2);
lean_inc_n(v_u_1916_, 2);
v_semiringInst_1917_ = lean_ctor_get(v_toRing_1909_, 4);
lean_inc_ref(v_semiringInst_1917_);
lean_dec_ref(v_toRing_1909_);
v___x_1918_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__3___closed__1));
v___x_1919_ = lean_box(0);
v___x_1920_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1920_, 0, v_u_1916_);
lean_ctor_set(v___x_1920_, 1, v___x_1919_);
lean_inc_ref(v___x_1920_);
v___x_1921_ = l_Lean_mkConst(v___x_1918_, v___x_1920_);
v___x_1922_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__3___closed__3));
v___x_1923_ = l_Lean_mkConst(v___x_1922_, v___x_1920_);
v___x_1924_ = l_Lean_mkAppB(v___x_1923_, v_type_1915_, v_semiringInst_1917_);
v_expectedInst_1925_ = l_Lean_mkAppB(v___x_1921_, v_type_1915_, v___x_1924_);
v___x_1926_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__3___closed__4));
v___x_1927_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__20));
v___x_1928_ = l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__3_spec__5(v_type_1915_, v_u_1916_, v___x_1926_, v___x_1927_, v_expectedInst_1925_, v___y_1892_, v___y_1893_, v___y_1894_, v___y_1895_, v___y_1896_, v___y_1897_, v___y_1898_, v___y_1899_, v___y_1900_, v___y_1901_, v___y_1902_);
if (lean_obj_tag(v___x_1928_) == 0)
{
lean_object* v_a_1929_; lean_object* v___f_1930_; lean_object* v___x_1931_; 
v_a_1929_ = lean_ctor_get(v___x_1928_, 0);
lean_inc_n(v_a_1929_, 2);
lean_dec_ref(v___x_1928_);
v___f_1930_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__3___lam__0), 2, 1);
lean_closure_set(v___f_1930_, 0, v_a_1929_);
v___x_1931_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(v___f_1930_, v___y_1892_, v___y_1893_);
if (lean_obj_tag(v___x_1931_) == 0)
{
lean_object* v___x_1933_; uint8_t v_isShared_1934_; uint8_t v_isSharedCheck_1938_; 
v_isSharedCheck_1938_ = !lean_is_exclusive(v___x_1931_);
if (v_isSharedCheck_1938_ == 0)
{
lean_object* v_unused_1939_; 
v_unused_1939_ = lean_ctor_get(v___x_1931_, 0);
lean_dec(v_unused_1939_);
v___x_1933_ = v___x_1931_;
v_isShared_1934_ = v_isSharedCheck_1938_;
goto v_resetjp_1932_;
}
else
{
lean_dec(v___x_1931_);
v___x_1933_ = lean_box(0);
v_isShared_1934_ = v_isSharedCheck_1938_;
goto v_resetjp_1932_;
}
v_resetjp_1932_:
{
lean_object* v___x_1936_; 
if (v_isShared_1934_ == 0)
{
lean_ctor_set(v___x_1933_, 0, v_a_1929_);
v___x_1936_ = v___x_1933_;
goto v_reusejp_1935_;
}
else
{
lean_object* v_reuseFailAlloc_1937_; 
v_reuseFailAlloc_1937_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1937_, 0, v_a_1929_);
v___x_1936_ = v_reuseFailAlloc_1937_;
goto v_reusejp_1935_;
}
v_reusejp_1935_:
{
return v___x_1936_;
}
}
}
else
{
lean_object* v_a_1940_; lean_object* v___x_1942_; uint8_t v_isShared_1943_; uint8_t v_isSharedCheck_1947_; 
lean_dec(v_a_1929_);
v_a_1940_ = lean_ctor_get(v___x_1931_, 0);
v_isSharedCheck_1947_ = !lean_is_exclusive(v___x_1931_);
if (v_isSharedCheck_1947_ == 0)
{
v___x_1942_ = v___x_1931_;
v_isShared_1943_ = v_isSharedCheck_1947_;
goto v_resetjp_1941_;
}
else
{
lean_inc(v_a_1940_);
lean_dec(v___x_1931_);
v___x_1942_ = lean_box(0);
v_isShared_1943_ = v_isSharedCheck_1947_;
goto v_resetjp_1941_;
}
v_resetjp_1941_:
{
lean_object* v___x_1945_; 
if (v_isShared_1943_ == 0)
{
v___x_1945_ = v___x_1942_;
goto v_reusejp_1944_;
}
else
{
lean_object* v_reuseFailAlloc_1946_; 
v_reuseFailAlloc_1946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1946_, 0, v_a_1940_);
v___x_1945_ = v_reuseFailAlloc_1946_;
goto v_reusejp_1944_;
}
v_reusejp_1944_:
{
return v___x_1945_;
}
}
}
}
else
{
return v___x_1928_;
}
}
}
}
else
{
lean_object* v_a_1949_; lean_object* v___x_1951_; uint8_t v_isShared_1952_; uint8_t v_isSharedCheck_1956_; 
v_a_1949_ = lean_ctor_get(v___x_1904_, 0);
v_isSharedCheck_1956_ = !lean_is_exclusive(v___x_1904_);
if (v_isSharedCheck_1956_ == 0)
{
v___x_1951_ = v___x_1904_;
v_isShared_1952_ = v_isSharedCheck_1956_;
goto v_resetjp_1950_;
}
else
{
lean_inc(v_a_1949_);
lean_dec(v___x_1904_);
v___x_1951_ = lean_box(0);
v_isShared_1952_ = v_isSharedCheck_1956_;
goto v_resetjp_1950_;
}
v_resetjp_1950_:
{
lean_object* v___x_1954_; 
if (v_isShared_1952_ == 0)
{
v___x_1954_ = v___x_1951_;
goto v_reusejp_1953_;
}
else
{
lean_object* v_reuseFailAlloc_1955_; 
v_reuseFailAlloc_1955_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1955_, 0, v_a_1949_);
v___x_1954_ = v_reuseFailAlloc_1955_;
goto v_reusejp_1953_;
}
v_reusejp_1953_:
{
return v___x_1954_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__3___boxed(lean_object* v___y_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_, lean_object* v___y_1968_){
_start:
{
lean_object* v_res_1969_; 
v_res_1969_ = l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__3(v___y_1957_, v___y_1958_, v___y_1959_, v___y_1960_, v___y_1961_, v___y_1962_, v___y_1963_, v___y_1964_, v___y_1965_, v___y_1966_, v___y_1967_);
lean_dec(v___y_1967_);
lean_dec_ref(v___y_1966_);
lean_dec(v___y_1965_);
lean_dec_ref(v___y_1964_);
lean_dec(v___y_1963_);
lean_dec_ref(v___y_1962_);
lean_dec(v___y_1961_);
lean_dec_ref(v___y_1960_);
lean_dec(v___y_1959_);
lean_dec(v___y_1958_);
lean_dec_ref(v___y_1957_);
return v_res_1969_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__3(void){
_start:
{
lean_object* v___x_1977_; lean_object* v___x_1978_; 
v___x_1977_ = lean_unsigned_to_nat(1u);
v___x_1978_ = lean_nat_to_int(v___x_1977_);
return v___x_1978_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv(lean_object* v_e_2003_, lean_object* v_inst_2004_, lean_object* v_a_2005_, lean_object* v_a_2006_, lean_object* v_a_2007_, lean_object* v_a_2008_, lean_object* v_a_2009_, lean_object* v_a_2010_, lean_object* v_a_2011_, lean_object* v_a_2012_, lean_object* v_a_2013_, lean_object* v_a_2014_, lean_object* v_a_2015_, lean_object* v_a_2016_){
_start:
{
lean_object* v___x_2021_; 
v___x_2021_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst(v_inst_2004_, v_a_2006_, v_a_2007_, v_a_2008_, v_a_2009_, v_a_2010_, v_a_2011_, v_a_2012_, v_a_2013_, v_a_2014_, v_a_2015_, v_a_2016_);
if (lean_obj_tag(v___x_2021_) == 0)
{
lean_object* v_a_2022_; lean_object* v___x_2024_; uint8_t v_isShared_2025_; uint8_t v_isSharedCheck_2281_; 
v_a_2022_ = lean_ctor_get(v___x_2021_, 0);
v_isSharedCheck_2281_ = !lean_is_exclusive(v___x_2021_);
if (v_isSharedCheck_2281_ == 0)
{
v___x_2024_ = v___x_2021_;
v_isShared_2025_ = v_isSharedCheck_2281_;
goto v_resetjp_2023_;
}
else
{
lean_inc(v_a_2022_);
lean_dec(v___x_2021_);
v___x_2024_ = lean_box(0);
v_isShared_2025_ = v_isSharedCheck_2281_;
goto v_resetjp_2023_;
}
v_resetjp_2023_:
{
uint8_t v___x_2026_; 
v___x_2026_ = lean_unbox(v_a_2022_);
lean_dec(v_a_2022_);
if (v___x_2026_ == 0)
{
lean_object* v___x_2027_; lean_object* v___x_2029_; 
lean_dec_ref(v_a_2005_);
lean_dec_ref(v_e_2003_);
v___x_2027_ = lean_box(0);
if (v_isShared_2025_ == 0)
{
lean_ctor_set(v___x_2024_, 0, v___x_2027_);
v___x_2029_ = v___x_2024_;
goto v_reusejp_2028_;
}
else
{
lean_object* v_reuseFailAlloc_2030_; 
v_reuseFailAlloc_2030_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2030_, 0, v___x_2027_);
v___x_2029_ = v_reuseFailAlloc_2030_;
goto v_reusejp_2028_;
}
v_reusejp_2028_:
{
return v___x_2029_;
}
}
else
{
lean_object* v___x_2031_; 
lean_del_object(v___x_2024_);
v___x_2031_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v_a_2006_, v_a_2007_, v_a_2008_, v_a_2009_, v_a_2010_, v_a_2011_, v_a_2012_, v_a_2013_, v_a_2014_, v_a_2015_, v_a_2016_);
if (lean_obj_tag(v___x_2031_) == 0)
{
lean_object* v_a_2032_; lean_object* v___x_2034_; uint8_t v_isShared_2035_; uint8_t v_isSharedCheck_2272_; 
v_a_2032_ = lean_ctor_get(v___x_2031_, 0);
v_isSharedCheck_2272_ = !lean_is_exclusive(v___x_2031_);
if (v_isSharedCheck_2272_ == 0)
{
v___x_2034_ = v___x_2031_;
v_isShared_2035_ = v_isSharedCheck_2272_;
goto v_resetjp_2033_;
}
else
{
lean_inc(v_a_2032_);
lean_dec(v___x_2031_);
v___x_2034_ = lean_box(0);
v_isShared_2035_ = v_isSharedCheck_2272_;
goto v_resetjp_2033_;
}
v_resetjp_2033_:
{
lean_object* v_fieldInst_x3f_2036_; 
v_fieldInst_x3f_2036_ = lean_ctor_get(v_a_2032_, 6);
lean_inc(v_fieldInst_x3f_2036_);
if (lean_obj_tag(v_fieldInst_x3f_2036_) == 1)
{
lean_object* v_toRing_2037_; lean_object* v_val_2038_; lean_object* v___y_2040_; lean_object* v___y_2041_; lean_object* v___y_2042_; lean_object* v___y_2043_; lean_object* v___y_2044_; lean_object* v___y_2045_; lean_object* v___y_2046_; lean_object* v___y_2047_; lean_object* v___y_2048_; lean_object* v___y_2049_; lean_object* v___x_2059_; 
lean_del_object(v___x_2034_);
v_toRing_2037_ = lean_ctor_get(v_a_2032_, 0);
lean_inc_ref(v_toRing_2037_);
lean_dec(v_a_2032_);
v_val_2038_ = lean_ctor_get(v_fieldInst_x3f_2036_, 0);
lean_inc(v_val_2038_);
lean_dec_ref(v_fieldInst_x3f_2036_);
v___x_2059_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v_a_2006_, v_a_2007_, v_a_2008_, v_a_2009_, v_a_2010_, v_a_2011_, v_a_2012_, v_a_2013_, v_a_2014_, v_a_2015_, v_a_2016_);
if (lean_obj_tag(v___x_2059_) == 0)
{
lean_object* v_a_2060_; lean_object* v___x_2062_; uint8_t v_isShared_2063_; uint8_t v_isSharedCheck_2259_; 
v_a_2060_ = lean_ctor_get(v___x_2059_, 0);
v_isSharedCheck_2259_ = !lean_is_exclusive(v___x_2059_);
if (v_isSharedCheck_2259_ == 0)
{
v___x_2062_ = v___x_2059_;
v_isShared_2063_ = v_isSharedCheck_2259_;
goto v_resetjp_2061_;
}
else
{
lean_inc(v_a_2060_);
lean_dec(v___x_2059_);
v___x_2062_ = lean_box(0);
v_isShared_2063_ = v_isSharedCheck_2259_;
goto v_resetjp_2061_;
}
v_resetjp_2061_:
{
lean_object* v_invSet_2064_; uint8_t v___x_2065_; 
v_invSet_2064_ = lean_ctor_get(v_a_2060_, 14);
lean_inc_ref(v_invSet_2064_);
lean_dec(v_a_2060_);
v___x_2065_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1___redArg(v_invSet_2064_, v_a_2005_);
lean_dec_ref(v_invSet_2064_);
if (v___x_2065_ == 0)
{
lean_object* v___f_2066_; lean_object* v___x_2067_; 
lean_del_object(v___x_2062_);
lean_inc_ref(v_a_2005_);
v___f_2066_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___lam__0), 2, 1);
lean_closure_set(v___f_2066_, 0, v_a_2005_);
v___x_2067_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(v___f_2066_, v_a_2006_, v_a_2007_);
if (lean_obj_tag(v___x_2067_) == 0)
{
lean_object* v___x_2068_; 
lean_dec_ref(v___x_2067_);
lean_inc_ref(v_a_2005_);
v___x_2068_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f(v_a_2005_, v_a_2006_, v_a_2007_, v_a_2008_, v_a_2009_, v_a_2010_, v_a_2011_, v_a_2012_, v_a_2013_, v_a_2014_, v_a_2015_, v_a_2016_);
if (lean_obj_tag(v___x_2068_) == 0)
{
lean_object* v_a_2069_; 
v_a_2069_ = lean_ctor_get(v___x_2068_, 0);
lean_inc(v_a_2069_);
lean_dec_ref(v___x_2068_);
if (lean_obj_tag(v_a_2069_) == 1)
{
lean_object* v_val_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; uint8_t v___x_2073_; 
v_val_2070_ = lean_ctor_get(v_a_2069_, 0);
lean_inc(v_val_2070_);
lean_dec_ref(v_a_2069_);
v___x_2071_ = lean_unsigned_to_nat(0u);
v___x_2072_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__4___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__4___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__4___closed__1);
v___x_2073_ = lean_int_dec_eq(v_val_2070_, v___x_2072_);
if (v___x_2073_ == 0)
{
lean_object* v___x_2074_; 
v___x_2074_ = l_Lean_Meta_Grind_Arith_CommRing_hasChar(v_a_2006_, v_a_2007_, v_a_2008_, v_a_2009_, v_a_2010_, v_a_2011_, v_a_2012_, v_a_2013_, v_a_2014_, v_a_2015_, v_a_2016_);
if (lean_obj_tag(v___x_2074_) == 0)
{
lean_object* v_a_2075_; uint8_t v___x_2076_; 
v_a_2075_ = lean_ctor_get(v___x_2074_, 0);
lean_inc(v_a_2075_);
lean_dec_ref(v___x_2074_);
v___x_2076_ = lean_unbox(v_a_2075_);
lean_dec(v_a_2075_);
if (v___x_2076_ == 0)
{
lean_dec(v_val_2070_);
lean_dec_ref(v_e_2003_);
v___y_2040_ = v_a_2007_;
v___y_2041_ = v_a_2008_;
v___y_2042_ = v_a_2009_;
v___y_2043_ = v_a_2010_;
v___y_2044_ = v_a_2011_;
v___y_2045_ = v_a_2012_;
v___y_2046_ = v_a_2013_;
v___y_2047_ = v_a_2014_;
v___y_2048_ = v_a_2015_;
v___y_2049_ = v_a_2016_;
goto v___jp_2039_;
}
else
{
lean_object* v___x_2077_; 
v___x_2077_ = l_Lean_Meta_Grind_Arith_CommRing_getCharInst(v_a_2006_, v_a_2007_, v_a_2008_, v_a_2009_, v_a_2010_, v_a_2011_, v_a_2012_, v_a_2013_, v_a_2014_, v_a_2015_, v_a_2016_);
if (lean_obj_tag(v___x_2077_) == 0)
{
lean_object* v_a_2078_; lean_object* v_fst_2079_; lean_object* v_snd_2080_; lean_object* v___x_2082_; uint8_t v_isShared_2083_; uint8_t v_isSharedCheck_2213_; 
v_a_2078_ = lean_ctor_get(v___x_2077_, 0);
lean_inc(v_a_2078_);
lean_dec_ref(v___x_2077_);
v_fst_2079_ = lean_ctor_get(v_a_2078_, 0);
v_snd_2080_ = lean_ctor_get(v_a_2078_, 1);
v_isSharedCheck_2213_ = !lean_is_exclusive(v_a_2078_);
if (v_isSharedCheck_2213_ == 0)
{
v___x_2082_ = v_a_2078_;
v_isShared_2083_ = v_isSharedCheck_2213_;
goto v_resetjp_2081_;
}
else
{
lean_inc(v_snd_2080_);
lean_inc(v_fst_2079_);
lean_dec(v_a_2078_);
v___x_2082_ = lean_box(0);
v_isShared_2083_ = v_isSharedCheck_2213_;
goto v_resetjp_2081_;
}
v_resetjp_2081_:
{
uint8_t v___x_2084_; 
v___x_2084_ = lean_nat_dec_eq(v_snd_2080_, v___x_2071_);
if (v___x_2084_ == 0)
{
lean_object* v___x_2085_; lean_object* v___x_2086_; uint8_t v___x_2087_; 
lean_inc(v_snd_2080_);
v___x_2085_ = lean_nat_to_int(v_snd_2080_);
v___x_2086_ = lean_int_emod(v_val_2070_, v___x_2085_);
lean_dec(v___x_2085_);
v___x_2087_ = lean_int_dec_eq(v___x_2086_, v___x_2072_);
lean_dec(v___x_2086_);
if (v___x_2087_ == 0)
{
lean_object* v___x_2088_; 
v___x_2088_ = l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__3(v_a_2006_, v_a_2007_, v_a_2008_, v_a_2009_, v_a_2010_, v_a_2011_, v_a_2012_, v_a_2013_, v_a_2014_, v_a_2015_, v_a_2016_);
if (lean_obj_tag(v___x_2088_) == 0)
{
lean_object* v_a_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; 
v_a_2089_ = lean_ctor_get(v___x_2088_, 0);
lean_inc(v_a_2089_);
lean_dec_ref(v___x_2088_);
v___x_2090_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__3, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__3);
v___x_2091_ = l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__4(v___x_2090_, v_a_2006_, v_a_2007_, v_a_2008_, v_a_2009_, v_a_2010_, v_a_2011_, v_a_2012_, v_a_2013_, v_a_2014_, v_a_2015_, v_a_2016_);
if (lean_obj_tag(v___x_2091_) == 0)
{
lean_object* v_a_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; 
v_a_2092_ = lean_ctor_get(v___x_2091_, 0);
lean_inc(v_a_2092_);
lean_dec_ref(v___x_2091_);
v___x_2093_ = l_Lean_mkAppB(v_a_2089_, v_a_2005_, v_e_2003_);
v___x_2094_ = l_Lean_Meta_mkEq(v___x_2093_, v_a_2092_, v_a_2013_, v_a_2014_, v_a_2015_, v_a_2016_);
if (lean_obj_tag(v___x_2094_) == 0)
{
lean_object* v_a_2095_; lean_object* v_type_2096_; lean_object* v_u_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2101_; 
v_a_2095_ = lean_ctor_get(v___x_2094_, 0);
lean_inc(v_a_2095_);
lean_dec_ref(v___x_2094_);
v_type_2096_ = lean_ctor_get(v_toRing_2037_, 1);
lean_inc_ref(v_type_2096_);
v_u_2097_ = lean_ctor_get(v_toRing_2037_, 2);
lean_inc(v_u_2097_);
lean_dec_ref(v_toRing_2037_);
v___x_2098_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__5));
v___x_2099_ = lean_box(0);
if (v_isShared_2083_ == 0)
{
lean_ctor_set_tag(v___x_2082_, 1);
lean_ctor_set(v___x_2082_, 1, v___x_2099_);
lean_ctor_set(v___x_2082_, 0, v_u_2097_);
v___x_2101_ = v___x_2082_;
goto v_reusejp_2100_;
}
else
{
lean_object* v_reuseFailAlloc_2109_; 
v_reuseFailAlloc_2109_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2109_, 0, v_u_2097_);
lean_ctor_set(v_reuseFailAlloc_2109_, 1, v___x_2099_);
v___x_2101_ = v_reuseFailAlloc_2109_;
goto v_reusejp_2100_;
}
v_reusejp_2100_:
{
lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; 
v___x_2102_ = l_Lean_mkConst(v___x_2098_, v___x_2101_);
v___x_2103_ = l_Lean_mkNatLit(v_snd_2080_);
v___x_2104_ = l_Lean_mkIntLit(v_val_2070_);
lean_dec(v_val_2070_);
v___x_2105_ = l_Lean_eagerReflBoolTrue;
v___x_2106_ = l_Lean_mkApp6(v___x_2102_, v_type_2096_, v___x_2103_, v_val_2038_, v_fst_2079_, v___x_2104_, v___x_2105_);
v___x_2107_ = l_Lean_Meta_mkExpectedPropHint(v___x_2106_, v_a_2095_);
v___x_2108_ = l_Lean_Meta_Grind_pushNewFact(v___x_2107_, v___x_2071_, v_a_2007_, v_a_2008_, v_a_2009_, v_a_2010_, v_a_2011_, v_a_2012_, v_a_2013_, v_a_2014_, v_a_2015_, v_a_2016_);
if (lean_obj_tag(v___x_2108_) == 0)
{
lean_dec_ref(v___x_2108_);
goto v___jp_2018_;
}
else
{
return v___x_2108_;
}
}
}
else
{
lean_object* v_a_2110_; lean_object* v___x_2112_; uint8_t v_isShared_2113_; uint8_t v_isSharedCheck_2117_; 
lean_del_object(v___x_2082_);
lean_dec(v_snd_2080_);
lean_dec(v_fst_2079_);
lean_dec(v_val_2070_);
lean_dec(v_val_2038_);
lean_dec_ref(v_toRing_2037_);
v_a_2110_ = lean_ctor_get(v___x_2094_, 0);
v_isSharedCheck_2117_ = !lean_is_exclusive(v___x_2094_);
if (v_isSharedCheck_2117_ == 0)
{
v___x_2112_ = v___x_2094_;
v_isShared_2113_ = v_isSharedCheck_2117_;
goto v_resetjp_2111_;
}
else
{
lean_inc(v_a_2110_);
lean_dec(v___x_2094_);
v___x_2112_ = lean_box(0);
v_isShared_2113_ = v_isSharedCheck_2117_;
goto v_resetjp_2111_;
}
v_resetjp_2111_:
{
lean_object* v___x_2115_; 
if (v_isShared_2113_ == 0)
{
v___x_2115_ = v___x_2112_;
goto v_reusejp_2114_;
}
else
{
lean_object* v_reuseFailAlloc_2116_; 
v_reuseFailAlloc_2116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2116_, 0, v_a_2110_);
v___x_2115_ = v_reuseFailAlloc_2116_;
goto v_reusejp_2114_;
}
v_reusejp_2114_:
{
return v___x_2115_;
}
}
}
}
else
{
lean_object* v_a_2118_; lean_object* v___x_2120_; uint8_t v_isShared_2121_; uint8_t v_isSharedCheck_2125_; 
lean_dec(v_a_2089_);
lean_del_object(v___x_2082_);
lean_dec(v_snd_2080_);
lean_dec(v_fst_2079_);
lean_dec(v_val_2070_);
lean_dec(v_val_2038_);
lean_dec_ref(v_toRing_2037_);
lean_dec_ref(v_a_2005_);
lean_dec_ref(v_e_2003_);
v_a_2118_ = lean_ctor_get(v___x_2091_, 0);
v_isSharedCheck_2125_ = !lean_is_exclusive(v___x_2091_);
if (v_isSharedCheck_2125_ == 0)
{
v___x_2120_ = v___x_2091_;
v_isShared_2121_ = v_isSharedCheck_2125_;
goto v_resetjp_2119_;
}
else
{
lean_inc(v_a_2118_);
lean_dec(v___x_2091_);
v___x_2120_ = lean_box(0);
v_isShared_2121_ = v_isSharedCheck_2125_;
goto v_resetjp_2119_;
}
v_resetjp_2119_:
{
lean_object* v___x_2123_; 
if (v_isShared_2121_ == 0)
{
v___x_2123_ = v___x_2120_;
goto v_reusejp_2122_;
}
else
{
lean_object* v_reuseFailAlloc_2124_; 
v_reuseFailAlloc_2124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2124_, 0, v_a_2118_);
v___x_2123_ = v_reuseFailAlloc_2124_;
goto v_reusejp_2122_;
}
v_reusejp_2122_:
{
return v___x_2123_;
}
}
}
}
else
{
lean_object* v_a_2126_; lean_object* v___x_2128_; uint8_t v_isShared_2129_; uint8_t v_isSharedCheck_2133_; 
lean_del_object(v___x_2082_);
lean_dec(v_snd_2080_);
lean_dec(v_fst_2079_);
lean_dec(v_val_2070_);
lean_dec(v_val_2038_);
lean_dec_ref(v_toRing_2037_);
lean_dec_ref(v_a_2005_);
lean_dec_ref(v_e_2003_);
v_a_2126_ = lean_ctor_get(v___x_2088_, 0);
v_isSharedCheck_2133_ = !lean_is_exclusive(v___x_2088_);
if (v_isSharedCheck_2133_ == 0)
{
v___x_2128_ = v___x_2088_;
v_isShared_2129_ = v_isSharedCheck_2133_;
goto v_resetjp_2127_;
}
else
{
lean_inc(v_a_2126_);
lean_dec(v___x_2088_);
v___x_2128_ = lean_box(0);
v_isShared_2129_ = v_isSharedCheck_2133_;
goto v_resetjp_2127_;
}
v_resetjp_2127_:
{
lean_object* v___x_2131_; 
if (v_isShared_2129_ == 0)
{
v___x_2131_ = v___x_2128_;
goto v_reusejp_2130_;
}
else
{
lean_object* v_reuseFailAlloc_2132_; 
v_reuseFailAlloc_2132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2132_, 0, v_a_2126_);
v___x_2131_ = v_reuseFailAlloc_2132_;
goto v_reusejp_2130_;
}
v_reusejp_2130_:
{
return v___x_2131_;
}
}
}
}
else
{
lean_object* v___x_2134_; 
lean_dec_ref(v_a_2005_);
v___x_2134_ = l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__4(v___x_2072_, v_a_2006_, v_a_2007_, v_a_2008_, v_a_2009_, v_a_2010_, v_a_2011_, v_a_2012_, v_a_2013_, v_a_2014_, v_a_2015_, v_a_2016_);
if (lean_obj_tag(v___x_2134_) == 0)
{
lean_object* v_a_2135_; lean_object* v___x_2136_; 
v_a_2135_ = lean_ctor_get(v___x_2134_, 0);
lean_inc(v_a_2135_);
lean_dec_ref(v___x_2134_);
v___x_2136_ = l_Lean_Meta_mkEq(v_e_2003_, v_a_2135_, v_a_2013_, v_a_2014_, v_a_2015_, v_a_2016_);
if (lean_obj_tag(v___x_2136_) == 0)
{
lean_object* v_a_2137_; lean_object* v_type_2138_; lean_object* v_u_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2143_; 
v_a_2137_ = lean_ctor_get(v___x_2136_, 0);
lean_inc(v_a_2137_);
lean_dec_ref(v___x_2136_);
v_type_2138_ = lean_ctor_get(v_toRing_2037_, 1);
lean_inc_ref(v_type_2138_);
v_u_2139_ = lean_ctor_get(v_toRing_2037_, 2);
lean_inc(v_u_2139_);
lean_dec_ref(v_toRing_2037_);
v___x_2140_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__7));
v___x_2141_ = lean_box(0);
if (v_isShared_2083_ == 0)
{
lean_ctor_set_tag(v___x_2082_, 1);
lean_ctor_set(v___x_2082_, 1, v___x_2141_);
lean_ctor_set(v___x_2082_, 0, v_u_2139_);
v___x_2143_ = v___x_2082_;
goto v_reusejp_2142_;
}
else
{
lean_object* v_reuseFailAlloc_2151_; 
v_reuseFailAlloc_2151_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2151_, 0, v_u_2139_);
lean_ctor_set(v_reuseFailAlloc_2151_, 1, v___x_2141_);
v___x_2143_ = v_reuseFailAlloc_2151_;
goto v_reusejp_2142_;
}
v_reusejp_2142_:
{
lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; 
v___x_2144_ = l_Lean_mkConst(v___x_2140_, v___x_2143_);
v___x_2145_ = l_Lean_mkNatLit(v_snd_2080_);
v___x_2146_ = l_Lean_mkIntLit(v_val_2070_);
lean_dec(v_val_2070_);
v___x_2147_ = l_Lean_eagerReflBoolTrue;
v___x_2148_ = l_Lean_mkApp6(v___x_2144_, v_type_2138_, v___x_2145_, v_val_2038_, v_fst_2079_, v___x_2146_, v___x_2147_);
v___x_2149_ = l_Lean_Meta_mkExpectedPropHint(v___x_2148_, v_a_2137_);
v___x_2150_ = l_Lean_Meta_Grind_pushNewFact(v___x_2149_, v___x_2071_, v_a_2007_, v_a_2008_, v_a_2009_, v_a_2010_, v_a_2011_, v_a_2012_, v_a_2013_, v_a_2014_, v_a_2015_, v_a_2016_);
if (lean_obj_tag(v___x_2150_) == 0)
{
lean_dec_ref(v___x_2150_);
goto v___jp_2018_;
}
else
{
return v___x_2150_;
}
}
}
else
{
lean_object* v_a_2152_; lean_object* v___x_2154_; uint8_t v_isShared_2155_; uint8_t v_isSharedCheck_2159_; 
lean_del_object(v___x_2082_);
lean_dec(v_snd_2080_);
lean_dec(v_fst_2079_);
lean_dec(v_val_2070_);
lean_dec(v_val_2038_);
lean_dec_ref(v_toRing_2037_);
v_a_2152_ = lean_ctor_get(v___x_2136_, 0);
v_isSharedCheck_2159_ = !lean_is_exclusive(v___x_2136_);
if (v_isSharedCheck_2159_ == 0)
{
v___x_2154_ = v___x_2136_;
v_isShared_2155_ = v_isSharedCheck_2159_;
goto v_resetjp_2153_;
}
else
{
lean_inc(v_a_2152_);
lean_dec(v___x_2136_);
v___x_2154_ = lean_box(0);
v_isShared_2155_ = v_isSharedCheck_2159_;
goto v_resetjp_2153_;
}
v_resetjp_2153_:
{
lean_object* v___x_2157_; 
if (v_isShared_2155_ == 0)
{
v___x_2157_ = v___x_2154_;
goto v_reusejp_2156_;
}
else
{
lean_object* v_reuseFailAlloc_2158_; 
v_reuseFailAlloc_2158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2158_, 0, v_a_2152_);
v___x_2157_ = v_reuseFailAlloc_2158_;
goto v_reusejp_2156_;
}
v_reusejp_2156_:
{
return v___x_2157_;
}
}
}
}
else
{
lean_object* v_a_2160_; lean_object* v___x_2162_; uint8_t v_isShared_2163_; uint8_t v_isSharedCheck_2167_; 
lean_del_object(v___x_2082_);
lean_dec(v_snd_2080_);
lean_dec(v_fst_2079_);
lean_dec(v_val_2070_);
lean_dec(v_val_2038_);
lean_dec_ref(v_toRing_2037_);
lean_dec_ref(v_e_2003_);
v_a_2160_ = lean_ctor_get(v___x_2134_, 0);
v_isSharedCheck_2167_ = !lean_is_exclusive(v___x_2134_);
if (v_isSharedCheck_2167_ == 0)
{
v___x_2162_ = v___x_2134_;
v_isShared_2163_ = v_isSharedCheck_2167_;
goto v_resetjp_2161_;
}
else
{
lean_inc(v_a_2160_);
lean_dec(v___x_2134_);
v___x_2162_ = lean_box(0);
v_isShared_2163_ = v_isSharedCheck_2167_;
goto v_resetjp_2161_;
}
v_resetjp_2161_:
{
lean_object* v___x_2165_; 
if (v_isShared_2163_ == 0)
{
v___x_2165_ = v___x_2162_;
goto v_reusejp_2164_;
}
else
{
lean_object* v_reuseFailAlloc_2166_; 
v_reuseFailAlloc_2166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2166_, 0, v_a_2160_);
v___x_2165_ = v_reuseFailAlloc_2166_;
goto v_reusejp_2164_;
}
v_reusejp_2164_:
{
return v___x_2165_;
}
}
}
}
}
else
{
lean_object* v___x_2168_; 
lean_dec(v_snd_2080_);
v___x_2168_ = l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__3(v_a_2006_, v_a_2007_, v_a_2008_, v_a_2009_, v_a_2010_, v_a_2011_, v_a_2012_, v_a_2013_, v_a_2014_, v_a_2015_, v_a_2016_);
if (lean_obj_tag(v___x_2168_) == 0)
{
lean_object* v_a_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; 
v_a_2169_ = lean_ctor_get(v___x_2168_, 0);
lean_inc(v_a_2169_);
lean_dec_ref(v___x_2168_);
v___x_2170_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__3, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__3);
v___x_2171_ = l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__4(v___x_2170_, v_a_2006_, v_a_2007_, v_a_2008_, v_a_2009_, v_a_2010_, v_a_2011_, v_a_2012_, v_a_2013_, v_a_2014_, v_a_2015_, v_a_2016_);
if (lean_obj_tag(v___x_2171_) == 0)
{
lean_object* v_a_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; 
v_a_2172_ = lean_ctor_get(v___x_2171_, 0);
lean_inc(v_a_2172_);
lean_dec_ref(v___x_2171_);
v___x_2173_ = l_Lean_mkAppB(v_a_2169_, v_a_2005_, v_e_2003_);
v___x_2174_ = l_Lean_Meta_mkEq(v___x_2173_, v_a_2172_, v_a_2013_, v_a_2014_, v_a_2015_, v_a_2016_);
if (lean_obj_tag(v___x_2174_) == 0)
{
lean_object* v_a_2175_; lean_object* v_type_2176_; lean_object* v_u_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; lean_object* v___x_2181_; 
v_a_2175_ = lean_ctor_get(v___x_2174_, 0);
lean_inc(v_a_2175_);
lean_dec_ref(v___x_2174_);
v_type_2176_ = lean_ctor_get(v_toRing_2037_, 1);
lean_inc_ref(v_type_2176_);
v_u_2177_ = lean_ctor_get(v_toRing_2037_, 2);
lean_inc(v_u_2177_);
lean_dec_ref(v_toRing_2037_);
v___x_2178_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__9));
v___x_2179_ = lean_box(0);
if (v_isShared_2083_ == 0)
{
lean_ctor_set_tag(v___x_2082_, 1);
lean_ctor_set(v___x_2082_, 1, v___x_2179_);
lean_ctor_set(v___x_2082_, 0, v_u_2177_);
v___x_2181_ = v___x_2082_;
goto v_reusejp_2180_;
}
else
{
lean_object* v_reuseFailAlloc_2188_; 
v_reuseFailAlloc_2188_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2188_, 0, v_u_2177_);
lean_ctor_set(v_reuseFailAlloc_2188_, 1, v___x_2179_);
v___x_2181_ = v_reuseFailAlloc_2188_;
goto v_reusejp_2180_;
}
v_reusejp_2180_:
{
lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; 
v___x_2182_ = l_Lean_mkConst(v___x_2178_, v___x_2181_);
v___x_2183_ = l_Lean_mkIntLit(v_val_2070_);
lean_dec(v_val_2070_);
v___x_2184_ = l_Lean_eagerReflBoolTrue;
v___x_2185_ = l_Lean_mkApp5(v___x_2182_, v_type_2176_, v_val_2038_, v_fst_2079_, v___x_2183_, v___x_2184_);
v___x_2186_ = l_Lean_Meta_mkExpectedPropHint(v___x_2185_, v_a_2175_);
v___x_2187_ = l_Lean_Meta_Grind_pushNewFact(v___x_2186_, v___x_2071_, v_a_2007_, v_a_2008_, v_a_2009_, v_a_2010_, v_a_2011_, v_a_2012_, v_a_2013_, v_a_2014_, v_a_2015_, v_a_2016_);
if (lean_obj_tag(v___x_2187_) == 0)
{
lean_dec_ref(v___x_2187_);
goto v___jp_2018_;
}
else
{
return v___x_2187_;
}
}
}
else
{
lean_object* v_a_2189_; lean_object* v___x_2191_; uint8_t v_isShared_2192_; uint8_t v_isSharedCheck_2196_; 
lean_del_object(v___x_2082_);
lean_dec(v_fst_2079_);
lean_dec(v_val_2070_);
lean_dec(v_val_2038_);
lean_dec_ref(v_toRing_2037_);
v_a_2189_ = lean_ctor_get(v___x_2174_, 0);
v_isSharedCheck_2196_ = !lean_is_exclusive(v___x_2174_);
if (v_isSharedCheck_2196_ == 0)
{
v___x_2191_ = v___x_2174_;
v_isShared_2192_ = v_isSharedCheck_2196_;
goto v_resetjp_2190_;
}
else
{
lean_inc(v_a_2189_);
lean_dec(v___x_2174_);
v___x_2191_ = lean_box(0);
v_isShared_2192_ = v_isSharedCheck_2196_;
goto v_resetjp_2190_;
}
v_resetjp_2190_:
{
lean_object* v___x_2194_; 
if (v_isShared_2192_ == 0)
{
v___x_2194_ = v___x_2191_;
goto v_reusejp_2193_;
}
else
{
lean_object* v_reuseFailAlloc_2195_; 
v_reuseFailAlloc_2195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2195_, 0, v_a_2189_);
v___x_2194_ = v_reuseFailAlloc_2195_;
goto v_reusejp_2193_;
}
v_reusejp_2193_:
{
return v___x_2194_;
}
}
}
}
else
{
lean_object* v_a_2197_; lean_object* v___x_2199_; uint8_t v_isShared_2200_; uint8_t v_isSharedCheck_2204_; 
lean_dec(v_a_2169_);
lean_del_object(v___x_2082_);
lean_dec(v_fst_2079_);
lean_dec(v_val_2070_);
lean_dec(v_val_2038_);
lean_dec_ref(v_toRing_2037_);
lean_dec_ref(v_a_2005_);
lean_dec_ref(v_e_2003_);
v_a_2197_ = lean_ctor_get(v___x_2171_, 0);
v_isSharedCheck_2204_ = !lean_is_exclusive(v___x_2171_);
if (v_isSharedCheck_2204_ == 0)
{
v___x_2199_ = v___x_2171_;
v_isShared_2200_ = v_isSharedCheck_2204_;
goto v_resetjp_2198_;
}
else
{
lean_inc(v_a_2197_);
lean_dec(v___x_2171_);
v___x_2199_ = lean_box(0);
v_isShared_2200_ = v_isSharedCheck_2204_;
goto v_resetjp_2198_;
}
v_resetjp_2198_:
{
lean_object* v___x_2202_; 
if (v_isShared_2200_ == 0)
{
v___x_2202_ = v___x_2199_;
goto v_reusejp_2201_;
}
else
{
lean_object* v_reuseFailAlloc_2203_; 
v_reuseFailAlloc_2203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2203_, 0, v_a_2197_);
v___x_2202_ = v_reuseFailAlloc_2203_;
goto v_reusejp_2201_;
}
v_reusejp_2201_:
{
return v___x_2202_;
}
}
}
}
else
{
lean_object* v_a_2205_; lean_object* v___x_2207_; uint8_t v_isShared_2208_; uint8_t v_isSharedCheck_2212_; 
lean_del_object(v___x_2082_);
lean_dec(v_fst_2079_);
lean_dec(v_val_2070_);
lean_dec(v_val_2038_);
lean_dec_ref(v_toRing_2037_);
lean_dec_ref(v_a_2005_);
lean_dec_ref(v_e_2003_);
v_a_2205_ = lean_ctor_get(v___x_2168_, 0);
v_isSharedCheck_2212_ = !lean_is_exclusive(v___x_2168_);
if (v_isSharedCheck_2212_ == 0)
{
v___x_2207_ = v___x_2168_;
v_isShared_2208_ = v_isSharedCheck_2212_;
goto v_resetjp_2206_;
}
else
{
lean_inc(v_a_2205_);
lean_dec(v___x_2168_);
v___x_2207_ = lean_box(0);
v_isShared_2208_ = v_isSharedCheck_2212_;
goto v_resetjp_2206_;
}
v_resetjp_2206_:
{
lean_object* v___x_2210_; 
if (v_isShared_2208_ == 0)
{
v___x_2210_ = v___x_2207_;
goto v_reusejp_2209_;
}
else
{
lean_object* v_reuseFailAlloc_2211_; 
v_reuseFailAlloc_2211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2211_, 0, v_a_2205_);
v___x_2210_ = v_reuseFailAlloc_2211_;
goto v_reusejp_2209_;
}
v_reusejp_2209_:
{
return v___x_2210_;
}
}
}
}
}
}
else
{
lean_object* v_a_2214_; lean_object* v___x_2216_; uint8_t v_isShared_2217_; uint8_t v_isSharedCheck_2221_; 
lean_dec(v_val_2070_);
lean_dec(v_val_2038_);
lean_dec_ref(v_toRing_2037_);
lean_dec_ref(v_a_2005_);
lean_dec_ref(v_e_2003_);
v_a_2214_ = lean_ctor_get(v___x_2077_, 0);
v_isSharedCheck_2221_ = !lean_is_exclusive(v___x_2077_);
if (v_isSharedCheck_2221_ == 0)
{
v___x_2216_ = v___x_2077_;
v_isShared_2217_ = v_isSharedCheck_2221_;
goto v_resetjp_2215_;
}
else
{
lean_inc(v_a_2214_);
lean_dec(v___x_2077_);
v___x_2216_ = lean_box(0);
v_isShared_2217_ = v_isSharedCheck_2221_;
goto v_resetjp_2215_;
}
v_resetjp_2215_:
{
lean_object* v___x_2219_; 
if (v_isShared_2217_ == 0)
{
v___x_2219_ = v___x_2216_;
goto v_reusejp_2218_;
}
else
{
lean_object* v_reuseFailAlloc_2220_; 
v_reuseFailAlloc_2220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2220_, 0, v_a_2214_);
v___x_2219_ = v_reuseFailAlloc_2220_;
goto v_reusejp_2218_;
}
v_reusejp_2218_:
{
return v___x_2219_;
}
}
}
}
}
else
{
lean_object* v_a_2222_; lean_object* v___x_2224_; uint8_t v_isShared_2225_; uint8_t v_isSharedCheck_2229_; 
lean_dec(v_val_2070_);
lean_dec(v_val_2038_);
lean_dec_ref(v_toRing_2037_);
lean_dec_ref(v_a_2005_);
lean_dec_ref(v_e_2003_);
v_a_2222_ = lean_ctor_get(v___x_2074_, 0);
v_isSharedCheck_2229_ = !lean_is_exclusive(v___x_2074_);
if (v_isSharedCheck_2229_ == 0)
{
v___x_2224_ = v___x_2074_;
v_isShared_2225_ = v_isSharedCheck_2229_;
goto v_resetjp_2223_;
}
else
{
lean_inc(v_a_2222_);
lean_dec(v___x_2074_);
v___x_2224_ = lean_box(0);
v_isShared_2225_ = v_isSharedCheck_2229_;
goto v_resetjp_2223_;
}
v_resetjp_2223_:
{
lean_object* v___x_2227_; 
if (v_isShared_2225_ == 0)
{
v___x_2227_ = v___x_2224_;
goto v_reusejp_2226_;
}
else
{
lean_object* v_reuseFailAlloc_2228_; 
v_reuseFailAlloc_2228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2228_, 0, v_a_2222_);
v___x_2227_ = v_reuseFailAlloc_2228_;
goto v_reusejp_2226_;
}
v_reusejp_2226_:
{
return v___x_2227_;
}
}
}
}
else
{
lean_object* v_type_2230_; lean_object* v_u_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; 
lean_dec(v_val_2070_);
v_type_2230_ = lean_ctor_get(v_toRing_2037_, 1);
lean_inc_ref(v_type_2230_);
v_u_2231_ = lean_ctor_get(v_toRing_2037_, 2);
lean_inc(v_u_2231_);
lean_dec_ref(v_toRing_2037_);
v___x_2232_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__11));
v___x_2233_ = lean_box(0);
v___x_2234_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2234_, 0, v_u_2231_);
lean_ctor_set(v___x_2234_, 1, v___x_2233_);
v___x_2235_ = l_Lean_mkConst(v___x_2232_, v___x_2234_);
v___x_2236_ = l_Lean_mkAppB(v___x_2235_, v_type_2230_, v_val_2038_);
v___x_2237_ = l_Lean_Meta_Grind_pushEqCore___redArg(v_e_2003_, v_a_2005_, v___x_2236_, v___x_2065_, v_a_2007_, v_a_2009_, v_a_2013_, v_a_2014_, v_a_2015_, v_a_2016_);
if (lean_obj_tag(v___x_2237_) == 0)
{
lean_object* v___x_2239_; uint8_t v_isShared_2240_; uint8_t v_isSharedCheck_2245_; 
v_isSharedCheck_2245_ = !lean_is_exclusive(v___x_2237_);
if (v_isSharedCheck_2245_ == 0)
{
lean_object* v_unused_2246_; 
v_unused_2246_ = lean_ctor_get(v___x_2237_, 0);
lean_dec(v_unused_2246_);
v___x_2239_ = v___x_2237_;
v_isShared_2240_ = v_isSharedCheck_2245_;
goto v_resetjp_2238_;
}
else
{
lean_dec(v___x_2237_);
v___x_2239_ = lean_box(0);
v_isShared_2240_ = v_isSharedCheck_2245_;
goto v_resetjp_2238_;
}
v_resetjp_2238_:
{
lean_object* v___x_2241_; lean_object* v___x_2243_; 
v___x_2241_ = lean_box(0);
if (v_isShared_2240_ == 0)
{
lean_ctor_set(v___x_2239_, 0, v___x_2241_);
v___x_2243_ = v___x_2239_;
goto v_reusejp_2242_;
}
else
{
lean_object* v_reuseFailAlloc_2244_; 
v_reuseFailAlloc_2244_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2244_, 0, v___x_2241_);
v___x_2243_ = v_reuseFailAlloc_2244_;
goto v_reusejp_2242_;
}
v_reusejp_2242_:
{
return v___x_2243_;
}
}
}
else
{
return v___x_2237_;
}
}
}
else
{
lean_dec(v_a_2069_);
lean_dec_ref(v_e_2003_);
v___y_2040_ = v_a_2007_;
v___y_2041_ = v_a_2008_;
v___y_2042_ = v_a_2009_;
v___y_2043_ = v_a_2010_;
v___y_2044_ = v_a_2011_;
v___y_2045_ = v_a_2012_;
v___y_2046_ = v_a_2013_;
v___y_2047_ = v_a_2014_;
v___y_2048_ = v_a_2015_;
v___y_2049_ = v_a_2016_;
goto v___jp_2039_;
}
}
else
{
lean_object* v_a_2247_; lean_object* v___x_2249_; uint8_t v_isShared_2250_; uint8_t v_isSharedCheck_2254_; 
lean_dec(v_val_2038_);
lean_dec_ref(v_toRing_2037_);
lean_dec_ref(v_a_2005_);
lean_dec_ref(v_e_2003_);
v_a_2247_ = lean_ctor_get(v___x_2068_, 0);
v_isSharedCheck_2254_ = !lean_is_exclusive(v___x_2068_);
if (v_isSharedCheck_2254_ == 0)
{
v___x_2249_ = v___x_2068_;
v_isShared_2250_ = v_isSharedCheck_2254_;
goto v_resetjp_2248_;
}
else
{
lean_inc(v_a_2247_);
lean_dec(v___x_2068_);
v___x_2249_ = lean_box(0);
v_isShared_2250_ = v_isSharedCheck_2254_;
goto v_resetjp_2248_;
}
v_resetjp_2248_:
{
lean_object* v___x_2252_; 
if (v_isShared_2250_ == 0)
{
v___x_2252_ = v___x_2249_;
goto v_reusejp_2251_;
}
else
{
lean_object* v_reuseFailAlloc_2253_; 
v_reuseFailAlloc_2253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2253_, 0, v_a_2247_);
v___x_2252_ = v_reuseFailAlloc_2253_;
goto v_reusejp_2251_;
}
v_reusejp_2251_:
{
return v___x_2252_;
}
}
}
}
else
{
lean_dec(v_val_2038_);
lean_dec_ref(v_toRing_2037_);
lean_dec_ref(v_a_2005_);
lean_dec_ref(v_e_2003_);
return v___x_2067_;
}
}
else
{
lean_object* v___x_2255_; lean_object* v___x_2257_; 
lean_dec(v_val_2038_);
lean_dec_ref(v_toRing_2037_);
lean_dec_ref(v_a_2005_);
lean_dec_ref(v_e_2003_);
v___x_2255_ = lean_box(0);
if (v_isShared_2063_ == 0)
{
lean_ctor_set(v___x_2062_, 0, v___x_2255_);
v___x_2257_ = v___x_2062_;
goto v_reusejp_2256_;
}
else
{
lean_object* v_reuseFailAlloc_2258_; 
v_reuseFailAlloc_2258_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2258_, 0, v___x_2255_);
v___x_2257_ = v_reuseFailAlloc_2258_;
goto v_reusejp_2256_;
}
v_reusejp_2256_:
{
return v___x_2257_;
}
}
}
}
else
{
lean_object* v_a_2260_; lean_object* v___x_2262_; uint8_t v_isShared_2263_; uint8_t v_isSharedCheck_2267_; 
lean_dec(v_val_2038_);
lean_dec_ref(v_toRing_2037_);
lean_dec_ref(v_a_2005_);
lean_dec_ref(v_e_2003_);
v_a_2260_ = lean_ctor_get(v___x_2059_, 0);
v_isSharedCheck_2267_ = !lean_is_exclusive(v___x_2059_);
if (v_isSharedCheck_2267_ == 0)
{
v___x_2262_ = v___x_2059_;
v_isShared_2263_ = v_isSharedCheck_2267_;
goto v_resetjp_2261_;
}
else
{
lean_inc(v_a_2260_);
lean_dec(v___x_2059_);
v___x_2262_ = lean_box(0);
v_isShared_2263_ = v_isSharedCheck_2267_;
goto v_resetjp_2261_;
}
v_resetjp_2261_:
{
lean_object* v___x_2265_; 
if (v_isShared_2263_ == 0)
{
v___x_2265_ = v___x_2262_;
goto v_reusejp_2264_;
}
else
{
lean_object* v_reuseFailAlloc_2266_; 
v_reuseFailAlloc_2266_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2266_, 0, v_a_2260_);
v___x_2265_ = v_reuseFailAlloc_2266_;
goto v_reusejp_2264_;
}
v_reusejp_2264_:
{
return v___x_2265_;
}
}
}
v___jp_2039_:
{
lean_object* v_type_2050_; lean_object* v_u_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; 
v_type_2050_ = lean_ctor_get(v_toRing_2037_, 1);
lean_inc_ref(v_type_2050_);
v_u_2051_ = lean_ctor_get(v_toRing_2037_, 2);
lean_inc(v_u_2051_);
lean_dec_ref(v_toRing_2037_);
v___x_2052_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__2));
v___x_2053_ = lean_box(0);
v___x_2054_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2054_, 0, v_u_2051_);
lean_ctor_set(v___x_2054_, 1, v___x_2053_);
v___x_2055_ = l_Lean_mkConst(v___x_2052_, v___x_2054_);
v___x_2056_ = l_Lean_mkApp3(v___x_2055_, v_type_2050_, v_val_2038_, v_a_2005_);
v___x_2057_ = lean_unsigned_to_nat(0u);
v___x_2058_ = l_Lean_Meta_Grind_pushNewFact(v___x_2056_, v___x_2057_, v___y_2040_, v___y_2041_, v___y_2042_, v___y_2043_, v___y_2044_, v___y_2045_, v___y_2046_, v___y_2047_, v___y_2048_, v___y_2049_);
return v___x_2058_;
}
}
else
{
lean_object* v___x_2268_; lean_object* v___x_2270_; 
lean_dec(v_fieldInst_x3f_2036_);
lean_dec(v_a_2032_);
lean_dec_ref(v_a_2005_);
lean_dec_ref(v_e_2003_);
v___x_2268_ = lean_box(0);
if (v_isShared_2035_ == 0)
{
lean_ctor_set(v___x_2034_, 0, v___x_2268_);
v___x_2270_ = v___x_2034_;
goto v_reusejp_2269_;
}
else
{
lean_object* v_reuseFailAlloc_2271_; 
v_reuseFailAlloc_2271_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2271_, 0, v___x_2268_);
v___x_2270_ = v_reuseFailAlloc_2271_;
goto v_reusejp_2269_;
}
v_reusejp_2269_:
{
return v___x_2270_;
}
}
}
}
else
{
lean_object* v_a_2273_; lean_object* v___x_2275_; uint8_t v_isShared_2276_; uint8_t v_isSharedCheck_2280_; 
lean_dec_ref(v_a_2005_);
lean_dec_ref(v_e_2003_);
v_a_2273_ = lean_ctor_get(v___x_2031_, 0);
v_isSharedCheck_2280_ = !lean_is_exclusive(v___x_2031_);
if (v_isSharedCheck_2280_ == 0)
{
v___x_2275_ = v___x_2031_;
v_isShared_2276_ = v_isSharedCheck_2280_;
goto v_resetjp_2274_;
}
else
{
lean_inc(v_a_2273_);
lean_dec(v___x_2031_);
v___x_2275_ = lean_box(0);
v_isShared_2276_ = v_isSharedCheck_2280_;
goto v_resetjp_2274_;
}
v_resetjp_2274_:
{
lean_object* v___x_2278_; 
if (v_isShared_2276_ == 0)
{
v___x_2278_ = v___x_2275_;
goto v_reusejp_2277_;
}
else
{
lean_object* v_reuseFailAlloc_2279_; 
v_reuseFailAlloc_2279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2279_, 0, v_a_2273_);
v___x_2278_ = v_reuseFailAlloc_2279_;
goto v_reusejp_2277_;
}
v_reusejp_2277_:
{
return v___x_2278_;
}
}
}
}
}
}
else
{
lean_object* v_a_2282_; lean_object* v___x_2284_; uint8_t v_isShared_2285_; uint8_t v_isSharedCheck_2289_; 
lean_dec_ref(v_a_2005_);
lean_dec_ref(v_e_2003_);
v_a_2282_ = lean_ctor_get(v___x_2021_, 0);
v_isSharedCheck_2289_ = !lean_is_exclusive(v___x_2021_);
if (v_isSharedCheck_2289_ == 0)
{
v___x_2284_ = v___x_2021_;
v_isShared_2285_ = v_isSharedCheck_2289_;
goto v_resetjp_2283_;
}
else
{
lean_inc(v_a_2282_);
lean_dec(v___x_2021_);
v___x_2284_ = lean_box(0);
v_isShared_2285_ = v_isSharedCheck_2289_;
goto v_resetjp_2283_;
}
v_resetjp_2283_:
{
lean_object* v___x_2287_; 
if (v_isShared_2285_ == 0)
{
v___x_2287_ = v___x_2284_;
goto v_reusejp_2286_;
}
else
{
lean_object* v_reuseFailAlloc_2288_; 
v_reuseFailAlloc_2288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2288_, 0, v_a_2282_);
v___x_2287_ = v_reuseFailAlloc_2288_;
goto v_reusejp_2286_;
}
v_reusejp_2286_:
{
return v___x_2287_;
}
}
}
v___jp_2018_:
{
lean_object* v___x_2019_; lean_object* v___x_2020_; 
v___x_2019_ = lean_box(0);
v___x_2020_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2020_, 0, v___x_2019_);
return v___x_2020_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___boxed(lean_object* v_e_2290_, lean_object* v_inst_2291_, lean_object* v_a_2292_, lean_object* v_a_2293_, lean_object* v_a_2294_, lean_object* v_a_2295_, lean_object* v_a_2296_, lean_object* v_a_2297_, lean_object* v_a_2298_, lean_object* v_a_2299_, lean_object* v_a_2300_, lean_object* v_a_2301_, lean_object* v_a_2302_, lean_object* v_a_2303_, lean_object* v_a_2304_){
_start:
{
lean_object* v_res_2305_; 
v_res_2305_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv(v_e_2290_, v_inst_2291_, v_a_2292_, v_a_2293_, v_a_2294_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_, v_a_2301_, v_a_2302_, v_a_2303_);
lean_dec(v_a_2303_);
lean_dec_ref(v_a_2302_);
lean_dec(v_a_2301_);
lean_dec_ref(v_a_2300_);
lean_dec(v_a_2299_);
lean_dec_ref(v_a_2298_);
lean_dec(v_a_2297_);
lean_dec_ref(v_a_2296_);
lean_dec(v_a_2295_);
lean_dec(v_a_2294_);
lean_dec_ref(v_a_2293_);
lean_dec_ref(v_inst_2291_);
return v_res_2305_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0(lean_object* v_00_u03b2_2306_, lean_object* v_x_2307_, lean_object* v_x_2308_, lean_object* v_x_2309_){
_start:
{
lean_object* v___x_2310_; 
v___x_2310_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0___redArg(v_x_2307_, v_x_2308_, v_x_2309_);
return v___x_2310_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1(lean_object* v_00_u03b2_2311_, lean_object* v_x_2312_, lean_object* v_x_2313_){
_start:
{
uint8_t v___x_2314_; 
v___x_2314_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1___redArg(v_x_2312_, v_x_2313_);
return v___x_2314_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1___boxed(lean_object* v_00_u03b2_2315_, lean_object* v_x_2316_, lean_object* v_x_2317_){
_start:
{
uint8_t v_res_2318_; lean_object* v_r_2319_; 
v_res_2318_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1(v_00_u03b2_2315_, v_x_2316_, v_x_2317_);
lean_dec_ref(v_x_2317_);
lean_dec_ref(v_x_2316_);
v_r_2319_ = lean_box(v_res_2318_);
return v_r_2319_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0(lean_object* v_00_u03b2_2320_, lean_object* v_x_2321_, size_t v_x_2322_, size_t v_x_2323_, lean_object* v_x_2324_, lean_object* v_x_2325_){
_start:
{
lean_object* v___x_2326_; 
v___x_2326_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg(v_x_2321_, v_x_2322_, v_x_2323_, v_x_2324_, v_x_2325_);
return v___x_2326_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2327_, lean_object* v_x_2328_, lean_object* v_x_2329_, lean_object* v_x_2330_, lean_object* v_x_2331_, lean_object* v_x_2332_){
_start:
{
size_t v_x_142026__boxed_2333_; size_t v_x_142027__boxed_2334_; lean_object* v_res_2335_; 
v_x_142026__boxed_2333_ = lean_unbox_usize(v_x_2329_);
lean_dec(v_x_2329_);
v_x_142027__boxed_2334_ = lean_unbox_usize(v_x_2330_);
lean_dec(v_x_2330_);
v_res_2335_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0(v_00_u03b2_2327_, v_x_2328_, v_x_142026__boxed_2333_, v_x_142027__boxed_2334_, v_x_2331_, v_x_2332_);
return v_res_2335_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1_spec__2(lean_object* v_00_u03b2_2336_, lean_object* v_x_2337_, size_t v_x_2338_, lean_object* v_x_2339_){
_start:
{
uint8_t v___x_2340_; 
v___x_2340_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1_spec__2___redArg(v_x_2337_, v_x_2338_, v_x_2339_);
return v___x_2340_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1_spec__2___boxed(lean_object* v_00_u03b2_2341_, lean_object* v_x_2342_, lean_object* v_x_2343_, lean_object* v_x_2344_){
_start:
{
size_t v_x_142043__boxed_2345_; uint8_t v_res_2346_; lean_object* v_r_2347_; 
v_x_142043__boxed_2345_ = lean_unbox_usize(v_x_2343_);
lean_dec(v_x_2343_);
v_res_2346_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1_spec__2(v_00_u03b2_2341_, v_x_2342_, v_x_142043__boxed_2345_, v_x_2344_);
lean_dec_ref(v_x_2344_);
lean_dec_ref(v_x_2342_);
v_r_2347_ = lean_box(v_res_2346_);
return v_r_2347_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_2348_, lean_object* v_n_2349_, lean_object* v_k_2350_, lean_object* v_v_2351_){
_start:
{
lean_object* v___x_2352_; 
v___x_2352_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0_spec__2___redArg(v_n_2349_, v_k_2350_, v_v_2351_);
return v___x_2352_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_2353_, size_t v_depth_2354_, lean_object* v_keys_2355_, lean_object* v_vals_2356_, lean_object* v_heq_2357_, lean_object* v_i_2358_, lean_object* v_entries_2359_){
_start:
{
lean_object* v___x_2360_; 
v___x_2360_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0_spec__3___redArg(v_depth_2354_, v_keys_2355_, v_vals_2356_, v_i_2358_, v_entries_2359_);
return v___x_2360_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b2_2361_, lean_object* v_depth_2362_, lean_object* v_keys_2363_, lean_object* v_vals_2364_, lean_object* v_heq_2365_, lean_object* v_i_2366_, lean_object* v_entries_2367_){
_start:
{
size_t v_depth_boxed_2368_; lean_object* v_res_2369_; 
v_depth_boxed_2368_ = lean_unbox_usize(v_depth_2362_);
lean_dec(v_depth_2362_);
v_res_2369_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0_spec__3(v_00_u03b2_2361_, v_depth_boxed_2368_, v_keys_2363_, v_vals_2364_, v_heq_2365_, v_i_2366_, v_entries_2367_);
lean_dec_ref(v_vals_2364_);
lean_dec_ref(v_keys_2363_);
return v_res_2369_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1_spec__2_spec__6(lean_object* v_00_u03b2_2370_, lean_object* v_keys_2371_, lean_object* v_vals_2372_, lean_object* v_heq_2373_, lean_object* v_i_2374_, lean_object* v_k_2375_){
_start:
{
uint8_t v___x_2376_; 
v___x_2376_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1_spec__2_spec__6___redArg(v_keys_2371_, v_i_2374_, v_k_2375_);
return v___x_2376_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1_spec__2_spec__6___boxed(lean_object* v_00_u03b2_2377_, lean_object* v_keys_2378_, lean_object* v_vals_2379_, lean_object* v_heq_2380_, lean_object* v_i_2381_, lean_object* v_k_2382_){
_start:
{
uint8_t v_res_2383_; lean_object* v_r_2384_; 
v_res_2383_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1_spec__2_spec__6(v_00_u03b2_2377_, v_keys_2378_, v_vals_2379_, v_heq_2380_, v_i_2381_, v_k_2382_);
lean_dec_ref(v_k_2382_);
lean_dec_ref(v_vals_2379_);
lean_dec_ref(v_keys_2378_);
v_r_2384_ = lean_box(v_res_2383_);
return v_r_2384_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0_spec__2_spec__6(lean_object* v_00_u03b2_2385_, lean_object* v_x_2386_, lean_object* v_x_2387_, lean_object* v_x_2388_, lean_object* v_x_2389_){
_start:
{
lean_object* v___x_2390_; 
v___x_2390_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0_spec__2_spec__6___redArg(v_x_2386_, v_x_2387_, v_x_2388_, v_x_2389_);
return v___x_2390_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars___lam__0(lean_object* v_size_2391_, lean_object* v_s_2392_){
_start:
{
lean_object* v_toRing_2393_; lean_object* v_invFn_x3f_2394_; lean_object* v_semiringId_x3f_2395_; lean_object* v_commSemiringInst_2396_; lean_object* v_commRingInst_2397_; lean_object* v_noZeroDivInst_x3f_2398_; lean_object* v_fieldInst_x3f_2399_; lean_object* v_powIdentityInst_x3f_2400_; lean_object* v_denoteEntries_2401_; lean_object* v_nextId_2402_; lean_object* v_steps_2403_; lean_object* v_queue_2404_; lean_object* v_basis_2405_; lean_object* v_diseqs_2406_; uint8_t v_recheck_2407_; lean_object* v_invSet_2408_; lean_object* v_numEq0_x3f_2409_; uint8_t v_numEq0Updated_2410_; lean_object* v___x_2412_; uint8_t v_isShared_2413_; uint8_t v_isSharedCheck_2417_; 
v_toRing_2393_ = lean_ctor_get(v_s_2392_, 0);
v_invFn_x3f_2394_ = lean_ctor_get(v_s_2392_, 1);
v_semiringId_x3f_2395_ = lean_ctor_get(v_s_2392_, 2);
v_commSemiringInst_2396_ = lean_ctor_get(v_s_2392_, 3);
v_commRingInst_2397_ = lean_ctor_get(v_s_2392_, 4);
v_noZeroDivInst_x3f_2398_ = lean_ctor_get(v_s_2392_, 5);
v_fieldInst_x3f_2399_ = lean_ctor_get(v_s_2392_, 6);
v_powIdentityInst_x3f_2400_ = lean_ctor_get(v_s_2392_, 7);
v_denoteEntries_2401_ = lean_ctor_get(v_s_2392_, 8);
v_nextId_2402_ = lean_ctor_get(v_s_2392_, 9);
v_steps_2403_ = lean_ctor_get(v_s_2392_, 10);
v_queue_2404_ = lean_ctor_get(v_s_2392_, 11);
v_basis_2405_ = lean_ctor_get(v_s_2392_, 12);
v_diseqs_2406_ = lean_ctor_get(v_s_2392_, 13);
v_recheck_2407_ = lean_ctor_get_uint8(v_s_2392_, sizeof(void*)*17);
v_invSet_2408_ = lean_ctor_get(v_s_2392_, 14);
v_numEq0_x3f_2409_ = lean_ctor_get(v_s_2392_, 16);
v_numEq0Updated_2410_ = lean_ctor_get_uint8(v_s_2392_, sizeof(void*)*17 + 1);
v_isSharedCheck_2417_ = !lean_is_exclusive(v_s_2392_);
if (v_isSharedCheck_2417_ == 0)
{
lean_object* v_unused_2418_; 
v_unused_2418_ = lean_ctor_get(v_s_2392_, 15);
lean_dec(v_unused_2418_);
v___x_2412_ = v_s_2392_;
v_isShared_2413_ = v_isSharedCheck_2417_;
goto v_resetjp_2411_;
}
else
{
lean_inc(v_numEq0_x3f_2409_);
lean_inc(v_invSet_2408_);
lean_inc(v_diseqs_2406_);
lean_inc(v_basis_2405_);
lean_inc(v_queue_2404_);
lean_inc(v_steps_2403_);
lean_inc(v_nextId_2402_);
lean_inc(v_denoteEntries_2401_);
lean_inc(v_powIdentityInst_x3f_2400_);
lean_inc(v_fieldInst_x3f_2399_);
lean_inc(v_noZeroDivInst_x3f_2398_);
lean_inc(v_commRingInst_2397_);
lean_inc(v_commSemiringInst_2396_);
lean_inc(v_semiringId_x3f_2395_);
lean_inc(v_invFn_x3f_2394_);
lean_inc(v_toRing_2393_);
lean_dec(v_s_2392_);
v___x_2412_ = lean_box(0);
v_isShared_2413_ = v_isSharedCheck_2417_;
goto v_resetjp_2411_;
}
v_resetjp_2411_:
{
lean_object* v___x_2415_; 
if (v_isShared_2413_ == 0)
{
lean_ctor_set(v___x_2412_, 15, v_size_2391_);
v___x_2415_ = v___x_2412_;
goto v_reusejp_2414_;
}
else
{
lean_object* v_reuseFailAlloc_2416_; 
v_reuseFailAlloc_2416_ = lean_alloc_ctor(0, 17, 2);
lean_ctor_set(v_reuseFailAlloc_2416_, 0, v_toRing_2393_);
lean_ctor_set(v_reuseFailAlloc_2416_, 1, v_invFn_x3f_2394_);
lean_ctor_set(v_reuseFailAlloc_2416_, 2, v_semiringId_x3f_2395_);
lean_ctor_set(v_reuseFailAlloc_2416_, 3, v_commSemiringInst_2396_);
lean_ctor_set(v_reuseFailAlloc_2416_, 4, v_commRingInst_2397_);
lean_ctor_set(v_reuseFailAlloc_2416_, 5, v_noZeroDivInst_x3f_2398_);
lean_ctor_set(v_reuseFailAlloc_2416_, 6, v_fieldInst_x3f_2399_);
lean_ctor_set(v_reuseFailAlloc_2416_, 7, v_powIdentityInst_x3f_2400_);
lean_ctor_set(v_reuseFailAlloc_2416_, 8, v_denoteEntries_2401_);
lean_ctor_set(v_reuseFailAlloc_2416_, 9, v_nextId_2402_);
lean_ctor_set(v_reuseFailAlloc_2416_, 10, v_steps_2403_);
lean_ctor_set(v_reuseFailAlloc_2416_, 11, v_queue_2404_);
lean_ctor_set(v_reuseFailAlloc_2416_, 12, v_basis_2405_);
lean_ctor_set(v_reuseFailAlloc_2416_, 13, v_diseqs_2406_);
lean_ctor_set(v_reuseFailAlloc_2416_, 14, v_invSet_2408_);
lean_ctor_set(v_reuseFailAlloc_2416_, 15, v_size_2391_);
lean_ctor_set(v_reuseFailAlloc_2416_, 16, v_numEq0_x3f_2409_);
lean_ctor_set_uint8(v_reuseFailAlloc_2416_, sizeof(void*)*17, v_recheck_2407_);
lean_ctor_set_uint8(v_reuseFailAlloc_2416_, sizeof(void*)*17 + 1, v_numEq0Updated_2410_);
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
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_2419_; double v___x_2420_; 
v___x_2419_ = lean_unsigned_to_nat(0u);
v___x_2420_ = lean_float_of_nat(v___x_2419_);
return v___x_2420_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg(lean_object* v_cls_2424_, lean_object* v_msg_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_){
_start:
{
lean_object* v_ref_2431_; lean_object* v___x_2432_; lean_object* v_a_2433_; lean_object* v___x_2435_; uint8_t v_isShared_2436_; uint8_t v_isSharedCheck_2477_; 
v_ref_2431_ = lean_ctor_get(v___y_2428_, 5);
v___x_2432_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1_spec__5_spec__8_spec__9(v_msg_2425_, v___y_2426_, v___y_2427_, v___y_2428_, v___y_2429_);
v_a_2433_ = lean_ctor_get(v___x_2432_, 0);
v_isSharedCheck_2477_ = !lean_is_exclusive(v___x_2432_);
if (v_isSharedCheck_2477_ == 0)
{
v___x_2435_ = v___x_2432_;
v_isShared_2436_ = v_isSharedCheck_2477_;
goto v_resetjp_2434_;
}
else
{
lean_inc(v_a_2433_);
lean_dec(v___x_2432_);
v___x_2435_ = lean_box(0);
v_isShared_2436_ = v_isSharedCheck_2477_;
goto v_resetjp_2434_;
}
v_resetjp_2434_:
{
lean_object* v___x_2437_; lean_object* v_traceState_2438_; lean_object* v_env_2439_; lean_object* v_nextMacroScope_2440_; lean_object* v_ngen_2441_; lean_object* v_auxDeclNGen_2442_; lean_object* v_cache_2443_; lean_object* v_messages_2444_; lean_object* v_infoState_2445_; lean_object* v_snapshotTasks_2446_; lean_object* v___x_2448_; uint8_t v_isShared_2449_; uint8_t v_isSharedCheck_2476_; 
v___x_2437_ = lean_st_ref_take(v___y_2429_);
v_traceState_2438_ = lean_ctor_get(v___x_2437_, 4);
v_env_2439_ = lean_ctor_get(v___x_2437_, 0);
v_nextMacroScope_2440_ = lean_ctor_get(v___x_2437_, 1);
v_ngen_2441_ = lean_ctor_get(v___x_2437_, 2);
v_auxDeclNGen_2442_ = lean_ctor_get(v___x_2437_, 3);
v_cache_2443_ = lean_ctor_get(v___x_2437_, 5);
v_messages_2444_ = lean_ctor_get(v___x_2437_, 6);
v_infoState_2445_ = lean_ctor_get(v___x_2437_, 7);
v_snapshotTasks_2446_ = lean_ctor_get(v___x_2437_, 8);
v_isSharedCheck_2476_ = !lean_is_exclusive(v___x_2437_);
if (v_isSharedCheck_2476_ == 0)
{
v___x_2448_ = v___x_2437_;
v_isShared_2449_ = v_isSharedCheck_2476_;
goto v_resetjp_2447_;
}
else
{
lean_inc(v_snapshotTasks_2446_);
lean_inc(v_infoState_2445_);
lean_inc(v_messages_2444_);
lean_inc(v_cache_2443_);
lean_inc(v_traceState_2438_);
lean_inc(v_auxDeclNGen_2442_);
lean_inc(v_ngen_2441_);
lean_inc(v_nextMacroScope_2440_);
lean_inc(v_env_2439_);
lean_dec(v___x_2437_);
v___x_2448_ = lean_box(0);
v_isShared_2449_ = v_isSharedCheck_2476_;
goto v_resetjp_2447_;
}
v_resetjp_2447_:
{
uint64_t v_tid_2450_; lean_object* v_traces_2451_; lean_object* v___x_2453_; uint8_t v_isShared_2454_; uint8_t v_isSharedCheck_2475_; 
v_tid_2450_ = lean_ctor_get_uint64(v_traceState_2438_, sizeof(void*)*1);
v_traces_2451_ = lean_ctor_get(v_traceState_2438_, 0);
v_isSharedCheck_2475_ = !lean_is_exclusive(v_traceState_2438_);
if (v_isSharedCheck_2475_ == 0)
{
v___x_2453_ = v_traceState_2438_;
v_isShared_2454_ = v_isSharedCheck_2475_;
goto v_resetjp_2452_;
}
else
{
lean_inc(v_traces_2451_);
lean_dec(v_traceState_2438_);
v___x_2453_ = lean_box(0);
v_isShared_2454_ = v_isSharedCheck_2475_;
goto v_resetjp_2452_;
}
v_resetjp_2452_:
{
lean_object* v___x_2455_; double v___x_2456_; uint8_t v___x_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2465_; 
v___x_2455_ = lean_box(0);
v___x_2456_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg___closed__0);
v___x_2457_ = 0;
v___x_2458_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg___closed__1));
v___x_2459_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2459_, 0, v_cls_2424_);
lean_ctor_set(v___x_2459_, 1, v___x_2455_);
lean_ctor_set(v___x_2459_, 2, v___x_2458_);
lean_ctor_set_float(v___x_2459_, sizeof(void*)*3, v___x_2456_);
lean_ctor_set_float(v___x_2459_, sizeof(void*)*3 + 8, v___x_2456_);
lean_ctor_set_uint8(v___x_2459_, sizeof(void*)*3 + 16, v___x_2457_);
v___x_2460_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg___closed__2));
v___x_2461_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2461_, 0, v___x_2459_);
lean_ctor_set(v___x_2461_, 1, v_a_2433_);
lean_ctor_set(v___x_2461_, 2, v___x_2460_);
lean_inc(v_ref_2431_);
v___x_2462_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2462_, 0, v_ref_2431_);
lean_ctor_set(v___x_2462_, 1, v___x_2461_);
v___x_2463_ = l_Lean_PersistentArray_push___redArg(v_traces_2451_, v___x_2462_);
if (v_isShared_2454_ == 0)
{
lean_ctor_set(v___x_2453_, 0, v___x_2463_);
v___x_2465_ = v___x_2453_;
goto v_reusejp_2464_;
}
else
{
lean_object* v_reuseFailAlloc_2474_; 
v_reuseFailAlloc_2474_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2474_, 0, v___x_2463_);
lean_ctor_set_uint64(v_reuseFailAlloc_2474_, sizeof(void*)*1, v_tid_2450_);
v___x_2465_ = v_reuseFailAlloc_2474_;
goto v_reusejp_2464_;
}
v_reusejp_2464_:
{
lean_object* v___x_2467_; 
if (v_isShared_2449_ == 0)
{
lean_ctor_set(v___x_2448_, 4, v___x_2465_);
v___x_2467_ = v___x_2448_;
goto v_reusejp_2466_;
}
else
{
lean_object* v_reuseFailAlloc_2473_; 
v_reuseFailAlloc_2473_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2473_, 0, v_env_2439_);
lean_ctor_set(v_reuseFailAlloc_2473_, 1, v_nextMacroScope_2440_);
lean_ctor_set(v_reuseFailAlloc_2473_, 2, v_ngen_2441_);
lean_ctor_set(v_reuseFailAlloc_2473_, 3, v_auxDeclNGen_2442_);
lean_ctor_set(v_reuseFailAlloc_2473_, 4, v___x_2465_);
lean_ctor_set(v_reuseFailAlloc_2473_, 5, v_cache_2443_);
lean_ctor_set(v_reuseFailAlloc_2473_, 6, v_messages_2444_);
lean_ctor_set(v_reuseFailAlloc_2473_, 7, v_infoState_2445_);
lean_ctor_set(v_reuseFailAlloc_2473_, 8, v_snapshotTasks_2446_);
v___x_2467_ = v_reuseFailAlloc_2473_;
goto v_reusejp_2466_;
}
v_reusejp_2466_:
{
lean_object* v___x_2468_; lean_object* v___x_2469_; lean_object* v___x_2471_; 
v___x_2468_ = lean_st_ref_set(v___y_2429_, v___x_2467_);
v___x_2469_ = lean_box(0);
if (v_isShared_2436_ == 0)
{
lean_ctor_set(v___x_2435_, 0, v___x_2469_);
v___x_2471_ = v___x_2435_;
goto v_reusejp_2470_;
}
else
{
lean_object* v_reuseFailAlloc_2472_; 
v_reuseFailAlloc_2472_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2472_, 0, v___x_2469_);
v___x_2471_ = v_reuseFailAlloc_2472_;
goto v_reusejp_2470_;
}
v_reusejp_2470_:
{
return v___x_2471_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg___boxed(lean_object* v_cls_2478_, lean_object* v_msg_2479_, lean_object* v___y_2480_, lean_object* v___y_2481_, lean_object* v___y_2482_, lean_object* v___y_2483_, lean_object* v___y_2484_){
_start:
{
lean_object* v_res_2485_; 
v_res_2485_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg(v_cls_2478_, v_msg_2479_, v___y_2480_, v___y_2481_, v___y_2482_, v___y_2483_);
lean_dec(v___y_2483_);
lean_dec_ref(v___y_2482_);
lean_dec(v___y_2481_);
lean_dec_ref(v___y_2480_);
return v_res_2485_;
}
}
static lean_object* _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__8(void){
_start:
{
lean_object* v___x_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; 
v___x_2501_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__5));
v___x_2502_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__7));
v___x_2503_ = l_Lean_Name_append(v___x_2502_, v___x_2501_);
return v___x_2503_;
}
}
static lean_object* _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__10(void){
_start:
{
lean_object* v___x_2505_; lean_object* v___x_2506_; 
v___x_2505_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__9));
v___x_2506_ = l_Lean_stringToMessageData(v___x_2505_);
return v___x_2506_;
}
}
static lean_object* _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__12(void){
_start:
{
lean_object* v___x_2508_; lean_object* v___x_2509_; 
v___x_2508_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__11));
v___x_2509_ = l_Lean_stringToMessageData(v___x_2508_);
return v___x_2509_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg(lean_object* v___x_2510_, lean_object* v_snd_2511_, lean_object* v_fst_2512_, lean_object* v_fst_2513_, lean_object* v___x_2514_, lean_object* v_range_2515_, lean_object* v_b_2516_, lean_object* v_i_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_, lean_object* v___y_2524_, lean_object* v___y_2525_, lean_object* v___y_2526_, lean_object* v___y_2527_, lean_object* v___y_2528_){
_start:
{
lean_object* v_stop_2530_; lean_object* v_step_2531_; uint8_t v___x_2532_; 
v_stop_2530_ = lean_ctor_get(v_range_2515_, 1);
v_step_2531_ = lean_ctor_get(v_range_2515_, 2);
v___x_2532_ = lean_nat_dec_lt(v_i_2517_, v_stop_2530_);
if (v___x_2532_ == 0)
{
lean_object* v___x_2533_; 
lean_dec(v_i_2517_);
lean_dec_ref(v_fst_2513_);
lean_dec_ref(v_fst_2512_);
lean_dec(v_snd_2511_);
lean_dec_ref(v___x_2510_);
v___x_2533_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2533_, 0, v_b_2516_);
return v___x_2533_;
}
else
{
lean_object* v_size_2534_; lean_object* v___x_2535_; lean_object* v___y_2537_; lean_object* v___y_2538_; lean_object* v___y_2539_; lean_object* v___y_2540_; lean_object* v___y_2541_; lean_object* v___y_2542_; lean_object* v___y_2543_; lean_object* v___y_2544_; lean_object* v___y_2545_; lean_object* v___y_2546_; lean_object* v___y_2547_; lean_object* v___y_2561_; lean_object* v___x_2586_; uint8_t v___x_2587_; 
v_size_2534_ = lean_ctor_get(v___x_2514_, 2);
v___x_2535_ = lean_box(0);
v___x_2586_ = l_Lean_instInhabitedExpr;
v___x_2587_ = lean_nat_dec_lt(v_i_2517_, v_size_2534_);
if (v___x_2587_ == 0)
{
lean_object* v___x_2588_; 
v___x_2588_ = l_outOfBounds___redArg(v___x_2586_);
v___y_2561_ = v___x_2588_;
goto v___jp_2560_;
}
else
{
lean_object* v___x_2589_; 
v___x_2589_ = l_Lean_PersistentArray_get_x21___redArg(v___x_2586_, v___x_2514_, v_i_2517_);
v___y_2561_ = v___x_2589_;
goto v___jp_2560_;
}
v___jp_2536_:
{
lean_object* v_type_2548_; lean_object* v_u_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; 
v_type_2548_ = lean_ctor_get(v___x_2510_, 1);
v_u_2549_ = lean_ctor_get(v___x_2510_, 2);
v___x_2550_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__2));
v___x_2551_ = lean_box(0);
lean_inc(v_u_2549_);
v___x_2552_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2552_, 0, v_u_2549_);
lean_ctor_set(v___x_2552_, 1, v___x_2551_);
v___x_2553_ = l_Lean_mkConst(v___x_2550_, v___x_2552_);
lean_inc(v_snd_2511_);
v___x_2554_ = l_Lean_mkNatLit(v_snd_2511_);
lean_inc_ref(v_fst_2513_);
lean_inc_ref(v_fst_2512_);
lean_inc_ref(v_type_2548_);
v___x_2555_ = l_Lean_mkApp5(v___x_2553_, v_type_2548_, v_fst_2512_, v___x_2554_, v_fst_2513_, v___y_2537_);
v___x_2556_ = lean_unsigned_to_nat(0u);
v___x_2557_ = l_Lean_Meta_Grind_pushNewFact(v___x_2555_, v___x_2556_, v___y_2538_, v___y_2539_, v___y_2540_, v___y_2541_, v___y_2542_, v___y_2543_, v___y_2544_, v___y_2545_, v___y_2546_, v___y_2547_);
if (lean_obj_tag(v___x_2557_) == 0)
{
lean_object* v___x_2558_; 
lean_dec_ref(v___x_2557_);
v___x_2558_ = lean_nat_add(v_i_2517_, v_step_2531_);
lean_dec(v_i_2517_);
v_b_2516_ = v___x_2535_;
v_i_2517_ = v___x_2558_;
goto _start;
}
else
{
lean_dec(v_i_2517_);
lean_dec_ref(v_fst_2513_);
lean_dec_ref(v_fst_2512_);
lean_dec(v_snd_2511_);
lean_dec_ref(v___x_2510_);
return v___x_2557_;
}
}
v___jp_2560_:
{
lean_object* v_options_2562_; uint8_t v_hasTrace_2563_; 
v_options_2562_ = lean_ctor_get(v___y_2527_, 2);
v_hasTrace_2563_ = lean_ctor_get_uint8(v_options_2562_, sizeof(void*)*1);
if (v_hasTrace_2563_ == 0)
{
v___y_2537_ = v___y_2561_;
v___y_2538_ = v___y_2519_;
v___y_2539_ = v___y_2520_;
v___y_2540_ = v___y_2521_;
v___y_2541_ = v___y_2522_;
v___y_2542_ = v___y_2523_;
v___y_2543_ = v___y_2524_;
v___y_2544_ = v___y_2525_;
v___y_2545_ = v___y_2526_;
v___y_2546_ = v___y_2527_;
v___y_2547_ = v___y_2528_;
goto v___jp_2536_;
}
else
{
lean_object* v_inheritedTraceOptions_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; uint8_t v___x_2567_; 
v_inheritedTraceOptions_2564_ = lean_ctor_get(v___y_2527_, 13);
v___x_2565_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__5));
v___x_2566_ = lean_obj_once(&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__8, &l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__8_once, _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__8);
v___x_2567_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2564_, v_options_2562_, v___x_2566_);
if (v___x_2567_ == 0)
{
v___y_2537_ = v___y_2561_;
v___y_2538_ = v___y_2519_;
v___y_2539_ = v___y_2520_;
v___y_2540_ = v___y_2521_;
v___y_2541_ = v___y_2522_;
v___y_2542_ = v___y_2523_;
v___y_2543_ = v___y_2524_;
v___y_2544_ = v___y_2525_;
v___y_2545_ = v___y_2526_;
v___y_2546_ = v___y_2527_;
v___y_2547_ = v___y_2528_;
goto v___jp_2536_;
}
else
{
lean_object* v___x_2568_; 
v___x_2568_ = l_Lean_Meta_Grind_updateLastTag(v___y_2519_, v___y_2520_, v___y_2521_, v___y_2522_, v___y_2523_, v___y_2524_, v___y_2525_, v___y_2526_, v___y_2527_, v___y_2528_);
if (lean_obj_tag(v___x_2568_) == 0)
{
lean_object* v___x_2570_; uint8_t v_isShared_2571_; uint8_t v_isSharedCheck_2584_; 
v_isSharedCheck_2584_ = !lean_is_exclusive(v___x_2568_);
if (v_isSharedCheck_2584_ == 0)
{
lean_object* v_unused_2585_; 
v_unused_2585_ = lean_ctor_get(v___x_2568_, 0);
lean_dec(v_unused_2585_);
v___x_2570_ = v___x_2568_;
v_isShared_2571_ = v_isSharedCheck_2584_;
goto v_resetjp_2569_;
}
else
{
lean_dec(v___x_2568_);
v___x_2570_ = lean_box(0);
v_isShared_2571_ = v_isSharedCheck_2584_;
goto v_resetjp_2569_;
}
v_resetjp_2569_:
{
lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2575_; 
v___x_2572_ = lean_obj_once(&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__10, &l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__10_once, _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__10);
lean_inc(v_snd_2511_);
v___x_2573_ = l_Nat_reprFast(v_snd_2511_);
if (v_isShared_2571_ == 0)
{
lean_ctor_set_tag(v___x_2570_, 3);
lean_ctor_set(v___x_2570_, 0, v___x_2573_);
v___x_2575_ = v___x_2570_;
goto v_reusejp_2574_;
}
else
{
lean_object* v_reuseFailAlloc_2583_; 
v_reuseFailAlloc_2583_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2583_, 0, v___x_2573_);
v___x_2575_ = v_reuseFailAlloc_2583_;
goto v_reusejp_2574_;
}
v_reusejp_2574_:
{
lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; 
v___x_2576_ = l_Lean_MessageData_ofFormat(v___x_2575_);
v___x_2577_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2577_, 0, v___x_2572_);
lean_ctor_set(v___x_2577_, 1, v___x_2576_);
v___x_2578_ = lean_obj_once(&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__12, &l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__12_once, _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__12);
v___x_2579_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2579_, 0, v___x_2577_);
lean_ctor_set(v___x_2579_, 1, v___x_2578_);
lean_inc_ref(v___y_2561_);
v___x_2580_ = l_Lean_MessageData_ofExpr(v___y_2561_);
v___x_2581_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2581_, 0, v___x_2579_);
lean_ctor_set(v___x_2581_, 1, v___x_2580_);
v___x_2582_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg(v___x_2565_, v___x_2581_, v___y_2525_, v___y_2526_, v___y_2527_, v___y_2528_);
if (lean_obj_tag(v___x_2582_) == 0)
{
lean_dec_ref(v___x_2582_);
v___y_2537_ = v___y_2561_;
v___y_2538_ = v___y_2519_;
v___y_2539_ = v___y_2520_;
v___y_2540_ = v___y_2521_;
v___y_2541_ = v___y_2522_;
v___y_2542_ = v___y_2523_;
v___y_2543_ = v___y_2524_;
v___y_2544_ = v___y_2525_;
v___y_2545_ = v___y_2526_;
v___y_2546_ = v___y_2527_;
v___y_2547_ = v___y_2528_;
goto v___jp_2536_;
}
else
{
lean_dec_ref(v___y_2561_);
lean_dec(v_i_2517_);
lean_dec_ref(v_fst_2513_);
lean_dec_ref(v_fst_2512_);
lean_dec(v_snd_2511_);
lean_dec_ref(v___x_2510_);
return v___x_2582_;
}
}
}
}
else
{
lean_dec_ref(v___y_2561_);
lean_dec(v_i_2517_);
lean_dec_ref(v_fst_2513_);
lean_dec_ref(v_fst_2512_);
lean_dec(v_snd_2511_);
lean_dec_ref(v___x_2510_);
return v___x_2568_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___boxed(lean_object** _args){
lean_object* v___x_2590_ = _args[0];
lean_object* v_snd_2591_ = _args[1];
lean_object* v_fst_2592_ = _args[2];
lean_object* v_fst_2593_ = _args[3];
lean_object* v___x_2594_ = _args[4];
lean_object* v_range_2595_ = _args[5];
lean_object* v_b_2596_ = _args[6];
lean_object* v_i_2597_ = _args[7];
lean_object* v___y_2598_ = _args[8];
lean_object* v___y_2599_ = _args[9];
lean_object* v___y_2600_ = _args[10];
lean_object* v___y_2601_ = _args[11];
lean_object* v___y_2602_ = _args[12];
lean_object* v___y_2603_ = _args[13];
lean_object* v___y_2604_ = _args[14];
lean_object* v___y_2605_ = _args[15];
lean_object* v___y_2606_ = _args[16];
lean_object* v___y_2607_ = _args[17];
lean_object* v___y_2608_ = _args[18];
lean_object* v___y_2609_ = _args[19];
_start:
{
lean_object* v_res_2610_; 
v_res_2610_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg(v___x_2590_, v_snd_2591_, v_fst_2592_, v_fst_2593_, v___x_2594_, v_range_2595_, v_b_2596_, v_i_2597_, v___y_2598_, v___y_2599_, v___y_2600_, v___y_2601_, v___y_2602_, v___y_2603_, v___y_2604_, v___y_2605_, v___y_2606_, v___y_2607_, v___y_2608_);
lean_dec(v___y_2608_);
lean_dec_ref(v___y_2607_);
lean_dec(v___y_2606_);
lean_dec_ref(v___y_2605_);
lean_dec(v___y_2604_);
lean_dec_ref(v___y_2603_);
lean_dec(v___y_2602_);
lean_dec_ref(v___y_2601_);
lean_dec(v___y_2600_);
lean_dec(v___y_2599_);
lean_dec_ref(v___y_2598_);
lean_dec_ref(v_range_2595_);
lean_dec_ref(v___x_2594_);
return v_res_2610_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars(lean_object* v_a_2611_, lean_object* v_a_2612_, lean_object* v_a_2613_, lean_object* v_a_2614_, lean_object* v_a_2615_, lean_object* v_a_2616_, lean_object* v_a_2617_, lean_object* v_a_2618_, lean_object* v_a_2619_, lean_object* v_a_2620_, lean_object* v_a_2621_){
_start:
{
lean_object* v___x_2623_; 
v___x_2623_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v_a_2611_, v_a_2612_, v_a_2613_, v_a_2614_, v_a_2615_, v_a_2616_, v_a_2617_, v_a_2618_, v_a_2619_, v_a_2620_, v_a_2621_);
if (lean_obj_tag(v___x_2623_) == 0)
{
lean_object* v_a_2624_; lean_object* v___x_2626_; uint8_t v_isShared_2627_; uint8_t v_isSharedCheck_2653_; 
v_a_2624_ = lean_ctor_get(v___x_2623_, 0);
v_isSharedCheck_2653_ = !lean_is_exclusive(v___x_2623_);
if (v_isSharedCheck_2653_ == 0)
{
v___x_2626_ = v___x_2623_;
v_isShared_2627_ = v_isSharedCheck_2653_;
goto v_resetjp_2625_;
}
else
{
lean_inc(v_a_2624_);
lean_dec(v___x_2623_);
v___x_2626_ = lean_box(0);
v_isShared_2627_ = v_isSharedCheck_2653_;
goto v_resetjp_2625_;
}
v_resetjp_2625_:
{
lean_object* v_powIdentityInst_x3f_2628_; 
v_powIdentityInst_x3f_2628_ = lean_ctor_get(v_a_2624_, 7);
if (lean_obj_tag(v_powIdentityInst_x3f_2628_) == 1)
{
lean_object* v_val_2629_; lean_object* v_snd_2630_; lean_object* v_toRing_2631_; lean_object* v_vars_2632_; lean_object* v_powIdentityVarCount_2633_; lean_object* v_fst_2634_; lean_object* v_fst_2635_; lean_object* v_snd_2636_; lean_object* v_size_2637_; uint8_t v___x_2638_; 
v_val_2629_ = lean_ctor_get(v_powIdentityInst_x3f_2628_, 0);
lean_inc(v_val_2629_);
v_snd_2630_ = lean_ctor_get(v_val_2629_, 1);
lean_inc(v_snd_2630_);
v_toRing_2631_ = lean_ctor_get(v_a_2624_, 0);
lean_inc_ref(v_toRing_2631_);
v_vars_2632_ = lean_ctor_get(v_toRing_2631_, 14);
lean_inc_ref(v_vars_2632_);
v_powIdentityVarCount_2633_ = lean_ctor_get(v_a_2624_, 15);
lean_inc(v_powIdentityVarCount_2633_);
lean_dec(v_a_2624_);
v_fst_2634_ = lean_ctor_get(v_val_2629_, 0);
lean_inc(v_fst_2634_);
lean_dec(v_val_2629_);
v_fst_2635_ = lean_ctor_get(v_snd_2630_, 0);
lean_inc(v_fst_2635_);
v_snd_2636_ = lean_ctor_get(v_snd_2630_, 1);
lean_inc(v_snd_2636_);
lean_dec(v_snd_2630_);
v_size_2637_ = lean_ctor_get(v_vars_2632_, 2);
lean_inc(v_size_2637_);
v___x_2638_ = lean_nat_dec_le(v_size_2637_, v_powIdentityVarCount_2633_);
if (v___x_2638_ == 0)
{
lean_object* v___x_2639_; lean_object* v___x_2640_; lean_object* v___x_2641_; lean_object* v___x_2642_; 
lean_del_object(v___x_2626_);
v___x_2639_ = lean_unsigned_to_nat(1u);
lean_inc(v_size_2637_);
lean_inc(v_powIdentityVarCount_2633_);
v___x_2640_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2640_, 0, v_powIdentityVarCount_2633_);
lean_ctor_set(v___x_2640_, 1, v_size_2637_);
lean_ctor_set(v___x_2640_, 2, v___x_2639_);
v___x_2641_ = lean_box(0);
v___x_2642_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg(v_toRing_2631_, v_snd_2636_, v_fst_2635_, v_fst_2634_, v_vars_2632_, v___x_2640_, v___x_2641_, v_powIdentityVarCount_2633_, v_a_2611_, v_a_2612_, v_a_2613_, v_a_2614_, v_a_2615_, v_a_2616_, v_a_2617_, v_a_2618_, v_a_2619_, v_a_2620_, v_a_2621_);
lean_dec_ref(v___x_2640_);
lean_dec_ref(v_vars_2632_);
if (lean_obj_tag(v___x_2642_) == 0)
{
lean_object* v___f_2643_; lean_object* v___x_2644_; 
lean_dec_ref(v___x_2642_);
v___f_2643_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars___lam__0), 2, 1);
lean_closure_set(v___f_2643_, 0, v_size_2637_);
v___x_2644_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(v___f_2643_, v_a_2611_, v_a_2612_);
return v___x_2644_;
}
else
{
lean_dec(v_size_2637_);
return v___x_2642_;
}
}
else
{
lean_object* v___x_2645_; lean_object* v___x_2647_; 
lean_dec(v_size_2637_);
lean_dec(v_snd_2636_);
lean_dec(v_fst_2635_);
lean_dec(v_fst_2634_);
lean_dec(v_powIdentityVarCount_2633_);
lean_dec_ref(v_vars_2632_);
lean_dec_ref(v_toRing_2631_);
v___x_2645_ = lean_box(0);
if (v_isShared_2627_ == 0)
{
lean_ctor_set(v___x_2626_, 0, v___x_2645_);
v___x_2647_ = v___x_2626_;
goto v_reusejp_2646_;
}
else
{
lean_object* v_reuseFailAlloc_2648_; 
v_reuseFailAlloc_2648_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2648_, 0, v___x_2645_);
v___x_2647_ = v_reuseFailAlloc_2648_;
goto v_reusejp_2646_;
}
v_reusejp_2646_:
{
return v___x_2647_;
}
}
}
else
{
lean_object* v___x_2649_; lean_object* v___x_2651_; 
lean_dec(v_a_2624_);
v___x_2649_ = lean_box(0);
if (v_isShared_2627_ == 0)
{
lean_ctor_set(v___x_2626_, 0, v___x_2649_);
v___x_2651_ = v___x_2626_;
goto v_reusejp_2650_;
}
else
{
lean_object* v_reuseFailAlloc_2652_; 
v_reuseFailAlloc_2652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2652_, 0, v___x_2649_);
v___x_2651_ = v_reuseFailAlloc_2652_;
goto v_reusejp_2650_;
}
v_reusejp_2650_:
{
return v___x_2651_;
}
}
}
}
else
{
lean_object* v_a_2654_; lean_object* v___x_2656_; uint8_t v_isShared_2657_; uint8_t v_isSharedCheck_2661_; 
v_a_2654_ = lean_ctor_get(v___x_2623_, 0);
v_isSharedCheck_2661_ = !lean_is_exclusive(v___x_2623_);
if (v_isSharedCheck_2661_ == 0)
{
v___x_2656_ = v___x_2623_;
v_isShared_2657_ = v_isSharedCheck_2661_;
goto v_resetjp_2655_;
}
else
{
lean_inc(v_a_2654_);
lean_dec(v___x_2623_);
v___x_2656_ = lean_box(0);
v_isShared_2657_ = v_isSharedCheck_2661_;
goto v_resetjp_2655_;
}
v_resetjp_2655_:
{
lean_object* v___x_2659_; 
if (v_isShared_2657_ == 0)
{
v___x_2659_ = v___x_2656_;
goto v_reusejp_2658_;
}
else
{
lean_object* v_reuseFailAlloc_2660_; 
v_reuseFailAlloc_2660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2660_, 0, v_a_2654_);
v___x_2659_ = v_reuseFailAlloc_2660_;
goto v_reusejp_2658_;
}
v_reusejp_2658_:
{
return v___x_2659_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars___boxed(lean_object* v_a_2662_, lean_object* v_a_2663_, lean_object* v_a_2664_, lean_object* v_a_2665_, lean_object* v_a_2666_, lean_object* v_a_2667_, lean_object* v_a_2668_, lean_object* v_a_2669_, lean_object* v_a_2670_, lean_object* v_a_2671_, lean_object* v_a_2672_, lean_object* v_a_2673_){
_start:
{
lean_object* v_res_2674_; 
v_res_2674_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars(v_a_2662_, v_a_2663_, v_a_2664_, v_a_2665_, v_a_2666_, v_a_2667_, v_a_2668_, v_a_2669_, v_a_2670_, v_a_2671_, v_a_2672_);
lean_dec(v_a_2672_);
lean_dec_ref(v_a_2671_);
lean_dec(v_a_2670_);
lean_dec_ref(v_a_2669_);
lean_dec(v_a_2668_);
lean_dec_ref(v_a_2667_);
lean_dec(v_a_2666_);
lean_dec_ref(v_a_2665_);
lean_dec(v_a_2664_);
lean_dec(v_a_2663_);
lean_dec_ref(v_a_2662_);
return v_res_2674_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0(lean_object* v_cls_2675_, lean_object* v_msg_2676_, lean_object* v___y_2677_, lean_object* v___y_2678_, lean_object* v___y_2679_, lean_object* v___y_2680_, lean_object* v___y_2681_, lean_object* v___y_2682_, lean_object* v___y_2683_, lean_object* v___y_2684_, lean_object* v___y_2685_, lean_object* v___y_2686_, lean_object* v___y_2687_){
_start:
{
lean_object* v___x_2689_; 
v___x_2689_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg(v_cls_2675_, v_msg_2676_, v___y_2684_, v___y_2685_, v___y_2686_, v___y_2687_);
return v___x_2689_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___boxed(lean_object* v_cls_2690_, lean_object* v_msg_2691_, lean_object* v___y_2692_, lean_object* v___y_2693_, lean_object* v___y_2694_, lean_object* v___y_2695_, lean_object* v___y_2696_, lean_object* v___y_2697_, lean_object* v___y_2698_, lean_object* v___y_2699_, lean_object* v___y_2700_, lean_object* v___y_2701_, lean_object* v___y_2702_, lean_object* v___y_2703_){
_start:
{
lean_object* v_res_2704_; 
v_res_2704_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0(v_cls_2690_, v_msg_2691_, v___y_2692_, v___y_2693_, v___y_2694_, v___y_2695_, v___y_2696_, v___y_2697_, v___y_2698_, v___y_2699_, v___y_2700_, v___y_2701_, v___y_2702_);
lean_dec(v___y_2702_);
lean_dec_ref(v___y_2701_);
lean_dec(v___y_2700_);
lean_dec_ref(v___y_2699_);
lean_dec(v___y_2698_);
lean_dec_ref(v___y_2697_);
lean_dec(v___y_2696_);
lean_dec_ref(v___y_2695_);
lean_dec(v___y_2694_);
lean_dec(v___y_2693_);
lean_dec_ref(v___y_2692_);
return v_res_2704_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1(lean_object* v___x_2705_, lean_object* v_snd_2706_, lean_object* v_fst_2707_, lean_object* v_fst_2708_, lean_object* v___x_2709_, lean_object* v_range_2710_, lean_object* v_b_2711_, lean_object* v_i_2712_, lean_object* v_hs_2713_, lean_object* v_hl_2714_, lean_object* v___y_2715_, lean_object* v___y_2716_, lean_object* v___y_2717_, lean_object* v___y_2718_, lean_object* v___y_2719_, lean_object* v___y_2720_, lean_object* v___y_2721_, lean_object* v___y_2722_, lean_object* v___y_2723_, lean_object* v___y_2724_, lean_object* v___y_2725_){
_start:
{
lean_object* v___x_2727_; 
v___x_2727_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg(v___x_2705_, v_snd_2706_, v_fst_2707_, v_fst_2708_, v___x_2709_, v_range_2710_, v_b_2711_, v_i_2712_, v___y_2715_, v___y_2716_, v___y_2717_, v___y_2718_, v___y_2719_, v___y_2720_, v___y_2721_, v___y_2722_, v___y_2723_, v___y_2724_, v___y_2725_);
return v___x_2727_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___boxed(lean_object** _args){
lean_object* v___x_2728_ = _args[0];
lean_object* v_snd_2729_ = _args[1];
lean_object* v_fst_2730_ = _args[2];
lean_object* v_fst_2731_ = _args[3];
lean_object* v___x_2732_ = _args[4];
lean_object* v_range_2733_ = _args[5];
lean_object* v_b_2734_ = _args[6];
lean_object* v_i_2735_ = _args[7];
lean_object* v_hs_2736_ = _args[8];
lean_object* v_hl_2737_ = _args[9];
lean_object* v___y_2738_ = _args[10];
lean_object* v___y_2739_ = _args[11];
lean_object* v___y_2740_ = _args[12];
lean_object* v___y_2741_ = _args[13];
lean_object* v___y_2742_ = _args[14];
lean_object* v___y_2743_ = _args[15];
lean_object* v___y_2744_ = _args[16];
lean_object* v___y_2745_ = _args[17];
lean_object* v___y_2746_ = _args[18];
lean_object* v___y_2747_ = _args[19];
lean_object* v___y_2748_ = _args[20];
lean_object* v___y_2749_ = _args[21];
_start:
{
lean_object* v_res_2750_; 
v_res_2750_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1(v___x_2728_, v_snd_2729_, v_fst_2730_, v_fst_2731_, v___x_2732_, v_range_2733_, v_b_2734_, v_i_2735_, v_hs_2736_, v_hl_2737_, v___y_2738_, v___y_2739_, v___y_2740_, v___y_2741_, v___y_2742_, v___y_2743_, v___y_2744_, v___y_2745_, v___y_2746_, v___y_2747_, v___y_2748_);
lean_dec(v___y_2748_);
lean_dec_ref(v___y_2747_);
lean_dec(v___y_2746_);
lean_dec_ref(v___y_2745_);
lean_dec(v___y_2744_);
lean_dec_ref(v___y_2743_);
lean_dec(v___y_2742_);
lean_dec_ref(v___y_2741_);
lean_dec(v___y_2740_);
lean_dec(v___y_2739_);
lean_dec_ref(v___y_2738_);
lean_dec_ref(v_range_2733_);
lean_dec_ref(v___x_2732_);
return v_res_2750_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeInv(lean_object* v_e_2751_, lean_object* v_a_2752_, lean_object* v_a_2753_, lean_object* v_a_2754_, lean_object* v_a_2755_, lean_object* v_a_2756_, lean_object* v_a_2757_, lean_object* v_a_2758_, lean_object* v_a_2759_, lean_object* v_a_2760_, lean_object* v_a_2761_){
_start:
{
lean_object* v___x_2763_; 
lean_inc_ref(v_e_2751_);
v___x_2763_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_2751_, v_a_2759_);
if (lean_obj_tag(v___x_2763_) == 0)
{
lean_object* v_a_2764_; lean_object* v___x_2766_; uint8_t v_isShared_2767_; uint8_t v_isSharedCheck_2825_; 
v_a_2764_ = lean_ctor_get(v___x_2763_, 0);
v_isSharedCheck_2825_ = !lean_is_exclusive(v___x_2763_);
if (v_isSharedCheck_2825_ == 0)
{
v___x_2766_ = v___x_2763_;
v_isShared_2767_ = v_isSharedCheck_2825_;
goto v_resetjp_2765_;
}
else
{
lean_inc(v_a_2764_);
lean_dec(v___x_2763_);
v___x_2766_ = lean_box(0);
v_isShared_2767_ = v_isSharedCheck_2825_;
goto v_resetjp_2765_;
}
v_resetjp_2765_:
{
lean_object* v___x_2774_; uint8_t v___x_2775_; 
v___x_2774_ = l_Lean_Expr_cleanupAnnotations(v_a_2764_);
v___x_2775_ = l_Lean_Expr_isApp(v___x_2774_);
if (v___x_2775_ == 0)
{
lean_dec_ref(v___x_2774_);
lean_dec_ref(v_e_2751_);
goto v___jp_2768_;
}
else
{
lean_object* v_arg_2776_; lean_object* v___x_2777_; uint8_t v___x_2778_; 
v_arg_2776_ = lean_ctor_get(v___x_2774_, 1);
lean_inc_ref(v_arg_2776_);
v___x_2777_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2774_);
v___x_2778_ = l_Lean_Expr_isApp(v___x_2777_);
if (v___x_2778_ == 0)
{
lean_dec_ref(v___x_2777_);
lean_dec_ref(v_arg_2776_);
lean_dec_ref(v_e_2751_);
goto v___jp_2768_;
}
else
{
lean_object* v_arg_2779_; lean_object* v___x_2780_; uint8_t v___x_2781_; 
v_arg_2779_ = lean_ctor_get(v___x_2777_, 1);
lean_inc_ref(v_arg_2779_);
v___x_2780_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2777_);
v___x_2781_ = l_Lean_Expr_isApp(v___x_2780_);
if (v___x_2781_ == 0)
{
lean_dec_ref(v___x_2780_);
lean_dec_ref(v_arg_2779_);
lean_dec_ref(v_arg_2776_);
lean_dec_ref(v_e_2751_);
goto v___jp_2768_;
}
else
{
lean_object* v_arg_2782_; lean_object* v___x_2783_; lean_object* v___x_2784_; uint8_t v___x_2785_; 
v_arg_2782_ = lean_ctor_get(v___x_2780_, 1);
lean_inc_ref(v_arg_2782_);
v___x_2783_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2780_);
v___x_2784_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___closed__6));
v___x_2785_ = l_Lean_Expr_isConstOf(v___x_2783_, v___x_2784_);
lean_dec_ref(v___x_2783_);
if (v___x_2785_ == 0)
{
lean_dec_ref(v_arg_2782_);
lean_dec_ref(v_arg_2779_);
lean_dec_ref(v_arg_2776_);
lean_dec_ref(v_e_2751_);
goto v___jp_2768_;
}
else
{
lean_object* v___x_2786_; 
lean_del_object(v___x_2766_);
v___x_2786_ = l_Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f(v_arg_2782_, v_a_2752_, v_a_2753_, v_a_2754_, v_a_2755_, v_a_2756_, v_a_2757_, v_a_2758_, v_a_2759_, v_a_2760_, v_a_2761_);
if (lean_obj_tag(v___x_2786_) == 0)
{
lean_object* v_a_2787_; lean_object* v___x_2789_; uint8_t v_isShared_2790_; uint8_t v_isSharedCheck_2816_; 
v_a_2787_ = lean_ctor_get(v___x_2786_, 0);
v_isSharedCheck_2816_ = !lean_is_exclusive(v___x_2786_);
if (v_isSharedCheck_2816_ == 0)
{
v___x_2789_ = v___x_2786_;
v_isShared_2790_ = v_isSharedCheck_2816_;
goto v_resetjp_2788_;
}
else
{
lean_inc(v_a_2787_);
lean_dec(v___x_2786_);
v___x_2789_ = lean_box(0);
v_isShared_2790_ = v_isSharedCheck_2816_;
goto v_resetjp_2788_;
}
v_resetjp_2788_:
{
if (lean_obj_tag(v_a_2787_) == 1)
{
lean_object* v_val_2791_; uint8_t v___x_2792_; lean_object* v___x_2793_; lean_object* v___x_2794_; 
lean_del_object(v___x_2789_);
v_val_2791_ = lean_ctor_get(v_a_2787_, 0);
lean_inc(v_val_2791_);
lean_dec_ref(v_a_2787_);
v___x_2792_ = 0;
v___x_2793_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2793_, 0, v_val_2791_);
lean_ctor_set_uint8(v___x_2793_, sizeof(void*)*1, v___x_2792_);
v___x_2794_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv(v_e_2751_, v_arg_2779_, v_arg_2776_, v___x_2793_, v_a_2752_, v_a_2753_, v_a_2754_, v_a_2755_, v_a_2756_, v_a_2757_, v_a_2758_, v_a_2759_, v_a_2760_, v_a_2761_);
lean_dec_ref(v___x_2793_);
lean_dec_ref(v_arg_2779_);
if (lean_obj_tag(v___x_2794_) == 0)
{
lean_object* v___x_2796_; uint8_t v_isShared_2797_; uint8_t v_isSharedCheck_2802_; 
v_isSharedCheck_2802_ = !lean_is_exclusive(v___x_2794_);
if (v_isSharedCheck_2802_ == 0)
{
lean_object* v_unused_2803_; 
v_unused_2803_ = lean_ctor_get(v___x_2794_, 0);
lean_dec(v_unused_2803_);
v___x_2796_ = v___x_2794_;
v_isShared_2797_ = v_isSharedCheck_2802_;
goto v_resetjp_2795_;
}
else
{
lean_dec(v___x_2794_);
v___x_2796_ = lean_box(0);
v_isShared_2797_ = v_isSharedCheck_2802_;
goto v_resetjp_2795_;
}
v_resetjp_2795_:
{
lean_object* v___x_2798_; lean_object* v___x_2800_; 
v___x_2798_ = lean_box(v___x_2785_);
if (v_isShared_2797_ == 0)
{
lean_ctor_set(v___x_2796_, 0, v___x_2798_);
v___x_2800_ = v___x_2796_;
goto v_reusejp_2799_;
}
else
{
lean_object* v_reuseFailAlloc_2801_; 
v_reuseFailAlloc_2801_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2801_, 0, v___x_2798_);
v___x_2800_ = v_reuseFailAlloc_2801_;
goto v_reusejp_2799_;
}
v_reusejp_2799_:
{
return v___x_2800_;
}
}
}
else
{
lean_object* v_a_2804_; lean_object* v___x_2806_; uint8_t v_isShared_2807_; uint8_t v_isSharedCheck_2811_; 
v_a_2804_ = lean_ctor_get(v___x_2794_, 0);
v_isSharedCheck_2811_ = !lean_is_exclusive(v___x_2794_);
if (v_isSharedCheck_2811_ == 0)
{
v___x_2806_ = v___x_2794_;
v_isShared_2807_ = v_isSharedCheck_2811_;
goto v_resetjp_2805_;
}
else
{
lean_inc(v_a_2804_);
lean_dec(v___x_2794_);
v___x_2806_ = lean_box(0);
v_isShared_2807_ = v_isSharedCheck_2811_;
goto v_resetjp_2805_;
}
v_resetjp_2805_:
{
lean_object* v___x_2809_; 
if (v_isShared_2807_ == 0)
{
v___x_2809_ = v___x_2806_;
goto v_reusejp_2808_;
}
else
{
lean_object* v_reuseFailAlloc_2810_; 
v_reuseFailAlloc_2810_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2810_, 0, v_a_2804_);
v___x_2809_ = v_reuseFailAlloc_2810_;
goto v_reusejp_2808_;
}
v_reusejp_2808_:
{
return v___x_2809_;
}
}
}
}
else
{
lean_object* v___x_2812_; lean_object* v___x_2814_; 
lean_dec(v_a_2787_);
lean_dec_ref(v_arg_2779_);
lean_dec_ref(v_arg_2776_);
lean_dec_ref(v_e_2751_);
v___x_2812_ = lean_box(v___x_2785_);
if (v_isShared_2790_ == 0)
{
lean_ctor_set(v___x_2789_, 0, v___x_2812_);
v___x_2814_ = v___x_2789_;
goto v_reusejp_2813_;
}
else
{
lean_object* v_reuseFailAlloc_2815_; 
v_reuseFailAlloc_2815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2815_, 0, v___x_2812_);
v___x_2814_ = v_reuseFailAlloc_2815_;
goto v_reusejp_2813_;
}
v_reusejp_2813_:
{
return v___x_2814_;
}
}
}
}
else
{
lean_object* v_a_2817_; lean_object* v___x_2819_; uint8_t v_isShared_2820_; uint8_t v_isSharedCheck_2824_; 
lean_dec_ref(v_arg_2779_);
lean_dec_ref(v_arg_2776_);
lean_dec_ref(v_e_2751_);
v_a_2817_ = lean_ctor_get(v___x_2786_, 0);
v_isSharedCheck_2824_ = !lean_is_exclusive(v___x_2786_);
if (v_isSharedCheck_2824_ == 0)
{
v___x_2819_ = v___x_2786_;
v_isShared_2820_ = v_isSharedCheck_2824_;
goto v_resetjp_2818_;
}
else
{
lean_inc(v_a_2817_);
lean_dec(v___x_2786_);
v___x_2819_ = lean_box(0);
v_isShared_2820_ = v_isSharedCheck_2824_;
goto v_resetjp_2818_;
}
v_resetjp_2818_:
{
lean_object* v___x_2822_; 
if (v_isShared_2820_ == 0)
{
v___x_2822_ = v___x_2819_;
goto v_reusejp_2821_;
}
else
{
lean_object* v_reuseFailAlloc_2823_; 
v_reuseFailAlloc_2823_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2823_, 0, v_a_2817_);
v___x_2822_ = v_reuseFailAlloc_2823_;
goto v_reusejp_2821_;
}
v_reusejp_2821_:
{
return v___x_2822_;
}
}
}
}
}
}
}
v___jp_2768_:
{
uint8_t v___x_2769_; lean_object* v___x_2770_; lean_object* v___x_2772_; 
v___x_2769_ = 0;
v___x_2770_ = lean_box(v___x_2769_);
if (v_isShared_2767_ == 0)
{
lean_ctor_set(v___x_2766_, 0, v___x_2770_);
v___x_2772_ = v___x_2766_;
goto v_reusejp_2771_;
}
else
{
lean_object* v_reuseFailAlloc_2773_; 
v_reuseFailAlloc_2773_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2773_, 0, v___x_2770_);
v___x_2772_ = v_reuseFailAlloc_2773_;
goto v_reusejp_2771_;
}
v_reusejp_2771_:
{
return v___x_2772_;
}
}
}
}
else
{
lean_object* v_a_2826_; lean_object* v___x_2828_; uint8_t v_isShared_2829_; uint8_t v_isSharedCheck_2833_; 
lean_dec_ref(v_e_2751_);
v_a_2826_ = lean_ctor_get(v___x_2763_, 0);
v_isSharedCheck_2833_ = !lean_is_exclusive(v___x_2763_);
if (v_isSharedCheck_2833_ == 0)
{
v___x_2828_ = v___x_2763_;
v_isShared_2829_ = v_isSharedCheck_2833_;
goto v_resetjp_2827_;
}
else
{
lean_inc(v_a_2826_);
lean_dec(v___x_2763_);
v___x_2828_ = lean_box(0);
v_isShared_2829_ = v_isSharedCheck_2833_;
goto v_resetjp_2827_;
}
v_resetjp_2827_:
{
lean_object* v___x_2831_; 
if (v_isShared_2829_ == 0)
{
v___x_2831_ = v___x_2828_;
goto v_reusejp_2830_;
}
else
{
lean_object* v_reuseFailAlloc_2832_; 
v_reuseFailAlloc_2832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2832_, 0, v_a_2826_);
v___x_2831_ = v_reuseFailAlloc_2832_;
goto v_reusejp_2830_;
}
v_reusejp_2830_:
{
return v___x_2831_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeInv___boxed(lean_object* v_e_2834_, lean_object* v_a_2835_, lean_object* v_a_2836_, lean_object* v_a_2837_, lean_object* v_a_2838_, lean_object* v_a_2839_, lean_object* v_a_2840_, lean_object* v_a_2841_, lean_object* v_a_2842_, lean_object* v_a_2843_, lean_object* v_a_2844_, lean_object* v_a_2845_){
_start:
{
lean_object* v_res_2846_; 
v_res_2846_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeInv(v_e_2834_, v_a_2835_, v_a_2836_, v_a_2837_, v_a_2838_, v_a_2839_, v_a_2840_, v_a_2841_, v_a_2842_, v_a_2843_, v_a_2844_);
lean_dec(v_a_2844_);
lean_dec_ref(v_a_2843_);
lean_dec(v_a_2842_);
lean_dec_ref(v_a_2841_);
lean_dec(v_a_2840_);
lean_dec_ref(v_a_2839_);
lean_dec(v_a_2838_);
lean_dec_ref(v_a_2837_);
lean_dec(v_a_2836_);
lean_dec(v_a_2835_);
return v_res_2846_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0_spec__1_spec__5___redArg(lean_object* v_x_2847_, lean_object* v_x_2848_, lean_object* v_x_2849_, lean_object* v_x_2850_){
_start:
{
lean_object* v_ks_2851_; lean_object* v_vs_2852_; lean_object* v___x_2854_; uint8_t v_isShared_2855_; uint8_t v_isSharedCheck_2876_; 
v_ks_2851_ = lean_ctor_get(v_x_2847_, 0);
v_vs_2852_ = lean_ctor_get(v_x_2847_, 1);
v_isSharedCheck_2876_ = !lean_is_exclusive(v_x_2847_);
if (v_isSharedCheck_2876_ == 0)
{
v___x_2854_ = v_x_2847_;
v_isShared_2855_ = v_isSharedCheck_2876_;
goto v_resetjp_2853_;
}
else
{
lean_inc(v_vs_2852_);
lean_inc(v_ks_2851_);
lean_dec(v_x_2847_);
v___x_2854_ = lean_box(0);
v_isShared_2855_ = v_isSharedCheck_2876_;
goto v_resetjp_2853_;
}
v_resetjp_2853_:
{
lean_object* v___x_2856_; uint8_t v___x_2857_; 
v___x_2856_ = lean_array_get_size(v_ks_2851_);
v___x_2857_ = lean_nat_dec_lt(v_x_2848_, v___x_2856_);
if (v___x_2857_ == 0)
{
lean_object* v___x_2858_; lean_object* v___x_2859_; lean_object* v___x_2861_; 
lean_dec(v_x_2848_);
v___x_2858_ = lean_array_push(v_ks_2851_, v_x_2849_);
v___x_2859_ = lean_array_push(v_vs_2852_, v_x_2850_);
if (v_isShared_2855_ == 0)
{
lean_ctor_set(v___x_2854_, 1, v___x_2859_);
lean_ctor_set(v___x_2854_, 0, v___x_2858_);
v___x_2861_ = v___x_2854_;
goto v_reusejp_2860_;
}
else
{
lean_object* v_reuseFailAlloc_2862_; 
v_reuseFailAlloc_2862_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2862_, 0, v___x_2858_);
lean_ctor_set(v_reuseFailAlloc_2862_, 1, v___x_2859_);
v___x_2861_ = v_reuseFailAlloc_2862_;
goto v_reusejp_2860_;
}
v_reusejp_2860_:
{
return v___x_2861_;
}
}
else
{
lean_object* v_k_x27_2863_; uint8_t v___x_2864_; 
v_k_x27_2863_ = lean_array_fget_borrowed(v_ks_2851_, v_x_2848_);
v___x_2864_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_2849_, v_k_x27_2863_);
if (v___x_2864_ == 0)
{
lean_object* v___x_2866_; 
if (v_isShared_2855_ == 0)
{
v___x_2866_ = v___x_2854_;
goto v_reusejp_2865_;
}
else
{
lean_object* v_reuseFailAlloc_2870_; 
v_reuseFailAlloc_2870_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2870_, 0, v_ks_2851_);
lean_ctor_set(v_reuseFailAlloc_2870_, 1, v_vs_2852_);
v___x_2866_ = v_reuseFailAlloc_2870_;
goto v_reusejp_2865_;
}
v_reusejp_2865_:
{
lean_object* v___x_2867_; lean_object* v___x_2868_; 
v___x_2867_ = lean_unsigned_to_nat(1u);
v___x_2868_ = lean_nat_add(v_x_2848_, v___x_2867_);
lean_dec(v_x_2848_);
v_x_2847_ = v___x_2866_;
v_x_2848_ = v___x_2868_;
goto _start;
}
}
else
{
lean_object* v___x_2871_; lean_object* v___x_2872_; lean_object* v___x_2874_; 
v___x_2871_ = lean_array_fset(v_ks_2851_, v_x_2848_, v_x_2849_);
v___x_2872_ = lean_array_fset(v_vs_2852_, v_x_2848_, v_x_2850_);
lean_dec(v_x_2848_);
if (v_isShared_2855_ == 0)
{
lean_ctor_set(v___x_2854_, 1, v___x_2872_);
lean_ctor_set(v___x_2854_, 0, v___x_2871_);
v___x_2874_ = v___x_2854_;
goto v_reusejp_2873_;
}
else
{
lean_object* v_reuseFailAlloc_2875_; 
v_reuseFailAlloc_2875_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2875_, 0, v___x_2871_);
lean_ctor_set(v_reuseFailAlloc_2875_, 1, v___x_2872_);
v___x_2874_ = v_reuseFailAlloc_2875_;
goto v_reusejp_2873_;
}
v_reusejp_2873_:
{
return v___x_2874_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0_spec__1___redArg(lean_object* v_n_2877_, lean_object* v_k_2878_, lean_object* v_v_2879_){
_start:
{
lean_object* v___x_2880_; lean_object* v___x_2881_; 
v___x_2880_ = lean_unsigned_to_nat(0u);
v___x_2881_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0_spec__1_spec__5___redArg(v_n_2877_, v___x_2880_, v_k_2878_, v_v_2879_);
return v___x_2881_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0___redArg(lean_object* v_x_2882_, size_t v_x_2883_, size_t v_x_2884_, lean_object* v_x_2885_, lean_object* v_x_2886_){
_start:
{
if (lean_obj_tag(v_x_2882_) == 0)
{
lean_object* v_es_2887_; size_t v___x_2888_; size_t v___x_2889_; size_t v___x_2890_; size_t v___x_2891_; lean_object* v_j_2892_; lean_object* v___x_2893_; uint8_t v___x_2894_; 
v_es_2887_ = lean_ctor_get(v_x_2882_, 0);
v___x_2888_ = ((size_t)5ULL);
v___x_2889_ = ((size_t)1ULL);
v___x_2890_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg___closed__1);
v___x_2891_ = lean_usize_land(v_x_2883_, v___x_2890_);
v_j_2892_ = lean_usize_to_nat(v___x_2891_);
v___x_2893_ = lean_array_get_size(v_es_2887_);
v___x_2894_ = lean_nat_dec_lt(v_j_2892_, v___x_2893_);
if (v___x_2894_ == 0)
{
lean_dec(v_j_2892_);
lean_dec(v_x_2886_);
lean_dec_ref(v_x_2885_);
return v_x_2882_;
}
else
{
lean_object* v___x_2896_; uint8_t v_isShared_2897_; uint8_t v_isSharedCheck_2931_; 
lean_inc_ref(v_es_2887_);
v_isSharedCheck_2931_ = !lean_is_exclusive(v_x_2882_);
if (v_isSharedCheck_2931_ == 0)
{
lean_object* v_unused_2932_; 
v_unused_2932_ = lean_ctor_get(v_x_2882_, 0);
lean_dec(v_unused_2932_);
v___x_2896_ = v_x_2882_;
v_isShared_2897_ = v_isSharedCheck_2931_;
goto v_resetjp_2895_;
}
else
{
lean_dec(v_x_2882_);
v___x_2896_ = lean_box(0);
v_isShared_2897_ = v_isSharedCheck_2931_;
goto v_resetjp_2895_;
}
v_resetjp_2895_:
{
lean_object* v_v_2898_; lean_object* v___x_2899_; lean_object* v_xs_x27_2900_; lean_object* v___y_2902_; 
v_v_2898_ = lean_array_fget(v_es_2887_, v_j_2892_);
v___x_2899_ = lean_box(0);
v_xs_x27_2900_ = lean_array_fset(v_es_2887_, v_j_2892_, v___x_2899_);
switch(lean_obj_tag(v_v_2898_))
{
case 0:
{
lean_object* v_key_2907_; lean_object* v_val_2908_; lean_object* v___x_2910_; uint8_t v_isShared_2911_; uint8_t v_isSharedCheck_2918_; 
v_key_2907_ = lean_ctor_get(v_v_2898_, 0);
v_val_2908_ = lean_ctor_get(v_v_2898_, 1);
v_isSharedCheck_2918_ = !lean_is_exclusive(v_v_2898_);
if (v_isSharedCheck_2918_ == 0)
{
v___x_2910_ = v_v_2898_;
v_isShared_2911_ = v_isSharedCheck_2918_;
goto v_resetjp_2909_;
}
else
{
lean_inc(v_val_2908_);
lean_inc(v_key_2907_);
lean_dec(v_v_2898_);
v___x_2910_ = lean_box(0);
v_isShared_2911_ = v_isSharedCheck_2918_;
goto v_resetjp_2909_;
}
v_resetjp_2909_:
{
uint8_t v___x_2912_; 
v___x_2912_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_2885_, v_key_2907_);
if (v___x_2912_ == 0)
{
lean_object* v___x_2913_; lean_object* v___x_2914_; 
lean_del_object(v___x_2910_);
v___x_2913_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_2907_, v_val_2908_, v_x_2885_, v_x_2886_);
v___x_2914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2914_, 0, v___x_2913_);
v___y_2902_ = v___x_2914_;
goto v___jp_2901_;
}
else
{
lean_object* v___x_2916_; 
lean_dec(v_val_2908_);
lean_dec(v_key_2907_);
if (v_isShared_2911_ == 0)
{
lean_ctor_set(v___x_2910_, 1, v_x_2886_);
lean_ctor_set(v___x_2910_, 0, v_x_2885_);
v___x_2916_ = v___x_2910_;
goto v_reusejp_2915_;
}
else
{
lean_object* v_reuseFailAlloc_2917_; 
v_reuseFailAlloc_2917_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2917_, 0, v_x_2885_);
lean_ctor_set(v_reuseFailAlloc_2917_, 1, v_x_2886_);
v___x_2916_ = v_reuseFailAlloc_2917_;
goto v_reusejp_2915_;
}
v_reusejp_2915_:
{
v___y_2902_ = v___x_2916_;
goto v___jp_2901_;
}
}
}
}
case 1:
{
lean_object* v_node_2919_; lean_object* v___x_2921_; uint8_t v_isShared_2922_; uint8_t v_isSharedCheck_2929_; 
v_node_2919_ = lean_ctor_get(v_v_2898_, 0);
v_isSharedCheck_2929_ = !lean_is_exclusive(v_v_2898_);
if (v_isSharedCheck_2929_ == 0)
{
v___x_2921_ = v_v_2898_;
v_isShared_2922_ = v_isSharedCheck_2929_;
goto v_resetjp_2920_;
}
else
{
lean_inc(v_node_2919_);
lean_dec(v_v_2898_);
v___x_2921_ = lean_box(0);
v_isShared_2922_ = v_isSharedCheck_2929_;
goto v_resetjp_2920_;
}
v_resetjp_2920_:
{
size_t v___x_2923_; size_t v___x_2924_; lean_object* v___x_2925_; lean_object* v___x_2927_; 
v___x_2923_ = lean_usize_shift_right(v_x_2883_, v___x_2888_);
v___x_2924_ = lean_usize_add(v_x_2884_, v___x_2889_);
v___x_2925_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0___redArg(v_node_2919_, v___x_2923_, v___x_2924_, v_x_2885_, v_x_2886_);
if (v_isShared_2922_ == 0)
{
lean_ctor_set(v___x_2921_, 0, v___x_2925_);
v___x_2927_ = v___x_2921_;
goto v_reusejp_2926_;
}
else
{
lean_object* v_reuseFailAlloc_2928_; 
v_reuseFailAlloc_2928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2928_, 0, v___x_2925_);
v___x_2927_ = v_reuseFailAlloc_2928_;
goto v_reusejp_2926_;
}
v_reusejp_2926_:
{
v___y_2902_ = v___x_2927_;
goto v___jp_2901_;
}
}
}
default: 
{
lean_object* v___x_2930_; 
v___x_2930_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2930_, 0, v_x_2885_);
lean_ctor_set(v___x_2930_, 1, v_x_2886_);
v___y_2902_ = v___x_2930_;
goto v___jp_2901_;
}
}
v___jp_2901_:
{
lean_object* v___x_2903_; lean_object* v___x_2905_; 
v___x_2903_ = lean_array_fset(v_xs_x27_2900_, v_j_2892_, v___y_2902_);
lean_dec(v_j_2892_);
if (v_isShared_2897_ == 0)
{
lean_ctor_set(v___x_2896_, 0, v___x_2903_);
v___x_2905_ = v___x_2896_;
goto v_reusejp_2904_;
}
else
{
lean_object* v_reuseFailAlloc_2906_; 
v_reuseFailAlloc_2906_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2906_, 0, v___x_2903_);
v___x_2905_ = v_reuseFailAlloc_2906_;
goto v_reusejp_2904_;
}
v_reusejp_2904_:
{
return v___x_2905_;
}
}
}
}
}
else
{
lean_object* v_ks_2933_; lean_object* v_vs_2934_; lean_object* v___x_2936_; uint8_t v_isShared_2937_; uint8_t v_isSharedCheck_2954_; 
v_ks_2933_ = lean_ctor_get(v_x_2882_, 0);
v_vs_2934_ = lean_ctor_get(v_x_2882_, 1);
v_isSharedCheck_2954_ = !lean_is_exclusive(v_x_2882_);
if (v_isSharedCheck_2954_ == 0)
{
v___x_2936_ = v_x_2882_;
v_isShared_2937_ = v_isSharedCheck_2954_;
goto v_resetjp_2935_;
}
else
{
lean_inc(v_vs_2934_);
lean_inc(v_ks_2933_);
lean_dec(v_x_2882_);
v___x_2936_ = lean_box(0);
v_isShared_2937_ = v_isSharedCheck_2954_;
goto v_resetjp_2935_;
}
v_resetjp_2935_:
{
lean_object* v___x_2939_; 
if (v_isShared_2937_ == 0)
{
v___x_2939_ = v___x_2936_;
goto v_reusejp_2938_;
}
else
{
lean_object* v_reuseFailAlloc_2953_; 
v_reuseFailAlloc_2953_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2953_, 0, v_ks_2933_);
lean_ctor_set(v_reuseFailAlloc_2953_, 1, v_vs_2934_);
v___x_2939_ = v_reuseFailAlloc_2953_;
goto v_reusejp_2938_;
}
v_reusejp_2938_:
{
lean_object* v_newNode_2940_; uint8_t v___y_2942_; size_t v___x_2948_; uint8_t v___x_2949_; 
v_newNode_2940_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0_spec__1___redArg(v___x_2939_, v_x_2885_, v_x_2886_);
v___x_2948_ = ((size_t)7ULL);
v___x_2949_ = lean_usize_dec_le(v___x_2948_, v_x_2884_);
if (v___x_2949_ == 0)
{
lean_object* v___x_2950_; lean_object* v___x_2951_; uint8_t v___x_2952_; 
v___x_2950_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2940_);
v___x_2951_ = lean_unsigned_to_nat(4u);
v___x_2952_ = lean_nat_dec_lt(v___x_2950_, v___x_2951_);
lean_dec(v___x_2950_);
v___y_2942_ = v___x_2952_;
goto v___jp_2941_;
}
else
{
v___y_2942_ = v___x_2949_;
goto v___jp_2941_;
}
v___jp_2941_:
{
if (v___y_2942_ == 0)
{
lean_object* v_ks_2943_; lean_object* v_vs_2944_; lean_object* v___x_2945_; lean_object* v___x_2946_; lean_object* v___x_2947_; 
v_ks_2943_ = lean_ctor_get(v_newNode_2940_, 0);
lean_inc_ref(v_ks_2943_);
v_vs_2944_ = lean_ctor_get(v_newNode_2940_, 1);
lean_inc_ref(v_vs_2944_);
lean_dec_ref(v_newNode_2940_);
v___x_2945_ = lean_unsigned_to_nat(0u);
v___x_2946_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg___closed__2);
v___x_2947_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0_spec__2___redArg(v_x_2884_, v_ks_2943_, v_vs_2944_, v___x_2945_, v___x_2946_);
lean_dec_ref(v_vs_2944_);
lean_dec_ref(v_ks_2943_);
return v___x_2947_;
}
else
{
return v_newNode_2940_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0_spec__2___redArg(size_t v_depth_2955_, lean_object* v_keys_2956_, lean_object* v_vals_2957_, lean_object* v_i_2958_, lean_object* v_entries_2959_){
_start:
{
lean_object* v___x_2960_; uint8_t v___x_2961_; 
v___x_2960_ = lean_array_get_size(v_keys_2956_);
v___x_2961_ = lean_nat_dec_lt(v_i_2958_, v___x_2960_);
if (v___x_2961_ == 0)
{
lean_dec(v_i_2958_);
return v_entries_2959_;
}
else
{
lean_object* v_k_2962_; lean_object* v_v_2963_; uint64_t v___x_2964_; size_t v_h_2965_; size_t v___x_2966_; lean_object* v___x_2967_; size_t v___x_2968_; size_t v___x_2969_; size_t v___x_2970_; size_t v_h_2971_; lean_object* v___x_2972_; lean_object* v___x_2973_; 
v_k_2962_ = lean_array_fget_borrowed(v_keys_2956_, v_i_2958_);
v_v_2963_ = lean_array_fget_borrowed(v_vals_2957_, v_i_2958_);
v___x_2964_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_k_2962_);
v_h_2965_ = lean_uint64_to_usize(v___x_2964_);
v___x_2966_ = ((size_t)5ULL);
v___x_2967_ = lean_unsigned_to_nat(1u);
v___x_2968_ = ((size_t)1ULL);
v___x_2969_ = lean_usize_sub(v_depth_2955_, v___x_2968_);
v___x_2970_ = lean_usize_mul(v___x_2966_, v___x_2969_);
v_h_2971_ = lean_usize_shift_right(v_h_2965_, v___x_2970_);
v___x_2972_ = lean_nat_add(v_i_2958_, v___x_2967_);
lean_dec(v_i_2958_);
lean_inc(v_v_2963_);
lean_inc(v_k_2962_);
v___x_2973_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0___redArg(v_entries_2959_, v_h_2971_, v_depth_2955_, v_k_2962_, v_v_2963_);
v_i_2958_ = v___x_2972_;
v_entries_2959_ = v___x_2973_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_2975_, lean_object* v_keys_2976_, lean_object* v_vals_2977_, lean_object* v_i_2978_, lean_object* v_entries_2979_){
_start:
{
size_t v_depth_boxed_2980_; lean_object* v_res_2981_; 
v_depth_boxed_2980_ = lean_unbox_usize(v_depth_2975_);
lean_dec(v_depth_2975_);
v_res_2981_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0_spec__2___redArg(v_depth_boxed_2980_, v_keys_2976_, v_vals_2977_, v_i_2978_, v_entries_2979_);
lean_dec_ref(v_vals_2977_);
lean_dec_ref(v_keys_2976_);
return v_res_2981_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0___redArg___boxed(lean_object* v_x_2982_, lean_object* v_x_2983_, lean_object* v_x_2984_, lean_object* v_x_2985_, lean_object* v_x_2986_){
_start:
{
size_t v_x_210704__boxed_2987_; size_t v_x_210705__boxed_2988_; lean_object* v_res_2989_; 
v_x_210704__boxed_2987_ = lean_unbox_usize(v_x_2983_);
lean_dec(v_x_2983_);
v_x_210705__boxed_2988_ = lean_unbox_usize(v_x_2984_);
lean_dec(v_x_2984_);
v_res_2989_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0___redArg(v_x_2982_, v_x_210704__boxed_2987_, v_x_210705__boxed_2988_, v_x_2985_, v_x_2986_);
return v_res_2989_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0___redArg(lean_object* v_x_2990_, lean_object* v_x_2991_, lean_object* v_x_2992_){
_start:
{
uint64_t v___x_2993_; size_t v___x_2994_; size_t v___x_2995_; lean_object* v___x_2996_; 
v___x_2993_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_2991_);
v___x_2994_ = lean_uint64_to_usize(v___x_2993_);
v___x_2995_ = ((size_t)1ULL);
v___x_2996_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0___redArg(v_x_2990_, v___x_2994_, v___x_2995_, v_x_2991_, v_x_2992_);
return v___x_2996_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_internalize___lam__0(lean_object* v_e_2997_, lean_object* v_val_2998_, lean_object* v_s_2999_){
_start:
{
lean_object* v_toRing_3000_; lean_object* v_invFn_x3f_3001_; lean_object* v_semiringId_x3f_3002_; lean_object* v_commSemiringInst_3003_; lean_object* v_commRingInst_3004_; lean_object* v_noZeroDivInst_x3f_3005_; lean_object* v_fieldInst_x3f_3006_; lean_object* v_powIdentityInst_x3f_3007_; lean_object* v_denoteEntries_3008_; lean_object* v_nextId_3009_; lean_object* v_steps_3010_; lean_object* v_queue_3011_; lean_object* v_basis_3012_; lean_object* v_diseqs_3013_; uint8_t v_recheck_3014_; lean_object* v_invSet_3015_; lean_object* v_powIdentityVarCount_3016_; lean_object* v_numEq0_x3f_3017_; uint8_t v_numEq0Updated_3018_; lean_object* v___x_3020_; uint8_t v_isShared_3021_; uint8_t v_isSharedCheck_3052_; 
v_toRing_3000_ = lean_ctor_get(v_s_2999_, 0);
v_invFn_x3f_3001_ = lean_ctor_get(v_s_2999_, 1);
v_semiringId_x3f_3002_ = lean_ctor_get(v_s_2999_, 2);
v_commSemiringInst_3003_ = lean_ctor_get(v_s_2999_, 3);
v_commRingInst_3004_ = lean_ctor_get(v_s_2999_, 4);
v_noZeroDivInst_x3f_3005_ = lean_ctor_get(v_s_2999_, 5);
v_fieldInst_x3f_3006_ = lean_ctor_get(v_s_2999_, 6);
v_powIdentityInst_x3f_3007_ = lean_ctor_get(v_s_2999_, 7);
v_denoteEntries_3008_ = lean_ctor_get(v_s_2999_, 8);
v_nextId_3009_ = lean_ctor_get(v_s_2999_, 9);
v_steps_3010_ = lean_ctor_get(v_s_2999_, 10);
v_queue_3011_ = lean_ctor_get(v_s_2999_, 11);
v_basis_3012_ = lean_ctor_get(v_s_2999_, 12);
v_diseqs_3013_ = lean_ctor_get(v_s_2999_, 13);
v_recheck_3014_ = lean_ctor_get_uint8(v_s_2999_, sizeof(void*)*17);
v_invSet_3015_ = lean_ctor_get(v_s_2999_, 14);
v_powIdentityVarCount_3016_ = lean_ctor_get(v_s_2999_, 15);
v_numEq0_x3f_3017_ = lean_ctor_get(v_s_2999_, 16);
v_numEq0Updated_3018_ = lean_ctor_get_uint8(v_s_2999_, sizeof(void*)*17 + 1);
v_isSharedCheck_3052_ = !lean_is_exclusive(v_s_2999_);
if (v_isSharedCheck_3052_ == 0)
{
v___x_3020_ = v_s_2999_;
v_isShared_3021_ = v_isSharedCheck_3052_;
goto v_resetjp_3019_;
}
else
{
lean_inc(v_numEq0_x3f_3017_);
lean_inc(v_powIdentityVarCount_3016_);
lean_inc(v_invSet_3015_);
lean_inc(v_diseqs_3013_);
lean_inc(v_basis_3012_);
lean_inc(v_queue_3011_);
lean_inc(v_steps_3010_);
lean_inc(v_nextId_3009_);
lean_inc(v_denoteEntries_3008_);
lean_inc(v_powIdentityInst_x3f_3007_);
lean_inc(v_fieldInst_x3f_3006_);
lean_inc(v_noZeroDivInst_x3f_3005_);
lean_inc(v_commRingInst_3004_);
lean_inc(v_commSemiringInst_3003_);
lean_inc(v_semiringId_x3f_3002_);
lean_inc(v_invFn_x3f_3001_);
lean_inc(v_toRing_3000_);
lean_dec(v_s_2999_);
v___x_3020_ = lean_box(0);
v_isShared_3021_ = v_isSharedCheck_3052_;
goto v_resetjp_3019_;
}
v_resetjp_3019_:
{
lean_object* v_id_3022_; lean_object* v_type_3023_; lean_object* v_u_3024_; lean_object* v_ringInst_3025_; lean_object* v_semiringInst_3026_; lean_object* v_charInst_x3f_3027_; lean_object* v_addFn_x3f_3028_; lean_object* v_mulFn_x3f_3029_; lean_object* v_subFn_x3f_3030_; lean_object* v_negFn_x3f_3031_; lean_object* v_powFn_x3f_3032_; lean_object* v_intCastFn_x3f_3033_; lean_object* v_natCastFn_x3f_3034_; lean_object* v_one_x3f_3035_; lean_object* v_vars_3036_; lean_object* v_varMap_3037_; lean_object* v_denote_3038_; lean_object* v___x_3040_; uint8_t v_isShared_3041_; uint8_t v_isSharedCheck_3051_; 
v_id_3022_ = lean_ctor_get(v_toRing_3000_, 0);
v_type_3023_ = lean_ctor_get(v_toRing_3000_, 1);
v_u_3024_ = lean_ctor_get(v_toRing_3000_, 2);
v_ringInst_3025_ = lean_ctor_get(v_toRing_3000_, 3);
v_semiringInst_3026_ = lean_ctor_get(v_toRing_3000_, 4);
v_charInst_x3f_3027_ = lean_ctor_get(v_toRing_3000_, 5);
v_addFn_x3f_3028_ = lean_ctor_get(v_toRing_3000_, 6);
v_mulFn_x3f_3029_ = lean_ctor_get(v_toRing_3000_, 7);
v_subFn_x3f_3030_ = lean_ctor_get(v_toRing_3000_, 8);
v_negFn_x3f_3031_ = lean_ctor_get(v_toRing_3000_, 9);
v_powFn_x3f_3032_ = lean_ctor_get(v_toRing_3000_, 10);
v_intCastFn_x3f_3033_ = lean_ctor_get(v_toRing_3000_, 11);
v_natCastFn_x3f_3034_ = lean_ctor_get(v_toRing_3000_, 12);
v_one_x3f_3035_ = lean_ctor_get(v_toRing_3000_, 13);
v_vars_3036_ = lean_ctor_get(v_toRing_3000_, 14);
v_varMap_3037_ = lean_ctor_get(v_toRing_3000_, 15);
v_denote_3038_ = lean_ctor_get(v_toRing_3000_, 16);
v_isSharedCheck_3051_ = !lean_is_exclusive(v_toRing_3000_);
if (v_isSharedCheck_3051_ == 0)
{
v___x_3040_ = v_toRing_3000_;
v_isShared_3041_ = v_isSharedCheck_3051_;
goto v_resetjp_3039_;
}
else
{
lean_inc(v_denote_3038_);
lean_inc(v_varMap_3037_);
lean_inc(v_vars_3036_);
lean_inc(v_one_x3f_3035_);
lean_inc(v_natCastFn_x3f_3034_);
lean_inc(v_intCastFn_x3f_3033_);
lean_inc(v_powFn_x3f_3032_);
lean_inc(v_negFn_x3f_3031_);
lean_inc(v_subFn_x3f_3030_);
lean_inc(v_mulFn_x3f_3029_);
lean_inc(v_addFn_x3f_3028_);
lean_inc(v_charInst_x3f_3027_);
lean_inc(v_semiringInst_3026_);
lean_inc(v_ringInst_3025_);
lean_inc(v_u_3024_);
lean_inc(v_type_3023_);
lean_inc(v_id_3022_);
lean_dec(v_toRing_3000_);
v___x_3040_ = lean_box(0);
v_isShared_3041_ = v_isSharedCheck_3051_;
goto v_resetjp_3039_;
}
v_resetjp_3039_:
{
lean_object* v___x_3042_; lean_object* v___x_3044_; 
lean_inc_ref(v_val_2998_);
lean_inc_ref(v_e_2997_);
v___x_3042_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0___redArg(v_denote_3038_, v_e_2997_, v_val_2998_);
if (v_isShared_3041_ == 0)
{
lean_ctor_set(v___x_3040_, 16, v___x_3042_);
v___x_3044_ = v___x_3040_;
goto v_reusejp_3043_;
}
else
{
lean_object* v_reuseFailAlloc_3050_; 
v_reuseFailAlloc_3050_ = lean_alloc_ctor(0, 17, 0);
lean_ctor_set(v_reuseFailAlloc_3050_, 0, v_id_3022_);
lean_ctor_set(v_reuseFailAlloc_3050_, 1, v_type_3023_);
lean_ctor_set(v_reuseFailAlloc_3050_, 2, v_u_3024_);
lean_ctor_set(v_reuseFailAlloc_3050_, 3, v_ringInst_3025_);
lean_ctor_set(v_reuseFailAlloc_3050_, 4, v_semiringInst_3026_);
lean_ctor_set(v_reuseFailAlloc_3050_, 5, v_charInst_x3f_3027_);
lean_ctor_set(v_reuseFailAlloc_3050_, 6, v_addFn_x3f_3028_);
lean_ctor_set(v_reuseFailAlloc_3050_, 7, v_mulFn_x3f_3029_);
lean_ctor_set(v_reuseFailAlloc_3050_, 8, v_subFn_x3f_3030_);
lean_ctor_set(v_reuseFailAlloc_3050_, 9, v_negFn_x3f_3031_);
lean_ctor_set(v_reuseFailAlloc_3050_, 10, v_powFn_x3f_3032_);
lean_ctor_set(v_reuseFailAlloc_3050_, 11, v_intCastFn_x3f_3033_);
lean_ctor_set(v_reuseFailAlloc_3050_, 12, v_natCastFn_x3f_3034_);
lean_ctor_set(v_reuseFailAlloc_3050_, 13, v_one_x3f_3035_);
lean_ctor_set(v_reuseFailAlloc_3050_, 14, v_vars_3036_);
lean_ctor_set(v_reuseFailAlloc_3050_, 15, v_varMap_3037_);
lean_ctor_set(v_reuseFailAlloc_3050_, 16, v___x_3042_);
v___x_3044_ = v_reuseFailAlloc_3050_;
goto v_reusejp_3043_;
}
v_reusejp_3043_:
{
lean_object* v___x_3045_; lean_object* v___x_3046_; lean_object* v___x_3048_; 
v___x_3045_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3045_, 0, v_e_2997_);
lean_ctor_set(v___x_3045_, 1, v_val_2998_);
v___x_3046_ = l_Lean_PersistentArray_push___redArg(v_denoteEntries_3008_, v___x_3045_);
if (v_isShared_3021_ == 0)
{
lean_ctor_set(v___x_3020_, 8, v___x_3046_);
lean_ctor_set(v___x_3020_, 0, v___x_3044_);
v___x_3048_ = v___x_3020_;
goto v_reusejp_3047_;
}
else
{
lean_object* v_reuseFailAlloc_3049_; 
v_reuseFailAlloc_3049_ = lean_alloc_ctor(0, 17, 2);
lean_ctor_set(v_reuseFailAlloc_3049_, 0, v___x_3044_);
lean_ctor_set(v_reuseFailAlloc_3049_, 1, v_invFn_x3f_3001_);
lean_ctor_set(v_reuseFailAlloc_3049_, 2, v_semiringId_x3f_3002_);
lean_ctor_set(v_reuseFailAlloc_3049_, 3, v_commSemiringInst_3003_);
lean_ctor_set(v_reuseFailAlloc_3049_, 4, v_commRingInst_3004_);
lean_ctor_set(v_reuseFailAlloc_3049_, 5, v_noZeroDivInst_x3f_3005_);
lean_ctor_set(v_reuseFailAlloc_3049_, 6, v_fieldInst_x3f_3006_);
lean_ctor_set(v_reuseFailAlloc_3049_, 7, v_powIdentityInst_x3f_3007_);
lean_ctor_set(v_reuseFailAlloc_3049_, 8, v___x_3046_);
lean_ctor_set(v_reuseFailAlloc_3049_, 9, v_nextId_3009_);
lean_ctor_set(v_reuseFailAlloc_3049_, 10, v_steps_3010_);
lean_ctor_set(v_reuseFailAlloc_3049_, 11, v_queue_3011_);
lean_ctor_set(v_reuseFailAlloc_3049_, 12, v_basis_3012_);
lean_ctor_set(v_reuseFailAlloc_3049_, 13, v_diseqs_3013_);
lean_ctor_set(v_reuseFailAlloc_3049_, 14, v_invSet_3015_);
lean_ctor_set(v_reuseFailAlloc_3049_, 15, v_powIdentityVarCount_3016_);
lean_ctor_set(v_reuseFailAlloc_3049_, 16, v_numEq0_x3f_3017_);
lean_ctor_set_uint8(v_reuseFailAlloc_3049_, sizeof(void*)*17, v_recheck_3014_);
lean_ctor_set_uint8(v_reuseFailAlloc_3049_, sizeof(void*)*17 + 1, v_numEq0Updated_3018_);
v___x_3048_ = v_reuseFailAlloc_3049_;
goto v_reusejp_3047_;
}
v_reusejp_3047_:
{
return v___x_3048_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_internalize___lam__1(lean_object* v___y_3053_, lean_object* v_e_3054_, lean_object* v_val_3055_, lean_object* v_s_3056_){
_start:
{
lean_object* v_rings_3057_; lean_object* v_typeIdOf_3058_; lean_object* v_exprToRingId_3059_; lean_object* v_semirings_3060_; lean_object* v_stypeIdOf_3061_; lean_object* v_exprToSemiringId_3062_; lean_object* v_ncRings_3063_; lean_object* v_exprToNCRingId_3064_; lean_object* v_nctypeIdOf_3065_; lean_object* v_ncSemirings_3066_; lean_object* v_exprToNCSemiringId_3067_; lean_object* v_ncstypeIdOf_3068_; lean_object* v_steps_3069_; uint8_t v_reportedMaxDegreeIssue_3070_; lean_object* v___x_3071_; uint8_t v___x_3072_; 
v_rings_3057_ = lean_ctor_get(v_s_3056_, 0);
v_typeIdOf_3058_ = lean_ctor_get(v_s_3056_, 1);
v_exprToRingId_3059_ = lean_ctor_get(v_s_3056_, 2);
v_semirings_3060_ = lean_ctor_get(v_s_3056_, 3);
v_stypeIdOf_3061_ = lean_ctor_get(v_s_3056_, 4);
v_exprToSemiringId_3062_ = lean_ctor_get(v_s_3056_, 5);
v_ncRings_3063_ = lean_ctor_get(v_s_3056_, 6);
v_exprToNCRingId_3064_ = lean_ctor_get(v_s_3056_, 7);
v_nctypeIdOf_3065_ = lean_ctor_get(v_s_3056_, 8);
v_ncSemirings_3066_ = lean_ctor_get(v_s_3056_, 9);
v_exprToNCSemiringId_3067_ = lean_ctor_get(v_s_3056_, 10);
v_ncstypeIdOf_3068_ = lean_ctor_get(v_s_3056_, 11);
v_steps_3069_ = lean_ctor_get(v_s_3056_, 12);
v_reportedMaxDegreeIssue_3070_ = lean_ctor_get_uint8(v_s_3056_, sizeof(void*)*13);
v___x_3071_ = lean_array_get_size(v_semirings_3060_);
v___x_3072_ = lean_nat_dec_lt(v___y_3053_, v___x_3071_);
if (v___x_3072_ == 0)
{
lean_dec_ref(v_val_3055_);
lean_dec_ref(v_e_3054_);
return v_s_3056_;
}
else
{
lean_object* v___x_3074_; uint8_t v_isShared_3075_; uint8_t v_isSharedCheck_3114_; 
lean_inc(v_steps_3069_);
lean_inc_ref(v_ncstypeIdOf_3068_);
lean_inc_ref(v_exprToNCSemiringId_3067_);
lean_inc_ref(v_ncSemirings_3066_);
lean_inc_ref(v_nctypeIdOf_3065_);
lean_inc_ref(v_exprToNCRingId_3064_);
lean_inc_ref(v_ncRings_3063_);
lean_inc_ref(v_exprToSemiringId_3062_);
lean_inc_ref(v_stypeIdOf_3061_);
lean_inc_ref(v_semirings_3060_);
lean_inc_ref(v_exprToRingId_3059_);
lean_inc_ref(v_typeIdOf_3058_);
lean_inc_ref(v_rings_3057_);
v_isSharedCheck_3114_ = !lean_is_exclusive(v_s_3056_);
if (v_isSharedCheck_3114_ == 0)
{
lean_object* v_unused_3115_; lean_object* v_unused_3116_; lean_object* v_unused_3117_; lean_object* v_unused_3118_; lean_object* v_unused_3119_; lean_object* v_unused_3120_; lean_object* v_unused_3121_; lean_object* v_unused_3122_; lean_object* v_unused_3123_; lean_object* v_unused_3124_; lean_object* v_unused_3125_; lean_object* v_unused_3126_; lean_object* v_unused_3127_; 
v_unused_3115_ = lean_ctor_get(v_s_3056_, 12);
lean_dec(v_unused_3115_);
v_unused_3116_ = lean_ctor_get(v_s_3056_, 11);
lean_dec(v_unused_3116_);
v_unused_3117_ = lean_ctor_get(v_s_3056_, 10);
lean_dec(v_unused_3117_);
v_unused_3118_ = lean_ctor_get(v_s_3056_, 9);
lean_dec(v_unused_3118_);
v_unused_3119_ = lean_ctor_get(v_s_3056_, 8);
lean_dec(v_unused_3119_);
v_unused_3120_ = lean_ctor_get(v_s_3056_, 7);
lean_dec(v_unused_3120_);
v_unused_3121_ = lean_ctor_get(v_s_3056_, 6);
lean_dec(v_unused_3121_);
v_unused_3122_ = lean_ctor_get(v_s_3056_, 5);
lean_dec(v_unused_3122_);
v_unused_3123_ = lean_ctor_get(v_s_3056_, 4);
lean_dec(v_unused_3123_);
v_unused_3124_ = lean_ctor_get(v_s_3056_, 3);
lean_dec(v_unused_3124_);
v_unused_3125_ = lean_ctor_get(v_s_3056_, 2);
lean_dec(v_unused_3125_);
v_unused_3126_ = lean_ctor_get(v_s_3056_, 1);
lean_dec(v_unused_3126_);
v_unused_3127_ = lean_ctor_get(v_s_3056_, 0);
lean_dec(v_unused_3127_);
v___x_3074_ = v_s_3056_;
v_isShared_3075_ = v_isSharedCheck_3114_;
goto v_resetjp_3073_;
}
else
{
lean_dec(v_s_3056_);
v___x_3074_ = lean_box(0);
v_isShared_3075_ = v_isSharedCheck_3114_;
goto v_resetjp_3073_;
}
v_resetjp_3073_:
{
lean_object* v_v_3076_; lean_object* v_toSemiring_3077_; lean_object* v_ringId_3078_; lean_object* v_commSemiringInst_3079_; lean_object* v_addRightCancelInst_x3f_3080_; lean_object* v_toQFn_x3f_3081_; lean_object* v___x_3083_; uint8_t v_isShared_3084_; uint8_t v_isSharedCheck_3113_; 
v_v_3076_ = lean_array_fget(v_semirings_3060_, v___y_3053_);
v_toSemiring_3077_ = lean_ctor_get(v_v_3076_, 0);
v_ringId_3078_ = lean_ctor_get(v_v_3076_, 1);
v_commSemiringInst_3079_ = lean_ctor_get(v_v_3076_, 2);
v_addRightCancelInst_x3f_3080_ = lean_ctor_get(v_v_3076_, 3);
v_toQFn_x3f_3081_ = lean_ctor_get(v_v_3076_, 4);
v_isSharedCheck_3113_ = !lean_is_exclusive(v_v_3076_);
if (v_isSharedCheck_3113_ == 0)
{
v___x_3083_ = v_v_3076_;
v_isShared_3084_ = v_isSharedCheck_3113_;
goto v_resetjp_3082_;
}
else
{
lean_inc(v_toQFn_x3f_3081_);
lean_inc(v_addRightCancelInst_x3f_3080_);
lean_inc(v_commSemiringInst_3079_);
lean_inc(v_ringId_3078_);
lean_inc(v_toSemiring_3077_);
lean_dec(v_v_3076_);
v___x_3083_ = lean_box(0);
v_isShared_3084_ = v_isSharedCheck_3113_;
goto v_resetjp_3082_;
}
v_resetjp_3082_:
{
lean_object* v_id_3085_; lean_object* v_type_3086_; lean_object* v_u_3087_; lean_object* v_semiringInst_3088_; lean_object* v_addFn_x3f_3089_; lean_object* v_mulFn_x3f_3090_; lean_object* v_powFn_x3f_3091_; lean_object* v_natCastFn_x3f_3092_; lean_object* v_denote_3093_; lean_object* v_vars_3094_; lean_object* v_varMap_3095_; lean_object* v___x_3097_; uint8_t v_isShared_3098_; uint8_t v_isSharedCheck_3112_; 
v_id_3085_ = lean_ctor_get(v_toSemiring_3077_, 0);
v_type_3086_ = lean_ctor_get(v_toSemiring_3077_, 1);
v_u_3087_ = lean_ctor_get(v_toSemiring_3077_, 2);
v_semiringInst_3088_ = lean_ctor_get(v_toSemiring_3077_, 3);
v_addFn_x3f_3089_ = lean_ctor_get(v_toSemiring_3077_, 4);
v_mulFn_x3f_3090_ = lean_ctor_get(v_toSemiring_3077_, 5);
v_powFn_x3f_3091_ = lean_ctor_get(v_toSemiring_3077_, 6);
v_natCastFn_x3f_3092_ = lean_ctor_get(v_toSemiring_3077_, 7);
v_denote_3093_ = lean_ctor_get(v_toSemiring_3077_, 8);
v_vars_3094_ = lean_ctor_get(v_toSemiring_3077_, 9);
v_varMap_3095_ = lean_ctor_get(v_toSemiring_3077_, 10);
v_isSharedCheck_3112_ = !lean_is_exclusive(v_toSemiring_3077_);
if (v_isSharedCheck_3112_ == 0)
{
v___x_3097_ = v_toSemiring_3077_;
v_isShared_3098_ = v_isSharedCheck_3112_;
goto v_resetjp_3096_;
}
else
{
lean_inc(v_varMap_3095_);
lean_inc(v_vars_3094_);
lean_inc(v_denote_3093_);
lean_inc(v_natCastFn_x3f_3092_);
lean_inc(v_powFn_x3f_3091_);
lean_inc(v_mulFn_x3f_3090_);
lean_inc(v_addFn_x3f_3089_);
lean_inc(v_semiringInst_3088_);
lean_inc(v_u_3087_);
lean_inc(v_type_3086_);
lean_inc(v_id_3085_);
lean_dec(v_toSemiring_3077_);
v___x_3097_ = lean_box(0);
v_isShared_3098_ = v_isSharedCheck_3112_;
goto v_resetjp_3096_;
}
v_resetjp_3096_:
{
lean_object* v___x_3099_; lean_object* v_xs_x27_3100_; lean_object* v___x_3101_; lean_object* v___x_3103_; 
v___x_3099_ = lean_box(0);
v_xs_x27_3100_ = lean_array_fset(v_semirings_3060_, v___y_3053_, v___x_3099_);
v___x_3101_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0___redArg(v_denote_3093_, v_e_3054_, v_val_3055_);
if (v_isShared_3098_ == 0)
{
lean_ctor_set(v___x_3097_, 8, v___x_3101_);
v___x_3103_ = v___x_3097_;
goto v_reusejp_3102_;
}
else
{
lean_object* v_reuseFailAlloc_3111_; 
v_reuseFailAlloc_3111_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_3111_, 0, v_id_3085_);
lean_ctor_set(v_reuseFailAlloc_3111_, 1, v_type_3086_);
lean_ctor_set(v_reuseFailAlloc_3111_, 2, v_u_3087_);
lean_ctor_set(v_reuseFailAlloc_3111_, 3, v_semiringInst_3088_);
lean_ctor_set(v_reuseFailAlloc_3111_, 4, v_addFn_x3f_3089_);
lean_ctor_set(v_reuseFailAlloc_3111_, 5, v_mulFn_x3f_3090_);
lean_ctor_set(v_reuseFailAlloc_3111_, 6, v_powFn_x3f_3091_);
lean_ctor_set(v_reuseFailAlloc_3111_, 7, v_natCastFn_x3f_3092_);
lean_ctor_set(v_reuseFailAlloc_3111_, 8, v___x_3101_);
lean_ctor_set(v_reuseFailAlloc_3111_, 9, v_vars_3094_);
lean_ctor_set(v_reuseFailAlloc_3111_, 10, v_varMap_3095_);
v___x_3103_ = v_reuseFailAlloc_3111_;
goto v_reusejp_3102_;
}
v_reusejp_3102_:
{
lean_object* v___x_3105_; 
if (v_isShared_3084_ == 0)
{
lean_ctor_set(v___x_3083_, 0, v___x_3103_);
v___x_3105_ = v___x_3083_;
goto v_reusejp_3104_;
}
else
{
lean_object* v_reuseFailAlloc_3110_; 
v_reuseFailAlloc_3110_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3110_, 0, v___x_3103_);
lean_ctor_set(v_reuseFailAlloc_3110_, 1, v_ringId_3078_);
lean_ctor_set(v_reuseFailAlloc_3110_, 2, v_commSemiringInst_3079_);
lean_ctor_set(v_reuseFailAlloc_3110_, 3, v_addRightCancelInst_x3f_3080_);
lean_ctor_set(v_reuseFailAlloc_3110_, 4, v_toQFn_x3f_3081_);
v___x_3105_ = v_reuseFailAlloc_3110_;
goto v_reusejp_3104_;
}
v_reusejp_3104_:
{
lean_object* v___x_3106_; lean_object* v___x_3108_; 
v___x_3106_ = lean_array_fset(v_xs_x27_3100_, v___y_3053_, v___x_3105_);
if (v_isShared_3075_ == 0)
{
lean_ctor_set(v___x_3074_, 3, v___x_3106_);
v___x_3108_ = v___x_3074_;
goto v_reusejp_3107_;
}
else
{
lean_object* v_reuseFailAlloc_3109_; 
v_reuseFailAlloc_3109_ = lean_alloc_ctor(0, 13, 1);
lean_ctor_set(v_reuseFailAlloc_3109_, 0, v_rings_3057_);
lean_ctor_set(v_reuseFailAlloc_3109_, 1, v_typeIdOf_3058_);
lean_ctor_set(v_reuseFailAlloc_3109_, 2, v_exprToRingId_3059_);
lean_ctor_set(v_reuseFailAlloc_3109_, 3, v___x_3106_);
lean_ctor_set(v_reuseFailAlloc_3109_, 4, v_stypeIdOf_3061_);
lean_ctor_set(v_reuseFailAlloc_3109_, 5, v_exprToSemiringId_3062_);
lean_ctor_set(v_reuseFailAlloc_3109_, 6, v_ncRings_3063_);
lean_ctor_set(v_reuseFailAlloc_3109_, 7, v_exprToNCRingId_3064_);
lean_ctor_set(v_reuseFailAlloc_3109_, 8, v_nctypeIdOf_3065_);
lean_ctor_set(v_reuseFailAlloc_3109_, 9, v_ncSemirings_3066_);
lean_ctor_set(v_reuseFailAlloc_3109_, 10, v_exprToNCSemiringId_3067_);
lean_ctor_set(v_reuseFailAlloc_3109_, 11, v_ncstypeIdOf_3068_);
lean_ctor_set(v_reuseFailAlloc_3109_, 12, v_steps_3069_);
lean_ctor_set_uint8(v_reuseFailAlloc_3109_, sizeof(void*)*13, v_reportedMaxDegreeIssue_3070_);
v___x_3108_ = v_reuseFailAlloc_3109_;
goto v_reusejp_3107_;
}
v_reusejp_3107_:
{
return v___x_3108_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_internalize___lam__1___boxed(lean_object* v___y_3128_, lean_object* v_e_3129_, lean_object* v_val_3130_, lean_object* v_s_3131_){
_start:
{
lean_object* v_res_3132_; 
v_res_3132_ = l_Lean_Meta_Grind_Arith_CommRing_internalize___lam__1(v___y_3128_, v_e_3129_, v_val_3130_, v_s_3131_);
lean_dec(v___y_3128_);
return v_res_3132_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_internalize___lam__2(lean_object* v_e_3133_, lean_object* v_val_3134_, lean_object* v_s_3135_){
_start:
{
lean_object* v_id_3136_; lean_object* v_type_3137_; lean_object* v_u_3138_; lean_object* v_ringInst_3139_; lean_object* v_semiringInst_3140_; lean_object* v_charInst_x3f_3141_; lean_object* v_addFn_x3f_3142_; lean_object* v_mulFn_x3f_3143_; lean_object* v_subFn_x3f_3144_; lean_object* v_negFn_x3f_3145_; lean_object* v_powFn_x3f_3146_; lean_object* v_intCastFn_x3f_3147_; lean_object* v_natCastFn_x3f_3148_; lean_object* v_one_x3f_3149_; lean_object* v_vars_3150_; lean_object* v_varMap_3151_; lean_object* v_denote_3152_; lean_object* v___x_3154_; uint8_t v_isShared_3155_; uint8_t v_isSharedCheck_3160_; 
v_id_3136_ = lean_ctor_get(v_s_3135_, 0);
v_type_3137_ = lean_ctor_get(v_s_3135_, 1);
v_u_3138_ = lean_ctor_get(v_s_3135_, 2);
v_ringInst_3139_ = lean_ctor_get(v_s_3135_, 3);
v_semiringInst_3140_ = lean_ctor_get(v_s_3135_, 4);
v_charInst_x3f_3141_ = lean_ctor_get(v_s_3135_, 5);
v_addFn_x3f_3142_ = lean_ctor_get(v_s_3135_, 6);
v_mulFn_x3f_3143_ = lean_ctor_get(v_s_3135_, 7);
v_subFn_x3f_3144_ = lean_ctor_get(v_s_3135_, 8);
v_negFn_x3f_3145_ = lean_ctor_get(v_s_3135_, 9);
v_powFn_x3f_3146_ = lean_ctor_get(v_s_3135_, 10);
v_intCastFn_x3f_3147_ = lean_ctor_get(v_s_3135_, 11);
v_natCastFn_x3f_3148_ = lean_ctor_get(v_s_3135_, 12);
v_one_x3f_3149_ = lean_ctor_get(v_s_3135_, 13);
v_vars_3150_ = lean_ctor_get(v_s_3135_, 14);
v_varMap_3151_ = lean_ctor_get(v_s_3135_, 15);
v_denote_3152_ = lean_ctor_get(v_s_3135_, 16);
v_isSharedCheck_3160_ = !lean_is_exclusive(v_s_3135_);
if (v_isSharedCheck_3160_ == 0)
{
v___x_3154_ = v_s_3135_;
v_isShared_3155_ = v_isSharedCheck_3160_;
goto v_resetjp_3153_;
}
else
{
lean_inc(v_denote_3152_);
lean_inc(v_varMap_3151_);
lean_inc(v_vars_3150_);
lean_inc(v_one_x3f_3149_);
lean_inc(v_natCastFn_x3f_3148_);
lean_inc(v_intCastFn_x3f_3147_);
lean_inc(v_powFn_x3f_3146_);
lean_inc(v_negFn_x3f_3145_);
lean_inc(v_subFn_x3f_3144_);
lean_inc(v_mulFn_x3f_3143_);
lean_inc(v_addFn_x3f_3142_);
lean_inc(v_charInst_x3f_3141_);
lean_inc(v_semiringInst_3140_);
lean_inc(v_ringInst_3139_);
lean_inc(v_u_3138_);
lean_inc(v_type_3137_);
lean_inc(v_id_3136_);
lean_dec(v_s_3135_);
v___x_3154_ = lean_box(0);
v_isShared_3155_ = v_isSharedCheck_3160_;
goto v_resetjp_3153_;
}
v_resetjp_3153_:
{
lean_object* v___x_3156_; lean_object* v___x_3158_; 
v___x_3156_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0___redArg(v_denote_3152_, v_e_3133_, v_val_3134_);
if (v_isShared_3155_ == 0)
{
lean_ctor_set(v___x_3154_, 16, v___x_3156_);
v___x_3158_ = v___x_3154_;
goto v_reusejp_3157_;
}
else
{
lean_object* v_reuseFailAlloc_3159_; 
v_reuseFailAlloc_3159_ = lean_alloc_ctor(0, 17, 0);
lean_ctor_set(v_reuseFailAlloc_3159_, 0, v_id_3136_);
lean_ctor_set(v_reuseFailAlloc_3159_, 1, v_type_3137_);
lean_ctor_set(v_reuseFailAlloc_3159_, 2, v_u_3138_);
lean_ctor_set(v_reuseFailAlloc_3159_, 3, v_ringInst_3139_);
lean_ctor_set(v_reuseFailAlloc_3159_, 4, v_semiringInst_3140_);
lean_ctor_set(v_reuseFailAlloc_3159_, 5, v_charInst_x3f_3141_);
lean_ctor_set(v_reuseFailAlloc_3159_, 6, v_addFn_x3f_3142_);
lean_ctor_set(v_reuseFailAlloc_3159_, 7, v_mulFn_x3f_3143_);
lean_ctor_set(v_reuseFailAlloc_3159_, 8, v_subFn_x3f_3144_);
lean_ctor_set(v_reuseFailAlloc_3159_, 9, v_negFn_x3f_3145_);
lean_ctor_set(v_reuseFailAlloc_3159_, 10, v_powFn_x3f_3146_);
lean_ctor_set(v_reuseFailAlloc_3159_, 11, v_intCastFn_x3f_3147_);
lean_ctor_set(v_reuseFailAlloc_3159_, 12, v_natCastFn_x3f_3148_);
lean_ctor_set(v_reuseFailAlloc_3159_, 13, v_one_x3f_3149_);
lean_ctor_set(v_reuseFailAlloc_3159_, 14, v_vars_3150_);
lean_ctor_set(v_reuseFailAlloc_3159_, 15, v_varMap_3151_);
lean_ctor_set(v_reuseFailAlloc_3159_, 16, v___x_3156_);
v___x_3158_ = v_reuseFailAlloc_3159_;
goto v_reusejp_3157_;
}
v_reusejp_3157_:
{
return v___x_3158_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_internalize___lam__3(lean_object* v_e_3161_, lean_object* v_val_3162_, lean_object* v_s_3163_){
_start:
{
lean_object* v_id_3164_; lean_object* v_type_3165_; lean_object* v_u_3166_; lean_object* v_semiringInst_3167_; lean_object* v_addFn_x3f_3168_; lean_object* v_mulFn_x3f_3169_; lean_object* v_powFn_x3f_3170_; lean_object* v_natCastFn_x3f_3171_; lean_object* v_denote_3172_; lean_object* v_vars_3173_; lean_object* v_varMap_3174_; lean_object* v___x_3176_; uint8_t v_isShared_3177_; uint8_t v_isSharedCheck_3182_; 
v_id_3164_ = lean_ctor_get(v_s_3163_, 0);
v_type_3165_ = lean_ctor_get(v_s_3163_, 1);
v_u_3166_ = lean_ctor_get(v_s_3163_, 2);
v_semiringInst_3167_ = lean_ctor_get(v_s_3163_, 3);
v_addFn_x3f_3168_ = lean_ctor_get(v_s_3163_, 4);
v_mulFn_x3f_3169_ = lean_ctor_get(v_s_3163_, 5);
v_powFn_x3f_3170_ = lean_ctor_get(v_s_3163_, 6);
v_natCastFn_x3f_3171_ = lean_ctor_get(v_s_3163_, 7);
v_denote_3172_ = lean_ctor_get(v_s_3163_, 8);
v_vars_3173_ = lean_ctor_get(v_s_3163_, 9);
v_varMap_3174_ = lean_ctor_get(v_s_3163_, 10);
v_isSharedCheck_3182_ = !lean_is_exclusive(v_s_3163_);
if (v_isSharedCheck_3182_ == 0)
{
v___x_3176_ = v_s_3163_;
v_isShared_3177_ = v_isSharedCheck_3182_;
goto v_resetjp_3175_;
}
else
{
lean_inc(v_varMap_3174_);
lean_inc(v_vars_3173_);
lean_inc(v_denote_3172_);
lean_inc(v_natCastFn_x3f_3171_);
lean_inc(v_powFn_x3f_3170_);
lean_inc(v_mulFn_x3f_3169_);
lean_inc(v_addFn_x3f_3168_);
lean_inc(v_semiringInst_3167_);
lean_inc(v_u_3166_);
lean_inc(v_type_3165_);
lean_inc(v_id_3164_);
lean_dec(v_s_3163_);
v___x_3176_ = lean_box(0);
v_isShared_3177_ = v_isSharedCheck_3182_;
goto v_resetjp_3175_;
}
v_resetjp_3175_:
{
lean_object* v___x_3178_; lean_object* v___x_3180_; 
v___x_3178_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0___redArg(v_denote_3172_, v_e_3161_, v_val_3162_);
if (v_isShared_3177_ == 0)
{
lean_ctor_set(v___x_3176_, 8, v___x_3178_);
v___x_3180_ = v___x_3176_;
goto v_reusejp_3179_;
}
else
{
lean_object* v_reuseFailAlloc_3181_; 
v_reuseFailAlloc_3181_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_3181_, 0, v_id_3164_);
lean_ctor_set(v_reuseFailAlloc_3181_, 1, v_type_3165_);
lean_ctor_set(v_reuseFailAlloc_3181_, 2, v_u_3166_);
lean_ctor_set(v_reuseFailAlloc_3181_, 3, v_semiringInst_3167_);
lean_ctor_set(v_reuseFailAlloc_3181_, 4, v_addFn_x3f_3168_);
lean_ctor_set(v_reuseFailAlloc_3181_, 5, v_mulFn_x3f_3169_);
lean_ctor_set(v_reuseFailAlloc_3181_, 6, v_powFn_x3f_3170_);
lean_ctor_set(v_reuseFailAlloc_3181_, 7, v_natCastFn_x3f_3171_);
lean_ctor_set(v_reuseFailAlloc_3181_, 8, v___x_3178_);
lean_ctor_set(v_reuseFailAlloc_3181_, 9, v_vars_3173_);
lean_ctor_set(v_reuseFailAlloc_3181_, 10, v_varMap_3174_);
v___x_3180_ = v_reuseFailAlloc_3181_;
goto v_reusejp_3179_;
}
v_reusejp_3179_:
{
return v___x_3180_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__1___redArg(lean_object* v_cls_3183_, lean_object* v_msg_3184_, lean_object* v___y_3185_, lean_object* v___y_3186_, lean_object* v___y_3187_, lean_object* v___y_3188_){
_start:
{
lean_object* v_ref_3190_; lean_object* v___x_3191_; lean_object* v_a_3192_; lean_object* v___x_3194_; uint8_t v_isShared_3195_; uint8_t v_isSharedCheck_3236_; 
v_ref_3190_ = lean_ctor_get(v___y_3187_, 5);
v___x_3191_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1_spec__5_spec__8_spec__9(v_msg_3184_, v___y_3185_, v___y_3186_, v___y_3187_, v___y_3188_);
v_a_3192_ = lean_ctor_get(v___x_3191_, 0);
v_isSharedCheck_3236_ = !lean_is_exclusive(v___x_3191_);
if (v_isSharedCheck_3236_ == 0)
{
v___x_3194_ = v___x_3191_;
v_isShared_3195_ = v_isSharedCheck_3236_;
goto v_resetjp_3193_;
}
else
{
lean_inc(v_a_3192_);
lean_dec(v___x_3191_);
v___x_3194_ = lean_box(0);
v_isShared_3195_ = v_isSharedCheck_3236_;
goto v_resetjp_3193_;
}
v_resetjp_3193_:
{
lean_object* v___x_3196_; lean_object* v_traceState_3197_; lean_object* v_env_3198_; lean_object* v_nextMacroScope_3199_; lean_object* v_ngen_3200_; lean_object* v_auxDeclNGen_3201_; lean_object* v_cache_3202_; lean_object* v_messages_3203_; lean_object* v_infoState_3204_; lean_object* v_snapshotTasks_3205_; lean_object* v___x_3207_; uint8_t v_isShared_3208_; uint8_t v_isSharedCheck_3235_; 
v___x_3196_ = lean_st_ref_take(v___y_3188_);
v_traceState_3197_ = lean_ctor_get(v___x_3196_, 4);
v_env_3198_ = lean_ctor_get(v___x_3196_, 0);
v_nextMacroScope_3199_ = lean_ctor_get(v___x_3196_, 1);
v_ngen_3200_ = lean_ctor_get(v___x_3196_, 2);
v_auxDeclNGen_3201_ = lean_ctor_get(v___x_3196_, 3);
v_cache_3202_ = lean_ctor_get(v___x_3196_, 5);
v_messages_3203_ = lean_ctor_get(v___x_3196_, 6);
v_infoState_3204_ = lean_ctor_get(v___x_3196_, 7);
v_snapshotTasks_3205_ = lean_ctor_get(v___x_3196_, 8);
v_isSharedCheck_3235_ = !lean_is_exclusive(v___x_3196_);
if (v_isSharedCheck_3235_ == 0)
{
v___x_3207_ = v___x_3196_;
v_isShared_3208_ = v_isSharedCheck_3235_;
goto v_resetjp_3206_;
}
else
{
lean_inc(v_snapshotTasks_3205_);
lean_inc(v_infoState_3204_);
lean_inc(v_messages_3203_);
lean_inc(v_cache_3202_);
lean_inc(v_traceState_3197_);
lean_inc(v_auxDeclNGen_3201_);
lean_inc(v_ngen_3200_);
lean_inc(v_nextMacroScope_3199_);
lean_inc(v_env_3198_);
lean_dec(v___x_3196_);
v___x_3207_ = lean_box(0);
v_isShared_3208_ = v_isSharedCheck_3235_;
goto v_resetjp_3206_;
}
v_resetjp_3206_:
{
uint64_t v_tid_3209_; lean_object* v_traces_3210_; lean_object* v___x_3212_; uint8_t v_isShared_3213_; uint8_t v_isSharedCheck_3234_; 
v_tid_3209_ = lean_ctor_get_uint64(v_traceState_3197_, sizeof(void*)*1);
v_traces_3210_ = lean_ctor_get(v_traceState_3197_, 0);
v_isSharedCheck_3234_ = !lean_is_exclusive(v_traceState_3197_);
if (v_isSharedCheck_3234_ == 0)
{
v___x_3212_ = v_traceState_3197_;
v_isShared_3213_ = v_isSharedCheck_3234_;
goto v_resetjp_3211_;
}
else
{
lean_inc(v_traces_3210_);
lean_dec(v_traceState_3197_);
v___x_3212_ = lean_box(0);
v_isShared_3213_ = v_isSharedCheck_3234_;
goto v_resetjp_3211_;
}
v_resetjp_3211_:
{
lean_object* v___x_3214_; double v___x_3215_; uint8_t v___x_3216_; lean_object* v___x_3217_; lean_object* v___x_3218_; lean_object* v___x_3219_; lean_object* v___x_3220_; lean_object* v___x_3221_; lean_object* v___x_3222_; lean_object* v___x_3224_; 
v___x_3214_ = lean_box(0);
v___x_3215_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg___closed__0);
v___x_3216_ = 0;
v___x_3217_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg___closed__1));
v___x_3218_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3218_, 0, v_cls_3183_);
lean_ctor_set(v___x_3218_, 1, v___x_3214_);
lean_ctor_set(v___x_3218_, 2, v___x_3217_);
lean_ctor_set_float(v___x_3218_, sizeof(void*)*3, v___x_3215_);
lean_ctor_set_float(v___x_3218_, sizeof(void*)*3 + 8, v___x_3215_);
lean_ctor_set_uint8(v___x_3218_, sizeof(void*)*3 + 16, v___x_3216_);
v___x_3219_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg___closed__2));
v___x_3220_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3220_, 0, v___x_3218_);
lean_ctor_set(v___x_3220_, 1, v_a_3192_);
lean_ctor_set(v___x_3220_, 2, v___x_3219_);
lean_inc(v_ref_3190_);
v___x_3221_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3221_, 0, v_ref_3190_);
lean_ctor_set(v___x_3221_, 1, v___x_3220_);
v___x_3222_ = l_Lean_PersistentArray_push___redArg(v_traces_3210_, v___x_3221_);
if (v_isShared_3213_ == 0)
{
lean_ctor_set(v___x_3212_, 0, v___x_3222_);
v___x_3224_ = v___x_3212_;
goto v_reusejp_3223_;
}
else
{
lean_object* v_reuseFailAlloc_3233_; 
v_reuseFailAlloc_3233_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3233_, 0, v___x_3222_);
lean_ctor_set_uint64(v_reuseFailAlloc_3233_, sizeof(void*)*1, v_tid_3209_);
v___x_3224_ = v_reuseFailAlloc_3233_;
goto v_reusejp_3223_;
}
v_reusejp_3223_:
{
lean_object* v___x_3226_; 
if (v_isShared_3208_ == 0)
{
lean_ctor_set(v___x_3207_, 4, v___x_3224_);
v___x_3226_ = v___x_3207_;
goto v_reusejp_3225_;
}
else
{
lean_object* v_reuseFailAlloc_3232_; 
v_reuseFailAlloc_3232_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3232_, 0, v_env_3198_);
lean_ctor_set(v_reuseFailAlloc_3232_, 1, v_nextMacroScope_3199_);
lean_ctor_set(v_reuseFailAlloc_3232_, 2, v_ngen_3200_);
lean_ctor_set(v_reuseFailAlloc_3232_, 3, v_auxDeclNGen_3201_);
lean_ctor_set(v_reuseFailAlloc_3232_, 4, v___x_3224_);
lean_ctor_set(v_reuseFailAlloc_3232_, 5, v_cache_3202_);
lean_ctor_set(v_reuseFailAlloc_3232_, 6, v_messages_3203_);
lean_ctor_set(v_reuseFailAlloc_3232_, 7, v_infoState_3204_);
lean_ctor_set(v_reuseFailAlloc_3232_, 8, v_snapshotTasks_3205_);
v___x_3226_ = v_reuseFailAlloc_3232_;
goto v_reusejp_3225_;
}
v_reusejp_3225_:
{
lean_object* v___x_3227_; lean_object* v___x_3228_; lean_object* v___x_3230_; 
v___x_3227_ = lean_st_ref_set(v___y_3188_, v___x_3226_);
v___x_3228_ = lean_box(0);
if (v_isShared_3195_ == 0)
{
lean_ctor_set(v___x_3194_, 0, v___x_3228_);
v___x_3230_ = v___x_3194_;
goto v_reusejp_3229_;
}
else
{
lean_object* v_reuseFailAlloc_3231_; 
v_reuseFailAlloc_3231_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3231_, 0, v___x_3228_);
v___x_3230_ = v_reuseFailAlloc_3231_;
goto v_reusejp_3229_;
}
v_reusejp_3229_:
{
return v___x_3230_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__1___redArg___boxed(lean_object* v_cls_3237_, lean_object* v_msg_3238_, lean_object* v___y_3239_, lean_object* v___y_3240_, lean_object* v___y_3241_, lean_object* v___y_3242_, lean_object* v___y_3243_){
_start:
{
lean_object* v_res_3244_; 
v_res_3244_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__1___redArg(v_cls_3237_, v_msg_3238_, v___y_3239_, v___y_3240_, v___y_3241_, v___y_3242_);
lean_dec(v___y_3242_);
lean_dec_ref(v___y_3241_);
lean_dec(v___y_3240_);
lean_dec_ref(v___y_3239_);
return v_res_3244_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__2___redArg(lean_object* v_cls_3245_, lean_object* v_msg_3246_, lean_object* v___y_3247_, lean_object* v___y_3248_, lean_object* v___y_3249_, lean_object* v___y_3250_){
_start:
{
lean_object* v_ref_3252_; lean_object* v___x_3253_; lean_object* v_a_3254_; lean_object* v___x_3256_; uint8_t v_isShared_3257_; uint8_t v_isSharedCheck_3298_; 
v_ref_3252_ = lean_ctor_get(v___y_3249_, 5);
v___x_3253_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1_spec__5_spec__8_spec__9(v_msg_3246_, v___y_3247_, v___y_3248_, v___y_3249_, v___y_3250_);
v_a_3254_ = lean_ctor_get(v___x_3253_, 0);
v_isSharedCheck_3298_ = !lean_is_exclusive(v___x_3253_);
if (v_isSharedCheck_3298_ == 0)
{
v___x_3256_ = v___x_3253_;
v_isShared_3257_ = v_isSharedCheck_3298_;
goto v_resetjp_3255_;
}
else
{
lean_inc(v_a_3254_);
lean_dec(v___x_3253_);
v___x_3256_ = lean_box(0);
v_isShared_3257_ = v_isSharedCheck_3298_;
goto v_resetjp_3255_;
}
v_resetjp_3255_:
{
lean_object* v___x_3258_; lean_object* v_traceState_3259_; lean_object* v_env_3260_; lean_object* v_nextMacroScope_3261_; lean_object* v_ngen_3262_; lean_object* v_auxDeclNGen_3263_; lean_object* v_cache_3264_; lean_object* v_messages_3265_; lean_object* v_infoState_3266_; lean_object* v_snapshotTasks_3267_; lean_object* v___x_3269_; uint8_t v_isShared_3270_; uint8_t v_isSharedCheck_3297_; 
v___x_3258_ = lean_st_ref_take(v___y_3250_);
v_traceState_3259_ = lean_ctor_get(v___x_3258_, 4);
v_env_3260_ = lean_ctor_get(v___x_3258_, 0);
v_nextMacroScope_3261_ = lean_ctor_get(v___x_3258_, 1);
v_ngen_3262_ = lean_ctor_get(v___x_3258_, 2);
v_auxDeclNGen_3263_ = lean_ctor_get(v___x_3258_, 3);
v_cache_3264_ = lean_ctor_get(v___x_3258_, 5);
v_messages_3265_ = lean_ctor_get(v___x_3258_, 6);
v_infoState_3266_ = lean_ctor_get(v___x_3258_, 7);
v_snapshotTasks_3267_ = lean_ctor_get(v___x_3258_, 8);
v_isSharedCheck_3297_ = !lean_is_exclusive(v___x_3258_);
if (v_isSharedCheck_3297_ == 0)
{
v___x_3269_ = v___x_3258_;
v_isShared_3270_ = v_isSharedCheck_3297_;
goto v_resetjp_3268_;
}
else
{
lean_inc(v_snapshotTasks_3267_);
lean_inc(v_infoState_3266_);
lean_inc(v_messages_3265_);
lean_inc(v_cache_3264_);
lean_inc(v_traceState_3259_);
lean_inc(v_auxDeclNGen_3263_);
lean_inc(v_ngen_3262_);
lean_inc(v_nextMacroScope_3261_);
lean_inc(v_env_3260_);
lean_dec(v___x_3258_);
v___x_3269_ = lean_box(0);
v_isShared_3270_ = v_isSharedCheck_3297_;
goto v_resetjp_3268_;
}
v_resetjp_3268_:
{
uint64_t v_tid_3271_; lean_object* v_traces_3272_; lean_object* v___x_3274_; uint8_t v_isShared_3275_; uint8_t v_isSharedCheck_3296_; 
v_tid_3271_ = lean_ctor_get_uint64(v_traceState_3259_, sizeof(void*)*1);
v_traces_3272_ = lean_ctor_get(v_traceState_3259_, 0);
v_isSharedCheck_3296_ = !lean_is_exclusive(v_traceState_3259_);
if (v_isSharedCheck_3296_ == 0)
{
v___x_3274_ = v_traceState_3259_;
v_isShared_3275_ = v_isSharedCheck_3296_;
goto v_resetjp_3273_;
}
else
{
lean_inc(v_traces_3272_);
lean_dec(v_traceState_3259_);
v___x_3274_ = lean_box(0);
v_isShared_3275_ = v_isSharedCheck_3296_;
goto v_resetjp_3273_;
}
v_resetjp_3273_:
{
lean_object* v___x_3276_; double v___x_3277_; uint8_t v___x_3278_; lean_object* v___x_3279_; lean_object* v___x_3280_; lean_object* v___x_3281_; lean_object* v___x_3282_; lean_object* v___x_3283_; lean_object* v___x_3284_; lean_object* v___x_3286_; 
v___x_3276_ = lean_box(0);
v___x_3277_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg___closed__0);
v___x_3278_ = 0;
v___x_3279_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg___closed__1));
v___x_3280_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3280_, 0, v_cls_3245_);
lean_ctor_set(v___x_3280_, 1, v___x_3276_);
lean_ctor_set(v___x_3280_, 2, v___x_3279_);
lean_ctor_set_float(v___x_3280_, sizeof(void*)*3, v___x_3277_);
lean_ctor_set_float(v___x_3280_, sizeof(void*)*3 + 8, v___x_3277_);
lean_ctor_set_uint8(v___x_3280_, sizeof(void*)*3 + 16, v___x_3278_);
v___x_3281_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg___closed__2));
v___x_3282_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3282_, 0, v___x_3280_);
lean_ctor_set(v___x_3282_, 1, v_a_3254_);
lean_ctor_set(v___x_3282_, 2, v___x_3281_);
lean_inc(v_ref_3252_);
v___x_3283_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3283_, 0, v_ref_3252_);
lean_ctor_set(v___x_3283_, 1, v___x_3282_);
v___x_3284_ = l_Lean_PersistentArray_push___redArg(v_traces_3272_, v___x_3283_);
if (v_isShared_3275_ == 0)
{
lean_ctor_set(v___x_3274_, 0, v___x_3284_);
v___x_3286_ = v___x_3274_;
goto v_reusejp_3285_;
}
else
{
lean_object* v_reuseFailAlloc_3295_; 
v_reuseFailAlloc_3295_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3295_, 0, v___x_3284_);
lean_ctor_set_uint64(v_reuseFailAlloc_3295_, sizeof(void*)*1, v_tid_3271_);
v___x_3286_ = v_reuseFailAlloc_3295_;
goto v_reusejp_3285_;
}
v_reusejp_3285_:
{
lean_object* v___x_3288_; 
if (v_isShared_3270_ == 0)
{
lean_ctor_set(v___x_3269_, 4, v___x_3286_);
v___x_3288_ = v___x_3269_;
goto v_reusejp_3287_;
}
else
{
lean_object* v_reuseFailAlloc_3294_; 
v_reuseFailAlloc_3294_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3294_, 0, v_env_3260_);
lean_ctor_set(v_reuseFailAlloc_3294_, 1, v_nextMacroScope_3261_);
lean_ctor_set(v_reuseFailAlloc_3294_, 2, v_ngen_3262_);
lean_ctor_set(v_reuseFailAlloc_3294_, 3, v_auxDeclNGen_3263_);
lean_ctor_set(v_reuseFailAlloc_3294_, 4, v___x_3286_);
lean_ctor_set(v_reuseFailAlloc_3294_, 5, v_cache_3264_);
lean_ctor_set(v_reuseFailAlloc_3294_, 6, v_messages_3265_);
lean_ctor_set(v_reuseFailAlloc_3294_, 7, v_infoState_3266_);
lean_ctor_set(v_reuseFailAlloc_3294_, 8, v_snapshotTasks_3267_);
v___x_3288_ = v_reuseFailAlloc_3294_;
goto v_reusejp_3287_;
}
v_reusejp_3287_:
{
lean_object* v___x_3289_; lean_object* v___x_3290_; lean_object* v___x_3292_; 
v___x_3289_ = lean_st_ref_set(v___y_3250_, v___x_3288_);
v___x_3290_ = lean_box(0);
if (v_isShared_3257_ == 0)
{
lean_ctor_set(v___x_3256_, 0, v___x_3290_);
v___x_3292_ = v___x_3256_;
goto v_reusejp_3291_;
}
else
{
lean_object* v_reuseFailAlloc_3293_; 
v_reuseFailAlloc_3293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3293_, 0, v___x_3290_);
v___x_3292_ = v_reuseFailAlloc_3293_;
goto v_reusejp_3291_;
}
v_reusejp_3291_:
{
return v___x_3292_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__2___redArg___boxed(lean_object* v_cls_3299_, lean_object* v_msg_3300_, lean_object* v___y_3301_, lean_object* v___y_3302_, lean_object* v___y_3303_, lean_object* v___y_3304_, lean_object* v___y_3305_){
_start:
{
lean_object* v_res_3306_; 
v_res_3306_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__2___redArg(v_cls_3299_, v_msg_3300_, v___y_3301_, v___y_3302_, v___y_3303_, v___y_3304_);
lean_dec(v___y_3304_);
lean_dec_ref(v___y_3303_);
lean_dec(v___y_3302_);
lean_dec_ref(v___y_3301_);
return v_res_3306_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__3___redArg(lean_object* v_cls_3307_, lean_object* v_msg_3308_, lean_object* v___y_3309_, lean_object* v___y_3310_, lean_object* v___y_3311_, lean_object* v___y_3312_){
_start:
{
lean_object* v_ref_3314_; lean_object* v___x_3315_; lean_object* v_a_3316_; lean_object* v___x_3318_; uint8_t v_isShared_3319_; uint8_t v_isSharedCheck_3360_; 
v_ref_3314_ = lean_ctor_get(v___y_3311_, 5);
v___x_3315_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1_spec__5_spec__8_spec__9(v_msg_3308_, v___y_3309_, v___y_3310_, v___y_3311_, v___y_3312_);
v_a_3316_ = lean_ctor_get(v___x_3315_, 0);
v_isSharedCheck_3360_ = !lean_is_exclusive(v___x_3315_);
if (v_isSharedCheck_3360_ == 0)
{
v___x_3318_ = v___x_3315_;
v_isShared_3319_ = v_isSharedCheck_3360_;
goto v_resetjp_3317_;
}
else
{
lean_inc(v_a_3316_);
lean_dec(v___x_3315_);
v___x_3318_ = lean_box(0);
v_isShared_3319_ = v_isSharedCheck_3360_;
goto v_resetjp_3317_;
}
v_resetjp_3317_:
{
lean_object* v___x_3320_; lean_object* v_traceState_3321_; lean_object* v_env_3322_; lean_object* v_nextMacroScope_3323_; lean_object* v_ngen_3324_; lean_object* v_auxDeclNGen_3325_; lean_object* v_cache_3326_; lean_object* v_messages_3327_; lean_object* v_infoState_3328_; lean_object* v_snapshotTasks_3329_; lean_object* v___x_3331_; uint8_t v_isShared_3332_; uint8_t v_isSharedCheck_3359_; 
v___x_3320_ = lean_st_ref_take(v___y_3312_);
v_traceState_3321_ = lean_ctor_get(v___x_3320_, 4);
v_env_3322_ = lean_ctor_get(v___x_3320_, 0);
v_nextMacroScope_3323_ = lean_ctor_get(v___x_3320_, 1);
v_ngen_3324_ = lean_ctor_get(v___x_3320_, 2);
v_auxDeclNGen_3325_ = lean_ctor_get(v___x_3320_, 3);
v_cache_3326_ = lean_ctor_get(v___x_3320_, 5);
v_messages_3327_ = lean_ctor_get(v___x_3320_, 6);
v_infoState_3328_ = lean_ctor_get(v___x_3320_, 7);
v_snapshotTasks_3329_ = lean_ctor_get(v___x_3320_, 8);
v_isSharedCheck_3359_ = !lean_is_exclusive(v___x_3320_);
if (v_isSharedCheck_3359_ == 0)
{
v___x_3331_ = v___x_3320_;
v_isShared_3332_ = v_isSharedCheck_3359_;
goto v_resetjp_3330_;
}
else
{
lean_inc(v_snapshotTasks_3329_);
lean_inc(v_infoState_3328_);
lean_inc(v_messages_3327_);
lean_inc(v_cache_3326_);
lean_inc(v_traceState_3321_);
lean_inc(v_auxDeclNGen_3325_);
lean_inc(v_ngen_3324_);
lean_inc(v_nextMacroScope_3323_);
lean_inc(v_env_3322_);
lean_dec(v___x_3320_);
v___x_3331_ = lean_box(0);
v_isShared_3332_ = v_isSharedCheck_3359_;
goto v_resetjp_3330_;
}
v_resetjp_3330_:
{
uint64_t v_tid_3333_; lean_object* v_traces_3334_; lean_object* v___x_3336_; uint8_t v_isShared_3337_; uint8_t v_isSharedCheck_3358_; 
v_tid_3333_ = lean_ctor_get_uint64(v_traceState_3321_, sizeof(void*)*1);
v_traces_3334_ = lean_ctor_get(v_traceState_3321_, 0);
v_isSharedCheck_3358_ = !lean_is_exclusive(v_traceState_3321_);
if (v_isSharedCheck_3358_ == 0)
{
v___x_3336_ = v_traceState_3321_;
v_isShared_3337_ = v_isSharedCheck_3358_;
goto v_resetjp_3335_;
}
else
{
lean_inc(v_traces_3334_);
lean_dec(v_traceState_3321_);
v___x_3336_ = lean_box(0);
v_isShared_3337_ = v_isSharedCheck_3358_;
goto v_resetjp_3335_;
}
v_resetjp_3335_:
{
lean_object* v___x_3338_; double v___x_3339_; uint8_t v___x_3340_; lean_object* v___x_3341_; lean_object* v___x_3342_; lean_object* v___x_3343_; lean_object* v___x_3344_; lean_object* v___x_3345_; lean_object* v___x_3346_; lean_object* v___x_3348_; 
v___x_3338_ = lean_box(0);
v___x_3339_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg___closed__0);
v___x_3340_ = 0;
v___x_3341_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg___closed__1));
v___x_3342_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3342_, 0, v_cls_3307_);
lean_ctor_set(v___x_3342_, 1, v___x_3338_);
lean_ctor_set(v___x_3342_, 2, v___x_3341_);
lean_ctor_set_float(v___x_3342_, sizeof(void*)*3, v___x_3339_);
lean_ctor_set_float(v___x_3342_, sizeof(void*)*3 + 8, v___x_3339_);
lean_ctor_set_uint8(v___x_3342_, sizeof(void*)*3 + 16, v___x_3340_);
v___x_3343_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg___closed__2));
v___x_3344_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3344_, 0, v___x_3342_);
lean_ctor_set(v___x_3344_, 1, v_a_3316_);
lean_ctor_set(v___x_3344_, 2, v___x_3343_);
lean_inc(v_ref_3314_);
v___x_3345_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3345_, 0, v_ref_3314_);
lean_ctor_set(v___x_3345_, 1, v___x_3344_);
v___x_3346_ = l_Lean_PersistentArray_push___redArg(v_traces_3334_, v___x_3345_);
if (v_isShared_3337_ == 0)
{
lean_ctor_set(v___x_3336_, 0, v___x_3346_);
v___x_3348_ = v___x_3336_;
goto v_reusejp_3347_;
}
else
{
lean_object* v_reuseFailAlloc_3357_; 
v_reuseFailAlloc_3357_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3357_, 0, v___x_3346_);
lean_ctor_set_uint64(v_reuseFailAlloc_3357_, sizeof(void*)*1, v_tid_3333_);
v___x_3348_ = v_reuseFailAlloc_3357_;
goto v_reusejp_3347_;
}
v_reusejp_3347_:
{
lean_object* v___x_3350_; 
if (v_isShared_3332_ == 0)
{
lean_ctor_set(v___x_3331_, 4, v___x_3348_);
v___x_3350_ = v___x_3331_;
goto v_reusejp_3349_;
}
else
{
lean_object* v_reuseFailAlloc_3356_; 
v_reuseFailAlloc_3356_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3356_, 0, v_env_3322_);
lean_ctor_set(v_reuseFailAlloc_3356_, 1, v_nextMacroScope_3323_);
lean_ctor_set(v_reuseFailAlloc_3356_, 2, v_ngen_3324_);
lean_ctor_set(v_reuseFailAlloc_3356_, 3, v_auxDeclNGen_3325_);
lean_ctor_set(v_reuseFailAlloc_3356_, 4, v___x_3348_);
lean_ctor_set(v_reuseFailAlloc_3356_, 5, v_cache_3326_);
lean_ctor_set(v_reuseFailAlloc_3356_, 6, v_messages_3327_);
lean_ctor_set(v_reuseFailAlloc_3356_, 7, v_infoState_3328_);
lean_ctor_set(v_reuseFailAlloc_3356_, 8, v_snapshotTasks_3329_);
v___x_3350_ = v_reuseFailAlloc_3356_;
goto v_reusejp_3349_;
}
v_reusejp_3349_:
{
lean_object* v___x_3351_; lean_object* v___x_3352_; lean_object* v___x_3354_; 
v___x_3351_ = lean_st_ref_set(v___y_3312_, v___x_3350_);
v___x_3352_ = lean_box(0);
if (v_isShared_3319_ == 0)
{
lean_ctor_set(v___x_3318_, 0, v___x_3352_);
v___x_3354_ = v___x_3318_;
goto v_reusejp_3353_;
}
else
{
lean_object* v_reuseFailAlloc_3355_; 
v_reuseFailAlloc_3355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3355_, 0, v___x_3352_);
v___x_3354_ = v_reuseFailAlloc_3355_;
goto v_reusejp_3353_;
}
v_reusejp_3353_:
{
return v___x_3354_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__3___redArg___boxed(lean_object* v_cls_3361_, lean_object* v_msg_3362_, lean_object* v___y_3363_, lean_object* v___y_3364_, lean_object* v___y_3365_, lean_object* v___y_3366_, lean_object* v___y_3367_){
_start:
{
lean_object* v_res_3368_; 
v_res_3368_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__3___redArg(v_cls_3361_, v_msg_3362_, v___y_3363_, v___y_3364_, v___y_3365_, v___y_3366_);
lean_dec(v___y_3366_);
lean_dec_ref(v___y_3365_);
lean_dec(v___y_3364_);
lean_dec_ref(v___y_3363_);
return v_res_3368_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__2(void){
_start:
{
lean_object* v___x_3374_; lean_object* v___x_3375_; lean_object* v___x_3376_; 
v___x_3374_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__1));
v___x_3375_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__7));
v___x_3376_ = l_Lean_Name_append(v___x_3375_, v___x_3374_);
return v___x_3376_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__4(void){
_start:
{
lean_object* v___x_3378_; lean_object* v___x_3379_; 
v___x_3378_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__3));
v___x_3379_ = l_Lean_stringToMessageData(v___x_3378_);
return v___x_3379_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__6(void){
_start:
{
lean_object* v___x_3381_; lean_object* v___x_3382_; 
v___x_3381_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__5));
v___x_3382_ = l_Lean_stringToMessageData(v___x_3381_);
return v___x_3382_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__8(void){
_start:
{
lean_object* v___x_3384_; lean_object* v___x_3385_; 
v___x_3384_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__7));
v___x_3385_ = l_Lean_stringToMessageData(v___x_3384_);
return v___x_3385_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__10(void){
_start:
{
lean_object* v___x_3387_; lean_object* v___x_3388_; 
v___x_3387_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__9));
v___x_3388_ = l_Lean_stringToMessageData(v___x_3387_);
return v___x_3388_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__12(void){
_start:
{
lean_object* v___x_3390_; lean_object* v___x_3391_; 
v___x_3390_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__11));
v___x_3391_ = l_Lean_stringToMessageData(v___x_3390_);
return v___x_3391_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_internalize(lean_object* v_e_3392_, lean_object* v_parent_x3f_3393_, lean_object* v_a_3394_, lean_object* v_a_3395_, lean_object* v_a_3396_, lean_object* v_a_3397_, lean_object* v_a_3398_, lean_object* v_a_3399_, lean_object* v_a_3400_, lean_object* v_a_3401_, lean_object* v_a_3402_, lean_object* v_a_3403_){
_start:
{
lean_object* v___x_3405_; 
v___x_3405_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_3396_);
if (lean_obj_tag(v___x_3405_) == 0)
{
lean_object* v_a_3406_; lean_object* v___x_3408_; uint8_t v_isShared_3409_; uint8_t v_isSharedCheck_3746_; 
v_a_3406_ = lean_ctor_get(v___x_3405_, 0);
v_isSharedCheck_3746_ = !lean_is_exclusive(v___x_3405_);
if (v_isSharedCheck_3746_ == 0)
{
v___x_3408_ = v___x_3405_;
v_isShared_3409_ = v_isSharedCheck_3746_;
goto v_resetjp_3407_;
}
else
{
lean_inc(v_a_3406_);
lean_dec(v___x_3405_);
v___x_3408_ = lean_box(0);
v_isShared_3409_ = v_isSharedCheck_3746_;
goto v_resetjp_3407_;
}
v_resetjp_3407_:
{
uint8_t v_ring_3410_; 
v_ring_3410_ = lean_ctor_get_uint8(v_a_3406_, sizeof(void*)*12 + 21);
lean_dec(v_a_3406_);
if (v_ring_3410_ == 0)
{
lean_object* v___x_3411_; lean_object* v___x_3413_; 
lean_dec(v_parent_x3f_3393_);
lean_dec_ref(v_e_3392_);
v___x_3411_ = lean_box(0);
if (v_isShared_3409_ == 0)
{
lean_ctor_set(v___x_3408_, 0, v___x_3411_);
v___x_3413_ = v___x_3408_;
goto v_reusejp_3412_;
}
else
{
lean_object* v_reuseFailAlloc_3414_; 
v_reuseFailAlloc_3414_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3414_, 0, v___x_3411_);
v___x_3413_ = v_reuseFailAlloc_3414_;
goto v_reusejp_3412_;
}
v_reusejp_3412_:
{
return v___x_3413_;
}
}
else
{
uint8_t v___x_3415_; 
v___x_3415_ = l_Lean_Meta_Grind_Arith_isIntModuleVirtualParent(v_parent_x3f_3393_);
if (v___x_3415_ == 0)
{
lean_object* v___x_3416_; 
lean_del_object(v___x_3408_);
lean_inc_ref(v_e_3392_);
v___x_3416_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeInv(v_e_3392_, v_a_3394_, v_a_3395_, v_a_3396_, v_a_3397_, v_a_3398_, v_a_3399_, v_a_3400_, v_a_3401_, v_a_3402_, v_a_3403_);
if (lean_obj_tag(v___x_3416_) == 0)
{
lean_object* v_a_3417_; lean_object* v___x_3419_; uint8_t v_isShared_3420_; uint8_t v_isSharedCheck_3733_; 
v_a_3417_ = lean_ctor_get(v___x_3416_, 0);
v_isSharedCheck_3733_ = !lean_is_exclusive(v___x_3416_);
if (v_isSharedCheck_3733_ == 0)
{
v___x_3419_ = v___x_3416_;
v_isShared_3420_ = v_isSharedCheck_3733_;
goto v_resetjp_3418_;
}
else
{
lean_inc(v_a_3417_);
lean_dec(v___x_3416_);
v___x_3419_ = lean_box(0);
v_isShared_3420_ = v_isSharedCheck_3733_;
goto v_resetjp_3418_;
}
v_resetjp_3418_:
{
uint8_t v___x_3421_; 
v___x_3421_ = lean_unbox(v_a_3417_);
lean_dec(v_a_3417_);
if (v___x_3421_ == 0)
{
lean_object* v___x_3422_; 
lean_inc_ref(v_e_3392_);
v___x_3422_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f(v_e_3392_);
if (lean_obj_tag(v___x_3422_) == 1)
{
lean_object* v_val_3423_; uint8_t v___x_3424_; 
v_val_3423_ = lean_ctor_get(v___x_3422_, 0);
lean_inc(v_val_3423_);
lean_dec_ref(v___x_3422_);
v___x_3424_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isForbiddenParent(v_parent_x3f_3393_);
if (v___x_3424_ == 0)
{
lean_object* v___x_3425_; 
lean_del_object(v___x_3419_);
lean_inc(v_val_3423_);
v___x_3425_ = l_Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f(v_val_3423_, v_a_3394_, v_a_3395_, v_a_3396_, v_a_3397_, v_a_3398_, v_a_3399_, v_a_3400_, v_a_3401_, v_a_3402_, v_a_3403_);
if (lean_obj_tag(v___x_3425_) == 0)
{
lean_object* v_a_3426_; 
v_a_3426_ = lean_ctor_get(v___x_3425_, 0);
lean_inc(v_a_3426_);
lean_dec_ref(v___x_3425_);
if (lean_obj_tag(v_a_3426_) == 1)
{
lean_object* v_val_3427_; lean_object* v___x_3428_; lean_object* v___x_3429_; lean_object* v___x_3430_; 
lean_dec(v_val_3423_);
v_val_3427_ = lean_ctor_get(v_a_3426_, 0);
lean_inc_n(v_val_3427_, 2);
lean_dec_ref(v_a_3426_);
v___x_3428_ = lean_unsigned_to_nat(0u);
v___x_3429_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3429_, 0, v_val_3427_);
lean_ctor_set_uint8(v___x_3429_, sizeof(void*)*1, v___x_3424_);
lean_inc_ref(v_e_3392_);
v___x_3430_ = l_Lean_Meta_Grind_Arith_CommRing_reify_x3f(v_e_3392_, v_ring_3410_, v___x_3428_, v___x_3429_, v_a_3394_, v_a_3395_, v_a_3396_, v_a_3397_, v_a_3398_, v_a_3399_, v_a_3400_, v_a_3401_, v_a_3402_, v_a_3403_);
if (lean_obj_tag(v___x_3430_) == 0)
{
lean_object* v_a_3431_; lean_object* v___x_3433_; uint8_t v_isShared_3434_; uint8_t v_isSharedCheck_3482_; 
v_a_3431_ = lean_ctor_get(v___x_3430_, 0);
v_isSharedCheck_3482_ = !lean_is_exclusive(v___x_3430_);
if (v_isSharedCheck_3482_ == 0)
{
v___x_3433_ = v___x_3430_;
v_isShared_3434_ = v_isSharedCheck_3482_;
goto v_resetjp_3432_;
}
else
{
lean_inc(v_a_3431_);
lean_dec(v___x_3430_);
v___x_3433_ = lean_box(0);
v_isShared_3434_ = v_isSharedCheck_3482_;
goto v_resetjp_3432_;
}
v_resetjp_3432_:
{
if (lean_obj_tag(v_a_3431_) == 1)
{
lean_object* v_options_3435_; lean_object* v_val_3436_; lean_object* v_inheritedTraceOptions_3437_; uint8_t v_hasTrace_3438_; lean_object* v___f_3439_; lean_object* v___y_3441_; lean_object* v___y_3442_; lean_object* v___y_3443_; lean_object* v___y_3444_; lean_object* v___y_3445_; lean_object* v___y_3446_; lean_object* v___y_3447_; lean_object* v___y_3448_; lean_object* v___y_3449_; lean_object* v___y_3450_; lean_object* v___y_3451_; 
lean_del_object(v___x_3433_);
v_options_3435_ = lean_ctor_get(v_a_3402_, 2);
v_val_3436_ = lean_ctor_get(v_a_3431_, 0);
lean_inc(v_val_3436_);
lean_dec_ref(v_a_3431_);
v_inheritedTraceOptions_3437_ = lean_ctor_get(v_a_3402_, 13);
v_hasTrace_3438_ = lean_ctor_get_uint8(v_options_3435_, sizeof(void*)*1);
lean_inc_ref(v_e_3392_);
v___f_3439_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_internalize___lam__0), 3, 2);
lean_closure_set(v___f_3439_, 0, v_e_3392_);
lean_closure_set(v___f_3439_, 1, v_val_3436_);
if (v_hasTrace_3438_ == 0)
{
lean_dec(v_val_3427_);
v___y_3441_ = v___x_3429_;
v___y_3442_ = v_a_3394_;
v___y_3443_ = v_a_3395_;
v___y_3444_ = v_a_3396_;
v___y_3445_ = v_a_3397_;
v___y_3446_ = v_a_3398_;
v___y_3447_ = v_a_3399_;
v___y_3448_ = v_a_3400_;
v___y_3449_ = v_a_3401_;
v___y_3450_ = v_a_3402_;
v___y_3451_ = v_a_3403_;
goto v___jp_3440_;
}
else
{
lean_object* v___x_3457_; lean_object* v___x_3458_; uint8_t v___x_3459_; 
v___x_3457_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__1));
v___x_3458_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__2, &l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__2_once, _init_l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__2);
v___x_3459_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3437_, v_options_3435_, v___x_3458_);
if (v___x_3459_ == 0)
{
lean_dec(v_val_3427_);
v___y_3441_ = v___x_3429_;
v___y_3442_ = v_a_3394_;
v___y_3443_ = v_a_3395_;
v___y_3444_ = v_a_3396_;
v___y_3445_ = v_a_3397_;
v___y_3446_ = v_a_3398_;
v___y_3447_ = v_a_3399_;
v___y_3448_ = v_a_3400_;
v___y_3449_ = v_a_3401_;
v___y_3450_ = v_a_3402_;
v___y_3451_ = v_a_3403_;
goto v___jp_3440_;
}
else
{
lean_object* v___x_3460_; 
v___x_3460_ = l_Lean_Meta_Grind_updateLastTag(v_a_3394_, v_a_3395_, v_a_3396_, v_a_3397_, v_a_3398_, v_a_3399_, v_a_3400_, v_a_3401_, v_a_3402_, v_a_3403_);
if (lean_obj_tag(v___x_3460_) == 0)
{
lean_object* v___x_3462_; uint8_t v_isShared_3463_; uint8_t v_isSharedCheck_3476_; 
v_isSharedCheck_3476_ = !lean_is_exclusive(v___x_3460_);
if (v_isSharedCheck_3476_ == 0)
{
lean_object* v_unused_3477_; 
v_unused_3477_ = lean_ctor_get(v___x_3460_, 0);
lean_dec(v_unused_3477_);
v___x_3462_ = v___x_3460_;
v_isShared_3463_ = v_isSharedCheck_3476_;
goto v_resetjp_3461_;
}
else
{
lean_dec(v___x_3460_);
v___x_3462_ = lean_box(0);
v_isShared_3463_ = v_isSharedCheck_3476_;
goto v_resetjp_3461_;
}
v_resetjp_3461_:
{
lean_object* v___x_3464_; lean_object* v___x_3465_; lean_object* v___x_3467_; 
v___x_3464_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__4, &l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__4_once, _init_l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__4);
v___x_3465_ = l_Nat_reprFast(v_val_3427_);
if (v_isShared_3463_ == 0)
{
lean_ctor_set_tag(v___x_3462_, 3);
lean_ctor_set(v___x_3462_, 0, v___x_3465_);
v___x_3467_ = v___x_3462_;
goto v_reusejp_3466_;
}
else
{
lean_object* v_reuseFailAlloc_3475_; 
v_reuseFailAlloc_3475_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3475_, 0, v___x_3465_);
v___x_3467_ = v_reuseFailAlloc_3475_;
goto v_reusejp_3466_;
}
v_reusejp_3466_:
{
lean_object* v___x_3468_; lean_object* v___x_3469_; lean_object* v___x_3470_; lean_object* v___x_3471_; lean_object* v___x_3472_; lean_object* v___x_3473_; lean_object* v___x_3474_; 
v___x_3468_ = l_Lean_MessageData_ofFormat(v___x_3467_);
v___x_3469_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3469_, 0, v___x_3464_);
lean_ctor_set(v___x_3469_, 1, v___x_3468_);
v___x_3470_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__6, &l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__6_once, _init_l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__6);
v___x_3471_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3471_, 0, v___x_3469_);
lean_ctor_set(v___x_3471_, 1, v___x_3470_);
lean_inc_ref(v_e_3392_);
v___x_3472_ = l_Lean_MessageData_ofExpr(v_e_3392_);
v___x_3473_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3473_, 0, v___x_3471_);
lean_ctor_set(v___x_3473_, 1, v___x_3472_);
v___x_3474_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg(v___x_3457_, v___x_3473_, v_a_3400_, v_a_3401_, v_a_3402_, v_a_3403_);
if (lean_obj_tag(v___x_3474_) == 0)
{
lean_dec_ref(v___x_3474_);
v___y_3441_ = v___x_3429_;
v___y_3442_ = v_a_3394_;
v___y_3443_ = v_a_3395_;
v___y_3444_ = v_a_3396_;
v___y_3445_ = v_a_3397_;
v___y_3446_ = v_a_3398_;
v___y_3447_ = v_a_3399_;
v___y_3448_ = v_a_3400_;
v___y_3449_ = v_a_3401_;
v___y_3450_ = v_a_3402_;
v___y_3451_ = v_a_3403_;
goto v___jp_3440_;
}
else
{
lean_dec_ref(v___f_3439_);
lean_dec_ref(v___x_3429_);
lean_dec_ref(v_e_3392_);
return v___x_3474_;
}
}
}
}
else
{
lean_dec_ref(v___f_3439_);
lean_dec_ref(v___x_3429_);
lean_dec(v_val_3427_);
lean_dec_ref(v_e_3392_);
return v___x_3460_;
}
}
}
v___jp_3440_:
{
lean_object* v___x_3452_; 
lean_inc_ref(v_e_3392_);
v___x_3452_ = l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg(v_e_3392_, v___y_3441_, v___y_3442_, v___y_3446_, v___y_3447_, v___y_3448_, v___y_3449_, v___y_3450_, v___y_3451_);
if (lean_obj_tag(v___x_3452_) == 0)
{
lean_object* v___x_3453_; lean_object* v___x_3454_; 
lean_dec_ref(v___x_3452_);
v___x_3453_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_3454_ = l_Lean_Meta_Grind_SolverExtension_markTerm___redArg(v___x_3453_, v_e_3392_, v___y_3442_, v___y_3443_, v___y_3444_, v___y_3445_, v___y_3446_, v___y_3447_, v___y_3448_, v___y_3449_, v___y_3450_, v___y_3451_);
if (lean_obj_tag(v___x_3454_) == 0)
{
lean_object* v___x_3455_; 
lean_dec_ref(v___x_3454_);
v___x_3455_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(v___f_3439_, v___y_3441_, v___y_3442_);
if (lean_obj_tag(v___x_3455_) == 0)
{
lean_object* v___x_3456_; 
lean_dec_ref(v___x_3455_);
v___x_3456_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars(v___y_3441_, v___y_3442_, v___y_3443_, v___y_3444_, v___y_3445_, v___y_3446_, v___y_3447_, v___y_3448_, v___y_3449_, v___y_3450_, v___y_3451_);
lean_dec_ref(v___y_3441_);
return v___x_3456_;
}
else
{
lean_dec_ref(v___y_3441_);
return v___x_3455_;
}
}
else
{
lean_dec_ref(v___y_3441_);
lean_dec_ref(v___f_3439_);
return v___x_3454_;
}
}
else
{
lean_dec_ref(v___y_3441_);
lean_dec_ref(v___f_3439_);
lean_dec_ref(v_e_3392_);
return v___x_3452_;
}
}
}
else
{
lean_object* v___x_3478_; lean_object* v___x_3480_; 
lean_dec(v_a_3431_);
lean_dec_ref(v___x_3429_);
lean_dec(v_val_3427_);
lean_dec_ref(v_e_3392_);
v___x_3478_ = lean_box(0);
if (v_isShared_3434_ == 0)
{
lean_ctor_set(v___x_3433_, 0, v___x_3478_);
v___x_3480_ = v___x_3433_;
goto v_reusejp_3479_;
}
else
{
lean_object* v_reuseFailAlloc_3481_; 
v_reuseFailAlloc_3481_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3481_, 0, v___x_3478_);
v___x_3480_ = v_reuseFailAlloc_3481_;
goto v_reusejp_3479_;
}
v_reusejp_3479_:
{
return v___x_3480_;
}
}
}
}
else
{
lean_object* v_a_3483_; lean_object* v___x_3485_; uint8_t v_isShared_3486_; uint8_t v_isSharedCheck_3490_; 
lean_dec_ref(v___x_3429_);
lean_dec(v_val_3427_);
lean_dec_ref(v_e_3392_);
v_a_3483_ = lean_ctor_get(v___x_3430_, 0);
v_isSharedCheck_3490_ = !lean_is_exclusive(v___x_3430_);
if (v_isSharedCheck_3490_ == 0)
{
v___x_3485_ = v___x_3430_;
v_isShared_3486_ = v_isSharedCheck_3490_;
goto v_resetjp_3484_;
}
else
{
lean_inc(v_a_3483_);
lean_dec(v___x_3430_);
v___x_3485_ = lean_box(0);
v_isShared_3486_ = v_isSharedCheck_3490_;
goto v_resetjp_3484_;
}
v_resetjp_3484_:
{
lean_object* v___x_3488_; 
if (v_isShared_3486_ == 0)
{
v___x_3488_ = v___x_3485_;
goto v_reusejp_3487_;
}
else
{
lean_object* v_reuseFailAlloc_3489_; 
v_reuseFailAlloc_3489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3489_, 0, v_a_3483_);
v___x_3488_ = v_reuseFailAlloc_3489_;
goto v_reusejp_3487_;
}
v_reusejp_3487_:
{
return v___x_3488_;
}
}
}
}
else
{
lean_object* v___x_3491_; 
lean_dec(v_a_3426_);
lean_inc(v_val_3423_);
v___x_3491_ = l_Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f(v_val_3423_, v_a_3394_, v_a_3395_, v_a_3396_, v_a_3397_, v_a_3398_, v_a_3399_, v_a_3400_, v_a_3401_, v_a_3402_, v_a_3403_);
if (lean_obj_tag(v___x_3491_) == 0)
{
lean_object* v_a_3492_; 
v_a_3492_ = lean_ctor_get(v___x_3491_, 0);
lean_inc(v_a_3492_);
lean_dec_ref(v___x_3491_);
if (lean_obj_tag(v_a_3492_) == 1)
{
lean_object* v_val_3493_; lean_object* v___x_3494_; 
lean_dec(v_val_3423_);
v_val_3493_ = lean_ctor_get(v_a_3492_, 0);
lean_inc(v_val_3493_);
lean_dec_ref(v_a_3492_);
lean_inc_ref(v_e_3392_);
v___x_3494_ = l_Lean_Meta_Grind_Arith_CommRing_sreify_x3f(v_e_3392_, v_val_3493_, v_a_3394_, v_a_3395_, v_a_3396_, v_a_3397_, v_a_3398_, v_a_3399_, v_a_3400_, v_a_3401_, v_a_3402_, v_a_3403_);
if (lean_obj_tag(v___x_3494_) == 0)
{
lean_object* v_a_3495_; lean_object* v___x_3497_; uint8_t v_isShared_3498_; uint8_t v_isSharedCheck_3545_; 
v_a_3495_ = lean_ctor_get(v___x_3494_, 0);
v_isSharedCheck_3545_ = !lean_is_exclusive(v___x_3494_);
if (v_isSharedCheck_3545_ == 0)
{
v___x_3497_ = v___x_3494_;
v_isShared_3498_ = v_isSharedCheck_3545_;
goto v_resetjp_3496_;
}
else
{
lean_inc(v_a_3495_);
lean_dec(v___x_3494_);
v___x_3497_ = lean_box(0);
v_isShared_3498_ = v_isSharedCheck_3545_;
goto v_resetjp_3496_;
}
v_resetjp_3496_:
{
if (lean_obj_tag(v_a_3495_) == 1)
{
lean_object* v_val_3499_; lean_object* v___y_3501_; lean_object* v___y_3502_; lean_object* v___y_3503_; lean_object* v___y_3504_; lean_object* v___y_3505_; lean_object* v___y_3506_; lean_object* v___y_3507_; lean_object* v___y_3508_; lean_object* v___y_3509_; lean_object* v___y_3510_; lean_object* v___y_3511_; lean_object* v_options_3517_; uint8_t v_hasTrace_3518_; 
lean_del_object(v___x_3497_);
v_val_3499_ = lean_ctor_get(v_a_3495_, 0);
lean_inc(v_val_3499_);
lean_dec_ref(v_a_3495_);
v_options_3517_ = lean_ctor_get(v_a_3402_, 2);
v_hasTrace_3518_ = lean_ctor_get_uint8(v_options_3517_, sizeof(void*)*1);
if (v_hasTrace_3518_ == 0)
{
v___y_3501_ = v_val_3493_;
v___y_3502_ = v_a_3394_;
v___y_3503_ = v_a_3395_;
v___y_3504_ = v_a_3396_;
v___y_3505_ = v_a_3397_;
v___y_3506_ = v_a_3398_;
v___y_3507_ = v_a_3399_;
v___y_3508_ = v_a_3400_;
v___y_3509_ = v_a_3401_;
v___y_3510_ = v_a_3402_;
v___y_3511_ = v_a_3403_;
goto v___jp_3500_;
}
else
{
lean_object* v_inheritedTraceOptions_3519_; lean_object* v___x_3520_; lean_object* v___x_3521_; uint8_t v___x_3522_; 
v_inheritedTraceOptions_3519_ = lean_ctor_get(v_a_3402_, 13);
v___x_3520_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__1));
v___x_3521_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__2, &l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__2_once, _init_l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__2);
v___x_3522_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3519_, v_options_3517_, v___x_3521_);
if (v___x_3522_ == 0)
{
v___y_3501_ = v_val_3493_;
v___y_3502_ = v_a_3394_;
v___y_3503_ = v_a_3395_;
v___y_3504_ = v_a_3396_;
v___y_3505_ = v_a_3397_;
v___y_3506_ = v_a_3398_;
v___y_3507_ = v_a_3399_;
v___y_3508_ = v_a_3400_;
v___y_3509_ = v_a_3401_;
v___y_3510_ = v_a_3402_;
v___y_3511_ = v_a_3403_;
goto v___jp_3500_;
}
else
{
lean_object* v___x_3523_; 
v___x_3523_ = l_Lean_Meta_Grind_updateLastTag(v_a_3394_, v_a_3395_, v_a_3396_, v_a_3397_, v_a_3398_, v_a_3399_, v_a_3400_, v_a_3401_, v_a_3402_, v_a_3403_);
if (lean_obj_tag(v___x_3523_) == 0)
{
lean_object* v___x_3525_; uint8_t v_isShared_3526_; uint8_t v_isSharedCheck_3539_; 
v_isSharedCheck_3539_ = !lean_is_exclusive(v___x_3523_);
if (v_isSharedCheck_3539_ == 0)
{
lean_object* v_unused_3540_; 
v_unused_3540_ = lean_ctor_get(v___x_3523_, 0);
lean_dec(v_unused_3540_);
v___x_3525_ = v___x_3523_;
v_isShared_3526_ = v_isSharedCheck_3539_;
goto v_resetjp_3524_;
}
else
{
lean_dec(v___x_3523_);
v___x_3525_ = lean_box(0);
v_isShared_3526_ = v_isSharedCheck_3539_;
goto v_resetjp_3524_;
}
v_resetjp_3524_:
{
lean_object* v___x_3527_; lean_object* v___x_3528_; lean_object* v___x_3530_; 
v___x_3527_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__8, &l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__8_once, _init_l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__8);
lean_inc(v_val_3493_);
v___x_3528_ = l_Nat_reprFast(v_val_3493_);
if (v_isShared_3526_ == 0)
{
lean_ctor_set_tag(v___x_3525_, 3);
lean_ctor_set(v___x_3525_, 0, v___x_3528_);
v___x_3530_ = v___x_3525_;
goto v_reusejp_3529_;
}
else
{
lean_object* v_reuseFailAlloc_3538_; 
v_reuseFailAlloc_3538_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3538_, 0, v___x_3528_);
v___x_3530_ = v_reuseFailAlloc_3538_;
goto v_reusejp_3529_;
}
v_reusejp_3529_:
{
lean_object* v___x_3531_; lean_object* v___x_3532_; lean_object* v___x_3533_; lean_object* v___x_3534_; lean_object* v___x_3535_; lean_object* v___x_3536_; lean_object* v___x_3537_; 
v___x_3531_ = l_Lean_MessageData_ofFormat(v___x_3530_);
v___x_3532_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3532_, 0, v___x_3527_);
lean_ctor_set(v___x_3532_, 1, v___x_3531_);
v___x_3533_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__6, &l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__6_once, _init_l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__6);
v___x_3534_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3534_, 0, v___x_3532_);
lean_ctor_set(v___x_3534_, 1, v___x_3533_);
lean_inc_ref(v_e_3392_);
v___x_3535_ = l_Lean_MessageData_ofExpr(v_e_3392_);
v___x_3536_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3536_, 0, v___x_3534_);
lean_ctor_set(v___x_3536_, 1, v___x_3535_);
v___x_3537_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__1___redArg(v___x_3520_, v___x_3536_, v_a_3400_, v_a_3401_, v_a_3402_, v_a_3403_);
if (lean_obj_tag(v___x_3537_) == 0)
{
lean_dec_ref(v___x_3537_);
v___y_3501_ = v_val_3493_;
v___y_3502_ = v_a_3394_;
v___y_3503_ = v_a_3395_;
v___y_3504_ = v_a_3396_;
v___y_3505_ = v_a_3397_;
v___y_3506_ = v_a_3398_;
v___y_3507_ = v_a_3399_;
v___y_3508_ = v_a_3400_;
v___y_3509_ = v_a_3401_;
v___y_3510_ = v_a_3402_;
v___y_3511_ = v_a_3403_;
goto v___jp_3500_;
}
else
{
lean_dec(v_val_3499_);
lean_dec(v_val_3493_);
lean_dec_ref(v_e_3392_);
return v___x_3537_;
}
}
}
}
else
{
lean_dec(v_val_3499_);
lean_dec(v_val_3493_);
lean_dec_ref(v_e_3392_);
return v___x_3523_;
}
}
}
v___jp_3500_:
{
lean_object* v___x_3512_; 
lean_inc_ref(v_e_3392_);
v___x_3512_ = l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg(v_e_3392_, v___y_3501_, v___y_3502_, v___y_3506_, v___y_3507_, v___y_3508_, v___y_3509_, v___y_3510_, v___y_3511_);
if (lean_obj_tag(v___x_3512_) == 0)
{
lean_object* v___x_3513_; lean_object* v___x_3514_; 
lean_dec_ref(v___x_3512_);
v___x_3513_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
lean_inc_ref(v_e_3392_);
v___x_3514_ = l_Lean_Meta_Grind_SolverExtension_markTerm___redArg(v___x_3513_, v_e_3392_, v___y_3502_, v___y_3503_, v___y_3504_, v___y_3505_, v___y_3506_, v___y_3507_, v___y_3508_, v___y_3509_, v___y_3510_, v___y_3511_);
if (lean_obj_tag(v___x_3514_) == 0)
{
lean_object* v___f_3515_; lean_object* v___x_3516_; 
lean_dec_ref(v___x_3514_);
v___f_3515_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_internalize___lam__1___boxed), 4, 3);
lean_closure_set(v___f_3515_, 0, v___y_3501_);
lean_closure_set(v___f_3515_, 1, v_e_3392_);
lean_closure_set(v___f_3515_, 2, v_val_3499_);
v___x_3516_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_3513_, v___f_3515_, v___y_3502_);
return v___x_3516_;
}
else
{
lean_dec(v___y_3501_);
lean_dec(v_val_3499_);
lean_dec_ref(v_e_3392_);
return v___x_3514_;
}
}
else
{
lean_dec(v___y_3501_);
lean_dec(v_val_3499_);
lean_dec_ref(v_e_3392_);
return v___x_3512_;
}
}
}
else
{
lean_object* v___x_3541_; lean_object* v___x_3543_; 
lean_dec(v_a_3495_);
lean_dec(v_val_3493_);
lean_dec_ref(v_e_3392_);
v___x_3541_ = lean_box(0);
if (v_isShared_3498_ == 0)
{
lean_ctor_set(v___x_3497_, 0, v___x_3541_);
v___x_3543_ = v___x_3497_;
goto v_reusejp_3542_;
}
else
{
lean_object* v_reuseFailAlloc_3544_; 
v_reuseFailAlloc_3544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3544_, 0, v___x_3541_);
v___x_3543_ = v_reuseFailAlloc_3544_;
goto v_reusejp_3542_;
}
v_reusejp_3542_:
{
return v___x_3543_;
}
}
}
}
else
{
lean_object* v_a_3546_; lean_object* v___x_3548_; uint8_t v_isShared_3549_; uint8_t v_isSharedCheck_3553_; 
lean_dec(v_val_3493_);
lean_dec_ref(v_e_3392_);
v_a_3546_ = lean_ctor_get(v___x_3494_, 0);
v_isSharedCheck_3553_ = !lean_is_exclusive(v___x_3494_);
if (v_isSharedCheck_3553_ == 0)
{
v___x_3548_ = v___x_3494_;
v_isShared_3549_ = v_isSharedCheck_3553_;
goto v_resetjp_3547_;
}
else
{
lean_inc(v_a_3546_);
lean_dec(v___x_3494_);
v___x_3548_ = lean_box(0);
v_isShared_3549_ = v_isSharedCheck_3553_;
goto v_resetjp_3547_;
}
v_resetjp_3547_:
{
lean_object* v___x_3551_; 
if (v_isShared_3549_ == 0)
{
v___x_3551_ = v___x_3548_;
goto v_reusejp_3550_;
}
else
{
lean_object* v_reuseFailAlloc_3552_; 
v_reuseFailAlloc_3552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3552_, 0, v_a_3546_);
v___x_3551_ = v_reuseFailAlloc_3552_;
goto v_reusejp_3550_;
}
v_reusejp_3550_:
{
return v___x_3551_;
}
}
}
}
else
{
lean_object* v___x_3554_; 
lean_dec(v_a_3492_);
lean_inc(v_val_3423_);
v___x_3554_ = l_Lean_Meta_Grind_Arith_CommRing_getNonCommRingId_x3f(v_val_3423_, v_a_3394_, v_a_3395_, v_a_3396_, v_a_3397_, v_a_3398_, v_a_3399_, v_a_3400_, v_a_3401_, v_a_3402_, v_a_3403_);
if (lean_obj_tag(v___x_3554_) == 0)
{
lean_object* v_a_3555_; 
v_a_3555_ = lean_ctor_get(v___x_3554_, 0);
lean_inc(v_a_3555_);
lean_dec_ref(v___x_3554_);
if (lean_obj_tag(v_a_3555_) == 1)
{
lean_object* v_val_3556_; lean_object* v___x_3557_; lean_object* v___x_3558_; 
lean_dec(v_val_3423_);
v_val_3556_ = lean_ctor_get(v_a_3555_, 0);
lean_inc(v_val_3556_);
lean_dec_ref(v_a_3555_);
v___x_3557_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_e_3392_);
v___x_3558_ = l_Lean_Meta_Grind_Arith_CommRing_ncreify_x3f(v_e_3392_, v_ring_3410_, v___x_3557_, v_val_3556_, v_a_3394_, v_a_3395_, v_a_3396_, v_a_3397_, v_a_3398_, v_a_3399_, v_a_3400_, v_a_3401_, v_a_3402_, v_a_3403_);
if (lean_obj_tag(v___x_3558_) == 0)
{
lean_object* v_a_3559_; lean_object* v___x_3561_; uint8_t v_isShared_3562_; uint8_t v_isSharedCheck_3609_; 
v_a_3559_ = lean_ctor_get(v___x_3558_, 0);
v_isSharedCheck_3609_ = !lean_is_exclusive(v___x_3558_);
if (v_isSharedCheck_3609_ == 0)
{
v___x_3561_ = v___x_3558_;
v_isShared_3562_ = v_isSharedCheck_3609_;
goto v_resetjp_3560_;
}
else
{
lean_inc(v_a_3559_);
lean_dec(v___x_3558_);
v___x_3561_ = lean_box(0);
v_isShared_3562_ = v_isSharedCheck_3609_;
goto v_resetjp_3560_;
}
v_resetjp_3560_:
{
if (lean_obj_tag(v_a_3559_) == 1)
{
lean_object* v_options_3563_; lean_object* v_val_3564_; lean_object* v_inheritedTraceOptions_3565_; uint8_t v_hasTrace_3566_; lean_object* v___f_3567_; lean_object* v___y_3569_; lean_object* v___y_3570_; lean_object* v___y_3571_; lean_object* v___y_3572_; lean_object* v___y_3573_; lean_object* v___y_3574_; lean_object* v___y_3575_; lean_object* v___y_3576_; lean_object* v___y_3577_; lean_object* v___y_3578_; lean_object* v___y_3579_; 
lean_del_object(v___x_3561_);
v_options_3563_ = lean_ctor_get(v_a_3402_, 2);
v_val_3564_ = lean_ctor_get(v_a_3559_, 0);
lean_inc(v_val_3564_);
lean_dec_ref(v_a_3559_);
v_inheritedTraceOptions_3565_ = lean_ctor_get(v_a_3402_, 13);
v_hasTrace_3566_ = lean_ctor_get_uint8(v_options_3563_, sizeof(void*)*1);
lean_inc_ref(v_e_3392_);
v___f_3567_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_internalize___lam__2), 3, 2);
lean_closure_set(v___f_3567_, 0, v_e_3392_);
lean_closure_set(v___f_3567_, 1, v_val_3564_);
if (v_hasTrace_3566_ == 0)
{
v___y_3569_ = v_val_3556_;
v___y_3570_ = v_a_3394_;
v___y_3571_ = v_a_3395_;
v___y_3572_ = v_a_3396_;
v___y_3573_ = v_a_3397_;
v___y_3574_ = v_a_3398_;
v___y_3575_ = v_a_3399_;
v___y_3576_ = v_a_3400_;
v___y_3577_ = v_a_3401_;
v___y_3578_ = v_a_3402_;
v___y_3579_ = v_a_3403_;
goto v___jp_3568_;
}
else
{
lean_object* v___x_3584_; lean_object* v___x_3585_; uint8_t v___x_3586_; 
v___x_3584_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__1));
v___x_3585_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__2, &l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__2_once, _init_l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__2);
v___x_3586_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3565_, v_options_3563_, v___x_3585_);
if (v___x_3586_ == 0)
{
v___y_3569_ = v_val_3556_;
v___y_3570_ = v_a_3394_;
v___y_3571_ = v_a_3395_;
v___y_3572_ = v_a_3396_;
v___y_3573_ = v_a_3397_;
v___y_3574_ = v_a_3398_;
v___y_3575_ = v_a_3399_;
v___y_3576_ = v_a_3400_;
v___y_3577_ = v_a_3401_;
v___y_3578_ = v_a_3402_;
v___y_3579_ = v_a_3403_;
goto v___jp_3568_;
}
else
{
lean_object* v___x_3587_; 
v___x_3587_ = l_Lean_Meta_Grind_updateLastTag(v_a_3394_, v_a_3395_, v_a_3396_, v_a_3397_, v_a_3398_, v_a_3399_, v_a_3400_, v_a_3401_, v_a_3402_, v_a_3403_);
if (lean_obj_tag(v___x_3587_) == 0)
{
lean_object* v___x_3589_; uint8_t v_isShared_3590_; uint8_t v_isSharedCheck_3603_; 
v_isSharedCheck_3603_ = !lean_is_exclusive(v___x_3587_);
if (v_isSharedCheck_3603_ == 0)
{
lean_object* v_unused_3604_; 
v_unused_3604_ = lean_ctor_get(v___x_3587_, 0);
lean_dec(v_unused_3604_);
v___x_3589_ = v___x_3587_;
v_isShared_3590_ = v_isSharedCheck_3603_;
goto v_resetjp_3588_;
}
else
{
lean_dec(v___x_3587_);
v___x_3589_ = lean_box(0);
v_isShared_3590_ = v_isSharedCheck_3603_;
goto v_resetjp_3588_;
}
v_resetjp_3588_:
{
lean_object* v___x_3591_; lean_object* v___x_3592_; lean_object* v___x_3594_; 
v___x_3591_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__10, &l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__10_once, _init_l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__10);
lean_inc(v_val_3556_);
v___x_3592_ = l_Nat_reprFast(v_val_3556_);
if (v_isShared_3590_ == 0)
{
lean_ctor_set_tag(v___x_3589_, 3);
lean_ctor_set(v___x_3589_, 0, v___x_3592_);
v___x_3594_ = v___x_3589_;
goto v_reusejp_3593_;
}
else
{
lean_object* v_reuseFailAlloc_3602_; 
v_reuseFailAlloc_3602_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3602_, 0, v___x_3592_);
v___x_3594_ = v_reuseFailAlloc_3602_;
goto v_reusejp_3593_;
}
v_reusejp_3593_:
{
lean_object* v___x_3595_; lean_object* v___x_3596_; lean_object* v___x_3597_; lean_object* v___x_3598_; lean_object* v___x_3599_; lean_object* v___x_3600_; lean_object* v___x_3601_; 
v___x_3595_ = l_Lean_MessageData_ofFormat(v___x_3594_);
v___x_3596_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3596_, 0, v___x_3591_);
lean_ctor_set(v___x_3596_, 1, v___x_3595_);
v___x_3597_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__6, &l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__6_once, _init_l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__6);
v___x_3598_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3598_, 0, v___x_3596_);
lean_ctor_set(v___x_3598_, 1, v___x_3597_);
lean_inc_ref(v_e_3392_);
v___x_3599_ = l_Lean_MessageData_ofExpr(v_e_3392_);
v___x_3600_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3600_, 0, v___x_3598_);
lean_ctor_set(v___x_3600_, 1, v___x_3599_);
v___x_3601_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__2___redArg(v___x_3584_, v___x_3600_, v_a_3400_, v_a_3401_, v_a_3402_, v_a_3403_);
if (lean_obj_tag(v___x_3601_) == 0)
{
lean_dec_ref(v___x_3601_);
v___y_3569_ = v_val_3556_;
v___y_3570_ = v_a_3394_;
v___y_3571_ = v_a_3395_;
v___y_3572_ = v_a_3396_;
v___y_3573_ = v_a_3397_;
v___y_3574_ = v_a_3398_;
v___y_3575_ = v_a_3399_;
v___y_3576_ = v_a_3400_;
v___y_3577_ = v_a_3401_;
v___y_3578_ = v_a_3402_;
v___y_3579_ = v_a_3403_;
goto v___jp_3568_;
}
else
{
lean_dec_ref(v___f_3567_);
lean_dec(v_val_3556_);
lean_dec_ref(v_e_3392_);
return v___x_3601_;
}
}
}
}
else
{
lean_dec_ref(v___f_3567_);
lean_dec(v_val_3556_);
lean_dec_ref(v_e_3392_);
return v___x_3587_;
}
}
}
v___jp_3568_:
{
lean_object* v___x_3580_; 
lean_inc_ref(v_e_3392_);
v___x_3580_ = l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId___redArg(v_e_3392_, v___y_3569_, v___y_3570_, v___y_3574_, v___y_3575_, v___y_3576_, v___y_3577_, v___y_3578_, v___y_3579_);
if (lean_obj_tag(v___x_3580_) == 0)
{
lean_object* v___x_3581_; lean_object* v___x_3582_; 
lean_dec_ref(v___x_3580_);
v___x_3581_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_3582_ = l_Lean_Meta_Grind_SolverExtension_markTerm___redArg(v___x_3581_, v_e_3392_, v___y_3570_, v___y_3571_, v___y_3572_, v___y_3573_, v___y_3574_, v___y_3575_, v___y_3576_, v___y_3577_, v___y_3578_, v___y_3579_);
if (lean_obj_tag(v___x_3582_) == 0)
{
lean_object* v___x_3583_; 
lean_dec_ref(v___x_3582_);
v___x_3583_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_modifyRing___redArg(v___f_3567_, v___y_3569_, v___y_3570_);
lean_dec(v___y_3569_);
return v___x_3583_;
}
else
{
lean_dec(v___y_3569_);
lean_dec_ref(v___f_3567_);
return v___x_3582_;
}
}
else
{
lean_dec(v___y_3569_);
lean_dec_ref(v___f_3567_);
lean_dec_ref(v_e_3392_);
return v___x_3580_;
}
}
}
else
{
lean_object* v___x_3605_; lean_object* v___x_3607_; 
lean_dec(v_a_3559_);
lean_dec(v_val_3556_);
lean_dec_ref(v_e_3392_);
v___x_3605_ = lean_box(0);
if (v_isShared_3562_ == 0)
{
lean_ctor_set(v___x_3561_, 0, v___x_3605_);
v___x_3607_ = v___x_3561_;
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
}
else
{
lean_object* v_a_3610_; lean_object* v___x_3612_; uint8_t v_isShared_3613_; uint8_t v_isSharedCheck_3617_; 
lean_dec(v_val_3556_);
lean_dec_ref(v_e_3392_);
v_a_3610_ = lean_ctor_get(v___x_3558_, 0);
v_isSharedCheck_3617_ = !lean_is_exclusive(v___x_3558_);
if (v_isSharedCheck_3617_ == 0)
{
v___x_3612_ = v___x_3558_;
v_isShared_3613_ = v_isSharedCheck_3617_;
goto v_resetjp_3611_;
}
else
{
lean_inc(v_a_3610_);
lean_dec(v___x_3558_);
v___x_3612_ = lean_box(0);
v_isShared_3613_ = v_isSharedCheck_3617_;
goto v_resetjp_3611_;
}
v_resetjp_3611_:
{
lean_object* v___x_3615_; 
if (v_isShared_3613_ == 0)
{
v___x_3615_ = v___x_3612_;
goto v_reusejp_3614_;
}
else
{
lean_object* v_reuseFailAlloc_3616_; 
v_reuseFailAlloc_3616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3616_, 0, v_a_3610_);
v___x_3615_ = v_reuseFailAlloc_3616_;
goto v_reusejp_3614_;
}
v_reusejp_3614_:
{
return v___x_3615_;
}
}
}
}
else
{
lean_object* v___x_3618_; 
lean_dec(v_a_3555_);
v___x_3618_ = l_Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f___redArg(v_val_3423_, v_a_3394_, v_a_3400_, v_a_3401_, v_a_3402_, v_a_3403_);
if (lean_obj_tag(v___x_3618_) == 0)
{
lean_object* v_a_3619_; lean_object* v___x_3621_; uint8_t v_isShared_3622_; uint8_t v_isSharedCheck_3688_; 
v_a_3619_ = lean_ctor_get(v___x_3618_, 0);
v_isSharedCheck_3688_ = !lean_is_exclusive(v___x_3618_);
if (v_isSharedCheck_3688_ == 0)
{
v___x_3621_ = v___x_3618_;
v_isShared_3622_ = v_isSharedCheck_3688_;
goto v_resetjp_3620_;
}
else
{
lean_inc(v_a_3619_);
lean_dec(v___x_3618_);
v___x_3621_ = lean_box(0);
v_isShared_3622_ = v_isSharedCheck_3688_;
goto v_resetjp_3620_;
}
v_resetjp_3620_:
{
if (lean_obj_tag(v_a_3619_) == 1)
{
lean_object* v_val_3623_; lean_object* v___x_3624_; 
lean_del_object(v___x_3621_);
v_val_3623_ = lean_ctor_get(v_a_3619_, 0);
lean_inc(v_val_3623_);
lean_dec_ref(v_a_3619_);
lean_inc_ref(v_e_3392_);
v___x_3624_ = l_Lean_Meta_Grind_Arith_CommRing_ncsreify_x3f(v_e_3392_, v_val_3623_, v_a_3394_, v_a_3395_, v_a_3396_, v_a_3397_, v_a_3398_, v_a_3399_, v_a_3400_, v_a_3401_, v_a_3402_, v_a_3403_);
if (lean_obj_tag(v___x_3624_) == 0)
{
lean_object* v_a_3625_; lean_object* v___x_3627_; uint8_t v_isShared_3628_; uint8_t v_isSharedCheck_3675_; 
v_a_3625_ = lean_ctor_get(v___x_3624_, 0);
v_isSharedCheck_3675_ = !lean_is_exclusive(v___x_3624_);
if (v_isSharedCheck_3675_ == 0)
{
v___x_3627_ = v___x_3624_;
v_isShared_3628_ = v_isSharedCheck_3675_;
goto v_resetjp_3626_;
}
else
{
lean_inc(v_a_3625_);
lean_dec(v___x_3624_);
v___x_3627_ = lean_box(0);
v_isShared_3628_ = v_isSharedCheck_3675_;
goto v_resetjp_3626_;
}
v_resetjp_3626_:
{
if (lean_obj_tag(v_a_3625_) == 1)
{
lean_object* v_options_3629_; lean_object* v_val_3630_; lean_object* v_inheritedTraceOptions_3631_; uint8_t v_hasTrace_3632_; lean_object* v___f_3633_; lean_object* v___y_3635_; lean_object* v___y_3636_; lean_object* v___y_3637_; lean_object* v___y_3638_; lean_object* v___y_3639_; lean_object* v___y_3640_; lean_object* v___y_3641_; lean_object* v___y_3642_; lean_object* v___y_3643_; lean_object* v___y_3644_; lean_object* v___y_3645_; 
lean_del_object(v___x_3627_);
v_options_3629_ = lean_ctor_get(v_a_3402_, 2);
v_val_3630_ = lean_ctor_get(v_a_3625_, 0);
lean_inc(v_val_3630_);
lean_dec_ref(v_a_3625_);
v_inheritedTraceOptions_3631_ = lean_ctor_get(v_a_3402_, 13);
v_hasTrace_3632_ = lean_ctor_get_uint8(v_options_3629_, sizeof(void*)*1);
lean_inc_ref(v_e_3392_);
v___f_3633_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_internalize___lam__3), 3, 2);
lean_closure_set(v___f_3633_, 0, v_e_3392_);
lean_closure_set(v___f_3633_, 1, v_val_3630_);
if (v_hasTrace_3632_ == 0)
{
v___y_3635_ = v_val_3623_;
v___y_3636_ = v_a_3394_;
v___y_3637_ = v_a_3395_;
v___y_3638_ = v_a_3396_;
v___y_3639_ = v_a_3397_;
v___y_3640_ = v_a_3398_;
v___y_3641_ = v_a_3399_;
v___y_3642_ = v_a_3400_;
v___y_3643_ = v_a_3401_;
v___y_3644_ = v_a_3402_;
v___y_3645_ = v_a_3403_;
goto v___jp_3634_;
}
else
{
lean_object* v___x_3650_; lean_object* v___x_3651_; uint8_t v___x_3652_; 
v___x_3650_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__1));
v___x_3651_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__2, &l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__2_once, _init_l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__2);
v___x_3652_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3631_, v_options_3629_, v___x_3651_);
if (v___x_3652_ == 0)
{
v___y_3635_ = v_val_3623_;
v___y_3636_ = v_a_3394_;
v___y_3637_ = v_a_3395_;
v___y_3638_ = v_a_3396_;
v___y_3639_ = v_a_3397_;
v___y_3640_ = v_a_3398_;
v___y_3641_ = v_a_3399_;
v___y_3642_ = v_a_3400_;
v___y_3643_ = v_a_3401_;
v___y_3644_ = v_a_3402_;
v___y_3645_ = v_a_3403_;
goto v___jp_3634_;
}
else
{
lean_object* v___x_3653_; 
v___x_3653_ = l_Lean_Meta_Grind_updateLastTag(v_a_3394_, v_a_3395_, v_a_3396_, v_a_3397_, v_a_3398_, v_a_3399_, v_a_3400_, v_a_3401_, v_a_3402_, v_a_3403_);
if (lean_obj_tag(v___x_3653_) == 0)
{
lean_object* v___x_3655_; uint8_t v_isShared_3656_; uint8_t v_isSharedCheck_3669_; 
v_isSharedCheck_3669_ = !lean_is_exclusive(v___x_3653_);
if (v_isSharedCheck_3669_ == 0)
{
lean_object* v_unused_3670_; 
v_unused_3670_ = lean_ctor_get(v___x_3653_, 0);
lean_dec(v_unused_3670_);
v___x_3655_ = v___x_3653_;
v_isShared_3656_ = v_isSharedCheck_3669_;
goto v_resetjp_3654_;
}
else
{
lean_dec(v___x_3653_);
v___x_3655_ = lean_box(0);
v_isShared_3656_ = v_isSharedCheck_3669_;
goto v_resetjp_3654_;
}
v_resetjp_3654_:
{
lean_object* v___x_3657_; lean_object* v___x_3658_; lean_object* v___x_3660_; 
v___x_3657_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__12, &l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__12_once, _init_l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__12);
lean_inc(v_val_3623_);
v___x_3658_ = l_Nat_reprFast(v_val_3623_);
if (v_isShared_3656_ == 0)
{
lean_ctor_set_tag(v___x_3655_, 3);
lean_ctor_set(v___x_3655_, 0, v___x_3658_);
v___x_3660_ = v___x_3655_;
goto v_reusejp_3659_;
}
else
{
lean_object* v_reuseFailAlloc_3668_; 
v_reuseFailAlloc_3668_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3668_, 0, v___x_3658_);
v___x_3660_ = v_reuseFailAlloc_3668_;
goto v_reusejp_3659_;
}
v_reusejp_3659_:
{
lean_object* v___x_3661_; lean_object* v___x_3662_; lean_object* v___x_3663_; lean_object* v___x_3664_; lean_object* v___x_3665_; lean_object* v___x_3666_; lean_object* v___x_3667_; 
v___x_3661_ = l_Lean_MessageData_ofFormat(v___x_3660_);
v___x_3662_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3662_, 0, v___x_3657_);
lean_ctor_set(v___x_3662_, 1, v___x_3661_);
v___x_3663_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__6, &l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__6_once, _init_l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__6);
v___x_3664_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3664_, 0, v___x_3662_);
lean_ctor_set(v___x_3664_, 1, v___x_3663_);
lean_inc_ref(v_e_3392_);
v___x_3665_ = l_Lean_MessageData_ofExpr(v_e_3392_);
v___x_3666_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3666_, 0, v___x_3664_);
lean_ctor_set(v___x_3666_, 1, v___x_3665_);
v___x_3667_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__3___redArg(v___x_3650_, v___x_3666_, v_a_3400_, v_a_3401_, v_a_3402_, v_a_3403_);
if (lean_obj_tag(v___x_3667_) == 0)
{
lean_dec_ref(v___x_3667_);
v___y_3635_ = v_val_3623_;
v___y_3636_ = v_a_3394_;
v___y_3637_ = v_a_3395_;
v___y_3638_ = v_a_3396_;
v___y_3639_ = v_a_3397_;
v___y_3640_ = v_a_3398_;
v___y_3641_ = v_a_3399_;
v___y_3642_ = v_a_3400_;
v___y_3643_ = v_a_3401_;
v___y_3644_ = v_a_3402_;
v___y_3645_ = v_a_3403_;
goto v___jp_3634_;
}
else
{
lean_dec_ref(v___f_3633_);
lean_dec(v_val_3623_);
lean_dec_ref(v_e_3392_);
return v___x_3667_;
}
}
}
}
else
{
lean_dec_ref(v___f_3633_);
lean_dec(v_val_3623_);
lean_dec_ref(v_e_3392_);
return v___x_3653_;
}
}
}
v___jp_3634_:
{
lean_object* v___x_3646_; 
lean_inc_ref(v_e_3392_);
v___x_3646_ = l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId___redArg(v_e_3392_, v___y_3635_, v___y_3636_, v___y_3640_, v___y_3641_, v___y_3642_, v___y_3643_, v___y_3644_, v___y_3645_);
if (lean_obj_tag(v___x_3646_) == 0)
{
lean_object* v___x_3647_; lean_object* v___x_3648_; 
lean_dec_ref(v___x_3646_);
v___x_3647_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_3648_ = l_Lean_Meta_Grind_SolverExtension_markTerm___redArg(v___x_3647_, v_e_3392_, v___y_3636_, v___y_3637_, v___y_3638_, v___y_3639_, v___y_3640_, v___y_3641_, v___y_3642_, v___y_3643_, v___y_3644_, v___y_3645_);
if (lean_obj_tag(v___x_3648_) == 0)
{
lean_object* v___x_3649_; 
lean_dec_ref(v___x_3648_);
v___x_3649_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_modifySemiring___redArg(v___f_3633_, v___y_3635_, v___y_3636_);
lean_dec(v___y_3635_);
return v___x_3649_;
}
else
{
lean_dec(v___y_3635_);
lean_dec_ref(v___f_3633_);
return v___x_3648_;
}
}
else
{
lean_dec(v___y_3635_);
lean_dec_ref(v___f_3633_);
lean_dec_ref(v_e_3392_);
return v___x_3646_;
}
}
}
else
{
lean_object* v___x_3671_; lean_object* v___x_3673_; 
lean_dec(v_a_3625_);
lean_dec(v_val_3623_);
lean_dec_ref(v_e_3392_);
v___x_3671_ = lean_box(0);
if (v_isShared_3628_ == 0)
{
lean_ctor_set(v___x_3627_, 0, v___x_3671_);
v___x_3673_ = v___x_3627_;
goto v_reusejp_3672_;
}
else
{
lean_object* v_reuseFailAlloc_3674_; 
v_reuseFailAlloc_3674_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3674_, 0, v___x_3671_);
v___x_3673_ = v_reuseFailAlloc_3674_;
goto v_reusejp_3672_;
}
v_reusejp_3672_:
{
return v___x_3673_;
}
}
}
}
else
{
lean_object* v_a_3676_; lean_object* v___x_3678_; uint8_t v_isShared_3679_; uint8_t v_isSharedCheck_3683_; 
lean_dec(v_val_3623_);
lean_dec_ref(v_e_3392_);
v_a_3676_ = lean_ctor_get(v___x_3624_, 0);
v_isSharedCheck_3683_ = !lean_is_exclusive(v___x_3624_);
if (v_isSharedCheck_3683_ == 0)
{
v___x_3678_ = v___x_3624_;
v_isShared_3679_ = v_isSharedCheck_3683_;
goto v_resetjp_3677_;
}
else
{
lean_inc(v_a_3676_);
lean_dec(v___x_3624_);
v___x_3678_ = lean_box(0);
v_isShared_3679_ = v_isSharedCheck_3683_;
goto v_resetjp_3677_;
}
v_resetjp_3677_:
{
lean_object* v___x_3681_; 
if (v_isShared_3679_ == 0)
{
v___x_3681_ = v___x_3678_;
goto v_reusejp_3680_;
}
else
{
lean_object* v_reuseFailAlloc_3682_; 
v_reuseFailAlloc_3682_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3682_, 0, v_a_3676_);
v___x_3681_ = v_reuseFailAlloc_3682_;
goto v_reusejp_3680_;
}
v_reusejp_3680_:
{
return v___x_3681_;
}
}
}
}
else
{
lean_object* v___x_3684_; lean_object* v___x_3686_; 
lean_dec(v_a_3619_);
lean_dec_ref(v_e_3392_);
v___x_3684_ = lean_box(0);
if (v_isShared_3622_ == 0)
{
lean_ctor_set(v___x_3621_, 0, v___x_3684_);
v___x_3686_ = v___x_3621_;
goto v_reusejp_3685_;
}
else
{
lean_object* v_reuseFailAlloc_3687_; 
v_reuseFailAlloc_3687_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3687_, 0, v___x_3684_);
v___x_3686_ = v_reuseFailAlloc_3687_;
goto v_reusejp_3685_;
}
v_reusejp_3685_:
{
return v___x_3686_;
}
}
}
}
else
{
lean_object* v_a_3689_; lean_object* v___x_3691_; uint8_t v_isShared_3692_; uint8_t v_isSharedCheck_3696_; 
lean_dec_ref(v_e_3392_);
v_a_3689_ = lean_ctor_get(v___x_3618_, 0);
v_isSharedCheck_3696_ = !lean_is_exclusive(v___x_3618_);
if (v_isSharedCheck_3696_ == 0)
{
v___x_3691_ = v___x_3618_;
v_isShared_3692_ = v_isSharedCheck_3696_;
goto v_resetjp_3690_;
}
else
{
lean_inc(v_a_3689_);
lean_dec(v___x_3618_);
v___x_3691_ = lean_box(0);
v_isShared_3692_ = v_isSharedCheck_3696_;
goto v_resetjp_3690_;
}
v_resetjp_3690_:
{
lean_object* v___x_3694_; 
if (v_isShared_3692_ == 0)
{
v___x_3694_ = v___x_3691_;
goto v_reusejp_3693_;
}
else
{
lean_object* v_reuseFailAlloc_3695_; 
v_reuseFailAlloc_3695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3695_, 0, v_a_3689_);
v___x_3694_ = v_reuseFailAlloc_3695_;
goto v_reusejp_3693_;
}
v_reusejp_3693_:
{
return v___x_3694_;
}
}
}
}
}
else
{
lean_object* v_a_3697_; lean_object* v___x_3699_; uint8_t v_isShared_3700_; uint8_t v_isSharedCheck_3704_; 
lean_dec(v_val_3423_);
lean_dec_ref(v_e_3392_);
v_a_3697_ = lean_ctor_get(v___x_3554_, 0);
v_isSharedCheck_3704_ = !lean_is_exclusive(v___x_3554_);
if (v_isSharedCheck_3704_ == 0)
{
v___x_3699_ = v___x_3554_;
v_isShared_3700_ = v_isSharedCheck_3704_;
goto v_resetjp_3698_;
}
else
{
lean_inc(v_a_3697_);
lean_dec(v___x_3554_);
v___x_3699_ = lean_box(0);
v_isShared_3700_ = v_isSharedCheck_3704_;
goto v_resetjp_3698_;
}
v_resetjp_3698_:
{
lean_object* v___x_3702_; 
if (v_isShared_3700_ == 0)
{
v___x_3702_ = v___x_3699_;
goto v_reusejp_3701_;
}
else
{
lean_object* v_reuseFailAlloc_3703_; 
v_reuseFailAlloc_3703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3703_, 0, v_a_3697_);
v___x_3702_ = v_reuseFailAlloc_3703_;
goto v_reusejp_3701_;
}
v_reusejp_3701_:
{
return v___x_3702_;
}
}
}
}
}
else
{
lean_object* v_a_3705_; lean_object* v___x_3707_; uint8_t v_isShared_3708_; uint8_t v_isSharedCheck_3712_; 
lean_dec(v_val_3423_);
lean_dec_ref(v_e_3392_);
v_a_3705_ = lean_ctor_get(v___x_3491_, 0);
v_isSharedCheck_3712_ = !lean_is_exclusive(v___x_3491_);
if (v_isSharedCheck_3712_ == 0)
{
v___x_3707_ = v___x_3491_;
v_isShared_3708_ = v_isSharedCheck_3712_;
goto v_resetjp_3706_;
}
else
{
lean_inc(v_a_3705_);
lean_dec(v___x_3491_);
v___x_3707_ = lean_box(0);
v_isShared_3708_ = v_isSharedCheck_3712_;
goto v_resetjp_3706_;
}
v_resetjp_3706_:
{
lean_object* v___x_3710_; 
if (v_isShared_3708_ == 0)
{
v___x_3710_ = v___x_3707_;
goto v_reusejp_3709_;
}
else
{
lean_object* v_reuseFailAlloc_3711_; 
v_reuseFailAlloc_3711_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3711_, 0, v_a_3705_);
v___x_3710_ = v_reuseFailAlloc_3711_;
goto v_reusejp_3709_;
}
v_reusejp_3709_:
{
return v___x_3710_;
}
}
}
}
}
else
{
lean_object* v_a_3713_; lean_object* v___x_3715_; uint8_t v_isShared_3716_; uint8_t v_isSharedCheck_3720_; 
lean_dec(v_val_3423_);
lean_dec_ref(v_e_3392_);
v_a_3713_ = lean_ctor_get(v___x_3425_, 0);
v_isSharedCheck_3720_ = !lean_is_exclusive(v___x_3425_);
if (v_isSharedCheck_3720_ == 0)
{
v___x_3715_ = v___x_3425_;
v_isShared_3716_ = v_isSharedCheck_3720_;
goto v_resetjp_3714_;
}
else
{
lean_inc(v_a_3713_);
lean_dec(v___x_3425_);
v___x_3715_ = lean_box(0);
v_isShared_3716_ = v_isSharedCheck_3720_;
goto v_resetjp_3714_;
}
v_resetjp_3714_:
{
lean_object* v___x_3718_; 
if (v_isShared_3716_ == 0)
{
v___x_3718_ = v___x_3715_;
goto v_reusejp_3717_;
}
else
{
lean_object* v_reuseFailAlloc_3719_; 
v_reuseFailAlloc_3719_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3719_, 0, v_a_3713_);
v___x_3718_ = v_reuseFailAlloc_3719_;
goto v_reusejp_3717_;
}
v_reusejp_3717_:
{
return v___x_3718_;
}
}
}
}
else
{
lean_object* v___x_3721_; lean_object* v___x_3723_; 
lean_dec(v_val_3423_);
lean_dec_ref(v_e_3392_);
v___x_3721_ = lean_box(0);
if (v_isShared_3420_ == 0)
{
lean_ctor_set(v___x_3419_, 0, v___x_3721_);
v___x_3723_ = v___x_3419_;
goto v_reusejp_3722_;
}
else
{
lean_object* v_reuseFailAlloc_3724_; 
v_reuseFailAlloc_3724_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3724_, 0, v___x_3721_);
v___x_3723_ = v_reuseFailAlloc_3724_;
goto v_reusejp_3722_;
}
v_reusejp_3722_:
{
return v___x_3723_;
}
}
}
else
{
lean_object* v___x_3725_; lean_object* v___x_3727_; 
lean_dec(v___x_3422_);
lean_dec(v_parent_x3f_3393_);
lean_dec_ref(v_e_3392_);
v___x_3725_ = lean_box(0);
if (v_isShared_3420_ == 0)
{
lean_ctor_set(v___x_3419_, 0, v___x_3725_);
v___x_3727_ = v___x_3419_;
goto v_reusejp_3726_;
}
else
{
lean_object* v_reuseFailAlloc_3728_; 
v_reuseFailAlloc_3728_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3728_, 0, v___x_3725_);
v___x_3727_ = v_reuseFailAlloc_3728_;
goto v_reusejp_3726_;
}
v_reusejp_3726_:
{
return v___x_3727_;
}
}
}
else
{
lean_object* v___x_3729_; lean_object* v___x_3731_; 
lean_dec(v_parent_x3f_3393_);
lean_dec_ref(v_e_3392_);
v___x_3729_ = lean_box(0);
if (v_isShared_3420_ == 0)
{
lean_ctor_set(v___x_3419_, 0, v___x_3729_);
v___x_3731_ = v___x_3419_;
goto v_reusejp_3730_;
}
else
{
lean_object* v_reuseFailAlloc_3732_; 
v_reuseFailAlloc_3732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3732_, 0, v___x_3729_);
v___x_3731_ = v_reuseFailAlloc_3732_;
goto v_reusejp_3730_;
}
v_reusejp_3730_:
{
return v___x_3731_;
}
}
}
}
else
{
lean_object* v_a_3734_; lean_object* v___x_3736_; uint8_t v_isShared_3737_; uint8_t v_isSharedCheck_3741_; 
lean_dec(v_parent_x3f_3393_);
lean_dec_ref(v_e_3392_);
v_a_3734_ = lean_ctor_get(v___x_3416_, 0);
v_isSharedCheck_3741_ = !lean_is_exclusive(v___x_3416_);
if (v_isSharedCheck_3741_ == 0)
{
v___x_3736_ = v___x_3416_;
v_isShared_3737_ = v_isSharedCheck_3741_;
goto v_resetjp_3735_;
}
else
{
lean_inc(v_a_3734_);
lean_dec(v___x_3416_);
v___x_3736_ = lean_box(0);
v_isShared_3737_ = v_isSharedCheck_3741_;
goto v_resetjp_3735_;
}
v_resetjp_3735_:
{
lean_object* v___x_3739_; 
if (v_isShared_3737_ == 0)
{
v___x_3739_ = v___x_3736_;
goto v_reusejp_3738_;
}
else
{
lean_object* v_reuseFailAlloc_3740_; 
v_reuseFailAlloc_3740_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3740_, 0, v_a_3734_);
v___x_3739_ = v_reuseFailAlloc_3740_;
goto v_reusejp_3738_;
}
v_reusejp_3738_:
{
return v___x_3739_;
}
}
}
}
else
{
lean_object* v___x_3742_; lean_object* v___x_3744_; 
lean_dec(v_parent_x3f_3393_);
lean_dec_ref(v_e_3392_);
v___x_3742_ = lean_box(0);
if (v_isShared_3409_ == 0)
{
lean_ctor_set(v___x_3408_, 0, v___x_3742_);
v___x_3744_ = v___x_3408_;
goto v_reusejp_3743_;
}
else
{
lean_object* v_reuseFailAlloc_3745_; 
v_reuseFailAlloc_3745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3745_, 0, v___x_3742_);
v___x_3744_ = v_reuseFailAlloc_3745_;
goto v_reusejp_3743_;
}
v_reusejp_3743_:
{
return v___x_3744_;
}
}
}
}
}
else
{
lean_object* v_a_3747_; lean_object* v___x_3749_; uint8_t v_isShared_3750_; uint8_t v_isSharedCheck_3754_; 
lean_dec(v_parent_x3f_3393_);
lean_dec_ref(v_e_3392_);
v_a_3747_ = lean_ctor_get(v___x_3405_, 0);
v_isSharedCheck_3754_ = !lean_is_exclusive(v___x_3405_);
if (v_isSharedCheck_3754_ == 0)
{
v___x_3749_ = v___x_3405_;
v_isShared_3750_ = v_isSharedCheck_3754_;
goto v_resetjp_3748_;
}
else
{
lean_inc(v_a_3747_);
lean_dec(v___x_3405_);
v___x_3749_ = lean_box(0);
v_isShared_3750_ = v_isSharedCheck_3754_;
goto v_resetjp_3748_;
}
v_resetjp_3748_:
{
lean_object* v___x_3752_; 
if (v_isShared_3750_ == 0)
{
v___x_3752_ = v___x_3749_;
goto v_reusejp_3751_;
}
else
{
lean_object* v_reuseFailAlloc_3753_; 
v_reuseFailAlloc_3753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3753_, 0, v_a_3747_);
v___x_3752_ = v_reuseFailAlloc_3753_;
goto v_reusejp_3751_;
}
v_reusejp_3751_:
{
return v___x_3752_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_internalize___boxed(lean_object* v_e_3755_, lean_object* v_parent_x3f_3756_, lean_object* v_a_3757_, lean_object* v_a_3758_, lean_object* v_a_3759_, lean_object* v_a_3760_, lean_object* v_a_3761_, lean_object* v_a_3762_, lean_object* v_a_3763_, lean_object* v_a_3764_, lean_object* v_a_3765_, lean_object* v_a_3766_, lean_object* v_a_3767_){
_start:
{
lean_object* v_res_3768_; 
v_res_3768_ = l_Lean_Meta_Grind_Arith_CommRing_internalize(v_e_3755_, v_parent_x3f_3756_, v_a_3757_, v_a_3758_, v_a_3759_, v_a_3760_, v_a_3761_, v_a_3762_, v_a_3763_, v_a_3764_, v_a_3765_, v_a_3766_);
lean_dec(v_a_3766_);
lean_dec_ref(v_a_3765_);
lean_dec(v_a_3764_);
lean_dec_ref(v_a_3763_);
lean_dec(v_a_3762_);
lean_dec_ref(v_a_3761_);
lean_dec(v_a_3760_);
lean_dec_ref(v_a_3759_);
lean_dec(v_a_3758_);
lean_dec(v_a_3757_);
return v_res_3768_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0(lean_object* v_00_u03b2_3769_, lean_object* v_x_3770_, lean_object* v_x_3771_, lean_object* v_x_3772_){
_start:
{
lean_object* v___x_3773_; 
v___x_3773_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0___redArg(v_x_3770_, v_x_3771_, v_x_3772_);
return v___x_3773_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__1(lean_object* v_cls_3774_, lean_object* v_msg_3775_, lean_object* v___y_3776_, lean_object* v___y_3777_, lean_object* v___y_3778_, lean_object* v___y_3779_, lean_object* v___y_3780_, lean_object* v___y_3781_, lean_object* v___y_3782_, lean_object* v___y_3783_, lean_object* v___y_3784_, lean_object* v___y_3785_, lean_object* v___y_3786_){
_start:
{
lean_object* v___x_3788_; 
v___x_3788_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__1___redArg(v_cls_3774_, v_msg_3775_, v___y_3783_, v___y_3784_, v___y_3785_, v___y_3786_);
return v___x_3788_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__1___boxed(lean_object* v_cls_3789_, lean_object* v_msg_3790_, lean_object* v___y_3791_, lean_object* v___y_3792_, lean_object* v___y_3793_, lean_object* v___y_3794_, lean_object* v___y_3795_, lean_object* v___y_3796_, lean_object* v___y_3797_, lean_object* v___y_3798_, lean_object* v___y_3799_, lean_object* v___y_3800_, lean_object* v___y_3801_, lean_object* v___y_3802_){
_start:
{
lean_object* v_res_3803_; 
v_res_3803_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__1(v_cls_3789_, v_msg_3790_, v___y_3791_, v___y_3792_, v___y_3793_, v___y_3794_, v___y_3795_, v___y_3796_, v___y_3797_, v___y_3798_, v___y_3799_, v___y_3800_, v___y_3801_);
lean_dec(v___y_3801_);
lean_dec_ref(v___y_3800_);
lean_dec(v___y_3799_);
lean_dec_ref(v___y_3798_);
lean_dec(v___y_3797_);
lean_dec_ref(v___y_3796_);
lean_dec(v___y_3795_);
lean_dec_ref(v___y_3794_);
lean_dec(v___y_3793_);
lean_dec(v___y_3792_);
lean_dec(v___y_3791_);
return v_res_3803_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__2(lean_object* v_cls_3804_, lean_object* v_msg_3805_, lean_object* v___y_3806_, lean_object* v___y_3807_, lean_object* v___y_3808_, lean_object* v___y_3809_, lean_object* v___y_3810_, lean_object* v___y_3811_, lean_object* v___y_3812_, lean_object* v___y_3813_, lean_object* v___y_3814_, lean_object* v___y_3815_, lean_object* v___y_3816_){
_start:
{
lean_object* v___x_3818_; 
v___x_3818_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__2___redArg(v_cls_3804_, v_msg_3805_, v___y_3813_, v___y_3814_, v___y_3815_, v___y_3816_);
return v___x_3818_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__2___boxed(lean_object* v_cls_3819_, lean_object* v_msg_3820_, lean_object* v___y_3821_, lean_object* v___y_3822_, lean_object* v___y_3823_, lean_object* v___y_3824_, lean_object* v___y_3825_, lean_object* v___y_3826_, lean_object* v___y_3827_, lean_object* v___y_3828_, lean_object* v___y_3829_, lean_object* v___y_3830_, lean_object* v___y_3831_, lean_object* v___y_3832_){
_start:
{
lean_object* v_res_3833_; 
v_res_3833_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__2(v_cls_3819_, v_msg_3820_, v___y_3821_, v___y_3822_, v___y_3823_, v___y_3824_, v___y_3825_, v___y_3826_, v___y_3827_, v___y_3828_, v___y_3829_, v___y_3830_, v___y_3831_);
lean_dec(v___y_3831_);
lean_dec_ref(v___y_3830_);
lean_dec(v___y_3829_);
lean_dec_ref(v___y_3828_);
lean_dec(v___y_3827_);
lean_dec_ref(v___y_3826_);
lean_dec(v___y_3825_);
lean_dec_ref(v___y_3824_);
lean_dec(v___y_3823_);
lean_dec(v___y_3822_);
lean_dec(v___y_3821_);
return v_res_3833_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__3(lean_object* v_cls_3834_, lean_object* v_msg_3835_, lean_object* v___y_3836_, lean_object* v___y_3837_, lean_object* v___y_3838_, lean_object* v___y_3839_, lean_object* v___y_3840_, lean_object* v___y_3841_, lean_object* v___y_3842_, lean_object* v___y_3843_, lean_object* v___y_3844_, lean_object* v___y_3845_, lean_object* v___y_3846_){
_start:
{
lean_object* v___x_3848_; 
v___x_3848_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__3___redArg(v_cls_3834_, v_msg_3835_, v___y_3843_, v___y_3844_, v___y_3845_, v___y_3846_);
return v___x_3848_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__3___boxed(lean_object* v_cls_3849_, lean_object* v_msg_3850_, lean_object* v___y_3851_, lean_object* v___y_3852_, lean_object* v___y_3853_, lean_object* v___y_3854_, lean_object* v___y_3855_, lean_object* v___y_3856_, lean_object* v___y_3857_, lean_object* v___y_3858_, lean_object* v___y_3859_, lean_object* v___y_3860_, lean_object* v___y_3861_, lean_object* v___y_3862_){
_start:
{
lean_object* v_res_3863_; 
v_res_3863_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__3(v_cls_3849_, v_msg_3850_, v___y_3851_, v___y_3852_, v___y_3853_, v___y_3854_, v___y_3855_, v___y_3856_, v___y_3857_, v___y_3858_, v___y_3859_, v___y_3860_, v___y_3861_);
lean_dec(v___y_3861_);
lean_dec_ref(v___y_3860_);
lean_dec(v___y_3859_);
lean_dec_ref(v___y_3858_);
lean_dec(v___y_3857_);
lean_dec_ref(v___y_3856_);
lean_dec(v___y_3855_);
lean_dec_ref(v___y_3854_);
lean_dec(v___y_3853_);
lean_dec(v___y_3852_);
lean_dec(v___y_3851_);
return v_res_3863_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0(lean_object* v_00_u03b2_3864_, lean_object* v_x_3865_, size_t v_x_3866_, size_t v_x_3867_, lean_object* v_x_3868_, lean_object* v_x_3869_){
_start:
{
lean_object* v___x_3870_; 
v___x_3870_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0___redArg(v_x_3865_, v_x_3866_, v_x_3867_, v_x_3868_, v_x_3869_);
return v___x_3870_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3871_, lean_object* v_x_3872_, lean_object* v_x_3873_, lean_object* v_x_3874_, lean_object* v_x_3875_, lean_object* v_x_3876_){
_start:
{
size_t v_x_212261__boxed_3877_; size_t v_x_212262__boxed_3878_; lean_object* v_res_3879_; 
v_x_212261__boxed_3877_ = lean_unbox_usize(v_x_3873_);
lean_dec(v_x_3873_);
v_x_212262__boxed_3878_ = lean_unbox_usize(v_x_3874_);
lean_dec(v_x_3874_);
v_res_3879_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0(v_00_u03b2_3871_, v_x_3872_, v_x_212261__boxed_3877_, v_x_212262__boxed_3878_, v_x_3875_, v_x_3876_);
return v_res_3879_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_3880_, lean_object* v_n_3881_, lean_object* v_k_3882_, lean_object* v_v_3883_){
_start:
{
lean_object* v___x_3884_; 
v___x_3884_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0_spec__1___redArg(v_n_3881_, v_k_3882_, v_v_3883_);
return v___x_3884_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_3885_, size_t v_depth_3886_, lean_object* v_keys_3887_, lean_object* v_vals_3888_, lean_object* v_heq_3889_, lean_object* v_i_3890_, lean_object* v_entries_3891_){
_start:
{
lean_object* v___x_3892_; 
v___x_3892_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0_spec__2___redArg(v_depth_3886_, v_keys_3887_, v_vals_3888_, v_i_3890_, v_entries_3891_);
return v___x_3892_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_3893_, lean_object* v_depth_3894_, lean_object* v_keys_3895_, lean_object* v_vals_3896_, lean_object* v_heq_3897_, lean_object* v_i_3898_, lean_object* v_entries_3899_){
_start:
{
size_t v_depth_boxed_3900_; lean_object* v_res_3901_; 
v_depth_boxed_3900_ = lean_unbox_usize(v_depth_3894_);
lean_dec(v_depth_3894_);
v_res_3901_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0_spec__2(v_00_u03b2_3893_, v_depth_boxed_3900_, v_keys_3895_, v_vals_3896_, v_heq_3897_, v_i_3898_, v_entries_3899_);
lean_dec_ref(v_vals_3896_);
lean_dec_ref(v_keys_3895_);
return v_res_3901_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0_spec__1_spec__5(lean_object* v_00_u03b2_3902_, lean_object* v_x_3903_, lean_object* v_x_3904_, lean_object* v_x_3905_, lean_object* v_x_3906_){
_start:
{
lean_object* v___x_3907_; 
v___x_3907_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0_spec__1_spec__5___redArg(v_x_3903_, v_x_3904_, v_x_3905_, v_x_3906_);
return v___x_3907_;
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
