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
lean_object* l_Lean_Meta_Sym_shareCommon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_synthInstance_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkInst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
size_t lean_usize_shift_right(size_t, size_t);
uint64_t lean_usize_to_uint64(size_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
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
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Meta_synthInstance_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* lean_st_ref_put(lean_object*, lean_object*);
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
lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg___closed__0;
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
lean_dec_ref_known(v_parent_x3f_134_, 1);
v___x_136_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f(v_val_135_);
if (lean_obj_tag(v___x_136_) == 0)
{
uint8_t v___x_137_; lean_object* v___x_138_; uint8_t v___x_139_; 
v___x_137_ = 0;
v___x_138_ = l_Lean_Expr_cleanupAnnotations(v_val_135_);
v___x_139_ = l_Lean_Expr_isApp(v___x_138_);
if (v___x_139_ == 0)
{
lean_dec_ref(v___x_138_);
return v___x_137_;
}
else
{
lean_object* v___x_140_; uint8_t v___x_141_; 
v___x_140_ = l_Lean_Expr_appFnCleanup___redArg(v___x_138_);
v___x_141_ = l_Lean_Expr_isApp(v___x_140_);
if (v___x_141_ == 0)
{
lean_dec_ref(v___x_140_);
return v___x_137_;
}
else
{
lean_object* v___x_142_; uint8_t v___x_143_; 
v___x_142_ = l_Lean_Expr_appFnCleanup___redArg(v___x_140_);
v___x_143_ = l_Lean_Expr_isApp(v___x_142_);
if (v___x_143_ == 0)
{
lean_dec_ref(v___x_142_);
return v___x_137_;
}
else
{
lean_object* v___x_144_; uint8_t v___x_145_; 
v___x_144_ = l_Lean_Expr_appFnCleanup___redArg(v___x_142_);
v___x_145_ = l_Lean_Expr_isApp(v___x_144_);
if (v___x_145_ == 0)
{
lean_dec_ref(v___x_144_);
return v___x_137_;
}
else
{
lean_object* v___x_146_; lean_object* v___x_147_; uint8_t v___x_148_; 
v___x_146_ = l_Lean_Expr_appFnCleanup___redArg(v___x_144_);
v___x_147_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isForbiddenParent___closed__2));
v___x_148_ = l_Lean_Expr_isConstOf(v___x_146_, v___x_147_);
if (v___x_148_ == 0)
{
lean_object* v___x_149_; uint8_t v___x_150_; 
v___x_149_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isForbiddenParent___closed__5));
v___x_150_ = l_Lean_Expr_isConstOf(v___x_146_, v___x_149_);
if (v___x_150_ == 0)
{
uint8_t v___x_151_; 
v___x_151_ = l_Lean_Expr_isApp(v___x_146_);
if (v___x_151_ == 0)
{
lean_dec_ref(v___x_146_);
return v___x_137_;
}
else
{
lean_object* v___x_152_; uint8_t v___x_153_; 
v___x_152_ = l_Lean_Expr_appFnCleanup___redArg(v___x_146_);
v___x_153_ = l_Lean_Expr_isApp(v___x_152_);
if (v___x_153_ == 0)
{
lean_dec_ref(v___x_152_);
return v___x_137_;
}
else
{
lean_object* v___x_154_; lean_object* v___x_155_; uint8_t v___x_156_; 
v___x_154_ = l_Lean_Expr_appFnCleanup___redArg(v___x_152_);
v___x_155_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isForbiddenParent___closed__8));
v___x_156_ = l_Lean_Expr_isConstOf(v___x_154_, v___x_155_);
if (v___x_156_ == 0)
{
lean_object* v___x_157_; uint8_t v___x_158_; 
v___x_157_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isForbiddenParent___closed__11));
v___x_158_ = l_Lean_Expr_isConstOf(v___x_154_, v___x_157_);
lean_dec_ref(v___x_154_);
if (v___x_158_ == 0)
{
return v___x_137_;
}
else
{
return v___x_145_;
}
}
else
{
lean_dec_ref(v___x_154_);
return v___x_145_;
}
}
}
}
else
{
lean_dec_ref(v___x_146_);
return v___x_145_;
}
}
else
{
lean_dec_ref(v___x_146_);
return v___x_145_;
}
}
}
}
}
}
else
{
uint8_t v___x_159_; 
lean_dec_ref_known(v___x_136_, 1);
lean_dec(v_val_135_);
v___x_159_ = 1;
return v___x_159_;
}
}
else
{
uint8_t v___x_160_; 
lean_dec(v_parent_x3f_134_);
v___x_160_ = 0;
return v___x_160_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isForbiddenParent___boxed(lean_object* v_parent_x3f_161_){
_start:
{
uint8_t v_res_162_; lean_object* v_r_163_; 
v_res_162_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isForbiddenParent(v_parent_x3f_161_);
v_r_163_ = lean_box(v_res_162_);
return v_r_163_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0___lam__0(lean_object* v_a_164_, lean_object* v_s_165_){
_start:
{
lean_object* v_toRing_166_; lean_object* v_invFn_x3f_167_; lean_object* v_semiringId_x3f_168_; lean_object* v_commSemiringInst_169_; lean_object* v_commRingInst_170_; lean_object* v_noZeroDivInst_x3f_171_; lean_object* v_fieldInst_x3f_172_; lean_object* v_powIdentityInst_x3f_173_; lean_object* v_denoteEntries_174_; lean_object* v_nextId_175_; lean_object* v_steps_176_; lean_object* v_queue_177_; lean_object* v_basis_178_; lean_object* v_diseqs_179_; uint8_t v_recheck_180_; lean_object* v_invSet_181_; lean_object* v_powIdentityVarCount_182_; lean_object* v_numEq0_x3f_183_; uint8_t v_numEq0Updated_184_; lean_object* v___x_186_; uint8_t v_isShared_187_; uint8_t v_isSharedCheck_216_; 
v_toRing_166_ = lean_ctor_get(v_s_165_, 0);
v_invFn_x3f_167_ = lean_ctor_get(v_s_165_, 1);
v_semiringId_x3f_168_ = lean_ctor_get(v_s_165_, 2);
v_commSemiringInst_169_ = lean_ctor_get(v_s_165_, 3);
v_commRingInst_170_ = lean_ctor_get(v_s_165_, 4);
v_noZeroDivInst_x3f_171_ = lean_ctor_get(v_s_165_, 5);
v_fieldInst_x3f_172_ = lean_ctor_get(v_s_165_, 6);
v_powIdentityInst_x3f_173_ = lean_ctor_get(v_s_165_, 7);
v_denoteEntries_174_ = lean_ctor_get(v_s_165_, 8);
v_nextId_175_ = lean_ctor_get(v_s_165_, 9);
v_steps_176_ = lean_ctor_get(v_s_165_, 10);
v_queue_177_ = lean_ctor_get(v_s_165_, 11);
v_basis_178_ = lean_ctor_get(v_s_165_, 12);
v_diseqs_179_ = lean_ctor_get(v_s_165_, 13);
v_recheck_180_ = lean_ctor_get_uint8(v_s_165_, sizeof(void*)*17);
v_invSet_181_ = lean_ctor_get(v_s_165_, 14);
v_powIdentityVarCount_182_ = lean_ctor_get(v_s_165_, 15);
v_numEq0_x3f_183_ = lean_ctor_get(v_s_165_, 16);
v_numEq0Updated_184_ = lean_ctor_get_uint8(v_s_165_, sizeof(void*)*17 + 1);
v_isSharedCheck_216_ = !lean_is_exclusive(v_s_165_);
if (v_isSharedCheck_216_ == 0)
{
v___x_186_ = v_s_165_;
v_isShared_187_ = v_isSharedCheck_216_;
goto v_resetjp_185_;
}
else
{
lean_inc(v_numEq0_x3f_183_);
lean_inc(v_powIdentityVarCount_182_);
lean_inc(v_invSet_181_);
lean_inc(v_diseqs_179_);
lean_inc(v_basis_178_);
lean_inc(v_queue_177_);
lean_inc(v_steps_176_);
lean_inc(v_nextId_175_);
lean_inc(v_denoteEntries_174_);
lean_inc(v_powIdentityInst_x3f_173_);
lean_inc(v_fieldInst_x3f_172_);
lean_inc(v_noZeroDivInst_x3f_171_);
lean_inc(v_commRingInst_170_);
lean_inc(v_commSemiringInst_169_);
lean_inc(v_semiringId_x3f_168_);
lean_inc(v_invFn_x3f_167_);
lean_inc(v_toRing_166_);
lean_dec(v_s_165_);
v___x_186_ = lean_box(0);
v_isShared_187_ = v_isSharedCheck_216_;
goto v_resetjp_185_;
}
v_resetjp_185_:
{
lean_object* v_id_188_; lean_object* v_type_189_; lean_object* v_u_190_; lean_object* v_ringInst_191_; lean_object* v_semiringInst_192_; lean_object* v_charInst_x3f_193_; lean_object* v_addFn_x3f_194_; lean_object* v_mulFn_x3f_195_; lean_object* v_subFn_x3f_196_; lean_object* v_powFn_x3f_197_; lean_object* v_intCastFn_x3f_198_; lean_object* v_natCastFn_x3f_199_; lean_object* v_one_x3f_200_; lean_object* v_vars_201_; lean_object* v_varMap_202_; lean_object* v_denote_203_; lean_object* v___x_205_; uint8_t v_isShared_206_; uint8_t v_isSharedCheck_214_; 
v_id_188_ = lean_ctor_get(v_toRing_166_, 0);
v_type_189_ = lean_ctor_get(v_toRing_166_, 1);
v_u_190_ = lean_ctor_get(v_toRing_166_, 2);
v_ringInst_191_ = lean_ctor_get(v_toRing_166_, 3);
v_semiringInst_192_ = lean_ctor_get(v_toRing_166_, 4);
v_charInst_x3f_193_ = lean_ctor_get(v_toRing_166_, 5);
v_addFn_x3f_194_ = lean_ctor_get(v_toRing_166_, 6);
v_mulFn_x3f_195_ = lean_ctor_get(v_toRing_166_, 7);
v_subFn_x3f_196_ = lean_ctor_get(v_toRing_166_, 8);
v_powFn_x3f_197_ = lean_ctor_get(v_toRing_166_, 10);
v_intCastFn_x3f_198_ = lean_ctor_get(v_toRing_166_, 11);
v_natCastFn_x3f_199_ = lean_ctor_get(v_toRing_166_, 12);
v_one_x3f_200_ = lean_ctor_get(v_toRing_166_, 13);
v_vars_201_ = lean_ctor_get(v_toRing_166_, 14);
v_varMap_202_ = lean_ctor_get(v_toRing_166_, 15);
v_denote_203_ = lean_ctor_get(v_toRing_166_, 16);
v_isSharedCheck_214_ = !lean_is_exclusive(v_toRing_166_);
if (v_isSharedCheck_214_ == 0)
{
lean_object* v_unused_215_; 
v_unused_215_ = lean_ctor_get(v_toRing_166_, 9);
lean_dec(v_unused_215_);
v___x_205_ = v_toRing_166_;
v_isShared_206_ = v_isSharedCheck_214_;
goto v_resetjp_204_;
}
else
{
lean_inc(v_denote_203_);
lean_inc(v_varMap_202_);
lean_inc(v_vars_201_);
lean_inc(v_one_x3f_200_);
lean_inc(v_natCastFn_x3f_199_);
lean_inc(v_intCastFn_x3f_198_);
lean_inc(v_powFn_x3f_197_);
lean_inc(v_subFn_x3f_196_);
lean_inc(v_mulFn_x3f_195_);
lean_inc(v_addFn_x3f_194_);
lean_inc(v_charInst_x3f_193_);
lean_inc(v_semiringInst_192_);
lean_inc(v_ringInst_191_);
lean_inc(v_u_190_);
lean_inc(v_type_189_);
lean_inc(v_id_188_);
lean_dec(v_toRing_166_);
v___x_205_ = lean_box(0);
v_isShared_206_ = v_isSharedCheck_214_;
goto v_resetjp_204_;
}
v_resetjp_204_:
{
lean_object* v___x_207_; lean_object* v___x_209_; 
v___x_207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_207_, 0, v_a_164_);
if (v_isShared_206_ == 0)
{
lean_ctor_set(v___x_205_, 9, v___x_207_);
v___x_209_ = v___x_205_;
goto v_reusejp_208_;
}
else
{
lean_object* v_reuseFailAlloc_213_; 
v_reuseFailAlloc_213_ = lean_alloc_ctor(0, 17, 0);
lean_ctor_set(v_reuseFailAlloc_213_, 0, v_id_188_);
lean_ctor_set(v_reuseFailAlloc_213_, 1, v_type_189_);
lean_ctor_set(v_reuseFailAlloc_213_, 2, v_u_190_);
lean_ctor_set(v_reuseFailAlloc_213_, 3, v_ringInst_191_);
lean_ctor_set(v_reuseFailAlloc_213_, 4, v_semiringInst_192_);
lean_ctor_set(v_reuseFailAlloc_213_, 5, v_charInst_x3f_193_);
lean_ctor_set(v_reuseFailAlloc_213_, 6, v_addFn_x3f_194_);
lean_ctor_set(v_reuseFailAlloc_213_, 7, v_mulFn_x3f_195_);
lean_ctor_set(v_reuseFailAlloc_213_, 8, v_subFn_x3f_196_);
lean_ctor_set(v_reuseFailAlloc_213_, 9, v___x_207_);
lean_ctor_set(v_reuseFailAlloc_213_, 10, v_powFn_x3f_197_);
lean_ctor_set(v_reuseFailAlloc_213_, 11, v_intCastFn_x3f_198_);
lean_ctor_set(v_reuseFailAlloc_213_, 12, v_natCastFn_x3f_199_);
lean_ctor_set(v_reuseFailAlloc_213_, 13, v_one_x3f_200_);
lean_ctor_set(v_reuseFailAlloc_213_, 14, v_vars_201_);
lean_ctor_set(v_reuseFailAlloc_213_, 15, v_varMap_202_);
lean_ctor_set(v_reuseFailAlloc_213_, 16, v_denote_203_);
v___x_209_ = v_reuseFailAlloc_213_;
goto v_reusejp_208_;
}
v_reusejp_208_:
{
lean_object* v___x_211_; 
if (v_isShared_187_ == 0)
{
lean_ctor_set(v___x_186_, 0, v___x_209_);
v___x_211_ = v___x_186_;
goto v_reusejp_210_;
}
else
{
lean_object* v_reuseFailAlloc_212_; 
v_reuseFailAlloc_212_ = lean_alloc_ctor(0, 17, 2);
lean_ctor_set(v_reuseFailAlloc_212_, 0, v___x_209_);
lean_ctor_set(v_reuseFailAlloc_212_, 1, v_invFn_x3f_167_);
lean_ctor_set(v_reuseFailAlloc_212_, 2, v_semiringId_x3f_168_);
lean_ctor_set(v_reuseFailAlloc_212_, 3, v_commSemiringInst_169_);
lean_ctor_set(v_reuseFailAlloc_212_, 4, v_commRingInst_170_);
lean_ctor_set(v_reuseFailAlloc_212_, 5, v_noZeroDivInst_x3f_171_);
lean_ctor_set(v_reuseFailAlloc_212_, 6, v_fieldInst_x3f_172_);
lean_ctor_set(v_reuseFailAlloc_212_, 7, v_powIdentityInst_x3f_173_);
lean_ctor_set(v_reuseFailAlloc_212_, 8, v_denoteEntries_174_);
lean_ctor_set(v_reuseFailAlloc_212_, 9, v_nextId_175_);
lean_ctor_set(v_reuseFailAlloc_212_, 10, v_steps_176_);
lean_ctor_set(v_reuseFailAlloc_212_, 11, v_queue_177_);
lean_ctor_set(v_reuseFailAlloc_212_, 12, v_basis_178_);
lean_ctor_set(v_reuseFailAlloc_212_, 13, v_diseqs_179_);
lean_ctor_set(v_reuseFailAlloc_212_, 14, v_invSet_181_);
lean_ctor_set(v_reuseFailAlloc_212_, 15, v_powIdentityVarCount_182_);
lean_ctor_set(v_reuseFailAlloc_212_, 16, v_numEq0_x3f_183_);
lean_ctor_set_uint8(v_reuseFailAlloc_212_, sizeof(void*)*17, v_recheck_180_);
lean_ctor_set_uint8(v_reuseFailAlloc_212_, sizeof(void*)*17 + 1, v_numEq0Updated_184_);
v___x_211_ = v_reuseFailAlloc_212_;
goto v_reusejp_210_;
}
v_reusejp_210_:
{
return v___x_211_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1_spec__5_spec__8_spec__9(lean_object* v_msgData_217_, lean_object* v___y_218_, lean_object* v___y_219_, lean_object* v___y_220_, lean_object* v___y_221_){
_start:
{
lean_object* v___x_223_; lean_object* v_env_224_; lean_object* v___x_225_; lean_object* v_toCold_226_; lean_object* v_mctx_227_; lean_object* v_lctx_228_; lean_object* v_options_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; 
v___x_223_ = lean_st_ref_get(v___y_221_);
v_env_224_ = lean_ctor_get(v___x_223_, 0);
lean_inc_ref(v_env_224_);
lean_dec(v___x_223_);
v___x_225_ = lean_st_ref_get(v___y_219_);
v_toCold_226_ = lean_ctor_get(v___y_220_, 0);
v_mctx_227_ = lean_ctor_get(v___x_225_, 0);
lean_inc_ref(v_mctx_227_);
lean_dec(v___x_225_);
v_lctx_228_ = lean_ctor_get(v___y_218_, 2);
v_options_229_ = lean_ctor_get(v_toCold_226_, 2);
lean_inc_ref(v_options_229_);
lean_inc_ref(v_lctx_228_);
v___x_230_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_230_, 0, v_env_224_);
lean_ctor_set(v___x_230_, 1, v_mctx_227_);
lean_ctor_set(v___x_230_, 2, v_lctx_228_);
lean_ctor_set(v___x_230_, 3, v_options_229_);
v___x_231_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_231_, 0, v___x_230_);
lean_ctor_set(v___x_231_, 1, v_msgData_217_);
v___x_232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_232_, 0, v___x_231_);
return v___x_232_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1_spec__5_spec__8_spec__9___boxed(lean_object* v_msgData_233_, lean_object* v___y_234_, lean_object* v___y_235_, lean_object* v___y_236_, lean_object* v___y_237_, lean_object* v___y_238_){
_start:
{
lean_object* v_res_239_; 
v_res_239_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1_spec__5_spec__8_spec__9(v_msgData_233_, v___y_234_, v___y_235_, v___y_236_, v___y_237_);
lean_dec(v___y_237_);
lean_dec_ref(v___y_236_);
lean_dec(v___y_235_);
lean_dec_ref(v___y_234_);
return v_res_239_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1_spec__5_spec__8___redArg(lean_object* v_msg_240_, lean_object* v___y_241_, lean_object* v___y_242_, lean_object* v___y_243_, lean_object* v___y_244_){
_start:
{
lean_object* v_ref_246_; lean_object* v___x_247_; lean_object* v_a_248_; lean_object* v___x_250_; uint8_t v_isShared_251_; uint8_t v_isSharedCheck_256_; 
v_ref_246_ = lean_ctor_get(v___y_243_, 2);
v___x_247_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1_spec__5_spec__8_spec__9(v_msg_240_, v___y_241_, v___y_242_, v___y_243_, v___y_244_);
v_a_248_ = lean_ctor_get(v___x_247_, 0);
v_isSharedCheck_256_ = !lean_is_exclusive(v___x_247_);
if (v_isSharedCheck_256_ == 0)
{
v___x_250_ = v___x_247_;
v_isShared_251_ = v_isSharedCheck_256_;
goto v_resetjp_249_;
}
else
{
lean_inc(v_a_248_);
lean_dec(v___x_247_);
v___x_250_ = lean_box(0);
v_isShared_251_ = v_isSharedCheck_256_;
goto v_resetjp_249_;
}
v_resetjp_249_:
{
lean_object* v___x_252_; lean_object* v___x_254_; 
lean_inc(v_ref_246_);
v___x_252_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_252_, 0, v_ref_246_);
lean_ctor_set(v___x_252_, 1, v_a_248_);
if (v_isShared_251_ == 0)
{
lean_ctor_set_tag(v___x_250_, 1);
lean_ctor_set(v___x_250_, 0, v___x_252_);
v___x_254_ = v___x_250_;
goto v_reusejp_253_;
}
else
{
lean_object* v_reuseFailAlloc_255_; 
v_reuseFailAlloc_255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_255_, 0, v___x_252_);
v___x_254_ = v_reuseFailAlloc_255_;
goto v_reusejp_253_;
}
v_reusejp_253_:
{
return v___x_254_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1_spec__5_spec__8___redArg___boxed(lean_object* v_msg_257_, lean_object* v___y_258_, lean_object* v___y_259_, lean_object* v___y_260_, lean_object* v___y_261_, lean_object* v___y_262_){
_start:
{
lean_object* v_res_263_; 
v_res_263_ = l_Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1_spec__5_spec__8___redArg(v_msg_257_, v___y_258_, v___y_259_, v___y_260_, v___y_261_);
lean_dec(v___y_261_);
lean_dec_ref(v___y_260_);
lean_dec(v___y_259_);
lean_dec_ref(v___y_258_);
return v_res_263_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1_spec__5___closed__1(void){
_start:
{
lean_object* v___x_265_; lean_object* v___x_266_; 
v___x_265_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1_spec__5___closed__0));
v___x_266_ = l_Lean_stringToMessageData(v___x_265_);
return v___x_266_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1_spec__5(lean_object* v_type_267_, lean_object* v___y_268_, lean_object* v___y_269_, lean_object* v___y_270_, lean_object* v___y_271_, lean_object* v___y_272_, lean_object* v___y_273_, lean_object* v___y_274_, lean_object* v___y_275_, lean_object* v___y_276_, lean_object* v___y_277_, lean_object* v___y_278_){
_start:
{
lean_object* v___x_280_; 
lean_inc_ref(v_type_267_);
v___x_280_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v_type_267_, v___y_274_, v___y_275_, v___y_276_, v___y_277_, v___y_278_);
if (lean_obj_tag(v___x_280_) == 0)
{
lean_object* v_a_281_; lean_object* v___x_283_; uint8_t v_isShared_284_; uint8_t v_isSharedCheck_293_; 
v_a_281_ = lean_ctor_get(v___x_280_, 0);
v_isSharedCheck_293_ = !lean_is_exclusive(v___x_280_);
if (v_isSharedCheck_293_ == 0)
{
v___x_283_ = v___x_280_;
v_isShared_284_ = v_isSharedCheck_293_;
goto v_resetjp_282_;
}
else
{
lean_inc(v_a_281_);
lean_dec(v___x_280_);
v___x_283_ = lean_box(0);
v_isShared_284_ = v_isSharedCheck_293_;
goto v_resetjp_282_;
}
v_resetjp_282_:
{
if (lean_obj_tag(v_a_281_) == 1)
{
lean_object* v_val_285_; lean_object* v___x_287_; 
lean_dec_ref(v_type_267_);
v_val_285_ = lean_ctor_get(v_a_281_, 0);
lean_inc(v_val_285_);
lean_dec_ref_known(v_a_281_, 1);
if (v_isShared_284_ == 0)
{
lean_ctor_set(v___x_283_, 0, v_val_285_);
v___x_287_ = v___x_283_;
goto v_reusejp_286_;
}
else
{
lean_object* v_reuseFailAlloc_288_; 
v_reuseFailAlloc_288_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_288_, 0, v_val_285_);
v___x_287_ = v_reuseFailAlloc_288_;
goto v_reusejp_286_;
}
v_reusejp_286_:
{
return v___x_287_;
}
}
else
{
lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; 
lean_del_object(v___x_283_);
lean_dec(v_a_281_);
v___x_289_ = lean_obj_once(&l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1_spec__5___closed__1, &l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1_spec__5___closed__1_once, _init_l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1_spec__5___closed__1);
v___x_290_ = l_Lean_indentExpr(v_type_267_);
v___x_291_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_291_, 0, v___x_289_);
lean_ctor_set(v___x_291_, 1, v___x_290_);
v___x_292_ = l_Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1_spec__5_spec__8___redArg(v___x_291_, v___y_275_, v___y_276_, v___y_277_, v___y_278_);
return v___x_292_;
}
}
}
else
{
lean_object* v_a_294_; lean_object* v___x_296_; uint8_t v_isShared_297_; uint8_t v_isSharedCheck_301_; 
lean_dec_ref(v_type_267_);
v_a_294_ = lean_ctor_get(v___x_280_, 0);
v_isSharedCheck_301_ = !lean_is_exclusive(v___x_280_);
if (v_isSharedCheck_301_ == 0)
{
v___x_296_ = v___x_280_;
v_isShared_297_ = v_isSharedCheck_301_;
goto v_resetjp_295_;
}
else
{
lean_inc(v_a_294_);
lean_dec(v___x_280_);
v___x_296_ = lean_box(0);
v_isShared_297_ = v_isSharedCheck_301_;
goto v_resetjp_295_;
}
v_resetjp_295_:
{
lean_object* v___x_299_; 
if (v_isShared_297_ == 0)
{
v___x_299_ = v___x_296_;
goto v_reusejp_298_;
}
else
{
lean_object* v_reuseFailAlloc_300_; 
v_reuseFailAlloc_300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_300_, 0, v_a_294_);
v___x_299_ = v_reuseFailAlloc_300_;
goto v_reusejp_298_;
}
v_reusejp_298_:
{
return v___x_299_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1_spec__5___boxed(lean_object* v_type_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_, lean_object* v___y_309_, lean_object* v___y_310_, lean_object* v___y_311_, lean_object* v___y_312_, lean_object* v___y_313_, lean_object* v___y_314_){
_start:
{
lean_object* v_res_315_; 
v_res_315_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1_spec__5(v_type_302_, v___y_303_, v___y_304_, v___y_305_, v___y_306_, v___y_307_, v___y_308_, v___y_309_, v___y_310_, v___y_311_, v___y_312_, v___y_313_);
lean_dec(v___y_313_);
lean_dec_ref(v___y_312_);
lean_dec(v___y_311_);
lean_dec_ref(v___y_310_);
lean_dec(v___y_309_);
lean_dec_ref(v___y_308_);
lean_dec(v___y_307_);
lean_dec_ref(v___y_306_);
lean_dec(v___y_305_);
lean_dec(v___y_304_);
lean_dec_ref(v___y_303_);
return v_res_315_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1(lean_object* v_type_316_, lean_object* v_u_317_, lean_object* v_instDeclName_318_, lean_object* v_declName_319_, lean_object* v_expectedInst_320_, lean_object* v___y_321_, lean_object* v___y_322_, lean_object* v___y_323_, lean_object* v___y_324_, lean_object* v___y_325_, lean_object* v___y_326_, lean_object* v___y_327_, lean_object* v___y_328_, lean_object* v___y_329_, lean_object* v___y_330_, lean_object* v___y_331_){
_start:
{
lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; 
v___x_333_ = lean_box(0);
v___x_334_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_334_, 0, v_u_317_);
lean_ctor_set(v___x_334_, 1, v___x_333_);
lean_inc_ref(v___x_334_);
v___x_335_ = l_Lean_mkConst(v_instDeclName_318_, v___x_334_);
lean_inc_ref(v_type_316_);
v___x_336_ = l_Lean_Expr_app___override(v___x_335_, v_type_316_);
v___x_337_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1_spec__5(v___x_336_, v___y_321_, v___y_322_, v___y_323_, v___y_324_, v___y_325_, v___y_326_, v___y_327_, v___y_328_, v___y_329_, v___y_330_, v___y_331_);
if (lean_obj_tag(v___x_337_) == 0)
{
lean_object* v_a_338_; lean_object* v___x_339_; 
v_a_338_ = lean_ctor_get(v___x_337_, 0);
lean_inc_n(v_a_338_, 2);
lean_dec_ref_known(v___x_337_, 1);
lean_inc(v_declName_319_);
v___x_339_ = l_Lean_Meta_Grind_Arith_CommRing_checkInst(v_declName_319_, v_a_338_, v_expectedInst_320_, v___y_328_, v___y_329_, v___y_330_, v___y_331_);
if (lean_obj_tag(v___x_339_) == 0)
{
lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; 
lean_dec_ref_known(v___x_339_, 1);
v___x_340_ = l_Lean_mkConst(v_declName_319_, v___x_334_);
v___x_341_ = l_Lean_mkAppB(v___x_340_, v_type_316_, v_a_338_);
v___x_342_ = l_Lean_Meta_Sym_canon(v___x_341_, v___y_326_, v___y_327_, v___y_328_, v___y_329_, v___y_330_, v___y_331_);
if (lean_obj_tag(v___x_342_) == 0)
{
lean_object* v_a_343_; lean_object* v___x_344_; 
v_a_343_ = lean_ctor_get(v___x_342_, 0);
lean_inc(v_a_343_);
lean_dec_ref_known(v___x_342_, 1);
v___x_344_ = l_Lean_Meta_Sym_shareCommon(v_a_343_, v___y_326_, v___y_327_, v___y_328_, v___y_329_, v___y_330_, v___y_331_);
return v___x_344_;
}
else
{
return v___x_342_;
}
}
else
{
lean_object* v_a_345_; lean_object* v___x_347_; uint8_t v_isShared_348_; uint8_t v_isSharedCheck_352_; 
lean_dec(v_a_338_);
lean_dec_ref_known(v___x_334_, 2);
lean_dec(v_declName_319_);
lean_dec_ref(v_type_316_);
v_a_345_ = lean_ctor_get(v___x_339_, 0);
v_isSharedCheck_352_ = !lean_is_exclusive(v___x_339_);
if (v_isSharedCheck_352_ == 0)
{
v___x_347_ = v___x_339_;
v_isShared_348_ = v_isSharedCheck_352_;
goto v_resetjp_346_;
}
else
{
lean_inc(v_a_345_);
lean_dec(v___x_339_);
v___x_347_ = lean_box(0);
v_isShared_348_ = v_isSharedCheck_352_;
goto v_resetjp_346_;
}
v_resetjp_346_:
{
lean_object* v___x_350_; 
if (v_isShared_348_ == 0)
{
v___x_350_ = v___x_347_;
goto v_reusejp_349_;
}
else
{
lean_object* v_reuseFailAlloc_351_; 
v_reuseFailAlloc_351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_351_, 0, v_a_345_);
v___x_350_ = v_reuseFailAlloc_351_;
goto v_reusejp_349_;
}
v_reusejp_349_:
{
return v___x_350_;
}
}
}
}
else
{
lean_dec_ref_known(v___x_334_, 2);
lean_dec_ref(v_expectedInst_320_);
lean_dec(v_declName_319_);
lean_dec_ref(v_type_316_);
return v___x_337_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1___boxed(lean_object** _args){
lean_object* v_type_353_ = _args[0];
lean_object* v_u_354_ = _args[1];
lean_object* v_instDeclName_355_ = _args[2];
lean_object* v_declName_356_ = _args[3];
lean_object* v_expectedInst_357_ = _args[4];
lean_object* v___y_358_ = _args[5];
lean_object* v___y_359_ = _args[6];
lean_object* v___y_360_ = _args[7];
lean_object* v___y_361_ = _args[8];
lean_object* v___y_362_ = _args[9];
lean_object* v___y_363_ = _args[10];
lean_object* v___y_364_ = _args[11];
lean_object* v___y_365_ = _args[12];
lean_object* v___y_366_ = _args[13];
lean_object* v___y_367_ = _args[14];
lean_object* v___y_368_ = _args[15];
lean_object* v___y_369_ = _args[16];
_start:
{
lean_object* v_res_370_; 
v_res_370_ = l_Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1(v_type_353_, v_u_354_, v_instDeclName_355_, v_declName_356_, v_expectedInst_357_, v___y_358_, v___y_359_, v___y_360_, v___y_361_, v___y_362_, v___y_363_, v___y_364_, v___y_365_, v___y_366_, v___y_367_, v___y_368_);
lean_dec(v___y_368_);
lean_dec_ref(v___y_367_);
lean_dec(v___y_366_);
lean_dec_ref(v___y_365_);
lean_dec(v___y_364_);
lean_dec_ref(v___y_363_);
lean_dec(v___y_362_);
lean_dec_ref(v___y_361_);
lean_dec(v___y_360_);
lean_dec(v___y_359_);
lean_dec_ref(v___y_358_);
return v_res_370_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0(lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_, lean_object* v___y_392_){
_start:
{
lean_object* v___x_394_; 
v___x_394_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v___y_382_, v___y_383_, v___y_384_, v___y_385_, v___y_386_, v___y_387_, v___y_388_, v___y_389_, v___y_390_, v___y_391_, v___y_392_);
if (lean_obj_tag(v___x_394_) == 0)
{
lean_object* v_a_395_; lean_object* v___x_397_; uint8_t v_isShared_398_; uint8_t v_isSharedCheck_435_; 
v_a_395_ = lean_ctor_get(v___x_394_, 0);
v_isSharedCheck_435_ = !lean_is_exclusive(v___x_394_);
if (v_isSharedCheck_435_ == 0)
{
v___x_397_ = v___x_394_;
v_isShared_398_ = v_isSharedCheck_435_;
goto v_resetjp_396_;
}
else
{
lean_inc(v_a_395_);
lean_dec(v___x_394_);
v___x_397_ = lean_box(0);
v_isShared_398_ = v_isSharedCheck_435_;
goto v_resetjp_396_;
}
v_resetjp_396_:
{
lean_object* v_toRing_399_; lean_object* v_negFn_x3f_400_; 
v_toRing_399_ = lean_ctor_get(v_a_395_, 0);
lean_inc_ref(v_toRing_399_);
lean_dec(v_a_395_);
v_negFn_x3f_400_ = lean_ctor_get(v_toRing_399_, 9);
if (lean_obj_tag(v_negFn_x3f_400_) == 1)
{
lean_object* v_val_401_; lean_object* v___x_403_; 
lean_inc_ref(v_negFn_x3f_400_);
lean_dec_ref(v_toRing_399_);
v_val_401_ = lean_ctor_get(v_negFn_x3f_400_, 0);
lean_inc(v_val_401_);
lean_dec_ref_known(v_negFn_x3f_400_, 1);
if (v_isShared_398_ == 0)
{
lean_ctor_set(v___x_397_, 0, v_val_401_);
v___x_403_ = v___x_397_;
goto v_reusejp_402_;
}
else
{
lean_object* v_reuseFailAlloc_404_; 
v_reuseFailAlloc_404_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_404_, 0, v_val_401_);
v___x_403_ = v_reuseFailAlloc_404_;
goto v_reusejp_402_;
}
v_reusejp_402_:
{
return v___x_403_;
}
}
else
{
lean_object* v_type_405_; lean_object* v_u_406_; lean_object* v_ringInst_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v_expectedInst_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; 
lean_del_object(v___x_397_);
v_type_405_ = lean_ctor_get(v_toRing_399_, 1);
lean_inc_ref_n(v_type_405_, 2);
v_u_406_ = lean_ctor_get(v_toRing_399_, 2);
lean_inc_n(v_u_406_, 2);
v_ringInst_407_ = lean_ctor_get(v_toRing_399_, 3);
lean_inc_ref(v_ringInst_407_);
lean_dec_ref(v_toRing_399_);
v___x_408_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0___closed__4));
v___x_409_ = lean_box(0);
v___x_410_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_410_, 0, v_u_406_);
lean_ctor_set(v___x_410_, 1, v___x_409_);
v___x_411_ = l_Lean_mkConst(v___x_408_, v___x_410_);
v_expectedInst_412_ = l_Lean_mkAppB(v___x_411_, v_type_405_, v_ringInst_407_);
v___x_413_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0___closed__5));
v___x_414_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__11));
v___x_415_ = l_Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1(v_type_405_, v_u_406_, v___x_413_, v___x_414_, v_expectedInst_412_, v___y_382_, v___y_383_, v___y_384_, v___y_385_, v___y_386_, v___y_387_, v___y_388_, v___y_389_, v___y_390_, v___y_391_, v___y_392_);
if (lean_obj_tag(v___x_415_) == 0)
{
lean_object* v_a_416_; lean_object* v___f_417_; lean_object* v___x_418_; 
v_a_416_ = lean_ctor_get(v___x_415_, 0);
lean_inc_n(v_a_416_, 2);
lean_dec_ref_known(v___x_415_, 1);
v___f_417_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0___lam__0), 2, 1);
lean_closure_set(v___f_417_, 0, v_a_416_);
v___x_418_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(v___f_417_, v___y_382_, v___y_383_);
if (lean_obj_tag(v___x_418_) == 0)
{
lean_object* v___x_420_; uint8_t v_isShared_421_; uint8_t v_isSharedCheck_425_; 
v_isSharedCheck_425_ = !lean_is_exclusive(v___x_418_);
if (v_isSharedCheck_425_ == 0)
{
lean_object* v_unused_426_; 
v_unused_426_ = lean_ctor_get(v___x_418_, 0);
lean_dec(v_unused_426_);
v___x_420_ = v___x_418_;
v_isShared_421_ = v_isSharedCheck_425_;
goto v_resetjp_419_;
}
else
{
lean_dec(v___x_418_);
v___x_420_ = lean_box(0);
v_isShared_421_ = v_isSharedCheck_425_;
goto v_resetjp_419_;
}
v_resetjp_419_:
{
lean_object* v___x_423_; 
if (v_isShared_421_ == 0)
{
lean_ctor_set(v___x_420_, 0, v_a_416_);
v___x_423_ = v___x_420_;
goto v_reusejp_422_;
}
else
{
lean_object* v_reuseFailAlloc_424_; 
v_reuseFailAlloc_424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_424_, 0, v_a_416_);
v___x_423_ = v_reuseFailAlloc_424_;
goto v_reusejp_422_;
}
v_reusejp_422_:
{
return v___x_423_;
}
}
}
else
{
lean_object* v_a_427_; lean_object* v___x_429_; uint8_t v_isShared_430_; uint8_t v_isSharedCheck_434_; 
lean_dec(v_a_416_);
v_a_427_ = lean_ctor_get(v___x_418_, 0);
v_isSharedCheck_434_ = !lean_is_exclusive(v___x_418_);
if (v_isSharedCheck_434_ == 0)
{
v___x_429_ = v___x_418_;
v_isShared_430_ = v_isSharedCheck_434_;
goto v_resetjp_428_;
}
else
{
lean_inc(v_a_427_);
lean_dec(v___x_418_);
v___x_429_ = lean_box(0);
v_isShared_430_ = v_isSharedCheck_434_;
goto v_resetjp_428_;
}
v_resetjp_428_:
{
lean_object* v___x_432_; 
if (v_isShared_430_ == 0)
{
v___x_432_ = v___x_429_;
goto v_reusejp_431_;
}
else
{
lean_object* v_reuseFailAlloc_433_; 
v_reuseFailAlloc_433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_433_, 0, v_a_427_);
v___x_432_ = v_reuseFailAlloc_433_;
goto v_reusejp_431_;
}
v_reusejp_431_:
{
return v___x_432_;
}
}
}
}
else
{
return v___x_415_;
}
}
}
}
else
{
lean_object* v_a_436_; lean_object* v___x_438_; uint8_t v_isShared_439_; uint8_t v_isSharedCheck_443_; 
v_a_436_ = lean_ctor_get(v___x_394_, 0);
v_isSharedCheck_443_ = !lean_is_exclusive(v___x_394_);
if (v_isSharedCheck_443_ == 0)
{
v___x_438_ = v___x_394_;
v_isShared_439_ = v_isSharedCheck_443_;
goto v_resetjp_437_;
}
else
{
lean_inc(v_a_436_);
lean_dec(v___x_394_);
v___x_438_ = lean_box(0);
v_isShared_439_ = v_isSharedCheck_443_;
goto v_resetjp_437_;
}
v_resetjp_437_:
{
lean_object* v___x_441_; 
if (v_isShared_439_ == 0)
{
v___x_441_ = v___x_438_;
goto v_reusejp_440_;
}
else
{
lean_object* v_reuseFailAlloc_442_; 
v_reuseFailAlloc_442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_442_, 0, v_a_436_);
v___x_441_ = v_reuseFailAlloc_442_;
goto v_reusejp_440_;
}
v_reusejp_440_:
{
return v___x_441_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0___boxed(lean_object* v___y_444_, lean_object* v___y_445_, lean_object* v___y_446_, lean_object* v___y_447_, lean_object* v___y_448_, lean_object* v___y_449_, lean_object* v___y_450_, lean_object* v___y_451_, lean_object* v___y_452_, lean_object* v___y_453_, lean_object* v___y_454_, lean_object* v___y_455_){
_start:
{
lean_object* v_res_456_; 
v_res_456_ = l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0(v___y_444_, v___y_445_, v___y_446_, v___y_447_, v___y_448_, v___y_449_, v___y_450_, v___y_451_, v___y_452_, v___y_453_, v___y_454_);
lean_dec(v___y_454_);
lean_dec_ref(v___y_453_);
lean_dec(v___y_452_);
lean_dec_ref(v___y_451_);
lean_dec(v___y_450_);
lean_dec_ref(v___y_449_);
lean_dec(v___y_448_);
lean_dec_ref(v___y_447_);
lean_dec(v___y_446_);
lean_dec(v___y_445_);
lean_dec_ref(v___y_444_);
return v_res_456_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0(lean_object* v_inst_457_, lean_object* v___y_458_, lean_object* v___y_459_, lean_object* v___y_460_, lean_object* v___y_461_, lean_object* v___y_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_, lean_object* v___y_468_){
_start:
{
lean_object* v___x_470_; 
v___x_470_ = l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0(v___y_458_, v___y_459_, v___y_460_, v___y_461_, v___y_462_, v___y_463_, v___y_464_, v___y_465_, v___y_466_, v___y_467_, v___y_468_);
if (lean_obj_tag(v___x_470_) == 0)
{
lean_object* v_a_471_; lean_object* v___x_473_; uint8_t v_isShared_474_; uint8_t v_isSharedCheck_483_; 
v_a_471_ = lean_ctor_get(v___x_470_, 0);
v_isSharedCheck_483_ = !lean_is_exclusive(v___x_470_);
if (v_isSharedCheck_483_ == 0)
{
v___x_473_ = v___x_470_;
v_isShared_474_ = v_isSharedCheck_483_;
goto v_resetjp_472_;
}
else
{
lean_inc(v_a_471_);
lean_dec(v___x_470_);
v___x_473_ = lean_box(0);
v_isShared_474_ = v_isSharedCheck_483_;
goto v_resetjp_472_;
}
v_resetjp_472_:
{
lean_object* v___x_475_; size_t v___x_476_; size_t v___x_477_; uint8_t v___x_478_; lean_object* v___x_479_; lean_object* v___x_481_; 
v___x_475_ = l_Lean_Expr_appArg_x21(v_a_471_);
lean_dec(v_a_471_);
v___x_476_ = lean_ptr_addr(v___x_475_);
lean_dec_ref(v___x_475_);
v___x_477_ = lean_ptr_addr(v_inst_457_);
v___x_478_ = lean_usize_dec_eq(v___x_476_, v___x_477_);
v___x_479_ = lean_box(v___x_478_);
if (v_isShared_474_ == 0)
{
lean_ctor_set(v___x_473_, 0, v___x_479_);
v___x_481_ = v___x_473_;
goto v_reusejp_480_;
}
else
{
lean_object* v_reuseFailAlloc_482_; 
v_reuseFailAlloc_482_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_482_, 0, v___x_479_);
v___x_481_ = v_reuseFailAlloc_482_;
goto v_reusejp_480_;
}
v_reusejp_480_:
{
return v___x_481_;
}
}
}
else
{
lean_object* v_a_484_; lean_object* v___x_486_; uint8_t v_isShared_487_; uint8_t v_isSharedCheck_491_; 
v_a_484_ = lean_ctor_get(v___x_470_, 0);
v_isSharedCheck_491_ = !lean_is_exclusive(v___x_470_);
if (v_isSharedCheck_491_ == 0)
{
v___x_486_ = v___x_470_;
v_isShared_487_ = v_isSharedCheck_491_;
goto v_resetjp_485_;
}
else
{
lean_inc(v_a_484_);
lean_dec(v___x_470_);
v___x_486_ = lean_box(0);
v_isShared_487_ = v_isSharedCheck_491_;
goto v_resetjp_485_;
}
v_resetjp_485_:
{
lean_object* v___x_489_; 
if (v_isShared_487_ == 0)
{
v___x_489_ = v___x_486_;
goto v_reusejp_488_;
}
else
{
lean_object* v_reuseFailAlloc_490_; 
v_reuseFailAlloc_490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_490_, 0, v_a_484_);
v___x_489_ = v_reuseFailAlloc_490_;
goto v_reusejp_488_;
}
v_reusejp_488_:
{
return v___x_489_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0___boxed(lean_object* v_inst_492_, lean_object* v___y_493_, lean_object* v___y_494_, lean_object* v___y_495_, lean_object* v___y_496_, lean_object* v___y_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_){
_start:
{
lean_object* v_res_505_; 
v_res_505_ = l_Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0(v_inst_492_, v___y_493_, v___y_494_, v___y_495_, v___y_496_, v___y_497_, v___y_498_, v___y_499_, v___y_500_, v___y_501_, v___y_502_, v___y_503_);
lean_dec(v___y_503_);
lean_dec_ref(v___y_502_);
lean_dec(v___y_501_);
lean_dec_ref(v___y_500_);
lean_dec(v___y_499_);
lean_dec_ref(v___y_498_);
lean_dec(v___y_497_);
lean_dec_ref(v___y_496_);
lean_dec(v___y_495_);
lean_dec(v___y_494_);
lean_dec_ref(v___y_493_);
lean_dec_ref(v_inst_492_);
return v_res_505_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isIntCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__1_spec__2___lam__0(lean_object* v_a_506_, lean_object* v_s_507_){
_start:
{
lean_object* v_toRing_508_; lean_object* v_invFn_x3f_509_; lean_object* v_semiringId_x3f_510_; lean_object* v_commSemiringInst_511_; lean_object* v_commRingInst_512_; lean_object* v_noZeroDivInst_x3f_513_; lean_object* v_fieldInst_x3f_514_; lean_object* v_powIdentityInst_x3f_515_; lean_object* v_denoteEntries_516_; lean_object* v_nextId_517_; lean_object* v_steps_518_; lean_object* v_queue_519_; lean_object* v_basis_520_; lean_object* v_diseqs_521_; uint8_t v_recheck_522_; lean_object* v_invSet_523_; lean_object* v_powIdentityVarCount_524_; lean_object* v_numEq0_x3f_525_; uint8_t v_numEq0Updated_526_; lean_object* v___x_528_; uint8_t v_isShared_529_; uint8_t v_isSharedCheck_558_; 
v_toRing_508_ = lean_ctor_get(v_s_507_, 0);
v_invFn_x3f_509_ = lean_ctor_get(v_s_507_, 1);
v_semiringId_x3f_510_ = lean_ctor_get(v_s_507_, 2);
v_commSemiringInst_511_ = lean_ctor_get(v_s_507_, 3);
v_commRingInst_512_ = lean_ctor_get(v_s_507_, 4);
v_noZeroDivInst_x3f_513_ = lean_ctor_get(v_s_507_, 5);
v_fieldInst_x3f_514_ = lean_ctor_get(v_s_507_, 6);
v_powIdentityInst_x3f_515_ = lean_ctor_get(v_s_507_, 7);
v_denoteEntries_516_ = lean_ctor_get(v_s_507_, 8);
v_nextId_517_ = lean_ctor_get(v_s_507_, 9);
v_steps_518_ = lean_ctor_get(v_s_507_, 10);
v_queue_519_ = lean_ctor_get(v_s_507_, 11);
v_basis_520_ = lean_ctor_get(v_s_507_, 12);
v_diseqs_521_ = lean_ctor_get(v_s_507_, 13);
v_recheck_522_ = lean_ctor_get_uint8(v_s_507_, sizeof(void*)*17);
v_invSet_523_ = lean_ctor_get(v_s_507_, 14);
v_powIdentityVarCount_524_ = lean_ctor_get(v_s_507_, 15);
v_numEq0_x3f_525_ = lean_ctor_get(v_s_507_, 16);
v_numEq0Updated_526_ = lean_ctor_get_uint8(v_s_507_, sizeof(void*)*17 + 1);
v_isSharedCheck_558_ = !lean_is_exclusive(v_s_507_);
if (v_isSharedCheck_558_ == 0)
{
v___x_528_ = v_s_507_;
v_isShared_529_ = v_isSharedCheck_558_;
goto v_resetjp_527_;
}
else
{
lean_inc(v_numEq0_x3f_525_);
lean_inc(v_powIdentityVarCount_524_);
lean_inc(v_invSet_523_);
lean_inc(v_diseqs_521_);
lean_inc(v_basis_520_);
lean_inc(v_queue_519_);
lean_inc(v_steps_518_);
lean_inc(v_nextId_517_);
lean_inc(v_denoteEntries_516_);
lean_inc(v_powIdentityInst_x3f_515_);
lean_inc(v_fieldInst_x3f_514_);
lean_inc(v_noZeroDivInst_x3f_513_);
lean_inc(v_commRingInst_512_);
lean_inc(v_commSemiringInst_511_);
lean_inc(v_semiringId_x3f_510_);
lean_inc(v_invFn_x3f_509_);
lean_inc(v_toRing_508_);
lean_dec(v_s_507_);
v___x_528_ = lean_box(0);
v_isShared_529_ = v_isSharedCheck_558_;
goto v_resetjp_527_;
}
v_resetjp_527_:
{
lean_object* v_id_530_; lean_object* v_type_531_; lean_object* v_u_532_; lean_object* v_ringInst_533_; lean_object* v_semiringInst_534_; lean_object* v_charInst_x3f_535_; lean_object* v_addFn_x3f_536_; lean_object* v_mulFn_x3f_537_; lean_object* v_subFn_x3f_538_; lean_object* v_negFn_x3f_539_; lean_object* v_powFn_x3f_540_; lean_object* v_natCastFn_x3f_541_; lean_object* v_one_x3f_542_; lean_object* v_vars_543_; lean_object* v_varMap_544_; lean_object* v_denote_545_; lean_object* v___x_547_; uint8_t v_isShared_548_; uint8_t v_isSharedCheck_556_; 
v_id_530_ = lean_ctor_get(v_toRing_508_, 0);
v_type_531_ = lean_ctor_get(v_toRing_508_, 1);
v_u_532_ = lean_ctor_get(v_toRing_508_, 2);
v_ringInst_533_ = lean_ctor_get(v_toRing_508_, 3);
v_semiringInst_534_ = lean_ctor_get(v_toRing_508_, 4);
v_charInst_x3f_535_ = lean_ctor_get(v_toRing_508_, 5);
v_addFn_x3f_536_ = lean_ctor_get(v_toRing_508_, 6);
v_mulFn_x3f_537_ = lean_ctor_get(v_toRing_508_, 7);
v_subFn_x3f_538_ = lean_ctor_get(v_toRing_508_, 8);
v_negFn_x3f_539_ = lean_ctor_get(v_toRing_508_, 9);
v_powFn_x3f_540_ = lean_ctor_get(v_toRing_508_, 10);
v_natCastFn_x3f_541_ = lean_ctor_get(v_toRing_508_, 12);
v_one_x3f_542_ = lean_ctor_get(v_toRing_508_, 13);
v_vars_543_ = lean_ctor_get(v_toRing_508_, 14);
v_varMap_544_ = lean_ctor_get(v_toRing_508_, 15);
v_denote_545_ = lean_ctor_get(v_toRing_508_, 16);
v_isSharedCheck_556_ = !lean_is_exclusive(v_toRing_508_);
if (v_isSharedCheck_556_ == 0)
{
lean_object* v_unused_557_; 
v_unused_557_ = lean_ctor_get(v_toRing_508_, 11);
lean_dec(v_unused_557_);
v___x_547_ = v_toRing_508_;
v_isShared_548_ = v_isSharedCheck_556_;
goto v_resetjp_546_;
}
else
{
lean_inc(v_denote_545_);
lean_inc(v_varMap_544_);
lean_inc(v_vars_543_);
lean_inc(v_one_x3f_542_);
lean_inc(v_natCastFn_x3f_541_);
lean_inc(v_powFn_x3f_540_);
lean_inc(v_negFn_x3f_539_);
lean_inc(v_subFn_x3f_538_);
lean_inc(v_mulFn_x3f_537_);
lean_inc(v_addFn_x3f_536_);
lean_inc(v_charInst_x3f_535_);
lean_inc(v_semiringInst_534_);
lean_inc(v_ringInst_533_);
lean_inc(v_u_532_);
lean_inc(v_type_531_);
lean_inc(v_id_530_);
lean_dec(v_toRing_508_);
v___x_547_ = lean_box(0);
v_isShared_548_ = v_isSharedCheck_556_;
goto v_resetjp_546_;
}
v_resetjp_546_:
{
lean_object* v___x_549_; lean_object* v___x_551_; 
v___x_549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_549_, 0, v_a_506_);
if (v_isShared_548_ == 0)
{
lean_ctor_set(v___x_547_, 11, v___x_549_);
v___x_551_ = v___x_547_;
goto v_reusejp_550_;
}
else
{
lean_object* v_reuseFailAlloc_555_; 
v_reuseFailAlloc_555_ = lean_alloc_ctor(0, 17, 0);
lean_ctor_set(v_reuseFailAlloc_555_, 0, v_id_530_);
lean_ctor_set(v_reuseFailAlloc_555_, 1, v_type_531_);
lean_ctor_set(v_reuseFailAlloc_555_, 2, v_u_532_);
lean_ctor_set(v_reuseFailAlloc_555_, 3, v_ringInst_533_);
lean_ctor_set(v_reuseFailAlloc_555_, 4, v_semiringInst_534_);
lean_ctor_set(v_reuseFailAlloc_555_, 5, v_charInst_x3f_535_);
lean_ctor_set(v_reuseFailAlloc_555_, 6, v_addFn_x3f_536_);
lean_ctor_set(v_reuseFailAlloc_555_, 7, v_mulFn_x3f_537_);
lean_ctor_set(v_reuseFailAlloc_555_, 8, v_subFn_x3f_538_);
lean_ctor_set(v_reuseFailAlloc_555_, 9, v_negFn_x3f_539_);
lean_ctor_set(v_reuseFailAlloc_555_, 10, v_powFn_x3f_540_);
lean_ctor_set(v_reuseFailAlloc_555_, 11, v___x_549_);
lean_ctor_set(v_reuseFailAlloc_555_, 12, v_natCastFn_x3f_541_);
lean_ctor_set(v_reuseFailAlloc_555_, 13, v_one_x3f_542_);
lean_ctor_set(v_reuseFailAlloc_555_, 14, v_vars_543_);
lean_ctor_set(v_reuseFailAlloc_555_, 15, v_varMap_544_);
lean_ctor_set(v_reuseFailAlloc_555_, 16, v_denote_545_);
v___x_551_ = v_reuseFailAlloc_555_;
goto v_reusejp_550_;
}
v_reusejp_550_:
{
lean_object* v___x_553_; 
if (v_isShared_529_ == 0)
{
lean_ctor_set(v___x_528_, 0, v___x_551_);
v___x_553_ = v___x_528_;
goto v_reusejp_552_;
}
else
{
lean_object* v_reuseFailAlloc_554_; 
v_reuseFailAlloc_554_ = lean_alloc_ctor(0, 17, 2);
lean_ctor_set(v_reuseFailAlloc_554_, 0, v___x_551_);
lean_ctor_set(v_reuseFailAlloc_554_, 1, v_invFn_x3f_509_);
lean_ctor_set(v_reuseFailAlloc_554_, 2, v_semiringId_x3f_510_);
lean_ctor_set(v_reuseFailAlloc_554_, 3, v_commSemiringInst_511_);
lean_ctor_set(v_reuseFailAlloc_554_, 4, v_commRingInst_512_);
lean_ctor_set(v_reuseFailAlloc_554_, 5, v_noZeroDivInst_x3f_513_);
lean_ctor_set(v_reuseFailAlloc_554_, 6, v_fieldInst_x3f_514_);
lean_ctor_set(v_reuseFailAlloc_554_, 7, v_powIdentityInst_x3f_515_);
lean_ctor_set(v_reuseFailAlloc_554_, 8, v_denoteEntries_516_);
lean_ctor_set(v_reuseFailAlloc_554_, 9, v_nextId_517_);
lean_ctor_set(v_reuseFailAlloc_554_, 10, v_steps_518_);
lean_ctor_set(v_reuseFailAlloc_554_, 11, v_queue_519_);
lean_ctor_set(v_reuseFailAlloc_554_, 12, v_basis_520_);
lean_ctor_set(v_reuseFailAlloc_554_, 13, v_diseqs_521_);
lean_ctor_set(v_reuseFailAlloc_554_, 14, v_invSet_523_);
lean_ctor_set(v_reuseFailAlloc_554_, 15, v_powIdentityVarCount_524_);
lean_ctor_set(v_reuseFailAlloc_554_, 16, v_numEq0_x3f_525_);
lean_ctor_set_uint8(v_reuseFailAlloc_554_, sizeof(void*)*17, v_recheck_522_);
lean_ctor_set_uint8(v_reuseFailAlloc_554_, sizeof(void*)*17 + 1, v_numEq0Updated_526_);
v___x_553_ = v_reuseFailAlloc_554_;
goto v_reusejp_552_;
}
v_reusejp_552_:
{
return v___x_553_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isIntCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__1_spec__2(lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_){
_start:
{
lean_object* v___y_583_; lean_object* v___y_584_; lean_object* v___y_585_; lean_object* v___x_605_; 
v___x_605_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v___y_570_, v___y_571_, v___y_572_, v___y_573_, v___y_574_, v___y_575_, v___y_576_, v___y_577_, v___y_578_, v___y_579_, v___y_580_);
if (lean_obj_tag(v___x_605_) == 0)
{
lean_object* v_a_606_; lean_object* v___x_608_; uint8_t v_isShared_609_; uint8_t v_isSharedCheck_664_; 
v_a_606_ = lean_ctor_get(v___x_605_, 0);
v_isSharedCheck_664_ = !lean_is_exclusive(v___x_605_);
if (v_isSharedCheck_664_ == 0)
{
v___x_608_ = v___x_605_;
v_isShared_609_ = v_isSharedCheck_664_;
goto v_resetjp_607_;
}
else
{
lean_inc(v_a_606_);
lean_dec(v___x_605_);
v___x_608_ = lean_box(0);
v_isShared_609_ = v_isSharedCheck_664_;
goto v_resetjp_607_;
}
v_resetjp_607_:
{
lean_object* v_toRing_610_; lean_object* v_intCastFn_x3f_611_; 
v_toRing_610_ = lean_ctor_get(v_a_606_, 0);
lean_inc_ref(v_toRing_610_);
lean_dec(v_a_606_);
v_intCastFn_x3f_611_ = lean_ctor_get(v_toRing_610_, 11);
if (lean_obj_tag(v_intCastFn_x3f_611_) == 1)
{
lean_object* v_val_612_; lean_object* v___x_614_; 
lean_inc_ref(v_intCastFn_x3f_611_);
lean_dec_ref(v_toRing_610_);
v_val_612_ = lean_ctor_get(v_intCastFn_x3f_611_, 0);
lean_inc(v_val_612_);
lean_dec_ref_known(v_intCastFn_x3f_611_, 1);
if (v_isShared_609_ == 0)
{
lean_ctor_set(v___x_608_, 0, v_val_612_);
v___x_614_ = v___x_608_;
goto v_reusejp_613_;
}
else
{
lean_object* v_reuseFailAlloc_615_; 
v_reuseFailAlloc_615_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_615_, 0, v_val_612_);
v___x_614_ = v_reuseFailAlloc_615_;
goto v_reusejp_613_;
}
v_reusejp_613_:
{
return v___x_614_;
}
}
else
{
lean_object* v_type_616_; lean_object* v_u_617_; lean_object* v_ringInst_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v_inst_x27_623_; lean_object* v_inst_625_; lean_object* v___y_626_; lean_object* v___y_627_; lean_object* v___y_628_; lean_object* v___y_629_; lean_object* v___y_630_; lean_object* v___y_631_; lean_object* v___y_632_; lean_object* v___y_633_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v_instType_642_; lean_object* v___x_643_; 
lean_del_object(v___x_608_);
v_type_616_ = lean_ctor_get(v_toRing_610_, 1);
lean_inc_ref_n(v_type_616_, 3);
v_u_617_ = lean_ctor_get(v_toRing_610_, 2);
lean_inc(v_u_617_);
v_ringInst_618_ = lean_ctor_get(v_toRing_610_, 3);
lean_inc_ref(v_ringInst_618_);
lean_dec_ref(v_toRing_610_);
v___x_619_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isIntCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__1_spec__2___closed__0));
v___x_620_ = lean_box(0);
v___x_621_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_621_, 0, v_u_617_);
lean_ctor_set(v___x_621_, 1, v___x_620_);
lean_inc_ref_n(v___x_621_, 2);
v___x_622_ = l_Lean_mkConst(v___x_619_, v___x_621_);
v_inst_x27_623_ = l_Lean_mkAppB(v___x_622_, v_type_616_, v_ringInst_618_);
v___x_640_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isIntCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__1_spec__2___closed__1));
v___x_641_ = l_Lean_mkConst(v___x_640_, v___x_621_);
v_instType_642_ = l_Lean_Expr_app___override(v___x_641_, v_type_616_);
v___x_643_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v_instType_642_, v___y_576_, v___y_577_, v___y_578_, v___y_579_, v___y_580_);
if (lean_obj_tag(v___x_643_) == 0)
{
lean_object* v_a_644_; 
v_a_644_ = lean_ctor_get(v___x_643_, 0);
lean_inc(v_a_644_);
lean_dec_ref_known(v___x_643_, 1);
if (lean_obj_tag(v_a_644_) == 0)
{
v_inst_625_ = v_inst_x27_623_;
v___y_626_ = v___y_570_;
v___y_627_ = v___y_571_;
v___y_628_ = v___y_575_;
v___y_629_ = v___y_576_;
v___y_630_ = v___y_577_;
v___y_631_ = v___y_578_;
v___y_632_ = v___y_579_;
v___y_633_ = v___y_580_;
goto v___jp_624_;
}
else
{
lean_object* v_val_645_; lean_object* v___x_646_; lean_object* v___x_647_; 
v_val_645_ = lean_ctor_get(v_a_644_, 0);
lean_inc_n(v_val_645_, 2);
lean_dec_ref_known(v_a_644_, 1);
v___x_646_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isIntCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__1_spec__2___closed__3));
v___x_647_ = l_Lean_Meta_Grind_Arith_CommRing_checkInst(v___x_646_, v_val_645_, v_inst_x27_623_, v___y_577_, v___y_578_, v___y_579_, v___y_580_);
if (lean_obj_tag(v___x_647_) == 0)
{
lean_dec_ref_known(v___x_647_, 1);
v_inst_625_ = v_val_645_;
v___y_626_ = v___y_570_;
v___y_627_ = v___y_571_;
v___y_628_ = v___y_575_;
v___y_629_ = v___y_576_;
v___y_630_ = v___y_577_;
v___y_631_ = v___y_578_;
v___y_632_ = v___y_579_;
v___y_633_ = v___y_580_;
goto v___jp_624_;
}
else
{
lean_object* v_a_648_; lean_object* v___x_650_; uint8_t v_isShared_651_; uint8_t v_isSharedCheck_655_; 
lean_dec(v_val_645_);
lean_dec_ref_known(v___x_621_, 2);
lean_dec_ref(v_type_616_);
v_a_648_ = lean_ctor_get(v___x_647_, 0);
v_isSharedCheck_655_ = !lean_is_exclusive(v___x_647_);
if (v_isSharedCheck_655_ == 0)
{
v___x_650_ = v___x_647_;
v_isShared_651_ = v_isSharedCheck_655_;
goto v_resetjp_649_;
}
else
{
lean_inc(v_a_648_);
lean_dec(v___x_647_);
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
}
}
else
{
lean_object* v_a_656_; lean_object* v___x_658_; uint8_t v_isShared_659_; uint8_t v_isSharedCheck_663_; 
lean_dec_ref(v_inst_x27_623_);
lean_dec_ref_known(v___x_621_, 2);
lean_dec_ref(v_type_616_);
v_a_656_ = lean_ctor_get(v___x_643_, 0);
v_isSharedCheck_663_ = !lean_is_exclusive(v___x_643_);
if (v_isSharedCheck_663_ == 0)
{
v___x_658_ = v___x_643_;
v_isShared_659_ = v_isSharedCheck_663_;
goto v_resetjp_657_;
}
else
{
lean_inc(v_a_656_);
lean_dec(v___x_643_);
v___x_658_ = lean_box(0);
v_isShared_659_ = v_isSharedCheck_663_;
goto v_resetjp_657_;
}
v_resetjp_657_:
{
lean_object* v___x_661_; 
if (v_isShared_659_ == 0)
{
v___x_661_ = v___x_658_;
goto v_reusejp_660_;
}
else
{
lean_object* v_reuseFailAlloc_662_; 
v_reuseFailAlloc_662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_662_, 0, v_a_656_);
v___x_661_ = v_reuseFailAlloc_662_;
goto v_reusejp_660_;
}
v_reusejp_660_:
{
return v___x_661_;
}
}
}
v___jp_624_:
{
lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; 
v___x_634_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__2));
v___x_635_ = l_Lean_mkConst(v___x_634_, v___x_621_);
v___x_636_ = l_Lean_mkAppB(v___x_635_, v_type_616_, v_inst_625_);
v___x_637_ = l_Lean_Meta_Sym_canon(v___x_636_, v___y_628_, v___y_629_, v___y_630_, v___y_631_, v___y_632_, v___y_633_);
if (lean_obj_tag(v___x_637_) == 0)
{
lean_object* v_a_638_; lean_object* v___x_639_; 
v_a_638_ = lean_ctor_get(v___x_637_, 0);
lean_inc(v_a_638_);
lean_dec_ref_known(v___x_637_, 1);
v___x_639_ = l_Lean_Meta_Sym_shareCommon(v_a_638_, v___y_628_, v___y_629_, v___y_630_, v___y_631_, v___y_632_, v___y_633_);
v___y_583_ = v___y_626_;
v___y_584_ = v___y_627_;
v___y_585_ = v___x_639_;
goto v___jp_582_;
}
else
{
v___y_583_ = v___y_626_;
v___y_584_ = v___y_627_;
v___y_585_ = v___x_637_;
goto v___jp_582_;
}
}
}
}
}
else
{
lean_object* v_a_665_; lean_object* v___x_667_; uint8_t v_isShared_668_; uint8_t v_isSharedCheck_672_; 
v_a_665_ = lean_ctor_get(v___x_605_, 0);
v_isSharedCheck_672_ = !lean_is_exclusive(v___x_605_);
if (v_isSharedCheck_672_ == 0)
{
v___x_667_ = v___x_605_;
v_isShared_668_ = v_isSharedCheck_672_;
goto v_resetjp_666_;
}
else
{
lean_inc(v_a_665_);
lean_dec(v___x_605_);
v___x_667_ = lean_box(0);
v_isShared_668_ = v_isSharedCheck_672_;
goto v_resetjp_666_;
}
v_resetjp_666_:
{
lean_object* v___x_670_; 
if (v_isShared_668_ == 0)
{
v___x_670_ = v___x_667_;
goto v_reusejp_669_;
}
else
{
lean_object* v_reuseFailAlloc_671_; 
v_reuseFailAlloc_671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_671_, 0, v_a_665_);
v___x_670_ = v_reuseFailAlloc_671_;
goto v_reusejp_669_;
}
v_reusejp_669_:
{
return v___x_670_;
}
}
}
v___jp_582_:
{
if (lean_obj_tag(v___y_585_) == 0)
{
lean_object* v_a_586_; lean_object* v___f_587_; lean_object* v___x_588_; 
v_a_586_ = lean_ctor_get(v___y_585_, 0);
lean_inc_n(v_a_586_, 2);
lean_dec_ref_known(v___y_585_, 1);
v___f_587_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isIntCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__1_spec__2___lam__0), 2, 1);
lean_closure_set(v___f_587_, 0, v_a_586_);
v___x_588_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(v___f_587_, v___y_583_, v___y_584_);
if (lean_obj_tag(v___x_588_) == 0)
{
lean_object* v___x_590_; uint8_t v_isShared_591_; uint8_t v_isSharedCheck_595_; 
v_isSharedCheck_595_ = !lean_is_exclusive(v___x_588_);
if (v_isSharedCheck_595_ == 0)
{
lean_object* v_unused_596_; 
v_unused_596_ = lean_ctor_get(v___x_588_, 0);
lean_dec(v_unused_596_);
v___x_590_ = v___x_588_;
v_isShared_591_ = v_isSharedCheck_595_;
goto v_resetjp_589_;
}
else
{
lean_dec(v___x_588_);
v___x_590_ = lean_box(0);
v_isShared_591_ = v_isSharedCheck_595_;
goto v_resetjp_589_;
}
v_resetjp_589_:
{
lean_object* v___x_593_; 
if (v_isShared_591_ == 0)
{
lean_ctor_set(v___x_590_, 0, v_a_586_);
v___x_593_ = v___x_590_;
goto v_reusejp_592_;
}
else
{
lean_object* v_reuseFailAlloc_594_; 
v_reuseFailAlloc_594_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_594_, 0, v_a_586_);
v___x_593_ = v_reuseFailAlloc_594_;
goto v_reusejp_592_;
}
v_reusejp_592_:
{
return v___x_593_;
}
}
}
else
{
lean_object* v_a_597_; lean_object* v___x_599_; uint8_t v_isShared_600_; uint8_t v_isSharedCheck_604_; 
lean_dec(v_a_586_);
v_a_597_ = lean_ctor_get(v___x_588_, 0);
v_isSharedCheck_604_ = !lean_is_exclusive(v___x_588_);
if (v_isSharedCheck_604_ == 0)
{
v___x_599_ = v___x_588_;
v_isShared_600_ = v_isSharedCheck_604_;
goto v_resetjp_598_;
}
else
{
lean_inc(v_a_597_);
lean_dec(v___x_588_);
v___x_599_ = lean_box(0);
v_isShared_600_ = v_isSharedCheck_604_;
goto v_resetjp_598_;
}
v_resetjp_598_:
{
lean_object* v___x_602_; 
if (v_isShared_600_ == 0)
{
v___x_602_ = v___x_599_;
goto v_reusejp_601_;
}
else
{
lean_object* v_reuseFailAlloc_603_; 
v_reuseFailAlloc_603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_603_, 0, v_a_597_);
v___x_602_ = v_reuseFailAlloc_603_;
goto v_reusejp_601_;
}
v_reusejp_601_:
{
return v___x_602_;
}
}
}
}
else
{
return v___y_585_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isIntCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__1_spec__2___boxed(lean_object* v___y_673_, lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_, lean_object* v___y_677_, lean_object* v___y_678_, lean_object* v___y_679_, lean_object* v___y_680_, lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_){
_start:
{
lean_object* v_res_685_; 
v_res_685_ = l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isIntCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__1_spec__2(v___y_673_, v___y_674_, v___y_675_, v___y_676_, v___y_677_, v___y_678_, v___y_679_, v___y_680_, v___y_681_, v___y_682_, v___y_683_);
lean_dec(v___y_683_);
lean_dec_ref(v___y_682_);
lean_dec(v___y_681_);
lean_dec_ref(v___y_680_);
lean_dec(v___y_679_);
lean_dec_ref(v___y_678_);
lean_dec(v___y_677_);
lean_dec_ref(v___y_676_);
lean_dec(v___y_675_);
lean_dec(v___y_674_);
lean_dec_ref(v___y_673_);
return v_res_685_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_isIntCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__1(lean_object* v_inst_686_, lean_object* v___y_687_, lean_object* v___y_688_, lean_object* v___y_689_, lean_object* v___y_690_, lean_object* v___y_691_, lean_object* v___y_692_, lean_object* v___y_693_, lean_object* v___y_694_, lean_object* v___y_695_, lean_object* v___y_696_, lean_object* v___y_697_){
_start:
{
lean_object* v___x_699_; 
v___x_699_ = l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isIntCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__1_spec__2(v___y_687_, v___y_688_, v___y_689_, v___y_690_, v___y_691_, v___y_692_, v___y_693_, v___y_694_, v___y_695_, v___y_696_, v___y_697_);
if (lean_obj_tag(v___x_699_) == 0)
{
lean_object* v_a_700_; lean_object* v___x_702_; uint8_t v_isShared_703_; uint8_t v_isSharedCheck_712_; 
v_a_700_ = lean_ctor_get(v___x_699_, 0);
v_isSharedCheck_712_ = !lean_is_exclusive(v___x_699_);
if (v_isSharedCheck_712_ == 0)
{
v___x_702_ = v___x_699_;
v_isShared_703_ = v_isSharedCheck_712_;
goto v_resetjp_701_;
}
else
{
lean_inc(v_a_700_);
lean_dec(v___x_699_);
v___x_702_ = lean_box(0);
v_isShared_703_ = v_isSharedCheck_712_;
goto v_resetjp_701_;
}
v_resetjp_701_:
{
lean_object* v___x_704_; size_t v___x_705_; size_t v___x_706_; uint8_t v___x_707_; lean_object* v___x_708_; lean_object* v___x_710_; 
v___x_704_ = l_Lean_Expr_appArg_x21(v_a_700_);
lean_dec(v_a_700_);
v___x_705_ = lean_ptr_addr(v___x_704_);
lean_dec_ref(v___x_704_);
v___x_706_ = lean_ptr_addr(v_inst_686_);
v___x_707_ = lean_usize_dec_eq(v___x_705_, v___x_706_);
v___x_708_ = lean_box(v___x_707_);
if (v_isShared_703_ == 0)
{
lean_ctor_set(v___x_702_, 0, v___x_708_);
v___x_710_ = v___x_702_;
goto v_reusejp_709_;
}
else
{
lean_object* v_reuseFailAlloc_711_; 
v_reuseFailAlloc_711_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_711_, 0, v___x_708_);
v___x_710_ = v_reuseFailAlloc_711_;
goto v_reusejp_709_;
}
v_reusejp_709_:
{
return v___x_710_;
}
}
}
else
{
lean_object* v_a_713_; lean_object* v___x_715_; uint8_t v_isShared_716_; uint8_t v_isSharedCheck_720_; 
v_a_713_ = lean_ctor_get(v___x_699_, 0);
v_isSharedCheck_720_ = !lean_is_exclusive(v___x_699_);
if (v_isSharedCheck_720_ == 0)
{
v___x_715_ = v___x_699_;
v_isShared_716_ = v_isSharedCheck_720_;
goto v_resetjp_714_;
}
else
{
lean_inc(v_a_713_);
lean_dec(v___x_699_);
v___x_715_ = lean_box(0);
v_isShared_716_ = v_isSharedCheck_720_;
goto v_resetjp_714_;
}
v_resetjp_714_:
{
lean_object* v___x_718_; 
if (v_isShared_716_ == 0)
{
v___x_718_ = v___x_715_;
goto v_reusejp_717_;
}
else
{
lean_object* v_reuseFailAlloc_719_; 
v_reuseFailAlloc_719_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_719_, 0, v_a_713_);
v___x_718_ = v_reuseFailAlloc_719_;
goto v_reusejp_717_;
}
v_reusejp_717_:
{
return v___x_718_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_isIntCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__1___boxed(lean_object* v_inst_721_, lean_object* v___y_722_, lean_object* v___y_723_, lean_object* v___y_724_, lean_object* v___y_725_, lean_object* v___y_726_, lean_object* v___y_727_, lean_object* v___y_728_, lean_object* v___y_729_, lean_object* v___y_730_, lean_object* v___y_731_, lean_object* v___y_732_, lean_object* v___y_733_){
_start:
{
lean_object* v_res_734_; 
v_res_734_ = l_Lean_Meta_Grind_Arith_CommRing_isIntCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__1(v_inst_721_, v___y_722_, v___y_723_, v___y_724_, v___y_725_, v___y_726_, v___y_727_, v___y_728_, v___y_729_, v___y_730_, v___y_731_, v___y_732_);
lean_dec(v___y_732_);
lean_dec_ref(v___y_731_);
lean_dec(v___y_730_);
lean_dec_ref(v___y_729_);
lean_dec(v___y_728_);
lean_dec_ref(v___y_727_);
lean_dec(v___y_726_);
lean_dec_ref(v___y_725_);
lean_dec(v___y_724_);
lean_dec(v___y_723_);
lean_dec_ref(v___y_722_);
lean_dec_ref(v_inst_721_);
return v_res_734_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isNatCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__2_spec__4___lam__0(lean_object* v_a_735_, lean_object* v_s_736_){
_start:
{
lean_object* v_toRing_737_; lean_object* v_invFn_x3f_738_; lean_object* v_semiringId_x3f_739_; lean_object* v_commSemiringInst_740_; lean_object* v_commRingInst_741_; lean_object* v_noZeroDivInst_x3f_742_; lean_object* v_fieldInst_x3f_743_; lean_object* v_powIdentityInst_x3f_744_; lean_object* v_denoteEntries_745_; lean_object* v_nextId_746_; lean_object* v_steps_747_; lean_object* v_queue_748_; lean_object* v_basis_749_; lean_object* v_diseqs_750_; uint8_t v_recheck_751_; lean_object* v_invSet_752_; lean_object* v_powIdentityVarCount_753_; lean_object* v_numEq0_x3f_754_; uint8_t v_numEq0Updated_755_; lean_object* v___x_757_; uint8_t v_isShared_758_; uint8_t v_isSharedCheck_787_; 
v_toRing_737_ = lean_ctor_get(v_s_736_, 0);
v_invFn_x3f_738_ = lean_ctor_get(v_s_736_, 1);
v_semiringId_x3f_739_ = lean_ctor_get(v_s_736_, 2);
v_commSemiringInst_740_ = lean_ctor_get(v_s_736_, 3);
v_commRingInst_741_ = lean_ctor_get(v_s_736_, 4);
v_noZeroDivInst_x3f_742_ = lean_ctor_get(v_s_736_, 5);
v_fieldInst_x3f_743_ = lean_ctor_get(v_s_736_, 6);
v_powIdentityInst_x3f_744_ = lean_ctor_get(v_s_736_, 7);
v_denoteEntries_745_ = lean_ctor_get(v_s_736_, 8);
v_nextId_746_ = lean_ctor_get(v_s_736_, 9);
v_steps_747_ = lean_ctor_get(v_s_736_, 10);
v_queue_748_ = lean_ctor_get(v_s_736_, 11);
v_basis_749_ = lean_ctor_get(v_s_736_, 12);
v_diseqs_750_ = lean_ctor_get(v_s_736_, 13);
v_recheck_751_ = lean_ctor_get_uint8(v_s_736_, sizeof(void*)*17);
v_invSet_752_ = lean_ctor_get(v_s_736_, 14);
v_powIdentityVarCount_753_ = lean_ctor_get(v_s_736_, 15);
v_numEq0_x3f_754_ = lean_ctor_get(v_s_736_, 16);
v_numEq0Updated_755_ = lean_ctor_get_uint8(v_s_736_, sizeof(void*)*17 + 1);
v_isSharedCheck_787_ = !lean_is_exclusive(v_s_736_);
if (v_isSharedCheck_787_ == 0)
{
v___x_757_ = v_s_736_;
v_isShared_758_ = v_isSharedCheck_787_;
goto v_resetjp_756_;
}
else
{
lean_inc(v_numEq0_x3f_754_);
lean_inc(v_powIdentityVarCount_753_);
lean_inc(v_invSet_752_);
lean_inc(v_diseqs_750_);
lean_inc(v_basis_749_);
lean_inc(v_queue_748_);
lean_inc(v_steps_747_);
lean_inc(v_nextId_746_);
lean_inc(v_denoteEntries_745_);
lean_inc(v_powIdentityInst_x3f_744_);
lean_inc(v_fieldInst_x3f_743_);
lean_inc(v_noZeroDivInst_x3f_742_);
lean_inc(v_commRingInst_741_);
lean_inc(v_commSemiringInst_740_);
lean_inc(v_semiringId_x3f_739_);
lean_inc(v_invFn_x3f_738_);
lean_inc(v_toRing_737_);
lean_dec(v_s_736_);
v___x_757_ = lean_box(0);
v_isShared_758_ = v_isSharedCheck_787_;
goto v_resetjp_756_;
}
v_resetjp_756_:
{
lean_object* v_id_759_; lean_object* v_type_760_; lean_object* v_u_761_; lean_object* v_ringInst_762_; lean_object* v_semiringInst_763_; lean_object* v_charInst_x3f_764_; lean_object* v_addFn_x3f_765_; lean_object* v_mulFn_x3f_766_; lean_object* v_subFn_x3f_767_; lean_object* v_negFn_x3f_768_; lean_object* v_powFn_x3f_769_; lean_object* v_intCastFn_x3f_770_; lean_object* v_one_x3f_771_; lean_object* v_vars_772_; lean_object* v_varMap_773_; lean_object* v_denote_774_; lean_object* v___x_776_; uint8_t v_isShared_777_; uint8_t v_isSharedCheck_785_; 
v_id_759_ = lean_ctor_get(v_toRing_737_, 0);
v_type_760_ = lean_ctor_get(v_toRing_737_, 1);
v_u_761_ = lean_ctor_get(v_toRing_737_, 2);
v_ringInst_762_ = lean_ctor_get(v_toRing_737_, 3);
v_semiringInst_763_ = lean_ctor_get(v_toRing_737_, 4);
v_charInst_x3f_764_ = lean_ctor_get(v_toRing_737_, 5);
v_addFn_x3f_765_ = lean_ctor_get(v_toRing_737_, 6);
v_mulFn_x3f_766_ = lean_ctor_get(v_toRing_737_, 7);
v_subFn_x3f_767_ = lean_ctor_get(v_toRing_737_, 8);
v_negFn_x3f_768_ = lean_ctor_get(v_toRing_737_, 9);
v_powFn_x3f_769_ = lean_ctor_get(v_toRing_737_, 10);
v_intCastFn_x3f_770_ = lean_ctor_get(v_toRing_737_, 11);
v_one_x3f_771_ = lean_ctor_get(v_toRing_737_, 13);
v_vars_772_ = lean_ctor_get(v_toRing_737_, 14);
v_varMap_773_ = lean_ctor_get(v_toRing_737_, 15);
v_denote_774_ = lean_ctor_get(v_toRing_737_, 16);
v_isSharedCheck_785_ = !lean_is_exclusive(v_toRing_737_);
if (v_isSharedCheck_785_ == 0)
{
lean_object* v_unused_786_; 
v_unused_786_ = lean_ctor_get(v_toRing_737_, 12);
lean_dec(v_unused_786_);
v___x_776_ = v_toRing_737_;
v_isShared_777_ = v_isSharedCheck_785_;
goto v_resetjp_775_;
}
else
{
lean_inc(v_denote_774_);
lean_inc(v_varMap_773_);
lean_inc(v_vars_772_);
lean_inc(v_one_x3f_771_);
lean_inc(v_intCastFn_x3f_770_);
lean_inc(v_powFn_x3f_769_);
lean_inc(v_negFn_x3f_768_);
lean_inc(v_subFn_x3f_767_);
lean_inc(v_mulFn_x3f_766_);
lean_inc(v_addFn_x3f_765_);
lean_inc(v_charInst_x3f_764_);
lean_inc(v_semiringInst_763_);
lean_inc(v_ringInst_762_);
lean_inc(v_u_761_);
lean_inc(v_type_760_);
lean_inc(v_id_759_);
lean_dec(v_toRing_737_);
v___x_776_ = lean_box(0);
v_isShared_777_ = v_isSharedCheck_785_;
goto v_resetjp_775_;
}
v_resetjp_775_:
{
lean_object* v___x_778_; lean_object* v___x_780_; 
v___x_778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_778_, 0, v_a_735_);
if (v_isShared_777_ == 0)
{
lean_ctor_set(v___x_776_, 12, v___x_778_);
v___x_780_ = v___x_776_;
goto v_reusejp_779_;
}
else
{
lean_object* v_reuseFailAlloc_784_; 
v_reuseFailAlloc_784_ = lean_alloc_ctor(0, 17, 0);
lean_ctor_set(v_reuseFailAlloc_784_, 0, v_id_759_);
lean_ctor_set(v_reuseFailAlloc_784_, 1, v_type_760_);
lean_ctor_set(v_reuseFailAlloc_784_, 2, v_u_761_);
lean_ctor_set(v_reuseFailAlloc_784_, 3, v_ringInst_762_);
lean_ctor_set(v_reuseFailAlloc_784_, 4, v_semiringInst_763_);
lean_ctor_set(v_reuseFailAlloc_784_, 5, v_charInst_x3f_764_);
lean_ctor_set(v_reuseFailAlloc_784_, 6, v_addFn_x3f_765_);
lean_ctor_set(v_reuseFailAlloc_784_, 7, v_mulFn_x3f_766_);
lean_ctor_set(v_reuseFailAlloc_784_, 8, v_subFn_x3f_767_);
lean_ctor_set(v_reuseFailAlloc_784_, 9, v_negFn_x3f_768_);
lean_ctor_set(v_reuseFailAlloc_784_, 10, v_powFn_x3f_769_);
lean_ctor_set(v_reuseFailAlloc_784_, 11, v_intCastFn_x3f_770_);
lean_ctor_set(v_reuseFailAlloc_784_, 12, v___x_778_);
lean_ctor_set(v_reuseFailAlloc_784_, 13, v_one_x3f_771_);
lean_ctor_set(v_reuseFailAlloc_784_, 14, v_vars_772_);
lean_ctor_set(v_reuseFailAlloc_784_, 15, v_varMap_773_);
lean_ctor_set(v_reuseFailAlloc_784_, 16, v_denote_774_);
v___x_780_ = v_reuseFailAlloc_784_;
goto v_reusejp_779_;
}
v_reusejp_779_:
{
lean_object* v___x_782_; 
if (v_isShared_758_ == 0)
{
lean_ctor_set(v___x_757_, 0, v___x_780_);
v___x_782_ = v___x_757_;
goto v_reusejp_781_;
}
else
{
lean_object* v_reuseFailAlloc_783_; 
v_reuseFailAlloc_783_ = lean_alloc_ctor(0, 17, 2);
lean_ctor_set(v_reuseFailAlloc_783_, 0, v___x_780_);
lean_ctor_set(v_reuseFailAlloc_783_, 1, v_invFn_x3f_738_);
lean_ctor_set(v_reuseFailAlloc_783_, 2, v_semiringId_x3f_739_);
lean_ctor_set(v_reuseFailAlloc_783_, 3, v_commSemiringInst_740_);
lean_ctor_set(v_reuseFailAlloc_783_, 4, v_commRingInst_741_);
lean_ctor_set(v_reuseFailAlloc_783_, 5, v_noZeroDivInst_x3f_742_);
lean_ctor_set(v_reuseFailAlloc_783_, 6, v_fieldInst_x3f_743_);
lean_ctor_set(v_reuseFailAlloc_783_, 7, v_powIdentityInst_x3f_744_);
lean_ctor_set(v_reuseFailAlloc_783_, 8, v_denoteEntries_745_);
lean_ctor_set(v_reuseFailAlloc_783_, 9, v_nextId_746_);
lean_ctor_set(v_reuseFailAlloc_783_, 10, v_steps_747_);
lean_ctor_set(v_reuseFailAlloc_783_, 11, v_queue_748_);
lean_ctor_set(v_reuseFailAlloc_783_, 12, v_basis_749_);
lean_ctor_set(v_reuseFailAlloc_783_, 13, v_diseqs_750_);
lean_ctor_set(v_reuseFailAlloc_783_, 14, v_invSet_752_);
lean_ctor_set(v_reuseFailAlloc_783_, 15, v_powIdentityVarCount_753_);
lean_ctor_set(v_reuseFailAlloc_783_, 16, v_numEq0_x3f_754_);
lean_ctor_set_uint8(v_reuseFailAlloc_783_, sizeof(void*)*17, v_recheck_751_);
lean_ctor_set_uint8(v_reuseFailAlloc_783_, sizeof(void*)*17 + 1, v_numEq0Updated_755_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_getNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isNatCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__2_spec__4_spec__6___redArg(lean_object* v_u_796_, lean_object* v_type_797_, lean_object* v_semiringInst_798_, lean_object* v___y_799_, lean_object* v___y_800_, lean_object* v___y_801_, lean_object* v___y_802_, lean_object* v___y_803_, lean_object* v___y_804_){
_start:
{
lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v_inst_x27_810_; lean_object* v_inst_812_; lean_object* v___y_813_; lean_object* v___y_814_; lean_object* v___y_815_; lean_object* v___y_816_; lean_object* v___y_817_; lean_object* v___y_818_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v_instType_827_; lean_object* v___x_828_; 
v___x_806_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_getNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isNatCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__2_spec__4_spec__6___redArg___closed__1));
v___x_807_ = lean_box(0);
v___x_808_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_808_, 0, v_u_796_);
lean_ctor_set(v___x_808_, 1, v___x_807_);
lean_inc_ref_n(v___x_808_, 2);
v___x_809_ = l_Lean_mkConst(v___x_806_, v___x_808_);
lean_inc_ref_n(v_type_797_, 2);
v_inst_x27_810_ = l_Lean_mkAppB(v___x_809_, v_type_797_, v_semiringInst_798_);
v___x_825_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_getNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isNatCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__2_spec__4_spec__6___redArg___closed__2));
v___x_826_ = l_Lean_mkConst(v___x_825_, v___x_808_);
v_instType_827_ = l_Lean_Expr_app___override(v___x_826_, v_type_797_);
v___x_828_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v_instType_827_, v___y_800_, v___y_801_, v___y_802_, v___y_803_, v___y_804_);
if (lean_obj_tag(v___x_828_) == 0)
{
lean_object* v_a_829_; 
v_a_829_ = lean_ctor_get(v___x_828_, 0);
lean_inc(v_a_829_);
lean_dec_ref_known(v___x_828_, 1);
if (lean_obj_tag(v_a_829_) == 0)
{
v_inst_812_ = v_inst_x27_810_;
v___y_813_ = v___y_799_;
v___y_814_ = v___y_800_;
v___y_815_ = v___y_801_;
v___y_816_ = v___y_802_;
v___y_817_ = v___y_803_;
v___y_818_ = v___y_804_;
goto v___jp_811_;
}
else
{
lean_object* v_val_830_; lean_object* v___x_831_; lean_object* v___x_832_; 
v_val_830_ = lean_ctor_get(v_a_829_, 0);
lean_inc_n(v_val_830_, 2);
lean_dec_ref_known(v_a_829_, 1);
v___x_831_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__5));
v___x_832_ = l_Lean_Meta_Grind_Arith_CommRing_checkInst(v___x_831_, v_val_830_, v_inst_x27_810_, v___y_801_, v___y_802_, v___y_803_, v___y_804_);
if (lean_obj_tag(v___x_832_) == 0)
{
lean_dec_ref_known(v___x_832_, 1);
v_inst_812_ = v_val_830_;
v___y_813_ = v___y_799_;
v___y_814_ = v___y_800_;
v___y_815_ = v___y_801_;
v___y_816_ = v___y_802_;
v___y_817_ = v___y_803_;
v___y_818_ = v___y_804_;
goto v___jp_811_;
}
else
{
lean_object* v_a_833_; lean_object* v___x_835_; uint8_t v_isShared_836_; uint8_t v_isSharedCheck_840_; 
lean_dec(v_val_830_);
lean_dec_ref_known(v___x_808_, 2);
lean_dec_ref(v_type_797_);
v_a_833_ = lean_ctor_get(v___x_832_, 0);
v_isSharedCheck_840_ = !lean_is_exclusive(v___x_832_);
if (v_isSharedCheck_840_ == 0)
{
v___x_835_ = v___x_832_;
v_isShared_836_ = v_isSharedCheck_840_;
goto v_resetjp_834_;
}
else
{
lean_inc(v_a_833_);
lean_dec(v___x_832_);
v___x_835_ = lean_box(0);
v_isShared_836_ = v_isSharedCheck_840_;
goto v_resetjp_834_;
}
v_resetjp_834_:
{
lean_object* v___x_838_; 
if (v_isShared_836_ == 0)
{
v___x_838_ = v___x_835_;
goto v_reusejp_837_;
}
else
{
lean_object* v_reuseFailAlloc_839_; 
v_reuseFailAlloc_839_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_839_, 0, v_a_833_);
v___x_838_ = v_reuseFailAlloc_839_;
goto v_reusejp_837_;
}
v_reusejp_837_:
{
return v___x_838_;
}
}
}
}
}
else
{
lean_object* v_a_841_; lean_object* v___x_843_; uint8_t v_isShared_844_; uint8_t v_isSharedCheck_848_; 
lean_dec_ref(v_inst_x27_810_);
lean_dec_ref_known(v___x_808_, 2);
lean_dec_ref(v_type_797_);
v_a_841_ = lean_ctor_get(v___x_828_, 0);
v_isSharedCheck_848_ = !lean_is_exclusive(v___x_828_);
if (v_isSharedCheck_848_ == 0)
{
v___x_843_ = v___x_828_;
v_isShared_844_ = v_isSharedCheck_848_;
goto v_resetjp_842_;
}
else
{
lean_inc(v_a_841_);
lean_dec(v___x_828_);
v___x_843_ = lean_box(0);
v_isShared_844_ = v_isSharedCheck_848_;
goto v_resetjp_842_;
}
v_resetjp_842_:
{
lean_object* v___x_846_; 
if (v_isShared_844_ == 0)
{
v___x_846_ = v___x_843_;
goto v_reusejp_845_;
}
else
{
lean_object* v_reuseFailAlloc_847_; 
v_reuseFailAlloc_847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_847_, 0, v_a_841_);
v___x_846_ = v_reuseFailAlloc_847_;
goto v_reusejp_845_;
}
v_reusejp_845_:
{
return v___x_846_;
}
}
}
v___jp_811_:
{
lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; 
v___x_819_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__5));
v___x_820_ = l_Lean_mkConst(v___x_819_, v___x_808_);
v___x_821_ = l_Lean_mkAppB(v___x_820_, v_type_797_, v_inst_812_);
v___x_822_ = l_Lean_Meta_Sym_canon(v___x_821_, v___y_813_, v___y_814_, v___y_815_, v___y_816_, v___y_817_, v___y_818_);
if (lean_obj_tag(v___x_822_) == 0)
{
lean_object* v_a_823_; lean_object* v___x_824_; 
v_a_823_ = lean_ctor_get(v___x_822_, 0);
lean_inc(v_a_823_);
lean_dec_ref_known(v___x_822_, 1);
v___x_824_ = l_Lean_Meta_Sym_shareCommon(v_a_823_, v___y_813_, v___y_814_, v___y_815_, v___y_816_, v___y_817_, v___y_818_);
return v___x_824_;
}
else
{
return v___x_822_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_getNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isNatCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__2_spec__4_spec__6___redArg___boxed(lean_object* v_u_849_, lean_object* v_type_850_, lean_object* v_semiringInst_851_, lean_object* v___y_852_, lean_object* v___y_853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_, lean_object* v___y_857_, lean_object* v___y_858_){
_start:
{
lean_object* v_res_859_; 
v_res_859_ = l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_getNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isNatCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__2_spec__4_spec__6___redArg(v_u_849_, v_type_850_, v_semiringInst_851_, v___y_852_, v___y_853_, v___y_854_, v___y_855_, v___y_856_, v___y_857_);
lean_dec(v___y_857_);
lean_dec_ref(v___y_856_);
lean_dec(v___y_855_);
lean_dec_ref(v___y_854_);
lean_dec(v___y_853_);
lean_dec_ref(v___y_852_);
return v_res_859_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isNatCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__2_spec__4(lean_object* v___y_860_, lean_object* v___y_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_, lean_object* v___y_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_, lean_object* v___y_870_){
_start:
{
lean_object* v___x_872_; 
v___x_872_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v___y_860_, v___y_861_, v___y_862_, v___y_863_, v___y_864_, v___y_865_, v___y_866_, v___y_867_, v___y_868_, v___y_869_, v___y_870_);
if (lean_obj_tag(v___x_872_) == 0)
{
lean_object* v_a_873_; lean_object* v___x_875_; uint8_t v_isShared_876_; uint8_t v_isSharedCheck_906_; 
v_a_873_ = lean_ctor_get(v___x_872_, 0);
v_isSharedCheck_906_ = !lean_is_exclusive(v___x_872_);
if (v_isSharedCheck_906_ == 0)
{
v___x_875_ = v___x_872_;
v_isShared_876_ = v_isSharedCheck_906_;
goto v_resetjp_874_;
}
else
{
lean_inc(v_a_873_);
lean_dec(v___x_872_);
v___x_875_ = lean_box(0);
v_isShared_876_ = v_isSharedCheck_906_;
goto v_resetjp_874_;
}
v_resetjp_874_:
{
lean_object* v_toRing_877_; lean_object* v_natCastFn_x3f_878_; 
v_toRing_877_ = lean_ctor_get(v_a_873_, 0);
lean_inc_ref(v_toRing_877_);
lean_dec(v_a_873_);
v_natCastFn_x3f_878_ = lean_ctor_get(v_toRing_877_, 12);
if (lean_obj_tag(v_natCastFn_x3f_878_) == 1)
{
lean_object* v_val_879_; lean_object* v___x_881_; 
lean_inc_ref(v_natCastFn_x3f_878_);
lean_dec_ref(v_toRing_877_);
v_val_879_ = lean_ctor_get(v_natCastFn_x3f_878_, 0);
lean_inc(v_val_879_);
lean_dec_ref_known(v_natCastFn_x3f_878_, 1);
if (v_isShared_876_ == 0)
{
lean_ctor_set(v___x_875_, 0, v_val_879_);
v___x_881_ = v___x_875_;
goto v_reusejp_880_;
}
else
{
lean_object* v_reuseFailAlloc_882_; 
v_reuseFailAlloc_882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_882_, 0, v_val_879_);
v___x_881_ = v_reuseFailAlloc_882_;
goto v_reusejp_880_;
}
v_reusejp_880_:
{
return v___x_881_;
}
}
else
{
lean_object* v_type_883_; lean_object* v_u_884_; lean_object* v_semiringInst_885_; lean_object* v___x_886_; 
lean_del_object(v___x_875_);
v_type_883_ = lean_ctor_get(v_toRing_877_, 1);
lean_inc_ref(v_type_883_);
v_u_884_ = lean_ctor_get(v_toRing_877_, 2);
lean_inc(v_u_884_);
v_semiringInst_885_ = lean_ctor_get(v_toRing_877_, 4);
lean_inc_ref(v_semiringInst_885_);
lean_dec_ref(v_toRing_877_);
v___x_886_ = l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_getNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isNatCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__2_spec__4_spec__6___redArg(v_u_884_, v_type_883_, v_semiringInst_885_, v___y_865_, v___y_866_, v___y_867_, v___y_868_, v___y_869_, v___y_870_);
if (lean_obj_tag(v___x_886_) == 0)
{
lean_object* v_a_887_; lean_object* v___f_888_; lean_object* v___x_889_; 
v_a_887_ = lean_ctor_get(v___x_886_, 0);
lean_inc_n(v_a_887_, 2);
lean_dec_ref_known(v___x_886_, 1);
v___f_888_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isNatCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__2_spec__4___lam__0), 2, 1);
lean_closure_set(v___f_888_, 0, v_a_887_);
v___x_889_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(v___f_888_, v___y_860_, v___y_861_);
if (lean_obj_tag(v___x_889_) == 0)
{
lean_object* v___x_891_; uint8_t v_isShared_892_; uint8_t v_isSharedCheck_896_; 
v_isSharedCheck_896_ = !lean_is_exclusive(v___x_889_);
if (v_isSharedCheck_896_ == 0)
{
lean_object* v_unused_897_; 
v_unused_897_ = lean_ctor_get(v___x_889_, 0);
lean_dec(v_unused_897_);
v___x_891_ = v___x_889_;
v_isShared_892_ = v_isSharedCheck_896_;
goto v_resetjp_890_;
}
else
{
lean_dec(v___x_889_);
v___x_891_ = lean_box(0);
v_isShared_892_ = v_isSharedCheck_896_;
goto v_resetjp_890_;
}
v_resetjp_890_:
{
lean_object* v___x_894_; 
if (v_isShared_892_ == 0)
{
lean_ctor_set(v___x_891_, 0, v_a_887_);
v___x_894_ = v___x_891_;
goto v_reusejp_893_;
}
else
{
lean_object* v_reuseFailAlloc_895_; 
v_reuseFailAlloc_895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_895_, 0, v_a_887_);
v___x_894_ = v_reuseFailAlloc_895_;
goto v_reusejp_893_;
}
v_reusejp_893_:
{
return v___x_894_;
}
}
}
else
{
lean_object* v_a_898_; lean_object* v___x_900_; uint8_t v_isShared_901_; uint8_t v_isSharedCheck_905_; 
lean_dec(v_a_887_);
v_a_898_ = lean_ctor_get(v___x_889_, 0);
v_isSharedCheck_905_ = !lean_is_exclusive(v___x_889_);
if (v_isSharedCheck_905_ == 0)
{
v___x_900_ = v___x_889_;
v_isShared_901_ = v_isSharedCheck_905_;
goto v_resetjp_899_;
}
else
{
lean_inc(v_a_898_);
lean_dec(v___x_889_);
v___x_900_ = lean_box(0);
v_isShared_901_ = v_isSharedCheck_905_;
goto v_resetjp_899_;
}
v_resetjp_899_:
{
lean_object* v___x_903_; 
if (v_isShared_901_ == 0)
{
v___x_903_ = v___x_900_;
goto v_reusejp_902_;
}
else
{
lean_object* v_reuseFailAlloc_904_; 
v_reuseFailAlloc_904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_904_, 0, v_a_898_);
v___x_903_ = v_reuseFailAlloc_904_;
goto v_reusejp_902_;
}
v_reusejp_902_:
{
return v___x_903_;
}
}
}
}
else
{
return v___x_886_;
}
}
}
}
else
{
lean_object* v_a_907_; lean_object* v___x_909_; uint8_t v_isShared_910_; uint8_t v_isSharedCheck_914_; 
v_a_907_ = lean_ctor_get(v___x_872_, 0);
v_isSharedCheck_914_ = !lean_is_exclusive(v___x_872_);
if (v_isSharedCheck_914_ == 0)
{
v___x_909_ = v___x_872_;
v_isShared_910_ = v_isSharedCheck_914_;
goto v_resetjp_908_;
}
else
{
lean_inc(v_a_907_);
lean_dec(v___x_872_);
v___x_909_ = lean_box(0);
v_isShared_910_ = v_isSharedCheck_914_;
goto v_resetjp_908_;
}
v_resetjp_908_:
{
lean_object* v___x_912_; 
if (v_isShared_910_ == 0)
{
v___x_912_ = v___x_909_;
goto v_reusejp_911_;
}
else
{
lean_object* v_reuseFailAlloc_913_; 
v_reuseFailAlloc_913_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_913_, 0, v_a_907_);
v___x_912_ = v_reuseFailAlloc_913_;
goto v_reusejp_911_;
}
v_reusejp_911_:
{
return v___x_912_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isNatCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__2_spec__4___boxed(lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_){
_start:
{
lean_object* v_res_927_; 
v_res_927_ = l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isNatCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__2_spec__4(v___y_915_, v___y_916_, v___y_917_, v___y_918_, v___y_919_, v___y_920_, v___y_921_, v___y_922_, v___y_923_, v___y_924_, v___y_925_);
lean_dec(v___y_925_);
lean_dec_ref(v___y_924_);
lean_dec(v___y_923_);
lean_dec_ref(v___y_922_);
lean_dec(v___y_921_);
lean_dec_ref(v___y_920_);
lean_dec(v___y_919_);
lean_dec_ref(v___y_918_);
lean_dec(v___y_917_);
lean_dec(v___y_916_);
lean_dec_ref(v___y_915_);
return v_res_927_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_isNatCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__2(lean_object* v_inst_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_){
_start:
{
lean_object* v___x_941_; 
v___x_941_ = l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isNatCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__2_spec__4(v___y_929_, v___y_930_, v___y_931_, v___y_932_, v___y_933_, v___y_934_, v___y_935_, v___y_936_, v___y_937_, v___y_938_, v___y_939_);
if (lean_obj_tag(v___x_941_) == 0)
{
lean_object* v_a_942_; lean_object* v___x_944_; uint8_t v_isShared_945_; uint8_t v_isSharedCheck_954_; 
v_a_942_ = lean_ctor_get(v___x_941_, 0);
v_isSharedCheck_954_ = !lean_is_exclusive(v___x_941_);
if (v_isSharedCheck_954_ == 0)
{
v___x_944_ = v___x_941_;
v_isShared_945_ = v_isSharedCheck_954_;
goto v_resetjp_943_;
}
else
{
lean_inc(v_a_942_);
lean_dec(v___x_941_);
v___x_944_ = lean_box(0);
v_isShared_945_ = v_isSharedCheck_954_;
goto v_resetjp_943_;
}
v_resetjp_943_:
{
lean_object* v___x_946_; size_t v___x_947_; size_t v___x_948_; uint8_t v___x_949_; lean_object* v___x_950_; lean_object* v___x_952_; 
v___x_946_ = l_Lean_Expr_appArg_x21(v_a_942_);
lean_dec(v_a_942_);
v___x_947_ = lean_ptr_addr(v___x_946_);
lean_dec_ref(v___x_946_);
v___x_948_ = lean_ptr_addr(v_inst_928_);
v___x_949_ = lean_usize_dec_eq(v___x_947_, v___x_948_);
v___x_950_ = lean_box(v___x_949_);
if (v_isShared_945_ == 0)
{
lean_ctor_set(v___x_944_, 0, v___x_950_);
v___x_952_ = v___x_944_;
goto v_reusejp_951_;
}
else
{
lean_object* v_reuseFailAlloc_953_; 
v_reuseFailAlloc_953_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_953_, 0, v___x_950_);
v___x_952_ = v_reuseFailAlloc_953_;
goto v_reusejp_951_;
}
v_reusejp_951_:
{
return v___x_952_;
}
}
}
else
{
lean_object* v_a_955_; lean_object* v___x_957_; uint8_t v_isShared_958_; uint8_t v_isSharedCheck_962_; 
v_a_955_ = lean_ctor_get(v___x_941_, 0);
v_isSharedCheck_962_ = !lean_is_exclusive(v___x_941_);
if (v_isSharedCheck_962_ == 0)
{
v___x_957_ = v___x_941_;
v_isShared_958_ = v_isSharedCheck_962_;
goto v_resetjp_956_;
}
else
{
lean_inc(v_a_955_);
lean_dec(v___x_941_);
v___x_957_ = lean_box(0);
v_isShared_958_ = v_isSharedCheck_962_;
goto v_resetjp_956_;
}
v_resetjp_956_:
{
lean_object* v___x_960_; 
if (v_isShared_958_ == 0)
{
v___x_960_ = v___x_957_;
goto v_reusejp_959_;
}
else
{
lean_object* v_reuseFailAlloc_961_; 
v_reuseFailAlloc_961_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_961_, 0, v_a_955_);
v___x_960_ = v_reuseFailAlloc_961_;
goto v_reusejp_959_;
}
v_reusejp_959_:
{
return v___x_960_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_isNatCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__2___boxed(lean_object* v_inst_963_, lean_object* v___y_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_){
_start:
{
lean_object* v_res_976_; 
v_res_976_ = l_Lean_Meta_Grind_Arith_CommRing_isNatCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__2(v_inst_963_, v___y_964_, v___y_965_, v___y_966_, v___y_967_, v___y_968_, v___y_969_, v___y_970_, v___y_971_, v___y_972_, v___y_973_, v___y_974_);
lean_dec(v___y_974_);
lean_dec_ref(v___y_973_);
lean_dec(v___y_972_);
lean_dec_ref(v___y_971_);
lean_dec(v___y_970_);
lean_dec_ref(v___y_969_);
lean_dec(v___y_968_);
lean_dec_ref(v___y_967_);
lean_dec(v___y_966_);
lean_dec(v___y_965_);
lean_dec_ref(v___y_964_);
lean_dec_ref(v_inst_963_);
return v_res_976_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f(lean_object* v_e_977_, lean_object* v_a_978_, lean_object* v_a_979_, lean_object* v_a_980_, lean_object* v_a_981_, lean_object* v_a_982_, lean_object* v_a_983_, lean_object* v_a_984_, lean_object* v_a_985_, lean_object* v_a_986_, lean_object* v_a_987_, lean_object* v_a_988_){
_start:
{
lean_object* v___x_993_; 
v___x_993_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_977_, v_a_986_);
if (lean_obj_tag(v___x_993_) == 0)
{
lean_object* v_a_994_; lean_object* v___x_995_; uint8_t v___x_996_; 
v_a_994_ = lean_ctor_get(v___x_993_, 0);
lean_inc(v_a_994_);
lean_dec_ref_known(v___x_993_, 1);
v___x_995_ = l_Lean_Expr_cleanupAnnotations(v_a_994_);
v___x_996_ = l_Lean_Expr_isApp(v___x_995_);
if (v___x_996_ == 0)
{
lean_dec_ref(v___x_995_);
goto v___jp_990_;
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
goto v___jp_990_;
}
else
{
lean_object* v_arg_1000_; lean_object* v___x_1001_; uint8_t v___x_1002_; 
v_arg_1000_ = lean_ctor_get(v___x_998_, 1);
lean_inc_ref(v_arg_1000_);
v___x_1001_ = l_Lean_Expr_appFnCleanup___redArg(v___x_998_);
v___x_1002_ = l_Lean_Expr_isApp(v___x_1001_);
if (v___x_1002_ == 0)
{
lean_dec_ref(v___x_1001_);
lean_dec_ref(v_arg_1000_);
lean_dec_ref(v_arg_997_);
goto v___jp_990_;
}
else
{
lean_object* v___x_1003_; lean_object* v___x_1004_; uint8_t v___x_1005_; 
v___x_1003_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1001_);
v___x_1004_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__8));
v___x_1005_ = l_Lean_Expr_isConstOf(v___x_1003_, v___x_1004_);
if (v___x_1005_ == 0)
{
lean_object* v___x_1006_; uint8_t v___x_1007_; 
v___x_1006_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__5));
v___x_1007_ = l_Lean_Expr_isConstOf(v___x_1003_, v___x_1006_);
if (v___x_1007_ == 0)
{
lean_object* v___x_1008_; uint8_t v___x_1009_; 
v___x_1008_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__2));
v___x_1009_ = l_Lean_Expr_isConstOf(v___x_1003_, v___x_1008_);
if (v___x_1009_ == 0)
{
lean_object* v___x_1010_; uint8_t v___x_1011_; 
v___x_1010_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__11));
v___x_1011_ = l_Lean_Expr_isConstOf(v___x_1003_, v___x_1010_);
lean_dec_ref(v___x_1003_);
if (v___x_1011_ == 0)
{
lean_dec_ref(v_arg_1000_);
lean_dec_ref(v_arg_997_);
goto v___jp_990_;
}
else
{
lean_object* v___x_1012_; 
v___x_1012_ = l_Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0(v_arg_1000_, v_a_978_, v_a_979_, v_a_980_, v_a_981_, v_a_982_, v_a_983_, v_a_984_, v_a_985_, v_a_986_, v_a_987_, v_a_988_);
lean_dec_ref(v_arg_1000_);
if (lean_obj_tag(v___x_1012_) == 0)
{
lean_object* v_a_1013_; lean_object* v___x_1015_; uint8_t v_isShared_1016_; uint8_t v_isSharedCheck_1041_; 
v_a_1013_ = lean_ctor_get(v___x_1012_, 0);
v_isSharedCheck_1041_ = !lean_is_exclusive(v___x_1012_);
if (v_isSharedCheck_1041_ == 0)
{
v___x_1015_ = v___x_1012_;
v_isShared_1016_ = v_isSharedCheck_1041_;
goto v_resetjp_1014_;
}
else
{
lean_inc(v_a_1013_);
lean_dec(v___x_1012_);
v___x_1015_ = lean_box(0);
v_isShared_1016_ = v_isSharedCheck_1041_;
goto v_resetjp_1014_;
}
v_resetjp_1014_:
{
uint8_t v___x_1017_; 
v___x_1017_ = lean_unbox(v_a_1013_);
lean_dec(v_a_1013_);
if (v___x_1017_ == 0)
{
lean_object* v___x_1018_; lean_object* v___x_1020_; 
lean_dec_ref(v_arg_997_);
v___x_1018_ = lean_box(0);
if (v_isShared_1016_ == 0)
{
lean_ctor_set(v___x_1015_, 0, v___x_1018_);
v___x_1020_ = v___x_1015_;
goto v_reusejp_1019_;
}
else
{
lean_object* v_reuseFailAlloc_1021_; 
v_reuseFailAlloc_1021_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1021_, 0, v___x_1018_);
v___x_1020_ = v_reuseFailAlloc_1021_;
goto v_reusejp_1019_;
}
v_reusejp_1019_:
{
return v___x_1020_;
}
}
else
{
lean_object* v___x_1022_; 
lean_del_object(v___x_1015_);
v___x_1022_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f(v_arg_997_, v_a_978_, v_a_979_, v_a_980_, v_a_981_, v_a_982_, v_a_983_, v_a_984_, v_a_985_, v_a_986_, v_a_987_, v_a_988_);
if (lean_obj_tag(v___x_1022_) == 0)
{
lean_object* v_a_1023_; 
v_a_1023_ = lean_ctor_get(v___x_1022_, 0);
lean_inc(v_a_1023_);
if (lean_obj_tag(v_a_1023_) == 0)
{
return v___x_1022_;
}
else
{
lean_object* v___x_1025_; uint8_t v_isShared_1026_; uint8_t v_isSharedCheck_1039_; 
v_isSharedCheck_1039_ = !lean_is_exclusive(v___x_1022_);
if (v_isSharedCheck_1039_ == 0)
{
lean_object* v_unused_1040_; 
v_unused_1040_ = lean_ctor_get(v___x_1022_, 0);
lean_dec(v_unused_1040_);
v___x_1025_ = v___x_1022_;
v_isShared_1026_ = v_isSharedCheck_1039_;
goto v_resetjp_1024_;
}
else
{
lean_dec(v___x_1022_);
v___x_1025_ = lean_box(0);
v_isShared_1026_ = v_isSharedCheck_1039_;
goto v_resetjp_1024_;
}
v_resetjp_1024_:
{
lean_object* v_val_1027_; lean_object* v___x_1029_; uint8_t v_isShared_1030_; uint8_t v_isSharedCheck_1038_; 
v_val_1027_ = lean_ctor_get(v_a_1023_, 0);
v_isSharedCheck_1038_ = !lean_is_exclusive(v_a_1023_);
if (v_isSharedCheck_1038_ == 0)
{
v___x_1029_ = v_a_1023_;
v_isShared_1030_ = v_isSharedCheck_1038_;
goto v_resetjp_1028_;
}
else
{
lean_inc(v_val_1027_);
lean_dec(v_a_1023_);
v___x_1029_ = lean_box(0);
v_isShared_1030_ = v_isSharedCheck_1038_;
goto v_resetjp_1028_;
}
v_resetjp_1028_:
{
lean_object* v___x_1031_; lean_object* v___x_1033_; 
v___x_1031_ = lean_int_neg(v_val_1027_);
lean_dec(v_val_1027_);
if (v_isShared_1030_ == 0)
{
lean_ctor_set(v___x_1029_, 0, v___x_1031_);
v___x_1033_ = v___x_1029_;
goto v_reusejp_1032_;
}
else
{
lean_object* v_reuseFailAlloc_1037_; 
v_reuseFailAlloc_1037_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1037_, 0, v___x_1031_);
v___x_1033_ = v_reuseFailAlloc_1037_;
goto v_reusejp_1032_;
}
v_reusejp_1032_:
{
lean_object* v___x_1035_; 
if (v_isShared_1026_ == 0)
{
lean_ctor_set(v___x_1025_, 0, v___x_1033_);
v___x_1035_ = v___x_1025_;
goto v_reusejp_1034_;
}
else
{
lean_object* v_reuseFailAlloc_1036_; 
v_reuseFailAlloc_1036_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1036_, 0, v___x_1033_);
v___x_1035_ = v_reuseFailAlloc_1036_;
goto v_reusejp_1034_;
}
v_reusejp_1034_:
{
return v___x_1035_;
}
}
}
}
}
}
else
{
return v___x_1022_;
}
}
}
}
else
{
lean_object* v_a_1042_; lean_object* v___x_1044_; uint8_t v_isShared_1045_; uint8_t v_isSharedCheck_1049_; 
lean_dec_ref(v_arg_997_);
v_a_1042_ = lean_ctor_get(v___x_1012_, 0);
v_isSharedCheck_1049_ = !lean_is_exclusive(v___x_1012_);
if (v_isSharedCheck_1049_ == 0)
{
v___x_1044_ = v___x_1012_;
v_isShared_1045_ = v_isSharedCheck_1049_;
goto v_resetjp_1043_;
}
else
{
lean_inc(v_a_1042_);
lean_dec(v___x_1012_);
v___x_1044_ = lean_box(0);
v_isShared_1045_ = v_isSharedCheck_1049_;
goto v_resetjp_1043_;
}
v_resetjp_1043_:
{
lean_object* v___x_1047_; 
if (v_isShared_1045_ == 0)
{
v___x_1047_ = v___x_1044_;
goto v_reusejp_1046_;
}
else
{
lean_object* v_reuseFailAlloc_1048_; 
v_reuseFailAlloc_1048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1048_, 0, v_a_1042_);
v___x_1047_ = v_reuseFailAlloc_1048_;
goto v_reusejp_1046_;
}
v_reusejp_1046_:
{
return v___x_1047_;
}
}
}
}
}
else
{
lean_object* v___x_1050_; 
lean_dec_ref(v___x_1003_);
v___x_1050_ = l_Lean_Meta_Grind_Arith_CommRing_isIntCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__1(v_arg_1000_, v_a_978_, v_a_979_, v_a_980_, v_a_981_, v_a_982_, v_a_983_, v_a_984_, v_a_985_, v_a_986_, v_a_987_, v_a_988_);
lean_dec_ref(v_arg_1000_);
if (lean_obj_tag(v___x_1050_) == 0)
{
lean_object* v_a_1051_; lean_object* v___x_1053_; uint8_t v_isShared_1054_; uint8_t v_isSharedCheck_1061_; 
v_a_1051_ = lean_ctor_get(v___x_1050_, 0);
v_isSharedCheck_1061_ = !lean_is_exclusive(v___x_1050_);
if (v_isSharedCheck_1061_ == 0)
{
v___x_1053_ = v___x_1050_;
v_isShared_1054_ = v_isSharedCheck_1061_;
goto v_resetjp_1052_;
}
else
{
lean_inc(v_a_1051_);
lean_dec(v___x_1050_);
v___x_1053_ = lean_box(0);
v_isShared_1054_ = v_isSharedCheck_1061_;
goto v_resetjp_1052_;
}
v_resetjp_1052_:
{
uint8_t v___x_1055_; 
v___x_1055_ = lean_unbox(v_a_1051_);
lean_dec(v_a_1051_);
if (v___x_1055_ == 0)
{
lean_object* v___x_1056_; lean_object* v___x_1058_; 
lean_dec_ref(v_arg_997_);
v___x_1056_ = lean_box(0);
if (v_isShared_1054_ == 0)
{
lean_ctor_set(v___x_1053_, 0, v___x_1056_);
v___x_1058_ = v___x_1053_;
goto v_reusejp_1057_;
}
else
{
lean_object* v_reuseFailAlloc_1059_; 
v_reuseFailAlloc_1059_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1059_, 0, v___x_1056_);
v___x_1058_ = v_reuseFailAlloc_1059_;
goto v_reusejp_1057_;
}
v_reusejp_1057_:
{
return v___x_1058_;
}
}
else
{
lean_object* v___x_1060_; 
lean_del_object(v___x_1053_);
v___x_1060_ = l_Lean_Meta_getIntValue_x3f(v_arg_997_, v_a_985_, v_a_986_, v_a_987_, v_a_988_);
return v___x_1060_;
}
}
}
else
{
lean_object* v_a_1062_; lean_object* v___x_1064_; uint8_t v_isShared_1065_; uint8_t v_isSharedCheck_1069_; 
lean_dec_ref(v_arg_997_);
v_a_1062_ = lean_ctor_get(v___x_1050_, 0);
v_isSharedCheck_1069_ = !lean_is_exclusive(v___x_1050_);
if (v_isSharedCheck_1069_ == 0)
{
v___x_1064_ = v___x_1050_;
v_isShared_1065_ = v_isSharedCheck_1069_;
goto v_resetjp_1063_;
}
else
{
lean_inc(v_a_1062_);
lean_dec(v___x_1050_);
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
}
else
{
lean_object* v___x_1070_; 
lean_dec_ref(v___x_1003_);
v___x_1070_ = l_Lean_Meta_Grind_Arith_CommRing_isNatCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__2(v_arg_1000_, v_a_978_, v_a_979_, v_a_980_, v_a_981_, v_a_982_, v_a_983_, v_a_984_, v_a_985_, v_a_986_, v_a_987_, v_a_988_);
lean_dec_ref(v_arg_1000_);
if (lean_obj_tag(v___x_1070_) == 0)
{
lean_object* v_a_1071_; lean_object* v___x_1073_; uint8_t v_isShared_1074_; uint8_t v_isSharedCheck_1110_; 
v_a_1071_ = lean_ctor_get(v___x_1070_, 0);
v_isSharedCheck_1110_ = !lean_is_exclusive(v___x_1070_);
if (v_isSharedCheck_1110_ == 0)
{
v___x_1073_ = v___x_1070_;
v_isShared_1074_ = v_isSharedCheck_1110_;
goto v_resetjp_1072_;
}
else
{
lean_inc(v_a_1071_);
lean_dec(v___x_1070_);
v___x_1073_ = lean_box(0);
v_isShared_1074_ = v_isSharedCheck_1110_;
goto v_resetjp_1072_;
}
v_resetjp_1072_:
{
uint8_t v___x_1075_; 
v___x_1075_ = lean_unbox(v_a_1071_);
lean_dec(v_a_1071_);
if (v___x_1075_ == 0)
{
lean_object* v___x_1076_; lean_object* v___x_1078_; 
lean_dec_ref(v_arg_997_);
v___x_1076_ = lean_box(0);
if (v_isShared_1074_ == 0)
{
lean_ctor_set(v___x_1073_, 0, v___x_1076_);
v___x_1078_ = v___x_1073_;
goto v_reusejp_1077_;
}
else
{
lean_object* v_reuseFailAlloc_1079_; 
v_reuseFailAlloc_1079_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1079_, 0, v___x_1076_);
v___x_1078_ = v_reuseFailAlloc_1079_;
goto v_reusejp_1077_;
}
v_reusejp_1077_:
{
return v___x_1078_;
}
}
else
{
lean_object* v___x_1080_; 
lean_del_object(v___x_1073_);
v___x_1080_ = l_Lean_Meta_getNatValue_x3f(v_arg_997_, v_a_985_, v_a_986_, v_a_987_, v_a_988_);
lean_dec_ref(v_arg_997_);
if (lean_obj_tag(v___x_1080_) == 0)
{
lean_object* v_a_1081_; lean_object* v___x_1083_; uint8_t v_isShared_1084_; uint8_t v_isSharedCheck_1101_; 
v_a_1081_ = lean_ctor_get(v___x_1080_, 0);
v_isSharedCheck_1101_ = !lean_is_exclusive(v___x_1080_);
if (v_isSharedCheck_1101_ == 0)
{
v___x_1083_ = v___x_1080_;
v_isShared_1084_ = v_isSharedCheck_1101_;
goto v_resetjp_1082_;
}
else
{
lean_inc(v_a_1081_);
lean_dec(v___x_1080_);
v___x_1083_ = lean_box(0);
v_isShared_1084_ = v_isSharedCheck_1101_;
goto v_resetjp_1082_;
}
v_resetjp_1082_:
{
if (lean_obj_tag(v_a_1081_) == 1)
{
lean_object* v_val_1085_; lean_object* v___x_1087_; uint8_t v_isShared_1088_; uint8_t v_isSharedCheck_1096_; 
v_val_1085_ = lean_ctor_get(v_a_1081_, 0);
v_isSharedCheck_1096_ = !lean_is_exclusive(v_a_1081_);
if (v_isSharedCheck_1096_ == 0)
{
v___x_1087_ = v_a_1081_;
v_isShared_1088_ = v_isSharedCheck_1096_;
goto v_resetjp_1086_;
}
else
{
lean_inc(v_val_1085_);
lean_dec(v_a_1081_);
v___x_1087_ = lean_box(0);
v_isShared_1088_ = v_isSharedCheck_1096_;
goto v_resetjp_1086_;
}
v_resetjp_1086_:
{
lean_object* v___x_1089_; lean_object* v___x_1091_; 
v___x_1089_ = lean_nat_to_int(v_val_1085_);
if (v_isShared_1088_ == 0)
{
lean_ctor_set(v___x_1087_, 0, v___x_1089_);
v___x_1091_ = v___x_1087_;
goto v_reusejp_1090_;
}
else
{
lean_object* v_reuseFailAlloc_1095_; 
v_reuseFailAlloc_1095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1095_, 0, v___x_1089_);
v___x_1091_ = v_reuseFailAlloc_1095_;
goto v_reusejp_1090_;
}
v_reusejp_1090_:
{
lean_object* v___x_1093_; 
if (v_isShared_1084_ == 0)
{
lean_ctor_set(v___x_1083_, 0, v___x_1091_);
v___x_1093_ = v___x_1083_;
goto v_reusejp_1092_;
}
else
{
lean_object* v_reuseFailAlloc_1094_; 
v_reuseFailAlloc_1094_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1094_, 0, v___x_1091_);
v___x_1093_ = v_reuseFailAlloc_1094_;
goto v_reusejp_1092_;
}
v_reusejp_1092_:
{
return v___x_1093_;
}
}
}
}
else
{
lean_object* v___x_1097_; lean_object* v___x_1099_; 
lean_dec(v_a_1081_);
v___x_1097_ = lean_box(0);
if (v_isShared_1084_ == 0)
{
lean_ctor_set(v___x_1083_, 0, v___x_1097_);
v___x_1099_ = v___x_1083_;
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
lean_object* v_a_1102_; lean_object* v___x_1104_; uint8_t v_isShared_1105_; uint8_t v_isSharedCheck_1109_; 
v_a_1102_ = lean_ctor_get(v___x_1080_, 0);
v_isSharedCheck_1109_ = !lean_is_exclusive(v___x_1080_);
if (v_isSharedCheck_1109_ == 0)
{
v___x_1104_ = v___x_1080_;
v_isShared_1105_ = v_isSharedCheck_1109_;
goto v_resetjp_1103_;
}
else
{
lean_inc(v_a_1102_);
lean_dec(v___x_1080_);
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
}
else
{
lean_object* v_a_1111_; lean_object* v___x_1113_; uint8_t v_isShared_1114_; uint8_t v_isSharedCheck_1118_; 
lean_dec_ref(v_arg_997_);
v_a_1111_ = lean_ctor_get(v___x_1070_, 0);
v_isSharedCheck_1118_ = !lean_is_exclusive(v___x_1070_);
if (v_isSharedCheck_1118_ == 0)
{
v___x_1113_ = v___x_1070_;
v_isShared_1114_ = v_isSharedCheck_1118_;
goto v_resetjp_1112_;
}
else
{
lean_inc(v_a_1111_);
lean_dec(v___x_1070_);
v___x_1113_ = lean_box(0);
v_isShared_1114_ = v_isSharedCheck_1118_;
goto v_resetjp_1112_;
}
v_resetjp_1112_:
{
lean_object* v___x_1116_; 
if (v_isShared_1114_ == 0)
{
v___x_1116_ = v___x_1113_;
goto v_reusejp_1115_;
}
else
{
lean_object* v_reuseFailAlloc_1117_; 
v_reuseFailAlloc_1117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1117_, 0, v_a_1111_);
v___x_1116_ = v_reuseFailAlloc_1117_;
goto v_reusejp_1115_;
}
v_reusejp_1115_:
{
return v___x_1116_;
}
}
}
}
}
else
{
lean_object* v___x_1119_; 
lean_dec_ref(v___x_1003_);
lean_dec_ref(v_arg_997_);
v___x_1119_ = l_Lean_Meta_getNatValue_x3f(v_arg_1000_, v_a_985_, v_a_986_, v_a_987_, v_a_988_);
lean_dec_ref(v_arg_1000_);
if (lean_obj_tag(v___x_1119_) == 0)
{
lean_object* v_a_1120_; lean_object* v___x_1122_; uint8_t v_isShared_1123_; uint8_t v_isSharedCheck_1140_; 
v_a_1120_ = lean_ctor_get(v___x_1119_, 0);
v_isSharedCheck_1140_ = !lean_is_exclusive(v___x_1119_);
if (v_isSharedCheck_1140_ == 0)
{
v___x_1122_ = v___x_1119_;
v_isShared_1123_ = v_isSharedCheck_1140_;
goto v_resetjp_1121_;
}
else
{
lean_inc(v_a_1120_);
lean_dec(v___x_1119_);
v___x_1122_ = lean_box(0);
v_isShared_1123_ = v_isSharedCheck_1140_;
goto v_resetjp_1121_;
}
v_resetjp_1121_:
{
if (lean_obj_tag(v_a_1120_) == 1)
{
lean_object* v_val_1124_; lean_object* v___x_1126_; uint8_t v_isShared_1127_; uint8_t v_isSharedCheck_1135_; 
v_val_1124_ = lean_ctor_get(v_a_1120_, 0);
v_isSharedCheck_1135_ = !lean_is_exclusive(v_a_1120_);
if (v_isSharedCheck_1135_ == 0)
{
v___x_1126_ = v_a_1120_;
v_isShared_1127_ = v_isSharedCheck_1135_;
goto v_resetjp_1125_;
}
else
{
lean_inc(v_val_1124_);
lean_dec(v_a_1120_);
v___x_1126_ = lean_box(0);
v_isShared_1127_ = v_isSharedCheck_1135_;
goto v_resetjp_1125_;
}
v_resetjp_1125_:
{
lean_object* v___x_1128_; lean_object* v___x_1130_; 
v___x_1128_ = lean_nat_to_int(v_val_1124_);
if (v_isShared_1127_ == 0)
{
lean_ctor_set(v___x_1126_, 0, v___x_1128_);
v___x_1130_ = v___x_1126_;
goto v_reusejp_1129_;
}
else
{
lean_object* v_reuseFailAlloc_1134_; 
v_reuseFailAlloc_1134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1134_, 0, v___x_1128_);
v___x_1130_ = v_reuseFailAlloc_1134_;
goto v_reusejp_1129_;
}
v_reusejp_1129_:
{
lean_object* v___x_1132_; 
if (v_isShared_1123_ == 0)
{
lean_ctor_set(v___x_1122_, 0, v___x_1130_);
v___x_1132_ = v___x_1122_;
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
}
}
else
{
lean_object* v___x_1136_; lean_object* v___x_1138_; 
lean_dec(v_a_1120_);
v___x_1136_ = lean_box(0);
if (v_isShared_1123_ == 0)
{
lean_ctor_set(v___x_1122_, 0, v___x_1136_);
v___x_1138_ = v___x_1122_;
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
lean_object* v_a_1141_; lean_object* v___x_1143_; uint8_t v_isShared_1144_; uint8_t v_isSharedCheck_1148_; 
v_a_1141_ = lean_ctor_get(v___x_1119_, 0);
v_isSharedCheck_1148_ = !lean_is_exclusive(v___x_1119_);
if (v_isSharedCheck_1148_ == 0)
{
v___x_1143_ = v___x_1119_;
v_isShared_1144_ = v_isSharedCheck_1148_;
goto v_resetjp_1142_;
}
else
{
lean_inc(v_a_1141_);
lean_dec(v___x_1119_);
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
}
}
}
else
{
lean_object* v_a_1149_; lean_object* v___x_1151_; uint8_t v_isShared_1152_; uint8_t v_isSharedCheck_1156_; 
v_a_1149_ = lean_ctor_get(v___x_993_, 0);
v_isSharedCheck_1156_ = !lean_is_exclusive(v___x_993_);
if (v_isSharedCheck_1156_ == 0)
{
v___x_1151_ = v___x_993_;
v_isShared_1152_ = v_isSharedCheck_1156_;
goto v_resetjp_1150_;
}
else
{
lean_inc(v_a_1149_);
lean_dec(v___x_993_);
v___x_1151_ = lean_box(0);
v_isShared_1152_ = v_isSharedCheck_1156_;
goto v_resetjp_1150_;
}
v_resetjp_1150_:
{
lean_object* v___x_1154_; 
if (v_isShared_1152_ == 0)
{
v___x_1154_ = v___x_1151_;
goto v_reusejp_1153_;
}
else
{
lean_object* v_reuseFailAlloc_1155_; 
v_reuseFailAlloc_1155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1155_, 0, v_a_1149_);
v___x_1154_ = v_reuseFailAlloc_1155_;
goto v_reusejp_1153_;
}
v_reusejp_1153_:
{
return v___x_1154_;
}
}
}
v___jp_990_:
{
lean_object* v___x_991_; lean_object* v___x_992_; 
v___x_991_ = lean_box(0);
v___x_992_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_992_, 0, v___x_991_);
return v___x_992_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f___boxed(lean_object* v_e_1157_, lean_object* v_a_1158_, lean_object* v_a_1159_, lean_object* v_a_1160_, lean_object* v_a_1161_, lean_object* v_a_1162_, lean_object* v_a_1163_, lean_object* v_a_1164_, lean_object* v_a_1165_, lean_object* v_a_1166_, lean_object* v_a_1167_, lean_object* v_a_1168_, lean_object* v_a_1169_){
_start:
{
lean_object* v_res_1170_; 
v_res_1170_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f(v_e_1157_, v_a_1158_, v_a_1159_, v_a_1160_, v_a_1161_, v_a_1162_, v_a_1163_, v_a_1164_, v_a_1165_, v_a_1166_, v_a_1167_, v_a_1168_);
lean_dec(v_a_1168_);
lean_dec_ref(v_a_1167_);
lean_dec(v_a_1166_);
lean_dec_ref(v_a_1165_);
lean_dec(v_a_1164_);
lean_dec_ref(v_a_1163_);
lean_dec(v_a_1162_);
lean_dec_ref(v_a_1161_);
lean_dec(v_a_1160_);
lean_dec(v_a_1159_);
lean_dec_ref(v_a_1158_);
return v_res_1170_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_getNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isNatCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__2_spec__4_spec__6(lean_object* v_u_1171_, lean_object* v_type_1172_, lean_object* v_semiringInst_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_){
_start:
{
lean_object* v___x_1186_; 
v___x_1186_ = l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_getNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isNatCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__2_spec__4_spec__6___redArg(v_u_1171_, v_type_1172_, v_semiringInst_1173_, v___y_1179_, v___y_1180_, v___y_1181_, v___y_1182_, v___y_1183_, v___y_1184_);
return v___x_1186_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_getNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isNatCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__2_spec__4_spec__6___boxed(lean_object* v_u_1187_, lean_object* v_type_1188_, lean_object* v_semiringInst_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_){
_start:
{
lean_object* v_res_1202_; 
v_res_1202_ = l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_getNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isNatCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__2_spec__4_spec__6(v_u_1187_, v_type_1188_, v_semiringInst_1189_, v___y_1190_, v___y_1191_, v___y_1192_, v___y_1193_, v___y_1194_, v___y_1195_, v___y_1196_, v___y_1197_, v___y_1198_, v___y_1199_, v___y_1200_);
lean_dec(v___y_1200_);
lean_dec_ref(v___y_1199_);
lean_dec(v___y_1198_);
lean_dec_ref(v___y_1197_);
lean_dec(v___y_1196_);
lean_dec_ref(v___y_1195_);
lean_dec(v___y_1194_);
lean_dec_ref(v___y_1193_);
lean_dec(v___y_1192_);
lean_dec(v___y_1191_);
lean_dec_ref(v___y_1190_);
return v_res_1202_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1_spec__5_spec__8(lean_object* v_00_u03b1_1203_, lean_object* v_msg_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_){
_start:
{
lean_object* v___x_1217_; 
v___x_1217_ = l_Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1_spec__5_spec__8___redArg(v_msg_1204_, v___y_1212_, v___y_1213_, v___y_1214_, v___y_1215_);
return v___x_1217_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1_spec__5_spec__8___boxed(lean_object* v_00_u03b1_1218_, lean_object* v_msg_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_){
_start:
{
lean_object* v_res_1232_; 
v_res_1232_ = l_Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1_spec__5_spec__8(v_00_u03b1_1218_, v_msg_1219_, v___y_1220_, v___y_1221_, v___y_1222_, v___y_1223_, v___y_1224_, v___y_1225_, v___y_1226_, v___y_1227_, v___y_1228_, v___y_1229_, v___y_1230_);
lean_dec(v___y_1230_);
lean_dec_ref(v___y_1229_);
lean_dec(v___y_1228_);
lean_dec_ref(v___y_1227_);
lean_dec(v___y_1226_);
lean_dec_ref(v___y_1225_);
lean_dec(v___y_1224_);
lean_dec_ref(v___y_1223_);
lean_dec(v___y_1222_);
lean_dec(v___y_1221_);
lean_dec_ref(v___y_1220_);
return v_res_1232_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___lam__0(lean_object* v_a_1233_, lean_object* v_s_1234_){
_start:
{
lean_object* v_toRing_1235_; lean_object* v_semiringId_x3f_1236_; lean_object* v_commSemiringInst_1237_; lean_object* v_commRingInst_1238_; lean_object* v_noZeroDivInst_x3f_1239_; lean_object* v_fieldInst_x3f_1240_; lean_object* v_powIdentityInst_x3f_1241_; lean_object* v_denoteEntries_1242_; lean_object* v_nextId_1243_; lean_object* v_steps_1244_; lean_object* v_queue_1245_; lean_object* v_basis_1246_; lean_object* v_diseqs_1247_; uint8_t v_recheck_1248_; lean_object* v_invSet_1249_; lean_object* v_powIdentityVarCount_1250_; lean_object* v_numEq0_x3f_1251_; uint8_t v_numEq0Updated_1252_; lean_object* v___x_1254_; uint8_t v_isShared_1255_; uint8_t v_isSharedCheck_1260_; 
v_toRing_1235_ = lean_ctor_get(v_s_1234_, 0);
v_semiringId_x3f_1236_ = lean_ctor_get(v_s_1234_, 2);
v_commSemiringInst_1237_ = lean_ctor_get(v_s_1234_, 3);
v_commRingInst_1238_ = lean_ctor_get(v_s_1234_, 4);
v_noZeroDivInst_x3f_1239_ = lean_ctor_get(v_s_1234_, 5);
v_fieldInst_x3f_1240_ = lean_ctor_get(v_s_1234_, 6);
v_powIdentityInst_x3f_1241_ = lean_ctor_get(v_s_1234_, 7);
v_denoteEntries_1242_ = lean_ctor_get(v_s_1234_, 8);
v_nextId_1243_ = lean_ctor_get(v_s_1234_, 9);
v_steps_1244_ = lean_ctor_get(v_s_1234_, 10);
v_queue_1245_ = lean_ctor_get(v_s_1234_, 11);
v_basis_1246_ = lean_ctor_get(v_s_1234_, 12);
v_diseqs_1247_ = lean_ctor_get(v_s_1234_, 13);
v_recheck_1248_ = lean_ctor_get_uint8(v_s_1234_, sizeof(void*)*17);
v_invSet_1249_ = lean_ctor_get(v_s_1234_, 14);
v_powIdentityVarCount_1250_ = lean_ctor_get(v_s_1234_, 15);
v_numEq0_x3f_1251_ = lean_ctor_get(v_s_1234_, 16);
v_numEq0Updated_1252_ = lean_ctor_get_uint8(v_s_1234_, sizeof(void*)*17 + 1);
v_isSharedCheck_1260_ = !lean_is_exclusive(v_s_1234_);
if (v_isSharedCheck_1260_ == 0)
{
lean_object* v_unused_1261_; 
v_unused_1261_ = lean_ctor_get(v_s_1234_, 1);
lean_dec(v_unused_1261_);
v___x_1254_ = v_s_1234_;
v_isShared_1255_ = v_isSharedCheck_1260_;
goto v_resetjp_1253_;
}
else
{
lean_inc(v_numEq0_x3f_1251_);
lean_inc(v_powIdentityVarCount_1250_);
lean_inc(v_invSet_1249_);
lean_inc(v_diseqs_1247_);
lean_inc(v_basis_1246_);
lean_inc(v_queue_1245_);
lean_inc(v_steps_1244_);
lean_inc(v_nextId_1243_);
lean_inc(v_denoteEntries_1242_);
lean_inc(v_powIdentityInst_x3f_1241_);
lean_inc(v_fieldInst_x3f_1240_);
lean_inc(v_noZeroDivInst_x3f_1239_);
lean_inc(v_commRingInst_1238_);
lean_inc(v_commSemiringInst_1237_);
lean_inc(v_semiringId_x3f_1236_);
lean_inc(v_toRing_1235_);
lean_dec(v_s_1234_);
v___x_1254_ = lean_box(0);
v_isShared_1255_ = v_isSharedCheck_1260_;
goto v_resetjp_1253_;
}
v_resetjp_1253_:
{
lean_object* v___x_1256_; lean_object* v___x_1258_; 
v___x_1256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1256_, 0, v_a_1233_);
if (v_isShared_1255_ == 0)
{
lean_ctor_set(v___x_1254_, 1, v___x_1256_);
v___x_1258_ = v___x_1254_;
goto v_reusejp_1257_;
}
else
{
lean_object* v_reuseFailAlloc_1259_; 
v_reuseFailAlloc_1259_ = lean_alloc_ctor(0, 17, 2);
lean_ctor_set(v_reuseFailAlloc_1259_, 0, v_toRing_1235_);
lean_ctor_set(v_reuseFailAlloc_1259_, 1, v___x_1256_);
lean_ctor_set(v_reuseFailAlloc_1259_, 2, v_semiringId_x3f_1236_);
lean_ctor_set(v_reuseFailAlloc_1259_, 3, v_commSemiringInst_1237_);
lean_ctor_set(v_reuseFailAlloc_1259_, 4, v_commRingInst_1238_);
lean_ctor_set(v_reuseFailAlloc_1259_, 5, v_noZeroDivInst_x3f_1239_);
lean_ctor_set(v_reuseFailAlloc_1259_, 6, v_fieldInst_x3f_1240_);
lean_ctor_set(v_reuseFailAlloc_1259_, 7, v_powIdentityInst_x3f_1241_);
lean_ctor_set(v_reuseFailAlloc_1259_, 8, v_denoteEntries_1242_);
lean_ctor_set(v_reuseFailAlloc_1259_, 9, v_nextId_1243_);
lean_ctor_set(v_reuseFailAlloc_1259_, 10, v_steps_1244_);
lean_ctor_set(v_reuseFailAlloc_1259_, 11, v_queue_1245_);
lean_ctor_set(v_reuseFailAlloc_1259_, 12, v_basis_1246_);
lean_ctor_set(v_reuseFailAlloc_1259_, 13, v_diseqs_1247_);
lean_ctor_set(v_reuseFailAlloc_1259_, 14, v_invSet_1249_);
lean_ctor_set(v_reuseFailAlloc_1259_, 15, v_powIdentityVarCount_1250_);
lean_ctor_set(v_reuseFailAlloc_1259_, 16, v_numEq0_x3f_1251_);
lean_ctor_set_uint8(v_reuseFailAlloc_1259_, sizeof(void*)*17, v_recheck_1248_);
lean_ctor_set_uint8(v_reuseFailAlloc_1259_, sizeof(void*)*17 + 1, v_numEq0Updated_1252_);
v___x_1258_ = v_reuseFailAlloc_1259_;
goto v_reusejp_1257_;
}
v_reusejp_1257_:
{
return v___x_1258_;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___closed__8(void){
_start:
{
lean_object* v___x_1277_; lean_object* v___x_1278_; 
v___x_1277_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___closed__7));
v___x_1278_ = l_Lean_stringToMessageData(v___x_1277_);
return v___x_1278_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0(lean_object* v___y_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_){
_start:
{
lean_object* v___x_1291_; 
v___x_1291_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v___y_1279_, v___y_1280_, v___y_1281_, v___y_1282_, v___y_1283_, v___y_1284_, v___y_1285_, v___y_1286_, v___y_1287_, v___y_1288_, v___y_1289_);
if (lean_obj_tag(v___x_1291_) == 0)
{
lean_object* v_a_1292_; lean_object* v___x_1294_; uint8_t v_isShared_1295_; uint8_t v_isSharedCheck_1339_; 
v_a_1292_ = lean_ctor_get(v___x_1291_, 0);
v_isSharedCheck_1339_ = !lean_is_exclusive(v___x_1291_);
if (v_isSharedCheck_1339_ == 0)
{
v___x_1294_ = v___x_1291_;
v_isShared_1295_ = v_isSharedCheck_1339_;
goto v_resetjp_1293_;
}
else
{
lean_inc(v_a_1292_);
lean_dec(v___x_1291_);
v___x_1294_ = lean_box(0);
v_isShared_1295_ = v_isSharedCheck_1339_;
goto v_resetjp_1293_;
}
v_resetjp_1293_:
{
lean_object* v_fieldInst_x3f_1296_; 
v_fieldInst_x3f_1296_ = lean_ctor_get(v_a_1292_, 6);
if (lean_obj_tag(v_fieldInst_x3f_1296_) == 1)
{
lean_object* v_invFn_x3f_1297_; 
lean_inc_ref(v_fieldInst_x3f_1296_);
v_invFn_x3f_1297_ = lean_ctor_get(v_a_1292_, 1);
if (lean_obj_tag(v_invFn_x3f_1297_) == 1)
{
lean_object* v_val_1298_; lean_object* v___x_1300_; 
lean_inc_ref(v_invFn_x3f_1297_);
lean_dec_ref_known(v_fieldInst_x3f_1296_, 1);
lean_dec(v_a_1292_);
v_val_1298_ = lean_ctor_get(v_invFn_x3f_1297_, 0);
lean_inc(v_val_1298_);
lean_dec_ref_known(v_invFn_x3f_1297_, 1);
if (v_isShared_1295_ == 0)
{
lean_ctor_set(v___x_1294_, 0, v_val_1298_);
v___x_1300_ = v___x_1294_;
goto v_reusejp_1299_;
}
else
{
lean_object* v_reuseFailAlloc_1301_; 
v_reuseFailAlloc_1301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1301_, 0, v_val_1298_);
v___x_1300_ = v_reuseFailAlloc_1301_;
goto v_reusejp_1299_;
}
v_reusejp_1299_:
{
return v___x_1300_;
}
}
else
{
lean_object* v_toRing_1302_; lean_object* v_val_1303_; lean_object* v_type_1304_; lean_object* v_u_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v_expectedInst_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; 
lean_del_object(v___x_1294_);
v_toRing_1302_ = lean_ctor_get(v_a_1292_, 0);
lean_inc_ref(v_toRing_1302_);
lean_dec(v_a_1292_);
v_val_1303_ = lean_ctor_get(v_fieldInst_x3f_1296_, 0);
lean_inc(v_val_1303_);
lean_dec_ref_known(v_fieldInst_x3f_1296_, 1);
v_type_1304_ = lean_ctor_get(v_toRing_1302_, 1);
lean_inc_ref_n(v_type_1304_, 2);
v_u_1305_ = lean_ctor_get(v_toRing_1302_, 2);
lean_inc_n(v_u_1305_, 2);
lean_dec_ref(v_toRing_1302_);
v___x_1306_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___closed__2));
v___x_1307_ = lean_box(0);
v___x_1308_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1308_, 0, v_u_1305_);
lean_ctor_set(v___x_1308_, 1, v___x_1307_);
v___x_1309_ = l_Lean_mkConst(v___x_1306_, v___x_1308_);
v_expectedInst_1310_ = l_Lean_mkAppB(v___x_1309_, v_type_1304_, v_val_1303_);
v___x_1311_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___closed__4));
v___x_1312_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___closed__6));
v___x_1313_ = l_Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1(v_type_1304_, v_u_1305_, v___x_1311_, v___x_1312_, v_expectedInst_1310_, v___y_1279_, v___y_1280_, v___y_1281_, v___y_1282_, v___y_1283_, v___y_1284_, v___y_1285_, v___y_1286_, v___y_1287_, v___y_1288_, v___y_1289_);
if (lean_obj_tag(v___x_1313_) == 0)
{
lean_object* v_a_1314_; lean_object* v___f_1315_; lean_object* v___x_1316_; 
v_a_1314_ = lean_ctor_get(v___x_1313_, 0);
lean_inc_n(v_a_1314_, 2);
lean_dec_ref_known(v___x_1313_, 1);
v___f_1315_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___lam__0), 2, 1);
lean_closure_set(v___f_1315_, 0, v_a_1314_);
v___x_1316_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(v___f_1315_, v___y_1279_, v___y_1280_);
if (lean_obj_tag(v___x_1316_) == 0)
{
lean_object* v___x_1318_; uint8_t v_isShared_1319_; uint8_t v_isSharedCheck_1323_; 
v_isSharedCheck_1323_ = !lean_is_exclusive(v___x_1316_);
if (v_isSharedCheck_1323_ == 0)
{
lean_object* v_unused_1324_; 
v_unused_1324_ = lean_ctor_get(v___x_1316_, 0);
lean_dec(v_unused_1324_);
v___x_1318_ = v___x_1316_;
v_isShared_1319_ = v_isSharedCheck_1323_;
goto v_resetjp_1317_;
}
else
{
lean_dec(v___x_1316_);
v___x_1318_ = lean_box(0);
v_isShared_1319_ = v_isSharedCheck_1323_;
goto v_resetjp_1317_;
}
v_resetjp_1317_:
{
lean_object* v___x_1321_; 
if (v_isShared_1319_ == 0)
{
lean_ctor_set(v___x_1318_, 0, v_a_1314_);
v___x_1321_ = v___x_1318_;
goto v_reusejp_1320_;
}
else
{
lean_object* v_reuseFailAlloc_1322_; 
v_reuseFailAlloc_1322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1322_, 0, v_a_1314_);
v___x_1321_ = v_reuseFailAlloc_1322_;
goto v_reusejp_1320_;
}
v_reusejp_1320_:
{
return v___x_1321_;
}
}
}
else
{
lean_object* v_a_1325_; lean_object* v___x_1327_; uint8_t v_isShared_1328_; uint8_t v_isSharedCheck_1332_; 
lean_dec(v_a_1314_);
v_a_1325_ = lean_ctor_get(v___x_1316_, 0);
v_isSharedCheck_1332_ = !lean_is_exclusive(v___x_1316_);
if (v_isSharedCheck_1332_ == 0)
{
v___x_1327_ = v___x_1316_;
v_isShared_1328_ = v_isSharedCheck_1332_;
goto v_resetjp_1326_;
}
else
{
lean_inc(v_a_1325_);
lean_dec(v___x_1316_);
v___x_1327_ = lean_box(0);
v_isShared_1328_ = v_isSharedCheck_1332_;
goto v_resetjp_1326_;
}
v_resetjp_1326_:
{
lean_object* v___x_1330_; 
if (v_isShared_1328_ == 0)
{
v___x_1330_ = v___x_1327_;
goto v_reusejp_1329_;
}
else
{
lean_object* v_reuseFailAlloc_1331_; 
v_reuseFailAlloc_1331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1331_, 0, v_a_1325_);
v___x_1330_ = v_reuseFailAlloc_1331_;
goto v_reusejp_1329_;
}
v_reusejp_1329_:
{
return v___x_1330_;
}
}
}
}
else
{
return v___x_1313_;
}
}
}
else
{
lean_object* v_toRing_1333_; lean_object* v_type_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; 
lean_del_object(v___x_1294_);
v_toRing_1333_ = lean_ctor_get(v_a_1292_, 0);
lean_inc_ref(v_toRing_1333_);
lean_dec(v_a_1292_);
v_type_1334_ = lean_ctor_get(v_toRing_1333_, 1);
lean_inc_ref(v_type_1334_);
lean_dec_ref(v_toRing_1333_);
v___x_1335_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___closed__8, &l_Lean_Meta_Grind_Arith_CommRing_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___closed__8_once, _init_l_Lean_Meta_Grind_Arith_CommRing_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___closed__8);
v___x_1336_ = l_Lean_indentExpr(v_type_1334_);
v___x_1337_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1337_, 0, v___x_1335_);
lean_ctor_set(v___x_1337_, 1, v___x_1336_);
v___x_1338_ = l_Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1_spec__5_spec__8___redArg(v___x_1337_, v___y_1286_, v___y_1287_, v___y_1288_, v___y_1289_);
return v___x_1338_;
}
}
}
else
{
lean_object* v_a_1340_; lean_object* v___x_1342_; uint8_t v_isShared_1343_; uint8_t v_isSharedCheck_1347_; 
v_a_1340_ = lean_ctor_get(v___x_1291_, 0);
v_isSharedCheck_1347_ = !lean_is_exclusive(v___x_1291_);
if (v_isSharedCheck_1347_ == 0)
{
v___x_1342_ = v___x_1291_;
v_isShared_1343_ = v_isSharedCheck_1347_;
goto v_resetjp_1341_;
}
else
{
lean_inc(v_a_1340_);
lean_dec(v___x_1291_);
v___x_1342_ = lean_box(0);
v_isShared_1343_ = v_isSharedCheck_1347_;
goto v_resetjp_1341_;
}
v_resetjp_1341_:
{
lean_object* v___x_1345_; 
if (v_isShared_1343_ == 0)
{
v___x_1345_ = v___x_1342_;
goto v_reusejp_1344_;
}
else
{
lean_object* v_reuseFailAlloc_1346_; 
v_reuseFailAlloc_1346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1346_, 0, v_a_1340_);
v___x_1345_ = v_reuseFailAlloc_1346_;
goto v_reusejp_1344_;
}
v_reusejp_1344_:
{
return v___x_1345_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___boxed(lean_object* v___y_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_){
_start:
{
lean_object* v_res_1360_; 
v_res_1360_ = l_Lean_Meta_Grind_Arith_CommRing_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0(v___y_1348_, v___y_1349_, v___y_1350_, v___y_1351_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_, v___y_1356_, v___y_1357_, v___y_1358_);
lean_dec(v___y_1358_);
lean_dec_ref(v___y_1357_);
lean_dec(v___y_1356_);
lean_dec_ref(v___y_1355_);
lean_dec(v___y_1354_);
lean_dec_ref(v___y_1353_);
lean_dec(v___y_1352_);
lean_dec_ref(v___y_1351_);
lean_dec(v___y_1350_);
lean_dec(v___y_1349_);
lean_dec_ref(v___y_1348_);
return v_res_1360_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst(lean_object* v_inst_1361_, lean_object* v_a_1362_, lean_object* v_a_1363_, lean_object* v_a_1364_, lean_object* v_a_1365_, lean_object* v_a_1366_, lean_object* v_a_1367_, lean_object* v_a_1368_, lean_object* v_a_1369_, lean_object* v_a_1370_, lean_object* v_a_1371_, lean_object* v_a_1372_){
_start:
{
lean_object* v___x_1374_; 
v___x_1374_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v_a_1362_, v_a_1363_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_, v_a_1368_, v_a_1369_, v_a_1370_, v_a_1371_, v_a_1372_);
if (lean_obj_tag(v___x_1374_) == 0)
{
lean_object* v_a_1375_; lean_object* v___x_1377_; uint8_t v_isShared_1378_; uint8_t v_isSharedCheck_1407_; 
v_a_1375_ = lean_ctor_get(v___x_1374_, 0);
v_isSharedCheck_1407_ = !lean_is_exclusive(v___x_1374_);
if (v_isSharedCheck_1407_ == 0)
{
v___x_1377_ = v___x_1374_;
v_isShared_1378_ = v_isSharedCheck_1407_;
goto v_resetjp_1376_;
}
else
{
lean_inc(v_a_1375_);
lean_dec(v___x_1374_);
v___x_1377_ = lean_box(0);
v_isShared_1378_ = v_isSharedCheck_1407_;
goto v_resetjp_1376_;
}
v_resetjp_1376_:
{
lean_object* v_fieldInst_x3f_1379_; 
v_fieldInst_x3f_1379_ = lean_ctor_get(v_a_1375_, 6);
lean_inc(v_fieldInst_x3f_1379_);
lean_dec(v_a_1375_);
if (lean_obj_tag(v_fieldInst_x3f_1379_) == 0)
{
uint8_t v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1383_; 
v___x_1380_ = 0;
v___x_1381_ = lean_box(v___x_1380_);
if (v_isShared_1378_ == 0)
{
lean_ctor_set(v___x_1377_, 0, v___x_1381_);
v___x_1383_ = v___x_1377_;
goto v_reusejp_1382_;
}
else
{
lean_object* v_reuseFailAlloc_1384_; 
v_reuseFailAlloc_1384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1384_, 0, v___x_1381_);
v___x_1383_ = v_reuseFailAlloc_1384_;
goto v_reusejp_1382_;
}
v_reusejp_1382_:
{
return v___x_1383_;
}
}
else
{
lean_object* v___x_1385_; 
lean_dec_ref_known(v_fieldInst_x3f_1379_, 1);
lean_del_object(v___x_1377_);
v___x_1385_ = l_Lean_Meta_Grind_Arith_CommRing_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0(v_a_1362_, v_a_1363_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_, v_a_1368_, v_a_1369_, v_a_1370_, v_a_1371_, v_a_1372_);
if (lean_obj_tag(v___x_1385_) == 0)
{
lean_object* v_a_1386_; lean_object* v___x_1388_; uint8_t v_isShared_1389_; uint8_t v_isSharedCheck_1398_; 
v_a_1386_ = lean_ctor_get(v___x_1385_, 0);
v_isSharedCheck_1398_ = !lean_is_exclusive(v___x_1385_);
if (v_isSharedCheck_1398_ == 0)
{
v___x_1388_ = v___x_1385_;
v_isShared_1389_ = v_isSharedCheck_1398_;
goto v_resetjp_1387_;
}
else
{
lean_inc(v_a_1386_);
lean_dec(v___x_1385_);
v___x_1388_ = lean_box(0);
v_isShared_1389_ = v_isSharedCheck_1398_;
goto v_resetjp_1387_;
}
v_resetjp_1387_:
{
lean_object* v___x_1390_; size_t v___x_1391_; size_t v___x_1392_; uint8_t v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1396_; 
v___x_1390_ = l_Lean_Expr_appArg_x21(v_a_1386_);
lean_dec(v_a_1386_);
v___x_1391_ = lean_ptr_addr(v___x_1390_);
lean_dec_ref(v___x_1390_);
v___x_1392_ = lean_ptr_addr(v_inst_1361_);
v___x_1393_ = lean_usize_dec_eq(v___x_1391_, v___x_1392_);
v___x_1394_ = lean_box(v___x_1393_);
if (v_isShared_1389_ == 0)
{
lean_ctor_set(v___x_1388_, 0, v___x_1394_);
v___x_1396_ = v___x_1388_;
goto v_reusejp_1395_;
}
else
{
lean_object* v_reuseFailAlloc_1397_; 
v_reuseFailAlloc_1397_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1397_, 0, v___x_1394_);
v___x_1396_ = v_reuseFailAlloc_1397_;
goto v_reusejp_1395_;
}
v_reusejp_1395_:
{
return v___x_1396_;
}
}
}
else
{
lean_object* v_a_1399_; lean_object* v___x_1401_; uint8_t v_isShared_1402_; uint8_t v_isSharedCheck_1406_; 
v_a_1399_ = lean_ctor_get(v___x_1385_, 0);
v_isSharedCheck_1406_ = !lean_is_exclusive(v___x_1385_);
if (v_isSharedCheck_1406_ == 0)
{
v___x_1401_ = v___x_1385_;
v_isShared_1402_ = v_isSharedCheck_1406_;
goto v_resetjp_1400_;
}
else
{
lean_inc(v_a_1399_);
lean_dec(v___x_1385_);
v___x_1401_ = lean_box(0);
v_isShared_1402_ = v_isSharedCheck_1406_;
goto v_resetjp_1400_;
}
v_resetjp_1400_:
{
lean_object* v___x_1404_; 
if (v_isShared_1402_ == 0)
{
v___x_1404_ = v___x_1401_;
goto v_reusejp_1403_;
}
else
{
lean_object* v_reuseFailAlloc_1405_; 
v_reuseFailAlloc_1405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1405_, 0, v_a_1399_);
v___x_1404_ = v_reuseFailAlloc_1405_;
goto v_reusejp_1403_;
}
v_reusejp_1403_:
{
return v___x_1404_;
}
}
}
}
}
}
else
{
lean_object* v_a_1408_; lean_object* v___x_1410_; uint8_t v_isShared_1411_; uint8_t v_isSharedCheck_1415_; 
v_a_1408_ = lean_ctor_get(v___x_1374_, 0);
v_isSharedCheck_1415_ = !lean_is_exclusive(v___x_1374_);
if (v_isSharedCheck_1415_ == 0)
{
v___x_1410_ = v___x_1374_;
v_isShared_1411_ = v_isSharedCheck_1415_;
goto v_resetjp_1409_;
}
else
{
lean_inc(v_a_1408_);
lean_dec(v___x_1374_);
v___x_1410_ = lean_box(0);
v_isShared_1411_ = v_isSharedCheck_1415_;
goto v_resetjp_1409_;
}
v_resetjp_1409_:
{
lean_object* v___x_1413_; 
if (v_isShared_1411_ == 0)
{
v___x_1413_ = v___x_1410_;
goto v_reusejp_1412_;
}
else
{
lean_object* v_reuseFailAlloc_1414_; 
v_reuseFailAlloc_1414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1414_, 0, v_a_1408_);
v___x_1413_ = v_reuseFailAlloc_1414_;
goto v_reusejp_1412_;
}
v_reusejp_1412_:
{
return v___x_1413_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst___boxed(lean_object* v_inst_1416_, lean_object* v_a_1417_, lean_object* v_a_1418_, lean_object* v_a_1419_, lean_object* v_a_1420_, lean_object* v_a_1421_, lean_object* v_a_1422_, lean_object* v_a_1423_, lean_object* v_a_1424_, lean_object* v_a_1425_, lean_object* v_a_1426_, lean_object* v_a_1427_, lean_object* v_a_1428_){
_start:
{
lean_object* v_res_1429_; 
v_res_1429_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst(v_inst_1416_, v_a_1417_, v_a_1418_, v_a_1419_, v_a_1420_, v_a_1421_, v_a_1422_, v_a_1423_, v_a_1424_, v_a_1425_, v_a_1426_, v_a_1427_);
lean_dec(v_a_1427_);
lean_dec_ref(v_a_1426_);
lean_dec(v_a_1425_);
lean_dec_ref(v_a_1424_);
lean_dec(v_a_1423_);
lean_dec_ref(v_a_1422_);
lean_dec(v_a_1421_);
lean_dec_ref(v_a_1420_);
lean_dec(v_a_1419_);
lean_dec(v_a_1418_);
lean_dec_ref(v_a_1417_);
lean_dec_ref(v_inst_1416_);
return v_res_1429_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__2(lean_object* v_a_1430_){
_start:
{
lean_object* v___x_1431_; 
v___x_1431_ = lean_nat_to_int(v_a_1430_);
return v___x_1431_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0_spec__2_spec__6___redArg(lean_object* v_x_1432_, lean_object* v_x_1433_, lean_object* v_x_1434_, lean_object* v_x_1435_){
_start:
{
lean_object* v_ks_1436_; lean_object* v_vs_1437_; lean_object* v___x_1439_; uint8_t v_isShared_1440_; uint8_t v_isSharedCheck_1461_; 
v_ks_1436_ = lean_ctor_get(v_x_1432_, 0);
v_vs_1437_ = lean_ctor_get(v_x_1432_, 1);
v_isSharedCheck_1461_ = !lean_is_exclusive(v_x_1432_);
if (v_isSharedCheck_1461_ == 0)
{
v___x_1439_ = v_x_1432_;
v_isShared_1440_ = v_isSharedCheck_1461_;
goto v_resetjp_1438_;
}
else
{
lean_inc(v_vs_1437_);
lean_inc(v_ks_1436_);
lean_dec(v_x_1432_);
v___x_1439_ = lean_box(0);
v_isShared_1440_ = v_isSharedCheck_1461_;
goto v_resetjp_1438_;
}
v_resetjp_1438_:
{
lean_object* v___x_1441_; uint8_t v___x_1442_; 
v___x_1441_ = lean_array_get_size(v_ks_1436_);
v___x_1442_ = lean_nat_dec_lt(v_x_1433_, v___x_1441_);
if (v___x_1442_ == 0)
{
lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1446_; 
lean_dec(v_x_1433_);
v___x_1443_ = lean_array_push(v_ks_1436_, v_x_1434_);
v___x_1444_ = lean_array_push(v_vs_1437_, v_x_1435_);
if (v_isShared_1440_ == 0)
{
lean_ctor_set(v___x_1439_, 1, v___x_1444_);
lean_ctor_set(v___x_1439_, 0, v___x_1443_);
v___x_1446_ = v___x_1439_;
goto v_reusejp_1445_;
}
else
{
lean_object* v_reuseFailAlloc_1447_; 
v_reuseFailAlloc_1447_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1447_, 0, v___x_1443_);
lean_ctor_set(v_reuseFailAlloc_1447_, 1, v___x_1444_);
v___x_1446_ = v_reuseFailAlloc_1447_;
goto v_reusejp_1445_;
}
v_reusejp_1445_:
{
return v___x_1446_;
}
}
else
{
lean_object* v_k_x27_1448_; uint8_t v___x_1449_; 
v_k_x27_1448_ = lean_array_fget_borrowed(v_ks_1436_, v_x_1433_);
v___x_1449_ = lean_expr_eqv(v_x_1434_, v_k_x27_1448_);
if (v___x_1449_ == 0)
{
lean_object* v___x_1451_; 
if (v_isShared_1440_ == 0)
{
v___x_1451_ = v___x_1439_;
goto v_reusejp_1450_;
}
else
{
lean_object* v_reuseFailAlloc_1455_; 
v_reuseFailAlloc_1455_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1455_, 0, v_ks_1436_);
lean_ctor_set(v_reuseFailAlloc_1455_, 1, v_vs_1437_);
v___x_1451_ = v_reuseFailAlloc_1455_;
goto v_reusejp_1450_;
}
v_reusejp_1450_:
{
lean_object* v___x_1452_; lean_object* v___x_1453_; 
v___x_1452_ = lean_unsigned_to_nat(1u);
v___x_1453_ = lean_nat_add(v_x_1433_, v___x_1452_);
lean_dec(v_x_1433_);
v_x_1432_ = v___x_1451_;
v_x_1433_ = v___x_1453_;
goto _start;
}
}
else
{
lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1459_; 
v___x_1456_ = lean_array_fset(v_ks_1436_, v_x_1433_, v_x_1434_);
v___x_1457_ = lean_array_fset(v_vs_1437_, v_x_1433_, v_x_1435_);
lean_dec(v_x_1433_);
if (v_isShared_1440_ == 0)
{
lean_ctor_set(v___x_1439_, 1, v___x_1457_);
lean_ctor_set(v___x_1439_, 0, v___x_1456_);
v___x_1459_ = v___x_1439_;
goto v_reusejp_1458_;
}
else
{
lean_object* v_reuseFailAlloc_1460_; 
v_reuseFailAlloc_1460_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1460_, 0, v___x_1456_);
lean_ctor_set(v_reuseFailAlloc_1460_, 1, v___x_1457_);
v___x_1459_ = v_reuseFailAlloc_1460_;
goto v_reusejp_1458_;
}
v_reusejp_1458_:
{
return v___x_1459_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0_spec__2___redArg(lean_object* v_n_1462_, lean_object* v_k_1463_, lean_object* v_v_1464_){
_start:
{
lean_object* v___x_1465_; lean_object* v___x_1466_; 
v___x_1465_ = lean_unsigned_to_nat(0u);
v___x_1466_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0_spec__2_spec__6___redArg(v_n_1462_, v___x_1465_, v_k_1463_, v_v_1464_);
return v___x_1466_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1467_; 
v___x_1467_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_1467_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg(lean_object* v_x_1468_, size_t v_x_1469_, size_t v_x_1470_, lean_object* v_x_1471_, lean_object* v_x_1472_){
_start:
{
if (lean_obj_tag(v_x_1468_) == 0)
{
lean_object* v_es_1473_; size_t v___x_1474_; size_t v___x_1475_; lean_object* v_j_1476_; lean_object* v___x_1477_; uint8_t v___x_1478_; 
v_es_1473_ = lean_ctor_get(v_x_1468_, 0);
v___x_1474_ = ((size_t)31ULL);
v___x_1475_ = lean_usize_land(v_x_1469_, v___x_1474_);
v_j_1476_ = lean_usize_to_nat(v___x_1475_);
v___x_1477_ = lean_array_get_size(v_es_1473_);
v___x_1478_ = lean_nat_dec_lt(v_j_1476_, v___x_1477_);
if (v___x_1478_ == 0)
{
lean_dec(v_j_1476_);
lean_dec(v_x_1472_);
lean_dec_ref(v_x_1471_);
return v_x_1468_;
}
else
{
lean_object* v___x_1480_; uint8_t v_isShared_1481_; uint8_t v_isSharedCheck_1517_; 
lean_inc_ref(v_es_1473_);
v_isSharedCheck_1517_ = !lean_is_exclusive(v_x_1468_);
if (v_isSharedCheck_1517_ == 0)
{
lean_object* v_unused_1518_; 
v_unused_1518_ = lean_ctor_get(v_x_1468_, 0);
lean_dec(v_unused_1518_);
v___x_1480_ = v_x_1468_;
v_isShared_1481_ = v_isSharedCheck_1517_;
goto v_resetjp_1479_;
}
else
{
lean_dec(v_x_1468_);
v___x_1480_ = lean_box(0);
v_isShared_1481_ = v_isSharedCheck_1517_;
goto v_resetjp_1479_;
}
v_resetjp_1479_:
{
lean_object* v_v_1482_; lean_object* v___x_1483_; lean_object* v_xs_x27_1484_; lean_object* v___y_1486_; 
v_v_1482_ = lean_array_fget(v_es_1473_, v_j_1476_);
v___x_1483_ = lean_box(0);
v_xs_x27_1484_ = lean_array_fset(v_es_1473_, v_j_1476_, v___x_1483_);
switch(lean_obj_tag(v_v_1482_))
{
case 0:
{
lean_object* v_key_1491_; lean_object* v_val_1492_; lean_object* v___x_1494_; uint8_t v_isShared_1495_; uint8_t v_isSharedCheck_1502_; 
v_key_1491_ = lean_ctor_get(v_v_1482_, 0);
v_val_1492_ = lean_ctor_get(v_v_1482_, 1);
v_isSharedCheck_1502_ = !lean_is_exclusive(v_v_1482_);
if (v_isSharedCheck_1502_ == 0)
{
v___x_1494_ = v_v_1482_;
v_isShared_1495_ = v_isSharedCheck_1502_;
goto v_resetjp_1493_;
}
else
{
lean_inc(v_val_1492_);
lean_inc(v_key_1491_);
lean_dec(v_v_1482_);
v___x_1494_ = lean_box(0);
v_isShared_1495_ = v_isSharedCheck_1502_;
goto v_resetjp_1493_;
}
v_resetjp_1493_:
{
uint8_t v___x_1496_; 
v___x_1496_ = lean_expr_eqv(v_x_1471_, v_key_1491_);
if (v___x_1496_ == 0)
{
lean_object* v___x_1497_; lean_object* v___x_1498_; 
lean_del_object(v___x_1494_);
v___x_1497_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1491_, v_val_1492_, v_x_1471_, v_x_1472_);
v___x_1498_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1498_, 0, v___x_1497_);
v___y_1486_ = v___x_1498_;
goto v___jp_1485_;
}
else
{
lean_object* v___x_1500_; 
lean_dec(v_val_1492_);
lean_dec(v_key_1491_);
if (v_isShared_1495_ == 0)
{
lean_ctor_set(v___x_1494_, 1, v_x_1472_);
lean_ctor_set(v___x_1494_, 0, v_x_1471_);
v___x_1500_ = v___x_1494_;
goto v_reusejp_1499_;
}
else
{
lean_object* v_reuseFailAlloc_1501_; 
v_reuseFailAlloc_1501_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1501_, 0, v_x_1471_);
lean_ctor_set(v_reuseFailAlloc_1501_, 1, v_x_1472_);
v___x_1500_ = v_reuseFailAlloc_1501_;
goto v_reusejp_1499_;
}
v_reusejp_1499_:
{
v___y_1486_ = v___x_1500_;
goto v___jp_1485_;
}
}
}
}
case 1:
{
lean_object* v_node_1503_; lean_object* v___x_1505_; uint8_t v_isShared_1506_; uint8_t v_isSharedCheck_1515_; 
v_node_1503_ = lean_ctor_get(v_v_1482_, 0);
v_isSharedCheck_1515_ = !lean_is_exclusive(v_v_1482_);
if (v_isSharedCheck_1515_ == 0)
{
v___x_1505_ = v_v_1482_;
v_isShared_1506_ = v_isSharedCheck_1515_;
goto v_resetjp_1504_;
}
else
{
lean_inc(v_node_1503_);
lean_dec(v_v_1482_);
v___x_1505_ = lean_box(0);
v_isShared_1506_ = v_isSharedCheck_1515_;
goto v_resetjp_1504_;
}
v_resetjp_1504_:
{
size_t v___x_1507_; size_t v___x_1508_; size_t v___x_1509_; size_t v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1513_; 
v___x_1507_ = ((size_t)5ULL);
v___x_1508_ = lean_usize_shift_right(v_x_1469_, v___x_1507_);
v___x_1509_ = ((size_t)1ULL);
v___x_1510_ = lean_usize_add(v_x_1470_, v___x_1509_);
v___x_1511_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg(v_node_1503_, v___x_1508_, v___x_1510_, v_x_1471_, v_x_1472_);
if (v_isShared_1506_ == 0)
{
lean_ctor_set(v___x_1505_, 0, v___x_1511_);
v___x_1513_ = v___x_1505_;
goto v_reusejp_1512_;
}
else
{
lean_object* v_reuseFailAlloc_1514_; 
v_reuseFailAlloc_1514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1514_, 0, v___x_1511_);
v___x_1513_ = v_reuseFailAlloc_1514_;
goto v_reusejp_1512_;
}
v_reusejp_1512_:
{
v___y_1486_ = v___x_1513_;
goto v___jp_1485_;
}
}
}
default: 
{
lean_object* v___x_1516_; 
v___x_1516_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1516_, 0, v_x_1471_);
lean_ctor_set(v___x_1516_, 1, v_x_1472_);
v___y_1486_ = v___x_1516_;
goto v___jp_1485_;
}
}
v___jp_1485_:
{
lean_object* v___x_1487_; lean_object* v___x_1489_; 
v___x_1487_ = lean_array_fset(v_xs_x27_1484_, v_j_1476_, v___y_1486_);
lean_dec(v_j_1476_);
if (v_isShared_1481_ == 0)
{
lean_ctor_set(v___x_1480_, 0, v___x_1487_);
v___x_1489_ = v___x_1480_;
goto v_reusejp_1488_;
}
else
{
lean_object* v_reuseFailAlloc_1490_; 
v_reuseFailAlloc_1490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1490_, 0, v___x_1487_);
v___x_1489_ = v_reuseFailAlloc_1490_;
goto v_reusejp_1488_;
}
v_reusejp_1488_:
{
return v___x_1489_;
}
}
}
}
}
else
{
lean_object* v_ks_1519_; lean_object* v_vs_1520_; lean_object* v___x_1522_; uint8_t v_isShared_1523_; uint8_t v_isSharedCheck_1538_; 
v_ks_1519_ = lean_ctor_get(v_x_1468_, 0);
v_vs_1520_ = lean_ctor_get(v_x_1468_, 1);
v_isSharedCheck_1538_ = !lean_is_exclusive(v_x_1468_);
if (v_isSharedCheck_1538_ == 0)
{
v___x_1522_ = v_x_1468_;
v_isShared_1523_ = v_isSharedCheck_1538_;
goto v_resetjp_1521_;
}
else
{
lean_inc(v_vs_1520_);
lean_inc(v_ks_1519_);
lean_dec(v_x_1468_);
v___x_1522_ = lean_box(0);
v_isShared_1523_ = v_isSharedCheck_1538_;
goto v_resetjp_1521_;
}
v_resetjp_1521_:
{
lean_object* v___x_1525_; 
if (v_isShared_1523_ == 0)
{
v___x_1525_ = v___x_1522_;
goto v_reusejp_1524_;
}
else
{
lean_object* v_reuseFailAlloc_1537_; 
v_reuseFailAlloc_1537_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1537_, 0, v_ks_1519_);
lean_ctor_set(v_reuseFailAlloc_1537_, 1, v_vs_1520_);
v___x_1525_ = v_reuseFailAlloc_1537_;
goto v_reusejp_1524_;
}
v_reusejp_1524_:
{
lean_object* v_newNode_1526_; size_t v___x_1527_; uint8_t v___x_1528_; 
v_newNode_1526_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0_spec__2___redArg(v___x_1525_, v_x_1471_, v_x_1472_);
v___x_1527_ = ((size_t)7ULL);
v___x_1528_ = lean_usize_dec_le(v___x_1527_, v_x_1470_);
if (v___x_1528_ == 0)
{
lean_object* v___x_1529_; lean_object* v___x_1530_; uint8_t v___x_1531_; 
v___x_1529_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1526_);
v___x_1530_ = lean_unsigned_to_nat(4u);
v___x_1531_ = lean_nat_dec_lt(v___x_1529_, v___x_1530_);
lean_dec(v___x_1529_);
if (v___x_1531_ == 0)
{
lean_object* v_ks_1532_; lean_object* v_vs_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; 
v_ks_1532_ = lean_ctor_get(v_newNode_1526_, 0);
lean_inc_ref(v_ks_1532_);
v_vs_1533_ = lean_ctor_get(v_newNode_1526_, 1);
lean_inc_ref(v_vs_1533_);
lean_dec_ref(v_newNode_1526_);
v___x_1534_ = lean_unsigned_to_nat(0u);
v___x_1535_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg___closed__0);
v___x_1536_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0_spec__3___redArg(v_x_1470_, v_ks_1532_, v_vs_1533_, v___x_1534_, v___x_1535_);
lean_dec_ref(v_vs_1533_);
lean_dec_ref(v_ks_1532_);
return v___x_1536_;
}
else
{
return v_newNode_1526_;
}
}
else
{
return v_newNode_1526_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0_spec__3___redArg(size_t v_depth_1539_, lean_object* v_keys_1540_, lean_object* v_vals_1541_, lean_object* v_i_1542_, lean_object* v_entries_1543_){
_start:
{
lean_object* v___x_1544_; uint8_t v___x_1545_; 
v___x_1544_ = lean_array_get_size(v_keys_1540_);
v___x_1545_ = lean_nat_dec_lt(v_i_1542_, v___x_1544_);
if (v___x_1545_ == 0)
{
lean_dec(v_i_1542_);
return v_entries_1543_;
}
else
{
lean_object* v_k_1546_; lean_object* v_v_1547_; uint64_t v___x_1548_; size_t v_h_1549_; size_t v___x_1550_; lean_object* v___x_1551_; size_t v___x_1552_; size_t v___x_1553_; size_t v___x_1554_; size_t v_h_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; 
v_k_1546_ = lean_array_fget_borrowed(v_keys_1540_, v_i_1542_);
v_v_1547_ = lean_array_fget_borrowed(v_vals_1541_, v_i_1542_);
v___x_1548_ = l_Lean_Expr_hash(v_k_1546_);
v_h_1549_ = lean_uint64_to_usize(v___x_1548_);
v___x_1550_ = ((size_t)5ULL);
v___x_1551_ = lean_unsigned_to_nat(1u);
v___x_1552_ = ((size_t)1ULL);
v___x_1553_ = lean_usize_sub(v_depth_1539_, v___x_1552_);
v___x_1554_ = lean_usize_mul(v___x_1550_, v___x_1553_);
v_h_1555_ = lean_usize_shift_right(v_h_1549_, v___x_1554_);
v___x_1556_ = lean_nat_add(v_i_1542_, v___x_1551_);
lean_dec(v_i_1542_);
lean_inc(v_v_1547_);
lean_inc(v_k_1546_);
v___x_1557_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg(v_entries_1543_, v_h_1555_, v_depth_1539_, v_k_1546_, v_v_1547_);
v_i_1542_ = v___x_1556_;
v_entries_1543_ = v___x_1557_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_depth_1559_, lean_object* v_keys_1560_, lean_object* v_vals_1561_, lean_object* v_i_1562_, lean_object* v_entries_1563_){
_start:
{
size_t v_depth_boxed_1564_; lean_object* v_res_1565_; 
v_depth_boxed_1564_ = lean_unbox_usize(v_depth_1559_);
lean_dec(v_depth_1559_);
v_res_1565_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0_spec__3___redArg(v_depth_boxed_1564_, v_keys_1560_, v_vals_1561_, v_i_1562_, v_entries_1563_);
lean_dec_ref(v_vals_1561_);
lean_dec_ref(v_keys_1560_);
return v_res_1565_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg___boxed(lean_object* v_x_1566_, lean_object* v_x_1567_, lean_object* v_x_1568_, lean_object* v_x_1569_, lean_object* v_x_1570_){
_start:
{
size_t v_x_81062__boxed_1571_; size_t v_x_81063__boxed_1572_; lean_object* v_res_1573_; 
v_x_81062__boxed_1571_ = lean_unbox_usize(v_x_1567_);
lean_dec(v_x_1567_);
v_x_81063__boxed_1572_ = lean_unbox_usize(v_x_1568_);
lean_dec(v_x_1568_);
v_res_1573_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg(v_x_1566_, v_x_81062__boxed_1571_, v_x_81063__boxed_1572_, v_x_1569_, v_x_1570_);
return v_res_1573_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0___redArg(lean_object* v_x_1574_, lean_object* v_x_1575_, lean_object* v_x_1576_){
_start:
{
uint64_t v___x_1577_; size_t v___x_1578_; size_t v___x_1579_; lean_object* v___x_1580_; 
v___x_1577_ = l_Lean_Expr_hash(v_x_1575_);
v___x_1578_ = lean_uint64_to_usize(v___x_1577_);
v___x_1579_ = ((size_t)1ULL);
v___x_1580_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg(v_x_1574_, v___x_1578_, v___x_1579_, v_x_1575_, v_x_1576_);
return v___x_1580_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___lam__0(lean_object* v_a_1581_, lean_object* v_s_1582_){
_start:
{
lean_object* v_toRing_1583_; lean_object* v_invFn_x3f_1584_; lean_object* v_semiringId_x3f_1585_; lean_object* v_commSemiringInst_1586_; lean_object* v_commRingInst_1587_; lean_object* v_noZeroDivInst_x3f_1588_; lean_object* v_fieldInst_x3f_1589_; lean_object* v_powIdentityInst_x3f_1590_; lean_object* v_denoteEntries_1591_; lean_object* v_nextId_1592_; lean_object* v_steps_1593_; lean_object* v_queue_1594_; lean_object* v_basis_1595_; lean_object* v_diseqs_1596_; uint8_t v_recheck_1597_; lean_object* v_invSet_1598_; lean_object* v_powIdentityVarCount_1599_; lean_object* v_numEq0_x3f_1600_; uint8_t v_numEq0Updated_1601_; lean_object* v___x_1603_; uint8_t v_isShared_1604_; uint8_t v_isSharedCheck_1610_; 
v_toRing_1583_ = lean_ctor_get(v_s_1582_, 0);
v_invFn_x3f_1584_ = lean_ctor_get(v_s_1582_, 1);
v_semiringId_x3f_1585_ = lean_ctor_get(v_s_1582_, 2);
v_commSemiringInst_1586_ = lean_ctor_get(v_s_1582_, 3);
v_commRingInst_1587_ = lean_ctor_get(v_s_1582_, 4);
v_noZeroDivInst_x3f_1588_ = lean_ctor_get(v_s_1582_, 5);
v_fieldInst_x3f_1589_ = lean_ctor_get(v_s_1582_, 6);
v_powIdentityInst_x3f_1590_ = lean_ctor_get(v_s_1582_, 7);
v_denoteEntries_1591_ = lean_ctor_get(v_s_1582_, 8);
v_nextId_1592_ = lean_ctor_get(v_s_1582_, 9);
v_steps_1593_ = lean_ctor_get(v_s_1582_, 10);
v_queue_1594_ = lean_ctor_get(v_s_1582_, 11);
v_basis_1595_ = lean_ctor_get(v_s_1582_, 12);
v_diseqs_1596_ = lean_ctor_get(v_s_1582_, 13);
v_recheck_1597_ = lean_ctor_get_uint8(v_s_1582_, sizeof(void*)*17);
v_invSet_1598_ = lean_ctor_get(v_s_1582_, 14);
v_powIdentityVarCount_1599_ = lean_ctor_get(v_s_1582_, 15);
v_numEq0_x3f_1600_ = lean_ctor_get(v_s_1582_, 16);
v_numEq0Updated_1601_ = lean_ctor_get_uint8(v_s_1582_, sizeof(void*)*17 + 1);
v_isSharedCheck_1610_ = !lean_is_exclusive(v_s_1582_);
if (v_isSharedCheck_1610_ == 0)
{
v___x_1603_ = v_s_1582_;
v_isShared_1604_ = v_isSharedCheck_1610_;
goto v_resetjp_1602_;
}
else
{
lean_inc(v_numEq0_x3f_1600_);
lean_inc(v_powIdentityVarCount_1599_);
lean_inc(v_invSet_1598_);
lean_inc(v_diseqs_1596_);
lean_inc(v_basis_1595_);
lean_inc(v_queue_1594_);
lean_inc(v_steps_1593_);
lean_inc(v_nextId_1592_);
lean_inc(v_denoteEntries_1591_);
lean_inc(v_powIdentityInst_x3f_1590_);
lean_inc(v_fieldInst_x3f_1589_);
lean_inc(v_noZeroDivInst_x3f_1588_);
lean_inc(v_commRingInst_1587_);
lean_inc(v_commSemiringInst_1586_);
lean_inc(v_semiringId_x3f_1585_);
lean_inc(v_invFn_x3f_1584_);
lean_inc(v_toRing_1583_);
lean_dec(v_s_1582_);
v___x_1603_ = lean_box(0);
v_isShared_1604_ = v_isSharedCheck_1610_;
goto v_resetjp_1602_;
}
v_resetjp_1602_:
{
lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1608_; 
v___x_1605_ = lean_box(0);
v___x_1606_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0___redArg(v_invSet_1598_, v_a_1581_, v___x_1605_);
if (v_isShared_1604_ == 0)
{
lean_ctor_set(v___x_1603_, 14, v___x_1606_);
v___x_1608_ = v___x_1603_;
goto v_reusejp_1607_;
}
else
{
lean_object* v_reuseFailAlloc_1609_; 
v_reuseFailAlloc_1609_ = lean_alloc_ctor(0, 17, 2);
lean_ctor_set(v_reuseFailAlloc_1609_, 0, v_toRing_1583_);
lean_ctor_set(v_reuseFailAlloc_1609_, 1, v_invFn_x3f_1584_);
lean_ctor_set(v_reuseFailAlloc_1609_, 2, v_semiringId_x3f_1585_);
lean_ctor_set(v_reuseFailAlloc_1609_, 3, v_commSemiringInst_1586_);
lean_ctor_set(v_reuseFailAlloc_1609_, 4, v_commRingInst_1587_);
lean_ctor_set(v_reuseFailAlloc_1609_, 5, v_noZeroDivInst_x3f_1588_);
lean_ctor_set(v_reuseFailAlloc_1609_, 6, v_fieldInst_x3f_1589_);
lean_ctor_set(v_reuseFailAlloc_1609_, 7, v_powIdentityInst_x3f_1590_);
lean_ctor_set(v_reuseFailAlloc_1609_, 8, v_denoteEntries_1591_);
lean_ctor_set(v_reuseFailAlloc_1609_, 9, v_nextId_1592_);
lean_ctor_set(v_reuseFailAlloc_1609_, 10, v_steps_1593_);
lean_ctor_set(v_reuseFailAlloc_1609_, 11, v_queue_1594_);
lean_ctor_set(v_reuseFailAlloc_1609_, 12, v_basis_1595_);
lean_ctor_set(v_reuseFailAlloc_1609_, 13, v_diseqs_1596_);
lean_ctor_set(v_reuseFailAlloc_1609_, 14, v___x_1606_);
lean_ctor_set(v_reuseFailAlloc_1609_, 15, v_powIdentityVarCount_1599_);
lean_ctor_set(v_reuseFailAlloc_1609_, 16, v_numEq0_x3f_1600_);
lean_ctor_set_uint8(v_reuseFailAlloc_1609_, sizeof(void*)*17, v_recheck_1597_);
lean_ctor_set_uint8(v_reuseFailAlloc_1609_, sizeof(void*)*17 + 1, v_numEq0Updated_1601_);
v___x_1608_ = v_reuseFailAlloc_1609_;
goto v_reusejp_1607_;
}
v_reusejp_1607_:
{
return v___x_1608_;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__4___closed__1(void){
_start:
{
lean_object* v___x_1613_; lean_object* v___x_1614_; 
v___x_1613_ = lean_unsigned_to_nat(0u);
v___x_1614_ = lean_nat_to_int(v___x_1613_);
return v___x_1614_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__4(lean_object* v_k_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_){
_start:
{
lean_object* v___x_1633_; 
v___x_1633_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v___y_1621_, v___y_1622_, v___y_1623_, v___y_1624_, v___y_1625_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_);
if (lean_obj_tag(v___x_1633_) == 0)
{
lean_object* v_a_1634_; lean_object* v___x_1636_; uint8_t v_isShared_1637_; uint8_t v_isSharedCheck_1695_; 
v_a_1634_ = lean_ctor_get(v___x_1633_, 0);
v_isSharedCheck_1695_ = !lean_is_exclusive(v___x_1633_);
if (v_isSharedCheck_1695_ == 0)
{
v___x_1636_ = v___x_1633_;
v_isShared_1637_ = v_isSharedCheck_1695_;
goto v_resetjp_1635_;
}
else
{
lean_inc(v_a_1634_);
lean_dec(v___x_1633_);
v___x_1636_ = lean_box(0);
v_isShared_1637_ = v_isSharedCheck_1695_;
goto v_resetjp_1635_;
}
v_resetjp_1635_:
{
lean_object* v_toRing_1638_; lean_object* v_type_1639_; lean_object* v_u_1640_; lean_object* v_semiringInst_1641_; lean_object* v___x_1642_; lean_object* v_n_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v_ofNatInst_1648_; lean_object* v___y_1649_; lean_object* v___y_1650_; lean_object* v___y_1651_; lean_object* v___y_1652_; lean_object* v___y_1653_; lean_object* v___y_1654_; lean_object* v___y_1655_; lean_object* v___y_1656_; lean_object* v___y_1657_; lean_object* v___y_1658_; lean_object* v___y_1659_; lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; 
v_toRing_1638_ = lean_ctor_get(v_a_1634_, 0);
lean_inc_ref(v_toRing_1638_);
lean_dec(v_a_1634_);
v_type_1639_ = lean_ctor_get(v_toRing_1638_, 1);
lean_inc_ref_n(v_type_1639_, 2);
v_u_1640_ = lean_ctor_get(v_toRing_1638_, 2);
lean_inc(v_u_1640_);
v_semiringInst_1641_ = lean_ctor_get(v_toRing_1638_, 4);
lean_inc_ref(v_semiringInst_1641_);
lean_dec_ref(v_toRing_1638_);
v___x_1642_ = lean_nat_abs(v_k_1620_);
v_n_1643_ = l_Lean_mkRawNatLit(v___x_1642_);
v___x_1644_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__4___closed__0));
v___x_1645_ = lean_box(0);
v___x_1646_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1646_, 0, v_u_1640_);
lean_ctor_set(v___x_1646_, 1, v___x_1645_);
lean_inc_ref(v___x_1646_);
v___x_1678_ = l_Lean_mkConst(v___x_1644_, v___x_1646_);
lean_inc_ref(v_n_1643_);
v___x_1679_ = l_Lean_mkAppB(v___x_1678_, v_type_1639_, v_n_1643_);
v___x_1680_ = lean_box(0);
v___x_1681_ = l_Lean_Meta_synthInstance_x3f(v___x_1679_, v___x_1680_, v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_);
if (lean_obj_tag(v___x_1681_) == 0)
{
lean_object* v_a_1682_; 
v_a_1682_ = lean_ctor_get(v___x_1681_, 0);
lean_inc(v_a_1682_);
lean_dec_ref_known(v___x_1681_, 1);
if (lean_obj_tag(v_a_1682_) == 1)
{
lean_object* v_val_1683_; 
lean_dec_ref(v_semiringInst_1641_);
v_val_1683_ = lean_ctor_get(v_a_1682_, 0);
lean_inc(v_val_1683_);
lean_dec_ref_known(v_a_1682_, 1);
v_ofNatInst_1648_ = v_val_1683_;
v___y_1649_ = v___y_1621_;
v___y_1650_ = v___y_1622_;
v___y_1651_ = v___y_1623_;
v___y_1652_ = v___y_1624_;
v___y_1653_ = v___y_1625_;
v___y_1654_ = v___y_1626_;
v___y_1655_ = v___y_1627_;
v___y_1656_ = v___y_1628_;
v___y_1657_ = v___y_1629_;
v___y_1658_ = v___y_1630_;
v___y_1659_ = v___y_1631_;
goto v___jp_1647_;
}
else
{
lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; 
lean_dec(v_a_1682_);
v___x_1684_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__4___closed__2));
lean_inc_ref(v___x_1646_);
v___x_1685_ = l_Lean_mkConst(v___x_1684_, v___x_1646_);
lean_inc_ref(v_n_1643_);
lean_inc_ref(v_type_1639_);
v___x_1686_ = l_Lean_mkApp3(v___x_1685_, v_type_1639_, v_semiringInst_1641_, v_n_1643_);
v_ofNatInst_1648_ = v___x_1686_;
v___y_1649_ = v___y_1621_;
v___y_1650_ = v___y_1622_;
v___y_1651_ = v___y_1623_;
v___y_1652_ = v___y_1624_;
v___y_1653_ = v___y_1625_;
v___y_1654_ = v___y_1626_;
v___y_1655_ = v___y_1627_;
v___y_1656_ = v___y_1628_;
v___y_1657_ = v___y_1629_;
v___y_1658_ = v___y_1630_;
v___y_1659_ = v___y_1631_;
goto v___jp_1647_;
}
}
else
{
lean_object* v_a_1687_; lean_object* v___x_1689_; uint8_t v_isShared_1690_; uint8_t v_isSharedCheck_1694_; 
lean_dec_ref_known(v___x_1646_, 2);
lean_dec_ref(v_n_1643_);
lean_dec_ref(v_semiringInst_1641_);
lean_dec_ref(v_type_1639_);
lean_del_object(v___x_1636_);
v_a_1687_ = lean_ctor_get(v___x_1681_, 0);
v_isSharedCheck_1694_ = !lean_is_exclusive(v___x_1681_);
if (v_isSharedCheck_1694_ == 0)
{
v___x_1689_ = v___x_1681_;
v_isShared_1690_ = v_isSharedCheck_1694_;
goto v_resetjp_1688_;
}
else
{
lean_inc(v_a_1687_);
lean_dec(v___x_1681_);
v___x_1689_ = lean_box(0);
v_isShared_1690_ = v_isSharedCheck_1694_;
goto v_resetjp_1688_;
}
v_resetjp_1688_:
{
lean_object* v___x_1692_; 
if (v_isShared_1690_ == 0)
{
v___x_1692_ = v___x_1689_;
goto v_reusejp_1691_;
}
else
{
lean_object* v_reuseFailAlloc_1693_; 
v_reuseFailAlloc_1693_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1693_, 0, v_a_1687_);
v___x_1692_ = v_reuseFailAlloc_1693_;
goto v_reusejp_1691_;
}
v_reusejp_1691_:
{
return v___x_1692_;
}
}
}
v___jp_1647_:
{
lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v_n_1662_; lean_object* v___x_1663_; uint8_t v___x_1664_; 
v___x_1660_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__8));
v___x_1661_ = l_Lean_mkConst(v___x_1660_, v___x_1646_);
v_n_1662_ = l_Lean_mkApp3(v___x_1661_, v_type_1639_, v_n_1643_, v_ofNatInst_1648_);
v___x_1663_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__4___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__4___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__4___closed__1);
v___x_1664_ = lean_int_dec_lt(v_k_1620_, v___x_1663_);
if (v___x_1664_ == 0)
{
lean_object* v___x_1666_; 
if (v_isShared_1637_ == 0)
{
lean_ctor_set(v___x_1636_, 0, v_n_1662_);
v___x_1666_ = v___x_1636_;
goto v_reusejp_1665_;
}
else
{
lean_object* v_reuseFailAlloc_1667_; 
v_reuseFailAlloc_1667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1667_, 0, v_n_1662_);
v___x_1666_ = v_reuseFailAlloc_1667_;
goto v_reusejp_1665_;
}
v_reusejp_1665_:
{
return v___x_1666_;
}
}
else
{
lean_object* v___x_1668_; 
lean_del_object(v___x_1636_);
v___x_1668_ = l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0(v___y_1649_, v___y_1650_, v___y_1651_, v___y_1652_, v___y_1653_, v___y_1654_, v___y_1655_, v___y_1656_, v___y_1657_, v___y_1658_, v___y_1659_);
if (lean_obj_tag(v___x_1668_) == 0)
{
lean_object* v_a_1669_; lean_object* v___x_1671_; uint8_t v_isShared_1672_; uint8_t v_isSharedCheck_1677_; 
v_a_1669_ = lean_ctor_get(v___x_1668_, 0);
v_isSharedCheck_1677_ = !lean_is_exclusive(v___x_1668_);
if (v_isSharedCheck_1677_ == 0)
{
v___x_1671_ = v___x_1668_;
v_isShared_1672_ = v_isSharedCheck_1677_;
goto v_resetjp_1670_;
}
else
{
lean_inc(v_a_1669_);
lean_dec(v___x_1668_);
v___x_1671_ = lean_box(0);
v_isShared_1672_ = v_isSharedCheck_1677_;
goto v_resetjp_1670_;
}
v_resetjp_1670_:
{
lean_object* v___x_1673_; lean_object* v___x_1675_; 
v___x_1673_ = l_Lean_Expr_app___override(v_a_1669_, v_n_1662_);
if (v_isShared_1672_ == 0)
{
lean_ctor_set(v___x_1671_, 0, v___x_1673_);
v___x_1675_ = v___x_1671_;
goto v_reusejp_1674_;
}
else
{
lean_object* v_reuseFailAlloc_1676_; 
v_reuseFailAlloc_1676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1676_, 0, v___x_1673_);
v___x_1675_ = v_reuseFailAlloc_1676_;
goto v_reusejp_1674_;
}
v_reusejp_1674_:
{
return v___x_1675_;
}
}
}
else
{
lean_dec_ref(v_n_1662_);
return v___x_1668_;
}
}
}
}
}
else
{
lean_object* v_a_1696_; lean_object* v___x_1698_; uint8_t v_isShared_1699_; uint8_t v_isSharedCheck_1703_; 
v_a_1696_ = lean_ctor_get(v___x_1633_, 0);
v_isSharedCheck_1703_ = !lean_is_exclusive(v___x_1633_);
if (v_isSharedCheck_1703_ == 0)
{
v___x_1698_ = v___x_1633_;
v_isShared_1699_ = v_isSharedCheck_1703_;
goto v_resetjp_1697_;
}
else
{
lean_inc(v_a_1696_);
lean_dec(v___x_1633_);
v___x_1698_ = lean_box(0);
v_isShared_1699_ = v_isSharedCheck_1703_;
goto v_resetjp_1697_;
}
v_resetjp_1697_:
{
lean_object* v___x_1701_; 
if (v_isShared_1699_ == 0)
{
v___x_1701_ = v___x_1698_;
goto v_reusejp_1700_;
}
else
{
lean_object* v_reuseFailAlloc_1702_; 
v_reuseFailAlloc_1702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1702_, 0, v_a_1696_);
v___x_1701_ = v_reuseFailAlloc_1702_;
goto v_reusejp_1700_;
}
v_reusejp_1700_:
{
return v___x_1701_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__4___boxed(lean_object* v_k_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_){
_start:
{
lean_object* v_res_1717_; 
v_res_1717_ = l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__4(v_k_1704_, v___y_1705_, v___y_1706_, v___y_1707_, v___y_1708_, v___y_1709_, v___y_1710_, v___y_1711_, v___y_1712_, v___y_1713_, v___y_1714_, v___y_1715_);
lean_dec(v___y_1715_);
lean_dec_ref(v___y_1714_);
lean_dec(v___y_1713_);
lean_dec_ref(v___y_1712_);
lean_dec(v___y_1711_);
lean_dec_ref(v___y_1710_);
lean_dec(v___y_1709_);
lean_dec_ref(v___y_1708_);
lean_dec(v___y_1707_);
lean_dec(v___y_1706_);
lean_dec_ref(v___y_1705_);
lean_dec(v_k_1704_);
return v_res_1717_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1_spec__2_spec__6___redArg(lean_object* v_keys_1718_, lean_object* v_i_1719_, lean_object* v_k_1720_){
_start:
{
lean_object* v___x_1721_; uint8_t v___x_1722_; 
v___x_1721_ = lean_array_get_size(v_keys_1718_);
v___x_1722_ = lean_nat_dec_lt(v_i_1719_, v___x_1721_);
if (v___x_1722_ == 0)
{
lean_dec(v_i_1719_);
return v___x_1722_;
}
else
{
lean_object* v_k_x27_1723_; uint8_t v___x_1724_; 
v_k_x27_1723_ = lean_array_fget_borrowed(v_keys_1718_, v_i_1719_);
v___x_1724_ = lean_expr_eqv(v_k_1720_, v_k_x27_1723_);
if (v___x_1724_ == 0)
{
lean_object* v___x_1725_; lean_object* v___x_1726_; 
v___x_1725_ = lean_unsigned_to_nat(1u);
v___x_1726_ = lean_nat_add(v_i_1719_, v___x_1725_);
lean_dec(v_i_1719_);
v_i_1719_ = v___x_1726_;
goto _start;
}
else
{
lean_dec(v_i_1719_);
return v___x_1722_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1_spec__2_spec__6___redArg___boxed(lean_object* v_keys_1728_, lean_object* v_i_1729_, lean_object* v_k_1730_){
_start:
{
uint8_t v_res_1731_; lean_object* v_r_1732_; 
v_res_1731_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1_spec__2_spec__6___redArg(v_keys_1728_, v_i_1729_, v_k_1730_);
lean_dec_ref(v_k_1730_);
lean_dec_ref(v_keys_1728_);
v_r_1732_ = lean_box(v_res_1731_);
return v_r_1732_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1_spec__2___redArg(lean_object* v_x_1733_, size_t v_x_1734_, lean_object* v_x_1735_){
_start:
{
if (lean_obj_tag(v_x_1733_) == 0)
{
lean_object* v_es_1736_; lean_object* v___x_1737_; size_t v___x_1738_; size_t v___x_1739_; lean_object* v_j_1740_; lean_object* v___x_1741_; 
v_es_1736_ = lean_ctor_get(v_x_1733_, 0);
v___x_1737_ = lean_box(2);
v___x_1738_ = ((size_t)31ULL);
v___x_1739_ = lean_usize_land(v_x_1734_, v___x_1738_);
v_j_1740_ = lean_usize_to_nat(v___x_1739_);
v___x_1741_ = lean_array_get_borrowed(v___x_1737_, v_es_1736_, v_j_1740_);
lean_dec(v_j_1740_);
switch(lean_obj_tag(v___x_1741_))
{
case 0:
{
lean_object* v_key_1742_; uint8_t v___x_1743_; 
v_key_1742_ = lean_ctor_get(v___x_1741_, 0);
v___x_1743_ = lean_expr_eqv(v_x_1735_, v_key_1742_);
return v___x_1743_;
}
case 1:
{
lean_object* v_node_1744_; size_t v___x_1745_; size_t v___x_1746_; 
v_node_1744_ = lean_ctor_get(v___x_1741_, 0);
v___x_1745_ = ((size_t)5ULL);
v___x_1746_ = lean_usize_shift_right(v_x_1734_, v___x_1745_);
v_x_1733_ = v_node_1744_;
v_x_1734_ = v___x_1746_;
goto _start;
}
default: 
{
uint8_t v___x_1748_; 
v___x_1748_ = 0;
return v___x_1748_;
}
}
}
else
{
lean_object* v_ks_1749_; lean_object* v___x_1750_; uint8_t v___x_1751_; 
v_ks_1749_ = lean_ctor_get(v_x_1733_, 0);
v___x_1750_ = lean_unsigned_to_nat(0u);
v___x_1751_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1_spec__2_spec__6___redArg(v_ks_1749_, v___x_1750_, v_x_1735_);
return v___x_1751_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1_spec__2___redArg___boxed(lean_object* v_x_1752_, lean_object* v_x_1753_, lean_object* v_x_1754_){
_start:
{
size_t v_x_81459__boxed_1755_; uint8_t v_res_1756_; lean_object* v_r_1757_; 
v_x_81459__boxed_1755_ = lean_unbox_usize(v_x_1753_);
lean_dec(v_x_1753_);
v_res_1756_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1_spec__2___redArg(v_x_1752_, v_x_81459__boxed_1755_, v_x_1754_);
lean_dec_ref(v_x_1754_);
lean_dec_ref(v_x_1752_);
v_r_1757_ = lean_box(v_res_1756_);
return v_r_1757_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1___redArg(lean_object* v_x_1758_, lean_object* v_x_1759_){
_start:
{
uint64_t v___x_1760_; size_t v___x_1761_; uint8_t v___x_1762_; 
v___x_1760_ = l_Lean_Expr_hash(v_x_1759_);
v___x_1761_ = lean_uint64_to_usize(v___x_1760_);
v___x_1762_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1_spec__2___redArg(v_x_1758_, v___x_1761_, v_x_1759_);
return v___x_1762_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1___redArg___boxed(lean_object* v_x_1763_, lean_object* v_x_1764_){
_start:
{
uint8_t v_res_1765_; lean_object* v_r_1766_; 
v_res_1765_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1___redArg(v_x_1763_, v_x_1764_);
lean_dec_ref(v_x_1764_);
lean_dec_ref(v_x_1763_);
v_r_1766_ = lean_box(v_res_1765_);
return v_r_1766_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__3___lam__0(lean_object* v_a_1767_, lean_object* v_s_1768_){
_start:
{
lean_object* v_toRing_1769_; lean_object* v_invFn_x3f_1770_; lean_object* v_semiringId_x3f_1771_; lean_object* v_commSemiringInst_1772_; lean_object* v_commRingInst_1773_; lean_object* v_noZeroDivInst_x3f_1774_; lean_object* v_fieldInst_x3f_1775_; lean_object* v_powIdentityInst_x3f_1776_; lean_object* v_denoteEntries_1777_; lean_object* v_nextId_1778_; lean_object* v_steps_1779_; lean_object* v_queue_1780_; lean_object* v_basis_1781_; lean_object* v_diseqs_1782_; uint8_t v_recheck_1783_; lean_object* v_invSet_1784_; lean_object* v_powIdentityVarCount_1785_; lean_object* v_numEq0_x3f_1786_; uint8_t v_numEq0Updated_1787_; lean_object* v___x_1789_; uint8_t v_isShared_1790_; uint8_t v_isSharedCheck_1819_; 
v_toRing_1769_ = lean_ctor_get(v_s_1768_, 0);
v_invFn_x3f_1770_ = lean_ctor_get(v_s_1768_, 1);
v_semiringId_x3f_1771_ = lean_ctor_get(v_s_1768_, 2);
v_commSemiringInst_1772_ = lean_ctor_get(v_s_1768_, 3);
v_commRingInst_1773_ = lean_ctor_get(v_s_1768_, 4);
v_noZeroDivInst_x3f_1774_ = lean_ctor_get(v_s_1768_, 5);
v_fieldInst_x3f_1775_ = lean_ctor_get(v_s_1768_, 6);
v_powIdentityInst_x3f_1776_ = lean_ctor_get(v_s_1768_, 7);
v_denoteEntries_1777_ = lean_ctor_get(v_s_1768_, 8);
v_nextId_1778_ = lean_ctor_get(v_s_1768_, 9);
v_steps_1779_ = lean_ctor_get(v_s_1768_, 10);
v_queue_1780_ = lean_ctor_get(v_s_1768_, 11);
v_basis_1781_ = lean_ctor_get(v_s_1768_, 12);
v_diseqs_1782_ = lean_ctor_get(v_s_1768_, 13);
v_recheck_1783_ = lean_ctor_get_uint8(v_s_1768_, sizeof(void*)*17);
v_invSet_1784_ = lean_ctor_get(v_s_1768_, 14);
v_powIdentityVarCount_1785_ = lean_ctor_get(v_s_1768_, 15);
v_numEq0_x3f_1786_ = lean_ctor_get(v_s_1768_, 16);
v_numEq0Updated_1787_ = lean_ctor_get_uint8(v_s_1768_, sizeof(void*)*17 + 1);
v_isSharedCheck_1819_ = !lean_is_exclusive(v_s_1768_);
if (v_isSharedCheck_1819_ == 0)
{
v___x_1789_ = v_s_1768_;
v_isShared_1790_ = v_isSharedCheck_1819_;
goto v_resetjp_1788_;
}
else
{
lean_inc(v_numEq0_x3f_1786_);
lean_inc(v_powIdentityVarCount_1785_);
lean_inc(v_invSet_1784_);
lean_inc(v_diseqs_1782_);
lean_inc(v_basis_1781_);
lean_inc(v_queue_1780_);
lean_inc(v_steps_1779_);
lean_inc(v_nextId_1778_);
lean_inc(v_denoteEntries_1777_);
lean_inc(v_powIdentityInst_x3f_1776_);
lean_inc(v_fieldInst_x3f_1775_);
lean_inc(v_noZeroDivInst_x3f_1774_);
lean_inc(v_commRingInst_1773_);
lean_inc(v_commSemiringInst_1772_);
lean_inc(v_semiringId_x3f_1771_);
lean_inc(v_invFn_x3f_1770_);
lean_inc(v_toRing_1769_);
lean_dec(v_s_1768_);
v___x_1789_ = lean_box(0);
v_isShared_1790_ = v_isSharedCheck_1819_;
goto v_resetjp_1788_;
}
v_resetjp_1788_:
{
lean_object* v_id_1791_; lean_object* v_type_1792_; lean_object* v_u_1793_; lean_object* v_ringInst_1794_; lean_object* v_semiringInst_1795_; lean_object* v_charInst_x3f_1796_; lean_object* v_addFn_x3f_1797_; lean_object* v_subFn_x3f_1798_; lean_object* v_negFn_x3f_1799_; lean_object* v_powFn_x3f_1800_; lean_object* v_intCastFn_x3f_1801_; lean_object* v_natCastFn_x3f_1802_; lean_object* v_one_x3f_1803_; lean_object* v_vars_1804_; lean_object* v_varMap_1805_; lean_object* v_denote_1806_; lean_object* v___x_1808_; uint8_t v_isShared_1809_; uint8_t v_isSharedCheck_1817_; 
v_id_1791_ = lean_ctor_get(v_toRing_1769_, 0);
v_type_1792_ = lean_ctor_get(v_toRing_1769_, 1);
v_u_1793_ = lean_ctor_get(v_toRing_1769_, 2);
v_ringInst_1794_ = lean_ctor_get(v_toRing_1769_, 3);
v_semiringInst_1795_ = lean_ctor_get(v_toRing_1769_, 4);
v_charInst_x3f_1796_ = lean_ctor_get(v_toRing_1769_, 5);
v_addFn_x3f_1797_ = lean_ctor_get(v_toRing_1769_, 6);
v_subFn_x3f_1798_ = lean_ctor_get(v_toRing_1769_, 8);
v_negFn_x3f_1799_ = lean_ctor_get(v_toRing_1769_, 9);
v_powFn_x3f_1800_ = lean_ctor_get(v_toRing_1769_, 10);
v_intCastFn_x3f_1801_ = lean_ctor_get(v_toRing_1769_, 11);
v_natCastFn_x3f_1802_ = lean_ctor_get(v_toRing_1769_, 12);
v_one_x3f_1803_ = lean_ctor_get(v_toRing_1769_, 13);
v_vars_1804_ = lean_ctor_get(v_toRing_1769_, 14);
v_varMap_1805_ = lean_ctor_get(v_toRing_1769_, 15);
v_denote_1806_ = lean_ctor_get(v_toRing_1769_, 16);
v_isSharedCheck_1817_ = !lean_is_exclusive(v_toRing_1769_);
if (v_isSharedCheck_1817_ == 0)
{
lean_object* v_unused_1818_; 
v_unused_1818_ = lean_ctor_get(v_toRing_1769_, 7);
lean_dec(v_unused_1818_);
v___x_1808_ = v_toRing_1769_;
v_isShared_1809_ = v_isSharedCheck_1817_;
goto v_resetjp_1807_;
}
else
{
lean_inc(v_denote_1806_);
lean_inc(v_varMap_1805_);
lean_inc(v_vars_1804_);
lean_inc(v_one_x3f_1803_);
lean_inc(v_natCastFn_x3f_1802_);
lean_inc(v_intCastFn_x3f_1801_);
lean_inc(v_powFn_x3f_1800_);
lean_inc(v_negFn_x3f_1799_);
lean_inc(v_subFn_x3f_1798_);
lean_inc(v_addFn_x3f_1797_);
lean_inc(v_charInst_x3f_1796_);
lean_inc(v_semiringInst_1795_);
lean_inc(v_ringInst_1794_);
lean_inc(v_u_1793_);
lean_inc(v_type_1792_);
lean_inc(v_id_1791_);
lean_dec(v_toRing_1769_);
v___x_1808_ = lean_box(0);
v_isShared_1809_ = v_isSharedCheck_1817_;
goto v_resetjp_1807_;
}
v_resetjp_1807_:
{
lean_object* v___x_1810_; lean_object* v___x_1812_; 
v___x_1810_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1810_, 0, v_a_1767_);
if (v_isShared_1809_ == 0)
{
lean_ctor_set(v___x_1808_, 7, v___x_1810_);
v___x_1812_ = v___x_1808_;
goto v_reusejp_1811_;
}
else
{
lean_object* v_reuseFailAlloc_1816_; 
v_reuseFailAlloc_1816_ = lean_alloc_ctor(0, 17, 0);
lean_ctor_set(v_reuseFailAlloc_1816_, 0, v_id_1791_);
lean_ctor_set(v_reuseFailAlloc_1816_, 1, v_type_1792_);
lean_ctor_set(v_reuseFailAlloc_1816_, 2, v_u_1793_);
lean_ctor_set(v_reuseFailAlloc_1816_, 3, v_ringInst_1794_);
lean_ctor_set(v_reuseFailAlloc_1816_, 4, v_semiringInst_1795_);
lean_ctor_set(v_reuseFailAlloc_1816_, 5, v_charInst_x3f_1796_);
lean_ctor_set(v_reuseFailAlloc_1816_, 6, v_addFn_x3f_1797_);
lean_ctor_set(v_reuseFailAlloc_1816_, 7, v___x_1810_);
lean_ctor_set(v_reuseFailAlloc_1816_, 8, v_subFn_x3f_1798_);
lean_ctor_set(v_reuseFailAlloc_1816_, 9, v_negFn_x3f_1799_);
lean_ctor_set(v_reuseFailAlloc_1816_, 10, v_powFn_x3f_1800_);
lean_ctor_set(v_reuseFailAlloc_1816_, 11, v_intCastFn_x3f_1801_);
lean_ctor_set(v_reuseFailAlloc_1816_, 12, v_natCastFn_x3f_1802_);
lean_ctor_set(v_reuseFailAlloc_1816_, 13, v_one_x3f_1803_);
lean_ctor_set(v_reuseFailAlloc_1816_, 14, v_vars_1804_);
lean_ctor_set(v_reuseFailAlloc_1816_, 15, v_varMap_1805_);
lean_ctor_set(v_reuseFailAlloc_1816_, 16, v_denote_1806_);
v___x_1812_ = v_reuseFailAlloc_1816_;
goto v_reusejp_1811_;
}
v_reusejp_1811_:
{
lean_object* v___x_1814_; 
if (v_isShared_1790_ == 0)
{
lean_ctor_set(v___x_1789_, 0, v___x_1812_);
v___x_1814_ = v___x_1789_;
goto v_reusejp_1813_;
}
else
{
lean_object* v_reuseFailAlloc_1815_; 
v_reuseFailAlloc_1815_ = lean_alloc_ctor(0, 17, 2);
lean_ctor_set(v_reuseFailAlloc_1815_, 0, v___x_1812_);
lean_ctor_set(v_reuseFailAlloc_1815_, 1, v_invFn_x3f_1770_);
lean_ctor_set(v_reuseFailAlloc_1815_, 2, v_semiringId_x3f_1771_);
lean_ctor_set(v_reuseFailAlloc_1815_, 3, v_commSemiringInst_1772_);
lean_ctor_set(v_reuseFailAlloc_1815_, 4, v_commRingInst_1773_);
lean_ctor_set(v_reuseFailAlloc_1815_, 5, v_noZeroDivInst_x3f_1774_);
lean_ctor_set(v_reuseFailAlloc_1815_, 6, v_fieldInst_x3f_1775_);
lean_ctor_set(v_reuseFailAlloc_1815_, 7, v_powIdentityInst_x3f_1776_);
lean_ctor_set(v_reuseFailAlloc_1815_, 8, v_denoteEntries_1777_);
lean_ctor_set(v_reuseFailAlloc_1815_, 9, v_nextId_1778_);
lean_ctor_set(v_reuseFailAlloc_1815_, 10, v_steps_1779_);
lean_ctor_set(v_reuseFailAlloc_1815_, 11, v_queue_1780_);
lean_ctor_set(v_reuseFailAlloc_1815_, 12, v_basis_1781_);
lean_ctor_set(v_reuseFailAlloc_1815_, 13, v_diseqs_1782_);
lean_ctor_set(v_reuseFailAlloc_1815_, 14, v_invSet_1784_);
lean_ctor_set(v_reuseFailAlloc_1815_, 15, v_powIdentityVarCount_1785_);
lean_ctor_set(v_reuseFailAlloc_1815_, 16, v_numEq0_x3f_1786_);
lean_ctor_set_uint8(v_reuseFailAlloc_1815_, sizeof(void*)*17, v_recheck_1783_);
lean_ctor_set_uint8(v_reuseFailAlloc_1815_, sizeof(void*)*17 + 1, v_numEq0Updated_1787_);
v___x_1814_ = v_reuseFailAlloc_1815_;
goto v_reusejp_1813_;
}
v_reusejp_1813_:
{
return v___x_1814_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__3_spec__5(lean_object* v_type_1820_, lean_object* v_u_1821_, lean_object* v_instDeclName_1822_, lean_object* v_declName_1823_, lean_object* v_expectedInst_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_){
_start:
{
lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; 
v___x_1837_ = lean_box(0);
lean_inc_n(v_u_1821_, 2);
v___x_1838_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1838_, 0, v_u_1821_);
lean_ctor_set(v___x_1838_, 1, v___x_1837_);
v___x_1839_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1839_, 0, v_u_1821_);
lean_ctor_set(v___x_1839_, 1, v___x_1838_);
v___x_1840_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1840_, 0, v_u_1821_);
lean_ctor_set(v___x_1840_, 1, v___x_1839_);
lean_inc_ref(v___x_1840_);
v___x_1841_ = l_Lean_mkConst(v_instDeclName_1822_, v___x_1840_);
lean_inc_ref_n(v_type_1820_, 3);
v___x_1842_ = l_Lean_mkApp3(v___x_1841_, v_type_1820_, v_type_1820_, v_type_1820_);
v___x_1843_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1_spec__5(v___x_1842_, v___y_1825_, v___y_1826_, v___y_1827_, v___y_1828_, v___y_1829_, v___y_1830_, v___y_1831_, v___y_1832_, v___y_1833_, v___y_1834_, v___y_1835_);
if (lean_obj_tag(v___x_1843_) == 0)
{
lean_object* v_a_1844_; lean_object* v___x_1845_; 
v_a_1844_ = lean_ctor_get(v___x_1843_, 0);
lean_inc_n(v_a_1844_, 2);
lean_dec_ref_known(v___x_1843_, 1);
lean_inc(v_declName_1823_);
v___x_1845_ = l_Lean_Meta_Grind_Arith_CommRing_checkInst(v_declName_1823_, v_a_1844_, v_expectedInst_1824_, v___y_1832_, v___y_1833_, v___y_1834_, v___y_1835_);
if (lean_obj_tag(v___x_1845_) == 0)
{
lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; 
lean_dec_ref_known(v___x_1845_, 1);
v___x_1846_ = l_Lean_mkConst(v_declName_1823_, v___x_1840_);
lean_inc_ref_n(v_type_1820_, 2);
v___x_1847_ = l_Lean_mkApp4(v___x_1846_, v_type_1820_, v_type_1820_, v_type_1820_, v_a_1844_);
v___x_1848_ = l_Lean_Meta_Sym_canon(v___x_1847_, v___y_1830_, v___y_1831_, v___y_1832_, v___y_1833_, v___y_1834_, v___y_1835_);
if (lean_obj_tag(v___x_1848_) == 0)
{
lean_object* v_a_1849_; lean_object* v___x_1850_; 
v_a_1849_ = lean_ctor_get(v___x_1848_, 0);
lean_inc(v_a_1849_);
lean_dec_ref_known(v___x_1848_, 1);
v___x_1850_ = l_Lean_Meta_Sym_shareCommon(v_a_1849_, v___y_1830_, v___y_1831_, v___y_1832_, v___y_1833_, v___y_1834_, v___y_1835_);
return v___x_1850_;
}
else
{
return v___x_1848_;
}
}
else
{
lean_object* v_a_1851_; lean_object* v___x_1853_; uint8_t v_isShared_1854_; uint8_t v_isSharedCheck_1858_; 
lean_dec(v_a_1844_);
lean_dec_ref_known(v___x_1840_, 2);
lean_dec(v_declName_1823_);
lean_dec_ref(v_type_1820_);
v_a_1851_ = lean_ctor_get(v___x_1845_, 0);
v_isSharedCheck_1858_ = !lean_is_exclusive(v___x_1845_);
if (v_isSharedCheck_1858_ == 0)
{
v___x_1853_ = v___x_1845_;
v_isShared_1854_ = v_isSharedCheck_1858_;
goto v_resetjp_1852_;
}
else
{
lean_inc(v_a_1851_);
lean_dec(v___x_1845_);
v___x_1853_ = lean_box(0);
v_isShared_1854_ = v_isSharedCheck_1858_;
goto v_resetjp_1852_;
}
v_resetjp_1852_:
{
lean_object* v___x_1856_; 
if (v_isShared_1854_ == 0)
{
v___x_1856_ = v___x_1853_;
goto v_reusejp_1855_;
}
else
{
lean_object* v_reuseFailAlloc_1857_; 
v_reuseFailAlloc_1857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1857_, 0, v_a_1851_);
v___x_1856_ = v_reuseFailAlloc_1857_;
goto v_reusejp_1855_;
}
v_reusejp_1855_:
{
return v___x_1856_;
}
}
}
}
else
{
lean_dec_ref_known(v___x_1840_, 2);
lean_dec_ref(v_expectedInst_1824_);
lean_dec(v_declName_1823_);
lean_dec_ref(v_type_1820_);
return v___x_1843_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__3_spec__5___boxed(lean_object** _args){
lean_object* v_type_1859_ = _args[0];
lean_object* v_u_1860_ = _args[1];
lean_object* v_instDeclName_1861_ = _args[2];
lean_object* v_declName_1862_ = _args[3];
lean_object* v_expectedInst_1863_ = _args[4];
lean_object* v___y_1864_ = _args[5];
lean_object* v___y_1865_ = _args[6];
lean_object* v___y_1866_ = _args[7];
lean_object* v___y_1867_ = _args[8];
lean_object* v___y_1868_ = _args[9];
lean_object* v___y_1869_ = _args[10];
lean_object* v___y_1870_ = _args[11];
lean_object* v___y_1871_ = _args[12];
lean_object* v___y_1872_ = _args[13];
lean_object* v___y_1873_ = _args[14];
lean_object* v___y_1874_ = _args[15];
lean_object* v___y_1875_ = _args[16];
_start:
{
lean_object* v_res_1876_; 
v_res_1876_ = l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__3_spec__5(v_type_1859_, v_u_1860_, v_instDeclName_1861_, v_declName_1862_, v_expectedInst_1863_, v___y_1864_, v___y_1865_, v___y_1866_, v___y_1867_, v___y_1868_, v___y_1869_, v___y_1870_, v___y_1871_, v___y_1872_, v___y_1873_, v___y_1874_);
lean_dec(v___y_1874_);
lean_dec_ref(v___y_1873_);
lean_dec(v___y_1872_);
lean_dec_ref(v___y_1871_);
lean_dec(v___y_1870_);
lean_dec_ref(v___y_1869_);
lean_dec(v___y_1868_);
lean_dec_ref(v___y_1867_);
lean_dec(v___y_1866_);
lean_dec(v___y_1865_);
lean_dec_ref(v___y_1864_);
return v_res_1876_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__3(lean_object* v___y_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_){
_start:
{
lean_object* v___x_1900_; 
v___x_1900_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v___y_1888_, v___y_1889_, v___y_1890_, v___y_1891_, v___y_1892_, v___y_1893_, v___y_1894_, v___y_1895_, v___y_1896_, v___y_1897_, v___y_1898_);
if (lean_obj_tag(v___x_1900_) == 0)
{
lean_object* v_a_1901_; lean_object* v___x_1903_; uint8_t v_isShared_1904_; uint8_t v_isSharedCheck_1944_; 
v_a_1901_ = lean_ctor_get(v___x_1900_, 0);
v_isSharedCheck_1944_ = !lean_is_exclusive(v___x_1900_);
if (v_isSharedCheck_1944_ == 0)
{
v___x_1903_ = v___x_1900_;
v_isShared_1904_ = v_isSharedCheck_1944_;
goto v_resetjp_1902_;
}
else
{
lean_inc(v_a_1901_);
lean_dec(v___x_1900_);
v___x_1903_ = lean_box(0);
v_isShared_1904_ = v_isSharedCheck_1944_;
goto v_resetjp_1902_;
}
v_resetjp_1902_:
{
lean_object* v_toRing_1905_; lean_object* v_mulFn_x3f_1906_; 
v_toRing_1905_ = lean_ctor_get(v_a_1901_, 0);
lean_inc_ref(v_toRing_1905_);
lean_dec(v_a_1901_);
v_mulFn_x3f_1906_ = lean_ctor_get(v_toRing_1905_, 7);
if (lean_obj_tag(v_mulFn_x3f_1906_) == 1)
{
lean_object* v_val_1907_; lean_object* v___x_1909_; 
lean_inc_ref(v_mulFn_x3f_1906_);
lean_dec_ref(v_toRing_1905_);
v_val_1907_ = lean_ctor_get(v_mulFn_x3f_1906_, 0);
lean_inc(v_val_1907_);
lean_dec_ref_known(v_mulFn_x3f_1906_, 1);
if (v_isShared_1904_ == 0)
{
lean_ctor_set(v___x_1903_, 0, v_val_1907_);
v___x_1909_ = v___x_1903_;
goto v_reusejp_1908_;
}
else
{
lean_object* v_reuseFailAlloc_1910_; 
v_reuseFailAlloc_1910_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1910_, 0, v_val_1907_);
v___x_1909_ = v_reuseFailAlloc_1910_;
goto v_reusejp_1908_;
}
v_reusejp_1908_:
{
return v___x_1909_;
}
}
else
{
lean_object* v_type_1911_; lean_object* v_u_1912_; lean_object* v_semiringInst_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v_expectedInst_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; 
lean_del_object(v___x_1903_);
v_type_1911_ = lean_ctor_get(v_toRing_1905_, 1);
lean_inc_ref_n(v_type_1911_, 3);
v_u_1912_ = lean_ctor_get(v_toRing_1905_, 2);
lean_inc_n(v_u_1912_, 2);
v_semiringInst_1913_ = lean_ctor_get(v_toRing_1905_, 4);
lean_inc_ref(v_semiringInst_1913_);
lean_dec_ref(v_toRing_1905_);
v___x_1914_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__3___closed__1));
v___x_1915_ = lean_box(0);
v___x_1916_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1916_, 0, v_u_1912_);
lean_ctor_set(v___x_1916_, 1, v___x_1915_);
lean_inc_ref(v___x_1916_);
v___x_1917_ = l_Lean_mkConst(v___x_1914_, v___x_1916_);
v___x_1918_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__3___closed__3));
v___x_1919_ = l_Lean_mkConst(v___x_1918_, v___x_1916_);
v___x_1920_ = l_Lean_mkAppB(v___x_1919_, v_type_1911_, v_semiringInst_1913_);
v_expectedInst_1921_ = l_Lean_mkAppB(v___x_1917_, v_type_1911_, v___x_1920_);
v___x_1922_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__3___closed__4));
v___x_1923_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__20));
v___x_1924_ = l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__3_spec__5(v_type_1911_, v_u_1912_, v___x_1922_, v___x_1923_, v_expectedInst_1921_, v___y_1888_, v___y_1889_, v___y_1890_, v___y_1891_, v___y_1892_, v___y_1893_, v___y_1894_, v___y_1895_, v___y_1896_, v___y_1897_, v___y_1898_);
if (lean_obj_tag(v___x_1924_) == 0)
{
lean_object* v_a_1925_; lean_object* v___f_1926_; lean_object* v___x_1927_; 
v_a_1925_ = lean_ctor_get(v___x_1924_, 0);
lean_inc_n(v_a_1925_, 2);
lean_dec_ref_known(v___x_1924_, 1);
v___f_1926_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__3___lam__0), 2, 1);
lean_closure_set(v___f_1926_, 0, v_a_1925_);
v___x_1927_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(v___f_1926_, v___y_1888_, v___y_1889_);
if (lean_obj_tag(v___x_1927_) == 0)
{
lean_object* v___x_1929_; uint8_t v_isShared_1930_; uint8_t v_isSharedCheck_1934_; 
v_isSharedCheck_1934_ = !lean_is_exclusive(v___x_1927_);
if (v_isSharedCheck_1934_ == 0)
{
lean_object* v_unused_1935_; 
v_unused_1935_ = lean_ctor_get(v___x_1927_, 0);
lean_dec(v_unused_1935_);
v___x_1929_ = v___x_1927_;
v_isShared_1930_ = v_isSharedCheck_1934_;
goto v_resetjp_1928_;
}
else
{
lean_dec(v___x_1927_);
v___x_1929_ = lean_box(0);
v_isShared_1930_ = v_isSharedCheck_1934_;
goto v_resetjp_1928_;
}
v_resetjp_1928_:
{
lean_object* v___x_1932_; 
if (v_isShared_1930_ == 0)
{
lean_ctor_set(v___x_1929_, 0, v_a_1925_);
v___x_1932_ = v___x_1929_;
goto v_reusejp_1931_;
}
else
{
lean_object* v_reuseFailAlloc_1933_; 
v_reuseFailAlloc_1933_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1933_, 0, v_a_1925_);
v___x_1932_ = v_reuseFailAlloc_1933_;
goto v_reusejp_1931_;
}
v_reusejp_1931_:
{
return v___x_1932_;
}
}
}
else
{
lean_object* v_a_1936_; lean_object* v___x_1938_; uint8_t v_isShared_1939_; uint8_t v_isSharedCheck_1943_; 
lean_dec(v_a_1925_);
v_a_1936_ = lean_ctor_get(v___x_1927_, 0);
v_isSharedCheck_1943_ = !lean_is_exclusive(v___x_1927_);
if (v_isSharedCheck_1943_ == 0)
{
v___x_1938_ = v___x_1927_;
v_isShared_1939_ = v_isSharedCheck_1943_;
goto v_resetjp_1937_;
}
else
{
lean_inc(v_a_1936_);
lean_dec(v___x_1927_);
v___x_1938_ = lean_box(0);
v_isShared_1939_ = v_isSharedCheck_1943_;
goto v_resetjp_1937_;
}
v_resetjp_1937_:
{
lean_object* v___x_1941_; 
if (v_isShared_1939_ == 0)
{
v___x_1941_ = v___x_1938_;
goto v_reusejp_1940_;
}
else
{
lean_object* v_reuseFailAlloc_1942_; 
v_reuseFailAlloc_1942_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1942_, 0, v_a_1936_);
v___x_1941_ = v_reuseFailAlloc_1942_;
goto v_reusejp_1940_;
}
v_reusejp_1940_:
{
return v___x_1941_;
}
}
}
}
else
{
return v___x_1924_;
}
}
}
}
else
{
lean_object* v_a_1945_; lean_object* v___x_1947_; uint8_t v_isShared_1948_; uint8_t v_isSharedCheck_1952_; 
v_a_1945_ = lean_ctor_get(v___x_1900_, 0);
v_isSharedCheck_1952_ = !lean_is_exclusive(v___x_1900_);
if (v_isSharedCheck_1952_ == 0)
{
v___x_1947_ = v___x_1900_;
v_isShared_1948_ = v_isSharedCheck_1952_;
goto v_resetjp_1946_;
}
else
{
lean_inc(v_a_1945_);
lean_dec(v___x_1900_);
v___x_1947_ = lean_box(0);
v_isShared_1948_ = v_isSharedCheck_1952_;
goto v_resetjp_1946_;
}
v_resetjp_1946_:
{
lean_object* v___x_1950_; 
if (v_isShared_1948_ == 0)
{
v___x_1950_ = v___x_1947_;
goto v_reusejp_1949_;
}
else
{
lean_object* v_reuseFailAlloc_1951_; 
v_reuseFailAlloc_1951_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1951_, 0, v_a_1945_);
v___x_1950_ = v_reuseFailAlloc_1951_;
goto v_reusejp_1949_;
}
v_reusejp_1949_:
{
return v___x_1950_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__3___boxed(lean_object* v___y_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_){
_start:
{
lean_object* v_res_1965_; 
v_res_1965_ = l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__3(v___y_1953_, v___y_1954_, v___y_1955_, v___y_1956_, v___y_1957_, v___y_1958_, v___y_1959_, v___y_1960_, v___y_1961_, v___y_1962_, v___y_1963_);
lean_dec(v___y_1963_);
lean_dec_ref(v___y_1962_);
lean_dec(v___y_1961_);
lean_dec_ref(v___y_1960_);
lean_dec(v___y_1959_);
lean_dec_ref(v___y_1958_);
lean_dec(v___y_1957_);
lean_dec_ref(v___y_1956_);
lean_dec(v___y_1955_);
lean_dec(v___y_1954_);
lean_dec_ref(v___y_1953_);
return v_res_1965_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__3(void){
_start:
{
lean_object* v___x_1973_; lean_object* v___x_1974_; 
v___x_1973_ = lean_unsigned_to_nat(1u);
v___x_1974_ = lean_nat_to_int(v___x_1973_);
return v___x_1974_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv(lean_object* v_e_1999_, lean_object* v_inst_2000_, lean_object* v_a_2001_, lean_object* v_a_2002_, lean_object* v_a_2003_, lean_object* v_a_2004_, lean_object* v_a_2005_, lean_object* v_a_2006_, lean_object* v_a_2007_, lean_object* v_a_2008_, lean_object* v_a_2009_, lean_object* v_a_2010_, lean_object* v_a_2011_, lean_object* v_a_2012_){
_start:
{
lean_object* v___f_2017_; lean_object* v___x_2018_; 
lean_inc_ref(v_a_2001_);
v___f_2017_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___lam__0), 2, 1);
lean_closure_set(v___f_2017_, 0, v_a_2001_);
v___x_2018_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst(v_inst_2000_, v_a_2002_, v_a_2003_, v_a_2004_, v_a_2005_, v_a_2006_, v_a_2007_, v_a_2008_, v_a_2009_, v_a_2010_, v_a_2011_, v_a_2012_);
if (lean_obj_tag(v___x_2018_) == 0)
{
lean_object* v_a_2019_; lean_object* v___x_2021_; uint8_t v_isShared_2022_; uint8_t v_isSharedCheck_2277_; 
v_a_2019_ = lean_ctor_get(v___x_2018_, 0);
v_isSharedCheck_2277_ = !lean_is_exclusive(v___x_2018_);
if (v_isSharedCheck_2277_ == 0)
{
v___x_2021_ = v___x_2018_;
v_isShared_2022_ = v_isSharedCheck_2277_;
goto v_resetjp_2020_;
}
else
{
lean_inc(v_a_2019_);
lean_dec(v___x_2018_);
v___x_2021_ = lean_box(0);
v_isShared_2022_ = v_isSharedCheck_2277_;
goto v_resetjp_2020_;
}
v_resetjp_2020_:
{
uint8_t v___x_2023_; 
v___x_2023_ = lean_unbox(v_a_2019_);
lean_dec(v_a_2019_);
if (v___x_2023_ == 0)
{
lean_object* v___x_2024_; lean_object* v___x_2026_; 
lean_dec_ref(v___f_2017_);
lean_dec_ref(v_a_2001_);
lean_dec_ref(v_e_1999_);
v___x_2024_ = lean_box(0);
if (v_isShared_2022_ == 0)
{
lean_ctor_set(v___x_2021_, 0, v___x_2024_);
v___x_2026_ = v___x_2021_;
goto v_reusejp_2025_;
}
else
{
lean_object* v_reuseFailAlloc_2027_; 
v_reuseFailAlloc_2027_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2027_, 0, v___x_2024_);
v___x_2026_ = v_reuseFailAlloc_2027_;
goto v_reusejp_2025_;
}
v_reusejp_2025_:
{
return v___x_2026_;
}
}
else
{
lean_object* v___x_2028_; 
lean_del_object(v___x_2021_);
v___x_2028_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v_a_2002_, v_a_2003_, v_a_2004_, v_a_2005_, v_a_2006_, v_a_2007_, v_a_2008_, v_a_2009_, v_a_2010_, v_a_2011_, v_a_2012_);
if (lean_obj_tag(v___x_2028_) == 0)
{
lean_object* v_a_2029_; lean_object* v___x_2031_; uint8_t v_isShared_2032_; uint8_t v_isSharedCheck_2268_; 
v_a_2029_ = lean_ctor_get(v___x_2028_, 0);
v_isSharedCheck_2268_ = !lean_is_exclusive(v___x_2028_);
if (v_isSharedCheck_2268_ == 0)
{
v___x_2031_ = v___x_2028_;
v_isShared_2032_ = v_isSharedCheck_2268_;
goto v_resetjp_2030_;
}
else
{
lean_inc(v_a_2029_);
lean_dec(v___x_2028_);
v___x_2031_ = lean_box(0);
v_isShared_2032_ = v_isSharedCheck_2268_;
goto v_resetjp_2030_;
}
v_resetjp_2030_:
{
lean_object* v_fieldInst_x3f_2033_; 
v_fieldInst_x3f_2033_ = lean_ctor_get(v_a_2029_, 6);
lean_inc(v_fieldInst_x3f_2033_);
if (lean_obj_tag(v_fieldInst_x3f_2033_) == 1)
{
lean_object* v_toRing_2034_; lean_object* v_val_2035_; lean_object* v___y_2037_; lean_object* v___y_2038_; lean_object* v___y_2039_; lean_object* v___y_2040_; lean_object* v___y_2041_; lean_object* v___y_2042_; lean_object* v___y_2043_; lean_object* v___y_2044_; lean_object* v___y_2045_; lean_object* v___y_2046_; lean_object* v___x_2056_; 
lean_del_object(v___x_2031_);
v_toRing_2034_ = lean_ctor_get(v_a_2029_, 0);
lean_inc_ref(v_toRing_2034_);
lean_dec(v_a_2029_);
v_val_2035_ = lean_ctor_get(v_fieldInst_x3f_2033_, 0);
lean_inc(v_val_2035_);
lean_dec_ref_known(v_fieldInst_x3f_2033_, 1);
v___x_2056_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v_a_2002_, v_a_2003_, v_a_2004_, v_a_2005_, v_a_2006_, v_a_2007_, v_a_2008_, v_a_2009_, v_a_2010_, v_a_2011_, v_a_2012_);
if (lean_obj_tag(v___x_2056_) == 0)
{
lean_object* v_a_2057_; lean_object* v___x_2059_; uint8_t v_isShared_2060_; uint8_t v_isSharedCheck_2255_; 
v_a_2057_ = lean_ctor_get(v___x_2056_, 0);
v_isSharedCheck_2255_ = !lean_is_exclusive(v___x_2056_);
if (v_isSharedCheck_2255_ == 0)
{
v___x_2059_ = v___x_2056_;
v_isShared_2060_ = v_isSharedCheck_2255_;
goto v_resetjp_2058_;
}
else
{
lean_inc(v_a_2057_);
lean_dec(v___x_2056_);
v___x_2059_ = lean_box(0);
v_isShared_2060_ = v_isSharedCheck_2255_;
goto v_resetjp_2058_;
}
v_resetjp_2058_:
{
lean_object* v_invSet_2061_; uint8_t v___x_2062_; 
v_invSet_2061_ = lean_ctor_get(v_a_2057_, 14);
lean_inc_ref(v_invSet_2061_);
lean_dec(v_a_2057_);
v___x_2062_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1___redArg(v_invSet_2061_, v_a_2001_);
lean_dec_ref(v_invSet_2061_);
if (v___x_2062_ == 0)
{
lean_object* v___x_2063_; 
lean_del_object(v___x_2059_);
v___x_2063_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(v___f_2017_, v_a_2002_, v_a_2003_);
if (lean_obj_tag(v___x_2063_) == 0)
{
lean_object* v___x_2064_; 
lean_dec_ref_known(v___x_2063_, 1);
lean_inc_ref(v_a_2001_);
v___x_2064_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f(v_a_2001_, v_a_2002_, v_a_2003_, v_a_2004_, v_a_2005_, v_a_2006_, v_a_2007_, v_a_2008_, v_a_2009_, v_a_2010_, v_a_2011_, v_a_2012_);
if (lean_obj_tag(v___x_2064_) == 0)
{
lean_object* v_a_2065_; 
v_a_2065_ = lean_ctor_get(v___x_2064_, 0);
lean_inc(v_a_2065_);
lean_dec_ref_known(v___x_2064_, 1);
if (lean_obj_tag(v_a_2065_) == 1)
{
lean_object* v_val_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; uint8_t v___x_2069_; 
v_val_2066_ = lean_ctor_get(v_a_2065_, 0);
lean_inc(v_val_2066_);
lean_dec_ref_known(v_a_2065_, 1);
v___x_2067_ = lean_unsigned_to_nat(0u);
v___x_2068_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__4___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__4___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__4___closed__1);
v___x_2069_ = lean_int_dec_eq(v_val_2066_, v___x_2068_);
if (v___x_2069_ == 0)
{
lean_object* v___x_2070_; 
v___x_2070_ = l_Lean_Meta_Grind_Arith_CommRing_hasChar(v_a_2002_, v_a_2003_, v_a_2004_, v_a_2005_, v_a_2006_, v_a_2007_, v_a_2008_, v_a_2009_, v_a_2010_, v_a_2011_, v_a_2012_);
if (lean_obj_tag(v___x_2070_) == 0)
{
lean_object* v_a_2071_; uint8_t v___x_2072_; 
v_a_2071_ = lean_ctor_get(v___x_2070_, 0);
lean_inc(v_a_2071_);
lean_dec_ref_known(v___x_2070_, 1);
v___x_2072_ = lean_unbox(v_a_2071_);
lean_dec(v_a_2071_);
if (v___x_2072_ == 0)
{
lean_dec(v_val_2066_);
lean_dec_ref(v_e_1999_);
v___y_2037_ = v_a_2003_;
v___y_2038_ = v_a_2004_;
v___y_2039_ = v_a_2005_;
v___y_2040_ = v_a_2006_;
v___y_2041_ = v_a_2007_;
v___y_2042_ = v_a_2008_;
v___y_2043_ = v_a_2009_;
v___y_2044_ = v_a_2010_;
v___y_2045_ = v_a_2011_;
v___y_2046_ = v_a_2012_;
goto v___jp_2036_;
}
else
{
lean_object* v___x_2073_; 
v___x_2073_ = l_Lean_Meta_Grind_Arith_CommRing_getCharInst(v_a_2002_, v_a_2003_, v_a_2004_, v_a_2005_, v_a_2006_, v_a_2007_, v_a_2008_, v_a_2009_, v_a_2010_, v_a_2011_, v_a_2012_);
if (lean_obj_tag(v___x_2073_) == 0)
{
lean_object* v_a_2074_; lean_object* v_fst_2075_; lean_object* v_snd_2076_; lean_object* v___x_2078_; uint8_t v_isShared_2079_; uint8_t v_isSharedCheck_2209_; 
v_a_2074_ = lean_ctor_get(v___x_2073_, 0);
lean_inc(v_a_2074_);
lean_dec_ref_known(v___x_2073_, 1);
v_fst_2075_ = lean_ctor_get(v_a_2074_, 0);
v_snd_2076_ = lean_ctor_get(v_a_2074_, 1);
v_isSharedCheck_2209_ = !lean_is_exclusive(v_a_2074_);
if (v_isSharedCheck_2209_ == 0)
{
v___x_2078_ = v_a_2074_;
v_isShared_2079_ = v_isSharedCheck_2209_;
goto v_resetjp_2077_;
}
else
{
lean_inc(v_snd_2076_);
lean_inc(v_fst_2075_);
lean_dec(v_a_2074_);
v___x_2078_ = lean_box(0);
v_isShared_2079_ = v_isSharedCheck_2209_;
goto v_resetjp_2077_;
}
v_resetjp_2077_:
{
uint8_t v___x_2080_; 
v___x_2080_ = lean_nat_dec_eq(v_snd_2076_, v___x_2067_);
if (v___x_2080_ == 0)
{
lean_object* v___x_2081_; lean_object* v___x_2082_; uint8_t v___x_2083_; 
lean_inc(v_snd_2076_);
v___x_2081_ = lean_nat_to_int(v_snd_2076_);
v___x_2082_ = lean_int_emod(v_val_2066_, v___x_2081_);
lean_dec(v___x_2081_);
v___x_2083_ = lean_int_dec_eq(v___x_2082_, v___x_2068_);
lean_dec(v___x_2082_);
if (v___x_2083_ == 0)
{
lean_object* v___x_2084_; 
v___x_2084_ = l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__3(v_a_2002_, v_a_2003_, v_a_2004_, v_a_2005_, v_a_2006_, v_a_2007_, v_a_2008_, v_a_2009_, v_a_2010_, v_a_2011_, v_a_2012_);
if (lean_obj_tag(v___x_2084_) == 0)
{
lean_object* v_a_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; 
v_a_2085_ = lean_ctor_get(v___x_2084_, 0);
lean_inc(v_a_2085_);
lean_dec_ref_known(v___x_2084_, 1);
v___x_2086_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__3, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__3);
v___x_2087_ = l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__4(v___x_2086_, v_a_2002_, v_a_2003_, v_a_2004_, v_a_2005_, v_a_2006_, v_a_2007_, v_a_2008_, v_a_2009_, v_a_2010_, v_a_2011_, v_a_2012_);
if (lean_obj_tag(v___x_2087_) == 0)
{
lean_object* v_a_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; 
v_a_2088_ = lean_ctor_get(v___x_2087_, 0);
lean_inc(v_a_2088_);
lean_dec_ref_known(v___x_2087_, 1);
v___x_2089_ = l_Lean_mkAppB(v_a_2085_, v_a_2001_, v_e_1999_);
v___x_2090_ = l_Lean_Meta_mkEq(v___x_2089_, v_a_2088_, v_a_2009_, v_a_2010_, v_a_2011_, v_a_2012_);
if (lean_obj_tag(v___x_2090_) == 0)
{
lean_object* v_a_2091_; lean_object* v_type_2092_; lean_object* v_u_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2097_; 
v_a_2091_ = lean_ctor_get(v___x_2090_, 0);
lean_inc(v_a_2091_);
lean_dec_ref_known(v___x_2090_, 1);
v_type_2092_ = lean_ctor_get(v_toRing_2034_, 1);
lean_inc_ref(v_type_2092_);
v_u_2093_ = lean_ctor_get(v_toRing_2034_, 2);
lean_inc(v_u_2093_);
lean_dec_ref(v_toRing_2034_);
v___x_2094_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__5));
v___x_2095_ = lean_box(0);
if (v_isShared_2079_ == 0)
{
lean_ctor_set_tag(v___x_2078_, 1);
lean_ctor_set(v___x_2078_, 1, v___x_2095_);
lean_ctor_set(v___x_2078_, 0, v_u_2093_);
v___x_2097_ = v___x_2078_;
goto v_reusejp_2096_;
}
else
{
lean_object* v_reuseFailAlloc_2105_; 
v_reuseFailAlloc_2105_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2105_, 0, v_u_2093_);
lean_ctor_set(v_reuseFailAlloc_2105_, 1, v___x_2095_);
v___x_2097_ = v_reuseFailAlloc_2105_;
goto v_reusejp_2096_;
}
v_reusejp_2096_:
{
lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; 
v___x_2098_ = l_Lean_mkConst(v___x_2094_, v___x_2097_);
v___x_2099_ = l_Lean_mkNatLit(v_snd_2076_);
v___x_2100_ = l_Lean_mkIntLit(v_val_2066_);
lean_dec(v_val_2066_);
v___x_2101_ = l_Lean_eagerReflBoolTrue;
v___x_2102_ = l_Lean_mkApp6(v___x_2098_, v_type_2092_, v___x_2099_, v_val_2035_, v_fst_2075_, v___x_2100_, v___x_2101_);
v___x_2103_ = l_Lean_Meta_mkExpectedPropHint(v___x_2102_, v_a_2091_);
v___x_2104_ = l_Lean_Meta_Grind_pushNewFact(v___x_2103_, v___x_2067_, v_a_2003_, v_a_2004_, v_a_2005_, v_a_2006_, v_a_2007_, v_a_2008_, v_a_2009_, v_a_2010_, v_a_2011_, v_a_2012_);
if (lean_obj_tag(v___x_2104_) == 0)
{
lean_dec_ref_known(v___x_2104_, 1);
goto v___jp_2014_;
}
else
{
return v___x_2104_;
}
}
}
else
{
lean_object* v_a_2106_; lean_object* v___x_2108_; uint8_t v_isShared_2109_; uint8_t v_isSharedCheck_2113_; 
lean_del_object(v___x_2078_);
lean_dec(v_snd_2076_);
lean_dec(v_fst_2075_);
lean_dec(v_val_2066_);
lean_dec(v_val_2035_);
lean_dec_ref(v_toRing_2034_);
v_a_2106_ = lean_ctor_get(v___x_2090_, 0);
v_isSharedCheck_2113_ = !lean_is_exclusive(v___x_2090_);
if (v_isSharedCheck_2113_ == 0)
{
v___x_2108_ = v___x_2090_;
v_isShared_2109_ = v_isSharedCheck_2113_;
goto v_resetjp_2107_;
}
else
{
lean_inc(v_a_2106_);
lean_dec(v___x_2090_);
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
lean_dec(v_a_2085_);
lean_del_object(v___x_2078_);
lean_dec(v_snd_2076_);
lean_dec(v_fst_2075_);
lean_dec(v_val_2066_);
lean_dec(v_val_2035_);
lean_dec_ref(v_toRing_2034_);
lean_dec_ref(v_a_2001_);
lean_dec_ref(v_e_1999_);
v_a_2114_ = lean_ctor_get(v___x_2087_, 0);
v_isSharedCheck_2121_ = !lean_is_exclusive(v___x_2087_);
if (v_isSharedCheck_2121_ == 0)
{
v___x_2116_ = v___x_2087_;
v_isShared_2117_ = v_isSharedCheck_2121_;
goto v_resetjp_2115_;
}
else
{
lean_inc(v_a_2114_);
lean_dec(v___x_2087_);
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
lean_object* v_a_2122_; lean_object* v___x_2124_; uint8_t v_isShared_2125_; uint8_t v_isSharedCheck_2129_; 
lean_del_object(v___x_2078_);
lean_dec(v_snd_2076_);
lean_dec(v_fst_2075_);
lean_dec(v_val_2066_);
lean_dec(v_val_2035_);
lean_dec_ref(v_toRing_2034_);
lean_dec_ref(v_a_2001_);
lean_dec_ref(v_e_1999_);
v_a_2122_ = lean_ctor_get(v___x_2084_, 0);
v_isSharedCheck_2129_ = !lean_is_exclusive(v___x_2084_);
if (v_isSharedCheck_2129_ == 0)
{
v___x_2124_ = v___x_2084_;
v_isShared_2125_ = v_isSharedCheck_2129_;
goto v_resetjp_2123_;
}
else
{
lean_inc(v_a_2122_);
lean_dec(v___x_2084_);
v___x_2124_ = lean_box(0);
v_isShared_2125_ = v_isSharedCheck_2129_;
goto v_resetjp_2123_;
}
v_resetjp_2123_:
{
lean_object* v___x_2127_; 
if (v_isShared_2125_ == 0)
{
v___x_2127_ = v___x_2124_;
goto v_reusejp_2126_;
}
else
{
lean_object* v_reuseFailAlloc_2128_; 
v_reuseFailAlloc_2128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2128_, 0, v_a_2122_);
v___x_2127_ = v_reuseFailAlloc_2128_;
goto v_reusejp_2126_;
}
v_reusejp_2126_:
{
return v___x_2127_;
}
}
}
}
else
{
lean_object* v___x_2130_; 
lean_dec_ref(v_a_2001_);
v___x_2130_ = l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__4(v___x_2068_, v_a_2002_, v_a_2003_, v_a_2004_, v_a_2005_, v_a_2006_, v_a_2007_, v_a_2008_, v_a_2009_, v_a_2010_, v_a_2011_, v_a_2012_);
if (lean_obj_tag(v___x_2130_) == 0)
{
lean_object* v_a_2131_; lean_object* v___x_2132_; 
v_a_2131_ = lean_ctor_get(v___x_2130_, 0);
lean_inc(v_a_2131_);
lean_dec_ref_known(v___x_2130_, 1);
v___x_2132_ = l_Lean_Meta_mkEq(v_e_1999_, v_a_2131_, v_a_2009_, v_a_2010_, v_a_2011_, v_a_2012_);
if (lean_obj_tag(v___x_2132_) == 0)
{
lean_object* v_a_2133_; lean_object* v_type_2134_; lean_object* v_u_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2139_; 
v_a_2133_ = lean_ctor_get(v___x_2132_, 0);
lean_inc(v_a_2133_);
lean_dec_ref_known(v___x_2132_, 1);
v_type_2134_ = lean_ctor_get(v_toRing_2034_, 1);
lean_inc_ref(v_type_2134_);
v_u_2135_ = lean_ctor_get(v_toRing_2034_, 2);
lean_inc(v_u_2135_);
lean_dec_ref(v_toRing_2034_);
v___x_2136_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__7));
v___x_2137_ = lean_box(0);
if (v_isShared_2079_ == 0)
{
lean_ctor_set_tag(v___x_2078_, 1);
lean_ctor_set(v___x_2078_, 1, v___x_2137_);
lean_ctor_set(v___x_2078_, 0, v_u_2135_);
v___x_2139_ = v___x_2078_;
goto v_reusejp_2138_;
}
else
{
lean_object* v_reuseFailAlloc_2147_; 
v_reuseFailAlloc_2147_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2147_, 0, v_u_2135_);
lean_ctor_set(v_reuseFailAlloc_2147_, 1, v___x_2137_);
v___x_2139_ = v_reuseFailAlloc_2147_;
goto v_reusejp_2138_;
}
v_reusejp_2138_:
{
lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; 
v___x_2140_ = l_Lean_mkConst(v___x_2136_, v___x_2139_);
v___x_2141_ = l_Lean_mkNatLit(v_snd_2076_);
v___x_2142_ = l_Lean_mkIntLit(v_val_2066_);
lean_dec(v_val_2066_);
v___x_2143_ = l_Lean_eagerReflBoolTrue;
v___x_2144_ = l_Lean_mkApp6(v___x_2140_, v_type_2134_, v___x_2141_, v_val_2035_, v_fst_2075_, v___x_2142_, v___x_2143_);
v___x_2145_ = l_Lean_Meta_mkExpectedPropHint(v___x_2144_, v_a_2133_);
v___x_2146_ = l_Lean_Meta_Grind_pushNewFact(v___x_2145_, v___x_2067_, v_a_2003_, v_a_2004_, v_a_2005_, v_a_2006_, v_a_2007_, v_a_2008_, v_a_2009_, v_a_2010_, v_a_2011_, v_a_2012_);
if (lean_obj_tag(v___x_2146_) == 0)
{
lean_dec_ref_known(v___x_2146_, 1);
goto v___jp_2014_;
}
else
{
return v___x_2146_;
}
}
}
else
{
lean_object* v_a_2148_; lean_object* v___x_2150_; uint8_t v_isShared_2151_; uint8_t v_isSharedCheck_2155_; 
lean_del_object(v___x_2078_);
lean_dec(v_snd_2076_);
lean_dec(v_fst_2075_);
lean_dec(v_val_2066_);
lean_dec(v_val_2035_);
lean_dec_ref(v_toRing_2034_);
v_a_2148_ = lean_ctor_get(v___x_2132_, 0);
v_isSharedCheck_2155_ = !lean_is_exclusive(v___x_2132_);
if (v_isSharedCheck_2155_ == 0)
{
v___x_2150_ = v___x_2132_;
v_isShared_2151_ = v_isSharedCheck_2155_;
goto v_resetjp_2149_;
}
else
{
lean_inc(v_a_2148_);
lean_dec(v___x_2132_);
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
else
{
lean_object* v_a_2156_; lean_object* v___x_2158_; uint8_t v_isShared_2159_; uint8_t v_isSharedCheck_2163_; 
lean_del_object(v___x_2078_);
lean_dec(v_snd_2076_);
lean_dec(v_fst_2075_);
lean_dec(v_val_2066_);
lean_dec(v_val_2035_);
lean_dec_ref(v_toRing_2034_);
lean_dec_ref(v_e_1999_);
v_a_2156_ = lean_ctor_get(v___x_2130_, 0);
v_isSharedCheck_2163_ = !lean_is_exclusive(v___x_2130_);
if (v_isSharedCheck_2163_ == 0)
{
v___x_2158_ = v___x_2130_;
v_isShared_2159_ = v_isSharedCheck_2163_;
goto v_resetjp_2157_;
}
else
{
lean_inc(v_a_2156_);
lean_dec(v___x_2130_);
v___x_2158_ = lean_box(0);
v_isShared_2159_ = v_isSharedCheck_2163_;
goto v_resetjp_2157_;
}
v_resetjp_2157_:
{
lean_object* v___x_2161_; 
if (v_isShared_2159_ == 0)
{
v___x_2161_ = v___x_2158_;
goto v_reusejp_2160_;
}
else
{
lean_object* v_reuseFailAlloc_2162_; 
v_reuseFailAlloc_2162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2162_, 0, v_a_2156_);
v___x_2161_ = v_reuseFailAlloc_2162_;
goto v_reusejp_2160_;
}
v_reusejp_2160_:
{
return v___x_2161_;
}
}
}
}
}
else
{
lean_object* v___x_2164_; 
lean_dec(v_snd_2076_);
v___x_2164_ = l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__3(v_a_2002_, v_a_2003_, v_a_2004_, v_a_2005_, v_a_2006_, v_a_2007_, v_a_2008_, v_a_2009_, v_a_2010_, v_a_2011_, v_a_2012_);
if (lean_obj_tag(v___x_2164_) == 0)
{
lean_object* v_a_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; 
v_a_2165_ = lean_ctor_get(v___x_2164_, 0);
lean_inc(v_a_2165_);
lean_dec_ref_known(v___x_2164_, 1);
v___x_2166_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__3, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__3);
v___x_2167_ = l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__4(v___x_2166_, v_a_2002_, v_a_2003_, v_a_2004_, v_a_2005_, v_a_2006_, v_a_2007_, v_a_2008_, v_a_2009_, v_a_2010_, v_a_2011_, v_a_2012_);
if (lean_obj_tag(v___x_2167_) == 0)
{
lean_object* v_a_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; 
v_a_2168_ = lean_ctor_get(v___x_2167_, 0);
lean_inc(v_a_2168_);
lean_dec_ref_known(v___x_2167_, 1);
v___x_2169_ = l_Lean_mkAppB(v_a_2165_, v_a_2001_, v_e_1999_);
v___x_2170_ = l_Lean_Meta_mkEq(v___x_2169_, v_a_2168_, v_a_2009_, v_a_2010_, v_a_2011_, v_a_2012_);
if (lean_obj_tag(v___x_2170_) == 0)
{
lean_object* v_a_2171_; lean_object* v_type_2172_; lean_object* v_u_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; lean_object* v___x_2177_; 
v_a_2171_ = lean_ctor_get(v___x_2170_, 0);
lean_inc(v_a_2171_);
lean_dec_ref_known(v___x_2170_, 1);
v_type_2172_ = lean_ctor_get(v_toRing_2034_, 1);
lean_inc_ref(v_type_2172_);
v_u_2173_ = lean_ctor_get(v_toRing_2034_, 2);
lean_inc(v_u_2173_);
lean_dec_ref(v_toRing_2034_);
v___x_2174_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__9));
v___x_2175_ = lean_box(0);
if (v_isShared_2079_ == 0)
{
lean_ctor_set_tag(v___x_2078_, 1);
lean_ctor_set(v___x_2078_, 1, v___x_2175_);
lean_ctor_set(v___x_2078_, 0, v_u_2173_);
v___x_2177_ = v___x_2078_;
goto v_reusejp_2176_;
}
else
{
lean_object* v_reuseFailAlloc_2184_; 
v_reuseFailAlloc_2184_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2184_, 0, v_u_2173_);
lean_ctor_set(v_reuseFailAlloc_2184_, 1, v___x_2175_);
v___x_2177_ = v_reuseFailAlloc_2184_;
goto v_reusejp_2176_;
}
v_reusejp_2176_:
{
lean_object* v___x_2178_; lean_object* v___x_2179_; lean_object* v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; 
v___x_2178_ = l_Lean_mkConst(v___x_2174_, v___x_2177_);
v___x_2179_ = l_Lean_mkIntLit(v_val_2066_);
lean_dec(v_val_2066_);
v___x_2180_ = l_Lean_eagerReflBoolTrue;
v___x_2181_ = l_Lean_mkApp5(v___x_2178_, v_type_2172_, v_val_2035_, v_fst_2075_, v___x_2179_, v___x_2180_);
v___x_2182_ = l_Lean_Meta_mkExpectedPropHint(v___x_2181_, v_a_2171_);
v___x_2183_ = l_Lean_Meta_Grind_pushNewFact(v___x_2182_, v___x_2067_, v_a_2003_, v_a_2004_, v_a_2005_, v_a_2006_, v_a_2007_, v_a_2008_, v_a_2009_, v_a_2010_, v_a_2011_, v_a_2012_);
if (lean_obj_tag(v___x_2183_) == 0)
{
lean_dec_ref_known(v___x_2183_, 1);
goto v___jp_2014_;
}
else
{
return v___x_2183_;
}
}
}
else
{
lean_object* v_a_2185_; lean_object* v___x_2187_; uint8_t v_isShared_2188_; uint8_t v_isSharedCheck_2192_; 
lean_del_object(v___x_2078_);
lean_dec(v_fst_2075_);
lean_dec(v_val_2066_);
lean_dec(v_val_2035_);
lean_dec_ref(v_toRing_2034_);
v_a_2185_ = lean_ctor_get(v___x_2170_, 0);
v_isSharedCheck_2192_ = !lean_is_exclusive(v___x_2170_);
if (v_isSharedCheck_2192_ == 0)
{
v___x_2187_ = v___x_2170_;
v_isShared_2188_ = v_isSharedCheck_2192_;
goto v_resetjp_2186_;
}
else
{
lean_inc(v_a_2185_);
lean_dec(v___x_2170_);
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
lean_dec(v_a_2165_);
lean_del_object(v___x_2078_);
lean_dec(v_fst_2075_);
lean_dec(v_val_2066_);
lean_dec(v_val_2035_);
lean_dec_ref(v_toRing_2034_);
lean_dec_ref(v_a_2001_);
lean_dec_ref(v_e_1999_);
v_a_2193_ = lean_ctor_get(v___x_2167_, 0);
v_isSharedCheck_2200_ = !lean_is_exclusive(v___x_2167_);
if (v_isSharedCheck_2200_ == 0)
{
v___x_2195_ = v___x_2167_;
v_isShared_2196_ = v_isSharedCheck_2200_;
goto v_resetjp_2194_;
}
else
{
lean_inc(v_a_2193_);
lean_dec(v___x_2167_);
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
else
{
lean_object* v_a_2201_; lean_object* v___x_2203_; uint8_t v_isShared_2204_; uint8_t v_isSharedCheck_2208_; 
lean_del_object(v___x_2078_);
lean_dec(v_fst_2075_);
lean_dec(v_val_2066_);
lean_dec(v_val_2035_);
lean_dec_ref(v_toRing_2034_);
lean_dec_ref(v_a_2001_);
lean_dec_ref(v_e_1999_);
v_a_2201_ = lean_ctor_get(v___x_2164_, 0);
v_isSharedCheck_2208_ = !lean_is_exclusive(v___x_2164_);
if (v_isSharedCheck_2208_ == 0)
{
v___x_2203_ = v___x_2164_;
v_isShared_2204_ = v_isSharedCheck_2208_;
goto v_resetjp_2202_;
}
else
{
lean_inc(v_a_2201_);
lean_dec(v___x_2164_);
v___x_2203_ = lean_box(0);
v_isShared_2204_ = v_isSharedCheck_2208_;
goto v_resetjp_2202_;
}
v_resetjp_2202_:
{
lean_object* v___x_2206_; 
if (v_isShared_2204_ == 0)
{
v___x_2206_ = v___x_2203_;
goto v_reusejp_2205_;
}
else
{
lean_object* v_reuseFailAlloc_2207_; 
v_reuseFailAlloc_2207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2207_, 0, v_a_2201_);
v___x_2206_ = v_reuseFailAlloc_2207_;
goto v_reusejp_2205_;
}
v_reusejp_2205_:
{
return v___x_2206_;
}
}
}
}
}
}
else
{
lean_object* v_a_2210_; lean_object* v___x_2212_; uint8_t v_isShared_2213_; uint8_t v_isSharedCheck_2217_; 
lean_dec(v_val_2066_);
lean_dec(v_val_2035_);
lean_dec_ref(v_toRing_2034_);
lean_dec_ref(v_a_2001_);
lean_dec_ref(v_e_1999_);
v_a_2210_ = lean_ctor_get(v___x_2073_, 0);
v_isSharedCheck_2217_ = !lean_is_exclusive(v___x_2073_);
if (v_isSharedCheck_2217_ == 0)
{
v___x_2212_ = v___x_2073_;
v_isShared_2213_ = v_isSharedCheck_2217_;
goto v_resetjp_2211_;
}
else
{
lean_inc(v_a_2210_);
lean_dec(v___x_2073_);
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
}
else
{
lean_object* v_a_2218_; lean_object* v___x_2220_; uint8_t v_isShared_2221_; uint8_t v_isSharedCheck_2225_; 
lean_dec(v_val_2066_);
lean_dec(v_val_2035_);
lean_dec_ref(v_toRing_2034_);
lean_dec_ref(v_a_2001_);
lean_dec_ref(v_e_1999_);
v_a_2218_ = lean_ctor_get(v___x_2070_, 0);
v_isSharedCheck_2225_ = !lean_is_exclusive(v___x_2070_);
if (v_isSharedCheck_2225_ == 0)
{
v___x_2220_ = v___x_2070_;
v_isShared_2221_ = v_isSharedCheck_2225_;
goto v_resetjp_2219_;
}
else
{
lean_inc(v_a_2218_);
lean_dec(v___x_2070_);
v___x_2220_ = lean_box(0);
v_isShared_2221_ = v_isSharedCheck_2225_;
goto v_resetjp_2219_;
}
v_resetjp_2219_:
{
lean_object* v___x_2223_; 
if (v_isShared_2221_ == 0)
{
v___x_2223_ = v___x_2220_;
goto v_reusejp_2222_;
}
else
{
lean_object* v_reuseFailAlloc_2224_; 
v_reuseFailAlloc_2224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2224_, 0, v_a_2218_);
v___x_2223_ = v_reuseFailAlloc_2224_;
goto v_reusejp_2222_;
}
v_reusejp_2222_:
{
return v___x_2223_;
}
}
}
}
else
{
lean_object* v_type_2226_; lean_object* v_u_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; 
lean_dec(v_val_2066_);
v_type_2226_ = lean_ctor_get(v_toRing_2034_, 1);
lean_inc_ref(v_type_2226_);
v_u_2227_ = lean_ctor_get(v_toRing_2034_, 2);
lean_inc(v_u_2227_);
lean_dec_ref(v_toRing_2034_);
v___x_2228_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__11));
v___x_2229_ = lean_box(0);
v___x_2230_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2230_, 0, v_u_2227_);
lean_ctor_set(v___x_2230_, 1, v___x_2229_);
v___x_2231_ = l_Lean_mkConst(v___x_2228_, v___x_2230_);
v___x_2232_ = l_Lean_mkAppB(v___x_2231_, v_type_2226_, v_val_2035_);
v___x_2233_ = l_Lean_Meta_Grind_pushEqCore___redArg(v_e_1999_, v_a_2001_, v___x_2232_, v___x_2062_, v_a_2003_, v_a_2005_, v_a_2009_, v_a_2010_, v_a_2011_, v_a_2012_);
if (lean_obj_tag(v___x_2233_) == 0)
{
lean_object* v___x_2235_; uint8_t v_isShared_2236_; uint8_t v_isSharedCheck_2241_; 
v_isSharedCheck_2241_ = !lean_is_exclusive(v___x_2233_);
if (v_isSharedCheck_2241_ == 0)
{
lean_object* v_unused_2242_; 
v_unused_2242_ = lean_ctor_get(v___x_2233_, 0);
lean_dec(v_unused_2242_);
v___x_2235_ = v___x_2233_;
v_isShared_2236_ = v_isSharedCheck_2241_;
goto v_resetjp_2234_;
}
else
{
lean_dec(v___x_2233_);
v___x_2235_ = lean_box(0);
v_isShared_2236_ = v_isSharedCheck_2241_;
goto v_resetjp_2234_;
}
v_resetjp_2234_:
{
lean_object* v___x_2237_; lean_object* v___x_2239_; 
v___x_2237_ = lean_box(0);
if (v_isShared_2236_ == 0)
{
lean_ctor_set(v___x_2235_, 0, v___x_2237_);
v___x_2239_ = v___x_2235_;
goto v_reusejp_2238_;
}
else
{
lean_object* v_reuseFailAlloc_2240_; 
v_reuseFailAlloc_2240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2240_, 0, v___x_2237_);
v___x_2239_ = v_reuseFailAlloc_2240_;
goto v_reusejp_2238_;
}
v_reusejp_2238_:
{
return v___x_2239_;
}
}
}
else
{
return v___x_2233_;
}
}
}
else
{
lean_dec(v_a_2065_);
lean_dec_ref(v_e_1999_);
v___y_2037_ = v_a_2003_;
v___y_2038_ = v_a_2004_;
v___y_2039_ = v_a_2005_;
v___y_2040_ = v_a_2006_;
v___y_2041_ = v_a_2007_;
v___y_2042_ = v_a_2008_;
v___y_2043_ = v_a_2009_;
v___y_2044_ = v_a_2010_;
v___y_2045_ = v_a_2011_;
v___y_2046_ = v_a_2012_;
goto v___jp_2036_;
}
}
else
{
lean_object* v_a_2243_; lean_object* v___x_2245_; uint8_t v_isShared_2246_; uint8_t v_isSharedCheck_2250_; 
lean_dec(v_val_2035_);
lean_dec_ref(v_toRing_2034_);
lean_dec_ref(v_a_2001_);
lean_dec_ref(v_e_1999_);
v_a_2243_ = lean_ctor_get(v___x_2064_, 0);
v_isSharedCheck_2250_ = !lean_is_exclusive(v___x_2064_);
if (v_isSharedCheck_2250_ == 0)
{
v___x_2245_ = v___x_2064_;
v_isShared_2246_ = v_isSharedCheck_2250_;
goto v_resetjp_2244_;
}
else
{
lean_inc(v_a_2243_);
lean_dec(v___x_2064_);
v___x_2245_ = lean_box(0);
v_isShared_2246_ = v_isSharedCheck_2250_;
goto v_resetjp_2244_;
}
v_resetjp_2244_:
{
lean_object* v___x_2248_; 
if (v_isShared_2246_ == 0)
{
v___x_2248_ = v___x_2245_;
goto v_reusejp_2247_;
}
else
{
lean_object* v_reuseFailAlloc_2249_; 
v_reuseFailAlloc_2249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2249_, 0, v_a_2243_);
v___x_2248_ = v_reuseFailAlloc_2249_;
goto v_reusejp_2247_;
}
v_reusejp_2247_:
{
return v___x_2248_;
}
}
}
}
else
{
lean_dec(v_val_2035_);
lean_dec_ref(v_toRing_2034_);
lean_dec_ref(v_a_2001_);
lean_dec_ref(v_e_1999_);
return v___x_2063_;
}
}
else
{
lean_object* v___x_2251_; lean_object* v___x_2253_; 
lean_dec(v_val_2035_);
lean_dec_ref(v_toRing_2034_);
lean_dec_ref(v___f_2017_);
lean_dec_ref(v_a_2001_);
lean_dec_ref(v_e_1999_);
v___x_2251_ = lean_box(0);
if (v_isShared_2060_ == 0)
{
lean_ctor_set(v___x_2059_, 0, v___x_2251_);
v___x_2253_ = v___x_2059_;
goto v_reusejp_2252_;
}
else
{
lean_object* v_reuseFailAlloc_2254_; 
v_reuseFailAlloc_2254_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2254_, 0, v___x_2251_);
v___x_2253_ = v_reuseFailAlloc_2254_;
goto v_reusejp_2252_;
}
v_reusejp_2252_:
{
return v___x_2253_;
}
}
}
}
else
{
lean_object* v_a_2256_; lean_object* v___x_2258_; uint8_t v_isShared_2259_; uint8_t v_isSharedCheck_2263_; 
lean_dec(v_val_2035_);
lean_dec_ref(v_toRing_2034_);
lean_dec_ref(v___f_2017_);
lean_dec_ref(v_a_2001_);
lean_dec_ref(v_e_1999_);
v_a_2256_ = lean_ctor_get(v___x_2056_, 0);
v_isSharedCheck_2263_ = !lean_is_exclusive(v___x_2056_);
if (v_isSharedCheck_2263_ == 0)
{
v___x_2258_ = v___x_2056_;
v_isShared_2259_ = v_isSharedCheck_2263_;
goto v_resetjp_2257_;
}
else
{
lean_inc(v_a_2256_);
lean_dec(v___x_2056_);
v___x_2258_ = lean_box(0);
v_isShared_2259_ = v_isSharedCheck_2263_;
goto v_resetjp_2257_;
}
v_resetjp_2257_:
{
lean_object* v___x_2261_; 
if (v_isShared_2259_ == 0)
{
v___x_2261_ = v___x_2258_;
goto v_reusejp_2260_;
}
else
{
lean_object* v_reuseFailAlloc_2262_; 
v_reuseFailAlloc_2262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2262_, 0, v_a_2256_);
v___x_2261_ = v_reuseFailAlloc_2262_;
goto v_reusejp_2260_;
}
v_reusejp_2260_:
{
return v___x_2261_;
}
}
}
v___jp_2036_:
{
lean_object* v_type_2047_; lean_object* v_u_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; 
v_type_2047_ = lean_ctor_get(v_toRing_2034_, 1);
lean_inc_ref(v_type_2047_);
v_u_2048_ = lean_ctor_get(v_toRing_2034_, 2);
lean_inc(v_u_2048_);
lean_dec_ref(v_toRing_2034_);
v___x_2049_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__2));
v___x_2050_ = lean_box(0);
v___x_2051_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2051_, 0, v_u_2048_);
lean_ctor_set(v___x_2051_, 1, v___x_2050_);
v___x_2052_ = l_Lean_mkConst(v___x_2049_, v___x_2051_);
v___x_2053_ = l_Lean_mkApp3(v___x_2052_, v_type_2047_, v_val_2035_, v_a_2001_);
v___x_2054_ = lean_unsigned_to_nat(0u);
v___x_2055_ = l_Lean_Meta_Grind_pushNewFact(v___x_2053_, v___x_2054_, v___y_2037_, v___y_2038_, v___y_2039_, v___y_2040_, v___y_2041_, v___y_2042_, v___y_2043_, v___y_2044_, v___y_2045_, v___y_2046_);
return v___x_2055_;
}
}
else
{
lean_object* v___x_2264_; lean_object* v___x_2266_; 
lean_dec(v_fieldInst_x3f_2033_);
lean_dec(v_a_2029_);
lean_dec_ref(v___f_2017_);
lean_dec_ref(v_a_2001_);
lean_dec_ref(v_e_1999_);
v___x_2264_ = lean_box(0);
if (v_isShared_2032_ == 0)
{
lean_ctor_set(v___x_2031_, 0, v___x_2264_);
v___x_2266_ = v___x_2031_;
goto v_reusejp_2265_;
}
else
{
lean_object* v_reuseFailAlloc_2267_; 
v_reuseFailAlloc_2267_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2267_, 0, v___x_2264_);
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
else
{
lean_object* v_a_2269_; lean_object* v___x_2271_; uint8_t v_isShared_2272_; uint8_t v_isSharedCheck_2276_; 
lean_dec_ref(v___f_2017_);
lean_dec_ref(v_a_2001_);
lean_dec_ref(v_e_1999_);
v_a_2269_ = lean_ctor_get(v___x_2028_, 0);
v_isSharedCheck_2276_ = !lean_is_exclusive(v___x_2028_);
if (v_isSharedCheck_2276_ == 0)
{
v___x_2271_ = v___x_2028_;
v_isShared_2272_ = v_isSharedCheck_2276_;
goto v_resetjp_2270_;
}
else
{
lean_inc(v_a_2269_);
lean_dec(v___x_2028_);
v___x_2271_ = lean_box(0);
v_isShared_2272_ = v_isSharedCheck_2276_;
goto v_resetjp_2270_;
}
v_resetjp_2270_:
{
lean_object* v___x_2274_; 
if (v_isShared_2272_ == 0)
{
v___x_2274_ = v___x_2271_;
goto v_reusejp_2273_;
}
else
{
lean_object* v_reuseFailAlloc_2275_; 
v_reuseFailAlloc_2275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2275_, 0, v_a_2269_);
v___x_2274_ = v_reuseFailAlloc_2275_;
goto v_reusejp_2273_;
}
v_reusejp_2273_:
{
return v___x_2274_;
}
}
}
}
}
}
else
{
lean_object* v_a_2278_; lean_object* v___x_2280_; uint8_t v_isShared_2281_; uint8_t v_isSharedCheck_2285_; 
lean_dec_ref(v___f_2017_);
lean_dec_ref(v_a_2001_);
lean_dec_ref(v_e_1999_);
v_a_2278_ = lean_ctor_get(v___x_2018_, 0);
v_isSharedCheck_2285_ = !lean_is_exclusive(v___x_2018_);
if (v_isSharedCheck_2285_ == 0)
{
v___x_2280_ = v___x_2018_;
v_isShared_2281_ = v_isSharedCheck_2285_;
goto v_resetjp_2279_;
}
else
{
lean_inc(v_a_2278_);
lean_dec(v___x_2018_);
v___x_2280_ = lean_box(0);
v_isShared_2281_ = v_isSharedCheck_2285_;
goto v_resetjp_2279_;
}
v_resetjp_2279_:
{
lean_object* v___x_2283_; 
if (v_isShared_2281_ == 0)
{
v___x_2283_ = v___x_2280_;
goto v_reusejp_2282_;
}
else
{
lean_object* v_reuseFailAlloc_2284_; 
v_reuseFailAlloc_2284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2284_, 0, v_a_2278_);
v___x_2283_ = v_reuseFailAlloc_2284_;
goto v_reusejp_2282_;
}
v_reusejp_2282_:
{
return v___x_2283_;
}
}
}
v___jp_2014_:
{
lean_object* v___x_2015_; lean_object* v___x_2016_; 
v___x_2015_ = lean_box(0);
v___x_2016_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2016_, 0, v___x_2015_);
return v___x_2016_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___boxed(lean_object* v_e_2286_, lean_object* v_inst_2287_, lean_object* v_a_2288_, lean_object* v_a_2289_, lean_object* v_a_2290_, lean_object* v_a_2291_, lean_object* v_a_2292_, lean_object* v_a_2293_, lean_object* v_a_2294_, lean_object* v_a_2295_, lean_object* v_a_2296_, lean_object* v_a_2297_, lean_object* v_a_2298_, lean_object* v_a_2299_, lean_object* v_a_2300_){
_start:
{
lean_object* v_res_2301_; 
v_res_2301_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv(v_e_2286_, v_inst_2287_, v_a_2288_, v_a_2289_, v_a_2290_, v_a_2291_, v_a_2292_, v_a_2293_, v_a_2294_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_);
lean_dec(v_a_2299_);
lean_dec_ref(v_a_2298_);
lean_dec(v_a_2297_);
lean_dec_ref(v_a_2296_);
lean_dec(v_a_2295_);
lean_dec_ref(v_a_2294_);
lean_dec(v_a_2293_);
lean_dec_ref(v_a_2292_);
lean_dec(v_a_2291_);
lean_dec(v_a_2290_);
lean_dec_ref(v_a_2289_);
lean_dec_ref(v_inst_2287_);
return v_res_2301_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0(lean_object* v_00_u03b2_2302_, lean_object* v_x_2303_, lean_object* v_x_2304_, lean_object* v_x_2305_){
_start:
{
lean_object* v___x_2306_; 
v___x_2306_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0___redArg(v_x_2303_, v_x_2304_, v_x_2305_);
return v___x_2306_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1(lean_object* v_00_u03b2_2307_, lean_object* v_x_2308_, lean_object* v_x_2309_){
_start:
{
uint8_t v___x_2310_; 
v___x_2310_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1___redArg(v_x_2308_, v_x_2309_);
return v___x_2310_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1___boxed(lean_object* v_00_u03b2_2311_, lean_object* v_x_2312_, lean_object* v_x_2313_){
_start:
{
uint8_t v_res_2314_; lean_object* v_r_2315_; 
v_res_2314_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1(v_00_u03b2_2311_, v_x_2312_, v_x_2313_);
lean_dec_ref(v_x_2313_);
lean_dec_ref(v_x_2312_);
v_r_2315_ = lean_box(v_res_2314_);
return v_r_2315_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0(lean_object* v_00_u03b2_2316_, lean_object* v_x_2317_, size_t v_x_2318_, size_t v_x_2319_, lean_object* v_x_2320_, lean_object* v_x_2321_){
_start:
{
lean_object* v___x_2322_; 
v___x_2322_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg(v_x_2317_, v_x_2318_, v_x_2319_, v_x_2320_, v_x_2321_);
return v___x_2322_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2323_, lean_object* v_x_2324_, lean_object* v_x_2325_, lean_object* v_x_2326_, lean_object* v_x_2327_, lean_object* v_x_2328_){
_start:
{
size_t v_x_82466__boxed_2329_; size_t v_x_82467__boxed_2330_; lean_object* v_res_2331_; 
v_x_82466__boxed_2329_ = lean_unbox_usize(v_x_2325_);
lean_dec(v_x_2325_);
v_x_82467__boxed_2330_ = lean_unbox_usize(v_x_2326_);
lean_dec(v_x_2326_);
v_res_2331_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0(v_00_u03b2_2323_, v_x_2324_, v_x_82466__boxed_2329_, v_x_82467__boxed_2330_, v_x_2327_, v_x_2328_);
return v_res_2331_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1_spec__2(lean_object* v_00_u03b2_2332_, lean_object* v_x_2333_, size_t v_x_2334_, lean_object* v_x_2335_){
_start:
{
uint8_t v___x_2336_; 
v___x_2336_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1_spec__2___redArg(v_x_2333_, v_x_2334_, v_x_2335_);
return v___x_2336_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1_spec__2___boxed(lean_object* v_00_u03b2_2337_, lean_object* v_x_2338_, lean_object* v_x_2339_, lean_object* v_x_2340_){
_start:
{
size_t v_x_82483__boxed_2341_; uint8_t v_res_2342_; lean_object* v_r_2343_; 
v_x_82483__boxed_2341_ = lean_unbox_usize(v_x_2339_);
lean_dec(v_x_2339_);
v_res_2342_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1_spec__2(v_00_u03b2_2337_, v_x_2338_, v_x_82483__boxed_2341_, v_x_2340_);
lean_dec_ref(v_x_2340_);
lean_dec_ref(v_x_2338_);
v_r_2343_ = lean_box(v_res_2342_);
return v_r_2343_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_2344_, lean_object* v_n_2345_, lean_object* v_k_2346_, lean_object* v_v_2347_){
_start:
{
lean_object* v___x_2348_; 
v___x_2348_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0_spec__2___redArg(v_n_2345_, v_k_2346_, v_v_2347_);
return v___x_2348_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_2349_, size_t v_depth_2350_, lean_object* v_keys_2351_, lean_object* v_vals_2352_, lean_object* v_heq_2353_, lean_object* v_i_2354_, lean_object* v_entries_2355_){
_start:
{
lean_object* v___x_2356_; 
v___x_2356_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0_spec__3___redArg(v_depth_2350_, v_keys_2351_, v_vals_2352_, v_i_2354_, v_entries_2355_);
return v___x_2356_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b2_2357_, lean_object* v_depth_2358_, lean_object* v_keys_2359_, lean_object* v_vals_2360_, lean_object* v_heq_2361_, lean_object* v_i_2362_, lean_object* v_entries_2363_){
_start:
{
size_t v_depth_boxed_2364_; lean_object* v_res_2365_; 
v_depth_boxed_2364_ = lean_unbox_usize(v_depth_2358_);
lean_dec(v_depth_2358_);
v_res_2365_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0_spec__3(v_00_u03b2_2357_, v_depth_boxed_2364_, v_keys_2359_, v_vals_2360_, v_heq_2361_, v_i_2362_, v_entries_2363_);
lean_dec_ref(v_vals_2360_);
lean_dec_ref(v_keys_2359_);
return v_res_2365_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1_spec__2_spec__6(lean_object* v_00_u03b2_2366_, lean_object* v_keys_2367_, lean_object* v_vals_2368_, lean_object* v_heq_2369_, lean_object* v_i_2370_, lean_object* v_k_2371_){
_start:
{
uint8_t v___x_2372_; 
v___x_2372_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1_spec__2_spec__6___redArg(v_keys_2367_, v_i_2370_, v_k_2371_);
return v___x_2372_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1_spec__2_spec__6___boxed(lean_object* v_00_u03b2_2373_, lean_object* v_keys_2374_, lean_object* v_vals_2375_, lean_object* v_heq_2376_, lean_object* v_i_2377_, lean_object* v_k_2378_){
_start:
{
uint8_t v_res_2379_; lean_object* v_r_2380_; 
v_res_2379_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1_spec__2_spec__6(v_00_u03b2_2373_, v_keys_2374_, v_vals_2375_, v_heq_2376_, v_i_2377_, v_k_2378_);
lean_dec_ref(v_k_2378_);
lean_dec_ref(v_vals_2375_);
lean_dec_ref(v_keys_2374_);
v_r_2380_ = lean_box(v_res_2379_);
return v_r_2380_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0_spec__2_spec__6(lean_object* v_00_u03b2_2381_, lean_object* v_x_2382_, lean_object* v_x_2383_, lean_object* v_x_2384_, lean_object* v_x_2385_){
_start:
{
lean_object* v___x_2386_; 
v___x_2386_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0_spec__2_spec__6___redArg(v_x_2382_, v_x_2383_, v_x_2384_, v_x_2385_);
return v___x_2386_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars___lam__0(lean_object* v_size_2387_, lean_object* v_s_2388_){
_start:
{
lean_object* v_toRing_2389_; lean_object* v_invFn_x3f_2390_; lean_object* v_semiringId_x3f_2391_; lean_object* v_commSemiringInst_2392_; lean_object* v_commRingInst_2393_; lean_object* v_noZeroDivInst_x3f_2394_; lean_object* v_fieldInst_x3f_2395_; lean_object* v_powIdentityInst_x3f_2396_; lean_object* v_denoteEntries_2397_; lean_object* v_nextId_2398_; lean_object* v_steps_2399_; lean_object* v_queue_2400_; lean_object* v_basis_2401_; lean_object* v_diseqs_2402_; uint8_t v_recheck_2403_; lean_object* v_invSet_2404_; lean_object* v_numEq0_x3f_2405_; uint8_t v_numEq0Updated_2406_; lean_object* v___x_2408_; uint8_t v_isShared_2409_; uint8_t v_isSharedCheck_2413_; 
v_toRing_2389_ = lean_ctor_get(v_s_2388_, 0);
v_invFn_x3f_2390_ = lean_ctor_get(v_s_2388_, 1);
v_semiringId_x3f_2391_ = lean_ctor_get(v_s_2388_, 2);
v_commSemiringInst_2392_ = lean_ctor_get(v_s_2388_, 3);
v_commRingInst_2393_ = lean_ctor_get(v_s_2388_, 4);
v_noZeroDivInst_x3f_2394_ = lean_ctor_get(v_s_2388_, 5);
v_fieldInst_x3f_2395_ = lean_ctor_get(v_s_2388_, 6);
v_powIdentityInst_x3f_2396_ = lean_ctor_get(v_s_2388_, 7);
v_denoteEntries_2397_ = lean_ctor_get(v_s_2388_, 8);
v_nextId_2398_ = lean_ctor_get(v_s_2388_, 9);
v_steps_2399_ = lean_ctor_get(v_s_2388_, 10);
v_queue_2400_ = lean_ctor_get(v_s_2388_, 11);
v_basis_2401_ = lean_ctor_get(v_s_2388_, 12);
v_diseqs_2402_ = lean_ctor_get(v_s_2388_, 13);
v_recheck_2403_ = lean_ctor_get_uint8(v_s_2388_, sizeof(void*)*17);
v_invSet_2404_ = lean_ctor_get(v_s_2388_, 14);
v_numEq0_x3f_2405_ = lean_ctor_get(v_s_2388_, 16);
v_numEq0Updated_2406_ = lean_ctor_get_uint8(v_s_2388_, sizeof(void*)*17 + 1);
v_isSharedCheck_2413_ = !lean_is_exclusive(v_s_2388_);
if (v_isSharedCheck_2413_ == 0)
{
lean_object* v_unused_2414_; 
v_unused_2414_ = lean_ctor_get(v_s_2388_, 15);
lean_dec(v_unused_2414_);
v___x_2408_ = v_s_2388_;
v_isShared_2409_ = v_isSharedCheck_2413_;
goto v_resetjp_2407_;
}
else
{
lean_inc(v_numEq0_x3f_2405_);
lean_inc(v_invSet_2404_);
lean_inc(v_diseqs_2402_);
lean_inc(v_basis_2401_);
lean_inc(v_queue_2400_);
lean_inc(v_steps_2399_);
lean_inc(v_nextId_2398_);
lean_inc(v_denoteEntries_2397_);
lean_inc(v_powIdentityInst_x3f_2396_);
lean_inc(v_fieldInst_x3f_2395_);
lean_inc(v_noZeroDivInst_x3f_2394_);
lean_inc(v_commRingInst_2393_);
lean_inc(v_commSemiringInst_2392_);
lean_inc(v_semiringId_x3f_2391_);
lean_inc(v_invFn_x3f_2390_);
lean_inc(v_toRing_2389_);
lean_dec(v_s_2388_);
v___x_2408_ = lean_box(0);
v_isShared_2409_ = v_isSharedCheck_2413_;
goto v_resetjp_2407_;
}
v_resetjp_2407_:
{
lean_object* v___x_2411_; 
if (v_isShared_2409_ == 0)
{
lean_ctor_set(v___x_2408_, 15, v_size_2387_);
v___x_2411_ = v___x_2408_;
goto v_reusejp_2410_;
}
else
{
lean_object* v_reuseFailAlloc_2412_; 
v_reuseFailAlloc_2412_ = lean_alloc_ctor(0, 17, 2);
lean_ctor_set(v_reuseFailAlloc_2412_, 0, v_toRing_2389_);
lean_ctor_set(v_reuseFailAlloc_2412_, 1, v_invFn_x3f_2390_);
lean_ctor_set(v_reuseFailAlloc_2412_, 2, v_semiringId_x3f_2391_);
lean_ctor_set(v_reuseFailAlloc_2412_, 3, v_commSemiringInst_2392_);
lean_ctor_set(v_reuseFailAlloc_2412_, 4, v_commRingInst_2393_);
lean_ctor_set(v_reuseFailAlloc_2412_, 5, v_noZeroDivInst_x3f_2394_);
lean_ctor_set(v_reuseFailAlloc_2412_, 6, v_fieldInst_x3f_2395_);
lean_ctor_set(v_reuseFailAlloc_2412_, 7, v_powIdentityInst_x3f_2396_);
lean_ctor_set(v_reuseFailAlloc_2412_, 8, v_denoteEntries_2397_);
lean_ctor_set(v_reuseFailAlloc_2412_, 9, v_nextId_2398_);
lean_ctor_set(v_reuseFailAlloc_2412_, 10, v_steps_2399_);
lean_ctor_set(v_reuseFailAlloc_2412_, 11, v_queue_2400_);
lean_ctor_set(v_reuseFailAlloc_2412_, 12, v_basis_2401_);
lean_ctor_set(v_reuseFailAlloc_2412_, 13, v_diseqs_2402_);
lean_ctor_set(v_reuseFailAlloc_2412_, 14, v_invSet_2404_);
lean_ctor_set(v_reuseFailAlloc_2412_, 15, v_size_2387_);
lean_ctor_set(v_reuseFailAlloc_2412_, 16, v_numEq0_x3f_2405_);
lean_ctor_set_uint8(v_reuseFailAlloc_2412_, sizeof(void*)*17, v_recheck_2403_);
lean_ctor_set_uint8(v_reuseFailAlloc_2412_, sizeof(void*)*17 + 1, v_numEq0Updated_2406_);
v___x_2411_ = v_reuseFailAlloc_2412_;
goto v_reusejp_2410_;
}
v_reusejp_2410_:
{
return v___x_2411_;
}
}
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_2415_; double v___x_2416_; 
v___x_2415_ = lean_unsigned_to_nat(0u);
v___x_2416_ = lean_float_of_nat(v___x_2415_);
return v___x_2416_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg(lean_object* v_cls_2420_, lean_object* v_msg_2421_, lean_object* v___y_2422_, lean_object* v___y_2423_, lean_object* v___y_2424_, lean_object* v___y_2425_){
_start:
{
lean_object* v_ref_2427_; lean_object* v___x_2428_; lean_object* v_a_2429_; lean_object* v___x_2431_; uint8_t v_isShared_2432_; uint8_t v_isSharedCheck_2473_; 
v_ref_2427_ = lean_ctor_get(v___y_2424_, 2);
v___x_2428_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1_spec__5_spec__8_spec__9(v_msg_2421_, v___y_2422_, v___y_2423_, v___y_2424_, v___y_2425_);
v_a_2429_ = lean_ctor_get(v___x_2428_, 0);
v_isSharedCheck_2473_ = !lean_is_exclusive(v___x_2428_);
if (v_isSharedCheck_2473_ == 0)
{
v___x_2431_ = v___x_2428_;
v_isShared_2432_ = v_isSharedCheck_2473_;
goto v_resetjp_2430_;
}
else
{
lean_inc(v_a_2429_);
lean_dec(v___x_2428_);
v___x_2431_ = lean_box(0);
v_isShared_2432_ = v_isSharedCheck_2473_;
goto v_resetjp_2430_;
}
v_resetjp_2430_:
{
lean_object* v___x_2433_; lean_object* v_traceState_2434_; lean_object* v_env_2435_; lean_object* v_nextMacroScope_2436_; lean_object* v_ngen_2437_; lean_object* v_auxDeclNGen_2438_; lean_object* v_cache_2439_; lean_object* v_messages_2440_; lean_object* v_infoState_2441_; lean_object* v_snapshotTasks_2442_; lean_object* v___x_2444_; uint8_t v_isShared_2445_; uint8_t v_isSharedCheck_2472_; 
v___x_2433_ = lean_st_ref_take(v___y_2425_);
v_traceState_2434_ = lean_ctor_get(v___x_2433_, 4);
v_env_2435_ = lean_ctor_get(v___x_2433_, 0);
v_nextMacroScope_2436_ = lean_ctor_get(v___x_2433_, 1);
v_ngen_2437_ = lean_ctor_get(v___x_2433_, 2);
v_auxDeclNGen_2438_ = lean_ctor_get(v___x_2433_, 3);
v_cache_2439_ = lean_ctor_get(v___x_2433_, 5);
v_messages_2440_ = lean_ctor_get(v___x_2433_, 6);
v_infoState_2441_ = lean_ctor_get(v___x_2433_, 7);
v_snapshotTasks_2442_ = lean_ctor_get(v___x_2433_, 8);
v_isSharedCheck_2472_ = !lean_is_exclusive(v___x_2433_);
if (v_isSharedCheck_2472_ == 0)
{
v___x_2444_ = v___x_2433_;
v_isShared_2445_ = v_isSharedCheck_2472_;
goto v_resetjp_2443_;
}
else
{
lean_inc(v_snapshotTasks_2442_);
lean_inc(v_infoState_2441_);
lean_inc(v_messages_2440_);
lean_inc(v_cache_2439_);
lean_inc(v_traceState_2434_);
lean_inc(v_auxDeclNGen_2438_);
lean_inc(v_ngen_2437_);
lean_inc(v_nextMacroScope_2436_);
lean_inc(v_env_2435_);
lean_dec(v___x_2433_);
v___x_2444_ = lean_box(0);
v_isShared_2445_ = v_isSharedCheck_2472_;
goto v_resetjp_2443_;
}
v_resetjp_2443_:
{
uint64_t v_tid_2446_; lean_object* v_traces_2447_; lean_object* v___x_2449_; uint8_t v_isShared_2450_; uint8_t v_isSharedCheck_2471_; 
v_tid_2446_ = lean_ctor_get_uint64(v_traceState_2434_, sizeof(void*)*1);
v_traces_2447_ = lean_ctor_get(v_traceState_2434_, 0);
v_isSharedCheck_2471_ = !lean_is_exclusive(v_traceState_2434_);
if (v_isSharedCheck_2471_ == 0)
{
v___x_2449_ = v_traceState_2434_;
v_isShared_2450_ = v_isSharedCheck_2471_;
goto v_resetjp_2448_;
}
else
{
lean_inc(v_traces_2447_);
lean_dec(v_traceState_2434_);
v___x_2449_ = lean_box(0);
v_isShared_2450_ = v_isSharedCheck_2471_;
goto v_resetjp_2448_;
}
v_resetjp_2448_:
{
lean_object* v___x_2451_; lean_object* v___x_2452_; double v___x_2453_; uint8_t v___x_2454_; lean_object* v___x_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; lean_object* v___x_2462_; 
v___x_2451_ = lean_box(0);
v___x_2452_ = lean_box(0);
v___x_2453_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg___closed__0);
v___x_2454_ = 0;
v___x_2455_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg___closed__1));
v___x_2456_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2456_, 0, v_cls_2420_);
lean_ctor_set(v___x_2456_, 1, v___x_2452_);
lean_ctor_set(v___x_2456_, 2, v___x_2455_);
lean_ctor_set_float(v___x_2456_, sizeof(void*)*3, v___x_2453_);
lean_ctor_set_float(v___x_2456_, sizeof(void*)*3 + 8, v___x_2453_);
lean_ctor_set_uint8(v___x_2456_, sizeof(void*)*3 + 16, v___x_2454_);
v___x_2457_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg___closed__2));
v___x_2458_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2458_, 0, v___x_2456_);
lean_ctor_set(v___x_2458_, 1, v_a_2429_);
lean_ctor_set(v___x_2458_, 2, v___x_2457_);
lean_inc(v_ref_2427_);
v___x_2459_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2459_, 0, v_ref_2427_);
lean_ctor_set(v___x_2459_, 1, v___x_2458_);
v___x_2460_ = l_Lean_PersistentArray_push___redArg(v_traces_2447_, v___x_2459_);
if (v_isShared_2450_ == 0)
{
lean_ctor_set(v___x_2449_, 0, v___x_2460_);
v___x_2462_ = v___x_2449_;
goto v_reusejp_2461_;
}
else
{
lean_object* v_reuseFailAlloc_2470_; 
v_reuseFailAlloc_2470_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2470_, 0, v___x_2460_);
lean_ctor_set_uint64(v_reuseFailAlloc_2470_, sizeof(void*)*1, v_tid_2446_);
v___x_2462_ = v_reuseFailAlloc_2470_;
goto v_reusejp_2461_;
}
v_reusejp_2461_:
{
lean_object* v___x_2464_; 
if (v_isShared_2445_ == 0)
{
lean_ctor_set(v___x_2444_, 4, v___x_2462_);
v___x_2464_ = v___x_2444_;
goto v_reusejp_2463_;
}
else
{
lean_object* v_reuseFailAlloc_2469_; 
v_reuseFailAlloc_2469_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2469_, 0, v_env_2435_);
lean_ctor_set(v_reuseFailAlloc_2469_, 1, v_nextMacroScope_2436_);
lean_ctor_set(v_reuseFailAlloc_2469_, 2, v_ngen_2437_);
lean_ctor_set(v_reuseFailAlloc_2469_, 3, v_auxDeclNGen_2438_);
lean_ctor_set(v_reuseFailAlloc_2469_, 4, v___x_2462_);
lean_ctor_set(v_reuseFailAlloc_2469_, 5, v_cache_2439_);
lean_ctor_set(v_reuseFailAlloc_2469_, 6, v_messages_2440_);
lean_ctor_set(v_reuseFailAlloc_2469_, 7, v_infoState_2441_);
lean_ctor_set(v_reuseFailAlloc_2469_, 8, v_snapshotTasks_2442_);
v___x_2464_ = v_reuseFailAlloc_2469_;
goto v_reusejp_2463_;
}
v_reusejp_2463_:
{
lean_object* v___x_2465_; lean_object* v___x_2467_; 
v___x_2465_ = lean_st_ref_put(v___y_2425_, v___x_2464_);
if (v_isShared_2432_ == 0)
{
lean_ctor_set(v___x_2431_, 0, v___x_2451_);
v___x_2467_ = v___x_2431_;
goto v_reusejp_2466_;
}
else
{
lean_object* v_reuseFailAlloc_2468_; 
v_reuseFailAlloc_2468_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2468_, 0, v___x_2451_);
v___x_2467_ = v_reuseFailAlloc_2468_;
goto v_reusejp_2466_;
}
v_reusejp_2466_:
{
return v___x_2467_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg___boxed(lean_object* v_cls_2474_, lean_object* v_msg_2475_, lean_object* v___y_2476_, lean_object* v___y_2477_, lean_object* v___y_2478_, lean_object* v___y_2479_, lean_object* v___y_2480_){
_start:
{
lean_object* v_res_2481_; 
v_res_2481_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg(v_cls_2474_, v_msg_2475_, v___y_2476_, v___y_2477_, v___y_2478_, v___y_2479_);
lean_dec(v___y_2479_);
lean_dec_ref(v___y_2478_);
lean_dec(v___y_2477_);
lean_dec_ref(v___y_2476_);
return v_res_2481_;
}
}
static lean_object* _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__8(void){
_start:
{
lean_object* v___x_2497_; lean_object* v___x_2498_; lean_object* v___x_2499_; 
v___x_2497_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__5));
v___x_2498_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__7));
v___x_2499_ = l_Lean_Name_append(v___x_2498_, v___x_2497_);
return v___x_2499_;
}
}
static lean_object* _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__10(void){
_start:
{
lean_object* v___x_2501_; lean_object* v___x_2502_; 
v___x_2501_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__9));
v___x_2502_ = l_Lean_stringToMessageData(v___x_2501_);
return v___x_2502_;
}
}
static lean_object* _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__12(void){
_start:
{
lean_object* v___x_2504_; lean_object* v___x_2505_; 
v___x_2504_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__11));
v___x_2505_ = l_Lean_stringToMessageData(v___x_2504_);
return v___x_2505_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg(lean_object* v___x_2506_, lean_object* v_snd_2507_, lean_object* v_fst_2508_, lean_object* v_fst_2509_, lean_object* v___x_2510_, lean_object* v_range_2511_, lean_object* v_b_2512_, lean_object* v_i_2513_, lean_object* v___y_2514_, lean_object* v___y_2515_, lean_object* v___y_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_, lean_object* v___y_2524_){
_start:
{
lean_object* v_stop_2526_; lean_object* v_step_2527_; uint8_t v___x_2528_; 
v_stop_2526_ = lean_ctor_get(v_range_2511_, 1);
v_step_2527_ = lean_ctor_get(v_range_2511_, 2);
v___x_2528_ = lean_nat_dec_lt(v_i_2513_, v_stop_2526_);
if (v___x_2528_ == 0)
{
lean_object* v___x_2529_; 
lean_dec(v_i_2513_);
lean_dec_ref(v_fst_2509_);
lean_dec_ref(v_fst_2508_);
lean_dec(v_snd_2507_);
lean_dec_ref(v___x_2506_);
v___x_2529_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2529_, 0, v_b_2512_);
return v___x_2529_;
}
else
{
lean_object* v_size_2530_; lean_object* v___x_2531_; lean_object* v___y_2533_; lean_object* v___y_2534_; lean_object* v___y_2535_; lean_object* v___y_2536_; lean_object* v___y_2537_; lean_object* v___y_2538_; lean_object* v___y_2539_; lean_object* v___y_2540_; lean_object* v___y_2541_; lean_object* v___y_2542_; lean_object* v___y_2543_; lean_object* v___y_2557_; lean_object* v___x_2583_; uint8_t v___x_2584_; 
v_size_2530_ = lean_ctor_get(v___x_2510_, 2);
v___x_2531_ = lean_box(0);
v___x_2583_ = l_Lean_instInhabitedExpr;
v___x_2584_ = lean_nat_dec_lt(v_i_2513_, v_size_2530_);
if (v___x_2584_ == 0)
{
lean_object* v___x_2585_; 
v___x_2585_ = l_outOfBounds___redArg(v___x_2583_);
v___y_2557_ = v___x_2585_;
goto v___jp_2556_;
}
else
{
lean_object* v___x_2586_; 
v___x_2586_ = l_Lean_PersistentArray_get_x21___redArg(v___x_2583_, v___x_2510_, v_i_2513_);
v___y_2557_ = v___x_2586_;
goto v___jp_2556_;
}
v___jp_2532_:
{
lean_object* v_type_2544_; lean_object* v_u_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; 
v_type_2544_ = lean_ctor_get(v___x_2506_, 1);
v_u_2545_ = lean_ctor_get(v___x_2506_, 2);
v___x_2546_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__2));
v___x_2547_ = lean_box(0);
lean_inc(v_u_2545_);
v___x_2548_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2548_, 0, v_u_2545_);
lean_ctor_set(v___x_2548_, 1, v___x_2547_);
v___x_2549_ = l_Lean_mkConst(v___x_2546_, v___x_2548_);
lean_inc(v_snd_2507_);
v___x_2550_ = l_Lean_mkNatLit(v_snd_2507_);
lean_inc_ref(v_fst_2509_);
lean_inc_ref(v_fst_2508_);
lean_inc_ref(v_type_2544_);
v___x_2551_ = l_Lean_mkApp5(v___x_2549_, v_type_2544_, v_fst_2508_, v___x_2550_, v_fst_2509_, v___y_2533_);
v___x_2552_ = lean_unsigned_to_nat(0u);
v___x_2553_ = l_Lean_Meta_Grind_pushNewFact(v___x_2551_, v___x_2552_, v___y_2534_, v___y_2535_, v___y_2536_, v___y_2537_, v___y_2538_, v___y_2539_, v___y_2540_, v___y_2541_, v___y_2542_, v___y_2543_);
if (lean_obj_tag(v___x_2553_) == 0)
{
lean_object* v___x_2554_; 
lean_dec_ref_known(v___x_2553_, 1);
v___x_2554_ = lean_nat_add(v_i_2513_, v_step_2527_);
lean_dec(v_i_2513_);
v_b_2512_ = v___x_2531_;
v_i_2513_ = v___x_2554_;
goto _start;
}
else
{
lean_dec(v_i_2513_);
lean_dec_ref(v_fst_2509_);
lean_dec_ref(v_fst_2508_);
lean_dec(v_snd_2507_);
lean_dec_ref(v___x_2506_);
return v___x_2553_;
}
}
v___jp_2556_:
{
lean_object* v_toCold_2558_; lean_object* v_options_2559_; uint8_t v_hasTrace_2560_; 
v_toCold_2558_ = lean_ctor_get(v___y_2523_, 0);
v_options_2559_ = lean_ctor_get(v_toCold_2558_, 2);
v_hasTrace_2560_ = lean_ctor_get_uint8(v_options_2559_, sizeof(void*)*1);
if (v_hasTrace_2560_ == 0)
{
v___y_2533_ = v___y_2557_;
v___y_2534_ = v___y_2515_;
v___y_2535_ = v___y_2516_;
v___y_2536_ = v___y_2517_;
v___y_2537_ = v___y_2518_;
v___y_2538_ = v___y_2519_;
v___y_2539_ = v___y_2520_;
v___y_2540_ = v___y_2521_;
v___y_2541_ = v___y_2522_;
v___y_2542_ = v___y_2523_;
v___y_2543_ = v___y_2524_;
goto v___jp_2532_;
}
else
{
lean_object* v_inheritedTraceOptions_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; uint8_t v___x_2564_; 
v_inheritedTraceOptions_2561_ = lean_ctor_get(v_toCold_2558_, 11);
v___x_2562_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__5));
v___x_2563_ = lean_obj_once(&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__8, &l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__8_once, _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__8);
v___x_2564_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2561_, v_options_2559_, v___x_2563_);
if (v___x_2564_ == 0)
{
v___y_2533_ = v___y_2557_;
v___y_2534_ = v___y_2515_;
v___y_2535_ = v___y_2516_;
v___y_2536_ = v___y_2517_;
v___y_2537_ = v___y_2518_;
v___y_2538_ = v___y_2519_;
v___y_2539_ = v___y_2520_;
v___y_2540_ = v___y_2521_;
v___y_2541_ = v___y_2522_;
v___y_2542_ = v___y_2523_;
v___y_2543_ = v___y_2524_;
goto v___jp_2532_;
}
else
{
lean_object* v___x_2565_; 
v___x_2565_ = l_Lean_Meta_Grind_updateLastTag(v___y_2515_, v___y_2516_, v___y_2517_, v___y_2518_, v___y_2519_, v___y_2520_, v___y_2521_, v___y_2522_, v___y_2523_, v___y_2524_);
if (lean_obj_tag(v___x_2565_) == 0)
{
lean_object* v___x_2567_; uint8_t v_isShared_2568_; uint8_t v_isSharedCheck_2581_; 
v_isSharedCheck_2581_ = !lean_is_exclusive(v___x_2565_);
if (v_isSharedCheck_2581_ == 0)
{
lean_object* v_unused_2582_; 
v_unused_2582_ = lean_ctor_get(v___x_2565_, 0);
lean_dec(v_unused_2582_);
v___x_2567_ = v___x_2565_;
v_isShared_2568_ = v_isSharedCheck_2581_;
goto v_resetjp_2566_;
}
else
{
lean_dec(v___x_2565_);
v___x_2567_ = lean_box(0);
v_isShared_2568_ = v_isSharedCheck_2581_;
goto v_resetjp_2566_;
}
v_resetjp_2566_:
{
lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2572_; 
v___x_2569_ = lean_obj_once(&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__10, &l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__10_once, _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__10);
lean_inc(v_snd_2507_);
v___x_2570_ = l_Nat_reprFast(v_snd_2507_);
if (v_isShared_2568_ == 0)
{
lean_ctor_set_tag(v___x_2567_, 3);
lean_ctor_set(v___x_2567_, 0, v___x_2570_);
v___x_2572_ = v___x_2567_;
goto v_reusejp_2571_;
}
else
{
lean_object* v_reuseFailAlloc_2580_; 
v_reuseFailAlloc_2580_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2580_, 0, v___x_2570_);
v___x_2572_ = v_reuseFailAlloc_2580_;
goto v_reusejp_2571_;
}
v_reusejp_2571_:
{
lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; 
v___x_2573_ = l_Lean_MessageData_ofFormat(v___x_2572_);
v___x_2574_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2574_, 0, v___x_2569_);
lean_ctor_set(v___x_2574_, 1, v___x_2573_);
v___x_2575_ = lean_obj_once(&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__12, &l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__12_once, _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__12);
v___x_2576_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2576_, 0, v___x_2574_);
lean_ctor_set(v___x_2576_, 1, v___x_2575_);
lean_inc_ref(v___y_2557_);
v___x_2577_ = l_Lean_MessageData_ofExpr(v___y_2557_);
v___x_2578_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2578_, 0, v___x_2576_);
lean_ctor_set(v___x_2578_, 1, v___x_2577_);
v___x_2579_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg(v___x_2562_, v___x_2578_, v___y_2521_, v___y_2522_, v___y_2523_, v___y_2524_);
if (lean_obj_tag(v___x_2579_) == 0)
{
lean_dec_ref_known(v___x_2579_, 1);
v___y_2533_ = v___y_2557_;
v___y_2534_ = v___y_2515_;
v___y_2535_ = v___y_2516_;
v___y_2536_ = v___y_2517_;
v___y_2537_ = v___y_2518_;
v___y_2538_ = v___y_2519_;
v___y_2539_ = v___y_2520_;
v___y_2540_ = v___y_2521_;
v___y_2541_ = v___y_2522_;
v___y_2542_ = v___y_2523_;
v___y_2543_ = v___y_2524_;
goto v___jp_2532_;
}
else
{
lean_dec_ref(v___y_2557_);
lean_dec(v_i_2513_);
lean_dec_ref(v_fst_2509_);
lean_dec_ref(v_fst_2508_);
lean_dec(v_snd_2507_);
lean_dec_ref(v___x_2506_);
return v___x_2579_;
}
}
}
}
else
{
lean_dec_ref(v___y_2557_);
lean_dec(v_i_2513_);
lean_dec_ref(v_fst_2509_);
lean_dec_ref(v_fst_2508_);
lean_dec(v_snd_2507_);
lean_dec_ref(v___x_2506_);
return v___x_2565_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___boxed(lean_object** _args){
lean_object* v___x_2587_ = _args[0];
lean_object* v_snd_2588_ = _args[1];
lean_object* v_fst_2589_ = _args[2];
lean_object* v_fst_2590_ = _args[3];
lean_object* v___x_2591_ = _args[4];
lean_object* v_range_2592_ = _args[5];
lean_object* v_b_2593_ = _args[6];
lean_object* v_i_2594_ = _args[7];
lean_object* v___y_2595_ = _args[8];
lean_object* v___y_2596_ = _args[9];
lean_object* v___y_2597_ = _args[10];
lean_object* v___y_2598_ = _args[11];
lean_object* v___y_2599_ = _args[12];
lean_object* v___y_2600_ = _args[13];
lean_object* v___y_2601_ = _args[14];
lean_object* v___y_2602_ = _args[15];
lean_object* v___y_2603_ = _args[16];
lean_object* v___y_2604_ = _args[17];
lean_object* v___y_2605_ = _args[18];
lean_object* v___y_2606_ = _args[19];
_start:
{
lean_object* v_res_2607_; 
v_res_2607_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg(v___x_2587_, v_snd_2588_, v_fst_2589_, v_fst_2590_, v___x_2591_, v_range_2592_, v_b_2593_, v_i_2594_, v___y_2595_, v___y_2596_, v___y_2597_, v___y_2598_, v___y_2599_, v___y_2600_, v___y_2601_, v___y_2602_, v___y_2603_, v___y_2604_, v___y_2605_);
lean_dec(v___y_2605_);
lean_dec_ref(v___y_2604_);
lean_dec(v___y_2603_);
lean_dec_ref(v___y_2602_);
lean_dec(v___y_2601_);
lean_dec_ref(v___y_2600_);
lean_dec(v___y_2599_);
lean_dec_ref(v___y_2598_);
lean_dec(v___y_2597_);
lean_dec(v___y_2596_);
lean_dec_ref(v___y_2595_);
lean_dec_ref(v_range_2592_);
lean_dec_ref(v___x_2591_);
return v_res_2607_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars(lean_object* v_a_2608_, lean_object* v_a_2609_, lean_object* v_a_2610_, lean_object* v_a_2611_, lean_object* v_a_2612_, lean_object* v_a_2613_, lean_object* v_a_2614_, lean_object* v_a_2615_, lean_object* v_a_2616_, lean_object* v_a_2617_, lean_object* v_a_2618_){
_start:
{
lean_object* v___x_2620_; 
v___x_2620_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v_a_2608_, v_a_2609_, v_a_2610_, v_a_2611_, v_a_2612_, v_a_2613_, v_a_2614_, v_a_2615_, v_a_2616_, v_a_2617_, v_a_2618_);
if (lean_obj_tag(v___x_2620_) == 0)
{
lean_object* v_a_2621_; lean_object* v___x_2623_; uint8_t v_isShared_2624_; uint8_t v_isSharedCheck_2650_; 
v_a_2621_ = lean_ctor_get(v___x_2620_, 0);
v_isSharedCheck_2650_ = !lean_is_exclusive(v___x_2620_);
if (v_isSharedCheck_2650_ == 0)
{
v___x_2623_ = v___x_2620_;
v_isShared_2624_ = v_isSharedCheck_2650_;
goto v_resetjp_2622_;
}
else
{
lean_inc(v_a_2621_);
lean_dec(v___x_2620_);
v___x_2623_ = lean_box(0);
v_isShared_2624_ = v_isSharedCheck_2650_;
goto v_resetjp_2622_;
}
v_resetjp_2622_:
{
lean_object* v_powIdentityInst_x3f_2625_; 
v_powIdentityInst_x3f_2625_ = lean_ctor_get(v_a_2621_, 7);
if (lean_obj_tag(v_powIdentityInst_x3f_2625_) == 1)
{
lean_object* v_val_2626_; lean_object* v_snd_2627_; lean_object* v_toRing_2628_; lean_object* v_vars_2629_; lean_object* v_powIdentityVarCount_2630_; lean_object* v_fst_2631_; lean_object* v_fst_2632_; lean_object* v_snd_2633_; lean_object* v_size_2634_; uint8_t v___x_2635_; 
v_val_2626_ = lean_ctor_get(v_powIdentityInst_x3f_2625_, 0);
lean_inc(v_val_2626_);
v_snd_2627_ = lean_ctor_get(v_val_2626_, 1);
lean_inc(v_snd_2627_);
v_toRing_2628_ = lean_ctor_get(v_a_2621_, 0);
lean_inc_ref(v_toRing_2628_);
v_vars_2629_ = lean_ctor_get(v_toRing_2628_, 14);
lean_inc_ref(v_vars_2629_);
v_powIdentityVarCount_2630_ = lean_ctor_get(v_a_2621_, 15);
lean_inc(v_powIdentityVarCount_2630_);
lean_dec(v_a_2621_);
v_fst_2631_ = lean_ctor_get(v_val_2626_, 0);
lean_inc(v_fst_2631_);
lean_dec(v_val_2626_);
v_fst_2632_ = lean_ctor_get(v_snd_2627_, 0);
lean_inc(v_fst_2632_);
v_snd_2633_ = lean_ctor_get(v_snd_2627_, 1);
lean_inc(v_snd_2633_);
lean_dec(v_snd_2627_);
v_size_2634_ = lean_ctor_get(v_vars_2629_, 2);
v___x_2635_ = lean_nat_dec_le(v_size_2634_, v_powIdentityVarCount_2630_);
if (v___x_2635_ == 0)
{
lean_object* v___f_2636_; lean_object* v___x_2637_; lean_object* v___x_2638_; lean_object* v___x_2639_; lean_object* v___x_2640_; 
lean_del_object(v___x_2623_);
lean_inc_n(v_size_2634_, 2);
v___f_2636_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars___lam__0), 2, 1);
lean_closure_set(v___f_2636_, 0, v_size_2634_);
v___x_2637_ = lean_unsigned_to_nat(1u);
lean_inc(v_powIdentityVarCount_2630_);
v___x_2638_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2638_, 0, v_powIdentityVarCount_2630_);
lean_ctor_set(v___x_2638_, 1, v_size_2634_);
lean_ctor_set(v___x_2638_, 2, v___x_2637_);
v___x_2639_ = lean_box(0);
v___x_2640_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg(v_toRing_2628_, v_snd_2633_, v_fst_2632_, v_fst_2631_, v_vars_2629_, v___x_2638_, v___x_2639_, v_powIdentityVarCount_2630_, v_a_2608_, v_a_2609_, v_a_2610_, v_a_2611_, v_a_2612_, v_a_2613_, v_a_2614_, v_a_2615_, v_a_2616_, v_a_2617_, v_a_2618_);
lean_dec_ref_known(v___x_2638_, 3);
lean_dec_ref(v_vars_2629_);
if (lean_obj_tag(v___x_2640_) == 0)
{
lean_object* v___x_2641_; 
lean_dec_ref_known(v___x_2640_, 1);
v___x_2641_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(v___f_2636_, v_a_2608_, v_a_2609_);
return v___x_2641_;
}
else
{
lean_dec_ref(v___f_2636_);
return v___x_2640_;
}
}
else
{
lean_object* v___x_2642_; lean_object* v___x_2644_; 
lean_dec(v_snd_2633_);
lean_dec(v_fst_2632_);
lean_dec(v_fst_2631_);
lean_dec(v_powIdentityVarCount_2630_);
lean_dec_ref(v_vars_2629_);
lean_dec_ref(v_toRing_2628_);
v___x_2642_ = lean_box(0);
if (v_isShared_2624_ == 0)
{
lean_ctor_set(v___x_2623_, 0, v___x_2642_);
v___x_2644_ = v___x_2623_;
goto v_reusejp_2643_;
}
else
{
lean_object* v_reuseFailAlloc_2645_; 
v_reuseFailAlloc_2645_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2645_, 0, v___x_2642_);
v___x_2644_ = v_reuseFailAlloc_2645_;
goto v_reusejp_2643_;
}
v_reusejp_2643_:
{
return v___x_2644_;
}
}
}
else
{
lean_object* v___x_2646_; lean_object* v___x_2648_; 
lean_dec(v_a_2621_);
v___x_2646_ = lean_box(0);
if (v_isShared_2624_ == 0)
{
lean_ctor_set(v___x_2623_, 0, v___x_2646_);
v___x_2648_ = v___x_2623_;
goto v_reusejp_2647_;
}
else
{
lean_object* v_reuseFailAlloc_2649_; 
v_reuseFailAlloc_2649_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2649_, 0, v___x_2646_);
v___x_2648_ = v_reuseFailAlloc_2649_;
goto v_reusejp_2647_;
}
v_reusejp_2647_:
{
return v___x_2648_;
}
}
}
}
else
{
lean_object* v_a_2651_; lean_object* v___x_2653_; uint8_t v_isShared_2654_; uint8_t v_isSharedCheck_2658_; 
v_a_2651_ = lean_ctor_get(v___x_2620_, 0);
v_isSharedCheck_2658_ = !lean_is_exclusive(v___x_2620_);
if (v_isSharedCheck_2658_ == 0)
{
v___x_2653_ = v___x_2620_;
v_isShared_2654_ = v_isSharedCheck_2658_;
goto v_resetjp_2652_;
}
else
{
lean_inc(v_a_2651_);
lean_dec(v___x_2620_);
v___x_2653_ = lean_box(0);
v_isShared_2654_ = v_isSharedCheck_2658_;
goto v_resetjp_2652_;
}
v_resetjp_2652_:
{
lean_object* v___x_2656_; 
if (v_isShared_2654_ == 0)
{
v___x_2656_ = v___x_2653_;
goto v_reusejp_2655_;
}
else
{
lean_object* v_reuseFailAlloc_2657_; 
v_reuseFailAlloc_2657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2657_, 0, v_a_2651_);
v___x_2656_ = v_reuseFailAlloc_2657_;
goto v_reusejp_2655_;
}
v_reusejp_2655_:
{
return v___x_2656_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars___boxed(lean_object* v_a_2659_, lean_object* v_a_2660_, lean_object* v_a_2661_, lean_object* v_a_2662_, lean_object* v_a_2663_, lean_object* v_a_2664_, lean_object* v_a_2665_, lean_object* v_a_2666_, lean_object* v_a_2667_, lean_object* v_a_2668_, lean_object* v_a_2669_, lean_object* v_a_2670_){
_start:
{
lean_object* v_res_2671_; 
v_res_2671_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars(v_a_2659_, v_a_2660_, v_a_2661_, v_a_2662_, v_a_2663_, v_a_2664_, v_a_2665_, v_a_2666_, v_a_2667_, v_a_2668_, v_a_2669_);
lean_dec(v_a_2669_);
lean_dec_ref(v_a_2668_);
lean_dec(v_a_2667_);
lean_dec_ref(v_a_2666_);
lean_dec(v_a_2665_);
lean_dec_ref(v_a_2664_);
lean_dec(v_a_2663_);
lean_dec_ref(v_a_2662_);
lean_dec(v_a_2661_);
lean_dec(v_a_2660_);
lean_dec_ref(v_a_2659_);
return v_res_2671_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0(lean_object* v_cls_2672_, lean_object* v_msg_2673_, lean_object* v___y_2674_, lean_object* v___y_2675_, lean_object* v___y_2676_, lean_object* v___y_2677_, lean_object* v___y_2678_, lean_object* v___y_2679_, lean_object* v___y_2680_, lean_object* v___y_2681_, lean_object* v___y_2682_, lean_object* v___y_2683_, lean_object* v___y_2684_){
_start:
{
lean_object* v___x_2686_; 
v___x_2686_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg(v_cls_2672_, v_msg_2673_, v___y_2681_, v___y_2682_, v___y_2683_, v___y_2684_);
return v___x_2686_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___boxed(lean_object* v_cls_2687_, lean_object* v_msg_2688_, lean_object* v___y_2689_, lean_object* v___y_2690_, lean_object* v___y_2691_, lean_object* v___y_2692_, lean_object* v___y_2693_, lean_object* v___y_2694_, lean_object* v___y_2695_, lean_object* v___y_2696_, lean_object* v___y_2697_, lean_object* v___y_2698_, lean_object* v___y_2699_, lean_object* v___y_2700_){
_start:
{
lean_object* v_res_2701_; 
v_res_2701_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0(v_cls_2687_, v_msg_2688_, v___y_2689_, v___y_2690_, v___y_2691_, v___y_2692_, v___y_2693_, v___y_2694_, v___y_2695_, v___y_2696_, v___y_2697_, v___y_2698_, v___y_2699_);
lean_dec(v___y_2699_);
lean_dec_ref(v___y_2698_);
lean_dec(v___y_2697_);
lean_dec_ref(v___y_2696_);
lean_dec(v___y_2695_);
lean_dec_ref(v___y_2694_);
lean_dec(v___y_2693_);
lean_dec_ref(v___y_2692_);
lean_dec(v___y_2691_);
lean_dec(v___y_2690_);
lean_dec_ref(v___y_2689_);
return v_res_2701_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1(lean_object* v___x_2702_, lean_object* v_snd_2703_, lean_object* v_fst_2704_, lean_object* v_fst_2705_, lean_object* v___x_2706_, lean_object* v_range_2707_, lean_object* v_b_2708_, lean_object* v_i_2709_, lean_object* v_hs_2710_, lean_object* v_hl_2711_, lean_object* v___y_2712_, lean_object* v___y_2713_, lean_object* v___y_2714_, lean_object* v___y_2715_, lean_object* v___y_2716_, lean_object* v___y_2717_, lean_object* v___y_2718_, lean_object* v___y_2719_, lean_object* v___y_2720_, lean_object* v___y_2721_, lean_object* v___y_2722_){
_start:
{
lean_object* v___x_2724_; 
v___x_2724_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg(v___x_2702_, v_snd_2703_, v_fst_2704_, v_fst_2705_, v___x_2706_, v_range_2707_, v_b_2708_, v_i_2709_, v___y_2712_, v___y_2713_, v___y_2714_, v___y_2715_, v___y_2716_, v___y_2717_, v___y_2718_, v___y_2719_, v___y_2720_, v___y_2721_, v___y_2722_);
return v___x_2724_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___boxed(lean_object** _args){
lean_object* v___x_2725_ = _args[0];
lean_object* v_snd_2726_ = _args[1];
lean_object* v_fst_2727_ = _args[2];
lean_object* v_fst_2728_ = _args[3];
lean_object* v___x_2729_ = _args[4];
lean_object* v_range_2730_ = _args[5];
lean_object* v_b_2731_ = _args[6];
lean_object* v_i_2732_ = _args[7];
lean_object* v_hs_2733_ = _args[8];
lean_object* v_hl_2734_ = _args[9];
lean_object* v___y_2735_ = _args[10];
lean_object* v___y_2736_ = _args[11];
lean_object* v___y_2737_ = _args[12];
lean_object* v___y_2738_ = _args[13];
lean_object* v___y_2739_ = _args[14];
lean_object* v___y_2740_ = _args[15];
lean_object* v___y_2741_ = _args[16];
lean_object* v___y_2742_ = _args[17];
lean_object* v___y_2743_ = _args[18];
lean_object* v___y_2744_ = _args[19];
lean_object* v___y_2745_ = _args[20];
lean_object* v___y_2746_ = _args[21];
_start:
{
lean_object* v_res_2747_; 
v_res_2747_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1(v___x_2725_, v_snd_2726_, v_fst_2727_, v_fst_2728_, v___x_2729_, v_range_2730_, v_b_2731_, v_i_2732_, v_hs_2733_, v_hl_2734_, v___y_2735_, v___y_2736_, v___y_2737_, v___y_2738_, v___y_2739_, v___y_2740_, v___y_2741_, v___y_2742_, v___y_2743_, v___y_2744_, v___y_2745_);
lean_dec(v___y_2745_);
lean_dec_ref(v___y_2744_);
lean_dec(v___y_2743_);
lean_dec_ref(v___y_2742_);
lean_dec(v___y_2741_);
lean_dec_ref(v___y_2740_);
lean_dec(v___y_2739_);
lean_dec_ref(v___y_2738_);
lean_dec(v___y_2737_);
lean_dec(v___y_2736_);
lean_dec_ref(v___y_2735_);
lean_dec_ref(v_range_2730_);
lean_dec_ref(v___x_2729_);
return v_res_2747_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeInv(lean_object* v_e_2748_, lean_object* v_a_2749_, lean_object* v_a_2750_, lean_object* v_a_2751_, lean_object* v_a_2752_, lean_object* v_a_2753_, lean_object* v_a_2754_, lean_object* v_a_2755_, lean_object* v_a_2756_, lean_object* v_a_2757_, lean_object* v_a_2758_){
_start:
{
lean_object* v___x_2764_; 
lean_inc_ref(v_e_2748_);
v___x_2764_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_2748_, v_a_2756_);
if (lean_obj_tag(v___x_2764_) == 0)
{
lean_object* v_a_2765_; lean_object* v___x_2766_; uint8_t v___x_2767_; 
v_a_2765_ = lean_ctor_get(v___x_2764_, 0);
lean_inc(v_a_2765_);
lean_dec_ref_known(v___x_2764_, 1);
v___x_2766_ = l_Lean_Expr_cleanupAnnotations(v_a_2765_);
v___x_2767_ = l_Lean_Expr_isApp(v___x_2766_);
if (v___x_2767_ == 0)
{
lean_dec_ref(v___x_2766_);
lean_dec_ref(v_e_2748_);
goto v___jp_2760_;
}
else
{
lean_object* v_arg_2768_; lean_object* v___x_2769_; uint8_t v___x_2770_; 
v_arg_2768_ = lean_ctor_get(v___x_2766_, 1);
lean_inc_ref(v_arg_2768_);
v___x_2769_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2766_);
v___x_2770_ = l_Lean_Expr_isApp(v___x_2769_);
if (v___x_2770_ == 0)
{
lean_dec_ref(v___x_2769_);
lean_dec_ref(v_arg_2768_);
lean_dec_ref(v_e_2748_);
goto v___jp_2760_;
}
else
{
lean_object* v_arg_2771_; lean_object* v___x_2772_; uint8_t v___x_2773_; 
v_arg_2771_ = lean_ctor_get(v___x_2769_, 1);
lean_inc_ref(v_arg_2771_);
v___x_2772_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2769_);
v___x_2773_ = l_Lean_Expr_isApp(v___x_2772_);
if (v___x_2773_ == 0)
{
lean_dec_ref(v___x_2772_);
lean_dec_ref(v_arg_2771_);
lean_dec_ref(v_arg_2768_);
lean_dec_ref(v_e_2748_);
goto v___jp_2760_;
}
else
{
lean_object* v_arg_2774_; lean_object* v___x_2775_; lean_object* v___x_2776_; uint8_t v___x_2777_; 
v_arg_2774_ = lean_ctor_get(v___x_2772_, 1);
lean_inc_ref(v_arg_2774_);
v___x_2775_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2772_);
v___x_2776_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___closed__6));
v___x_2777_ = l_Lean_Expr_isConstOf(v___x_2775_, v___x_2776_);
lean_dec_ref(v___x_2775_);
if (v___x_2777_ == 0)
{
lean_dec_ref(v_arg_2774_);
lean_dec_ref(v_arg_2771_);
lean_dec_ref(v_arg_2768_);
lean_dec_ref(v_e_2748_);
goto v___jp_2760_;
}
else
{
lean_object* v___x_2778_; 
v___x_2778_ = l_Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f(v_arg_2774_, v_a_2749_, v_a_2750_, v_a_2751_, v_a_2752_, v_a_2753_, v_a_2754_, v_a_2755_, v_a_2756_, v_a_2757_, v_a_2758_);
if (lean_obj_tag(v___x_2778_) == 0)
{
lean_object* v_a_2779_; lean_object* v___x_2781_; uint8_t v_isShared_2782_; uint8_t v_isSharedCheck_2808_; 
v_a_2779_ = lean_ctor_get(v___x_2778_, 0);
v_isSharedCheck_2808_ = !lean_is_exclusive(v___x_2778_);
if (v_isSharedCheck_2808_ == 0)
{
v___x_2781_ = v___x_2778_;
v_isShared_2782_ = v_isSharedCheck_2808_;
goto v_resetjp_2780_;
}
else
{
lean_inc(v_a_2779_);
lean_dec(v___x_2778_);
v___x_2781_ = lean_box(0);
v_isShared_2782_ = v_isSharedCheck_2808_;
goto v_resetjp_2780_;
}
v_resetjp_2780_:
{
if (lean_obj_tag(v_a_2779_) == 1)
{
lean_object* v_val_2783_; uint8_t v___x_2784_; lean_object* v___x_2785_; lean_object* v___x_2786_; 
lean_del_object(v___x_2781_);
v_val_2783_ = lean_ctor_get(v_a_2779_, 0);
lean_inc(v_val_2783_);
lean_dec_ref_known(v_a_2779_, 1);
v___x_2784_ = 0;
v___x_2785_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2785_, 0, v_val_2783_);
lean_ctor_set_uint8(v___x_2785_, sizeof(void*)*1, v___x_2784_);
v___x_2786_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv(v_e_2748_, v_arg_2771_, v_arg_2768_, v___x_2785_, v_a_2749_, v_a_2750_, v_a_2751_, v_a_2752_, v_a_2753_, v_a_2754_, v_a_2755_, v_a_2756_, v_a_2757_, v_a_2758_);
lean_dec_ref_known(v___x_2785_, 1);
lean_dec_ref(v_arg_2771_);
if (lean_obj_tag(v___x_2786_) == 0)
{
lean_object* v___x_2788_; uint8_t v_isShared_2789_; uint8_t v_isSharedCheck_2794_; 
v_isSharedCheck_2794_ = !lean_is_exclusive(v___x_2786_);
if (v_isSharedCheck_2794_ == 0)
{
lean_object* v_unused_2795_; 
v_unused_2795_ = lean_ctor_get(v___x_2786_, 0);
lean_dec(v_unused_2795_);
v___x_2788_ = v___x_2786_;
v_isShared_2789_ = v_isSharedCheck_2794_;
goto v_resetjp_2787_;
}
else
{
lean_dec(v___x_2786_);
v___x_2788_ = lean_box(0);
v_isShared_2789_ = v_isSharedCheck_2794_;
goto v_resetjp_2787_;
}
v_resetjp_2787_:
{
lean_object* v___x_2790_; lean_object* v___x_2792_; 
v___x_2790_ = lean_box(v___x_2777_);
if (v_isShared_2789_ == 0)
{
lean_ctor_set(v___x_2788_, 0, v___x_2790_);
v___x_2792_ = v___x_2788_;
goto v_reusejp_2791_;
}
else
{
lean_object* v_reuseFailAlloc_2793_; 
v_reuseFailAlloc_2793_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2793_, 0, v___x_2790_);
v___x_2792_ = v_reuseFailAlloc_2793_;
goto v_reusejp_2791_;
}
v_reusejp_2791_:
{
return v___x_2792_;
}
}
}
else
{
lean_object* v_a_2796_; lean_object* v___x_2798_; uint8_t v_isShared_2799_; uint8_t v_isSharedCheck_2803_; 
v_a_2796_ = lean_ctor_get(v___x_2786_, 0);
v_isSharedCheck_2803_ = !lean_is_exclusive(v___x_2786_);
if (v_isSharedCheck_2803_ == 0)
{
v___x_2798_ = v___x_2786_;
v_isShared_2799_ = v_isSharedCheck_2803_;
goto v_resetjp_2797_;
}
else
{
lean_inc(v_a_2796_);
lean_dec(v___x_2786_);
v___x_2798_ = lean_box(0);
v_isShared_2799_ = v_isSharedCheck_2803_;
goto v_resetjp_2797_;
}
v_resetjp_2797_:
{
lean_object* v___x_2801_; 
if (v_isShared_2799_ == 0)
{
v___x_2801_ = v___x_2798_;
goto v_reusejp_2800_;
}
else
{
lean_object* v_reuseFailAlloc_2802_; 
v_reuseFailAlloc_2802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2802_, 0, v_a_2796_);
v___x_2801_ = v_reuseFailAlloc_2802_;
goto v_reusejp_2800_;
}
v_reusejp_2800_:
{
return v___x_2801_;
}
}
}
}
else
{
lean_object* v___x_2804_; lean_object* v___x_2806_; 
lean_dec(v_a_2779_);
lean_dec_ref(v_arg_2771_);
lean_dec_ref(v_arg_2768_);
lean_dec_ref(v_e_2748_);
v___x_2804_ = lean_box(v___x_2777_);
if (v_isShared_2782_ == 0)
{
lean_ctor_set(v___x_2781_, 0, v___x_2804_);
v___x_2806_ = v___x_2781_;
goto v_reusejp_2805_;
}
else
{
lean_object* v_reuseFailAlloc_2807_; 
v_reuseFailAlloc_2807_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2807_, 0, v___x_2804_);
v___x_2806_ = v_reuseFailAlloc_2807_;
goto v_reusejp_2805_;
}
v_reusejp_2805_:
{
return v___x_2806_;
}
}
}
}
else
{
lean_object* v_a_2809_; lean_object* v___x_2811_; uint8_t v_isShared_2812_; uint8_t v_isSharedCheck_2816_; 
lean_dec_ref(v_arg_2771_);
lean_dec_ref(v_arg_2768_);
lean_dec_ref(v_e_2748_);
v_a_2809_ = lean_ctor_get(v___x_2778_, 0);
v_isSharedCheck_2816_ = !lean_is_exclusive(v___x_2778_);
if (v_isSharedCheck_2816_ == 0)
{
v___x_2811_ = v___x_2778_;
v_isShared_2812_ = v_isSharedCheck_2816_;
goto v_resetjp_2810_;
}
else
{
lean_inc(v_a_2809_);
lean_dec(v___x_2778_);
v___x_2811_ = lean_box(0);
v_isShared_2812_ = v_isSharedCheck_2816_;
goto v_resetjp_2810_;
}
v_resetjp_2810_:
{
lean_object* v___x_2814_; 
if (v_isShared_2812_ == 0)
{
v___x_2814_ = v___x_2811_;
goto v_reusejp_2813_;
}
else
{
lean_object* v_reuseFailAlloc_2815_; 
v_reuseFailAlloc_2815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2815_, 0, v_a_2809_);
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
}
}
}
}
else
{
lean_object* v_a_2817_; lean_object* v___x_2819_; uint8_t v_isShared_2820_; uint8_t v_isSharedCheck_2824_; 
lean_dec_ref(v_e_2748_);
v_a_2817_ = lean_ctor_get(v___x_2764_, 0);
v_isSharedCheck_2824_ = !lean_is_exclusive(v___x_2764_);
if (v_isSharedCheck_2824_ == 0)
{
v___x_2819_ = v___x_2764_;
v_isShared_2820_ = v_isSharedCheck_2824_;
goto v_resetjp_2818_;
}
else
{
lean_inc(v_a_2817_);
lean_dec(v___x_2764_);
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
v___jp_2760_:
{
uint8_t v___x_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; 
v___x_2761_ = 0;
v___x_2762_ = lean_box(v___x_2761_);
v___x_2763_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2763_, 0, v___x_2762_);
return v___x_2763_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeInv___boxed(lean_object* v_e_2825_, lean_object* v_a_2826_, lean_object* v_a_2827_, lean_object* v_a_2828_, lean_object* v_a_2829_, lean_object* v_a_2830_, lean_object* v_a_2831_, lean_object* v_a_2832_, lean_object* v_a_2833_, lean_object* v_a_2834_, lean_object* v_a_2835_, lean_object* v_a_2836_){
_start:
{
lean_object* v_res_2837_; 
v_res_2837_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeInv(v_e_2825_, v_a_2826_, v_a_2827_, v_a_2828_, v_a_2829_, v_a_2830_, v_a_2831_, v_a_2832_, v_a_2833_, v_a_2834_, v_a_2835_);
lean_dec(v_a_2835_);
lean_dec_ref(v_a_2834_);
lean_dec(v_a_2833_);
lean_dec_ref(v_a_2832_);
lean_dec(v_a_2831_);
lean_dec_ref(v_a_2830_);
lean_dec(v_a_2829_);
lean_dec_ref(v_a_2828_);
lean_dec(v_a_2827_);
lean_dec(v_a_2826_);
return v_res_2837_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0_spec__1_spec__5___redArg(lean_object* v_x_2838_, lean_object* v_x_2839_, lean_object* v_x_2840_, lean_object* v_x_2841_){
_start:
{
lean_object* v_ks_2842_; lean_object* v_vs_2843_; lean_object* v___x_2845_; uint8_t v_isShared_2846_; uint8_t v_isSharedCheck_2869_; 
v_ks_2842_ = lean_ctor_get(v_x_2838_, 0);
v_vs_2843_ = lean_ctor_get(v_x_2838_, 1);
v_isSharedCheck_2869_ = !lean_is_exclusive(v_x_2838_);
if (v_isSharedCheck_2869_ == 0)
{
v___x_2845_ = v_x_2838_;
v_isShared_2846_ = v_isSharedCheck_2869_;
goto v_resetjp_2844_;
}
else
{
lean_inc(v_vs_2843_);
lean_inc(v_ks_2842_);
lean_dec(v_x_2838_);
v___x_2845_ = lean_box(0);
v_isShared_2846_ = v_isSharedCheck_2869_;
goto v_resetjp_2844_;
}
v_resetjp_2844_:
{
lean_object* v___x_2847_; uint8_t v___x_2848_; 
v___x_2847_ = lean_array_get_size(v_ks_2842_);
v___x_2848_ = lean_nat_dec_lt(v_x_2839_, v___x_2847_);
if (v___x_2848_ == 0)
{
lean_object* v___x_2849_; lean_object* v___x_2850_; lean_object* v___x_2852_; 
lean_dec(v_x_2839_);
v___x_2849_ = lean_array_push(v_ks_2842_, v_x_2840_);
v___x_2850_ = lean_array_push(v_vs_2843_, v_x_2841_);
if (v_isShared_2846_ == 0)
{
lean_ctor_set(v___x_2845_, 1, v___x_2850_);
lean_ctor_set(v___x_2845_, 0, v___x_2849_);
v___x_2852_ = v___x_2845_;
goto v_reusejp_2851_;
}
else
{
lean_object* v_reuseFailAlloc_2853_; 
v_reuseFailAlloc_2853_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2853_, 0, v___x_2849_);
lean_ctor_set(v_reuseFailAlloc_2853_, 1, v___x_2850_);
v___x_2852_ = v_reuseFailAlloc_2853_;
goto v_reusejp_2851_;
}
v_reusejp_2851_:
{
return v___x_2852_;
}
}
else
{
lean_object* v_k_x27_2854_; size_t v___x_2855_; size_t v___x_2856_; uint8_t v___x_2857_; 
v_k_x27_2854_ = lean_array_fget_borrowed(v_ks_2842_, v_x_2839_);
v___x_2855_ = lean_ptr_addr(v_x_2840_);
v___x_2856_ = lean_ptr_addr(v_k_x27_2854_);
v___x_2857_ = lean_usize_dec_eq(v___x_2855_, v___x_2856_);
if (v___x_2857_ == 0)
{
lean_object* v___x_2859_; 
if (v_isShared_2846_ == 0)
{
v___x_2859_ = v___x_2845_;
goto v_reusejp_2858_;
}
else
{
lean_object* v_reuseFailAlloc_2863_; 
v_reuseFailAlloc_2863_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2863_, 0, v_ks_2842_);
lean_ctor_set(v_reuseFailAlloc_2863_, 1, v_vs_2843_);
v___x_2859_ = v_reuseFailAlloc_2863_;
goto v_reusejp_2858_;
}
v_reusejp_2858_:
{
lean_object* v___x_2860_; lean_object* v___x_2861_; 
v___x_2860_ = lean_unsigned_to_nat(1u);
v___x_2861_ = lean_nat_add(v_x_2839_, v___x_2860_);
lean_dec(v_x_2839_);
v_x_2838_ = v___x_2859_;
v_x_2839_ = v___x_2861_;
goto _start;
}
}
else
{
lean_object* v___x_2864_; lean_object* v___x_2865_; lean_object* v___x_2867_; 
v___x_2864_ = lean_array_fset(v_ks_2842_, v_x_2839_, v_x_2840_);
v___x_2865_ = lean_array_fset(v_vs_2843_, v_x_2839_, v_x_2841_);
lean_dec(v_x_2839_);
if (v_isShared_2846_ == 0)
{
lean_ctor_set(v___x_2845_, 1, v___x_2865_);
lean_ctor_set(v___x_2845_, 0, v___x_2864_);
v___x_2867_ = v___x_2845_;
goto v_reusejp_2866_;
}
else
{
lean_object* v_reuseFailAlloc_2868_; 
v_reuseFailAlloc_2868_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2868_, 0, v___x_2864_);
lean_ctor_set(v_reuseFailAlloc_2868_, 1, v___x_2865_);
v___x_2867_ = v_reuseFailAlloc_2868_;
goto v_reusejp_2866_;
}
v_reusejp_2866_:
{
return v___x_2867_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0_spec__1___redArg(lean_object* v_n_2870_, lean_object* v_k_2871_, lean_object* v_v_2872_){
_start:
{
lean_object* v___x_2873_; lean_object* v___x_2874_; 
v___x_2873_ = lean_unsigned_to_nat(0u);
v___x_2874_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0_spec__1_spec__5___redArg(v_n_2870_, v___x_2873_, v_k_2871_, v_v_2872_);
return v___x_2874_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0___redArg(lean_object* v_x_2875_, size_t v_x_2876_, size_t v_x_2877_, lean_object* v_x_2878_, lean_object* v_x_2879_){
_start:
{
if (lean_obj_tag(v_x_2875_) == 0)
{
lean_object* v_es_2880_; size_t v___x_2881_; size_t v___x_2882_; lean_object* v_j_2883_; lean_object* v___x_2884_; uint8_t v___x_2885_; 
v_es_2880_ = lean_ctor_get(v_x_2875_, 0);
v___x_2881_ = ((size_t)31ULL);
v___x_2882_ = lean_usize_land(v_x_2876_, v___x_2881_);
v_j_2883_ = lean_usize_to_nat(v___x_2882_);
v___x_2884_ = lean_array_get_size(v_es_2880_);
v___x_2885_ = lean_nat_dec_lt(v_j_2883_, v___x_2884_);
if (v___x_2885_ == 0)
{
lean_dec(v_j_2883_);
lean_dec(v_x_2879_);
lean_dec_ref(v_x_2878_);
return v_x_2875_;
}
else
{
lean_object* v___x_2887_; uint8_t v_isShared_2888_; uint8_t v_isSharedCheck_2926_; 
lean_inc_ref(v_es_2880_);
v_isSharedCheck_2926_ = !lean_is_exclusive(v_x_2875_);
if (v_isSharedCheck_2926_ == 0)
{
lean_object* v_unused_2927_; 
v_unused_2927_ = lean_ctor_get(v_x_2875_, 0);
lean_dec(v_unused_2927_);
v___x_2887_ = v_x_2875_;
v_isShared_2888_ = v_isSharedCheck_2926_;
goto v_resetjp_2886_;
}
else
{
lean_dec(v_x_2875_);
v___x_2887_ = lean_box(0);
v_isShared_2888_ = v_isSharedCheck_2926_;
goto v_resetjp_2886_;
}
v_resetjp_2886_:
{
lean_object* v_v_2889_; lean_object* v___x_2890_; lean_object* v_xs_x27_2891_; lean_object* v___y_2893_; 
v_v_2889_ = lean_array_fget(v_es_2880_, v_j_2883_);
v___x_2890_ = lean_box(0);
v_xs_x27_2891_ = lean_array_fset(v_es_2880_, v_j_2883_, v___x_2890_);
switch(lean_obj_tag(v_v_2889_))
{
case 0:
{
lean_object* v_key_2898_; lean_object* v_val_2899_; lean_object* v___x_2901_; uint8_t v_isShared_2902_; uint8_t v_isSharedCheck_2911_; 
v_key_2898_ = lean_ctor_get(v_v_2889_, 0);
v_val_2899_ = lean_ctor_get(v_v_2889_, 1);
v_isSharedCheck_2911_ = !lean_is_exclusive(v_v_2889_);
if (v_isSharedCheck_2911_ == 0)
{
v___x_2901_ = v_v_2889_;
v_isShared_2902_ = v_isSharedCheck_2911_;
goto v_resetjp_2900_;
}
else
{
lean_inc(v_val_2899_);
lean_inc(v_key_2898_);
lean_dec(v_v_2889_);
v___x_2901_ = lean_box(0);
v_isShared_2902_ = v_isSharedCheck_2911_;
goto v_resetjp_2900_;
}
v_resetjp_2900_:
{
size_t v___x_2903_; size_t v___x_2904_; uint8_t v___x_2905_; 
v___x_2903_ = lean_ptr_addr(v_x_2878_);
v___x_2904_ = lean_ptr_addr(v_key_2898_);
v___x_2905_ = lean_usize_dec_eq(v___x_2903_, v___x_2904_);
if (v___x_2905_ == 0)
{
lean_object* v___x_2906_; lean_object* v___x_2907_; 
lean_del_object(v___x_2901_);
v___x_2906_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_2898_, v_val_2899_, v_x_2878_, v_x_2879_);
v___x_2907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2907_, 0, v___x_2906_);
v___y_2893_ = v___x_2907_;
goto v___jp_2892_;
}
else
{
lean_object* v___x_2909_; 
lean_dec(v_val_2899_);
lean_dec(v_key_2898_);
if (v_isShared_2902_ == 0)
{
lean_ctor_set(v___x_2901_, 1, v_x_2879_);
lean_ctor_set(v___x_2901_, 0, v_x_2878_);
v___x_2909_ = v___x_2901_;
goto v_reusejp_2908_;
}
else
{
lean_object* v_reuseFailAlloc_2910_; 
v_reuseFailAlloc_2910_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2910_, 0, v_x_2878_);
lean_ctor_set(v_reuseFailAlloc_2910_, 1, v_x_2879_);
v___x_2909_ = v_reuseFailAlloc_2910_;
goto v_reusejp_2908_;
}
v_reusejp_2908_:
{
v___y_2893_ = v___x_2909_;
goto v___jp_2892_;
}
}
}
}
case 1:
{
lean_object* v_node_2912_; lean_object* v___x_2914_; uint8_t v_isShared_2915_; uint8_t v_isSharedCheck_2924_; 
v_node_2912_ = lean_ctor_get(v_v_2889_, 0);
v_isSharedCheck_2924_ = !lean_is_exclusive(v_v_2889_);
if (v_isSharedCheck_2924_ == 0)
{
v___x_2914_ = v_v_2889_;
v_isShared_2915_ = v_isSharedCheck_2924_;
goto v_resetjp_2913_;
}
else
{
lean_inc(v_node_2912_);
lean_dec(v_v_2889_);
v___x_2914_ = lean_box(0);
v_isShared_2915_ = v_isSharedCheck_2924_;
goto v_resetjp_2913_;
}
v_resetjp_2913_:
{
size_t v___x_2916_; size_t v___x_2917_; size_t v___x_2918_; size_t v___x_2919_; lean_object* v___x_2920_; lean_object* v___x_2922_; 
v___x_2916_ = ((size_t)5ULL);
v___x_2917_ = lean_usize_shift_right(v_x_2876_, v___x_2916_);
v___x_2918_ = ((size_t)1ULL);
v___x_2919_ = lean_usize_add(v_x_2877_, v___x_2918_);
v___x_2920_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0___redArg(v_node_2912_, v___x_2917_, v___x_2919_, v_x_2878_, v_x_2879_);
if (v_isShared_2915_ == 0)
{
lean_ctor_set(v___x_2914_, 0, v___x_2920_);
v___x_2922_ = v___x_2914_;
goto v_reusejp_2921_;
}
else
{
lean_object* v_reuseFailAlloc_2923_; 
v_reuseFailAlloc_2923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2923_, 0, v___x_2920_);
v___x_2922_ = v_reuseFailAlloc_2923_;
goto v_reusejp_2921_;
}
v_reusejp_2921_:
{
v___y_2893_ = v___x_2922_;
goto v___jp_2892_;
}
}
}
default: 
{
lean_object* v___x_2925_; 
v___x_2925_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2925_, 0, v_x_2878_);
lean_ctor_set(v___x_2925_, 1, v_x_2879_);
v___y_2893_ = v___x_2925_;
goto v___jp_2892_;
}
}
v___jp_2892_:
{
lean_object* v___x_2894_; lean_object* v___x_2896_; 
v___x_2894_ = lean_array_fset(v_xs_x27_2891_, v_j_2883_, v___y_2893_);
lean_dec(v_j_2883_);
if (v_isShared_2888_ == 0)
{
lean_ctor_set(v___x_2887_, 0, v___x_2894_);
v___x_2896_ = v___x_2887_;
goto v_reusejp_2895_;
}
else
{
lean_object* v_reuseFailAlloc_2897_; 
v_reuseFailAlloc_2897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2897_, 0, v___x_2894_);
v___x_2896_ = v_reuseFailAlloc_2897_;
goto v_reusejp_2895_;
}
v_reusejp_2895_:
{
return v___x_2896_;
}
}
}
}
}
else
{
lean_object* v_ks_2928_; lean_object* v_vs_2929_; lean_object* v___x_2931_; uint8_t v_isShared_2932_; uint8_t v_isSharedCheck_2947_; 
v_ks_2928_ = lean_ctor_get(v_x_2875_, 0);
v_vs_2929_ = lean_ctor_get(v_x_2875_, 1);
v_isSharedCheck_2947_ = !lean_is_exclusive(v_x_2875_);
if (v_isSharedCheck_2947_ == 0)
{
v___x_2931_ = v_x_2875_;
v_isShared_2932_ = v_isSharedCheck_2947_;
goto v_resetjp_2930_;
}
else
{
lean_inc(v_vs_2929_);
lean_inc(v_ks_2928_);
lean_dec(v_x_2875_);
v___x_2931_ = lean_box(0);
v_isShared_2932_ = v_isSharedCheck_2947_;
goto v_resetjp_2930_;
}
v_resetjp_2930_:
{
lean_object* v___x_2934_; 
if (v_isShared_2932_ == 0)
{
v___x_2934_ = v___x_2931_;
goto v_reusejp_2933_;
}
else
{
lean_object* v_reuseFailAlloc_2946_; 
v_reuseFailAlloc_2946_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2946_, 0, v_ks_2928_);
lean_ctor_set(v_reuseFailAlloc_2946_, 1, v_vs_2929_);
v___x_2934_ = v_reuseFailAlloc_2946_;
goto v_reusejp_2933_;
}
v_reusejp_2933_:
{
lean_object* v_newNode_2935_; size_t v___x_2936_; uint8_t v___x_2937_; 
v_newNode_2935_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0_spec__1___redArg(v___x_2934_, v_x_2878_, v_x_2879_);
v___x_2936_ = ((size_t)7ULL);
v___x_2937_ = lean_usize_dec_le(v___x_2936_, v_x_2877_);
if (v___x_2937_ == 0)
{
lean_object* v___x_2938_; lean_object* v___x_2939_; uint8_t v___x_2940_; 
v___x_2938_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2935_);
v___x_2939_ = lean_unsigned_to_nat(4u);
v___x_2940_ = lean_nat_dec_lt(v___x_2938_, v___x_2939_);
lean_dec(v___x_2938_);
if (v___x_2940_ == 0)
{
lean_object* v_ks_2941_; lean_object* v_vs_2942_; lean_object* v___x_2943_; lean_object* v___x_2944_; lean_object* v___x_2945_; 
v_ks_2941_ = lean_ctor_get(v_newNode_2935_, 0);
lean_inc_ref(v_ks_2941_);
v_vs_2942_ = lean_ctor_get(v_newNode_2935_, 1);
lean_inc_ref(v_vs_2942_);
lean_dec_ref(v_newNode_2935_);
v___x_2943_ = lean_unsigned_to_nat(0u);
v___x_2944_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg___closed__0);
v___x_2945_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0_spec__2___redArg(v_x_2877_, v_ks_2941_, v_vs_2942_, v___x_2943_, v___x_2944_);
lean_dec_ref(v_vs_2942_);
lean_dec_ref(v_ks_2941_);
return v___x_2945_;
}
else
{
return v_newNode_2935_;
}
}
else
{
return v_newNode_2935_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0_spec__2___redArg(size_t v_depth_2948_, lean_object* v_keys_2949_, lean_object* v_vals_2950_, lean_object* v_i_2951_, lean_object* v_entries_2952_){
_start:
{
lean_object* v___x_2953_; uint8_t v___x_2954_; 
v___x_2953_ = lean_array_get_size(v_keys_2949_);
v___x_2954_ = lean_nat_dec_lt(v_i_2951_, v___x_2953_);
if (v___x_2954_ == 0)
{
lean_dec(v_i_2951_);
return v_entries_2952_;
}
else
{
lean_object* v_k_2955_; lean_object* v_v_2956_; size_t v___x_2957_; size_t v___x_2958_; size_t v___x_2959_; uint64_t v___x_2960_; size_t v_h_2961_; size_t v___x_2962_; lean_object* v___x_2963_; size_t v___x_2964_; size_t v___x_2965_; size_t v___x_2966_; size_t v_h_2967_; lean_object* v___x_2968_; lean_object* v___x_2969_; 
v_k_2955_ = lean_array_fget_borrowed(v_keys_2949_, v_i_2951_);
v_v_2956_ = lean_array_fget_borrowed(v_vals_2950_, v_i_2951_);
v___x_2957_ = lean_ptr_addr(v_k_2955_);
v___x_2958_ = ((size_t)3ULL);
v___x_2959_ = lean_usize_shift_right(v___x_2957_, v___x_2958_);
v___x_2960_ = lean_usize_to_uint64(v___x_2959_);
v_h_2961_ = lean_uint64_to_usize(v___x_2960_);
v___x_2962_ = ((size_t)5ULL);
v___x_2963_ = lean_unsigned_to_nat(1u);
v___x_2964_ = ((size_t)1ULL);
v___x_2965_ = lean_usize_sub(v_depth_2948_, v___x_2964_);
v___x_2966_ = lean_usize_mul(v___x_2962_, v___x_2965_);
v_h_2967_ = lean_usize_shift_right(v_h_2961_, v___x_2966_);
v___x_2968_ = lean_nat_add(v_i_2951_, v___x_2963_);
lean_dec(v_i_2951_);
lean_inc(v_v_2956_);
lean_inc(v_k_2955_);
v___x_2969_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0___redArg(v_entries_2952_, v_h_2967_, v_depth_2948_, v_k_2955_, v_v_2956_);
v_i_2951_ = v___x_2968_;
v_entries_2952_ = v___x_2969_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_2971_, lean_object* v_keys_2972_, lean_object* v_vals_2973_, lean_object* v_i_2974_, lean_object* v_entries_2975_){
_start:
{
size_t v_depth_boxed_2976_; lean_object* v_res_2977_; 
v_depth_boxed_2976_ = lean_unbox_usize(v_depth_2971_);
lean_dec(v_depth_2971_);
v_res_2977_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0_spec__2___redArg(v_depth_boxed_2976_, v_keys_2972_, v_vals_2973_, v_i_2974_, v_entries_2975_);
lean_dec_ref(v_vals_2973_);
lean_dec_ref(v_keys_2972_);
return v_res_2977_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0___redArg___boxed(lean_object* v_x_2978_, lean_object* v_x_2979_, lean_object* v_x_2980_, lean_object* v_x_2981_, lean_object* v_x_2982_){
_start:
{
size_t v_x_151195__boxed_2983_; size_t v_x_151196__boxed_2984_; lean_object* v_res_2985_; 
v_x_151195__boxed_2983_ = lean_unbox_usize(v_x_2979_);
lean_dec(v_x_2979_);
v_x_151196__boxed_2984_ = lean_unbox_usize(v_x_2980_);
lean_dec(v_x_2980_);
v_res_2985_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0___redArg(v_x_2978_, v_x_151195__boxed_2983_, v_x_151196__boxed_2984_, v_x_2981_, v_x_2982_);
return v_res_2985_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0___redArg(lean_object* v_x_2986_, lean_object* v_x_2987_, lean_object* v_x_2988_){
_start:
{
size_t v___x_2989_; size_t v___x_2990_; size_t v___x_2991_; uint64_t v___x_2992_; size_t v___x_2993_; size_t v___x_2994_; lean_object* v___x_2995_; 
v___x_2989_ = lean_ptr_addr(v_x_2987_);
v___x_2990_ = ((size_t)3ULL);
v___x_2991_ = lean_usize_shift_right(v___x_2989_, v___x_2990_);
v___x_2992_ = lean_usize_to_uint64(v___x_2991_);
v___x_2993_ = lean_uint64_to_usize(v___x_2992_);
v___x_2994_ = ((size_t)1ULL);
v___x_2995_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0___redArg(v_x_2986_, v___x_2993_, v___x_2994_, v_x_2987_, v_x_2988_);
return v___x_2995_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_internalize___lam__0(lean_object* v_e_2996_, lean_object* v_val_2997_, lean_object* v_s_2998_){
_start:
{
lean_object* v_toRing_2999_; lean_object* v_invFn_x3f_3000_; lean_object* v_semiringId_x3f_3001_; lean_object* v_commSemiringInst_3002_; lean_object* v_commRingInst_3003_; lean_object* v_noZeroDivInst_x3f_3004_; lean_object* v_fieldInst_x3f_3005_; lean_object* v_powIdentityInst_x3f_3006_; lean_object* v_denoteEntries_3007_; lean_object* v_nextId_3008_; lean_object* v_steps_3009_; lean_object* v_queue_3010_; lean_object* v_basis_3011_; lean_object* v_diseqs_3012_; uint8_t v_recheck_3013_; lean_object* v_invSet_3014_; lean_object* v_powIdentityVarCount_3015_; lean_object* v_numEq0_x3f_3016_; uint8_t v_numEq0Updated_3017_; lean_object* v___x_3019_; uint8_t v_isShared_3020_; uint8_t v_isSharedCheck_3051_; 
v_toRing_2999_ = lean_ctor_get(v_s_2998_, 0);
v_invFn_x3f_3000_ = lean_ctor_get(v_s_2998_, 1);
v_semiringId_x3f_3001_ = lean_ctor_get(v_s_2998_, 2);
v_commSemiringInst_3002_ = lean_ctor_get(v_s_2998_, 3);
v_commRingInst_3003_ = lean_ctor_get(v_s_2998_, 4);
v_noZeroDivInst_x3f_3004_ = lean_ctor_get(v_s_2998_, 5);
v_fieldInst_x3f_3005_ = lean_ctor_get(v_s_2998_, 6);
v_powIdentityInst_x3f_3006_ = lean_ctor_get(v_s_2998_, 7);
v_denoteEntries_3007_ = lean_ctor_get(v_s_2998_, 8);
v_nextId_3008_ = lean_ctor_get(v_s_2998_, 9);
v_steps_3009_ = lean_ctor_get(v_s_2998_, 10);
v_queue_3010_ = lean_ctor_get(v_s_2998_, 11);
v_basis_3011_ = lean_ctor_get(v_s_2998_, 12);
v_diseqs_3012_ = lean_ctor_get(v_s_2998_, 13);
v_recheck_3013_ = lean_ctor_get_uint8(v_s_2998_, sizeof(void*)*17);
v_invSet_3014_ = lean_ctor_get(v_s_2998_, 14);
v_powIdentityVarCount_3015_ = lean_ctor_get(v_s_2998_, 15);
v_numEq0_x3f_3016_ = lean_ctor_get(v_s_2998_, 16);
v_numEq0Updated_3017_ = lean_ctor_get_uint8(v_s_2998_, sizeof(void*)*17 + 1);
v_isSharedCheck_3051_ = !lean_is_exclusive(v_s_2998_);
if (v_isSharedCheck_3051_ == 0)
{
v___x_3019_ = v_s_2998_;
v_isShared_3020_ = v_isSharedCheck_3051_;
goto v_resetjp_3018_;
}
else
{
lean_inc(v_numEq0_x3f_3016_);
lean_inc(v_powIdentityVarCount_3015_);
lean_inc(v_invSet_3014_);
lean_inc(v_diseqs_3012_);
lean_inc(v_basis_3011_);
lean_inc(v_queue_3010_);
lean_inc(v_steps_3009_);
lean_inc(v_nextId_3008_);
lean_inc(v_denoteEntries_3007_);
lean_inc(v_powIdentityInst_x3f_3006_);
lean_inc(v_fieldInst_x3f_3005_);
lean_inc(v_noZeroDivInst_x3f_3004_);
lean_inc(v_commRingInst_3003_);
lean_inc(v_commSemiringInst_3002_);
lean_inc(v_semiringId_x3f_3001_);
lean_inc(v_invFn_x3f_3000_);
lean_inc(v_toRing_2999_);
lean_dec(v_s_2998_);
v___x_3019_ = lean_box(0);
v_isShared_3020_ = v_isSharedCheck_3051_;
goto v_resetjp_3018_;
}
v_resetjp_3018_:
{
lean_object* v_id_3021_; lean_object* v_type_3022_; lean_object* v_u_3023_; lean_object* v_ringInst_3024_; lean_object* v_semiringInst_3025_; lean_object* v_charInst_x3f_3026_; lean_object* v_addFn_x3f_3027_; lean_object* v_mulFn_x3f_3028_; lean_object* v_subFn_x3f_3029_; lean_object* v_negFn_x3f_3030_; lean_object* v_powFn_x3f_3031_; lean_object* v_intCastFn_x3f_3032_; lean_object* v_natCastFn_x3f_3033_; lean_object* v_one_x3f_3034_; lean_object* v_vars_3035_; lean_object* v_varMap_3036_; lean_object* v_denote_3037_; lean_object* v___x_3039_; uint8_t v_isShared_3040_; uint8_t v_isSharedCheck_3050_; 
v_id_3021_ = lean_ctor_get(v_toRing_2999_, 0);
v_type_3022_ = lean_ctor_get(v_toRing_2999_, 1);
v_u_3023_ = lean_ctor_get(v_toRing_2999_, 2);
v_ringInst_3024_ = lean_ctor_get(v_toRing_2999_, 3);
v_semiringInst_3025_ = lean_ctor_get(v_toRing_2999_, 4);
v_charInst_x3f_3026_ = lean_ctor_get(v_toRing_2999_, 5);
v_addFn_x3f_3027_ = lean_ctor_get(v_toRing_2999_, 6);
v_mulFn_x3f_3028_ = lean_ctor_get(v_toRing_2999_, 7);
v_subFn_x3f_3029_ = lean_ctor_get(v_toRing_2999_, 8);
v_negFn_x3f_3030_ = lean_ctor_get(v_toRing_2999_, 9);
v_powFn_x3f_3031_ = lean_ctor_get(v_toRing_2999_, 10);
v_intCastFn_x3f_3032_ = lean_ctor_get(v_toRing_2999_, 11);
v_natCastFn_x3f_3033_ = lean_ctor_get(v_toRing_2999_, 12);
v_one_x3f_3034_ = lean_ctor_get(v_toRing_2999_, 13);
v_vars_3035_ = lean_ctor_get(v_toRing_2999_, 14);
v_varMap_3036_ = lean_ctor_get(v_toRing_2999_, 15);
v_denote_3037_ = lean_ctor_get(v_toRing_2999_, 16);
v_isSharedCheck_3050_ = !lean_is_exclusive(v_toRing_2999_);
if (v_isSharedCheck_3050_ == 0)
{
v___x_3039_ = v_toRing_2999_;
v_isShared_3040_ = v_isSharedCheck_3050_;
goto v_resetjp_3038_;
}
else
{
lean_inc(v_denote_3037_);
lean_inc(v_varMap_3036_);
lean_inc(v_vars_3035_);
lean_inc(v_one_x3f_3034_);
lean_inc(v_natCastFn_x3f_3033_);
lean_inc(v_intCastFn_x3f_3032_);
lean_inc(v_powFn_x3f_3031_);
lean_inc(v_negFn_x3f_3030_);
lean_inc(v_subFn_x3f_3029_);
lean_inc(v_mulFn_x3f_3028_);
lean_inc(v_addFn_x3f_3027_);
lean_inc(v_charInst_x3f_3026_);
lean_inc(v_semiringInst_3025_);
lean_inc(v_ringInst_3024_);
lean_inc(v_u_3023_);
lean_inc(v_type_3022_);
lean_inc(v_id_3021_);
lean_dec(v_toRing_2999_);
v___x_3039_ = lean_box(0);
v_isShared_3040_ = v_isSharedCheck_3050_;
goto v_resetjp_3038_;
}
v_resetjp_3038_:
{
lean_object* v___x_3041_; lean_object* v___x_3043_; 
lean_inc_ref(v_val_2997_);
lean_inc_ref(v_e_2996_);
v___x_3041_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0___redArg(v_denote_3037_, v_e_2996_, v_val_2997_);
if (v_isShared_3040_ == 0)
{
lean_ctor_set(v___x_3039_, 16, v___x_3041_);
v___x_3043_ = v___x_3039_;
goto v_reusejp_3042_;
}
else
{
lean_object* v_reuseFailAlloc_3049_; 
v_reuseFailAlloc_3049_ = lean_alloc_ctor(0, 17, 0);
lean_ctor_set(v_reuseFailAlloc_3049_, 0, v_id_3021_);
lean_ctor_set(v_reuseFailAlloc_3049_, 1, v_type_3022_);
lean_ctor_set(v_reuseFailAlloc_3049_, 2, v_u_3023_);
lean_ctor_set(v_reuseFailAlloc_3049_, 3, v_ringInst_3024_);
lean_ctor_set(v_reuseFailAlloc_3049_, 4, v_semiringInst_3025_);
lean_ctor_set(v_reuseFailAlloc_3049_, 5, v_charInst_x3f_3026_);
lean_ctor_set(v_reuseFailAlloc_3049_, 6, v_addFn_x3f_3027_);
lean_ctor_set(v_reuseFailAlloc_3049_, 7, v_mulFn_x3f_3028_);
lean_ctor_set(v_reuseFailAlloc_3049_, 8, v_subFn_x3f_3029_);
lean_ctor_set(v_reuseFailAlloc_3049_, 9, v_negFn_x3f_3030_);
lean_ctor_set(v_reuseFailAlloc_3049_, 10, v_powFn_x3f_3031_);
lean_ctor_set(v_reuseFailAlloc_3049_, 11, v_intCastFn_x3f_3032_);
lean_ctor_set(v_reuseFailAlloc_3049_, 12, v_natCastFn_x3f_3033_);
lean_ctor_set(v_reuseFailAlloc_3049_, 13, v_one_x3f_3034_);
lean_ctor_set(v_reuseFailAlloc_3049_, 14, v_vars_3035_);
lean_ctor_set(v_reuseFailAlloc_3049_, 15, v_varMap_3036_);
lean_ctor_set(v_reuseFailAlloc_3049_, 16, v___x_3041_);
v___x_3043_ = v_reuseFailAlloc_3049_;
goto v_reusejp_3042_;
}
v_reusejp_3042_:
{
lean_object* v___x_3044_; lean_object* v___x_3045_; lean_object* v___x_3047_; 
v___x_3044_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3044_, 0, v_e_2996_);
lean_ctor_set(v___x_3044_, 1, v_val_2997_);
v___x_3045_ = l_Lean_PersistentArray_push___redArg(v_denoteEntries_3007_, v___x_3044_);
if (v_isShared_3020_ == 0)
{
lean_ctor_set(v___x_3019_, 8, v___x_3045_);
lean_ctor_set(v___x_3019_, 0, v___x_3043_);
v___x_3047_ = v___x_3019_;
goto v_reusejp_3046_;
}
else
{
lean_object* v_reuseFailAlloc_3048_; 
v_reuseFailAlloc_3048_ = lean_alloc_ctor(0, 17, 2);
lean_ctor_set(v_reuseFailAlloc_3048_, 0, v___x_3043_);
lean_ctor_set(v_reuseFailAlloc_3048_, 1, v_invFn_x3f_3000_);
lean_ctor_set(v_reuseFailAlloc_3048_, 2, v_semiringId_x3f_3001_);
lean_ctor_set(v_reuseFailAlloc_3048_, 3, v_commSemiringInst_3002_);
lean_ctor_set(v_reuseFailAlloc_3048_, 4, v_commRingInst_3003_);
lean_ctor_set(v_reuseFailAlloc_3048_, 5, v_noZeroDivInst_x3f_3004_);
lean_ctor_set(v_reuseFailAlloc_3048_, 6, v_fieldInst_x3f_3005_);
lean_ctor_set(v_reuseFailAlloc_3048_, 7, v_powIdentityInst_x3f_3006_);
lean_ctor_set(v_reuseFailAlloc_3048_, 8, v___x_3045_);
lean_ctor_set(v_reuseFailAlloc_3048_, 9, v_nextId_3008_);
lean_ctor_set(v_reuseFailAlloc_3048_, 10, v_steps_3009_);
lean_ctor_set(v_reuseFailAlloc_3048_, 11, v_queue_3010_);
lean_ctor_set(v_reuseFailAlloc_3048_, 12, v_basis_3011_);
lean_ctor_set(v_reuseFailAlloc_3048_, 13, v_diseqs_3012_);
lean_ctor_set(v_reuseFailAlloc_3048_, 14, v_invSet_3014_);
lean_ctor_set(v_reuseFailAlloc_3048_, 15, v_powIdentityVarCount_3015_);
lean_ctor_set(v_reuseFailAlloc_3048_, 16, v_numEq0_x3f_3016_);
lean_ctor_set_uint8(v_reuseFailAlloc_3048_, sizeof(void*)*17, v_recheck_3013_);
lean_ctor_set_uint8(v_reuseFailAlloc_3048_, sizeof(void*)*17 + 1, v_numEq0Updated_3017_);
v___x_3047_ = v_reuseFailAlloc_3048_;
goto v_reusejp_3046_;
}
v_reusejp_3046_:
{
return v___x_3047_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_internalize___lam__1(lean_object* v___y_3052_, lean_object* v_e_3053_, lean_object* v_val_3054_, lean_object* v_s_3055_){
_start:
{
lean_object* v_rings_3056_; lean_object* v_typeIdOf_3057_; lean_object* v_exprToRingId_3058_; lean_object* v_semirings_3059_; lean_object* v_stypeIdOf_3060_; lean_object* v_exprToSemiringId_3061_; lean_object* v_ncRings_3062_; lean_object* v_exprToNCRingId_3063_; lean_object* v_nctypeIdOf_3064_; lean_object* v_ncSemirings_3065_; lean_object* v_exprToNCSemiringId_3066_; lean_object* v_ncstypeIdOf_3067_; lean_object* v_steps_3068_; uint8_t v_reportedMaxDegreeIssue_3069_; lean_object* v___x_3070_; uint8_t v___x_3071_; 
v_rings_3056_ = lean_ctor_get(v_s_3055_, 0);
v_typeIdOf_3057_ = lean_ctor_get(v_s_3055_, 1);
v_exprToRingId_3058_ = lean_ctor_get(v_s_3055_, 2);
v_semirings_3059_ = lean_ctor_get(v_s_3055_, 3);
v_stypeIdOf_3060_ = lean_ctor_get(v_s_3055_, 4);
v_exprToSemiringId_3061_ = lean_ctor_get(v_s_3055_, 5);
v_ncRings_3062_ = lean_ctor_get(v_s_3055_, 6);
v_exprToNCRingId_3063_ = lean_ctor_get(v_s_3055_, 7);
v_nctypeIdOf_3064_ = lean_ctor_get(v_s_3055_, 8);
v_ncSemirings_3065_ = lean_ctor_get(v_s_3055_, 9);
v_exprToNCSemiringId_3066_ = lean_ctor_get(v_s_3055_, 10);
v_ncstypeIdOf_3067_ = lean_ctor_get(v_s_3055_, 11);
v_steps_3068_ = lean_ctor_get(v_s_3055_, 12);
v_reportedMaxDegreeIssue_3069_ = lean_ctor_get_uint8(v_s_3055_, sizeof(void*)*13);
v___x_3070_ = lean_array_get_size(v_semirings_3059_);
v___x_3071_ = lean_nat_dec_lt(v___y_3052_, v___x_3070_);
if (v___x_3071_ == 0)
{
lean_dec_ref(v_val_3054_);
lean_dec_ref(v_e_3053_);
return v_s_3055_;
}
else
{
lean_object* v___x_3073_; uint8_t v_isShared_3074_; uint8_t v_isSharedCheck_3113_; 
lean_inc(v_steps_3068_);
lean_inc_ref(v_ncstypeIdOf_3067_);
lean_inc_ref(v_exprToNCSemiringId_3066_);
lean_inc_ref(v_ncSemirings_3065_);
lean_inc_ref(v_nctypeIdOf_3064_);
lean_inc_ref(v_exprToNCRingId_3063_);
lean_inc_ref(v_ncRings_3062_);
lean_inc_ref(v_exprToSemiringId_3061_);
lean_inc_ref(v_stypeIdOf_3060_);
lean_inc_ref(v_semirings_3059_);
lean_inc_ref(v_exprToRingId_3058_);
lean_inc_ref(v_typeIdOf_3057_);
lean_inc_ref(v_rings_3056_);
v_isSharedCheck_3113_ = !lean_is_exclusive(v_s_3055_);
if (v_isSharedCheck_3113_ == 0)
{
lean_object* v_unused_3114_; lean_object* v_unused_3115_; lean_object* v_unused_3116_; lean_object* v_unused_3117_; lean_object* v_unused_3118_; lean_object* v_unused_3119_; lean_object* v_unused_3120_; lean_object* v_unused_3121_; lean_object* v_unused_3122_; lean_object* v_unused_3123_; lean_object* v_unused_3124_; lean_object* v_unused_3125_; lean_object* v_unused_3126_; 
v_unused_3114_ = lean_ctor_get(v_s_3055_, 12);
lean_dec(v_unused_3114_);
v_unused_3115_ = lean_ctor_get(v_s_3055_, 11);
lean_dec(v_unused_3115_);
v_unused_3116_ = lean_ctor_get(v_s_3055_, 10);
lean_dec(v_unused_3116_);
v_unused_3117_ = lean_ctor_get(v_s_3055_, 9);
lean_dec(v_unused_3117_);
v_unused_3118_ = lean_ctor_get(v_s_3055_, 8);
lean_dec(v_unused_3118_);
v_unused_3119_ = lean_ctor_get(v_s_3055_, 7);
lean_dec(v_unused_3119_);
v_unused_3120_ = lean_ctor_get(v_s_3055_, 6);
lean_dec(v_unused_3120_);
v_unused_3121_ = lean_ctor_get(v_s_3055_, 5);
lean_dec(v_unused_3121_);
v_unused_3122_ = lean_ctor_get(v_s_3055_, 4);
lean_dec(v_unused_3122_);
v_unused_3123_ = lean_ctor_get(v_s_3055_, 3);
lean_dec(v_unused_3123_);
v_unused_3124_ = lean_ctor_get(v_s_3055_, 2);
lean_dec(v_unused_3124_);
v_unused_3125_ = lean_ctor_get(v_s_3055_, 1);
lean_dec(v_unused_3125_);
v_unused_3126_ = lean_ctor_get(v_s_3055_, 0);
lean_dec(v_unused_3126_);
v___x_3073_ = v_s_3055_;
v_isShared_3074_ = v_isSharedCheck_3113_;
goto v_resetjp_3072_;
}
else
{
lean_dec(v_s_3055_);
v___x_3073_ = lean_box(0);
v_isShared_3074_ = v_isSharedCheck_3113_;
goto v_resetjp_3072_;
}
v_resetjp_3072_:
{
lean_object* v_v_3075_; lean_object* v_toSemiring_3076_; lean_object* v_ringId_3077_; lean_object* v_commSemiringInst_3078_; lean_object* v_addRightCancelInst_x3f_3079_; lean_object* v_toQFn_x3f_3080_; lean_object* v___x_3082_; uint8_t v_isShared_3083_; uint8_t v_isSharedCheck_3112_; 
v_v_3075_ = lean_array_fget(v_semirings_3059_, v___y_3052_);
v_toSemiring_3076_ = lean_ctor_get(v_v_3075_, 0);
v_ringId_3077_ = lean_ctor_get(v_v_3075_, 1);
v_commSemiringInst_3078_ = lean_ctor_get(v_v_3075_, 2);
v_addRightCancelInst_x3f_3079_ = lean_ctor_get(v_v_3075_, 3);
v_toQFn_x3f_3080_ = lean_ctor_get(v_v_3075_, 4);
v_isSharedCheck_3112_ = !lean_is_exclusive(v_v_3075_);
if (v_isSharedCheck_3112_ == 0)
{
v___x_3082_ = v_v_3075_;
v_isShared_3083_ = v_isSharedCheck_3112_;
goto v_resetjp_3081_;
}
else
{
lean_inc(v_toQFn_x3f_3080_);
lean_inc(v_addRightCancelInst_x3f_3079_);
lean_inc(v_commSemiringInst_3078_);
lean_inc(v_ringId_3077_);
lean_inc(v_toSemiring_3076_);
lean_dec(v_v_3075_);
v___x_3082_ = lean_box(0);
v_isShared_3083_ = v_isSharedCheck_3112_;
goto v_resetjp_3081_;
}
v_resetjp_3081_:
{
lean_object* v_id_3084_; lean_object* v_type_3085_; lean_object* v_u_3086_; lean_object* v_semiringInst_3087_; lean_object* v_addFn_x3f_3088_; lean_object* v_mulFn_x3f_3089_; lean_object* v_powFn_x3f_3090_; lean_object* v_natCastFn_x3f_3091_; lean_object* v_denote_3092_; lean_object* v_vars_3093_; lean_object* v_varMap_3094_; lean_object* v___x_3096_; uint8_t v_isShared_3097_; uint8_t v_isSharedCheck_3111_; 
v_id_3084_ = lean_ctor_get(v_toSemiring_3076_, 0);
v_type_3085_ = lean_ctor_get(v_toSemiring_3076_, 1);
v_u_3086_ = lean_ctor_get(v_toSemiring_3076_, 2);
v_semiringInst_3087_ = lean_ctor_get(v_toSemiring_3076_, 3);
v_addFn_x3f_3088_ = lean_ctor_get(v_toSemiring_3076_, 4);
v_mulFn_x3f_3089_ = lean_ctor_get(v_toSemiring_3076_, 5);
v_powFn_x3f_3090_ = lean_ctor_get(v_toSemiring_3076_, 6);
v_natCastFn_x3f_3091_ = lean_ctor_get(v_toSemiring_3076_, 7);
v_denote_3092_ = lean_ctor_get(v_toSemiring_3076_, 8);
v_vars_3093_ = lean_ctor_get(v_toSemiring_3076_, 9);
v_varMap_3094_ = lean_ctor_get(v_toSemiring_3076_, 10);
v_isSharedCheck_3111_ = !lean_is_exclusive(v_toSemiring_3076_);
if (v_isSharedCheck_3111_ == 0)
{
v___x_3096_ = v_toSemiring_3076_;
v_isShared_3097_ = v_isSharedCheck_3111_;
goto v_resetjp_3095_;
}
else
{
lean_inc(v_varMap_3094_);
lean_inc(v_vars_3093_);
lean_inc(v_denote_3092_);
lean_inc(v_natCastFn_x3f_3091_);
lean_inc(v_powFn_x3f_3090_);
lean_inc(v_mulFn_x3f_3089_);
lean_inc(v_addFn_x3f_3088_);
lean_inc(v_semiringInst_3087_);
lean_inc(v_u_3086_);
lean_inc(v_type_3085_);
lean_inc(v_id_3084_);
lean_dec(v_toSemiring_3076_);
v___x_3096_ = lean_box(0);
v_isShared_3097_ = v_isSharedCheck_3111_;
goto v_resetjp_3095_;
}
v_resetjp_3095_:
{
lean_object* v___x_3098_; lean_object* v_xs_x27_3099_; lean_object* v___x_3100_; lean_object* v___x_3102_; 
v___x_3098_ = lean_box(0);
v_xs_x27_3099_ = lean_array_fset(v_semirings_3059_, v___y_3052_, v___x_3098_);
v___x_3100_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0___redArg(v_denote_3092_, v_e_3053_, v_val_3054_);
if (v_isShared_3097_ == 0)
{
lean_ctor_set(v___x_3096_, 8, v___x_3100_);
v___x_3102_ = v___x_3096_;
goto v_reusejp_3101_;
}
else
{
lean_object* v_reuseFailAlloc_3110_; 
v_reuseFailAlloc_3110_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_3110_, 0, v_id_3084_);
lean_ctor_set(v_reuseFailAlloc_3110_, 1, v_type_3085_);
lean_ctor_set(v_reuseFailAlloc_3110_, 2, v_u_3086_);
lean_ctor_set(v_reuseFailAlloc_3110_, 3, v_semiringInst_3087_);
lean_ctor_set(v_reuseFailAlloc_3110_, 4, v_addFn_x3f_3088_);
lean_ctor_set(v_reuseFailAlloc_3110_, 5, v_mulFn_x3f_3089_);
lean_ctor_set(v_reuseFailAlloc_3110_, 6, v_powFn_x3f_3090_);
lean_ctor_set(v_reuseFailAlloc_3110_, 7, v_natCastFn_x3f_3091_);
lean_ctor_set(v_reuseFailAlloc_3110_, 8, v___x_3100_);
lean_ctor_set(v_reuseFailAlloc_3110_, 9, v_vars_3093_);
lean_ctor_set(v_reuseFailAlloc_3110_, 10, v_varMap_3094_);
v___x_3102_ = v_reuseFailAlloc_3110_;
goto v_reusejp_3101_;
}
v_reusejp_3101_:
{
lean_object* v___x_3104_; 
if (v_isShared_3083_ == 0)
{
lean_ctor_set(v___x_3082_, 0, v___x_3102_);
v___x_3104_ = v___x_3082_;
goto v_reusejp_3103_;
}
else
{
lean_object* v_reuseFailAlloc_3109_; 
v_reuseFailAlloc_3109_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3109_, 0, v___x_3102_);
lean_ctor_set(v_reuseFailAlloc_3109_, 1, v_ringId_3077_);
lean_ctor_set(v_reuseFailAlloc_3109_, 2, v_commSemiringInst_3078_);
lean_ctor_set(v_reuseFailAlloc_3109_, 3, v_addRightCancelInst_x3f_3079_);
lean_ctor_set(v_reuseFailAlloc_3109_, 4, v_toQFn_x3f_3080_);
v___x_3104_ = v_reuseFailAlloc_3109_;
goto v_reusejp_3103_;
}
v_reusejp_3103_:
{
lean_object* v___x_3105_; lean_object* v___x_3107_; 
v___x_3105_ = lean_array_fset(v_xs_x27_3099_, v___y_3052_, v___x_3104_);
if (v_isShared_3074_ == 0)
{
lean_ctor_set(v___x_3073_, 3, v___x_3105_);
v___x_3107_ = v___x_3073_;
goto v_reusejp_3106_;
}
else
{
lean_object* v_reuseFailAlloc_3108_; 
v_reuseFailAlloc_3108_ = lean_alloc_ctor(0, 13, 1);
lean_ctor_set(v_reuseFailAlloc_3108_, 0, v_rings_3056_);
lean_ctor_set(v_reuseFailAlloc_3108_, 1, v_typeIdOf_3057_);
lean_ctor_set(v_reuseFailAlloc_3108_, 2, v_exprToRingId_3058_);
lean_ctor_set(v_reuseFailAlloc_3108_, 3, v___x_3105_);
lean_ctor_set(v_reuseFailAlloc_3108_, 4, v_stypeIdOf_3060_);
lean_ctor_set(v_reuseFailAlloc_3108_, 5, v_exprToSemiringId_3061_);
lean_ctor_set(v_reuseFailAlloc_3108_, 6, v_ncRings_3062_);
lean_ctor_set(v_reuseFailAlloc_3108_, 7, v_exprToNCRingId_3063_);
lean_ctor_set(v_reuseFailAlloc_3108_, 8, v_nctypeIdOf_3064_);
lean_ctor_set(v_reuseFailAlloc_3108_, 9, v_ncSemirings_3065_);
lean_ctor_set(v_reuseFailAlloc_3108_, 10, v_exprToNCSemiringId_3066_);
lean_ctor_set(v_reuseFailAlloc_3108_, 11, v_ncstypeIdOf_3067_);
lean_ctor_set(v_reuseFailAlloc_3108_, 12, v_steps_3068_);
lean_ctor_set_uint8(v_reuseFailAlloc_3108_, sizeof(void*)*13, v_reportedMaxDegreeIssue_3069_);
v___x_3107_ = v_reuseFailAlloc_3108_;
goto v_reusejp_3106_;
}
v_reusejp_3106_:
{
return v___x_3107_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_internalize___lam__1___boxed(lean_object* v___y_3127_, lean_object* v_e_3128_, lean_object* v_val_3129_, lean_object* v_s_3130_){
_start:
{
lean_object* v_res_3131_; 
v_res_3131_ = l_Lean_Meta_Grind_Arith_CommRing_internalize___lam__1(v___y_3127_, v_e_3128_, v_val_3129_, v_s_3130_);
lean_dec(v___y_3127_);
return v_res_3131_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_internalize___lam__2(lean_object* v_e_3132_, lean_object* v_val_3133_, lean_object* v_s_3134_){
_start:
{
lean_object* v_id_3135_; lean_object* v_type_3136_; lean_object* v_u_3137_; lean_object* v_ringInst_3138_; lean_object* v_semiringInst_3139_; lean_object* v_charInst_x3f_3140_; lean_object* v_addFn_x3f_3141_; lean_object* v_mulFn_x3f_3142_; lean_object* v_subFn_x3f_3143_; lean_object* v_negFn_x3f_3144_; lean_object* v_powFn_x3f_3145_; lean_object* v_intCastFn_x3f_3146_; lean_object* v_natCastFn_x3f_3147_; lean_object* v_one_x3f_3148_; lean_object* v_vars_3149_; lean_object* v_varMap_3150_; lean_object* v_denote_3151_; lean_object* v___x_3153_; uint8_t v_isShared_3154_; uint8_t v_isSharedCheck_3159_; 
v_id_3135_ = lean_ctor_get(v_s_3134_, 0);
v_type_3136_ = lean_ctor_get(v_s_3134_, 1);
v_u_3137_ = lean_ctor_get(v_s_3134_, 2);
v_ringInst_3138_ = lean_ctor_get(v_s_3134_, 3);
v_semiringInst_3139_ = lean_ctor_get(v_s_3134_, 4);
v_charInst_x3f_3140_ = lean_ctor_get(v_s_3134_, 5);
v_addFn_x3f_3141_ = lean_ctor_get(v_s_3134_, 6);
v_mulFn_x3f_3142_ = lean_ctor_get(v_s_3134_, 7);
v_subFn_x3f_3143_ = lean_ctor_get(v_s_3134_, 8);
v_negFn_x3f_3144_ = lean_ctor_get(v_s_3134_, 9);
v_powFn_x3f_3145_ = lean_ctor_get(v_s_3134_, 10);
v_intCastFn_x3f_3146_ = lean_ctor_get(v_s_3134_, 11);
v_natCastFn_x3f_3147_ = lean_ctor_get(v_s_3134_, 12);
v_one_x3f_3148_ = lean_ctor_get(v_s_3134_, 13);
v_vars_3149_ = lean_ctor_get(v_s_3134_, 14);
v_varMap_3150_ = lean_ctor_get(v_s_3134_, 15);
v_denote_3151_ = lean_ctor_get(v_s_3134_, 16);
v_isSharedCheck_3159_ = !lean_is_exclusive(v_s_3134_);
if (v_isSharedCheck_3159_ == 0)
{
v___x_3153_ = v_s_3134_;
v_isShared_3154_ = v_isSharedCheck_3159_;
goto v_resetjp_3152_;
}
else
{
lean_inc(v_denote_3151_);
lean_inc(v_varMap_3150_);
lean_inc(v_vars_3149_);
lean_inc(v_one_x3f_3148_);
lean_inc(v_natCastFn_x3f_3147_);
lean_inc(v_intCastFn_x3f_3146_);
lean_inc(v_powFn_x3f_3145_);
lean_inc(v_negFn_x3f_3144_);
lean_inc(v_subFn_x3f_3143_);
lean_inc(v_mulFn_x3f_3142_);
lean_inc(v_addFn_x3f_3141_);
lean_inc(v_charInst_x3f_3140_);
lean_inc(v_semiringInst_3139_);
lean_inc(v_ringInst_3138_);
lean_inc(v_u_3137_);
lean_inc(v_type_3136_);
lean_inc(v_id_3135_);
lean_dec(v_s_3134_);
v___x_3153_ = lean_box(0);
v_isShared_3154_ = v_isSharedCheck_3159_;
goto v_resetjp_3152_;
}
v_resetjp_3152_:
{
lean_object* v___x_3155_; lean_object* v___x_3157_; 
v___x_3155_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0___redArg(v_denote_3151_, v_e_3132_, v_val_3133_);
if (v_isShared_3154_ == 0)
{
lean_ctor_set(v___x_3153_, 16, v___x_3155_);
v___x_3157_ = v___x_3153_;
goto v_reusejp_3156_;
}
else
{
lean_object* v_reuseFailAlloc_3158_; 
v_reuseFailAlloc_3158_ = lean_alloc_ctor(0, 17, 0);
lean_ctor_set(v_reuseFailAlloc_3158_, 0, v_id_3135_);
lean_ctor_set(v_reuseFailAlloc_3158_, 1, v_type_3136_);
lean_ctor_set(v_reuseFailAlloc_3158_, 2, v_u_3137_);
lean_ctor_set(v_reuseFailAlloc_3158_, 3, v_ringInst_3138_);
lean_ctor_set(v_reuseFailAlloc_3158_, 4, v_semiringInst_3139_);
lean_ctor_set(v_reuseFailAlloc_3158_, 5, v_charInst_x3f_3140_);
lean_ctor_set(v_reuseFailAlloc_3158_, 6, v_addFn_x3f_3141_);
lean_ctor_set(v_reuseFailAlloc_3158_, 7, v_mulFn_x3f_3142_);
lean_ctor_set(v_reuseFailAlloc_3158_, 8, v_subFn_x3f_3143_);
lean_ctor_set(v_reuseFailAlloc_3158_, 9, v_negFn_x3f_3144_);
lean_ctor_set(v_reuseFailAlloc_3158_, 10, v_powFn_x3f_3145_);
lean_ctor_set(v_reuseFailAlloc_3158_, 11, v_intCastFn_x3f_3146_);
lean_ctor_set(v_reuseFailAlloc_3158_, 12, v_natCastFn_x3f_3147_);
lean_ctor_set(v_reuseFailAlloc_3158_, 13, v_one_x3f_3148_);
lean_ctor_set(v_reuseFailAlloc_3158_, 14, v_vars_3149_);
lean_ctor_set(v_reuseFailAlloc_3158_, 15, v_varMap_3150_);
lean_ctor_set(v_reuseFailAlloc_3158_, 16, v___x_3155_);
v___x_3157_ = v_reuseFailAlloc_3158_;
goto v_reusejp_3156_;
}
v_reusejp_3156_:
{
return v___x_3157_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_internalize___lam__3(lean_object* v_e_3160_, lean_object* v_val_3161_, lean_object* v_s_3162_){
_start:
{
lean_object* v_id_3163_; lean_object* v_type_3164_; lean_object* v_u_3165_; lean_object* v_semiringInst_3166_; lean_object* v_addFn_x3f_3167_; lean_object* v_mulFn_x3f_3168_; lean_object* v_powFn_x3f_3169_; lean_object* v_natCastFn_x3f_3170_; lean_object* v_denote_3171_; lean_object* v_vars_3172_; lean_object* v_varMap_3173_; lean_object* v___x_3175_; uint8_t v_isShared_3176_; uint8_t v_isSharedCheck_3181_; 
v_id_3163_ = lean_ctor_get(v_s_3162_, 0);
v_type_3164_ = lean_ctor_get(v_s_3162_, 1);
v_u_3165_ = lean_ctor_get(v_s_3162_, 2);
v_semiringInst_3166_ = lean_ctor_get(v_s_3162_, 3);
v_addFn_x3f_3167_ = lean_ctor_get(v_s_3162_, 4);
v_mulFn_x3f_3168_ = lean_ctor_get(v_s_3162_, 5);
v_powFn_x3f_3169_ = lean_ctor_get(v_s_3162_, 6);
v_natCastFn_x3f_3170_ = lean_ctor_get(v_s_3162_, 7);
v_denote_3171_ = lean_ctor_get(v_s_3162_, 8);
v_vars_3172_ = lean_ctor_get(v_s_3162_, 9);
v_varMap_3173_ = lean_ctor_get(v_s_3162_, 10);
v_isSharedCheck_3181_ = !lean_is_exclusive(v_s_3162_);
if (v_isSharedCheck_3181_ == 0)
{
v___x_3175_ = v_s_3162_;
v_isShared_3176_ = v_isSharedCheck_3181_;
goto v_resetjp_3174_;
}
else
{
lean_inc(v_varMap_3173_);
lean_inc(v_vars_3172_);
lean_inc(v_denote_3171_);
lean_inc(v_natCastFn_x3f_3170_);
lean_inc(v_powFn_x3f_3169_);
lean_inc(v_mulFn_x3f_3168_);
lean_inc(v_addFn_x3f_3167_);
lean_inc(v_semiringInst_3166_);
lean_inc(v_u_3165_);
lean_inc(v_type_3164_);
lean_inc(v_id_3163_);
lean_dec(v_s_3162_);
v___x_3175_ = lean_box(0);
v_isShared_3176_ = v_isSharedCheck_3181_;
goto v_resetjp_3174_;
}
v_resetjp_3174_:
{
lean_object* v___x_3177_; lean_object* v___x_3179_; 
v___x_3177_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0___redArg(v_denote_3171_, v_e_3160_, v_val_3161_);
if (v_isShared_3176_ == 0)
{
lean_ctor_set(v___x_3175_, 8, v___x_3177_);
v___x_3179_ = v___x_3175_;
goto v_reusejp_3178_;
}
else
{
lean_object* v_reuseFailAlloc_3180_; 
v_reuseFailAlloc_3180_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_3180_, 0, v_id_3163_);
lean_ctor_set(v_reuseFailAlloc_3180_, 1, v_type_3164_);
lean_ctor_set(v_reuseFailAlloc_3180_, 2, v_u_3165_);
lean_ctor_set(v_reuseFailAlloc_3180_, 3, v_semiringInst_3166_);
lean_ctor_set(v_reuseFailAlloc_3180_, 4, v_addFn_x3f_3167_);
lean_ctor_set(v_reuseFailAlloc_3180_, 5, v_mulFn_x3f_3168_);
lean_ctor_set(v_reuseFailAlloc_3180_, 6, v_powFn_x3f_3169_);
lean_ctor_set(v_reuseFailAlloc_3180_, 7, v_natCastFn_x3f_3170_);
lean_ctor_set(v_reuseFailAlloc_3180_, 8, v___x_3177_);
lean_ctor_set(v_reuseFailAlloc_3180_, 9, v_vars_3172_);
lean_ctor_set(v_reuseFailAlloc_3180_, 10, v_varMap_3173_);
v___x_3179_ = v_reuseFailAlloc_3180_;
goto v_reusejp_3178_;
}
v_reusejp_3178_:
{
return v___x_3179_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__1___redArg(lean_object* v_cls_3182_, lean_object* v_msg_3183_, lean_object* v___y_3184_, lean_object* v___y_3185_, lean_object* v___y_3186_, lean_object* v___y_3187_){
_start:
{
lean_object* v_ref_3189_; lean_object* v___x_3190_; lean_object* v_a_3191_; lean_object* v___x_3193_; uint8_t v_isShared_3194_; uint8_t v_isSharedCheck_3235_; 
v_ref_3189_ = lean_ctor_get(v___y_3186_, 2);
v___x_3190_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1_spec__5_spec__8_spec__9(v_msg_3183_, v___y_3184_, v___y_3185_, v___y_3186_, v___y_3187_);
v_a_3191_ = lean_ctor_get(v___x_3190_, 0);
v_isSharedCheck_3235_ = !lean_is_exclusive(v___x_3190_);
if (v_isSharedCheck_3235_ == 0)
{
v___x_3193_ = v___x_3190_;
v_isShared_3194_ = v_isSharedCheck_3235_;
goto v_resetjp_3192_;
}
else
{
lean_inc(v_a_3191_);
lean_dec(v___x_3190_);
v___x_3193_ = lean_box(0);
v_isShared_3194_ = v_isSharedCheck_3235_;
goto v_resetjp_3192_;
}
v_resetjp_3192_:
{
lean_object* v___x_3195_; lean_object* v_traceState_3196_; lean_object* v_env_3197_; lean_object* v_nextMacroScope_3198_; lean_object* v_ngen_3199_; lean_object* v_auxDeclNGen_3200_; lean_object* v_cache_3201_; lean_object* v_messages_3202_; lean_object* v_infoState_3203_; lean_object* v_snapshotTasks_3204_; lean_object* v___x_3206_; uint8_t v_isShared_3207_; uint8_t v_isSharedCheck_3234_; 
v___x_3195_ = lean_st_ref_take(v___y_3187_);
v_traceState_3196_ = lean_ctor_get(v___x_3195_, 4);
v_env_3197_ = lean_ctor_get(v___x_3195_, 0);
v_nextMacroScope_3198_ = lean_ctor_get(v___x_3195_, 1);
v_ngen_3199_ = lean_ctor_get(v___x_3195_, 2);
v_auxDeclNGen_3200_ = lean_ctor_get(v___x_3195_, 3);
v_cache_3201_ = lean_ctor_get(v___x_3195_, 5);
v_messages_3202_ = lean_ctor_get(v___x_3195_, 6);
v_infoState_3203_ = lean_ctor_get(v___x_3195_, 7);
v_snapshotTasks_3204_ = lean_ctor_get(v___x_3195_, 8);
v_isSharedCheck_3234_ = !lean_is_exclusive(v___x_3195_);
if (v_isSharedCheck_3234_ == 0)
{
v___x_3206_ = v___x_3195_;
v_isShared_3207_ = v_isSharedCheck_3234_;
goto v_resetjp_3205_;
}
else
{
lean_inc(v_snapshotTasks_3204_);
lean_inc(v_infoState_3203_);
lean_inc(v_messages_3202_);
lean_inc(v_cache_3201_);
lean_inc(v_traceState_3196_);
lean_inc(v_auxDeclNGen_3200_);
lean_inc(v_ngen_3199_);
lean_inc(v_nextMacroScope_3198_);
lean_inc(v_env_3197_);
lean_dec(v___x_3195_);
v___x_3206_ = lean_box(0);
v_isShared_3207_ = v_isSharedCheck_3234_;
goto v_resetjp_3205_;
}
v_resetjp_3205_:
{
uint64_t v_tid_3208_; lean_object* v_traces_3209_; lean_object* v___x_3211_; uint8_t v_isShared_3212_; uint8_t v_isSharedCheck_3233_; 
v_tid_3208_ = lean_ctor_get_uint64(v_traceState_3196_, sizeof(void*)*1);
v_traces_3209_ = lean_ctor_get(v_traceState_3196_, 0);
v_isSharedCheck_3233_ = !lean_is_exclusive(v_traceState_3196_);
if (v_isSharedCheck_3233_ == 0)
{
v___x_3211_ = v_traceState_3196_;
v_isShared_3212_ = v_isSharedCheck_3233_;
goto v_resetjp_3210_;
}
else
{
lean_inc(v_traces_3209_);
lean_dec(v_traceState_3196_);
v___x_3211_ = lean_box(0);
v_isShared_3212_ = v_isSharedCheck_3233_;
goto v_resetjp_3210_;
}
v_resetjp_3210_:
{
lean_object* v___x_3213_; lean_object* v___x_3214_; double v___x_3215_; uint8_t v___x_3216_; lean_object* v___x_3217_; lean_object* v___x_3218_; lean_object* v___x_3219_; lean_object* v___x_3220_; lean_object* v___x_3221_; lean_object* v___x_3222_; lean_object* v___x_3224_; 
v___x_3213_ = lean_box(0);
v___x_3214_ = lean_box(0);
v___x_3215_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg___closed__0);
v___x_3216_ = 0;
v___x_3217_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg___closed__1));
v___x_3218_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3218_, 0, v_cls_3182_);
lean_ctor_set(v___x_3218_, 1, v___x_3214_);
lean_ctor_set(v___x_3218_, 2, v___x_3217_);
lean_ctor_set_float(v___x_3218_, sizeof(void*)*3, v___x_3215_);
lean_ctor_set_float(v___x_3218_, sizeof(void*)*3 + 8, v___x_3215_);
lean_ctor_set_uint8(v___x_3218_, sizeof(void*)*3 + 16, v___x_3216_);
v___x_3219_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg___closed__2));
v___x_3220_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3220_, 0, v___x_3218_);
lean_ctor_set(v___x_3220_, 1, v_a_3191_);
lean_ctor_set(v___x_3220_, 2, v___x_3219_);
lean_inc(v_ref_3189_);
v___x_3221_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3221_, 0, v_ref_3189_);
lean_ctor_set(v___x_3221_, 1, v___x_3220_);
v___x_3222_ = l_Lean_PersistentArray_push___redArg(v_traces_3209_, v___x_3221_);
if (v_isShared_3212_ == 0)
{
lean_ctor_set(v___x_3211_, 0, v___x_3222_);
v___x_3224_ = v___x_3211_;
goto v_reusejp_3223_;
}
else
{
lean_object* v_reuseFailAlloc_3232_; 
v_reuseFailAlloc_3232_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3232_, 0, v___x_3222_);
lean_ctor_set_uint64(v_reuseFailAlloc_3232_, sizeof(void*)*1, v_tid_3208_);
v___x_3224_ = v_reuseFailAlloc_3232_;
goto v_reusejp_3223_;
}
v_reusejp_3223_:
{
lean_object* v___x_3226_; 
if (v_isShared_3207_ == 0)
{
lean_ctor_set(v___x_3206_, 4, v___x_3224_);
v___x_3226_ = v___x_3206_;
goto v_reusejp_3225_;
}
else
{
lean_object* v_reuseFailAlloc_3231_; 
v_reuseFailAlloc_3231_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3231_, 0, v_env_3197_);
lean_ctor_set(v_reuseFailAlloc_3231_, 1, v_nextMacroScope_3198_);
lean_ctor_set(v_reuseFailAlloc_3231_, 2, v_ngen_3199_);
lean_ctor_set(v_reuseFailAlloc_3231_, 3, v_auxDeclNGen_3200_);
lean_ctor_set(v_reuseFailAlloc_3231_, 4, v___x_3224_);
lean_ctor_set(v_reuseFailAlloc_3231_, 5, v_cache_3201_);
lean_ctor_set(v_reuseFailAlloc_3231_, 6, v_messages_3202_);
lean_ctor_set(v_reuseFailAlloc_3231_, 7, v_infoState_3203_);
lean_ctor_set(v_reuseFailAlloc_3231_, 8, v_snapshotTasks_3204_);
v___x_3226_ = v_reuseFailAlloc_3231_;
goto v_reusejp_3225_;
}
v_reusejp_3225_:
{
lean_object* v___x_3227_; lean_object* v___x_3229_; 
v___x_3227_ = lean_st_ref_put(v___y_3187_, v___x_3226_);
if (v_isShared_3194_ == 0)
{
lean_ctor_set(v___x_3193_, 0, v___x_3213_);
v___x_3229_ = v___x_3193_;
goto v_reusejp_3228_;
}
else
{
lean_object* v_reuseFailAlloc_3230_; 
v_reuseFailAlloc_3230_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3230_, 0, v___x_3213_);
v___x_3229_ = v_reuseFailAlloc_3230_;
goto v_reusejp_3228_;
}
v_reusejp_3228_:
{
return v___x_3229_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__1___redArg___boxed(lean_object* v_cls_3236_, lean_object* v_msg_3237_, lean_object* v___y_3238_, lean_object* v___y_3239_, lean_object* v___y_3240_, lean_object* v___y_3241_, lean_object* v___y_3242_){
_start:
{
lean_object* v_res_3243_; 
v_res_3243_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__1___redArg(v_cls_3236_, v_msg_3237_, v___y_3238_, v___y_3239_, v___y_3240_, v___y_3241_);
lean_dec(v___y_3241_);
lean_dec_ref(v___y_3240_);
lean_dec(v___y_3239_);
lean_dec_ref(v___y_3238_);
return v_res_3243_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__2___redArg(lean_object* v_cls_3244_, lean_object* v_msg_3245_, lean_object* v___y_3246_, lean_object* v___y_3247_, lean_object* v___y_3248_, lean_object* v___y_3249_){
_start:
{
lean_object* v_ref_3251_; lean_object* v___x_3252_; lean_object* v_a_3253_; lean_object* v___x_3255_; uint8_t v_isShared_3256_; uint8_t v_isSharedCheck_3297_; 
v_ref_3251_ = lean_ctor_get(v___y_3248_, 2);
v___x_3252_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1_spec__5_spec__8_spec__9(v_msg_3245_, v___y_3246_, v___y_3247_, v___y_3248_, v___y_3249_);
v_a_3253_ = lean_ctor_get(v___x_3252_, 0);
v_isSharedCheck_3297_ = !lean_is_exclusive(v___x_3252_);
if (v_isSharedCheck_3297_ == 0)
{
v___x_3255_ = v___x_3252_;
v_isShared_3256_ = v_isSharedCheck_3297_;
goto v_resetjp_3254_;
}
else
{
lean_inc(v_a_3253_);
lean_dec(v___x_3252_);
v___x_3255_ = lean_box(0);
v_isShared_3256_ = v_isSharedCheck_3297_;
goto v_resetjp_3254_;
}
v_resetjp_3254_:
{
lean_object* v___x_3257_; lean_object* v_traceState_3258_; lean_object* v_env_3259_; lean_object* v_nextMacroScope_3260_; lean_object* v_ngen_3261_; lean_object* v_auxDeclNGen_3262_; lean_object* v_cache_3263_; lean_object* v_messages_3264_; lean_object* v_infoState_3265_; lean_object* v_snapshotTasks_3266_; lean_object* v___x_3268_; uint8_t v_isShared_3269_; uint8_t v_isSharedCheck_3296_; 
v___x_3257_ = lean_st_ref_take(v___y_3249_);
v_traceState_3258_ = lean_ctor_get(v___x_3257_, 4);
v_env_3259_ = lean_ctor_get(v___x_3257_, 0);
v_nextMacroScope_3260_ = lean_ctor_get(v___x_3257_, 1);
v_ngen_3261_ = lean_ctor_get(v___x_3257_, 2);
v_auxDeclNGen_3262_ = lean_ctor_get(v___x_3257_, 3);
v_cache_3263_ = lean_ctor_get(v___x_3257_, 5);
v_messages_3264_ = lean_ctor_get(v___x_3257_, 6);
v_infoState_3265_ = lean_ctor_get(v___x_3257_, 7);
v_snapshotTasks_3266_ = lean_ctor_get(v___x_3257_, 8);
v_isSharedCheck_3296_ = !lean_is_exclusive(v___x_3257_);
if (v_isSharedCheck_3296_ == 0)
{
v___x_3268_ = v___x_3257_;
v_isShared_3269_ = v_isSharedCheck_3296_;
goto v_resetjp_3267_;
}
else
{
lean_inc(v_snapshotTasks_3266_);
lean_inc(v_infoState_3265_);
lean_inc(v_messages_3264_);
lean_inc(v_cache_3263_);
lean_inc(v_traceState_3258_);
lean_inc(v_auxDeclNGen_3262_);
lean_inc(v_ngen_3261_);
lean_inc(v_nextMacroScope_3260_);
lean_inc(v_env_3259_);
lean_dec(v___x_3257_);
v___x_3268_ = lean_box(0);
v_isShared_3269_ = v_isSharedCheck_3296_;
goto v_resetjp_3267_;
}
v_resetjp_3267_:
{
uint64_t v_tid_3270_; lean_object* v_traces_3271_; lean_object* v___x_3273_; uint8_t v_isShared_3274_; uint8_t v_isSharedCheck_3295_; 
v_tid_3270_ = lean_ctor_get_uint64(v_traceState_3258_, sizeof(void*)*1);
v_traces_3271_ = lean_ctor_get(v_traceState_3258_, 0);
v_isSharedCheck_3295_ = !lean_is_exclusive(v_traceState_3258_);
if (v_isSharedCheck_3295_ == 0)
{
v___x_3273_ = v_traceState_3258_;
v_isShared_3274_ = v_isSharedCheck_3295_;
goto v_resetjp_3272_;
}
else
{
lean_inc(v_traces_3271_);
lean_dec(v_traceState_3258_);
v___x_3273_ = lean_box(0);
v_isShared_3274_ = v_isSharedCheck_3295_;
goto v_resetjp_3272_;
}
v_resetjp_3272_:
{
lean_object* v___x_3275_; lean_object* v___x_3276_; double v___x_3277_; uint8_t v___x_3278_; lean_object* v___x_3279_; lean_object* v___x_3280_; lean_object* v___x_3281_; lean_object* v___x_3282_; lean_object* v___x_3283_; lean_object* v___x_3284_; lean_object* v___x_3286_; 
v___x_3275_ = lean_box(0);
v___x_3276_ = lean_box(0);
v___x_3277_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg___closed__0);
v___x_3278_ = 0;
v___x_3279_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg___closed__1));
v___x_3280_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3280_, 0, v_cls_3244_);
lean_ctor_set(v___x_3280_, 1, v___x_3276_);
lean_ctor_set(v___x_3280_, 2, v___x_3279_);
lean_ctor_set_float(v___x_3280_, sizeof(void*)*3, v___x_3277_);
lean_ctor_set_float(v___x_3280_, sizeof(void*)*3 + 8, v___x_3277_);
lean_ctor_set_uint8(v___x_3280_, sizeof(void*)*3 + 16, v___x_3278_);
v___x_3281_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg___closed__2));
v___x_3282_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3282_, 0, v___x_3280_);
lean_ctor_set(v___x_3282_, 1, v_a_3253_);
lean_ctor_set(v___x_3282_, 2, v___x_3281_);
lean_inc(v_ref_3251_);
v___x_3283_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3283_, 0, v_ref_3251_);
lean_ctor_set(v___x_3283_, 1, v___x_3282_);
v___x_3284_ = l_Lean_PersistentArray_push___redArg(v_traces_3271_, v___x_3283_);
if (v_isShared_3274_ == 0)
{
lean_ctor_set(v___x_3273_, 0, v___x_3284_);
v___x_3286_ = v___x_3273_;
goto v_reusejp_3285_;
}
else
{
lean_object* v_reuseFailAlloc_3294_; 
v_reuseFailAlloc_3294_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3294_, 0, v___x_3284_);
lean_ctor_set_uint64(v_reuseFailAlloc_3294_, sizeof(void*)*1, v_tid_3270_);
v___x_3286_ = v_reuseFailAlloc_3294_;
goto v_reusejp_3285_;
}
v_reusejp_3285_:
{
lean_object* v___x_3288_; 
if (v_isShared_3269_ == 0)
{
lean_ctor_set(v___x_3268_, 4, v___x_3286_);
v___x_3288_ = v___x_3268_;
goto v_reusejp_3287_;
}
else
{
lean_object* v_reuseFailAlloc_3293_; 
v_reuseFailAlloc_3293_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3293_, 0, v_env_3259_);
lean_ctor_set(v_reuseFailAlloc_3293_, 1, v_nextMacroScope_3260_);
lean_ctor_set(v_reuseFailAlloc_3293_, 2, v_ngen_3261_);
lean_ctor_set(v_reuseFailAlloc_3293_, 3, v_auxDeclNGen_3262_);
lean_ctor_set(v_reuseFailAlloc_3293_, 4, v___x_3286_);
lean_ctor_set(v_reuseFailAlloc_3293_, 5, v_cache_3263_);
lean_ctor_set(v_reuseFailAlloc_3293_, 6, v_messages_3264_);
lean_ctor_set(v_reuseFailAlloc_3293_, 7, v_infoState_3265_);
lean_ctor_set(v_reuseFailAlloc_3293_, 8, v_snapshotTasks_3266_);
v___x_3288_ = v_reuseFailAlloc_3293_;
goto v_reusejp_3287_;
}
v_reusejp_3287_:
{
lean_object* v___x_3289_; lean_object* v___x_3291_; 
v___x_3289_ = lean_st_ref_put(v___y_3249_, v___x_3288_);
if (v_isShared_3256_ == 0)
{
lean_ctor_set(v___x_3255_, 0, v___x_3275_);
v___x_3291_ = v___x_3255_;
goto v_reusejp_3290_;
}
else
{
lean_object* v_reuseFailAlloc_3292_; 
v_reuseFailAlloc_3292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3292_, 0, v___x_3275_);
v___x_3291_ = v_reuseFailAlloc_3292_;
goto v_reusejp_3290_;
}
v_reusejp_3290_:
{
return v___x_3291_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__2___redArg___boxed(lean_object* v_cls_3298_, lean_object* v_msg_3299_, lean_object* v___y_3300_, lean_object* v___y_3301_, lean_object* v___y_3302_, lean_object* v___y_3303_, lean_object* v___y_3304_){
_start:
{
lean_object* v_res_3305_; 
v_res_3305_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__2___redArg(v_cls_3298_, v_msg_3299_, v___y_3300_, v___y_3301_, v___y_3302_, v___y_3303_);
lean_dec(v___y_3303_);
lean_dec_ref(v___y_3302_);
lean_dec(v___y_3301_);
lean_dec_ref(v___y_3300_);
return v_res_3305_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__3___redArg(lean_object* v_cls_3306_, lean_object* v_msg_3307_, lean_object* v___y_3308_, lean_object* v___y_3309_, lean_object* v___y_3310_, lean_object* v___y_3311_){
_start:
{
lean_object* v_ref_3313_; lean_object* v___x_3314_; lean_object* v_a_3315_; lean_object* v___x_3317_; uint8_t v_isShared_3318_; uint8_t v_isSharedCheck_3359_; 
v_ref_3313_ = lean_ctor_get(v___y_3310_, 2);
v___x_3314_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1_spec__5_spec__8_spec__9(v_msg_3307_, v___y_3308_, v___y_3309_, v___y_3310_, v___y_3311_);
v_a_3315_ = lean_ctor_get(v___x_3314_, 0);
v_isSharedCheck_3359_ = !lean_is_exclusive(v___x_3314_);
if (v_isSharedCheck_3359_ == 0)
{
v___x_3317_ = v___x_3314_;
v_isShared_3318_ = v_isSharedCheck_3359_;
goto v_resetjp_3316_;
}
else
{
lean_inc(v_a_3315_);
lean_dec(v___x_3314_);
v___x_3317_ = lean_box(0);
v_isShared_3318_ = v_isSharedCheck_3359_;
goto v_resetjp_3316_;
}
v_resetjp_3316_:
{
lean_object* v___x_3319_; lean_object* v_traceState_3320_; lean_object* v_env_3321_; lean_object* v_nextMacroScope_3322_; lean_object* v_ngen_3323_; lean_object* v_auxDeclNGen_3324_; lean_object* v_cache_3325_; lean_object* v_messages_3326_; lean_object* v_infoState_3327_; lean_object* v_snapshotTasks_3328_; lean_object* v___x_3330_; uint8_t v_isShared_3331_; uint8_t v_isSharedCheck_3358_; 
v___x_3319_ = lean_st_ref_take(v___y_3311_);
v_traceState_3320_ = lean_ctor_get(v___x_3319_, 4);
v_env_3321_ = lean_ctor_get(v___x_3319_, 0);
v_nextMacroScope_3322_ = lean_ctor_get(v___x_3319_, 1);
v_ngen_3323_ = lean_ctor_get(v___x_3319_, 2);
v_auxDeclNGen_3324_ = lean_ctor_get(v___x_3319_, 3);
v_cache_3325_ = lean_ctor_get(v___x_3319_, 5);
v_messages_3326_ = lean_ctor_get(v___x_3319_, 6);
v_infoState_3327_ = lean_ctor_get(v___x_3319_, 7);
v_snapshotTasks_3328_ = lean_ctor_get(v___x_3319_, 8);
v_isSharedCheck_3358_ = !lean_is_exclusive(v___x_3319_);
if (v_isSharedCheck_3358_ == 0)
{
v___x_3330_ = v___x_3319_;
v_isShared_3331_ = v_isSharedCheck_3358_;
goto v_resetjp_3329_;
}
else
{
lean_inc(v_snapshotTasks_3328_);
lean_inc(v_infoState_3327_);
lean_inc(v_messages_3326_);
lean_inc(v_cache_3325_);
lean_inc(v_traceState_3320_);
lean_inc(v_auxDeclNGen_3324_);
lean_inc(v_ngen_3323_);
lean_inc(v_nextMacroScope_3322_);
lean_inc(v_env_3321_);
lean_dec(v___x_3319_);
v___x_3330_ = lean_box(0);
v_isShared_3331_ = v_isSharedCheck_3358_;
goto v_resetjp_3329_;
}
v_resetjp_3329_:
{
uint64_t v_tid_3332_; lean_object* v_traces_3333_; lean_object* v___x_3335_; uint8_t v_isShared_3336_; uint8_t v_isSharedCheck_3357_; 
v_tid_3332_ = lean_ctor_get_uint64(v_traceState_3320_, sizeof(void*)*1);
v_traces_3333_ = lean_ctor_get(v_traceState_3320_, 0);
v_isSharedCheck_3357_ = !lean_is_exclusive(v_traceState_3320_);
if (v_isSharedCheck_3357_ == 0)
{
v___x_3335_ = v_traceState_3320_;
v_isShared_3336_ = v_isSharedCheck_3357_;
goto v_resetjp_3334_;
}
else
{
lean_inc(v_traces_3333_);
lean_dec(v_traceState_3320_);
v___x_3335_ = lean_box(0);
v_isShared_3336_ = v_isSharedCheck_3357_;
goto v_resetjp_3334_;
}
v_resetjp_3334_:
{
lean_object* v___x_3337_; lean_object* v___x_3338_; double v___x_3339_; uint8_t v___x_3340_; lean_object* v___x_3341_; lean_object* v___x_3342_; lean_object* v___x_3343_; lean_object* v___x_3344_; lean_object* v___x_3345_; lean_object* v___x_3346_; lean_object* v___x_3348_; 
v___x_3337_ = lean_box(0);
v___x_3338_ = lean_box(0);
v___x_3339_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg___closed__0);
v___x_3340_ = 0;
v___x_3341_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg___closed__1));
v___x_3342_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3342_, 0, v_cls_3306_);
lean_ctor_set(v___x_3342_, 1, v___x_3338_);
lean_ctor_set(v___x_3342_, 2, v___x_3341_);
lean_ctor_set_float(v___x_3342_, sizeof(void*)*3, v___x_3339_);
lean_ctor_set_float(v___x_3342_, sizeof(void*)*3 + 8, v___x_3339_);
lean_ctor_set_uint8(v___x_3342_, sizeof(void*)*3 + 16, v___x_3340_);
v___x_3343_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg___closed__2));
v___x_3344_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3344_, 0, v___x_3342_);
lean_ctor_set(v___x_3344_, 1, v_a_3315_);
lean_ctor_set(v___x_3344_, 2, v___x_3343_);
lean_inc(v_ref_3313_);
v___x_3345_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3345_, 0, v_ref_3313_);
lean_ctor_set(v___x_3345_, 1, v___x_3344_);
v___x_3346_ = l_Lean_PersistentArray_push___redArg(v_traces_3333_, v___x_3345_);
if (v_isShared_3336_ == 0)
{
lean_ctor_set(v___x_3335_, 0, v___x_3346_);
v___x_3348_ = v___x_3335_;
goto v_reusejp_3347_;
}
else
{
lean_object* v_reuseFailAlloc_3356_; 
v_reuseFailAlloc_3356_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3356_, 0, v___x_3346_);
lean_ctor_set_uint64(v_reuseFailAlloc_3356_, sizeof(void*)*1, v_tid_3332_);
v___x_3348_ = v_reuseFailAlloc_3356_;
goto v_reusejp_3347_;
}
v_reusejp_3347_:
{
lean_object* v___x_3350_; 
if (v_isShared_3331_ == 0)
{
lean_ctor_set(v___x_3330_, 4, v___x_3348_);
v___x_3350_ = v___x_3330_;
goto v_reusejp_3349_;
}
else
{
lean_object* v_reuseFailAlloc_3355_; 
v_reuseFailAlloc_3355_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3355_, 0, v_env_3321_);
lean_ctor_set(v_reuseFailAlloc_3355_, 1, v_nextMacroScope_3322_);
lean_ctor_set(v_reuseFailAlloc_3355_, 2, v_ngen_3323_);
lean_ctor_set(v_reuseFailAlloc_3355_, 3, v_auxDeclNGen_3324_);
lean_ctor_set(v_reuseFailAlloc_3355_, 4, v___x_3348_);
lean_ctor_set(v_reuseFailAlloc_3355_, 5, v_cache_3325_);
lean_ctor_set(v_reuseFailAlloc_3355_, 6, v_messages_3326_);
lean_ctor_set(v_reuseFailAlloc_3355_, 7, v_infoState_3327_);
lean_ctor_set(v_reuseFailAlloc_3355_, 8, v_snapshotTasks_3328_);
v___x_3350_ = v_reuseFailAlloc_3355_;
goto v_reusejp_3349_;
}
v_reusejp_3349_:
{
lean_object* v___x_3351_; lean_object* v___x_3353_; 
v___x_3351_ = lean_st_ref_put(v___y_3311_, v___x_3350_);
if (v_isShared_3318_ == 0)
{
lean_ctor_set(v___x_3317_, 0, v___x_3337_);
v___x_3353_ = v___x_3317_;
goto v_reusejp_3352_;
}
else
{
lean_object* v_reuseFailAlloc_3354_; 
v_reuseFailAlloc_3354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3354_, 0, v___x_3337_);
v___x_3353_ = v_reuseFailAlloc_3354_;
goto v_reusejp_3352_;
}
v_reusejp_3352_:
{
return v___x_3353_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__3___redArg___boxed(lean_object* v_cls_3360_, lean_object* v_msg_3361_, lean_object* v___y_3362_, lean_object* v___y_3363_, lean_object* v___y_3364_, lean_object* v___y_3365_, lean_object* v___y_3366_){
_start:
{
lean_object* v_res_3367_; 
v_res_3367_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__3___redArg(v_cls_3360_, v_msg_3361_, v___y_3362_, v___y_3363_, v___y_3364_, v___y_3365_);
lean_dec(v___y_3365_);
lean_dec_ref(v___y_3364_);
lean_dec(v___y_3363_);
lean_dec_ref(v___y_3362_);
return v_res_3367_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__2(void){
_start:
{
lean_object* v___x_3373_; lean_object* v___x_3374_; lean_object* v___x_3375_; 
v___x_3373_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__1));
v___x_3374_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__7));
v___x_3375_ = l_Lean_Name_append(v___x_3374_, v___x_3373_);
return v___x_3375_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__4(void){
_start:
{
lean_object* v___x_3377_; lean_object* v___x_3378_; 
v___x_3377_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__3));
v___x_3378_ = l_Lean_stringToMessageData(v___x_3377_);
return v___x_3378_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__6(void){
_start:
{
lean_object* v___x_3380_; lean_object* v___x_3381_; 
v___x_3380_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__5));
v___x_3381_ = l_Lean_stringToMessageData(v___x_3380_);
return v___x_3381_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__8(void){
_start:
{
lean_object* v___x_3383_; lean_object* v___x_3384_; 
v___x_3383_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__7));
v___x_3384_ = l_Lean_stringToMessageData(v___x_3383_);
return v___x_3384_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__10(void){
_start:
{
lean_object* v___x_3386_; lean_object* v___x_3387_; 
v___x_3386_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__9));
v___x_3387_ = l_Lean_stringToMessageData(v___x_3386_);
return v___x_3387_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__12(void){
_start:
{
lean_object* v___x_3389_; lean_object* v___x_3390_; 
v___x_3389_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__11));
v___x_3390_ = l_Lean_stringToMessageData(v___x_3389_);
return v___x_3390_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_internalize(lean_object* v_e_3391_, lean_object* v_parent_x3f_3392_, lean_object* v_a_3393_, lean_object* v_a_3394_, lean_object* v_a_3395_, lean_object* v_a_3396_, lean_object* v_a_3397_, lean_object* v_a_3398_, lean_object* v_a_3399_, lean_object* v_a_3400_, lean_object* v_a_3401_, lean_object* v_a_3402_){
_start:
{
lean_object* v___x_3404_; 
v___x_3404_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_3395_);
if (lean_obj_tag(v___x_3404_) == 0)
{
lean_object* v_a_3405_; lean_object* v___x_3407_; uint8_t v_isShared_3408_; uint8_t v_isSharedCheck_3749_; 
v_a_3405_ = lean_ctor_get(v___x_3404_, 0);
v_isSharedCheck_3749_ = !lean_is_exclusive(v___x_3404_);
if (v_isSharedCheck_3749_ == 0)
{
v___x_3407_ = v___x_3404_;
v_isShared_3408_ = v_isSharedCheck_3749_;
goto v_resetjp_3406_;
}
else
{
lean_inc(v_a_3405_);
lean_dec(v___x_3404_);
v___x_3407_ = lean_box(0);
v_isShared_3408_ = v_isSharedCheck_3749_;
goto v_resetjp_3406_;
}
v_resetjp_3406_:
{
uint8_t v_ring_3409_; 
v_ring_3409_ = lean_ctor_get_uint8(v_a_3405_, sizeof(void*)*14 + 21);
lean_dec(v_a_3405_);
if (v_ring_3409_ == 0)
{
lean_object* v___x_3410_; lean_object* v___x_3412_; 
lean_dec(v_parent_x3f_3392_);
lean_dec_ref(v_e_3391_);
v___x_3410_ = lean_box(0);
if (v_isShared_3408_ == 0)
{
lean_ctor_set(v___x_3407_, 0, v___x_3410_);
v___x_3412_ = v___x_3407_;
goto v_reusejp_3411_;
}
else
{
lean_object* v_reuseFailAlloc_3413_; 
v_reuseFailAlloc_3413_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3413_, 0, v___x_3410_);
v___x_3412_ = v_reuseFailAlloc_3413_;
goto v_reusejp_3411_;
}
v_reusejp_3411_:
{
return v___x_3412_;
}
}
else
{
uint8_t v___x_3414_; 
v___x_3414_ = l_Lean_Meta_Grind_Arith_isIntModuleVirtualParent(v_parent_x3f_3392_);
if (v___x_3414_ == 0)
{
lean_object* v___x_3415_; 
lean_del_object(v___x_3407_);
lean_inc_ref(v_e_3391_);
v___x_3415_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeInv(v_e_3391_, v_a_3393_, v_a_3394_, v_a_3395_, v_a_3396_, v_a_3397_, v_a_3398_, v_a_3399_, v_a_3400_, v_a_3401_, v_a_3402_);
if (lean_obj_tag(v___x_3415_) == 0)
{
lean_object* v_a_3416_; lean_object* v___x_3418_; uint8_t v_isShared_3419_; uint8_t v_isSharedCheck_3736_; 
v_a_3416_ = lean_ctor_get(v___x_3415_, 0);
v_isSharedCheck_3736_ = !lean_is_exclusive(v___x_3415_);
if (v_isSharedCheck_3736_ == 0)
{
v___x_3418_ = v___x_3415_;
v_isShared_3419_ = v_isSharedCheck_3736_;
goto v_resetjp_3417_;
}
else
{
lean_inc(v_a_3416_);
lean_dec(v___x_3415_);
v___x_3418_ = lean_box(0);
v_isShared_3419_ = v_isSharedCheck_3736_;
goto v_resetjp_3417_;
}
v_resetjp_3417_:
{
uint8_t v___x_3420_; 
v___x_3420_ = lean_unbox(v_a_3416_);
lean_dec(v_a_3416_);
if (v___x_3420_ == 0)
{
lean_object* v___x_3421_; 
lean_inc_ref(v_e_3391_);
v___x_3421_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f(v_e_3391_);
if (lean_obj_tag(v___x_3421_) == 1)
{
lean_object* v_val_3422_; uint8_t v___x_3423_; 
v_val_3422_ = lean_ctor_get(v___x_3421_, 0);
lean_inc(v_val_3422_);
lean_dec_ref_known(v___x_3421_, 1);
v___x_3423_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isForbiddenParent(v_parent_x3f_3392_);
if (v___x_3423_ == 0)
{
lean_object* v___x_3424_; 
lean_del_object(v___x_3418_);
lean_inc(v_val_3422_);
v___x_3424_ = l_Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f(v_val_3422_, v_a_3393_, v_a_3394_, v_a_3395_, v_a_3396_, v_a_3397_, v_a_3398_, v_a_3399_, v_a_3400_, v_a_3401_, v_a_3402_);
if (lean_obj_tag(v___x_3424_) == 0)
{
lean_object* v_a_3425_; 
v_a_3425_ = lean_ctor_get(v___x_3424_, 0);
lean_inc(v_a_3425_);
lean_dec_ref_known(v___x_3424_, 1);
if (lean_obj_tag(v_a_3425_) == 1)
{
lean_object* v_val_3426_; lean_object* v___x_3427_; lean_object* v___x_3428_; lean_object* v___x_3429_; 
lean_dec(v_val_3422_);
v_val_3426_ = lean_ctor_get(v_a_3425_, 0);
lean_inc_n(v_val_3426_, 2);
lean_dec_ref_known(v_a_3425_, 1);
v___x_3427_ = lean_unsigned_to_nat(0u);
v___x_3428_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3428_, 0, v_val_3426_);
lean_ctor_set_uint8(v___x_3428_, sizeof(void*)*1, v___x_3423_);
lean_inc_ref(v_e_3391_);
v___x_3429_ = l_Lean_Meta_Grind_Arith_CommRing_reify_x3f(v_e_3391_, v_ring_3409_, v___x_3427_, v___x_3428_, v_a_3393_, v_a_3394_, v_a_3395_, v_a_3396_, v_a_3397_, v_a_3398_, v_a_3399_, v_a_3400_, v_a_3401_, v_a_3402_);
if (lean_obj_tag(v___x_3429_) == 0)
{
lean_object* v_a_3430_; lean_object* v___x_3432_; uint8_t v_isShared_3433_; uint8_t v_isSharedCheck_3482_; 
v_a_3430_ = lean_ctor_get(v___x_3429_, 0);
v_isSharedCheck_3482_ = !lean_is_exclusive(v___x_3429_);
if (v_isSharedCheck_3482_ == 0)
{
v___x_3432_ = v___x_3429_;
v_isShared_3433_ = v_isSharedCheck_3482_;
goto v_resetjp_3431_;
}
else
{
lean_inc(v_a_3430_);
lean_dec(v___x_3429_);
v___x_3432_ = lean_box(0);
v_isShared_3433_ = v_isSharedCheck_3482_;
goto v_resetjp_3431_;
}
v_resetjp_3431_:
{
if (lean_obj_tag(v_a_3430_) == 1)
{
lean_object* v_toCold_3434_; lean_object* v_options_3435_; lean_object* v_val_3436_; lean_object* v_inheritedTraceOptions_3437_; uint8_t v_hasTrace_3438_; lean_object* v___f_3439_; lean_object* v___y_3441_; lean_object* v___y_3442_; lean_object* v___y_3443_; lean_object* v___y_3444_; lean_object* v___y_3445_; lean_object* v___y_3446_; lean_object* v___y_3447_; lean_object* v___y_3448_; lean_object* v___y_3449_; lean_object* v___y_3450_; lean_object* v___y_3451_; 
lean_del_object(v___x_3432_);
v_toCold_3434_ = lean_ctor_get(v_a_3401_, 0);
v_options_3435_ = lean_ctor_get(v_toCold_3434_, 2);
v_val_3436_ = lean_ctor_get(v_a_3430_, 0);
lean_inc(v_val_3436_);
lean_dec_ref_known(v_a_3430_, 1);
v_inheritedTraceOptions_3437_ = lean_ctor_get(v_toCold_3434_, 11);
v_hasTrace_3438_ = lean_ctor_get_uint8(v_options_3435_, sizeof(void*)*1);
lean_inc_ref(v_e_3391_);
v___f_3439_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_internalize___lam__0), 3, 2);
lean_closure_set(v___f_3439_, 0, v_e_3391_);
lean_closure_set(v___f_3439_, 1, v_val_3436_);
if (v_hasTrace_3438_ == 0)
{
lean_dec(v_val_3426_);
v___y_3441_ = v___x_3428_;
v___y_3442_ = v_a_3393_;
v___y_3443_ = v_a_3394_;
v___y_3444_ = v_a_3395_;
v___y_3445_ = v_a_3396_;
v___y_3446_ = v_a_3397_;
v___y_3447_ = v_a_3398_;
v___y_3448_ = v_a_3399_;
v___y_3449_ = v_a_3400_;
v___y_3450_ = v_a_3401_;
v___y_3451_ = v_a_3402_;
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
lean_dec(v_val_3426_);
v___y_3441_ = v___x_3428_;
v___y_3442_ = v_a_3393_;
v___y_3443_ = v_a_3394_;
v___y_3444_ = v_a_3395_;
v___y_3445_ = v_a_3396_;
v___y_3446_ = v_a_3397_;
v___y_3447_ = v_a_3398_;
v___y_3448_ = v_a_3399_;
v___y_3449_ = v_a_3400_;
v___y_3450_ = v_a_3401_;
v___y_3451_ = v_a_3402_;
goto v___jp_3440_;
}
else
{
lean_object* v___x_3460_; 
v___x_3460_ = l_Lean_Meta_Grind_updateLastTag(v_a_3393_, v_a_3394_, v_a_3395_, v_a_3396_, v_a_3397_, v_a_3398_, v_a_3399_, v_a_3400_, v_a_3401_, v_a_3402_);
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
v___x_3465_ = l_Nat_reprFast(v_val_3426_);
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
lean_inc_ref(v_e_3391_);
v___x_3472_ = l_Lean_MessageData_ofExpr(v_e_3391_);
v___x_3473_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3473_, 0, v___x_3471_);
lean_ctor_set(v___x_3473_, 1, v___x_3472_);
v___x_3474_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg(v___x_3457_, v___x_3473_, v_a_3399_, v_a_3400_, v_a_3401_, v_a_3402_);
if (lean_obj_tag(v___x_3474_) == 0)
{
lean_dec_ref_known(v___x_3474_, 1);
v___y_3441_ = v___x_3428_;
v___y_3442_ = v_a_3393_;
v___y_3443_ = v_a_3394_;
v___y_3444_ = v_a_3395_;
v___y_3445_ = v_a_3396_;
v___y_3446_ = v_a_3397_;
v___y_3447_ = v_a_3398_;
v___y_3448_ = v_a_3399_;
v___y_3449_ = v_a_3400_;
v___y_3450_ = v_a_3401_;
v___y_3451_ = v_a_3402_;
goto v___jp_3440_;
}
else
{
lean_dec_ref(v___f_3439_);
lean_dec_ref_known(v___x_3428_, 1);
lean_dec_ref(v_e_3391_);
return v___x_3474_;
}
}
}
}
else
{
lean_dec_ref(v___f_3439_);
lean_dec_ref_known(v___x_3428_, 1);
lean_dec(v_val_3426_);
lean_dec_ref(v_e_3391_);
return v___x_3460_;
}
}
}
v___jp_3440_:
{
lean_object* v___x_3452_; 
lean_inc_ref(v_e_3391_);
v___x_3452_ = l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg(v_e_3391_, v___y_3441_, v___y_3442_, v___y_3446_, v___y_3447_, v___y_3448_, v___y_3449_, v___y_3450_, v___y_3451_);
if (lean_obj_tag(v___x_3452_) == 0)
{
lean_object* v___x_3453_; lean_object* v___x_3454_; 
lean_dec_ref_known(v___x_3452_, 1);
v___x_3453_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_3454_ = l_Lean_Meta_Grind_SolverExtension_markTerm___redArg(v___x_3453_, v_e_3391_, v___y_3442_, v___y_3443_, v___y_3444_, v___y_3445_, v___y_3446_, v___y_3447_, v___y_3448_, v___y_3449_, v___y_3450_, v___y_3451_);
if (lean_obj_tag(v___x_3454_) == 0)
{
lean_object* v___x_3455_; 
lean_dec_ref_known(v___x_3454_, 1);
v___x_3455_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(v___f_3439_, v___y_3441_, v___y_3442_);
if (lean_obj_tag(v___x_3455_) == 0)
{
lean_object* v___x_3456_; 
lean_dec_ref_known(v___x_3455_, 1);
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
lean_dec_ref(v_e_3391_);
return v___x_3452_;
}
}
}
else
{
lean_object* v___x_3478_; lean_object* v___x_3480_; 
lean_dec(v_a_3430_);
lean_dec_ref_known(v___x_3428_, 1);
lean_dec(v_val_3426_);
lean_dec_ref(v_e_3391_);
v___x_3478_ = lean_box(0);
if (v_isShared_3433_ == 0)
{
lean_ctor_set(v___x_3432_, 0, v___x_3478_);
v___x_3480_ = v___x_3432_;
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
lean_dec_ref_known(v___x_3428_, 1);
lean_dec(v_val_3426_);
lean_dec_ref(v_e_3391_);
v_a_3483_ = lean_ctor_get(v___x_3429_, 0);
v_isSharedCheck_3490_ = !lean_is_exclusive(v___x_3429_);
if (v_isSharedCheck_3490_ == 0)
{
v___x_3485_ = v___x_3429_;
v_isShared_3486_ = v_isSharedCheck_3490_;
goto v_resetjp_3484_;
}
else
{
lean_inc(v_a_3483_);
lean_dec(v___x_3429_);
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
lean_dec(v_a_3425_);
lean_inc(v_val_3422_);
v___x_3491_ = l_Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f(v_val_3422_, v_a_3393_, v_a_3394_, v_a_3395_, v_a_3396_, v_a_3397_, v_a_3398_, v_a_3399_, v_a_3400_, v_a_3401_, v_a_3402_);
if (lean_obj_tag(v___x_3491_) == 0)
{
lean_object* v_a_3492_; 
v_a_3492_ = lean_ctor_get(v___x_3491_, 0);
lean_inc(v_a_3492_);
lean_dec_ref_known(v___x_3491_, 1);
if (lean_obj_tag(v_a_3492_) == 1)
{
lean_object* v_val_3493_; lean_object* v___x_3494_; 
lean_dec(v_val_3422_);
v_val_3493_ = lean_ctor_get(v_a_3492_, 0);
lean_inc(v_val_3493_);
lean_dec_ref_known(v_a_3492_, 1);
lean_inc_ref(v_e_3391_);
v___x_3494_ = l_Lean_Meta_Grind_Arith_CommRing_sreify_x3f(v_e_3391_, v_val_3493_, v_a_3393_, v_a_3394_, v_a_3395_, v_a_3396_, v_a_3397_, v_a_3398_, v_a_3399_, v_a_3400_, v_a_3401_, v_a_3402_);
if (lean_obj_tag(v___x_3494_) == 0)
{
lean_object* v_a_3495_; lean_object* v___x_3497_; uint8_t v_isShared_3498_; uint8_t v_isSharedCheck_3546_; 
v_a_3495_ = lean_ctor_get(v___x_3494_, 0);
v_isSharedCheck_3546_ = !lean_is_exclusive(v___x_3494_);
if (v_isSharedCheck_3546_ == 0)
{
v___x_3497_ = v___x_3494_;
v_isShared_3498_ = v_isSharedCheck_3546_;
goto v_resetjp_3496_;
}
else
{
lean_inc(v_a_3495_);
lean_dec(v___x_3494_);
v___x_3497_ = lean_box(0);
v_isShared_3498_ = v_isSharedCheck_3546_;
goto v_resetjp_3496_;
}
v_resetjp_3496_:
{
if (lean_obj_tag(v_a_3495_) == 1)
{
lean_object* v_val_3499_; lean_object* v___y_3501_; lean_object* v___y_3502_; lean_object* v___y_3503_; lean_object* v___y_3504_; lean_object* v___y_3505_; lean_object* v___y_3506_; lean_object* v___y_3507_; lean_object* v___y_3508_; lean_object* v___y_3509_; lean_object* v___y_3510_; lean_object* v___y_3511_; lean_object* v_toCold_3517_; lean_object* v_options_3518_; uint8_t v_hasTrace_3519_; 
lean_del_object(v___x_3497_);
v_val_3499_ = lean_ctor_get(v_a_3495_, 0);
lean_inc(v_val_3499_);
lean_dec_ref_known(v_a_3495_, 1);
v_toCold_3517_ = lean_ctor_get(v_a_3401_, 0);
v_options_3518_ = lean_ctor_get(v_toCold_3517_, 2);
v_hasTrace_3519_ = lean_ctor_get_uint8(v_options_3518_, sizeof(void*)*1);
if (v_hasTrace_3519_ == 0)
{
v___y_3501_ = v_val_3493_;
v___y_3502_ = v_a_3393_;
v___y_3503_ = v_a_3394_;
v___y_3504_ = v_a_3395_;
v___y_3505_ = v_a_3396_;
v___y_3506_ = v_a_3397_;
v___y_3507_ = v_a_3398_;
v___y_3508_ = v_a_3399_;
v___y_3509_ = v_a_3400_;
v___y_3510_ = v_a_3401_;
v___y_3511_ = v_a_3402_;
goto v___jp_3500_;
}
else
{
lean_object* v_inheritedTraceOptions_3520_; lean_object* v___x_3521_; lean_object* v___x_3522_; uint8_t v___x_3523_; 
v_inheritedTraceOptions_3520_ = lean_ctor_get(v_toCold_3517_, 11);
v___x_3521_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__1));
v___x_3522_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__2, &l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__2_once, _init_l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__2);
v___x_3523_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3520_, v_options_3518_, v___x_3522_);
if (v___x_3523_ == 0)
{
v___y_3501_ = v_val_3493_;
v___y_3502_ = v_a_3393_;
v___y_3503_ = v_a_3394_;
v___y_3504_ = v_a_3395_;
v___y_3505_ = v_a_3396_;
v___y_3506_ = v_a_3397_;
v___y_3507_ = v_a_3398_;
v___y_3508_ = v_a_3399_;
v___y_3509_ = v_a_3400_;
v___y_3510_ = v_a_3401_;
v___y_3511_ = v_a_3402_;
goto v___jp_3500_;
}
else
{
lean_object* v___x_3524_; 
v___x_3524_ = l_Lean_Meta_Grind_updateLastTag(v_a_3393_, v_a_3394_, v_a_3395_, v_a_3396_, v_a_3397_, v_a_3398_, v_a_3399_, v_a_3400_, v_a_3401_, v_a_3402_);
if (lean_obj_tag(v___x_3524_) == 0)
{
lean_object* v___x_3526_; uint8_t v_isShared_3527_; uint8_t v_isSharedCheck_3540_; 
v_isSharedCheck_3540_ = !lean_is_exclusive(v___x_3524_);
if (v_isSharedCheck_3540_ == 0)
{
lean_object* v_unused_3541_; 
v_unused_3541_ = lean_ctor_get(v___x_3524_, 0);
lean_dec(v_unused_3541_);
v___x_3526_ = v___x_3524_;
v_isShared_3527_ = v_isSharedCheck_3540_;
goto v_resetjp_3525_;
}
else
{
lean_dec(v___x_3524_);
v___x_3526_ = lean_box(0);
v_isShared_3527_ = v_isSharedCheck_3540_;
goto v_resetjp_3525_;
}
v_resetjp_3525_:
{
lean_object* v___x_3528_; lean_object* v___x_3529_; lean_object* v___x_3531_; 
v___x_3528_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__8, &l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__8_once, _init_l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__8);
lean_inc(v_val_3493_);
v___x_3529_ = l_Nat_reprFast(v_val_3493_);
if (v_isShared_3527_ == 0)
{
lean_ctor_set_tag(v___x_3526_, 3);
lean_ctor_set(v___x_3526_, 0, v___x_3529_);
v___x_3531_ = v___x_3526_;
goto v_reusejp_3530_;
}
else
{
lean_object* v_reuseFailAlloc_3539_; 
v_reuseFailAlloc_3539_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3539_, 0, v___x_3529_);
v___x_3531_ = v_reuseFailAlloc_3539_;
goto v_reusejp_3530_;
}
v_reusejp_3530_:
{
lean_object* v___x_3532_; lean_object* v___x_3533_; lean_object* v___x_3534_; lean_object* v___x_3535_; lean_object* v___x_3536_; lean_object* v___x_3537_; lean_object* v___x_3538_; 
v___x_3532_ = l_Lean_MessageData_ofFormat(v___x_3531_);
v___x_3533_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3533_, 0, v___x_3528_);
lean_ctor_set(v___x_3533_, 1, v___x_3532_);
v___x_3534_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__6, &l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__6_once, _init_l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__6);
v___x_3535_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3535_, 0, v___x_3533_);
lean_ctor_set(v___x_3535_, 1, v___x_3534_);
lean_inc_ref(v_e_3391_);
v___x_3536_ = l_Lean_MessageData_ofExpr(v_e_3391_);
v___x_3537_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3537_, 0, v___x_3535_);
lean_ctor_set(v___x_3537_, 1, v___x_3536_);
v___x_3538_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__1___redArg(v___x_3521_, v___x_3537_, v_a_3399_, v_a_3400_, v_a_3401_, v_a_3402_);
if (lean_obj_tag(v___x_3538_) == 0)
{
lean_dec_ref_known(v___x_3538_, 1);
v___y_3501_ = v_val_3493_;
v___y_3502_ = v_a_3393_;
v___y_3503_ = v_a_3394_;
v___y_3504_ = v_a_3395_;
v___y_3505_ = v_a_3396_;
v___y_3506_ = v_a_3397_;
v___y_3507_ = v_a_3398_;
v___y_3508_ = v_a_3399_;
v___y_3509_ = v_a_3400_;
v___y_3510_ = v_a_3401_;
v___y_3511_ = v_a_3402_;
goto v___jp_3500_;
}
else
{
lean_dec(v_val_3499_);
lean_dec(v_val_3493_);
lean_dec_ref(v_e_3391_);
return v___x_3538_;
}
}
}
}
else
{
lean_dec(v_val_3499_);
lean_dec(v_val_3493_);
lean_dec_ref(v_e_3391_);
return v___x_3524_;
}
}
}
v___jp_3500_:
{
lean_object* v___f_3512_; lean_object* v___x_3513_; 
lean_inc_ref_n(v_e_3391_, 2);
lean_inc(v___y_3501_);
v___f_3512_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_internalize___lam__1___boxed), 4, 3);
lean_closure_set(v___f_3512_, 0, v___y_3501_);
lean_closure_set(v___f_3512_, 1, v_e_3391_);
lean_closure_set(v___f_3512_, 2, v_val_3499_);
v___x_3513_ = l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg(v_e_3391_, v___y_3501_, v___y_3502_, v___y_3506_, v___y_3507_, v___y_3508_, v___y_3509_, v___y_3510_, v___y_3511_);
lean_dec(v___y_3501_);
if (lean_obj_tag(v___x_3513_) == 0)
{
lean_object* v___x_3514_; lean_object* v___x_3515_; 
lean_dec_ref_known(v___x_3513_, 1);
v___x_3514_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_3515_ = l_Lean_Meta_Grind_SolverExtension_markTerm___redArg(v___x_3514_, v_e_3391_, v___y_3502_, v___y_3503_, v___y_3504_, v___y_3505_, v___y_3506_, v___y_3507_, v___y_3508_, v___y_3509_, v___y_3510_, v___y_3511_);
if (lean_obj_tag(v___x_3515_) == 0)
{
lean_object* v___x_3516_; 
lean_dec_ref_known(v___x_3515_, 1);
v___x_3516_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_3514_, v___f_3512_, v___y_3502_);
return v___x_3516_;
}
else
{
lean_dec_ref(v___f_3512_);
return v___x_3515_;
}
}
else
{
lean_dec_ref(v___f_3512_);
lean_dec_ref(v_e_3391_);
return v___x_3513_;
}
}
}
else
{
lean_object* v___x_3542_; lean_object* v___x_3544_; 
lean_dec(v_a_3495_);
lean_dec(v_val_3493_);
lean_dec_ref(v_e_3391_);
v___x_3542_ = lean_box(0);
if (v_isShared_3498_ == 0)
{
lean_ctor_set(v___x_3497_, 0, v___x_3542_);
v___x_3544_ = v___x_3497_;
goto v_reusejp_3543_;
}
else
{
lean_object* v_reuseFailAlloc_3545_; 
v_reuseFailAlloc_3545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3545_, 0, v___x_3542_);
v___x_3544_ = v_reuseFailAlloc_3545_;
goto v_reusejp_3543_;
}
v_reusejp_3543_:
{
return v___x_3544_;
}
}
}
}
else
{
lean_object* v_a_3547_; lean_object* v___x_3549_; uint8_t v_isShared_3550_; uint8_t v_isSharedCheck_3554_; 
lean_dec(v_val_3493_);
lean_dec_ref(v_e_3391_);
v_a_3547_ = lean_ctor_get(v___x_3494_, 0);
v_isSharedCheck_3554_ = !lean_is_exclusive(v___x_3494_);
if (v_isSharedCheck_3554_ == 0)
{
v___x_3549_ = v___x_3494_;
v_isShared_3550_ = v_isSharedCheck_3554_;
goto v_resetjp_3548_;
}
else
{
lean_inc(v_a_3547_);
lean_dec(v___x_3494_);
v___x_3549_ = lean_box(0);
v_isShared_3550_ = v_isSharedCheck_3554_;
goto v_resetjp_3548_;
}
v_resetjp_3548_:
{
lean_object* v___x_3552_; 
if (v_isShared_3550_ == 0)
{
v___x_3552_ = v___x_3549_;
goto v_reusejp_3551_;
}
else
{
lean_object* v_reuseFailAlloc_3553_; 
v_reuseFailAlloc_3553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3553_, 0, v_a_3547_);
v___x_3552_ = v_reuseFailAlloc_3553_;
goto v_reusejp_3551_;
}
v_reusejp_3551_:
{
return v___x_3552_;
}
}
}
}
else
{
lean_object* v___x_3555_; 
lean_dec(v_a_3492_);
lean_inc(v_val_3422_);
v___x_3555_ = l_Lean_Meta_Grind_Arith_CommRing_getNonCommRingId_x3f(v_val_3422_, v_a_3393_, v_a_3394_, v_a_3395_, v_a_3396_, v_a_3397_, v_a_3398_, v_a_3399_, v_a_3400_, v_a_3401_, v_a_3402_);
if (lean_obj_tag(v___x_3555_) == 0)
{
lean_object* v_a_3556_; 
v_a_3556_ = lean_ctor_get(v___x_3555_, 0);
lean_inc(v_a_3556_);
lean_dec_ref_known(v___x_3555_, 1);
if (lean_obj_tag(v_a_3556_) == 1)
{
lean_object* v_val_3557_; lean_object* v___x_3558_; lean_object* v___x_3559_; 
lean_dec(v_val_3422_);
v_val_3557_ = lean_ctor_get(v_a_3556_, 0);
lean_inc(v_val_3557_);
lean_dec_ref_known(v_a_3556_, 1);
v___x_3558_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_e_3391_);
v___x_3559_ = l_Lean_Meta_Grind_Arith_CommRing_ncreify_x3f(v_e_3391_, v_ring_3409_, v___x_3558_, v_val_3557_, v_a_3393_, v_a_3394_, v_a_3395_, v_a_3396_, v_a_3397_, v_a_3398_, v_a_3399_, v_a_3400_, v_a_3401_, v_a_3402_);
if (lean_obj_tag(v___x_3559_) == 0)
{
lean_object* v_a_3560_; lean_object* v___x_3562_; uint8_t v_isShared_3563_; uint8_t v_isSharedCheck_3611_; 
v_a_3560_ = lean_ctor_get(v___x_3559_, 0);
v_isSharedCheck_3611_ = !lean_is_exclusive(v___x_3559_);
if (v_isSharedCheck_3611_ == 0)
{
v___x_3562_ = v___x_3559_;
v_isShared_3563_ = v_isSharedCheck_3611_;
goto v_resetjp_3561_;
}
else
{
lean_inc(v_a_3560_);
lean_dec(v___x_3559_);
v___x_3562_ = lean_box(0);
v_isShared_3563_ = v_isSharedCheck_3611_;
goto v_resetjp_3561_;
}
v_resetjp_3561_:
{
if (lean_obj_tag(v_a_3560_) == 1)
{
lean_object* v_toCold_3564_; lean_object* v_options_3565_; lean_object* v_val_3566_; lean_object* v_inheritedTraceOptions_3567_; uint8_t v_hasTrace_3568_; lean_object* v___f_3569_; lean_object* v___y_3571_; lean_object* v___y_3572_; lean_object* v___y_3573_; lean_object* v___y_3574_; lean_object* v___y_3575_; lean_object* v___y_3576_; lean_object* v___y_3577_; lean_object* v___y_3578_; lean_object* v___y_3579_; lean_object* v___y_3580_; lean_object* v___y_3581_; 
lean_del_object(v___x_3562_);
v_toCold_3564_ = lean_ctor_get(v_a_3401_, 0);
v_options_3565_ = lean_ctor_get(v_toCold_3564_, 2);
v_val_3566_ = lean_ctor_get(v_a_3560_, 0);
lean_inc(v_val_3566_);
lean_dec_ref_known(v_a_3560_, 1);
v_inheritedTraceOptions_3567_ = lean_ctor_get(v_toCold_3564_, 11);
v_hasTrace_3568_ = lean_ctor_get_uint8(v_options_3565_, sizeof(void*)*1);
lean_inc_ref(v_e_3391_);
v___f_3569_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_internalize___lam__2), 3, 2);
lean_closure_set(v___f_3569_, 0, v_e_3391_);
lean_closure_set(v___f_3569_, 1, v_val_3566_);
if (v_hasTrace_3568_ == 0)
{
v___y_3571_ = v_val_3557_;
v___y_3572_ = v_a_3393_;
v___y_3573_ = v_a_3394_;
v___y_3574_ = v_a_3395_;
v___y_3575_ = v_a_3396_;
v___y_3576_ = v_a_3397_;
v___y_3577_ = v_a_3398_;
v___y_3578_ = v_a_3399_;
v___y_3579_ = v_a_3400_;
v___y_3580_ = v_a_3401_;
v___y_3581_ = v_a_3402_;
goto v___jp_3570_;
}
else
{
lean_object* v___x_3586_; lean_object* v___x_3587_; uint8_t v___x_3588_; 
v___x_3586_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__1));
v___x_3587_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__2, &l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__2_once, _init_l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__2);
v___x_3588_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3567_, v_options_3565_, v___x_3587_);
if (v___x_3588_ == 0)
{
v___y_3571_ = v_val_3557_;
v___y_3572_ = v_a_3393_;
v___y_3573_ = v_a_3394_;
v___y_3574_ = v_a_3395_;
v___y_3575_ = v_a_3396_;
v___y_3576_ = v_a_3397_;
v___y_3577_ = v_a_3398_;
v___y_3578_ = v_a_3399_;
v___y_3579_ = v_a_3400_;
v___y_3580_ = v_a_3401_;
v___y_3581_ = v_a_3402_;
goto v___jp_3570_;
}
else
{
lean_object* v___x_3589_; 
v___x_3589_ = l_Lean_Meta_Grind_updateLastTag(v_a_3393_, v_a_3394_, v_a_3395_, v_a_3396_, v_a_3397_, v_a_3398_, v_a_3399_, v_a_3400_, v_a_3401_, v_a_3402_);
if (lean_obj_tag(v___x_3589_) == 0)
{
lean_object* v___x_3591_; uint8_t v_isShared_3592_; uint8_t v_isSharedCheck_3605_; 
v_isSharedCheck_3605_ = !lean_is_exclusive(v___x_3589_);
if (v_isSharedCheck_3605_ == 0)
{
lean_object* v_unused_3606_; 
v_unused_3606_ = lean_ctor_get(v___x_3589_, 0);
lean_dec(v_unused_3606_);
v___x_3591_ = v___x_3589_;
v_isShared_3592_ = v_isSharedCheck_3605_;
goto v_resetjp_3590_;
}
else
{
lean_dec(v___x_3589_);
v___x_3591_ = lean_box(0);
v_isShared_3592_ = v_isSharedCheck_3605_;
goto v_resetjp_3590_;
}
v_resetjp_3590_:
{
lean_object* v___x_3593_; lean_object* v___x_3594_; lean_object* v___x_3596_; 
v___x_3593_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__10, &l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__10_once, _init_l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__10);
lean_inc(v_val_3557_);
v___x_3594_ = l_Nat_reprFast(v_val_3557_);
if (v_isShared_3592_ == 0)
{
lean_ctor_set_tag(v___x_3591_, 3);
lean_ctor_set(v___x_3591_, 0, v___x_3594_);
v___x_3596_ = v___x_3591_;
goto v_reusejp_3595_;
}
else
{
lean_object* v_reuseFailAlloc_3604_; 
v_reuseFailAlloc_3604_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3604_, 0, v___x_3594_);
v___x_3596_ = v_reuseFailAlloc_3604_;
goto v_reusejp_3595_;
}
v_reusejp_3595_:
{
lean_object* v___x_3597_; lean_object* v___x_3598_; lean_object* v___x_3599_; lean_object* v___x_3600_; lean_object* v___x_3601_; lean_object* v___x_3602_; lean_object* v___x_3603_; 
v___x_3597_ = l_Lean_MessageData_ofFormat(v___x_3596_);
v___x_3598_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3598_, 0, v___x_3593_);
lean_ctor_set(v___x_3598_, 1, v___x_3597_);
v___x_3599_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__6, &l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__6_once, _init_l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__6);
v___x_3600_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3600_, 0, v___x_3598_);
lean_ctor_set(v___x_3600_, 1, v___x_3599_);
lean_inc_ref(v_e_3391_);
v___x_3601_ = l_Lean_MessageData_ofExpr(v_e_3391_);
v___x_3602_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3602_, 0, v___x_3600_);
lean_ctor_set(v___x_3602_, 1, v___x_3601_);
v___x_3603_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__2___redArg(v___x_3586_, v___x_3602_, v_a_3399_, v_a_3400_, v_a_3401_, v_a_3402_);
if (lean_obj_tag(v___x_3603_) == 0)
{
lean_dec_ref_known(v___x_3603_, 1);
v___y_3571_ = v_val_3557_;
v___y_3572_ = v_a_3393_;
v___y_3573_ = v_a_3394_;
v___y_3574_ = v_a_3395_;
v___y_3575_ = v_a_3396_;
v___y_3576_ = v_a_3397_;
v___y_3577_ = v_a_3398_;
v___y_3578_ = v_a_3399_;
v___y_3579_ = v_a_3400_;
v___y_3580_ = v_a_3401_;
v___y_3581_ = v_a_3402_;
goto v___jp_3570_;
}
else
{
lean_dec_ref(v___f_3569_);
lean_dec(v_val_3557_);
lean_dec_ref(v_e_3391_);
return v___x_3603_;
}
}
}
}
else
{
lean_dec_ref(v___f_3569_);
lean_dec(v_val_3557_);
lean_dec_ref(v_e_3391_);
return v___x_3589_;
}
}
}
v___jp_3570_:
{
lean_object* v___x_3582_; 
lean_inc_ref(v_e_3391_);
v___x_3582_ = l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId___redArg(v_e_3391_, v___y_3571_, v___y_3572_, v___y_3576_, v___y_3577_, v___y_3578_, v___y_3579_, v___y_3580_, v___y_3581_);
if (lean_obj_tag(v___x_3582_) == 0)
{
lean_object* v___x_3583_; lean_object* v___x_3584_; 
lean_dec_ref_known(v___x_3582_, 1);
v___x_3583_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_3584_ = l_Lean_Meta_Grind_SolverExtension_markTerm___redArg(v___x_3583_, v_e_3391_, v___y_3572_, v___y_3573_, v___y_3574_, v___y_3575_, v___y_3576_, v___y_3577_, v___y_3578_, v___y_3579_, v___y_3580_, v___y_3581_);
if (lean_obj_tag(v___x_3584_) == 0)
{
lean_object* v___x_3585_; 
lean_dec_ref_known(v___x_3584_, 1);
v___x_3585_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_modifyRing___redArg(v___f_3569_, v___y_3571_, v___y_3572_);
lean_dec(v___y_3571_);
return v___x_3585_;
}
else
{
lean_dec(v___y_3571_);
lean_dec_ref(v___f_3569_);
return v___x_3584_;
}
}
else
{
lean_dec(v___y_3571_);
lean_dec_ref(v___f_3569_);
lean_dec_ref(v_e_3391_);
return v___x_3582_;
}
}
}
else
{
lean_object* v___x_3607_; lean_object* v___x_3609_; 
lean_dec(v_a_3560_);
lean_dec(v_val_3557_);
lean_dec_ref(v_e_3391_);
v___x_3607_ = lean_box(0);
if (v_isShared_3563_ == 0)
{
lean_ctor_set(v___x_3562_, 0, v___x_3607_);
v___x_3609_ = v___x_3562_;
goto v_reusejp_3608_;
}
else
{
lean_object* v_reuseFailAlloc_3610_; 
v_reuseFailAlloc_3610_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3610_, 0, v___x_3607_);
v___x_3609_ = v_reuseFailAlloc_3610_;
goto v_reusejp_3608_;
}
v_reusejp_3608_:
{
return v___x_3609_;
}
}
}
}
else
{
lean_object* v_a_3612_; lean_object* v___x_3614_; uint8_t v_isShared_3615_; uint8_t v_isSharedCheck_3619_; 
lean_dec(v_val_3557_);
lean_dec_ref(v_e_3391_);
v_a_3612_ = lean_ctor_get(v___x_3559_, 0);
v_isSharedCheck_3619_ = !lean_is_exclusive(v___x_3559_);
if (v_isSharedCheck_3619_ == 0)
{
v___x_3614_ = v___x_3559_;
v_isShared_3615_ = v_isSharedCheck_3619_;
goto v_resetjp_3613_;
}
else
{
lean_inc(v_a_3612_);
lean_dec(v___x_3559_);
v___x_3614_ = lean_box(0);
v_isShared_3615_ = v_isSharedCheck_3619_;
goto v_resetjp_3613_;
}
v_resetjp_3613_:
{
lean_object* v___x_3617_; 
if (v_isShared_3615_ == 0)
{
v___x_3617_ = v___x_3614_;
goto v_reusejp_3616_;
}
else
{
lean_object* v_reuseFailAlloc_3618_; 
v_reuseFailAlloc_3618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3618_, 0, v_a_3612_);
v___x_3617_ = v_reuseFailAlloc_3618_;
goto v_reusejp_3616_;
}
v_reusejp_3616_:
{
return v___x_3617_;
}
}
}
}
else
{
lean_object* v___x_3620_; 
lean_dec(v_a_3556_);
v___x_3620_ = l_Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f___redArg(v_val_3422_, v_a_3393_, v_a_3398_, v_a_3399_, v_a_3400_, v_a_3401_, v_a_3402_);
if (lean_obj_tag(v___x_3620_) == 0)
{
lean_object* v_a_3621_; lean_object* v___x_3623_; uint8_t v_isShared_3624_; uint8_t v_isSharedCheck_3691_; 
v_a_3621_ = lean_ctor_get(v___x_3620_, 0);
v_isSharedCheck_3691_ = !lean_is_exclusive(v___x_3620_);
if (v_isSharedCheck_3691_ == 0)
{
v___x_3623_ = v___x_3620_;
v_isShared_3624_ = v_isSharedCheck_3691_;
goto v_resetjp_3622_;
}
else
{
lean_inc(v_a_3621_);
lean_dec(v___x_3620_);
v___x_3623_ = lean_box(0);
v_isShared_3624_ = v_isSharedCheck_3691_;
goto v_resetjp_3622_;
}
v_resetjp_3622_:
{
if (lean_obj_tag(v_a_3621_) == 1)
{
lean_object* v_val_3625_; lean_object* v___x_3626_; 
lean_del_object(v___x_3623_);
v_val_3625_ = lean_ctor_get(v_a_3621_, 0);
lean_inc(v_val_3625_);
lean_dec_ref_known(v_a_3621_, 1);
lean_inc_ref(v_e_3391_);
v___x_3626_ = l_Lean_Meta_Grind_Arith_CommRing_ncsreify_x3f(v_e_3391_, v_val_3625_, v_a_3393_, v_a_3394_, v_a_3395_, v_a_3396_, v_a_3397_, v_a_3398_, v_a_3399_, v_a_3400_, v_a_3401_, v_a_3402_);
if (lean_obj_tag(v___x_3626_) == 0)
{
lean_object* v_a_3627_; lean_object* v___x_3629_; uint8_t v_isShared_3630_; uint8_t v_isSharedCheck_3678_; 
v_a_3627_ = lean_ctor_get(v___x_3626_, 0);
v_isSharedCheck_3678_ = !lean_is_exclusive(v___x_3626_);
if (v_isSharedCheck_3678_ == 0)
{
v___x_3629_ = v___x_3626_;
v_isShared_3630_ = v_isSharedCheck_3678_;
goto v_resetjp_3628_;
}
else
{
lean_inc(v_a_3627_);
lean_dec(v___x_3626_);
v___x_3629_ = lean_box(0);
v_isShared_3630_ = v_isSharedCheck_3678_;
goto v_resetjp_3628_;
}
v_resetjp_3628_:
{
if (lean_obj_tag(v_a_3627_) == 1)
{
lean_object* v_toCold_3631_; lean_object* v_options_3632_; lean_object* v_val_3633_; lean_object* v_inheritedTraceOptions_3634_; uint8_t v_hasTrace_3635_; lean_object* v___f_3636_; lean_object* v___y_3638_; lean_object* v___y_3639_; lean_object* v___y_3640_; lean_object* v___y_3641_; lean_object* v___y_3642_; lean_object* v___y_3643_; lean_object* v___y_3644_; lean_object* v___y_3645_; lean_object* v___y_3646_; lean_object* v___y_3647_; lean_object* v___y_3648_; 
lean_del_object(v___x_3629_);
v_toCold_3631_ = lean_ctor_get(v_a_3401_, 0);
v_options_3632_ = lean_ctor_get(v_toCold_3631_, 2);
v_val_3633_ = lean_ctor_get(v_a_3627_, 0);
lean_inc(v_val_3633_);
lean_dec_ref_known(v_a_3627_, 1);
v_inheritedTraceOptions_3634_ = lean_ctor_get(v_toCold_3631_, 11);
v_hasTrace_3635_ = lean_ctor_get_uint8(v_options_3632_, sizeof(void*)*1);
lean_inc_ref(v_e_3391_);
v___f_3636_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_internalize___lam__3), 3, 2);
lean_closure_set(v___f_3636_, 0, v_e_3391_);
lean_closure_set(v___f_3636_, 1, v_val_3633_);
if (v_hasTrace_3635_ == 0)
{
v___y_3638_ = v_val_3625_;
v___y_3639_ = v_a_3393_;
v___y_3640_ = v_a_3394_;
v___y_3641_ = v_a_3395_;
v___y_3642_ = v_a_3396_;
v___y_3643_ = v_a_3397_;
v___y_3644_ = v_a_3398_;
v___y_3645_ = v_a_3399_;
v___y_3646_ = v_a_3400_;
v___y_3647_ = v_a_3401_;
v___y_3648_ = v_a_3402_;
goto v___jp_3637_;
}
else
{
lean_object* v___x_3653_; lean_object* v___x_3654_; uint8_t v___x_3655_; 
v___x_3653_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__1));
v___x_3654_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__2, &l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__2_once, _init_l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__2);
v___x_3655_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3634_, v_options_3632_, v___x_3654_);
if (v___x_3655_ == 0)
{
v___y_3638_ = v_val_3625_;
v___y_3639_ = v_a_3393_;
v___y_3640_ = v_a_3394_;
v___y_3641_ = v_a_3395_;
v___y_3642_ = v_a_3396_;
v___y_3643_ = v_a_3397_;
v___y_3644_ = v_a_3398_;
v___y_3645_ = v_a_3399_;
v___y_3646_ = v_a_3400_;
v___y_3647_ = v_a_3401_;
v___y_3648_ = v_a_3402_;
goto v___jp_3637_;
}
else
{
lean_object* v___x_3656_; 
v___x_3656_ = l_Lean_Meta_Grind_updateLastTag(v_a_3393_, v_a_3394_, v_a_3395_, v_a_3396_, v_a_3397_, v_a_3398_, v_a_3399_, v_a_3400_, v_a_3401_, v_a_3402_);
if (lean_obj_tag(v___x_3656_) == 0)
{
lean_object* v___x_3658_; uint8_t v_isShared_3659_; uint8_t v_isSharedCheck_3672_; 
v_isSharedCheck_3672_ = !lean_is_exclusive(v___x_3656_);
if (v_isSharedCheck_3672_ == 0)
{
lean_object* v_unused_3673_; 
v_unused_3673_ = lean_ctor_get(v___x_3656_, 0);
lean_dec(v_unused_3673_);
v___x_3658_ = v___x_3656_;
v_isShared_3659_ = v_isSharedCheck_3672_;
goto v_resetjp_3657_;
}
else
{
lean_dec(v___x_3656_);
v___x_3658_ = lean_box(0);
v_isShared_3659_ = v_isSharedCheck_3672_;
goto v_resetjp_3657_;
}
v_resetjp_3657_:
{
lean_object* v___x_3660_; lean_object* v___x_3661_; lean_object* v___x_3663_; 
v___x_3660_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__12, &l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__12_once, _init_l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__12);
lean_inc(v_val_3625_);
v___x_3661_ = l_Nat_reprFast(v_val_3625_);
if (v_isShared_3659_ == 0)
{
lean_ctor_set_tag(v___x_3658_, 3);
lean_ctor_set(v___x_3658_, 0, v___x_3661_);
v___x_3663_ = v___x_3658_;
goto v_reusejp_3662_;
}
else
{
lean_object* v_reuseFailAlloc_3671_; 
v_reuseFailAlloc_3671_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3671_, 0, v___x_3661_);
v___x_3663_ = v_reuseFailAlloc_3671_;
goto v_reusejp_3662_;
}
v_reusejp_3662_:
{
lean_object* v___x_3664_; lean_object* v___x_3665_; lean_object* v___x_3666_; lean_object* v___x_3667_; lean_object* v___x_3668_; lean_object* v___x_3669_; lean_object* v___x_3670_; 
v___x_3664_ = l_Lean_MessageData_ofFormat(v___x_3663_);
v___x_3665_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3665_, 0, v___x_3660_);
lean_ctor_set(v___x_3665_, 1, v___x_3664_);
v___x_3666_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__6, &l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__6_once, _init_l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__6);
v___x_3667_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3667_, 0, v___x_3665_);
lean_ctor_set(v___x_3667_, 1, v___x_3666_);
lean_inc_ref(v_e_3391_);
v___x_3668_ = l_Lean_MessageData_ofExpr(v_e_3391_);
v___x_3669_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3669_, 0, v___x_3667_);
lean_ctor_set(v___x_3669_, 1, v___x_3668_);
v___x_3670_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__3___redArg(v___x_3653_, v___x_3669_, v_a_3399_, v_a_3400_, v_a_3401_, v_a_3402_);
if (lean_obj_tag(v___x_3670_) == 0)
{
lean_dec_ref_known(v___x_3670_, 1);
v___y_3638_ = v_val_3625_;
v___y_3639_ = v_a_3393_;
v___y_3640_ = v_a_3394_;
v___y_3641_ = v_a_3395_;
v___y_3642_ = v_a_3396_;
v___y_3643_ = v_a_3397_;
v___y_3644_ = v_a_3398_;
v___y_3645_ = v_a_3399_;
v___y_3646_ = v_a_3400_;
v___y_3647_ = v_a_3401_;
v___y_3648_ = v_a_3402_;
goto v___jp_3637_;
}
else
{
lean_dec_ref(v___f_3636_);
lean_dec(v_val_3625_);
lean_dec_ref(v_e_3391_);
return v___x_3670_;
}
}
}
}
else
{
lean_dec_ref(v___f_3636_);
lean_dec(v_val_3625_);
lean_dec_ref(v_e_3391_);
return v___x_3656_;
}
}
}
v___jp_3637_:
{
lean_object* v___x_3649_; 
lean_inc_ref(v_e_3391_);
v___x_3649_ = l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId___redArg(v_e_3391_, v___y_3638_, v___y_3639_, v___y_3643_, v___y_3644_, v___y_3645_, v___y_3646_, v___y_3647_, v___y_3648_);
if (lean_obj_tag(v___x_3649_) == 0)
{
lean_object* v___x_3650_; lean_object* v___x_3651_; 
lean_dec_ref_known(v___x_3649_, 1);
v___x_3650_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_3651_ = l_Lean_Meta_Grind_SolverExtension_markTerm___redArg(v___x_3650_, v_e_3391_, v___y_3639_, v___y_3640_, v___y_3641_, v___y_3642_, v___y_3643_, v___y_3644_, v___y_3645_, v___y_3646_, v___y_3647_, v___y_3648_);
if (lean_obj_tag(v___x_3651_) == 0)
{
lean_object* v___x_3652_; 
lean_dec_ref_known(v___x_3651_, 1);
v___x_3652_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_modifySemiring___redArg(v___f_3636_, v___y_3638_, v___y_3639_);
lean_dec(v___y_3638_);
return v___x_3652_;
}
else
{
lean_dec(v___y_3638_);
lean_dec_ref(v___f_3636_);
return v___x_3651_;
}
}
else
{
lean_dec(v___y_3638_);
lean_dec_ref(v___f_3636_);
lean_dec_ref(v_e_3391_);
return v___x_3649_;
}
}
}
else
{
lean_object* v___x_3674_; lean_object* v___x_3676_; 
lean_dec(v_a_3627_);
lean_dec(v_val_3625_);
lean_dec_ref(v_e_3391_);
v___x_3674_ = lean_box(0);
if (v_isShared_3630_ == 0)
{
lean_ctor_set(v___x_3629_, 0, v___x_3674_);
v___x_3676_ = v___x_3629_;
goto v_reusejp_3675_;
}
else
{
lean_object* v_reuseFailAlloc_3677_; 
v_reuseFailAlloc_3677_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3677_, 0, v___x_3674_);
v___x_3676_ = v_reuseFailAlloc_3677_;
goto v_reusejp_3675_;
}
v_reusejp_3675_:
{
return v___x_3676_;
}
}
}
}
else
{
lean_object* v_a_3679_; lean_object* v___x_3681_; uint8_t v_isShared_3682_; uint8_t v_isSharedCheck_3686_; 
lean_dec(v_val_3625_);
lean_dec_ref(v_e_3391_);
v_a_3679_ = lean_ctor_get(v___x_3626_, 0);
v_isSharedCheck_3686_ = !lean_is_exclusive(v___x_3626_);
if (v_isSharedCheck_3686_ == 0)
{
v___x_3681_ = v___x_3626_;
v_isShared_3682_ = v_isSharedCheck_3686_;
goto v_resetjp_3680_;
}
else
{
lean_inc(v_a_3679_);
lean_dec(v___x_3626_);
v___x_3681_ = lean_box(0);
v_isShared_3682_ = v_isSharedCheck_3686_;
goto v_resetjp_3680_;
}
v_resetjp_3680_:
{
lean_object* v___x_3684_; 
if (v_isShared_3682_ == 0)
{
v___x_3684_ = v___x_3681_;
goto v_reusejp_3683_;
}
else
{
lean_object* v_reuseFailAlloc_3685_; 
v_reuseFailAlloc_3685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3685_, 0, v_a_3679_);
v___x_3684_ = v_reuseFailAlloc_3685_;
goto v_reusejp_3683_;
}
v_reusejp_3683_:
{
return v___x_3684_;
}
}
}
}
else
{
lean_object* v___x_3687_; lean_object* v___x_3689_; 
lean_dec(v_a_3621_);
lean_dec_ref(v_e_3391_);
v___x_3687_ = lean_box(0);
if (v_isShared_3624_ == 0)
{
lean_ctor_set(v___x_3623_, 0, v___x_3687_);
v___x_3689_ = v___x_3623_;
goto v_reusejp_3688_;
}
else
{
lean_object* v_reuseFailAlloc_3690_; 
v_reuseFailAlloc_3690_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3690_, 0, v___x_3687_);
v___x_3689_ = v_reuseFailAlloc_3690_;
goto v_reusejp_3688_;
}
v_reusejp_3688_:
{
return v___x_3689_;
}
}
}
}
else
{
lean_object* v_a_3692_; lean_object* v___x_3694_; uint8_t v_isShared_3695_; uint8_t v_isSharedCheck_3699_; 
lean_dec_ref(v_e_3391_);
v_a_3692_ = lean_ctor_get(v___x_3620_, 0);
v_isSharedCheck_3699_ = !lean_is_exclusive(v___x_3620_);
if (v_isSharedCheck_3699_ == 0)
{
v___x_3694_ = v___x_3620_;
v_isShared_3695_ = v_isSharedCheck_3699_;
goto v_resetjp_3693_;
}
else
{
lean_inc(v_a_3692_);
lean_dec(v___x_3620_);
v___x_3694_ = lean_box(0);
v_isShared_3695_ = v_isSharedCheck_3699_;
goto v_resetjp_3693_;
}
v_resetjp_3693_:
{
lean_object* v___x_3697_; 
if (v_isShared_3695_ == 0)
{
v___x_3697_ = v___x_3694_;
goto v_reusejp_3696_;
}
else
{
lean_object* v_reuseFailAlloc_3698_; 
v_reuseFailAlloc_3698_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3698_, 0, v_a_3692_);
v___x_3697_ = v_reuseFailAlloc_3698_;
goto v_reusejp_3696_;
}
v_reusejp_3696_:
{
return v___x_3697_;
}
}
}
}
}
else
{
lean_object* v_a_3700_; lean_object* v___x_3702_; uint8_t v_isShared_3703_; uint8_t v_isSharedCheck_3707_; 
lean_dec(v_val_3422_);
lean_dec_ref(v_e_3391_);
v_a_3700_ = lean_ctor_get(v___x_3555_, 0);
v_isSharedCheck_3707_ = !lean_is_exclusive(v___x_3555_);
if (v_isSharedCheck_3707_ == 0)
{
v___x_3702_ = v___x_3555_;
v_isShared_3703_ = v_isSharedCheck_3707_;
goto v_resetjp_3701_;
}
else
{
lean_inc(v_a_3700_);
lean_dec(v___x_3555_);
v___x_3702_ = lean_box(0);
v_isShared_3703_ = v_isSharedCheck_3707_;
goto v_resetjp_3701_;
}
v_resetjp_3701_:
{
lean_object* v___x_3705_; 
if (v_isShared_3703_ == 0)
{
v___x_3705_ = v___x_3702_;
goto v_reusejp_3704_;
}
else
{
lean_object* v_reuseFailAlloc_3706_; 
v_reuseFailAlloc_3706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3706_, 0, v_a_3700_);
v___x_3705_ = v_reuseFailAlloc_3706_;
goto v_reusejp_3704_;
}
v_reusejp_3704_:
{
return v___x_3705_;
}
}
}
}
}
else
{
lean_object* v_a_3708_; lean_object* v___x_3710_; uint8_t v_isShared_3711_; uint8_t v_isSharedCheck_3715_; 
lean_dec(v_val_3422_);
lean_dec_ref(v_e_3391_);
v_a_3708_ = lean_ctor_get(v___x_3491_, 0);
v_isSharedCheck_3715_ = !lean_is_exclusive(v___x_3491_);
if (v_isSharedCheck_3715_ == 0)
{
v___x_3710_ = v___x_3491_;
v_isShared_3711_ = v_isSharedCheck_3715_;
goto v_resetjp_3709_;
}
else
{
lean_inc(v_a_3708_);
lean_dec(v___x_3491_);
v___x_3710_ = lean_box(0);
v_isShared_3711_ = v_isSharedCheck_3715_;
goto v_resetjp_3709_;
}
v_resetjp_3709_:
{
lean_object* v___x_3713_; 
if (v_isShared_3711_ == 0)
{
v___x_3713_ = v___x_3710_;
goto v_reusejp_3712_;
}
else
{
lean_object* v_reuseFailAlloc_3714_; 
v_reuseFailAlloc_3714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3714_, 0, v_a_3708_);
v___x_3713_ = v_reuseFailAlloc_3714_;
goto v_reusejp_3712_;
}
v_reusejp_3712_:
{
return v___x_3713_;
}
}
}
}
}
else
{
lean_object* v_a_3716_; lean_object* v___x_3718_; uint8_t v_isShared_3719_; uint8_t v_isSharedCheck_3723_; 
lean_dec(v_val_3422_);
lean_dec_ref(v_e_3391_);
v_a_3716_ = lean_ctor_get(v___x_3424_, 0);
v_isSharedCheck_3723_ = !lean_is_exclusive(v___x_3424_);
if (v_isSharedCheck_3723_ == 0)
{
v___x_3718_ = v___x_3424_;
v_isShared_3719_ = v_isSharedCheck_3723_;
goto v_resetjp_3717_;
}
else
{
lean_inc(v_a_3716_);
lean_dec(v___x_3424_);
v___x_3718_ = lean_box(0);
v_isShared_3719_ = v_isSharedCheck_3723_;
goto v_resetjp_3717_;
}
v_resetjp_3717_:
{
lean_object* v___x_3721_; 
if (v_isShared_3719_ == 0)
{
v___x_3721_ = v___x_3718_;
goto v_reusejp_3720_;
}
else
{
lean_object* v_reuseFailAlloc_3722_; 
v_reuseFailAlloc_3722_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3722_, 0, v_a_3716_);
v___x_3721_ = v_reuseFailAlloc_3722_;
goto v_reusejp_3720_;
}
v_reusejp_3720_:
{
return v___x_3721_;
}
}
}
}
else
{
lean_object* v___x_3724_; lean_object* v___x_3726_; 
lean_dec(v_val_3422_);
lean_dec_ref(v_e_3391_);
v___x_3724_ = lean_box(0);
if (v_isShared_3419_ == 0)
{
lean_ctor_set(v___x_3418_, 0, v___x_3724_);
v___x_3726_ = v___x_3418_;
goto v_reusejp_3725_;
}
else
{
lean_object* v_reuseFailAlloc_3727_; 
v_reuseFailAlloc_3727_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3727_, 0, v___x_3724_);
v___x_3726_ = v_reuseFailAlloc_3727_;
goto v_reusejp_3725_;
}
v_reusejp_3725_:
{
return v___x_3726_;
}
}
}
else
{
lean_object* v___x_3728_; lean_object* v___x_3730_; 
lean_dec(v___x_3421_);
lean_dec(v_parent_x3f_3392_);
lean_dec_ref(v_e_3391_);
v___x_3728_ = lean_box(0);
if (v_isShared_3419_ == 0)
{
lean_ctor_set(v___x_3418_, 0, v___x_3728_);
v___x_3730_ = v___x_3418_;
goto v_reusejp_3729_;
}
else
{
lean_object* v_reuseFailAlloc_3731_; 
v_reuseFailAlloc_3731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3731_, 0, v___x_3728_);
v___x_3730_ = v_reuseFailAlloc_3731_;
goto v_reusejp_3729_;
}
v_reusejp_3729_:
{
return v___x_3730_;
}
}
}
else
{
lean_object* v___x_3732_; lean_object* v___x_3734_; 
lean_dec(v_parent_x3f_3392_);
lean_dec_ref(v_e_3391_);
v___x_3732_ = lean_box(0);
if (v_isShared_3419_ == 0)
{
lean_ctor_set(v___x_3418_, 0, v___x_3732_);
v___x_3734_ = v___x_3418_;
goto v_reusejp_3733_;
}
else
{
lean_object* v_reuseFailAlloc_3735_; 
v_reuseFailAlloc_3735_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3735_, 0, v___x_3732_);
v___x_3734_ = v_reuseFailAlloc_3735_;
goto v_reusejp_3733_;
}
v_reusejp_3733_:
{
return v___x_3734_;
}
}
}
}
else
{
lean_object* v_a_3737_; lean_object* v___x_3739_; uint8_t v_isShared_3740_; uint8_t v_isSharedCheck_3744_; 
lean_dec(v_parent_x3f_3392_);
lean_dec_ref(v_e_3391_);
v_a_3737_ = lean_ctor_get(v___x_3415_, 0);
v_isSharedCheck_3744_ = !lean_is_exclusive(v___x_3415_);
if (v_isSharedCheck_3744_ == 0)
{
v___x_3739_ = v___x_3415_;
v_isShared_3740_ = v_isSharedCheck_3744_;
goto v_resetjp_3738_;
}
else
{
lean_inc(v_a_3737_);
lean_dec(v___x_3415_);
v___x_3739_ = lean_box(0);
v_isShared_3740_ = v_isSharedCheck_3744_;
goto v_resetjp_3738_;
}
v_resetjp_3738_:
{
lean_object* v___x_3742_; 
if (v_isShared_3740_ == 0)
{
v___x_3742_ = v___x_3739_;
goto v_reusejp_3741_;
}
else
{
lean_object* v_reuseFailAlloc_3743_; 
v_reuseFailAlloc_3743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3743_, 0, v_a_3737_);
v___x_3742_ = v_reuseFailAlloc_3743_;
goto v_reusejp_3741_;
}
v_reusejp_3741_:
{
return v___x_3742_;
}
}
}
}
else
{
lean_object* v___x_3745_; lean_object* v___x_3747_; 
lean_dec(v_parent_x3f_3392_);
lean_dec_ref(v_e_3391_);
v___x_3745_ = lean_box(0);
if (v_isShared_3408_ == 0)
{
lean_ctor_set(v___x_3407_, 0, v___x_3745_);
v___x_3747_ = v___x_3407_;
goto v_reusejp_3746_;
}
else
{
lean_object* v_reuseFailAlloc_3748_; 
v_reuseFailAlloc_3748_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3748_, 0, v___x_3745_);
v___x_3747_ = v_reuseFailAlloc_3748_;
goto v_reusejp_3746_;
}
v_reusejp_3746_:
{
return v___x_3747_;
}
}
}
}
}
else
{
lean_object* v_a_3750_; lean_object* v___x_3752_; uint8_t v_isShared_3753_; uint8_t v_isSharedCheck_3757_; 
lean_dec(v_parent_x3f_3392_);
lean_dec_ref(v_e_3391_);
v_a_3750_ = lean_ctor_get(v___x_3404_, 0);
v_isSharedCheck_3757_ = !lean_is_exclusive(v___x_3404_);
if (v_isSharedCheck_3757_ == 0)
{
v___x_3752_ = v___x_3404_;
v_isShared_3753_ = v_isSharedCheck_3757_;
goto v_resetjp_3751_;
}
else
{
lean_inc(v_a_3750_);
lean_dec(v___x_3404_);
v___x_3752_ = lean_box(0);
v_isShared_3753_ = v_isSharedCheck_3757_;
goto v_resetjp_3751_;
}
v_resetjp_3751_:
{
lean_object* v___x_3755_; 
if (v_isShared_3753_ == 0)
{
v___x_3755_ = v___x_3752_;
goto v_reusejp_3754_;
}
else
{
lean_object* v_reuseFailAlloc_3756_; 
v_reuseFailAlloc_3756_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3756_, 0, v_a_3750_);
v___x_3755_ = v_reuseFailAlloc_3756_;
goto v_reusejp_3754_;
}
v_reusejp_3754_:
{
return v___x_3755_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_internalize___boxed(lean_object* v_e_3758_, lean_object* v_parent_x3f_3759_, lean_object* v_a_3760_, lean_object* v_a_3761_, lean_object* v_a_3762_, lean_object* v_a_3763_, lean_object* v_a_3764_, lean_object* v_a_3765_, lean_object* v_a_3766_, lean_object* v_a_3767_, lean_object* v_a_3768_, lean_object* v_a_3769_, lean_object* v_a_3770_){
_start:
{
lean_object* v_res_3771_; 
v_res_3771_ = l_Lean_Meta_Grind_Arith_CommRing_internalize(v_e_3758_, v_parent_x3f_3759_, v_a_3760_, v_a_3761_, v_a_3762_, v_a_3763_, v_a_3764_, v_a_3765_, v_a_3766_, v_a_3767_, v_a_3768_, v_a_3769_);
lean_dec(v_a_3769_);
lean_dec_ref(v_a_3768_);
lean_dec(v_a_3767_);
lean_dec_ref(v_a_3766_);
lean_dec(v_a_3765_);
lean_dec_ref(v_a_3764_);
lean_dec(v_a_3763_);
lean_dec_ref(v_a_3762_);
lean_dec(v_a_3761_);
lean_dec(v_a_3760_);
return v_res_3771_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0(lean_object* v_00_u03b2_3772_, lean_object* v_x_3773_, lean_object* v_x_3774_, lean_object* v_x_3775_){
_start:
{
lean_object* v___x_3776_; 
v___x_3776_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0___redArg(v_x_3773_, v_x_3774_, v_x_3775_);
return v___x_3776_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__1(lean_object* v_cls_3777_, lean_object* v_msg_3778_, lean_object* v___y_3779_, lean_object* v___y_3780_, lean_object* v___y_3781_, lean_object* v___y_3782_, lean_object* v___y_3783_, lean_object* v___y_3784_, lean_object* v___y_3785_, lean_object* v___y_3786_, lean_object* v___y_3787_, lean_object* v___y_3788_, lean_object* v___y_3789_){
_start:
{
lean_object* v___x_3791_; 
v___x_3791_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__1___redArg(v_cls_3777_, v_msg_3778_, v___y_3786_, v___y_3787_, v___y_3788_, v___y_3789_);
return v___x_3791_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__1___boxed(lean_object* v_cls_3792_, lean_object* v_msg_3793_, lean_object* v___y_3794_, lean_object* v___y_3795_, lean_object* v___y_3796_, lean_object* v___y_3797_, lean_object* v___y_3798_, lean_object* v___y_3799_, lean_object* v___y_3800_, lean_object* v___y_3801_, lean_object* v___y_3802_, lean_object* v___y_3803_, lean_object* v___y_3804_, lean_object* v___y_3805_){
_start:
{
lean_object* v_res_3806_; 
v_res_3806_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__1(v_cls_3792_, v_msg_3793_, v___y_3794_, v___y_3795_, v___y_3796_, v___y_3797_, v___y_3798_, v___y_3799_, v___y_3800_, v___y_3801_, v___y_3802_, v___y_3803_, v___y_3804_);
lean_dec(v___y_3804_);
lean_dec_ref(v___y_3803_);
lean_dec(v___y_3802_);
lean_dec_ref(v___y_3801_);
lean_dec(v___y_3800_);
lean_dec_ref(v___y_3799_);
lean_dec(v___y_3798_);
lean_dec_ref(v___y_3797_);
lean_dec(v___y_3796_);
lean_dec(v___y_3795_);
lean_dec(v___y_3794_);
return v_res_3806_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__2(lean_object* v_cls_3807_, lean_object* v_msg_3808_, lean_object* v___y_3809_, lean_object* v___y_3810_, lean_object* v___y_3811_, lean_object* v___y_3812_, lean_object* v___y_3813_, lean_object* v___y_3814_, lean_object* v___y_3815_, lean_object* v___y_3816_, lean_object* v___y_3817_, lean_object* v___y_3818_, lean_object* v___y_3819_){
_start:
{
lean_object* v___x_3821_; 
v___x_3821_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__2___redArg(v_cls_3807_, v_msg_3808_, v___y_3816_, v___y_3817_, v___y_3818_, v___y_3819_);
return v___x_3821_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__2___boxed(lean_object* v_cls_3822_, lean_object* v_msg_3823_, lean_object* v___y_3824_, lean_object* v___y_3825_, lean_object* v___y_3826_, lean_object* v___y_3827_, lean_object* v___y_3828_, lean_object* v___y_3829_, lean_object* v___y_3830_, lean_object* v___y_3831_, lean_object* v___y_3832_, lean_object* v___y_3833_, lean_object* v___y_3834_, lean_object* v___y_3835_){
_start:
{
lean_object* v_res_3836_; 
v_res_3836_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__2(v_cls_3822_, v_msg_3823_, v___y_3824_, v___y_3825_, v___y_3826_, v___y_3827_, v___y_3828_, v___y_3829_, v___y_3830_, v___y_3831_, v___y_3832_, v___y_3833_, v___y_3834_);
lean_dec(v___y_3834_);
lean_dec_ref(v___y_3833_);
lean_dec(v___y_3832_);
lean_dec_ref(v___y_3831_);
lean_dec(v___y_3830_);
lean_dec_ref(v___y_3829_);
lean_dec(v___y_3828_);
lean_dec_ref(v___y_3827_);
lean_dec(v___y_3826_);
lean_dec(v___y_3825_);
lean_dec(v___y_3824_);
return v_res_3836_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__3(lean_object* v_cls_3837_, lean_object* v_msg_3838_, lean_object* v___y_3839_, lean_object* v___y_3840_, lean_object* v___y_3841_, lean_object* v___y_3842_, lean_object* v___y_3843_, lean_object* v___y_3844_, lean_object* v___y_3845_, lean_object* v___y_3846_, lean_object* v___y_3847_, lean_object* v___y_3848_, lean_object* v___y_3849_){
_start:
{
lean_object* v___x_3851_; 
v___x_3851_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__3___redArg(v_cls_3837_, v_msg_3838_, v___y_3846_, v___y_3847_, v___y_3848_, v___y_3849_);
return v___x_3851_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__3___boxed(lean_object* v_cls_3852_, lean_object* v_msg_3853_, lean_object* v___y_3854_, lean_object* v___y_3855_, lean_object* v___y_3856_, lean_object* v___y_3857_, lean_object* v___y_3858_, lean_object* v___y_3859_, lean_object* v___y_3860_, lean_object* v___y_3861_, lean_object* v___y_3862_, lean_object* v___y_3863_, lean_object* v___y_3864_, lean_object* v___y_3865_){
_start:
{
lean_object* v_res_3866_; 
v_res_3866_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__3(v_cls_3852_, v_msg_3853_, v___y_3854_, v___y_3855_, v___y_3856_, v___y_3857_, v___y_3858_, v___y_3859_, v___y_3860_, v___y_3861_, v___y_3862_, v___y_3863_, v___y_3864_);
lean_dec(v___y_3864_);
lean_dec_ref(v___y_3863_);
lean_dec(v___y_3862_);
lean_dec_ref(v___y_3861_);
lean_dec(v___y_3860_);
lean_dec_ref(v___y_3859_);
lean_dec(v___y_3858_);
lean_dec_ref(v___y_3857_);
lean_dec(v___y_3856_);
lean_dec(v___y_3855_);
lean_dec(v___y_3854_);
return v_res_3866_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0(lean_object* v_00_u03b2_3867_, lean_object* v_x_3868_, size_t v_x_3869_, size_t v_x_3870_, lean_object* v_x_3871_, lean_object* v_x_3872_){
_start:
{
lean_object* v___x_3873_; 
v___x_3873_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0___redArg(v_x_3868_, v_x_3869_, v_x_3870_, v_x_3871_, v_x_3872_);
return v___x_3873_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3874_, lean_object* v_x_3875_, lean_object* v_x_3876_, lean_object* v_x_3877_, lean_object* v_x_3878_, lean_object* v_x_3879_){
_start:
{
size_t v_x_152760__boxed_3880_; size_t v_x_152761__boxed_3881_; lean_object* v_res_3882_; 
v_x_152760__boxed_3880_ = lean_unbox_usize(v_x_3876_);
lean_dec(v_x_3876_);
v_x_152761__boxed_3881_ = lean_unbox_usize(v_x_3877_);
lean_dec(v_x_3877_);
v_res_3882_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0(v_00_u03b2_3874_, v_x_3875_, v_x_152760__boxed_3880_, v_x_152761__boxed_3881_, v_x_3878_, v_x_3879_);
return v_res_3882_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_3883_, lean_object* v_n_3884_, lean_object* v_k_3885_, lean_object* v_v_3886_){
_start:
{
lean_object* v___x_3887_; 
v___x_3887_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0_spec__1___redArg(v_n_3884_, v_k_3885_, v_v_3886_);
return v___x_3887_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_3888_, size_t v_depth_3889_, lean_object* v_keys_3890_, lean_object* v_vals_3891_, lean_object* v_heq_3892_, lean_object* v_i_3893_, lean_object* v_entries_3894_){
_start:
{
lean_object* v___x_3895_; 
v___x_3895_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0_spec__2___redArg(v_depth_3889_, v_keys_3890_, v_vals_3891_, v_i_3893_, v_entries_3894_);
return v___x_3895_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_3896_, lean_object* v_depth_3897_, lean_object* v_keys_3898_, lean_object* v_vals_3899_, lean_object* v_heq_3900_, lean_object* v_i_3901_, lean_object* v_entries_3902_){
_start:
{
size_t v_depth_boxed_3903_; lean_object* v_res_3904_; 
v_depth_boxed_3903_ = lean_unbox_usize(v_depth_3897_);
lean_dec(v_depth_3897_);
v_res_3904_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0_spec__2(v_00_u03b2_3896_, v_depth_boxed_3903_, v_keys_3898_, v_vals_3899_, v_heq_3900_, v_i_3901_, v_entries_3902_);
lean_dec_ref(v_vals_3899_);
lean_dec_ref(v_keys_3898_);
return v_res_3904_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0_spec__1_spec__5(lean_object* v_00_u03b2_3905_, lean_object* v_x_3906_, lean_object* v_x_3907_, lean_object* v_x_3908_, lean_object* v_x_3909_){
_start:
{
lean_object* v___x_3910_; 
v___x_3910_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0_spec__1_spec__5___redArg(v_x_3906_, v_x_3907_, v_x_3908_, v_x_3909_);
return v___x_3910_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Simp(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Util(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Reify(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
