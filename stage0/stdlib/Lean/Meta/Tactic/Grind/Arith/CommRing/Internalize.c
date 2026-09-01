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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
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
lean_object* v___x_223_; lean_object* v_env_224_; lean_object* v___x_225_; lean_object* v_mctx_226_; lean_object* v_lctx_227_; lean_object* v_options_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; 
v___x_223_ = lean_st_ref_get(v___y_221_);
v_env_224_ = lean_ctor_get(v___x_223_, 0);
lean_inc_ref(v_env_224_);
lean_dec(v___x_223_);
v___x_225_ = lean_st_ref_get(v___y_219_);
v_mctx_226_ = lean_ctor_get(v___x_225_, 0);
lean_inc_ref(v_mctx_226_);
lean_dec(v___x_225_);
v_lctx_227_ = lean_ctor_get(v___y_218_, 2);
v_options_228_ = lean_ctor_get(v___y_220_, 1);
lean_inc_ref(v_options_228_);
lean_inc_ref(v_lctx_227_);
v___x_229_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_229_, 0, v_env_224_);
lean_ctor_set(v___x_229_, 1, v_mctx_226_);
lean_ctor_set(v___x_229_, 2, v_lctx_227_);
lean_ctor_set(v___x_229_, 3, v_options_228_);
v___x_230_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_230_, 0, v___x_229_);
lean_ctor_set(v___x_230_, 1, v_msgData_217_);
v___x_231_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_231_, 0, v___x_230_);
return v___x_231_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1_spec__5_spec__8_spec__9___boxed(lean_object* v_msgData_232_, lean_object* v___y_233_, lean_object* v___y_234_, lean_object* v___y_235_, lean_object* v___y_236_, lean_object* v___y_237_){
_start:
{
lean_object* v_res_238_; 
v_res_238_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1_spec__5_spec__8_spec__9(v_msgData_232_, v___y_233_, v___y_234_, v___y_235_, v___y_236_);
lean_dec(v___y_236_);
lean_dec_ref(v___y_235_);
lean_dec(v___y_234_);
lean_dec_ref(v___y_233_);
return v_res_238_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1_spec__5_spec__8___redArg(lean_object* v_msg_239_, lean_object* v___y_240_, lean_object* v___y_241_, lean_object* v___y_242_, lean_object* v___y_243_){
_start:
{
lean_object* v_ref_245_; lean_object* v___x_246_; lean_object* v_a_247_; lean_object* v___x_249_; uint8_t v_isShared_250_; uint8_t v_isSharedCheck_255_; 
v_ref_245_ = lean_ctor_get(v___y_242_, 4);
v___x_246_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1_spec__5_spec__8_spec__9(v_msg_239_, v___y_240_, v___y_241_, v___y_242_, v___y_243_);
v_a_247_ = lean_ctor_get(v___x_246_, 0);
v_isSharedCheck_255_ = !lean_is_exclusive(v___x_246_);
if (v_isSharedCheck_255_ == 0)
{
v___x_249_ = v___x_246_;
v_isShared_250_ = v_isSharedCheck_255_;
goto v_resetjp_248_;
}
else
{
lean_inc(v_a_247_);
lean_dec(v___x_246_);
v___x_249_ = lean_box(0);
v_isShared_250_ = v_isSharedCheck_255_;
goto v_resetjp_248_;
}
v_resetjp_248_:
{
lean_object* v___x_251_; lean_object* v___x_253_; 
lean_inc(v_ref_245_);
v___x_251_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_251_, 0, v_ref_245_);
lean_ctor_set(v___x_251_, 1, v_a_247_);
if (v_isShared_250_ == 0)
{
lean_ctor_set_tag(v___x_249_, 1);
lean_ctor_set(v___x_249_, 0, v___x_251_);
v___x_253_ = v___x_249_;
goto v_reusejp_252_;
}
else
{
lean_object* v_reuseFailAlloc_254_; 
v_reuseFailAlloc_254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_254_, 0, v___x_251_);
v___x_253_ = v_reuseFailAlloc_254_;
goto v_reusejp_252_;
}
v_reusejp_252_:
{
return v___x_253_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1_spec__5_spec__8___redArg___boxed(lean_object* v_msg_256_, lean_object* v___y_257_, lean_object* v___y_258_, lean_object* v___y_259_, lean_object* v___y_260_, lean_object* v___y_261_){
_start:
{
lean_object* v_res_262_; 
v_res_262_ = l_Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1_spec__5_spec__8___redArg(v_msg_256_, v___y_257_, v___y_258_, v___y_259_, v___y_260_);
lean_dec(v___y_260_);
lean_dec_ref(v___y_259_);
lean_dec(v___y_258_);
lean_dec_ref(v___y_257_);
return v_res_262_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1_spec__5___closed__1(void){
_start:
{
lean_object* v___x_264_; lean_object* v___x_265_; 
v___x_264_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1_spec__5___closed__0));
v___x_265_ = l_Lean_stringToMessageData(v___x_264_);
return v___x_265_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1_spec__5(lean_object* v_type_266_, lean_object* v___y_267_, lean_object* v___y_268_, lean_object* v___y_269_, lean_object* v___y_270_, lean_object* v___y_271_, lean_object* v___y_272_, lean_object* v___y_273_, lean_object* v___y_274_, lean_object* v___y_275_, lean_object* v___y_276_, lean_object* v___y_277_){
_start:
{
lean_object* v___x_279_; 
lean_inc_ref(v_type_266_);
v___x_279_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v_type_266_, v___y_273_, v___y_274_, v___y_275_, v___y_276_, v___y_277_);
if (lean_obj_tag(v___x_279_) == 0)
{
lean_object* v_a_280_; lean_object* v___x_282_; uint8_t v_isShared_283_; uint8_t v_isSharedCheck_292_; 
v_a_280_ = lean_ctor_get(v___x_279_, 0);
v_isSharedCheck_292_ = !lean_is_exclusive(v___x_279_);
if (v_isSharedCheck_292_ == 0)
{
v___x_282_ = v___x_279_;
v_isShared_283_ = v_isSharedCheck_292_;
goto v_resetjp_281_;
}
else
{
lean_inc(v_a_280_);
lean_dec(v___x_279_);
v___x_282_ = lean_box(0);
v_isShared_283_ = v_isSharedCheck_292_;
goto v_resetjp_281_;
}
v_resetjp_281_:
{
if (lean_obj_tag(v_a_280_) == 1)
{
lean_object* v_val_284_; lean_object* v___x_286_; 
lean_dec_ref(v_type_266_);
v_val_284_ = lean_ctor_get(v_a_280_, 0);
lean_inc(v_val_284_);
lean_dec_ref_known(v_a_280_, 1);
if (v_isShared_283_ == 0)
{
lean_ctor_set(v___x_282_, 0, v_val_284_);
v___x_286_ = v___x_282_;
goto v_reusejp_285_;
}
else
{
lean_object* v_reuseFailAlloc_287_; 
v_reuseFailAlloc_287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_287_, 0, v_val_284_);
v___x_286_ = v_reuseFailAlloc_287_;
goto v_reusejp_285_;
}
v_reusejp_285_:
{
return v___x_286_;
}
}
else
{
lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; 
lean_del_object(v___x_282_);
lean_dec(v_a_280_);
v___x_288_ = lean_obj_once(&l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1_spec__5___closed__1, &l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1_spec__5___closed__1_once, _init_l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1_spec__5___closed__1);
v___x_289_ = l_Lean_indentExpr(v_type_266_);
v___x_290_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_290_, 0, v___x_288_);
lean_ctor_set(v___x_290_, 1, v___x_289_);
v___x_291_ = l_Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1_spec__5_spec__8___redArg(v___x_290_, v___y_274_, v___y_275_, v___y_276_, v___y_277_);
return v___x_291_;
}
}
}
else
{
lean_object* v_a_293_; lean_object* v___x_295_; uint8_t v_isShared_296_; uint8_t v_isSharedCheck_300_; 
lean_dec_ref(v_type_266_);
v_a_293_ = lean_ctor_get(v___x_279_, 0);
v_isSharedCheck_300_ = !lean_is_exclusive(v___x_279_);
if (v_isSharedCheck_300_ == 0)
{
v___x_295_ = v___x_279_;
v_isShared_296_ = v_isSharedCheck_300_;
goto v_resetjp_294_;
}
else
{
lean_inc(v_a_293_);
lean_dec(v___x_279_);
v___x_295_ = lean_box(0);
v_isShared_296_ = v_isSharedCheck_300_;
goto v_resetjp_294_;
}
v_resetjp_294_:
{
lean_object* v___x_298_; 
if (v_isShared_296_ == 0)
{
v___x_298_ = v___x_295_;
goto v_reusejp_297_;
}
else
{
lean_object* v_reuseFailAlloc_299_; 
v_reuseFailAlloc_299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_299_, 0, v_a_293_);
v___x_298_ = v_reuseFailAlloc_299_;
goto v_reusejp_297_;
}
v_reusejp_297_:
{
return v___x_298_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1_spec__5___boxed(lean_object* v_type_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_, lean_object* v___y_309_, lean_object* v___y_310_, lean_object* v___y_311_, lean_object* v___y_312_, lean_object* v___y_313_){
_start:
{
lean_object* v_res_314_; 
v_res_314_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1_spec__5(v_type_301_, v___y_302_, v___y_303_, v___y_304_, v___y_305_, v___y_306_, v___y_307_, v___y_308_, v___y_309_, v___y_310_, v___y_311_, v___y_312_);
lean_dec(v___y_312_);
lean_dec_ref(v___y_311_);
lean_dec(v___y_310_);
lean_dec_ref(v___y_309_);
lean_dec(v___y_308_);
lean_dec_ref(v___y_307_);
lean_dec(v___y_306_);
lean_dec_ref(v___y_305_);
lean_dec(v___y_304_);
lean_dec(v___y_303_);
lean_dec_ref(v___y_302_);
return v_res_314_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1(lean_object* v_type_315_, lean_object* v_u_316_, lean_object* v_instDeclName_317_, lean_object* v_declName_318_, lean_object* v_expectedInst_319_, lean_object* v___y_320_, lean_object* v___y_321_, lean_object* v___y_322_, lean_object* v___y_323_, lean_object* v___y_324_, lean_object* v___y_325_, lean_object* v___y_326_, lean_object* v___y_327_, lean_object* v___y_328_, lean_object* v___y_329_, lean_object* v___y_330_){
_start:
{
lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; 
v___x_332_ = lean_box(0);
v___x_333_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_333_, 0, v_u_316_);
lean_ctor_set(v___x_333_, 1, v___x_332_);
lean_inc_ref(v___x_333_);
v___x_334_ = l_Lean_mkConst(v_instDeclName_317_, v___x_333_);
lean_inc_ref(v_type_315_);
v___x_335_ = l_Lean_Expr_app___override(v___x_334_, v_type_315_);
v___x_336_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1_spec__5(v___x_335_, v___y_320_, v___y_321_, v___y_322_, v___y_323_, v___y_324_, v___y_325_, v___y_326_, v___y_327_, v___y_328_, v___y_329_, v___y_330_);
if (lean_obj_tag(v___x_336_) == 0)
{
lean_object* v_a_337_; lean_object* v___x_338_; 
v_a_337_ = lean_ctor_get(v___x_336_, 0);
lean_inc_n(v_a_337_, 2);
lean_dec_ref_known(v___x_336_, 1);
lean_inc(v_declName_318_);
v___x_338_ = l_Lean_Meta_Grind_Arith_CommRing_checkInst(v_declName_318_, v_a_337_, v_expectedInst_319_, v___y_327_, v___y_328_, v___y_329_, v___y_330_);
if (lean_obj_tag(v___x_338_) == 0)
{
lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; 
lean_dec_ref_known(v___x_338_, 1);
v___x_339_ = l_Lean_mkConst(v_declName_318_, v___x_333_);
v___x_340_ = l_Lean_mkAppB(v___x_339_, v_type_315_, v_a_337_);
v___x_341_ = l_Lean_Meta_Sym_canon(v___x_340_, v___y_325_, v___y_326_, v___y_327_, v___y_328_, v___y_329_, v___y_330_);
if (lean_obj_tag(v___x_341_) == 0)
{
lean_object* v_a_342_; lean_object* v___x_343_; 
v_a_342_ = lean_ctor_get(v___x_341_, 0);
lean_inc(v_a_342_);
lean_dec_ref_known(v___x_341_, 1);
v___x_343_ = l_Lean_Meta_Sym_shareCommon(v_a_342_, v___y_325_, v___y_326_, v___y_327_, v___y_328_, v___y_329_, v___y_330_);
return v___x_343_;
}
else
{
return v___x_341_;
}
}
else
{
lean_object* v_a_344_; lean_object* v___x_346_; uint8_t v_isShared_347_; uint8_t v_isSharedCheck_351_; 
lean_dec(v_a_337_);
lean_dec_ref_known(v___x_333_, 2);
lean_dec(v_declName_318_);
lean_dec_ref(v_type_315_);
v_a_344_ = lean_ctor_get(v___x_338_, 0);
v_isSharedCheck_351_ = !lean_is_exclusive(v___x_338_);
if (v_isSharedCheck_351_ == 0)
{
v___x_346_ = v___x_338_;
v_isShared_347_ = v_isSharedCheck_351_;
goto v_resetjp_345_;
}
else
{
lean_inc(v_a_344_);
lean_dec(v___x_338_);
v___x_346_ = lean_box(0);
v_isShared_347_ = v_isSharedCheck_351_;
goto v_resetjp_345_;
}
v_resetjp_345_:
{
lean_object* v___x_349_; 
if (v_isShared_347_ == 0)
{
v___x_349_ = v___x_346_;
goto v_reusejp_348_;
}
else
{
lean_object* v_reuseFailAlloc_350_; 
v_reuseFailAlloc_350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_350_, 0, v_a_344_);
v___x_349_ = v_reuseFailAlloc_350_;
goto v_reusejp_348_;
}
v_reusejp_348_:
{
return v___x_349_;
}
}
}
}
else
{
lean_dec_ref_known(v___x_333_, 2);
lean_dec_ref(v_expectedInst_319_);
lean_dec(v_declName_318_);
lean_dec_ref(v_type_315_);
return v___x_336_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1___boxed(lean_object** _args){
lean_object* v_type_352_ = _args[0];
lean_object* v_u_353_ = _args[1];
lean_object* v_instDeclName_354_ = _args[2];
lean_object* v_declName_355_ = _args[3];
lean_object* v_expectedInst_356_ = _args[4];
lean_object* v___y_357_ = _args[5];
lean_object* v___y_358_ = _args[6];
lean_object* v___y_359_ = _args[7];
lean_object* v___y_360_ = _args[8];
lean_object* v___y_361_ = _args[9];
lean_object* v___y_362_ = _args[10];
lean_object* v___y_363_ = _args[11];
lean_object* v___y_364_ = _args[12];
lean_object* v___y_365_ = _args[13];
lean_object* v___y_366_ = _args[14];
lean_object* v___y_367_ = _args[15];
lean_object* v___y_368_ = _args[16];
_start:
{
lean_object* v_res_369_; 
v_res_369_ = l_Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1(v_type_352_, v_u_353_, v_instDeclName_354_, v_declName_355_, v_expectedInst_356_, v___y_357_, v___y_358_, v___y_359_, v___y_360_, v___y_361_, v___y_362_, v___y_363_, v___y_364_, v___y_365_, v___y_366_, v___y_367_);
lean_dec(v___y_367_);
lean_dec_ref(v___y_366_);
lean_dec(v___y_365_);
lean_dec_ref(v___y_364_);
lean_dec(v___y_363_);
lean_dec_ref(v___y_362_);
lean_dec(v___y_361_);
lean_dec_ref(v___y_360_);
lean_dec(v___y_359_);
lean_dec(v___y_358_);
lean_dec_ref(v___y_357_);
return v_res_369_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0(lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_){
_start:
{
lean_object* v___x_393_; 
v___x_393_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v___y_381_, v___y_382_, v___y_383_, v___y_384_, v___y_385_, v___y_386_, v___y_387_, v___y_388_, v___y_389_, v___y_390_, v___y_391_);
if (lean_obj_tag(v___x_393_) == 0)
{
lean_object* v_a_394_; lean_object* v___x_396_; uint8_t v_isShared_397_; uint8_t v_isSharedCheck_434_; 
v_a_394_ = lean_ctor_get(v___x_393_, 0);
v_isSharedCheck_434_ = !lean_is_exclusive(v___x_393_);
if (v_isSharedCheck_434_ == 0)
{
v___x_396_ = v___x_393_;
v_isShared_397_ = v_isSharedCheck_434_;
goto v_resetjp_395_;
}
else
{
lean_inc(v_a_394_);
lean_dec(v___x_393_);
v___x_396_ = lean_box(0);
v_isShared_397_ = v_isSharedCheck_434_;
goto v_resetjp_395_;
}
v_resetjp_395_:
{
lean_object* v_toRing_398_; lean_object* v_negFn_x3f_399_; 
v_toRing_398_ = lean_ctor_get(v_a_394_, 0);
lean_inc_ref(v_toRing_398_);
lean_dec(v_a_394_);
v_negFn_x3f_399_ = lean_ctor_get(v_toRing_398_, 9);
if (lean_obj_tag(v_negFn_x3f_399_) == 1)
{
lean_object* v_val_400_; lean_object* v___x_402_; 
lean_inc_ref(v_negFn_x3f_399_);
lean_dec_ref(v_toRing_398_);
v_val_400_ = lean_ctor_get(v_negFn_x3f_399_, 0);
lean_inc(v_val_400_);
lean_dec_ref_known(v_negFn_x3f_399_, 1);
if (v_isShared_397_ == 0)
{
lean_ctor_set(v___x_396_, 0, v_val_400_);
v___x_402_ = v___x_396_;
goto v_reusejp_401_;
}
else
{
lean_object* v_reuseFailAlloc_403_; 
v_reuseFailAlloc_403_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_403_, 0, v_val_400_);
v___x_402_ = v_reuseFailAlloc_403_;
goto v_reusejp_401_;
}
v_reusejp_401_:
{
return v___x_402_;
}
}
else
{
lean_object* v_type_404_; lean_object* v_u_405_; lean_object* v_ringInst_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v_expectedInst_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; 
lean_del_object(v___x_396_);
v_type_404_ = lean_ctor_get(v_toRing_398_, 1);
lean_inc_ref_n(v_type_404_, 2);
v_u_405_ = lean_ctor_get(v_toRing_398_, 2);
lean_inc_n(v_u_405_, 2);
v_ringInst_406_ = lean_ctor_get(v_toRing_398_, 3);
lean_inc_ref(v_ringInst_406_);
lean_dec_ref(v_toRing_398_);
v___x_407_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0___closed__4));
v___x_408_ = lean_box(0);
v___x_409_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_409_, 0, v_u_405_);
lean_ctor_set(v___x_409_, 1, v___x_408_);
v___x_410_ = l_Lean_mkConst(v___x_407_, v___x_409_);
v_expectedInst_411_ = l_Lean_mkAppB(v___x_410_, v_type_404_, v_ringInst_406_);
v___x_412_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0___closed__5));
v___x_413_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__11));
v___x_414_ = l_Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1(v_type_404_, v_u_405_, v___x_412_, v___x_413_, v_expectedInst_411_, v___y_381_, v___y_382_, v___y_383_, v___y_384_, v___y_385_, v___y_386_, v___y_387_, v___y_388_, v___y_389_, v___y_390_, v___y_391_);
if (lean_obj_tag(v___x_414_) == 0)
{
lean_object* v_a_415_; lean_object* v___f_416_; lean_object* v___x_417_; 
v_a_415_ = lean_ctor_get(v___x_414_, 0);
lean_inc_n(v_a_415_, 2);
lean_dec_ref_known(v___x_414_, 1);
v___f_416_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0___lam__0), 2, 1);
lean_closure_set(v___f_416_, 0, v_a_415_);
v___x_417_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(v___f_416_, v___y_381_, v___y_382_);
if (lean_obj_tag(v___x_417_) == 0)
{
lean_object* v___x_419_; uint8_t v_isShared_420_; uint8_t v_isSharedCheck_424_; 
v_isSharedCheck_424_ = !lean_is_exclusive(v___x_417_);
if (v_isSharedCheck_424_ == 0)
{
lean_object* v_unused_425_; 
v_unused_425_ = lean_ctor_get(v___x_417_, 0);
lean_dec(v_unused_425_);
v___x_419_ = v___x_417_;
v_isShared_420_ = v_isSharedCheck_424_;
goto v_resetjp_418_;
}
else
{
lean_dec(v___x_417_);
v___x_419_ = lean_box(0);
v_isShared_420_ = v_isSharedCheck_424_;
goto v_resetjp_418_;
}
v_resetjp_418_:
{
lean_object* v___x_422_; 
if (v_isShared_420_ == 0)
{
lean_ctor_set(v___x_419_, 0, v_a_415_);
v___x_422_ = v___x_419_;
goto v_reusejp_421_;
}
else
{
lean_object* v_reuseFailAlloc_423_; 
v_reuseFailAlloc_423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_423_, 0, v_a_415_);
v___x_422_ = v_reuseFailAlloc_423_;
goto v_reusejp_421_;
}
v_reusejp_421_:
{
return v___x_422_;
}
}
}
else
{
lean_object* v_a_426_; lean_object* v___x_428_; uint8_t v_isShared_429_; uint8_t v_isSharedCheck_433_; 
lean_dec(v_a_415_);
v_a_426_ = lean_ctor_get(v___x_417_, 0);
v_isSharedCheck_433_ = !lean_is_exclusive(v___x_417_);
if (v_isSharedCheck_433_ == 0)
{
v___x_428_ = v___x_417_;
v_isShared_429_ = v_isSharedCheck_433_;
goto v_resetjp_427_;
}
else
{
lean_inc(v_a_426_);
lean_dec(v___x_417_);
v___x_428_ = lean_box(0);
v_isShared_429_ = v_isSharedCheck_433_;
goto v_resetjp_427_;
}
v_resetjp_427_:
{
lean_object* v___x_431_; 
if (v_isShared_429_ == 0)
{
v___x_431_ = v___x_428_;
goto v_reusejp_430_;
}
else
{
lean_object* v_reuseFailAlloc_432_; 
v_reuseFailAlloc_432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_432_, 0, v_a_426_);
v___x_431_ = v_reuseFailAlloc_432_;
goto v_reusejp_430_;
}
v_reusejp_430_:
{
return v___x_431_;
}
}
}
}
else
{
return v___x_414_;
}
}
}
}
else
{
lean_object* v_a_435_; lean_object* v___x_437_; uint8_t v_isShared_438_; uint8_t v_isSharedCheck_442_; 
v_a_435_ = lean_ctor_get(v___x_393_, 0);
v_isSharedCheck_442_ = !lean_is_exclusive(v___x_393_);
if (v_isSharedCheck_442_ == 0)
{
v___x_437_ = v___x_393_;
v_isShared_438_ = v_isSharedCheck_442_;
goto v_resetjp_436_;
}
else
{
lean_inc(v_a_435_);
lean_dec(v___x_393_);
v___x_437_ = lean_box(0);
v_isShared_438_ = v_isSharedCheck_442_;
goto v_resetjp_436_;
}
v_resetjp_436_:
{
lean_object* v___x_440_; 
if (v_isShared_438_ == 0)
{
v___x_440_ = v___x_437_;
goto v_reusejp_439_;
}
else
{
lean_object* v_reuseFailAlloc_441_; 
v_reuseFailAlloc_441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_441_, 0, v_a_435_);
v___x_440_ = v_reuseFailAlloc_441_;
goto v_reusejp_439_;
}
v_reusejp_439_:
{
return v___x_440_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0___boxed(lean_object* v___y_443_, lean_object* v___y_444_, lean_object* v___y_445_, lean_object* v___y_446_, lean_object* v___y_447_, lean_object* v___y_448_, lean_object* v___y_449_, lean_object* v___y_450_, lean_object* v___y_451_, lean_object* v___y_452_, lean_object* v___y_453_, lean_object* v___y_454_){
_start:
{
lean_object* v_res_455_; 
v_res_455_ = l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0(v___y_443_, v___y_444_, v___y_445_, v___y_446_, v___y_447_, v___y_448_, v___y_449_, v___y_450_, v___y_451_, v___y_452_, v___y_453_);
lean_dec(v___y_453_);
lean_dec_ref(v___y_452_);
lean_dec(v___y_451_);
lean_dec_ref(v___y_450_);
lean_dec(v___y_449_);
lean_dec_ref(v___y_448_);
lean_dec(v___y_447_);
lean_dec_ref(v___y_446_);
lean_dec(v___y_445_);
lean_dec(v___y_444_);
lean_dec_ref(v___y_443_);
return v_res_455_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0(lean_object* v_inst_456_, lean_object* v___y_457_, lean_object* v___y_458_, lean_object* v___y_459_, lean_object* v___y_460_, lean_object* v___y_461_, lean_object* v___y_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_){
_start:
{
lean_object* v___x_469_; 
v___x_469_ = l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0(v___y_457_, v___y_458_, v___y_459_, v___y_460_, v___y_461_, v___y_462_, v___y_463_, v___y_464_, v___y_465_, v___y_466_, v___y_467_);
if (lean_obj_tag(v___x_469_) == 0)
{
lean_object* v_a_470_; lean_object* v___x_472_; uint8_t v_isShared_473_; uint8_t v_isSharedCheck_482_; 
v_a_470_ = lean_ctor_get(v___x_469_, 0);
v_isSharedCheck_482_ = !lean_is_exclusive(v___x_469_);
if (v_isSharedCheck_482_ == 0)
{
v___x_472_ = v___x_469_;
v_isShared_473_ = v_isSharedCheck_482_;
goto v_resetjp_471_;
}
else
{
lean_inc(v_a_470_);
lean_dec(v___x_469_);
v___x_472_ = lean_box(0);
v_isShared_473_ = v_isSharedCheck_482_;
goto v_resetjp_471_;
}
v_resetjp_471_:
{
lean_object* v___x_474_; size_t v___x_475_; size_t v___x_476_; uint8_t v___x_477_; lean_object* v___x_478_; lean_object* v___x_480_; 
v___x_474_ = l_Lean_Expr_appArg_x21(v_a_470_);
lean_dec(v_a_470_);
v___x_475_ = lean_ptr_addr(v___x_474_);
lean_dec_ref(v___x_474_);
v___x_476_ = lean_ptr_addr(v_inst_456_);
v___x_477_ = lean_usize_dec_eq(v___x_475_, v___x_476_);
v___x_478_ = lean_box(v___x_477_);
if (v_isShared_473_ == 0)
{
lean_ctor_set(v___x_472_, 0, v___x_478_);
v___x_480_ = v___x_472_;
goto v_reusejp_479_;
}
else
{
lean_object* v_reuseFailAlloc_481_; 
v_reuseFailAlloc_481_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_481_, 0, v___x_478_);
v___x_480_ = v_reuseFailAlloc_481_;
goto v_reusejp_479_;
}
v_reusejp_479_:
{
return v___x_480_;
}
}
}
else
{
lean_object* v_a_483_; lean_object* v___x_485_; uint8_t v_isShared_486_; uint8_t v_isSharedCheck_490_; 
v_a_483_ = lean_ctor_get(v___x_469_, 0);
v_isSharedCheck_490_ = !lean_is_exclusive(v___x_469_);
if (v_isSharedCheck_490_ == 0)
{
v___x_485_ = v___x_469_;
v_isShared_486_ = v_isSharedCheck_490_;
goto v_resetjp_484_;
}
else
{
lean_inc(v_a_483_);
lean_dec(v___x_469_);
v___x_485_ = lean_box(0);
v_isShared_486_ = v_isSharedCheck_490_;
goto v_resetjp_484_;
}
v_resetjp_484_:
{
lean_object* v___x_488_; 
if (v_isShared_486_ == 0)
{
v___x_488_ = v___x_485_;
goto v_reusejp_487_;
}
else
{
lean_object* v_reuseFailAlloc_489_; 
v_reuseFailAlloc_489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_489_, 0, v_a_483_);
v___x_488_ = v_reuseFailAlloc_489_;
goto v_reusejp_487_;
}
v_reusejp_487_:
{
return v___x_488_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0___boxed(lean_object* v_inst_491_, lean_object* v___y_492_, lean_object* v___y_493_, lean_object* v___y_494_, lean_object* v___y_495_, lean_object* v___y_496_, lean_object* v___y_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_){
_start:
{
lean_object* v_res_504_; 
v_res_504_ = l_Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0(v_inst_491_, v___y_492_, v___y_493_, v___y_494_, v___y_495_, v___y_496_, v___y_497_, v___y_498_, v___y_499_, v___y_500_, v___y_501_, v___y_502_);
lean_dec(v___y_502_);
lean_dec_ref(v___y_501_);
lean_dec(v___y_500_);
lean_dec_ref(v___y_499_);
lean_dec(v___y_498_);
lean_dec_ref(v___y_497_);
lean_dec(v___y_496_);
lean_dec_ref(v___y_495_);
lean_dec(v___y_494_);
lean_dec(v___y_493_);
lean_dec_ref(v___y_492_);
lean_dec_ref(v_inst_491_);
return v_res_504_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isIntCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__1_spec__2___lam__0(lean_object* v_a_505_, lean_object* v_s_506_){
_start:
{
lean_object* v_toRing_507_; lean_object* v_invFn_x3f_508_; lean_object* v_semiringId_x3f_509_; lean_object* v_commSemiringInst_510_; lean_object* v_commRingInst_511_; lean_object* v_noZeroDivInst_x3f_512_; lean_object* v_fieldInst_x3f_513_; lean_object* v_powIdentityInst_x3f_514_; lean_object* v_denoteEntries_515_; lean_object* v_nextId_516_; lean_object* v_steps_517_; lean_object* v_queue_518_; lean_object* v_basis_519_; lean_object* v_diseqs_520_; uint8_t v_recheck_521_; lean_object* v_invSet_522_; lean_object* v_powIdentityVarCount_523_; lean_object* v_numEq0_x3f_524_; uint8_t v_numEq0Updated_525_; lean_object* v___x_527_; uint8_t v_isShared_528_; uint8_t v_isSharedCheck_557_; 
v_toRing_507_ = lean_ctor_get(v_s_506_, 0);
v_invFn_x3f_508_ = lean_ctor_get(v_s_506_, 1);
v_semiringId_x3f_509_ = lean_ctor_get(v_s_506_, 2);
v_commSemiringInst_510_ = lean_ctor_get(v_s_506_, 3);
v_commRingInst_511_ = lean_ctor_get(v_s_506_, 4);
v_noZeroDivInst_x3f_512_ = lean_ctor_get(v_s_506_, 5);
v_fieldInst_x3f_513_ = lean_ctor_get(v_s_506_, 6);
v_powIdentityInst_x3f_514_ = lean_ctor_get(v_s_506_, 7);
v_denoteEntries_515_ = lean_ctor_get(v_s_506_, 8);
v_nextId_516_ = lean_ctor_get(v_s_506_, 9);
v_steps_517_ = lean_ctor_get(v_s_506_, 10);
v_queue_518_ = lean_ctor_get(v_s_506_, 11);
v_basis_519_ = lean_ctor_get(v_s_506_, 12);
v_diseqs_520_ = lean_ctor_get(v_s_506_, 13);
v_recheck_521_ = lean_ctor_get_uint8(v_s_506_, sizeof(void*)*17);
v_invSet_522_ = lean_ctor_get(v_s_506_, 14);
v_powIdentityVarCount_523_ = lean_ctor_get(v_s_506_, 15);
v_numEq0_x3f_524_ = lean_ctor_get(v_s_506_, 16);
v_numEq0Updated_525_ = lean_ctor_get_uint8(v_s_506_, sizeof(void*)*17 + 1);
v_isSharedCheck_557_ = !lean_is_exclusive(v_s_506_);
if (v_isSharedCheck_557_ == 0)
{
v___x_527_ = v_s_506_;
v_isShared_528_ = v_isSharedCheck_557_;
goto v_resetjp_526_;
}
else
{
lean_inc(v_numEq0_x3f_524_);
lean_inc(v_powIdentityVarCount_523_);
lean_inc(v_invSet_522_);
lean_inc(v_diseqs_520_);
lean_inc(v_basis_519_);
lean_inc(v_queue_518_);
lean_inc(v_steps_517_);
lean_inc(v_nextId_516_);
lean_inc(v_denoteEntries_515_);
lean_inc(v_powIdentityInst_x3f_514_);
lean_inc(v_fieldInst_x3f_513_);
lean_inc(v_noZeroDivInst_x3f_512_);
lean_inc(v_commRingInst_511_);
lean_inc(v_commSemiringInst_510_);
lean_inc(v_semiringId_x3f_509_);
lean_inc(v_invFn_x3f_508_);
lean_inc(v_toRing_507_);
lean_dec(v_s_506_);
v___x_527_ = lean_box(0);
v_isShared_528_ = v_isSharedCheck_557_;
goto v_resetjp_526_;
}
v_resetjp_526_:
{
lean_object* v_id_529_; lean_object* v_type_530_; lean_object* v_u_531_; lean_object* v_ringInst_532_; lean_object* v_semiringInst_533_; lean_object* v_charInst_x3f_534_; lean_object* v_addFn_x3f_535_; lean_object* v_mulFn_x3f_536_; lean_object* v_subFn_x3f_537_; lean_object* v_negFn_x3f_538_; lean_object* v_powFn_x3f_539_; lean_object* v_natCastFn_x3f_540_; lean_object* v_one_x3f_541_; lean_object* v_vars_542_; lean_object* v_varMap_543_; lean_object* v_denote_544_; lean_object* v___x_546_; uint8_t v_isShared_547_; uint8_t v_isSharedCheck_555_; 
v_id_529_ = lean_ctor_get(v_toRing_507_, 0);
v_type_530_ = lean_ctor_get(v_toRing_507_, 1);
v_u_531_ = lean_ctor_get(v_toRing_507_, 2);
v_ringInst_532_ = lean_ctor_get(v_toRing_507_, 3);
v_semiringInst_533_ = lean_ctor_get(v_toRing_507_, 4);
v_charInst_x3f_534_ = lean_ctor_get(v_toRing_507_, 5);
v_addFn_x3f_535_ = lean_ctor_get(v_toRing_507_, 6);
v_mulFn_x3f_536_ = lean_ctor_get(v_toRing_507_, 7);
v_subFn_x3f_537_ = lean_ctor_get(v_toRing_507_, 8);
v_negFn_x3f_538_ = lean_ctor_get(v_toRing_507_, 9);
v_powFn_x3f_539_ = lean_ctor_get(v_toRing_507_, 10);
v_natCastFn_x3f_540_ = lean_ctor_get(v_toRing_507_, 12);
v_one_x3f_541_ = lean_ctor_get(v_toRing_507_, 13);
v_vars_542_ = lean_ctor_get(v_toRing_507_, 14);
v_varMap_543_ = lean_ctor_get(v_toRing_507_, 15);
v_denote_544_ = lean_ctor_get(v_toRing_507_, 16);
v_isSharedCheck_555_ = !lean_is_exclusive(v_toRing_507_);
if (v_isSharedCheck_555_ == 0)
{
lean_object* v_unused_556_; 
v_unused_556_ = lean_ctor_get(v_toRing_507_, 11);
lean_dec(v_unused_556_);
v___x_546_ = v_toRing_507_;
v_isShared_547_ = v_isSharedCheck_555_;
goto v_resetjp_545_;
}
else
{
lean_inc(v_denote_544_);
lean_inc(v_varMap_543_);
lean_inc(v_vars_542_);
lean_inc(v_one_x3f_541_);
lean_inc(v_natCastFn_x3f_540_);
lean_inc(v_powFn_x3f_539_);
lean_inc(v_negFn_x3f_538_);
lean_inc(v_subFn_x3f_537_);
lean_inc(v_mulFn_x3f_536_);
lean_inc(v_addFn_x3f_535_);
lean_inc(v_charInst_x3f_534_);
lean_inc(v_semiringInst_533_);
lean_inc(v_ringInst_532_);
lean_inc(v_u_531_);
lean_inc(v_type_530_);
lean_inc(v_id_529_);
lean_dec(v_toRing_507_);
v___x_546_ = lean_box(0);
v_isShared_547_ = v_isSharedCheck_555_;
goto v_resetjp_545_;
}
v_resetjp_545_:
{
lean_object* v___x_548_; lean_object* v___x_550_; 
v___x_548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_548_, 0, v_a_505_);
if (v_isShared_547_ == 0)
{
lean_ctor_set(v___x_546_, 11, v___x_548_);
v___x_550_ = v___x_546_;
goto v_reusejp_549_;
}
else
{
lean_object* v_reuseFailAlloc_554_; 
v_reuseFailAlloc_554_ = lean_alloc_ctor(0, 17, 0);
lean_ctor_set(v_reuseFailAlloc_554_, 0, v_id_529_);
lean_ctor_set(v_reuseFailAlloc_554_, 1, v_type_530_);
lean_ctor_set(v_reuseFailAlloc_554_, 2, v_u_531_);
lean_ctor_set(v_reuseFailAlloc_554_, 3, v_ringInst_532_);
lean_ctor_set(v_reuseFailAlloc_554_, 4, v_semiringInst_533_);
lean_ctor_set(v_reuseFailAlloc_554_, 5, v_charInst_x3f_534_);
lean_ctor_set(v_reuseFailAlloc_554_, 6, v_addFn_x3f_535_);
lean_ctor_set(v_reuseFailAlloc_554_, 7, v_mulFn_x3f_536_);
lean_ctor_set(v_reuseFailAlloc_554_, 8, v_subFn_x3f_537_);
lean_ctor_set(v_reuseFailAlloc_554_, 9, v_negFn_x3f_538_);
lean_ctor_set(v_reuseFailAlloc_554_, 10, v_powFn_x3f_539_);
lean_ctor_set(v_reuseFailAlloc_554_, 11, v___x_548_);
lean_ctor_set(v_reuseFailAlloc_554_, 12, v_natCastFn_x3f_540_);
lean_ctor_set(v_reuseFailAlloc_554_, 13, v_one_x3f_541_);
lean_ctor_set(v_reuseFailAlloc_554_, 14, v_vars_542_);
lean_ctor_set(v_reuseFailAlloc_554_, 15, v_varMap_543_);
lean_ctor_set(v_reuseFailAlloc_554_, 16, v_denote_544_);
v___x_550_ = v_reuseFailAlloc_554_;
goto v_reusejp_549_;
}
v_reusejp_549_:
{
lean_object* v___x_552_; 
if (v_isShared_528_ == 0)
{
lean_ctor_set(v___x_527_, 0, v___x_550_);
v___x_552_ = v___x_527_;
goto v_reusejp_551_;
}
else
{
lean_object* v_reuseFailAlloc_553_; 
v_reuseFailAlloc_553_ = lean_alloc_ctor(0, 17, 2);
lean_ctor_set(v_reuseFailAlloc_553_, 0, v___x_550_);
lean_ctor_set(v_reuseFailAlloc_553_, 1, v_invFn_x3f_508_);
lean_ctor_set(v_reuseFailAlloc_553_, 2, v_semiringId_x3f_509_);
lean_ctor_set(v_reuseFailAlloc_553_, 3, v_commSemiringInst_510_);
lean_ctor_set(v_reuseFailAlloc_553_, 4, v_commRingInst_511_);
lean_ctor_set(v_reuseFailAlloc_553_, 5, v_noZeroDivInst_x3f_512_);
lean_ctor_set(v_reuseFailAlloc_553_, 6, v_fieldInst_x3f_513_);
lean_ctor_set(v_reuseFailAlloc_553_, 7, v_powIdentityInst_x3f_514_);
lean_ctor_set(v_reuseFailAlloc_553_, 8, v_denoteEntries_515_);
lean_ctor_set(v_reuseFailAlloc_553_, 9, v_nextId_516_);
lean_ctor_set(v_reuseFailAlloc_553_, 10, v_steps_517_);
lean_ctor_set(v_reuseFailAlloc_553_, 11, v_queue_518_);
lean_ctor_set(v_reuseFailAlloc_553_, 12, v_basis_519_);
lean_ctor_set(v_reuseFailAlloc_553_, 13, v_diseqs_520_);
lean_ctor_set(v_reuseFailAlloc_553_, 14, v_invSet_522_);
lean_ctor_set(v_reuseFailAlloc_553_, 15, v_powIdentityVarCount_523_);
lean_ctor_set(v_reuseFailAlloc_553_, 16, v_numEq0_x3f_524_);
lean_ctor_set_uint8(v_reuseFailAlloc_553_, sizeof(void*)*17, v_recheck_521_);
lean_ctor_set_uint8(v_reuseFailAlloc_553_, sizeof(void*)*17 + 1, v_numEq0Updated_525_);
v___x_552_ = v_reuseFailAlloc_553_;
goto v_reusejp_551_;
}
v_reusejp_551_:
{
return v___x_552_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isIntCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__1_spec__2(lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_){
_start:
{
lean_object* v___y_582_; lean_object* v___y_583_; lean_object* v___y_584_; lean_object* v___x_604_; 
v___x_604_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v___y_569_, v___y_570_, v___y_571_, v___y_572_, v___y_573_, v___y_574_, v___y_575_, v___y_576_, v___y_577_, v___y_578_, v___y_579_);
if (lean_obj_tag(v___x_604_) == 0)
{
lean_object* v_a_605_; lean_object* v___x_607_; uint8_t v_isShared_608_; uint8_t v_isSharedCheck_663_; 
v_a_605_ = lean_ctor_get(v___x_604_, 0);
v_isSharedCheck_663_ = !lean_is_exclusive(v___x_604_);
if (v_isSharedCheck_663_ == 0)
{
v___x_607_ = v___x_604_;
v_isShared_608_ = v_isSharedCheck_663_;
goto v_resetjp_606_;
}
else
{
lean_inc(v_a_605_);
lean_dec(v___x_604_);
v___x_607_ = lean_box(0);
v_isShared_608_ = v_isSharedCheck_663_;
goto v_resetjp_606_;
}
v_resetjp_606_:
{
lean_object* v_toRing_609_; lean_object* v_intCastFn_x3f_610_; 
v_toRing_609_ = lean_ctor_get(v_a_605_, 0);
lean_inc_ref(v_toRing_609_);
lean_dec(v_a_605_);
v_intCastFn_x3f_610_ = lean_ctor_get(v_toRing_609_, 11);
if (lean_obj_tag(v_intCastFn_x3f_610_) == 1)
{
lean_object* v_val_611_; lean_object* v___x_613_; 
lean_inc_ref(v_intCastFn_x3f_610_);
lean_dec_ref(v_toRing_609_);
v_val_611_ = lean_ctor_get(v_intCastFn_x3f_610_, 0);
lean_inc(v_val_611_);
lean_dec_ref_known(v_intCastFn_x3f_610_, 1);
if (v_isShared_608_ == 0)
{
lean_ctor_set(v___x_607_, 0, v_val_611_);
v___x_613_ = v___x_607_;
goto v_reusejp_612_;
}
else
{
lean_object* v_reuseFailAlloc_614_; 
v_reuseFailAlloc_614_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_614_, 0, v_val_611_);
v___x_613_ = v_reuseFailAlloc_614_;
goto v_reusejp_612_;
}
v_reusejp_612_:
{
return v___x_613_;
}
}
else
{
lean_object* v_type_615_; lean_object* v_u_616_; lean_object* v_ringInst_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v_inst_x27_622_; lean_object* v_inst_624_; lean_object* v___y_625_; lean_object* v___y_626_; lean_object* v___y_627_; lean_object* v___y_628_; lean_object* v___y_629_; lean_object* v___y_630_; lean_object* v___y_631_; lean_object* v___y_632_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v_instType_641_; lean_object* v___x_642_; 
lean_del_object(v___x_607_);
v_type_615_ = lean_ctor_get(v_toRing_609_, 1);
lean_inc_ref_n(v_type_615_, 3);
v_u_616_ = lean_ctor_get(v_toRing_609_, 2);
lean_inc(v_u_616_);
v_ringInst_617_ = lean_ctor_get(v_toRing_609_, 3);
lean_inc_ref(v_ringInst_617_);
lean_dec_ref(v_toRing_609_);
v___x_618_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isIntCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__1_spec__2___closed__0));
v___x_619_ = lean_box(0);
v___x_620_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_620_, 0, v_u_616_);
lean_ctor_set(v___x_620_, 1, v___x_619_);
lean_inc_ref_n(v___x_620_, 2);
v___x_621_ = l_Lean_mkConst(v___x_618_, v___x_620_);
v_inst_x27_622_ = l_Lean_mkAppB(v___x_621_, v_type_615_, v_ringInst_617_);
v___x_639_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isIntCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__1_spec__2___closed__1));
v___x_640_ = l_Lean_mkConst(v___x_639_, v___x_620_);
v_instType_641_ = l_Lean_Expr_app___override(v___x_640_, v_type_615_);
v___x_642_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v_instType_641_, v___y_575_, v___y_576_, v___y_577_, v___y_578_, v___y_579_);
if (lean_obj_tag(v___x_642_) == 0)
{
lean_object* v_a_643_; 
v_a_643_ = lean_ctor_get(v___x_642_, 0);
lean_inc(v_a_643_);
lean_dec_ref_known(v___x_642_, 1);
if (lean_obj_tag(v_a_643_) == 0)
{
v_inst_624_ = v_inst_x27_622_;
v___y_625_ = v___y_569_;
v___y_626_ = v___y_570_;
v___y_627_ = v___y_574_;
v___y_628_ = v___y_575_;
v___y_629_ = v___y_576_;
v___y_630_ = v___y_577_;
v___y_631_ = v___y_578_;
v___y_632_ = v___y_579_;
goto v___jp_623_;
}
else
{
lean_object* v_val_644_; lean_object* v___x_645_; lean_object* v___x_646_; 
v_val_644_ = lean_ctor_get(v_a_643_, 0);
lean_inc_n(v_val_644_, 2);
lean_dec_ref_known(v_a_643_, 1);
v___x_645_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isIntCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__1_spec__2___closed__3));
v___x_646_ = l_Lean_Meta_Grind_Arith_CommRing_checkInst(v___x_645_, v_val_644_, v_inst_x27_622_, v___y_576_, v___y_577_, v___y_578_, v___y_579_);
if (lean_obj_tag(v___x_646_) == 0)
{
lean_dec_ref_known(v___x_646_, 1);
v_inst_624_ = v_val_644_;
v___y_625_ = v___y_569_;
v___y_626_ = v___y_570_;
v___y_627_ = v___y_574_;
v___y_628_ = v___y_575_;
v___y_629_ = v___y_576_;
v___y_630_ = v___y_577_;
v___y_631_ = v___y_578_;
v___y_632_ = v___y_579_;
goto v___jp_623_;
}
else
{
lean_object* v_a_647_; lean_object* v___x_649_; uint8_t v_isShared_650_; uint8_t v_isSharedCheck_654_; 
lean_dec(v_val_644_);
lean_dec_ref_known(v___x_620_, 2);
lean_dec_ref(v_type_615_);
v_a_647_ = lean_ctor_get(v___x_646_, 0);
v_isSharedCheck_654_ = !lean_is_exclusive(v___x_646_);
if (v_isSharedCheck_654_ == 0)
{
v___x_649_ = v___x_646_;
v_isShared_650_ = v_isSharedCheck_654_;
goto v_resetjp_648_;
}
else
{
lean_inc(v_a_647_);
lean_dec(v___x_646_);
v___x_649_ = lean_box(0);
v_isShared_650_ = v_isSharedCheck_654_;
goto v_resetjp_648_;
}
v_resetjp_648_:
{
lean_object* v___x_652_; 
if (v_isShared_650_ == 0)
{
v___x_652_ = v___x_649_;
goto v_reusejp_651_;
}
else
{
lean_object* v_reuseFailAlloc_653_; 
v_reuseFailAlloc_653_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_653_, 0, v_a_647_);
v___x_652_ = v_reuseFailAlloc_653_;
goto v_reusejp_651_;
}
v_reusejp_651_:
{
return v___x_652_;
}
}
}
}
}
else
{
lean_object* v_a_655_; lean_object* v___x_657_; uint8_t v_isShared_658_; uint8_t v_isSharedCheck_662_; 
lean_dec_ref(v_inst_x27_622_);
lean_dec_ref_known(v___x_620_, 2);
lean_dec_ref(v_type_615_);
v_a_655_ = lean_ctor_get(v___x_642_, 0);
v_isSharedCheck_662_ = !lean_is_exclusive(v___x_642_);
if (v_isSharedCheck_662_ == 0)
{
v___x_657_ = v___x_642_;
v_isShared_658_ = v_isSharedCheck_662_;
goto v_resetjp_656_;
}
else
{
lean_inc(v_a_655_);
lean_dec(v___x_642_);
v___x_657_ = lean_box(0);
v_isShared_658_ = v_isSharedCheck_662_;
goto v_resetjp_656_;
}
v_resetjp_656_:
{
lean_object* v___x_660_; 
if (v_isShared_658_ == 0)
{
v___x_660_ = v___x_657_;
goto v_reusejp_659_;
}
else
{
lean_object* v_reuseFailAlloc_661_; 
v_reuseFailAlloc_661_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_661_, 0, v_a_655_);
v___x_660_ = v_reuseFailAlloc_661_;
goto v_reusejp_659_;
}
v_reusejp_659_:
{
return v___x_660_;
}
}
}
v___jp_623_:
{
lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; 
v___x_633_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__2));
v___x_634_ = l_Lean_mkConst(v___x_633_, v___x_620_);
v___x_635_ = l_Lean_mkAppB(v___x_634_, v_type_615_, v_inst_624_);
v___x_636_ = l_Lean_Meta_Sym_canon(v___x_635_, v___y_627_, v___y_628_, v___y_629_, v___y_630_, v___y_631_, v___y_632_);
if (lean_obj_tag(v___x_636_) == 0)
{
lean_object* v_a_637_; lean_object* v___x_638_; 
v_a_637_ = lean_ctor_get(v___x_636_, 0);
lean_inc(v_a_637_);
lean_dec_ref_known(v___x_636_, 1);
v___x_638_ = l_Lean_Meta_Sym_shareCommon(v_a_637_, v___y_627_, v___y_628_, v___y_629_, v___y_630_, v___y_631_, v___y_632_);
v___y_582_ = v___y_625_;
v___y_583_ = v___y_626_;
v___y_584_ = v___x_638_;
goto v___jp_581_;
}
else
{
v___y_582_ = v___y_625_;
v___y_583_ = v___y_626_;
v___y_584_ = v___x_636_;
goto v___jp_581_;
}
}
}
}
}
else
{
lean_object* v_a_664_; lean_object* v___x_666_; uint8_t v_isShared_667_; uint8_t v_isSharedCheck_671_; 
v_a_664_ = lean_ctor_get(v___x_604_, 0);
v_isSharedCheck_671_ = !lean_is_exclusive(v___x_604_);
if (v_isSharedCheck_671_ == 0)
{
v___x_666_ = v___x_604_;
v_isShared_667_ = v_isSharedCheck_671_;
goto v_resetjp_665_;
}
else
{
lean_inc(v_a_664_);
lean_dec(v___x_604_);
v___x_666_ = lean_box(0);
v_isShared_667_ = v_isSharedCheck_671_;
goto v_resetjp_665_;
}
v_resetjp_665_:
{
lean_object* v___x_669_; 
if (v_isShared_667_ == 0)
{
v___x_669_ = v___x_666_;
goto v_reusejp_668_;
}
else
{
lean_object* v_reuseFailAlloc_670_; 
v_reuseFailAlloc_670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_670_, 0, v_a_664_);
v___x_669_ = v_reuseFailAlloc_670_;
goto v_reusejp_668_;
}
v_reusejp_668_:
{
return v___x_669_;
}
}
}
v___jp_581_:
{
if (lean_obj_tag(v___y_584_) == 0)
{
lean_object* v_a_585_; lean_object* v___f_586_; lean_object* v___x_587_; 
v_a_585_ = lean_ctor_get(v___y_584_, 0);
lean_inc_n(v_a_585_, 2);
lean_dec_ref_known(v___y_584_, 1);
v___f_586_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isIntCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__1_spec__2___lam__0), 2, 1);
lean_closure_set(v___f_586_, 0, v_a_585_);
v___x_587_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(v___f_586_, v___y_582_, v___y_583_);
if (lean_obj_tag(v___x_587_) == 0)
{
lean_object* v___x_589_; uint8_t v_isShared_590_; uint8_t v_isSharedCheck_594_; 
v_isSharedCheck_594_ = !lean_is_exclusive(v___x_587_);
if (v_isSharedCheck_594_ == 0)
{
lean_object* v_unused_595_; 
v_unused_595_ = lean_ctor_get(v___x_587_, 0);
lean_dec(v_unused_595_);
v___x_589_ = v___x_587_;
v_isShared_590_ = v_isSharedCheck_594_;
goto v_resetjp_588_;
}
else
{
lean_dec(v___x_587_);
v___x_589_ = lean_box(0);
v_isShared_590_ = v_isSharedCheck_594_;
goto v_resetjp_588_;
}
v_resetjp_588_:
{
lean_object* v___x_592_; 
if (v_isShared_590_ == 0)
{
lean_ctor_set(v___x_589_, 0, v_a_585_);
v___x_592_ = v___x_589_;
goto v_reusejp_591_;
}
else
{
lean_object* v_reuseFailAlloc_593_; 
v_reuseFailAlloc_593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_593_, 0, v_a_585_);
v___x_592_ = v_reuseFailAlloc_593_;
goto v_reusejp_591_;
}
v_reusejp_591_:
{
return v___x_592_;
}
}
}
else
{
lean_object* v_a_596_; lean_object* v___x_598_; uint8_t v_isShared_599_; uint8_t v_isSharedCheck_603_; 
lean_dec(v_a_585_);
v_a_596_ = lean_ctor_get(v___x_587_, 0);
v_isSharedCheck_603_ = !lean_is_exclusive(v___x_587_);
if (v_isSharedCheck_603_ == 0)
{
v___x_598_ = v___x_587_;
v_isShared_599_ = v_isSharedCheck_603_;
goto v_resetjp_597_;
}
else
{
lean_inc(v_a_596_);
lean_dec(v___x_587_);
v___x_598_ = lean_box(0);
v_isShared_599_ = v_isSharedCheck_603_;
goto v_resetjp_597_;
}
v_resetjp_597_:
{
lean_object* v___x_601_; 
if (v_isShared_599_ == 0)
{
v___x_601_ = v___x_598_;
goto v_reusejp_600_;
}
else
{
lean_object* v_reuseFailAlloc_602_; 
v_reuseFailAlloc_602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_602_, 0, v_a_596_);
v___x_601_ = v_reuseFailAlloc_602_;
goto v_reusejp_600_;
}
v_reusejp_600_:
{
return v___x_601_;
}
}
}
}
else
{
return v___y_584_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isIntCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__1_spec__2___boxed(lean_object* v___y_672_, lean_object* v___y_673_, lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_, lean_object* v___y_677_, lean_object* v___y_678_, lean_object* v___y_679_, lean_object* v___y_680_, lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_){
_start:
{
lean_object* v_res_684_; 
v_res_684_ = l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isIntCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__1_spec__2(v___y_672_, v___y_673_, v___y_674_, v___y_675_, v___y_676_, v___y_677_, v___y_678_, v___y_679_, v___y_680_, v___y_681_, v___y_682_);
lean_dec(v___y_682_);
lean_dec_ref(v___y_681_);
lean_dec(v___y_680_);
lean_dec_ref(v___y_679_);
lean_dec(v___y_678_);
lean_dec_ref(v___y_677_);
lean_dec(v___y_676_);
lean_dec_ref(v___y_675_);
lean_dec(v___y_674_);
lean_dec(v___y_673_);
lean_dec_ref(v___y_672_);
return v_res_684_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_isIntCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__1(lean_object* v_inst_685_, lean_object* v___y_686_, lean_object* v___y_687_, lean_object* v___y_688_, lean_object* v___y_689_, lean_object* v___y_690_, lean_object* v___y_691_, lean_object* v___y_692_, lean_object* v___y_693_, lean_object* v___y_694_, lean_object* v___y_695_, lean_object* v___y_696_){
_start:
{
lean_object* v___x_698_; 
v___x_698_ = l_Lean_Meta_Grind_Arith_CommRing_getIntCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isIntCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__1_spec__2(v___y_686_, v___y_687_, v___y_688_, v___y_689_, v___y_690_, v___y_691_, v___y_692_, v___y_693_, v___y_694_, v___y_695_, v___y_696_);
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
lean_object* v___x_703_; size_t v___x_704_; size_t v___x_705_; uint8_t v___x_706_; lean_object* v___x_707_; lean_object* v___x_709_; 
v___x_703_ = l_Lean_Expr_appArg_x21(v_a_699_);
lean_dec(v_a_699_);
v___x_704_ = lean_ptr_addr(v___x_703_);
lean_dec_ref(v___x_703_);
v___x_705_ = lean_ptr_addr(v_inst_685_);
v___x_706_ = lean_usize_dec_eq(v___x_704_, v___x_705_);
v___x_707_ = lean_box(v___x_706_);
if (v_isShared_702_ == 0)
{
lean_ctor_set(v___x_701_, 0, v___x_707_);
v___x_709_ = v___x_701_;
goto v_reusejp_708_;
}
else
{
lean_object* v_reuseFailAlloc_710_; 
v_reuseFailAlloc_710_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_710_, 0, v___x_707_);
v___x_709_ = v_reuseFailAlloc_710_;
goto v_reusejp_708_;
}
v_reusejp_708_:
{
return v___x_709_;
}
}
}
else
{
lean_object* v_a_712_; lean_object* v___x_714_; uint8_t v_isShared_715_; uint8_t v_isSharedCheck_719_; 
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_isIntCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__1___boxed(lean_object* v_inst_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_, lean_object* v___y_724_, lean_object* v___y_725_, lean_object* v___y_726_, lean_object* v___y_727_, lean_object* v___y_728_, lean_object* v___y_729_, lean_object* v___y_730_, lean_object* v___y_731_, lean_object* v___y_732_){
_start:
{
lean_object* v_res_733_; 
v_res_733_ = l_Lean_Meta_Grind_Arith_CommRing_isIntCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__1(v_inst_720_, v___y_721_, v___y_722_, v___y_723_, v___y_724_, v___y_725_, v___y_726_, v___y_727_, v___y_728_, v___y_729_, v___y_730_, v___y_731_);
lean_dec(v___y_731_);
lean_dec_ref(v___y_730_);
lean_dec(v___y_729_);
lean_dec_ref(v___y_728_);
lean_dec(v___y_727_);
lean_dec_ref(v___y_726_);
lean_dec(v___y_725_);
lean_dec_ref(v___y_724_);
lean_dec(v___y_723_);
lean_dec(v___y_722_);
lean_dec_ref(v___y_721_);
lean_dec_ref(v_inst_720_);
return v_res_733_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isNatCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__2_spec__4___lam__0(lean_object* v_a_734_, lean_object* v_s_735_){
_start:
{
lean_object* v_toRing_736_; lean_object* v_invFn_x3f_737_; lean_object* v_semiringId_x3f_738_; lean_object* v_commSemiringInst_739_; lean_object* v_commRingInst_740_; lean_object* v_noZeroDivInst_x3f_741_; lean_object* v_fieldInst_x3f_742_; lean_object* v_powIdentityInst_x3f_743_; lean_object* v_denoteEntries_744_; lean_object* v_nextId_745_; lean_object* v_steps_746_; lean_object* v_queue_747_; lean_object* v_basis_748_; lean_object* v_diseqs_749_; uint8_t v_recheck_750_; lean_object* v_invSet_751_; lean_object* v_powIdentityVarCount_752_; lean_object* v_numEq0_x3f_753_; uint8_t v_numEq0Updated_754_; lean_object* v___x_756_; uint8_t v_isShared_757_; uint8_t v_isSharedCheck_786_; 
v_toRing_736_ = lean_ctor_get(v_s_735_, 0);
v_invFn_x3f_737_ = lean_ctor_get(v_s_735_, 1);
v_semiringId_x3f_738_ = lean_ctor_get(v_s_735_, 2);
v_commSemiringInst_739_ = lean_ctor_get(v_s_735_, 3);
v_commRingInst_740_ = lean_ctor_get(v_s_735_, 4);
v_noZeroDivInst_x3f_741_ = lean_ctor_get(v_s_735_, 5);
v_fieldInst_x3f_742_ = lean_ctor_get(v_s_735_, 6);
v_powIdentityInst_x3f_743_ = lean_ctor_get(v_s_735_, 7);
v_denoteEntries_744_ = lean_ctor_get(v_s_735_, 8);
v_nextId_745_ = lean_ctor_get(v_s_735_, 9);
v_steps_746_ = lean_ctor_get(v_s_735_, 10);
v_queue_747_ = lean_ctor_get(v_s_735_, 11);
v_basis_748_ = lean_ctor_get(v_s_735_, 12);
v_diseqs_749_ = lean_ctor_get(v_s_735_, 13);
v_recheck_750_ = lean_ctor_get_uint8(v_s_735_, sizeof(void*)*17);
v_invSet_751_ = lean_ctor_get(v_s_735_, 14);
v_powIdentityVarCount_752_ = lean_ctor_get(v_s_735_, 15);
v_numEq0_x3f_753_ = lean_ctor_get(v_s_735_, 16);
v_numEq0Updated_754_ = lean_ctor_get_uint8(v_s_735_, sizeof(void*)*17 + 1);
v_isSharedCheck_786_ = !lean_is_exclusive(v_s_735_);
if (v_isSharedCheck_786_ == 0)
{
v___x_756_ = v_s_735_;
v_isShared_757_ = v_isSharedCheck_786_;
goto v_resetjp_755_;
}
else
{
lean_inc(v_numEq0_x3f_753_);
lean_inc(v_powIdentityVarCount_752_);
lean_inc(v_invSet_751_);
lean_inc(v_diseqs_749_);
lean_inc(v_basis_748_);
lean_inc(v_queue_747_);
lean_inc(v_steps_746_);
lean_inc(v_nextId_745_);
lean_inc(v_denoteEntries_744_);
lean_inc(v_powIdentityInst_x3f_743_);
lean_inc(v_fieldInst_x3f_742_);
lean_inc(v_noZeroDivInst_x3f_741_);
lean_inc(v_commRingInst_740_);
lean_inc(v_commSemiringInst_739_);
lean_inc(v_semiringId_x3f_738_);
lean_inc(v_invFn_x3f_737_);
lean_inc(v_toRing_736_);
lean_dec(v_s_735_);
v___x_756_ = lean_box(0);
v_isShared_757_ = v_isSharedCheck_786_;
goto v_resetjp_755_;
}
v_resetjp_755_:
{
lean_object* v_id_758_; lean_object* v_type_759_; lean_object* v_u_760_; lean_object* v_ringInst_761_; lean_object* v_semiringInst_762_; lean_object* v_charInst_x3f_763_; lean_object* v_addFn_x3f_764_; lean_object* v_mulFn_x3f_765_; lean_object* v_subFn_x3f_766_; lean_object* v_negFn_x3f_767_; lean_object* v_powFn_x3f_768_; lean_object* v_intCastFn_x3f_769_; lean_object* v_one_x3f_770_; lean_object* v_vars_771_; lean_object* v_varMap_772_; lean_object* v_denote_773_; lean_object* v___x_775_; uint8_t v_isShared_776_; uint8_t v_isSharedCheck_784_; 
v_id_758_ = lean_ctor_get(v_toRing_736_, 0);
v_type_759_ = lean_ctor_get(v_toRing_736_, 1);
v_u_760_ = lean_ctor_get(v_toRing_736_, 2);
v_ringInst_761_ = lean_ctor_get(v_toRing_736_, 3);
v_semiringInst_762_ = lean_ctor_get(v_toRing_736_, 4);
v_charInst_x3f_763_ = lean_ctor_get(v_toRing_736_, 5);
v_addFn_x3f_764_ = lean_ctor_get(v_toRing_736_, 6);
v_mulFn_x3f_765_ = lean_ctor_get(v_toRing_736_, 7);
v_subFn_x3f_766_ = lean_ctor_get(v_toRing_736_, 8);
v_negFn_x3f_767_ = lean_ctor_get(v_toRing_736_, 9);
v_powFn_x3f_768_ = lean_ctor_get(v_toRing_736_, 10);
v_intCastFn_x3f_769_ = lean_ctor_get(v_toRing_736_, 11);
v_one_x3f_770_ = lean_ctor_get(v_toRing_736_, 13);
v_vars_771_ = lean_ctor_get(v_toRing_736_, 14);
v_varMap_772_ = lean_ctor_get(v_toRing_736_, 15);
v_denote_773_ = lean_ctor_get(v_toRing_736_, 16);
v_isSharedCheck_784_ = !lean_is_exclusive(v_toRing_736_);
if (v_isSharedCheck_784_ == 0)
{
lean_object* v_unused_785_; 
v_unused_785_ = lean_ctor_get(v_toRing_736_, 12);
lean_dec(v_unused_785_);
v___x_775_ = v_toRing_736_;
v_isShared_776_ = v_isSharedCheck_784_;
goto v_resetjp_774_;
}
else
{
lean_inc(v_denote_773_);
lean_inc(v_varMap_772_);
lean_inc(v_vars_771_);
lean_inc(v_one_x3f_770_);
lean_inc(v_intCastFn_x3f_769_);
lean_inc(v_powFn_x3f_768_);
lean_inc(v_negFn_x3f_767_);
lean_inc(v_subFn_x3f_766_);
lean_inc(v_mulFn_x3f_765_);
lean_inc(v_addFn_x3f_764_);
lean_inc(v_charInst_x3f_763_);
lean_inc(v_semiringInst_762_);
lean_inc(v_ringInst_761_);
lean_inc(v_u_760_);
lean_inc(v_type_759_);
lean_inc(v_id_758_);
lean_dec(v_toRing_736_);
v___x_775_ = lean_box(0);
v_isShared_776_ = v_isSharedCheck_784_;
goto v_resetjp_774_;
}
v_resetjp_774_:
{
lean_object* v___x_777_; lean_object* v___x_779_; 
v___x_777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_777_, 0, v_a_734_);
if (v_isShared_776_ == 0)
{
lean_ctor_set(v___x_775_, 12, v___x_777_);
v___x_779_ = v___x_775_;
goto v_reusejp_778_;
}
else
{
lean_object* v_reuseFailAlloc_783_; 
v_reuseFailAlloc_783_ = lean_alloc_ctor(0, 17, 0);
lean_ctor_set(v_reuseFailAlloc_783_, 0, v_id_758_);
lean_ctor_set(v_reuseFailAlloc_783_, 1, v_type_759_);
lean_ctor_set(v_reuseFailAlloc_783_, 2, v_u_760_);
lean_ctor_set(v_reuseFailAlloc_783_, 3, v_ringInst_761_);
lean_ctor_set(v_reuseFailAlloc_783_, 4, v_semiringInst_762_);
lean_ctor_set(v_reuseFailAlloc_783_, 5, v_charInst_x3f_763_);
lean_ctor_set(v_reuseFailAlloc_783_, 6, v_addFn_x3f_764_);
lean_ctor_set(v_reuseFailAlloc_783_, 7, v_mulFn_x3f_765_);
lean_ctor_set(v_reuseFailAlloc_783_, 8, v_subFn_x3f_766_);
lean_ctor_set(v_reuseFailAlloc_783_, 9, v_negFn_x3f_767_);
lean_ctor_set(v_reuseFailAlloc_783_, 10, v_powFn_x3f_768_);
lean_ctor_set(v_reuseFailAlloc_783_, 11, v_intCastFn_x3f_769_);
lean_ctor_set(v_reuseFailAlloc_783_, 12, v___x_777_);
lean_ctor_set(v_reuseFailAlloc_783_, 13, v_one_x3f_770_);
lean_ctor_set(v_reuseFailAlloc_783_, 14, v_vars_771_);
lean_ctor_set(v_reuseFailAlloc_783_, 15, v_varMap_772_);
lean_ctor_set(v_reuseFailAlloc_783_, 16, v_denote_773_);
v___x_779_ = v_reuseFailAlloc_783_;
goto v_reusejp_778_;
}
v_reusejp_778_:
{
lean_object* v___x_781_; 
if (v_isShared_757_ == 0)
{
lean_ctor_set(v___x_756_, 0, v___x_779_);
v___x_781_ = v___x_756_;
goto v_reusejp_780_;
}
else
{
lean_object* v_reuseFailAlloc_782_; 
v_reuseFailAlloc_782_ = lean_alloc_ctor(0, 17, 2);
lean_ctor_set(v_reuseFailAlloc_782_, 0, v___x_779_);
lean_ctor_set(v_reuseFailAlloc_782_, 1, v_invFn_x3f_737_);
lean_ctor_set(v_reuseFailAlloc_782_, 2, v_semiringId_x3f_738_);
lean_ctor_set(v_reuseFailAlloc_782_, 3, v_commSemiringInst_739_);
lean_ctor_set(v_reuseFailAlloc_782_, 4, v_commRingInst_740_);
lean_ctor_set(v_reuseFailAlloc_782_, 5, v_noZeroDivInst_x3f_741_);
lean_ctor_set(v_reuseFailAlloc_782_, 6, v_fieldInst_x3f_742_);
lean_ctor_set(v_reuseFailAlloc_782_, 7, v_powIdentityInst_x3f_743_);
lean_ctor_set(v_reuseFailAlloc_782_, 8, v_denoteEntries_744_);
lean_ctor_set(v_reuseFailAlloc_782_, 9, v_nextId_745_);
lean_ctor_set(v_reuseFailAlloc_782_, 10, v_steps_746_);
lean_ctor_set(v_reuseFailAlloc_782_, 11, v_queue_747_);
lean_ctor_set(v_reuseFailAlloc_782_, 12, v_basis_748_);
lean_ctor_set(v_reuseFailAlloc_782_, 13, v_diseqs_749_);
lean_ctor_set(v_reuseFailAlloc_782_, 14, v_invSet_751_);
lean_ctor_set(v_reuseFailAlloc_782_, 15, v_powIdentityVarCount_752_);
lean_ctor_set(v_reuseFailAlloc_782_, 16, v_numEq0_x3f_753_);
lean_ctor_set_uint8(v_reuseFailAlloc_782_, sizeof(void*)*17, v_recheck_750_);
lean_ctor_set_uint8(v_reuseFailAlloc_782_, sizeof(void*)*17 + 1, v_numEq0Updated_754_);
v___x_781_ = v_reuseFailAlloc_782_;
goto v_reusejp_780_;
}
v_reusejp_780_:
{
return v___x_781_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_getNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isNatCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__2_spec__4_spec__6___redArg(lean_object* v_u_795_, lean_object* v_type_796_, lean_object* v_semiringInst_797_, lean_object* v___y_798_, lean_object* v___y_799_, lean_object* v___y_800_, lean_object* v___y_801_, lean_object* v___y_802_, lean_object* v___y_803_){
_start:
{
lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v_inst_x27_809_; lean_object* v_inst_811_; lean_object* v___y_812_; lean_object* v___y_813_; lean_object* v___y_814_; lean_object* v___y_815_; lean_object* v___y_816_; lean_object* v___y_817_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v_instType_826_; lean_object* v___x_827_; 
v___x_805_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_getNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isNatCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__2_spec__4_spec__6___redArg___closed__1));
v___x_806_ = lean_box(0);
v___x_807_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_807_, 0, v_u_795_);
lean_ctor_set(v___x_807_, 1, v___x_806_);
lean_inc_ref_n(v___x_807_, 2);
v___x_808_ = l_Lean_mkConst(v___x_805_, v___x_807_);
lean_inc_ref_n(v_type_796_, 2);
v_inst_x27_809_ = l_Lean_mkAppB(v___x_808_, v_type_796_, v_semiringInst_797_);
v___x_824_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_getNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isNatCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__2_spec__4_spec__6___redArg___closed__2));
v___x_825_ = l_Lean_mkConst(v___x_824_, v___x_807_);
v_instType_826_ = l_Lean_Expr_app___override(v___x_825_, v_type_796_);
v___x_827_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v_instType_826_, v___y_799_, v___y_800_, v___y_801_, v___y_802_, v___y_803_);
if (lean_obj_tag(v___x_827_) == 0)
{
lean_object* v_a_828_; 
v_a_828_ = lean_ctor_get(v___x_827_, 0);
lean_inc(v_a_828_);
lean_dec_ref_known(v___x_827_, 1);
if (lean_obj_tag(v_a_828_) == 0)
{
v_inst_811_ = v_inst_x27_809_;
v___y_812_ = v___y_798_;
v___y_813_ = v___y_799_;
v___y_814_ = v___y_800_;
v___y_815_ = v___y_801_;
v___y_816_ = v___y_802_;
v___y_817_ = v___y_803_;
goto v___jp_810_;
}
else
{
lean_object* v_val_829_; lean_object* v___x_830_; lean_object* v___x_831_; 
v_val_829_ = lean_ctor_get(v_a_828_, 0);
lean_inc_n(v_val_829_, 2);
lean_dec_ref_known(v_a_828_, 1);
v___x_830_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__5));
v___x_831_ = l_Lean_Meta_Grind_Arith_CommRing_checkInst(v___x_830_, v_val_829_, v_inst_x27_809_, v___y_800_, v___y_801_, v___y_802_, v___y_803_);
if (lean_obj_tag(v___x_831_) == 0)
{
lean_dec_ref_known(v___x_831_, 1);
v_inst_811_ = v_val_829_;
v___y_812_ = v___y_798_;
v___y_813_ = v___y_799_;
v___y_814_ = v___y_800_;
v___y_815_ = v___y_801_;
v___y_816_ = v___y_802_;
v___y_817_ = v___y_803_;
goto v___jp_810_;
}
else
{
lean_object* v_a_832_; lean_object* v___x_834_; uint8_t v_isShared_835_; uint8_t v_isSharedCheck_839_; 
lean_dec(v_val_829_);
lean_dec_ref_known(v___x_807_, 2);
lean_dec_ref(v_type_796_);
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
lean_dec_ref(v_inst_x27_809_);
lean_dec_ref_known(v___x_807_, 2);
lean_dec_ref(v_type_796_);
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
v___jp_810_:
{
lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; 
v___x_818_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__5));
v___x_819_ = l_Lean_mkConst(v___x_818_, v___x_807_);
v___x_820_ = l_Lean_mkAppB(v___x_819_, v_type_796_, v_inst_811_);
v___x_821_ = l_Lean_Meta_Sym_canon(v___x_820_, v___y_812_, v___y_813_, v___y_814_, v___y_815_, v___y_816_, v___y_817_);
if (lean_obj_tag(v___x_821_) == 0)
{
lean_object* v_a_822_; lean_object* v___x_823_; 
v_a_822_ = lean_ctor_get(v___x_821_, 0);
lean_inc(v_a_822_);
lean_dec_ref_known(v___x_821_, 1);
v___x_823_ = l_Lean_Meta_Sym_shareCommon(v_a_822_, v___y_812_, v___y_813_, v___y_814_, v___y_815_, v___y_816_, v___y_817_);
return v___x_823_;
}
else
{
return v___x_821_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_getNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isNatCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__2_spec__4_spec__6___redArg___boxed(lean_object* v_u_848_, lean_object* v_type_849_, lean_object* v_semiringInst_850_, lean_object* v___y_851_, lean_object* v___y_852_, lean_object* v___y_853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_, lean_object* v___y_857_){
_start:
{
lean_object* v_res_858_; 
v_res_858_ = l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_getNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isNatCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__2_spec__4_spec__6___redArg(v_u_848_, v_type_849_, v_semiringInst_850_, v___y_851_, v___y_852_, v___y_853_, v___y_854_, v___y_855_, v___y_856_);
lean_dec(v___y_856_);
lean_dec_ref(v___y_855_);
lean_dec(v___y_854_);
lean_dec_ref(v___y_853_);
lean_dec(v___y_852_);
lean_dec_ref(v___y_851_);
return v_res_858_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isNatCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__2_spec__4(lean_object* v___y_859_, lean_object* v___y_860_, lean_object* v___y_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_, lean_object* v___y_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_){
_start:
{
lean_object* v___x_871_; 
v___x_871_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v___y_859_, v___y_860_, v___y_861_, v___y_862_, v___y_863_, v___y_864_, v___y_865_, v___y_866_, v___y_867_, v___y_868_, v___y_869_);
if (lean_obj_tag(v___x_871_) == 0)
{
lean_object* v_a_872_; lean_object* v___x_874_; uint8_t v_isShared_875_; uint8_t v_isSharedCheck_905_; 
v_a_872_ = lean_ctor_get(v___x_871_, 0);
v_isSharedCheck_905_ = !lean_is_exclusive(v___x_871_);
if (v_isSharedCheck_905_ == 0)
{
v___x_874_ = v___x_871_;
v_isShared_875_ = v_isSharedCheck_905_;
goto v_resetjp_873_;
}
else
{
lean_inc(v_a_872_);
lean_dec(v___x_871_);
v___x_874_ = lean_box(0);
v_isShared_875_ = v_isSharedCheck_905_;
goto v_resetjp_873_;
}
v_resetjp_873_:
{
lean_object* v_toRing_876_; lean_object* v_natCastFn_x3f_877_; 
v_toRing_876_ = lean_ctor_get(v_a_872_, 0);
lean_inc_ref(v_toRing_876_);
lean_dec(v_a_872_);
v_natCastFn_x3f_877_ = lean_ctor_get(v_toRing_876_, 12);
if (lean_obj_tag(v_natCastFn_x3f_877_) == 1)
{
lean_object* v_val_878_; lean_object* v___x_880_; 
lean_inc_ref(v_natCastFn_x3f_877_);
lean_dec_ref(v_toRing_876_);
v_val_878_ = lean_ctor_get(v_natCastFn_x3f_877_, 0);
lean_inc(v_val_878_);
lean_dec_ref_known(v_natCastFn_x3f_877_, 1);
if (v_isShared_875_ == 0)
{
lean_ctor_set(v___x_874_, 0, v_val_878_);
v___x_880_ = v___x_874_;
goto v_reusejp_879_;
}
else
{
lean_object* v_reuseFailAlloc_881_; 
v_reuseFailAlloc_881_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_881_, 0, v_val_878_);
v___x_880_ = v_reuseFailAlloc_881_;
goto v_reusejp_879_;
}
v_reusejp_879_:
{
return v___x_880_;
}
}
else
{
lean_object* v_type_882_; lean_object* v_u_883_; lean_object* v_semiringInst_884_; lean_object* v___x_885_; 
lean_del_object(v___x_874_);
v_type_882_ = lean_ctor_get(v_toRing_876_, 1);
lean_inc_ref(v_type_882_);
v_u_883_ = lean_ctor_get(v_toRing_876_, 2);
lean_inc(v_u_883_);
v_semiringInst_884_ = lean_ctor_get(v_toRing_876_, 4);
lean_inc_ref(v_semiringInst_884_);
lean_dec_ref(v_toRing_876_);
v___x_885_ = l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_getNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isNatCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__2_spec__4_spec__6___redArg(v_u_883_, v_type_882_, v_semiringInst_884_, v___y_864_, v___y_865_, v___y_866_, v___y_867_, v___y_868_, v___y_869_);
if (lean_obj_tag(v___x_885_) == 0)
{
lean_object* v_a_886_; lean_object* v___f_887_; lean_object* v___x_888_; 
v_a_886_ = lean_ctor_get(v___x_885_, 0);
lean_inc_n(v_a_886_, 2);
lean_dec_ref_known(v___x_885_, 1);
v___f_887_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isNatCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__2_spec__4___lam__0), 2, 1);
lean_closure_set(v___f_887_, 0, v_a_886_);
v___x_888_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(v___f_887_, v___y_859_, v___y_860_);
if (lean_obj_tag(v___x_888_) == 0)
{
lean_object* v___x_890_; uint8_t v_isShared_891_; uint8_t v_isSharedCheck_895_; 
v_isSharedCheck_895_ = !lean_is_exclusive(v___x_888_);
if (v_isSharedCheck_895_ == 0)
{
lean_object* v_unused_896_; 
v_unused_896_ = lean_ctor_get(v___x_888_, 0);
lean_dec(v_unused_896_);
v___x_890_ = v___x_888_;
v_isShared_891_ = v_isSharedCheck_895_;
goto v_resetjp_889_;
}
else
{
lean_dec(v___x_888_);
v___x_890_ = lean_box(0);
v_isShared_891_ = v_isSharedCheck_895_;
goto v_resetjp_889_;
}
v_resetjp_889_:
{
lean_object* v___x_893_; 
if (v_isShared_891_ == 0)
{
lean_ctor_set(v___x_890_, 0, v_a_886_);
v___x_893_ = v___x_890_;
goto v_reusejp_892_;
}
else
{
lean_object* v_reuseFailAlloc_894_; 
v_reuseFailAlloc_894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_894_, 0, v_a_886_);
v___x_893_ = v_reuseFailAlloc_894_;
goto v_reusejp_892_;
}
v_reusejp_892_:
{
return v___x_893_;
}
}
}
else
{
lean_object* v_a_897_; lean_object* v___x_899_; uint8_t v_isShared_900_; uint8_t v_isSharedCheck_904_; 
lean_dec(v_a_886_);
v_a_897_ = lean_ctor_get(v___x_888_, 0);
v_isSharedCheck_904_ = !lean_is_exclusive(v___x_888_);
if (v_isSharedCheck_904_ == 0)
{
v___x_899_ = v___x_888_;
v_isShared_900_ = v_isSharedCheck_904_;
goto v_resetjp_898_;
}
else
{
lean_inc(v_a_897_);
lean_dec(v___x_888_);
v___x_899_ = lean_box(0);
v_isShared_900_ = v_isSharedCheck_904_;
goto v_resetjp_898_;
}
v_resetjp_898_:
{
lean_object* v___x_902_; 
if (v_isShared_900_ == 0)
{
v___x_902_ = v___x_899_;
goto v_reusejp_901_;
}
else
{
lean_object* v_reuseFailAlloc_903_; 
v_reuseFailAlloc_903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_903_, 0, v_a_897_);
v___x_902_ = v_reuseFailAlloc_903_;
goto v_reusejp_901_;
}
v_reusejp_901_:
{
return v___x_902_;
}
}
}
}
else
{
return v___x_885_;
}
}
}
}
else
{
lean_object* v_a_906_; lean_object* v___x_908_; uint8_t v_isShared_909_; uint8_t v_isSharedCheck_913_; 
v_a_906_ = lean_ctor_get(v___x_871_, 0);
v_isSharedCheck_913_ = !lean_is_exclusive(v___x_871_);
if (v_isSharedCheck_913_ == 0)
{
v___x_908_ = v___x_871_;
v_isShared_909_ = v_isSharedCheck_913_;
goto v_resetjp_907_;
}
else
{
lean_inc(v_a_906_);
lean_dec(v___x_871_);
v___x_908_ = lean_box(0);
v_isShared_909_ = v_isSharedCheck_913_;
goto v_resetjp_907_;
}
v_resetjp_907_:
{
lean_object* v___x_911_; 
if (v_isShared_909_ == 0)
{
v___x_911_ = v___x_908_;
goto v_reusejp_910_;
}
else
{
lean_object* v_reuseFailAlloc_912_; 
v_reuseFailAlloc_912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_912_, 0, v_a_906_);
v___x_911_ = v_reuseFailAlloc_912_;
goto v_reusejp_910_;
}
v_reusejp_910_:
{
return v___x_911_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isNatCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__2_spec__4___boxed(lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_){
_start:
{
lean_object* v_res_926_; 
v_res_926_ = l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isNatCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__2_spec__4(v___y_914_, v___y_915_, v___y_916_, v___y_917_, v___y_918_, v___y_919_, v___y_920_, v___y_921_, v___y_922_, v___y_923_, v___y_924_);
lean_dec(v___y_924_);
lean_dec_ref(v___y_923_);
lean_dec(v___y_922_);
lean_dec_ref(v___y_921_);
lean_dec(v___y_920_);
lean_dec_ref(v___y_919_);
lean_dec(v___y_918_);
lean_dec_ref(v___y_917_);
lean_dec(v___y_916_);
lean_dec(v___y_915_);
lean_dec_ref(v___y_914_);
return v_res_926_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_isNatCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__2(lean_object* v_inst_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_){
_start:
{
lean_object* v___x_940_; 
v___x_940_ = l_Lean_Meta_Grind_Arith_CommRing_getNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isNatCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__2_spec__4(v___y_928_, v___y_929_, v___y_930_, v___y_931_, v___y_932_, v___y_933_, v___y_934_, v___y_935_, v___y_936_, v___y_937_, v___y_938_);
if (lean_obj_tag(v___x_940_) == 0)
{
lean_object* v_a_941_; lean_object* v___x_943_; uint8_t v_isShared_944_; uint8_t v_isSharedCheck_953_; 
v_a_941_ = lean_ctor_get(v___x_940_, 0);
v_isSharedCheck_953_ = !lean_is_exclusive(v___x_940_);
if (v_isSharedCheck_953_ == 0)
{
v___x_943_ = v___x_940_;
v_isShared_944_ = v_isSharedCheck_953_;
goto v_resetjp_942_;
}
else
{
lean_inc(v_a_941_);
lean_dec(v___x_940_);
v___x_943_ = lean_box(0);
v_isShared_944_ = v_isSharedCheck_953_;
goto v_resetjp_942_;
}
v_resetjp_942_:
{
lean_object* v___x_945_; size_t v___x_946_; size_t v___x_947_; uint8_t v___x_948_; lean_object* v___x_949_; lean_object* v___x_951_; 
v___x_945_ = l_Lean_Expr_appArg_x21(v_a_941_);
lean_dec(v_a_941_);
v___x_946_ = lean_ptr_addr(v___x_945_);
lean_dec_ref(v___x_945_);
v___x_947_ = lean_ptr_addr(v_inst_927_);
v___x_948_ = lean_usize_dec_eq(v___x_946_, v___x_947_);
v___x_949_ = lean_box(v___x_948_);
if (v_isShared_944_ == 0)
{
lean_ctor_set(v___x_943_, 0, v___x_949_);
v___x_951_ = v___x_943_;
goto v_reusejp_950_;
}
else
{
lean_object* v_reuseFailAlloc_952_; 
v_reuseFailAlloc_952_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_952_, 0, v___x_949_);
v___x_951_ = v_reuseFailAlloc_952_;
goto v_reusejp_950_;
}
v_reusejp_950_:
{
return v___x_951_;
}
}
}
else
{
lean_object* v_a_954_; lean_object* v___x_956_; uint8_t v_isShared_957_; uint8_t v_isSharedCheck_961_; 
v_a_954_ = lean_ctor_get(v___x_940_, 0);
v_isSharedCheck_961_ = !lean_is_exclusive(v___x_940_);
if (v_isSharedCheck_961_ == 0)
{
v___x_956_ = v___x_940_;
v_isShared_957_ = v_isSharedCheck_961_;
goto v_resetjp_955_;
}
else
{
lean_inc(v_a_954_);
lean_dec(v___x_940_);
v___x_956_ = lean_box(0);
v_isShared_957_ = v_isSharedCheck_961_;
goto v_resetjp_955_;
}
v_resetjp_955_:
{
lean_object* v___x_959_; 
if (v_isShared_957_ == 0)
{
v___x_959_ = v___x_956_;
goto v_reusejp_958_;
}
else
{
lean_object* v_reuseFailAlloc_960_; 
v_reuseFailAlloc_960_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_960_, 0, v_a_954_);
v___x_959_ = v_reuseFailAlloc_960_;
goto v_reusejp_958_;
}
v_reusejp_958_:
{
return v___x_959_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_isNatCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__2___boxed(lean_object* v_inst_962_, lean_object* v___y_963_, lean_object* v___y_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_){
_start:
{
lean_object* v_res_975_; 
v_res_975_ = l_Lean_Meta_Grind_Arith_CommRing_isNatCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__2(v_inst_962_, v___y_963_, v___y_964_, v___y_965_, v___y_966_, v___y_967_, v___y_968_, v___y_969_, v___y_970_, v___y_971_, v___y_972_, v___y_973_);
lean_dec(v___y_973_);
lean_dec_ref(v___y_972_);
lean_dec(v___y_971_);
lean_dec_ref(v___y_970_);
lean_dec(v___y_969_);
lean_dec_ref(v___y_968_);
lean_dec(v___y_967_);
lean_dec_ref(v___y_966_);
lean_dec(v___y_965_);
lean_dec(v___y_964_);
lean_dec_ref(v___y_963_);
lean_dec_ref(v_inst_962_);
return v_res_975_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f(lean_object* v_e_976_, lean_object* v_a_977_, lean_object* v_a_978_, lean_object* v_a_979_, lean_object* v_a_980_, lean_object* v_a_981_, lean_object* v_a_982_, lean_object* v_a_983_, lean_object* v_a_984_, lean_object* v_a_985_, lean_object* v_a_986_, lean_object* v_a_987_){
_start:
{
lean_object* v___x_989_; 
v___x_989_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_976_, v_a_985_);
if (lean_obj_tag(v___x_989_) == 0)
{
lean_object* v_a_990_; lean_object* v___x_992_; uint8_t v_isShared_993_; uint8_t v_isSharedCheck_1153_; 
v_a_990_ = lean_ctor_get(v___x_989_, 0);
v_isSharedCheck_1153_ = !lean_is_exclusive(v___x_989_);
if (v_isSharedCheck_1153_ == 0)
{
v___x_992_ = v___x_989_;
v_isShared_993_ = v_isSharedCheck_1153_;
goto v_resetjp_991_;
}
else
{
lean_inc(v_a_990_);
lean_dec(v___x_989_);
v___x_992_ = lean_box(0);
v_isShared_993_ = v_isSharedCheck_1153_;
goto v_resetjp_991_;
}
v_resetjp_991_:
{
lean_object* v___x_999_; uint8_t v___x_1000_; 
v___x_999_ = l_Lean_Expr_cleanupAnnotations(v_a_990_);
v___x_1000_ = l_Lean_Expr_isApp(v___x_999_);
if (v___x_1000_ == 0)
{
lean_dec_ref(v___x_999_);
goto v___jp_994_;
}
else
{
lean_object* v_arg_1001_; lean_object* v___x_1002_; uint8_t v___x_1003_; 
v_arg_1001_ = lean_ctor_get(v___x_999_, 1);
lean_inc_ref(v_arg_1001_);
v___x_1002_ = l_Lean_Expr_appFnCleanup___redArg(v___x_999_);
v___x_1003_ = l_Lean_Expr_isApp(v___x_1002_);
if (v___x_1003_ == 0)
{
lean_dec_ref(v___x_1002_);
lean_dec_ref(v_arg_1001_);
goto v___jp_994_;
}
else
{
lean_object* v_arg_1004_; lean_object* v___x_1005_; uint8_t v___x_1006_; 
v_arg_1004_ = lean_ctor_get(v___x_1002_, 1);
lean_inc_ref(v_arg_1004_);
v___x_1005_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1002_);
v___x_1006_ = l_Lean_Expr_isApp(v___x_1005_);
if (v___x_1006_ == 0)
{
lean_dec_ref(v___x_1005_);
lean_dec_ref(v_arg_1004_);
lean_dec_ref(v_arg_1001_);
goto v___jp_994_;
}
else
{
lean_object* v___x_1007_; lean_object* v___x_1008_; uint8_t v___x_1009_; 
v___x_1007_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1005_);
v___x_1008_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__8));
v___x_1009_ = l_Lean_Expr_isConstOf(v___x_1007_, v___x_1008_);
if (v___x_1009_ == 0)
{
lean_object* v___x_1010_; uint8_t v___x_1011_; 
v___x_1010_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__5));
v___x_1011_ = l_Lean_Expr_isConstOf(v___x_1007_, v___x_1010_);
if (v___x_1011_ == 0)
{
lean_object* v___x_1012_; uint8_t v___x_1013_; 
v___x_1012_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__2));
v___x_1013_ = l_Lean_Expr_isConstOf(v___x_1007_, v___x_1012_);
if (v___x_1013_ == 0)
{
lean_object* v___x_1014_; uint8_t v___x_1015_; 
v___x_1014_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__11));
v___x_1015_ = l_Lean_Expr_isConstOf(v___x_1007_, v___x_1014_);
lean_dec_ref(v___x_1007_);
if (v___x_1015_ == 0)
{
lean_dec_ref(v_arg_1004_);
lean_dec_ref(v_arg_1001_);
goto v___jp_994_;
}
else
{
lean_object* v___x_1016_; 
lean_del_object(v___x_992_);
v___x_1016_ = l_Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0(v_arg_1004_, v_a_977_, v_a_978_, v_a_979_, v_a_980_, v_a_981_, v_a_982_, v_a_983_, v_a_984_, v_a_985_, v_a_986_, v_a_987_);
lean_dec_ref(v_arg_1004_);
if (lean_obj_tag(v___x_1016_) == 0)
{
lean_object* v_a_1017_; lean_object* v___x_1019_; uint8_t v_isShared_1020_; uint8_t v_isSharedCheck_1045_; 
v_a_1017_ = lean_ctor_get(v___x_1016_, 0);
v_isSharedCheck_1045_ = !lean_is_exclusive(v___x_1016_);
if (v_isSharedCheck_1045_ == 0)
{
v___x_1019_ = v___x_1016_;
v_isShared_1020_ = v_isSharedCheck_1045_;
goto v_resetjp_1018_;
}
else
{
lean_inc(v_a_1017_);
lean_dec(v___x_1016_);
v___x_1019_ = lean_box(0);
v_isShared_1020_ = v_isSharedCheck_1045_;
goto v_resetjp_1018_;
}
v_resetjp_1018_:
{
uint8_t v___x_1021_; 
v___x_1021_ = lean_unbox(v_a_1017_);
lean_dec(v_a_1017_);
if (v___x_1021_ == 0)
{
lean_object* v___x_1022_; lean_object* v___x_1024_; 
lean_dec_ref(v_arg_1001_);
v___x_1022_ = lean_box(0);
if (v_isShared_1020_ == 0)
{
lean_ctor_set(v___x_1019_, 0, v___x_1022_);
v___x_1024_ = v___x_1019_;
goto v_reusejp_1023_;
}
else
{
lean_object* v_reuseFailAlloc_1025_; 
v_reuseFailAlloc_1025_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1025_, 0, v___x_1022_);
v___x_1024_ = v_reuseFailAlloc_1025_;
goto v_reusejp_1023_;
}
v_reusejp_1023_:
{
return v___x_1024_;
}
}
else
{
lean_object* v___x_1026_; 
lean_del_object(v___x_1019_);
v___x_1026_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f(v_arg_1001_, v_a_977_, v_a_978_, v_a_979_, v_a_980_, v_a_981_, v_a_982_, v_a_983_, v_a_984_, v_a_985_, v_a_986_, v_a_987_);
if (lean_obj_tag(v___x_1026_) == 0)
{
lean_object* v_a_1027_; 
v_a_1027_ = lean_ctor_get(v___x_1026_, 0);
lean_inc(v_a_1027_);
if (lean_obj_tag(v_a_1027_) == 0)
{
return v___x_1026_;
}
else
{
lean_object* v___x_1029_; uint8_t v_isShared_1030_; uint8_t v_isSharedCheck_1043_; 
v_isSharedCheck_1043_ = !lean_is_exclusive(v___x_1026_);
if (v_isSharedCheck_1043_ == 0)
{
lean_object* v_unused_1044_; 
v_unused_1044_ = lean_ctor_get(v___x_1026_, 0);
lean_dec(v_unused_1044_);
v___x_1029_ = v___x_1026_;
v_isShared_1030_ = v_isSharedCheck_1043_;
goto v_resetjp_1028_;
}
else
{
lean_dec(v___x_1026_);
v___x_1029_ = lean_box(0);
v_isShared_1030_ = v_isSharedCheck_1043_;
goto v_resetjp_1028_;
}
v_resetjp_1028_:
{
lean_object* v_val_1031_; lean_object* v___x_1033_; uint8_t v_isShared_1034_; uint8_t v_isSharedCheck_1042_; 
v_val_1031_ = lean_ctor_get(v_a_1027_, 0);
v_isSharedCheck_1042_ = !lean_is_exclusive(v_a_1027_);
if (v_isSharedCheck_1042_ == 0)
{
v___x_1033_ = v_a_1027_;
v_isShared_1034_ = v_isSharedCheck_1042_;
goto v_resetjp_1032_;
}
else
{
lean_inc(v_val_1031_);
lean_dec(v_a_1027_);
v___x_1033_ = lean_box(0);
v_isShared_1034_ = v_isSharedCheck_1042_;
goto v_resetjp_1032_;
}
v_resetjp_1032_:
{
lean_object* v___x_1035_; lean_object* v___x_1037_; 
v___x_1035_ = lean_int_neg(v_val_1031_);
lean_dec(v_val_1031_);
if (v_isShared_1034_ == 0)
{
lean_ctor_set(v___x_1033_, 0, v___x_1035_);
v___x_1037_ = v___x_1033_;
goto v_reusejp_1036_;
}
else
{
lean_object* v_reuseFailAlloc_1041_; 
v_reuseFailAlloc_1041_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1041_, 0, v___x_1035_);
v___x_1037_ = v_reuseFailAlloc_1041_;
goto v_reusejp_1036_;
}
v_reusejp_1036_:
{
lean_object* v___x_1039_; 
if (v_isShared_1030_ == 0)
{
lean_ctor_set(v___x_1029_, 0, v___x_1037_);
v___x_1039_ = v___x_1029_;
goto v_reusejp_1038_;
}
else
{
lean_object* v_reuseFailAlloc_1040_; 
v_reuseFailAlloc_1040_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1040_, 0, v___x_1037_);
v___x_1039_ = v_reuseFailAlloc_1040_;
goto v_reusejp_1038_;
}
v_reusejp_1038_:
{
return v___x_1039_;
}
}
}
}
}
}
else
{
return v___x_1026_;
}
}
}
}
else
{
lean_object* v_a_1046_; lean_object* v___x_1048_; uint8_t v_isShared_1049_; uint8_t v_isSharedCheck_1053_; 
lean_dec_ref(v_arg_1001_);
v_a_1046_ = lean_ctor_get(v___x_1016_, 0);
v_isSharedCheck_1053_ = !lean_is_exclusive(v___x_1016_);
if (v_isSharedCheck_1053_ == 0)
{
v___x_1048_ = v___x_1016_;
v_isShared_1049_ = v_isSharedCheck_1053_;
goto v_resetjp_1047_;
}
else
{
lean_inc(v_a_1046_);
lean_dec(v___x_1016_);
v___x_1048_ = lean_box(0);
v_isShared_1049_ = v_isSharedCheck_1053_;
goto v_resetjp_1047_;
}
v_resetjp_1047_:
{
lean_object* v___x_1051_; 
if (v_isShared_1049_ == 0)
{
v___x_1051_ = v___x_1048_;
goto v_reusejp_1050_;
}
else
{
lean_object* v_reuseFailAlloc_1052_; 
v_reuseFailAlloc_1052_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1052_, 0, v_a_1046_);
v___x_1051_ = v_reuseFailAlloc_1052_;
goto v_reusejp_1050_;
}
v_reusejp_1050_:
{
return v___x_1051_;
}
}
}
}
}
else
{
lean_object* v___x_1054_; 
lean_dec_ref(v___x_1007_);
lean_del_object(v___x_992_);
v___x_1054_ = l_Lean_Meta_Grind_Arith_CommRing_isIntCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__1(v_arg_1004_, v_a_977_, v_a_978_, v_a_979_, v_a_980_, v_a_981_, v_a_982_, v_a_983_, v_a_984_, v_a_985_, v_a_986_, v_a_987_);
lean_dec_ref(v_arg_1004_);
if (lean_obj_tag(v___x_1054_) == 0)
{
lean_object* v_a_1055_; lean_object* v___x_1057_; uint8_t v_isShared_1058_; uint8_t v_isSharedCheck_1065_; 
v_a_1055_ = lean_ctor_get(v___x_1054_, 0);
v_isSharedCheck_1065_ = !lean_is_exclusive(v___x_1054_);
if (v_isSharedCheck_1065_ == 0)
{
v___x_1057_ = v___x_1054_;
v_isShared_1058_ = v_isSharedCheck_1065_;
goto v_resetjp_1056_;
}
else
{
lean_inc(v_a_1055_);
lean_dec(v___x_1054_);
v___x_1057_ = lean_box(0);
v_isShared_1058_ = v_isSharedCheck_1065_;
goto v_resetjp_1056_;
}
v_resetjp_1056_:
{
uint8_t v___x_1059_; 
v___x_1059_ = lean_unbox(v_a_1055_);
lean_dec(v_a_1055_);
if (v___x_1059_ == 0)
{
lean_object* v___x_1060_; lean_object* v___x_1062_; 
lean_dec_ref(v_arg_1001_);
v___x_1060_ = lean_box(0);
if (v_isShared_1058_ == 0)
{
lean_ctor_set(v___x_1057_, 0, v___x_1060_);
v___x_1062_ = v___x_1057_;
goto v_reusejp_1061_;
}
else
{
lean_object* v_reuseFailAlloc_1063_; 
v_reuseFailAlloc_1063_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1063_, 0, v___x_1060_);
v___x_1062_ = v_reuseFailAlloc_1063_;
goto v_reusejp_1061_;
}
v_reusejp_1061_:
{
return v___x_1062_;
}
}
else
{
lean_object* v___x_1064_; 
lean_del_object(v___x_1057_);
v___x_1064_ = l_Lean_Meta_getIntValue_x3f(v_arg_1001_, v_a_984_, v_a_985_, v_a_986_, v_a_987_);
return v___x_1064_;
}
}
}
else
{
lean_object* v_a_1066_; lean_object* v___x_1068_; uint8_t v_isShared_1069_; uint8_t v_isSharedCheck_1073_; 
lean_dec_ref(v_arg_1001_);
v_a_1066_ = lean_ctor_get(v___x_1054_, 0);
v_isSharedCheck_1073_ = !lean_is_exclusive(v___x_1054_);
if (v_isSharedCheck_1073_ == 0)
{
v___x_1068_ = v___x_1054_;
v_isShared_1069_ = v_isSharedCheck_1073_;
goto v_resetjp_1067_;
}
else
{
lean_inc(v_a_1066_);
lean_dec(v___x_1054_);
v___x_1068_ = lean_box(0);
v_isShared_1069_ = v_isSharedCheck_1073_;
goto v_resetjp_1067_;
}
v_resetjp_1067_:
{
lean_object* v___x_1071_; 
if (v_isShared_1069_ == 0)
{
v___x_1071_ = v___x_1068_;
goto v_reusejp_1070_;
}
else
{
lean_object* v_reuseFailAlloc_1072_; 
v_reuseFailAlloc_1072_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1072_, 0, v_a_1066_);
v___x_1071_ = v_reuseFailAlloc_1072_;
goto v_reusejp_1070_;
}
v_reusejp_1070_:
{
return v___x_1071_;
}
}
}
}
}
else
{
lean_object* v___x_1074_; 
lean_dec_ref(v___x_1007_);
lean_del_object(v___x_992_);
v___x_1074_ = l_Lean_Meta_Grind_Arith_CommRing_isNatCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__2(v_arg_1004_, v_a_977_, v_a_978_, v_a_979_, v_a_980_, v_a_981_, v_a_982_, v_a_983_, v_a_984_, v_a_985_, v_a_986_, v_a_987_);
lean_dec_ref(v_arg_1004_);
if (lean_obj_tag(v___x_1074_) == 0)
{
lean_object* v_a_1075_; lean_object* v___x_1077_; uint8_t v_isShared_1078_; uint8_t v_isSharedCheck_1114_; 
v_a_1075_ = lean_ctor_get(v___x_1074_, 0);
v_isSharedCheck_1114_ = !lean_is_exclusive(v___x_1074_);
if (v_isSharedCheck_1114_ == 0)
{
v___x_1077_ = v___x_1074_;
v_isShared_1078_ = v_isSharedCheck_1114_;
goto v_resetjp_1076_;
}
else
{
lean_inc(v_a_1075_);
lean_dec(v___x_1074_);
v___x_1077_ = lean_box(0);
v_isShared_1078_ = v_isSharedCheck_1114_;
goto v_resetjp_1076_;
}
v_resetjp_1076_:
{
uint8_t v___x_1079_; 
v___x_1079_ = lean_unbox(v_a_1075_);
lean_dec(v_a_1075_);
if (v___x_1079_ == 0)
{
lean_object* v___x_1080_; lean_object* v___x_1082_; 
lean_dec_ref(v_arg_1001_);
v___x_1080_ = lean_box(0);
if (v_isShared_1078_ == 0)
{
lean_ctor_set(v___x_1077_, 0, v___x_1080_);
v___x_1082_ = v___x_1077_;
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
else
{
lean_object* v___x_1084_; 
lean_del_object(v___x_1077_);
v___x_1084_ = l_Lean_Meta_getNatValue_x3f(v_arg_1001_, v_a_984_, v_a_985_, v_a_986_, v_a_987_);
lean_dec_ref(v_arg_1001_);
if (lean_obj_tag(v___x_1084_) == 0)
{
lean_object* v_a_1085_; lean_object* v___x_1087_; uint8_t v_isShared_1088_; uint8_t v_isSharedCheck_1105_; 
v_a_1085_ = lean_ctor_get(v___x_1084_, 0);
v_isSharedCheck_1105_ = !lean_is_exclusive(v___x_1084_);
if (v_isSharedCheck_1105_ == 0)
{
v___x_1087_ = v___x_1084_;
v_isShared_1088_ = v_isSharedCheck_1105_;
goto v_resetjp_1086_;
}
else
{
lean_inc(v_a_1085_);
lean_dec(v___x_1084_);
v___x_1087_ = lean_box(0);
v_isShared_1088_ = v_isSharedCheck_1105_;
goto v_resetjp_1086_;
}
v_resetjp_1086_:
{
if (lean_obj_tag(v_a_1085_) == 1)
{
lean_object* v_val_1089_; lean_object* v___x_1091_; uint8_t v_isShared_1092_; uint8_t v_isSharedCheck_1100_; 
v_val_1089_ = lean_ctor_get(v_a_1085_, 0);
v_isSharedCheck_1100_ = !lean_is_exclusive(v_a_1085_);
if (v_isSharedCheck_1100_ == 0)
{
v___x_1091_ = v_a_1085_;
v_isShared_1092_ = v_isSharedCheck_1100_;
goto v_resetjp_1090_;
}
else
{
lean_inc(v_val_1089_);
lean_dec(v_a_1085_);
v___x_1091_ = lean_box(0);
v_isShared_1092_ = v_isSharedCheck_1100_;
goto v_resetjp_1090_;
}
v_resetjp_1090_:
{
lean_object* v___x_1093_; lean_object* v___x_1095_; 
v___x_1093_ = lean_nat_to_int(v_val_1089_);
if (v_isShared_1092_ == 0)
{
lean_ctor_set(v___x_1091_, 0, v___x_1093_);
v___x_1095_ = v___x_1091_;
goto v_reusejp_1094_;
}
else
{
lean_object* v_reuseFailAlloc_1099_; 
v_reuseFailAlloc_1099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1099_, 0, v___x_1093_);
v___x_1095_ = v_reuseFailAlloc_1099_;
goto v_reusejp_1094_;
}
v_reusejp_1094_:
{
lean_object* v___x_1097_; 
if (v_isShared_1088_ == 0)
{
lean_ctor_set(v___x_1087_, 0, v___x_1095_);
v___x_1097_ = v___x_1087_;
goto v_reusejp_1096_;
}
else
{
lean_object* v_reuseFailAlloc_1098_; 
v_reuseFailAlloc_1098_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1098_, 0, v___x_1095_);
v___x_1097_ = v_reuseFailAlloc_1098_;
goto v_reusejp_1096_;
}
v_reusejp_1096_:
{
return v___x_1097_;
}
}
}
}
else
{
lean_object* v___x_1101_; lean_object* v___x_1103_; 
lean_dec(v_a_1085_);
v___x_1101_ = lean_box(0);
if (v_isShared_1088_ == 0)
{
lean_ctor_set(v___x_1087_, 0, v___x_1101_);
v___x_1103_ = v___x_1087_;
goto v_reusejp_1102_;
}
else
{
lean_object* v_reuseFailAlloc_1104_; 
v_reuseFailAlloc_1104_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1104_, 0, v___x_1101_);
v___x_1103_ = v_reuseFailAlloc_1104_;
goto v_reusejp_1102_;
}
v_reusejp_1102_:
{
return v___x_1103_;
}
}
}
}
else
{
lean_object* v_a_1106_; lean_object* v___x_1108_; uint8_t v_isShared_1109_; uint8_t v_isSharedCheck_1113_; 
v_a_1106_ = lean_ctor_get(v___x_1084_, 0);
v_isSharedCheck_1113_ = !lean_is_exclusive(v___x_1084_);
if (v_isSharedCheck_1113_ == 0)
{
v___x_1108_ = v___x_1084_;
v_isShared_1109_ = v_isSharedCheck_1113_;
goto v_resetjp_1107_;
}
else
{
lean_inc(v_a_1106_);
lean_dec(v___x_1084_);
v___x_1108_ = lean_box(0);
v_isShared_1109_ = v_isSharedCheck_1113_;
goto v_resetjp_1107_;
}
v_resetjp_1107_:
{
lean_object* v___x_1111_; 
if (v_isShared_1109_ == 0)
{
v___x_1111_ = v___x_1108_;
goto v_reusejp_1110_;
}
else
{
lean_object* v_reuseFailAlloc_1112_; 
v_reuseFailAlloc_1112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1112_, 0, v_a_1106_);
v___x_1111_ = v_reuseFailAlloc_1112_;
goto v_reusejp_1110_;
}
v_reusejp_1110_:
{
return v___x_1111_;
}
}
}
}
}
}
else
{
lean_object* v_a_1115_; lean_object* v___x_1117_; uint8_t v_isShared_1118_; uint8_t v_isSharedCheck_1122_; 
lean_dec_ref(v_arg_1001_);
v_a_1115_ = lean_ctor_get(v___x_1074_, 0);
v_isSharedCheck_1122_ = !lean_is_exclusive(v___x_1074_);
if (v_isSharedCheck_1122_ == 0)
{
v___x_1117_ = v___x_1074_;
v_isShared_1118_ = v_isSharedCheck_1122_;
goto v_resetjp_1116_;
}
else
{
lean_inc(v_a_1115_);
lean_dec(v___x_1074_);
v___x_1117_ = lean_box(0);
v_isShared_1118_ = v_isSharedCheck_1122_;
goto v_resetjp_1116_;
}
v_resetjp_1116_:
{
lean_object* v___x_1120_; 
if (v_isShared_1118_ == 0)
{
v___x_1120_ = v___x_1117_;
goto v_reusejp_1119_;
}
else
{
lean_object* v_reuseFailAlloc_1121_; 
v_reuseFailAlloc_1121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1121_, 0, v_a_1115_);
v___x_1120_ = v_reuseFailAlloc_1121_;
goto v_reusejp_1119_;
}
v_reusejp_1119_:
{
return v___x_1120_;
}
}
}
}
}
else
{
lean_object* v___x_1123_; 
lean_dec_ref(v___x_1007_);
lean_dec_ref(v_arg_1001_);
lean_del_object(v___x_992_);
v___x_1123_ = l_Lean_Meta_getNatValue_x3f(v_arg_1004_, v_a_984_, v_a_985_, v_a_986_, v_a_987_);
lean_dec_ref(v_arg_1004_);
if (lean_obj_tag(v___x_1123_) == 0)
{
lean_object* v_a_1124_; lean_object* v___x_1126_; uint8_t v_isShared_1127_; uint8_t v_isSharedCheck_1144_; 
v_a_1124_ = lean_ctor_get(v___x_1123_, 0);
v_isSharedCheck_1144_ = !lean_is_exclusive(v___x_1123_);
if (v_isSharedCheck_1144_ == 0)
{
v___x_1126_ = v___x_1123_;
v_isShared_1127_ = v_isSharedCheck_1144_;
goto v_resetjp_1125_;
}
else
{
lean_inc(v_a_1124_);
lean_dec(v___x_1123_);
v___x_1126_ = lean_box(0);
v_isShared_1127_ = v_isSharedCheck_1144_;
goto v_resetjp_1125_;
}
v_resetjp_1125_:
{
if (lean_obj_tag(v_a_1124_) == 1)
{
lean_object* v_val_1128_; lean_object* v___x_1130_; uint8_t v_isShared_1131_; uint8_t v_isSharedCheck_1139_; 
v_val_1128_ = lean_ctor_get(v_a_1124_, 0);
v_isSharedCheck_1139_ = !lean_is_exclusive(v_a_1124_);
if (v_isSharedCheck_1139_ == 0)
{
v___x_1130_ = v_a_1124_;
v_isShared_1131_ = v_isSharedCheck_1139_;
goto v_resetjp_1129_;
}
else
{
lean_inc(v_val_1128_);
lean_dec(v_a_1124_);
v___x_1130_ = lean_box(0);
v_isShared_1131_ = v_isSharedCheck_1139_;
goto v_resetjp_1129_;
}
v_resetjp_1129_:
{
lean_object* v___x_1132_; lean_object* v___x_1134_; 
v___x_1132_ = lean_nat_to_int(v_val_1128_);
if (v_isShared_1131_ == 0)
{
lean_ctor_set(v___x_1130_, 0, v___x_1132_);
v___x_1134_ = v___x_1130_;
goto v_reusejp_1133_;
}
else
{
lean_object* v_reuseFailAlloc_1138_; 
v_reuseFailAlloc_1138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1138_, 0, v___x_1132_);
v___x_1134_ = v_reuseFailAlloc_1138_;
goto v_reusejp_1133_;
}
v_reusejp_1133_:
{
lean_object* v___x_1136_; 
if (v_isShared_1127_ == 0)
{
lean_ctor_set(v___x_1126_, 0, v___x_1134_);
v___x_1136_ = v___x_1126_;
goto v_reusejp_1135_;
}
else
{
lean_object* v_reuseFailAlloc_1137_; 
v_reuseFailAlloc_1137_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1137_, 0, v___x_1134_);
v___x_1136_ = v_reuseFailAlloc_1137_;
goto v_reusejp_1135_;
}
v_reusejp_1135_:
{
return v___x_1136_;
}
}
}
}
else
{
lean_object* v___x_1140_; lean_object* v___x_1142_; 
lean_dec(v_a_1124_);
v___x_1140_ = lean_box(0);
if (v_isShared_1127_ == 0)
{
lean_ctor_set(v___x_1126_, 0, v___x_1140_);
v___x_1142_ = v___x_1126_;
goto v_reusejp_1141_;
}
else
{
lean_object* v_reuseFailAlloc_1143_; 
v_reuseFailAlloc_1143_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1143_, 0, v___x_1140_);
v___x_1142_ = v_reuseFailAlloc_1143_;
goto v_reusejp_1141_;
}
v_reusejp_1141_:
{
return v___x_1142_;
}
}
}
}
else
{
lean_object* v_a_1145_; lean_object* v___x_1147_; uint8_t v_isShared_1148_; uint8_t v_isSharedCheck_1152_; 
v_a_1145_ = lean_ctor_get(v___x_1123_, 0);
v_isSharedCheck_1152_ = !lean_is_exclusive(v___x_1123_);
if (v_isSharedCheck_1152_ == 0)
{
v___x_1147_ = v___x_1123_;
v_isShared_1148_ = v_isSharedCheck_1152_;
goto v_resetjp_1146_;
}
else
{
lean_inc(v_a_1145_);
lean_dec(v___x_1123_);
v___x_1147_ = lean_box(0);
v_isShared_1148_ = v_isSharedCheck_1152_;
goto v_resetjp_1146_;
}
v_resetjp_1146_:
{
lean_object* v___x_1150_; 
if (v_isShared_1148_ == 0)
{
v___x_1150_ = v___x_1147_;
goto v_reusejp_1149_;
}
else
{
lean_object* v_reuseFailAlloc_1151_; 
v_reuseFailAlloc_1151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1151_, 0, v_a_1145_);
v___x_1150_ = v_reuseFailAlloc_1151_;
goto v_reusejp_1149_;
}
v_reusejp_1149_:
{
return v___x_1150_;
}
}
}
}
}
}
}
v___jp_994_:
{
lean_object* v___x_995_; lean_object* v___x_997_; 
v___x_995_ = lean_box(0);
if (v_isShared_993_ == 0)
{
lean_ctor_set(v___x_992_, 0, v___x_995_);
v___x_997_ = v___x_992_;
goto v_reusejp_996_;
}
else
{
lean_object* v_reuseFailAlloc_998_; 
v_reuseFailAlloc_998_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_998_, 0, v___x_995_);
v___x_997_ = v_reuseFailAlloc_998_;
goto v_reusejp_996_;
}
v_reusejp_996_:
{
return v___x_997_;
}
}
}
}
else
{
lean_object* v_a_1154_; lean_object* v___x_1156_; uint8_t v_isShared_1157_; uint8_t v_isSharedCheck_1161_; 
v_a_1154_ = lean_ctor_get(v___x_989_, 0);
v_isSharedCheck_1161_ = !lean_is_exclusive(v___x_989_);
if (v_isSharedCheck_1161_ == 0)
{
v___x_1156_ = v___x_989_;
v_isShared_1157_ = v_isSharedCheck_1161_;
goto v_resetjp_1155_;
}
else
{
lean_inc(v_a_1154_);
lean_dec(v___x_989_);
v___x_1156_ = lean_box(0);
v_isShared_1157_ = v_isSharedCheck_1161_;
goto v_resetjp_1155_;
}
v_resetjp_1155_:
{
lean_object* v___x_1159_; 
if (v_isShared_1157_ == 0)
{
v___x_1159_ = v___x_1156_;
goto v_reusejp_1158_;
}
else
{
lean_object* v_reuseFailAlloc_1160_; 
v_reuseFailAlloc_1160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1160_, 0, v_a_1154_);
v___x_1159_ = v_reuseFailAlloc_1160_;
goto v_reusejp_1158_;
}
v_reusejp_1158_:
{
return v___x_1159_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f___boxed(lean_object* v_e_1162_, lean_object* v_a_1163_, lean_object* v_a_1164_, lean_object* v_a_1165_, lean_object* v_a_1166_, lean_object* v_a_1167_, lean_object* v_a_1168_, lean_object* v_a_1169_, lean_object* v_a_1170_, lean_object* v_a_1171_, lean_object* v_a_1172_, lean_object* v_a_1173_, lean_object* v_a_1174_){
_start:
{
lean_object* v_res_1175_; 
v_res_1175_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f(v_e_1162_, v_a_1163_, v_a_1164_, v_a_1165_, v_a_1166_, v_a_1167_, v_a_1168_, v_a_1169_, v_a_1170_, v_a_1171_, v_a_1172_, v_a_1173_);
lean_dec(v_a_1173_);
lean_dec_ref(v_a_1172_);
lean_dec(v_a_1171_);
lean_dec_ref(v_a_1170_);
lean_dec(v_a_1169_);
lean_dec_ref(v_a_1168_);
lean_dec(v_a_1167_);
lean_dec_ref(v_a_1166_);
lean_dec(v_a_1165_);
lean_dec(v_a_1164_);
lean_dec_ref(v_a_1163_);
return v_res_1175_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_getNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isNatCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__2_spec__4_spec__6(lean_object* v_u_1176_, lean_object* v_type_1177_, lean_object* v_semiringInst_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_){
_start:
{
lean_object* v___x_1191_; 
v___x_1191_ = l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_getNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isNatCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__2_spec__4_spec__6___redArg(v_u_1176_, v_type_1177_, v_semiringInst_1178_, v___y_1184_, v___y_1185_, v___y_1186_, v___y_1187_, v___y_1188_, v___y_1189_);
return v___x_1191_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_getNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isNatCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__2_spec__4_spec__6___boxed(lean_object* v_u_1192_, lean_object* v_type_1193_, lean_object* v_semiringInst_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_){
_start:
{
lean_object* v_res_1207_; 
v_res_1207_ = l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_getNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isNatCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__2_spec__4_spec__6(v_u_1192_, v_type_1193_, v_semiringInst_1194_, v___y_1195_, v___y_1196_, v___y_1197_, v___y_1198_, v___y_1199_, v___y_1200_, v___y_1201_, v___y_1202_, v___y_1203_, v___y_1204_, v___y_1205_);
lean_dec(v___y_1205_);
lean_dec_ref(v___y_1204_);
lean_dec(v___y_1203_);
lean_dec_ref(v___y_1202_);
lean_dec(v___y_1201_);
lean_dec_ref(v___y_1200_);
lean_dec(v___y_1199_);
lean_dec_ref(v___y_1198_);
lean_dec(v___y_1197_);
lean_dec(v___y_1196_);
lean_dec_ref(v___y_1195_);
return v_res_1207_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1_spec__5_spec__8(lean_object* v_00_u03b1_1208_, lean_object* v_msg_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_){
_start:
{
lean_object* v___x_1222_; 
v___x_1222_ = l_Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1_spec__5_spec__8___redArg(v_msg_1209_, v___y_1217_, v___y_1218_, v___y_1219_, v___y_1220_);
return v___x_1222_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1_spec__5_spec__8___boxed(lean_object* v_00_u03b1_1223_, lean_object* v_msg_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_){
_start:
{
lean_object* v_res_1237_; 
v_res_1237_ = l_Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1_spec__5_spec__8(v_00_u03b1_1223_, v_msg_1224_, v___y_1225_, v___y_1226_, v___y_1227_, v___y_1228_, v___y_1229_, v___y_1230_, v___y_1231_, v___y_1232_, v___y_1233_, v___y_1234_, v___y_1235_);
lean_dec(v___y_1235_);
lean_dec_ref(v___y_1234_);
lean_dec(v___y_1233_);
lean_dec_ref(v___y_1232_);
lean_dec(v___y_1231_);
lean_dec_ref(v___y_1230_);
lean_dec(v___y_1229_);
lean_dec_ref(v___y_1228_);
lean_dec(v___y_1227_);
lean_dec(v___y_1226_);
lean_dec_ref(v___y_1225_);
return v_res_1237_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___lam__0(lean_object* v_a_1238_, lean_object* v_s_1239_){
_start:
{
lean_object* v_toRing_1240_; lean_object* v_semiringId_x3f_1241_; lean_object* v_commSemiringInst_1242_; lean_object* v_commRingInst_1243_; lean_object* v_noZeroDivInst_x3f_1244_; lean_object* v_fieldInst_x3f_1245_; lean_object* v_powIdentityInst_x3f_1246_; lean_object* v_denoteEntries_1247_; lean_object* v_nextId_1248_; lean_object* v_steps_1249_; lean_object* v_queue_1250_; lean_object* v_basis_1251_; lean_object* v_diseqs_1252_; uint8_t v_recheck_1253_; lean_object* v_invSet_1254_; lean_object* v_powIdentityVarCount_1255_; lean_object* v_numEq0_x3f_1256_; uint8_t v_numEq0Updated_1257_; lean_object* v___x_1259_; uint8_t v_isShared_1260_; uint8_t v_isSharedCheck_1265_; 
v_toRing_1240_ = lean_ctor_get(v_s_1239_, 0);
v_semiringId_x3f_1241_ = lean_ctor_get(v_s_1239_, 2);
v_commSemiringInst_1242_ = lean_ctor_get(v_s_1239_, 3);
v_commRingInst_1243_ = lean_ctor_get(v_s_1239_, 4);
v_noZeroDivInst_x3f_1244_ = lean_ctor_get(v_s_1239_, 5);
v_fieldInst_x3f_1245_ = lean_ctor_get(v_s_1239_, 6);
v_powIdentityInst_x3f_1246_ = lean_ctor_get(v_s_1239_, 7);
v_denoteEntries_1247_ = lean_ctor_get(v_s_1239_, 8);
v_nextId_1248_ = lean_ctor_get(v_s_1239_, 9);
v_steps_1249_ = lean_ctor_get(v_s_1239_, 10);
v_queue_1250_ = lean_ctor_get(v_s_1239_, 11);
v_basis_1251_ = lean_ctor_get(v_s_1239_, 12);
v_diseqs_1252_ = lean_ctor_get(v_s_1239_, 13);
v_recheck_1253_ = lean_ctor_get_uint8(v_s_1239_, sizeof(void*)*17);
v_invSet_1254_ = lean_ctor_get(v_s_1239_, 14);
v_powIdentityVarCount_1255_ = lean_ctor_get(v_s_1239_, 15);
v_numEq0_x3f_1256_ = lean_ctor_get(v_s_1239_, 16);
v_numEq0Updated_1257_ = lean_ctor_get_uint8(v_s_1239_, sizeof(void*)*17 + 1);
v_isSharedCheck_1265_ = !lean_is_exclusive(v_s_1239_);
if (v_isSharedCheck_1265_ == 0)
{
lean_object* v_unused_1266_; 
v_unused_1266_ = lean_ctor_get(v_s_1239_, 1);
lean_dec(v_unused_1266_);
v___x_1259_ = v_s_1239_;
v_isShared_1260_ = v_isSharedCheck_1265_;
goto v_resetjp_1258_;
}
else
{
lean_inc(v_numEq0_x3f_1256_);
lean_inc(v_powIdentityVarCount_1255_);
lean_inc(v_invSet_1254_);
lean_inc(v_diseqs_1252_);
lean_inc(v_basis_1251_);
lean_inc(v_queue_1250_);
lean_inc(v_steps_1249_);
lean_inc(v_nextId_1248_);
lean_inc(v_denoteEntries_1247_);
lean_inc(v_powIdentityInst_x3f_1246_);
lean_inc(v_fieldInst_x3f_1245_);
lean_inc(v_noZeroDivInst_x3f_1244_);
lean_inc(v_commRingInst_1243_);
lean_inc(v_commSemiringInst_1242_);
lean_inc(v_semiringId_x3f_1241_);
lean_inc(v_toRing_1240_);
lean_dec(v_s_1239_);
v___x_1259_ = lean_box(0);
v_isShared_1260_ = v_isSharedCheck_1265_;
goto v_resetjp_1258_;
}
v_resetjp_1258_:
{
lean_object* v___x_1261_; lean_object* v___x_1263_; 
v___x_1261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1261_, 0, v_a_1238_);
if (v_isShared_1260_ == 0)
{
lean_ctor_set(v___x_1259_, 1, v___x_1261_);
v___x_1263_ = v___x_1259_;
goto v_reusejp_1262_;
}
else
{
lean_object* v_reuseFailAlloc_1264_; 
v_reuseFailAlloc_1264_ = lean_alloc_ctor(0, 17, 2);
lean_ctor_set(v_reuseFailAlloc_1264_, 0, v_toRing_1240_);
lean_ctor_set(v_reuseFailAlloc_1264_, 1, v___x_1261_);
lean_ctor_set(v_reuseFailAlloc_1264_, 2, v_semiringId_x3f_1241_);
lean_ctor_set(v_reuseFailAlloc_1264_, 3, v_commSemiringInst_1242_);
lean_ctor_set(v_reuseFailAlloc_1264_, 4, v_commRingInst_1243_);
lean_ctor_set(v_reuseFailAlloc_1264_, 5, v_noZeroDivInst_x3f_1244_);
lean_ctor_set(v_reuseFailAlloc_1264_, 6, v_fieldInst_x3f_1245_);
lean_ctor_set(v_reuseFailAlloc_1264_, 7, v_powIdentityInst_x3f_1246_);
lean_ctor_set(v_reuseFailAlloc_1264_, 8, v_denoteEntries_1247_);
lean_ctor_set(v_reuseFailAlloc_1264_, 9, v_nextId_1248_);
lean_ctor_set(v_reuseFailAlloc_1264_, 10, v_steps_1249_);
lean_ctor_set(v_reuseFailAlloc_1264_, 11, v_queue_1250_);
lean_ctor_set(v_reuseFailAlloc_1264_, 12, v_basis_1251_);
lean_ctor_set(v_reuseFailAlloc_1264_, 13, v_diseqs_1252_);
lean_ctor_set(v_reuseFailAlloc_1264_, 14, v_invSet_1254_);
lean_ctor_set(v_reuseFailAlloc_1264_, 15, v_powIdentityVarCount_1255_);
lean_ctor_set(v_reuseFailAlloc_1264_, 16, v_numEq0_x3f_1256_);
lean_ctor_set_uint8(v_reuseFailAlloc_1264_, sizeof(void*)*17, v_recheck_1253_);
lean_ctor_set_uint8(v_reuseFailAlloc_1264_, sizeof(void*)*17 + 1, v_numEq0Updated_1257_);
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
lean_dec_ref_known(v_fieldInst_x3f_1301_, 1);
lean_dec(v_a_1297_);
v_val_1303_ = lean_ctor_get(v_invFn_x3f_1302_, 0);
lean_inc(v_val_1303_);
lean_dec_ref_known(v_invFn_x3f_1302_, 1);
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
lean_dec_ref_known(v_fieldInst_x3f_1301_, 1);
v_type_1309_ = lean_ctor_get(v_toRing_1307_, 1);
lean_inc_ref_n(v_type_1309_, 2);
v_u_1310_ = lean_ctor_get(v_toRing_1307_, 2);
lean_inc_n(v_u_1310_, 2);
lean_dec_ref(v_toRing_1307_);
v___x_1311_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___closed__2));
v___x_1312_ = lean_box(0);
v___x_1313_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1313_, 0, v_u_1310_);
lean_ctor_set(v___x_1313_, 1, v___x_1312_);
v___x_1314_ = l_Lean_mkConst(v___x_1311_, v___x_1313_);
v_expectedInst_1315_ = l_Lean_mkAppB(v___x_1314_, v_type_1309_, v_val_1308_);
v___x_1316_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___closed__4));
v___x_1317_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___closed__6));
v___x_1318_ = l_Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1(v_type_1309_, v_u_1310_, v___x_1316_, v___x_1317_, v_expectedInst_1315_, v___y_1284_, v___y_1285_, v___y_1286_, v___y_1287_, v___y_1288_, v___y_1289_, v___y_1290_, v___y_1291_, v___y_1292_, v___y_1293_, v___y_1294_);
if (lean_obj_tag(v___x_1318_) == 0)
{
lean_object* v_a_1319_; lean_object* v___f_1320_; lean_object* v___x_1321_; 
v_a_1319_ = lean_ctor_get(v___x_1318_, 0);
lean_inc_n(v_a_1319_, 2);
lean_dec_ref_known(v___x_1318_, 1);
v___f_1320_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___lam__0), 2, 1);
lean_closure_set(v___f_1320_, 0, v_a_1319_);
v___x_1321_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(v___f_1320_, v___y_1284_, v___y_1285_);
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
return v___x_1318_;
}
}
}
else
{
lean_object* v_toRing_1338_; lean_object* v_type_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; 
lean_del_object(v___x_1299_);
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
v___x_1343_ = l_Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1_spec__5_spec__8___redArg(v___x_1342_, v___y_1291_, v___y_1292_, v___y_1293_, v___y_1294_);
return v___x_1343_;
}
}
}
else
{
lean_object* v_a_1345_; lean_object* v___x_1347_; uint8_t v_isShared_1348_; uint8_t v_isSharedCheck_1352_; 
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
lean_dec(v___y_1363_);
lean_dec_ref(v___y_1362_);
lean_dec(v___y_1361_);
lean_dec_ref(v___y_1360_);
lean_dec(v___y_1359_);
lean_dec_ref(v___y_1358_);
lean_dec(v___y_1357_);
lean_dec_ref(v___y_1356_);
lean_dec(v___y_1355_);
lean_dec(v___y_1354_);
lean_dec_ref(v___y_1353_);
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
lean_object* v_a_1380_; lean_object* v___x_1382_; uint8_t v_isShared_1383_; uint8_t v_isSharedCheck_1412_; 
v_a_1380_ = lean_ctor_get(v___x_1379_, 0);
v_isSharedCheck_1412_ = !lean_is_exclusive(v___x_1379_);
if (v_isSharedCheck_1412_ == 0)
{
v___x_1382_ = v___x_1379_;
v_isShared_1383_ = v_isSharedCheck_1412_;
goto v_resetjp_1381_;
}
else
{
lean_inc(v_a_1380_);
lean_dec(v___x_1379_);
v___x_1382_ = lean_box(0);
v_isShared_1383_ = v_isSharedCheck_1412_;
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
lean_dec_ref_known(v_fieldInst_x3f_1384_, 1);
lean_del_object(v___x_1382_);
v___x_1390_ = l_Lean_Meta_Grind_Arith_CommRing_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0(v_a_1367_, v_a_1368_, v_a_1369_, v_a_1370_, v_a_1371_, v_a_1372_, v_a_1373_, v_a_1374_, v_a_1375_, v_a_1376_, v_a_1377_);
if (lean_obj_tag(v___x_1390_) == 0)
{
lean_object* v_a_1391_; lean_object* v___x_1393_; uint8_t v_isShared_1394_; uint8_t v_isSharedCheck_1403_; 
v_a_1391_ = lean_ctor_get(v___x_1390_, 0);
v_isSharedCheck_1403_ = !lean_is_exclusive(v___x_1390_);
if (v_isSharedCheck_1403_ == 0)
{
v___x_1393_ = v___x_1390_;
v_isShared_1394_ = v_isSharedCheck_1403_;
goto v_resetjp_1392_;
}
else
{
lean_inc(v_a_1391_);
lean_dec(v___x_1390_);
v___x_1393_ = lean_box(0);
v_isShared_1394_ = v_isSharedCheck_1403_;
goto v_resetjp_1392_;
}
v_resetjp_1392_:
{
lean_object* v___x_1395_; size_t v___x_1396_; size_t v___x_1397_; uint8_t v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1401_; 
v___x_1395_ = l_Lean_Expr_appArg_x21(v_a_1391_);
lean_dec(v_a_1391_);
v___x_1396_ = lean_ptr_addr(v___x_1395_);
lean_dec_ref(v___x_1395_);
v___x_1397_ = lean_ptr_addr(v_inst_1366_);
v___x_1398_ = lean_usize_dec_eq(v___x_1396_, v___x_1397_);
v___x_1399_ = lean_box(v___x_1398_);
if (v_isShared_1394_ == 0)
{
lean_ctor_set(v___x_1393_, 0, v___x_1399_);
v___x_1401_ = v___x_1393_;
goto v_reusejp_1400_;
}
else
{
lean_object* v_reuseFailAlloc_1402_; 
v_reuseFailAlloc_1402_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1402_, 0, v___x_1399_);
v___x_1401_ = v_reuseFailAlloc_1402_;
goto v_reusejp_1400_;
}
v_reusejp_1400_:
{
return v___x_1401_;
}
}
}
else
{
lean_object* v_a_1404_; lean_object* v___x_1406_; uint8_t v_isShared_1407_; uint8_t v_isSharedCheck_1411_; 
v_a_1404_ = lean_ctor_get(v___x_1390_, 0);
v_isSharedCheck_1411_ = !lean_is_exclusive(v___x_1390_);
if (v_isSharedCheck_1411_ == 0)
{
v___x_1406_ = v___x_1390_;
v_isShared_1407_ = v_isSharedCheck_1411_;
goto v_resetjp_1405_;
}
else
{
lean_inc(v_a_1404_);
lean_dec(v___x_1390_);
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
}
else
{
lean_object* v_a_1413_; lean_object* v___x_1415_; uint8_t v_isShared_1416_; uint8_t v_isSharedCheck_1420_; 
v_a_1413_ = lean_ctor_get(v___x_1379_, 0);
v_isSharedCheck_1420_ = !lean_is_exclusive(v___x_1379_);
if (v_isSharedCheck_1420_ == 0)
{
v___x_1415_ = v___x_1379_;
v_isShared_1416_ = v_isSharedCheck_1420_;
goto v_resetjp_1414_;
}
else
{
lean_inc(v_a_1413_);
lean_dec(v___x_1379_);
v___x_1415_ = lean_box(0);
v_isShared_1416_ = v_isSharedCheck_1420_;
goto v_resetjp_1414_;
}
v_resetjp_1414_:
{
lean_object* v___x_1418_; 
if (v_isShared_1416_ == 0)
{
v___x_1418_ = v___x_1415_;
goto v_reusejp_1417_;
}
else
{
lean_object* v_reuseFailAlloc_1419_; 
v_reuseFailAlloc_1419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1419_, 0, v_a_1413_);
v___x_1418_ = v_reuseFailAlloc_1419_;
goto v_reusejp_1417_;
}
v_reusejp_1417_:
{
return v___x_1418_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst___boxed(lean_object* v_inst_1421_, lean_object* v_a_1422_, lean_object* v_a_1423_, lean_object* v_a_1424_, lean_object* v_a_1425_, lean_object* v_a_1426_, lean_object* v_a_1427_, lean_object* v_a_1428_, lean_object* v_a_1429_, lean_object* v_a_1430_, lean_object* v_a_1431_, lean_object* v_a_1432_, lean_object* v_a_1433_){
_start:
{
lean_object* v_res_1434_; 
v_res_1434_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst(v_inst_1421_, v_a_1422_, v_a_1423_, v_a_1424_, v_a_1425_, v_a_1426_, v_a_1427_, v_a_1428_, v_a_1429_, v_a_1430_, v_a_1431_, v_a_1432_);
lean_dec(v_a_1432_);
lean_dec_ref(v_a_1431_);
lean_dec(v_a_1430_);
lean_dec_ref(v_a_1429_);
lean_dec(v_a_1428_);
lean_dec_ref(v_a_1427_);
lean_dec(v_a_1426_);
lean_dec_ref(v_a_1425_);
lean_dec(v_a_1424_);
lean_dec(v_a_1423_);
lean_dec_ref(v_a_1422_);
lean_dec_ref(v_inst_1421_);
return v_res_1434_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__2(lean_object* v_a_1435_){
_start:
{
lean_object* v___x_1436_; 
v___x_1436_ = lean_nat_to_int(v_a_1435_);
return v___x_1436_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0_spec__2_spec__6___redArg(lean_object* v_x_1437_, lean_object* v_x_1438_, lean_object* v_x_1439_, lean_object* v_x_1440_){
_start:
{
lean_object* v_ks_1441_; lean_object* v_vs_1442_; lean_object* v___x_1444_; uint8_t v_isShared_1445_; uint8_t v_isSharedCheck_1466_; 
v_ks_1441_ = lean_ctor_get(v_x_1437_, 0);
v_vs_1442_ = lean_ctor_get(v_x_1437_, 1);
v_isSharedCheck_1466_ = !lean_is_exclusive(v_x_1437_);
if (v_isSharedCheck_1466_ == 0)
{
v___x_1444_ = v_x_1437_;
v_isShared_1445_ = v_isSharedCheck_1466_;
goto v_resetjp_1443_;
}
else
{
lean_inc(v_vs_1442_);
lean_inc(v_ks_1441_);
lean_dec(v_x_1437_);
v___x_1444_ = lean_box(0);
v_isShared_1445_ = v_isSharedCheck_1466_;
goto v_resetjp_1443_;
}
v_resetjp_1443_:
{
lean_object* v___x_1446_; uint8_t v___x_1447_; 
v___x_1446_ = lean_array_get_size(v_ks_1441_);
v___x_1447_ = lean_nat_dec_lt(v_x_1438_, v___x_1446_);
if (v___x_1447_ == 0)
{
lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1451_; 
lean_dec(v_x_1438_);
v___x_1448_ = lean_array_push(v_ks_1441_, v_x_1439_);
v___x_1449_ = lean_array_push(v_vs_1442_, v_x_1440_);
if (v_isShared_1445_ == 0)
{
lean_ctor_set(v___x_1444_, 1, v___x_1449_);
lean_ctor_set(v___x_1444_, 0, v___x_1448_);
v___x_1451_ = v___x_1444_;
goto v_reusejp_1450_;
}
else
{
lean_object* v_reuseFailAlloc_1452_; 
v_reuseFailAlloc_1452_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1452_, 0, v___x_1448_);
lean_ctor_set(v_reuseFailAlloc_1452_, 1, v___x_1449_);
v___x_1451_ = v_reuseFailAlloc_1452_;
goto v_reusejp_1450_;
}
v_reusejp_1450_:
{
return v___x_1451_;
}
}
else
{
lean_object* v_k_x27_1453_; uint8_t v___x_1454_; 
v_k_x27_1453_ = lean_array_fget_borrowed(v_ks_1441_, v_x_1438_);
v___x_1454_ = lean_expr_eqv(v_x_1439_, v_k_x27_1453_);
if (v___x_1454_ == 0)
{
lean_object* v___x_1456_; 
if (v_isShared_1445_ == 0)
{
v___x_1456_ = v___x_1444_;
goto v_reusejp_1455_;
}
else
{
lean_object* v_reuseFailAlloc_1460_; 
v_reuseFailAlloc_1460_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1460_, 0, v_ks_1441_);
lean_ctor_set(v_reuseFailAlloc_1460_, 1, v_vs_1442_);
v___x_1456_ = v_reuseFailAlloc_1460_;
goto v_reusejp_1455_;
}
v_reusejp_1455_:
{
lean_object* v___x_1457_; lean_object* v___x_1458_; 
v___x_1457_ = lean_unsigned_to_nat(1u);
v___x_1458_ = lean_nat_add(v_x_1438_, v___x_1457_);
lean_dec(v_x_1438_);
v_x_1437_ = v___x_1456_;
v_x_1438_ = v___x_1458_;
goto _start;
}
}
else
{
lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1464_; 
v___x_1461_ = lean_array_fset(v_ks_1441_, v_x_1438_, v_x_1439_);
v___x_1462_ = lean_array_fset(v_vs_1442_, v_x_1438_, v_x_1440_);
lean_dec(v_x_1438_);
if (v_isShared_1445_ == 0)
{
lean_ctor_set(v___x_1444_, 1, v___x_1462_);
lean_ctor_set(v___x_1444_, 0, v___x_1461_);
v___x_1464_ = v___x_1444_;
goto v_reusejp_1463_;
}
else
{
lean_object* v_reuseFailAlloc_1465_; 
v_reuseFailAlloc_1465_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1465_, 0, v___x_1461_);
lean_ctor_set(v_reuseFailAlloc_1465_, 1, v___x_1462_);
v___x_1464_ = v_reuseFailAlloc_1465_;
goto v_reusejp_1463_;
}
v_reusejp_1463_:
{
return v___x_1464_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0_spec__2___redArg(lean_object* v_n_1467_, lean_object* v_k_1468_, lean_object* v_v_1469_){
_start:
{
lean_object* v___x_1470_; lean_object* v___x_1471_; 
v___x_1470_ = lean_unsigned_to_nat(0u);
v___x_1471_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0_spec__2_spec__6___redArg(v_n_1467_, v___x_1470_, v_k_1468_, v_v_1469_);
return v___x_1471_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1472_; 
v___x_1472_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1472_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg(lean_object* v_x_1473_, size_t v_x_1474_, size_t v_x_1475_, lean_object* v_x_1476_, lean_object* v_x_1477_){
_start:
{
if (lean_obj_tag(v_x_1473_) == 0)
{
lean_object* v_es_1478_; size_t v___x_1479_; size_t v___x_1480_; lean_object* v_j_1481_; lean_object* v___x_1482_; uint8_t v___x_1483_; 
v_es_1478_ = lean_ctor_get(v_x_1473_, 0);
v___x_1479_ = ((size_t)31ULL);
v___x_1480_ = lean_usize_land(v_x_1474_, v___x_1479_);
v_j_1481_ = lean_usize_to_nat(v___x_1480_);
v___x_1482_ = lean_array_get_size(v_es_1478_);
v___x_1483_ = lean_nat_dec_lt(v_j_1481_, v___x_1482_);
if (v___x_1483_ == 0)
{
lean_dec(v_j_1481_);
lean_dec(v_x_1477_);
lean_dec_ref(v_x_1476_);
return v_x_1473_;
}
else
{
lean_object* v___x_1485_; uint8_t v_isShared_1486_; uint8_t v_isSharedCheck_1522_; 
lean_inc_ref(v_es_1478_);
v_isSharedCheck_1522_ = !lean_is_exclusive(v_x_1473_);
if (v_isSharedCheck_1522_ == 0)
{
lean_object* v_unused_1523_; 
v_unused_1523_ = lean_ctor_get(v_x_1473_, 0);
lean_dec(v_unused_1523_);
v___x_1485_ = v_x_1473_;
v_isShared_1486_ = v_isSharedCheck_1522_;
goto v_resetjp_1484_;
}
else
{
lean_dec(v_x_1473_);
v___x_1485_ = lean_box(0);
v_isShared_1486_ = v_isSharedCheck_1522_;
goto v_resetjp_1484_;
}
v_resetjp_1484_:
{
lean_object* v_v_1487_; lean_object* v___x_1488_; lean_object* v_xs_x27_1489_; lean_object* v___y_1491_; 
v_v_1487_ = lean_array_fget(v_es_1478_, v_j_1481_);
v___x_1488_ = lean_box(0);
v_xs_x27_1489_ = lean_array_fset(v_es_1478_, v_j_1481_, v___x_1488_);
switch(lean_obj_tag(v_v_1487_))
{
case 0:
{
lean_object* v_key_1496_; lean_object* v_val_1497_; lean_object* v___x_1499_; uint8_t v_isShared_1500_; uint8_t v_isSharedCheck_1507_; 
v_key_1496_ = lean_ctor_get(v_v_1487_, 0);
v_val_1497_ = lean_ctor_get(v_v_1487_, 1);
v_isSharedCheck_1507_ = !lean_is_exclusive(v_v_1487_);
if (v_isSharedCheck_1507_ == 0)
{
v___x_1499_ = v_v_1487_;
v_isShared_1500_ = v_isSharedCheck_1507_;
goto v_resetjp_1498_;
}
else
{
lean_inc(v_val_1497_);
lean_inc(v_key_1496_);
lean_dec(v_v_1487_);
v___x_1499_ = lean_box(0);
v_isShared_1500_ = v_isSharedCheck_1507_;
goto v_resetjp_1498_;
}
v_resetjp_1498_:
{
uint8_t v___x_1501_; 
v___x_1501_ = lean_expr_eqv(v_x_1476_, v_key_1496_);
if (v___x_1501_ == 0)
{
lean_object* v___x_1502_; lean_object* v___x_1503_; 
lean_del_object(v___x_1499_);
v___x_1502_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1496_, v_val_1497_, v_x_1476_, v_x_1477_);
v___x_1503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1503_, 0, v___x_1502_);
v___y_1491_ = v___x_1503_;
goto v___jp_1490_;
}
else
{
lean_object* v___x_1505_; 
lean_dec(v_val_1497_);
lean_dec(v_key_1496_);
if (v_isShared_1500_ == 0)
{
lean_ctor_set(v___x_1499_, 1, v_x_1477_);
lean_ctor_set(v___x_1499_, 0, v_x_1476_);
v___x_1505_ = v___x_1499_;
goto v_reusejp_1504_;
}
else
{
lean_object* v_reuseFailAlloc_1506_; 
v_reuseFailAlloc_1506_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1506_, 0, v_x_1476_);
lean_ctor_set(v_reuseFailAlloc_1506_, 1, v_x_1477_);
v___x_1505_ = v_reuseFailAlloc_1506_;
goto v_reusejp_1504_;
}
v_reusejp_1504_:
{
v___y_1491_ = v___x_1505_;
goto v___jp_1490_;
}
}
}
}
case 1:
{
lean_object* v_node_1508_; lean_object* v___x_1510_; uint8_t v_isShared_1511_; uint8_t v_isSharedCheck_1520_; 
v_node_1508_ = lean_ctor_get(v_v_1487_, 0);
v_isSharedCheck_1520_ = !lean_is_exclusive(v_v_1487_);
if (v_isSharedCheck_1520_ == 0)
{
v___x_1510_ = v_v_1487_;
v_isShared_1511_ = v_isSharedCheck_1520_;
goto v_resetjp_1509_;
}
else
{
lean_inc(v_node_1508_);
lean_dec(v_v_1487_);
v___x_1510_ = lean_box(0);
v_isShared_1511_ = v_isSharedCheck_1520_;
goto v_resetjp_1509_;
}
v_resetjp_1509_:
{
size_t v___x_1512_; size_t v___x_1513_; size_t v___x_1514_; size_t v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1518_; 
v___x_1512_ = ((size_t)5ULL);
v___x_1513_ = lean_usize_shift_right(v_x_1474_, v___x_1512_);
v___x_1514_ = ((size_t)1ULL);
v___x_1515_ = lean_usize_add(v_x_1475_, v___x_1514_);
v___x_1516_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg(v_node_1508_, v___x_1513_, v___x_1515_, v_x_1476_, v_x_1477_);
if (v_isShared_1511_ == 0)
{
lean_ctor_set(v___x_1510_, 0, v___x_1516_);
v___x_1518_ = v___x_1510_;
goto v_reusejp_1517_;
}
else
{
lean_object* v_reuseFailAlloc_1519_; 
v_reuseFailAlloc_1519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1519_, 0, v___x_1516_);
v___x_1518_ = v_reuseFailAlloc_1519_;
goto v_reusejp_1517_;
}
v_reusejp_1517_:
{
v___y_1491_ = v___x_1518_;
goto v___jp_1490_;
}
}
}
default: 
{
lean_object* v___x_1521_; 
v___x_1521_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1521_, 0, v_x_1476_);
lean_ctor_set(v___x_1521_, 1, v_x_1477_);
v___y_1491_ = v___x_1521_;
goto v___jp_1490_;
}
}
v___jp_1490_:
{
lean_object* v___x_1492_; lean_object* v___x_1494_; 
v___x_1492_ = lean_array_fset(v_xs_x27_1489_, v_j_1481_, v___y_1491_);
lean_dec(v_j_1481_);
if (v_isShared_1486_ == 0)
{
lean_ctor_set(v___x_1485_, 0, v___x_1492_);
v___x_1494_ = v___x_1485_;
goto v_reusejp_1493_;
}
else
{
lean_object* v_reuseFailAlloc_1495_; 
v_reuseFailAlloc_1495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1495_, 0, v___x_1492_);
v___x_1494_ = v_reuseFailAlloc_1495_;
goto v_reusejp_1493_;
}
v_reusejp_1493_:
{
return v___x_1494_;
}
}
}
}
}
else
{
lean_object* v_ks_1524_; lean_object* v_vs_1525_; lean_object* v___x_1527_; uint8_t v_isShared_1528_; uint8_t v_isSharedCheck_1543_; 
v_ks_1524_ = lean_ctor_get(v_x_1473_, 0);
v_vs_1525_ = lean_ctor_get(v_x_1473_, 1);
v_isSharedCheck_1543_ = !lean_is_exclusive(v_x_1473_);
if (v_isSharedCheck_1543_ == 0)
{
v___x_1527_ = v_x_1473_;
v_isShared_1528_ = v_isSharedCheck_1543_;
goto v_resetjp_1526_;
}
else
{
lean_inc(v_vs_1525_);
lean_inc(v_ks_1524_);
lean_dec(v_x_1473_);
v___x_1527_ = lean_box(0);
v_isShared_1528_ = v_isSharedCheck_1543_;
goto v_resetjp_1526_;
}
v_resetjp_1526_:
{
lean_object* v___x_1530_; 
if (v_isShared_1528_ == 0)
{
v___x_1530_ = v___x_1527_;
goto v_reusejp_1529_;
}
else
{
lean_object* v_reuseFailAlloc_1542_; 
v_reuseFailAlloc_1542_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1542_, 0, v_ks_1524_);
lean_ctor_set(v_reuseFailAlloc_1542_, 1, v_vs_1525_);
v___x_1530_ = v_reuseFailAlloc_1542_;
goto v_reusejp_1529_;
}
v_reusejp_1529_:
{
lean_object* v_newNode_1531_; size_t v___x_1532_; uint8_t v___x_1533_; 
v_newNode_1531_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0_spec__2___redArg(v___x_1530_, v_x_1476_, v_x_1477_);
v___x_1532_ = ((size_t)7ULL);
v___x_1533_ = lean_usize_dec_le(v___x_1532_, v_x_1475_);
if (v___x_1533_ == 0)
{
lean_object* v___x_1534_; lean_object* v___x_1535_; uint8_t v___x_1536_; 
v___x_1534_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1531_);
v___x_1535_ = lean_unsigned_to_nat(4u);
v___x_1536_ = lean_nat_dec_lt(v___x_1534_, v___x_1535_);
lean_dec(v___x_1534_);
if (v___x_1536_ == 0)
{
lean_object* v_ks_1537_; lean_object* v_vs_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; 
v_ks_1537_ = lean_ctor_get(v_newNode_1531_, 0);
lean_inc_ref(v_ks_1537_);
v_vs_1538_ = lean_ctor_get(v_newNode_1531_, 1);
lean_inc_ref(v_vs_1538_);
lean_dec_ref(v_newNode_1531_);
v___x_1539_ = lean_unsigned_to_nat(0u);
v___x_1540_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg___closed__0);
v___x_1541_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0_spec__3___redArg(v_x_1475_, v_ks_1537_, v_vs_1538_, v___x_1539_, v___x_1540_);
lean_dec_ref(v_vs_1538_);
lean_dec_ref(v_ks_1537_);
return v___x_1541_;
}
else
{
return v_newNode_1531_;
}
}
else
{
return v_newNode_1531_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0_spec__3___redArg(size_t v_depth_1544_, lean_object* v_keys_1545_, lean_object* v_vals_1546_, lean_object* v_i_1547_, lean_object* v_entries_1548_){
_start:
{
lean_object* v___x_1549_; uint8_t v___x_1550_; 
v___x_1549_ = lean_array_get_size(v_keys_1545_);
v___x_1550_ = lean_nat_dec_lt(v_i_1547_, v___x_1549_);
if (v___x_1550_ == 0)
{
lean_dec(v_i_1547_);
return v_entries_1548_;
}
else
{
lean_object* v_k_1551_; lean_object* v_v_1552_; uint64_t v___x_1553_; size_t v_h_1554_; size_t v___x_1555_; lean_object* v___x_1556_; size_t v___x_1557_; size_t v___x_1558_; size_t v___x_1559_; size_t v_h_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; 
v_k_1551_ = lean_array_fget_borrowed(v_keys_1545_, v_i_1547_);
v_v_1552_ = lean_array_fget_borrowed(v_vals_1546_, v_i_1547_);
v___x_1553_ = l_Lean_Expr_hash(v_k_1551_);
v_h_1554_ = lean_uint64_to_usize(v___x_1553_);
v___x_1555_ = ((size_t)5ULL);
v___x_1556_ = lean_unsigned_to_nat(1u);
v___x_1557_ = ((size_t)1ULL);
v___x_1558_ = lean_usize_sub(v_depth_1544_, v___x_1557_);
v___x_1559_ = lean_usize_mul(v___x_1555_, v___x_1558_);
v_h_1560_ = lean_usize_shift_right(v_h_1554_, v___x_1559_);
v___x_1561_ = lean_nat_add(v_i_1547_, v___x_1556_);
lean_dec(v_i_1547_);
lean_inc(v_v_1552_);
lean_inc(v_k_1551_);
v___x_1562_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg(v_entries_1548_, v_h_1560_, v_depth_1544_, v_k_1551_, v_v_1552_);
v_i_1547_ = v___x_1561_;
v_entries_1548_ = v___x_1562_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_depth_1564_, lean_object* v_keys_1565_, lean_object* v_vals_1566_, lean_object* v_i_1567_, lean_object* v_entries_1568_){
_start:
{
size_t v_depth_boxed_1569_; lean_object* v_res_1570_; 
v_depth_boxed_1569_ = lean_unbox_usize(v_depth_1564_);
lean_dec(v_depth_1564_);
v_res_1570_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0_spec__3___redArg(v_depth_boxed_1569_, v_keys_1565_, v_vals_1566_, v_i_1567_, v_entries_1568_);
lean_dec_ref(v_vals_1566_);
lean_dec_ref(v_keys_1565_);
return v_res_1570_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg___boxed(lean_object* v_x_1571_, lean_object* v_x_1572_, lean_object* v_x_1573_, lean_object* v_x_1574_, lean_object* v_x_1575_){
_start:
{
size_t v_x_81056__boxed_1576_; size_t v_x_81057__boxed_1577_; lean_object* v_res_1578_; 
v_x_81056__boxed_1576_ = lean_unbox_usize(v_x_1572_);
lean_dec(v_x_1572_);
v_x_81057__boxed_1577_ = lean_unbox_usize(v_x_1573_);
lean_dec(v_x_1573_);
v_res_1578_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg(v_x_1571_, v_x_81056__boxed_1576_, v_x_81057__boxed_1577_, v_x_1574_, v_x_1575_);
return v_res_1578_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0___redArg(lean_object* v_x_1579_, lean_object* v_x_1580_, lean_object* v_x_1581_){
_start:
{
uint64_t v___x_1582_; size_t v___x_1583_; size_t v___x_1584_; lean_object* v___x_1585_; 
v___x_1582_ = l_Lean_Expr_hash(v_x_1580_);
v___x_1583_ = lean_uint64_to_usize(v___x_1582_);
v___x_1584_ = ((size_t)1ULL);
v___x_1585_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg(v_x_1579_, v___x_1583_, v___x_1584_, v_x_1580_, v_x_1581_);
return v___x_1585_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___lam__0(lean_object* v_a_1586_, lean_object* v_s_1587_){
_start:
{
lean_object* v_toRing_1588_; lean_object* v_invFn_x3f_1589_; lean_object* v_semiringId_x3f_1590_; lean_object* v_commSemiringInst_1591_; lean_object* v_commRingInst_1592_; lean_object* v_noZeroDivInst_x3f_1593_; lean_object* v_fieldInst_x3f_1594_; lean_object* v_powIdentityInst_x3f_1595_; lean_object* v_denoteEntries_1596_; lean_object* v_nextId_1597_; lean_object* v_steps_1598_; lean_object* v_queue_1599_; lean_object* v_basis_1600_; lean_object* v_diseqs_1601_; uint8_t v_recheck_1602_; lean_object* v_invSet_1603_; lean_object* v_powIdentityVarCount_1604_; lean_object* v_numEq0_x3f_1605_; uint8_t v_numEq0Updated_1606_; lean_object* v___x_1608_; uint8_t v_isShared_1609_; uint8_t v_isSharedCheck_1615_; 
v_toRing_1588_ = lean_ctor_get(v_s_1587_, 0);
v_invFn_x3f_1589_ = lean_ctor_get(v_s_1587_, 1);
v_semiringId_x3f_1590_ = lean_ctor_get(v_s_1587_, 2);
v_commSemiringInst_1591_ = lean_ctor_get(v_s_1587_, 3);
v_commRingInst_1592_ = lean_ctor_get(v_s_1587_, 4);
v_noZeroDivInst_x3f_1593_ = lean_ctor_get(v_s_1587_, 5);
v_fieldInst_x3f_1594_ = lean_ctor_get(v_s_1587_, 6);
v_powIdentityInst_x3f_1595_ = lean_ctor_get(v_s_1587_, 7);
v_denoteEntries_1596_ = lean_ctor_get(v_s_1587_, 8);
v_nextId_1597_ = lean_ctor_get(v_s_1587_, 9);
v_steps_1598_ = lean_ctor_get(v_s_1587_, 10);
v_queue_1599_ = lean_ctor_get(v_s_1587_, 11);
v_basis_1600_ = lean_ctor_get(v_s_1587_, 12);
v_diseqs_1601_ = lean_ctor_get(v_s_1587_, 13);
v_recheck_1602_ = lean_ctor_get_uint8(v_s_1587_, sizeof(void*)*17);
v_invSet_1603_ = lean_ctor_get(v_s_1587_, 14);
v_powIdentityVarCount_1604_ = lean_ctor_get(v_s_1587_, 15);
v_numEq0_x3f_1605_ = lean_ctor_get(v_s_1587_, 16);
v_numEq0Updated_1606_ = lean_ctor_get_uint8(v_s_1587_, sizeof(void*)*17 + 1);
v_isSharedCheck_1615_ = !lean_is_exclusive(v_s_1587_);
if (v_isSharedCheck_1615_ == 0)
{
v___x_1608_ = v_s_1587_;
v_isShared_1609_ = v_isSharedCheck_1615_;
goto v_resetjp_1607_;
}
else
{
lean_inc(v_numEq0_x3f_1605_);
lean_inc(v_powIdentityVarCount_1604_);
lean_inc(v_invSet_1603_);
lean_inc(v_diseqs_1601_);
lean_inc(v_basis_1600_);
lean_inc(v_queue_1599_);
lean_inc(v_steps_1598_);
lean_inc(v_nextId_1597_);
lean_inc(v_denoteEntries_1596_);
lean_inc(v_powIdentityInst_x3f_1595_);
lean_inc(v_fieldInst_x3f_1594_);
lean_inc(v_noZeroDivInst_x3f_1593_);
lean_inc(v_commRingInst_1592_);
lean_inc(v_commSemiringInst_1591_);
lean_inc(v_semiringId_x3f_1590_);
lean_inc(v_invFn_x3f_1589_);
lean_inc(v_toRing_1588_);
lean_dec(v_s_1587_);
v___x_1608_ = lean_box(0);
v_isShared_1609_ = v_isSharedCheck_1615_;
goto v_resetjp_1607_;
}
v_resetjp_1607_:
{
lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1613_; 
v___x_1610_ = lean_box(0);
v___x_1611_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0___redArg(v_invSet_1603_, v_a_1586_, v___x_1610_);
if (v_isShared_1609_ == 0)
{
lean_ctor_set(v___x_1608_, 14, v___x_1611_);
v___x_1613_ = v___x_1608_;
goto v_reusejp_1612_;
}
else
{
lean_object* v_reuseFailAlloc_1614_; 
v_reuseFailAlloc_1614_ = lean_alloc_ctor(0, 17, 2);
lean_ctor_set(v_reuseFailAlloc_1614_, 0, v_toRing_1588_);
lean_ctor_set(v_reuseFailAlloc_1614_, 1, v_invFn_x3f_1589_);
lean_ctor_set(v_reuseFailAlloc_1614_, 2, v_semiringId_x3f_1590_);
lean_ctor_set(v_reuseFailAlloc_1614_, 3, v_commSemiringInst_1591_);
lean_ctor_set(v_reuseFailAlloc_1614_, 4, v_commRingInst_1592_);
lean_ctor_set(v_reuseFailAlloc_1614_, 5, v_noZeroDivInst_x3f_1593_);
lean_ctor_set(v_reuseFailAlloc_1614_, 6, v_fieldInst_x3f_1594_);
lean_ctor_set(v_reuseFailAlloc_1614_, 7, v_powIdentityInst_x3f_1595_);
lean_ctor_set(v_reuseFailAlloc_1614_, 8, v_denoteEntries_1596_);
lean_ctor_set(v_reuseFailAlloc_1614_, 9, v_nextId_1597_);
lean_ctor_set(v_reuseFailAlloc_1614_, 10, v_steps_1598_);
lean_ctor_set(v_reuseFailAlloc_1614_, 11, v_queue_1599_);
lean_ctor_set(v_reuseFailAlloc_1614_, 12, v_basis_1600_);
lean_ctor_set(v_reuseFailAlloc_1614_, 13, v_diseqs_1601_);
lean_ctor_set(v_reuseFailAlloc_1614_, 14, v___x_1611_);
lean_ctor_set(v_reuseFailAlloc_1614_, 15, v_powIdentityVarCount_1604_);
lean_ctor_set(v_reuseFailAlloc_1614_, 16, v_numEq0_x3f_1605_);
lean_ctor_set_uint8(v_reuseFailAlloc_1614_, sizeof(void*)*17, v_recheck_1602_);
lean_ctor_set_uint8(v_reuseFailAlloc_1614_, sizeof(void*)*17 + 1, v_numEq0Updated_1606_);
v___x_1613_ = v_reuseFailAlloc_1614_;
goto v_reusejp_1612_;
}
v_reusejp_1612_:
{
return v___x_1613_;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__4___closed__1(void){
_start:
{
lean_object* v___x_1618_; lean_object* v___x_1619_; 
v___x_1618_ = lean_unsigned_to_nat(0u);
v___x_1619_ = lean_nat_to_int(v___x_1618_);
return v___x_1619_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__4(lean_object* v_k_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_){
_start:
{
lean_object* v___x_1638_; 
v___x_1638_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_);
if (lean_obj_tag(v___x_1638_) == 0)
{
lean_object* v_a_1639_; lean_object* v_toRing_1640_; lean_object* v_type_1641_; lean_object* v_u_1642_; lean_object* v_semiringInst_1643_; lean_object* v___x_1644_; lean_object* v_n_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; 
v_a_1639_ = lean_ctor_get(v___x_1638_, 0);
lean_inc(v_a_1639_);
lean_dec_ref_known(v___x_1638_, 1);
v_toRing_1640_ = lean_ctor_get(v_a_1639_, 0);
lean_inc_ref(v_toRing_1640_);
lean_dec(v_a_1639_);
v_type_1641_ = lean_ctor_get(v_toRing_1640_, 1);
lean_inc_ref_n(v_type_1641_, 2);
v_u_1642_ = lean_ctor_get(v_toRing_1640_, 2);
lean_inc(v_u_1642_);
v_semiringInst_1643_ = lean_ctor_get(v_toRing_1640_, 4);
lean_inc_ref(v_semiringInst_1643_);
lean_dec_ref(v_toRing_1640_);
v___x_1644_ = lean_nat_abs(v_k_1625_);
v_n_1645_ = l_Lean_mkRawNatLit(v___x_1644_);
v___x_1646_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__4___closed__0));
v___x_1647_ = lean_box(0);
v___x_1648_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1648_, 0, v_u_1642_);
lean_ctor_set(v___x_1648_, 1, v___x_1647_);
lean_inc_ref(v___x_1648_);
v___x_1649_ = l_Lean_mkConst(v___x_1646_, v___x_1648_);
lean_inc_ref(v_n_1645_);
v___x_1650_ = l_Lean_mkAppB(v___x_1649_, v_type_1641_, v_n_1645_);
v___x_1651_ = lean_box(0);
v___x_1652_ = l_Lean_Meta_synthInstance_x3f(v___x_1650_, v___x_1651_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_);
if (lean_obj_tag(v___x_1652_) == 0)
{
lean_object* v_a_1653_; lean_object* v___x_1655_; uint8_t v_isShared_1656_; uint8_t v_isSharedCheck_1692_; 
v_a_1653_ = lean_ctor_get(v___x_1652_, 0);
v_isSharedCheck_1692_ = !lean_is_exclusive(v___x_1652_);
if (v_isSharedCheck_1692_ == 0)
{
v___x_1655_ = v___x_1652_;
v_isShared_1656_ = v_isSharedCheck_1692_;
goto v_resetjp_1654_;
}
else
{
lean_inc(v_a_1653_);
lean_dec(v___x_1652_);
v___x_1655_ = lean_box(0);
v_isShared_1656_ = v_isSharedCheck_1692_;
goto v_resetjp_1654_;
}
v_resetjp_1654_:
{
lean_object* v_ofNatInst_1658_; lean_object* v___y_1659_; lean_object* v___y_1660_; lean_object* v___y_1661_; lean_object* v___y_1662_; lean_object* v___y_1663_; lean_object* v___y_1664_; lean_object* v___y_1665_; lean_object* v___y_1666_; lean_object* v___y_1667_; lean_object* v___y_1668_; lean_object* v___y_1669_; 
if (lean_obj_tag(v_a_1653_) == 1)
{
lean_object* v_val_1688_; 
lean_dec_ref(v_semiringInst_1643_);
v_val_1688_ = lean_ctor_get(v_a_1653_, 0);
lean_inc(v_val_1688_);
lean_dec_ref_known(v_a_1653_, 1);
v_ofNatInst_1658_ = v_val_1688_;
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
v___y_1669_ = v___y_1636_;
goto v___jp_1657_;
}
else
{
lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; 
lean_dec(v_a_1653_);
v___x_1689_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__4___closed__2));
lean_inc_ref(v___x_1648_);
v___x_1690_ = l_Lean_mkConst(v___x_1689_, v___x_1648_);
lean_inc_ref(v_n_1645_);
lean_inc_ref(v_type_1641_);
v___x_1691_ = l_Lean_mkApp3(v___x_1690_, v_type_1641_, v_semiringInst_1643_, v_n_1645_);
v_ofNatInst_1658_ = v___x_1691_;
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
v___y_1669_ = v___y_1636_;
goto v___jp_1657_;
}
v___jp_1657_:
{
lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v_n_1672_; lean_object* v___x_1673_; uint8_t v___x_1674_; 
v___x_1670_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__8));
v___x_1671_ = l_Lean_mkConst(v___x_1670_, v___x_1648_);
v_n_1672_ = l_Lean_mkApp3(v___x_1671_, v_type_1641_, v_n_1645_, v_ofNatInst_1658_);
v___x_1673_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__4___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__4___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__4___closed__1);
v___x_1674_ = lean_int_dec_lt(v_k_1625_, v___x_1673_);
if (v___x_1674_ == 0)
{
lean_object* v___x_1676_; 
if (v_isShared_1656_ == 0)
{
lean_ctor_set(v___x_1655_, 0, v_n_1672_);
v___x_1676_ = v___x_1655_;
goto v_reusejp_1675_;
}
else
{
lean_object* v_reuseFailAlloc_1677_; 
v_reuseFailAlloc_1677_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1677_, 0, v_n_1672_);
v___x_1676_ = v_reuseFailAlloc_1677_;
goto v_reusejp_1675_;
}
v_reusejp_1675_:
{
return v___x_1676_;
}
}
else
{
lean_object* v___x_1678_; 
lean_del_object(v___x_1655_);
v___x_1678_ = l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0(v___y_1659_, v___y_1660_, v___y_1661_, v___y_1662_, v___y_1663_, v___y_1664_, v___y_1665_, v___y_1666_, v___y_1667_, v___y_1668_, v___y_1669_);
if (lean_obj_tag(v___x_1678_) == 0)
{
lean_object* v_a_1679_; lean_object* v___x_1681_; uint8_t v_isShared_1682_; uint8_t v_isSharedCheck_1687_; 
v_a_1679_ = lean_ctor_get(v___x_1678_, 0);
v_isSharedCheck_1687_ = !lean_is_exclusive(v___x_1678_);
if (v_isSharedCheck_1687_ == 0)
{
v___x_1681_ = v___x_1678_;
v_isShared_1682_ = v_isSharedCheck_1687_;
goto v_resetjp_1680_;
}
else
{
lean_inc(v_a_1679_);
lean_dec(v___x_1678_);
v___x_1681_ = lean_box(0);
v_isShared_1682_ = v_isSharedCheck_1687_;
goto v_resetjp_1680_;
}
v_resetjp_1680_:
{
lean_object* v___x_1683_; lean_object* v___x_1685_; 
v___x_1683_ = l_Lean_Expr_app___override(v_a_1679_, v_n_1672_);
if (v_isShared_1682_ == 0)
{
lean_ctor_set(v___x_1681_, 0, v___x_1683_);
v___x_1685_ = v___x_1681_;
goto v_reusejp_1684_;
}
else
{
lean_object* v_reuseFailAlloc_1686_; 
v_reuseFailAlloc_1686_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1686_, 0, v___x_1683_);
v___x_1685_ = v_reuseFailAlloc_1686_;
goto v_reusejp_1684_;
}
v_reusejp_1684_:
{
return v___x_1685_;
}
}
}
else
{
lean_dec_ref(v_n_1672_);
return v___x_1678_;
}
}
}
}
}
else
{
lean_object* v_a_1693_; lean_object* v___x_1695_; uint8_t v_isShared_1696_; uint8_t v_isSharedCheck_1700_; 
lean_dec_ref_known(v___x_1648_, 2);
lean_dec_ref(v_n_1645_);
lean_dec_ref(v_semiringInst_1643_);
lean_dec_ref(v_type_1641_);
v_a_1693_ = lean_ctor_get(v___x_1652_, 0);
v_isSharedCheck_1700_ = !lean_is_exclusive(v___x_1652_);
if (v_isSharedCheck_1700_ == 0)
{
v___x_1695_ = v___x_1652_;
v_isShared_1696_ = v_isSharedCheck_1700_;
goto v_resetjp_1694_;
}
else
{
lean_inc(v_a_1693_);
lean_dec(v___x_1652_);
v___x_1695_ = lean_box(0);
v_isShared_1696_ = v_isSharedCheck_1700_;
goto v_resetjp_1694_;
}
v_resetjp_1694_:
{
lean_object* v___x_1698_; 
if (v_isShared_1696_ == 0)
{
v___x_1698_ = v___x_1695_;
goto v_reusejp_1697_;
}
else
{
lean_object* v_reuseFailAlloc_1699_; 
v_reuseFailAlloc_1699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1699_, 0, v_a_1693_);
v___x_1698_ = v_reuseFailAlloc_1699_;
goto v_reusejp_1697_;
}
v_reusejp_1697_:
{
return v___x_1698_;
}
}
}
}
else
{
lean_object* v_a_1701_; lean_object* v___x_1703_; uint8_t v_isShared_1704_; uint8_t v_isSharedCheck_1708_; 
v_a_1701_ = lean_ctor_get(v___x_1638_, 0);
v_isSharedCheck_1708_ = !lean_is_exclusive(v___x_1638_);
if (v_isSharedCheck_1708_ == 0)
{
v___x_1703_ = v___x_1638_;
v_isShared_1704_ = v_isSharedCheck_1708_;
goto v_resetjp_1702_;
}
else
{
lean_inc(v_a_1701_);
lean_dec(v___x_1638_);
v___x_1703_ = lean_box(0);
v_isShared_1704_ = v_isSharedCheck_1708_;
goto v_resetjp_1702_;
}
v_resetjp_1702_:
{
lean_object* v___x_1706_; 
if (v_isShared_1704_ == 0)
{
v___x_1706_ = v___x_1703_;
goto v_reusejp_1705_;
}
else
{
lean_object* v_reuseFailAlloc_1707_; 
v_reuseFailAlloc_1707_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1707_, 0, v_a_1701_);
v___x_1706_ = v_reuseFailAlloc_1707_;
goto v_reusejp_1705_;
}
v_reusejp_1705_:
{
return v___x_1706_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__4___boxed(lean_object* v_k_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_){
_start:
{
lean_object* v_res_1722_; 
v_res_1722_ = l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__4(v_k_1709_, v___y_1710_, v___y_1711_, v___y_1712_, v___y_1713_, v___y_1714_, v___y_1715_, v___y_1716_, v___y_1717_, v___y_1718_, v___y_1719_, v___y_1720_);
lean_dec(v___y_1720_);
lean_dec_ref(v___y_1719_);
lean_dec(v___y_1718_);
lean_dec_ref(v___y_1717_);
lean_dec(v___y_1716_);
lean_dec_ref(v___y_1715_);
lean_dec(v___y_1714_);
lean_dec_ref(v___y_1713_);
lean_dec(v___y_1712_);
lean_dec(v___y_1711_);
lean_dec_ref(v___y_1710_);
lean_dec(v_k_1709_);
return v_res_1722_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1_spec__2_spec__6___redArg(lean_object* v_keys_1723_, lean_object* v_i_1724_, lean_object* v_k_1725_){
_start:
{
lean_object* v___x_1726_; uint8_t v___x_1727_; 
v___x_1726_ = lean_array_get_size(v_keys_1723_);
v___x_1727_ = lean_nat_dec_lt(v_i_1724_, v___x_1726_);
if (v___x_1727_ == 0)
{
lean_dec(v_i_1724_);
return v___x_1727_;
}
else
{
lean_object* v_k_x27_1728_; uint8_t v___x_1729_; 
v_k_x27_1728_ = lean_array_fget_borrowed(v_keys_1723_, v_i_1724_);
v___x_1729_ = lean_expr_eqv(v_k_1725_, v_k_x27_1728_);
if (v___x_1729_ == 0)
{
lean_object* v___x_1730_; lean_object* v___x_1731_; 
v___x_1730_ = lean_unsigned_to_nat(1u);
v___x_1731_ = lean_nat_add(v_i_1724_, v___x_1730_);
lean_dec(v_i_1724_);
v_i_1724_ = v___x_1731_;
goto _start;
}
else
{
lean_dec(v_i_1724_);
return v___x_1727_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1_spec__2_spec__6___redArg___boxed(lean_object* v_keys_1733_, lean_object* v_i_1734_, lean_object* v_k_1735_){
_start:
{
uint8_t v_res_1736_; lean_object* v_r_1737_; 
v_res_1736_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1_spec__2_spec__6___redArg(v_keys_1733_, v_i_1734_, v_k_1735_);
lean_dec_ref(v_k_1735_);
lean_dec_ref(v_keys_1733_);
v_r_1737_ = lean_box(v_res_1736_);
return v_r_1737_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1_spec__2___redArg(lean_object* v_x_1738_, size_t v_x_1739_, lean_object* v_x_1740_){
_start:
{
if (lean_obj_tag(v_x_1738_) == 0)
{
lean_object* v_es_1741_; lean_object* v___x_1742_; size_t v___x_1743_; size_t v___x_1744_; lean_object* v_j_1745_; lean_object* v___x_1746_; 
v_es_1741_ = lean_ctor_get(v_x_1738_, 0);
v___x_1742_ = lean_box(2);
v___x_1743_ = ((size_t)31ULL);
v___x_1744_ = lean_usize_land(v_x_1739_, v___x_1743_);
v_j_1745_ = lean_usize_to_nat(v___x_1744_);
v___x_1746_ = lean_array_get_borrowed(v___x_1742_, v_es_1741_, v_j_1745_);
lean_dec(v_j_1745_);
switch(lean_obj_tag(v___x_1746_))
{
case 0:
{
lean_object* v_key_1747_; uint8_t v___x_1748_; 
v_key_1747_ = lean_ctor_get(v___x_1746_, 0);
v___x_1748_ = lean_expr_eqv(v_x_1740_, v_key_1747_);
return v___x_1748_;
}
case 1:
{
lean_object* v_node_1749_; size_t v___x_1750_; size_t v___x_1751_; 
v_node_1749_ = lean_ctor_get(v___x_1746_, 0);
v___x_1750_ = ((size_t)5ULL);
v___x_1751_ = lean_usize_shift_right(v_x_1739_, v___x_1750_);
v_x_1738_ = v_node_1749_;
v_x_1739_ = v___x_1751_;
goto _start;
}
default: 
{
uint8_t v___x_1753_; 
v___x_1753_ = 0;
return v___x_1753_;
}
}
}
else
{
lean_object* v_ks_1754_; lean_object* v___x_1755_; uint8_t v___x_1756_; 
v_ks_1754_ = lean_ctor_get(v_x_1738_, 0);
v___x_1755_ = lean_unsigned_to_nat(0u);
v___x_1756_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1_spec__2_spec__6___redArg(v_ks_1754_, v___x_1755_, v_x_1740_);
return v___x_1756_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1_spec__2___redArg___boxed(lean_object* v_x_1757_, lean_object* v_x_1758_, lean_object* v_x_1759_){
_start:
{
size_t v_x_81453__boxed_1760_; uint8_t v_res_1761_; lean_object* v_r_1762_; 
v_x_81453__boxed_1760_ = lean_unbox_usize(v_x_1758_);
lean_dec(v_x_1758_);
v_res_1761_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1_spec__2___redArg(v_x_1757_, v_x_81453__boxed_1760_, v_x_1759_);
lean_dec_ref(v_x_1759_);
lean_dec_ref(v_x_1757_);
v_r_1762_ = lean_box(v_res_1761_);
return v_r_1762_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1___redArg(lean_object* v_x_1763_, lean_object* v_x_1764_){
_start:
{
uint64_t v___x_1765_; size_t v___x_1766_; uint8_t v___x_1767_; 
v___x_1765_ = l_Lean_Expr_hash(v_x_1764_);
v___x_1766_ = lean_uint64_to_usize(v___x_1765_);
v___x_1767_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1_spec__2___redArg(v_x_1763_, v___x_1766_, v_x_1764_);
return v___x_1767_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1___redArg___boxed(lean_object* v_x_1768_, lean_object* v_x_1769_){
_start:
{
uint8_t v_res_1770_; lean_object* v_r_1771_; 
v_res_1770_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1___redArg(v_x_1768_, v_x_1769_);
lean_dec_ref(v_x_1769_);
lean_dec_ref(v_x_1768_);
v_r_1771_ = lean_box(v_res_1770_);
return v_r_1771_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__3___lam__0(lean_object* v_a_1772_, lean_object* v_s_1773_){
_start:
{
lean_object* v_toRing_1774_; lean_object* v_invFn_x3f_1775_; lean_object* v_semiringId_x3f_1776_; lean_object* v_commSemiringInst_1777_; lean_object* v_commRingInst_1778_; lean_object* v_noZeroDivInst_x3f_1779_; lean_object* v_fieldInst_x3f_1780_; lean_object* v_powIdentityInst_x3f_1781_; lean_object* v_denoteEntries_1782_; lean_object* v_nextId_1783_; lean_object* v_steps_1784_; lean_object* v_queue_1785_; lean_object* v_basis_1786_; lean_object* v_diseqs_1787_; uint8_t v_recheck_1788_; lean_object* v_invSet_1789_; lean_object* v_powIdentityVarCount_1790_; lean_object* v_numEq0_x3f_1791_; uint8_t v_numEq0Updated_1792_; lean_object* v___x_1794_; uint8_t v_isShared_1795_; uint8_t v_isSharedCheck_1824_; 
v_toRing_1774_ = lean_ctor_get(v_s_1773_, 0);
v_invFn_x3f_1775_ = lean_ctor_get(v_s_1773_, 1);
v_semiringId_x3f_1776_ = lean_ctor_get(v_s_1773_, 2);
v_commSemiringInst_1777_ = lean_ctor_get(v_s_1773_, 3);
v_commRingInst_1778_ = lean_ctor_get(v_s_1773_, 4);
v_noZeroDivInst_x3f_1779_ = lean_ctor_get(v_s_1773_, 5);
v_fieldInst_x3f_1780_ = lean_ctor_get(v_s_1773_, 6);
v_powIdentityInst_x3f_1781_ = lean_ctor_get(v_s_1773_, 7);
v_denoteEntries_1782_ = lean_ctor_get(v_s_1773_, 8);
v_nextId_1783_ = lean_ctor_get(v_s_1773_, 9);
v_steps_1784_ = lean_ctor_get(v_s_1773_, 10);
v_queue_1785_ = lean_ctor_get(v_s_1773_, 11);
v_basis_1786_ = lean_ctor_get(v_s_1773_, 12);
v_diseqs_1787_ = lean_ctor_get(v_s_1773_, 13);
v_recheck_1788_ = lean_ctor_get_uint8(v_s_1773_, sizeof(void*)*17);
v_invSet_1789_ = lean_ctor_get(v_s_1773_, 14);
v_powIdentityVarCount_1790_ = lean_ctor_get(v_s_1773_, 15);
v_numEq0_x3f_1791_ = lean_ctor_get(v_s_1773_, 16);
v_numEq0Updated_1792_ = lean_ctor_get_uint8(v_s_1773_, sizeof(void*)*17 + 1);
v_isSharedCheck_1824_ = !lean_is_exclusive(v_s_1773_);
if (v_isSharedCheck_1824_ == 0)
{
v___x_1794_ = v_s_1773_;
v_isShared_1795_ = v_isSharedCheck_1824_;
goto v_resetjp_1793_;
}
else
{
lean_inc(v_numEq0_x3f_1791_);
lean_inc(v_powIdentityVarCount_1790_);
lean_inc(v_invSet_1789_);
lean_inc(v_diseqs_1787_);
lean_inc(v_basis_1786_);
lean_inc(v_queue_1785_);
lean_inc(v_steps_1784_);
lean_inc(v_nextId_1783_);
lean_inc(v_denoteEntries_1782_);
lean_inc(v_powIdentityInst_x3f_1781_);
lean_inc(v_fieldInst_x3f_1780_);
lean_inc(v_noZeroDivInst_x3f_1779_);
lean_inc(v_commRingInst_1778_);
lean_inc(v_commSemiringInst_1777_);
lean_inc(v_semiringId_x3f_1776_);
lean_inc(v_invFn_x3f_1775_);
lean_inc(v_toRing_1774_);
lean_dec(v_s_1773_);
v___x_1794_ = lean_box(0);
v_isShared_1795_ = v_isSharedCheck_1824_;
goto v_resetjp_1793_;
}
v_resetjp_1793_:
{
lean_object* v_id_1796_; lean_object* v_type_1797_; lean_object* v_u_1798_; lean_object* v_ringInst_1799_; lean_object* v_semiringInst_1800_; lean_object* v_charInst_x3f_1801_; lean_object* v_addFn_x3f_1802_; lean_object* v_subFn_x3f_1803_; lean_object* v_negFn_x3f_1804_; lean_object* v_powFn_x3f_1805_; lean_object* v_intCastFn_x3f_1806_; lean_object* v_natCastFn_x3f_1807_; lean_object* v_one_x3f_1808_; lean_object* v_vars_1809_; lean_object* v_varMap_1810_; lean_object* v_denote_1811_; lean_object* v___x_1813_; uint8_t v_isShared_1814_; uint8_t v_isSharedCheck_1822_; 
v_id_1796_ = lean_ctor_get(v_toRing_1774_, 0);
v_type_1797_ = lean_ctor_get(v_toRing_1774_, 1);
v_u_1798_ = lean_ctor_get(v_toRing_1774_, 2);
v_ringInst_1799_ = lean_ctor_get(v_toRing_1774_, 3);
v_semiringInst_1800_ = lean_ctor_get(v_toRing_1774_, 4);
v_charInst_x3f_1801_ = lean_ctor_get(v_toRing_1774_, 5);
v_addFn_x3f_1802_ = lean_ctor_get(v_toRing_1774_, 6);
v_subFn_x3f_1803_ = lean_ctor_get(v_toRing_1774_, 8);
v_negFn_x3f_1804_ = lean_ctor_get(v_toRing_1774_, 9);
v_powFn_x3f_1805_ = lean_ctor_get(v_toRing_1774_, 10);
v_intCastFn_x3f_1806_ = lean_ctor_get(v_toRing_1774_, 11);
v_natCastFn_x3f_1807_ = lean_ctor_get(v_toRing_1774_, 12);
v_one_x3f_1808_ = lean_ctor_get(v_toRing_1774_, 13);
v_vars_1809_ = lean_ctor_get(v_toRing_1774_, 14);
v_varMap_1810_ = lean_ctor_get(v_toRing_1774_, 15);
v_denote_1811_ = lean_ctor_get(v_toRing_1774_, 16);
v_isSharedCheck_1822_ = !lean_is_exclusive(v_toRing_1774_);
if (v_isSharedCheck_1822_ == 0)
{
lean_object* v_unused_1823_; 
v_unused_1823_ = lean_ctor_get(v_toRing_1774_, 7);
lean_dec(v_unused_1823_);
v___x_1813_ = v_toRing_1774_;
v_isShared_1814_ = v_isSharedCheck_1822_;
goto v_resetjp_1812_;
}
else
{
lean_inc(v_denote_1811_);
lean_inc(v_varMap_1810_);
lean_inc(v_vars_1809_);
lean_inc(v_one_x3f_1808_);
lean_inc(v_natCastFn_x3f_1807_);
lean_inc(v_intCastFn_x3f_1806_);
lean_inc(v_powFn_x3f_1805_);
lean_inc(v_negFn_x3f_1804_);
lean_inc(v_subFn_x3f_1803_);
lean_inc(v_addFn_x3f_1802_);
lean_inc(v_charInst_x3f_1801_);
lean_inc(v_semiringInst_1800_);
lean_inc(v_ringInst_1799_);
lean_inc(v_u_1798_);
lean_inc(v_type_1797_);
lean_inc(v_id_1796_);
lean_dec(v_toRing_1774_);
v___x_1813_ = lean_box(0);
v_isShared_1814_ = v_isSharedCheck_1822_;
goto v_resetjp_1812_;
}
v_resetjp_1812_:
{
lean_object* v___x_1815_; lean_object* v___x_1817_; 
v___x_1815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1815_, 0, v_a_1772_);
if (v_isShared_1814_ == 0)
{
lean_ctor_set(v___x_1813_, 7, v___x_1815_);
v___x_1817_ = v___x_1813_;
goto v_reusejp_1816_;
}
else
{
lean_object* v_reuseFailAlloc_1821_; 
v_reuseFailAlloc_1821_ = lean_alloc_ctor(0, 17, 0);
lean_ctor_set(v_reuseFailAlloc_1821_, 0, v_id_1796_);
lean_ctor_set(v_reuseFailAlloc_1821_, 1, v_type_1797_);
lean_ctor_set(v_reuseFailAlloc_1821_, 2, v_u_1798_);
lean_ctor_set(v_reuseFailAlloc_1821_, 3, v_ringInst_1799_);
lean_ctor_set(v_reuseFailAlloc_1821_, 4, v_semiringInst_1800_);
lean_ctor_set(v_reuseFailAlloc_1821_, 5, v_charInst_x3f_1801_);
lean_ctor_set(v_reuseFailAlloc_1821_, 6, v_addFn_x3f_1802_);
lean_ctor_set(v_reuseFailAlloc_1821_, 7, v___x_1815_);
lean_ctor_set(v_reuseFailAlloc_1821_, 8, v_subFn_x3f_1803_);
lean_ctor_set(v_reuseFailAlloc_1821_, 9, v_negFn_x3f_1804_);
lean_ctor_set(v_reuseFailAlloc_1821_, 10, v_powFn_x3f_1805_);
lean_ctor_set(v_reuseFailAlloc_1821_, 11, v_intCastFn_x3f_1806_);
lean_ctor_set(v_reuseFailAlloc_1821_, 12, v_natCastFn_x3f_1807_);
lean_ctor_set(v_reuseFailAlloc_1821_, 13, v_one_x3f_1808_);
lean_ctor_set(v_reuseFailAlloc_1821_, 14, v_vars_1809_);
lean_ctor_set(v_reuseFailAlloc_1821_, 15, v_varMap_1810_);
lean_ctor_set(v_reuseFailAlloc_1821_, 16, v_denote_1811_);
v___x_1817_ = v_reuseFailAlloc_1821_;
goto v_reusejp_1816_;
}
v_reusejp_1816_:
{
lean_object* v___x_1819_; 
if (v_isShared_1795_ == 0)
{
lean_ctor_set(v___x_1794_, 0, v___x_1817_);
v___x_1819_ = v___x_1794_;
goto v_reusejp_1818_;
}
else
{
lean_object* v_reuseFailAlloc_1820_; 
v_reuseFailAlloc_1820_ = lean_alloc_ctor(0, 17, 2);
lean_ctor_set(v_reuseFailAlloc_1820_, 0, v___x_1817_);
lean_ctor_set(v_reuseFailAlloc_1820_, 1, v_invFn_x3f_1775_);
lean_ctor_set(v_reuseFailAlloc_1820_, 2, v_semiringId_x3f_1776_);
lean_ctor_set(v_reuseFailAlloc_1820_, 3, v_commSemiringInst_1777_);
lean_ctor_set(v_reuseFailAlloc_1820_, 4, v_commRingInst_1778_);
lean_ctor_set(v_reuseFailAlloc_1820_, 5, v_noZeroDivInst_x3f_1779_);
lean_ctor_set(v_reuseFailAlloc_1820_, 6, v_fieldInst_x3f_1780_);
lean_ctor_set(v_reuseFailAlloc_1820_, 7, v_powIdentityInst_x3f_1781_);
lean_ctor_set(v_reuseFailAlloc_1820_, 8, v_denoteEntries_1782_);
lean_ctor_set(v_reuseFailAlloc_1820_, 9, v_nextId_1783_);
lean_ctor_set(v_reuseFailAlloc_1820_, 10, v_steps_1784_);
lean_ctor_set(v_reuseFailAlloc_1820_, 11, v_queue_1785_);
lean_ctor_set(v_reuseFailAlloc_1820_, 12, v_basis_1786_);
lean_ctor_set(v_reuseFailAlloc_1820_, 13, v_diseqs_1787_);
lean_ctor_set(v_reuseFailAlloc_1820_, 14, v_invSet_1789_);
lean_ctor_set(v_reuseFailAlloc_1820_, 15, v_powIdentityVarCount_1790_);
lean_ctor_set(v_reuseFailAlloc_1820_, 16, v_numEq0_x3f_1791_);
lean_ctor_set_uint8(v_reuseFailAlloc_1820_, sizeof(void*)*17, v_recheck_1788_);
lean_ctor_set_uint8(v_reuseFailAlloc_1820_, sizeof(void*)*17 + 1, v_numEq0Updated_1792_);
v___x_1819_ = v_reuseFailAlloc_1820_;
goto v_reusejp_1818_;
}
v_reusejp_1818_:
{
return v___x_1819_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__3_spec__5(lean_object* v_type_1825_, lean_object* v_u_1826_, lean_object* v_instDeclName_1827_, lean_object* v_declName_1828_, lean_object* v_expectedInst_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_){
_start:
{
lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; 
v___x_1842_ = lean_box(0);
lean_inc_n(v_u_1826_, 2);
v___x_1843_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1843_, 0, v_u_1826_);
lean_ctor_set(v___x_1843_, 1, v___x_1842_);
v___x_1844_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1844_, 0, v_u_1826_);
lean_ctor_set(v___x_1844_, 1, v___x_1843_);
v___x_1845_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1845_, 0, v_u_1826_);
lean_ctor_set(v___x_1845_, 1, v___x_1844_);
lean_inc_ref(v___x_1845_);
v___x_1846_ = l_Lean_mkConst(v_instDeclName_1827_, v___x_1845_);
lean_inc_ref_n(v_type_1825_, 3);
v___x_1847_ = l_Lean_mkApp3(v___x_1846_, v_type_1825_, v_type_1825_, v_type_1825_);
v___x_1848_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1_spec__5(v___x_1847_, v___y_1830_, v___y_1831_, v___y_1832_, v___y_1833_, v___y_1834_, v___y_1835_, v___y_1836_, v___y_1837_, v___y_1838_, v___y_1839_, v___y_1840_);
if (lean_obj_tag(v___x_1848_) == 0)
{
lean_object* v_a_1849_; lean_object* v___x_1850_; 
v_a_1849_ = lean_ctor_get(v___x_1848_, 0);
lean_inc_n(v_a_1849_, 2);
lean_dec_ref_known(v___x_1848_, 1);
lean_inc(v_declName_1828_);
v___x_1850_ = l_Lean_Meta_Grind_Arith_CommRing_checkInst(v_declName_1828_, v_a_1849_, v_expectedInst_1829_, v___y_1837_, v___y_1838_, v___y_1839_, v___y_1840_);
if (lean_obj_tag(v___x_1850_) == 0)
{
lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; 
lean_dec_ref_known(v___x_1850_, 1);
v___x_1851_ = l_Lean_mkConst(v_declName_1828_, v___x_1845_);
lean_inc_ref_n(v_type_1825_, 2);
v___x_1852_ = l_Lean_mkApp4(v___x_1851_, v_type_1825_, v_type_1825_, v_type_1825_, v_a_1849_);
v___x_1853_ = l_Lean_Meta_Sym_canon(v___x_1852_, v___y_1835_, v___y_1836_, v___y_1837_, v___y_1838_, v___y_1839_, v___y_1840_);
if (lean_obj_tag(v___x_1853_) == 0)
{
lean_object* v_a_1854_; lean_object* v___x_1855_; 
v_a_1854_ = lean_ctor_get(v___x_1853_, 0);
lean_inc(v_a_1854_);
lean_dec_ref_known(v___x_1853_, 1);
v___x_1855_ = l_Lean_Meta_Sym_shareCommon(v_a_1854_, v___y_1835_, v___y_1836_, v___y_1837_, v___y_1838_, v___y_1839_, v___y_1840_);
return v___x_1855_;
}
else
{
return v___x_1853_;
}
}
else
{
lean_object* v_a_1856_; lean_object* v___x_1858_; uint8_t v_isShared_1859_; uint8_t v_isSharedCheck_1863_; 
lean_dec(v_a_1849_);
lean_dec_ref_known(v___x_1845_, 2);
lean_dec(v_declName_1828_);
lean_dec_ref(v_type_1825_);
v_a_1856_ = lean_ctor_get(v___x_1850_, 0);
v_isSharedCheck_1863_ = !lean_is_exclusive(v___x_1850_);
if (v_isSharedCheck_1863_ == 0)
{
v___x_1858_ = v___x_1850_;
v_isShared_1859_ = v_isSharedCheck_1863_;
goto v_resetjp_1857_;
}
else
{
lean_inc(v_a_1856_);
lean_dec(v___x_1850_);
v___x_1858_ = lean_box(0);
v_isShared_1859_ = v_isSharedCheck_1863_;
goto v_resetjp_1857_;
}
v_resetjp_1857_:
{
lean_object* v___x_1861_; 
if (v_isShared_1859_ == 0)
{
v___x_1861_ = v___x_1858_;
goto v_reusejp_1860_;
}
else
{
lean_object* v_reuseFailAlloc_1862_; 
v_reuseFailAlloc_1862_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1862_, 0, v_a_1856_);
v___x_1861_ = v_reuseFailAlloc_1862_;
goto v_reusejp_1860_;
}
v_reusejp_1860_:
{
return v___x_1861_;
}
}
}
}
else
{
lean_dec_ref_known(v___x_1845_, 2);
lean_dec_ref(v_expectedInst_1829_);
lean_dec(v_declName_1828_);
lean_dec_ref(v_type_1825_);
return v___x_1848_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__3_spec__5___boxed(lean_object** _args){
lean_object* v_type_1864_ = _args[0];
lean_object* v_u_1865_ = _args[1];
lean_object* v_instDeclName_1866_ = _args[2];
lean_object* v_declName_1867_ = _args[3];
lean_object* v_expectedInst_1868_ = _args[4];
lean_object* v___y_1869_ = _args[5];
lean_object* v___y_1870_ = _args[6];
lean_object* v___y_1871_ = _args[7];
lean_object* v___y_1872_ = _args[8];
lean_object* v___y_1873_ = _args[9];
lean_object* v___y_1874_ = _args[10];
lean_object* v___y_1875_ = _args[11];
lean_object* v___y_1876_ = _args[12];
lean_object* v___y_1877_ = _args[13];
lean_object* v___y_1878_ = _args[14];
lean_object* v___y_1879_ = _args[15];
lean_object* v___y_1880_ = _args[16];
_start:
{
lean_object* v_res_1881_; 
v_res_1881_ = l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__3_spec__5(v_type_1864_, v_u_1865_, v_instDeclName_1866_, v_declName_1867_, v_expectedInst_1868_, v___y_1869_, v___y_1870_, v___y_1871_, v___y_1872_, v___y_1873_, v___y_1874_, v___y_1875_, v___y_1876_, v___y_1877_, v___y_1878_, v___y_1879_);
lean_dec(v___y_1879_);
lean_dec_ref(v___y_1878_);
lean_dec(v___y_1877_);
lean_dec_ref(v___y_1876_);
lean_dec(v___y_1875_);
lean_dec_ref(v___y_1874_);
lean_dec(v___y_1873_);
lean_dec_ref(v___y_1872_);
lean_dec(v___y_1871_);
lean_dec(v___y_1870_);
lean_dec_ref(v___y_1869_);
return v_res_1881_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__3(lean_object* v___y_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_){
_start:
{
lean_object* v___x_1905_; 
v___x_1905_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v___y_1893_, v___y_1894_, v___y_1895_, v___y_1896_, v___y_1897_, v___y_1898_, v___y_1899_, v___y_1900_, v___y_1901_, v___y_1902_, v___y_1903_);
if (lean_obj_tag(v___x_1905_) == 0)
{
lean_object* v_a_1906_; lean_object* v___x_1908_; uint8_t v_isShared_1909_; uint8_t v_isSharedCheck_1949_; 
v_a_1906_ = lean_ctor_get(v___x_1905_, 0);
v_isSharedCheck_1949_ = !lean_is_exclusive(v___x_1905_);
if (v_isSharedCheck_1949_ == 0)
{
v___x_1908_ = v___x_1905_;
v_isShared_1909_ = v_isSharedCheck_1949_;
goto v_resetjp_1907_;
}
else
{
lean_inc(v_a_1906_);
lean_dec(v___x_1905_);
v___x_1908_ = lean_box(0);
v_isShared_1909_ = v_isSharedCheck_1949_;
goto v_resetjp_1907_;
}
v_resetjp_1907_:
{
lean_object* v_toRing_1910_; lean_object* v_mulFn_x3f_1911_; 
v_toRing_1910_ = lean_ctor_get(v_a_1906_, 0);
lean_inc_ref(v_toRing_1910_);
lean_dec(v_a_1906_);
v_mulFn_x3f_1911_ = lean_ctor_get(v_toRing_1910_, 7);
if (lean_obj_tag(v_mulFn_x3f_1911_) == 1)
{
lean_object* v_val_1912_; lean_object* v___x_1914_; 
lean_inc_ref(v_mulFn_x3f_1911_);
lean_dec_ref(v_toRing_1910_);
v_val_1912_ = lean_ctor_get(v_mulFn_x3f_1911_, 0);
lean_inc(v_val_1912_);
lean_dec_ref_known(v_mulFn_x3f_1911_, 1);
if (v_isShared_1909_ == 0)
{
lean_ctor_set(v___x_1908_, 0, v_val_1912_);
v___x_1914_ = v___x_1908_;
goto v_reusejp_1913_;
}
else
{
lean_object* v_reuseFailAlloc_1915_; 
v_reuseFailAlloc_1915_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1915_, 0, v_val_1912_);
v___x_1914_ = v_reuseFailAlloc_1915_;
goto v_reusejp_1913_;
}
v_reusejp_1913_:
{
return v___x_1914_;
}
}
else
{
lean_object* v_type_1916_; lean_object* v_u_1917_; lean_object* v_semiringInst_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v_expectedInst_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; 
lean_del_object(v___x_1908_);
v_type_1916_ = lean_ctor_get(v_toRing_1910_, 1);
lean_inc_ref_n(v_type_1916_, 3);
v_u_1917_ = lean_ctor_get(v_toRing_1910_, 2);
lean_inc_n(v_u_1917_, 2);
v_semiringInst_1918_ = lean_ctor_get(v_toRing_1910_, 4);
lean_inc_ref(v_semiringInst_1918_);
lean_dec_ref(v_toRing_1910_);
v___x_1919_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__3___closed__1));
v___x_1920_ = lean_box(0);
v___x_1921_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1921_, 0, v_u_1917_);
lean_ctor_set(v___x_1921_, 1, v___x_1920_);
lean_inc_ref(v___x_1921_);
v___x_1922_ = l_Lean_mkConst(v___x_1919_, v___x_1921_);
v___x_1923_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__3___closed__3));
v___x_1924_ = l_Lean_mkConst(v___x_1923_, v___x_1921_);
v___x_1925_ = l_Lean_mkAppB(v___x_1924_, v_type_1916_, v_semiringInst_1918_);
v_expectedInst_1926_ = l_Lean_mkAppB(v___x_1922_, v_type_1916_, v___x_1925_);
v___x_1927_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__3___closed__4));
v___x_1928_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__20));
v___x_1929_ = l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__3_spec__5(v_type_1916_, v_u_1917_, v___x_1927_, v___x_1928_, v_expectedInst_1926_, v___y_1893_, v___y_1894_, v___y_1895_, v___y_1896_, v___y_1897_, v___y_1898_, v___y_1899_, v___y_1900_, v___y_1901_, v___y_1902_, v___y_1903_);
if (lean_obj_tag(v___x_1929_) == 0)
{
lean_object* v_a_1930_; lean_object* v___f_1931_; lean_object* v___x_1932_; 
v_a_1930_ = lean_ctor_get(v___x_1929_, 0);
lean_inc_n(v_a_1930_, 2);
lean_dec_ref_known(v___x_1929_, 1);
v___f_1931_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__3___lam__0), 2, 1);
lean_closure_set(v___f_1931_, 0, v_a_1930_);
v___x_1932_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(v___f_1931_, v___y_1893_, v___y_1894_);
if (lean_obj_tag(v___x_1932_) == 0)
{
lean_object* v___x_1934_; uint8_t v_isShared_1935_; uint8_t v_isSharedCheck_1939_; 
v_isSharedCheck_1939_ = !lean_is_exclusive(v___x_1932_);
if (v_isSharedCheck_1939_ == 0)
{
lean_object* v_unused_1940_; 
v_unused_1940_ = lean_ctor_get(v___x_1932_, 0);
lean_dec(v_unused_1940_);
v___x_1934_ = v___x_1932_;
v_isShared_1935_ = v_isSharedCheck_1939_;
goto v_resetjp_1933_;
}
else
{
lean_dec(v___x_1932_);
v___x_1934_ = lean_box(0);
v_isShared_1935_ = v_isSharedCheck_1939_;
goto v_resetjp_1933_;
}
v_resetjp_1933_:
{
lean_object* v___x_1937_; 
if (v_isShared_1935_ == 0)
{
lean_ctor_set(v___x_1934_, 0, v_a_1930_);
v___x_1937_ = v___x_1934_;
goto v_reusejp_1936_;
}
else
{
lean_object* v_reuseFailAlloc_1938_; 
v_reuseFailAlloc_1938_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1938_, 0, v_a_1930_);
v___x_1937_ = v_reuseFailAlloc_1938_;
goto v_reusejp_1936_;
}
v_reusejp_1936_:
{
return v___x_1937_;
}
}
}
else
{
lean_object* v_a_1941_; lean_object* v___x_1943_; uint8_t v_isShared_1944_; uint8_t v_isSharedCheck_1948_; 
lean_dec(v_a_1930_);
v_a_1941_ = lean_ctor_get(v___x_1932_, 0);
v_isSharedCheck_1948_ = !lean_is_exclusive(v___x_1932_);
if (v_isSharedCheck_1948_ == 0)
{
v___x_1943_ = v___x_1932_;
v_isShared_1944_ = v_isSharedCheck_1948_;
goto v_resetjp_1942_;
}
else
{
lean_inc(v_a_1941_);
lean_dec(v___x_1932_);
v___x_1943_ = lean_box(0);
v_isShared_1944_ = v_isSharedCheck_1948_;
goto v_resetjp_1942_;
}
v_resetjp_1942_:
{
lean_object* v___x_1946_; 
if (v_isShared_1944_ == 0)
{
v___x_1946_ = v___x_1943_;
goto v_reusejp_1945_;
}
else
{
lean_object* v_reuseFailAlloc_1947_; 
v_reuseFailAlloc_1947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1947_, 0, v_a_1941_);
v___x_1946_ = v_reuseFailAlloc_1947_;
goto v_reusejp_1945_;
}
v_reusejp_1945_:
{
return v___x_1946_;
}
}
}
}
else
{
return v___x_1929_;
}
}
}
}
else
{
lean_object* v_a_1950_; lean_object* v___x_1952_; uint8_t v_isShared_1953_; uint8_t v_isSharedCheck_1957_; 
v_a_1950_ = lean_ctor_get(v___x_1905_, 0);
v_isSharedCheck_1957_ = !lean_is_exclusive(v___x_1905_);
if (v_isSharedCheck_1957_ == 0)
{
v___x_1952_ = v___x_1905_;
v_isShared_1953_ = v_isSharedCheck_1957_;
goto v_resetjp_1951_;
}
else
{
lean_inc(v_a_1950_);
lean_dec(v___x_1905_);
v___x_1952_ = lean_box(0);
v_isShared_1953_ = v_isSharedCheck_1957_;
goto v_resetjp_1951_;
}
v_resetjp_1951_:
{
lean_object* v___x_1955_; 
if (v_isShared_1953_ == 0)
{
v___x_1955_ = v___x_1952_;
goto v_reusejp_1954_;
}
else
{
lean_object* v_reuseFailAlloc_1956_; 
v_reuseFailAlloc_1956_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1956_, 0, v_a_1950_);
v___x_1955_ = v_reuseFailAlloc_1956_;
goto v_reusejp_1954_;
}
v_reusejp_1954_:
{
return v___x_1955_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__3___boxed(lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_){
_start:
{
lean_object* v_res_1970_; 
v_res_1970_ = l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__3(v___y_1958_, v___y_1959_, v___y_1960_, v___y_1961_, v___y_1962_, v___y_1963_, v___y_1964_, v___y_1965_, v___y_1966_, v___y_1967_, v___y_1968_);
lean_dec(v___y_1968_);
lean_dec_ref(v___y_1967_);
lean_dec(v___y_1966_);
lean_dec_ref(v___y_1965_);
lean_dec(v___y_1964_);
lean_dec_ref(v___y_1963_);
lean_dec(v___y_1962_);
lean_dec_ref(v___y_1961_);
lean_dec(v___y_1960_);
lean_dec(v___y_1959_);
lean_dec_ref(v___y_1958_);
return v_res_1970_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__3(void){
_start:
{
lean_object* v___x_1978_; lean_object* v___x_1979_; 
v___x_1978_ = lean_unsigned_to_nat(1u);
v___x_1979_ = lean_nat_to_int(v___x_1978_);
return v___x_1979_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv(lean_object* v_e_2004_, lean_object* v_inst_2005_, lean_object* v_a_2006_, lean_object* v_a_2007_, lean_object* v_a_2008_, lean_object* v_a_2009_, lean_object* v_a_2010_, lean_object* v_a_2011_, lean_object* v_a_2012_, lean_object* v_a_2013_, lean_object* v_a_2014_, lean_object* v_a_2015_, lean_object* v_a_2016_, lean_object* v_a_2017_){
_start:
{
lean_object* v___x_2022_; 
v___x_2022_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst(v_inst_2005_, v_a_2007_, v_a_2008_, v_a_2009_, v_a_2010_, v_a_2011_, v_a_2012_, v_a_2013_, v_a_2014_, v_a_2015_, v_a_2016_, v_a_2017_);
if (lean_obj_tag(v___x_2022_) == 0)
{
lean_object* v_a_2023_; lean_object* v___x_2025_; uint8_t v_isShared_2026_; uint8_t v_isSharedCheck_2282_; 
v_a_2023_ = lean_ctor_get(v___x_2022_, 0);
v_isSharedCheck_2282_ = !lean_is_exclusive(v___x_2022_);
if (v_isSharedCheck_2282_ == 0)
{
v___x_2025_ = v___x_2022_;
v_isShared_2026_ = v_isSharedCheck_2282_;
goto v_resetjp_2024_;
}
else
{
lean_inc(v_a_2023_);
lean_dec(v___x_2022_);
v___x_2025_ = lean_box(0);
v_isShared_2026_ = v_isSharedCheck_2282_;
goto v_resetjp_2024_;
}
v_resetjp_2024_:
{
uint8_t v___x_2027_; 
v___x_2027_ = lean_unbox(v_a_2023_);
lean_dec(v_a_2023_);
if (v___x_2027_ == 0)
{
lean_object* v___x_2028_; lean_object* v___x_2030_; 
lean_dec_ref(v_a_2006_);
lean_dec_ref(v_e_2004_);
v___x_2028_ = lean_box(0);
if (v_isShared_2026_ == 0)
{
lean_ctor_set(v___x_2025_, 0, v___x_2028_);
v___x_2030_ = v___x_2025_;
goto v_reusejp_2029_;
}
else
{
lean_object* v_reuseFailAlloc_2031_; 
v_reuseFailAlloc_2031_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2031_, 0, v___x_2028_);
v___x_2030_ = v_reuseFailAlloc_2031_;
goto v_reusejp_2029_;
}
v_reusejp_2029_:
{
return v___x_2030_;
}
}
else
{
lean_object* v___x_2032_; 
lean_del_object(v___x_2025_);
v___x_2032_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v_a_2007_, v_a_2008_, v_a_2009_, v_a_2010_, v_a_2011_, v_a_2012_, v_a_2013_, v_a_2014_, v_a_2015_, v_a_2016_, v_a_2017_);
if (lean_obj_tag(v___x_2032_) == 0)
{
lean_object* v_a_2033_; lean_object* v___x_2035_; uint8_t v_isShared_2036_; uint8_t v_isSharedCheck_2273_; 
v_a_2033_ = lean_ctor_get(v___x_2032_, 0);
v_isSharedCheck_2273_ = !lean_is_exclusive(v___x_2032_);
if (v_isSharedCheck_2273_ == 0)
{
v___x_2035_ = v___x_2032_;
v_isShared_2036_ = v_isSharedCheck_2273_;
goto v_resetjp_2034_;
}
else
{
lean_inc(v_a_2033_);
lean_dec(v___x_2032_);
v___x_2035_ = lean_box(0);
v_isShared_2036_ = v_isSharedCheck_2273_;
goto v_resetjp_2034_;
}
v_resetjp_2034_:
{
lean_object* v_fieldInst_x3f_2037_; 
v_fieldInst_x3f_2037_ = lean_ctor_get(v_a_2033_, 6);
lean_inc(v_fieldInst_x3f_2037_);
if (lean_obj_tag(v_fieldInst_x3f_2037_) == 1)
{
lean_object* v_toRing_2038_; lean_object* v_val_2039_; lean_object* v___y_2041_; lean_object* v___y_2042_; lean_object* v___y_2043_; lean_object* v___y_2044_; lean_object* v___y_2045_; lean_object* v___y_2046_; lean_object* v___y_2047_; lean_object* v___y_2048_; lean_object* v___y_2049_; lean_object* v___y_2050_; lean_object* v___x_2060_; 
lean_del_object(v___x_2035_);
v_toRing_2038_ = lean_ctor_get(v_a_2033_, 0);
lean_inc_ref(v_toRing_2038_);
lean_dec(v_a_2033_);
v_val_2039_ = lean_ctor_get(v_fieldInst_x3f_2037_, 0);
lean_inc(v_val_2039_);
lean_dec_ref_known(v_fieldInst_x3f_2037_, 1);
v___x_2060_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v_a_2007_, v_a_2008_, v_a_2009_, v_a_2010_, v_a_2011_, v_a_2012_, v_a_2013_, v_a_2014_, v_a_2015_, v_a_2016_, v_a_2017_);
if (lean_obj_tag(v___x_2060_) == 0)
{
lean_object* v_a_2061_; lean_object* v___x_2063_; uint8_t v_isShared_2064_; uint8_t v_isSharedCheck_2260_; 
v_a_2061_ = lean_ctor_get(v___x_2060_, 0);
v_isSharedCheck_2260_ = !lean_is_exclusive(v___x_2060_);
if (v_isSharedCheck_2260_ == 0)
{
v___x_2063_ = v___x_2060_;
v_isShared_2064_ = v_isSharedCheck_2260_;
goto v_resetjp_2062_;
}
else
{
lean_inc(v_a_2061_);
lean_dec(v___x_2060_);
v___x_2063_ = lean_box(0);
v_isShared_2064_ = v_isSharedCheck_2260_;
goto v_resetjp_2062_;
}
v_resetjp_2062_:
{
lean_object* v_invSet_2065_; uint8_t v___x_2066_; 
v_invSet_2065_ = lean_ctor_get(v_a_2061_, 14);
lean_inc_ref(v_invSet_2065_);
lean_dec(v_a_2061_);
v___x_2066_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1___redArg(v_invSet_2065_, v_a_2006_);
lean_dec_ref(v_invSet_2065_);
if (v___x_2066_ == 0)
{
lean_object* v___f_2067_; lean_object* v___x_2068_; 
lean_del_object(v___x_2063_);
lean_inc_ref(v_a_2006_);
v___f_2067_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___lam__0), 2, 1);
lean_closure_set(v___f_2067_, 0, v_a_2006_);
v___x_2068_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(v___f_2067_, v_a_2007_, v_a_2008_);
if (lean_obj_tag(v___x_2068_) == 0)
{
lean_object* v___x_2069_; 
lean_dec_ref_known(v___x_2068_, 1);
lean_inc_ref(v_a_2006_);
v___x_2069_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f(v_a_2006_, v_a_2007_, v_a_2008_, v_a_2009_, v_a_2010_, v_a_2011_, v_a_2012_, v_a_2013_, v_a_2014_, v_a_2015_, v_a_2016_, v_a_2017_);
if (lean_obj_tag(v___x_2069_) == 0)
{
lean_object* v_a_2070_; 
v_a_2070_ = lean_ctor_get(v___x_2069_, 0);
lean_inc(v_a_2070_);
lean_dec_ref_known(v___x_2069_, 1);
if (lean_obj_tag(v_a_2070_) == 1)
{
lean_object* v_val_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; uint8_t v___x_2074_; 
v_val_2071_ = lean_ctor_get(v_a_2070_, 0);
lean_inc(v_val_2071_);
lean_dec_ref_known(v_a_2070_, 1);
v___x_2072_ = lean_unsigned_to_nat(0u);
v___x_2073_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__4___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__4___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__4___closed__1);
v___x_2074_ = lean_int_dec_eq(v_val_2071_, v___x_2073_);
if (v___x_2074_ == 0)
{
lean_object* v___x_2075_; 
v___x_2075_ = l_Lean_Meta_Grind_Arith_CommRing_hasChar(v_a_2007_, v_a_2008_, v_a_2009_, v_a_2010_, v_a_2011_, v_a_2012_, v_a_2013_, v_a_2014_, v_a_2015_, v_a_2016_, v_a_2017_);
if (lean_obj_tag(v___x_2075_) == 0)
{
lean_object* v_a_2076_; uint8_t v___x_2077_; 
v_a_2076_ = lean_ctor_get(v___x_2075_, 0);
lean_inc(v_a_2076_);
lean_dec_ref_known(v___x_2075_, 1);
v___x_2077_ = lean_unbox(v_a_2076_);
lean_dec(v_a_2076_);
if (v___x_2077_ == 0)
{
lean_dec(v_val_2071_);
lean_dec_ref(v_e_2004_);
v___y_2041_ = v_a_2008_;
v___y_2042_ = v_a_2009_;
v___y_2043_ = v_a_2010_;
v___y_2044_ = v_a_2011_;
v___y_2045_ = v_a_2012_;
v___y_2046_ = v_a_2013_;
v___y_2047_ = v_a_2014_;
v___y_2048_ = v_a_2015_;
v___y_2049_ = v_a_2016_;
v___y_2050_ = v_a_2017_;
goto v___jp_2040_;
}
else
{
lean_object* v___x_2078_; 
v___x_2078_ = l_Lean_Meta_Grind_Arith_CommRing_getCharInst(v_a_2007_, v_a_2008_, v_a_2009_, v_a_2010_, v_a_2011_, v_a_2012_, v_a_2013_, v_a_2014_, v_a_2015_, v_a_2016_, v_a_2017_);
if (lean_obj_tag(v___x_2078_) == 0)
{
lean_object* v_a_2079_; lean_object* v_fst_2080_; lean_object* v_snd_2081_; lean_object* v___x_2083_; uint8_t v_isShared_2084_; uint8_t v_isSharedCheck_2214_; 
v_a_2079_ = lean_ctor_get(v___x_2078_, 0);
lean_inc(v_a_2079_);
lean_dec_ref_known(v___x_2078_, 1);
v_fst_2080_ = lean_ctor_get(v_a_2079_, 0);
v_snd_2081_ = lean_ctor_get(v_a_2079_, 1);
v_isSharedCheck_2214_ = !lean_is_exclusive(v_a_2079_);
if (v_isSharedCheck_2214_ == 0)
{
v___x_2083_ = v_a_2079_;
v_isShared_2084_ = v_isSharedCheck_2214_;
goto v_resetjp_2082_;
}
else
{
lean_inc(v_snd_2081_);
lean_inc(v_fst_2080_);
lean_dec(v_a_2079_);
v___x_2083_ = lean_box(0);
v_isShared_2084_ = v_isSharedCheck_2214_;
goto v_resetjp_2082_;
}
v_resetjp_2082_:
{
uint8_t v___x_2085_; 
v___x_2085_ = lean_nat_dec_eq(v_snd_2081_, v___x_2072_);
if (v___x_2085_ == 0)
{
lean_object* v___x_2086_; lean_object* v___x_2087_; uint8_t v___x_2088_; 
lean_inc(v_snd_2081_);
v___x_2086_ = lean_nat_to_int(v_snd_2081_);
v___x_2087_ = lean_int_emod(v_val_2071_, v___x_2086_);
lean_dec(v___x_2086_);
v___x_2088_ = lean_int_dec_eq(v___x_2087_, v___x_2073_);
lean_dec(v___x_2087_);
if (v___x_2088_ == 0)
{
lean_object* v___x_2089_; 
v___x_2089_ = l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__3(v_a_2007_, v_a_2008_, v_a_2009_, v_a_2010_, v_a_2011_, v_a_2012_, v_a_2013_, v_a_2014_, v_a_2015_, v_a_2016_, v_a_2017_);
if (lean_obj_tag(v___x_2089_) == 0)
{
lean_object* v_a_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; 
v_a_2090_ = lean_ctor_get(v___x_2089_, 0);
lean_inc(v_a_2090_);
lean_dec_ref_known(v___x_2089_, 1);
v___x_2091_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__3, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__3);
v___x_2092_ = l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__4(v___x_2091_, v_a_2007_, v_a_2008_, v_a_2009_, v_a_2010_, v_a_2011_, v_a_2012_, v_a_2013_, v_a_2014_, v_a_2015_, v_a_2016_, v_a_2017_);
if (lean_obj_tag(v___x_2092_) == 0)
{
lean_object* v_a_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; 
v_a_2093_ = lean_ctor_get(v___x_2092_, 0);
lean_inc(v_a_2093_);
lean_dec_ref_known(v___x_2092_, 1);
v___x_2094_ = l_Lean_mkAppB(v_a_2090_, v_a_2006_, v_e_2004_);
v___x_2095_ = l_Lean_Meta_mkEq(v___x_2094_, v_a_2093_, v_a_2014_, v_a_2015_, v_a_2016_, v_a_2017_);
if (lean_obj_tag(v___x_2095_) == 0)
{
lean_object* v_a_2096_; lean_object* v_type_2097_; lean_object* v_u_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; lean_object* v___x_2102_; 
v_a_2096_ = lean_ctor_get(v___x_2095_, 0);
lean_inc(v_a_2096_);
lean_dec_ref_known(v___x_2095_, 1);
v_type_2097_ = lean_ctor_get(v_toRing_2038_, 1);
lean_inc_ref(v_type_2097_);
v_u_2098_ = lean_ctor_get(v_toRing_2038_, 2);
lean_inc(v_u_2098_);
lean_dec_ref(v_toRing_2038_);
v___x_2099_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__5));
v___x_2100_ = lean_box(0);
if (v_isShared_2084_ == 0)
{
lean_ctor_set_tag(v___x_2083_, 1);
lean_ctor_set(v___x_2083_, 1, v___x_2100_);
lean_ctor_set(v___x_2083_, 0, v_u_2098_);
v___x_2102_ = v___x_2083_;
goto v_reusejp_2101_;
}
else
{
lean_object* v_reuseFailAlloc_2110_; 
v_reuseFailAlloc_2110_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2110_, 0, v_u_2098_);
lean_ctor_set(v_reuseFailAlloc_2110_, 1, v___x_2100_);
v___x_2102_ = v_reuseFailAlloc_2110_;
goto v_reusejp_2101_;
}
v_reusejp_2101_:
{
lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; 
v___x_2103_ = l_Lean_mkConst(v___x_2099_, v___x_2102_);
v___x_2104_ = l_Lean_mkNatLit(v_snd_2081_);
v___x_2105_ = l_Lean_mkIntLit(v_val_2071_);
lean_dec(v_val_2071_);
v___x_2106_ = l_Lean_eagerReflBoolTrue;
v___x_2107_ = l_Lean_mkApp6(v___x_2103_, v_type_2097_, v___x_2104_, v_val_2039_, v_fst_2080_, v___x_2105_, v___x_2106_);
v___x_2108_ = l_Lean_Meta_mkExpectedPropHint(v___x_2107_, v_a_2096_);
v___x_2109_ = l_Lean_Meta_Grind_pushNewFact(v___x_2108_, v___x_2072_, v_a_2008_, v_a_2009_, v_a_2010_, v_a_2011_, v_a_2012_, v_a_2013_, v_a_2014_, v_a_2015_, v_a_2016_, v_a_2017_);
if (lean_obj_tag(v___x_2109_) == 0)
{
lean_dec_ref_known(v___x_2109_, 1);
goto v___jp_2019_;
}
else
{
return v___x_2109_;
}
}
}
else
{
lean_object* v_a_2111_; lean_object* v___x_2113_; uint8_t v_isShared_2114_; uint8_t v_isSharedCheck_2118_; 
lean_del_object(v___x_2083_);
lean_dec(v_snd_2081_);
lean_dec(v_fst_2080_);
lean_dec(v_val_2071_);
lean_dec(v_val_2039_);
lean_dec_ref(v_toRing_2038_);
v_a_2111_ = lean_ctor_get(v___x_2095_, 0);
v_isSharedCheck_2118_ = !lean_is_exclusive(v___x_2095_);
if (v_isSharedCheck_2118_ == 0)
{
v___x_2113_ = v___x_2095_;
v_isShared_2114_ = v_isSharedCheck_2118_;
goto v_resetjp_2112_;
}
else
{
lean_inc(v_a_2111_);
lean_dec(v___x_2095_);
v___x_2113_ = lean_box(0);
v_isShared_2114_ = v_isSharedCheck_2118_;
goto v_resetjp_2112_;
}
v_resetjp_2112_:
{
lean_object* v___x_2116_; 
if (v_isShared_2114_ == 0)
{
v___x_2116_ = v___x_2113_;
goto v_reusejp_2115_;
}
else
{
lean_object* v_reuseFailAlloc_2117_; 
v_reuseFailAlloc_2117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2117_, 0, v_a_2111_);
v___x_2116_ = v_reuseFailAlloc_2117_;
goto v_reusejp_2115_;
}
v_reusejp_2115_:
{
return v___x_2116_;
}
}
}
}
else
{
lean_object* v_a_2119_; lean_object* v___x_2121_; uint8_t v_isShared_2122_; uint8_t v_isSharedCheck_2126_; 
lean_dec(v_a_2090_);
lean_del_object(v___x_2083_);
lean_dec(v_snd_2081_);
lean_dec(v_fst_2080_);
lean_dec(v_val_2071_);
lean_dec(v_val_2039_);
lean_dec_ref(v_toRing_2038_);
lean_dec_ref(v_a_2006_);
lean_dec_ref(v_e_2004_);
v_a_2119_ = lean_ctor_get(v___x_2092_, 0);
v_isSharedCheck_2126_ = !lean_is_exclusive(v___x_2092_);
if (v_isSharedCheck_2126_ == 0)
{
v___x_2121_ = v___x_2092_;
v_isShared_2122_ = v_isSharedCheck_2126_;
goto v_resetjp_2120_;
}
else
{
lean_inc(v_a_2119_);
lean_dec(v___x_2092_);
v___x_2121_ = lean_box(0);
v_isShared_2122_ = v_isSharedCheck_2126_;
goto v_resetjp_2120_;
}
v_resetjp_2120_:
{
lean_object* v___x_2124_; 
if (v_isShared_2122_ == 0)
{
v___x_2124_ = v___x_2121_;
goto v_reusejp_2123_;
}
else
{
lean_object* v_reuseFailAlloc_2125_; 
v_reuseFailAlloc_2125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2125_, 0, v_a_2119_);
v___x_2124_ = v_reuseFailAlloc_2125_;
goto v_reusejp_2123_;
}
v_reusejp_2123_:
{
return v___x_2124_;
}
}
}
}
else
{
lean_object* v_a_2127_; lean_object* v___x_2129_; uint8_t v_isShared_2130_; uint8_t v_isSharedCheck_2134_; 
lean_del_object(v___x_2083_);
lean_dec(v_snd_2081_);
lean_dec(v_fst_2080_);
lean_dec(v_val_2071_);
lean_dec(v_val_2039_);
lean_dec_ref(v_toRing_2038_);
lean_dec_ref(v_a_2006_);
lean_dec_ref(v_e_2004_);
v_a_2127_ = lean_ctor_get(v___x_2089_, 0);
v_isSharedCheck_2134_ = !lean_is_exclusive(v___x_2089_);
if (v_isSharedCheck_2134_ == 0)
{
v___x_2129_ = v___x_2089_;
v_isShared_2130_ = v_isSharedCheck_2134_;
goto v_resetjp_2128_;
}
else
{
lean_inc(v_a_2127_);
lean_dec(v___x_2089_);
v___x_2129_ = lean_box(0);
v_isShared_2130_ = v_isSharedCheck_2134_;
goto v_resetjp_2128_;
}
v_resetjp_2128_:
{
lean_object* v___x_2132_; 
if (v_isShared_2130_ == 0)
{
v___x_2132_ = v___x_2129_;
goto v_reusejp_2131_;
}
else
{
lean_object* v_reuseFailAlloc_2133_; 
v_reuseFailAlloc_2133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2133_, 0, v_a_2127_);
v___x_2132_ = v_reuseFailAlloc_2133_;
goto v_reusejp_2131_;
}
v_reusejp_2131_:
{
return v___x_2132_;
}
}
}
}
else
{
lean_object* v___x_2135_; 
lean_dec_ref(v_a_2006_);
v___x_2135_ = l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__4(v___x_2073_, v_a_2007_, v_a_2008_, v_a_2009_, v_a_2010_, v_a_2011_, v_a_2012_, v_a_2013_, v_a_2014_, v_a_2015_, v_a_2016_, v_a_2017_);
if (lean_obj_tag(v___x_2135_) == 0)
{
lean_object* v_a_2136_; lean_object* v___x_2137_; 
v_a_2136_ = lean_ctor_get(v___x_2135_, 0);
lean_inc(v_a_2136_);
lean_dec_ref_known(v___x_2135_, 1);
v___x_2137_ = l_Lean_Meta_mkEq(v_e_2004_, v_a_2136_, v_a_2014_, v_a_2015_, v_a_2016_, v_a_2017_);
if (lean_obj_tag(v___x_2137_) == 0)
{
lean_object* v_a_2138_; lean_object* v_type_2139_; lean_object* v_u_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2144_; 
v_a_2138_ = lean_ctor_get(v___x_2137_, 0);
lean_inc(v_a_2138_);
lean_dec_ref_known(v___x_2137_, 1);
v_type_2139_ = lean_ctor_get(v_toRing_2038_, 1);
lean_inc_ref(v_type_2139_);
v_u_2140_ = lean_ctor_get(v_toRing_2038_, 2);
lean_inc(v_u_2140_);
lean_dec_ref(v_toRing_2038_);
v___x_2141_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__7));
v___x_2142_ = lean_box(0);
if (v_isShared_2084_ == 0)
{
lean_ctor_set_tag(v___x_2083_, 1);
lean_ctor_set(v___x_2083_, 1, v___x_2142_);
lean_ctor_set(v___x_2083_, 0, v_u_2140_);
v___x_2144_ = v___x_2083_;
goto v_reusejp_2143_;
}
else
{
lean_object* v_reuseFailAlloc_2152_; 
v_reuseFailAlloc_2152_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2152_, 0, v_u_2140_);
lean_ctor_set(v_reuseFailAlloc_2152_, 1, v___x_2142_);
v___x_2144_ = v_reuseFailAlloc_2152_;
goto v_reusejp_2143_;
}
v_reusejp_2143_:
{
lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; 
v___x_2145_ = l_Lean_mkConst(v___x_2141_, v___x_2144_);
v___x_2146_ = l_Lean_mkNatLit(v_snd_2081_);
v___x_2147_ = l_Lean_mkIntLit(v_val_2071_);
lean_dec(v_val_2071_);
v___x_2148_ = l_Lean_eagerReflBoolTrue;
v___x_2149_ = l_Lean_mkApp6(v___x_2145_, v_type_2139_, v___x_2146_, v_val_2039_, v_fst_2080_, v___x_2147_, v___x_2148_);
v___x_2150_ = l_Lean_Meta_mkExpectedPropHint(v___x_2149_, v_a_2138_);
v___x_2151_ = l_Lean_Meta_Grind_pushNewFact(v___x_2150_, v___x_2072_, v_a_2008_, v_a_2009_, v_a_2010_, v_a_2011_, v_a_2012_, v_a_2013_, v_a_2014_, v_a_2015_, v_a_2016_, v_a_2017_);
if (lean_obj_tag(v___x_2151_) == 0)
{
lean_dec_ref_known(v___x_2151_, 1);
goto v___jp_2019_;
}
else
{
return v___x_2151_;
}
}
}
else
{
lean_object* v_a_2153_; lean_object* v___x_2155_; uint8_t v_isShared_2156_; uint8_t v_isSharedCheck_2160_; 
lean_del_object(v___x_2083_);
lean_dec(v_snd_2081_);
lean_dec(v_fst_2080_);
lean_dec(v_val_2071_);
lean_dec(v_val_2039_);
lean_dec_ref(v_toRing_2038_);
v_a_2153_ = lean_ctor_get(v___x_2137_, 0);
v_isSharedCheck_2160_ = !lean_is_exclusive(v___x_2137_);
if (v_isSharedCheck_2160_ == 0)
{
v___x_2155_ = v___x_2137_;
v_isShared_2156_ = v_isSharedCheck_2160_;
goto v_resetjp_2154_;
}
else
{
lean_inc(v_a_2153_);
lean_dec(v___x_2137_);
v___x_2155_ = lean_box(0);
v_isShared_2156_ = v_isSharedCheck_2160_;
goto v_resetjp_2154_;
}
v_resetjp_2154_:
{
lean_object* v___x_2158_; 
if (v_isShared_2156_ == 0)
{
v___x_2158_ = v___x_2155_;
goto v_reusejp_2157_;
}
else
{
lean_object* v_reuseFailAlloc_2159_; 
v_reuseFailAlloc_2159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2159_, 0, v_a_2153_);
v___x_2158_ = v_reuseFailAlloc_2159_;
goto v_reusejp_2157_;
}
v_reusejp_2157_:
{
return v___x_2158_;
}
}
}
}
else
{
lean_object* v_a_2161_; lean_object* v___x_2163_; uint8_t v_isShared_2164_; uint8_t v_isSharedCheck_2168_; 
lean_del_object(v___x_2083_);
lean_dec(v_snd_2081_);
lean_dec(v_fst_2080_);
lean_dec(v_val_2071_);
lean_dec(v_val_2039_);
lean_dec_ref(v_toRing_2038_);
lean_dec_ref(v_e_2004_);
v_a_2161_ = lean_ctor_get(v___x_2135_, 0);
v_isSharedCheck_2168_ = !lean_is_exclusive(v___x_2135_);
if (v_isSharedCheck_2168_ == 0)
{
v___x_2163_ = v___x_2135_;
v_isShared_2164_ = v_isSharedCheck_2168_;
goto v_resetjp_2162_;
}
else
{
lean_inc(v_a_2161_);
lean_dec(v___x_2135_);
v___x_2163_ = lean_box(0);
v_isShared_2164_ = v_isSharedCheck_2168_;
goto v_resetjp_2162_;
}
v_resetjp_2162_:
{
lean_object* v___x_2166_; 
if (v_isShared_2164_ == 0)
{
v___x_2166_ = v___x_2163_;
goto v_reusejp_2165_;
}
else
{
lean_object* v_reuseFailAlloc_2167_; 
v_reuseFailAlloc_2167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2167_, 0, v_a_2161_);
v___x_2166_ = v_reuseFailAlloc_2167_;
goto v_reusejp_2165_;
}
v_reusejp_2165_:
{
return v___x_2166_;
}
}
}
}
}
else
{
lean_object* v___x_2169_; 
lean_dec(v_snd_2081_);
v___x_2169_ = l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__3(v_a_2007_, v_a_2008_, v_a_2009_, v_a_2010_, v_a_2011_, v_a_2012_, v_a_2013_, v_a_2014_, v_a_2015_, v_a_2016_, v_a_2017_);
if (lean_obj_tag(v___x_2169_) == 0)
{
lean_object* v_a_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; 
v_a_2170_ = lean_ctor_get(v___x_2169_, 0);
lean_inc(v_a_2170_);
lean_dec_ref_known(v___x_2169_, 1);
v___x_2171_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__3, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__3);
v___x_2172_ = l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__4(v___x_2171_, v_a_2007_, v_a_2008_, v_a_2009_, v_a_2010_, v_a_2011_, v_a_2012_, v_a_2013_, v_a_2014_, v_a_2015_, v_a_2016_, v_a_2017_);
if (lean_obj_tag(v___x_2172_) == 0)
{
lean_object* v_a_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; 
v_a_2173_ = lean_ctor_get(v___x_2172_, 0);
lean_inc(v_a_2173_);
lean_dec_ref_known(v___x_2172_, 1);
v___x_2174_ = l_Lean_mkAppB(v_a_2170_, v_a_2006_, v_e_2004_);
v___x_2175_ = l_Lean_Meta_mkEq(v___x_2174_, v_a_2173_, v_a_2014_, v_a_2015_, v_a_2016_, v_a_2017_);
if (lean_obj_tag(v___x_2175_) == 0)
{
lean_object* v_a_2176_; lean_object* v_type_2177_; lean_object* v_u_2178_; lean_object* v___x_2179_; lean_object* v___x_2180_; lean_object* v___x_2182_; 
v_a_2176_ = lean_ctor_get(v___x_2175_, 0);
lean_inc(v_a_2176_);
lean_dec_ref_known(v___x_2175_, 1);
v_type_2177_ = lean_ctor_get(v_toRing_2038_, 1);
lean_inc_ref(v_type_2177_);
v_u_2178_ = lean_ctor_get(v_toRing_2038_, 2);
lean_inc(v_u_2178_);
lean_dec_ref(v_toRing_2038_);
v___x_2179_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__9));
v___x_2180_ = lean_box(0);
if (v_isShared_2084_ == 0)
{
lean_ctor_set_tag(v___x_2083_, 1);
lean_ctor_set(v___x_2083_, 1, v___x_2180_);
lean_ctor_set(v___x_2083_, 0, v_u_2178_);
v___x_2182_ = v___x_2083_;
goto v_reusejp_2181_;
}
else
{
lean_object* v_reuseFailAlloc_2189_; 
v_reuseFailAlloc_2189_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2189_, 0, v_u_2178_);
lean_ctor_set(v_reuseFailAlloc_2189_, 1, v___x_2180_);
v___x_2182_ = v_reuseFailAlloc_2189_;
goto v_reusejp_2181_;
}
v_reusejp_2181_:
{
lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; 
v___x_2183_ = l_Lean_mkConst(v___x_2179_, v___x_2182_);
v___x_2184_ = l_Lean_mkIntLit(v_val_2071_);
lean_dec(v_val_2071_);
v___x_2185_ = l_Lean_eagerReflBoolTrue;
v___x_2186_ = l_Lean_mkApp5(v___x_2183_, v_type_2177_, v_val_2039_, v_fst_2080_, v___x_2184_, v___x_2185_);
v___x_2187_ = l_Lean_Meta_mkExpectedPropHint(v___x_2186_, v_a_2176_);
v___x_2188_ = l_Lean_Meta_Grind_pushNewFact(v___x_2187_, v___x_2072_, v_a_2008_, v_a_2009_, v_a_2010_, v_a_2011_, v_a_2012_, v_a_2013_, v_a_2014_, v_a_2015_, v_a_2016_, v_a_2017_);
if (lean_obj_tag(v___x_2188_) == 0)
{
lean_dec_ref_known(v___x_2188_, 1);
goto v___jp_2019_;
}
else
{
return v___x_2188_;
}
}
}
else
{
lean_object* v_a_2190_; lean_object* v___x_2192_; uint8_t v_isShared_2193_; uint8_t v_isSharedCheck_2197_; 
lean_del_object(v___x_2083_);
lean_dec(v_fst_2080_);
lean_dec(v_val_2071_);
lean_dec(v_val_2039_);
lean_dec_ref(v_toRing_2038_);
v_a_2190_ = lean_ctor_get(v___x_2175_, 0);
v_isSharedCheck_2197_ = !lean_is_exclusive(v___x_2175_);
if (v_isSharedCheck_2197_ == 0)
{
v___x_2192_ = v___x_2175_;
v_isShared_2193_ = v_isSharedCheck_2197_;
goto v_resetjp_2191_;
}
else
{
lean_inc(v_a_2190_);
lean_dec(v___x_2175_);
v___x_2192_ = lean_box(0);
v_isShared_2193_ = v_isSharedCheck_2197_;
goto v_resetjp_2191_;
}
v_resetjp_2191_:
{
lean_object* v___x_2195_; 
if (v_isShared_2193_ == 0)
{
v___x_2195_ = v___x_2192_;
goto v_reusejp_2194_;
}
else
{
lean_object* v_reuseFailAlloc_2196_; 
v_reuseFailAlloc_2196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2196_, 0, v_a_2190_);
v___x_2195_ = v_reuseFailAlloc_2196_;
goto v_reusejp_2194_;
}
v_reusejp_2194_:
{
return v___x_2195_;
}
}
}
}
else
{
lean_object* v_a_2198_; lean_object* v___x_2200_; uint8_t v_isShared_2201_; uint8_t v_isSharedCheck_2205_; 
lean_dec(v_a_2170_);
lean_del_object(v___x_2083_);
lean_dec(v_fst_2080_);
lean_dec(v_val_2071_);
lean_dec(v_val_2039_);
lean_dec_ref(v_toRing_2038_);
lean_dec_ref(v_a_2006_);
lean_dec_ref(v_e_2004_);
v_a_2198_ = lean_ctor_get(v___x_2172_, 0);
v_isSharedCheck_2205_ = !lean_is_exclusive(v___x_2172_);
if (v_isSharedCheck_2205_ == 0)
{
v___x_2200_ = v___x_2172_;
v_isShared_2201_ = v_isSharedCheck_2205_;
goto v_resetjp_2199_;
}
else
{
lean_inc(v_a_2198_);
lean_dec(v___x_2172_);
v___x_2200_ = lean_box(0);
v_isShared_2201_ = v_isSharedCheck_2205_;
goto v_resetjp_2199_;
}
v_resetjp_2199_:
{
lean_object* v___x_2203_; 
if (v_isShared_2201_ == 0)
{
v___x_2203_ = v___x_2200_;
goto v_reusejp_2202_;
}
else
{
lean_object* v_reuseFailAlloc_2204_; 
v_reuseFailAlloc_2204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2204_, 0, v_a_2198_);
v___x_2203_ = v_reuseFailAlloc_2204_;
goto v_reusejp_2202_;
}
v_reusejp_2202_:
{
return v___x_2203_;
}
}
}
}
else
{
lean_object* v_a_2206_; lean_object* v___x_2208_; uint8_t v_isShared_2209_; uint8_t v_isSharedCheck_2213_; 
lean_del_object(v___x_2083_);
lean_dec(v_fst_2080_);
lean_dec(v_val_2071_);
lean_dec(v_val_2039_);
lean_dec_ref(v_toRing_2038_);
lean_dec_ref(v_a_2006_);
lean_dec_ref(v_e_2004_);
v_a_2206_ = lean_ctor_get(v___x_2169_, 0);
v_isSharedCheck_2213_ = !lean_is_exclusive(v___x_2169_);
if (v_isSharedCheck_2213_ == 0)
{
v___x_2208_ = v___x_2169_;
v_isShared_2209_ = v_isSharedCheck_2213_;
goto v_resetjp_2207_;
}
else
{
lean_inc(v_a_2206_);
lean_dec(v___x_2169_);
v___x_2208_ = lean_box(0);
v_isShared_2209_ = v_isSharedCheck_2213_;
goto v_resetjp_2207_;
}
v_resetjp_2207_:
{
lean_object* v___x_2211_; 
if (v_isShared_2209_ == 0)
{
v___x_2211_ = v___x_2208_;
goto v_reusejp_2210_;
}
else
{
lean_object* v_reuseFailAlloc_2212_; 
v_reuseFailAlloc_2212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2212_, 0, v_a_2206_);
v___x_2211_ = v_reuseFailAlloc_2212_;
goto v_reusejp_2210_;
}
v_reusejp_2210_:
{
return v___x_2211_;
}
}
}
}
}
}
else
{
lean_object* v_a_2215_; lean_object* v___x_2217_; uint8_t v_isShared_2218_; uint8_t v_isSharedCheck_2222_; 
lean_dec(v_val_2071_);
lean_dec(v_val_2039_);
lean_dec_ref(v_toRing_2038_);
lean_dec_ref(v_a_2006_);
lean_dec_ref(v_e_2004_);
v_a_2215_ = lean_ctor_get(v___x_2078_, 0);
v_isSharedCheck_2222_ = !lean_is_exclusive(v___x_2078_);
if (v_isSharedCheck_2222_ == 0)
{
v___x_2217_ = v___x_2078_;
v_isShared_2218_ = v_isSharedCheck_2222_;
goto v_resetjp_2216_;
}
else
{
lean_inc(v_a_2215_);
lean_dec(v___x_2078_);
v___x_2217_ = lean_box(0);
v_isShared_2218_ = v_isSharedCheck_2222_;
goto v_resetjp_2216_;
}
v_resetjp_2216_:
{
lean_object* v___x_2220_; 
if (v_isShared_2218_ == 0)
{
v___x_2220_ = v___x_2217_;
goto v_reusejp_2219_;
}
else
{
lean_object* v_reuseFailAlloc_2221_; 
v_reuseFailAlloc_2221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2221_, 0, v_a_2215_);
v___x_2220_ = v_reuseFailAlloc_2221_;
goto v_reusejp_2219_;
}
v_reusejp_2219_:
{
return v___x_2220_;
}
}
}
}
}
else
{
lean_object* v_a_2223_; lean_object* v___x_2225_; uint8_t v_isShared_2226_; uint8_t v_isSharedCheck_2230_; 
lean_dec(v_val_2071_);
lean_dec(v_val_2039_);
lean_dec_ref(v_toRing_2038_);
lean_dec_ref(v_a_2006_);
lean_dec_ref(v_e_2004_);
v_a_2223_ = lean_ctor_get(v___x_2075_, 0);
v_isSharedCheck_2230_ = !lean_is_exclusive(v___x_2075_);
if (v_isSharedCheck_2230_ == 0)
{
v___x_2225_ = v___x_2075_;
v_isShared_2226_ = v_isSharedCheck_2230_;
goto v_resetjp_2224_;
}
else
{
lean_inc(v_a_2223_);
lean_dec(v___x_2075_);
v___x_2225_ = lean_box(0);
v_isShared_2226_ = v_isSharedCheck_2230_;
goto v_resetjp_2224_;
}
v_resetjp_2224_:
{
lean_object* v___x_2228_; 
if (v_isShared_2226_ == 0)
{
v___x_2228_ = v___x_2225_;
goto v_reusejp_2227_;
}
else
{
lean_object* v_reuseFailAlloc_2229_; 
v_reuseFailAlloc_2229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2229_, 0, v_a_2223_);
v___x_2228_ = v_reuseFailAlloc_2229_;
goto v_reusejp_2227_;
}
v_reusejp_2227_:
{
return v___x_2228_;
}
}
}
}
else
{
lean_object* v_type_2231_; lean_object* v_u_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; 
lean_dec(v_val_2071_);
v_type_2231_ = lean_ctor_get(v_toRing_2038_, 1);
lean_inc_ref(v_type_2231_);
v_u_2232_ = lean_ctor_get(v_toRing_2038_, 2);
lean_inc(v_u_2232_);
lean_dec_ref(v_toRing_2038_);
v___x_2233_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__11));
v___x_2234_ = lean_box(0);
v___x_2235_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2235_, 0, v_u_2232_);
lean_ctor_set(v___x_2235_, 1, v___x_2234_);
v___x_2236_ = l_Lean_mkConst(v___x_2233_, v___x_2235_);
v___x_2237_ = l_Lean_mkAppB(v___x_2236_, v_type_2231_, v_val_2039_);
v___x_2238_ = l_Lean_Meta_Grind_pushEqCore___redArg(v_e_2004_, v_a_2006_, v___x_2237_, v___x_2066_, v_a_2008_, v_a_2010_, v_a_2014_, v_a_2015_, v_a_2016_, v_a_2017_);
if (lean_obj_tag(v___x_2238_) == 0)
{
lean_object* v___x_2240_; uint8_t v_isShared_2241_; uint8_t v_isSharedCheck_2246_; 
v_isSharedCheck_2246_ = !lean_is_exclusive(v___x_2238_);
if (v_isSharedCheck_2246_ == 0)
{
lean_object* v_unused_2247_; 
v_unused_2247_ = lean_ctor_get(v___x_2238_, 0);
lean_dec(v_unused_2247_);
v___x_2240_ = v___x_2238_;
v_isShared_2241_ = v_isSharedCheck_2246_;
goto v_resetjp_2239_;
}
else
{
lean_dec(v___x_2238_);
v___x_2240_ = lean_box(0);
v_isShared_2241_ = v_isSharedCheck_2246_;
goto v_resetjp_2239_;
}
v_resetjp_2239_:
{
lean_object* v___x_2242_; lean_object* v___x_2244_; 
v___x_2242_ = lean_box(0);
if (v_isShared_2241_ == 0)
{
lean_ctor_set(v___x_2240_, 0, v___x_2242_);
v___x_2244_ = v___x_2240_;
goto v_reusejp_2243_;
}
else
{
lean_object* v_reuseFailAlloc_2245_; 
v_reuseFailAlloc_2245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2245_, 0, v___x_2242_);
v___x_2244_ = v_reuseFailAlloc_2245_;
goto v_reusejp_2243_;
}
v_reusejp_2243_:
{
return v___x_2244_;
}
}
}
else
{
return v___x_2238_;
}
}
}
else
{
lean_dec(v_a_2070_);
lean_dec_ref(v_e_2004_);
v___y_2041_ = v_a_2008_;
v___y_2042_ = v_a_2009_;
v___y_2043_ = v_a_2010_;
v___y_2044_ = v_a_2011_;
v___y_2045_ = v_a_2012_;
v___y_2046_ = v_a_2013_;
v___y_2047_ = v_a_2014_;
v___y_2048_ = v_a_2015_;
v___y_2049_ = v_a_2016_;
v___y_2050_ = v_a_2017_;
goto v___jp_2040_;
}
}
else
{
lean_object* v_a_2248_; lean_object* v___x_2250_; uint8_t v_isShared_2251_; uint8_t v_isSharedCheck_2255_; 
lean_dec(v_val_2039_);
lean_dec_ref(v_toRing_2038_);
lean_dec_ref(v_a_2006_);
lean_dec_ref(v_e_2004_);
v_a_2248_ = lean_ctor_get(v___x_2069_, 0);
v_isSharedCheck_2255_ = !lean_is_exclusive(v___x_2069_);
if (v_isSharedCheck_2255_ == 0)
{
v___x_2250_ = v___x_2069_;
v_isShared_2251_ = v_isSharedCheck_2255_;
goto v_resetjp_2249_;
}
else
{
lean_inc(v_a_2248_);
lean_dec(v___x_2069_);
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
}
else
{
lean_dec(v_val_2039_);
lean_dec_ref(v_toRing_2038_);
lean_dec_ref(v_a_2006_);
lean_dec_ref(v_e_2004_);
return v___x_2068_;
}
}
else
{
lean_object* v___x_2256_; lean_object* v___x_2258_; 
lean_dec(v_val_2039_);
lean_dec_ref(v_toRing_2038_);
lean_dec_ref(v_a_2006_);
lean_dec_ref(v_e_2004_);
v___x_2256_ = lean_box(0);
if (v_isShared_2064_ == 0)
{
lean_ctor_set(v___x_2063_, 0, v___x_2256_);
v___x_2258_ = v___x_2063_;
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
lean_dec(v_val_2039_);
lean_dec_ref(v_toRing_2038_);
lean_dec_ref(v_a_2006_);
lean_dec_ref(v_e_2004_);
v_a_2261_ = lean_ctor_get(v___x_2060_, 0);
v_isSharedCheck_2268_ = !lean_is_exclusive(v___x_2060_);
if (v_isSharedCheck_2268_ == 0)
{
v___x_2263_ = v___x_2060_;
v_isShared_2264_ = v_isSharedCheck_2268_;
goto v_resetjp_2262_;
}
else
{
lean_inc(v_a_2261_);
lean_dec(v___x_2060_);
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
v___jp_2040_:
{
lean_object* v_type_2051_; lean_object* v_u_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; 
v_type_2051_ = lean_ctor_get(v_toRing_2038_, 1);
lean_inc_ref(v_type_2051_);
v_u_2052_ = lean_ctor_get(v_toRing_2038_, 2);
lean_inc(v_u_2052_);
lean_dec_ref(v_toRing_2038_);
v___x_2053_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__2));
v___x_2054_ = lean_box(0);
v___x_2055_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2055_, 0, v_u_2052_);
lean_ctor_set(v___x_2055_, 1, v___x_2054_);
v___x_2056_ = l_Lean_mkConst(v___x_2053_, v___x_2055_);
v___x_2057_ = l_Lean_mkApp3(v___x_2056_, v_type_2051_, v_val_2039_, v_a_2006_);
v___x_2058_ = lean_unsigned_to_nat(0u);
v___x_2059_ = l_Lean_Meta_Grind_pushNewFact(v___x_2057_, v___x_2058_, v___y_2041_, v___y_2042_, v___y_2043_, v___y_2044_, v___y_2045_, v___y_2046_, v___y_2047_, v___y_2048_, v___y_2049_, v___y_2050_);
return v___x_2059_;
}
}
else
{
lean_object* v___x_2269_; lean_object* v___x_2271_; 
lean_dec(v_fieldInst_x3f_2037_);
lean_dec(v_a_2033_);
lean_dec_ref(v_a_2006_);
lean_dec_ref(v_e_2004_);
v___x_2269_ = lean_box(0);
if (v_isShared_2036_ == 0)
{
lean_ctor_set(v___x_2035_, 0, v___x_2269_);
v___x_2271_ = v___x_2035_;
goto v_reusejp_2270_;
}
else
{
lean_object* v_reuseFailAlloc_2272_; 
v_reuseFailAlloc_2272_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2272_, 0, v___x_2269_);
v___x_2271_ = v_reuseFailAlloc_2272_;
goto v_reusejp_2270_;
}
v_reusejp_2270_:
{
return v___x_2271_;
}
}
}
}
else
{
lean_object* v_a_2274_; lean_object* v___x_2276_; uint8_t v_isShared_2277_; uint8_t v_isSharedCheck_2281_; 
lean_dec_ref(v_a_2006_);
lean_dec_ref(v_e_2004_);
v_a_2274_ = lean_ctor_get(v___x_2032_, 0);
v_isSharedCheck_2281_ = !lean_is_exclusive(v___x_2032_);
if (v_isSharedCheck_2281_ == 0)
{
v___x_2276_ = v___x_2032_;
v_isShared_2277_ = v_isSharedCheck_2281_;
goto v_resetjp_2275_;
}
else
{
lean_inc(v_a_2274_);
lean_dec(v___x_2032_);
v___x_2276_ = lean_box(0);
v_isShared_2277_ = v_isSharedCheck_2281_;
goto v_resetjp_2275_;
}
v_resetjp_2275_:
{
lean_object* v___x_2279_; 
if (v_isShared_2277_ == 0)
{
v___x_2279_ = v___x_2276_;
goto v_reusejp_2278_;
}
else
{
lean_object* v_reuseFailAlloc_2280_; 
v_reuseFailAlloc_2280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2280_, 0, v_a_2274_);
v___x_2279_ = v_reuseFailAlloc_2280_;
goto v_reusejp_2278_;
}
v_reusejp_2278_:
{
return v___x_2279_;
}
}
}
}
}
}
else
{
lean_object* v_a_2283_; lean_object* v___x_2285_; uint8_t v_isShared_2286_; uint8_t v_isSharedCheck_2290_; 
lean_dec_ref(v_a_2006_);
lean_dec_ref(v_e_2004_);
v_a_2283_ = lean_ctor_get(v___x_2022_, 0);
v_isSharedCheck_2290_ = !lean_is_exclusive(v___x_2022_);
if (v_isSharedCheck_2290_ == 0)
{
v___x_2285_ = v___x_2022_;
v_isShared_2286_ = v_isSharedCheck_2290_;
goto v_resetjp_2284_;
}
else
{
lean_inc(v_a_2283_);
lean_dec(v___x_2022_);
v___x_2285_ = lean_box(0);
v_isShared_2286_ = v_isSharedCheck_2290_;
goto v_resetjp_2284_;
}
v_resetjp_2284_:
{
lean_object* v___x_2288_; 
if (v_isShared_2286_ == 0)
{
v___x_2288_ = v___x_2285_;
goto v_reusejp_2287_;
}
else
{
lean_object* v_reuseFailAlloc_2289_; 
v_reuseFailAlloc_2289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2289_, 0, v_a_2283_);
v___x_2288_ = v_reuseFailAlloc_2289_;
goto v_reusejp_2287_;
}
v_reusejp_2287_:
{
return v___x_2288_;
}
}
}
v___jp_2019_:
{
lean_object* v___x_2020_; lean_object* v___x_2021_; 
v___x_2020_ = lean_box(0);
v___x_2021_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2021_, 0, v___x_2020_);
return v___x_2021_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___boxed(lean_object* v_e_2291_, lean_object* v_inst_2292_, lean_object* v_a_2293_, lean_object* v_a_2294_, lean_object* v_a_2295_, lean_object* v_a_2296_, lean_object* v_a_2297_, lean_object* v_a_2298_, lean_object* v_a_2299_, lean_object* v_a_2300_, lean_object* v_a_2301_, lean_object* v_a_2302_, lean_object* v_a_2303_, lean_object* v_a_2304_, lean_object* v_a_2305_){
_start:
{
lean_object* v_res_2306_; 
v_res_2306_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv(v_e_2291_, v_inst_2292_, v_a_2293_, v_a_2294_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_, v_a_2301_, v_a_2302_, v_a_2303_, v_a_2304_);
lean_dec(v_a_2304_);
lean_dec_ref(v_a_2303_);
lean_dec(v_a_2302_);
lean_dec_ref(v_a_2301_);
lean_dec(v_a_2300_);
lean_dec_ref(v_a_2299_);
lean_dec(v_a_2298_);
lean_dec_ref(v_a_2297_);
lean_dec(v_a_2296_);
lean_dec(v_a_2295_);
lean_dec_ref(v_a_2294_);
lean_dec_ref(v_inst_2292_);
return v_res_2306_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0(lean_object* v_00_u03b2_2307_, lean_object* v_x_2308_, lean_object* v_x_2309_, lean_object* v_x_2310_){
_start:
{
lean_object* v___x_2311_; 
v___x_2311_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0___redArg(v_x_2308_, v_x_2309_, v_x_2310_);
return v___x_2311_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1(lean_object* v_00_u03b2_2312_, lean_object* v_x_2313_, lean_object* v_x_2314_){
_start:
{
uint8_t v___x_2315_; 
v___x_2315_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1___redArg(v_x_2313_, v_x_2314_);
return v___x_2315_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1___boxed(lean_object* v_00_u03b2_2316_, lean_object* v_x_2317_, lean_object* v_x_2318_){
_start:
{
uint8_t v_res_2319_; lean_object* v_r_2320_; 
v_res_2319_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1(v_00_u03b2_2316_, v_x_2317_, v_x_2318_);
lean_dec_ref(v_x_2318_);
lean_dec_ref(v_x_2317_);
v_r_2320_ = lean_box(v_res_2319_);
return v_r_2320_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0(lean_object* v_00_u03b2_2321_, lean_object* v_x_2322_, size_t v_x_2323_, size_t v_x_2324_, lean_object* v_x_2325_, lean_object* v_x_2326_){
_start:
{
lean_object* v___x_2327_; 
v___x_2327_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg(v_x_2322_, v_x_2323_, v_x_2324_, v_x_2325_, v_x_2326_);
return v___x_2327_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2328_, lean_object* v_x_2329_, lean_object* v_x_2330_, lean_object* v_x_2331_, lean_object* v_x_2332_, lean_object* v_x_2333_){
_start:
{
size_t v_x_82460__boxed_2334_; size_t v_x_82461__boxed_2335_; lean_object* v_res_2336_; 
v_x_82460__boxed_2334_ = lean_unbox_usize(v_x_2330_);
lean_dec(v_x_2330_);
v_x_82461__boxed_2335_ = lean_unbox_usize(v_x_2331_);
lean_dec(v_x_2331_);
v_res_2336_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0(v_00_u03b2_2328_, v_x_2329_, v_x_82460__boxed_2334_, v_x_82461__boxed_2335_, v_x_2332_, v_x_2333_);
return v_res_2336_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1_spec__2(lean_object* v_00_u03b2_2337_, lean_object* v_x_2338_, size_t v_x_2339_, lean_object* v_x_2340_){
_start:
{
uint8_t v___x_2341_; 
v___x_2341_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1_spec__2___redArg(v_x_2338_, v_x_2339_, v_x_2340_);
return v___x_2341_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1_spec__2___boxed(lean_object* v_00_u03b2_2342_, lean_object* v_x_2343_, lean_object* v_x_2344_, lean_object* v_x_2345_){
_start:
{
size_t v_x_82477__boxed_2346_; uint8_t v_res_2347_; lean_object* v_r_2348_; 
v_x_82477__boxed_2346_ = lean_unbox_usize(v_x_2344_);
lean_dec(v_x_2344_);
v_res_2347_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1_spec__2(v_00_u03b2_2342_, v_x_2343_, v_x_82477__boxed_2346_, v_x_2345_);
lean_dec_ref(v_x_2345_);
lean_dec_ref(v_x_2343_);
v_r_2348_ = lean_box(v_res_2347_);
return v_r_2348_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_2349_, lean_object* v_n_2350_, lean_object* v_k_2351_, lean_object* v_v_2352_){
_start:
{
lean_object* v___x_2353_; 
v___x_2353_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0_spec__2___redArg(v_n_2350_, v_k_2351_, v_v_2352_);
return v___x_2353_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_2354_, size_t v_depth_2355_, lean_object* v_keys_2356_, lean_object* v_vals_2357_, lean_object* v_heq_2358_, lean_object* v_i_2359_, lean_object* v_entries_2360_){
_start:
{
lean_object* v___x_2361_; 
v___x_2361_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0_spec__3___redArg(v_depth_2355_, v_keys_2356_, v_vals_2357_, v_i_2359_, v_entries_2360_);
return v___x_2361_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b2_2362_, lean_object* v_depth_2363_, lean_object* v_keys_2364_, lean_object* v_vals_2365_, lean_object* v_heq_2366_, lean_object* v_i_2367_, lean_object* v_entries_2368_){
_start:
{
size_t v_depth_boxed_2369_; lean_object* v_res_2370_; 
v_depth_boxed_2369_ = lean_unbox_usize(v_depth_2363_);
lean_dec(v_depth_2363_);
v_res_2370_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0_spec__3(v_00_u03b2_2362_, v_depth_boxed_2369_, v_keys_2364_, v_vals_2365_, v_heq_2366_, v_i_2367_, v_entries_2368_);
lean_dec_ref(v_vals_2365_);
lean_dec_ref(v_keys_2364_);
return v_res_2370_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1_spec__2_spec__6(lean_object* v_00_u03b2_2371_, lean_object* v_keys_2372_, lean_object* v_vals_2373_, lean_object* v_heq_2374_, lean_object* v_i_2375_, lean_object* v_k_2376_){
_start:
{
uint8_t v___x_2377_; 
v___x_2377_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1_spec__2_spec__6___redArg(v_keys_2372_, v_i_2375_, v_k_2376_);
return v___x_2377_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1_spec__2_spec__6___boxed(lean_object* v_00_u03b2_2378_, lean_object* v_keys_2379_, lean_object* v_vals_2380_, lean_object* v_heq_2381_, lean_object* v_i_2382_, lean_object* v_k_2383_){
_start:
{
uint8_t v_res_2384_; lean_object* v_r_2385_; 
v_res_2384_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1_spec__2_spec__6(v_00_u03b2_2378_, v_keys_2379_, v_vals_2380_, v_heq_2381_, v_i_2382_, v_k_2383_);
lean_dec_ref(v_k_2383_);
lean_dec_ref(v_vals_2380_);
lean_dec_ref(v_keys_2379_);
v_r_2385_ = lean_box(v_res_2384_);
return v_r_2385_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0_spec__2_spec__6(lean_object* v_00_u03b2_2386_, lean_object* v_x_2387_, lean_object* v_x_2388_, lean_object* v_x_2389_, lean_object* v_x_2390_){
_start:
{
lean_object* v___x_2391_; 
v___x_2391_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0_spec__2_spec__6___redArg(v_x_2387_, v_x_2388_, v_x_2389_, v_x_2390_);
return v___x_2391_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars___lam__0(lean_object* v_size_2392_, lean_object* v_s_2393_){
_start:
{
lean_object* v_toRing_2394_; lean_object* v_invFn_x3f_2395_; lean_object* v_semiringId_x3f_2396_; lean_object* v_commSemiringInst_2397_; lean_object* v_commRingInst_2398_; lean_object* v_noZeroDivInst_x3f_2399_; lean_object* v_fieldInst_x3f_2400_; lean_object* v_powIdentityInst_x3f_2401_; lean_object* v_denoteEntries_2402_; lean_object* v_nextId_2403_; lean_object* v_steps_2404_; lean_object* v_queue_2405_; lean_object* v_basis_2406_; lean_object* v_diseqs_2407_; uint8_t v_recheck_2408_; lean_object* v_invSet_2409_; lean_object* v_numEq0_x3f_2410_; uint8_t v_numEq0Updated_2411_; lean_object* v___x_2413_; uint8_t v_isShared_2414_; uint8_t v_isSharedCheck_2418_; 
v_toRing_2394_ = lean_ctor_get(v_s_2393_, 0);
v_invFn_x3f_2395_ = lean_ctor_get(v_s_2393_, 1);
v_semiringId_x3f_2396_ = lean_ctor_get(v_s_2393_, 2);
v_commSemiringInst_2397_ = lean_ctor_get(v_s_2393_, 3);
v_commRingInst_2398_ = lean_ctor_get(v_s_2393_, 4);
v_noZeroDivInst_x3f_2399_ = lean_ctor_get(v_s_2393_, 5);
v_fieldInst_x3f_2400_ = lean_ctor_get(v_s_2393_, 6);
v_powIdentityInst_x3f_2401_ = lean_ctor_get(v_s_2393_, 7);
v_denoteEntries_2402_ = lean_ctor_get(v_s_2393_, 8);
v_nextId_2403_ = lean_ctor_get(v_s_2393_, 9);
v_steps_2404_ = lean_ctor_get(v_s_2393_, 10);
v_queue_2405_ = lean_ctor_get(v_s_2393_, 11);
v_basis_2406_ = lean_ctor_get(v_s_2393_, 12);
v_diseqs_2407_ = lean_ctor_get(v_s_2393_, 13);
v_recheck_2408_ = lean_ctor_get_uint8(v_s_2393_, sizeof(void*)*17);
v_invSet_2409_ = lean_ctor_get(v_s_2393_, 14);
v_numEq0_x3f_2410_ = lean_ctor_get(v_s_2393_, 16);
v_numEq0Updated_2411_ = lean_ctor_get_uint8(v_s_2393_, sizeof(void*)*17 + 1);
v_isSharedCheck_2418_ = !lean_is_exclusive(v_s_2393_);
if (v_isSharedCheck_2418_ == 0)
{
lean_object* v_unused_2419_; 
v_unused_2419_ = lean_ctor_get(v_s_2393_, 15);
lean_dec(v_unused_2419_);
v___x_2413_ = v_s_2393_;
v_isShared_2414_ = v_isSharedCheck_2418_;
goto v_resetjp_2412_;
}
else
{
lean_inc(v_numEq0_x3f_2410_);
lean_inc(v_invSet_2409_);
lean_inc(v_diseqs_2407_);
lean_inc(v_basis_2406_);
lean_inc(v_queue_2405_);
lean_inc(v_steps_2404_);
lean_inc(v_nextId_2403_);
lean_inc(v_denoteEntries_2402_);
lean_inc(v_powIdentityInst_x3f_2401_);
lean_inc(v_fieldInst_x3f_2400_);
lean_inc(v_noZeroDivInst_x3f_2399_);
lean_inc(v_commRingInst_2398_);
lean_inc(v_commSemiringInst_2397_);
lean_inc(v_semiringId_x3f_2396_);
lean_inc(v_invFn_x3f_2395_);
lean_inc(v_toRing_2394_);
lean_dec(v_s_2393_);
v___x_2413_ = lean_box(0);
v_isShared_2414_ = v_isSharedCheck_2418_;
goto v_resetjp_2412_;
}
v_resetjp_2412_:
{
lean_object* v___x_2416_; 
if (v_isShared_2414_ == 0)
{
lean_ctor_set(v___x_2413_, 15, v_size_2392_);
v___x_2416_ = v___x_2413_;
goto v_reusejp_2415_;
}
else
{
lean_object* v_reuseFailAlloc_2417_; 
v_reuseFailAlloc_2417_ = lean_alloc_ctor(0, 17, 2);
lean_ctor_set(v_reuseFailAlloc_2417_, 0, v_toRing_2394_);
lean_ctor_set(v_reuseFailAlloc_2417_, 1, v_invFn_x3f_2395_);
lean_ctor_set(v_reuseFailAlloc_2417_, 2, v_semiringId_x3f_2396_);
lean_ctor_set(v_reuseFailAlloc_2417_, 3, v_commSemiringInst_2397_);
lean_ctor_set(v_reuseFailAlloc_2417_, 4, v_commRingInst_2398_);
lean_ctor_set(v_reuseFailAlloc_2417_, 5, v_noZeroDivInst_x3f_2399_);
lean_ctor_set(v_reuseFailAlloc_2417_, 6, v_fieldInst_x3f_2400_);
lean_ctor_set(v_reuseFailAlloc_2417_, 7, v_powIdentityInst_x3f_2401_);
lean_ctor_set(v_reuseFailAlloc_2417_, 8, v_denoteEntries_2402_);
lean_ctor_set(v_reuseFailAlloc_2417_, 9, v_nextId_2403_);
lean_ctor_set(v_reuseFailAlloc_2417_, 10, v_steps_2404_);
lean_ctor_set(v_reuseFailAlloc_2417_, 11, v_queue_2405_);
lean_ctor_set(v_reuseFailAlloc_2417_, 12, v_basis_2406_);
lean_ctor_set(v_reuseFailAlloc_2417_, 13, v_diseqs_2407_);
lean_ctor_set(v_reuseFailAlloc_2417_, 14, v_invSet_2409_);
lean_ctor_set(v_reuseFailAlloc_2417_, 15, v_size_2392_);
lean_ctor_set(v_reuseFailAlloc_2417_, 16, v_numEq0_x3f_2410_);
lean_ctor_set_uint8(v_reuseFailAlloc_2417_, sizeof(void*)*17, v_recheck_2408_);
lean_ctor_set_uint8(v_reuseFailAlloc_2417_, sizeof(void*)*17 + 1, v_numEq0Updated_2411_);
v___x_2416_ = v_reuseFailAlloc_2417_;
goto v_reusejp_2415_;
}
v_reusejp_2415_:
{
return v___x_2416_;
}
}
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_2420_; double v___x_2421_; 
v___x_2420_ = lean_unsigned_to_nat(0u);
v___x_2421_ = lean_float_of_nat(v___x_2420_);
return v___x_2421_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg(lean_object* v_cls_2425_, lean_object* v_msg_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_){
_start:
{
lean_object* v_ref_2432_; lean_object* v___x_2433_; lean_object* v_a_2434_; lean_object* v___x_2436_; uint8_t v_isShared_2437_; uint8_t v_isSharedCheck_2478_; 
v_ref_2432_ = lean_ctor_get(v___y_2429_, 4);
v___x_2433_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1_spec__5_spec__8_spec__9(v_msg_2426_, v___y_2427_, v___y_2428_, v___y_2429_, v___y_2430_);
v_a_2434_ = lean_ctor_get(v___x_2433_, 0);
v_isSharedCheck_2478_ = !lean_is_exclusive(v___x_2433_);
if (v_isSharedCheck_2478_ == 0)
{
v___x_2436_ = v___x_2433_;
v_isShared_2437_ = v_isSharedCheck_2478_;
goto v_resetjp_2435_;
}
else
{
lean_inc(v_a_2434_);
lean_dec(v___x_2433_);
v___x_2436_ = lean_box(0);
v_isShared_2437_ = v_isSharedCheck_2478_;
goto v_resetjp_2435_;
}
v_resetjp_2435_:
{
lean_object* v___x_2438_; lean_object* v_traceState_2439_; lean_object* v_env_2440_; lean_object* v_nextMacroScope_2441_; lean_object* v_ngen_2442_; lean_object* v_auxDeclNGen_2443_; lean_object* v_cache_2444_; lean_object* v_messages_2445_; lean_object* v_infoState_2446_; lean_object* v_snapshotTasks_2447_; lean_object* v___x_2449_; uint8_t v_isShared_2450_; uint8_t v_isSharedCheck_2477_; 
v___x_2438_ = lean_st_ref_take(v___y_2430_);
v_traceState_2439_ = lean_ctor_get(v___x_2438_, 4);
v_env_2440_ = lean_ctor_get(v___x_2438_, 0);
v_nextMacroScope_2441_ = lean_ctor_get(v___x_2438_, 1);
v_ngen_2442_ = lean_ctor_get(v___x_2438_, 2);
v_auxDeclNGen_2443_ = lean_ctor_get(v___x_2438_, 3);
v_cache_2444_ = lean_ctor_get(v___x_2438_, 5);
v_messages_2445_ = lean_ctor_get(v___x_2438_, 6);
v_infoState_2446_ = lean_ctor_get(v___x_2438_, 7);
v_snapshotTasks_2447_ = lean_ctor_get(v___x_2438_, 8);
v_isSharedCheck_2477_ = !lean_is_exclusive(v___x_2438_);
if (v_isSharedCheck_2477_ == 0)
{
v___x_2449_ = v___x_2438_;
v_isShared_2450_ = v_isSharedCheck_2477_;
goto v_resetjp_2448_;
}
else
{
lean_inc(v_snapshotTasks_2447_);
lean_inc(v_infoState_2446_);
lean_inc(v_messages_2445_);
lean_inc(v_cache_2444_);
lean_inc(v_traceState_2439_);
lean_inc(v_auxDeclNGen_2443_);
lean_inc(v_ngen_2442_);
lean_inc(v_nextMacroScope_2441_);
lean_inc(v_env_2440_);
lean_dec(v___x_2438_);
v___x_2449_ = lean_box(0);
v_isShared_2450_ = v_isSharedCheck_2477_;
goto v_resetjp_2448_;
}
v_resetjp_2448_:
{
uint64_t v_tid_2451_; lean_object* v_traces_2452_; lean_object* v___x_2454_; uint8_t v_isShared_2455_; uint8_t v_isSharedCheck_2476_; 
v_tid_2451_ = lean_ctor_get_uint64(v_traceState_2439_, sizeof(void*)*1);
v_traces_2452_ = lean_ctor_get(v_traceState_2439_, 0);
v_isSharedCheck_2476_ = !lean_is_exclusive(v_traceState_2439_);
if (v_isSharedCheck_2476_ == 0)
{
v___x_2454_ = v_traceState_2439_;
v_isShared_2455_ = v_isSharedCheck_2476_;
goto v_resetjp_2453_;
}
else
{
lean_inc(v_traces_2452_);
lean_dec(v_traceState_2439_);
v___x_2454_ = lean_box(0);
v_isShared_2455_ = v_isSharedCheck_2476_;
goto v_resetjp_2453_;
}
v_resetjp_2453_:
{
lean_object* v___x_2456_; double v___x_2457_; uint8_t v___x_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2466_; 
v___x_2456_ = lean_box(0);
v___x_2457_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg___closed__0);
v___x_2458_ = 0;
v___x_2459_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg___closed__1));
v___x_2460_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2460_, 0, v_cls_2425_);
lean_ctor_set(v___x_2460_, 1, v___x_2456_);
lean_ctor_set(v___x_2460_, 2, v___x_2459_);
lean_ctor_set_float(v___x_2460_, sizeof(void*)*3, v___x_2457_);
lean_ctor_set_float(v___x_2460_, sizeof(void*)*3 + 8, v___x_2457_);
lean_ctor_set_uint8(v___x_2460_, sizeof(void*)*3 + 16, v___x_2458_);
v___x_2461_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg___closed__2));
v___x_2462_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2462_, 0, v___x_2460_);
lean_ctor_set(v___x_2462_, 1, v_a_2434_);
lean_ctor_set(v___x_2462_, 2, v___x_2461_);
lean_inc(v_ref_2432_);
v___x_2463_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2463_, 0, v_ref_2432_);
lean_ctor_set(v___x_2463_, 1, v___x_2462_);
v___x_2464_ = l_Lean_PersistentArray_push___redArg(v_traces_2452_, v___x_2463_);
if (v_isShared_2455_ == 0)
{
lean_ctor_set(v___x_2454_, 0, v___x_2464_);
v___x_2466_ = v___x_2454_;
goto v_reusejp_2465_;
}
else
{
lean_object* v_reuseFailAlloc_2475_; 
v_reuseFailAlloc_2475_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2475_, 0, v___x_2464_);
lean_ctor_set_uint64(v_reuseFailAlloc_2475_, sizeof(void*)*1, v_tid_2451_);
v___x_2466_ = v_reuseFailAlloc_2475_;
goto v_reusejp_2465_;
}
v_reusejp_2465_:
{
lean_object* v___x_2468_; 
if (v_isShared_2450_ == 0)
{
lean_ctor_set(v___x_2449_, 4, v___x_2466_);
v___x_2468_ = v___x_2449_;
goto v_reusejp_2467_;
}
else
{
lean_object* v_reuseFailAlloc_2474_; 
v_reuseFailAlloc_2474_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2474_, 0, v_env_2440_);
lean_ctor_set(v_reuseFailAlloc_2474_, 1, v_nextMacroScope_2441_);
lean_ctor_set(v_reuseFailAlloc_2474_, 2, v_ngen_2442_);
lean_ctor_set(v_reuseFailAlloc_2474_, 3, v_auxDeclNGen_2443_);
lean_ctor_set(v_reuseFailAlloc_2474_, 4, v___x_2466_);
lean_ctor_set(v_reuseFailAlloc_2474_, 5, v_cache_2444_);
lean_ctor_set(v_reuseFailAlloc_2474_, 6, v_messages_2445_);
lean_ctor_set(v_reuseFailAlloc_2474_, 7, v_infoState_2446_);
lean_ctor_set(v_reuseFailAlloc_2474_, 8, v_snapshotTasks_2447_);
v___x_2468_ = v_reuseFailAlloc_2474_;
goto v_reusejp_2467_;
}
v_reusejp_2467_:
{
lean_object* v___x_2469_; lean_object* v___x_2470_; lean_object* v___x_2472_; 
v___x_2469_ = lean_st_ref_put(v___y_2430_, v___x_2468_);
v___x_2470_ = lean_box(0);
if (v_isShared_2437_ == 0)
{
lean_ctor_set(v___x_2436_, 0, v___x_2470_);
v___x_2472_ = v___x_2436_;
goto v_reusejp_2471_;
}
else
{
lean_object* v_reuseFailAlloc_2473_; 
v_reuseFailAlloc_2473_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2473_, 0, v___x_2470_);
v___x_2472_ = v_reuseFailAlloc_2473_;
goto v_reusejp_2471_;
}
v_reusejp_2471_:
{
return v___x_2472_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg___boxed(lean_object* v_cls_2479_, lean_object* v_msg_2480_, lean_object* v___y_2481_, lean_object* v___y_2482_, lean_object* v___y_2483_, lean_object* v___y_2484_, lean_object* v___y_2485_){
_start:
{
lean_object* v_res_2486_; 
v_res_2486_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg(v_cls_2479_, v_msg_2480_, v___y_2481_, v___y_2482_, v___y_2483_, v___y_2484_);
lean_dec(v___y_2484_);
lean_dec_ref(v___y_2483_);
lean_dec(v___y_2482_);
lean_dec_ref(v___y_2481_);
return v_res_2486_;
}
}
static lean_object* _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__8(void){
_start:
{
lean_object* v___x_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; 
v___x_2502_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__5));
v___x_2503_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__7));
v___x_2504_ = l_Lean_Name_append(v___x_2503_, v___x_2502_);
return v___x_2504_;
}
}
static lean_object* _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__10(void){
_start:
{
lean_object* v___x_2506_; lean_object* v___x_2507_; 
v___x_2506_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__9));
v___x_2507_ = l_Lean_stringToMessageData(v___x_2506_);
return v___x_2507_;
}
}
static lean_object* _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__12(void){
_start:
{
lean_object* v___x_2509_; lean_object* v___x_2510_; 
v___x_2509_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__11));
v___x_2510_ = l_Lean_stringToMessageData(v___x_2509_);
return v___x_2510_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg(lean_object* v___x_2511_, lean_object* v_snd_2512_, lean_object* v_fst_2513_, lean_object* v_fst_2514_, lean_object* v___x_2515_, lean_object* v_range_2516_, lean_object* v_b_2517_, lean_object* v_i_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_, lean_object* v___y_2524_, lean_object* v___y_2525_, lean_object* v___y_2526_, lean_object* v___y_2527_, lean_object* v___y_2528_, lean_object* v___y_2529_){
_start:
{
lean_object* v_stop_2531_; lean_object* v_step_2532_; uint8_t v___x_2533_; 
v_stop_2531_ = lean_ctor_get(v_range_2516_, 1);
v_step_2532_ = lean_ctor_get(v_range_2516_, 2);
v___x_2533_ = lean_nat_dec_lt(v_i_2518_, v_stop_2531_);
if (v___x_2533_ == 0)
{
lean_object* v___x_2534_; 
lean_dec(v_i_2518_);
lean_dec_ref(v_fst_2514_);
lean_dec_ref(v_fst_2513_);
lean_dec(v_snd_2512_);
lean_dec_ref(v___x_2511_);
v___x_2534_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2534_, 0, v_b_2517_);
return v___x_2534_;
}
else
{
lean_object* v_size_2535_; lean_object* v___x_2536_; lean_object* v___y_2538_; lean_object* v___y_2539_; lean_object* v___y_2540_; lean_object* v___y_2541_; lean_object* v___y_2542_; lean_object* v___y_2543_; lean_object* v___y_2544_; lean_object* v___y_2545_; lean_object* v___y_2546_; lean_object* v___y_2547_; lean_object* v___y_2548_; lean_object* v___y_2562_; lean_object* v___x_2588_; uint8_t v___x_2589_; 
v_size_2535_ = lean_ctor_get(v___x_2515_, 2);
v___x_2536_ = lean_box(0);
v___x_2588_ = l_Lean_instInhabitedExpr;
v___x_2589_ = lean_nat_dec_lt(v_i_2518_, v_size_2535_);
if (v___x_2589_ == 0)
{
lean_object* v___x_2590_; 
v___x_2590_ = l_outOfBounds___redArg(v___x_2588_);
v___y_2562_ = v___x_2590_;
goto v___jp_2561_;
}
else
{
lean_object* v___x_2591_; 
v___x_2591_ = l_Lean_PersistentArray_get_x21___redArg(v___x_2588_, v___x_2515_, v_i_2518_);
v___y_2562_ = v___x_2591_;
goto v___jp_2561_;
}
v___jp_2537_:
{
lean_object* v_type_2549_; lean_object* v_u_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; 
v_type_2549_ = lean_ctor_get(v___x_2511_, 1);
v_u_2550_ = lean_ctor_get(v___x_2511_, 2);
v___x_2551_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__2));
v___x_2552_ = lean_box(0);
lean_inc(v_u_2550_);
v___x_2553_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2553_, 0, v_u_2550_);
lean_ctor_set(v___x_2553_, 1, v___x_2552_);
v___x_2554_ = l_Lean_mkConst(v___x_2551_, v___x_2553_);
lean_inc(v_snd_2512_);
v___x_2555_ = l_Lean_mkNatLit(v_snd_2512_);
lean_inc_ref(v_fst_2514_);
lean_inc_ref(v_fst_2513_);
lean_inc_ref(v_type_2549_);
v___x_2556_ = l_Lean_mkApp5(v___x_2554_, v_type_2549_, v_fst_2513_, v___x_2555_, v_fst_2514_, v___y_2538_);
v___x_2557_ = lean_unsigned_to_nat(0u);
v___x_2558_ = l_Lean_Meta_Grind_pushNewFact(v___x_2556_, v___x_2557_, v___y_2539_, v___y_2540_, v___y_2541_, v___y_2542_, v___y_2543_, v___y_2544_, v___y_2545_, v___y_2546_, v___y_2547_, v___y_2548_);
if (lean_obj_tag(v___x_2558_) == 0)
{
lean_object* v___x_2559_; 
lean_dec_ref_known(v___x_2558_, 1);
v___x_2559_ = lean_nat_add(v_i_2518_, v_step_2532_);
lean_dec(v_i_2518_);
v_b_2517_ = v___x_2536_;
v_i_2518_ = v___x_2559_;
goto _start;
}
else
{
lean_dec(v_i_2518_);
lean_dec_ref(v_fst_2514_);
lean_dec_ref(v_fst_2513_);
lean_dec(v_snd_2512_);
lean_dec_ref(v___x_2511_);
return v___x_2558_;
}
}
v___jp_2561_:
{
lean_object* v_options_2563_; uint8_t v_hasTrace_2564_; 
v_options_2563_ = lean_ctor_get(v___y_2528_, 1);
v_hasTrace_2564_ = lean_ctor_get_uint8(v_options_2563_, sizeof(void*)*1);
if (v_hasTrace_2564_ == 0)
{
v___y_2538_ = v___y_2562_;
v___y_2539_ = v___y_2520_;
v___y_2540_ = v___y_2521_;
v___y_2541_ = v___y_2522_;
v___y_2542_ = v___y_2523_;
v___y_2543_ = v___y_2524_;
v___y_2544_ = v___y_2525_;
v___y_2545_ = v___y_2526_;
v___y_2546_ = v___y_2527_;
v___y_2547_ = v___y_2528_;
v___y_2548_ = v___y_2529_;
goto v___jp_2537_;
}
else
{
lean_object* v_toCold_2565_; lean_object* v_inheritedTraceOptions_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; uint8_t v___x_2569_; 
v_toCold_2565_ = lean_ctor_get(v___y_2528_, 0);
v_inheritedTraceOptions_2566_ = lean_ctor_get(v_toCold_2565_, 4);
v___x_2567_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__5));
v___x_2568_ = lean_obj_once(&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__8, &l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__8_once, _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__8);
v___x_2569_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2566_, v_options_2563_, v___x_2568_);
if (v___x_2569_ == 0)
{
v___y_2538_ = v___y_2562_;
v___y_2539_ = v___y_2520_;
v___y_2540_ = v___y_2521_;
v___y_2541_ = v___y_2522_;
v___y_2542_ = v___y_2523_;
v___y_2543_ = v___y_2524_;
v___y_2544_ = v___y_2525_;
v___y_2545_ = v___y_2526_;
v___y_2546_ = v___y_2527_;
v___y_2547_ = v___y_2528_;
v___y_2548_ = v___y_2529_;
goto v___jp_2537_;
}
else
{
lean_object* v___x_2570_; 
v___x_2570_ = l_Lean_Meta_Grind_updateLastTag(v___y_2520_, v___y_2521_, v___y_2522_, v___y_2523_, v___y_2524_, v___y_2525_, v___y_2526_, v___y_2527_, v___y_2528_, v___y_2529_);
if (lean_obj_tag(v___x_2570_) == 0)
{
lean_object* v___x_2572_; uint8_t v_isShared_2573_; uint8_t v_isSharedCheck_2586_; 
v_isSharedCheck_2586_ = !lean_is_exclusive(v___x_2570_);
if (v_isSharedCheck_2586_ == 0)
{
lean_object* v_unused_2587_; 
v_unused_2587_ = lean_ctor_get(v___x_2570_, 0);
lean_dec(v_unused_2587_);
v___x_2572_ = v___x_2570_;
v_isShared_2573_ = v_isSharedCheck_2586_;
goto v_resetjp_2571_;
}
else
{
lean_dec(v___x_2570_);
v___x_2572_ = lean_box(0);
v_isShared_2573_ = v_isSharedCheck_2586_;
goto v_resetjp_2571_;
}
v_resetjp_2571_:
{
lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2577_; 
v___x_2574_ = lean_obj_once(&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__10, &l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__10_once, _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__10);
lean_inc(v_snd_2512_);
v___x_2575_ = l_Nat_reprFast(v_snd_2512_);
if (v_isShared_2573_ == 0)
{
lean_ctor_set_tag(v___x_2572_, 3);
lean_ctor_set(v___x_2572_, 0, v___x_2575_);
v___x_2577_ = v___x_2572_;
goto v_reusejp_2576_;
}
else
{
lean_object* v_reuseFailAlloc_2585_; 
v_reuseFailAlloc_2585_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2585_, 0, v___x_2575_);
v___x_2577_ = v_reuseFailAlloc_2585_;
goto v_reusejp_2576_;
}
v_reusejp_2576_:
{
lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; 
v___x_2578_ = l_Lean_MessageData_ofFormat(v___x_2577_);
v___x_2579_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2579_, 0, v___x_2574_);
lean_ctor_set(v___x_2579_, 1, v___x_2578_);
v___x_2580_ = lean_obj_once(&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__12, &l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__12_once, _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__12);
v___x_2581_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2581_, 0, v___x_2579_);
lean_ctor_set(v___x_2581_, 1, v___x_2580_);
lean_inc_ref(v___y_2562_);
v___x_2582_ = l_Lean_MessageData_ofExpr(v___y_2562_);
v___x_2583_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2583_, 0, v___x_2581_);
lean_ctor_set(v___x_2583_, 1, v___x_2582_);
v___x_2584_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg(v___x_2567_, v___x_2583_, v___y_2526_, v___y_2527_, v___y_2528_, v___y_2529_);
if (lean_obj_tag(v___x_2584_) == 0)
{
lean_dec_ref_known(v___x_2584_, 1);
v___y_2538_ = v___y_2562_;
v___y_2539_ = v___y_2520_;
v___y_2540_ = v___y_2521_;
v___y_2541_ = v___y_2522_;
v___y_2542_ = v___y_2523_;
v___y_2543_ = v___y_2524_;
v___y_2544_ = v___y_2525_;
v___y_2545_ = v___y_2526_;
v___y_2546_ = v___y_2527_;
v___y_2547_ = v___y_2528_;
v___y_2548_ = v___y_2529_;
goto v___jp_2537_;
}
else
{
lean_dec_ref(v___y_2562_);
lean_dec(v_i_2518_);
lean_dec_ref(v_fst_2514_);
lean_dec_ref(v_fst_2513_);
lean_dec(v_snd_2512_);
lean_dec_ref(v___x_2511_);
return v___x_2584_;
}
}
}
}
else
{
lean_dec_ref(v___y_2562_);
lean_dec(v_i_2518_);
lean_dec_ref(v_fst_2514_);
lean_dec_ref(v_fst_2513_);
lean_dec(v_snd_2512_);
lean_dec_ref(v___x_2511_);
return v___x_2570_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___boxed(lean_object** _args){
lean_object* v___x_2592_ = _args[0];
lean_object* v_snd_2593_ = _args[1];
lean_object* v_fst_2594_ = _args[2];
lean_object* v_fst_2595_ = _args[3];
lean_object* v___x_2596_ = _args[4];
lean_object* v_range_2597_ = _args[5];
lean_object* v_b_2598_ = _args[6];
lean_object* v_i_2599_ = _args[7];
lean_object* v___y_2600_ = _args[8];
lean_object* v___y_2601_ = _args[9];
lean_object* v___y_2602_ = _args[10];
lean_object* v___y_2603_ = _args[11];
lean_object* v___y_2604_ = _args[12];
lean_object* v___y_2605_ = _args[13];
lean_object* v___y_2606_ = _args[14];
lean_object* v___y_2607_ = _args[15];
lean_object* v___y_2608_ = _args[16];
lean_object* v___y_2609_ = _args[17];
lean_object* v___y_2610_ = _args[18];
lean_object* v___y_2611_ = _args[19];
_start:
{
lean_object* v_res_2612_; 
v_res_2612_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg(v___x_2592_, v_snd_2593_, v_fst_2594_, v_fst_2595_, v___x_2596_, v_range_2597_, v_b_2598_, v_i_2599_, v___y_2600_, v___y_2601_, v___y_2602_, v___y_2603_, v___y_2604_, v___y_2605_, v___y_2606_, v___y_2607_, v___y_2608_, v___y_2609_, v___y_2610_);
lean_dec(v___y_2610_);
lean_dec_ref(v___y_2609_);
lean_dec(v___y_2608_);
lean_dec_ref(v___y_2607_);
lean_dec(v___y_2606_);
lean_dec_ref(v___y_2605_);
lean_dec(v___y_2604_);
lean_dec_ref(v___y_2603_);
lean_dec(v___y_2602_);
lean_dec(v___y_2601_);
lean_dec_ref(v___y_2600_);
lean_dec_ref(v_range_2597_);
lean_dec_ref(v___x_2596_);
return v_res_2612_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars(lean_object* v_a_2613_, lean_object* v_a_2614_, lean_object* v_a_2615_, lean_object* v_a_2616_, lean_object* v_a_2617_, lean_object* v_a_2618_, lean_object* v_a_2619_, lean_object* v_a_2620_, lean_object* v_a_2621_, lean_object* v_a_2622_, lean_object* v_a_2623_){
_start:
{
lean_object* v___x_2625_; 
v___x_2625_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v_a_2613_, v_a_2614_, v_a_2615_, v_a_2616_, v_a_2617_, v_a_2618_, v_a_2619_, v_a_2620_, v_a_2621_, v_a_2622_, v_a_2623_);
if (lean_obj_tag(v___x_2625_) == 0)
{
lean_object* v_a_2626_; lean_object* v___x_2628_; uint8_t v_isShared_2629_; uint8_t v_isSharedCheck_2655_; 
v_a_2626_ = lean_ctor_get(v___x_2625_, 0);
v_isSharedCheck_2655_ = !lean_is_exclusive(v___x_2625_);
if (v_isSharedCheck_2655_ == 0)
{
v___x_2628_ = v___x_2625_;
v_isShared_2629_ = v_isSharedCheck_2655_;
goto v_resetjp_2627_;
}
else
{
lean_inc(v_a_2626_);
lean_dec(v___x_2625_);
v___x_2628_ = lean_box(0);
v_isShared_2629_ = v_isSharedCheck_2655_;
goto v_resetjp_2627_;
}
v_resetjp_2627_:
{
lean_object* v_powIdentityInst_x3f_2630_; 
v_powIdentityInst_x3f_2630_ = lean_ctor_get(v_a_2626_, 7);
if (lean_obj_tag(v_powIdentityInst_x3f_2630_) == 1)
{
lean_object* v_val_2631_; lean_object* v_snd_2632_; lean_object* v_toRing_2633_; lean_object* v_vars_2634_; lean_object* v_powIdentityVarCount_2635_; lean_object* v_fst_2636_; lean_object* v_fst_2637_; lean_object* v_snd_2638_; lean_object* v_size_2639_; uint8_t v___x_2640_; 
v_val_2631_ = lean_ctor_get(v_powIdentityInst_x3f_2630_, 0);
lean_inc(v_val_2631_);
v_snd_2632_ = lean_ctor_get(v_val_2631_, 1);
lean_inc(v_snd_2632_);
v_toRing_2633_ = lean_ctor_get(v_a_2626_, 0);
lean_inc_ref(v_toRing_2633_);
v_vars_2634_ = lean_ctor_get(v_toRing_2633_, 14);
lean_inc_ref(v_vars_2634_);
v_powIdentityVarCount_2635_ = lean_ctor_get(v_a_2626_, 15);
lean_inc(v_powIdentityVarCount_2635_);
lean_dec(v_a_2626_);
v_fst_2636_ = lean_ctor_get(v_val_2631_, 0);
lean_inc(v_fst_2636_);
lean_dec(v_val_2631_);
v_fst_2637_ = lean_ctor_get(v_snd_2632_, 0);
lean_inc(v_fst_2637_);
v_snd_2638_ = lean_ctor_get(v_snd_2632_, 1);
lean_inc(v_snd_2638_);
lean_dec(v_snd_2632_);
v_size_2639_ = lean_ctor_get(v_vars_2634_, 2);
lean_inc(v_size_2639_);
v___x_2640_ = lean_nat_dec_le(v_size_2639_, v_powIdentityVarCount_2635_);
if (v___x_2640_ == 0)
{
lean_object* v___x_2641_; lean_object* v___x_2642_; lean_object* v___x_2643_; lean_object* v___x_2644_; 
lean_del_object(v___x_2628_);
v___x_2641_ = lean_unsigned_to_nat(1u);
lean_inc(v_size_2639_);
lean_inc(v_powIdentityVarCount_2635_);
v___x_2642_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2642_, 0, v_powIdentityVarCount_2635_);
lean_ctor_set(v___x_2642_, 1, v_size_2639_);
lean_ctor_set(v___x_2642_, 2, v___x_2641_);
v___x_2643_ = lean_box(0);
v___x_2644_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg(v_toRing_2633_, v_snd_2638_, v_fst_2637_, v_fst_2636_, v_vars_2634_, v___x_2642_, v___x_2643_, v_powIdentityVarCount_2635_, v_a_2613_, v_a_2614_, v_a_2615_, v_a_2616_, v_a_2617_, v_a_2618_, v_a_2619_, v_a_2620_, v_a_2621_, v_a_2622_, v_a_2623_);
lean_dec_ref_known(v___x_2642_, 3);
lean_dec_ref(v_vars_2634_);
if (lean_obj_tag(v___x_2644_) == 0)
{
lean_object* v___f_2645_; lean_object* v___x_2646_; 
lean_dec_ref_known(v___x_2644_, 1);
v___f_2645_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars___lam__0), 2, 1);
lean_closure_set(v___f_2645_, 0, v_size_2639_);
v___x_2646_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(v___f_2645_, v_a_2613_, v_a_2614_);
return v___x_2646_;
}
else
{
lean_dec(v_size_2639_);
return v___x_2644_;
}
}
else
{
lean_object* v___x_2647_; lean_object* v___x_2649_; 
lean_dec(v_size_2639_);
lean_dec(v_snd_2638_);
lean_dec(v_fst_2637_);
lean_dec(v_fst_2636_);
lean_dec(v_powIdentityVarCount_2635_);
lean_dec_ref(v_vars_2634_);
lean_dec_ref(v_toRing_2633_);
v___x_2647_ = lean_box(0);
if (v_isShared_2629_ == 0)
{
lean_ctor_set(v___x_2628_, 0, v___x_2647_);
v___x_2649_ = v___x_2628_;
goto v_reusejp_2648_;
}
else
{
lean_object* v_reuseFailAlloc_2650_; 
v_reuseFailAlloc_2650_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2650_, 0, v___x_2647_);
v___x_2649_ = v_reuseFailAlloc_2650_;
goto v_reusejp_2648_;
}
v_reusejp_2648_:
{
return v___x_2649_;
}
}
}
else
{
lean_object* v___x_2651_; lean_object* v___x_2653_; 
lean_dec(v_a_2626_);
v___x_2651_ = lean_box(0);
if (v_isShared_2629_ == 0)
{
lean_ctor_set(v___x_2628_, 0, v___x_2651_);
v___x_2653_ = v___x_2628_;
goto v_reusejp_2652_;
}
else
{
lean_object* v_reuseFailAlloc_2654_; 
v_reuseFailAlloc_2654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2654_, 0, v___x_2651_);
v___x_2653_ = v_reuseFailAlloc_2654_;
goto v_reusejp_2652_;
}
v_reusejp_2652_:
{
return v___x_2653_;
}
}
}
}
else
{
lean_object* v_a_2656_; lean_object* v___x_2658_; uint8_t v_isShared_2659_; uint8_t v_isSharedCheck_2663_; 
v_a_2656_ = lean_ctor_get(v___x_2625_, 0);
v_isSharedCheck_2663_ = !lean_is_exclusive(v___x_2625_);
if (v_isSharedCheck_2663_ == 0)
{
v___x_2658_ = v___x_2625_;
v_isShared_2659_ = v_isSharedCheck_2663_;
goto v_resetjp_2657_;
}
else
{
lean_inc(v_a_2656_);
lean_dec(v___x_2625_);
v___x_2658_ = lean_box(0);
v_isShared_2659_ = v_isSharedCheck_2663_;
goto v_resetjp_2657_;
}
v_resetjp_2657_:
{
lean_object* v___x_2661_; 
if (v_isShared_2659_ == 0)
{
v___x_2661_ = v___x_2658_;
goto v_reusejp_2660_;
}
else
{
lean_object* v_reuseFailAlloc_2662_; 
v_reuseFailAlloc_2662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2662_, 0, v_a_2656_);
v___x_2661_ = v_reuseFailAlloc_2662_;
goto v_reusejp_2660_;
}
v_reusejp_2660_:
{
return v___x_2661_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars___boxed(lean_object* v_a_2664_, lean_object* v_a_2665_, lean_object* v_a_2666_, lean_object* v_a_2667_, lean_object* v_a_2668_, lean_object* v_a_2669_, lean_object* v_a_2670_, lean_object* v_a_2671_, lean_object* v_a_2672_, lean_object* v_a_2673_, lean_object* v_a_2674_, lean_object* v_a_2675_){
_start:
{
lean_object* v_res_2676_; 
v_res_2676_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars(v_a_2664_, v_a_2665_, v_a_2666_, v_a_2667_, v_a_2668_, v_a_2669_, v_a_2670_, v_a_2671_, v_a_2672_, v_a_2673_, v_a_2674_);
lean_dec(v_a_2674_);
lean_dec_ref(v_a_2673_);
lean_dec(v_a_2672_);
lean_dec_ref(v_a_2671_);
lean_dec(v_a_2670_);
lean_dec_ref(v_a_2669_);
lean_dec(v_a_2668_);
lean_dec_ref(v_a_2667_);
lean_dec(v_a_2666_);
lean_dec(v_a_2665_);
lean_dec_ref(v_a_2664_);
return v_res_2676_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0(lean_object* v_cls_2677_, lean_object* v_msg_2678_, lean_object* v___y_2679_, lean_object* v___y_2680_, lean_object* v___y_2681_, lean_object* v___y_2682_, lean_object* v___y_2683_, lean_object* v___y_2684_, lean_object* v___y_2685_, lean_object* v___y_2686_, lean_object* v___y_2687_, lean_object* v___y_2688_, lean_object* v___y_2689_){
_start:
{
lean_object* v___x_2691_; 
v___x_2691_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg(v_cls_2677_, v_msg_2678_, v___y_2686_, v___y_2687_, v___y_2688_, v___y_2689_);
return v___x_2691_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___boxed(lean_object* v_cls_2692_, lean_object* v_msg_2693_, lean_object* v___y_2694_, lean_object* v___y_2695_, lean_object* v___y_2696_, lean_object* v___y_2697_, lean_object* v___y_2698_, lean_object* v___y_2699_, lean_object* v___y_2700_, lean_object* v___y_2701_, lean_object* v___y_2702_, lean_object* v___y_2703_, lean_object* v___y_2704_, lean_object* v___y_2705_){
_start:
{
lean_object* v_res_2706_; 
v_res_2706_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0(v_cls_2692_, v_msg_2693_, v___y_2694_, v___y_2695_, v___y_2696_, v___y_2697_, v___y_2698_, v___y_2699_, v___y_2700_, v___y_2701_, v___y_2702_, v___y_2703_, v___y_2704_);
lean_dec(v___y_2704_);
lean_dec_ref(v___y_2703_);
lean_dec(v___y_2702_);
lean_dec_ref(v___y_2701_);
lean_dec(v___y_2700_);
lean_dec_ref(v___y_2699_);
lean_dec(v___y_2698_);
lean_dec_ref(v___y_2697_);
lean_dec(v___y_2696_);
lean_dec(v___y_2695_);
lean_dec_ref(v___y_2694_);
return v_res_2706_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1(lean_object* v___x_2707_, lean_object* v_snd_2708_, lean_object* v_fst_2709_, lean_object* v_fst_2710_, lean_object* v___x_2711_, lean_object* v_range_2712_, lean_object* v_b_2713_, lean_object* v_i_2714_, lean_object* v_hs_2715_, lean_object* v_hl_2716_, lean_object* v___y_2717_, lean_object* v___y_2718_, lean_object* v___y_2719_, lean_object* v___y_2720_, lean_object* v___y_2721_, lean_object* v___y_2722_, lean_object* v___y_2723_, lean_object* v___y_2724_, lean_object* v___y_2725_, lean_object* v___y_2726_, lean_object* v___y_2727_){
_start:
{
lean_object* v___x_2729_; 
v___x_2729_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg(v___x_2707_, v_snd_2708_, v_fst_2709_, v_fst_2710_, v___x_2711_, v_range_2712_, v_b_2713_, v_i_2714_, v___y_2717_, v___y_2718_, v___y_2719_, v___y_2720_, v___y_2721_, v___y_2722_, v___y_2723_, v___y_2724_, v___y_2725_, v___y_2726_, v___y_2727_);
return v___x_2729_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___boxed(lean_object** _args){
lean_object* v___x_2730_ = _args[0];
lean_object* v_snd_2731_ = _args[1];
lean_object* v_fst_2732_ = _args[2];
lean_object* v_fst_2733_ = _args[3];
lean_object* v___x_2734_ = _args[4];
lean_object* v_range_2735_ = _args[5];
lean_object* v_b_2736_ = _args[6];
lean_object* v_i_2737_ = _args[7];
lean_object* v_hs_2738_ = _args[8];
lean_object* v_hl_2739_ = _args[9];
lean_object* v___y_2740_ = _args[10];
lean_object* v___y_2741_ = _args[11];
lean_object* v___y_2742_ = _args[12];
lean_object* v___y_2743_ = _args[13];
lean_object* v___y_2744_ = _args[14];
lean_object* v___y_2745_ = _args[15];
lean_object* v___y_2746_ = _args[16];
lean_object* v___y_2747_ = _args[17];
lean_object* v___y_2748_ = _args[18];
lean_object* v___y_2749_ = _args[19];
lean_object* v___y_2750_ = _args[20];
lean_object* v___y_2751_ = _args[21];
_start:
{
lean_object* v_res_2752_; 
v_res_2752_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1(v___x_2730_, v_snd_2731_, v_fst_2732_, v_fst_2733_, v___x_2734_, v_range_2735_, v_b_2736_, v_i_2737_, v_hs_2738_, v_hl_2739_, v___y_2740_, v___y_2741_, v___y_2742_, v___y_2743_, v___y_2744_, v___y_2745_, v___y_2746_, v___y_2747_, v___y_2748_, v___y_2749_, v___y_2750_);
lean_dec(v___y_2750_);
lean_dec_ref(v___y_2749_);
lean_dec(v___y_2748_);
lean_dec_ref(v___y_2747_);
lean_dec(v___y_2746_);
lean_dec_ref(v___y_2745_);
lean_dec(v___y_2744_);
lean_dec_ref(v___y_2743_);
lean_dec(v___y_2742_);
lean_dec(v___y_2741_);
lean_dec_ref(v___y_2740_);
lean_dec_ref(v_range_2735_);
lean_dec_ref(v___x_2734_);
return v_res_2752_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeInv(lean_object* v_e_2753_, lean_object* v_a_2754_, lean_object* v_a_2755_, lean_object* v_a_2756_, lean_object* v_a_2757_, lean_object* v_a_2758_, lean_object* v_a_2759_, lean_object* v_a_2760_, lean_object* v_a_2761_, lean_object* v_a_2762_, lean_object* v_a_2763_){
_start:
{
lean_object* v___x_2765_; 
lean_inc_ref(v_e_2753_);
v___x_2765_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_2753_, v_a_2761_);
if (lean_obj_tag(v___x_2765_) == 0)
{
lean_object* v_a_2766_; lean_object* v___x_2768_; uint8_t v_isShared_2769_; uint8_t v_isSharedCheck_2827_; 
v_a_2766_ = lean_ctor_get(v___x_2765_, 0);
v_isSharedCheck_2827_ = !lean_is_exclusive(v___x_2765_);
if (v_isSharedCheck_2827_ == 0)
{
v___x_2768_ = v___x_2765_;
v_isShared_2769_ = v_isSharedCheck_2827_;
goto v_resetjp_2767_;
}
else
{
lean_inc(v_a_2766_);
lean_dec(v___x_2765_);
v___x_2768_ = lean_box(0);
v_isShared_2769_ = v_isSharedCheck_2827_;
goto v_resetjp_2767_;
}
v_resetjp_2767_:
{
lean_object* v___x_2776_; uint8_t v___x_2777_; 
v___x_2776_ = l_Lean_Expr_cleanupAnnotations(v_a_2766_);
v___x_2777_ = l_Lean_Expr_isApp(v___x_2776_);
if (v___x_2777_ == 0)
{
lean_dec_ref(v___x_2776_);
lean_dec_ref(v_e_2753_);
goto v___jp_2770_;
}
else
{
lean_object* v_arg_2778_; lean_object* v___x_2779_; uint8_t v___x_2780_; 
v_arg_2778_ = lean_ctor_get(v___x_2776_, 1);
lean_inc_ref(v_arg_2778_);
v___x_2779_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2776_);
v___x_2780_ = l_Lean_Expr_isApp(v___x_2779_);
if (v___x_2780_ == 0)
{
lean_dec_ref(v___x_2779_);
lean_dec_ref(v_arg_2778_);
lean_dec_ref(v_e_2753_);
goto v___jp_2770_;
}
else
{
lean_object* v_arg_2781_; lean_object* v___x_2782_; uint8_t v___x_2783_; 
v_arg_2781_ = lean_ctor_get(v___x_2779_, 1);
lean_inc_ref(v_arg_2781_);
v___x_2782_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2779_);
v___x_2783_ = l_Lean_Expr_isApp(v___x_2782_);
if (v___x_2783_ == 0)
{
lean_dec_ref(v___x_2782_);
lean_dec_ref(v_arg_2781_);
lean_dec_ref(v_arg_2778_);
lean_dec_ref(v_e_2753_);
goto v___jp_2770_;
}
else
{
lean_object* v_arg_2784_; lean_object* v___x_2785_; lean_object* v___x_2786_; uint8_t v___x_2787_; 
v_arg_2784_ = lean_ctor_get(v___x_2782_, 1);
lean_inc_ref(v_arg_2784_);
v___x_2785_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2782_);
v___x_2786_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___closed__6));
v___x_2787_ = l_Lean_Expr_isConstOf(v___x_2785_, v___x_2786_);
lean_dec_ref(v___x_2785_);
if (v___x_2787_ == 0)
{
lean_dec_ref(v_arg_2784_);
lean_dec_ref(v_arg_2781_);
lean_dec_ref(v_arg_2778_);
lean_dec_ref(v_e_2753_);
goto v___jp_2770_;
}
else
{
lean_object* v___x_2788_; 
lean_del_object(v___x_2768_);
v___x_2788_ = l_Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f(v_arg_2784_, v_a_2754_, v_a_2755_, v_a_2756_, v_a_2757_, v_a_2758_, v_a_2759_, v_a_2760_, v_a_2761_, v_a_2762_, v_a_2763_);
if (lean_obj_tag(v___x_2788_) == 0)
{
lean_object* v_a_2789_; lean_object* v___x_2791_; uint8_t v_isShared_2792_; uint8_t v_isSharedCheck_2818_; 
v_a_2789_ = lean_ctor_get(v___x_2788_, 0);
v_isSharedCheck_2818_ = !lean_is_exclusive(v___x_2788_);
if (v_isSharedCheck_2818_ == 0)
{
v___x_2791_ = v___x_2788_;
v_isShared_2792_ = v_isSharedCheck_2818_;
goto v_resetjp_2790_;
}
else
{
lean_inc(v_a_2789_);
lean_dec(v___x_2788_);
v___x_2791_ = lean_box(0);
v_isShared_2792_ = v_isSharedCheck_2818_;
goto v_resetjp_2790_;
}
v_resetjp_2790_:
{
if (lean_obj_tag(v_a_2789_) == 1)
{
lean_object* v_val_2793_; uint8_t v___x_2794_; lean_object* v___x_2795_; lean_object* v___x_2796_; 
lean_del_object(v___x_2791_);
v_val_2793_ = lean_ctor_get(v_a_2789_, 0);
lean_inc(v_val_2793_);
lean_dec_ref_known(v_a_2789_, 1);
v___x_2794_ = 0;
v___x_2795_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2795_, 0, v_val_2793_);
lean_ctor_set_uint8(v___x_2795_, sizeof(void*)*1, v___x_2794_);
v___x_2796_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv(v_e_2753_, v_arg_2781_, v_arg_2778_, v___x_2795_, v_a_2754_, v_a_2755_, v_a_2756_, v_a_2757_, v_a_2758_, v_a_2759_, v_a_2760_, v_a_2761_, v_a_2762_, v_a_2763_);
lean_dec_ref_known(v___x_2795_, 1);
lean_dec_ref(v_arg_2781_);
if (lean_obj_tag(v___x_2796_) == 0)
{
lean_object* v___x_2798_; uint8_t v_isShared_2799_; uint8_t v_isSharedCheck_2804_; 
v_isSharedCheck_2804_ = !lean_is_exclusive(v___x_2796_);
if (v_isSharedCheck_2804_ == 0)
{
lean_object* v_unused_2805_; 
v_unused_2805_ = lean_ctor_get(v___x_2796_, 0);
lean_dec(v_unused_2805_);
v___x_2798_ = v___x_2796_;
v_isShared_2799_ = v_isSharedCheck_2804_;
goto v_resetjp_2797_;
}
else
{
lean_dec(v___x_2796_);
v___x_2798_ = lean_box(0);
v_isShared_2799_ = v_isSharedCheck_2804_;
goto v_resetjp_2797_;
}
v_resetjp_2797_:
{
lean_object* v___x_2800_; lean_object* v___x_2802_; 
v___x_2800_ = lean_box(v___x_2787_);
if (v_isShared_2799_ == 0)
{
lean_ctor_set(v___x_2798_, 0, v___x_2800_);
v___x_2802_ = v___x_2798_;
goto v_reusejp_2801_;
}
else
{
lean_object* v_reuseFailAlloc_2803_; 
v_reuseFailAlloc_2803_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2803_, 0, v___x_2800_);
v___x_2802_ = v_reuseFailAlloc_2803_;
goto v_reusejp_2801_;
}
v_reusejp_2801_:
{
return v___x_2802_;
}
}
}
else
{
lean_object* v_a_2806_; lean_object* v___x_2808_; uint8_t v_isShared_2809_; uint8_t v_isSharedCheck_2813_; 
v_a_2806_ = lean_ctor_get(v___x_2796_, 0);
v_isSharedCheck_2813_ = !lean_is_exclusive(v___x_2796_);
if (v_isSharedCheck_2813_ == 0)
{
v___x_2808_ = v___x_2796_;
v_isShared_2809_ = v_isSharedCheck_2813_;
goto v_resetjp_2807_;
}
else
{
lean_inc(v_a_2806_);
lean_dec(v___x_2796_);
v___x_2808_ = lean_box(0);
v_isShared_2809_ = v_isSharedCheck_2813_;
goto v_resetjp_2807_;
}
v_resetjp_2807_:
{
lean_object* v___x_2811_; 
if (v_isShared_2809_ == 0)
{
v___x_2811_ = v___x_2808_;
goto v_reusejp_2810_;
}
else
{
lean_object* v_reuseFailAlloc_2812_; 
v_reuseFailAlloc_2812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2812_, 0, v_a_2806_);
v___x_2811_ = v_reuseFailAlloc_2812_;
goto v_reusejp_2810_;
}
v_reusejp_2810_:
{
return v___x_2811_;
}
}
}
}
else
{
lean_object* v___x_2814_; lean_object* v___x_2816_; 
lean_dec(v_a_2789_);
lean_dec_ref(v_arg_2781_);
lean_dec_ref(v_arg_2778_);
lean_dec_ref(v_e_2753_);
v___x_2814_ = lean_box(v___x_2787_);
if (v_isShared_2792_ == 0)
{
lean_ctor_set(v___x_2791_, 0, v___x_2814_);
v___x_2816_ = v___x_2791_;
goto v_reusejp_2815_;
}
else
{
lean_object* v_reuseFailAlloc_2817_; 
v_reuseFailAlloc_2817_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2817_, 0, v___x_2814_);
v___x_2816_ = v_reuseFailAlloc_2817_;
goto v_reusejp_2815_;
}
v_reusejp_2815_:
{
return v___x_2816_;
}
}
}
}
else
{
lean_object* v_a_2819_; lean_object* v___x_2821_; uint8_t v_isShared_2822_; uint8_t v_isSharedCheck_2826_; 
lean_dec_ref(v_arg_2781_);
lean_dec_ref(v_arg_2778_);
lean_dec_ref(v_e_2753_);
v_a_2819_ = lean_ctor_get(v___x_2788_, 0);
v_isSharedCheck_2826_ = !lean_is_exclusive(v___x_2788_);
if (v_isSharedCheck_2826_ == 0)
{
v___x_2821_ = v___x_2788_;
v_isShared_2822_ = v_isSharedCheck_2826_;
goto v_resetjp_2820_;
}
else
{
lean_inc(v_a_2819_);
lean_dec(v___x_2788_);
v___x_2821_ = lean_box(0);
v_isShared_2822_ = v_isSharedCheck_2826_;
goto v_resetjp_2820_;
}
v_resetjp_2820_:
{
lean_object* v___x_2824_; 
if (v_isShared_2822_ == 0)
{
v___x_2824_ = v___x_2821_;
goto v_reusejp_2823_;
}
else
{
lean_object* v_reuseFailAlloc_2825_; 
v_reuseFailAlloc_2825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2825_, 0, v_a_2819_);
v___x_2824_ = v_reuseFailAlloc_2825_;
goto v_reusejp_2823_;
}
v_reusejp_2823_:
{
return v___x_2824_;
}
}
}
}
}
}
}
v___jp_2770_:
{
uint8_t v___x_2771_; lean_object* v___x_2772_; lean_object* v___x_2774_; 
v___x_2771_ = 0;
v___x_2772_ = lean_box(v___x_2771_);
if (v_isShared_2769_ == 0)
{
lean_ctor_set(v___x_2768_, 0, v___x_2772_);
v___x_2774_ = v___x_2768_;
goto v_reusejp_2773_;
}
else
{
lean_object* v_reuseFailAlloc_2775_; 
v_reuseFailAlloc_2775_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2775_, 0, v___x_2772_);
v___x_2774_ = v_reuseFailAlloc_2775_;
goto v_reusejp_2773_;
}
v_reusejp_2773_:
{
return v___x_2774_;
}
}
}
}
else
{
lean_object* v_a_2828_; lean_object* v___x_2830_; uint8_t v_isShared_2831_; uint8_t v_isSharedCheck_2835_; 
lean_dec_ref(v_e_2753_);
v_a_2828_ = lean_ctor_get(v___x_2765_, 0);
v_isSharedCheck_2835_ = !lean_is_exclusive(v___x_2765_);
if (v_isSharedCheck_2835_ == 0)
{
v___x_2830_ = v___x_2765_;
v_isShared_2831_ = v_isSharedCheck_2835_;
goto v_resetjp_2829_;
}
else
{
lean_inc(v_a_2828_);
lean_dec(v___x_2765_);
v___x_2830_ = lean_box(0);
v_isShared_2831_ = v_isSharedCheck_2835_;
goto v_resetjp_2829_;
}
v_resetjp_2829_:
{
lean_object* v___x_2833_; 
if (v_isShared_2831_ == 0)
{
v___x_2833_ = v___x_2830_;
goto v_reusejp_2832_;
}
else
{
lean_object* v_reuseFailAlloc_2834_; 
v_reuseFailAlloc_2834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2834_, 0, v_a_2828_);
v___x_2833_ = v_reuseFailAlloc_2834_;
goto v_reusejp_2832_;
}
v_reusejp_2832_:
{
return v___x_2833_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeInv___boxed(lean_object* v_e_2836_, lean_object* v_a_2837_, lean_object* v_a_2838_, lean_object* v_a_2839_, lean_object* v_a_2840_, lean_object* v_a_2841_, lean_object* v_a_2842_, lean_object* v_a_2843_, lean_object* v_a_2844_, lean_object* v_a_2845_, lean_object* v_a_2846_, lean_object* v_a_2847_){
_start:
{
lean_object* v_res_2848_; 
v_res_2848_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeInv(v_e_2836_, v_a_2837_, v_a_2838_, v_a_2839_, v_a_2840_, v_a_2841_, v_a_2842_, v_a_2843_, v_a_2844_, v_a_2845_, v_a_2846_);
lean_dec(v_a_2846_);
lean_dec_ref(v_a_2845_);
lean_dec(v_a_2844_);
lean_dec_ref(v_a_2843_);
lean_dec(v_a_2842_);
lean_dec_ref(v_a_2841_);
lean_dec(v_a_2840_);
lean_dec_ref(v_a_2839_);
lean_dec(v_a_2838_);
lean_dec(v_a_2837_);
return v_res_2848_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0_spec__1_spec__5___redArg(lean_object* v_x_2849_, lean_object* v_x_2850_, lean_object* v_x_2851_, lean_object* v_x_2852_){
_start:
{
lean_object* v_ks_2853_; lean_object* v_vs_2854_; lean_object* v___x_2856_; uint8_t v_isShared_2857_; uint8_t v_isSharedCheck_2880_; 
v_ks_2853_ = lean_ctor_get(v_x_2849_, 0);
v_vs_2854_ = lean_ctor_get(v_x_2849_, 1);
v_isSharedCheck_2880_ = !lean_is_exclusive(v_x_2849_);
if (v_isSharedCheck_2880_ == 0)
{
v___x_2856_ = v_x_2849_;
v_isShared_2857_ = v_isSharedCheck_2880_;
goto v_resetjp_2855_;
}
else
{
lean_inc(v_vs_2854_);
lean_inc(v_ks_2853_);
lean_dec(v_x_2849_);
v___x_2856_ = lean_box(0);
v_isShared_2857_ = v_isSharedCheck_2880_;
goto v_resetjp_2855_;
}
v_resetjp_2855_:
{
lean_object* v___x_2858_; uint8_t v___x_2859_; 
v___x_2858_ = lean_array_get_size(v_ks_2853_);
v___x_2859_ = lean_nat_dec_lt(v_x_2850_, v___x_2858_);
if (v___x_2859_ == 0)
{
lean_object* v___x_2860_; lean_object* v___x_2861_; lean_object* v___x_2863_; 
lean_dec(v_x_2850_);
v___x_2860_ = lean_array_push(v_ks_2853_, v_x_2851_);
v___x_2861_ = lean_array_push(v_vs_2854_, v_x_2852_);
if (v_isShared_2857_ == 0)
{
lean_ctor_set(v___x_2856_, 1, v___x_2861_);
lean_ctor_set(v___x_2856_, 0, v___x_2860_);
v___x_2863_ = v___x_2856_;
goto v_reusejp_2862_;
}
else
{
lean_object* v_reuseFailAlloc_2864_; 
v_reuseFailAlloc_2864_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2864_, 0, v___x_2860_);
lean_ctor_set(v_reuseFailAlloc_2864_, 1, v___x_2861_);
v___x_2863_ = v_reuseFailAlloc_2864_;
goto v_reusejp_2862_;
}
v_reusejp_2862_:
{
return v___x_2863_;
}
}
else
{
lean_object* v_k_x27_2865_; size_t v___x_2866_; size_t v___x_2867_; uint8_t v___x_2868_; 
v_k_x27_2865_ = lean_array_fget_borrowed(v_ks_2853_, v_x_2850_);
v___x_2866_ = lean_ptr_addr(v_x_2851_);
v___x_2867_ = lean_ptr_addr(v_k_x27_2865_);
v___x_2868_ = lean_usize_dec_eq(v___x_2866_, v___x_2867_);
if (v___x_2868_ == 0)
{
lean_object* v___x_2870_; 
if (v_isShared_2857_ == 0)
{
v___x_2870_ = v___x_2856_;
goto v_reusejp_2869_;
}
else
{
lean_object* v_reuseFailAlloc_2874_; 
v_reuseFailAlloc_2874_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2874_, 0, v_ks_2853_);
lean_ctor_set(v_reuseFailAlloc_2874_, 1, v_vs_2854_);
v___x_2870_ = v_reuseFailAlloc_2874_;
goto v_reusejp_2869_;
}
v_reusejp_2869_:
{
lean_object* v___x_2871_; lean_object* v___x_2872_; 
v___x_2871_ = lean_unsigned_to_nat(1u);
v___x_2872_ = lean_nat_add(v_x_2850_, v___x_2871_);
lean_dec(v_x_2850_);
v_x_2849_ = v___x_2870_;
v_x_2850_ = v___x_2872_;
goto _start;
}
}
else
{
lean_object* v___x_2875_; lean_object* v___x_2876_; lean_object* v___x_2878_; 
v___x_2875_ = lean_array_fset(v_ks_2853_, v_x_2850_, v_x_2851_);
v___x_2876_ = lean_array_fset(v_vs_2854_, v_x_2850_, v_x_2852_);
lean_dec(v_x_2850_);
if (v_isShared_2857_ == 0)
{
lean_ctor_set(v___x_2856_, 1, v___x_2876_);
lean_ctor_set(v___x_2856_, 0, v___x_2875_);
v___x_2878_ = v___x_2856_;
goto v_reusejp_2877_;
}
else
{
lean_object* v_reuseFailAlloc_2879_; 
v_reuseFailAlloc_2879_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2879_, 0, v___x_2875_);
lean_ctor_set(v_reuseFailAlloc_2879_, 1, v___x_2876_);
v___x_2878_ = v_reuseFailAlloc_2879_;
goto v_reusejp_2877_;
}
v_reusejp_2877_:
{
return v___x_2878_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0_spec__1___redArg(lean_object* v_n_2881_, lean_object* v_k_2882_, lean_object* v_v_2883_){
_start:
{
lean_object* v___x_2884_; lean_object* v___x_2885_; 
v___x_2884_ = lean_unsigned_to_nat(0u);
v___x_2885_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0_spec__1_spec__5___redArg(v_n_2881_, v___x_2884_, v_k_2882_, v_v_2883_);
return v___x_2885_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0___redArg(lean_object* v_x_2886_, size_t v_x_2887_, size_t v_x_2888_, lean_object* v_x_2889_, lean_object* v_x_2890_){
_start:
{
if (lean_obj_tag(v_x_2886_) == 0)
{
lean_object* v_es_2891_; size_t v___x_2892_; size_t v___x_2893_; lean_object* v_j_2894_; lean_object* v___x_2895_; uint8_t v___x_2896_; 
v_es_2891_ = lean_ctor_get(v_x_2886_, 0);
v___x_2892_ = ((size_t)31ULL);
v___x_2893_ = lean_usize_land(v_x_2887_, v___x_2892_);
v_j_2894_ = lean_usize_to_nat(v___x_2893_);
v___x_2895_ = lean_array_get_size(v_es_2891_);
v___x_2896_ = lean_nat_dec_lt(v_j_2894_, v___x_2895_);
if (v___x_2896_ == 0)
{
lean_dec(v_j_2894_);
lean_dec(v_x_2890_);
lean_dec_ref(v_x_2889_);
return v_x_2886_;
}
else
{
lean_object* v___x_2898_; uint8_t v_isShared_2899_; uint8_t v_isSharedCheck_2937_; 
lean_inc_ref(v_es_2891_);
v_isSharedCheck_2937_ = !lean_is_exclusive(v_x_2886_);
if (v_isSharedCheck_2937_ == 0)
{
lean_object* v_unused_2938_; 
v_unused_2938_ = lean_ctor_get(v_x_2886_, 0);
lean_dec(v_unused_2938_);
v___x_2898_ = v_x_2886_;
v_isShared_2899_ = v_isSharedCheck_2937_;
goto v_resetjp_2897_;
}
else
{
lean_dec(v_x_2886_);
v___x_2898_ = lean_box(0);
v_isShared_2899_ = v_isSharedCheck_2937_;
goto v_resetjp_2897_;
}
v_resetjp_2897_:
{
lean_object* v_v_2900_; lean_object* v___x_2901_; lean_object* v_xs_x27_2902_; lean_object* v___y_2904_; 
v_v_2900_ = lean_array_fget(v_es_2891_, v_j_2894_);
v___x_2901_ = lean_box(0);
v_xs_x27_2902_ = lean_array_fset(v_es_2891_, v_j_2894_, v___x_2901_);
switch(lean_obj_tag(v_v_2900_))
{
case 0:
{
lean_object* v_key_2909_; lean_object* v_val_2910_; lean_object* v___x_2912_; uint8_t v_isShared_2913_; uint8_t v_isSharedCheck_2922_; 
v_key_2909_ = lean_ctor_get(v_v_2900_, 0);
v_val_2910_ = lean_ctor_get(v_v_2900_, 1);
v_isSharedCheck_2922_ = !lean_is_exclusive(v_v_2900_);
if (v_isSharedCheck_2922_ == 0)
{
v___x_2912_ = v_v_2900_;
v_isShared_2913_ = v_isSharedCheck_2922_;
goto v_resetjp_2911_;
}
else
{
lean_inc(v_val_2910_);
lean_inc(v_key_2909_);
lean_dec(v_v_2900_);
v___x_2912_ = lean_box(0);
v_isShared_2913_ = v_isSharedCheck_2922_;
goto v_resetjp_2911_;
}
v_resetjp_2911_:
{
size_t v___x_2914_; size_t v___x_2915_; uint8_t v___x_2916_; 
v___x_2914_ = lean_ptr_addr(v_x_2889_);
v___x_2915_ = lean_ptr_addr(v_key_2909_);
v___x_2916_ = lean_usize_dec_eq(v___x_2914_, v___x_2915_);
if (v___x_2916_ == 0)
{
lean_object* v___x_2917_; lean_object* v___x_2918_; 
lean_del_object(v___x_2912_);
v___x_2917_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_2909_, v_val_2910_, v_x_2889_, v_x_2890_);
v___x_2918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2918_, 0, v___x_2917_);
v___y_2904_ = v___x_2918_;
goto v___jp_2903_;
}
else
{
lean_object* v___x_2920_; 
lean_dec(v_val_2910_);
lean_dec(v_key_2909_);
if (v_isShared_2913_ == 0)
{
lean_ctor_set(v___x_2912_, 1, v_x_2890_);
lean_ctor_set(v___x_2912_, 0, v_x_2889_);
v___x_2920_ = v___x_2912_;
goto v_reusejp_2919_;
}
else
{
lean_object* v_reuseFailAlloc_2921_; 
v_reuseFailAlloc_2921_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2921_, 0, v_x_2889_);
lean_ctor_set(v_reuseFailAlloc_2921_, 1, v_x_2890_);
v___x_2920_ = v_reuseFailAlloc_2921_;
goto v_reusejp_2919_;
}
v_reusejp_2919_:
{
v___y_2904_ = v___x_2920_;
goto v___jp_2903_;
}
}
}
}
case 1:
{
lean_object* v_node_2923_; lean_object* v___x_2925_; uint8_t v_isShared_2926_; uint8_t v_isSharedCheck_2935_; 
v_node_2923_ = lean_ctor_get(v_v_2900_, 0);
v_isSharedCheck_2935_ = !lean_is_exclusive(v_v_2900_);
if (v_isSharedCheck_2935_ == 0)
{
v___x_2925_ = v_v_2900_;
v_isShared_2926_ = v_isSharedCheck_2935_;
goto v_resetjp_2924_;
}
else
{
lean_inc(v_node_2923_);
lean_dec(v_v_2900_);
v___x_2925_ = lean_box(0);
v_isShared_2926_ = v_isSharedCheck_2935_;
goto v_resetjp_2924_;
}
v_resetjp_2924_:
{
size_t v___x_2927_; size_t v___x_2928_; size_t v___x_2929_; size_t v___x_2930_; lean_object* v___x_2931_; lean_object* v___x_2933_; 
v___x_2927_ = ((size_t)5ULL);
v___x_2928_ = lean_usize_shift_right(v_x_2887_, v___x_2927_);
v___x_2929_ = ((size_t)1ULL);
v___x_2930_ = lean_usize_add(v_x_2888_, v___x_2929_);
v___x_2931_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0___redArg(v_node_2923_, v___x_2928_, v___x_2930_, v_x_2889_, v_x_2890_);
if (v_isShared_2926_ == 0)
{
lean_ctor_set(v___x_2925_, 0, v___x_2931_);
v___x_2933_ = v___x_2925_;
goto v_reusejp_2932_;
}
else
{
lean_object* v_reuseFailAlloc_2934_; 
v_reuseFailAlloc_2934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2934_, 0, v___x_2931_);
v___x_2933_ = v_reuseFailAlloc_2934_;
goto v_reusejp_2932_;
}
v_reusejp_2932_:
{
v___y_2904_ = v___x_2933_;
goto v___jp_2903_;
}
}
}
default: 
{
lean_object* v___x_2936_; 
v___x_2936_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2936_, 0, v_x_2889_);
lean_ctor_set(v___x_2936_, 1, v_x_2890_);
v___y_2904_ = v___x_2936_;
goto v___jp_2903_;
}
}
v___jp_2903_:
{
lean_object* v___x_2905_; lean_object* v___x_2907_; 
v___x_2905_ = lean_array_fset(v_xs_x27_2902_, v_j_2894_, v___y_2904_);
lean_dec(v_j_2894_);
if (v_isShared_2899_ == 0)
{
lean_ctor_set(v___x_2898_, 0, v___x_2905_);
v___x_2907_ = v___x_2898_;
goto v_reusejp_2906_;
}
else
{
lean_object* v_reuseFailAlloc_2908_; 
v_reuseFailAlloc_2908_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2908_, 0, v___x_2905_);
v___x_2907_ = v_reuseFailAlloc_2908_;
goto v_reusejp_2906_;
}
v_reusejp_2906_:
{
return v___x_2907_;
}
}
}
}
}
else
{
lean_object* v_ks_2939_; lean_object* v_vs_2940_; lean_object* v___x_2942_; uint8_t v_isShared_2943_; uint8_t v_isSharedCheck_2958_; 
v_ks_2939_ = lean_ctor_get(v_x_2886_, 0);
v_vs_2940_ = lean_ctor_get(v_x_2886_, 1);
v_isSharedCheck_2958_ = !lean_is_exclusive(v_x_2886_);
if (v_isSharedCheck_2958_ == 0)
{
v___x_2942_ = v_x_2886_;
v_isShared_2943_ = v_isSharedCheck_2958_;
goto v_resetjp_2941_;
}
else
{
lean_inc(v_vs_2940_);
lean_inc(v_ks_2939_);
lean_dec(v_x_2886_);
v___x_2942_ = lean_box(0);
v_isShared_2943_ = v_isSharedCheck_2958_;
goto v_resetjp_2941_;
}
v_resetjp_2941_:
{
lean_object* v___x_2945_; 
if (v_isShared_2943_ == 0)
{
v___x_2945_ = v___x_2942_;
goto v_reusejp_2944_;
}
else
{
lean_object* v_reuseFailAlloc_2957_; 
v_reuseFailAlloc_2957_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2957_, 0, v_ks_2939_);
lean_ctor_set(v_reuseFailAlloc_2957_, 1, v_vs_2940_);
v___x_2945_ = v_reuseFailAlloc_2957_;
goto v_reusejp_2944_;
}
v_reusejp_2944_:
{
lean_object* v_newNode_2946_; size_t v___x_2947_; uint8_t v___x_2948_; 
v_newNode_2946_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0_spec__1___redArg(v___x_2945_, v_x_2889_, v_x_2890_);
v___x_2947_ = ((size_t)7ULL);
v___x_2948_ = lean_usize_dec_le(v___x_2947_, v_x_2888_);
if (v___x_2948_ == 0)
{
lean_object* v___x_2949_; lean_object* v___x_2950_; uint8_t v___x_2951_; 
v___x_2949_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2946_);
v___x_2950_ = lean_unsigned_to_nat(4u);
v___x_2951_ = lean_nat_dec_lt(v___x_2949_, v___x_2950_);
lean_dec(v___x_2949_);
if (v___x_2951_ == 0)
{
lean_object* v_ks_2952_; lean_object* v_vs_2953_; lean_object* v___x_2954_; lean_object* v___x_2955_; lean_object* v___x_2956_; 
v_ks_2952_ = lean_ctor_get(v_newNode_2946_, 0);
lean_inc_ref(v_ks_2952_);
v_vs_2953_ = lean_ctor_get(v_newNode_2946_, 1);
lean_inc_ref(v_vs_2953_);
lean_dec_ref(v_newNode_2946_);
v___x_2954_ = lean_unsigned_to_nat(0u);
v___x_2955_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg___closed__0);
v___x_2956_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0_spec__2___redArg(v_x_2888_, v_ks_2952_, v_vs_2953_, v___x_2954_, v___x_2955_);
lean_dec_ref(v_vs_2953_);
lean_dec_ref(v_ks_2952_);
return v___x_2956_;
}
else
{
return v_newNode_2946_;
}
}
else
{
return v_newNode_2946_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0_spec__2___redArg(size_t v_depth_2959_, lean_object* v_keys_2960_, lean_object* v_vals_2961_, lean_object* v_i_2962_, lean_object* v_entries_2963_){
_start:
{
lean_object* v___x_2964_; uint8_t v___x_2965_; 
v___x_2964_ = lean_array_get_size(v_keys_2960_);
v___x_2965_ = lean_nat_dec_lt(v_i_2962_, v___x_2964_);
if (v___x_2965_ == 0)
{
lean_dec(v_i_2962_);
return v_entries_2963_;
}
else
{
lean_object* v_k_2966_; lean_object* v_v_2967_; size_t v___x_2968_; size_t v___x_2969_; size_t v___x_2970_; uint64_t v___x_2971_; size_t v_h_2972_; size_t v___x_2973_; lean_object* v___x_2974_; size_t v___x_2975_; size_t v___x_2976_; size_t v___x_2977_; size_t v_h_2978_; lean_object* v___x_2979_; lean_object* v___x_2980_; 
v_k_2966_ = lean_array_fget_borrowed(v_keys_2960_, v_i_2962_);
v_v_2967_ = lean_array_fget_borrowed(v_vals_2961_, v_i_2962_);
v___x_2968_ = lean_ptr_addr(v_k_2966_);
v___x_2969_ = ((size_t)3ULL);
v___x_2970_ = lean_usize_shift_right(v___x_2968_, v___x_2969_);
v___x_2971_ = lean_usize_to_uint64(v___x_2970_);
v_h_2972_ = lean_uint64_to_usize(v___x_2971_);
v___x_2973_ = ((size_t)5ULL);
v___x_2974_ = lean_unsigned_to_nat(1u);
v___x_2975_ = ((size_t)1ULL);
v___x_2976_ = lean_usize_sub(v_depth_2959_, v___x_2975_);
v___x_2977_ = lean_usize_mul(v___x_2973_, v___x_2976_);
v_h_2978_ = lean_usize_shift_right(v_h_2972_, v___x_2977_);
v___x_2979_ = lean_nat_add(v_i_2962_, v___x_2974_);
lean_dec(v_i_2962_);
lean_inc(v_v_2967_);
lean_inc(v_k_2966_);
v___x_2980_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0___redArg(v_entries_2963_, v_h_2978_, v_depth_2959_, v_k_2966_, v_v_2967_);
v_i_2962_ = v___x_2979_;
v_entries_2963_ = v___x_2980_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_2982_, lean_object* v_keys_2983_, lean_object* v_vals_2984_, lean_object* v_i_2985_, lean_object* v_entries_2986_){
_start:
{
size_t v_depth_boxed_2987_; lean_object* v_res_2988_; 
v_depth_boxed_2987_ = lean_unbox_usize(v_depth_2982_);
lean_dec(v_depth_2982_);
v_res_2988_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0_spec__2___redArg(v_depth_boxed_2987_, v_keys_2983_, v_vals_2984_, v_i_2985_, v_entries_2986_);
lean_dec_ref(v_vals_2984_);
lean_dec_ref(v_keys_2983_);
return v_res_2988_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0___redArg___boxed(lean_object* v_x_2989_, lean_object* v_x_2990_, lean_object* v_x_2991_, lean_object* v_x_2992_, lean_object* v_x_2993_){
_start:
{
size_t v_x_150515__boxed_2994_; size_t v_x_150516__boxed_2995_; lean_object* v_res_2996_; 
v_x_150515__boxed_2994_ = lean_unbox_usize(v_x_2990_);
lean_dec(v_x_2990_);
v_x_150516__boxed_2995_ = lean_unbox_usize(v_x_2991_);
lean_dec(v_x_2991_);
v_res_2996_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0___redArg(v_x_2989_, v_x_150515__boxed_2994_, v_x_150516__boxed_2995_, v_x_2992_, v_x_2993_);
return v_res_2996_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0___redArg(lean_object* v_x_2997_, lean_object* v_x_2998_, lean_object* v_x_2999_){
_start:
{
size_t v___x_3000_; size_t v___x_3001_; size_t v___x_3002_; uint64_t v___x_3003_; size_t v___x_3004_; size_t v___x_3005_; lean_object* v___x_3006_; 
v___x_3000_ = lean_ptr_addr(v_x_2998_);
v___x_3001_ = ((size_t)3ULL);
v___x_3002_ = lean_usize_shift_right(v___x_3000_, v___x_3001_);
v___x_3003_ = lean_usize_to_uint64(v___x_3002_);
v___x_3004_ = lean_uint64_to_usize(v___x_3003_);
v___x_3005_ = ((size_t)1ULL);
v___x_3006_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0___redArg(v_x_2997_, v___x_3004_, v___x_3005_, v_x_2998_, v_x_2999_);
return v___x_3006_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_internalize___lam__0(lean_object* v_e_3007_, lean_object* v_val_3008_, lean_object* v_s_3009_){
_start:
{
lean_object* v_toRing_3010_; lean_object* v_invFn_x3f_3011_; lean_object* v_semiringId_x3f_3012_; lean_object* v_commSemiringInst_3013_; lean_object* v_commRingInst_3014_; lean_object* v_noZeroDivInst_x3f_3015_; lean_object* v_fieldInst_x3f_3016_; lean_object* v_powIdentityInst_x3f_3017_; lean_object* v_denoteEntries_3018_; lean_object* v_nextId_3019_; lean_object* v_steps_3020_; lean_object* v_queue_3021_; lean_object* v_basis_3022_; lean_object* v_diseqs_3023_; uint8_t v_recheck_3024_; lean_object* v_invSet_3025_; lean_object* v_powIdentityVarCount_3026_; lean_object* v_numEq0_x3f_3027_; uint8_t v_numEq0Updated_3028_; lean_object* v___x_3030_; uint8_t v_isShared_3031_; uint8_t v_isSharedCheck_3062_; 
v_toRing_3010_ = lean_ctor_get(v_s_3009_, 0);
v_invFn_x3f_3011_ = lean_ctor_get(v_s_3009_, 1);
v_semiringId_x3f_3012_ = lean_ctor_get(v_s_3009_, 2);
v_commSemiringInst_3013_ = lean_ctor_get(v_s_3009_, 3);
v_commRingInst_3014_ = lean_ctor_get(v_s_3009_, 4);
v_noZeroDivInst_x3f_3015_ = lean_ctor_get(v_s_3009_, 5);
v_fieldInst_x3f_3016_ = lean_ctor_get(v_s_3009_, 6);
v_powIdentityInst_x3f_3017_ = lean_ctor_get(v_s_3009_, 7);
v_denoteEntries_3018_ = lean_ctor_get(v_s_3009_, 8);
v_nextId_3019_ = lean_ctor_get(v_s_3009_, 9);
v_steps_3020_ = lean_ctor_get(v_s_3009_, 10);
v_queue_3021_ = lean_ctor_get(v_s_3009_, 11);
v_basis_3022_ = lean_ctor_get(v_s_3009_, 12);
v_diseqs_3023_ = lean_ctor_get(v_s_3009_, 13);
v_recheck_3024_ = lean_ctor_get_uint8(v_s_3009_, sizeof(void*)*17);
v_invSet_3025_ = lean_ctor_get(v_s_3009_, 14);
v_powIdentityVarCount_3026_ = lean_ctor_get(v_s_3009_, 15);
v_numEq0_x3f_3027_ = lean_ctor_get(v_s_3009_, 16);
v_numEq0Updated_3028_ = lean_ctor_get_uint8(v_s_3009_, sizeof(void*)*17 + 1);
v_isSharedCheck_3062_ = !lean_is_exclusive(v_s_3009_);
if (v_isSharedCheck_3062_ == 0)
{
v___x_3030_ = v_s_3009_;
v_isShared_3031_ = v_isSharedCheck_3062_;
goto v_resetjp_3029_;
}
else
{
lean_inc(v_numEq0_x3f_3027_);
lean_inc(v_powIdentityVarCount_3026_);
lean_inc(v_invSet_3025_);
lean_inc(v_diseqs_3023_);
lean_inc(v_basis_3022_);
lean_inc(v_queue_3021_);
lean_inc(v_steps_3020_);
lean_inc(v_nextId_3019_);
lean_inc(v_denoteEntries_3018_);
lean_inc(v_powIdentityInst_x3f_3017_);
lean_inc(v_fieldInst_x3f_3016_);
lean_inc(v_noZeroDivInst_x3f_3015_);
lean_inc(v_commRingInst_3014_);
lean_inc(v_commSemiringInst_3013_);
lean_inc(v_semiringId_x3f_3012_);
lean_inc(v_invFn_x3f_3011_);
lean_inc(v_toRing_3010_);
lean_dec(v_s_3009_);
v___x_3030_ = lean_box(0);
v_isShared_3031_ = v_isSharedCheck_3062_;
goto v_resetjp_3029_;
}
v_resetjp_3029_:
{
lean_object* v_id_3032_; lean_object* v_type_3033_; lean_object* v_u_3034_; lean_object* v_ringInst_3035_; lean_object* v_semiringInst_3036_; lean_object* v_charInst_x3f_3037_; lean_object* v_addFn_x3f_3038_; lean_object* v_mulFn_x3f_3039_; lean_object* v_subFn_x3f_3040_; lean_object* v_negFn_x3f_3041_; lean_object* v_powFn_x3f_3042_; lean_object* v_intCastFn_x3f_3043_; lean_object* v_natCastFn_x3f_3044_; lean_object* v_one_x3f_3045_; lean_object* v_vars_3046_; lean_object* v_varMap_3047_; lean_object* v_denote_3048_; lean_object* v___x_3050_; uint8_t v_isShared_3051_; uint8_t v_isSharedCheck_3061_; 
v_id_3032_ = lean_ctor_get(v_toRing_3010_, 0);
v_type_3033_ = lean_ctor_get(v_toRing_3010_, 1);
v_u_3034_ = lean_ctor_get(v_toRing_3010_, 2);
v_ringInst_3035_ = lean_ctor_get(v_toRing_3010_, 3);
v_semiringInst_3036_ = lean_ctor_get(v_toRing_3010_, 4);
v_charInst_x3f_3037_ = lean_ctor_get(v_toRing_3010_, 5);
v_addFn_x3f_3038_ = lean_ctor_get(v_toRing_3010_, 6);
v_mulFn_x3f_3039_ = lean_ctor_get(v_toRing_3010_, 7);
v_subFn_x3f_3040_ = lean_ctor_get(v_toRing_3010_, 8);
v_negFn_x3f_3041_ = lean_ctor_get(v_toRing_3010_, 9);
v_powFn_x3f_3042_ = lean_ctor_get(v_toRing_3010_, 10);
v_intCastFn_x3f_3043_ = lean_ctor_get(v_toRing_3010_, 11);
v_natCastFn_x3f_3044_ = lean_ctor_get(v_toRing_3010_, 12);
v_one_x3f_3045_ = lean_ctor_get(v_toRing_3010_, 13);
v_vars_3046_ = lean_ctor_get(v_toRing_3010_, 14);
v_varMap_3047_ = lean_ctor_get(v_toRing_3010_, 15);
v_denote_3048_ = lean_ctor_get(v_toRing_3010_, 16);
v_isSharedCheck_3061_ = !lean_is_exclusive(v_toRing_3010_);
if (v_isSharedCheck_3061_ == 0)
{
v___x_3050_ = v_toRing_3010_;
v_isShared_3051_ = v_isSharedCheck_3061_;
goto v_resetjp_3049_;
}
else
{
lean_inc(v_denote_3048_);
lean_inc(v_varMap_3047_);
lean_inc(v_vars_3046_);
lean_inc(v_one_x3f_3045_);
lean_inc(v_natCastFn_x3f_3044_);
lean_inc(v_intCastFn_x3f_3043_);
lean_inc(v_powFn_x3f_3042_);
lean_inc(v_negFn_x3f_3041_);
lean_inc(v_subFn_x3f_3040_);
lean_inc(v_mulFn_x3f_3039_);
lean_inc(v_addFn_x3f_3038_);
lean_inc(v_charInst_x3f_3037_);
lean_inc(v_semiringInst_3036_);
lean_inc(v_ringInst_3035_);
lean_inc(v_u_3034_);
lean_inc(v_type_3033_);
lean_inc(v_id_3032_);
lean_dec(v_toRing_3010_);
v___x_3050_ = lean_box(0);
v_isShared_3051_ = v_isSharedCheck_3061_;
goto v_resetjp_3049_;
}
v_resetjp_3049_:
{
lean_object* v___x_3052_; lean_object* v___x_3054_; 
lean_inc_ref(v_val_3008_);
lean_inc_ref(v_e_3007_);
v___x_3052_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0___redArg(v_denote_3048_, v_e_3007_, v_val_3008_);
if (v_isShared_3051_ == 0)
{
lean_ctor_set(v___x_3050_, 16, v___x_3052_);
v___x_3054_ = v___x_3050_;
goto v_reusejp_3053_;
}
else
{
lean_object* v_reuseFailAlloc_3060_; 
v_reuseFailAlloc_3060_ = lean_alloc_ctor(0, 17, 0);
lean_ctor_set(v_reuseFailAlloc_3060_, 0, v_id_3032_);
lean_ctor_set(v_reuseFailAlloc_3060_, 1, v_type_3033_);
lean_ctor_set(v_reuseFailAlloc_3060_, 2, v_u_3034_);
lean_ctor_set(v_reuseFailAlloc_3060_, 3, v_ringInst_3035_);
lean_ctor_set(v_reuseFailAlloc_3060_, 4, v_semiringInst_3036_);
lean_ctor_set(v_reuseFailAlloc_3060_, 5, v_charInst_x3f_3037_);
lean_ctor_set(v_reuseFailAlloc_3060_, 6, v_addFn_x3f_3038_);
lean_ctor_set(v_reuseFailAlloc_3060_, 7, v_mulFn_x3f_3039_);
lean_ctor_set(v_reuseFailAlloc_3060_, 8, v_subFn_x3f_3040_);
lean_ctor_set(v_reuseFailAlloc_3060_, 9, v_negFn_x3f_3041_);
lean_ctor_set(v_reuseFailAlloc_3060_, 10, v_powFn_x3f_3042_);
lean_ctor_set(v_reuseFailAlloc_3060_, 11, v_intCastFn_x3f_3043_);
lean_ctor_set(v_reuseFailAlloc_3060_, 12, v_natCastFn_x3f_3044_);
lean_ctor_set(v_reuseFailAlloc_3060_, 13, v_one_x3f_3045_);
lean_ctor_set(v_reuseFailAlloc_3060_, 14, v_vars_3046_);
lean_ctor_set(v_reuseFailAlloc_3060_, 15, v_varMap_3047_);
lean_ctor_set(v_reuseFailAlloc_3060_, 16, v___x_3052_);
v___x_3054_ = v_reuseFailAlloc_3060_;
goto v_reusejp_3053_;
}
v_reusejp_3053_:
{
lean_object* v___x_3055_; lean_object* v___x_3056_; lean_object* v___x_3058_; 
v___x_3055_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3055_, 0, v_e_3007_);
lean_ctor_set(v___x_3055_, 1, v_val_3008_);
v___x_3056_ = l_Lean_PersistentArray_push___redArg(v_denoteEntries_3018_, v___x_3055_);
if (v_isShared_3031_ == 0)
{
lean_ctor_set(v___x_3030_, 8, v___x_3056_);
lean_ctor_set(v___x_3030_, 0, v___x_3054_);
v___x_3058_ = v___x_3030_;
goto v_reusejp_3057_;
}
else
{
lean_object* v_reuseFailAlloc_3059_; 
v_reuseFailAlloc_3059_ = lean_alloc_ctor(0, 17, 2);
lean_ctor_set(v_reuseFailAlloc_3059_, 0, v___x_3054_);
lean_ctor_set(v_reuseFailAlloc_3059_, 1, v_invFn_x3f_3011_);
lean_ctor_set(v_reuseFailAlloc_3059_, 2, v_semiringId_x3f_3012_);
lean_ctor_set(v_reuseFailAlloc_3059_, 3, v_commSemiringInst_3013_);
lean_ctor_set(v_reuseFailAlloc_3059_, 4, v_commRingInst_3014_);
lean_ctor_set(v_reuseFailAlloc_3059_, 5, v_noZeroDivInst_x3f_3015_);
lean_ctor_set(v_reuseFailAlloc_3059_, 6, v_fieldInst_x3f_3016_);
lean_ctor_set(v_reuseFailAlloc_3059_, 7, v_powIdentityInst_x3f_3017_);
lean_ctor_set(v_reuseFailAlloc_3059_, 8, v___x_3056_);
lean_ctor_set(v_reuseFailAlloc_3059_, 9, v_nextId_3019_);
lean_ctor_set(v_reuseFailAlloc_3059_, 10, v_steps_3020_);
lean_ctor_set(v_reuseFailAlloc_3059_, 11, v_queue_3021_);
lean_ctor_set(v_reuseFailAlloc_3059_, 12, v_basis_3022_);
lean_ctor_set(v_reuseFailAlloc_3059_, 13, v_diseqs_3023_);
lean_ctor_set(v_reuseFailAlloc_3059_, 14, v_invSet_3025_);
lean_ctor_set(v_reuseFailAlloc_3059_, 15, v_powIdentityVarCount_3026_);
lean_ctor_set(v_reuseFailAlloc_3059_, 16, v_numEq0_x3f_3027_);
lean_ctor_set_uint8(v_reuseFailAlloc_3059_, sizeof(void*)*17, v_recheck_3024_);
lean_ctor_set_uint8(v_reuseFailAlloc_3059_, sizeof(void*)*17 + 1, v_numEq0Updated_3028_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_internalize___lam__1(lean_object* v___y_3063_, lean_object* v_e_3064_, lean_object* v_val_3065_, lean_object* v_s_3066_){
_start:
{
lean_object* v_rings_3067_; lean_object* v_typeIdOf_3068_; lean_object* v_exprToRingId_3069_; lean_object* v_semirings_3070_; lean_object* v_stypeIdOf_3071_; lean_object* v_exprToSemiringId_3072_; lean_object* v_ncRings_3073_; lean_object* v_exprToNCRingId_3074_; lean_object* v_nctypeIdOf_3075_; lean_object* v_ncSemirings_3076_; lean_object* v_exprToNCSemiringId_3077_; lean_object* v_ncstypeIdOf_3078_; lean_object* v_steps_3079_; uint8_t v_reportedMaxDegreeIssue_3080_; lean_object* v___x_3081_; uint8_t v___x_3082_; 
v_rings_3067_ = lean_ctor_get(v_s_3066_, 0);
v_typeIdOf_3068_ = lean_ctor_get(v_s_3066_, 1);
v_exprToRingId_3069_ = lean_ctor_get(v_s_3066_, 2);
v_semirings_3070_ = lean_ctor_get(v_s_3066_, 3);
v_stypeIdOf_3071_ = lean_ctor_get(v_s_3066_, 4);
v_exprToSemiringId_3072_ = lean_ctor_get(v_s_3066_, 5);
v_ncRings_3073_ = lean_ctor_get(v_s_3066_, 6);
v_exprToNCRingId_3074_ = lean_ctor_get(v_s_3066_, 7);
v_nctypeIdOf_3075_ = lean_ctor_get(v_s_3066_, 8);
v_ncSemirings_3076_ = lean_ctor_get(v_s_3066_, 9);
v_exprToNCSemiringId_3077_ = lean_ctor_get(v_s_3066_, 10);
v_ncstypeIdOf_3078_ = lean_ctor_get(v_s_3066_, 11);
v_steps_3079_ = lean_ctor_get(v_s_3066_, 12);
v_reportedMaxDegreeIssue_3080_ = lean_ctor_get_uint8(v_s_3066_, sizeof(void*)*13);
v___x_3081_ = lean_array_get_size(v_semirings_3070_);
v___x_3082_ = lean_nat_dec_lt(v___y_3063_, v___x_3081_);
if (v___x_3082_ == 0)
{
lean_dec_ref(v_val_3065_);
lean_dec_ref(v_e_3064_);
return v_s_3066_;
}
else
{
lean_object* v___x_3084_; uint8_t v_isShared_3085_; uint8_t v_isSharedCheck_3124_; 
lean_inc(v_steps_3079_);
lean_inc_ref(v_ncstypeIdOf_3078_);
lean_inc_ref(v_exprToNCSemiringId_3077_);
lean_inc_ref(v_ncSemirings_3076_);
lean_inc_ref(v_nctypeIdOf_3075_);
lean_inc_ref(v_exprToNCRingId_3074_);
lean_inc_ref(v_ncRings_3073_);
lean_inc_ref(v_exprToSemiringId_3072_);
lean_inc_ref(v_stypeIdOf_3071_);
lean_inc_ref(v_semirings_3070_);
lean_inc_ref(v_exprToRingId_3069_);
lean_inc_ref(v_typeIdOf_3068_);
lean_inc_ref(v_rings_3067_);
v_isSharedCheck_3124_ = !lean_is_exclusive(v_s_3066_);
if (v_isSharedCheck_3124_ == 0)
{
lean_object* v_unused_3125_; lean_object* v_unused_3126_; lean_object* v_unused_3127_; lean_object* v_unused_3128_; lean_object* v_unused_3129_; lean_object* v_unused_3130_; lean_object* v_unused_3131_; lean_object* v_unused_3132_; lean_object* v_unused_3133_; lean_object* v_unused_3134_; lean_object* v_unused_3135_; lean_object* v_unused_3136_; lean_object* v_unused_3137_; 
v_unused_3125_ = lean_ctor_get(v_s_3066_, 12);
lean_dec(v_unused_3125_);
v_unused_3126_ = lean_ctor_get(v_s_3066_, 11);
lean_dec(v_unused_3126_);
v_unused_3127_ = lean_ctor_get(v_s_3066_, 10);
lean_dec(v_unused_3127_);
v_unused_3128_ = lean_ctor_get(v_s_3066_, 9);
lean_dec(v_unused_3128_);
v_unused_3129_ = lean_ctor_get(v_s_3066_, 8);
lean_dec(v_unused_3129_);
v_unused_3130_ = lean_ctor_get(v_s_3066_, 7);
lean_dec(v_unused_3130_);
v_unused_3131_ = lean_ctor_get(v_s_3066_, 6);
lean_dec(v_unused_3131_);
v_unused_3132_ = lean_ctor_get(v_s_3066_, 5);
lean_dec(v_unused_3132_);
v_unused_3133_ = lean_ctor_get(v_s_3066_, 4);
lean_dec(v_unused_3133_);
v_unused_3134_ = lean_ctor_get(v_s_3066_, 3);
lean_dec(v_unused_3134_);
v_unused_3135_ = lean_ctor_get(v_s_3066_, 2);
lean_dec(v_unused_3135_);
v_unused_3136_ = lean_ctor_get(v_s_3066_, 1);
lean_dec(v_unused_3136_);
v_unused_3137_ = lean_ctor_get(v_s_3066_, 0);
lean_dec(v_unused_3137_);
v___x_3084_ = v_s_3066_;
v_isShared_3085_ = v_isSharedCheck_3124_;
goto v_resetjp_3083_;
}
else
{
lean_dec(v_s_3066_);
v___x_3084_ = lean_box(0);
v_isShared_3085_ = v_isSharedCheck_3124_;
goto v_resetjp_3083_;
}
v_resetjp_3083_:
{
lean_object* v_v_3086_; lean_object* v_toSemiring_3087_; lean_object* v_ringId_3088_; lean_object* v_commSemiringInst_3089_; lean_object* v_addRightCancelInst_x3f_3090_; lean_object* v_toQFn_x3f_3091_; lean_object* v___x_3093_; uint8_t v_isShared_3094_; uint8_t v_isSharedCheck_3123_; 
v_v_3086_ = lean_array_fget(v_semirings_3070_, v___y_3063_);
v_toSemiring_3087_ = lean_ctor_get(v_v_3086_, 0);
v_ringId_3088_ = lean_ctor_get(v_v_3086_, 1);
v_commSemiringInst_3089_ = lean_ctor_get(v_v_3086_, 2);
v_addRightCancelInst_x3f_3090_ = lean_ctor_get(v_v_3086_, 3);
v_toQFn_x3f_3091_ = lean_ctor_get(v_v_3086_, 4);
v_isSharedCheck_3123_ = !lean_is_exclusive(v_v_3086_);
if (v_isSharedCheck_3123_ == 0)
{
v___x_3093_ = v_v_3086_;
v_isShared_3094_ = v_isSharedCheck_3123_;
goto v_resetjp_3092_;
}
else
{
lean_inc(v_toQFn_x3f_3091_);
lean_inc(v_addRightCancelInst_x3f_3090_);
lean_inc(v_commSemiringInst_3089_);
lean_inc(v_ringId_3088_);
lean_inc(v_toSemiring_3087_);
lean_dec(v_v_3086_);
v___x_3093_ = lean_box(0);
v_isShared_3094_ = v_isSharedCheck_3123_;
goto v_resetjp_3092_;
}
v_resetjp_3092_:
{
lean_object* v_id_3095_; lean_object* v_type_3096_; lean_object* v_u_3097_; lean_object* v_semiringInst_3098_; lean_object* v_addFn_x3f_3099_; lean_object* v_mulFn_x3f_3100_; lean_object* v_powFn_x3f_3101_; lean_object* v_natCastFn_x3f_3102_; lean_object* v_denote_3103_; lean_object* v_vars_3104_; lean_object* v_varMap_3105_; lean_object* v___x_3107_; uint8_t v_isShared_3108_; uint8_t v_isSharedCheck_3122_; 
v_id_3095_ = lean_ctor_get(v_toSemiring_3087_, 0);
v_type_3096_ = lean_ctor_get(v_toSemiring_3087_, 1);
v_u_3097_ = lean_ctor_get(v_toSemiring_3087_, 2);
v_semiringInst_3098_ = lean_ctor_get(v_toSemiring_3087_, 3);
v_addFn_x3f_3099_ = lean_ctor_get(v_toSemiring_3087_, 4);
v_mulFn_x3f_3100_ = lean_ctor_get(v_toSemiring_3087_, 5);
v_powFn_x3f_3101_ = lean_ctor_get(v_toSemiring_3087_, 6);
v_natCastFn_x3f_3102_ = lean_ctor_get(v_toSemiring_3087_, 7);
v_denote_3103_ = lean_ctor_get(v_toSemiring_3087_, 8);
v_vars_3104_ = lean_ctor_get(v_toSemiring_3087_, 9);
v_varMap_3105_ = lean_ctor_get(v_toSemiring_3087_, 10);
v_isSharedCheck_3122_ = !lean_is_exclusive(v_toSemiring_3087_);
if (v_isSharedCheck_3122_ == 0)
{
v___x_3107_ = v_toSemiring_3087_;
v_isShared_3108_ = v_isSharedCheck_3122_;
goto v_resetjp_3106_;
}
else
{
lean_inc(v_varMap_3105_);
lean_inc(v_vars_3104_);
lean_inc(v_denote_3103_);
lean_inc(v_natCastFn_x3f_3102_);
lean_inc(v_powFn_x3f_3101_);
lean_inc(v_mulFn_x3f_3100_);
lean_inc(v_addFn_x3f_3099_);
lean_inc(v_semiringInst_3098_);
lean_inc(v_u_3097_);
lean_inc(v_type_3096_);
lean_inc(v_id_3095_);
lean_dec(v_toSemiring_3087_);
v___x_3107_ = lean_box(0);
v_isShared_3108_ = v_isSharedCheck_3122_;
goto v_resetjp_3106_;
}
v_resetjp_3106_:
{
lean_object* v___x_3109_; lean_object* v_xs_x27_3110_; lean_object* v___x_3111_; lean_object* v___x_3113_; 
v___x_3109_ = lean_box(0);
v_xs_x27_3110_ = lean_array_fset(v_semirings_3070_, v___y_3063_, v___x_3109_);
v___x_3111_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0___redArg(v_denote_3103_, v_e_3064_, v_val_3065_);
if (v_isShared_3108_ == 0)
{
lean_ctor_set(v___x_3107_, 8, v___x_3111_);
v___x_3113_ = v___x_3107_;
goto v_reusejp_3112_;
}
else
{
lean_object* v_reuseFailAlloc_3121_; 
v_reuseFailAlloc_3121_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_3121_, 0, v_id_3095_);
lean_ctor_set(v_reuseFailAlloc_3121_, 1, v_type_3096_);
lean_ctor_set(v_reuseFailAlloc_3121_, 2, v_u_3097_);
lean_ctor_set(v_reuseFailAlloc_3121_, 3, v_semiringInst_3098_);
lean_ctor_set(v_reuseFailAlloc_3121_, 4, v_addFn_x3f_3099_);
lean_ctor_set(v_reuseFailAlloc_3121_, 5, v_mulFn_x3f_3100_);
lean_ctor_set(v_reuseFailAlloc_3121_, 6, v_powFn_x3f_3101_);
lean_ctor_set(v_reuseFailAlloc_3121_, 7, v_natCastFn_x3f_3102_);
lean_ctor_set(v_reuseFailAlloc_3121_, 8, v___x_3111_);
lean_ctor_set(v_reuseFailAlloc_3121_, 9, v_vars_3104_);
lean_ctor_set(v_reuseFailAlloc_3121_, 10, v_varMap_3105_);
v___x_3113_ = v_reuseFailAlloc_3121_;
goto v_reusejp_3112_;
}
v_reusejp_3112_:
{
lean_object* v___x_3115_; 
if (v_isShared_3094_ == 0)
{
lean_ctor_set(v___x_3093_, 0, v___x_3113_);
v___x_3115_ = v___x_3093_;
goto v_reusejp_3114_;
}
else
{
lean_object* v_reuseFailAlloc_3120_; 
v_reuseFailAlloc_3120_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3120_, 0, v___x_3113_);
lean_ctor_set(v_reuseFailAlloc_3120_, 1, v_ringId_3088_);
lean_ctor_set(v_reuseFailAlloc_3120_, 2, v_commSemiringInst_3089_);
lean_ctor_set(v_reuseFailAlloc_3120_, 3, v_addRightCancelInst_x3f_3090_);
lean_ctor_set(v_reuseFailAlloc_3120_, 4, v_toQFn_x3f_3091_);
v___x_3115_ = v_reuseFailAlloc_3120_;
goto v_reusejp_3114_;
}
v_reusejp_3114_:
{
lean_object* v___x_3116_; lean_object* v___x_3118_; 
v___x_3116_ = lean_array_fset(v_xs_x27_3110_, v___y_3063_, v___x_3115_);
if (v_isShared_3085_ == 0)
{
lean_ctor_set(v___x_3084_, 3, v___x_3116_);
v___x_3118_ = v___x_3084_;
goto v_reusejp_3117_;
}
else
{
lean_object* v_reuseFailAlloc_3119_; 
v_reuseFailAlloc_3119_ = lean_alloc_ctor(0, 13, 1);
lean_ctor_set(v_reuseFailAlloc_3119_, 0, v_rings_3067_);
lean_ctor_set(v_reuseFailAlloc_3119_, 1, v_typeIdOf_3068_);
lean_ctor_set(v_reuseFailAlloc_3119_, 2, v_exprToRingId_3069_);
lean_ctor_set(v_reuseFailAlloc_3119_, 3, v___x_3116_);
lean_ctor_set(v_reuseFailAlloc_3119_, 4, v_stypeIdOf_3071_);
lean_ctor_set(v_reuseFailAlloc_3119_, 5, v_exprToSemiringId_3072_);
lean_ctor_set(v_reuseFailAlloc_3119_, 6, v_ncRings_3073_);
lean_ctor_set(v_reuseFailAlloc_3119_, 7, v_exprToNCRingId_3074_);
lean_ctor_set(v_reuseFailAlloc_3119_, 8, v_nctypeIdOf_3075_);
lean_ctor_set(v_reuseFailAlloc_3119_, 9, v_ncSemirings_3076_);
lean_ctor_set(v_reuseFailAlloc_3119_, 10, v_exprToNCSemiringId_3077_);
lean_ctor_set(v_reuseFailAlloc_3119_, 11, v_ncstypeIdOf_3078_);
lean_ctor_set(v_reuseFailAlloc_3119_, 12, v_steps_3079_);
lean_ctor_set_uint8(v_reuseFailAlloc_3119_, sizeof(void*)*13, v_reportedMaxDegreeIssue_3080_);
v___x_3118_ = v_reuseFailAlloc_3119_;
goto v_reusejp_3117_;
}
v_reusejp_3117_:
{
return v___x_3118_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_internalize___lam__1___boxed(lean_object* v___y_3138_, lean_object* v_e_3139_, lean_object* v_val_3140_, lean_object* v_s_3141_){
_start:
{
lean_object* v_res_3142_; 
v_res_3142_ = l_Lean_Meta_Grind_Arith_CommRing_internalize___lam__1(v___y_3138_, v_e_3139_, v_val_3140_, v_s_3141_);
lean_dec(v___y_3138_);
return v_res_3142_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_internalize___lam__2(lean_object* v_e_3143_, lean_object* v_val_3144_, lean_object* v_s_3145_){
_start:
{
lean_object* v_id_3146_; lean_object* v_type_3147_; lean_object* v_u_3148_; lean_object* v_ringInst_3149_; lean_object* v_semiringInst_3150_; lean_object* v_charInst_x3f_3151_; lean_object* v_addFn_x3f_3152_; lean_object* v_mulFn_x3f_3153_; lean_object* v_subFn_x3f_3154_; lean_object* v_negFn_x3f_3155_; lean_object* v_powFn_x3f_3156_; lean_object* v_intCastFn_x3f_3157_; lean_object* v_natCastFn_x3f_3158_; lean_object* v_one_x3f_3159_; lean_object* v_vars_3160_; lean_object* v_varMap_3161_; lean_object* v_denote_3162_; lean_object* v___x_3164_; uint8_t v_isShared_3165_; uint8_t v_isSharedCheck_3170_; 
v_id_3146_ = lean_ctor_get(v_s_3145_, 0);
v_type_3147_ = lean_ctor_get(v_s_3145_, 1);
v_u_3148_ = lean_ctor_get(v_s_3145_, 2);
v_ringInst_3149_ = lean_ctor_get(v_s_3145_, 3);
v_semiringInst_3150_ = lean_ctor_get(v_s_3145_, 4);
v_charInst_x3f_3151_ = lean_ctor_get(v_s_3145_, 5);
v_addFn_x3f_3152_ = lean_ctor_get(v_s_3145_, 6);
v_mulFn_x3f_3153_ = lean_ctor_get(v_s_3145_, 7);
v_subFn_x3f_3154_ = lean_ctor_get(v_s_3145_, 8);
v_negFn_x3f_3155_ = lean_ctor_get(v_s_3145_, 9);
v_powFn_x3f_3156_ = lean_ctor_get(v_s_3145_, 10);
v_intCastFn_x3f_3157_ = lean_ctor_get(v_s_3145_, 11);
v_natCastFn_x3f_3158_ = lean_ctor_get(v_s_3145_, 12);
v_one_x3f_3159_ = lean_ctor_get(v_s_3145_, 13);
v_vars_3160_ = lean_ctor_get(v_s_3145_, 14);
v_varMap_3161_ = lean_ctor_get(v_s_3145_, 15);
v_denote_3162_ = lean_ctor_get(v_s_3145_, 16);
v_isSharedCheck_3170_ = !lean_is_exclusive(v_s_3145_);
if (v_isSharedCheck_3170_ == 0)
{
v___x_3164_ = v_s_3145_;
v_isShared_3165_ = v_isSharedCheck_3170_;
goto v_resetjp_3163_;
}
else
{
lean_inc(v_denote_3162_);
lean_inc(v_varMap_3161_);
lean_inc(v_vars_3160_);
lean_inc(v_one_x3f_3159_);
lean_inc(v_natCastFn_x3f_3158_);
lean_inc(v_intCastFn_x3f_3157_);
lean_inc(v_powFn_x3f_3156_);
lean_inc(v_negFn_x3f_3155_);
lean_inc(v_subFn_x3f_3154_);
lean_inc(v_mulFn_x3f_3153_);
lean_inc(v_addFn_x3f_3152_);
lean_inc(v_charInst_x3f_3151_);
lean_inc(v_semiringInst_3150_);
lean_inc(v_ringInst_3149_);
lean_inc(v_u_3148_);
lean_inc(v_type_3147_);
lean_inc(v_id_3146_);
lean_dec(v_s_3145_);
v___x_3164_ = lean_box(0);
v_isShared_3165_ = v_isSharedCheck_3170_;
goto v_resetjp_3163_;
}
v_resetjp_3163_:
{
lean_object* v___x_3166_; lean_object* v___x_3168_; 
v___x_3166_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0___redArg(v_denote_3162_, v_e_3143_, v_val_3144_);
if (v_isShared_3165_ == 0)
{
lean_ctor_set(v___x_3164_, 16, v___x_3166_);
v___x_3168_ = v___x_3164_;
goto v_reusejp_3167_;
}
else
{
lean_object* v_reuseFailAlloc_3169_; 
v_reuseFailAlloc_3169_ = lean_alloc_ctor(0, 17, 0);
lean_ctor_set(v_reuseFailAlloc_3169_, 0, v_id_3146_);
lean_ctor_set(v_reuseFailAlloc_3169_, 1, v_type_3147_);
lean_ctor_set(v_reuseFailAlloc_3169_, 2, v_u_3148_);
lean_ctor_set(v_reuseFailAlloc_3169_, 3, v_ringInst_3149_);
lean_ctor_set(v_reuseFailAlloc_3169_, 4, v_semiringInst_3150_);
lean_ctor_set(v_reuseFailAlloc_3169_, 5, v_charInst_x3f_3151_);
lean_ctor_set(v_reuseFailAlloc_3169_, 6, v_addFn_x3f_3152_);
lean_ctor_set(v_reuseFailAlloc_3169_, 7, v_mulFn_x3f_3153_);
lean_ctor_set(v_reuseFailAlloc_3169_, 8, v_subFn_x3f_3154_);
lean_ctor_set(v_reuseFailAlloc_3169_, 9, v_negFn_x3f_3155_);
lean_ctor_set(v_reuseFailAlloc_3169_, 10, v_powFn_x3f_3156_);
lean_ctor_set(v_reuseFailAlloc_3169_, 11, v_intCastFn_x3f_3157_);
lean_ctor_set(v_reuseFailAlloc_3169_, 12, v_natCastFn_x3f_3158_);
lean_ctor_set(v_reuseFailAlloc_3169_, 13, v_one_x3f_3159_);
lean_ctor_set(v_reuseFailAlloc_3169_, 14, v_vars_3160_);
lean_ctor_set(v_reuseFailAlloc_3169_, 15, v_varMap_3161_);
lean_ctor_set(v_reuseFailAlloc_3169_, 16, v___x_3166_);
v___x_3168_ = v_reuseFailAlloc_3169_;
goto v_reusejp_3167_;
}
v_reusejp_3167_:
{
return v___x_3168_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_internalize___lam__3(lean_object* v_e_3171_, lean_object* v_val_3172_, lean_object* v_s_3173_){
_start:
{
lean_object* v_id_3174_; lean_object* v_type_3175_; lean_object* v_u_3176_; lean_object* v_semiringInst_3177_; lean_object* v_addFn_x3f_3178_; lean_object* v_mulFn_x3f_3179_; lean_object* v_powFn_x3f_3180_; lean_object* v_natCastFn_x3f_3181_; lean_object* v_denote_3182_; lean_object* v_vars_3183_; lean_object* v_varMap_3184_; lean_object* v___x_3186_; uint8_t v_isShared_3187_; uint8_t v_isSharedCheck_3192_; 
v_id_3174_ = lean_ctor_get(v_s_3173_, 0);
v_type_3175_ = lean_ctor_get(v_s_3173_, 1);
v_u_3176_ = lean_ctor_get(v_s_3173_, 2);
v_semiringInst_3177_ = lean_ctor_get(v_s_3173_, 3);
v_addFn_x3f_3178_ = lean_ctor_get(v_s_3173_, 4);
v_mulFn_x3f_3179_ = lean_ctor_get(v_s_3173_, 5);
v_powFn_x3f_3180_ = lean_ctor_get(v_s_3173_, 6);
v_natCastFn_x3f_3181_ = lean_ctor_get(v_s_3173_, 7);
v_denote_3182_ = lean_ctor_get(v_s_3173_, 8);
v_vars_3183_ = lean_ctor_get(v_s_3173_, 9);
v_varMap_3184_ = lean_ctor_get(v_s_3173_, 10);
v_isSharedCheck_3192_ = !lean_is_exclusive(v_s_3173_);
if (v_isSharedCheck_3192_ == 0)
{
v___x_3186_ = v_s_3173_;
v_isShared_3187_ = v_isSharedCheck_3192_;
goto v_resetjp_3185_;
}
else
{
lean_inc(v_varMap_3184_);
lean_inc(v_vars_3183_);
lean_inc(v_denote_3182_);
lean_inc(v_natCastFn_x3f_3181_);
lean_inc(v_powFn_x3f_3180_);
lean_inc(v_mulFn_x3f_3179_);
lean_inc(v_addFn_x3f_3178_);
lean_inc(v_semiringInst_3177_);
lean_inc(v_u_3176_);
lean_inc(v_type_3175_);
lean_inc(v_id_3174_);
lean_dec(v_s_3173_);
v___x_3186_ = lean_box(0);
v_isShared_3187_ = v_isSharedCheck_3192_;
goto v_resetjp_3185_;
}
v_resetjp_3185_:
{
lean_object* v___x_3188_; lean_object* v___x_3190_; 
v___x_3188_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0___redArg(v_denote_3182_, v_e_3171_, v_val_3172_);
if (v_isShared_3187_ == 0)
{
lean_ctor_set(v___x_3186_, 8, v___x_3188_);
v___x_3190_ = v___x_3186_;
goto v_reusejp_3189_;
}
else
{
lean_object* v_reuseFailAlloc_3191_; 
v_reuseFailAlloc_3191_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_3191_, 0, v_id_3174_);
lean_ctor_set(v_reuseFailAlloc_3191_, 1, v_type_3175_);
lean_ctor_set(v_reuseFailAlloc_3191_, 2, v_u_3176_);
lean_ctor_set(v_reuseFailAlloc_3191_, 3, v_semiringInst_3177_);
lean_ctor_set(v_reuseFailAlloc_3191_, 4, v_addFn_x3f_3178_);
lean_ctor_set(v_reuseFailAlloc_3191_, 5, v_mulFn_x3f_3179_);
lean_ctor_set(v_reuseFailAlloc_3191_, 6, v_powFn_x3f_3180_);
lean_ctor_set(v_reuseFailAlloc_3191_, 7, v_natCastFn_x3f_3181_);
lean_ctor_set(v_reuseFailAlloc_3191_, 8, v___x_3188_);
lean_ctor_set(v_reuseFailAlloc_3191_, 9, v_vars_3183_);
lean_ctor_set(v_reuseFailAlloc_3191_, 10, v_varMap_3184_);
v___x_3190_ = v_reuseFailAlloc_3191_;
goto v_reusejp_3189_;
}
v_reusejp_3189_:
{
return v___x_3190_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__1___redArg(lean_object* v_cls_3193_, lean_object* v_msg_3194_, lean_object* v___y_3195_, lean_object* v___y_3196_, lean_object* v___y_3197_, lean_object* v___y_3198_){
_start:
{
lean_object* v_ref_3200_; lean_object* v___x_3201_; lean_object* v_a_3202_; lean_object* v___x_3204_; uint8_t v_isShared_3205_; uint8_t v_isSharedCheck_3246_; 
v_ref_3200_ = lean_ctor_get(v___y_3197_, 4);
v___x_3201_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1_spec__5_spec__8_spec__9(v_msg_3194_, v___y_3195_, v___y_3196_, v___y_3197_, v___y_3198_);
v_a_3202_ = lean_ctor_get(v___x_3201_, 0);
v_isSharedCheck_3246_ = !lean_is_exclusive(v___x_3201_);
if (v_isSharedCheck_3246_ == 0)
{
v___x_3204_ = v___x_3201_;
v_isShared_3205_ = v_isSharedCheck_3246_;
goto v_resetjp_3203_;
}
else
{
lean_inc(v_a_3202_);
lean_dec(v___x_3201_);
v___x_3204_ = lean_box(0);
v_isShared_3205_ = v_isSharedCheck_3246_;
goto v_resetjp_3203_;
}
v_resetjp_3203_:
{
lean_object* v___x_3206_; lean_object* v_traceState_3207_; lean_object* v_env_3208_; lean_object* v_nextMacroScope_3209_; lean_object* v_ngen_3210_; lean_object* v_auxDeclNGen_3211_; lean_object* v_cache_3212_; lean_object* v_messages_3213_; lean_object* v_infoState_3214_; lean_object* v_snapshotTasks_3215_; lean_object* v___x_3217_; uint8_t v_isShared_3218_; uint8_t v_isSharedCheck_3245_; 
v___x_3206_ = lean_st_ref_take(v___y_3198_);
v_traceState_3207_ = lean_ctor_get(v___x_3206_, 4);
v_env_3208_ = lean_ctor_get(v___x_3206_, 0);
v_nextMacroScope_3209_ = lean_ctor_get(v___x_3206_, 1);
v_ngen_3210_ = lean_ctor_get(v___x_3206_, 2);
v_auxDeclNGen_3211_ = lean_ctor_get(v___x_3206_, 3);
v_cache_3212_ = lean_ctor_get(v___x_3206_, 5);
v_messages_3213_ = lean_ctor_get(v___x_3206_, 6);
v_infoState_3214_ = lean_ctor_get(v___x_3206_, 7);
v_snapshotTasks_3215_ = lean_ctor_get(v___x_3206_, 8);
v_isSharedCheck_3245_ = !lean_is_exclusive(v___x_3206_);
if (v_isSharedCheck_3245_ == 0)
{
v___x_3217_ = v___x_3206_;
v_isShared_3218_ = v_isSharedCheck_3245_;
goto v_resetjp_3216_;
}
else
{
lean_inc(v_snapshotTasks_3215_);
lean_inc(v_infoState_3214_);
lean_inc(v_messages_3213_);
lean_inc(v_cache_3212_);
lean_inc(v_traceState_3207_);
lean_inc(v_auxDeclNGen_3211_);
lean_inc(v_ngen_3210_);
lean_inc(v_nextMacroScope_3209_);
lean_inc(v_env_3208_);
lean_dec(v___x_3206_);
v___x_3217_ = lean_box(0);
v_isShared_3218_ = v_isSharedCheck_3245_;
goto v_resetjp_3216_;
}
v_resetjp_3216_:
{
uint64_t v_tid_3219_; lean_object* v_traces_3220_; lean_object* v___x_3222_; uint8_t v_isShared_3223_; uint8_t v_isSharedCheck_3244_; 
v_tid_3219_ = lean_ctor_get_uint64(v_traceState_3207_, sizeof(void*)*1);
v_traces_3220_ = lean_ctor_get(v_traceState_3207_, 0);
v_isSharedCheck_3244_ = !lean_is_exclusive(v_traceState_3207_);
if (v_isSharedCheck_3244_ == 0)
{
v___x_3222_ = v_traceState_3207_;
v_isShared_3223_ = v_isSharedCheck_3244_;
goto v_resetjp_3221_;
}
else
{
lean_inc(v_traces_3220_);
lean_dec(v_traceState_3207_);
v___x_3222_ = lean_box(0);
v_isShared_3223_ = v_isSharedCheck_3244_;
goto v_resetjp_3221_;
}
v_resetjp_3221_:
{
lean_object* v___x_3224_; double v___x_3225_; uint8_t v___x_3226_; lean_object* v___x_3227_; lean_object* v___x_3228_; lean_object* v___x_3229_; lean_object* v___x_3230_; lean_object* v___x_3231_; lean_object* v___x_3232_; lean_object* v___x_3234_; 
v___x_3224_ = lean_box(0);
v___x_3225_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg___closed__0);
v___x_3226_ = 0;
v___x_3227_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg___closed__1));
v___x_3228_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3228_, 0, v_cls_3193_);
lean_ctor_set(v___x_3228_, 1, v___x_3224_);
lean_ctor_set(v___x_3228_, 2, v___x_3227_);
lean_ctor_set_float(v___x_3228_, sizeof(void*)*3, v___x_3225_);
lean_ctor_set_float(v___x_3228_, sizeof(void*)*3 + 8, v___x_3225_);
lean_ctor_set_uint8(v___x_3228_, sizeof(void*)*3 + 16, v___x_3226_);
v___x_3229_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg___closed__2));
v___x_3230_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3230_, 0, v___x_3228_);
lean_ctor_set(v___x_3230_, 1, v_a_3202_);
lean_ctor_set(v___x_3230_, 2, v___x_3229_);
lean_inc(v_ref_3200_);
v___x_3231_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3231_, 0, v_ref_3200_);
lean_ctor_set(v___x_3231_, 1, v___x_3230_);
v___x_3232_ = l_Lean_PersistentArray_push___redArg(v_traces_3220_, v___x_3231_);
if (v_isShared_3223_ == 0)
{
lean_ctor_set(v___x_3222_, 0, v___x_3232_);
v___x_3234_ = v___x_3222_;
goto v_reusejp_3233_;
}
else
{
lean_object* v_reuseFailAlloc_3243_; 
v_reuseFailAlloc_3243_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3243_, 0, v___x_3232_);
lean_ctor_set_uint64(v_reuseFailAlloc_3243_, sizeof(void*)*1, v_tid_3219_);
v___x_3234_ = v_reuseFailAlloc_3243_;
goto v_reusejp_3233_;
}
v_reusejp_3233_:
{
lean_object* v___x_3236_; 
if (v_isShared_3218_ == 0)
{
lean_ctor_set(v___x_3217_, 4, v___x_3234_);
v___x_3236_ = v___x_3217_;
goto v_reusejp_3235_;
}
else
{
lean_object* v_reuseFailAlloc_3242_; 
v_reuseFailAlloc_3242_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3242_, 0, v_env_3208_);
lean_ctor_set(v_reuseFailAlloc_3242_, 1, v_nextMacroScope_3209_);
lean_ctor_set(v_reuseFailAlloc_3242_, 2, v_ngen_3210_);
lean_ctor_set(v_reuseFailAlloc_3242_, 3, v_auxDeclNGen_3211_);
lean_ctor_set(v_reuseFailAlloc_3242_, 4, v___x_3234_);
lean_ctor_set(v_reuseFailAlloc_3242_, 5, v_cache_3212_);
lean_ctor_set(v_reuseFailAlloc_3242_, 6, v_messages_3213_);
lean_ctor_set(v_reuseFailAlloc_3242_, 7, v_infoState_3214_);
lean_ctor_set(v_reuseFailAlloc_3242_, 8, v_snapshotTasks_3215_);
v___x_3236_ = v_reuseFailAlloc_3242_;
goto v_reusejp_3235_;
}
v_reusejp_3235_:
{
lean_object* v___x_3237_; lean_object* v___x_3238_; lean_object* v___x_3240_; 
v___x_3237_ = lean_st_ref_put(v___y_3198_, v___x_3236_);
v___x_3238_ = lean_box(0);
if (v_isShared_3205_ == 0)
{
lean_ctor_set(v___x_3204_, 0, v___x_3238_);
v___x_3240_ = v___x_3204_;
goto v_reusejp_3239_;
}
else
{
lean_object* v_reuseFailAlloc_3241_; 
v_reuseFailAlloc_3241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3241_, 0, v___x_3238_);
v___x_3240_ = v_reuseFailAlloc_3241_;
goto v_reusejp_3239_;
}
v_reusejp_3239_:
{
return v___x_3240_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__1___redArg___boxed(lean_object* v_cls_3247_, lean_object* v_msg_3248_, lean_object* v___y_3249_, lean_object* v___y_3250_, lean_object* v___y_3251_, lean_object* v___y_3252_, lean_object* v___y_3253_){
_start:
{
lean_object* v_res_3254_; 
v_res_3254_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__1___redArg(v_cls_3247_, v_msg_3248_, v___y_3249_, v___y_3250_, v___y_3251_, v___y_3252_);
lean_dec(v___y_3252_);
lean_dec_ref(v___y_3251_);
lean_dec(v___y_3250_);
lean_dec_ref(v___y_3249_);
return v_res_3254_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__2___redArg(lean_object* v_cls_3255_, lean_object* v_msg_3256_, lean_object* v___y_3257_, lean_object* v___y_3258_, lean_object* v___y_3259_, lean_object* v___y_3260_){
_start:
{
lean_object* v_ref_3262_; lean_object* v___x_3263_; lean_object* v_a_3264_; lean_object* v___x_3266_; uint8_t v_isShared_3267_; uint8_t v_isSharedCheck_3308_; 
v_ref_3262_ = lean_ctor_get(v___y_3259_, 4);
v___x_3263_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1_spec__5_spec__8_spec__9(v_msg_3256_, v___y_3257_, v___y_3258_, v___y_3259_, v___y_3260_);
v_a_3264_ = lean_ctor_get(v___x_3263_, 0);
v_isSharedCheck_3308_ = !lean_is_exclusive(v___x_3263_);
if (v_isSharedCheck_3308_ == 0)
{
v___x_3266_ = v___x_3263_;
v_isShared_3267_ = v_isSharedCheck_3308_;
goto v_resetjp_3265_;
}
else
{
lean_inc(v_a_3264_);
lean_dec(v___x_3263_);
v___x_3266_ = lean_box(0);
v_isShared_3267_ = v_isSharedCheck_3308_;
goto v_resetjp_3265_;
}
v_resetjp_3265_:
{
lean_object* v___x_3268_; lean_object* v_traceState_3269_; lean_object* v_env_3270_; lean_object* v_nextMacroScope_3271_; lean_object* v_ngen_3272_; lean_object* v_auxDeclNGen_3273_; lean_object* v_cache_3274_; lean_object* v_messages_3275_; lean_object* v_infoState_3276_; lean_object* v_snapshotTasks_3277_; lean_object* v___x_3279_; uint8_t v_isShared_3280_; uint8_t v_isSharedCheck_3307_; 
v___x_3268_ = lean_st_ref_take(v___y_3260_);
v_traceState_3269_ = lean_ctor_get(v___x_3268_, 4);
v_env_3270_ = lean_ctor_get(v___x_3268_, 0);
v_nextMacroScope_3271_ = lean_ctor_get(v___x_3268_, 1);
v_ngen_3272_ = lean_ctor_get(v___x_3268_, 2);
v_auxDeclNGen_3273_ = lean_ctor_get(v___x_3268_, 3);
v_cache_3274_ = lean_ctor_get(v___x_3268_, 5);
v_messages_3275_ = lean_ctor_get(v___x_3268_, 6);
v_infoState_3276_ = lean_ctor_get(v___x_3268_, 7);
v_snapshotTasks_3277_ = lean_ctor_get(v___x_3268_, 8);
v_isSharedCheck_3307_ = !lean_is_exclusive(v___x_3268_);
if (v_isSharedCheck_3307_ == 0)
{
v___x_3279_ = v___x_3268_;
v_isShared_3280_ = v_isSharedCheck_3307_;
goto v_resetjp_3278_;
}
else
{
lean_inc(v_snapshotTasks_3277_);
lean_inc(v_infoState_3276_);
lean_inc(v_messages_3275_);
lean_inc(v_cache_3274_);
lean_inc(v_traceState_3269_);
lean_inc(v_auxDeclNGen_3273_);
lean_inc(v_ngen_3272_);
lean_inc(v_nextMacroScope_3271_);
lean_inc(v_env_3270_);
lean_dec(v___x_3268_);
v___x_3279_ = lean_box(0);
v_isShared_3280_ = v_isSharedCheck_3307_;
goto v_resetjp_3278_;
}
v_resetjp_3278_:
{
uint64_t v_tid_3281_; lean_object* v_traces_3282_; lean_object* v___x_3284_; uint8_t v_isShared_3285_; uint8_t v_isSharedCheck_3306_; 
v_tid_3281_ = lean_ctor_get_uint64(v_traceState_3269_, sizeof(void*)*1);
v_traces_3282_ = lean_ctor_get(v_traceState_3269_, 0);
v_isSharedCheck_3306_ = !lean_is_exclusive(v_traceState_3269_);
if (v_isSharedCheck_3306_ == 0)
{
v___x_3284_ = v_traceState_3269_;
v_isShared_3285_ = v_isSharedCheck_3306_;
goto v_resetjp_3283_;
}
else
{
lean_inc(v_traces_3282_);
lean_dec(v_traceState_3269_);
v___x_3284_ = lean_box(0);
v_isShared_3285_ = v_isSharedCheck_3306_;
goto v_resetjp_3283_;
}
v_resetjp_3283_:
{
lean_object* v___x_3286_; double v___x_3287_; uint8_t v___x_3288_; lean_object* v___x_3289_; lean_object* v___x_3290_; lean_object* v___x_3291_; lean_object* v___x_3292_; lean_object* v___x_3293_; lean_object* v___x_3294_; lean_object* v___x_3296_; 
v___x_3286_ = lean_box(0);
v___x_3287_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg___closed__0);
v___x_3288_ = 0;
v___x_3289_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg___closed__1));
v___x_3290_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3290_, 0, v_cls_3255_);
lean_ctor_set(v___x_3290_, 1, v___x_3286_);
lean_ctor_set(v___x_3290_, 2, v___x_3289_);
lean_ctor_set_float(v___x_3290_, sizeof(void*)*3, v___x_3287_);
lean_ctor_set_float(v___x_3290_, sizeof(void*)*3 + 8, v___x_3287_);
lean_ctor_set_uint8(v___x_3290_, sizeof(void*)*3 + 16, v___x_3288_);
v___x_3291_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg___closed__2));
v___x_3292_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3292_, 0, v___x_3290_);
lean_ctor_set(v___x_3292_, 1, v_a_3264_);
lean_ctor_set(v___x_3292_, 2, v___x_3291_);
lean_inc(v_ref_3262_);
v___x_3293_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3293_, 0, v_ref_3262_);
lean_ctor_set(v___x_3293_, 1, v___x_3292_);
v___x_3294_ = l_Lean_PersistentArray_push___redArg(v_traces_3282_, v___x_3293_);
if (v_isShared_3285_ == 0)
{
lean_ctor_set(v___x_3284_, 0, v___x_3294_);
v___x_3296_ = v___x_3284_;
goto v_reusejp_3295_;
}
else
{
lean_object* v_reuseFailAlloc_3305_; 
v_reuseFailAlloc_3305_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3305_, 0, v___x_3294_);
lean_ctor_set_uint64(v_reuseFailAlloc_3305_, sizeof(void*)*1, v_tid_3281_);
v___x_3296_ = v_reuseFailAlloc_3305_;
goto v_reusejp_3295_;
}
v_reusejp_3295_:
{
lean_object* v___x_3298_; 
if (v_isShared_3280_ == 0)
{
lean_ctor_set(v___x_3279_, 4, v___x_3296_);
v___x_3298_ = v___x_3279_;
goto v_reusejp_3297_;
}
else
{
lean_object* v_reuseFailAlloc_3304_; 
v_reuseFailAlloc_3304_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3304_, 0, v_env_3270_);
lean_ctor_set(v_reuseFailAlloc_3304_, 1, v_nextMacroScope_3271_);
lean_ctor_set(v_reuseFailAlloc_3304_, 2, v_ngen_3272_);
lean_ctor_set(v_reuseFailAlloc_3304_, 3, v_auxDeclNGen_3273_);
lean_ctor_set(v_reuseFailAlloc_3304_, 4, v___x_3296_);
lean_ctor_set(v_reuseFailAlloc_3304_, 5, v_cache_3274_);
lean_ctor_set(v_reuseFailAlloc_3304_, 6, v_messages_3275_);
lean_ctor_set(v_reuseFailAlloc_3304_, 7, v_infoState_3276_);
lean_ctor_set(v_reuseFailAlloc_3304_, 8, v_snapshotTasks_3277_);
v___x_3298_ = v_reuseFailAlloc_3304_;
goto v_reusejp_3297_;
}
v_reusejp_3297_:
{
lean_object* v___x_3299_; lean_object* v___x_3300_; lean_object* v___x_3302_; 
v___x_3299_ = lean_st_ref_put(v___y_3260_, v___x_3298_);
v___x_3300_ = lean_box(0);
if (v_isShared_3267_ == 0)
{
lean_ctor_set(v___x_3266_, 0, v___x_3300_);
v___x_3302_ = v___x_3266_;
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
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__2___redArg___boxed(lean_object* v_cls_3309_, lean_object* v_msg_3310_, lean_object* v___y_3311_, lean_object* v___y_3312_, lean_object* v___y_3313_, lean_object* v___y_3314_, lean_object* v___y_3315_){
_start:
{
lean_object* v_res_3316_; 
v_res_3316_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__2___redArg(v_cls_3309_, v_msg_3310_, v___y_3311_, v___y_3312_, v___y_3313_, v___y_3314_);
lean_dec(v___y_3314_);
lean_dec_ref(v___y_3313_);
lean_dec(v___y_3312_);
lean_dec_ref(v___y_3311_);
return v_res_3316_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__3___redArg(lean_object* v_cls_3317_, lean_object* v_msg_3318_, lean_object* v___y_3319_, lean_object* v___y_3320_, lean_object* v___y_3321_, lean_object* v___y_3322_){
_start:
{
lean_object* v_ref_3324_; lean_object* v___x_3325_; lean_object* v_a_3326_; lean_object* v___x_3328_; uint8_t v_isShared_3329_; uint8_t v_isSharedCheck_3370_; 
v_ref_3324_ = lean_ctor_get(v___y_3321_, 4);
v___x_3325_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1_spec__5_spec__8_spec__9(v_msg_3318_, v___y_3319_, v___y_3320_, v___y_3321_, v___y_3322_);
v_a_3326_ = lean_ctor_get(v___x_3325_, 0);
v_isSharedCheck_3370_ = !lean_is_exclusive(v___x_3325_);
if (v_isSharedCheck_3370_ == 0)
{
v___x_3328_ = v___x_3325_;
v_isShared_3329_ = v_isSharedCheck_3370_;
goto v_resetjp_3327_;
}
else
{
lean_inc(v_a_3326_);
lean_dec(v___x_3325_);
v___x_3328_ = lean_box(0);
v_isShared_3329_ = v_isSharedCheck_3370_;
goto v_resetjp_3327_;
}
v_resetjp_3327_:
{
lean_object* v___x_3330_; lean_object* v_traceState_3331_; lean_object* v_env_3332_; lean_object* v_nextMacroScope_3333_; lean_object* v_ngen_3334_; lean_object* v_auxDeclNGen_3335_; lean_object* v_cache_3336_; lean_object* v_messages_3337_; lean_object* v_infoState_3338_; lean_object* v_snapshotTasks_3339_; lean_object* v___x_3341_; uint8_t v_isShared_3342_; uint8_t v_isSharedCheck_3369_; 
v___x_3330_ = lean_st_ref_take(v___y_3322_);
v_traceState_3331_ = lean_ctor_get(v___x_3330_, 4);
v_env_3332_ = lean_ctor_get(v___x_3330_, 0);
v_nextMacroScope_3333_ = lean_ctor_get(v___x_3330_, 1);
v_ngen_3334_ = lean_ctor_get(v___x_3330_, 2);
v_auxDeclNGen_3335_ = lean_ctor_get(v___x_3330_, 3);
v_cache_3336_ = lean_ctor_get(v___x_3330_, 5);
v_messages_3337_ = lean_ctor_get(v___x_3330_, 6);
v_infoState_3338_ = lean_ctor_get(v___x_3330_, 7);
v_snapshotTasks_3339_ = lean_ctor_get(v___x_3330_, 8);
v_isSharedCheck_3369_ = !lean_is_exclusive(v___x_3330_);
if (v_isSharedCheck_3369_ == 0)
{
v___x_3341_ = v___x_3330_;
v_isShared_3342_ = v_isSharedCheck_3369_;
goto v_resetjp_3340_;
}
else
{
lean_inc(v_snapshotTasks_3339_);
lean_inc(v_infoState_3338_);
lean_inc(v_messages_3337_);
lean_inc(v_cache_3336_);
lean_inc(v_traceState_3331_);
lean_inc(v_auxDeclNGen_3335_);
lean_inc(v_ngen_3334_);
lean_inc(v_nextMacroScope_3333_);
lean_inc(v_env_3332_);
lean_dec(v___x_3330_);
v___x_3341_ = lean_box(0);
v_isShared_3342_ = v_isSharedCheck_3369_;
goto v_resetjp_3340_;
}
v_resetjp_3340_:
{
uint64_t v_tid_3343_; lean_object* v_traces_3344_; lean_object* v___x_3346_; uint8_t v_isShared_3347_; uint8_t v_isSharedCheck_3368_; 
v_tid_3343_ = lean_ctor_get_uint64(v_traceState_3331_, sizeof(void*)*1);
v_traces_3344_ = lean_ctor_get(v_traceState_3331_, 0);
v_isSharedCheck_3368_ = !lean_is_exclusive(v_traceState_3331_);
if (v_isSharedCheck_3368_ == 0)
{
v___x_3346_ = v_traceState_3331_;
v_isShared_3347_ = v_isSharedCheck_3368_;
goto v_resetjp_3345_;
}
else
{
lean_inc(v_traces_3344_);
lean_dec(v_traceState_3331_);
v___x_3346_ = lean_box(0);
v_isShared_3347_ = v_isSharedCheck_3368_;
goto v_resetjp_3345_;
}
v_resetjp_3345_:
{
lean_object* v___x_3348_; double v___x_3349_; uint8_t v___x_3350_; lean_object* v___x_3351_; lean_object* v___x_3352_; lean_object* v___x_3353_; lean_object* v___x_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; lean_object* v___x_3358_; 
v___x_3348_ = lean_box(0);
v___x_3349_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg___closed__0);
v___x_3350_ = 0;
v___x_3351_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg___closed__1));
v___x_3352_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3352_, 0, v_cls_3317_);
lean_ctor_set(v___x_3352_, 1, v___x_3348_);
lean_ctor_set(v___x_3352_, 2, v___x_3351_);
lean_ctor_set_float(v___x_3352_, sizeof(void*)*3, v___x_3349_);
lean_ctor_set_float(v___x_3352_, sizeof(void*)*3 + 8, v___x_3349_);
lean_ctor_set_uint8(v___x_3352_, sizeof(void*)*3 + 16, v___x_3350_);
v___x_3353_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg___closed__2));
v___x_3354_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3354_, 0, v___x_3352_);
lean_ctor_set(v___x_3354_, 1, v_a_3326_);
lean_ctor_set(v___x_3354_, 2, v___x_3353_);
lean_inc(v_ref_3324_);
v___x_3355_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3355_, 0, v_ref_3324_);
lean_ctor_set(v___x_3355_, 1, v___x_3354_);
v___x_3356_ = l_Lean_PersistentArray_push___redArg(v_traces_3344_, v___x_3355_);
if (v_isShared_3347_ == 0)
{
lean_ctor_set(v___x_3346_, 0, v___x_3356_);
v___x_3358_ = v___x_3346_;
goto v_reusejp_3357_;
}
else
{
lean_object* v_reuseFailAlloc_3367_; 
v_reuseFailAlloc_3367_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3367_, 0, v___x_3356_);
lean_ctor_set_uint64(v_reuseFailAlloc_3367_, sizeof(void*)*1, v_tid_3343_);
v___x_3358_ = v_reuseFailAlloc_3367_;
goto v_reusejp_3357_;
}
v_reusejp_3357_:
{
lean_object* v___x_3360_; 
if (v_isShared_3342_ == 0)
{
lean_ctor_set(v___x_3341_, 4, v___x_3358_);
v___x_3360_ = v___x_3341_;
goto v_reusejp_3359_;
}
else
{
lean_object* v_reuseFailAlloc_3366_; 
v_reuseFailAlloc_3366_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3366_, 0, v_env_3332_);
lean_ctor_set(v_reuseFailAlloc_3366_, 1, v_nextMacroScope_3333_);
lean_ctor_set(v_reuseFailAlloc_3366_, 2, v_ngen_3334_);
lean_ctor_set(v_reuseFailAlloc_3366_, 3, v_auxDeclNGen_3335_);
lean_ctor_set(v_reuseFailAlloc_3366_, 4, v___x_3358_);
lean_ctor_set(v_reuseFailAlloc_3366_, 5, v_cache_3336_);
lean_ctor_set(v_reuseFailAlloc_3366_, 6, v_messages_3337_);
lean_ctor_set(v_reuseFailAlloc_3366_, 7, v_infoState_3338_);
lean_ctor_set(v_reuseFailAlloc_3366_, 8, v_snapshotTasks_3339_);
v___x_3360_ = v_reuseFailAlloc_3366_;
goto v_reusejp_3359_;
}
v_reusejp_3359_:
{
lean_object* v___x_3361_; lean_object* v___x_3362_; lean_object* v___x_3364_; 
v___x_3361_ = lean_st_ref_put(v___y_3322_, v___x_3360_);
v___x_3362_ = lean_box(0);
if (v_isShared_3329_ == 0)
{
lean_ctor_set(v___x_3328_, 0, v___x_3362_);
v___x_3364_ = v___x_3328_;
goto v_reusejp_3363_;
}
else
{
lean_object* v_reuseFailAlloc_3365_; 
v_reuseFailAlloc_3365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3365_, 0, v___x_3362_);
v___x_3364_ = v_reuseFailAlloc_3365_;
goto v_reusejp_3363_;
}
v_reusejp_3363_:
{
return v___x_3364_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__3___redArg___boxed(lean_object* v_cls_3371_, lean_object* v_msg_3372_, lean_object* v___y_3373_, lean_object* v___y_3374_, lean_object* v___y_3375_, lean_object* v___y_3376_, lean_object* v___y_3377_){
_start:
{
lean_object* v_res_3378_; 
v_res_3378_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__3___redArg(v_cls_3371_, v_msg_3372_, v___y_3373_, v___y_3374_, v___y_3375_, v___y_3376_);
lean_dec(v___y_3376_);
lean_dec_ref(v___y_3375_);
lean_dec(v___y_3374_);
lean_dec_ref(v___y_3373_);
return v_res_3378_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__2(void){
_start:
{
lean_object* v___x_3384_; lean_object* v___x_3385_; lean_object* v___x_3386_; 
v___x_3384_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__1));
v___x_3385_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__7));
v___x_3386_ = l_Lean_Name_append(v___x_3385_, v___x_3384_);
return v___x_3386_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__4(void){
_start:
{
lean_object* v___x_3388_; lean_object* v___x_3389_; 
v___x_3388_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__3));
v___x_3389_ = l_Lean_stringToMessageData(v___x_3388_);
return v___x_3389_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__6(void){
_start:
{
lean_object* v___x_3391_; lean_object* v___x_3392_; 
v___x_3391_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__5));
v___x_3392_ = l_Lean_stringToMessageData(v___x_3391_);
return v___x_3392_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__8(void){
_start:
{
lean_object* v___x_3394_; lean_object* v___x_3395_; 
v___x_3394_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__7));
v___x_3395_ = l_Lean_stringToMessageData(v___x_3394_);
return v___x_3395_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__10(void){
_start:
{
lean_object* v___x_3397_; lean_object* v___x_3398_; 
v___x_3397_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__9));
v___x_3398_ = l_Lean_stringToMessageData(v___x_3397_);
return v___x_3398_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__12(void){
_start:
{
lean_object* v___x_3400_; lean_object* v___x_3401_; 
v___x_3400_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__11));
v___x_3401_ = l_Lean_stringToMessageData(v___x_3400_);
return v___x_3401_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_internalize(lean_object* v_e_3402_, lean_object* v_parent_x3f_3403_, lean_object* v_a_3404_, lean_object* v_a_3405_, lean_object* v_a_3406_, lean_object* v_a_3407_, lean_object* v_a_3408_, lean_object* v_a_3409_, lean_object* v_a_3410_, lean_object* v_a_3411_, lean_object* v_a_3412_, lean_object* v_a_3413_){
_start:
{
lean_object* v___x_3415_; 
v___x_3415_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_3406_);
if (lean_obj_tag(v___x_3415_) == 0)
{
lean_object* v_a_3416_; lean_object* v___x_3418_; uint8_t v_isShared_3419_; uint8_t v_isSharedCheck_3760_; 
v_a_3416_ = lean_ctor_get(v___x_3415_, 0);
v_isSharedCheck_3760_ = !lean_is_exclusive(v___x_3415_);
if (v_isSharedCheck_3760_ == 0)
{
v___x_3418_ = v___x_3415_;
v_isShared_3419_ = v_isSharedCheck_3760_;
goto v_resetjp_3417_;
}
else
{
lean_inc(v_a_3416_);
lean_dec(v___x_3415_);
v___x_3418_ = lean_box(0);
v_isShared_3419_ = v_isSharedCheck_3760_;
goto v_resetjp_3417_;
}
v_resetjp_3417_:
{
uint8_t v_ring_3420_; 
v_ring_3420_ = lean_ctor_get_uint8(v_a_3416_, sizeof(void*)*14 + 21);
lean_dec(v_a_3416_);
if (v_ring_3420_ == 0)
{
lean_object* v___x_3421_; lean_object* v___x_3423_; 
lean_dec(v_parent_x3f_3403_);
lean_dec_ref(v_e_3402_);
v___x_3421_ = lean_box(0);
if (v_isShared_3419_ == 0)
{
lean_ctor_set(v___x_3418_, 0, v___x_3421_);
v___x_3423_ = v___x_3418_;
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
else
{
uint8_t v___x_3425_; 
v___x_3425_ = l_Lean_Meta_Grind_Arith_isIntModuleVirtualParent(v_parent_x3f_3403_);
if (v___x_3425_ == 0)
{
lean_object* v___x_3426_; 
lean_del_object(v___x_3418_);
lean_inc_ref(v_e_3402_);
v___x_3426_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeInv(v_e_3402_, v_a_3404_, v_a_3405_, v_a_3406_, v_a_3407_, v_a_3408_, v_a_3409_, v_a_3410_, v_a_3411_, v_a_3412_, v_a_3413_);
if (lean_obj_tag(v___x_3426_) == 0)
{
lean_object* v_a_3427_; lean_object* v___x_3429_; uint8_t v_isShared_3430_; uint8_t v_isSharedCheck_3747_; 
v_a_3427_ = lean_ctor_get(v___x_3426_, 0);
v_isSharedCheck_3747_ = !lean_is_exclusive(v___x_3426_);
if (v_isSharedCheck_3747_ == 0)
{
v___x_3429_ = v___x_3426_;
v_isShared_3430_ = v_isSharedCheck_3747_;
goto v_resetjp_3428_;
}
else
{
lean_inc(v_a_3427_);
lean_dec(v___x_3426_);
v___x_3429_ = lean_box(0);
v_isShared_3430_ = v_isSharedCheck_3747_;
goto v_resetjp_3428_;
}
v_resetjp_3428_:
{
uint8_t v___x_3431_; 
v___x_3431_ = lean_unbox(v_a_3427_);
lean_dec(v_a_3427_);
if (v___x_3431_ == 0)
{
lean_object* v___x_3432_; 
lean_inc_ref(v_e_3402_);
v___x_3432_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f(v_e_3402_);
if (lean_obj_tag(v___x_3432_) == 1)
{
lean_object* v_val_3433_; uint8_t v___x_3434_; 
v_val_3433_ = lean_ctor_get(v___x_3432_, 0);
lean_inc(v_val_3433_);
lean_dec_ref_known(v___x_3432_, 1);
v___x_3434_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isForbiddenParent(v_parent_x3f_3403_);
if (v___x_3434_ == 0)
{
lean_object* v___x_3435_; 
lean_del_object(v___x_3429_);
lean_inc(v_val_3433_);
v___x_3435_ = l_Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f(v_val_3433_, v_a_3404_, v_a_3405_, v_a_3406_, v_a_3407_, v_a_3408_, v_a_3409_, v_a_3410_, v_a_3411_, v_a_3412_, v_a_3413_);
if (lean_obj_tag(v___x_3435_) == 0)
{
lean_object* v_a_3436_; 
v_a_3436_ = lean_ctor_get(v___x_3435_, 0);
lean_inc(v_a_3436_);
lean_dec_ref_known(v___x_3435_, 1);
if (lean_obj_tag(v_a_3436_) == 1)
{
lean_object* v_val_3437_; lean_object* v___x_3438_; lean_object* v___x_3439_; lean_object* v___x_3440_; 
lean_dec(v_val_3433_);
v_val_3437_ = lean_ctor_get(v_a_3436_, 0);
lean_inc_n(v_val_3437_, 2);
lean_dec_ref_known(v_a_3436_, 1);
v___x_3438_ = lean_unsigned_to_nat(0u);
v___x_3439_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3439_, 0, v_val_3437_);
lean_ctor_set_uint8(v___x_3439_, sizeof(void*)*1, v___x_3434_);
lean_inc_ref(v_e_3402_);
v___x_3440_ = l_Lean_Meta_Grind_Arith_CommRing_reify_x3f(v_e_3402_, v_ring_3420_, v___x_3438_, v___x_3439_, v_a_3404_, v_a_3405_, v_a_3406_, v_a_3407_, v_a_3408_, v_a_3409_, v_a_3410_, v_a_3411_, v_a_3412_, v_a_3413_);
if (lean_obj_tag(v___x_3440_) == 0)
{
lean_object* v_a_3441_; lean_object* v___x_3443_; uint8_t v_isShared_3444_; uint8_t v_isSharedCheck_3493_; 
v_a_3441_ = lean_ctor_get(v___x_3440_, 0);
v_isSharedCheck_3493_ = !lean_is_exclusive(v___x_3440_);
if (v_isSharedCheck_3493_ == 0)
{
v___x_3443_ = v___x_3440_;
v_isShared_3444_ = v_isSharedCheck_3493_;
goto v_resetjp_3442_;
}
else
{
lean_inc(v_a_3441_);
lean_dec(v___x_3440_);
v___x_3443_ = lean_box(0);
v_isShared_3444_ = v_isSharedCheck_3493_;
goto v_resetjp_3442_;
}
v_resetjp_3442_:
{
if (lean_obj_tag(v_a_3441_) == 1)
{
lean_object* v_options_3445_; lean_object* v_val_3446_; lean_object* v_toCold_3447_; uint8_t v_hasTrace_3448_; lean_object* v___f_3449_; lean_object* v___y_3451_; lean_object* v___y_3452_; lean_object* v___y_3453_; lean_object* v___y_3454_; lean_object* v___y_3455_; lean_object* v___y_3456_; lean_object* v___y_3457_; lean_object* v___y_3458_; lean_object* v___y_3459_; lean_object* v___y_3460_; lean_object* v___y_3461_; 
lean_del_object(v___x_3443_);
v_options_3445_ = lean_ctor_get(v_a_3412_, 1);
v_val_3446_ = lean_ctor_get(v_a_3441_, 0);
lean_inc(v_val_3446_);
lean_dec_ref_known(v_a_3441_, 1);
v_toCold_3447_ = lean_ctor_get(v_a_3412_, 0);
v_hasTrace_3448_ = lean_ctor_get_uint8(v_options_3445_, sizeof(void*)*1);
lean_inc_ref(v_e_3402_);
v___f_3449_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_internalize___lam__0), 3, 2);
lean_closure_set(v___f_3449_, 0, v_e_3402_);
lean_closure_set(v___f_3449_, 1, v_val_3446_);
if (v_hasTrace_3448_ == 0)
{
lean_dec(v_val_3437_);
v___y_3451_ = v___x_3439_;
v___y_3452_ = v_a_3404_;
v___y_3453_ = v_a_3405_;
v___y_3454_ = v_a_3406_;
v___y_3455_ = v_a_3407_;
v___y_3456_ = v_a_3408_;
v___y_3457_ = v_a_3409_;
v___y_3458_ = v_a_3410_;
v___y_3459_ = v_a_3411_;
v___y_3460_ = v_a_3412_;
v___y_3461_ = v_a_3413_;
goto v___jp_3450_;
}
else
{
lean_object* v_inheritedTraceOptions_3467_; lean_object* v___x_3468_; lean_object* v___x_3469_; uint8_t v___x_3470_; 
v_inheritedTraceOptions_3467_ = lean_ctor_get(v_toCold_3447_, 4);
v___x_3468_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__1));
v___x_3469_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__2, &l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__2_once, _init_l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__2);
v___x_3470_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3467_, v_options_3445_, v___x_3469_);
if (v___x_3470_ == 0)
{
lean_dec(v_val_3437_);
v___y_3451_ = v___x_3439_;
v___y_3452_ = v_a_3404_;
v___y_3453_ = v_a_3405_;
v___y_3454_ = v_a_3406_;
v___y_3455_ = v_a_3407_;
v___y_3456_ = v_a_3408_;
v___y_3457_ = v_a_3409_;
v___y_3458_ = v_a_3410_;
v___y_3459_ = v_a_3411_;
v___y_3460_ = v_a_3412_;
v___y_3461_ = v_a_3413_;
goto v___jp_3450_;
}
else
{
lean_object* v___x_3471_; 
v___x_3471_ = l_Lean_Meta_Grind_updateLastTag(v_a_3404_, v_a_3405_, v_a_3406_, v_a_3407_, v_a_3408_, v_a_3409_, v_a_3410_, v_a_3411_, v_a_3412_, v_a_3413_);
if (lean_obj_tag(v___x_3471_) == 0)
{
lean_object* v___x_3473_; uint8_t v_isShared_3474_; uint8_t v_isSharedCheck_3487_; 
v_isSharedCheck_3487_ = !lean_is_exclusive(v___x_3471_);
if (v_isSharedCheck_3487_ == 0)
{
lean_object* v_unused_3488_; 
v_unused_3488_ = lean_ctor_get(v___x_3471_, 0);
lean_dec(v_unused_3488_);
v___x_3473_ = v___x_3471_;
v_isShared_3474_ = v_isSharedCheck_3487_;
goto v_resetjp_3472_;
}
else
{
lean_dec(v___x_3471_);
v___x_3473_ = lean_box(0);
v_isShared_3474_ = v_isSharedCheck_3487_;
goto v_resetjp_3472_;
}
v_resetjp_3472_:
{
lean_object* v___x_3475_; lean_object* v___x_3476_; lean_object* v___x_3478_; 
v___x_3475_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__4, &l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__4_once, _init_l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__4);
v___x_3476_ = l_Nat_reprFast(v_val_3437_);
if (v_isShared_3474_ == 0)
{
lean_ctor_set_tag(v___x_3473_, 3);
lean_ctor_set(v___x_3473_, 0, v___x_3476_);
v___x_3478_ = v___x_3473_;
goto v_reusejp_3477_;
}
else
{
lean_object* v_reuseFailAlloc_3486_; 
v_reuseFailAlloc_3486_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3486_, 0, v___x_3476_);
v___x_3478_ = v_reuseFailAlloc_3486_;
goto v_reusejp_3477_;
}
v_reusejp_3477_:
{
lean_object* v___x_3479_; lean_object* v___x_3480_; lean_object* v___x_3481_; lean_object* v___x_3482_; lean_object* v___x_3483_; lean_object* v___x_3484_; lean_object* v___x_3485_; 
v___x_3479_ = l_Lean_MessageData_ofFormat(v___x_3478_);
v___x_3480_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3480_, 0, v___x_3475_);
lean_ctor_set(v___x_3480_, 1, v___x_3479_);
v___x_3481_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__6, &l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__6_once, _init_l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__6);
v___x_3482_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3482_, 0, v___x_3480_);
lean_ctor_set(v___x_3482_, 1, v___x_3481_);
lean_inc_ref(v_e_3402_);
v___x_3483_ = l_Lean_MessageData_ofExpr(v_e_3402_);
v___x_3484_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3484_, 0, v___x_3482_);
lean_ctor_set(v___x_3484_, 1, v___x_3483_);
v___x_3485_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg(v___x_3468_, v___x_3484_, v_a_3410_, v_a_3411_, v_a_3412_, v_a_3413_);
if (lean_obj_tag(v___x_3485_) == 0)
{
lean_dec_ref_known(v___x_3485_, 1);
v___y_3451_ = v___x_3439_;
v___y_3452_ = v_a_3404_;
v___y_3453_ = v_a_3405_;
v___y_3454_ = v_a_3406_;
v___y_3455_ = v_a_3407_;
v___y_3456_ = v_a_3408_;
v___y_3457_ = v_a_3409_;
v___y_3458_ = v_a_3410_;
v___y_3459_ = v_a_3411_;
v___y_3460_ = v_a_3412_;
v___y_3461_ = v_a_3413_;
goto v___jp_3450_;
}
else
{
lean_dec_ref(v___f_3449_);
lean_dec_ref_known(v___x_3439_, 1);
lean_dec_ref(v_e_3402_);
return v___x_3485_;
}
}
}
}
else
{
lean_dec_ref(v___f_3449_);
lean_dec_ref_known(v___x_3439_, 1);
lean_dec(v_val_3437_);
lean_dec_ref(v_e_3402_);
return v___x_3471_;
}
}
}
v___jp_3450_:
{
lean_object* v___x_3462_; 
lean_inc_ref(v_e_3402_);
v___x_3462_ = l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg(v_e_3402_, v___y_3451_, v___y_3452_, v___y_3456_, v___y_3457_, v___y_3458_, v___y_3459_, v___y_3460_, v___y_3461_);
if (lean_obj_tag(v___x_3462_) == 0)
{
lean_object* v___x_3463_; lean_object* v___x_3464_; 
lean_dec_ref_known(v___x_3462_, 1);
v___x_3463_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_3464_ = l_Lean_Meta_Grind_SolverExtension_markTerm___redArg(v___x_3463_, v_e_3402_, v___y_3452_, v___y_3453_, v___y_3454_, v___y_3455_, v___y_3456_, v___y_3457_, v___y_3458_, v___y_3459_, v___y_3460_, v___y_3461_);
if (lean_obj_tag(v___x_3464_) == 0)
{
lean_object* v___x_3465_; 
lean_dec_ref_known(v___x_3464_, 1);
v___x_3465_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(v___f_3449_, v___y_3451_, v___y_3452_);
if (lean_obj_tag(v___x_3465_) == 0)
{
lean_object* v___x_3466_; 
lean_dec_ref_known(v___x_3465_, 1);
v___x_3466_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars(v___y_3451_, v___y_3452_, v___y_3453_, v___y_3454_, v___y_3455_, v___y_3456_, v___y_3457_, v___y_3458_, v___y_3459_, v___y_3460_, v___y_3461_);
lean_dec_ref(v___y_3451_);
return v___x_3466_;
}
else
{
lean_dec_ref(v___y_3451_);
return v___x_3465_;
}
}
else
{
lean_dec_ref(v___y_3451_);
lean_dec_ref(v___f_3449_);
return v___x_3464_;
}
}
else
{
lean_dec_ref(v___y_3451_);
lean_dec_ref(v___f_3449_);
lean_dec_ref(v_e_3402_);
return v___x_3462_;
}
}
}
else
{
lean_object* v___x_3489_; lean_object* v___x_3491_; 
lean_dec(v_a_3441_);
lean_dec_ref_known(v___x_3439_, 1);
lean_dec(v_val_3437_);
lean_dec_ref(v_e_3402_);
v___x_3489_ = lean_box(0);
if (v_isShared_3444_ == 0)
{
lean_ctor_set(v___x_3443_, 0, v___x_3489_);
v___x_3491_ = v___x_3443_;
goto v_reusejp_3490_;
}
else
{
lean_object* v_reuseFailAlloc_3492_; 
v_reuseFailAlloc_3492_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3492_, 0, v___x_3489_);
v___x_3491_ = v_reuseFailAlloc_3492_;
goto v_reusejp_3490_;
}
v_reusejp_3490_:
{
return v___x_3491_;
}
}
}
}
else
{
lean_object* v_a_3494_; lean_object* v___x_3496_; uint8_t v_isShared_3497_; uint8_t v_isSharedCheck_3501_; 
lean_dec_ref_known(v___x_3439_, 1);
lean_dec(v_val_3437_);
lean_dec_ref(v_e_3402_);
v_a_3494_ = lean_ctor_get(v___x_3440_, 0);
v_isSharedCheck_3501_ = !lean_is_exclusive(v___x_3440_);
if (v_isSharedCheck_3501_ == 0)
{
v___x_3496_ = v___x_3440_;
v_isShared_3497_ = v_isSharedCheck_3501_;
goto v_resetjp_3495_;
}
else
{
lean_inc(v_a_3494_);
lean_dec(v___x_3440_);
v___x_3496_ = lean_box(0);
v_isShared_3497_ = v_isSharedCheck_3501_;
goto v_resetjp_3495_;
}
v_resetjp_3495_:
{
lean_object* v___x_3499_; 
if (v_isShared_3497_ == 0)
{
v___x_3499_ = v___x_3496_;
goto v_reusejp_3498_;
}
else
{
lean_object* v_reuseFailAlloc_3500_; 
v_reuseFailAlloc_3500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3500_, 0, v_a_3494_);
v___x_3499_ = v_reuseFailAlloc_3500_;
goto v_reusejp_3498_;
}
v_reusejp_3498_:
{
return v___x_3499_;
}
}
}
}
else
{
lean_object* v___x_3502_; 
lean_dec(v_a_3436_);
lean_inc(v_val_3433_);
v___x_3502_ = l_Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f(v_val_3433_, v_a_3404_, v_a_3405_, v_a_3406_, v_a_3407_, v_a_3408_, v_a_3409_, v_a_3410_, v_a_3411_, v_a_3412_, v_a_3413_);
if (lean_obj_tag(v___x_3502_) == 0)
{
lean_object* v_a_3503_; 
v_a_3503_ = lean_ctor_get(v___x_3502_, 0);
lean_inc(v_a_3503_);
lean_dec_ref_known(v___x_3502_, 1);
if (lean_obj_tag(v_a_3503_) == 1)
{
lean_object* v_val_3504_; lean_object* v___x_3505_; 
lean_dec(v_val_3433_);
v_val_3504_ = lean_ctor_get(v_a_3503_, 0);
lean_inc(v_val_3504_);
lean_dec_ref_known(v_a_3503_, 1);
lean_inc_ref(v_e_3402_);
v___x_3505_ = l_Lean_Meta_Grind_Arith_CommRing_sreify_x3f(v_e_3402_, v_val_3504_, v_a_3404_, v_a_3405_, v_a_3406_, v_a_3407_, v_a_3408_, v_a_3409_, v_a_3410_, v_a_3411_, v_a_3412_, v_a_3413_);
if (lean_obj_tag(v___x_3505_) == 0)
{
lean_object* v_a_3506_; lean_object* v___x_3508_; uint8_t v_isShared_3509_; uint8_t v_isSharedCheck_3557_; 
v_a_3506_ = lean_ctor_get(v___x_3505_, 0);
v_isSharedCheck_3557_ = !lean_is_exclusive(v___x_3505_);
if (v_isSharedCheck_3557_ == 0)
{
v___x_3508_ = v___x_3505_;
v_isShared_3509_ = v_isSharedCheck_3557_;
goto v_resetjp_3507_;
}
else
{
lean_inc(v_a_3506_);
lean_dec(v___x_3505_);
v___x_3508_ = lean_box(0);
v_isShared_3509_ = v_isSharedCheck_3557_;
goto v_resetjp_3507_;
}
v_resetjp_3507_:
{
if (lean_obj_tag(v_a_3506_) == 1)
{
lean_object* v_val_3510_; lean_object* v___y_3512_; lean_object* v___y_3513_; lean_object* v___y_3514_; lean_object* v___y_3515_; lean_object* v___y_3516_; lean_object* v___y_3517_; lean_object* v___y_3518_; lean_object* v___y_3519_; lean_object* v___y_3520_; lean_object* v___y_3521_; lean_object* v___y_3522_; lean_object* v_options_3528_; uint8_t v_hasTrace_3529_; 
lean_del_object(v___x_3508_);
v_val_3510_ = lean_ctor_get(v_a_3506_, 0);
lean_inc(v_val_3510_);
lean_dec_ref_known(v_a_3506_, 1);
v_options_3528_ = lean_ctor_get(v_a_3412_, 1);
v_hasTrace_3529_ = lean_ctor_get_uint8(v_options_3528_, sizeof(void*)*1);
if (v_hasTrace_3529_ == 0)
{
v___y_3512_ = v_val_3504_;
v___y_3513_ = v_a_3404_;
v___y_3514_ = v_a_3405_;
v___y_3515_ = v_a_3406_;
v___y_3516_ = v_a_3407_;
v___y_3517_ = v_a_3408_;
v___y_3518_ = v_a_3409_;
v___y_3519_ = v_a_3410_;
v___y_3520_ = v_a_3411_;
v___y_3521_ = v_a_3412_;
v___y_3522_ = v_a_3413_;
goto v___jp_3511_;
}
else
{
lean_object* v_toCold_3530_; lean_object* v_inheritedTraceOptions_3531_; lean_object* v___x_3532_; lean_object* v___x_3533_; uint8_t v___x_3534_; 
v_toCold_3530_ = lean_ctor_get(v_a_3412_, 0);
v_inheritedTraceOptions_3531_ = lean_ctor_get(v_toCold_3530_, 4);
v___x_3532_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__1));
v___x_3533_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__2, &l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__2_once, _init_l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__2);
v___x_3534_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3531_, v_options_3528_, v___x_3533_);
if (v___x_3534_ == 0)
{
v___y_3512_ = v_val_3504_;
v___y_3513_ = v_a_3404_;
v___y_3514_ = v_a_3405_;
v___y_3515_ = v_a_3406_;
v___y_3516_ = v_a_3407_;
v___y_3517_ = v_a_3408_;
v___y_3518_ = v_a_3409_;
v___y_3519_ = v_a_3410_;
v___y_3520_ = v_a_3411_;
v___y_3521_ = v_a_3412_;
v___y_3522_ = v_a_3413_;
goto v___jp_3511_;
}
else
{
lean_object* v___x_3535_; 
v___x_3535_ = l_Lean_Meta_Grind_updateLastTag(v_a_3404_, v_a_3405_, v_a_3406_, v_a_3407_, v_a_3408_, v_a_3409_, v_a_3410_, v_a_3411_, v_a_3412_, v_a_3413_);
if (lean_obj_tag(v___x_3535_) == 0)
{
lean_object* v___x_3537_; uint8_t v_isShared_3538_; uint8_t v_isSharedCheck_3551_; 
v_isSharedCheck_3551_ = !lean_is_exclusive(v___x_3535_);
if (v_isSharedCheck_3551_ == 0)
{
lean_object* v_unused_3552_; 
v_unused_3552_ = lean_ctor_get(v___x_3535_, 0);
lean_dec(v_unused_3552_);
v___x_3537_ = v___x_3535_;
v_isShared_3538_ = v_isSharedCheck_3551_;
goto v_resetjp_3536_;
}
else
{
lean_dec(v___x_3535_);
v___x_3537_ = lean_box(0);
v_isShared_3538_ = v_isSharedCheck_3551_;
goto v_resetjp_3536_;
}
v_resetjp_3536_:
{
lean_object* v___x_3539_; lean_object* v___x_3540_; lean_object* v___x_3542_; 
v___x_3539_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__8, &l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__8_once, _init_l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__8);
lean_inc(v_val_3504_);
v___x_3540_ = l_Nat_reprFast(v_val_3504_);
if (v_isShared_3538_ == 0)
{
lean_ctor_set_tag(v___x_3537_, 3);
lean_ctor_set(v___x_3537_, 0, v___x_3540_);
v___x_3542_ = v___x_3537_;
goto v_reusejp_3541_;
}
else
{
lean_object* v_reuseFailAlloc_3550_; 
v_reuseFailAlloc_3550_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3550_, 0, v___x_3540_);
v___x_3542_ = v_reuseFailAlloc_3550_;
goto v_reusejp_3541_;
}
v_reusejp_3541_:
{
lean_object* v___x_3543_; lean_object* v___x_3544_; lean_object* v___x_3545_; lean_object* v___x_3546_; lean_object* v___x_3547_; lean_object* v___x_3548_; lean_object* v___x_3549_; 
v___x_3543_ = l_Lean_MessageData_ofFormat(v___x_3542_);
v___x_3544_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3544_, 0, v___x_3539_);
lean_ctor_set(v___x_3544_, 1, v___x_3543_);
v___x_3545_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__6, &l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__6_once, _init_l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__6);
v___x_3546_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3546_, 0, v___x_3544_);
lean_ctor_set(v___x_3546_, 1, v___x_3545_);
lean_inc_ref(v_e_3402_);
v___x_3547_ = l_Lean_MessageData_ofExpr(v_e_3402_);
v___x_3548_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3548_, 0, v___x_3546_);
lean_ctor_set(v___x_3548_, 1, v___x_3547_);
v___x_3549_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__1___redArg(v___x_3532_, v___x_3548_, v_a_3410_, v_a_3411_, v_a_3412_, v_a_3413_);
if (lean_obj_tag(v___x_3549_) == 0)
{
lean_dec_ref_known(v___x_3549_, 1);
v___y_3512_ = v_val_3504_;
v___y_3513_ = v_a_3404_;
v___y_3514_ = v_a_3405_;
v___y_3515_ = v_a_3406_;
v___y_3516_ = v_a_3407_;
v___y_3517_ = v_a_3408_;
v___y_3518_ = v_a_3409_;
v___y_3519_ = v_a_3410_;
v___y_3520_ = v_a_3411_;
v___y_3521_ = v_a_3412_;
v___y_3522_ = v_a_3413_;
goto v___jp_3511_;
}
else
{
lean_dec(v_val_3510_);
lean_dec(v_val_3504_);
lean_dec_ref(v_e_3402_);
return v___x_3549_;
}
}
}
}
else
{
lean_dec(v_val_3510_);
lean_dec(v_val_3504_);
lean_dec_ref(v_e_3402_);
return v___x_3535_;
}
}
}
v___jp_3511_:
{
lean_object* v___x_3523_; 
lean_inc_ref(v_e_3402_);
v___x_3523_ = l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg(v_e_3402_, v___y_3512_, v___y_3513_, v___y_3517_, v___y_3518_, v___y_3519_, v___y_3520_, v___y_3521_, v___y_3522_);
if (lean_obj_tag(v___x_3523_) == 0)
{
lean_object* v___x_3524_; lean_object* v___x_3525_; 
lean_dec_ref_known(v___x_3523_, 1);
v___x_3524_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
lean_inc_ref(v_e_3402_);
v___x_3525_ = l_Lean_Meta_Grind_SolverExtension_markTerm___redArg(v___x_3524_, v_e_3402_, v___y_3513_, v___y_3514_, v___y_3515_, v___y_3516_, v___y_3517_, v___y_3518_, v___y_3519_, v___y_3520_, v___y_3521_, v___y_3522_);
if (lean_obj_tag(v___x_3525_) == 0)
{
lean_object* v___f_3526_; lean_object* v___x_3527_; 
lean_dec_ref_known(v___x_3525_, 1);
v___f_3526_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_internalize___lam__1___boxed), 4, 3);
lean_closure_set(v___f_3526_, 0, v___y_3512_);
lean_closure_set(v___f_3526_, 1, v_e_3402_);
lean_closure_set(v___f_3526_, 2, v_val_3510_);
v___x_3527_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_3524_, v___f_3526_, v___y_3513_);
return v___x_3527_;
}
else
{
lean_dec(v___y_3512_);
lean_dec(v_val_3510_);
lean_dec_ref(v_e_3402_);
return v___x_3525_;
}
}
else
{
lean_dec(v___y_3512_);
lean_dec(v_val_3510_);
lean_dec_ref(v_e_3402_);
return v___x_3523_;
}
}
}
else
{
lean_object* v___x_3553_; lean_object* v___x_3555_; 
lean_dec(v_a_3506_);
lean_dec(v_val_3504_);
lean_dec_ref(v_e_3402_);
v___x_3553_ = lean_box(0);
if (v_isShared_3509_ == 0)
{
lean_ctor_set(v___x_3508_, 0, v___x_3553_);
v___x_3555_ = v___x_3508_;
goto v_reusejp_3554_;
}
else
{
lean_object* v_reuseFailAlloc_3556_; 
v_reuseFailAlloc_3556_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3556_, 0, v___x_3553_);
v___x_3555_ = v_reuseFailAlloc_3556_;
goto v_reusejp_3554_;
}
v_reusejp_3554_:
{
return v___x_3555_;
}
}
}
}
else
{
lean_object* v_a_3558_; lean_object* v___x_3560_; uint8_t v_isShared_3561_; uint8_t v_isSharedCheck_3565_; 
lean_dec(v_val_3504_);
lean_dec_ref(v_e_3402_);
v_a_3558_ = lean_ctor_get(v___x_3505_, 0);
v_isSharedCheck_3565_ = !lean_is_exclusive(v___x_3505_);
if (v_isSharedCheck_3565_ == 0)
{
v___x_3560_ = v___x_3505_;
v_isShared_3561_ = v_isSharedCheck_3565_;
goto v_resetjp_3559_;
}
else
{
lean_inc(v_a_3558_);
lean_dec(v___x_3505_);
v___x_3560_ = lean_box(0);
v_isShared_3561_ = v_isSharedCheck_3565_;
goto v_resetjp_3559_;
}
v_resetjp_3559_:
{
lean_object* v___x_3563_; 
if (v_isShared_3561_ == 0)
{
v___x_3563_ = v___x_3560_;
goto v_reusejp_3562_;
}
else
{
lean_object* v_reuseFailAlloc_3564_; 
v_reuseFailAlloc_3564_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3564_, 0, v_a_3558_);
v___x_3563_ = v_reuseFailAlloc_3564_;
goto v_reusejp_3562_;
}
v_reusejp_3562_:
{
return v___x_3563_;
}
}
}
}
else
{
lean_object* v___x_3566_; 
lean_dec(v_a_3503_);
lean_inc(v_val_3433_);
v___x_3566_ = l_Lean_Meta_Grind_Arith_CommRing_getNonCommRingId_x3f(v_val_3433_, v_a_3404_, v_a_3405_, v_a_3406_, v_a_3407_, v_a_3408_, v_a_3409_, v_a_3410_, v_a_3411_, v_a_3412_, v_a_3413_);
if (lean_obj_tag(v___x_3566_) == 0)
{
lean_object* v_a_3567_; 
v_a_3567_ = lean_ctor_get(v___x_3566_, 0);
lean_inc(v_a_3567_);
lean_dec_ref_known(v___x_3566_, 1);
if (lean_obj_tag(v_a_3567_) == 1)
{
lean_object* v_val_3568_; lean_object* v___x_3569_; lean_object* v___x_3570_; 
lean_dec(v_val_3433_);
v_val_3568_ = lean_ctor_get(v_a_3567_, 0);
lean_inc(v_val_3568_);
lean_dec_ref_known(v_a_3567_, 1);
v___x_3569_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_e_3402_);
v___x_3570_ = l_Lean_Meta_Grind_Arith_CommRing_ncreify_x3f(v_e_3402_, v_ring_3420_, v___x_3569_, v_val_3568_, v_a_3404_, v_a_3405_, v_a_3406_, v_a_3407_, v_a_3408_, v_a_3409_, v_a_3410_, v_a_3411_, v_a_3412_, v_a_3413_);
if (lean_obj_tag(v___x_3570_) == 0)
{
lean_object* v_a_3571_; lean_object* v___x_3573_; uint8_t v_isShared_3574_; uint8_t v_isSharedCheck_3622_; 
v_a_3571_ = lean_ctor_get(v___x_3570_, 0);
v_isSharedCheck_3622_ = !lean_is_exclusive(v___x_3570_);
if (v_isSharedCheck_3622_ == 0)
{
v___x_3573_ = v___x_3570_;
v_isShared_3574_ = v_isSharedCheck_3622_;
goto v_resetjp_3572_;
}
else
{
lean_inc(v_a_3571_);
lean_dec(v___x_3570_);
v___x_3573_ = lean_box(0);
v_isShared_3574_ = v_isSharedCheck_3622_;
goto v_resetjp_3572_;
}
v_resetjp_3572_:
{
if (lean_obj_tag(v_a_3571_) == 1)
{
lean_object* v_options_3575_; lean_object* v_val_3576_; lean_object* v_toCold_3577_; uint8_t v_hasTrace_3578_; lean_object* v___f_3579_; lean_object* v___y_3581_; lean_object* v___y_3582_; lean_object* v___y_3583_; lean_object* v___y_3584_; lean_object* v___y_3585_; lean_object* v___y_3586_; lean_object* v___y_3587_; lean_object* v___y_3588_; lean_object* v___y_3589_; lean_object* v___y_3590_; lean_object* v___y_3591_; 
lean_del_object(v___x_3573_);
v_options_3575_ = lean_ctor_get(v_a_3412_, 1);
v_val_3576_ = lean_ctor_get(v_a_3571_, 0);
lean_inc(v_val_3576_);
lean_dec_ref_known(v_a_3571_, 1);
v_toCold_3577_ = lean_ctor_get(v_a_3412_, 0);
v_hasTrace_3578_ = lean_ctor_get_uint8(v_options_3575_, sizeof(void*)*1);
lean_inc_ref(v_e_3402_);
v___f_3579_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_internalize___lam__2), 3, 2);
lean_closure_set(v___f_3579_, 0, v_e_3402_);
lean_closure_set(v___f_3579_, 1, v_val_3576_);
if (v_hasTrace_3578_ == 0)
{
v___y_3581_ = v_val_3568_;
v___y_3582_ = v_a_3404_;
v___y_3583_ = v_a_3405_;
v___y_3584_ = v_a_3406_;
v___y_3585_ = v_a_3407_;
v___y_3586_ = v_a_3408_;
v___y_3587_ = v_a_3409_;
v___y_3588_ = v_a_3410_;
v___y_3589_ = v_a_3411_;
v___y_3590_ = v_a_3412_;
v___y_3591_ = v_a_3413_;
goto v___jp_3580_;
}
else
{
lean_object* v_inheritedTraceOptions_3596_; lean_object* v___x_3597_; lean_object* v___x_3598_; uint8_t v___x_3599_; 
v_inheritedTraceOptions_3596_ = lean_ctor_get(v_toCold_3577_, 4);
v___x_3597_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__1));
v___x_3598_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__2, &l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__2_once, _init_l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__2);
v___x_3599_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3596_, v_options_3575_, v___x_3598_);
if (v___x_3599_ == 0)
{
v___y_3581_ = v_val_3568_;
v___y_3582_ = v_a_3404_;
v___y_3583_ = v_a_3405_;
v___y_3584_ = v_a_3406_;
v___y_3585_ = v_a_3407_;
v___y_3586_ = v_a_3408_;
v___y_3587_ = v_a_3409_;
v___y_3588_ = v_a_3410_;
v___y_3589_ = v_a_3411_;
v___y_3590_ = v_a_3412_;
v___y_3591_ = v_a_3413_;
goto v___jp_3580_;
}
else
{
lean_object* v___x_3600_; 
v___x_3600_ = l_Lean_Meta_Grind_updateLastTag(v_a_3404_, v_a_3405_, v_a_3406_, v_a_3407_, v_a_3408_, v_a_3409_, v_a_3410_, v_a_3411_, v_a_3412_, v_a_3413_);
if (lean_obj_tag(v___x_3600_) == 0)
{
lean_object* v___x_3602_; uint8_t v_isShared_3603_; uint8_t v_isSharedCheck_3616_; 
v_isSharedCheck_3616_ = !lean_is_exclusive(v___x_3600_);
if (v_isSharedCheck_3616_ == 0)
{
lean_object* v_unused_3617_; 
v_unused_3617_ = lean_ctor_get(v___x_3600_, 0);
lean_dec(v_unused_3617_);
v___x_3602_ = v___x_3600_;
v_isShared_3603_ = v_isSharedCheck_3616_;
goto v_resetjp_3601_;
}
else
{
lean_dec(v___x_3600_);
v___x_3602_ = lean_box(0);
v_isShared_3603_ = v_isSharedCheck_3616_;
goto v_resetjp_3601_;
}
v_resetjp_3601_:
{
lean_object* v___x_3604_; lean_object* v___x_3605_; lean_object* v___x_3607_; 
v___x_3604_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__10, &l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__10_once, _init_l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__10);
lean_inc(v_val_3568_);
v___x_3605_ = l_Nat_reprFast(v_val_3568_);
if (v_isShared_3603_ == 0)
{
lean_ctor_set_tag(v___x_3602_, 3);
lean_ctor_set(v___x_3602_, 0, v___x_3605_);
v___x_3607_ = v___x_3602_;
goto v_reusejp_3606_;
}
else
{
lean_object* v_reuseFailAlloc_3615_; 
v_reuseFailAlloc_3615_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3615_, 0, v___x_3605_);
v___x_3607_ = v_reuseFailAlloc_3615_;
goto v_reusejp_3606_;
}
v_reusejp_3606_:
{
lean_object* v___x_3608_; lean_object* v___x_3609_; lean_object* v___x_3610_; lean_object* v___x_3611_; lean_object* v___x_3612_; lean_object* v___x_3613_; lean_object* v___x_3614_; 
v___x_3608_ = l_Lean_MessageData_ofFormat(v___x_3607_);
v___x_3609_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3609_, 0, v___x_3604_);
lean_ctor_set(v___x_3609_, 1, v___x_3608_);
v___x_3610_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__6, &l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__6_once, _init_l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__6);
v___x_3611_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3611_, 0, v___x_3609_);
lean_ctor_set(v___x_3611_, 1, v___x_3610_);
lean_inc_ref(v_e_3402_);
v___x_3612_ = l_Lean_MessageData_ofExpr(v_e_3402_);
v___x_3613_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3613_, 0, v___x_3611_);
lean_ctor_set(v___x_3613_, 1, v___x_3612_);
v___x_3614_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__2___redArg(v___x_3597_, v___x_3613_, v_a_3410_, v_a_3411_, v_a_3412_, v_a_3413_);
if (lean_obj_tag(v___x_3614_) == 0)
{
lean_dec_ref_known(v___x_3614_, 1);
v___y_3581_ = v_val_3568_;
v___y_3582_ = v_a_3404_;
v___y_3583_ = v_a_3405_;
v___y_3584_ = v_a_3406_;
v___y_3585_ = v_a_3407_;
v___y_3586_ = v_a_3408_;
v___y_3587_ = v_a_3409_;
v___y_3588_ = v_a_3410_;
v___y_3589_ = v_a_3411_;
v___y_3590_ = v_a_3412_;
v___y_3591_ = v_a_3413_;
goto v___jp_3580_;
}
else
{
lean_dec_ref(v___f_3579_);
lean_dec(v_val_3568_);
lean_dec_ref(v_e_3402_);
return v___x_3614_;
}
}
}
}
else
{
lean_dec_ref(v___f_3579_);
lean_dec(v_val_3568_);
lean_dec_ref(v_e_3402_);
return v___x_3600_;
}
}
}
v___jp_3580_:
{
lean_object* v___x_3592_; 
lean_inc_ref(v_e_3402_);
v___x_3592_ = l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId___redArg(v_e_3402_, v___y_3581_, v___y_3582_, v___y_3586_, v___y_3587_, v___y_3588_, v___y_3589_, v___y_3590_, v___y_3591_);
if (lean_obj_tag(v___x_3592_) == 0)
{
lean_object* v___x_3593_; lean_object* v___x_3594_; 
lean_dec_ref_known(v___x_3592_, 1);
v___x_3593_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_3594_ = l_Lean_Meta_Grind_SolverExtension_markTerm___redArg(v___x_3593_, v_e_3402_, v___y_3582_, v___y_3583_, v___y_3584_, v___y_3585_, v___y_3586_, v___y_3587_, v___y_3588_, v___y_3589_, v___y_3590_, v___y_3591_);
if (lean_obj_tag(v___x_3594_) == 0)
{
lean_object* v___x_3595_; 
lean_dec_ref_known(v___x_3594_, 1);
v___x_3595_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_modifyRing___redArg(v___f_3579_, v___y_3581_, v___y_3582_);
lean_dec(v___y_3581_);
return v___x_3595_;
}
else
{
lean_dec(v___y_3581_);
lean_dec_ref(v___f_3579_);
return v___x_3594_;
}
}
else
{
lean_dec(v___y_3581_);
lean_dec_ref(v___f_3579_);
lean_dec_ref(v_e_3402_);
return v___x_3592_;
}
}
}
else
{
lean_object* v___x_3618_; lean_object* v___x_3620_; 
lean_dec(v_a_3571_);
lean_dec(v_val_3568_);
lean_dec_ref(v_e_3402_);
v___x_3618_ = lean_box(0);
if (v_isShared_3574_ == 0)
{
lean_ctor_set(v___x_3573_, 0, v___x_3618_);
v___x_3620_ = v___x_3573_;
goto v_reusejp_3619_;
}
else
{
lean_object* v_reuseFailAlloc_3621_; 
v_reuseFailAlloc_3621_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3621_, 0, v___x_3618_);
v___x_3620_ = v_reuseFailAlloc_3621_;
goto v_reusejp_3619_;
}
v_reusejp_3619_:
{
return v___x_3620_;
}
}
}
}
else
{
lean_object* v_a_3623_; lean_object* v___x_3625_; uint8_t v_isShared_3626_; uint8_t v_isSharedCheck_3630_; 
lean_dec(v_val_3568_);
lean_dec_ref(v_e_3402_);
v_a_3623_ = lean_ctor_get(v___x_3570_, 0);
v_isSharedCheck_3630_ = !lean_is_exclusive(v___x_3570_);
if (v_isSharedCheck_3630_ == 0)
{
v___x_3625_ = v___x_3570_;
v_isShared_3626_ = v_isSharedCheck_3630_;
goto v_resetjp_3624_;
}
else
{
lean_inc(v_a_3623_);
lean_dec(v___x_3570_);
v___x_3625_ = lean_box(0);
v_isShared_3626_ = v_isSharedCheck_3630_;
goto v_resetjp_3624_;
}
v_resetjp_3624_:
{
lean_object* v___x_3628_; 
if (v_isShared_3626_ == 0)
{
v___x_3628_ = v___x_3625_;
goto v_reusejp_3627_;
}
else
{
lean_object* v_reuseFailAlloc_3629_; 
v_reuseFailAlloc_3629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3629_, 0, v_a_3623_);
v___x_3628_ = v_reuseFailAlloc_3629_;
goto v_reusejp_3627_;
}
v_reusejp_3627_:
{
return v___x_3628_;
}
}
}
}
else
{
lean_object* v___x_3631_; 
lean_dec(v_a_3567_);
v___x_3631_ = l_Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f___redArg(v_val_3433_, v_a_3404_, v_a_3409_, v_a_3410_, v_a_3411_, v_a_3412_, v_a_3413_);
if (lean_obj_tag(v___x_3631_) == 0)
{
lean_object* v_a_3632_; lean_object* v___x_3634_; uint8_t v_isShared_3635_; uint8_t v_isSharedCheck_3702_; 
v_a_3632_ = lean_ctor_get(v___x_3631_, 0);
v_isSharedCheck_3702_ = !lean_is_exclusive(v___x_3631_);
if (v_isSharedCheck_3702_ == 0)
{
v___x_3634_ = v___x_3631_;
v_isShared_3635_ = v_isSharedCheck_3702_;
goto v_resetjp_3633_;
}
else
{
lean_inc(v_a_3632_);
lean_dec(v___x_3631_);
v___x_3634_ = lean_box(0);
v_isShared_3635_ = v_isSharedCheck_3702_;
goto v_resetjp_3633_;
}
v_resetjp_3633_:
{
if (lean_obj_tag(v_a_3632_) == 1)
{
lean_object* v_val_3636_; lean_object* v___x_3637_; 
lean_del_object(v___x_3634_);
v_val_3636_ = lean_ctor_get(v_a_3632_, 0);
lean_inc(v_val_3636_);
lean_dec_ref_known(v_a_3632_, 1);
lean_inc_ref(v_e_3402_);
v___x_3637_ = l_Lean_Meta_Grind_Arith_CommRing_ncsreify_x3f(v_e_3402_, v_val_3636_, v_a_3404_, v_a_3405_, v_a_3406_, v_a_3407_, v_a_3408_, v_a_3409_, v_a_3410_, v_a_3411_, v_a_3412_, v_a_3413_);
if (lean_obj_tag(v___x_3637_) == 0)
{
lean_object* v_a_3638_; lean_object* v___x_3640_; uint8_t v_isShared_3641_; uint8_t v_isSharedCheck_3689_; 
v_a_3638_ = lean_ctor_get(v___x_3637_, 0);
v_isSharedCheck_3689_ = !lean_is_exclusive(v___x_3637_);
if (v_isSharedCheck_3689_ == 0)
{
v___x_3640_ = v___x_3637_;
v_isShared_3641_ = v_isSharedCheck_3689_;
goto v_resetjp_3639_;
}
else
{
lean_inc(v_a_3638_);
lean_dec(v___x_3637_);
v___x_3640_ = lean_box(0);
v_isShared_3641_ = v_isSharedCheck_3689_;
goto v_resetjp_3639_;
}
v_resetjp_3639_:
{
if (lean_obj_tag(v_a_3638_) == 1)
{
lean_object* v_options_3642_; lean_object* v_val_3643_; lean_object* v_toCold_3644_; uint8_t v_hasTrace_3645_; lean_object* v___f_3646_; lean_object* v___y_3648_; lean_object* v___y_3649_; lean_object* v___y_3650_; lean_object* v___y_3651_; lean_object* v___y_3652_; lean_object* v___y_3653_; lean_object* v___y_3654_; lean_object* v___y_3655_; lean_object* v___y_3656_; lean_object* v___y_3657_; lean_object* v___y_3658_; 
lean_del_object(v___x_3640_);
v_options_3642_ = lean_ctor_get(v_a_3412_, 1);
v_val_3643_ = lean_ctor_get(v_a_3638_, 0);
lean_inc(v_val_3643_);
lean_dec_ref_known(v_a_3638_, 1);
v_toCold_3644_ = lean_ctor_get(v_a_3412_, 0);
v_hasTrace_3645_ = lean_ctor_get_uint8(v_options_3642_, sizeof(void*)*1);
lean_inc_ref(v_e_3402_);
v___f_3646_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_internalize___lam__3), 3, 2);
lean_closure_set(v___f_3646_, 0, v_e_3402_);
lean_closure_set(v___f_3646_, 1, v_val_3643_);
if (v_hasTrace_3645_ == 0)
{
v___y_3648_ = v_val_3636_;
v___y_3649_ = v_a_3404_;
v___y_3650_ = v_a_3405_;
v___y_3651_ = v_a_3406_;
v___y_3652_ = v_a_3407_;
v___y_3653_ = v_a_3408_;
v___y_3654_ = v_a_3409_;
v___y_3655_ = v_a_3410_;
v___y_3656_ = v_a_3411_;
v___y_3657_ = v_a_3412_;
v___y_3658_ = v_a_3413_;
goto v___jp_3647_;
}
else
{
lean_object* v_inheritedTraceOptions_3663_; lean_object* v___x_3664_; lean_object* v___x_3665_; uint8_t v___x_3666_; 
v_inheritedTraceOptions_3663_ = lean_ctor_get(v_toCold_3644_, 4);
v___x_3664_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__1));
v___x_3665_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__2, &l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__2_once, _init_l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__2);
v___x_3666_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3663_, v_options_3642_, v___x_3665_);
if (v___x_3666_ == 0)
{
v___y_3648_ = v_val_3636_;
v___y_3649_ = v_a_3404_;
v___y_3650_ = v_a_3405_;
v___y_3651_ = v_a_3406_;
v___y_3652_ = v_a_3407_;
v___y_3653_ = v_a_3408_;
v___y_3654_ = v_a_3409_;
v___y_3655_ = v_a_3410_;
v___y_3656_ = v_a_3411_;
v___y_3657_ = v_a_3412_;
v___y_3658_ = v_a_3413_;
goto v___jp_3647_;
}
else
{
lean_object* v___x_3667_; 
v___x_3667_ = l_Lean_Meta_Grind_updateLastTag(v_a_3404_, v_a_3405_, v_a_3406_, v_a_3407_, v_a_3408_, v_a_3409_, v_a_3410_, v_a_3411_, v_a_3412_, v_a_3413_);
if (lean_obj_tag(v___x_3667_) == 0)
{
lean_object* v___x_3669_; uint8_t v_isShared_3670_; uint8_t v_isSharedCheck_3683_; 
v_isSharedCheck_3683_ = !lean_is_exclusive(v___x_3667_);
if (v_isSharedCheck_3683_ == 0)
{
lean_object* v_unused_3684_; 
v_unused_3684_ = lean_ctor_get(v___x_3667_, 0);
lean_dec(v_unused_3684_);
v___x_3669_ = v___x_3667_;
v_isShared_3670_ = v_isSharedCheck_3683_;
goto v_resetjp_3668_;
}
else
{
lean_dec(v___x_3667_);
v___x_3669_ = lean_box(0);
v_isShared_3670_ = v_isSharedCheck_3683_;
goto v_resetjp_3668_;
}
v_resetjp_3668_:
{
lean_object* v___x_3671_; lean_object* v___x_3672_; lean_object* v___x_3674_; 
v___x_3671_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__12, &l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__12_once, _init_l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__12);
lean_inc(v_val_3636_);
v___x_3672_ = l_Nat_reprFast(v_val_3636_);
if (v_isShared_3670_ == 0)
{
lean_ctor_set_tag(v___x_3669_, 3);
lean_ctor_set(v___x_3669_, 0, v___x_3672_);
v___x_3674_ = v___x_3669_;
goto v_reusejp_3673_;
}
else
{
lean_object* v_reuseFailAlloc_3682_; 
v_reuseFailAlloc_3682_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3682_, 0, v___x_3672_);
v___x_3674_ = v_reuseFailAlloc_3682_;
goto v_reusejp_3673_;
}
v_reusejp_3673_:
{
lean_object* v___x_3675_; lean_object* v___x_3676_; lean_object* v___x_3677_; lean_object* v___x_3678_; lean_object* v___x_3679_; lean_object* v___x_3680_; lean_object* v___x_3681_; 
v___x_3675_ = l_Lean_MessageData_ofFormat(v___x_3674_);
v___x_3676_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3676_, 0, v___x_3671_);
lean_ctor_set(v___x_3676_, 1, v___x_3675_);
v___x_3677_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__6, &l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__6_once, _init_l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__6);
v___x_3678_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3678_, 0, v___x_3676_);
lean_ctor_set(v___x_3678_, 1, v___x_3677_);
lean_inc_ref(v_e_3402_);
v___x_3679_ = l_Lean_MessageData_ofExpr(v_e_3402_);
v___x_3680_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3680_, 0, v___x_3678_);
lean_ctor_set(v___x_3680_, 1, v___x_3679_);
v___x_3681_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__3___redArg(v___x_3664_, v___x_3680_, v_a_3410_, v_a_3411_, v_a_3412_, v_a_3413_);
if (lean_obj_tag(v___x_3681_) == 0)
{
lean_dec_ref_known(v___x_3681_, 1);
v___y_3648_ = v_val_3636_;
v___y_3649_ = v_a_3404_;
v___y_3650_ = v_a_3405_;
v___y_3651_ = v_a_3406_;
v___y_3652_ = v_a_3407_;
v___y_3653_ = v_a_3408_;
v___y_3654_ = v_a_3409_;
v___y_3655_ = v_a_3410_;
v___y_3656_ = v_a_3411_;
v___y_3657_ = v_a_3412_;
v___y_3658_ = v_a_3413_;
goto v___jp_3647_;
}
else
{
lean_dec_ref(v___f_3646_);
lean_dec(v_val_3636_);
lean_dec_ref(v_e_3402_);
return v___x_3681_;
}
}
}
}
else
{
lean_dec_ref(v___f_3646_);
lean_dec(v_val_3636_);
lean_dec_ref(v_e_3402_);
return v___x_3667_;
}
}
}
v___jp_3647_:
{
lean_object* v___x_3659_; 
lean_inc_ref(v_e_3402_);
v___x_3659_ = l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId___redArg(v_e_3402_, v___y_3648_, v___y_3649_, v___y_3653_, v___y_3654_, v___y_3655_, v___y_3656_, v___y_3657_, v___y_3658_);
if (lean_obj_tag(v___x_3659_) == 0)
{
lean_object* v___x_3660_; lean_object* v___x_3661_; 
lean_dec_ref_known(v___x_3659_, 1);
v___x_3660_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_3661_ = l_Lean_Meta_Grind_SolverExtension_markTerm___redArg(v___x_3660_, v_e_3402_, v___y_3649_, v___y_3650_, v___y_3651_, v___y_3652_, v___y_3653_, v___y_3654_, v___y_3655_, v___y_3656_, v___y_3657_, v___y_3658_);
if (lean_obj_tag(v___x_3661_) == 0)
{
lean_object* v___x_3662_; 
lean_dec_ref_known(v___x_3661_, 1);
v___x_3662_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_modifySemiring___redArg(v___f_3646_, v___y_3648_, v___y_3649_);
lean_dec(v___y_3648_);
return v___x_3662_;
}
else
{
lean_dec(v___y_3648_);
lean_dec_ref(v___f_3646_);
return v___x_3661_;
}
}
else
{
lean_dec(v___y_3648_);
lean_dec_ref(v___f_3646_);
lean_dec_ref(v_e_3402_);
return v___x_3659_;
}
}
}
else
{
lean_object* v___x_3685_; lean_object* v___x_3687_; 
lean_dec(v_a_3638_);
lean_dec(v_val_3636_);
lean_dec_ref(v_e_3402_);
v___x_3685_ = lean_box(0);
if (v_isShared_3641_ == 0)
{
lean_ctor_set(v___x_3640_, 0, v___x_3685_);
v___x_3687_ = v___x_3640_;
goto v_reusejp_3686_;
}
else
{
lean_object* v_reuseFailAlloc_3688_; 
v_reuseFailAlloc_3688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3688_, 0, v___x_3685_);
v___x_3687_ = v_reuseFailAlloc_3688_;
goto v_reusejp_3686_;
}
v_reusejp_3686_:
{
return v___x_3687_;
}
}
}
}
else
{
lean_object* v_a_3690_; lean_object* v___x_3692_; uint8_t v_isShared_3693_; uint8_t v_isSharedCheck_3697_; 
lean_dec(v_val_3636_);
lean_dec_ref(v_e_3402_);
v_a_3690_ = lean_ctor_get(v___x_3637_, 0);
v_isSharedCheck_3697_ = !lean_is_exclusive(v___x_3637_);
if (v_isSharedCheck_3697_ == 0)
{
v___x_3692_ = v___x_3637_;
v_isShared_3693_ = v_isSharedCheck_3697_;
goto v_resetjp_3691_;
}
else
{
lean_inc(v_a_3690_);
lean_dec(v___x_3637_);
v___x_3692_ = lean_box(0);
v_isShared_3693_ = v_isSharedCheck_3697_;
goto v_resetjp_3691_;
}
v_resetjp_3691_:
{
lean_object* v___x_3695_; 
if (v_isShared_3693_ == 0)
{
v___x_3695_ = v___x_3692_;
goto v_reusejp_3694_;
}
else
{
lean_object* v_reuseFailAlloc_3696_; 
v_reuseFailAlloc_3696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3696_, 0, v_a_3690_);
v___x_3695_ = v_reuseFailAlloc_3696_;
goto v_reusejp_3694_;
}
v_reusejp_3694_:
{
return v___x_3695_;
}
}
}
}
else
{
lean_object* v___x_3698_; lean_object* v___x_3700_; 
lean_dec(v_a_3632_);
lean_dec_ref(v_e_3402_);
v___x_3698_ = lean_box(0);
if (v_isShared_3635_ == 0)
{
lean_ctor_set(v___x_3634_, 0, v___x_3698_);
v___x_3700_ = v___x_3634_;
goto v_reusejp_3699_;
}
else
{
lean_object* v_reuseFailAlloc_3701_; 
v_reuseFailAlloc_3701_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3701_, 0, v___x_3698_);
v___x_3700_ = v_reuseFailAlloc_3701_;
goto v_reusejp_3699_;
}
v_reusejp_3699_:
{
return v___x_3700_;
}
}
}
}
else
{
lean_object* v_a_3703_; lean_object* v___x_3705_; uint8_t v_isShared_3706_; uint8_t v_isSharedCheck_3710_; 
lean_dec_ref(v_e_3402_);
v_a_3703_ = lean_ctor_get(v___x_3631_, 0);
v_isSharedCheck_3710_ = !lean_is_exclusive(v___x_3631_);
if (v_isSharedCheck_3710_ == 0)
{
v___x_3705_ = v___x_3631_;
v_isShared_3706_ = v_isSharedCheck_3710_;
goto v_resetjp_3704_;
}
else
{
lean_inc(v_a_3703_);
lean_dec(v___x_3631_);
v___x_3705_ = lean_box(0);
v_isShared_3706_ = v_isSharedCheck_3710_;
goto v_resetjp_3704_;
}
v_resetjp_3704_:
{
lean_object* v___x_3708_; 
if (v_isShared_3706_ == 0)
{
v___x_3708_ = v___x_3705_;
goto v_reusejp_3707_;
}
else
{
lean_object* v_reuseFailAlloc_3709_; 
v_reuseFailAlloc_3709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3709_, 0, v_a_3703_);
v___x_3708_ = v_reuseFailAlloc_3709_;
goto v_reusejp_3707_;
}
v_reusejp_3707_:
{
return v___x_3708_;
}
}
}
}
}
else
{
lean_object* v_a_3711_; lean_object* v___x_3713_; uint8_t v_isShared_3714_; uint8_t v_isSharedCheck_3718_; 
lean_dec(v_val_3433_);
lean_dec_ref(v_e_3402_);
v_a_3711_ = lean_ctor_get(v___x_3566_, 0);
v_isSharedCheck_3718_ = !lean_is_exclusive(v___x_3566_);
if (v_isSharedCheck_3718_ == 0)
{
v___x_3713_ = v___x_3566_;
v_isShared_3714_ = v_isSharedCheck_3718_;
goto v_resetjp_3712_;
}
else
{
lean_inc(v_a_3711_);
lean_dec(v___x_3566_);
v___x_3713_ = lean_box(0);
v_isShared_3714_ = v_isSharedCheck_3718_;
goto v_resetjp_3712_;
}
v_resetjp_3712_:
{
lean_object* v___x_3716_; 
if (v_isShared_3714_ == 0)
{
v___x_3716_ = v___x_3713_;
goto v_reusejp_3715_;
}
else
{
lean_object* v_reuseFailAlloc_3717_; 
v_reuseFailAlloc_3717_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3717_, 0, v_a_3711_);
v___x_3716_ = v_reuseFailAlloc_3717_;
goto v_reusejp_3715_;
}
v_reusejp_3715_:
{
return v___x_3716_;
}
}
}
}
}
else
{
lean_object* v_a_3719_; lean_object* v___x_3721_; uint8_t v_isShared_3722_; uint8_t v_isSharedCheck_3726_; 
lean_dec(v_val_3433_);
lean_dec_ref(v_e_3402_);
v_a_3719_ = lean_ctor_get(v___x_3502_, 0);
v_isSharedCheck_3726_ = !lean_is_exclusive(v___x_3502_);
if (v_isSharedCheck_3726_ == 0)
{
v___x_3721_ = v___x_3502_;
v_isShared_3722_ = v_isSharedCheck_3726_;
goto v_resetjp_3720_;
}
else
{
lean_inc(v_a_3719_);
lean_dec(v___x_3502_);
v___x_3721_ = lean_box(0);
v_isShared_3722_ = v_isSharedCheck_3726_;
goto v_resetjp_3720_;
}
v_resetjp_3720_:
{
lean_object* v___x_3724_; 
if (v_isShared_3722_ == 0)
{
v___x_3724_ = v___x_3721_;
goto v_reusejp_3723_;
}
else
{
lean_object* v_reuseFailAlloc_3725_; 
v_reuseFailAlloc_3725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3725_, 0, v_a_3719_);
v___x_3724_ = v_reuseFailAlloc_3725_;
goto v_reusejp_3723_;
}
v_reusejp_3723_:
{
return v___x_3724_;
}
}
}
}
}
else
{
lean_object* v_a_3727_; lean_object* v___x_3729_; uint8_t v_isShared_3730_; uint8_t v_isSharedCheck_3734_; 
lean_dec(v_val_3433_);
lean_dec_ref(v_e_3402_);
v_a_3727_ = lean_ctor_get(v___x_3435_, 0);
v_isSharedCheck_3734_ = !lean_is_exclusive(v___x_3435_);
if (v_isSharedCheck_3734_ == 0)
{
v___x_3729_ = v___x_3435_;
v_isShared_3730_ = v_isSharedCheck_3734_;
goto v_resetjp_3728_;
}
else
{
lean_inc(v_a_3727_);
lean_dec(v___x_3435_);
v___x_3729_ = lean_box(0);
v_isShared_3730_ = v_isSharedCheck_3734_;
goto v_resetjp_3728_;
}
v_resetjp_3728_:
{
lean_object* v___x_3732_; 
if (v_isShared_3730_ == 0)
{
v___x_3732_ = v___x_3729_;
goto v_reusejp_3731_;
}
else
{
lean_object* v_reuseFailAlloc_3733_; 
v_reuseFailAlloc_3733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3733_, 0, v_a_3727_);
v___x_3732_ = v_reuseFailAlloc_3733_;
goto v_reusejp_3731_;
}
v_reusejp_3731_:
{
return v___x_3732_;
}
}
}
}
else
{
lean_object* v___x_3735_; lean_object* v___x_3737_; 
lean_dec(v_val_3433_);
lean_dec_ref(v_e_3402_);
v___x_3735_ = lean_box(0);
if (v_isShared_3430_ == 0)
{
lean_ctor_set(v___x_3429_, 0, v___x_3735_);
v___x_3737_ = v___x_3429_;
goto v_reusejp_3736_;
}
else
{
lean_object* v_reuseFailAlloc_3738_; 
v_reuseFailAlloc_3738_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3738_, 0, v___x_3735_);
v___x_3737_ = v_reuseFailAlloc_3738_;
goto v_reusejp_3736_;
}
v_reusejp_3736_:
{
return v___x_3737_;
}
}
}
else
{
lean_object* v___x_3739_; lean_object* v___x_3741_; 
lean_dec(v___x_3432_);
lean_dec(v_parent_x3f_3403_);
lean_dec_ref(v_e_3402_);
v___x_3739_ = lean_box(0);
if (v_isShared_3430_ == 0)
{
lean_ctor_set(v___x_3429_, 0, v___x_3739_);
v___x_3741_ = v___x_3429_;
goto v_reusejp_3740_;
}
else
{
lean_object* v_reuseFailAlloc_3742_; 
v_reuseFailAlloc_3742_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3742_, 0, v___x_3739_);
v___x_3741_ = v_reuseFailAlloc_3742_;
goto v_reusejp_3740_;
}
v_reusejp_3740_:
{
return v___x_3741_;
}
}
}
else
{
lean_object* v___x_3743_; lean_object* v___x_3745_; 
lean_dec(v_parent_x3f_3403_);
lean_dec_ref(v_e_3402_);
v___x_3743_ = lean_box(0);
if (v_isShared_3430_ == 0)
{
lean_ctor_set(v___x_3429_, 0, v___x_3743_);
v___x_3745_ = v___x_3429_;
goto v_reusejp_3744_;
}
else
{
lean_object* v_reuseFailAlloc_3746_; 
v_reuseFailAlloc_3746_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3746_, 0, v___x_3743_);
v___x_3745_ = v_reuseFailAlloc_3746_;
goto v_reusejp_3744_;
}
v_reusejp_3744_:
{
return v___x_3745_;
}
}
}
}
else
{
lean_object* v_a_3748_; lean_object* v___x_3750_; uint8_t v_isShared_3751_; uint8_t v_isSharedCheck_3755_; 
lean_dec(v_parent_x3f_3403_);
lean_dec_ref(v_e_3402_);
v_a_3748_ = lean_ctor_get(v___x_3426_, 0);
v_isSharedCheck_3755_ = !lean_is_exclusive(v___x_3426_);
if (v_isSharedCheck_3755_ == 0)
{
v___x_3750_ = v___x_3426_;
v_isShared_3751_ = v_isSharedCheck_3755_;
goto v_resetjp_3749_;
}
else
{
lean_inc(v_a_3748_);
lean_dec(v___x_3426_);
v___x_3750_ = lean_box(0);
v_isShared_3751_ = v_isSharedCheck_3755_;
goto v_resetjp_3749_;
}
v_resetjp_3749_:
{
lean_object* v___x_3753_; 
if (v_isShared_3751_ == 0)
{
v___x_3753_ = v___x_3750_;
goto v_reusejp_3752_;
}
else
{
lean_object* v_reuseFailAlloc_3754_; 
v_reuseFailAlloc_3754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3754_, 0, v_a_3748_);
v___x_3753_ = v_reuseFailAlloc_3754_;
goto v_reusejp_3752_;
}
v_reusejp_3752_:
{
return v___x_3753_;
}
}
}
}
else
{
lean_object* v___x_3756_; lean_object* v___x_3758_; 
lean_dec(v_parent_x3f_3403_);
lean_dec_ref(v_e_3402_);
v___x_3756_ = lean_box(0);
if (v_isShared_3419_ == 0)
{
lean_ctor_set(v___x_3418_, 0, v___x_3756_);
v___x_3758_ = v___x_3418_;
goto v_reusejp_3757_;
}
else
{
lean_object* v_reuseFailAlloc_3759_; 
v_reuseFailAlloc_3759_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3759_, 0, v___x_3756_);
v___x_3758_ = v_reuseFailAlloc_3759_;
goto v_reusejp_3757_;
}
v_reusejp_3757_:
{
return v___x_3758_;
}
}
}
}
}
else
{
lean_object* v_a_3761_; lean_object* v___x_3763_; uint8_t v_isShared_3764_; uint8_t v_isSharedCheck_3768_; 
lean_dec(v_parent_x3f_3403_);
lean_dec_ref(v_e_3402_);
v_a_3761_ = lean_ctor_get(v___x_3415_, 0);
v_isSharedCheck_3768_ = !lean_is_exclusive(v___x_3415_);
if (v_isSharedCheck_3768_ == 0)
{
v___x_3763_ = v___x_3415_;
v_isShared_3764_ = v_isSharedCheck_3768_;
goto v_resetjp_3762_;
}
else
{
lean_inc(v_a_3761_);
lean_dec(v___x_3415_);
v___x_3763_ = lean_box(0);
v_isShared_3764_ = v_isSharedCheck_3768_;
goto v_resetjp_3762_;
}
v_resetjp_3762_:
{
lean_object* v___x_3766_; 
if (v_isShared_3764_ == 0)
{
v___x_3766_ = v___x_3763_;
goto v_reusejp_3765_;
}
else
{
lean_object* v_reuseFailAlloc_3767_; 
v_reuseFailAlloc_3767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3767_, 0, v_a_3761_);
v___x_3766_ = v_reuseFailAlloc_3767_;
goto v_reusejp_3765_;
}
v_reusejp_3765_:
{
return v___x_3766_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_internalize___boxed(lean_object* v_e_3769_, lean_object* v_parent_x3f_3770_, lean_object* v_a_3771_, lean_object* v_a_3772_, lean_object* v_a_3773_, lean_object* v_a_3774_, lean_object* v_a_3775_, lean_object* v_a_3776_, lean_object* v_a_3777_, lean_object* v_a_3778_, lean_object* v_a_3779_, lean_object* v_a_3780_, lean_object* v_a_3781_){
_start:
{
lean_object* v_res_3782_; 
v_res_3782_ = l_Lean_Meta_Grind_Arith_CommRing_internalize(v_e_3769_, v_parent_x3f_3770_, v_a_3771_, v_a_3772_, v_a_3773_, v_a_3774_, v_a_3775_, v_a_3776_, v_a_3777_, v_a_3778_, v_a_3779_, v_a_3780_);
lean_dec(v_a_3780_);
lean_dec_ref(v_a_3779_);
lean_dec(v_a_3778_);
lean_dec_ref(v_a_3777_);
lean_dec(v_a_3776_);
lean_dec_ref(v_a_3775_);
lean_dec(v_a_3774_);
lean_dec_ref(v_a_3773_);
lean_dec(v_a_3772_);
lean_dec(v_a_3771_);
return v_res_3782_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0(lean_object* v_00_u03b2_3783_, lean_object* v_x_3784_, lean_object* v_x_3785_, lean_object* v_x_3786_){
_start:
{
lean_object* v___x_3787_; 
v___x_3787_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0___redArg(v_x_3784_, v_x_3785_, v_x_3786_);
return v___x_3787_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__1(lean_object* v_cls_3788_, lean_object* v_msg_3789_, lean_object* v___y_3790_, lean_object* v___y_3791_, lean_object* v___y_3792_, lean_object* v___y_3793_, lean_object* v___y_3794_, lean_object* v___y_3795_, lean_object* v___y_3796_, lean_object* v___y_3797_, lean_object* v___y_3798_, lean_object* v___y_3799_, lean_object* v___y_3800_){
_start:
{
lean_object* v___x_3802_; 
v___x_3802_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__1___redArg(v_cls_3788_, v_msg_3789_, v___y_3797_, v___y_3798_, v___y_3799_, v___y_3800_);
return v___x_3802_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__1___boxed(lean_object* v_cls_3803_, lean_object* v_msg_3804_, lean_object* v___y_3805_, lean_object* v___y_3806_, lean_object* v___y_3807_, lean_object* v___y_3808_, lean_object* v___y_3809_, lean_object* v___y_3810_, lean_object* v___y_3811_, lean_object* v___y_3812_, lean_object* v___y_3813_, lean_object* v___y_3814_, lean_object* v___y_3815_, lean_object* v___y_3816_){
_start:
{
lean_object* v_res_3817_; 
v_res_3817_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__1(v_cls_3803_, v_msg_3804_, v___y_3805_, v___y_3806_, v___y_3807_, v___y_3808_, v___y_3809_, v___y_3810_, v___y_3811_, v___y_3812_, v___y_3813_, v___y_3814_, v___y_3815_);
lean_dec(v___y_3815_);
lean_dec_ref(v___y_3814_);
lean_dec(v___y_3813_);
lean_dec_ref(v___y_3812_);
lean_dec(v___y_3811_);
lean_dec_ref(v___y_3810_);
lean_dec(v___y_3809_);
lean_dec_ref(v___y_3808_);
lean_dec(v___y_3807_);
lean_dec(v___y_3806_);
lean_dec(v___y_3805_);
return v_res_3817_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__2(lean_object* v_cls_3818_, lean_object* v_msg_3819_, lean_object* v___y_3820_, lean_object* v___y_3821_, lean_object* v___y_3822_, lean_object* v___y_3823_, lean_object* v___y_3824_, lean_object* v___y_3825_, lean_object* v___y_3826_, lean_object* v___y_3827_, lean_object* v___y_3828_, lean_object* v___y_3829_, lean_object* v___y_3830_){
_start:
{
lean_object* v___x_3832_; 
v___x_3832_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__2___redArg(v_cls_3818_, v_msg_3819_, v___y_3827_, v___y_3828_, v___y_3829_, v___y_3830_);
return v___x_3832_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__2___boxed(lean_object* v_cls_3833_, lean_object* v_msg_3834_, lean_object* v___y_3835_, lean_object* v___y_3836_, lean_object* v___y_3837_, lean_object* v___y_3838_, lean_object* v___y_3839_, lean_object* v___y_3840_, lean_object* v___y_3841_, lean_object* v___y_3842_, lean_object* v___y_3843_, lean_object* v___y_3844_, lean_object* v___y_3845_, lean_object* v___y_3846_){
_start:
{
lean_object* v_res_3847_; 
v_res_3847_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__2(v_cls_3833_, v_msg_3834_, v___y_3835_, v___y_3836_, v___y_3837_, v___y_3838_, v___y_3839_, v___y_3840_, v___y_3841_, v___y_3842_, v___y_3843_, v___y_3844_, v___y_3845_);
lean_dec(v___y_3845_);
lean_dec_ref(v___y_3844_);
lean_dec(v___y_3843_);
lean_dec_ref(v___y_3842_);
lean_dec(v___y_3841_);
lean_dec_ref(v___y_3840_);
lean_dec(v___y_3839_);
lean_dec_ref(v___y_3838_);
lean_dec(v___y_3837_);
lean_dec(v___y_3836_);
lean_dec(v___y_3835_);
return v_res_3847_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__3(lean_object* v_cls_3848_, lean_object* v_msg_3849_, lean_object* v___y_3850_, lean_object* v___y_3851_, lean_object* v___y_3852_, lean_object* v___y_3853_, lean_object* v___y_3854_, lean_object* v___y_3855_, lean_object* v___y_3856_, lean_object* v___y_3857_, lean_object* v___y_3858_, lean_object* v___y_3859_, lean_object* v___y_3860_){
_start:
{
lean_object* v___x_3862_; 
v___x_3862_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__3___redArg(v_cls_3848_, v_msg_3849_, v___y_3857_, v___y_3858_, v___y_3859_, v___y_3860_);
return v___x_3862_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__3___boxed(lean_object* v_cls_3863_, lean_object* v_msg_3864_, lean_object* v___y_3865_, lean_object* v___y_3866_, lean_object* v___y_3867_, lean_object* v___y_3868_, lean_object* v___y_3869_, lean_object* v___y_3870_, lean_object* v___y_3871_, lean_object* v___y_3872_, lean_object* v___y_3873_, lean_object* v___y_3874_, lean_object* v___y_3875_, lean_object* v___y_3876_){
_start:
{
lean_object* v_res_3877_; 
v_res_3877_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__3(v_cls_3863_, v_msg_3864_, v___y_3865_, v___y_3866_, v___y_3867_, v___y_3868_, v___y_3869_, v___y_3870_, v___y_3871_, v___y_3872_, v___y_3873_, v___y_3874_, v___y_3875_);
lean_dec(v___y_3875_);
lean_dec_ref(v___y_3874_);
lean_dec(v___y_3873_);
lean_dec_ref(v___y_3872_);
lean_dec(v___y_3871_);
lean_dec_ref(v___y_3870_);
lean_dec(v___y_3869_);
lean_dec_ref(v___y_3868_);
lean_dec(v___y_3867_);
lean_dec(v___y_3866_);
lean_dec(v___y_3865_);
return v_res_3877_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0(lean_object* v_00_u03b2_3878_, lean_object* v_x_3879_, size_t v_x_3880_, size_t v_x_3881_, lean_object* v_x_3882_, lean_object* v_x_3883_){
_start:
{
lean_object* v___x_3884_; 
v___x_3884_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0___redArg(v_x_3879_, v_x_3880_, v_x_3881_, v_x_3882_, v_x_3883_);
return v___x_3884_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3885_, lean_object* v_x_3886_, lean_object* v_x_3887_, lean_object* v_x_3888_, lean_object* v_x_3889_, lean_object* v_x_3890_){
_start:
{
size_t v_x_152080__boxed_3891_; size_t v_x_152081__boxed_3892_; lean_object* v_res_3893_; 
v_x_152080__boxed_3891_ = lean_unbox_usize(v_x_3887_);
lean_dec(v_x_3887_);
v_x_152081__boxed_3892_ = lean_unbox_usize(v_x_3888_);
lean_dec(v_x_3888_);
v_res_3893_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0(v_00_u03b2_3885_, v_x_3886_, v_x_152080__boxed_3891_, v_x_152081__boxed_3892_, v_x_3889_, v_x_3890_);
return v_res_3893_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_3894_, lean_object* v_n_3895_, lean_object* v_k_3896_, lean_object* v_v_3897_){
_start:
{
lean_object* v___x_3898_; 
v___x_3898_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0_spec__1___redArg(v_n_3895_, v_k_3896_, v_v_3897_);
return v___x_3898_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_3899_, size_t v_depth_3900_, lean_object* v_keys_3901_, lean_object* v_vals_3902_, lean_object* v_heq_3903_, lean_object* v_i_3904_, lean_object* v_entries_3905_){
_start:
{
lean_object* v___x_3906_; 
v___x_3906_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0_spec__2___redArg(v_depth_3900_, v_keys_3901_, v_vals_3902_, v_i_3904_, v_entries_3905_);
return v___x_3906_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_3907_, lean_object* v_depth_3908_, lean_object* v_keys_3909_, lean_object* v_vals_3910_, lean_object* v_heq_3911_, lean_object* v_i_3912_, lean_object* v_entries_3913_){
_start:
{
size_t v_depth_boxed_3914_; lean_object* v_res_3915_; 
v_depth_boxed_3914_ = lean_unbox_usize(v_depth_3908_);
lean_dec(v_depth_3908_);
v_res_3915_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0_spec__2(v_00_u03b2_3907_, v_depth_boxed_3914_, v_keys_3909_, v_vals_3910_, v_heq_3911_, v_i_3912_, v_entries_3913_);
lean_dec_ref(v_vals_3910_);
lean_dec_ref(v_keys_3909_);
return v_res_3915_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0_spec__1_spec__5(lean_object* v_00_u03b2_3916_, lean_object* v_x_3917_, lean_object* v_x_3918_, lean_object* v_x_3919_, lean_object* v_x_3920_){
_start:
{
lean_object* v___x_3921_; 
v___x_3921_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0_spec__1_spec__5___redArg(v_x_3917_, v_x_3918_, v_x_3919_, v_x_3920_);
return v___x_3921_;
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
