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
lean_object* v___x_990_; 
v___x_990_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_977_, v_a_986_);
if (lean_obj_tag(v___x_990_) == 0)
{
lean_object* v_a_991_; lean_object* v___x_993_; uint8_t v_isShared_994_; uint8_t v_isSharedCheck_1154_; 
v_a_991_ = lean_ctor_get(v___x_990_, 0);
v_isSharedCheck_1154_ = !lean_is_exclusive(v___x_990_);
if (v_isSharedCheck_1154_ == 0)
{
v___x_993_ = v___x_990_;
v_isShared_994_ = v_isSharedCheck_1154_;
goto v_resetjp_992_;
}
else
{
lean_inc(v_a_991_);
lean_dec(v___x_990_);
v___x_993_ = lean_box(0);
v_isShared_994_ = v_isSharedCheck_1154_;
goto v_resetjp_992_;
}
v_resetjp_992_:
{
lean_object* v___x_1000_; uint8_t v___x_1001_; 
v___x_1000_ = l_Lean_Expr_cleanupAnnotations(v_a_991_);
v___x_1001_ = l_Lean_Expr_isApp(v___x_1000_);
if (v___x_1001_ == 0)
{
lean_dec_ref(v___x_1000_);
goto v___jp_995_;
}
else
{
lean_object* v_arg_1002_; lean_object* v___x_1003_; uint8_t v___x_1004_; 
v_arg_1002_ = lean_ctor_get(v___x_1000_, 1);
lean_inc_ref(v_arg_1002_);
v___x_1003_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1000_);
v___x_1004_ = l_Lean_Expr_isApp(v___x_1003_);
if (v___x_1004_ == 0)
{
lean_dec_ref(v___x_1003_);
lean_dec_ref(v_arg_1002_);
goto v___jp_995_;
}
else
{
lean_object* v_arg_1005_; lean_object* v___x_1006_; uint8_t v___x_1007_; 
v_arg_1005_ = lean_ctor_get(v___x_1003_, 1);
lean_inc_ref(v_arg_1005_);
v___x_1006_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1003_);
v___x_1007_ = l_Lean_Expr_isApp(v___x_1006_);
if (v___x_1007_ == 0)
{
lean_dec_ref(v___x_1006_);
lean_dec_ref(v_arg_1005_);
lean_dec_ref(v_arg_1002_);
goto v___jp_995_;
}
else
{
lean_object* v___x_1008_; lean_object* v___x_1009_; uint8_t v___x_1010_; 
v___x_1008_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1006_);
v___x_1009_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__8));
v___x_1010_ = l_Lean_Expr_isConstOf(v___x_1008_, v___x_1009_);
if (v___x_1010_ == 0)
{
lean_object* v___x_1011_; uint8_t v___x_1012_; 
v___x_1011_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__5));
v___x_1012_ = l_Lean_Expr_isConstOf(v___x_1008_, v___x_1011_);
if (v___x_1012_ == 0)
{
lean_object* v___x_1013_; uint8_t v___x_1014_; 
v___x_1013_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__2));
v___x_1014_ = l_Lean_Expr_isConstOf(v___x_1008_, v___x_1013_);
if (v___x_1014_ == 0)
{
lean_object* v___x_1015_; uint8_t v___x_1016_; 
v___x_1015_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__11));
v___x_1016_ = l_Lean_Expr_isConstOf(v___x_1008_, v___x_1015_);
lean_dec_ref(v___x_1008_);
if (v___x_1016_ == 0)
{
lean_dec_ref(v_arg_1005_);
lean_dec_ref(v_arg_1002_);
goto v___jp_995_;
}
else
{
lean_object* v___x_1017_; 
lean_del_object(v___x_993_);
v___x_1017_ = l_Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0(v_arg_1005_, v_a_978_, v_a_979_, v_a_980_, v_a_981_, v_a_982_, v_a_983_, v_a_984_, v_a_985_, v_a_986_, v_a_987_, v_a_988_);
lean_dec_ref(v_arg_1005_);
if (lean_obj_tag(v___x_1017_) == 0)
{
lean_object* v_a_1018_; lean_object* v___x_1020_; uint8_t v_isShared_1021_; uint8_t v_isSharedCheck_1046_; 
v_a_1018_ = lean_ctor_get(v___x_1017_, 0);
v_isSharedCheck_1046_ = !lean_is_exclusive(v___x_1017_);
if (v_isSharedCheck_1046_ == 0)
{
v___x_1020_ = v___x_1017_;
v_isShared_1021_ = v_isSharedCheck_1046_;
goto v_resetjp_1019_;
}
else
{
lean_inc(v_a_1018_);
lean_dec(v___x_1017_);
v___x_1020_ = lean_box(0);
v_isShared_1021_ = v_isSharedCheck_1046_;
goto v_resetjp_1019_;
}
v_resetjp_1019_:
{
uint8_t v___x_1022_; 
v___x_1022_ = lean_unbox(v_a_1018_);
lean_dec(v_a_1018_);
if (v___x_1022_ == 0)
{
lean_object* v___x_1023_; lean_object* v___x_1025_; 
lean_dec_ref(v_arg_1002_);
v___x_1023_ = lean_box(0);
if (v_isShared_1021_ == 0)
{
lean_ctor_set(v___x_1020_, 0, v___x_1023_);
v___x_1025_ = v___x_1020_;
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
lean_del_object(v___x_1020_);
v___x_1027_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f(v_arg_1002_, v_a_978_, v_a_979_, v_a_980_, v_a_981_, v_a_982_, v_a_983_, v_a_984_, v_a_985_, v_a_986_, v_a_987_, v_a_988_);
if (lean_obj_tag(v___x_1027_) == 0)
{
lean_object* v_a_1028_; 
v_a_1028_ = lean_ctor_get(v___x_1027_, 0);
lean_inc(v_a_1028_);
if (lean_obj_tag(v_a_1028_) == 0)
{
return v___x_1027_;
}
else
{
lean_object* v___x_1030_; uint8_t v_isShared_1031_; uint8_t v_isSharedCheck_1044_; 
v_isSharedCheck_1044_ = !lean_is_exclusive(v___x_1027_);
if (v_isSharedCheck_1044_ == 0)
{
lean_object* v_unused_1045_; 
v_unused_1045_ = lean_ctor_get(v___x_1027_, 0);
lean_dec(v_unused_1045_);
v___x_1030_ = v___x_1027_;
v_isShared_1031_ = v_isSharedCheck_1044_;
goto v_resetjp_1029_;
}
else
{
lean_dec(v___x_1027_);
v___x_1030_ = lean_box(0);
v_isShared_1031_ = v_isSharedCheck_1044_;
goto v_resetjp_1029_;
}
v_resetjp_1029_:
{
lean_object* v_val_1032_; lean_object* v___x_1034_; uint8_t v_isShared_1035_; uint8_t v_isSharedCheck_1043_; 
v_val_1032_ = lean_ctor_get(v_a_1028_, 0);
v_isSharedCheck_1043_ = !lean_is_exclusive(v_a_1028_);
if (v_isSharedCheck_1043_ == 0)
{
v___x_1034_ = v_a_1028_;
v_isShared_1035_ = v_isSharedCheck_1043_;
goto v_resetjp_1033_;
}
else
{
lean_inc(v_val_1032_);
lean_dec(v_a_1028_);
v___x_1034_ = lean_box(0);
v_isShared_1035_ = v_isSharedCheck_1043_;
goto v_resetjp_1033_;
}
v_resetjp_1033_:
{
lean_object* v___x_1036_; lean_object* v___x_1038_; 
v___x_1036_ = lean_int_neg(v_val_1032_);
lean_dec(v_val_1032_);
if (v_isShared_1035_ == 0)
{
lean_ctor_set(v___x_1034_, 0, v___x_1036_);
v___x_1038_ = v___x_1034_;
goto v_reusejp_1037_;
}
else
{
lean_object* v_reuseFailAlloc_1042_; 
v_reuseFailAlloc_1042_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1042_, 0, v___x_1036_);
v___x_1038_ = v_reuseFailAlloc_1042_;
goto v_reusejp_1037_;
}
v_reusejp_1037_:
{
lean_object* v___x_1040_; 
if (v_isShared_1031_ == 0)
{
lean_ctor_set(v___x_1030_, 0, v___x_1038_);
v___x_1040_ = v___x_1030_;
goto v_reusejp_1039_;
}
else
{
lean_object* v_reuseFailAlloc_1041_; 
v_reuseFailAlloc_1041_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1041_, 0, v___x_1038_);
v___x_1040_ = v_reuseFailAlloc_1041_;
goto v_reusejp_1039_;
}
v_reusejp_1039_:
{
return v___x_1040_;
}
}
}
}
}
}
else
{
return v___x_1027_;
}
}
}
}
else
{
lean_object* v_a_1047_; lean_object* v___x_1049_; uint8_t v_isShared_1050_; uint8_t v_isSharedCheck_1054_; 
lean_dec_ref(v_arg_1002_);
v_a_1047_ = lean_ctor_get(v___x_1017_, 0);
v_isSharedCheck_1054_ = !lean_is_exclusive(v___x_1017_);
if (v_isSharedCheck_1054_ == 0)
{
v___x_1049_ = v___x_1017_;
v_isShared_1050_ = v_isSharedCheck_1054_;
goto v_resetjp_1048_;
}
else
{
lean_inc(v_a_1047_);
lean_dec(v___x_1017_);
v___x_1049_ = lean_box(0);
v_isShared_1050_ = v_isSharedCheck_1054_;
goto v_resetjp_1048_;
}
v_resetjp_1048_:
{
lean_object* v___x_1052_; 
if (v_isShared_1050_ == 0)
{
v___x_1052_ = v___x_1049_;
goto v_reusejp_1051_;
}
else
{
lean_object* v_reuseFailAlloc_1053_; 
v_reuseFailAlloc_1053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1053_, 0, v_a_1047_);
v___x_1052_ = v_reuseFailAlloc_1053_;
goto v_reusejp_1051_;
}
v_reusejp_1051_:
{
return v___x_1052_;
}
}
}
}
}
else
{
lean_object* v___x_1055_; 
lean_dec_ref(v___x_1008_);
lean_del_object(v___x_993_);
v___x_1055_ = l_Lean_Meta_Grind_Arith_CommRing_isIntCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__1(v_arg_1005_, v_a_978_, v_a_979_, v_a_980_, v_a_981_, v_a_982_, v_a_983_, v_a_984_, v_a_985_, v_a_986_, v_a_987_, v_a_988_);
lean_dec_ref(v_arg_1005_);
if (lean_obj_tag(v___x_1055_) == 0)
{
lean_object* v_a_1056_; lean_object* v___x_1058_; uint8_t v_isShared_1059_; uint8_t v_isSharedCheck_1066_; 
v_a_1056_ = lean_ctor_get(v___x_1055_, 0);
v_isSharedCheck_1066_ = !lean_is_exclusive(v___x_1055_);
if (v_isSharedCheck_1066_ == 0)
{
v___x_1058_ = v___x_1055_;
v_isShared_1059_ = v_isSharedCheck_1066_;
goto v_resetjp_1057_;
}
else
{
lean_inc(v_a_1056_);
lean_dec(v___x_1055_);
v___x_1058_ = lean_box(0);
v_isShared_1059_ = v_isSharedCheck_1066_;
goto v_resetjp_1057_;
}
v_resetjp_1057_:
{
uint8_t v___x_1060_; 
v___x_1060_ = lean_unbox(v_a_1056_);
lean_dec(v_a_1056_);
if (v___x_1060_ == 0)
{
lean_object* v___x_1061_; lean_object* v___x_1063_; 
lean_dec_ref(v_arg_1002_);
v___x_1061_ = lean_box(0);
if (v_isShared_1059_ == 0)
{
lean_ctor_set(v___x_1058_, 0, v___x_1061_);
v___x_1063_ = v___x_1058_;
goto v_reusejp_1062_;
}
else
{
lean_object* v_reuseFailAlloc_1064_; 
v_reuseFailAlloc_1064_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1064_, 0, v___x_1061_);
v___x_1063_ = v_reuseFailAlloc_1064_;
goto v_reusejp_1062_;
}
v_reusejp_1062_:
{
return v___x_1063_;
}
}
else
{
lean_object* v___x_1065_; 
lean_del_object(v___x_1058_);
v___x_1065_ = l_Lean_Meta_getIntValue_x3f(v_arg_1002_, v_a_985_, v_a_986_, v_a_987_, v_a_988_);
return v___x_1065_;
}
}
}
else
{
lean_object* v_a_1067_; lean_object* v___x_1069_; uint8_t v_isShared_1070_; uint8_t v_isSharedCheck_1074_; 
lean_dec_ref(v_arg_1002_);
v_a_1067_ = lean_ctor_get(v___x_1055_, 0);
v_isSharedCheck_1074_ = !lean_is_exclusive(v___x_1055_);
if (v_isSharedCheck_1074_ == 0)
{
v___x_1069_ = v___x_1055_;
v_isShared_1070_ = v_isSharedCheck_1074_;
goto v_resetjp_1068_;
}
else
{
lean_inc(v_a_1067_);
lean_dec(v___x_1055_);
v___x_1069_ = lean_box(0);
v_isShared_1070_ = v_isSharedCheck_1074_;
goto v_resetjp_1068_;
}
v_resetjp_1068_:
{
lean_object* v___x_1072_; 
if (v_isShared_1070_ == 0)
{
v___x_1072_ = v___x_1069_;
goto v_reusejp_1071_;
}
else
{
lean_object* v_reuseFailAlloc_1073_; 
v_reuseFailAlloc_1073_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1073_, 0, v_a_1067_);
v___x_1072_ = v_reuseFailAlloc_1073_;
goto v_reusejp_1071_;
}
v_reusejp_1071_:
{
return v___x_1072_;
}
}
}
}
}
else
{
lean_object* v___x_1075_; 
lean_dec_ref(v___x_1008_);
lean_del_object(v___x_993_);
v___x_1075_ = l_Lean_Meta_Grind_Arith_CommRing_isNatCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__2(v_arg_1005_, v_a_978_, v_a_979_, v_a_980_, v_a_981_, v_a_982_, v_a_983_, v_a_984_, v_a_985_, v_a_986_, v_a_987_, v_a_988_);
lean_dec_ref(v_arg_1005_);
if (lean_obj_tag(v___x_1075_) == 0)
{
lean_object* v_a_1076_; lean_object* v___x_1078_; uint8_t v_isShared_1079_; uint8_t v_isSharedCheck_1115_; 
v_a_1076_ = lean_ctor_get(v___x_1075_, 0);
v_isSharedCheck_1115_ = !lean_is_exclusive(v___x_1075_);
if (v_isSharedCheck_1115_ == 0)
{
v___x_1078_ = v___x_1075_;
v_isShared_1079_ = v_isSharedCheck_1115_;
goto v_resetjp_1077_;
}
else
{
lean_inc(v_a_1076_);
lean_dec(v___x_1075_);
v___x_1078_ = lean_box(0);
v_isShared_1079_ = v_isSharedCheck_1115_;
goto v_resetjp_1077_;
}
v_resetjp_1077_:
{
uint8_t v___x_1080_; 
v___x_1080_ = lean_unbox(v_a_1076_);
lean_dec(v_a_1076_);
if (v___x_1080_ == 0)
{
lean_object* v___x_1081_; lean_object* v___x_1083_; 
lean_dec_ref(v_arg_1002_);
v___x_1081_ = lean_box(0);
if (v_isShared_1079_ == 0)
{
lean_ctor_set(v___x_1078_, 0, v___x_1081_);
v___x_1083_ = v___x_1078_;
goto v_reusejp_1082_;
}
else
{
lean_object* v_reuseFailAlloc_1084_; 
v_reuseFailAlloc_1084_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1084_, 0, v___x_1081_);
v___x_1083_ = v_reuseFailAlloc_1084_;
goto v_reusejp_1082_;
}
v_reusejp_1082_:
{
return v___x_1083_;
}
}
else
{
lean_object* v___x_1085_; 
lean_del_object(v___x_1078_);
v___x_1085_ = l_Lean_Meta_getNatValue_x3f(v_arg_1002_, v_a_985_, v_a_986_, v_a_987_, v_a_988_);
lean_dec_ref(v_arg_1002_);
if (lean_obj_tag(v___x_1085_) == 0)
{
lean_object* v_a_1086_; lean_object* v___x_1088_; uint8_t v_isShared_1089_; uint8_t v_isSharedCheck_1106_; 
v_a_1086_ = lean_ctor_get(v___x_1085_, 0);
v_isSharedCheck_1106_ = !lean_is_exclusive(v___x_1085_);
if (v_isSharedCheck_1106_ == 0)
{
v___x_1088_ = v___x_1085_;
v_isShared_1089_ = v_isSharedCheck_1106_;
goto v_resetjp_1087_;
}
else
{
lean_inc(v_a_1086_);
lean_dec(v___x_1085_);
v___x_1088_ = lean_box(0);
v_isShared_1089_ = v_isSharedCheck_1106_;
goto v_resetjp_1087_;
}
v_resetjp_1087_:
{
if (lean_obj_tag(v_a_1086_) == 1)
{
lean_object* v_val_1090_; lean_object* v___x_1092_; uint8_t v_isShared_1093_; uint8_t v_isSharedCheck_1101_; 
v_val_1090_ = lean_ctor_get(v_a_1086_, 0);
v_isSharedCheck_1101_ = !lean_is_exclusive(v_a_1086_);
if (v_isSharedCheck_1101_ == 0)
{
v___x_1092_ = v_a_1086_;
v_isShared_1093_ = v_isSharedCheck_1101_;
goto v_resetjp_1091_;
}
else
{
lean_inc(v_val_1090_);
lean_dec(v_a_1086_);
v___x_1092_ = lean_box(0);
v_isShared_1093_ = v_isSharedCheck_1101_;
goto v_resetjp_1091_;
}
v_resetjp_1091_:
{
lean_object* v___x_1094_; lean_object* v___x_1096_; 
v___x_1094_ = lean_nat_to_int(v_val_1090_);
if (v_isShared_1093_ == 0)
{
lean_ctor_set(v___x_1092_, 0, v___x_1094_);
v___x_1096_ = v___x_1092_;
goto v_reusejp_1095_;
}
else
{
lean_object* v_reuseFailAlloc_1100_; 
v_reuseFailAlloc_1100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1100_, 0, v___x_1094_);
v___x_1096_ = v_reuseFailAlloc_1100_;
goto v_reusejp_1095_;
}
v_reusejp_1095_:
{
lean_object* v___x_1098_; 
if (v_isShared_1089_ == 0)
{
lean_ctor_set(v___x_1088_, 0, v___x_1096_);
v___x_1098_ = v___x_1088_;
goto v_reusejp_1097_;
}
else
{
lean_object* v_reuseFailAlloc_1099_; 
v_reuseFailAlloc_1099_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1099_, 0, v___x_1096_);
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
else
{
lean_object* v___x_1102_; lean_object* v___x_1104_; 
lean_dec(v_a_1086_);
v___x_1102_ = lean_box(0);
if (v_isShared_1089_ == 0)
{
lean_ctor_set(v___x_1088_, 0, v___x_1102_);
v___x_1104_ = v___x_1088_;
goto v_reusejp_1103_;
}
else
{
lean_object* v_reuseFailAlloc_1105_; 
v_reuseFailAlloc_1105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1105_, 0, v___x_1102_);
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
else
{
lean_object* v_a_1107_; lean_object* v___x_1109_; uint8_t v_isShared_1110_; uint8_t v_isSharedCheck_1114_; 
v_a_1107_ = lean_ctor_get(v___x_1085_, 0);
v_isSharedCheck_1114_ = !lean_is_exclusive(v___x_1085_);
if (v_isSharedCheck_1114_ == 0)
{
v___x_1109_ = v___x_1085_;
v_isShared_1110_ = v_isSharedCheck_1114_;
goto v_resetjp_1108_;
}
else
{
lean_inc(v_a_1107_);
lean_dec(v___x_1085_);
v___x_1109_ = lean_box(0);
v_isShared_1110_ = v_isSharedCheck_1114_;
goto v_resetjp_1108_;
}
v_resetjp_1108_:
{
lean_object* v___x_1112_; 
if (v_isShared_1110_ == 0)
{
v___x_1112_ = v___x_1109_;
goto v_reusejp_1111_;
}
else
{
lean_object* v_reuseFailAlloc_1113_; 
v_reuseFailAlloc_1113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1113_, 0, v_a_1107_);
v___x_1112_ = v_reuseFailAlloc_1113_;
goto v_reusejp_1111_;
}
v_reusejp_1111_:
{
return v___x_1112_;
}
}
}
}
}
}
else
{
lean_object* v_a_1116_; lean_object* v___x_1118_; uint8_t v_isShared_1119_; uint8_t v_isSharedCheck_1123_; 
lean_dec_ref(v_arg_1002_);
v_a_1116_ = lean_ctor_get(v___x_1075_, 0);
v_isSharedCheck_1123_ = !lean_is_exclusive(v___x_1075_);
if (v_isSharedCheck_1123_ == 0)
{
v___x_1118_ = v___x_1075_;
v_isShared_1119_ = v_isSharedCheck_1123_;
goto v_resetjp_1117_;
}
else
{
lean_inc(v_a_1116_);
lean_dec(v___x_1075_);
v___x_1118_ = lean_box(0);
v_isShared_1119_ = v_isSharedCheck_1123_;
goto v_resetjp_1117_;
}
v_resetjp_1117_:
{
lean_object* v___x_1121_; 
if (v_isShared_1119_ == 0)
{
v___x_1121_ = v___x_1118_;
goto v_reusejp_1120_;
}
else
{
lean_object* v_reuseFailAlloc_1122_; 
v_reuseFailAlloc_1122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1122_, 0, v_a_1116_);
v___x_1121_ = v_reuseFailAlloc_1122_;
goto v_reusejp_1120_;
}
v_reusejp_1120_:
{
return v___x_1121_;
}
}
}
}
}
else
{
lean_object* v___x_1124_; 
lean_dec_ref(v___x_1008_);
lean_dec_ref(v_arg_1002_);
lean_del_object(v___x_993_);
v___x_1124_ = l_Lean_Meta_getNatValue_x3f(v_arg_1005_, v_a_985_, v_a_986_, v_a_987_, v_a_988_);
lean_dec_ref(v_arg_1005_);
if (lean_obj_tag(v___x_1124_) == 0)
{
lean_object* v_a_1125_; lean_object* v___x_1127_; uint8_t v_isShared_1128_; uint8_t v_isSharedCheck_1145_; 
v_a_1125_ = lean_ctor_get(v___x_1124_, 0);
v_isSharedCheck_1145_ = !lean_is_exclusive(v___x_1124_);
if (v_isSharedCheck_1145_ == 0)
{
v___x_1127_ = v___x_1124_;
v_isShared_1128_ = v_isSharedCheck_1145_;
goto v_resetjp_1126_;
}
else
{
lean_inc(v_a_1125_);
lean_dec(v___x_1124_);
v___x_1127_ = lean_box(0);
v_isShared_1128_ = v_isSharedCheck_1145_;
goto v_resetjp_1126_;
}
v_resetjp_1126_:
{
if (lean_obj_tag(v_a_1125_) == 1)
{
lean_object* v_val_1129_; lean_object* v___x_1131_; uint8_t v_isShared_1132_; uint8_t v_isSharedCheck_1140_; 
v_val_1129_ = lean_ctor_get(v_a_1125_, 0);
v_isSharedCheck_1140_ = !lean_is_exclusive(v_a_1125_);
if (v_isSharedCheck_1140_ == 0)
{
v___x_1131_ = v_a_1125_;
v_isShared_1132_ = v_isSharedCheck_1140_;
goto v_resetjp_1130_;
}
else
{
lean_inc(v_val_1129_);
lean_dec(v_a_1125_);
v___x_1131_ = lean_box(0);
v_isShared_1132_ = v_isSharedCheck_1140_;
goto v_resetjp_1130_;
}
v_resetjp_1130_:
{
lean_object* v___x_1133_; lean_object* v___x_1135_; 
v___x_1133_ = lean_nat_to_int(v_val_1129_);
if (v_isShared_1132_ == 0)
{
lean_ctor_set(v___x_1131_, 0, v___x_1133_);
v___x_1135_ = v___x_1131_;
goto v_reusejp_1134_;
}
else
{
lean_object* v_reuseFailAlloc_1139_; 
v_reuseFailAlloc_1139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1139_, 0, v___x_1133_);
v___x_1135_ = v_reuseFailAlloc_1139_;
goto v_reusejp_1134_;
}
v_reusejp_1134_:
{
lean_object* v___x_1137_; 
if (v_isShared_1128_ == 0)
{
lean_ctor_set(v___x_1127_, 0, v___x_1135_);
v___x_1137_ = v___x_1127_;
goto v_reusejp_1136_;
}
else
{
lean_object* v_reuseFailAlloc_1138_; 
v_reuseFailAlloc_1138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1138_, 0, v___x_1135_);
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
else
{
lean_object* v___x_1141_; lean_object* v___x_1143_; 
lean_dec(v_a_1125_);
v___x_1141_ = lean_box(0);
if (v_isShared_1128_ == 0)
{
lean_ctor_set(v___x_1127_, 0, v___x_1141_);
v___x_1143_ = v___x_1127_;
goto v_reusejp_1142_;
}
else
{
lean_object* v_reuseFailAlloc_1144_; 
v_reuseFailAlloc_1144_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1144_, 0, v___x_1141_);
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
else
{
lean_object* v_a_1146_; lean_object* v___x_1148_; uint8_t v_isShared_1149_; uint8_t v_isSharedCheck_1153_; 
v_a_1146_ = lean_ctor_get(v___x_1124_, 0);
v_isSharedCheck_1153_ = !lean_is_exclusive(v___x_1124_);
if (v_isSharedCheck_1153_ == 0)
{
v___x_1148_ = v___x_1124_;
v_isShared_1149_ = v_isSharedCheck_1153_;
goto v_resetjp_1147_;
}
else
{
lean_inc(v_a_1146_);
lean_dec(v___x_1124_);
v___x_1148_ = lean_box(0);
v_isShared_1149_ = v_isSharedCheck_1153_;
goto v_resetjp_1147_;
}
v_resetjp_1147_:
{
lean_object* v___x_1151_; 
if (v_isShared_1149_ == 0)
{
v___x_1151_ = v___x_1148_;
goto v_reusejp_1150_;
}
else
{
lean_object* v_reuseFailAlloc_1152_; 
v_reuseFailAlloc_1152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1152_, 0, v_a_1146_);
v___x_1151_ = v_reuseFailAlloc_1152_;
goto v_reusejp_1150_;
}
v_reusejp_1150_:
{
return v___x_1151_;
}
}
}
}
}
}
}
v___jp_995_:
{
lean_object* v___x_996_; lean_object* v___x_998_; 
v___x_996_ = lean_box(0);
if (v_isShared_994_ == 0)
{
lean_ctor_set(v___x_993_, 0, v___x_996_);
v___x_998_ = v___x_993_;
goto v_reusejp_997_;
}
else
{
lean_object* v_reuseFailAlloc_999_; 
v_reuseFailAlloc_999_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_999_, 0, v___x_996_);
v___x_998_ = v_reuseFailAlloc_999_;
goto v_reusejp_997_;
}
v_reusejp_997_:
{
return v___x_998_;
}
}
}
}
else
{
lean_object* v_a_1155_; lean_object* v___x_1157_; uint8_t v_isShared_1158_; uint8_t v_isSharedCheck_1162_; 
v_a_1155_ = lean_ctor_get(v___x_990_, 0);
v_isSharedCheck_1162_ = !lean_is_exclusive(v___x_990_);
if (v_isSharedCheck_1162_ == 0)
{
v___x_1157_ = v___x_990_;
v_isShared_1158_ = v_isSharedCheck_1162_;
goto v_resetjp_1156_;
}
else
{
lean_inc(v_a_1155_);
lean_dec(v___x_990_);
v___x_1157_ = lean_box(0);
v_isShared_1158_ = v_isSharedCheck_1162_;
goto v_resetjp_1156_;
}
v_resetjp_1156_:
{
lean_object* v___x_1160_; 
if (v_isShared_1158_ == 0)
{
v___x_1160_ = v___x_1157_;
goto v_reusejp_1159_;
}
else
{
lean_object* v_reuseFailAlloc_1161_; 
v_reuseFailAlloc_1161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1161_, 0, v_a_1155_);
v___x_1160_ = v_reuseFailAlloc_1161_;
goto v_reusejp_1159_;
}
v_reusejp_1159_:
{
return v___x_1160_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f___boxed(lean_object* v_e_1163_, lean_object* v_a_1164_, lean_object* v_a_1165_, lean_object* v_a_1166_, lean_object* v_a_1167_, lean_object* v_a_1168_, lean_object* v_a_1169_, lean_object* v_a_1170_, lean_object* v_a_1171_, lean_object* v_a_1172_, lean_object* v_a_1173_, lean_object* v_a_1174_, lean_object* v_a_1175_){
_start:
{
lean_object* v_res_1176_; 
v_res_1176_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f(v_e_1163_, v_a_1164_, v_a_1165_, v_a_1166_, v_a_1167_, v_a_1168_, v_a_1169_, v_a_1170_, v_a_1171_, v_a_1172_, v_a_1173_, v_a_1174_);
lean_dec(v_a_1174_);
lean_dec_ref(v_a_1173_);
lean_dec(v_a_1172_);
lean_dec_ref(v_a_1171_);
lean_dec(v_a_1170_);
lean_dec_ref(v_a_1169_);
lean_dec(v_a_1168_);
lean_dec_ref(v_a_1167_);
lean_dec(v_a_1166_);
lean_dec(v_a_1165_);
lean_dec_ref(v_a_1164_);
return v_res_1176_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_getNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isNatCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__2_spec__4_spec__6(lean_object* v_u_1177_, lean_object* v_type_1178_, lean_object* v_semiringInst_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_){
_start:
{
lean_object* v___x_1192_; 
v___x_1192_ = l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_getNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isNatCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__2_spec__4_spec__6___redArg(v_u_1177_, v_type_1178_, v_semiringInst_1179_, v___y_1185_, v___y_1186_, v___y_1187_, v___y_1188_, v___y_1189_, v___y_1190_);
return v___x_1192_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_getNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isNatCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__2_spec__4_spec__6___boxed(lean_object* v_u_1193_, lean_object* v_type_1194_, lean_object* v_semiringInst_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_){
_start:
{
lean_object* v_res_1208_; 
v_res_1208_ = l_Lean_Meta_Grind_Arith_CommRing_mkNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_getNatCastFn___at___00Lean_Meta_Grind_Arith_CommRing_isNatCastInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__2_spec__4_spec__6(v_u_1193_, v_type_1194_, v_semiringInst_1195_, v___y_1196_, v___y_1197_, v___y_1198_, v___y_1199_, v___y_1200_, v___y_1201_, v___y_1202_, v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_);
lean_dec(v___y_1206_);
lean_dec_ref(v___y_1205_);
lean_dec(v___y_1204_);
lean_dec_ref(v___y_1203_);
lean_dec(v___y_1202_);
lean_dec_ref(v___y_1201_);
lean_dec(v___y_1200_);
lean_dec_ref(v___y_1199_);
lean_dec(v___y_1198_);
lean_dec(v___y_1197_);
lean_dec_ref(v___y_1196_);
return v_res_1208_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1_spec__5_spec__8(lean_object* v_00_u03b1_1209_, lean_object* v_msg_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_){
_start:
{
lean_object* v___x_1223_; 
v___x_1223_ = l_Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1_spec__5_spec__8___redArg(v_msg_1210_, v___y_1218_, v___y_1219_, v___y_1220_, v___y_1221_);
return v___x_1223_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1_spec__5_spec__8___boxed(lean_object* v_00_u03b1_1224_, lean_object* v_msg_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_){
_start:
{
lean_object* v_res_1238_; 
v_res_1238_ = l_Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1_spec__5_spec__8(v_00_u03b1_1224_, v_msg_1225_, v___y_1226_, v___y_1227_, v___y_1228_, v___y_1229_, v___y_1230_, v___y_1231_, v___y_1232_, v___y_1233_, v___y_1234_, v___y_1235_, v___y_1236_);
lean_dec(v___y_1236_);
lean_dec_ref(v___y_1235_);
lean_dec(v___y_1234_);
lean_dec_ref(v___y_1233_);
lean_dec(v___y_1232_);
lean_dec_ref(v___y_1231_);
lean_dec(v___y_1230_);
lean_dec_ref(v___y_1229_);
lean_dec(v___y_1228_);
lean_dec(v___y_1227_);
lean_dec_ref(v___y_1226_);
return v_res_1238_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___lam__0(lean_object* v_a_1239_, lean_object* v_s_1240_){
_start:
{
lean_object* v_toRing_1241_; lean_object* v_semiringId_x3f_1242_; lean_object* v_commSemiringInst_1243_; lean_object* v_commRingInst_1244_; lean_object* v_noZeroDivInst_x3f_1245_; lean_object* v_fieldInst_x3f_1246_; lean_object* v_powIdentityInst_x3f_1247_; lean_object* v_denoteEntries_1248_; lean_object* v_nextId_1249_; lean_object* v_steps_1250_; lean_object* v_queue_1251_; lean_object* v_basis_1252_; lean_object* v_diseqs_1253_; uint8_t v_recheck_1254_; lean_object* v_invSet_1255_; lean_object* v_powIdentityVarCount_1256_; lean_object* v_numEq0_x3f_1257_; uint8_t v_numEq0Updated_1258_; lean_object* v___x_1260_; uint8_t v_isShared_1261_; uint8_t v_isSharedCheck_1266_; 
v_toRing_1241_ = lean_ctor_get(v_s_1240_, 0);
v_semiringId_x3f_1242_ = lean_ctor_get(v_s_1240_, 2);
v_commSemiringInst_1243_ = lean_ctor_get(v_s_1240_, 3);
v_commRingInst_1244_ = lean_ctor_get(v_s_1240_, 4);
v_noZeroDivInst_x3f_1245_ = lean_ctor_get(v_s_1240_, 5);
v_fieldInst_x3f_1246_ = lean_ctor_get(v_s_1240_, 6);
v_powIdentityInst_x3f_1247_ = lean_ctor_get(v_s_1240_, 7);
v_denoteEntries_1248_ = lean_ctor_get(v_s_1240_, 8);
v_nextId_1249_ = lean_ctor_get(v_s_1240_, 9);
v_steps_1250_ = lean_ctor_get(v_s_1240_, 10);
v_queue_1251_ = lean_ctor_get(v_s_1240_, 11);
v_basis_1252_ = lean_ctor_get(v_s_1240_, 12);
v_diseqs_1253_ = lean_ctor_get(v_s_1240_, 13);
v_recheck_1254_ = lean_ctor_get_uint8(v_s_1240_, sizeof(void*)*17);
v_invSet_1255_ = lean_ctor_get(v_s_1240_, 14);
v_powIdentityVarCount_1256_ = lean_ctor_get(v_s_1240_, 15);
v_numEq0_x3f_1257_ = lean_ctor_get(v_s_1240_, 16);
v_numEq0Updated_1258_ = lean_ctor_get_uint8(v_s_1240_, sizeof(void*)*17 + 1);
v_isSharedCheck_1266_ = !lean_is_exclusive(v_s_1240_);
if (v_isSharedCheck_1266_ == 0)
{
lean_object* v_unused_1267_; 
v_unused_1267_ = lean_ctor_get(v_s_1240_, 1);
lean_dec(v_unused_1267_);
v___x_1260_ = v_s_1240_;
v_isShared_1261_ = v_isSharedCheck_1266_;
goto v_resetjp_1259_;
}
else
{
lean_inc(v_numEq0_x3f_1257_);
lean_inc(v_powIdentityVarCount_1256_);
lean_inc(v_invSet_1255_);
lean_inc(v_diseqs_1253_);
lean_inc(v_basis_1252_);
lean_inc(v_queue_1251_);
lean_inc(v_steps_1250_);
lean_inc(v_nextId_1249_);
lean_inc(v_denoteEntries_1248_);
lean_inc(v_powIdentityInst_x3f_1247_);
lean_inc(v_fieldInst_x3f_1246_);
lean_inc(v_noZeroDivInst_x3f_1245_);
lean_inc(v_commRingInst_1244_);
lean_inc(v_commSemiringInst_1243_);
lean_inc(v_semiringId_x3f_1242_);
lean_inc(v_toRing_1241_);
lean_dec(v_s_1240_);
v___x_1260_ = lean_box(0);
v_isShared_1261_ = v_isSharedCheck_1266_;
goto v_resetjp_1259_;
}
v_resetjp_1259_:
{
lean_object* v___x_1262_; lean_object* v___x_1264_; 
v___x_1262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1262_, 0, v_a_1239_);
if (v_isShared_1261_ == 0)
{
lean_ctor_set(v___x_1260_, 1, v___x_1262_);
v___x_1264_ = v___x_1260_;
goto v_reusejp_1263_;
}
else
{
lean_object* v_reuseFailAlloc_1265_; 
v_reuseFailAlloc_1265_ = lean_alloc_ctor(0, 17, 2);
lean_ctor_set(v_reuseFailAlloc_1265_, 0, v_toRing_1241_);
lean_ctor_set(v_reuseFailAlloc_1265_, 1, v___x_1262_);
lean_ctor_set(v_reuseFailAlloc_1265_, 2, v_semiringId_x3f_1242_);
lean_ctor_set(v_reuseFailAlloc_1265_, 3, v_commSemiringInst_1243_);
lean_ctor_set(v_reuseFailAlloc_1265_, 4, v_commRingInst_1244_);
lean_ctor_set(v_reuseFailAlloc_1265_, 5, v_noZeroDivInst_x3f_1245_);
lean_ctor_set(v_reuseFailAlloc_1265_, 6, v_fieldInst_x3f_1246_);
lean_ctor_set(v_reuseFailAlloc_1265_, 7, v_powIdentityInst_x3f_1247_);
lean_ctor_set(v_reuseFailAlloc_1265_, 8, v_denoteEntries_1248_);
lean_ctor_set(v_reuseFailAlloc_1265_, 9, v_nextId_1249_);
lean_ctor_set(v_reuseFailAlloc_1265_, 10, v_steps_1250_);
lean_ctor_set(v_reuseFailAlloc_1265_, 11, v_queue_1251_);
lean_ctor_set(v_reuseFailAlloc_1265_, 12, v_basis_1252_);
lean_ctor_set(v_reuseFailAlloc_1265_, 13, v_diseqs_1253_);
lean_ctor_set(v_reuseFailAlloc_1265_, 14, v_invSet_1255_);
lean_ctor_set(v_reuseFailAlloc_1265_, 15, v_powIdentityVarCount_1256_);
lean_ctor_set(v_reuseFailAlloc_1265_, 16, v_numEq0_x3f_1257_);
lean_ctor_set_uint8(v_reuseFailAlloc_1265_, sizeof(void*)*17, v_recheck_1254_);
lean_ctor_set_uint8(v_reuseFailAlloc_1265_, sizeof(void*)*17 + 1, v_numEq0Updated_1258_);
v___x_1264_ = v_reuseFailAlloc_1265_;
goto v_reusejp_1263_;
}
v_reusejp_1263_:
{
return v___x_1264_;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___closed__8(void){
_start:
{
lean_object* v___x_1283_; lean_object* v___x_1284_; 
v___x_1283_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___closed__7));
v___x_1284_ = l_Lean_stringToMessageData(v___x_1283_);
return v___x_1284_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0(lean_object* v___y_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_){
_start:
{
lean_object* v___x_1297_; 
v___x_1297_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v___y_1285_, v___y_1286_, v___y_1287_, v___y_1288_, v___y_1289_, v___y_1290_, v___y_1291_, v___y_1292_, v___y_1293_, v___y_1294_, v___y_1295_);
if (lean_obj_tag(v___x_1297_) == 0)
{
lean_object* v_a_1298_; lean_object* v___x_1300_; uint8_t v_isShared_1301_; uint8_t v_isSharedCheck_1345_; 
v_a_1298_ = lean_ctor_get(v___x_1297_, 0);
v_isSharedCheck_1345_ = !lean_is_exclusive(v___x_1297_);
if (v_isSharedCheck_1345_ == 0)
{
v___x_1300_ = v___x_1297_;
v_isShared_1301_ = v_isSharedCheck_1345_;
goto v_resetjp_1299_;
}
else
{
lean_inc(v_a_1298_);
lean_dec(v___x_1297_);
v___x_1300_ = lean_box(0);
v_isShared_1301_ = v_isSharedCheck_1345_;
goto v_resetjp_1299_;
}
v_resetjp_1299_:
{
lean_object* v_fieldInst_x3f_1302_; 
v_fieldInst_x3f_1302_ = lean_ctor_get(v_a_1298_, 6);
if (lean_obj_tag(v_fieldInst_x3f_1302_) == 1)
{
lean_object* v_invFn_x3f_1303_; 
lean_inc_ref(v_fieldInst_x3f_1302_);
v_invFn_x3f_1303_ = lean_ctor_get(v_a_1298_, 1);
if (lean_obj_tag(v_invFn_x3f_1303_) == 1)
{
lean_object* v_val_1304_; lean_object* v___x_1306_; 
lean_inc_ref(v_invFn_x3f_1303_);
lean_dec_ref_known(v_fieldInst_x3f_1302_, 1);
lean_dec(v_a_1298_);
v_val_1304_ = lean_ctor_get(v_invFn_x3f_1303_, 0);
lean_inc(v_val_1304_);
lean_dec_ref_known(v_invFn_x3f_1303_, 1);
if (v_isShared_1301_ == 0)
{
lean_ctor_set(v___x_1300_, 0, v_val_1304_);
v___x_1306_ = v___x_1300_;
goto v_reusejp_1305_;
}
else
{
lean_object* v_reuseFailAlloc_1307_; 
v_reuseFailAlloc_1307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1307_, 0, v_val_1304_);
v___x_1306_ = v_reuseFailAlloc_1307_;
goto v_reusejp_1305_;
}
v_reusejp_1305_:
{
return v___x_1306_;
}
}
else
{
lean_object* v_toRing_1308_; lean_object* v_val_1309_; lean_object* v_type_1310_; lean_object* v_u_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v_expectedInst_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; 
lean_del_object(v___x_1300_);
v_toRing_1308_ = lean_ctor_get(v_a_1298_, 0);
lean_inc_ref(v_toRing_1308_);
lean_dec(v_a_1298_);
v_val_1309_ = lean_ctor_get(v_fieldInst_x3f_1302_, 0);
lean_inc(v_val_1309_);
lean_dec_ref_known(v_fieldInst_x3f_1302_, 1);
v_type_1310_ = lean_ctor_get(v_toRing_1308_, 1);
lean_inc_ref_n(v_type_1310_, 2);
v_u_1311_ = lean_ctor_get(v_toRing_1308_, 2);
lean_inc_n(v_u_1311_, 2);
lean_dec_ref(v_toRing_1308_);
v___x_1312_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___closed__2));
v___x_1313_ = lean_box(0);
v___x_1314_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1314_, 0, v_u_1311_);
lean_ctor_set(v___x_1314_, 1, v___x_1313_);
v___x_1315_ = l_Lean_mkConst(v___x_1312_, v___x_1314_);
v_expectedInst_1316_ = l_Lean_mkAppB(v___x_1315_, v_type_1310_, v_val_1309_);
v___x_1317_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___closed__4));
v___x_1318_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___closed__6));
v___x_1319_ = l_Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1(v_type_1310_, v_u_1311_, v___x_1317_, v___x_1318_, v_expectedInst_1316_, v___y_1285_, v___y_1286_, v___y_1287_, v___y_1288_, v___y_1289_, v___y_1290_, v___y_1291_, v___y_1292_, v___y_1293_, v___y_1294_, v___y_1295_);
if (lean_obj_tag(v___x_1319_) == 0)
{
lean_object* v_a_1320_; lean_object* v___f_1321_; lean_object* v___x_1322_; 
v_a_1320_ = lean_ctor_get(v___x_1319_, 0);
lean_inc_n(v_a_1320_, 2);
lean_dec_ref_known(v___x_1319_, 1);
v___f_1321_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___lam__0), 2, 1);
lean_closure_set(v___f_1321_, 0, v_a_1320_);
v___x_1322_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(v___f_1321_, v___y_1285_, v___y_1286_);
if (lean_obj_tag(v___x_1322_) == 0)
{
lean_object* v___x_1324_; uint8_t v_isShared_1325_; uint8_t v_isSharedCheck_1329_; 
v_isSharedCheck_1329_ = !lean_is_exclusive(v___x_1322_);
if (v_isSharedCheck_1329_ == 0)
{
lean_object* v_unused_1330_; 
v_unused_1330_ = lean_ctor_get(v___x_1322_, 0);
lean_dec(v_unused_1330_);
v___x_1324_ = v___x_1322_;
v_isShared_1325_ = v_isSharedCheck_1329_;
goto v_resetjp_1323_;
}
else
{
lean_dec(v___x_1322_);
v___x_1324_ = lean_box(0);
v_isShared_1325_ = v_isSharedCheck_1329_;
goto v_resetjp_1323_;
}
v_resetjp_1323_:
{
lean_object* v___x_1327_; 
if (v_isShared_1325_ == 0)
{
lean_ctor_set(v___x_1324_, 0, v_a_1320_);
v___x_1327_ = v___x_1324_;
goto v_reusejp_1326_;
}
else
{
lean_object* v_reuseFailAlloc_1328_; 
v_reuseFailAlloc_1328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1328_, 0, v_a_1320_);
v___x_1327_ = v_reuseFailAlloc_1328_;
goto v_reusejp_1326_;
}
v_reusejp_1326_:
{
return v___x_1327_;
}
}
}
else
{
lean_object* v_a_1331_; lean_object* v___x_1333_; uint8_t v_isShared_1334_; uint8_t v_isSharedCheck_1338_; 
lean_dec(v_a_1320_);
v_a_1331_ = lean_ctor_get(v___x_1322_, 0);
v_isSharedCheck_1338_ = !lean_is_exclusive(v___x_1322_);
if (v_isSharedCheck_1338_ == 0)
{
v___x_1333_ = v___x_1322_;
v_isShared_1334_ = v_isSharedCheck_1338_;
goto v_resetjp_1332_;
}
else
{
lean_inc(v_a_1331_);
lean_dec(v___x_1322_);
v___x_1333_ = lean_box(0);
v_isShared_1334_ = v_isSharedCheck_1338_;
goto v_resetjp_1332_;
}
v_resetjp_1332_:
{
lean_object* v___x_1336_; 
if (v_isShared_1334_ == 0)
{
v___x_1336_ = v___x_1333_;
goto v_reusejp_1335_;
}
else
{
lean_object* v_reuseFailAlloc_1337_; 
v_reuseFailAlloc_1337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1337_, 0, v_a_1331_);
v___x_1336_ = v_reuseFailAlloc_1337_;
goto v_reusejp_1335_;
}
v_reusejp_1335_:
{
return v___x_1336_;
}
}
}
}
else
{
return v___x_1319_;
}
}
}
else
{
lean_object* v_toRing_1339_; lean_object* v_type_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; 
lean_del_object(v___x_1300_);
v_toRing_1339_ = lean_ctor_get(v_a_1298_, 0);
lean_inc_ref(v_toRing_1339_);
lean_dec(v_a_1298_);
v_type_1340_ = lean_ctor_get(v_toRing_1339_, 1);
lean_inc_ref(v_type_1340_);
lean_dec_ref(v_toRing_1339_);
v___x_1341_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___closed__8, &l_Lean_Meta_Grind_Arith_CommRing_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___closed__8_once, _init_l_Lean_Meta_Grind_Arith_CommRing_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___closed__8);
v___x_1342_ = l_Lean_indentExpr(v_type_1340_);
v___x_1343_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1343_, 0, v___x_1341_);
lean_ctor_set(v___x_1343_, 1, v___x_1342_);
v___x_1344_ = l_Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1_spec__5_spec__8___redArg(v___x_1343_, v___y_1292_, v___y_1293_, v___y_1294_, v___y_1295_);
return v___x_1344_;
}
}
}
else
{
lean_object* v_a_1346_; lean_object* v___x_1348_; uint8_t v_isShared_1349_; uint8_t v_isSharedCheck_1353_; 
v_a_1346_ = lean_ctor_get(v___x_1297_, 0);
v_isSharedCheck_1353_ = !lean_is_exclusive(v___x_1297_);
if (v_isSharedCheck_1353_ == 0)
{
v___x_1348_ = v___x_1297_;
v_isShared_1349_ = v_isSharedCheck_1353_;
goto v_resetjp_1347_;
}
else
{
lean_inc(v_a_1346_);
lean_dec(v___x_1297_);
v___x_1348_ = lean_box(0);
v_isShared_1349_ = v_isSharedCheck_1353_;
goto v_resetjp_1347_;
}
v_resetjp_1347_:
{
lean_object* v___x_1351_; 
if (v_isShared_1349_ == 0)
{
v___x_1351_ = v___x_1348_;
goto v_reusejp_1350_;
}
else
{
lean_object* v_reuseFailAlloc_1352_; 
v_reuseFailAlloc_1352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1352_, 0, v_a_1346_);
v___x_1351_ = v_reuseFailAlloc_1352_;
goto v_reusejp_1350_;
}
v_reusejp_1350_:
{
return v___x_1351_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___boxed(lean_object* v___y_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_){
_start:
{
lean_object* v_res_1366_; 
v_res_1366_ = l_Lean_Meta_Grind_Arith_CommRing_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0(v___y_1354_, v___y_1355_, v___y_1356_, v___y_1357_, v___y_1358_, v___y_1359_, v___y_1360_, v___y_1361_, v___y_1362_, v___y_1363_, v___y_1364_);
lean_dec(v___y_1364_);
lean_dec_ref(v___y_1363_);
lean_dec(v___y_1362_);
lean_dec_ref(v___y_1361_);
lean_dec(v___y_1360_);
lean_dec_ref(v___y_1359_);
lean_dec(v___y_1358_);
lean_dec_ref(v___y_1357_);
lean_dec(v___y_1356_);
lean_dec(v___y_1355_);
lean_dec_ref(v___y_1354_);
return v_res_1366_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst(lean_object* v_inst_1367_, lean_object* v_a_1368_, lean_object* v_a_1369_, lean_object* v_a_1370_, lean_object* v_a_1371_, lean_object* v_a_1372_, lean_object* v_a_1373_, lean_object* v_a_1374_, lean_object* v_a_1375_, lean_object* v_a_1376_, lean_object* v_a_1377_, lean_object* v_a_1378_){
_start:
{
lean_object* v___x_1380_; 
v___x_1380_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v_a_1368_, v_a_1369_, v_a_1370_, v_a_1371_, v_a_1372_, v_a_1373_, v_a_1374_, v_a_1375_, v_a_1376_, v_a_1377_, v_a_1378_);
if (lean_obj_tag(v___x_1380_) == 0)
{
lean_object* v_a_1381_; lean_object* v___x_1383_; uint8_t v_isShared_1384_; uint8_t v_isSharedCheck_1413_; 
v_a_1381_ = lean_ctor_get(v___x_1380_, 0);
v_isSharedCheck_1413_ = !lean_is_exclusive(v___x_1380_);
if (v_isSharedCheck_1413_ == 0)
{
v___x_1383_ = v___x_1380_;
v_isShared_1384_ = v_isSharedCheck_1413_;
goto v_resetjp_1382_;
}
else
{
lean_inc(v_a_1381_);
lean_dec(v___x_1380_);
v___x_1383_ = lean_box(0);
v_isShared_1384_ = v_isSharedCheck_1413_;
goto v_resetjp_1382_;
}
v_resetjp_1382_:
{
lean_object* v_fieldInst_x3f_1385_; 
v_fieldInst_x3f_1385_ = lean_ctor_get(v_a_1381_, 6);
lean_inc(v_fieldInst_x3f_1385_);
lean_dec(v_a_1381_);
if (lean_obj_tag(v_fieldInst_x3f_1385_) == 0)
{
uint8_t v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1389_; 
v___x_1386_ = 0;
v___x_1387_ = lean_box(v___x_1386_);
if (v_isShared_1384_ == 0)
{
lean_ctor_set(v___x_1383_, 0, v___x_1387_);
v___x_1389_ = v___x_1383_;
goto v_reusejp_1388_;
}
else
{
lean_object* v_reuseFailAlloc_1390_; 
v_reuseFailAlloc_1390_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1390_, 0, v___x_1387_);
v___x_1389_ = v_reuseFailAlloc_1390_;
goto v_reusejp_1388_;
}
v_reusejp_1388_:
{
return v___x_1389_;
}
}
else
{
lean_object* v___x_1391_; 
lean_dec_ref_known(v_fieldInst_x3f_1385_, 1);
lean_del_object(v___x_1383_);
v___x_1391_ = l_Lean_Meta_Grind_Arith_CommRing_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0(v_a_1368_, v_a_1369_, v_a_1370_, v_a_1371_, v_a_1372_, v_a_1373_, v_a_1374_, v_a_1375_, v_a_1376_, v_a_1377_, v_a_1378_);
if (lean_obj_tag(v___x_1391_) == 0)
{
lean_object* v_a_1392_; lean_object* v___x_1394_; uint8_t v_isShared_1395_; uint8_t v_isSharedCheck_1404_; 
v_a_1392_ = lean_ctor_get(v___x_1391_, 0);
v_isSharedCheck_1404_ = !lean_is_exclusive(v___x_1391_);
if (v_isSharedCheck_1404_ == 0)
{
v___x_1394_ = v___x_1391_;
v_isShared_1395_ = v_isSharedCheck_1404_;
goto v_resetjp_1393_;
}
else
{
lean_inc(v_a_1392_);
lean_dec(v___x_1391_);
v___x_1394_ = lean_box(0);
v_isShared_1395_ = v_isSharedCheck_1404_;
goto v_resetjp_1393_;
}
v_resetjp_1393_:
{
lean_object* v___x_1396_; size_t v___x_1397_; size_t v___x_1398_; uint8_t v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1402_; 
v___x_1396_ = l_Lean_Expr_appArg_x21(v_a_1392_);
lean_dec(v_a_1392_);
v___x_1397_ = lean_ptr_addr(v___x_1396_);
lean_dec_ref(v___x_1396_);
v___x_1398_ = lean_ptr_addr(v_inst_1367_);
v___x_1399_ = lean_usize_dec_eq(v___x_1397_, v___x_1398_);
v___x_1400_ = lean_box(v___x_1399_);
if (v_isShared_1395_ == 0)
{
lean_ctor_set(v___x_1394_, 0, v___x_1400_);
v___x_1402_ = v___x_1394_;
goto v_reusejp_1401_;
}
else
{
lean_object* v_reuseFailAlloc_1403_; 
v_reuseFailAlloc_1403_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1403_, 0, v___x_1400_);
v___x_1402_ = v_reuseFailAlloc_1403_;
goto v_reusejp_1401_;
}
v_reusejp_1401_:
{
return v___x_1402_;
}
}
}
else
{
lean_object* v_a_1405_; lean_object* v___x_1407_; uint8_t v_isShared_1408_; uint8_t v_isSharedCheck_1412_; 
v_a_1405_ = lean_ctor_get(v___x_1391_, 0);
v_isSharedCheck_1412_ = !lean_is_exclusive(v___x_1391_);
if (v_isSharedCheck_1412_ == 0)
{
v___x_1407_ = v___x_1391_;
v_isShared_1408_ = v_isSharedCheck_1412_;
goto v_resetjp_1406_;
}
else
{
lean_inc(v_a_1405_);
lean_dec(v___x_1391_);
v___x_1407_ = lean_box(0);
v_isShared_1408_ = v_isSharedCheck_1412_;
goto v_resetjp_1406_;
}
v_resetjp_1406_:
{
lean_object* v___x_1410_; 
if (v_isShared_1408_ == 0)
{
v___x_1410_ = v___x_1407_;
goto v_reusejp_1409_;
}
else
{
lean_object* v_reuseFailAlloc_1411_; 
v_reuseFailAlloc_1411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1411_, 0, v_a_1405_);
v___x_1410_ = v_reuseFailAlloc_1411_;
goto v_reusejp_1409_;
}
v_reusejp_1409_:
{
return v___x_1410_;
}
}
}
}
}
}
else
{
lean_object* v_a_1414_; lean_object* v___x_1416_; uint8_t v_isShared_1417_; uint8_t v_isSharedCheck_1421_; 
v_a_1414_ = lean_ctor_get(v___x_1380_, 0);
v_isSharedCheck_1421_ = !lean_is_exclusive(v___x_1380_);
if (v_isSharedCheck_1421_ == 0)
{
v___x_1416_ = v___x_1380_;
v_isShared_1417_ = v_isSharedCheck_1421_;
goto v_resetjp_1415_;
}
else
{
lean_inc(v_a_1414_);
lean_dec(v___x_1380_);
v___x_1416_ = lean_box(0);
v_isShared_1417_ = v_isSharedCheck_1421_;
goto v_resetjp_1415_;
}
v_resetjp_1415_:
{
lean_object* v___x_1419_; 
if (v_isShared_1417_ == 0)
{
v___x_1419_ = v___x_1416_;
goto v_reusejp_1418_;
}
else
{
lean_object* v_reuseFailAlloc_1420_; 
v_reuseFailAlloc_1420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1420_, 0, v_a_1414_);
v___x_1419_ = v_reuseFailAlloc_1420_;
goto v_reusejp_1418_;
}
v_reusejp_1418_:
{
return v___x_1419_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst___boxed(lean_object* v_inst_1422_, lean_object* v_a_1423_, lean_object* v_a_1424_, lean_object* v_a_1425_, lean_object* v_a_1426_, lean_object* v_a_1427_, lean_object* v_a_1428_, lean_object* v_a_1429_, lean_object* v_a_1430_, lean_object* v_a_1431_, lean_object* v_a_1432_, lean_object* v_a_1433_, lean_object* v_a_1434_){
_start:
{
lean_object* v_res_1435_; 
v_res_1435_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst(v_inst_1422_, v_a_1423_, v_a_1424_, v_a_1425_, v_a_1426_, v_a_1427_, v_a_1428_, v_a_1429_, v_a_1430_, v_a_1431_, v_a_1432_, v_a_1433_);
lean_dec(v_a_1433_);
lean_dec_ref(v_a_1432_);
lean_dec(v_a_1431_);
lean_dec_ref(v_a_1430_);
lean_dec(v_a_1429_);
lean_dec_ref(v_a_1428_);
lean_dec(v_a_1427_);
lean_dec_ref(v_a_1426_);
lean_dec(v_a_1425_);
lean_dec(v_a_1424_);
lean_dec_ref(v_a_1423_);
lean_dec_ref(v_inst_1422_);
return v_res_1435_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__2(lean_object* v_a_1436_){
_start:
{
lean_object* v___x_1437_; 
v___x_1437_ = lean_nat_to_int(v_a_1436_);
return v___x_1437_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0_spec__2_spec__6___redArg(lean_object* v_x_1438_, lean_object* v_x_1439_, lean_object* v_x_1440_, lean_object* v_x_1441_){
_start:
{
lean_object* v_ks_1442_; lean_object* v_vs_1443_; lean_object* v___x_1445_; uint8_t v_isShared_1446_; uint8_t v_isSharedCheck_1467_; 
v_ks_1442_ = lean_ctor_get(v_x_1438_, 0);
v_vs_1443_ = lean_ctor_get(v_x_1438_, 1);
v_isSharedCheck_1467_ = !lean_is_exclusive(v_x_1438_);
if (v_isSharedCheck_1467_ == 0)
{
v___x_1445_ = v_x_1438_;
v_isShared_1446_ = v_isSharedCheck_1467_;
goto v_resetjp_1444_;
}
else
{
lean_inc(v_vs_1443_);
lean_inc(v_ks_1442_);
lean_dec(v_x_1438_);
v___x_1445_ = lean_box(0);
v_isShared_1446_ = v_isSharedCheck_1467_;
goto v_resetjp_1444_;
}
v_resetjp_1444_:
{
lean_object* v___x_1447_; uint8_t v___x_1448_; 
v___x_1447_ = lean_array_get_size(v_ks_1442_);
v___x_1448_ = lean_nat_dec_lt(v_x_1439_, v___x_1447_);
if (v___x_1448_ == 0)
{
lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1452_; 
lean_dec(v_x_1439_);
v___x_1449_ = lean_array_push(v_ks_1442_, v_x_1440_);
v___x_1450_ = lean_array_push(v_vs_1443_, v_x_1441_);
if (v_isShared_1446_ == 0)
{
lean_ctor_set(v___x_1445_, 1, v___x_1450_);
lean_ctor_set(v___x_1445_, 0, v___x_1449_);
v___x_1452_ = v___x_1445_;
goto v_reusejp_1451_;
}
else
{
lean_object* v_reuseFailAlloc_1453_; 
v_reuseFailAlloc_1453_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1453_, 0, v___x_1449_);
lean_ctor_set(v_reuseFailAlloc_1453_, 1, v___x_1450_);
v___x_1452_ = v_reuseFailAlloc_1453_;
goto v_reusejp_1451_;
}
v_reusejp_1451_:
{
return v___x_1452_;
}
}
else
{
lean_object* v_k_x27_1454_; uint8_t v___x_1455_; 
v_k_x27_1454_ = lean_array_fget_borrowed(v_ks_1442_, v_x_1439_);
v___x_1455_ = lean_expr_eqv(v_x_1440_, v_k_x27_1454_);
if (v___x_1455_ == 0)
{
lean_object* v___x_1457_; 
if (v_isShared_1446_ == 0)
{
v___x_1457_ = v___x_1445_;
goto v_reusejp_1456_;
}
else
{
lean_object* v_reuseFailAlloc_1461_; 
v_reuseFailAlloc_1461_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1461_, 0, v_ks_1442_);
lean_ctor_set(v_reuseFailAlloc_1461_, 1, v_vs_1443_);
v___x_1457_ = v_reuseFailAlloc_1461_;
goto v_reusejp_1456_;
}
v_reusejp_1456_:
{
lean_object* v___x_1458_; lean_object* v___x_1459_; 
v___x_1458_ = lean_unsigned_to_nat(1u);
v___x_1459_ = lean_nat_add(v_x_1439_, v___x_1458_);
lean_dec(v_x_1439_);
v_x_1438_ = v___x_1457_;
v_x_1439_ = v___x_1459_;
goto _start;
}
}
else
{
lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1465_; 
v___x_1462_ = lean_array_fset(v_ks_1442_, v_x_1439_, v_x_1440_);
v___x_1463_ = lean_array_fset(v_vs_1443_, v_x_1439_, v_x_1441_);
lean_dec(v_x_1439_);
if (v_isShared_1446_ == 0)
{
lean_ctor_set(v___x_1445_, 1, v___x_1463_);
lean_ctor_set(v___x_1445_, 0, v___x_1462_);
v___x_1465_ = v___x_1445_;
goto v_reusejp_1464_;
}
else
{
lean_object* v_reuseFailAlloc_1466_; 
v_reuseFailAlloc_1466_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1466_, 0, v___x_1462_);
lean_ctor_set(v_reuseFailAlloc_1466_, 1, v___x_1463_);
v___x_1465_ = v_reuseFailAlloc_1466_;
goto v_reusejp_1464_;
}
v_reusejp_1464_:
{
return v___x_1465_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0_spec__2___redArg(lean_object* v_n_1468_, lean_object* v_k_1469_, lean_object* v_v_1470_){
_start:
{
lean_object* v___x_1471_; lean_object* v___x_1472_; 
v___x_1471_ = lean_unsigned_to_nat(0u);
v___x_1472_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0_spec__2_spec__6___redArg(v_n_1468_, v___x_1471_, v_k_1469_, v_v_1470_);
return v___x_1472_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1473_; 
v___x_1473_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1473_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg(lean_object* v_x_1474_, size_t v_x_1475_, size_t v_x_1476_, lean_object* v_x_1477_, lean_object* v_x_1478_){
_start:
{
if (lean_obj_tag(v_x_1474_) == 0)
{
lean_object* v_es_1479_; size_t v___x_1480_; size_t v___x_1481_; lean_object* v_j_1482_; lean_object* v___x_1483_; uint8_t v___x_1484_; 
v_es_1479_ = lean_ctor_get(v_x_1474_, 0);
v___x_1480_ = ((size_t)31ULL);
v___x_1481_ = lean_usize_land(v_x_1475_, v___x_1480_);
v_j_1482_ = lean_usize_to_nat(v___x_1481_);
v___x_1483_ = lean_array_get_size(v_es_1479_);
v___x_1484_ = lean_nat_dec_lt(v_j_1482_, v___x_1483_);
if (v___x_1484_ == 0)
{
lean_dec(v_j_1482_);
lean_dec(v_x_1478_);
lean_dec_ref(v_x_1477_);
return v_x_1474_;
}
else
{
lean_object* v___x_1486_; uint8_t v_isShared_1487_; uint8_t v_isSharedCheck_1523_; 
lean_inc_ref(v_es_1479_);
v_isSharedCheck_1523_ = !lean_is_exclusive(v_x_1474_);
if (v_isSharedCheck_1523_ == 0)
{
lean_object* v_unused_1524_; 
v_unused_1524_ = lean_ctor_get(v_x_1474_, 0);
lean_dec(v_unused_1524_);
v___x_1486_ = v_x_1474_;
v_isShared_1487_ = v_isSharedCheck_1523_;
goto v_resetjp_1485_;
}
else
{
lean_dec(v_x_1474_);
v___x_1486_ = lean_box(0);
v_isShared_1487_ = v_isSharedCheck_1523_;
goto v_resetjp_1485_;
}
v_resetjp_1485_:
{
lean_object* v_v_1488_; lean_object* v___x_1489_; lean_object* v_xs_x27_1490_; lean_object* v___y_1492_; 
v_v_1488_ = lean_array_fget(v_es_1479_, v_j_1482_);
v___x_1489_ = lean_box(0);
v_xs_x27_1490_ = lean_array_fset(v_es_1479_, v_j_1482_, v___x_1489_);
switch(lean_obj_tag(v_v_1488_))
{
case 0:
{
lean_object* v_key_1497_; lean_object* v_val_1498_; lean_object* v___x_1500_; uint8_t v_isShared_1501_; uint8_t v_isSharedCheck_1508_; 
v_key_1497_ = lean_ctor_get(v_v_1488_, 0);
v_val_1498_ = lean_ctor_get(v_v_1488_, 1);
v_isSharedCheck_1508_ = !lean_is_exclusive(v_v_1488_);
if (v_isSharedCheck_1508_ == 0)
{
v___x_1500_ = v_v_1488_;
v_isShared_1501_ = v_isSharedCheck_1508_;
goto v_resetjp_1499_;
}
else
{
lean_inc(v_val_1498_);
lean_inc(v_key_1497_);
lean_dec(v_v_1488_);
v___x_1500_ = lean_box(0);
v_isShared_1501_ = v_isSharedCheck_1508_;
goto v_resetjp_1499_;
}
v_resetjp_1499_:
{
uint8_t v___x_1502_; 
v___x_1502_ = lean_expr_eqv(v_x_1477_, v_key_1497_);
if (v___x_1502_ == 0)
{
lean_object* v___x_1503_; lean_object* v___x_1504_; 
lean_del_object(v___x_1500_);
v___x_1503_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1497_, v_val_1498_, v_x_1477_, v_x_1478_);
v___x_1504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1504_, 0, v___x_1503_);
v___y_1492_ = v___x_1504_;
goto v___jp_1491_;
}
else
{
lean_object* v___x_1506_; 
lean_dec(v_val_1498_);
lean_dec(v_key_1497_);
if (v_isShared_1501_ == 0)
{
lean_ctor_set(v___x_1500_, 1, v_x_1478_);
lean_ctor_set(v___x_1500_, 0, v_x_1477_);
v___x_1506_ = v___x_1500_;
goto v_reusejp_1505_;
}
else
{
lean_object* v_reuseFailAlloc_1507_; 
v_reuseFailAlloc_1507_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1507_, 0, v_x_1477_);
lean_ctor_set(v_reuseFailAlloc_1507_, 1, v_x_1478_);
v___x_1506_ = v_reuseFailAlloc_1507_;
goto v_reusejp_1505_;
}
v_reusejp_1505_:
{
v___y_1492_ = v___x_1506_;
goto v___jp_1491_;
}
}
}
}
case 1:
{
lean_object* v_node_1509_; lean_object* v___x_1511_; uint8_t v_isShared_1512_; uint8_t v_isSharedCheck_1521_; 
v_node_1509_ = lean_ctor_get(v_v_1488_, 0);
v_isSharedCheck_1521_ = !lean_is_exclusive(v_v_1488_);
if (v_isSharedCheck_1521_ == 0)
{
v___x_1511_ = v_v_1488_;
v_isShared_1512_ = v_isSharedCheck_1521_;
goto v_resetjp_1510_;
}
else
{
lean_inc(v_node_1509_);
lean_dec(v_v_1488_);
v___x_1511_ = lean_box(0);
v_isShared_1512_ = v_isSharedCheck_1521_;
goto v_resetjp_1510_;
}
v_resetjp_1510_:
{
size_t v___x_1513_; size_t v___x_1514_; size_t v___x_1515_; size_t v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1519_; 
v___x_1513_ = ((size_t)5ULL);
v___x_1514_ = lean_usize_shift_right(v_x_1475_, v___x_1513_);
v___x_1515_ = ((size_t)1ULL);
v___x_1516_ = lean_usize_add(v_x_1476_, v___x_1515_);
v___x_1517_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg(v_node_1509_, v___x_1514_, v___x_1516_, v_x_1477_, v_x_1478_);
if (v_isShared_1512_ == 0)
{
lean_ctor_set(v___x_1511_, 0, v___x_1517_);
v___x_1519_ = v___x_1511_;
goto v_reusejp_1518_;
}
else
{
lean_object* v_reuseFailAlloc_1520_; 
v_reuseFailAlloc_1520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1520_, 0, v___x_1517_);
v___x_1519_ = v_reuseFailAlloc_1520_;
goto v_reusejp_1518_;
}
v_reusejp_1518_:
{
v___y_1492_ = v___x_1519_;
goto v___jp_1491_;
}
}
}
default: 
{
lean_object* v___x_1522_; 
v___x_1522_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1522_, 0, v_x_1477_);
lean_ctor_set(v___x_1522_, 1, v_x_1478_);
v___y_1492_ = v___x_1522_;
goto v___jp_1491_;
}
}
v___jp_1491_:
{
lean_object* v___x_1493_; lean_object* v___x_1495_; 
v___x_1493_ = lean_array_fset(v_xs_x27_1490_, v_j_1482_, v___y_1492_);
lean_dec(v_j_1482_);
if (v_isShared_1487_ == 0)
{
lean_ctor_set(v___x_1486_, 0, v___x_1493_);
v___x_1495_ = v___x_1486_;
goto v_reusejp_1494_;
}
else
{
lean_object* v_reuseFailAlloc_1496_; 
v_reuseFailAlloc_1496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1496_, 0, v___x_1493_);
v___x_1495_ = v_reuseFailAlloc_1496_;
goto v_reusejp_1494_;
}
v_reusejp_1494_:
{
return v___x_1495_;
}
}
}
}
}
else
{
lean_object* v_ks_1525_; lean_object* v_vs_1526_; lean_object* v___x_1528_; uint8_t v_isShared_1529_; uint8_t v_isSharedCheck_1544_; 
v_ks_1525_ = lean_ctor_get(v_x_1474_, 0);
v_vs_1526_ = lean_ctor_get(v_x_1474_, 1);
v_isSharedCheck_1544_ = !lean_is_exclusive(v_x_1474_);
if (v_isSharedCheck_1544_ == 0)
{
v___x_1528_ = v_x_1474_;
v_isShared_1529_ = v_isSharedCheck_1544_;
goto v_resetjp_1527_;
}
else
{
lean_inc(v_vs_1526_);
lean_inc(v_ks_1525_);
lean_dec(v_x_1474_);
v___x_1528_ = lean_box(0);
v_isShared_1529_ = v_isSharedCheck_1544_;
goto v_resetjp_1527_;
}
v_resetjp_1527_:
{
lean_object* v___x_1531_; 
if (v_isShared_1529_ == 0)
{
v___x_1531_ = v___x_1528_;
goto v_reusejp_1530_;
}
else
{
lean_object* v_reuseFailAlloc_1543_; 
v_reuseFailAlloc_1543_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1543_, 0, v_ks_1525_);
lean_ctor_set(v_reuseFailAlloc_1543_, 1, v_vs_1526_);
v___x_1531_ = v_reuseFailAlloc_1543_;
goto v_reusejp_1530_;
}
v_reusejp_1530_:
{
lean_object* v_newNode_1532_; size_t v___x_1533_; uint8_t v___x_1534_; 
v_newNode_1532_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0_spec__2___redArg(v___x_1531_, v_x_1477_, v_x_1478_);
v___x_1533_ = ((size_t)7ULL);
v___x_1534_ = lean_usize_dec_le(v___x_1533_, v_x_1476_);
if (v___x_1534_ == 0)
{
lean_object* v___x_1535_; lean_object* v___x_1536_; uint8_t v___x_1537_; 
v___x_1535_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1532_);
v___x_1536_ = lean_unsigned_to_nat(4u);
v___x_1537_ = lean_nat_dec_lt(v___x_1535_, v___x_1536_);
lean_dec(v___x_1535_);
if (v___x_1537_ == 0)
{
lean_object* v_ks_1538_; lean_object* v_vs_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; 
v_ks_1538_ = lean_ctor_get(v_newNode_1532_, 0);
lean_inc_ref(v_ks_1538_);
v_vs_1539_ = lean_ctor_get(v_newNode_1532_, 1);
lean_inc_ref(v_vs_1539_);
lean_dec_ref(v_newNode_1532_);
v___x_1540_ = lean_unsigned_to_nat(0u);
v___x_1541_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg___closed__0);
v___x_1542_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0_spec__3___redArg(v_x_1476_, v_ks_1538_, v_vs_1539_, v___x_1540_, v___x_1541_);
lean_dec_ref(v_vs_1539_);
lean_dec_ref(v_ks_1538_);
return v___x_1542_;
}
else
{
return v_newNode_1532_;
}
}
else
{
return v_newNode_1532_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0_spec__3___redArg(size_t v_depth_1545_, lean_object* v_keys_1546_, lean_object* v_vals_1547_, lean_object* v_i_1548_, lean_object* v_entries_1549_){
_start:
{
lean_object* v___x_1550_; uint8_t v___x_1551_; 
v___x_1550_ = lean_array_get_size(v_keys_1546_);
v___x_1551_ = lean_nat_dec_lt(v_i_1548_, v___x_1550_);
if (v___x_1551_ == 0)
{
lean_dec(v_i_1548_);
return v_entries_1549_;
}
else
{
lean_object* v_k_1552_; lean_object* v_v_1553_; uint64_t v___x_1554_; size_t v_h_1555_; size_t v___x_1556_; lean_object* v___x_1557_; size_t v___x_1558_; size_t v___x_1559_; size_t v___x_1560_; size_t v_h_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; 
v_k_1552_ = lean_array_fget_borrowed(v_keys_1546_, v_i_1548_);
v_v_1553_ = lean_array_fget_borrowed(v_vals_1547_, v_i_1548_);
v___x_1554_ = l_Lean_Expr_hash(v_k_1552_);
v_h_1555_ = lean_uint64_to_usize(v___x_1554_);
v___x_1556_ = ((size_t)5ULL);
v___x_1557_ = lean_unsigned_to_nat(1u);
v___x_1558_ = ((size_t)1ULL);
v___x_1559_ = lean_usize_sub(v_depth_1545_, v___x_1558_);
v___x_1560_ = lean_usize_mul(v___x_1556_, v___x_1559_);
v_h_1561_ = lean_usize_shift_right(v_h_1555_, v___x_1560_);
v___x_1562_ = lean_nat_add(v_i_1548_, v___x_1557_);
lean_dec(v_i_1548_);
lean_inc(v_v_1553_);
lean_inc(v_k_1552_);
v___x_1563_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg(v_entries_1549_, v_h_1561_, v_depth_1545_, v_k_1552_, v_v_1553_);
v_i_1548_ = v___x_1562_;
v_entries_1549_ = v___x_1563_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_depth_1565_, lean_object* v_keys_1566_, lean_object* v_vals_1567_, lean_object* v_i_1568_, lean_object* v_entries_1569_){
_start:
{
size_t v_depth_boxed_1570_; lean_object* v_res_1571_; 
v_depth_boxed_1570_ = lean_unbox_usize(v_depth_1565_);
lean_dec(v_depth_1565_);
v_res_1571_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0_spec__3___redArg(v_depth_boxed_1570_, v_keys_1566_, v_vals_1567_, v_i_1568_, v_entries_1569_);
lean_dec_ref(v_vals_1567_);
lean_dec_ref(v_keys_1566_);
return v_res_1571_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg___boxed(lean_object* v_x_1572_, lean_object* v_x_1573_, lean_object* v_x_1574_, lean_object* v_x_1575_, lean_object* v_x_1576_){
_start:
{
size_t v_x_81056__boxed_1577_; size_t v_x_81057__boxed_1578_; lean_object* v_res_1579_; 
v_x_81056__boxed_1577_ = lean_unbox_usize(v_x_1573_);
lean_dec(v_x_1573_);
v_x_81057__boxed_1578_ = lean_unbox_usize(v_x_1574_);
lean_dec(v_x_1574_);
v_res_1579_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg(v_x_1572_, v_x_81056__boxed_1577_, v_x_81057__boxed_1578_, v_x_1575_, v_x_1576_);
return v_res_1579_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0___redArg(lean_object* v_x_1580_, lean_object* v_x_1581_, lean_object* v_x_1582_){
_start:
{
uint64_t v___x_1583_; size_t v___x_1584_; size_t v___x_1585_; lean_object* v___x_1586_; 
v___x_1583_ = l_Lean_Expr_hash(v_x_1581_);
v___x_1584_ = lean_uint64_to_usize(v___x_1583_);
v___x_1585_ = ((size_t)1ULL);
v___x_1586_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg(v_x_1580_, v___x_1584_, v___x_1585_, v_x_1581_, v_x_1582_);
return v___x_1586_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___lam__0(lean_object* v_a_1587_, lean_object* v_s_1588_){
_start:
{
lean_object* v_toRing_1589_; lean_object* v_invFn_x3f_1590_; lean_object* v_semiringId_x3f_1591_; lean_object* v_commSemiringInst_1592_; lean_object* v_commRingInst_1593_; lean_object* v_noZeroDivInst_x3f_1594_; lean_object* v_fieldInst_x3f_1595_; lean_object* v_powIdentityInst_x3f_1596_; lean_object* v_denoteEntries_1597_; lean_object* v_nextId_1598_; lean_object* v_steps_1599_; lean_object* v_queue_1600_; lean_object* v_basis_1601_; lean_object* v_diseqs_1602_; uint8_t v_recheck_1603_; lean_object* v_invSet_1604_; lean_object* v_powIdentityVarCount_1605_; lean_object* v_numEq0_x3f_1606_; uint8_t v_numEq0Updated_1607_; lean_object* v___x_1609_; uint8_t v_isShared_1610_; uint8_t v_isSharedCheck_1616_; 
v_toRing_1589_ = lean_ctor_get(v_s_1588_, 0);
v_invFn_x3f_1590_ = lean_ctor_get(v_s_1588_, 1);
v_semiringId_x3f_1591_ = lean_ctor_get(v_s_1588_, 2);
v_commSemiringInst_1592_ = lean_ctor_get(v_s_1588_, 3);
v_commRingInst_1593_ = lean_ctor_get(v_s_1588_, 4);
v_noZeroDivInst_x3f_1594_ = lean_ctor_get(v_s_1588_, 5);
v_fieldInst_x3f_1595_ = lean_ctor_get(v_s_1588_, 6);
v_powIdentityInst_x3f_1596_ = lean_ctor_get(v_s_1588_, 7);
v_denoteEntries_1597_ = lean_ctor_get(v_s_1588_, 8);
v_nextId_1598_ = lean_ctor_get(v_s_1588_, 9);
v_steps_1599_ = lean_ctor_get(v_s_1588_, 10);
v_queue_1600_ = lean_ctor_get(v_s_1588_, 11);
v_basis_1601_ = lean_ctor_get(v_s_1588_, 12);
v_diseqs_1602_ = lean_ctor_get(v_s_1588_, 13);
v_recheck_1603_ = lean_ctor_get_uint8(v_s_1588_, sizeof(void*)*17);
v_invSet_1604_ = lean_ctor_get(v_s_1588_, 14);
v_powIdentityVarCount_1605_ = lean_ctor_get(v_s_1588_, 15);
v_numEq0_x3f_1606_ = lean_ctor_get(v_s_1588_, 16);
v_numEq0Updated_1607_ = lean_ctor_get_uint8(v_s_1588_, sizeof(void*)*17 + 1);
v_isSharedCheck_1616_ = !lean_is_exclusive(v_s_1588_);
if (v_isSharedCheck_1616_ == 0)
{
v___x_1609_ = v_s_1588_;
v_isShared_1610_ = v_isSharedCheck_1616_;
goto v_resetjp_1608_;
}
else
{
lean_inc(v_numEq0_x3f_1606_);
lean_inc(v_powIdentityVarCount_1605_);
lean_inc(v_invSet_1604_);
lean_inc(v_diseqs_1602_);
lean_inc(v_basis_1601_);
lean_inc(v_queue_1600_);
lean_inc(v_steps_1599_);
lean_inc(v_nextId_1598_);
lean_inc(v_denoteEntries_1597_);
lean_inc(v_powIdentityInst_x3f_1596_);
lean_inc(v_fieldInst_x3f_1595_);
lean_inc(v_noZeroDivInst_x3f_1594_);
lean_inc(v_commRingInst_1593_);
lean_inc(v_commSemiringInst_1592_);
lean_inc(v_semiringId_x3f_1591_);
lean_inc(v_invFn_x3f_1590_);
lean_inc(v_toRing_1589_);
lean_dec(v_s_1588_);
v___x_1609_ = lean_box(0);
v_isShared_1610_ = v_isSharedCheck_1616_;
goto v_resetjp_1608_;
}
v_resetjp_1608_:
{
lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1614_; 
v___x_1611_ = lean_box(0);
v___x_1612_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0___redArg(v_invSet_1604_, v_a_1587_, v___x_1611_);
if (v_isShared_1610_ == 0)
{
lean_ctor_set(v___x_1609_, 14, v___x_1612_);
v___x_1614_ = v___x_1609_;
goto v_reusejp_1613_;
}
else
{
lean_object* v_reuseFailAlloc_1615_; 
v_reuseFailAlloc_1615_ = lean_alloc_ctor(0, 17, 2);
lean_ctor_set(v_reuseFailAlloc_1615_, 0, v_toRing_1589_);
lean_ctor_set(v_reuseFailAlloc_1615_, 1, v_invFn_x3f_1590_);
lean_ctor_set(v_reuseFailAlloc_1615_, 2, v_semiringId_x3f_1591_);
lean_ctor_set(v_reuseFailAlloc_1615_, 3, v_commSemiringInst_1592_);
lean_ctor_set(v_reuseFailAlloc_1615_, 4, v_commRingInst_1593_);
lean_ctor_set(v_reuseFailAlloc_1615_, 5, v_noZeroDivInst_x3f_1594_);
lean_ctor_set(v_reuseFailAlloc_1615_, 6, v_fieldInst_x3f_1595_);
lean_ctor_set(v_reuseFailAlloc_1615_, 7, v_powIdentityInst_x3f_1596_);
lean_ctor_set(v_reuseFailAlloc_1615_, 8, v_denoteEntries_1597_);
lean_ctor_set(v_reuseFailAlloc_1615_, 9, v_nextId_1598_);
lean_ctor_set(v_reuseFailAlloc_1615_, 10, v_steps_1599_);
lean_ctor_set(v_reuseFailAlloc_1615_, 11, v_queue_1600_);
lean_ctor_set(v_reuseFailAlloc_1615_, 12, v_basis_1601_);
lean_ctor_set(v_reuseFailAlloc_1615_, 13, v_diseqs_1602_);
lean_ctor_set(v_reuseFailAlloc_1615_, 14, v___x_1612_);
lean_ctor_set(v_reuseFailAlloc_1615_, 15, v_powIdentityVarCount_1605_);
lean_ctor_set(v_reuseFailAlloc_1615_, 16, v_numEq0_x3f_1606_);
lean_ctor_set_uint8(v_reuseFailAlloc_1615_, sizeof(void*)*17, v_recheck_1603_);
lean_ctor_set_uint8(v_reuseFailAlloc_1615_, sizeof(void*)*17 + 1, v_numEq0Updated_1607_);
v___x_1614_ = v_reuseFailAlloc_1615_;
goto v_reusejp_1613_;
}
v_reusejp_1613_:
{
return v___x_1614_;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__4___closed__1(void){
_start:
{
lean_object* v___x_1619_; lean_object* v___x_1620_; 
v___x_1619_ = lean_unsigned_to_nat(0u);
v___x_1620_ = lean_nat_to_int(v___x_1619_);
return v___x_1620_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__4(lean_object* v_k_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_){
_start:
{
lean_object* v___x_1639_; 
v___x_1639_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v___y_1627_, v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_, v___y_1637_);
if (lean_obj_tag(v___x_1639_) == 0)
{
lean_object* v_a_1640_; lean_object* v_toRing_1641_; lean_object* v_type_1642_; lean_object* v_u_1643_; lean_object* v_semiringInst_1644_; lean_object* v___x_1645_; lean_object* v_n_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; 
v_a_1640_ = lean_ctor_get(v___x_1639_, 0);
lean_inc(v_a_1640_);
lean_dec_ref_known(v___x_1639_, 1);
v_toRing_1641_ = lean_ctor_get(v_a_1640_, 0);
lean_inc_ref(v_toRing_1641_);
lean_dec(v_a_1640_);
v_type_1642_ = lean_ctor_get(v_toRing_1641_, 1);
lean_inc_ref_n(v_type_1642_, 2);
v_u_1643_ = lean_ctor_get(v_toRing_1641_, 2);
lean_inc(v_u_1643_);
v_semiringInst_1644_ = lean_ctor_get(v_toRing_1641_, 4);
lean_inc_ref(v_semiringInst_1644_);
lean_dec_ref(v_toRing_1641_);
v___x_1645_ = lean_nat_abs(v_k_1626_);
v_n_1646_ = l_Lean_mkRawNatLit(v___x_1645_);
v___x_1647_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__4___closed__0));
v___x_1648_ = lean_box(0);
v___x_1649_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1649_, 0, v_u_1643_);
lean_ctor_set(v___x_1649_, 1, v___x_1648_);
lean_inc_ref(v___x_1649_);
v___x_1650_ = l_Lean_mkConst(v___x_1647_, v___x_1649_);
lean_inc_ref(v_n_1646_);
v___x_1651_ = l_Lean_mkAppB(v___x_1650_, v_type_1642_, v_n_1646_);
v___x_1652_ = lean_box(0);
v___x_1653_ = l_Lean_Meta_synthInstance_x3f(v___x_1651_, v___x_1652_, v___y_1634_, v___y_1635_, v___y_1636_, v___y_1637_);
if (lean_obj_tag(v___x_1653_) == 0)
{
lean_object* v_a_1654_; lean_object* v___x_1656_; uint8_t v_isShared_1657_; uint8_t v_isSharedCheck_1693_; 
v_a_1654_ = lean_ctor_get(v___x_1653_, 0);
v_isSharedCheck_1693_ = !lean_is_exclusive(v___x_1653_);
if (v_isSharedCheck_1693_ == 0)
{
v___x_1656_ = v___x_1653_;
v_isShared_1657_ = v_isSharedCheck_1693_;
goto v_resetjp_1655_;
}
else
{
lean_inc(v_a_1654_);
lean_dec(v___x_1653_);
v___x_1656_ = lean_box(0);
v_isShared_1657_ = v_isSharedCheck_1693_;
goto v_resetjp_1655_;
}
v_resetjp_1655_:
{
lean_object* v_ofNatInst_1659_; lean_object* v___y_1660_; lean_object* v___y_1661_; lean_object* v___y_1662_; lean_object* v___y_1663_; lean_object* v___y_1664_; lean_object* v___y_1665_; lean_object* v___y_1666_; lean_object* v___y_1667_; lean_object* v___y_1668_; lean_object* v___y_1669_; lean_object* v___y_1670_; 
if (lean_obj_tag(v_a_1654_) == 1)
{
lean_object* v_val_1689_; 
lean_dec_ref(v_semiringInst_1644_);
v_val_1689_ = lean_ctor_get(v_a_1654_, 0);
lean_inc(v_val_1689_);
lean_dec_ref_known(v_a_1654_, 1);
v_ofNatInst_1659_ = v_val_1689_;
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
v___y_1670_ = v___y_1637_;
goto v___jp_1658_;
}
else
{
lean_object* v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; 
lean_dec(v_a_1654_);
v___x_1690_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__4___closed__2));
lean_inc_ref(v___x_1649_);
v___x_1691_ = l_Lean_mkConst(v___x_1690_, v___x_1649_);
lean_inc_ref(v_n_1646_);
lean_inc_ref(v_type_1642_);
v___x_1692_ = l_Lean_mkApp3(v___x_1691_, v_type_1642_, v_semiringInst_1644_, v_n_1646_);
v_ofNatInst_1659_ = v___x_1692_;
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
v___y_1670_ = v___y_1637_;
goto v___jp_1658_;
}
v___jp_1658_:
{
lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v_n_1673_; lean_object* v___x_1674_; uint8_t v___x_1675_; 
v___x_1671_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__8));
v___x_1672_ = l_Lean_mkConst(v___x_1671_, v___x_1649_);
v_n_1673_ = l_Lean_mkApp3(v___x_1672_, v_type_1642_, v_n_1646_, v_ofNatInst_1659_);
v___x_1674_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__4___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__4___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__4___closed__1);
v___x_1675_ = lean_int_dec_lt(v_k_1626_, v___x_1674_);
if (v___x_1675_ == 0)
{
lean_object* v___x_1677_; 
if (v_isShared_1657_ == 0)
{
lean_ctor_set(v___x_1656_, 0, v_n_1673_);
v___x_1677_ = v___x_1656_;
goto v_reusejp_1676_;
}
else
{
lean_object* v_reuseFailAlloc_1678_; 
v_reuseFailAlloc_1678_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1678_, 0, v_n_1673_);
v___x_1677_ = v_reuseFailAlloc_1678_;
goto v_reusejp_1676_;
}
v_reusejp_1676_:
{
return v___x_1677_;
}
}
else
{
lean_object* v___x_1679_; 
lean_del_object(v___x_1656_);
v___x_1679_ = l_Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0(v___y_1660_, v___y_1661_, v___y_1662_, v___y_1663_, v___y_1664_, v___y_1665_, v___y_1666_, v___y_1667_, v___y_1668_, v___y_1669_, v___y_1670_);
if (lean_obj_tag(v___x_1679_) == 0)
{
lean_object* v_a_1680_; lean_object* v___x_1682_; uint8_t v_isShared_1683_; uint8_t v_isSharedCheck_1688_; 
v_a_1680_ = lean_ctor_get(v___x_1679_, 0);
v_isSharedCheck_1688_ = !lean_is_exclusive(v___x_1679_);
if (v_isSharedCheck_1688_ == 0)
{
v___x_1682_ = v___x_1679_;
v_isShared_1683_ = v_isSharedCheck_1688_;
goto v_resetjp_1681_;
}
else
{
lean_inc(v_a_1680_);
lean_dec(v___x_1679_);
v___x_1682_ = lean_box(0);
v_isShared_1683_ = v_isSharedCheck_1688_;
goto v_resetjp_1681_;
}
v_resetjp_1681_:
{
lean_object* v___x_1684_; lean_object* v___x_1686_; 
v___x_1684_ = l_Lean_Expr_app___override(v_a_1680_, v_n_1673_);
if (v_isShared_1683_ == 0)
{
lean_ctor_set(v___x_1682_, 0, v___x_1684_);
v___x_1686_ = v___x_1682_;
goto v_reusejp_1685_;
}
else
{
lean_object* v_reuseFailAlloc_1687_; 
v_reuseFailAlloc_1687_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1687_, 0, v___x_1684_);
v___x_1686_ = v_reuseFailAlloc_1687_;
goto v_reusejp_1685_;
}
v_reusejp_1685_:
{
return v___x_1686_;
}
}
}
else
{
lean_dec_ref(v_n_1673_);
return v___x_1679_;
}
}
}
}
}
else
{
lean_object* v_a_1694_; lean_object* v___x_1696_; uint8_t v_isShared_1697_; uint8_t v_isSharedCheck_1701_; 
lean_dec_ref_known(v___x_1649_, 2);
lean_dec_ref(v_n_1646_);
lean_dec_ref(v_semiringInst_1644_);
lean_dec_ref(v_type_1642_);
v_a_1694_ = lean_ctor_get(v___x_1653_, 0);
v_isSharedCheck_1701_ = !lean_is_exclusive(v___x_1653_);
if (v_isSharedCheck_1701_ == 0)
{
v___x_1696_ = v___x_1653_;
v_isShared_1697_ = v_isSharedCheck_1701_;
goto v_resetjp_1695_;
}
else
{
lean_inc(v_a_1694_);
lean_dec(v___x_1653_);
v___x_1696_ = lean_box(0);
v_isShared_1697_ = v_isSharedCheck_1701_;
goto v_resetjp_1695_;
}
v_resetjp_1695_:
{
lean_object* v___x_1699_; 
if (v_isShared_1697_ == 0)
{
v___x_1699_ = v___x_1696_;
goto v_reusejp_1698_;
}
else
{
lean_object* v_reuseFailAlloc_1700_; 
v_reuseFailAlloc_1700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1700_, 0, v_a_1694_);
v___x_1699_ = v_reuseFailAlloc_1700_;
goto v_reusejp_1698_;
}
v_reusejp_1698_:
{
return v___x_1699_;
}
}
}
}
else
{
lean_object* v_a_1702_; lean_object* v___x_1704_; uint8_t v_isShared_1705_; uint8_t v_isSharedCheck_1709_; 
v_a_1702_ = lean_ctor_get(v___x_1639_, 0);
v_isSharedCheck_1709_ = !lean_is_exclusive(v___x_1639_);
if (v_isSharedCheck_1709_ == 0)
{
v___x_1704_ = v___x_1639_;
v_isShared_1705_ = v_isSharedCheck_1709_;
goto v_resetjp_1703_;
}
else
{
lean_inc(v_a_1702_);
lean_dec(v___x_1639_);
v___x_1704_ = lean_box(0);
v_isShared_1705_ = v_isSharedCheck_1709_;
goto v_resetjp_1703_;
}
v_resetjp_1703_:
{
lean_object* v___x_1707_; 
if (v_isShared_1705_ == 0)
{
v___x_1707_ = v___x_1704_;
goto v_reusejp_1706_;
}
else
{
lean_object* v_reuseFailAlloc_1708_; 
v_reuseFailAlloc_1708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1708_, 0, v_a_1702_);
v___x_1707_ = v_reuseFailAlloc_1708_;
goto v_reusejp_1706_;
}
v_reusejp_1706_:
{
return v___x_1707_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__4___boxed(lean_object* v_k_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_){
_start:
{
lean_object* v_res_1723_; 
v_res_1723_ = l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__4(v_k_1710_, v___y_1711_, v___y_1712_, v___y_1713_, v___y_1714_, v___y_1715_, v___y_1716_, v___y_1717_, v___y_1718_, v___y_1719_, v___y_1720_, v___y_1721_);
lean_dec(v___y_1721_);
lean_dec_ref(v___y_1720_);
lean_dec(v___y_1719_);
lean_dec_ref(v___y_1718_);
lean_dec(v___y_1717_);
lean_dec_ref(v___y_1716_);
lean_dec(v___y_1715_);
lean_dec_ref(v___y_1714_);
lean_dec(v___y_1713_);
lean_dec(v___y_1712_);
lean_dec_ref(v___y_1711_);
lean_dec(v_k_1710_);
return v_res_1723_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1_spec__2_spec__6___redArg(lean_object* v_keys_1724_, lean_object* v_i_1725_, lean_object* v_k_1726_){
_start:
{
lean_object* v___x_1727_; uint8_t v___x_1728_; 
v___x_1727_ = lean_array_get_size(v_keys_1724_);
v___x_1728_ = lean_nat_dec_lt(v_i_1725_, v___x_1727_);
if (v___x_1728_ == 0)
{
lean_dec(v_i_1725_);
return v___x_1728_;
}
else
{
lean_object* v_k_x27_1729_; uint8_t v___x_1730_; 
v_k_x27_1729_ = lean_array_fget_borrowed(v_keys_1724_, v_i_1725_);
v___x_1730_ = lean_expr_eqv(v_k_1726_, v_k_x27_1729_);
if (v___x_1730_ == 0)
{
lean_object* v___x_1731_; lean_object* v___x_1732_; 
v___x_1731_ = lean_unsigned_to_nat(1u);
v___x_1732_ = lean_nat_add(v_i_1725_, v___x_1731_);
lean_dec(v_i_1725_);
v_i_1725_ = v___x_1732_;
goto _start;
}
else
{
lean_dec(v_i_1725_);
return v___x_1728_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1_spec__2_spec__6___redArg___boxed(lean_object* v_keys_1734_, lean_object* v_i_1735_, lean_object* v_k_1736_){
_start:
{
uint8_t v_res_1737_; lean_object* v_r_1738_; 
v_res_1737_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1_spec__2_spec__6___redArg(v_keys_1734_, v_i_1735_, v_k_1736_);
lean_dec_ref(v_k_1736_);
lean_dec_ref(v_keys_1734_);
v_r_1738_ = lean_box(v_res_1737_);
return v_r_1738_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1_spec__2___redArg(lean_object* v_x_1739_, size_t v_x_1740_, lean_object* v_x_1741_){
_start:
{
if (lean_obj_tag(v_x_1739_) == 0)
{
lean_object* v_es_1742_; lean_object* v___x_1743_; size_t v___x_1744_; size_t v___x_1745_; lean_object* v_j_1746_; lean_object* v___x_1747_; 
v_es_1742_ = lean_ctor_get(v_x_1739_, 0);
v___x_1743_ = lean_box(2);
v___x_1744_ = ((size_t)31ULL);
v___x_1745_ = lean_usize_land(v_x_1740_, v___x_1744_);
v_j_1746_ = lean_usize_to_nat(v___x_1745_);
v___x_1747_ = lean_array_get_borrowed(v___x_1743_, v_es_1742_, v_j_1746_);
lean_dec(v_j_1746_);
switch(lean_obj_tag(v___x_1747_))
{
case 0:
{
lean_object* v_key_1748_; uint8_t v___x_1749_; 
v_key_1748_ = lean_ctor_get(v___x_1747_, 0);
v___x_1749_ = lean_expr_eqv(v_x_1741_, v_key_1748_);
return v___x_1749_;
}
case 1:
{
lean_object* v_node_1750_; size_t v___x_1751_; size_t v___x_1752_; 
v_node_1750_ = lean_ctor_get(v___x_1747_, 0);
v___x_1751_ = ((size_t)5ULL);
v___x_1752_ = lean_usize_shift_right(v_x_1740_, v___x_1751_);
v_x_1739_ = v_node_1750_;
v_x_1740_ = v___x_1752_;
goto _start;
}
default: 
{
uint8_t v___x_1754_; 
v___x_1754_ = 0;
return v___x_1754_;
}
}
}
else
{
lean_object* v_ks_1755_; lean_object* v___x_1756_; uint8_t v___x_1757_; 
v_ks_1755_ = lean_ctor_get(v_x_1739_, 0);
v___x_1756_ = lean_unsigned_to_nat(0u);
v___x_1757_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1_spec__2_spec__6___redArg(v_ks_1755_, v___x_1756_, v_x_1741_);
return v___x_1757_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1_spec__2___redArg___boxed(lean_object* v_x_1758_, lean_object* v_x_1759_, lean_object* v_x_1760_){
_start:
{
size_t v_x_81453__boxed_1761_; uint8_t v_res_1762_; lean_object* v_r_1763_; 
v_x_81453__boxed_1761_ = lean_unbox_usize(v_x_1759_);
lean_dec(v_x_1759_);
v_res_1762_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1_spec__2___redArg(v_x_1758_, v_x_81453__boxed_1761_, v_x_1760_);
lean_dec_ref(v_x_1760_);
lean_dec_ref(v_x_1758_);
v_r_1763_ = lean_box(v_res_1762_);
return v_r_1763_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1___redArg(lean_object* v_x_1764_, lean_object* v_x_1765_){
_start:
{
uint64_t v___x_1766_; size_t v___x_1767_; uint8_t v___x_1768_; 
v___x_1766_ = l_Lean_Expr_hash(v_x_1765_);
v___x_1767_ = lean_uint64_to_usize(v___x_1766_);
v___x_1768_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1_spec__2___redArg(v_x_1764_, v___x_1767_, v_x_1765_);
return v___x_1768_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1___redArg___boxed(lean_object* v_x_1769_, lean_object* v_x_1770_){
_start:
{
uint8_t v_res_1771_; lean_object* v_r_1772_; 
v_res_1771_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1___redArg(v_x_1769_, v_x_1770_);
lean_dec_ref(v_x_1770_);
lean_dec_ref(v_x_1769_);
v_r_1772_ = lean_box(v_res_1771_);
return v_r_1772_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__3___lam__0(lean_object* v_a_1773_, lean_object* v_s_1774_){
_start:
{
lean_object* v_toRing_1775_; lean_object* v_invFn_x3f_1776_; lean_object* v_semiringId_x3f_1777_; lean_object* v_commSemiringInst_1778_; lean_object* v_commRingInst_1779_; lean_object* v_noZeroDivInst_x3f_1780_; lean_object* v_fieldInst_x3f_1781_; lean_object* v_powIdentityInst_x3f_1782_; lean_object* v_denoteEntries_1783_; lean_object* v_nextId_1784_; lean_object* v_steps_1785_; lean_object* v_queue_1786_; lean_object* v_basis_1787_; lean_object* v_diseqs_1788_; uint8_t v_recheck_1789_; lean_object* v_invSet_1790_; lean_object* v_powIdentityVarCount_1791_; lean_object* v_numEq0_x3f_1792_; uint8_t v_numEq0Updated_1793_; lean_object* v___x_1795_; uint8_t v_isShared_1796_; uint8_t v_isSharedCheck_1825_; 
v_toRing_1775_ = lean_ctor_get(v_s_1774_, 0);
v_invFn_x3f_1776_ = lean_ctor_get(v_s_1774_, 1);
v_semiringId_x3f_1777_ = lean_ctor_get(v_s_1774_, 2);
v_commSemiringInst_1778_ = lean_ctor_get(v_s_1774_, 3);
v_commRingInst_1779_ = lean_ctor_get(v_s_1774_, 4);
v_noZeroDivInst_x3f_1780_ = lean_ctor_get(v_s_1774_, 5);
v_fieldInst_x3f_1781_ = lean_ctor_get(v_s_1774_, 6);
v_powIdentityInst_x3f_1782_ = lean_ctor_get(v_s_1774_, 7);
v_denoteEntries_1783_ = lean_ctor_get(v_s_1774_, 8);
v_nextId_1784_ = lean_ctor_get(v_s_1774_, 9);
v_steps_1785_ = lean_ctor_get(v_s_1774_, 10);
v_queue_1786_ = lean_ctor_get(v_s_1774_, 11);
v_basis_1787_ = lean_ctor_get(v_s_1774_, 12);
v_diseqs_1788_ = lean_ctor_get(v_s_1774_, 13);
v_recheck_1789_ = lean_ctor_get_uint8(v_s_1774_, sizeof(void*)*17);
v_invSet_1790_ = lean_ctor_get(v_s_1774_, 14);
v_powIdentityVarCount_1791_ = lean_ctor_get(v_s_1774_, 15);
v_numEq0_x3f_1792_ = lean_ctor_get(v_s_1774_, 16);
v_numEq0Updated_1793_ = lean_ctor_get_uint8(v_s_1774_, sizeof(void*)*17 + 1);
v_isSharedCheck_1825_ = !lean_is_exclusive(v_s_1774_);
if (v_isSharedCheck_1825_ == 0)
{
v___x_1795_ = v_s_1774_;
v_isShared_1796_ = v_isSharedCheck_1825_;
goto v_resetjp_1794_;
}
else
{
lean_inc(v_numEq0_x3f_1792_);
lean_inc(v_powIdentityVarCount_1791_);
lean_inc(v_invSet_1790_);
lean_inc(v_diseqs_1788_);
lean_inc(v_basis_1787_);
lean_inc(v_queue_1786_);
lean_inc(v_steps_1785_);
lean_inc(v_nextId_1784_);
lean_inc(v_denoteEntries_1783_);
lean_inc(v_powIdentityInst_x3f_1782_);
lean_inc(v_fieldInst_x3f_1781_);
lean_inc(v_noZeroDivInst_x3f_1780_);
lean_inc(v_commRingInst_1779_);
lean_inc(v_commSemiringInst_1778_);
lean_inc(v_semiringId_x3f_1777_);
lean_inc(v_invFn_x3f_1776_);
lean_inc(v_toRing_1775_);
lean_dec(v_s_1774_);
v___x_1795_ = lean_box(0);
v_isShared_1796_ = v_isSharedCheck_1825_;
goto v_resetjp_1794_;
}
v_resetjp_1794_:
{
lean_object* v_id_1797_; lean_object* v_type_1798_; lean_object* v_u_1799_; lean_object* v_ringInst_1800_; lean_object* v_semiringInst_1801_; lean_object* v_charInst_x3f_1802_; lean_object* v_addFn_x3f_1803_; lean_object* v_subFn_x3f_1804_; lean_object* v_negFn_x3f_1805_; lean_object* v_powFn_x3f_1806_; lean_object* v_intCastFn_x3f_1807_; lean_object* v_natCastFn_x3f_1808_; lean_object* v_one_x3f_1809_; lean_object* v_vars_1810_; lean_object* v_varMap_1811_; lean_object* v_denote_1812_; lean_object* v___x_1814_; uint8_t v_isShared_1815_; uint8_t v_isSharedCheck_1823_; 
v_id_1797_ = lean_ctor_get(v_toRing_1775_, 0);
v_type_1798_ = lean_ctor_get(v_toRing_1775_, 1);
v_u_1799_ = lean_ctor_get(v_toRing_1775_, 2);
v_ringInst_1800_ = lean_ctor_get(v_toRing_1775_, 3);
v_semiringInst_1801_ = lean_ctor_get(v_toRing_1775_, 4);
v_charInst_x3f_1802_ = lean_ctor_get(v_toRing_1775_, 5);
v_addFn_x3f_1803_ = lean_ctor_get(v_toRing_1775_, 6);
v_subFn_x3f_1804_ = lean_ctor_get(v_toRing_1775_, 8);
v_negFn_x3f_1805_ = lean_ctor_get(v_toRing_1775_, 9);
v_powFn_x3f_1806_ = lean_ctor_get(v_toRing_1775_, 10);
v_intCastFn_x3f_1807_ = lean_ctor_get(v_toRing_1775_, 11);
v_natCastFn_x3f_1808_ = lean_ctor_get(v_toRing_1775_, 12);
v_one_x3f_1809_ = lean_ctor_get(v_toRing_1775_, 13);
v_vars_1810_ = lean_ctor_get(v_toRing_1775_, 14);
v_varMap_1811_ = lean_ctor_get(v_toRing_1775_, 15);
v_denote_1812_ = lean_ctor_get(v_toRing_1775_, 16);
v_isSharedCheck_1823_ = !lean_is_exclusive(v_toRing_1775_);
if (v_isSharedCheck_1823_ == 0)
{
lean_object* v_unused_1824_; 
v_unused_1824_ = lean_ctor_get(v_toRing_1775_, 7);
lean_dec(v_unused_1824_);
v___x_1814_ = v_toRing_1775_;
v_isShared_1815_ = v_isSharedCheck_1823_;
goto v_resetjp_1813_;
}
else
{
lean_inc(v_denote_1812_);
lean_inc(v_varMap_1811_);
lean_inc(v_vars_1810_);
lean_inc(v_one_x3f_1809_);
lean_inc(v_natCastFn_x3f_1808_);
lean_inc(v_intCastFn_x3f_1807_);
lean_inc(v_powFn_x3f_1806_);
lean_inc(v_negFn_x3f_1805_);
lean_inc(v_subFn_x3f_1804_);
lean_inc(v_addFn_x3f_1803_);
lean_inc(v_charInst_x3f_1802_);
lean_inc(v_semiringInst_1801_);
lean_inc(v_ringInst_1800_);
lean_inc(v_u_1799_);
lean_inc(v_type_1798_);
lean_inc(v_id_1797_);
lean_dec(v_toRing_1775_);
v___x_1814_ = lean_box(0);
v_isShared_1815_ = v_isSharedCheck_1823_;
goto v_resetjp_1813_;
}
v_resetjp_1813_:
{
lean_object* v___x_1816_; lean_object* v___x_1818_; 
v___x_1816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1816_, 0, v_a_1773_);
if (v_isShared_1815_ == 0)
{
lean_ctor_set(v___x_1814_, 7, v___x_1816_);
v___x_1818_ = v___x_1814_;
goto v_reusejp_1817_;
}
else
{
lean_object* v_reuseFailAlloc_1822_; 
v_reuseFailAlloc_1822_ = lean_alloc_ctor(0, 17, 0);
lean_ctor_set(v_reuseFailAlloc_1822_, 0, v_id_1797_);
lean_ctor_set(v_reuseFailAlloc_1822_, 1, v_type_1798_);
lean_ctor_set(v_reuseFailAlloc_1822_, 2, v_u_1799_);
lean_ctor_set(v_reuseFailAlloc_1822_, 3, v_ringInst_1800_);
lean_ctor_set(v_reuseFailAlloc_1822_, 4, v_semiringInst_1801_);
lean_ctor_set(v_reuseFailAlloc_1822_, 5, v_charInst_x3f_1802_);
lean_ctor_set(v_reuseFailAlloc_1822_, 6, v_addFn_x3f_1803_);
lean_ctor_set(v_reuseFailAlloc_1822_, 7, v___x_1816_);
lean_ctor_set(v_reuseFailAlloc_1822_, 8, v_subFn_x3f_1804_);
lean_ctor_set(v_reuseFailAlloc_1822_, 9, v_negFn_x3f_1805_);
lean_ctor_set(v_reuseFailAlloc_1822_, 10, v_powFn_x3f_1806_);
lean_ctor_set(v_reuseFailAlloc_1822_, 11, v_intCastFn_x3f_1807_);
lean_ctor_set(v_reuseFailAlloc_1822_, 12, v_natCastFn_x3f_1808_);
lean_ctor_set(v_reuseFailAlloc_1822_, 13, v_one_x3f_1809_);
lean_ctor_set(v_reuseFailAlloc_1822_, 14, v_vars_1810_);
lean_ctor_set(v_reuseFailAlloc_1822_, 15, v_varMap_1811_);
lean_ctor_set(v_reuseFailAlloc_1822_, 16, v_denote_1812_);
v___x_1818_ = v_reuseFailAlloc_1822_;
goto v_reusejp_1817_;
}
v_reusejp_1817_:
{
lean_object* v___x_1820_; 
if (v_isShared_1796_ == 0)
{
lean_ctor_set(v___x_1795_, 0, v___x_1818_);
v___x_1820_ = v___x_1795_;
goto v_reusejp_1819_;
}
else
{
lean_object* v_reuseFailAlloc_1821_; 
v_reuseFailAlloc_1821_ = lean_alloc_ctor(0, 17, 2);
lean_ctor_set(v_reuseFailAlloc_1821_, 0, v___x_1818_);
lean_ctor_set(v_reuseFailAlloc_1821_, 1, v_invFn_x3f_1776_);
lean_ctor_set(v_reuseFailAlloc_1821_, 2, v_semiringId_x3f_1777_);
lean_ctor_set(v_reuseFailAlloc_1821_, 3, v_commSemiringInst_1778_);
lean_ctor_set(v_reuseFailAlloc_1821_, 4, v_commRingInst_1779_);
lean_ctor_set(v_reuseFailAlloc_1821_, 5, v_noZeroDivInst_x3f_1780_);
lean_ctor_set(v_reuseFailAlloc_1821_, 6, v_fieldInst_x3f_1781_);
lean_ctor_set(v_reuseFailAlloc_1821_, 7, v_powIdentityInst_x3f_1782_);
lean_ctor_set(v_reuseFailAlloc_1821_, 8, v_denoteEntries_1783_);
lean_ctor_set(v_reuseFailAlloc_1821_, 9, v_nextId_1784_);
lean_ctor_set(v_reuseFailAlloc_1821_, 10, v_steps_1785_);
lean_ctor_set(v_reuseFailAlloc_1821_, 11, v_queue_1786_);
lean_ctor_set(v_reuseFailAlloc_1821_, 12, v_basis_1787_);
lean_ctor_set(v_reuseFailAlloc_1821_, 13, v_diseqs_1788_);
lean_ctor_set(v_reuseFailAlloc_1821_, 14, v_invSet_1790_);
lean_ctor_set(v_reuseFailAlloc_1821_, 15, v_powIdentityVarCount_1791_);
lean_ctor_set(v_reuseFailAlloc_1821_, 16, v_numEq0_x3f_1792_);
lean_ctor_set_uint8(v_reuseFailAlloc_1821_, sizeof(void*)*17, v_recheck_1789_);
lean_ctor_set_uint8(v_reuseFailAlloc_1821_, sizeof(void*)*17 + 1, v_numEq0Updated_1793_);
v___x_1820_ = v_reuseFailAlloc_1821_;
goto v_reusejp_1819_;
}
v_reusejp_1819_:
{
return v___x_1820_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__3_spec__5(lean_object* v_type_1826_, lean_object* v_u_1827_, lean_object* v_instDeclName_1828_, lean_object* v_declName_1829_, lean_object* v_expectedInst_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_){
_start:
{
lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; 
v___x_1843_ = lean_box(0);
lean_inc_n(v_u_1827_, 2);
v___x_1844_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1844_, 0, v_u_1827_);
lean_ctor_set(v___x_1844_, 1, v___x_1843_);
v___x_1845_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1845_, 0, v_u_1827_);
lean_ctor_set(v___x_1845_, 1, v___x_1844_);
v___x_1846_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1846_, 0, v_u_1827_);
lean_ctor_set(v___x_1846_, 1, v___x_1845_);
lean_inc_ref(v___x_1846_);
v___x_1847_ = l_Lean_mkConst(v_instDeclName_1828_, v___x_1846_);
lean_inc_ref_n(v_type_1826_, 3);
v___x_1848_ = l_Lean_mkApp3(v___x_1847_, v_type_1826_, v_type_1826_, v_type_1826_);
v___x_1849_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1_spec__5(v___x_1848_, v___y_1831_, v___y_1832_, v___y_1833_, v___y_1834_, v___y_1835_, v___y_1836_, v___y_1837_, v___y_1838_, v___y_1839_, v___y_1840_, v___y_1841_);
if (lean_obj_tag(v___x_1849_) == 0)
{
lean_object* v_a_1850_; lean_object* v___x_1851_; 
v_a_1850_ = lean_ctor_get(v___x_1849_, 0);
lean_inc_n(v_a_1850_, 2);
lean_dec_ref_known(v___x_1849_, 1);
lean_inc(v_declName_1829_);
v___x_1851_ = l_Lean_Meta_Grind_Arith_CommRing_checkInst(v_declName_1829_, v_a_1850_, v_expectedInst_1830_, v___y_1838_, v___y_1839_, v___y_1840_, v___y_1841_);
if (lean_obj_tag(v___x_1851_) == 0)
{
lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; 
lean_dec_ref_known(v___x_1851_, 1);
v___x_1852_ = l_Lean_mkConst(v_declName_1829_, v___x_1846_);
lean_inc_ref_n(v_type_1826_, 2);
v___x_1853_ = l_Lean_mkApp4(v___x_1852_, v_type_1826_, v_type_1826_, v_type_1826_, v_a_1850_);
v___x_1854_ = l_Lean_Meta_Sym_canon(v___x_1853_, v___y_1836_, v___y_1837_, v___y_1838_, v___y_1839_, v___y_1840_, v___y_1841_);
if (lean_obj_tag(v___x_1854_) == 0)
{
lean_object* v_a_1855_; lean_object* v___x_1856_; 
v_a_1855_ = lean_ctor_get(v___x_1854_, 0);
lean_inc(v_a_1855_);
lean_dec_ref_known(v___x_1854_, 1);
v___x_1856_ = l_Lean_Meta_Sym_shareCommon(v_a_1855_, v___y_1836_, v___y_1837_, v___y_1838_, v___y_1839_, v___y_1840_, v___y_1841_);
return v___x_1856_;
}
else
{
return v___x_1854_;
}
}
else
{
lean_object* v_a_1857_; lean_object* v___x_1859_; uint8_t v_isShared_1860_; uint8_t v_isSharedCheck_1864_; 
lean_dec(v_a_1850_);
lean_dec_ref_known(v___x_1846_, 2);
lean_dec(v_declName_1829_);
lean_dec_ref(v_type_1826_);
v_a_1857_ = lean_ctor_get(v___x_1851_, 0);
v_isSharedCheck_1864_ = !lean_is_exclusive(v___x_1851_);
if (v_isSharedCheck_1864_ == 0)
{
v___x_1859_ = v___x_1851_;
v_isShared_1860_ = v_isSharedCheck_1864_;
goto v_resetjp_1858_;
}
else
{
lean_inc(v_a_1857_);
lean_dec(v___x_1851_);
v___x_1859_ = lean_box(0);
v_isShared_1860_ = v_isSharedCheck_1864_;
goto v_resetjp_1858_;
}
v_resetjp_1858_:
{
lean_object* v___x_1862_; 
if (v_isShared_1860_ == 0)
{
v___x_1862_ = v___x_1859_;
goto v_reusejp_1861_;
}
else
{
lean_object* v_reuseFailAlloc_1863_; 
v_reuseFailAlloc_1863_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1863_, 0, v_a_1857_);
v___x_1862_ = v_reuseFailAlloc_1863_;
goto v_reusejp_1861_;
}
v_reusejp_1861_:
{
return v___x_1862_;
}
}
}
}
else
{
lean_dec_ref_known(v___x_1846_, 2);
lean_dec_ref(v_expectedInst_1830_);
lean_dec(v_declName_1829_);
lean_dec_ref(v_type_1826_);
return v___x_1849_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__3_spec__5___boxed(lean_object** _args){
lean_object* v_type_1865_ = _args[0];
lean_object* v_u_1866_ = _args[1];
lean_object* v_instDeclName_1867_ = _args[2];
lean_object* v_declName_1868_ = _args[3];
lean_object* v_expectedInst_1869_ = _args[4];
lean_object* v___y_1870_ = _args[5];
lean_object* v___y_1871_ = _args[6];
lean_object* v___y_1872_ = _args[7];
lean_object* v___y_1873_ = _args[8];
lean_object* v___y_1874_ = _args[9];
lean_object* v___y_1875_ = _args[10];
lean_object* v___y_1876_ = _args[11];
lean_object* v___y_1877_ = _args[12];
lean_object* v___y_1878_ = _args[13];
lean_object* v___y_1879_ = _args[14];
lean_object* v___y_1880_ = _args[15];
lean_object* v___y_1881_ = _args[16];
_start:
{
lean_object* v_res_1882_; 
v_res_1882_ = l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__3_spec__5(v_type_1865_, v_u_1866_, v_instDeclName_1867_, v_declName_1868_, v_expectedInst_1869_, v___y_1870_, v___y_1871_, v___y_1872_, v___y_1873_, v___y_1874_, v___y_1875_, v___y_1876_, v___y_1877_, v___y_1878_, v___y_1879_, v___y_1880_);
lean_dec(v___y_1880_);
lean_dec_ref(v___y_1879_);
lean_dec(v___y_1878_);
lean_dec_ref(v___y_1877_);
lean_dec(v___y_1876_);
lean_dec_ref(v___y_1875_);
lean_dec(v___y_1874_);
lean_dec_ref(v___y_1873_);
lean_dec(v___y_1872_);
lean_dec(v___y_1871_);
lean_dec_ref(v___y_1870_);
return v_res_1882_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__3(lean_object* v___y_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_){
_start:
{
lean_object* v___x_1906_; 
v___x_1906_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v___y_1894_, v___y_1895_, v___y_1896_, v___y_1897_, v___y_1898_, v___y_1899_, v___y_1900_, v___y_1901_, v___y_1902_, v___y_1903_, v___y_1904_);
if (lean_obj_tag(v___x_1906_) == 0)
{
lean_object* v_a_1907_; lean_object* v___x_1909_; uint8_t v_isShared_1910_; uint8_t v_isSharedCheck_1950_; 
v_a_1907_ = lean_ctor_get(v___x_1906_, 0);
v_isSharedCheck_1950_ = !lean_is_exclusive(v___x_1906_);
if (v_isSharedCheck_1950_ == 0)
{
v___x_1909_ = v___x_1906_;
v_isShared_1910_ = v_isSharedCheck_1950_;
goto v_resetjp_1908_;
}
else
{
lean_inc(v_a_1907_);
lean_dec(v___x_1906_);
v___x_1909_ = lean_box(0);
v_isShared_1910_ = v_isSharedCheck_1950_;
goto v_resetjp_1908_;
}
v_resetjp_1908_:
{
lean_object* v_toRing_1911_; lean_object* v_mulFn_x3f_1912_; 
v_toRing_1911_ = lean_ctor_get(v_a_1907_, 0);
lean_inc_ref(v_toRing_1911_);
lean_dec(v_a_1907_);
v_mulFn_x3f_1912_ = lean_ctor_get(v_toRing_1911_, 7);
if (lean_obj_tag(v_mulFn_x3f_1912_) == 1)
{
lean_object* v_val_1913_; lean_object* v___x_1915_; 
lean_inc_ref(v_mulFn_x3f_1912_);
lean_dec_ref(v_toRing_1911_);
v_val_1913_ = lean_ctor_get(v_mulFn_x3f_1912_, 0);
lean_inc(v_val_1913_);
lean_dec_ref_known(v_mulFn_x3f_1912_, 1);
if (v_isShared_1910_ == 0)
{
lean_ctor_set(v___x_1909_, 0, v_val_1913_);
v___x_1915_ = v___x_1909_;
goto v_reusejp_1914_;
}
else
{
lean_object* v_reuseFailAlloc_1916_; 
v_reuseFailAlloc_1916_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1916_, 0, v_val_1913_);
v___x_1915_ = v_reuseFailAlloc_1916_;
goto v_reusejp_1914_;
}
v_reusejp_1914_:
{
return v___x_1915_;
}
}
else
{
lean_object* v_type_1917_; lean_object* v_u_1918_; lean_object* v_semiringInst_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v_expectedInst_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; 
lean_del_object(v___x_1909_);
v_type_1917_ = lean_ctor_get(v_toRing_1911_, 1);
lean_inc_ref_n(v_type_1917_, 3);
v_u_1918_ = lean_ctor_get(v_toRing_1911_, 2);
lean_inc_n(v_u_1918_, 2);
v_semiringInst_1919_ = lean_ctor_get(v_toRing_1911_, 4);
lean_inc_ref(v_semiringInst_1919_);
lean_dec_ref(v_toRing_1911_);
v___x_1920_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__3___closed__1));
v___x_1921_ = lean_box(0);
v___x_1922_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1922_, 0, v_u_1918_);
lean_ctor_set(v___x_1922_, 1, v___x_1921_);
lean_inc_ref(v___x_1922_);
v___x_1923_ = l_Lean_mkConst(v___x_1920_, v___x_1922_);
v___x_1924_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__3___closed__3));
v___x_1925_ = l_Lean_mkConst(v___x_1924_, v___x_1922_);
v___x_1926_ = l_Lean_mkAppB(v___x_1925_, v_type_1917_, v_semiringInst_1919_);
v_expectedInst_1927_ = l_Lean_mkAppB(v___x_1923_, v_type_1917_, v___x_1926_);
v___x_1928_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__3___closed__4));
v___x_1929_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__20));
v___x_1930_ = l_Lean_Meta_Grind_Arith_CommRing_mkBinHomoFn___at___00Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__3_spec__5(v_type_1917_, v_u_1918_, v___x_1928_, v___x_1929_, v_expectedInst_1927_, v___y_1894_, v___y_1895_, v___y_1896_, v___y_1897_, v___y_1898_, v___y_1899_, v___y_1900_, v___y_1901_, v___y_1902_, v___y_1903_, v___y_1904_);
if (lean_obj_tag(v___x_1930_) == 0)
{
lean_object* v_a_1931_; lean_object* v___f_1932_; lean_object* v___x_1933_; 
v_a_1931_ = lean_ctor_get(v___x_1930_, 0);
lean_inc_n(v_a_1931_, 2);
lean_dec_ref_known(v___x_1930_, 1);
v___f_1932_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__3___lam__0), 2, 1);
lean_closure_set(v___f_1932_, 0, v_a_1931_);
v___x_1933_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(v___f_1932_, v___y_1894_, v___y_1895_);
if (lean_obj_tag(v___x_1933_) == 0)
{
lean_object* v___x_1935_; uint8_t v_isShared_1936_; uint8_t v_isSharedCheck_1940_; 
v_isSharedCheck_1940_ = !lean_is_exclusive(v___x_1933_);
if (v_isSharedCheck_1940_ == 0)
{
lean_object* v_unused_1941_; 
v_unused_1941_ = lean_ctor_get(v___x_1933_, 0);
lean_dec(v_unused_1941_);
v___x_1935_ = v___x_1933_;
v_isShared_1936_ = v_isSharedCheck_1940_;
goto v_resetjp_1934_;
}
else
{
lean_dec(v___x_1933_);
v___x_1935_ = lean_box(0);
v_isShared_1936_ = v_isSharedCheck_1940_;
goto v_resetjp_1934_;
}
v_resetjp_1934_:
{
lean_object* v___x_1938_; 
if (v_isShared_1936_ == 0)
{
lean_ctor_set(v___x_1935_, 0, v_a_1931_);
v___x_1938_ = v___x_1935_;
goto v_reusejp_1937_;
}
else
{
lean_object* v_reuseFailAlloc_1939_; 
v_reuseFailAlloc_1939_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1939_, 0, v_a_1931_);
v___x_1938_ = v_reuseFailAlloc_1939_;
goto v_reusejp_1937_;
}
v_reusejp_1937_:
{
return v___x_1938_;
}
}
}
else
{
lean_object* v_a_1942_; lean_object* v___x_1944_; uint8_t v_isShared_1945_; uint8_t v_isSharedCheck_1949_; 
lean_dec(v_a_1931_);
v_a_1942_ = lean_ctor_get(v___x_1933_, 0);
v_isSharedCheck_1949_ = !lean_is_exclusive(v___x_1933_);
if (v_isSharedCheck_1949_ == 0)
{
v___x_1944_ = v___x_1933_;
v_isShared_1945_ = v_isSharedCheck_1949_;
goto v_resetjp_1943_;
}
else
{
lean_inc(v_a_1942_);
lean_dec(v___x_1933_);
v___x_1944_ = lean_box(0);
v_isShared_1945_ = v_isSharedCheck_1949_;
goto v_resetjp_1943_;
}
v_resetjp_1943_:
{
lean_object* v___x_1947_; 
if (v_isShared_1945_ == 0)
{
v___x_1947_ = v___x_1944_;
goto v_reusejp_1946_;
}
else
{
lean_object* v_reuseFailAlloc_1948_; 
v_reuseFailAlloc_1948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1948_, 0, v_a_1942_);
v___x_1947_ = v_reuseFailAlloc_1948_;
goto v_reusejp_1946_;
}
v_reusejp_1946_:
{
return v___x_1947_;
}
}
}
}
else
{
return v___x_1930_;
}
}
}
}
else
{
lean_object* v_a_1951_; lean_object* v___x_1953_; uint8_t v_isShared_1954_; uint8_t v_isSharedCheck_1958_; 
v_a_1951_ = lean_ctor_get(v___x_1906_, 0);
v_isSharedCheck_1958_ = !lean_is_exclusive(v___x_1906_);
if (v_isSharedCheck_1958_ == 0)
{
v___x_1953_ = v___x_1906_;
v_isShared_1954_ = v_isSharedCheck_1958_;
goto v_resetjp_1952_;
}
else
{
lean_inc(v_a_1951_);
lean_dec(v___x_1906_);
v___x_1953_ = lean_box(0);
v_isShared_1954_ = v_isSharedCheck_1958_;
goto v_resetjp_1952_;
}
v_resetjp_1952_:
{
lean_object* v___x_1956_; 
if (v_isShared_1954_ == 0)
{
v___x_1956_ = v___x_1953_;
goto v_reusejp_1955_;
}
else
{
lean_object* v_reuseFailAlloc_1957_; 
v_reuseFailAlloc_1957_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1957_, 0, v_a_1951_);
v___x_1956_ = v_reuseFailAlloc_1957_;
goto v_reusejp_1955_;
}
v_reusejp_1955_:
{
return v___x_1956_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__3___boxed(lean_object* v___y_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_){
_start:
{
lean_object* v_res_1971_; 
v_res_1971_ = l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__3(v___y_1959_, v___y_1960_, v___y_1961_, v___y_1962_, v___y_1963_, v___y_1964_, v___y_1965_, v___y_1966_, v___y_1967_, v___y_1968_, v___y_1969_);
lean_dec(v___y_1969_);
lean_dec_ref(v___y_1968_);
lean_dec(v___y_1967_);
lean_dec_ref(v___y_1966_);
lean_dec(v___y_1965_);
lean_dec_ref(v___y_1964_);
lean_dec(v___y_1963_);
lean_dec_ref(v___y_1962_);
lean_dec(v___y_1961_);
lean_dec(v___y_1960_);
lean_dec_ref(v___y_1959_);
return v_res_1971_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__3(void){
_start:
{
lean_object* v___x_1979_; lean_object* v___x_1980_; 
v___x_1979_ = lean_unsigned_to_nat(1u);
v___x_1980_ = lean_nat_to_int(v___x_1979_);
return v___x_1980_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv(lean_object* v_e_2005_, lean_object* v_inst_2006_, lean_object* v_a_2007_, lean_object* v_a_2008_, lean_object* v_a_2009_, lean_object* v_a_2010_, lean_object* v_a_2011_, lean_object* v_a_2012_, lean_object* v_a_2013_, lean_object* v_a_2014_, lean_object* v_a_2015_, lean_object* v_a_2016_, lean_object* v_a_2017_, lean_object* v_a_2018_){
_start:
{
lean_object* v___x_2023_; 
v___x_2023_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst(v_inst_2006_, v_a_2008_, v_a_2009_, v_a_2010_, v_a_2011_, v_a_2012_, v_a_2013_, v_a_2014_, v_a_2015_, v_a_2016_, v_a_2017_, v_a_2018_);
if (lean_obj_tag(v___x_2023_) == 0)
{
lean_object* v_a_2024_; lean_object* v___x_2026_; uint8_t v_isShared_2027_; uint8_t v_isSharedCheck_2283_; 
v_a_2024_ = lean_ctor_get(v___x_2023_, 0);
v_isSharedCheck_2283_ = !lean_is_exclusive(v___x_2023_);
if (v_isSharedCheck_2283_ == 0)
{
v___x_2026_ = v___x_2023_;
v_isShared_2027_ = v_isSharedCheck_2283_;
goto v_resetjp_2025_;
}
else
{
lean_inc(v_a_2024_);
lean_dec(v___x_2023_);
v___x_2026_ = lean_box(0);
v_isShared_2027_ = v_isSharedCheck_2283_;
goto v_resetjp_2025_;
}
v_resetjp_2025_:
{
uint8_t v___x_2028_; 
v___x_2028_ = lean_unbox(v_a_2024_);
lean_dec(v_a_2024_);
if (v___x_2028_ == 0)
{
lean_object* v___x_2029_; lean_object* v___x_2031_; 
lean_dec_ref(v_a_2007_);
lean_dec_ref(v_e_2005_);
v___x_2029_ = lean_box(0);
if (v_isShared_2027_ == 0)
{
lean_ctor_set(v___x_2026_, 0, v___x_2029_);
v___x_2031_ = v___x_2026_;
goto v_reusejp_2030_;
}
else
{
lean_object* v_reuseFailAlloc_2032_; 
v_reuseFailAlloc_2032_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2032_, 0, v___x_2029_);
v___x_2031_ = v_reuseFailAlloc_2032_;
goto v_reusejp_2030_;
}
v_reusejp_2030_:
{
return v___x_2031_;
}
}
else
{
lean_object* v___x_2033_; 
lean_del_object(v___x_2026_);
v___x_2033_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v_a_2008_, v_a_2009_, v_a_2010_, v_a_2011_, v_a_2012_, v_a_2013_, v_a_2014_, v_a_2015_, v_a_2016_, v_a_2017_, v_a_2018_);
if (lean_obj_tag(v___x_2033_) == 0)
{
lean_object* v_a_2034_; lean_object* v___x_2036_; uint8_t v_isShared_2037_; uint8_t v_isSharedCheck_2274_; 
v_a_2034_ = lean_ctor_get(v___x_2033_, 0);
v_isSharedCheck_2274_ = !lean_is_exclusive(v___x_2033_);
if (v_isSharedCheck_2274_ == 0)
{
v___x_2036_ = v___x_2033_;
v_isShared_2037_ = v_isSharedCheck_2274_;
goto v_resetjp_2035_;
}
else
{
lean_inc(v_a_2034_);
lean_dec(v___x_2033_);
v___x_2036_ = lean_box(0);
v_isShared_2037_ = v_isSharedCheck_2274_;
goto v_resetjp_2035_;
}
v_resetjp_2035_:
{
lean_object* v_fieldInst_x3f_2038_; 
v_fieldInst_x3f_2038_ = lean_ctor_get(v_a_2034_, 6);
lean_inc(v_fieldInst_x3f_2038_);
if (lean_obj_tag(v_fieldInst_x3f_2038_) == 1)
{
lean_object* v_toRing_2039_; lean_object* v_val_2040_; lean_object* v___y_2042_; lean_object* v___y_2043_; lean_object* v___y_2044_; lean_object* v___y_2045_; lean_object* v___y_2046_; lean_object* v___y_2047_; lean_object* v___y_2048_; lean_object* v___y_2049_; lean_object* v___y_2050_; lean_object* v___y_2051_; lean_object* v___x_2061_; 
lean_del_object(v___x_2036_);
v_toRing_2039_ = lean_ctor_get(v_a_2034_, 0);
lean_inc_ref(v_toRing_2039_);
lean_dec(v_a_2034_);
v_val_2040_ = lean_ctor_get(v_fieldInst_x3f_2038_, 0);
lean_inc(v_val_2040_);
lean_dec_ref_known(v_fieldInst_x3f_2038_, 1);
v___x_2061_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v_a_2008_, v_a_2009_, v_a_2010_, v_a_2011_, v_a_2012_, v_a_2013_, v_a_2014_, v_a_2015_, v_a_2016_, v_a_2017_, v_a_2018_);
if (lean_obj_tag(v___x_2061_) == 0)
{
lean_object* v_a_2062_; lean_object* v___x_2064_; uint8_t v_isShared_2065_; uint8_t v_isSharedCheck_2261_; 
v_a_2062_ = lean_ctor_get(v___x_2061_, 0);
v_isSharedCheck_2261_ = !lean_is_exclusive(v___x_2061_);
if (v_isSharedCheck_2261_ == 0)
{
v___x_2064_ = v___x_2061_;
v_isShared_2065_ = v_isSharedCheck_2261_;
goto v_resetjp_2063_;
}
else
{
lean_inc(v_a_2062_);
lean_dec(v___x_2061_);
v___x_2064_ = lean_box(0);
v_isShared_2065_ = v_isSharedCheck_2261_;
goto v_resetjp_2063_;
}
v_resetjp_2063_:
{
lean_object* v_invSet_2066_; uint8_t v___x_2067_; 
v_invSet_2066_ = lean_ctor_get(v_a_2062_, 14);
lean_inc_ref(v_invSet_2066_);
lean_dec(v_a_2062_);
v___x_2067_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1___redArg(v_invSet_2066_, v_a_2007_);
lean_dec_ref(v_invSet_2066_);
if (v___x_2067_ == 0)
{
lean_object* v___f_2068_; lean_object* v___x_2069_; 
lean_del_object(v___x_2064_);
lean_inc_ref(v_a_2007_);
v___f_2068_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___lam__0), 2, 1);
lean_closure_set(v___f_2068_, 0, v_a_2007_);
v___x_2069_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(v___f_2068_, v_a_2008_, v_a_2009_);
if (lean_obj_tag(v___x_2069_) == 0)
{
lean_object* v___x_2070_; 
lean_dec_ref_known(v___x_2069_, 1);
lean_inc_ref(v_a_2007_);
v___x_2070_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f(v_a_2007_, v_a_2008_, v_a_2009_, v_a_2010_, v_a_2011_, v_a_2012_, v_a_2013_, v_a_2014_, v_a_2015_, v_a_2016_, v_a_2017_, v_a_2018_);
if (lean_obj_tag(v___x_2070_) == 0)
{
lean_object* v_a_2071_; 
v_a_2071_ = lean_ctor_get(v___x_2070_, 0);
lean_inc(v_a_2071_);
lean_dec_ref_known(v___x_2070_, 1);
if (lean_obj_tag(v_a_2071_) == 1)
{
lean_object* v_val_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; uint8_t v___x_2075_; 
v_val_2072_ = lean_ctor_get(v_a_2071_, 0);
lean_inc(v_val_2072_);
lean_dec_ref_known(v_a_2071_, 1);
v___x_2073_ = lean_unsigned_to_nat(0u);
v___x_2074_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__4___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__4___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__4___closed__1);
v___x_2075_ = lean_int_dec_eq(v_val_2072_, v___x_2074_);
if (v___x_2075_ == 0)
{
lean_object* v___x_2076_; 
v___x_2076_ = l_Lean_Meta_Grind_Arith_CommRing_hasChar(v_a_2008_, v_a_2009_, v_a_2010_, v_a_2011_, v_a_2012_, v_a_2013_, v_a_2014_, v_a_2015_, v_a_2016_, v_a_2017_, v_a_2018_);
if (lean_obj_tag(v___x_2076_) == 0)
{
lean_object* v_a_2077_; uint8_t v___x_2078_; 
v_a_2077_ = lean_ctor_get(v___x_2076_, 0);
lean_inc(v_a_2077_);
lean_dec_ref_known(v___x_2076_, 1);
v___x_2078_ = lean_unbox(v_a_2077_);
lean_dec(v_a_2077_);
if (v___x_2078_ == 0)
{
lean_dec(v_val_2072_);
lean_dec_ref(v_e_2005_);
v___y_2042_ = v_a_2009_;
v___y_2043_ = v_a_2010_;
v___y_2044_ = v_a_2011_;
v___y_2045_ = v_a_2012_;
v___y_2046_ = v_a_2013_;
v___y_2047_ = v_a_2014_;
v___y_2048_ = v_a_2015_;
v___y_2049_ = v_a_2016_;
v___y_2050_ = v_a_2017_;
v___y_2051_ = v_a_2018_;
goto v___jp_2041_;
}
else
{
lean_object* v___x_2079_; 
v___x_2079_ = l_Lean_Meta_Grind_Arith_CommRing_getCharInst(v_a_2008_, v_a_2009_, v_a_2010_, v_a_2011_, v_a_2012_, v_a_2013_, v_a_2014_, v_a_2015_, v_a_2016_, v_a_2017_, v_a_2018_);
if (lean_obj_tag(v___x_2079_) == 0)
{
lean_object* v_a_2080_; lean_object* v_fst_2081_; lean_object* v_snd_2082_; lean_object* v___x_2084_; uint8_t v_isShared_2085_; uint8_t v_isSharedCheck_2215_; 
v_a_2080_ = lean_ctor_get(v___x_2079_, 0);
lean_inc(v_a_2080_);
lean_dec_ref_known(v___x_2079_, 1);
v_fst_2081_ = lean_ctor_get(v_a_2080_, 0);
v_snd_2082_ = lean_ctor_get(v_a_2080_, 1);
v_isSharedCheck_2215_ = !lean_is_exclusive(v_a_2080_);
if (v_isSharedCheck_2215_ == 0)
{
v___x_2084_ = v_a_2080_;
v_isShared_2085_ = v_isSharedCheck_2215_;
goto v_resetjp_2083_;
}
else
{
lean_inc(v_snd_2082_);
lean_inc(v_fst_2081_);
lean_dec(v_a_2080_);
v___x_2084_ = lean_box(0);
v_isShared_2085_ = v_isSharedCheck_2215_;
goto v_resetjp_2083_;
}
v_resetjp_2083_:
{
uint8_t v___x_2086_; 
v___x_2086_ = lean_nat_dec_eq(v_snd_2082_, v___x_2073_);
if (v___x_2086_ == 0)
{
lean_object* v___x_2087_; lean_object* v___x_2088_; uint8_t v___x_2089_; 
lean_inc(v_snd_2082_);
v___x_2087_ = lean_nat_to_int(v_snd_2082_);
v___x_2088_ = lean_int_emod(v_val_2072_, v___x_2087_);
lean_dec(v___x_2087_);
v___x_2089_ = lean_int_dec_eq(v___x_2088_, v___x_2074_);
lean_dec(v___x_2088_);
if (v___x_2089_ == 0)
{
lean_object* v___x_2090_; 
v___x_2090_ = l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__3(v_a_2008_, v_a_2009_, v_a_2010_, v_a_2011_, v_a_2012_, v_a_2013_, v_a_2014_, v_a_2015_, v_a_2016_, v_a_2017_, v_a_2018_);
if (lean_obj_tag(v___x_2090_) == 0)
{
lean_object* v_a_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; 
v_a_2091_ = lean_ctor_get(v___x_2090_, 0);
lean_inc(v_a_2091_);
lean_dec_ref_known(v___x_2090_, 1);
v___x_2092_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__3, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__3);
v___x_2093_ = l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__4(v___x_2092_, v_a_2008_, v_a_2009_, v_a_2010_, v_a_2011_, v_a_2012_, v_a_2013_, v_a_2014_, v_a_2015_, v_a_2016_, v_a_2017_, v_a_2018_);
if (lean_obj_tag(v___x_2093_) == 0)
{
lean_object* v_a_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; 
v_a_2094_ = lean_ctor_get(v___x_2093_, 0);
lean_inc(v_a_2094_);
lean_dec_ref_known(v___x_2093_, 1);
v___x_2095_ = l_Lean_mkAppB(v_a_2091_, v_a_2007_, v_e_2005_);
v___x_2096_ = l_Lean_Meta_mkEq(v___x_2095_, v_a_2094_, v_a_2015_, v_a_2016_, v_a_2017_, v_a_2018_);
if (lean_obj_tag(v___x_2096_) == 0)
{
lean_object* v_a_2097_; lean_object* v_type_2098_; lean_object* v_u_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; lean_object* v___x_2103_; 
v_a_2097_ = lean_ctor_get(v___x_2096_, 0);
lean_inc(v_a_2097_);
lean_dec_ref_known(v___x_2096_, 1);
v_type_2098_ = lean_ctor_get(v_toRing_2039_, 1);
lean_inc_ref(v_type_2098_);
v_u_2099_ = lean_ctor_get(v_toRing_2039_, 2);
lean_inc(v_u_2099_);
lean_dec_ref(v_toRing_2039_);
v___x_2100_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__5));
v___x_2101_ = lean_box(0);
if (v_isShared_2085_ == 0)
{
lean_ctor_set_tag(v___x_2084_, 1);
lean_ctor_set(v___x_2084_, 1, v___x_2101_);
lean_ctor_set(v___x_2084_, 0, v_u_2099_);
v___x_2103_ = v___x_2084_;
goto v_reusejp_2102_;
}
else
{
lean_object* v_reuseFailAlloc_2111_; 
v_reuseFailAlloc_2111_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2111_, 0, v_u_2099_);
lean_ctor_set(v_reuseFailAlloc_2111_, 1, v___x_2101_);
v___x_2103_ = v_reuseFailAlloc_2111_;
goto v_reusejp_2102_;
}
v_reusejp_2102_:
{
lean_object* v___x_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; 
v___x_2104_ = l_Lean_mkConst(v___x_2100_, v___x_2103_);
v___x_2105_ = l_Lean_mkNatLit(v_snd_2082_);
v___x_2106_ = l_Lean_mkIntLit(v_val_2072_);
lean_dec(v_val_2072_);
v___x_2107_ = l_Lean_eagerReflBoolTrue;
v___x_2108_ = l_Lean_mkApp6(v___x_2104_, v_type_2098_, v___x_2105_, v_val_2040_, v_fst_2081_, v___x_2106_, v___x_2107_);
v___x_2109_ = l_Lean_Meta_mkExpectedPropHint(v___x_2108_, v_a_2097_);
v___x_2110_ = l_Lean_Meta_Grind_pushNewFact(v___x_2109_, v___x_2073_, v_a_2009_, v_a_2010_, v_a_2011_, v_a_2012_, v_a_2013_, v_a_2014_, v_a_2015_, v_a_2016_, v_a_2017_, v_a_2018_);
if (lean_obj_tag(v___x_2110_) == 0)
{
lean_dec_ref_known(v___x_2110_, 1);
goto v___jp_2020_;
}
else
{
return v___x_2110_;
}
}
}
else
{
lean_object* v_a_2112_; lean_object* v___x_2114_; uint8_t v_isShared_2115_; uint8_t v_isSharedCheck_2119_; 
lean_del_object(v___x_2084_);
lean_dec(v_snd_2082_);
lean_dec(v_fst_2081_);
lean_dec(v_val_2072_);
lean_dec(v_val_2040_);
lean_dec_ref(v_toRing_2039_);
v_a_2112_ = lean_ctor_get(v___x_2096_, 0);
v_isSharedCheck_2119_ = !lean_is_exclusive(v___x_2096_);
if (v_isSharedCheck_2119_ == 0)
{
v___x_2114_ = v___x_2096_;
v_isShared_2115_ = v_isSharedCheck_2119_;
goto v_resetjp_2113_;
}
else
{
lean_inc(v_a_2112_);
lean_dec(v___x_2096_);
v___x_2114_ = lean_box(0);
v_isShared_2115_ = v_isSharedCheck_2119_;
goto v_resetjp_2113_;
}
v_resetjp_2113_:
{
lean_object* v___x_2117_; 
if (v_isShared_2115_ == 0)
{
v___x_2117_ = v___x_2114_;
goto v_reusejp_2116_;
}
else
{
lean_object* v_reuseFailAlloc_2118_; 
v_reuseFailAlloc_2118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2118_, 0, v_a_2112_);
v___x_2117_ = v_reuseFailAlloc_2118_;
goto v_reusejp_2116_;
}
v_reusejp_2116_:
{
return v___x_2117_;
}
}
}
}
else
{
lean_object* v_a_2120_; lean_object* v___x_2122_; uint8_t v_isShared_2123_; uint8_t v_isSharedCheck_2127_; 
lean_dec(v_a_2091_);
lean_del_object(v___x_2084_);
lean_dec(v_snd_2082_);
lean_dec(v_fst_2081_);
lean_dec(v_val_2072_);
lean_dec(v_val_2040_);
lean_dec_ref(v_toRing_2039_);
lean_dec_ref(v_a_2007_);
lean_dec_ref(v_e_2005_);
v_a_2120_ = lean_ctor_get(v___x_2093_, 0);
v_isSharedCheck_2127_ = !lean_is_exclusive(v___x_2093_);
if (v_isSharedCheck_2127_ == 0)
{
v___x_2122_ = v___x_2093_;
v_isShared_2123_ = v_isSharedCheck_2127_;
goto v_resetjp_2121_;
}
else
{
lean_inc(v_a_2120_);
lean_dec(v___x_2093_);
v___x_2122_ = lean_box(0);
v_isShared_2123_ = v_isSharedCheck_2127_;
goto v_resetjp_2121_;
}
v_resetjp_2121_:
{
lean_object* v___x_2125_; 
if (v_isShared_2123_ == 0)
{
v___x_2125_ = v___x_2122_;
goto v_reusejp_2124_;
}
else
{
lean_object* v_reuseFailAlloc_2126_; 
v_reuseFailAlloc_2126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2126_, 0, v_a_2120_);
v___x_2125_ = v_reuseFailAlloc_2126_;
goto v_reusejp_2124_;
}
v_reusejp_2124_:
{
return v___x_2125_;
}
}
}
}
else
{
lean_object* v_a_2128_; lean_object* v___x_2130_; uint8_t v_isShared_2131_; uint8_t v_isSharedCheck_2135_; 
lean_del_object(v___x_2084_);
lean_dec(v_snd_2082_);
lean_dec(v_fst_2081_);
lean_dec(v_val_2072_);
lean_dec(v_val_2040_);
lean_dec_ref(v_toRing_2039_);
lean_dec_ref(v_a_2007_);
lean_dec_ref(v_e_2005_);
v_a_2128_ = lean_ctor_get(v___x_2090_, 0);
v_isSharedCheck_2135_ = !lean_is_exclusive(v___x_2090_);
if (v_isSharedCheck_2135_ == 0)
{
v___x_2130_ = v___x_2090_;
v_isShared_2131_ = v_isSharedCheck_2135_;
goto v_resetjp_2129_;
}
else
{
lean_inc(v_a_2128_);
lean_dec(v___x_2090_);
v___x_2130_ = lean_box(0);
v_isShared_2131_ = v_isSharedCheck_2135_;
goto v_resetjp_2129_;
}
v_resetjp_2129_:
{
lean_object* v___x_2133_; 
if (v_isShared_2131_ == 0)
{
v___x_2133_ = v___x_2130_;
goto v_reusejp_2132_;
}
else
{
lean_object* v_reuseFailAlloc_2134_; 
v_reuseFailAlloc_2134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2134_, 0, v_a_2128_);
v___x_2133_ = v_reuseFailAlloc_2134_;
goto v_reusejp_2132_;
}
v_reusejp_2132_:
{
return v___x_2133_;
}
}
}
}
else
{
lean_object* v___x_2136_; 
lean_dec_ref(v_a_2007_);
v___x_2136_ = l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__4(v___x_2074_, v_a_2008_, v_a_2009_, v_a_2010_, v_a_2011_, v_a_2012_, v_a_2013_, v_a_2014_, v_a_2015_, v_a_2016_, v_a_2017_, v_a_2018_);
if (lean_obj_tag(v___x_2136_) == 0)
{
lean_object* v_a_2137_; lean_object* v___x_2138_; 
v_a_2137_ = lean_ctor_get(v___x_2136_, 0);
lean_inc(v_a_2137_);
lean_dec_ref_known(v___x_2136_, 1);
v___x_2138_ = l_Lean_Meta_mkEq(v_e_2005_, v_a_2137_, v_a_2015_, v_a_2016_, v_a_2017_, v_a_2018_);
if (lean_obj_tag(v___x_2138_) == 0)
{
lean_object* v_a_2139_; lean_object* v_type_2140_; lean_object* v_u_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2145_; 
v_a_2139_ = lean_ctor_get(v___x_2138_, 0);
lean_inc(v_a_2139_);
lean_dec_ref_known(v___x_2138_, 1);
v_type_2140_ = lean_ctor_get(v_toRing_2039_, 1);
lean_inc_ref(v_type_2140_);
v_u_2141_ = lean_ctor_get(v_toRing_2039_, 2);
lean_inc(v_u_2141_);
lean_dec_ref(v_toRing_2039_);
v___x_2142_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__7));
v___x_2143_ = lean_box(0);
if (v_isShared_2085_ == 0)
{
lean_ctor_set_tag(v___x_2084_, 1);
lean_ctor_set(v___x_2084_, 1, v___x_2143_);
lean_ctor_set(v___x_2084_, 0, v_u_2141_);
v___x_2145_ = v___x_2084_;
goto v_reusejp_2144_;
}
else
{
lean_object* v_reuseFailAlloc_2153_; 
v_reuseFailAlloc_2153_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2153_, 0, v_u_2141_);
lean_ctor_set(v_reuseFailAlloc_2153_, 1, v___x_2143_);
v___x_2145_ = v_reuseFailAlloc_2153_;
goto v_reusejp_2144_;
}
v_reusejp_2144_:
{
lean_object* v___x_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; 
v___x_2146_ = l_Lean_mkConst(v___x_2142_, v___x_2145_);
v___x_2147_ = l_Lean_mkNatLit(v_snd_2082_);
v___x_2148_ = l_Lean_mkIntLit(v_val_2072_);
lean_dec(v_val_2072_);
v___x_2149_ = l_Lean_eagerReflBoolTrue;
v___x_2150_ = l_Lean_mkApp6(v___x_2146_, v_type_2140_, v___x_2147_, v_val_2040_, v_fst_2081_, v___x_2148_, v___x_2149_);
v___x_2151_ = l_Lean_Meta_mkExpectedPropHint(v___x_2150_, v_a_2139_);
v___x_2152_ = l_Lean_Meta_Grind_pushNewFact(v___x_2151_, v___x_2073_, v_a_2009_, v_a_2010_, v_a_2011_, v_a_2012_, v_a_2013_, v_a_2014_, v_a_2015_, v_a_2016_, v_a_2017_, v_a_2018_);
if (lean_obj_tag(v___x_2152_) == 0)
{
lean_dec_ref_known(v___x_2152_, 1);
goto v___jp_2020_;
}
else
{
return v___x_2152_;
}
}
}
else
{
lean_object* v_a_2154_; lean_object* v___x_2156_; uint8_t v_isShared_2157_; uint8_t v_isSharedCheck_2161_; 
lean_del_object(v___x_2084_);
lean_dec(v_snd_2082_);
lean_dec(v_fst_2081_);
lean_dec(v_val_2072_);
lean_dec(v_val_2040_);
lean_dec_ref(v_toRing_2039_);
v_a_2154_ = lean_ctor_get(v___x_2138_, 0);
v_isSharedCheck_2161_ = !lean_is_exclusive(v___x_2138_);
if (v_isSharedCheck_2161_ == 0)
{
v___x_2156_ = v___x_2138_;
v_isShared_2157_ = v_isSharedCheck_2161_;
goto v_resetjp_2155_;
}
else
{
lean_inc(v_a_2154_);
lean_dec(v___x_2138_);
v___x_2156_ = lean_box(0);
v_isShared_2157_ = v_isSharedCheck_2161_;
goto v_resetjp_2155_;
}
v_resetjp_2155_:
{
lean_object* v___x_2159_; 
if (v_isShared_2157_ == 0)
{
v___x_2159_ = v___x_2156_;
goto v_reusejp_2158_;
}
else
{
lean_object* v_reuseFailAlloc_2160_; 
v_reuseFailAlloc_2160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2160_, 0, v_a_2154_);
v___x_2159_ = v_reuseFailAlloc_2160_;
goto v_reusejp_2158_;
}
v_reusejp_2158_:
{
return v___x_2159_;
}
}
}
}
else
{
lean_object* v_a_2162_; lean_object* v___x_2164_; uint8_t v_isShared_2165_; uint8_t v_isSharedCheck_2169_; 
lean_del_object(v___x_2084_);
lean_dec(v_snd_2082_);
lean_dec(v_fst_2081_);
lean_dec(v_val_2072_);
lean_dec(v_val_2040_);
lean_dec_ref(v_toRing_2039_);
lean_dec_ref(v_e_2005_);
v_a_2162_ = lean_ctor_get(v___x_2136_, 0);
v_isSharedCheck_2169_ = !lean_is_exclusive(v___x_2136_);
if (v_isSharedCheck_2169_ == 0)
{
v___x_2164_ = v___x_2136_;
v_isShared_2165_ = v_isSharedCheck_2169_;
goto v_resetjp_2163_;
}
else
{
lean_inc(v_a_2162_);
lean_dec(v___x_2136_);
v___x_2164_ = lean_box(0);
v_isShared_2165_ = v_isSharedCheck_2169_;
goto v_resetjp_2163_;
}
v_resetjp_2163_:
{
lean_object* v___x_2167_; 
if (v_isShared_2165_ == 0)
{
v___x_2167_ = v___x_2164_;
goto v_reusejp_2166_;
}
else
{
lean_object* v_reuseFailAlloc_2168_; 
v_reuseFailAlloc_2168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2168_, 0, v_a_2162_);
v___x_2167_ = v_reuseFailAlloc_2168_;
goto v_reusejp_2166_;
}
v_reusejp_2166_:
{
return v___x_2167_;
}
}
}
}
}
else
{
lean_object* v___x_2170_; 
lean_dec(v_snd_2082_);
v___x_2170_ = l_Lean_Meta_Grind_Arith_CommRing_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__3(v_a_2008_, v_a_2009_, v_a_2010_, v_a_2011_, v_a_2012_, v_a_2013_, v_a_2014_, v_a_2015_, v_a_2016_, v_a_2017_, v_a_2018_);
if (lean_obj_tag(v___x_2170_) == 0)
{
lean_object* v_a_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; 
v_a_2171_ = lean_ctor_get(v___x_2170_, 0);
lean_inc(v_a_2171_);
lean_dec_ref_known(v___x_2170_, 1);
v___x_2172_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__3, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__3);
v___x_2173_ = l_Lean_Meta_Grind_Arith_CommRing_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__4(v___x_2172_, v_a_2008_, v_a_2009_, v_a_2010_, v_a_2011_, v_a_2012_, v_a_2013_, v_a_2014_, v_a_2015_, v_a_2016_, v_a_2017_, v_a_2018_);
if (lean_obj_tag(v___x_2173_) == 0)
{
lean_object* v_a_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; 
v_a_2174_ = lean_ctor_get(v___x_2173_, 0);
lean_inc(v_a_2174_);
lean_dec_ref_known(v___x_2173_, 1);
v___x_2175_ = l_Lean_mkAppB(v_a_2171_, v_a_2007_, v_e_2005_);
v___x_2176_ = l_Lean_Meta_mkEq(v___x_2175_, v_a_2174_, v_a_2015_, v_a_2016_, v_a_2017_, v_a_2018_);
if (lean_obj_tag(v___x_2176_) == 0)
{
lean_object* v_a_2177_; lean_object* v_type_2178_; lean_object* v_u_2179_; lean_object* v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2183_; 
v_a_2177_ = lean_ctor_get(v___x_2176_, 0);
lean_inc(v_a_2177_);
lean_dec_ref_known(v___x_2176_, 1);
v_type_2178_ = lean_ctor_get(v_toRing_2039_, 1);
lean_inc_ref(v_type_2178_);
v_u_2179_ = lean_ctor_get(v_toRing_2039_, 2);
lean_inc(v_u_2179_);
lean_dec_ref(v_toRing_2039_);
v___x_2180_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__9));
v___x_2181_ = lean_box(0);
if (v_isShared_2085_ == 0)
{
lean_ctor_set_tag(v___x_2084_, 1);
lean_ctor_set(v___x_2084_, 1, v___x_2181_);
lean_ctor_set(v___x_2084_, 0, v_u_2179_);
v___x_2183_ = v___x_2084_;
goto v_reusejp_2182_;
}
else
{
lean_object* v_reuseFailAlloc_2190_; 
v_reuseFailAlloc_2190_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2190_, 0, v_u_2179_);
lean_ctor_set(v_reuseFailAlloc_2190_, 1, v___x_2181_);
v___x_2183_ = v_reuseFailAlloc_2190_;
goto v_reusejp_2182_;
}
v_reusejp_2182_:
{
lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; 
v___x_2184_ = l_Lean_mkConst(v___x_2180_, v___x_2183_);
v___x_2185_ = l_Lean_mkIntLit(v_val_2072_);
lean_dec(v_val_2072_);
v___x_2186_ = l_Lean_eagerReflBoolTrue;
v___x_2187_ = l_Lean_mkApp5(v___x_2184_, v_type_2178_, v_val_2040_, v_fst_2081_, v___x_2185_, v___x_2186_);
v___x_2188_ = l_Lean_Meta_mkExpectedPropHint(v___x_2187_, v_a_2177_);
v___x_2189_ = l_Lean_Meta_Grind_pushNewFact(v___x_2188_, v___x_2073_, v_a_2009_, v_a_2010_, v_a_2011_, v_a_2012_, v_a_2013_, v_a_2014_, v_a_2015_, v_a_2016_, v_a_2017_, v_a_2018_);
if (lean_obj_tag(v___x_2189_) == 0)
{
lean_dec_ref_known(v___x_2189_, 1);
goto v___jp_2020_;
}
else
{
return v___x_2189_;
}
}
}
else
{
lean_object* v_a_2191_; lean_object* v___x_2193_; uint8_t v_isShared_2194_; uint8_t v_isSharedCheck_2198_; 
lean_del_object(v___x_2084_);
lean_dec(v_fst_2081_);
lean_dec(v_val_2072_);
lean_dec(v_val_2040_);
lean_dec_ref(v_toRing_2039_);
v_a_2191_ = lean_ctor_get(v___x_2176_, 0);
v_isSharedCheck_2198_ = !lean_is_exclusive(v___x_2176_);
if (v_isSharedCheck_2198_ == 0)
{
v___x_2193_ = v___x_2176_;
v_isShared_2194_ = v_isSharedCheck_2198_;
goto v_resetjp_2192_;
}
else
{
lean_inc(v_a_2191_);
lean_dec(v___x_2176_);
v___x_2193_ = lean_box(0);
v_isShared_2194_ = v_isSharedCheck_2198_;
goto v_resetjp_2192_;
}
v_resetjp_2192_:
{
lean_object* v___x_2196_; 
if (v_isShared_2194_ == 0)
{
v___x_2196_ = v___x_2193_;
goto v_reusejp_2195_;
}
else
{
lean_object* v_reuseFailAlloc_2197_; 
v_reuseFailAlloc_2197_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2197_, 0, v_a_2191_);
v___x_2196_ = v_reuseFailAlloc_2197_;
goto v_reusejp_2195_;
}
v_reusejp_2195_:
{
return v___x_2196_;
}
}
}
}
else
{
lean_object* v_a_2199_; lean_object* v___x_2201_; uint8_t v_isShared_2202_; uint8_t v_isSharedCheck_2206_; 
lean_dec(v_a_2171_);
lean_del_object(v___x_2084_);
lean_dec(v_fst_2081_);
lean_dec(v_val_2072_);
lean_dec(v_val_2040_);
lean_dec_ref(v_toRing_2039_);
lean_dec_ref(v_a_2007_);
lean_dec_ref(v_e_2005_);
v_a_2199_ = lean_ctor_get(v___x_2173_, 0);
v_isSharedCheck_2206_ = !lean_is_exclusive(v___x_2173_);
if (v_isSharedCheck_2206_ == 0)
{
v___x_2201_ = v___x_2173_;
v_isShared_2202_ = v_isSharedCheck_2206_;
goto v_resetjp_2200_;
}
else
{
lean_inc(v_a_2199_);
lean_dec(v___x_2173_);
v___x_2201_ = lean_box(0);
v_isShared_2202_ = v_isSharedCheck_2206_;
goto v_resetjp_2200_;
}
v_resetjp_2200_:
{
lean_object* v___x_2204_; 
if (v_isShared_2202_ == 0)
{
v___x_2204_ = v___x_2201_;
goto v_reusejp_2203_;
}
else
{
lean_object* v_reuseFailAlloc_2205_; 
v_reuseFailAlloc_2205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2205_, 0, v_a_2199_);
v___x_2204_ = v_reuseFailAlloc_2205_;
goto v_reusejp_2203_;
}
v_reusejp_2203_:
{
return v___x_2204_;
}
}
}
}
else
{
lean_object* v_a_2207_; lean_object* v___x_2209_; uint8_t v_isShared_2210_; uint8_t v_isSharedCheck_2214_; 
lean_del_object(v___x_2084_);
lean_dec(v_fst_2081_);
lean_dec(v_val_2072_);
lean_dec(v_val_2040_);
lean_dec_ref(v_toRing_2039_);
lean_dec_ref(v_a_2007_);
lean_dec_ref(v_e_2005_);
v_a_2207_ = lean_ctor_get(v___x_2170_, 0);
v_isSharedCheck_2214_ = !lean_is_exclusive(v___x_2170_);
if (v_isSharedCheck_2214_ == 0)
{
v___x_2209_ = v___x_2170_;
v_isShared_2210_ = v_isSharedCheck_2214_;
goto v_resetjp_2208_;
}
else
{
lean_inc(v_a_2207_);
lean_dec(v___x_2170_);
v___x_2209_ = lean_box(0);
v_isShared_2210_ = v_isSharedCheck_2214_;
goto v_resetjp_2208_;
}
v_resetjp_2208_:
{
lean_object* v___x_2212_; 
if (v_isShared_2210_ == 0)
{
v___x_2212_ = v___x_2209_;
goto v_reusejp_2211_;
}
else
{
lean_object* v_reuseFailAlloc_2213_; 
v_reuseFailAlloc_2213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2213_, 0, v_a_2207_);
v___x_2212_ = v_reuseFailAlloc_2213_;
goto v_reusejp_2211_;
}
v_reusejp_2211_:
{
return v___x_2212_;
}
}
}
}
}
}
else
{
lean_object* v_a_2216_; lean_object* v___x_2218_; uint8_t v_isShared_2219_; uint8_t v_isSharedCheck_2223_; 
lean_dec(v_val_2072_);
lean_dec(v_val_2040_);
lean_dec_ref(v_toRing_2039_);
lean_dec_ref(v_a_2007_);
lean_dec_ref(v_e_2005_);
v_a_2216_ = lean_ctor_get(v___x_2079_, 0);
v_isSharedCheck_2223_ = !lean_is_exclusive(v___x_2079_);
if (v_isSharedCheck_2223_ == 0)
{
v___x_2218_ = v___x_2079_;
v_isShared_2219_ = v_isSharedCheck_2223_;
goto v_resetjp_2217_;
}
else
{
lean_inc(v_a_2216_);
lean_dec(v___x_2079_);
v___x_2218_ = lean_box(0);
v_isShared_2219_ = v_isSharedCheck_2223_;
goto v_resetjp_2217_;
}
v_resetjp_2217_:
{
lean_object* v___x_2221_; 
if (v_isShared_2219_ == 0)
{
v___x_2221_ = v___x_2218_;
goto v_reusejp_2220_;
}
else
{
lean_object* v_reuseFailAlloc_2222_; 
v_reuseFailAlloc_2222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2222_, 0, v_a_2216_);
v___x_2221_ = v_reuseFailAlloc_2222_;
goto v_reusejp_2220_;
}
v_reusejp_2220_:
{
return v___x_2221_;
}
}
}
}
}
else
{
lean_object* v_a_2224_; lean_object* v___x_2226_; uint8_t v_isShared_2227_; uint8_t v_isSharedCheck_2231_; 
lean_dec(v_val_2072_);
lean_dec(v_val_2040_);
lean_dec_ref(v_toRing_2039_);
lean_dec_ref(v_a_2007_);
lean_dec_ref(v_e_2005_);
v_a_2224_ = lean_ctor_get(v___x_2076_, 0);
v_isSharedCheck_2231_ = !lean_is_exclusive(v___x_2076_);
if (v_isSharedCheck_2231_ == 0)
{
v___x_2226_ = v___x_2076_;
v_isShared_2227_ = v_isSharedCheck_2231_;
goto v_resetjp_2225_;
}
else
{
lean_inc(v_a_2224_);
lean_dec(v___x_2076_);
v___x_2226_ = lean_box(0);
v_isShared_2227_ = v_isSharedCheck_2231_;
goto v_resetjp_2225_;
}
v_resetjp_2225_:
{
lean_object* v___x_2229_; 
if (v_isShared_2227_ == 0)
{
v___x_2229_ = v___x_2226_;
goto v_reusejp_2228_;
}
else
{
lean_object* v_reuseFailAlloc_2230_; 
v_reuseFailAlloc_2230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2230_, 0, v_a_2224_);
v___x_2229_ = v_reuseFailAlloc_2230_;
goto v_reusejp_2228_;
}
v_reusejp_2228_:
{
return v___x_2229_;
}
}
}
}
else
{
lean_object* v_type_2232_; lean_object* v_u_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; 
lean_dec(v_val_2072_);
v_type_2232_ = lean_ctor_get(v_toRing_2039_, 1);
lean_inc_ref(v_type_2232_);
v_u_2233_ = lean_ctor_get(v_toRing_2039_, 2);
lean_inc(v_u_2233_);
lean_dec_ref(v_toRing_2039_);
v___x_2234_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__11));
v___x_2235_ = lean_box(0);
v___x_2236_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2236_, 0, v_u_2233_);
lean_ctor_set(v___x_2236_, 1, v___x_2235_);
v___x_2237_ = l_Lean_mkConst(v___x_2234_, v___x_2236_);
v___x_2238_ = l_Lean_mkAppB(v___x_2237_, v_type_2232_, v_val_2040_);
v___x_2239_ = l_Lean_Meta_Grind_pushEqCore___redArg(v_e_2005_, v_a_2007_, v___x_2238_, v___x_2067_, v_a_2009_, v_a_2011_, v_a_2015_, v_a_2016_, v_a_2017_, v_a_2018_);
if (lean_obj_tag(v___x_2239_) == 0)
{
lean_object* v___x_2241_; uint8_t v_isShared_2242_; uint8_t v_isSharedCheck_2247_; 
v_isSharedCheck_2247_ = !lean_is_exclusive(v___x_2239_);
if (v_isSharedCheck_2247_ == 0)
{
lean_object* v_unused_2248_; 
v_unused_2248_ = lean_ctor_get(v___x_2239_, 0);
lean_dec(v_unused_2248_);
v___x_2241_ = v___x_2239_;
v_isShared_2242_ = v_isSharedCheck_2247_;
goto v_resetjp_2240_;
}
else
{
lean_dec(v___x_2239_);
v___x_2241_ = lean_box(0);
v_isShared_2242_ = v_isSharedCheck_2247_;
goto v_resetjp_2240_;
}
v_resetjp_2240_:
{
lean_object* v___x_2243_; lean_object* v___x_2245_; 
v___x_2243_ = lean_box(0);
if (v_isShared_2242_ == 0)
{
lean_ctor_set(v___x_2241_, 0, v___x_2243_);
v___x_2245_ = v___x_2241_;
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
else
{
return v___x_2239_;
}
}
}
else
{
lean_dec(v_a_2071_);
lean_dec_ref(v_e_2005_);
v___y_2042_ = v_a_2009_;
v___y_2043_ = v_a_2010_;
v___y_2044_ = v_a_2011_;
v___y_2045_ = v_a_2012_;
v___y_2046_ = v_a_2013_;
v___y_2047_ = v_a_2014_;
v___y_2048_ = v_a_2015_;
v___y_2049_ = v_a_2016_;
v___y_2050_ = v_a_2017_;
v___y_2051_ = v_a_2018_;
goto v___jp_2041_;
}
}
else
{
lean_object* v_a_2249_; lean_object* v___x_2251_; uint8_t v_isShared_2252_; uint8_t v_isSharedCheck_2256_; 
lean_dec(v_val_2040_);
lean_dec_ref(v_toRing_2039_);
lean_dec_ref(v_a_2007_);
lean_dec_ref(v_e_2005_);
v_a_2249_ = lean_ctor_get(v___x_2070_, 0);
v_isSharedCheck_2256_ = !lean_is_exclusive(v___x_2070_);
if (v_isSharedCheck_2256_ == 0)
{
v___x_2251_ = v___x_2070_;
v_isShared_2252_ = v_isSharedCheck_2256_;
goto v_resetjp_2250_;
}
else
{
lean_inc(v_a_2249_);
lean_dec(v___x_2070_);
v___x_2251_ = lean_box(0);
v_isShared_2252_ = v_isSharedCheck_2256_;
goto v_resetjp_2250_;
}
v_resetjp_2250_:
{
lean_object* v___x_2254_; 
if (v_isShared_2252_ == 0)
{
v___x_2254_ = v___x_2251_;
goto v_reusejp_2253_;
}
else
{
lean_object* v_reuseFailAlloc_2255_; 
v_reuseFailAlloc_2255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2255_, 0, v_a_2249_);
v___x_2254_ = v_reuseFailAlloc_2255_;
goto v_reusejp_2253_;
}
v_reusejp_2253_:
{
return v___x_2254_;
}
}
}
}
else
{
lean_dec(v_val_2040_);
lean_dec_ref(v_toRing_2039_);
lean_dec_ref(v_a_2007_);
lean_dec_ref(v_e_2005_);
return v___x_2069_;
}
}
else
{
lean_object* v___x_2257_; lean_object* v___x_2259_; 
lean_dec(v_val_2040_);
lean_dec_ref(v_toRing_2039_);
lean_dec_ref(v_a_2007_);
lean_dec_ref(v_e_2005_);
v___x_2257_ = lean_box(0);
if (v_isShared_2065_ == 0)
{
lean_ctor_set(v___x_2064_, 0, v___x_2257_);
v___x_2259_ = v___x_2064_;
goto v_reusejp_2258_;
}
else
{
lean_object* v_reuseFailAlloc_2260_; 
v_reuseFailAlloc_2260_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2260_, 0, v___x_2257_);
v___x_2259_ = v_reuseFailAlloc_2260_;
goto v_reusejp_2258_;
}
v_reusejp_2258_:
{
return v___x_2259_;
}
}
}
}
else
{
lean_object* v_a_2262_; lean_object* v___x_2264_; uint8_t v_isShared_2265_; uint8_t v_isSharedCheck_2269_; 
lean_dec(v_val_2040_);
lean_dec_ref(v_toRing_2039_);
lean_dec_ref(v_a_2007_);
lean_dec_ref(v_e_2005_);
v_a_2262_ = lean_ctor_get(v___x_2061_, 0);
v_isSharedCheck_2269_ = !lean_is_exclusive(v___x_2061_);
if (v_isSharedCheck_2269_ == 0)
{
v___x_2264_ = v___x_2061_;
v_isShared_2265_ = v_isSharedCheck_2269_;
goto v_resetjp_2263_;
}
else
{
lean_inc(v_a_2262_);
lean_dec(v___x_2061_);
v___x_2264_ = lean_box(0);
v_isShared_2265_ = v_isSharedCheck_2269_;
goto v_resetjp_2263_;
}
v_resetjp_2263_:
{
lean_object* v___x_2267_; 
if (v_isShared_2265_ == 0)
{
v___x_2267_ = v___x_2264_;
goto v_reusejp_2266_;
}
else
{
lean_object* v_reuseFailAlloc_2268_; 
v_reuseFailAlloc_2268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2268_, 0, v_a_2262_);
v___x_2267_ = v_reuseFailAlloc_2268_;
goto v_reusejp_2266_;
}
v_reusejp_2266_:
{
return v___x_2267_;
}
}
}
v___jp_2041_:
{
lean_object* v_type_2052_; lean_object* v_u_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; 
v_type_2052_ = lean_ctor_get(v_toRing_2039_, 1);
lean_inc_ref(v_type_2052_);
v_u_2053_ = lean_ctor_get(v_toRing_2039_, 2);
lean_inc(v_u_2053_);
lean_dec_ref(v_toRing_2039_);
v___x_2054_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__2));
v___x_2055_ = lean_box(0);
v___x_2056_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2056_, 0, v_u_2053_);
lean_ctor_set(v___x_2056_, 1, v___x_2055_);
v___x_2057_ = l_Lean_mkConst(v___x_2054_, v___x_2056_);
v___x_2058_ = l_Lean_mkApp3(v___x_2057_, v_type_2052_, v_val_2040_, v_a_2007_);
v___x_2059_ = lean_unsigned_to_nat(0u);
v___x_2060_ = l_Lean_Meta_Grind_pushNewFact(v___x_2058_, v___x_2059_, v___y_2042_, v___y_2043_, v___y_2044_, v___y_2045_, v___y_2046_, v___y_2047_, v___y_2048_, v___y_2049_, v___y_2050_, v___y_2051_);
return v___x_2060_;
}
}
else
{
lean_object* v___x_2270_; lean_object* v___x_2272_; 
lean_dec(v_fieldInst_x3f_2038_);
lean_dec(v_a_2034_);
lean_dec_ref(v_a_2007_);
lean_dec_ref(v_e_2005_);
v___x_2270_ = lean_box(0);
if (v_isShared_2037_ == 0)
{
lean_ctor_set(v___x_2036_, 0, v___x_2270_);
v___x_2272_ = v___x_2036_;
goto v_reusejp_2271_;
}
else
{
lean_object* v_reuseFailAlloc_2273_; 
v_reuseFailAlloc_2273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2273_, 0, v___x_2270_);
v___x_2272_ = v_reuseFailAlloc_2273_;
goto v_reusejp_2271_;
}
v_reusejp_2271_:
{
return v___x_2272_;
}
}
}
}
else
{
lean_object* v_a_2275_; lean_object* v___x_2277_; uint8_t v_isShared_2278_; uint8_t v_isSharedCheck_2282_; 
lean_dec_ref(v_a_2007_);
lean_dec_ref(v_e_2005_);
v_a_2275_ = lean_ctor_get(v___x_2033_, 0);
v_isSharedCheck_2282_ = !lean_is_exclusive(v___x_2033_);
if (v_isSharedCheck_2282_ == 0)
{
v___x_2277_ = v___x_2033_;
v_isShared_2278_ = v_isSharedCheck_2282_;
goto v_resetjp_2276_;
}
else
{
lean_inc(v_a_2275_);
lean_dec(v___x_2033_);
v___x_2277_ = lean_box(0);
v_isShared_2278_ = v_isSharedCheck_2282_;
goto v_resetjp_2276_;
}
v_resetjp_2276_:
{
lean_object* v___x_2280_; 
if (v_isShared_2278_ == 0)
{
v___x_2280_ = v___x_2277_;
goto v_reusejp_2279_;
}
else
{
lean_object* v_reuseFailAlloc_2281_; 
v_reuseFailAlloc_2281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2281_, 0, v_a_2275_);
v___x_2280_ = v_reuseFailAlloc_2281_;
goto v_reusejp_2279_;
}
v_reusejp_2279_:
{
return v___x_2280_;
}
}
}
}
}
}
else
{
lean_object* v_a_2284_; lean_object* v___x_2286_; uint8_t v_isShared_2287_; uint8_t v_isSharedCheck_2291_; 
lean_dec_ref(v_a_2007_);
lean_dec_ref(v_e_2005_);
v_a_2284_ = lean_ctor_get(v___x_2023_, 0);
v_isSharedCheck_2291_ = !lean_is_exclusive(v___x_2023_);
if (v_isSharedCheck_2291_ == 0)
{
v___x_2286_ = v___x_2023_;
v_isShared_2287_ = v_isSharedCheck_2291_;
goto v_resetjp_2285_;
}
else
{
lean_inc(v_a_2284_);
lean_dec(v___x_2023_);
v___x_2286_ = lean_box(0);
v_isShared_2287_ = v_isSharedCheck_2291_;
goto v_resetjp_2285_;
}
v_resetjp_2285_:
{
lean_object* v___x_2289_; 
if (v_isShared_2287_ == 0)
{
v___x_2289_ = v___x_2286_;
goto v_reusejp_2288_;
}
else
{
lean_object* v_reuseFailAlloc_2290_; 
v_reuseFailAlloc_2290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2290_, 0, v_a_2284_);
v___x_2289_ = v_reuseFailAlloc_2290_;
goto v_reusejp_2288_;
}
v_reusejp_2288_:
{
return v___x_2289_;
}
}
}
v___jp_2020_:
{
lean_object* v___x_2021_; lean_object* v___x_2022_; 
v___x_2021_ = lean_box(0);
v___x_2022_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2022_, 0, v___x_2021_);
return v___x_2022_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___boxed(lean_object* v_e_2292_, lean_object* v_inst_2293_, lean_object* v_a_2294_, lean_object* v_a_2295_, lean_object* v_a_2296_, lean_object* v_a_2297_, lean_object* v_a_2298_, lean_object* v_a_2299_, lean_object* v_a_2300_, lean_object* v_a_2301_, lean_object* v_a_2302_, lean_object* v_a_2303_, lean_object* v_a_2304_, lean_object* v_a_2305_, lean_object* v_a_2306_){
_start:
{
lean_object* v_res_2307_; 
v_res_2307_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv(v_e_2292_, v_inst_2293_, v_a_2294_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_, v_a_2301_, v_a_2302_, v_a_2303_, v_a_2304_, v_a_2305_);
lean_dec(v_a_2305_);
lean_dec_ref(v_a_2304_);
lean_dec(v_a_2303_);
lean_dec_ref(v_a_2302_);
lean_dec(v_a_2301_);
lean_dec_ref(v_a_2300_);
lean_dec(v_a_2299_);
lean_dec_ref(v_a_2298_);
lean_dec(v_a_2297_);
lean_dec(v_a_2296_);
lean_dec_ref(v_a_2295_);
lean_dec_ref(v_inst_2293_);
return v_res_2307_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0(lean_object* v_00_u03b2_2308_, lean_object* v_x_2309_, lean_object* v_x_2310_, lean_object* v_x_2311_){
_start:
{
lean_object* v___x_2312_; 
v___x_2312_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0___redArg(v_x_2309_, v_x_2310_, v_x_2311_);
return v___x_2312_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1(lean_object* v_00_u03b2_2313_, lean_object* v_x_2314_, lean_object* v_x_2315_){
_start:
{
uint8_t v___x_2316_; 
v___x_2316_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1___redArg(v_x_2314_, v_x_2315_);
return v___x_2316_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1___boxed(lean_object* v_00_u03b2_2317_, lean_object* v_x_2318_, lean_object* v_x_2319_){
_start:
{
uint8_t v_res_2320_; lean_object* v_r_2321_; 
v_res_2320_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1(v_00_u03b2_2317_, v_x_2318_, v_x_2319_);
lean_dec_ref(v_x_2319_);
lean_dec_ref(v_x_2318_);
v_r_2321_ = lean_box(v_res_2320_);
return v_r_2321_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0(lean_object* v_00_u03b2_2322_, lean_object* v_x_2323_, size_t v_x_2324_, size_t v_x_2325_, lean_object* v_x_2326_, lean_object* v_x_2327_){
_start:
{
lean_object* v___x_2328_; 
v___x_2328_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg(v_x_2323_, v_x_2324_, v_x_2325_, v_x_2326_, v_x_2327_);
return v___x_2328_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2329_, lean_object* v_x_2330_, lean_object* v_x_2331_, lean_object* v_x_2332_, lean_object* v_x_2333_, lean_object* v_x_2334_){
_start:
{
size_t v_x_82460__boxed_2335_; size_t v_x_82461__boxed_2336_; lean_object* v_res_2337_; 
v_x_82460__boxed_2335_ = lean_unbox_usize(v_x_2331_);
lean_dec(v_x_2331_);
v_x_82461__boxed_2336_ = lean_unbox_usize(v_x_2332_);
lean_dec(v_x_2332_);
v_res_2337_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0(v_00_u03b2_2329_, v_x_2330_, v_x_82460__boxed_2335_, v_x_82461__boxed_2336_, v_x_2333_, v_x_2334_);
return v_res_2337_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1_spec__2(lean_object* v_00_u03b2_2338_, lean_object* v_x_2339_, size_t v_x_2340_, lean_object* v_x_2341_){
_start:
{
uint8_t v___x_2342_; 
v___x_2342_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1_spec__2___redArg(v_x_2339_, v_x_2340_, v_x_2341_);
return v___x_2342_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1_spec__2___boxed(lean_object* v_00_u03b2_2343_, lean_object* v_x_2344_, lean_object* v_x_2345_, lean_object* v_x_2346_){
_start:
{
size_t v_x_82477__boxed_2347_; uint8_t v_res_2348_; lean_object* v_r_2349_; 
v_x_82477__boxed_2347_ = lean_unbox_usize(v_x_2345_);
lean_dec(v_x_2345_);
v_res_2348_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1_spec__2(v_00_u03b2_2343_, v_x_2344_, v_x_82477__boxed_2347_, v_x_2346_);
lean_dec_ref(v_x_2346_);
lean_dec_ref(v_x_2344_);
v_r_2349_ = lean_box(v_res_2348_);
return v_r_2349_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_2350_, lean_object* v_n_2351_, lean_object* v_k_2352_, lean_object* v_v_2353_){
_start:
{
lean_object* v___x_2354_; 
v___x_2354_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0_spec__2___redArg(v_n_2351_, v_k_2352_, v_v_2353_);
return v___x_2354_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_2355_, size_t v_depth_2356_, lean_object* v_keys_2357_, lean_object* v_vals_2358_, lean_object* v_heq_2359_, lean_object* v_i_2360_, lean_object* v_entries_2361_){
_start:
{
lean_object* v___x_2362_; 
v___x_2362_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0_spec__3___redArg(v_depth_2356_, v_keys_2357_, v_vals_2358_, v_i_2360_, v_entries_2361_);
return v___x_2362_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b2_2363_, lean_object* v_depth_2364_, lean_object* v_keys_2365_, lean_object* v_vals_2366_, lean_object* v_heq_2367_, lean_object* v_i_2368_, lean_object* v_entries_2369_){
_start:
{
size_t v_depth_boxed_2370_; lean_object* v_res_2371_; 
v_depth_boxed_2370_ = lean_unbox_usize(v_depth_2364_);
lean_dec(v_depth_2364_);
v_res_2371_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0_spec__3(v_00_u03b2_2363_, v_depth_boxed_2370_, v_keys_2365_, v_vals_2366_, v_heq_2367_, v_i_2368_, v_entries_2369_);
lean_dec_ref(v_vals_2366_);
lean_dec_ref(v_keys_2365_);
return v_res_2371_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1_spec__2_spec__6(lean_object* v_00_u03b2_2372_, lean_object* v_keys_2373_, lean_object* v_vals_2374_, lean_object* v_heq_2375_, lean_object* v_i_2376_, lean_object* v_k_2377_){
_start:
{
uint8_t v___x_2378_; 
v___x_2378_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1_spec__2_spec__6___redArg(v_keys_2373_, v_i_2376_, v_k_2377_);
return v___x_2378_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1_spec__2_spec__6___boxed(lean_object* v_00_u03b2_2379_, lean_object* v_keys_2380_, lean_object* v_vals_2381_, lean_object* v_heq_2382_, lean_object* v_i_2383_, lean_object* v_k_2384_){
_start:
{
uint8_t v_res_2385_; lean_object* v_r_2386_; 
v_res_2385_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1_spec__2_spec__6(v_00_u03b2_2379_, v_keys_2380_, v_vals_2381_, v_heq_2382_, v_i_2383_, v_k_2384_);
lean_dec_ref(v_k_2384_);
lean_dec_ref(v_vals_2381_);
lean_dec_ref(v_keys_2380_);
v_r_2386_ = lean_box(v_res_2385_);
return v_r_2386_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0_spec__2_spec__6(lean_object* v_00_u03b2_2387_, lean_object* v_x_2388_, lean_object* v_x_2389_, lean_object* v_x_2390_, lean_object* v_x_2391_){
_start:
{
lean_object* v___x_2392_; 
v___x_2392_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0_spec__2_spec__6___redArg(v_x_2388_, v_x_2389_, v_x_2390_, v_x_2391_);
return v___x_2392_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars___lam__0(lean_object* v_size_2393_, lean_object* v_s_2394_){
_start:
{
lean_object* v_toRing_2395_; lean_object* v_invFn_x3f_2396_; lean_object* v_semiringId_x3f_2397_; lean_object* v_commSemiringInst_2398_; lean_object* v_commRingInst_2399_; lean_object* v_noZeroDivInst_x3f_2400_; lean_object* v_fieldInst_x3f_2401_; lean_object* v_powIdentityInst_x3f_2402_; lean_object* v_denoteEntries_2403_; lean_object* v_nextId_2404_; lean_object* v_steps_2405_; lean_object* v_queue_2406_; lean_object* v_basis_2407_; lean_object* v_diseqs_2408_; uint8_t v_recheck_2409_; lean_object* v_invSet_2410_; lean_object* v_numEq0_x3f_2411_; uint8_t v_numEq0Updated_2412_; lean_object* v___x_2414_; uint8_t v_isShared_2415_; uint8_t v_isSharedCheck_2419_; 
v_toRing_2395_ = lean_ctor_get(v_s_2394_, 0);
v_invFn_x3f_2396_ = lean_ctor_get(v_s_2394_, 1);
v_semiringId_x3f_2397_ = lean_ctor_get(v_s_2394_, 2);
v_commSemiringInst_2398_ = lean_ctor_get(v_s_2394_, 3);
v_commRingInst_2399_ = lean_ctor_get(v_s_2394_, 4);
v_noZeroDivInst_x3f_2400_ = lean_ctor_get(v_s_2394_, 5);
v_fieldInst_x3f_2401_ = lean_ctor_get(v_s_2394_, 6);
v_powIdentityInst_x3f_2402_ = lean_ctor_get(v_s_2394_, 7);
v_denoteEntries_2403_ = lean_ctor_get(v_s_2394_, 8);
v_nextId_2404_ = lean_ctor_get(v_s_2394_, 9);
v_steps_2405_ = lean_ctor_get(v_s_2394_, 10);
v_queue_2406_ = lean_ctor_get(v_s_2394_, 11);
v_basis_2407_ = lean_ctor_get(v_s_2394_, 12);
v_diseqs_2408_ = lean_ctor_get(v_s_2394_, 13);
v_recheck_2409_ = lean_ctor_get_uint8(v_s_2394_, sizeof(void*)*17);
v_invSet_2410_ = lean_ctor_get(v_s_2394_, 14);
v_numEq0_x3f_2411_ = lean_ctor_get(v_s_2394_, 16);
v_numEq0Updated_2412_ = lean_ctor_get_uint8(v_s_2394_, sizeof(void*)*17 + 1);
v_isSharedCheck_2419_ = !lean_is_exclusive(v_s_2394_);
if (v_isSharedCheck_2419_ == 0)
{
lean_object* v_unused_2420_; 
v_unused_2420_ = lean_ctor_get(v_s_2394_, 15);
lean_dec(v_unused_2420_);
v___x_2414_ = v_s_2394_;
v_isShared_2415_ = v_isSharedCheck_2419_;
goto v_resetjp_2413_;
}
else
{
lean_inc(v_numEq0_x3f_2411_);
lean_inc(v_invSet_2410_);
lean_inc(v_diseqs_2408_);
lean_inc(v_basis_2407_);
lean_inc(v_queue_2406_);
lean_inc(v_steps_2405_);
lean_inc(v_nextId_2404_);
lean_inc(v_denoteEntries_2403_);
lean_inc(v_powIdentityInst_x3f_2402_);
lean_inc(v_fieldInst_x3f_2401_);
lean_inc(v_noZeroDivInst_x3f_2400_);
lean_inc(v_commRingInst_2399_);
lean_inc(v_commSemiringInst_2398_);
lean_inc(v_semiringId_x3f_2397_);
lean_inc(v_invFn_x3f_2396_);
lean_inc(v_toRing_2395_);
lean_dec(v_s_2394_);
v___x_2414_ = lean_box(0);
v_isShared_2415_ = v_isSharedCheck_2419_;
goto v_resetjp_2413_;
}
v_resetjp_2413_:
{
lean_object* v___x_2417_; 
if (v_isShared_2415_ == 0)
{
lean_ctor_set(v___x_2414_, 15, v_size_2393_);
v___x_2417_ = v___x_2414_;
goto v_reusejp_2416_;
}
else
{
lean_object* v_reuseFailAlloc_2418_; 
v_reuseFailAlloc_2418_ = lean_alloc_ctor(0, 17, 2);
lean_ctor_set(v_reuseFailAlloc_2418_, 0, v_toRing_2395_);
lean_ctor_set(v_reuseFailAlloc_2418_, 1, v_invFn_x3f_2396_);
lean_ctor_set(v_reuseFailAlloc_2418_, 2, v_semiringId_x3f_2397_);
lean_ctor_set(v_reuseFailAlloc_2418_, 3, v_commSemiringInst_2398_);
lean_ctor_set(v_reuseFailAlloc_2418_, 4, v_commRingInst_2399_);
lean_ctor_set(v_reuseFailAlloc_2418_, 5, v_noZeroDivInst_x3f_2400_);
lean_ctor_set(v_reuseFailAlloc_2418_, 6, v_fieldInst_x3f_2401_);
lean_ctor_set(v_reuseFailAlloc_2418_, 7, v_powIdentityInst_x3f_2402_);
lean_ctor_set(v_reuseFailAlloc_2418_, 8, v_denoteEntries_2403_);
lean_ctor_set(v_reuseFailAlloc_2418_, 9, v_nextId_2404_);
lean_ctor_set(v_reuseFailAlloc_2418_, 10, v_steps_2405_);
lean_ctor_set(v_reuseFailAlloc_2418_, 11, v_queue_2406_);
lean_ctor_set(v_reuseFailAlloc_2418_, 12, v_basis_2407_);
lean_ctor_set(v_reuseFailAlloc_2418_, 13, v_diseqs_2408_);
lean_ctor_set(v_reuseFailAlloc_2418_, 14, v_invSet_2410_);
lean_ctor_set(v_reuseFailAlloc_2418_, 15, v_size_2393_);
lean_ctor_set(v_reuseFailAlloc_2418_, 16, v_numEq0_x3f_2411_);
lean_ctor_set_uint8(v_reuseFailAlloc_2418_, sizeof(void*)*17, v_recheck_2409_);
lean_ctor_set_uint8(v_reuseFailAlloc_2418_, sizeof(void*)*17 + 1, v_numEq0Updated_2412_);
v___x_2417_ = v_reuseFailAlloc_2418_;
goto v_reusejp_2416_;
}
v_reusejp_2416_:
{
return v___x_2417_;
}
}
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_2421_; double v___x_2422_; 
v___x_2421_ = lean_unsigned_to_nat(0u);
v___x_2422_ = lean_float_of_nat(v___x_2421_);
return v___x_2422_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg(lean_object* v_cls_2426_, lean_object* v_msg_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_, lean_object* v___y_2431_){
_start:
{
lean_object* v_ref_2433_; lean_object* v___x_2434_; lean_object* v_a_2435_; lean_object* v___x_2437_; uint8_t v_isShared_2438_; uint8_t v_isSharedCheck_2479_; 
v_ref_2433_ = lean_ctor_get(v___y_2430_, 2);
v___x_2434_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1_spec__5_spec__8_spec__9(v_msg_2427_, v___y_2428_, v___y_2429_, v___y_2430_, v___y_2431_);
v_a_2435_ = lean_ctor_get(v___x_2434_, 0);
v_isSharedCheck_2479_ = !lean_is_exclusive(v___x_2434_);
if (v_isSharedCheck_2479_ == 0)
{
v___x_2437_ = v___x_2434_;
v_isShared_2438_ = v_isSharedCheck_2479_;
goto v_resetjp_2436_;
}
else
{
lean_inc(v_a_2435_);
lean_dec(v___x_2434_);
v___x_2437_ = lean_box(0);
v_isShared_2438_ = v_isSharedCheck_2479_;
goto v_resetjp_2436_;
}
v_resetjp_2436_:
{
lean_object* v___x_2439_; lean_object* v_traceState_2440_; lean_object* v_env_2441_; lean_object* v_nextMacroScope_2442_; lean_object* v_ngen_2443_; lean_object* v_auxDeclNGen_2444_; lean_object* v_cache_2445_; lean_object* v_messages_2446_; lean_object* v_infoState_2447_; lean_object* v_snapshotTasks_2448_; lean_object* v___x_2450_; uint8_t v_isShared_2451_; uint8_t v_isSharedCheck_2478_; 
v___x_2439_ = lean_st_ref_take(v___y_2431_);
v_traceState_2440_ = lean_ctor_get(v___x_2439_, 4);
v_env_2441_ = lean_ctor_get(v___x_2439_, 0);
v_nextMacroScope_2442_ = lean_ctor_get(v___x_2439_, 1);
v_ngen_2443_ = lean_ctor_get(v___x_2439_, 2);
v_auxDeclNGen_2444_ = lean_ctor_get(v___x_2439_, 3);
v_cache_2445_ = lean_ctor_get(v___x_2439_, 5);
v_messages_2446_ = lean_ctor_get(v___x_2439_, 6);
v_infoState_2447_ = lean_ctor_get(v___x_2439_, 7);
v_snapshotTasks_2448_ = lean_ctor_get(v___x_2439_, 8);
v_isSharedCheck_2478_ = !lean_is_exclusive(v___x_2439_);
if (v_isSharedCheck_2478_ == 0)
{
v___x_2450_ = v___x_2439_;
v_isShared_2451_ = v_isSharedCheck_2478_;
goto v_resetjp_2449_;
}
else
{
lean_inc(v_snapshotTasks_2448_);
lean_inc(v_infoState_2447_);
lean_inc(v_messages_2446_);
lean_inc(v_cache_2445_);
lean_inc(v_traceState_2440_);
lean_inc(v_auxDeclNGen_2444_);
lean_inc(v_ngen_2443_);
lean_inc(v_nextMacroScope_2442_);
lean_inc(v_env_2441_);
lean_dec(v___x_2439_);
v___x_2450_ = lean_box(0);
v_isShared_2451_ = v_isSharedCheck_2478_;
goto v_resetjp_2449_;
}
v_resetjp_2449_:
{
uint64_t v_tid_2452_; lean_object* v_traces_2453_; lean_object* v___x_2455_; uint8_t v_isShared_2456_; uint8_t v_isSharedCheck_2477_; 
v_tid_2452_ = lean_ctor_get_uint64(v_traceState_2440_, sizeof(void*)*1);
v_traces_2453_ = lean_ctor_get(v_traceState_2440_, 0);
v_isSharedCheck_2477_ = !lean_is_exclusive(v_traceState_2440_);
if (v_isSharedCheck_2477_ == 0)
{
v___x_2455_ = v_traceState_2440_;
v_isShared_2456_ = v_isSharedCheck_2477_;
goto v_resetjp_2454_;
}
else
{
lean_inc(v_traces_2453_);
lean_dec(v_traceState_2440_);
v___x_2455_ = lean_box(0);
v_isShared_2456_ = v_isSharedCheck_2477_;
goto v_resetjp_2454_;
}
v_resetjp_2454_:
{
lean_object* v___x_2457_; double v___x_2458_; uint8_t v___x_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v___x_2467_; 
v___x_2457_ = lean_box(0);
v___x_2458_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg___closed__0);
v___x_2459_ = 0;
v___x_2460_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg___closed__1));
v___x_2461_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2461_, 0, v_cls_2426_);
lean_ctor_set(v___x_2461_, 1, v___x_2457_);
lean_ctor_set(v___x_2461_, 2, v___x_2460_);
lean_ctor_set_float(v___x_2461_, sizeof(void*)*3, v___x_2458_);
lean_ctor_set_float(v___x_2461_, sizeof(void*)*3 + 8, v___x_2458_);
lean_ctor_set_uint8(v___x_2461_, sizeof(void*)*3 + 16, v___x_2459_);
v___x_2462_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg___closed__2));
v___x_2463_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2463_, 0, v___x_2461_);
lean_ctor_set(v___x_2463_, 1, v_a_2435_);
lean_ctor_set(v___x_2463_, 2, v___x_2462_);
lean_inc(v_ref_2433_);
v___x_2464_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2464_, 0, v_ref_2433_);
lean_ctor_set(v___x_2464_, 1, v___x_2463_);
v___x_2465_ = l_Lean_PersistentArray_push___redArg(v_traces_2453_, v___x_2464_);
if (v_isShared_2456_ == 0)
{
lean_ctor_set(v___x_2455_, 0, v___x_2465_);
v___x_2467_ = v___x_2455_;
goto v_reusejp_2466_;
}
else
{
lean_object* v_reuseFailAlloc_2476_; 
v_reuseFailAlloc_2476_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2476_, 0, v___x_2465_);
lean_ctor_set_uint64(v_reuseFailAlloc_2476_, sizeof(void*)*1, v_tid_2452_);
v___x_2467_ = v_reuseFailAlloc_2476_;
goto v_reusejp_2466_;
}
v_reusejp_2466_:
{
lean_object* v___x_2469_; 
if (v_isShared_2451_ == 0)
{
lean_ctor_set(v___x_2450_, 4, v___x_2467_);
v___x_2469_ = v___x_2450_;
goto v_reusejp_2468_;
}
else
{
lean_object* v_reuseFailAlloc_2475_; 
v_reuseFailAlloc_2475_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2475_, 0, v_env_2441_);
lean_ctor_set(v_reuseFailAlloc_2475_, 1, v_nextMacroScope_2442_);
lean_ctor_set(v_reuseFailAlloc_2475_, 2, v_ngen_2443_);
lean_ctor_set(v_reuseFailAlloc_2475_, 3, v_auxDeclNGen_2444_);
lean_ctor_set(v_reuseFailAlloc_2475_, 4, v___x_2467_);
lean_ctor_set(v_reuseFailAlloc_2475_, 5, v_cache_2445_);
lean_ctor_set(v_reuseFailAlloc_2475_, 6, v_messages_2446_);
lean_ctor_set(v_reuseFailAlloc_2475_, 7, v_infoState_2447_);
lean_ctor_set(v_reuseFailAlloc_2475_, 8, v_snapshotTasks_2448_);
v___x_2469_ = v_reuseFailAlloc_2475_;
goto v_reusejp_2468_;
}
v_reusejp_2468_:
{
lean_object* v___x_2470_; lean_object* v___x_2471_; lean_object* v___x_2473_; 
v___x_2470_ = lean_st_ref_put(v___y_2431_, v___x_2469_);
v___x_2471_ = lean_box(0);
if (v_isShared_2438_ == 0)
{
lean_ctor_set(v___x_2437_, 0, v___x_2471_);
v___x_2473_ = v___x_2437_;
goto v_reusejp_2472_;
}
else
{
lean_object* v_reuseFailAlloc_2474_; 
v_reuseFailAlloc_2474_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2474_, 0, v___x_2471_);
v___x_2473_ = v_reuseFailAlloc_2474_;
goto v_reusejp_2472_;
}
v_reusejp_2472_:
{
return v___x_2473_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg___boxed(lean_object* v_cls_2480_, lean_object* v_msg_2481_, lean_object* v___y_2482_, lean_object* v___y_2483_, lean_object* v___y_2484_, lean_object* v___y_2485_, lean_object* v___y_2486_){
_start:
{
lean_object* v_res_2487_; 
v_res_2487_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg(v_cls_2480_, v_msg_2481_, v___y_2482_, v___y_2483_, v___y_2484_, v___y_2485_);
lean_dec(v___y_2485_);
lean_dec_ref(v___y_2484_);
lean_dec(v___y_2483_);
lean_dec_ref(v___y_2482_);
return v_res_2487_;
}
}
static lean_object* _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__8(void){
_start:
{
lean_object* v___x_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; 
v___x_2503_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__5));
v___x_2504_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__7));
v___x_2505_ = l_Lean_Name_append(v___x_2504_, v___x_2503_);
return v___x_2505_;
}
}
static lean_object* _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__10(void){
_start:
{
lean_object* v___x_2507_; lean_object* v___x_2508_; 
v___x_2507_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__9));
v___x_2508_ = l_Lean_stringToMessageData(v___x_2507_);
return v___x_2508_;
}
}
static lean_object* _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__12(void){
_start:
{
lean_object* v___x_2510_; lean_object* v___x_2511_; 
v___x_2510_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__11));
v___x_2511_ = l_Lean_stringToMessageData(v___x_2510_);
return v___x_2511_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg(lean_object* v___x_2512_, lean_object* v_snd_2513_, lean_object* v_fst_2514_, lean_object* v_fst_2515_, lean_object* v___x_2516_, lean_object* v_range_2517_, lean_object* v_b_2518_, lean_object* v_i_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_, lean_object* v___y_2524_, lean_object* v___y_2525_, lean_object* v___y_2526_, lean_object* v___y_2527_, lean_object* v___y_2528_, lean_object* v___y_2529_, lean_object* v___y_2530_){
_start:
{
lean_object* v_stop_2532_; lean_object* v_step_2533_; uint8_t v___x_2534_; 
v_stop_2532_ = lean_ctor_get(v_range_2517_, 1);
v_step_2533_ = lean_ctor_get(v_range_2517_, 2);
v___x_2534_ = lean_nat_dec_lt(v_i_2519_, v_stop_2532_);
if (v___x_2534_ == 0)
{
lean_object* v___x_2535_; 
lean_dec(v_i_2519_);
lean_dec_ref(v_fst_2515_);
lean_dec_ref(v_fst_2514_);
lean_dec(v_snd_2513_);
lean_dec_ref(v___x_2512_);
v___x_2535_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2535_, 0, v_b_2518_);
return v___x_2535_;
}
else
{
lean_object* v_size_2536_; lean_object* v___x_2537_; lean_object* v___y_2539_; lean_object* v___y_2540_; lean_object* v___y_2541_; lean_object* v___y_2542_; lean_object* v___y_2543_; lean_object* v___y_2544_; lean_object* v___y_2545_; lean_object* v___y_2546_; lean_object* v___y_2547_; lean_object* v___y_2548_; lean_object* v___y_2549_; lean_object* v___y_2563_; lean_object* v___x_2589_; uint8_t v___x_2590_; 
v_size_2536_ = lean_ctor_get(v___x_2516_, 2);
v___x_2537_ = lean_box(0);
v___x_2589_ = l_Lean_instInhabitedExpr;
v___x_2590_ = lean_nat_dec_lt(v_i_2519_, v_size_2536_);
if (v___x_2590_ == 0)
{
lean_object* v___x_2591_; 
v___x_2591_ = l_outOfBounds___redArg(v___x_2589_);
v___y_2563_ = v___x_2591_;
goto v___jp_2562_;
}
else
{
lean_object* v___x_2592_; 
v___x_2592_ = l_Lean_PersistentArray_get_x21___redArg(v___x_2589_, v___x_2516_, v_i_2519_);
v___y_2563_ = v___x_2592_;
goto v___jp_2562_;
}
v___jp_2538_:
{
lean_object* v_type_2550_; lean_object* v_u_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; 
v_type_2550_ = lean_ctor_get(v___x_2512_, 1);
v_u_2551_ = lean_ctor_get(v___x_2512_, 2);
v___x_2552_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__2));
v___x_2553_ = lean_box(0);
lean_inc(v_u_2551_);
v___x_2554_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2554_, 0, v_u_2551_);
lean_ctor_set(v___x_2554_, 1, v___x_2553_);
v___x_2555_ = l_Lean_mkConst(v___x_2552_, v___x_2554_);
lean_inc(v_snd_2513_);
v___x_2556_ = l_Lean_mkNatLit(v_snd_2513_);
lean_inc_ref(v_fst_2515_);
lean_inc_ref(v_fst_2514_);
lean_inc_ref(v_type_2550_);
v___x_2557_ = l_Lean_mkApp5(v___x_2555_, v_type_2550_, v_fst_2514_, v___x_2556_, v_fst_2515_, v___y_2539_);
v___x_2558_ = lean_unsigned_to_nat(0u);
v___x_2559_ = l_Lean_Meta_Grind_pushNewFact(v___x_2557_, v___x_2558_, v___y_2540_, v___y_2541_, v___y_2542_, v___y_2543_, v___y_2544_, v___y_2545_, v___y_2546_, v___y_2547_, v___y_2548_, v___y_2549_);
if (lean_obj_tag(v___x_2559_) == 0)
{
lean_object* v___x_2560_; 
lean_dec_ref_known(v___x_2559_, 1);
v___x_2560_ = lean_nat_add(v_i_2519_, v_step_2533_);
lean_dec(v_i_2519_);
v_b_2518_ = v___x_2537_;
v_i_2519_ = v___x_2560_;
goto _start;
}
else
{
lean_dec(v_i_2519_);
lean_dec_ref(v_fst_2515_);
lean_dec_ref(v_fst_2514_);
lean_dec(v_snd_2513_);
lean_dec_ref(v___x_2512_);
return v___x_2559_;
}
}
v___jp_2562_:
{
lean_object* v_toCold_2564_; lean_object* v_options_2565_; uint8_t v_hasTrace_2566_; 
v_toCold_2564_ = lean_ctor_get(v___y_2529_, 0);
v_options_2565_ = lean_ctor_get(v_toCold_2564_, 2);
v_hasTrace_2566_ = lean_ctor_get_uint8(v_options_2565_, sizeof(void*)*1);
if (v_hasTrace_2566_ == 0)
{
v___y_2539_ = v___y_2563_;
v___y_2540_ = v___y_2521_;
v___y_2541_ = v___y_2522_;
v___y_2542_ = v___y_2523_;
v___y_2543_ = v___y_2524_;
v___y_2544_ = v___y_2525_;
v___y_2545_ = v___y_2526_;
v___y_2546_ = v___y_2527_;
v___y_2547_ = v___y_2528_;
v___y_2548_ = v___y_2529_;
v___y_2549_ = v___y_2530_;
goto v___jp_2538_;
}
else
{
lean_object* v_inheritedTraceOptions_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; uint8_t v___x_2570_; 
v_inheritedTraceOptions_2567_ = lean_ctor_get(v_toCold_2564_, 11);
v___x_2568_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__5));
v___x_2569_ = lean_obj_once(&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__8, &l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__8_once, _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__8);
v___x_2570_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2567_, v_options_2565_, v___x_2569_);
if (v___x_2570_ == 0)
{
v___y_2539_ = v___y_2563_;
v___y_2540_ = v___y_2521_;
v___y_2541_ = v___y_2522_;
v___y_2542_ = v___y_2523_;
v___y_2543_ = v___y_2524_;
v___y_2544_ = v___y_2525_;
v___y_2545_ = v___y_2526_;
v___y_2546_ = v___y_2527_;
v___y_2547_ = v___y_2528_;
v___y_2548_ = v___y_2529_;
v___y_2549_ = v___y_2530_;
goto v___jp_2538_;
}
else
{
lean_object* v___x_2571_; 
v___x_2571_ = l_Lean_Meta_Grind_updateLastTag(v___y_2521_, v___y_2522_, v___y_2523_, v___y_2524_, v___y_2525_, v___y_2526_, v___y_2527_, v___y_2528_, v___y_2529_, v___y_2530_);
if (lean_obj_tag(v___x_2571_) == 0)
{
lean_object* v___x_2573_; uint8_t v_isShared_2574_; uint8_t v_isSharedCheck_2587_; 
v_isSharedCheck_2587_ = !lean_is_exclusive(v___x_2571_);
if (v_isSharedCheck_2587_ == 0)
{
lean_object* v_unused_2588_; 
v_unused_2588_ = lean_ctor_get(v___x_2571_, 0);
lean_dec(v_unused_2588_);
v___x_2573_ = v___x_2571_;
v_isShared_2574_ = v_isSharedCheck_2587_;
goto v_resetjp_2572_;
}
else
{
lean_dec(v___x_2571_);
v___x_2573_ = lean_box(0);
v_isShared_2574_ = v_isSharedCheck_2587_;
goto v_resetjp_2572_;
}
v_resetjp_2572_:
{
lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2578_; 
v___x_2575_ = lean_obj_once(&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__10, &l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__10_once, _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__10);
lean_inc(v_snd_2513_);
v___x_2576_ = l_Nat_reprFast(v_snd_2513_);
if (v_isShared_2574_ == 0)
{
lean_ctor_set_tag(v___x_2573_, 3);
lean_ctor_set(v___x_2573_, 0, v___x_2576_);
v___x_2578_ = v___x_2573_;
goto v_reusejp_2577_;
}
else
{
lean_object* v_reuseFailAlloc_2586_; 
v_reuseFailAlloc_2586_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2586_, 0, v___x_2576_);
v___x_2578_ = v_reuseFailAlloc_2586_;
goto v_reusejp_2577_;
}
v_reusejp_2577_:
{
lean_object* v___x_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; 
v___x_2579_ = l_Lean_MessageData_ofFormat(v___x_2578_);
v___x_2580_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2580_, 0, v___x_2575_);
lean_ctor_set(v___x_2580_, 1, v___x_2579_);
v___x_2581_ = lean_obj_once(&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__12, &l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__12_once, _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__12);
v___x_2582_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2582_, 0, v___x_2580_);
lean_ctor_set(v___x_2582_, 1, v___x_2581_);
lean_inc_ref(v___y_2563_);
v___x_2583_ = l_Lean_MessageData_ofExpr(v___y_2563_);
v___x_2584_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2584_, 0, v___x_2582_);
lean_ctor_set(v___x_2584_, 1, v___x_2583_);
v___x_2585_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg(v___x_2568_, v___x_2584_, v___y_2527_, v___y_2528_, v___y_2529_, v___y_2530_);
if (lean_obj_tag(v___x_2585_) == 0)
{
lean_dec_ref_known(v___x_2585_, 1);
v___y_2539_ = v___y_2563_;
v___y_2540_ = v___y_2521_;
v___y_2541_ = v___y_2522_;
v___y_2542_ = v___y_2523_;
v___y_2543_ = v___y_2524_;
v___y_2544_ = v___y_2525_;
v___y_2545_ = v___y_2526_;
v___y_2546_ = v___y_2527_;
v___y_2547_ = v___y_2528_;
v___y_2548_ = v___y_2529_;
v___y_2549_ = v___y_2530_;
goto v___jp_2538_;
}
else
{
lean_dec_ref(v___y_2563_);
lean_dec(v_i_2519_);
lean_dec_ref(v_fst_2515_);
lean_dec_ref(v_fst_2514_);
lean_dec(v_snd_2513_);
lean_dec_ref(v___x_2512_);
return v___x_2585_;
}
}
}
}
else
{
lean_dec_ref(v___y_2563_);
lean_dec(v_i_2519_);
lean_dec_ref(v_fst_2515_);
lean_dec_ref(v_fst_2514_);
lean_dec(v_snd_2513_);
lean_dec_ref(v___x_2512_);
return v___x_2571_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___boxed(lean_object** _args){
lean_object* v___x_2593_ = _args[0];
lean_object* v_snd_2594_ = _args[1];
lean_object* v_fst_2595_ = _args[2];
lean_object* v_fst_2596_ = _args[3];
lean_object* v___x_2597_ = _args[4];
lean_object* v_range_2598_ = _args[5];
lean_object* v_b_2599_ = _args[6];
lean_object* v_i_2600_ = _args[7];
lean_object* v___y_2601_ = _args[8];
lean_object* v___y_2602_ = _args[9];
lean_object* v___y_2603_ = _args[10];
lean_object* v___y_2604_ = _args[11];
lean_object* v___y_2605_ = _args[12];
lean_object* v___y_2606_ = _args[13];
lean_object* v___y_2607_ = _args[14];
lean_object* v___y_2608_ = _args[15];
lean_object* v___y_2609_ = _args[16];
lean_object* v___y_2610_ = _args[17];
lean_object* v___y_2611_ = _args[18];
lean_object* v___y_2612_ = _args[19];
_start:
{
lean_object* v_res_2613_; 
v_res_2613_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg(v___x_2593_, v_snd_2594_, v_fst_2595_, v_fst_2596_, v___x_2597_, v_range_2598_, v_b_2599_, v_i_2600_, v___y_2601_, v___y_2602_, v___y_2603_, v___y_2604_, v___y_2605_, v___y_2606_, v___y_2607_, v___y_2608_, v___y_2609_, v___y_2610_, v___y_2611_);
lean_dec(v___y_2611_);
lean_dec_ref(v___y_2610_);
lean_dec(v___y_2609_);
lean_dec_ref(v___y_2608_);
lean_dec(v___y_2607_);
lean_dec_ref(v___y_2606_);
lean_dec(v___y_2605_);
lean_dec_ref(v___y_2604_);
lean_dec(v___y_2603_);
lean_dec(v___y_2602_);
lean_dec_ref(v___y_2601_);
lean_dec_ref(v_range_2598_);
lean_dec_ref(v___x_2597_);
return v_res_2613_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars(lean_object* v_a_2614_, lean_object* v_a_2615_, lean_object* v_a_2616_, lean_object* v_a_2617_, lean_object* v_a_2618_, lean_object* v_a_2619_, lean_object* v_a_2620_, lean_object* v_a_2621_, lean_object* v_a_2622_, lean_object* v_a_2623_, lean_object* v_a_2624_){
_start:
{
lean_object* v___x_2626_; 
v___x_2626_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v_a_2614_, v_a_2615_, v_a_2616_, v_a_2617_, v_a_2618_, v_a_2619_, v_a_2620_, v_a_2621_, v_a_2622_, v_a_2623_, v_a_2624_);
if (lean_obj_tag(v___x_2626_) == 0)
{
lean_object* v_a_2627_; lean_object* v___x_2629_; uint8_t v_isShared_2630_; uint8_t v_isSharedCheck_2656_; 
v_a_2627_ = lean_ctor_get(v___x_2626_, 0);
v_isSharedCheck_2656_ = !lean_is_exclusive(v___x_2626_);
if (v_isSharedCheck_2656_ == 0)
{
v___x_2629_ = v___x_2626_;
v_isShared_2630_ = v_isSharedCheck_2656_;
goto v_resetjp_2628_;
}
else
{
lean_inc(v_a_2627_);
lean_dec(v___x_2626_);
v___x_2629_ = lean_box(0);
v_isShared_2630_ = v_isSharedCheck_2656_;
goto v_resetjp_2628_;
}
v_resetjp_2628_:
{
lean_object* v_powIdentityInst_x3f_2631_; 
v_powIdentityInst_x3f_2631_ = lean_ctor_get(v_a_2627_, 7);
if (lean_obj_tag(v_powIdentityInst_x3f_2631_) == 1)
{
lean_object* v_val_2632_; lean_object* v_snd_2633_; lean_object* v_toRing_2634_; lean_object* v_vars_2635_; lean_object* v_powIdentityVarCount_2636_; lean_object* v_fst_2637_; lean_object* v_fst_2638_; lean_object* v_snd_2639_; lean_object* v_size_2640_; uint8_t v___x_2641_; 
v_val_2632_ = lean_ctor_get(v_powIdentityInst_x3f_2631_, 0);
lean_inc(v_val_2632_);
v_snd_2633_ = lean_ctor_get(v_val_2632_, 1);
lean_inc(v_snd_2633_);
v_toRing_2634_ = lean_ctor_get(v_a_2627_, 0);
lean_inc_ref(v_toRing_2634_);
v_vars_2635_ = lean_ctor_get(v_toRing_2634_, 14);
lean_inc_ref(v_vars_2635_);
v_powIdentityVarCount_2636_ = lean_ctor_get(v_a_2627_, 15);
lean_inc(v_powIdentityVarCount_2636_);
lean_dec(v_a_2627_);
v_fst_2637_ = lean_ctor_get(v_val_2632_, 0);
lean_inc(v_fst_2637_);
lean_dec(v_val_2632_);
v_fst_2638_ = lean_ctor_get(v_snd_2633_, 0);
lean_inc(v_fst_2638_);
v_snd_2639_ = lean_ctor_get(v_snd_2633_, 1);
lean_inc(v_snd_2639_);
lean_dec(v_snd_2633_);
v_size_2640_ = lean_ctor_get(v_vars_2635_, 2);
lean_inc(v_size_2640_);
v___x_2641_ = lean_nat_dec_le(v_size_2640_, v_powIdentityVarCount_2636_);
if (v___x_2641_ == 0)
{
lean_object* v___x_2642_; lean_object* v___x_2643_; lean_object* v___x_2644_; lean_object* v___x_2645_; 
lean_del_object(v___x_2629_);
v___x_2642_ = lean_unsigned_to_nat(1u);
lean_inc(v_size_2640_);
lean_inc(v_powIdentityVarCount_2636_);
v___x_2643_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2643_, 0, v_powIdentityVarCount_2636_);
lean_ctor_set(v___x_2643_, 1, v_size_2640_);
lean_ctor_set(v___x_2643_, 2, v___x_2642_);
v___x_2644_ = lean_box(0);
v___x_2645_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg(v_toRing_2634_, v_snd_2639_, v_fst_2638_, v_fst_2637_, v_vars_2635_, v___x_2643_, v___x_2644_, v_powIdentityVarCount_2636_, v_a_2614_, v_a_2615_, v_a_2616_, v_a_2617_, v_a_2618_, v_a_2619_, v_a_2620_, v_a_2621_, v_a_2622_, v_a_2623_, v_a_2624_);
lean_dec_ref_known(v___x_2643_, 3);
lean_dec_ref(v_vars_2635_);
if (lean_obj_tag(v___x_2645_) == 0)
{
lean_object* v___f_2646_; lean_object* v___x_2647_; 
lean_dec_ref_known(v___x_2645_, 1);
v___f_2646_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars___lam__0), 2, 1);
lean_closure_set(v___f_2646_, 0, v_size_2640_);
v___x_2647_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(v___f_2646_, v_a_2614_, v_a_2615_);
return v___x_2647_;
}
else
{
lean_dec(v_size_2640_);
return v___x_2645_;
}
}
else
{
lean_object* v___x_2648_; lean_object* v___x_2650_; 
lean_dec(v_size_2640_);
lean_dec(v_snd_2639_);
lean_dec(v_fst_2638_);
lean_dec(v_fst_2637_);
lean_dec(v_powIdentityVarCount_2636_);
lean_dec_ref(v_vars_2635_);
lean_dec_ref(v_toRing_2634_);
v___x_2648_ = lean_box(0);
if (v_isShared_2630_ == 0)
{
lean_ctor_set(v___x_2629_, 0, v___x_2648_);
v___x_2650_ = v___x_2629_;
goto v_reusejp_2649_;
}
else
{
lean_object* v_reuseFailAlloc_2651_; 
v_reuseFailAlloc_2651_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2651_, 0, v___x_2648_);
v___x_2650_ = v_reuseFailAlloc_2651_;
goto v_reusejp_2649_;
}
v_reusejp_2649_:
{
return v___x_2650_;
}
}
}
else
{
lean_object* v___x_2652_; lean_object* v___x_2654_; 
lean_dec(v_a_2627_);
v___x_2652_ = lean_box(0);
if (v_isShared_2630_ == 0)
{
lean_ctor_set(v___x_2629_, 0, v___x_2652_);
v___x_2654_ = v___x_2629_;
goto v_reusejp_2653_;
}
else
{
lean_object* v_reuseFailAlloc_2655_; 
v_reuseFailAlloc_2655_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2655_, 0, v___x_2652_);
v___x_2654_ = v_reuseFailAlloc_2655_;
goto v_reusejp_2653_;
}
v_reusejp_2653_:
{
return v___x_2654_;
}
}
}
}
else
{
lean_object* v_a_2657_; lean_object* v___x_2659_; uint8_t v_isShared_2660_; uint8_t v_isSharedCheck_2664_; 
v_a_2657_ = lean_ctor_get(v___x_2626_, 0);
v_isSharedCheck_2664_ = !lean_is_exclusive(v___x_2626_);
if (v_isSharedCheck_2664_ == 0)
{
v___x_2659_ = v___x_2626_;
v_isShared_2660_ = v_isSharedCheck_2664_;
goto v_resetjp_2658_;
}
else
{
lean_inc(v_a_2657_);
lean_dec(v___x_2626_);
v___x_2659_ = lean_box(0);
v_isShared_2660_ = v_isSharedCheck_2664_;
goto v_resetjp_2658_;
}
v_resetjp_2658_:
{
lean_object* v___x_2662_; 
if (v_isShared_2660_ == 0)
{
v___x_2662_ = v___x_2659_;
goto v_reusejp_2661_;
}
else
{
lean_object* v_reuseFailAlloc_2663_; 
v_reuseFailAlloc_2663_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2663_, 0, v_a_2657_);
v___x_2662_ = v_reuseFailAlloc_2663_;
goto v_reusejp_2661_;
}
v_reusejp_2661_:
{
return v___x_2662_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars___boxed(lean_object* v_a_2665_, lean_object* v_a_2666_, lean_object* v_a_2667_, lean_object* v_a_2668_, lean_object* v_a_2669_, lean_object* v_a_2670_, lean_object* v_a_2671_, lean_object* v_a_2672_, lean_object* v_a_2673_, lean_object* v_a_2674_, lean_object* v_a_2675_, lean_object* v_a_2676_){
_start:
{
lean_object* v_res_2677_; 
v_res_2677_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars(v_a_2665_, v_a_2666_, v_a_2667_, v_a_2668_, v_a_2669_, v_a_2670_, v_a_2671_, v_a_2672_, v_a_2673_, v_a_2674_, v_a_2675_);
lean_dec(v_a_2675_);
lean_dec_ref(v_a_2674_);
lean_dec(v_a_2673_);
lean_dec_ref(v_a_2672_);
lean_dec(v_a_2671_);
lean_dec_ref(v_a_2670_);
lean_dec(v_a_2669_);
lean_dec_ref(v_a_2668_);
lean_dec(v_a_2667_);
lean_dec(v_a_2666_);
lean_dec_ref(v_a_2665_);
return v_res_2677_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0(lean_object* v_cls_2678_, lean_object* v_msg_2679_, lean_object* v___y_2680_, lean_object* v___y_2681_, lean_object* v___y_2682_, lean_object* v___y_2683_, lean_object* v___y_2684_, lean_object* v___y_2685_, lean_object* v___y_2686_, lean_object* v___y_2687_, lean_object* v___y_2688_, lean_object* v___y_2689_, lean_object* v___y_2690_){
_start:
{
lean_object* v___x_2692_; 
v___x_2692_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg(v_cls_2678_, v_msg_2679_, v___y_2687_, v___y_2688_, v___y_2689_, v___y_2690_);
return v___x_2692_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___boxed(lean_object* v_cls_2693_, lean_object* v_msg_2694_, lean_object* v___y_2695_, lean_object* v___y_2696_, lean_object* v___y_2697_, lean_object* v___y_2698_, lean_object* v___y_2699_, lean_object* v___y_2700_, lean_object* v___y_2701_, lean_object* v___y_2702_, lean_object* v___y_2703_, lean_object* v___y_2704_, lean_object* v___y_2705_, lean_object* v___y_2706_){
_start:
{
lean_object* v_res_2707_; 
v_res_2707_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0(v_cls_2693_, v_msg_2694_, v___y_2695_, v___y_2696_, v___y_2697_, v___y_2698_, v___y_2699_, v___y_2700_, v___y_2701_, v___y_2702_, v___y_2703_, v___y_2704_, v___y_2705_);
lean_dec(v___y_2705_);
lean_dec_ref(v___y_2704_);
lean_dec(v___y_2703_);
lean_dec_ref(v___y_2702_);
lean_dec(v___y_2701_);
lean_dec_ref(v___y_2700_);
lean_dec(v___y_2699_);
lean_dec_ref(v___y_2698_);
lean_dec(v___y_2697_);
lean_dec(v___y_2696_);
lean_dec_ref(v___y_2695_);
return v_res_2707_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1(lean_object* v___x_2708_, lean_object* v_snd_2709_, lean_object* v_fst_2710_, lean_object* v_fst_2711_, lean_object* v___x_2712_, lean_object* v_range_2713_, lean_object* v_b_2714_, lean_object* v_i_2715_, lean_object* v_hs_2716_, lean_object* v_hl_2717_, lean_object* v___y_2718_, lean_object* v___y_2719_, lean_object* v___y_2720_, lean_object* v___y_2721_, lean_object* v___y_2722_, lean_object* v___y_2723_, lean_object* v___y_2724_, lean_object* v___y_2725_, lean_object* v___y_2726_, lean_object* v___y_2727_, lean_object* v___y_2728_){
_start:
{
lean_object* v___x_2730_; 
v___x_2730_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg(v___x_2708_, v_snd_2709_, v_fst_2710_, v_fst_2711_, v___x_2712_, v_range_2713_, v_b_2714_, v_i_2715_, v___y_2718_, v___y_2719_, v___y_2720_, v___y_2721_, v___y_2722_, v___y_2723_, v___y_2724_, v___y_2725_, v___y_2726_, v___y_2727_, v___y_2728_);
return v___x_2730_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___boxed(lean_object** _args){
lean_object* v___x_2731_ = _args[0];
lean_object* v_snd_2732_ = _args[1];
lean_object* v_fst_2733_ = _args[2];
lean_object* v_fst_2734_ = _args[3];
lean_object* v___x_2735_ = _args[4];
lean_object* v_range_2736_ = _args[5];
lean_object* v_b_2737_ = _args[6];
lean_object* v_i_2738_ = _args[7];
lean_object* v_hs_2739_ = _args[8];
lean_object* v_hl_2740_ = _args[9];
lean_object* v___y_2741_ = _args[10];
lean_object* v___y_2742_ = _args[11];
lean_object* v___y_2743_ = _args[12];
lean_object* v___y_2744_ = _args[13];
lean_object* v___y_2745_ = _args[14];
lean_object* v___y_2746_ = _args[15];
lean_object* v___y_2747_ = _args[16];
lean_object* v___y_2748_ = _args[17];
lean_object* v___y_2749_ = _args[18];
lean_object* v___y_2750_ = _args[19];
lean_object* v___y_2751_ = _args[20];
lean_object* v___y_2752_ = _args[21];
_start:
{
lean_object* v_res_2753_; 
v_res_2753_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1(v___x_2731_, v_snd_2732_, v_fst_2733_, v_fst_2734_, v___x_2735_, v_range_2736_, v_b_2737_, v_i_2738_, v_hs_2739_, v_hl_2740_, v___y_2741_, v___y_2742_, v___y_2743_, v___y_2744_, v___y_2745_, v___y_2746_, v___y_2747_, v___y_2748_, v___y_2749_, v___y_2750_, v___y_2751_);
lean_dec(v___y_2751_);
lean_dec_ref(v___y_2750_);
lean_dec(v___y_2749_);
lean_dec_ref(v___y_2748_);
lean_dec(v___y_2747_);
lean_dec_ref(v___y_2746_);
lean_dec(v___y_2745_);
lean_dec_ref(v___y_2744_);
lean_dec(v___y_2743_);
lean_dec(v___y_2742_);
lean_dec_ref(v___y_2741_);
lean_dec_ref(v_range_2736_);
lean_dec_ref(v___x_2735_);
return v_res_2753_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeInv(lean_object* v_e_2754_, lean_object* v_a_2755_, lean_object* v_a_2756_, lean_object* v_a_2757_, lean_object* v_a_2758_, lean_object* v_a_2759_, lean_object* v_a_2760_, lean_object* v_a_2761_, lean_object* v_a_2762_, lean_object* v_a_2763_, lean_object* v_a_2764_){
_start:
{
lean_object* v___x_2766_; 
lean_inc_ref(v_e_2754_);
v___x_2766_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_2754_, v_a_2762_);
if (lean_obj_tag(v___x_2766_) == 0)
{
lean_object* v_a_2767_; lean_object* v___x_2769_; uint8_t v_isShared_2770_; uint8_t v_isSharedCheck_2828_; 
v_a_2767_ = lean_ctor_get(v___x_2766_, 0);
v_isSharedCheck_2828_ = !lean_is_exclusive(v___x_2766_);
if (v_isSharedCheck_2828_ == 0)
{
v___x_2769_ = v___x_2766_;
v_isShared_2770_ = v_isSharedCheck_2828_;
goto v_resetjp_2768_;
}
else
{
lean_inc(v_a_2767_);
lean_dec(v___x_2766_);
v___x_2769_ = lean_box(0);
v_isShared_2770_ = v_isSharedCheck_2828_;
goto v_resetjp_2768_;
}
v_resetjp_2768_:
{
lean_object* v___x_2777_; uint8_t v___x_2778_; 
v___x_2777_ = l_Lean_Expr_cleanupAnnotations(v_a_2767_);
v___x_2778_ = l_Lean_Expr_isApp(v___x_2777_);
if (v___x_2778_ == 0)
{
lean_dec_ref(v___x_2777_);
lean_dec_ref(v_e_2754_);
goto v___jp_2771_;
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
lean_dec_ref(v_e_2754_);
goto v___jp_2771_;
}
else
{
lean_object* v_arg_2782_; lean_object* v___x_2783_; uint8_t v___x_2784_; 
v_arg_2782_ = lean_ctor_get(v___x_2780_, 1);
lean_inc_ref(v_arg_2782_);
v___x_2783_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2780_);
v___x_2784_ = l_Lean_Expr_isApp(v___x_2783_);
if (v___x_2784_ == 0)
{
lean_dec_ref(v___x_2783_);
lean_dec_ref(v_arg_2782_);
lean_dec_ref(v_arg_2779_);
lean_dec_ref(v_e_2754_);
goto v___jp_2771_;
}
else
{
lean_object* v_arg_2785_; lean_object* v___x_2786_; lean_object* v___x_2787_; uint8_t v___x_2788_; 
v_arg_2785_ = lean_ctor_get(v___x_2783_, 1);
lean_inc_ref(v_arg_2785_);
v___x_2786_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2783_);
v___x_2787_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___closed__6));
v___x_2788_ = l_Lean_Expr_isConstOf(v___x_2786_, v___x_2787_);
lean_dec_ref(v___x_2786_);
if (v___x_2788_ == 0)
{
lean_dec_ref(v_arg_2785_);
lean_dec_ref(v_arg_2782_);
lean_dec_ref(v_arg_2779_);
lean_dec_ref(v_e_2754_);
goto v___jp_2771_;
}
else
{
lean_object* v___x_2789_; 
lean_del_object(v___x_2769_);
v___x_2789_ = l_Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f(v_arg_2785_, v_a_2755_, v_a_2756_, v_a_2757_, v_a_2758_, v_a_2759_, v_a_2760_, v_a_2761_, v_a_2762_, v_a_2763_, v_a_2764_);
if (lean_obj_tag(v___x_2789_) == 0)
{
lean_object* v_a_2790_; lean_object* v___x_2792_; uint8_t v_isShared_2793_; uint8_t v_isSharedCheck_2819_; 
v_a_2790_ = lean_ctor_get(v___x_2789_, 0);
v_isSharedCheck_2819_ = !lean_is_exclusive(v___x_2789_);
if (v_isSharedCheck_2819_ == 0)
{
v___x_2792_ = v___x_2789_;
v_isShared_2793_ = v_isSharedCheck_2819_;
goto v_resetjp_2791_;
}
else
{
lean_inc(v_a_2790_);
lean_dec(v___x_2789_);
v___x_2792_ = lean_box(0);
v_isShared_2793_ = v_isSharedCheck_2819_;
goto v_resetjp_2791_;
}
v_resetjp_2791_:
{
if (lean_obj_tag(v_a_2790_) == 1)
{
lean_object* v_val_2794_; uint8_t v___x_2795_; lean_object* v___x_2796_; lean_object* v___x_2797_; 
lean_del_object(v___x_2792_);
v_val_2794_ = lean_ctor_get(v_a_2790_, 0);
lean_inc(v_val_2794_);
lean_dec_ref_known(v_a_2790_, 1);
v___x_2795_ = 0;
v___x_2796_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2796_, 0, v_val_2794_);
lean_ctor_set_uint8(v___x_2796_, sizeof(void*)*1, v___x_2795_);
v___x_2797_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv(v_e_2754_, v_arg_2782_, v_arg_2779_, v___x_2796_, v_a_2755_, v_a_2756_, v_a_2757_, v_a_2758_, v_a_2759_, v_a_2760_, v_a_2761_, v_a_2762_, v_a_2763_, v_a_2764_);
lean_dec_ref_known(v___x_2796_, 1);
lean_dec_ref(v_arg_2782_);
if (lean_obj_tag(v___x_2797_) == 0)
{
lean_object* v___x_2799_; uint8_t v_isShared_2800_; uint8_t v_isSharedCheck_2805_; 
v_isSharedCheck_2805_ = !lean_is_exclusive(v___x_2797_);
if (v_isSharedCheck_2805_ == 0)
{
lean_object* v_unused_2806_; 
v_unused_2806_ = lean_ctor_get(v___x_2797_, 0);
lean_dec(v_unused_2806_);
v___x_2799_ = v___x_2797_;
v_isShared_2800_ = v_isSharedCheck_2805_;
goto v_resetjp_2798_;
}
else
{
lean_dec(v___x_2797_);
v___x_2799_ = lean_box(0);
v_isShared_2800_ = v_isSharedCheck_2805_;
goto v_resetjp_2798_;
}
v_resetjp_2798_:
{
lean_object* v___x_2801_; lean_object* v___x_2803_; 
v___x_2801_ = lean_box(v___x_2788_);
if (v_isShared_2800_ == 0)
{
lean_ctor_set(v___x_2799_, 0, v___x_2801_);
v___x_2803_ = v___x_2799_;
goto v_reusejp_2802_;
}
else
{
lean_object* v_reuseFailAlloc_2804_; 
v_reuseFailAlloc_2804_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2804_, 0, v___x_2801_);
v___x_2803_ = v_reuseFailAlloc_2804_;
goto v_reusejp_2802_;
}
v_reusejp_2802_:
{
return v___x_2803_;
}
}
}
else
{
lean_object* v_a_2807_; lean_object* v___x_2809_; uint8_t v_isShared_2810_; uint8_t v_isSharedCheck_2814_; 
v_a_2807_ = lean_ctor_get(v___x_2797_, 0);
v_isSharedCheck_2814_ = !lean_is_exclusive(v___x_2797_);
if (v_isSharedCheck_2814_ == 0)
{
v___x_2809_ = v___x_2797_;
v_isShared_2810_ = v_isSharedCheck_2814_;
goto v_resetjp_2808_;
}
else
{
lean_inc(v_a_2807_);
lean_dec(v___x_2797_);
v___x_2809_ = lean_box(0);
v_isShared_2810_ = v_isSharedCheck_2814_;
goto v_resetjp_2808_;
}
v_resetjp_2808_:
{
lean_object* v___x_2812_; 
if (v_isShared_2810_ == 0)
{
v___x_2812_ = v___x_2809_;
goto v_reusejp_2811_;
}
else
{
lean_object* v_reuseFailAlloc_2813_; 
v_reuseFailAlloc_2813_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2813_, 0, v_a_2807_);
v___x_2812_ = v_reuseFailAlloc_2813_;
goto v_reusejp_2811_;
}
v_reusejp_2811_:
{
return v___x_2812_;
}
}
}
}
else
{
lean_object* v___x_2815_; lean_object* v___x_2817_; 
lean_dec(v_a_2790_);
lean_dec_ref(v_arg_2782_);
lean_dec_ref(v_arg_2779_);
lean_dec_ref(v_e_2754_);
v___x_2815_ = lean_box(v___x_2788_);
if (v_isShared_2793_ == 0)
{
lean_ctor_set(v___x_2792_, 0, v___x_2815_);
v___x_2817_ = v___x_2792_;
goto v_reusejp_2816_;
}
else
{
lean_object* v_reuseFailAlloc_2818_; 
v_reuseFailAlloc_2818_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2818_, 0, v___x_2815_);
v___x_2817_ = v_reuseFailAlloc_2818_;
goto v_reusejp_2816_;
}
v_reusejp_2816_:
{
return v___x_2817_;
}
}
}
}
else
{
lean_object* v_a_2820_; lean_object* v___x_2822_; uint8_t v_isShared_2823_; uint8_t v_isSharedCheck_2827_; 
lean_dec_ref(v_arg_2782_);
lean_dec_ref(v_arg_2779_);
lean_dec_ref(v_e_2754_);
v_a_2820_ = lean_ctor_get(v___x_2789_, 0);
v_isSharedCheck_2827_ = !lean_is_exclusive(v___x_2789_);
if (v_isSharedCheck_2827_ == 0)
{
v___x_2822_ = v___x_2789_;
v_isShared_2823_ = v_isSharedCheck_2827_;
goto v_resetjp_2821_;
}
else
{
lean_inc(v_a_2820_);
lean_dec(v___x_2789_);
v___x_2822_ = lean_box(0);
v_isShared_2823_ = v_isSharedCheck_2827_;
goto v_resetjp_2821_;
}
v_resetjp_2821_:
{
lean_object* v___x_2825_; 
if (v_isShared_2823_ == 0)
{
v___x_2825_ = v___x_2822_;
goto v_reusejp_2824_;
}
else
{
lean_object* v_reuseFailAlloc_2826_; 
v_reuseFailAlloc_2826_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2826_, 0, v_a_2820_);
v___x_2825_ = v_reuseFailAlloc_2826_;
goto v_reusejp_2824_;
}
v_reusejp_2824_:
{
return v___x_2825_;
}
}
}
}
}
}
}
v___jp_2771_:
{
uint8_t v___x_2772_; lean_object* v___x_2773_; lean_object* v___x_2775_; 
v___x_2772_ = 0;
v___x_2773_ = lean_box(v___x_2772_);
if (v_isShared_2770_ == 0)
{
lean_ctor_set(v___x_2769_, 0, v___x_2773_);
v___x_2775_ = v___x_2769_;
goto v_reusejp_2774_;
}
else
{
lean_object* v_reuseFailAlloc_2776_; 
v_reuseFailAlloc_2776_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2776_, 0, v___x_2773_);
v___x_2775_ = v_reuseFailAlloc_2776_;
goto v_reusejp_2774_;
}
v_reusejp_2774_:
{
return v___x_2775_;
}
}
}
}
else
{
lean_object* v_a_2829_; lean_object* v___x_2831_; uint8_t v_isShared_2832_; uint8_t v_isSharedCheck_2836_; 
lean_dec_ref(v_e_2754_);
v_a_2829_ = lean_ctor_get(v___x_2766_, 0);
v_isSharedCheck_2836_ = !lean_is_exclusive(v___x_2766_);
if (v_isSharedCheck_2836_ == 0)
{
v___x_2831_ = v___x_2766_;
v_isShared_2832_ = v_isSharedCheck_2836_;
goto v_resetjp_2830_;
}
else
{
lean_inc(v_a_2829_);
lean_dec(v___x_2766_);
v___x_2831_ = lean_box(0);
v_isShared_2832_ = v_isSharedCheck_2836_;
goto v_resetjp_2830_;
}
v_resetjp_2830_:
{
lean_object* v___x_2834_; 
if (v_isShared_2832_ == 0)
{
v___x_2834_ = v___x_2831_;
goto v_reusejp_2833_;
}
else
{
lean_object* v_reuseFailAlloc_2835_; 
v_reuseFailAlloc_2835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2835_, 0, v_a_2829_);
v___x_2834_ = v_reuseFailAlloc_2835_;
goto v_reusejp_2833_;
}
v_reusejp_2833_:
{
return v___x_2834_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeInv___boxed(lean_object* v_e_2837_, lean_object* v_a_2838_, lean_object* v_a_2839_, lean_object* v_a_2840_, lean_object* v_a_2841_, lean_object* v_a_2842_, lean_object* v_a_2843_, lean_object* v_a_2844_, lean_object* v_a_2845_, lean_object* v_a_2846_, lean_object* v_a_2847_, lean_object* v_a_2848_){
_start:
{
lean_object* v_res_2849_; 
v_res_2849_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeInv(v_e_2837_, v_a_2838_, v_a_2839_, v_a_2840_, v_a_2841_, v_a_2842_, v_a_2843_, v_a_2844_, v_a_2845_, v_a_2846_, v_a_2847_);
lean_dec(v_a_2847_);
lean_dec_ref(v_a_2846_);
lean_dec(v_a_2845_);
lean_dec_ref(v_a_2844_);
lean_dec(v_a_2843_);
lean_dec_ref(v_a_2842_);
lean_dec(v_a_2841_);
lean_dec_ref(v_a_2840_);
lean_dec(v_a_2839_);
lean_dec(v_a_2838_);
return v_res_2849_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0_spec__1_spec__5___redArg(lean_object* v_x_2850_, lean_object* v_x_2851_, lean_object* v_x_2852_, lean_object* v_x_2853_){
_start:
{
lean_object* v_ks_2854_; lean_object* v_vs_2855_; lean_object* v___x_2857_; uint8_t v_isShared_2858_; uint8_t v_isSharedCheck_2881_; 
v_ks_2854_ = lean_ctor_get(v_x_2850_, 0);
v_vs_2855_ = lean_ctor_get(v_x_2850_, 1);
v_isSharedCheck_2881_ = !lean_is_exclusive(v_x_2850_);
if (v_isSharedCheck_2881_ == 0)
{
v___x_2857_ = v_x_2850_;
v_isShared_2858_ = v_isSharedCheck_2881_;
goto v_resetjp_2856_;
}
else
{
lean_inc(v_vs_2855_);
lean_inc(v_ks_2854_);
lean_dec(v_x_2850_);
v___x_2857_ = lean_box(0);
v_isShared_2858_ = v_isSharedCheck_2881_;
goto v_resetjp_2856_;
}
v_resetjp_2856_:
{
lean_object* v___x_2859_; uint8_t v___x_2860_; 
v___x_2859_ = lean_array_get_size(v_ks_2854_);
v___x_2860_ = lean_nat_dec_lt(v_x_2851_, v___x_2859_);
if (v___x_2860_ == 0)
{
lean_object* v___x_2861_; lean_object* v___x_2862_; lean_object* v___x_2864_; 
lean_dec(v_x_2851_);
v___x_2861_ = lean_array_push(v_ks_2854_, v_x_2852_);
v___x_2862_ = lean_array_push(v_vs_2855_, v_x_2853_);
if (v_isShared_2858_ == 0)
{
lean_ctor_set(v___x_2857_, 1, v___x_2862_);
lean_ctor_set(v___x_2857_, 0, v___x_2861_);
v___x_2864_ = v___x_2857_;
goto v_reusejp_2863_;
}
else
{
lean_object* v_reuseFailAlloc_2865_; 
v_reuseFailAlloc_2865_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2865_, 0, v___x_2861_);
lean_ctor_set(v_reuseFailAlloc_2865_, 1, v___x_2862_);
v___x_2864_ = v_reuseFailAlloc_2865_;
goto v_reusejp_2863_;
}
v_reusejp_2863_:
{
return v___x_2864_;
}
}
else
{
lean_object* v_k_x27_2866_; size_t v___x_2867_; size_t v___x_2868_; uint8_t v___x_2869_; 
v_k_x27_2866_ = lean_array_fget_borrowed(v_ks_2854_, v_x_2851_);
v___x_2867_ = lean_ptr_addr(v_x_2852_);
v___x_2868_ = lean_ptr_addr(v_k_x27_2866_);
v___x_2869_ = lean_usize_dec_eq(v___x_2867_, v___x_2868_);
if (v___x_2869_ == 0)
{
lean_object* v___x_2871_; 
if (v_isShared_2858_ == 0)
{
v___x_2871_ = v___x_2857_;
goto v_reusejp_2870_;
}
else
{
lean_object* v_reuseFailAlloc_2875_; 
v_reuseFailAlloc_2875_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2875_, 0, v_ks_2854_);
lean_ctor_set(v_reuseFailAlloc_2875_, 1, v_vs_2855_);
v___x_2871_ = v_reuseFailAlloc_2875_;
goto v_reusejp_2870_;
}
v_reusejp_2870_:
{
lean_object* v___x_2872_; lean_object* v___x_2873_; 
v___x_2872_ = lean_unsigned_to_nat(1u);
v___x_2873_ = lean_nat_add(v_x_2851_, v___x_2872_);
lean_dec(v_x_2851_);
v_x_2850_ = v___x_2871_;
v_x_2851_ = v___x_2873_;
goto _start;
}
}
else
{
lean_object* v___x_2876_; lean_object* v___x_2877_; lean_object* v___x_2879_; 
v___x_2876_ = lean_array_fset(v_ks_2854_, v_x_2851_, v_x_2852_);
v___x_2877_ = lean_array_fset(v_vs_2855_, v_x_2851_, v_x_2853_);
lean_dec(v_x_2851_);
if (v_isShared_2858_ == 0)
{
lean_ctor_set(v___x_2857_, 1, v___x_2877_);
lean_ctor_set(v___x_2857_, 0, v___x_2876_);
v___x_2879_ = v___x_2857_;
goto v_reusejp_2878_;
}
else
{
lean_object* v_reuseFailAlloc_2880_; 
v_reuseFailAlloc_2880_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2880_, 0, v___x_2876_);
lean_ctor_set(v_reuseFailAlloc_2880_, 1, v___x_2877_);
v___x_2879_ = v_reuseFailAlloc_2880_;
goto v_reusejp_2878_;
}
v_reusejp_2878_:
{
return v___x_2879_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0_spec__1___redArg(lean_object* v_n_2882_, lean_object* v_k_2883_, lean_object* v_v_2884_){
_start:
{
lean_object* v___x_2885_; lean_object* v___x_2886_; 
v___x_2885_ = lean_unsigned_to_nat(0u);
v___x_2886_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0_spec__1_spec__5___redArg(v_n_2882_, v___x_2885_, v_k_2883_, v_v_2884_);
return v___x_2886_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0___redArg(lean_object* v_x_2887_, size_t v_x_2888_, size_t v_x_2889_, lean_object* v_x_2890_, lean_object* v_x_2891_){
_start:
{
if (lean_obj_tag(v_x_2887_) == 0)
{
lean_object* v_es_2892_; size_t v___x_2893_; size_t v___x_2894_; lean_object* v_j_2895_; lean_object* v___x_2896_; uint8_t v___x_2897_; 
v_es_2892_ = lean_ctor_get(v_x_2887_, 0);
v___x_2893_ = ((size_t)31ULL);
v___x_2894_ = lean_usize_land(v_x_2888_, v___x_2893_);
v_j_2895_ = lean_usize_to_nat(v___x_2894_);
v___x_2896_ = lean_array_get_size(v_es_2892_);
v___x_2897_ = lean_nat_dec_lt(v_j_2895_, v___x_2896_);
if (v___x_2897_ == 0)
{
lean_dec(v_j_2895_);
lean_dec(v_x_2891_);
lean_dec_ref(v_x_2890_);
return v_x_2887_;
}
else
{
lean_object* v___x_2899_; uint8_t v_isShared_2900_; uint8_t v_isSharedCheck_2938_; 
lean_inc_ref(v_es_2892_);
v_isSharedCheck_2938_ = !lean_is_exclusive(v_x_2887_);
if (v_isSharedCheck_2938_ == 0)
{
lean_object* v_unused_2939_; 
v_unused_2939_ = lean_ctor_get(v_x_2887_, 0);
lean_dec(v_unused_2939_);
v___x_2899_ = v_x_2887_;
v_isShared_2900_ = v_isSharedCheck_2938_;
goto v_resetjp_2898_;
}
else
{
lean_dec(v_x_2887_);
v___x_2899_ = lean_box(0);
v_isShared_2900_ = v_isSharedCheck_2938_;
goto v_resetjp_2898_;
}
v_resetjp_2898_:
{
lean_object* v_v_2901_; lean_object* v___x_2902_; lean_object* v_xs_x27_2903_; lean_object* v___y_2905_; 
v_v_2901_ = lean_array_fget(v_es_2892_, v_j_2895_);
v___x_2902_ = lean_box(0);
v_xs_x27_2903_ = lean_array_fset(v_es_2892_, v_j_2895_, v___x_2902_);
switch(lean_obj_tag(v_v_2901_))
{
case 0:
{
lean_object* v_key_2910_; lean_object* v_val_2911_; lean_object* v___x_2913_; uint8_t v_isShared_2914_; uint8_t v_isSharedCheck_2923_; 
v_key_2910_ = lean_ctor_get(v_v_2901_, 0);
v_val_2911_ = lean_ctor_get(v_v_2901_, 1);
v_isSharedCheck_2923_ = !lean_is_exclusive(v_v_2901_);
if (v_isSharedCheck_2923_ == 0)
{
v___x_2913_ = v_v_2901_;
v_isShared_2914_ = v_isSharedCheck_2923_;
goto v_resetjp_2912_;
}
else
{
lean_inc(v_val_2911_);
lean_inc(v_key_2910_);
lean_dec(v_v_2901_);
v___x_2913_ = lean_box(0);
v_isShared_2914_ = v_isSharedCheck_2923_;
goto v_resetjp_2912_;
}
v_resetjp_2912_:
{
size_t v___x_2915_; size_t v___x_2916_; uint8_t v___x_2917_; 
v___x_2915_ = lean_ptr_addr(v_x_2890_);
v___x_2916_ = lean_ptr_addr(v_key_2910_);
v___x_2917_ = lean_usize_dec_eq(v___x_2915_, v___x_2916_);
if (v___x_2917_ == 0)
{
lean_object* v___x_2918_; lean_object* v___x_2919_; 
lean_del_object(v___x_2913_);
v___x_2918_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_2910_, v_val_2911_, v_x_2890_, v_x_2891_);
v___x_2919_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2919_, 0, v___x_2918_);
v___y_2905_ = v___x_2919_;
goto v___jp_2904_;
}
else
{
lean_object* v___x_2921_; 
lean_dec(v_val_2911_);
lean_dec(v_key_2910_);
if (v_isShared_2914_ == 0)
{
lean_ctor_set(v___x_2913_, 1, v_x_2891_);
lean_ctor_set(v___x_2913_, 0, v_x_2890_);
v___x_2921_ = v___x_2913_;
goto v_reusejp_2920_;
}
else
{
lean_object* v_reuseFailAlloc_2922_; 
v_reuseFailAlloc_2922_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2922_, 0, v_x_2890_);
lean_ctor_set(v_reuseFailAlloc_2922_, 1, v_x_2891_);
v___x_2921_ = v_reuseFailAlloc_2922_;
goto v_reusejp_2920_;
}
v_reusejp_2920_:
{
v___y_2905_ = v___x_2921_;
goto v___jp_2904_;
}
}
}
}
case 1:
{
lean_object* v_node_2924_; lean_object* v___x_2926_; uint8_t v_isShared_2927_; uint8_t v_isSharedCheck_2936_; 
v_node_2924_ = lean_ctor_get(v_v_2901_, 0);
v_isSharedCheck_2936_ = !lean_is_exclusive(v_v_2901_);
if (v_isSharedCheck_2936_ == 0)
{
v___x_2926_ = v_v_2901_;
v_isShared_2927_ = v_isSharedCheck_2936_;
goto v_resetjp_2925_;
}
else
{
lean_inc(v_node_2924_);
lean_dec(v_v_2901_);
v___x_2926_ = lean_box(0);
v_isShared_2927_ = v_isSharedCheck_2936_;
goto v_resetjp_2925_;
}
v_resetjp_2925_:
{
size_t v___x_2928_; size_t v___x_2929_; size_t v___x_2930_; size_t v___x_2931_; lean_object* v___x_2932_; lean_object* v___x_2934_; 
v___x_2928_ = ((size_t)5ULL);
v___x_2929_ = lean_usize_shift_right(v_x_2888_, v___x_2928_);
v___x_2930_ = ((size_t)1ULL);
v___x_2931_ = lean_usize_add(v_x_2889_, v___x_2930_);
v___x_2932_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0___redArg(v_node_2924_, v___x_2929_, v___x_2931_, v_x_2890_, v_x_2891_);
if (v_isShared_2927_ == 0)
{
lean_ctor_set(v___x_2926_, 0, v___x_2932_);
v___x_2934_ = v___x_2926_;
goto v_reusejp_2933_;
}
else
{
lean_object* v_reuseFailAlloc_2935_; 
v_reuseFailAlloc_2935_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2935_, 0, v___x_2932_);
v___x_2934_ = v_reuseFailAlloc_2935_;
goto v_reusejp_2933_;
}
v_reusejp_2933_:
{
v___y_2905_ = v___x_2934_;
goto v___jp_2904_;
}
}
}
default: 
{
lean_object* v___x_2937_; 
v___x_2937_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2937_, 0, v_x_2890_);
lean_ctor_set(v___x_2937_, 1, v_x_2891_);
v___y_2905_ = v___x_2937_;
goto v___jp_2904_;
}
}
v___jp_2904_:
{
lean_object* v___x_2906_; lean_object* v___x_2908_; 
v___x_2906_ = lean_array_fset(v_xs_x27_2903_, v_j_2895_, v___y_2905_);
lean_dec(v_j_2895_);
if (v_isShared_2900_ == 0)
{
lean_ctor_set(v___x_2899_, 0, v___x_2906_);
v___x_2908_ = v___x_2899_;
goto v_reusejp_2907_;
}
else
{
lean_object* v_reuseFailAlloc_2909_; 
v_reuseFailAlloc_2909_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2909_, 0, v___x_2906_);
v___x_2908_ = v_reuseFailAlloc_2909_;
goto v_reusejp_2907_;
}
v_reusejp_2907_:
{
return v___x_2908_;
}
}
}
}
}
else
{
lean_object* v_ks_2940_; lean_object* v_vs_2941_; lean_object* v___x_2943_; uint8_t v_isShared_2944_; uint8_t v_isSharedCheck_2959_; 
v_ks_2940_ = lean_ctor_get(v_x_2887_, 0);
v_vs_2941_ = lean_ctor_get(v_x_2887_, 1);
v_isSharedCheck_2959_ = !lean_is_exclusive(v_x_2887_);
if (v_isSharedCheck_2959_ == 0)
{
v___x_2943_ = v_x_2887_;
v_isShared_2944_ = v_isSharedCheck_2959_;
goto v_resetjp_2942_;
}
else
{
lean_inc(v_vs_2941_);
lean_inc(v_ks_2940_);
lean_dec(v_x_2887_);
v___x_2943_ = lean_box(0);
v_isShared_2944_ = v_isSharedCheck_2959_;
goto v_resetjp_2942_;
}
v_resetjp_2942_:
{
lean_object* v___x_2946_; 
if (v_isShared_2944_ == 0)
{
v___x_2946_ = v___x_2943_;
goto v_reusejp_2945_;
}
else
{
lean_object* v_reuseFailAlloc_2958_; 
v_reuseFailAlloc_2958_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2958_, 0, v_ks_2940_);
lean_ctor_set(v_reuseFailAlloc_2958_, 1, v_vs_2941_);
v___x_2946_ = v_reuseFailAlloc_2958_;
goto v_reusejp_2945_;
}
v_reusejp_2945_:
{
lean_object* v_newNode_2947_; size_t v___x_2948_; uint8_t v___x_2949_; 
v_newNode_2947_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0_spec__1___redArg(v___x_2946_, v_x_2890_, v_x_2891_);
v___x_2948_ = ((size_t)7ULL);
v___x_2949_ = lean_usize_dec_le(v___x_2948_, v_x_2889_);
if (v___x_2949_ == 0)
{
lean_object* v___x_2950_; lean_object* v___x_2951_; uint8_t v___x_2952_; 
v___x_2950_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2947_);
v___x_2951_ = lean_unsigned_to_nat(4u);
v___x_2952_ = lean_nat_dec_lt(v___x_2950_, v___x_2951_);
lean_dec(v___x_2950_);
if (v___x_2952_ == 0)
{
lean_object* v_ks_2953_; lean_object* v_vs_2954_; lean_object* v___x_2955_; lean_object* v___x_2956_; lean_object* v___x_2957_; 
v_ks_2953_ = lean_ctor_get(v_newNode_2947_, 0);
lean_inc_ref(v_ks_2953_);
v_vs_2954_ = lean_ctor_get(v_newNode_2947_, 1);
lean_inc_ref(v_vs_2954_);
lean_dec_ref(v_newNode_2947_);
v___x_2955_ = lean_unsigned_to_nat(0u);
v___x_2956_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg___closed__0);
v___x_2957_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0_spec__2___redArg(v_x_2889_, v_ks_2953_, v_vs_2954_, v___x_2955_, v___x_2956_);
lean_dec_ref(v_vs_2954_);
lean_dec_ref(v_ks_2953_);
return v___x_2957_;
}
else
{
return v_newNode_2947_;
}
}
else
{
return v_newNode_2947_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0_spec__2___redArg(size_t v_depth_2960_, lean_object* v_keys_2961_, lean_object* v_vals_2962_, lean_object* v_i_2963_, lean_object* v_entries_2964_){
_start:
{
lean_object* v___x_2965_; uint8_t v___x_2966_; 
v___x_2965_ = lean_array_get_size(v_keys_2961_);
v___x_2966_ = lean_nat_dec_lt(v_i_2963_, v___x_2965_);
if (v___x_2966_ == 0)
{
lean_dec(v_i_2963_);
return v_entries_2964_;
}
else
{
lean_object* v_k_2967_; lean_object* v_v_2968_; size_t v___x_2969_; size_t v___x_2970_; size_t v___x_2971_; uint64_t v___x_2972_; size_t v_h_2973_; size_t v___x_2974_; lean_object* v___x_2975_; size_t v___x_2976_; size_t v___x_2977_; size_t v___x_2978_; size_t v_h_2979_; lean_object* v___x_2980_; lean_object* v___x_2981_; 
v_k_2967_ = lean_array_fget_borrowed(v_keys_2961_, v_i_2963_);
v_v_2968_ = lean_array_fget_borrowed(v_vals_2962_, v_i_2963_);
v___x_2969_ = lean_ptr_addr(v_k_2967_);
v___x_2970_ = ((size_t)3ULL);
v___x_2971_ = lean_usize_shift_right(v___x_2969_, v___x_2970_);
v___x_2972_ = lean_usize_to_uint64(v___x_2971_);
v_h_2973_ = lean_uint64_to_usize(v___x_2972_);
v___x_2974_ = ((size_t)5ULL);
v___x_2975_ = lean_unsigned_to_nat(1u);
v___x_2976_ = ((size_t)1ULL);
v___x_2977_ = lean_usize_sub(v_depth_2960_, v___x_2976_);
v___x_2978_ = lean_usize_mul(v___x_2974_, v___x_2977_);
v_h_2979_ = lean_usize_shift_right(v_h_2973_, v___x_2978_);
v___x_2980_ = lean_nat_add(v_i_2963_, v___x_2975_);
lean_dec(v_i_2963_);
lean_inc(v_v_2968_);
lean_inc(v_k_2967_);
v___x_2981_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0___redArg(v_entries_2964_, v_h_2979_, v_depth_2960_, v_k_2967_, v_v_2968_);
v_i_2963_ = v___x_2980_;
v_entries_2964_ = v___x_2981_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_2983_, lean_object* v_keys_2984_, lean_object* v_vals_2985_, lean_object* v_i_2986_, lean_object* v_entries_2987_){
_start:
{
size_t v_depth_boxed_2988_; lean_object* v_res_2989_; 
v_depth_boxed_2988_ = lean_unbox_usize(v_depth_2983_);
lean_dec(v_depth_2983_);
v_res_2989_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0_spec__2___redArg(v_depth_boxed_2988_, v_keys_2984_, v_vals_2985_, v_i_2986_, v_entries_2987_);
lean_dec_ref(v_vals_2985_);
lean_dec_ref(v_keys_2984_);
return v_res_2989_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0___redArg___boxed(lean_object* v_x_2990_, lean_object* v_x_2991_, lean_object* v_x_2992_, lean_object* v_x_2993_, lean_object* v_x_2994_){
_start:
{
size_t v_x_151173__boxed_2995_; size_t v_x_151174__boxed_2996_; lean_object* v_res_2997_; 
v_x_151173__boxed_2995_ = lean_unbox_usize(v_x_2991_);
lean_dec(v_x_2991_);
v_x_151174__boxed_2996_ = lean_unbox_usize(v_x_2992_);
lean_dec(v_x_2992_);
v_res_2997_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0___redArg(v_x_2990_, v_x_151173__boxed_2995_, v_x_151174__boxed_2996_, v_x_2993_, v_x_2994_);
return v_res_2997_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0___redArg(lean_object* v_x_2998_, lean_object* v_x_2999_, lean_object* v_x_3000_){
_start:
{
size_t v___x_3001_; size_t v___x_3002_; size_t v___x_3003_; uint64_t v___x_3004_; size_t v___x_3005_; size_t v___x_3006_; lean_object* v___x_3007_; 
v___x_3001_ = lean_ptr_addr(v_x_2999_);
v___x_3002_ = ((size_t)3ULL);
v___x_3003_ = lean_usize_shift_right(v___x_3001_, v___x_3002_);
v___x_3004_ = lean_usize_to_uint64(v___x_3003_);
v___x_3005_ = lean_uint64_to_usize(v___x_3004_);
v___x_3006_ = ((size_t)1ULL);
v___x_3007_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0___redArg(v_x_2998_, v___x_3005_, v___x_3006_, v_x_2999_, v_x_3000_);
return v___x_3007_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_internalize___lam__0(lean_object* v_e_3008_, lean_object* v_val_3009_, lean_object* v_s_3010_){
_start:
{
lean_object* v_toRing_3011_; lean_object* v_invFn_x3f_3012_; lean_object* v_semiringId_x3f_3013_; lean_object* v_commSemiringInst_3014_; lean_object* v_commRingInst_3015_; lean_object* v_noZeroDivInst_x3f_3016_; lean_object* v_fieldInst_x3f_3017_; lean_object* v_powIdentityInst_x3f_3018_; lean_object* v_denoteEntries_3019_; lean_object* v_nextId_3020_; lean_object* v_steps_3021_; lean_object* v_queue_3022_; lean_object* v_basis_3023_; lean_object* v_diseqs_3024_; uint8_t v_recheck_3025_; lean_object* v_invSet_3026_; lean_object* v_powIdentityVarCount_3027_; lean_object* v_numEq0_x3f_3028_; uint8_t v_numEq0Updated_3029_; lean_object* v___x_3031_; uint8_t v_isShared_3032_; uint8_t v_isSharedCheck_3063_; 
v_toRing_3011_ = lean_ctor_get(v_s_3010_, 0);
v_invFn_x3f_3012_ = lean_ctor_get(v_s_3010_, 1);
v_semiringId_x3f_3013_ = lean_ctor_get(v_s_3010_, 2);
v_commSemiringInst_3014_ = lean_ctor_get(v_s_3010_, 3);
v_commRingInst_3015_ = lean_ctor_get(v_s_3010_, 4);
v_noZeroDivInst_x3f_3016_ = lean_ctor_get(v_s_3010_, 5);
v_fieldInst_x3f_3017_ = lean_ctor_get(v_s_3010_, 6);
v_powIdentityInst_x3f_3018_ = lean_ctor_get(v_s_3010_, 7);
v_denoteEntries_3019_ = lean_ctor_get(v_s_3010_, 8);
v_nextId_3020_ = lean_ctor_get(v_s_3010_, 9);
v_steps_3021_ = lean_ctor_get(v_s_3010_, 10);
v_queue_3022_ = lean_ctor_get(v_s_3010_, 11);
v_basis_3023_ = lean_ctor_get(v_s_3010_, 12);
v_diseqs_3024_ = lean_ctor_get(v_s_3010_, 13);
v_recheck_3025_ = lean_ctor_get_uint8(v_s_3010_, sizeof(void*)*17);
v_invSet_3026_ = lean_ctor_get(v_s_3010_, 14);
v_powIdentityVarCount_3027_ = lean_ctor_get(v_s_3010_, 15);
v_numEq0_x3f_3028_ = lean_ctor_get(v_s_3010_, 16);
v_numEq0Updated_3029_ = lean_ctor_get_uint8(v_s_3010_, sizeof(void*)*17 + 1);
v_isSharedCheck_3063_ = !lean_is_exclusive(v_s_3010_);
if (v_isSharedCheck_3063_ == 0)
{
v___x_3031_ = v_s_3010_;
v_isShared_3032_ = v_isSharedCheck_3063_;
goto v_resetjp_3030_;
}
else
{
lean_inc(v_numEq0_x3f_3028_);
lean_inc(v_powIdentityVarCount_3027_);
lean_inc(v_invSet_3026_);
lean_inc(v_diseqs_3024_);
lean_inc(v_basis_3023_);
lean_inc(v_queue_3022_);
lean_inc(v_steps_3021_);
lean_inc(v_nextId_3020_);
lean_inc(v_denoteEntries_3019_);
lean_inc(v_powIdentityInst_x3f_3018_);
lean_inc(v_fieldInst_x3f_3017_);
lean_inc(v_noZeroDivInst_x3f_3016_);
lean_inc(v_commRingInst_3015_);
lean_inc(v_commSemiringInst_3014_);
lean_inc(v_semiringId_x3f_3013_);
lean_inc(v_invFn_x3f_3012_);
lean_inc(v_toRing_3011_);
lean_dec(v_s_3010_);
v___x_3031_ = lean_box(0);
v_isShared_3032_ = v_isSharedCheck_3063_;
goto v_resetjp_3030_;
}
v_resetjp_3030_:
{
lean_object* v_id_3033_; lean_object* v_type_3034_; lean_object* v_u_3035_; lean_object* v_ringInst_3036_; lean_object* v_semiringInst_3037_; lean_object* v_charInst_x3f_3038_; lean_object* v_addFn_x3f_3039_; lean_object* v_mulFn_x3f_3040_; lean_object* v_subFn_x3f_3041_; lean_object* v_negFn_x3f_3042_; lean_object* v_powFn_x3f_3043_; lean_object* v_intCastFn_x3f_3044_; lean_object* v_natCastFn_x3f_3045_; lean_object* v_one_x3f_3046_; lean_object* v_vars_3047_; lean_object* v_varMap_3048_; lean_object* v_denote_3049_; lean_object* v___x_3051_; uint8_t v_isShared_3052_; uint8_t v_isSharedCheck_3062_; 
v_id_3033_ = lean_ctor_get(v_toRing_3011_, 0);
v_type_3034_ = lean_ctor_get(v_toRing_3011_, 1);
v_u_3035_ = lean_ctor_get(v_toRing_3011_, 2);
v_ringInst_3036_ = lean_ctor_get(v_toRing_3011_, 3);
v_semiringInst_3037_ = lean_ctor_get(v_toRing_3011_, 4);
v_charInst_x3f_3038_ = lean_ctor_get(v_toRing_3011_, 5);
v_addFn_x3f_3039_ = lean_ctor_get(v_toRing_3011_, 6);
v_mulFn_x3f_3040_ = lean_ctor_get(v_toRing_3011_, 7);
v_subFn_x3f_3041_ = lean_ctor_get(v_toRing_3011_, 8);
v_negFn_x3f_3042_ = lean_ctor_get(v_toRing_3011_, 9);
v_powFn_x3f_3043_ = lean_ctor_get(v_toRing_3011_, 10);
v_intCastFn_x3f_3044_ = lean_ctor_get(v_toRing_3011_, 11);
v_natCastFn_x3f_3045_ = lean_ctor_get(v_toRing_3011_, 12);
v_one_x3f_3046_ = lean_ctor_get(v_toRing_3011_, 13);
v_vars_3047_ = lean_ctor_get(v_toRing_3011_, 14);
v_varMap_3048_ = lean_ctor_get(v_toRing_3011_, 15);
v_denote_3049_ = lean_ctor_get(v_toRing_3011_, 16);
v_isSharedCheck_3062_ = !lean_is_exclusive(v_toRing_3011_);
if (v_isSharedCheck_3062_ == 0)
{
v___x_3051_ = v_toRing_3011_;
v_isShared_3052_ = v_isSharedCheck_3062_;
goto v_resetjp_3050_;
}
else
{
lean_inc(v_denote_3049_);
lean_inc(v_varMap_3048_);
lean_inc(v_vars_3047_);
lean_inc(v_one_x3f_3046_);
lean_inc(v_natCastFn_x3f_3045_);
lean_inc(v_intCastFn_x3f_3044_);
lean_inc(v_powFn_x3f_3043_);
lean_inc(v_negFn_x3f_3042_);
lean_inc(v_subFn_x3f_3041_);
lean_inc(v_mulFn_x3f_3040_);
lean_inc(v_addFn_x3f_3039_);
lean_inc(v_charInst_x3f_3038_);
lean_inc(v_semiringInst_3037_);
lean_inc(v_ringInst_3036_);
lean_inc(v_u_3035_);
lean_inc(v_type_3034_);
lean_inc(v_id_3033_);
lean_dec(v_toRing_3011_);
v___x_3051_ = lean_box(0);
v_isShared_3052_ = v_isSharedCheck_3062_;
goto v_resetjp_3050_;
}
v_resetjp_3050_:
{
lean_object* v___x_3053_; lean_object* v___x_3055_; 
lean_inc_ref(v_val_3009_);
lean_inc_ref(v_e_3008_);
v___x_3053_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0___redArg(v_denote_3049_, v_e_3008_, v_val_3009_);
if (v_isShared_3052_ == 0)
{
lean_ctor_set(v___x_3051_, 16, v___x_3053_);
v___x_3055_ = v___x_3051_;
goto v_reusejp_3054_;
}
else
{
lean_object* v_reuseFailAlloc_3061_; 
v_reuseFailAlloc_3061_ = lean_alloc_ctor(0, 17, 0);
lean_ctor_set(v_reuseFailAlloc_3061_, 0, v_id_3033_);
lean_ctor_set(v_reuseFailAlloc_3061_, 1, v_type_3034_);
lean_ctor_set(v_reuseFailAlloc_3061_, 2, v_u_3035_);
lean_ctor_set(v_reuseFailAlloc_3061_, 3, v_ringInst_3036_);
lean_ctor_set(v_reuseFailAlloc_3061_, 4, v_semiringInst_3037_);
lean_ctor_set(v_reuseFailAlloc_3061_, 5, v_charInst_x3f_3038_);
lean_ctor_set(v_reuseFailAlloc_3061_, 6, v_addFn_x3f_3039_);
lean_ctor_set(v_reuseFailAlloc_3061_, 7, v_mulFn_x3f_3040_);
lean_ctor_set(v_reuseFailAlloc_3061_, 8, v_subFn_x3f_3041_);
lean_ctor_set(v_reuseFailAlloc_3061_, 9, v_negFn_x3f_3042_);
lean_ctor_set(v_reuseFailAlloc_3061_, 10, v_powFn_x3f_3043_);
lean_ctor_set(v_reuseFailAlloc_3061_, 11, v_intCastFn_x3f_3044_);
lean_ctor_set(v_reuseFailAlloc_3061_, 12, v_natCastFn_x3f_3045_);
lean_ctor_set(v_reuseFailAlloc_3061_, 13, v_one_x3f_3046_);
lean_ctor_set(v_reuseFailAlloc_3061_, 14, v_vars_3047_);
lean_ctor_set(v_reuseFailAlloc_3061_, 15, v_varMap_3048_);
lean_ctor_set(v_reuseFailAlloc_3061_, 16, v___x_3053_);
v___x_3055_ = v_reuseFailAlloc_3061_;
goto v_reusejp_3054_;
}
v_reusejp_3054_:
{
lean_object* v___x_3056_; lean_object* v___x_3057_; lean_object* v___x_3059_; 
v___x_3056_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3056_, 0, v_e_3008_);
lean_ctor_set(v___x_3056_, 1, v_val_3009_);
v___x_3057_ = l_Lean_PersistentArray_push___redArg(v_denoteEntries_3019_, v___x_3056_);
if (v_isShared_3032_ == 0)
{
lean_ctor_set(v___x_3031_, 8, v___x_3057_);
lean_ctor_set(v___x_3031_, 0, v___x_3055_);
v___x_3059_ = v___x_3031_;
goto v_reusejp_3058_;
}
else
{
lean_object* v_reuseFailAlloc_3060_; 
v_reuseFailAlloc_3060_ = lean_alloc_ctor(0, 17, 2);
lean_ctor_set(v_reuseFailAlloc_3060_, 0, v___x_3055_);
lean_ctor_set(v_reuseFailAlloc_3060_, 1, v_invFn_x3f_3012_);
lean_ctor_set(v_reuseFailAlloc_3060_, 2, v_semiringId_x3f_3013_);
lean_ctor_set(v_reuseFailAlloc_3060_, 3, v_commSemiringInst_3014_);
lean_ctor_set(v_reuseFailAlloc_3060_, 4, v_commRingInst_3015_);
lean_ctor_set(v_reuseFailAlloc_3060_, 5, v_noZeroDivInst_x3f_3016_);
lean_ctor_set(v_reuseFailAlloc_3060_, 6, v_fieldInst_x3f_3017_);
lean_ctor_set(v_reuseFailAlloc_3060_, 7, v_powIdentityInst_x3f_3018_);
lean_ctor_set(v_reuseFailAlloc_3060_, 8, v___x_3057_);
lean_ctor_set(v_reuseFailAlloc_3060_, 9, v_nextId_3020_);
lean_ctor_set(v_reuseFailAlloc_3060_, 10, v_steps_3021_);
lean_ctor_set(v_reuseFailAlloc_3060_, 11, v_queue_3022_);
lean_ctor_set(v_reuseFailAlloc_3060_, 12, v_basis_3023_);
lean_ctor_set(v_reuseFailAlloc_3060_, 13, v_diseqs_3024_);
lean_ctor_set(v_reuseFailAlloc_3060_, 14, v_invSet_3026_);
lean_ctor_set(v_reuseFailAlloc_3060_, 15, v_powIdentityVarCount_3027_);
lean_ctor_set(v_reuseFailAlloc_3060_, 16, v_numEq0_x3f_3028_);
lean_ctor_set_uint8(v_reuseFailAlloc_3060_, sizeof(void*)*17, v_recheck_3025_);
lean_ctor_set_uint8(v_reuseFailAlloc_3060_, sizeof(void*)*17 + 1, v_numEq0Updated_3029_);
v___x_3059_ = v_reuseFailAlloc_3060_;
goto v_reusejp_3058_;
}
v_reusejp_3058_:
{
return v___x_3059_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_internalize___lam__1(lean_object* v___y_3064_, lean_object* v_e_3065_, lean_object* v_val_3066_, lean_object* v_s_3067_){
_start:
{
lean_object* v_rings_3068_; lean_object* v_typeIdOf_3069_; lean_object* v_exprToRingId_3070_; lean_object* v_semirings_3071_; lean_object* v_stypeIdOf_3072_; lean_object* v_exprToSemiringId_3073_; lean_object* v_ncRings_3074_; lean_object* v_exprToNCRingId_3075_; lean_object* v_nctypeIdOf_3076_; lean_object* v_ncSemirings_3077_; lean_object* v_exprToNCSemiringId_3078_; lean_object* v_ncstypeIdOf_3079_; lean_object* v_steps_3080_; uint8_t v_reportedMaxDegreeIssue_3081_; lean_object* v___x_3082_; uint8_t v___x_3083_; 
v_rings_3068_ = lean_ctor_get(v_s_3067_, 0);
v_typeIdOf_3069_ = lean_ctor_get(v_s_3067_, 1);
v_exprToRingId_3070_ = lean_ctor_get(v_s_3067_, 2);
v_semirings_3071_ = lean_ctor_get(v_s_3067_, 3);
v_stypeIdOf_3072_ = lean_ctor_get(v_s_3067_, 4);
v_exprToSemiringId_3073_ = lean_ctor_get(v_s_3067_, 5);
v_ncRings_3074_ = lean_ctor_get(v_s_3067_, 6);
v_exprToNCRingId_3075_ = lean_ctor_get(v_s_3067_, 7);
v_nctypeIdOf_3076_ = lean_ctor_get(v_s_3067_, 8);
v_ncSemirings_3077_ = lean_ctor_get(v_s_3067_, 9);
v_exprToNCSemiringId_3078_ = lean_ctor_get(v_s_3067_, 10);
v_ncstypeIdOf_3079_ = lean_ctor_get(v_s_3067_, 11);
v_steps_3080_ = lean_ctor_get(v_s_3067_, 12);
v_reportedMaxDegreeIssue_3081_ = lean_ctor_get_uint8(v_s_3067_, sizeof(void*)*13);
v___x_3082_ = lean_array_get_size(v_semirings_3071_);
v___x_3083_ = lean_nat_dec_lt(v___y_3064_, v___x_3082_);
if (v___x_3083_ == 0)
{
lean_dec_ref(v_val_3066_);
lean_dec_ref(v_e_3065_);
return v_s_3067_;
}
else
{
lean_object* v___x_3085_; uint8_t v_isShared_3086_; uint8_t v_isSharedCheck_3125_; 
lean_inc(v_steps_3080_);
lean_inc_ref(v_ncstypeIdOf_3079_);
lean_inc_ref(v_exprToNCSemiringId_3078_);
lean_inc_ref(v_ncSemirings_3077_);
lean_inc_ref(v_nctypeIdOf_3076_);
lean_inc_ref(v_exprToNCRingId_3075_);
lean_inc_ref(v_ncRings_3074_);
lean_inc_ref(v_exprToSemiringId_3073_);
lean_inc_ref(v_stypeIdOf_3072_);
lean_inc_ref(v_semirings_3071_);
lean_inc_ref(v_exprToRingId_3070_);
lean_inc_ref(v_typeIdOf_3069_);
lean_inc_ref(v_rings_3068_);
v_isSharedCheck_3125_ = !lean_is_exclusive(v_s_3067_);
if (v_isSharedCheck_3125_ == 0)
{
lean_object* v_unused_3126_; lean_object* v_unused_3127_; lean_object* v_unused_3128_; lean_object* v_unused_3129_; lean_object* v_unused_3130_; lean_object* v_unused_3131_; lean_object* v_unused_3132_; lean_object* v_unused_3133_; lean_object* v_unused_3134_; lean_object* v_unused_3135_; lean_object* v_unused_3136_; lean_object* v_unused_3137_; lean_object* v_unused_3138_; 
v_unused_3126_ = lean_ctor_get(v_s_3067_, 12);
lean_dec(v_unused_3126_);
v_unused_3127_ = lean_ctor_get(v_s_3067_, 11);
lean_dec(v_unused_3127_);
v_unused_3128_ = lean_ctor_get(v_s_3067_, 10);
lean_dec(v_unused_3128_);
v_unused_3129_ = lean_ctor_get(v_s_3067_, 9);
lean_dec(v_unused_3129_);
v_unused_3130_ = lean_ctor_get(v_s_3067_, 8);
lean_dec(v_unused_3130_);
v_unused_3131_ = lean_ctor_get(v_s_3067_, 7);
lean_dec(v_unused_3131_);
v_unused_3132_ = lean_ctor_get(v_s_3067_, 6);
lean_dec(v_unused_3132_);
v_unused_3133_ = lean_ctor_get(v_s_3067_, 5);
lean_dec(v_unused_3133_);
v_unused_3134_ = lean_ctor_get(v_s_3067_, 4);
lean_dec(v_unused_3134_);
v_unused_3135_ = lean_ctor_get(v_s_3067_, 3);
lean_dec(v_unused_3135_);
v_unused_3136_ = lean_ctor_get(v_s_3067_, 2);
lean_dec(v_unused_3136_);
v_unused_3137_ = lean_ctor_get(v_s_3067_, 1);
lean_dec(v_unused_3137_);
v_unused_3138_ = lean_ctor_get(v_s_3067_, 0);
lean_dec(v_unused_3138_);
v___x_3085_ = v_s_3067_;
v_isShared_3086_ = v_isSharedCheck_3125_;
goto v_resetjp_3084_;
}
else
{
lean_dec(v_s_3067_);
v___x_3085_ = lean_box(0);
v_isShared_3086_ = v_isSharedCheck_3125_;
goto v_resetjp_3084_;
}
v_resetjp_3084_:
{
lean_object* v_v_3087_; lean_object* v_toSemiring_3088_; lean_object* v_ringId_3089_; lean_object* v_commSemiringInst_3090_; lean_object* v_addRightCancelInst_x3f_3091_; lean_object* v_toQFn_x3f_3092_; lean_object* v___x_3094_; uint8_t v_isShared_3095_; uint8_t v_isSharedCheck_3124_; 
v_v_3087_ = lean_array_fget(v_semirings_3071_, v___y_3064_);
v_toSemiring_3088_ = lean_ctor_get(v_v_3087_, 0);
v_ringId_3089_ = lean_ctor_get(v_v_3087_, 1);
v_commSemiringInst_3090_ = lean_ctor_get(v_v_3087_, 2);
v_addRightCancelInst_x3f_3091_ = lean_ctor_get(v_v_3087_, 3);
v_toQFn_x3f_3092_ = lean_ctor_get(v_v_3087_, 4);
v_isSharedCheck_3124_ = !lean_is_exclusive(v_v_3087_);
if (v_isSharedCheck_3124_ == 0)
{
v___x_3094_ = v_v_3087_;
v_isShared_3095_ = v_isSharedCheck_3124_;
goto v_resetjp_3093_;
}
else
{
lean_inc(v_toQFn_x3f_3092_);
lean_inc(v_addRightCancelInst_x3f_3091_);
lean_inc(v_commSemiringInst_3090_);
lean_inc(v_ringId_3089_);
lean_inc(v_toSemiring_3088_);
lean_dec(v_v_3087_);
v___x_3094_ = lean_box(0);
v_isShared_3095_ = v_isSharedCheck_3124_;
goto v_resetjp_3093_;
}
v_resetjp_3093_:
{
lean_object* v_id_3096_; lean_object* v_type_3097_; lean_object* v_u_3098_; lean_object* v_semiringInst_3099_; lean_object* v_addFn_x3f_3100_; lean_object* v_mulFn_x3f_3101_; lean_object* v_powFn_x3f_3102_; lean_object* v_natCastFn_x3f_3103_; lean_object* v_denote_3104_; lean_object* v_vars_3105_; lean_object* v_varMap_3106_; lean_object* v___x_3108_; uint8_t v_isShared_3109_; uint8_t v_isSharedCheck_3123_; 
v_id_3096_ = lean_ctor_get(v_toSemiring_3088_, 0);
v_type_3097_ = lean_ctor_get(v_toSemiring_3088_, 1);
v_u_3098_ = lean_ctor_get(v_toSemiring_3088_, 2);
v_semiringInst_3099_ = lean_ctor_get(v_toSemiring_3088_, 3);
v_addFn_x3f_3100_ = lean_ctor_get(v_toSemiring_3088_, 4);
v_mulFn_x3f_3101_ = lean_ctor_get(v_toSemiring_3088_, 5);
v_powFn_x3f_3102_ = lean_ctor_get(v_toSemiring_3088_, 6);
v_natCastFn_x3f_3103_ = lean_ctor_get(v_toSemiring_3088_, 7);
v_denote_3104_ = lean_ctor_get(v_toSemiring_3088_, 8);
v_vars_3105_ = lean_ctor_get(v_toSemiring_3088_, 9);
v_varMap_3106_ = lean_ctor_get(v_toSemiring_3088_, 10);
v_isSharedCheck_3123_ = !lean_is_exclusive(v_toSemiring_3088_);
if (v_isSharedCheck_3123_ == 0)
{
v___x_3108_ = v_toSemiring_3088_;
v_isShared_3109_ = v_isSharedCheck_3123_;
goto v_resetjp_3107_;
}
else
{
lean_inc(v_varMap_3106_);
lean_inc(v_vars_3105_);
lean_inc(v_denote_3104_);
lean_inc(v_natCastFn_x3f_3103_);
lean_inc(v_powFn_x3f_3102_);
lean_inc(v_mulFn_x3f_3101_);
lean_inc(v_addFn_x3f_3100_);
lean_inc(v_semiringInst_3099_);
lean_inc(v_u_3098_);
lean_inc(v_type_3097_);
lean_inc(v_id_3096_);
lean_dec(v_toSemiring_3088_);
v___x_3108_ = lean_box(0);
v_isShared_3109_ = v_isSharedCheck_3123_;
goto v_resetjp_3107_;
}
v_resetjp_3107_:
{
lean_object* v___x_3110_; lean_object* v_xs_x27_3111_; lean_object* v___x_3112_; lean_object* v___x_3114_; 
v___x_3110_ = lean_box(0);
v_xs_x27_3111_ = lean_array_fset(v_semirings_3071_, v___y_3064_, v___x_3110_);
v___x_3112_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0___redArg(v_denote_3104_, v_e_3065_, v_val_3066_);
if (v_isShared_3109_ == 0)
{
lean_ctor_set(v___x_3108_, 8, v___x_3112_);
v___x_3114_ = v___x_3108_;
goto v_reusejp_3113_;
}
else
{
lean_object* v_reuseFailAlloc_3122_; 
v_reuseFailAlloc_3122_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_3122_, 0, v_id_3096_);
lean_ctor_set(v_reuseFailAlloc_3122_, 1, v_type_3097_);
lean_ctor_set(v_reuseFailAlloc_3122_, 2, v_u_3098_);
lean_ctor_set(v_reuseFailAlloc_3122_, 3, v_semiringInst_3099_);
lean_ctor_set(v_reuseFailAlloc_3122_, 4, v_addFn_x3f_3100_);
lean_ctor_set(v_reuseFailAlloc_3122_, 5, v_mulFn_x3f_3101_);
lean_ctor_set(v_reuseFailAlloc_3122_, 6, v_powFn_x3f_3102_);
lean_ctor_set(v_reuseFailAlloc_3122_, 7, v_natCastFn_x3f_3103_);
lean_ctor_set(v_reuseFailAlloc_3122_, 8, v___x_3112_);
lean_ctor_set(v_reuseFailAlloc_3122_, 9, v_vars_3105_);
lean_ctor_set(v_reuseFailAlloc_3122_, 10, v_varMap_3106_);
v___x_3114_ = v_reuseFailAlloc_3122_;
goto v_reusejp_3113_;
}
v_reusejp_3113_:
{
lean_object* v___x_3116_; 
if (v_isShared_3095_ == 0)
{
lean_ctor_set(v___x_3094_, 0, v___x_3114_);
v___x_3116_ = v___x_3094_;
goto v_reusejp_3115_;
}
else
{
lean_object* v_reuseFailAlloc_3121_; 
v_reuseFailAlloc_3121_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3121_, 0, v___x_3114_);
lean_ctor_set(v_reuseFailAlloc_3121_, 1, v_ringId_3089_);
lean_ctor_set(v_reuseFailAlloc_3121_, 2, v_commSemiringInst_3090_);
lean_ctor_set(v_reuseFailAlloc_3121_, 3, v_addRightCancelInst_x3f_3091_);
lean_ctor_set(v_reuseFailAlloc_3121_, 4, v_toQFn_x3f_3092_);
v___x_3116_ = v_reuseFailAlloc_3121_;
goto v_reusejp_3115_;
}
v_reusejp_3115_:
{
lean_object* v___x_3117_; lean_object* v___x_3119_; 
v___x_3117_ = lean_array_fset(v_xs_x27_3111_, v___y_3064_, v___x_3116_);
if (v_isShared_3086_ == 0)
{
lean_ctor_set(v___x_3085_, 3, v___x_3117_);
v___x_3119_ = v___x_3085_;
goto v_reusejp_3118_;
}
else
{
lean_object* v_reuseFailAlloc_3120_; 
v_reuseFailAlloc_3120_ = lean_alloc_ctor(0, 13, 1);
lean_ctor_set(v_reuseFailAlloc_3120_, 0, v_rings_3068_);
lean_ctor_set(v_reuseFailAlloc_3120_, 1, v_typeIdOf_3069_);
lean_ctor_set(v_reuseFailAlloc_3120_, 2, v_exprToRingId_3070_);
lean_ctor_set(v_reuseFailAlloc_3120_, 3, v___x_3117_);
lean_ctor_set(v_reuseFailAlloc_3120_, 4, v_stypeIdOf_3072_);
lean_ctor_set(v_reuseFailAlloc_3120_, 5, v_exprToSemiringId_3073_);
lean_ctor_set(v_reuseFailAlloc_3120_, 6, v_ncRings_3074_);
lean_ctor_set(v_reuseFailAlloc_3120_, 7, v_exprToNCRingId_3075_);
lean_ctor_set(v_reuseFailAlloc_3120_, 8, v_nctypeIdOf_3076_);
lean_ctor_set(v_reuseFailAlloc_3120_, 9, v_ncSemirings_3077_);
lean_ctor_set(v_reuseFailAlloc_3120_, 10, v_exprToNCSemiringId_3078_);
lean_ctor_set(v_reuseFailAlloc_3120_, 11, v_ncstypeIdOf_3079_);
lean_ctor_set(v_reuseFailAlloc_3120_, 12, v_steps_3080_);
lean_ctor_set_uint8(v_reuseFailAlloc_3120_, sizeof(void*)*13, v_reportedMaxDegreeIssue_3081_);
v___x_3119_ = v_reuseFailAlloc_3120_;
goto v_reusejp_3118_;
}
v_reusejp_3118_:
{
return v___x_3119_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_internalize___lam__1___boxed(lean_object* v___y_3139_, lean_object* v_e_3140_, lean_object* v_val_3141_, lean_object* v_s_3142_){
_start:
{
lean_object* v_res_3143_; 
v_res_3143_ = l_Lean_Meta_Grind_Arith_CommRing_internalize___lam__1(v___y_3139_, v_e_3140_, v_val_3141_, v_s_3142_);
lean_dec(v___y_3139_);
return v_res_3143_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_internalize___lam__2(lean_object* v_e_3144_, lean_object* v_val_3145_, lean_object* v_s_3146_){
_start:
{
lean_object* v_id_3147_; lean_object* v_type_3148_; lean_object* v_u_3149_; lean_object* v_ringInst_3150_; lean_object* v_semiringInst_3151_; lean_object* v_charInst_x3f_3152_; lean_object* v_addFn_x3f_3153_; lean_object* v_mulFn_x3f_3154_; lean_object* v_subFn_x3f_3155_; lean_object* v_negFn_x3f_3156_; lean_object* v_powFn_x3f_3157_; lean_object* v_intCastFn_x3f_3158_; lean_object* v_natCastFn_x3f_3159_; lean_object* v_one_x3f_3160_; lean_object* v_vars_3161_; lean_object* v_varMap_3162_; lean_object* v_denote_3163_; lean_object* v___x_3165_; uint8_t v_isShared_3166_; uint8_t v_isSharedCheck_3171_; 
v_id_3147_ = lean_ctor_get(v_s_3146_, 0);
v_type_3148_ = lean_ctor_get(v_s_3146_, 1);
v_u_3149_ = lean_ctor_get(v_s_3146_, 2);
v_ringInst_3150_ = lean_ctor_get(v_s_3146_, 3);
v_semiringInst_3151_ = lean_ctor_get(v_s_3146_, 4);
v_charInst_x3f_3152_ = lean_ctor_get(v_s_3146_, 5);
v_addFn_x3f_3153_ = lean_ctor_get(v_s_3146_, 6);
v_mulFn_x3f_3154_ = lean_ctor_get(v_s_3146_, 7);
v_subFn_x3f_3155_ = lean_ctor_get(v_s_3146_, 8);
v_negFn_x3f_3156_ = lean_ctor_get(v_s_3146_, 9);
v_powFn_x3f_3157_ = lean_ctor_get(v_s_3146_, 10);
v_intCastFn_x3f_3158_ = lean_ctor_get(v_s_3146_, 11);
v_natCastFn_x3f_3159_ = lean_ctor_get(v_s_3146_, 12);
v_one_x3f_3160_ = lean_ctor_get(v_s_3146_, 13);
v_vars_3161_ = lean_ctor_get(v_s_3146_, 14);
v_varMap_3162_ = lean_ctor_get(v_s_3146_, 15);
v_denote_3163_ = lean_ctor_get(v_s_3146_, 16);
v_isSharedCheck_3171_ = !lean_is_exclusive(v_s_3146_);
if (v_isSharedCheck_3171_ == 0)
{
v___x_3165_ = v_s_3146_;
v_isShared_3166_ = v_isSharedCheck_3171_;
goto v_resetjp_3164_;
}
else
{
lean_inc(v_denote_3163_);
lean_inc(v_varMap_3162_);
lean_inc(v_vars_3161_);
lean_inc(v_one_x3f_3160_);
lean_inc(v_natCastFn_x3f_3159_);
lean_inc(v_intCastFn_x3f_3158_);
lean_inc(v_powFn_x3f_3157_);
lean_inc(v_negFn_x3f_3156_);
lean_inc(v_subFn_x3f_3155_);
lean_inc(v_mulFn_x3f_3154_);
lean_inc(v_addFn_x3f_3153_);
lean_inc(v_charInst_x3f_3152_);
lean_inc(v_semiringInst_3151_);
lean_inc(v_ringInst_3150_);
lean_inc(v_u_3149_);
lean_inc(v_type_3148_);
lean_inc(v_id_3147_);
lean_dec(v_s_3146_);
v___x_3165_ = lean_box(0);
v_isShared_3166_ = v_isSharedCheck_3171_;
goto v_resetjp_3164_;
}
v_resetjp_3164_:
{
lean_object* v___x_3167_; lean_object* v___x_3169_; 
v___x_3167_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0___redArg(v_denote_3163_, v_e_3144_, v_val_3145_);
if (v_isShared_3166_ == 0)
{
lean_ctor_set(v___x_3165_, 16, v___x_3167_);
v___x_3169_ = v___x_3165_;
goto v_reusejp_3168_;
}
else
{
lean_object* v_reuseFailAlloc_3170_; 
v_reuseFailAlloc_3170_ = lean_alloc_ctor(0, 17, 0);
lean_ctor_set(v_reuseFailAlloc_3170_, 0, v_id_3147_);
lean_ctor_set(v_reuseFailAlloc_3170_, 1, v_type_3148_);
lean_ctor_set(v_reuseFailAlloc_3170_, 2, v_u_3149_);
lean_ctor_set(v_reuseFailAlloc_3170_, 3, v_ringInst_3150_);
lean_ctor_set(v_reuseFailAlloc_3170_, 4, v_semiringInst_3151_);
lean_ctor_set(v_reuseFailAlloc_3170_, 5, v_charInst_x3f_3152_);
lean_ctor_set(v_reuseFailAlloc_3170_, 6, v_addFn_x3f_3153_);
lean_ctor_set(v_reuseFailAlloc_3170_, 7, v_mulFn_x3f_3154_);
lean_ctor_set(v_reuseFailAlloc_3170_, 8, v_subFn_x3f_3155_);
lean_ctor_set(v_reuseFailAlloc_3170_, 9, v_negFn_x3f_3156_);
lean_ctor_set(v_reuseFailAlloc_3170_, 10, v_powFn_x3f_3157_);
lean_ctor_set(v_reuseFailAlloc_3170_, 11, v_intCastFn_x3f_3158_);
lean_ctor_set(v_reuseFailAlloc_3170_, 12, v_natCastFn_x3f_3159_);
lean_ctor_set(v_reuseFailAlloc_3170_, 13, v_one_x3f_3160_);
lean_ctor_set(v_reuseFailAlloc_3170_, 14, v_vars_3161_);
lean_ctor_set(v_reuseFailAlloc_3170_, 15, v_varMap_3162_);
lean_ctor_set(v_reuseFailAlloc_3170_, 16, v___x_3167_);
v___x_3169_ = v_reuseFailAlloc_3170_;
goto v_reusejp_3168_;
}
v_reusejp_3168_:
{
return v___x_3169_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_internalize___lam__3(lean_object* v_e_3172_, lean_object* v_val_3173_, lean_object* v_s_3174_){
_start:
{
lean_object* v_id_3175_; lean_object* v_type_3176_; lean_object* v_u_3177_; lean_object* v_semiringInst_3178_; lean_object* v_addFn_x3f_3179_; lean_object* v_mulFn_x3f_3180_; lean_object* v_powFn_x3f_3181_; lean_object* v_natCastFn_x3f_3182_; lean_object* v_denote_3183_; lean_object* v_vars_3184_; lean_object* v_varMap_3185_; lean_object* v___x_3187_; uint8_t v_isShared_3188_; uint8_t v_isSharedCheck_3193_; 
v_id_3175_ = lean_ctor_get(v_s_3174_, 0);
v_type_3176_ = lean_ctor_get(v_s_3174_, 1);
v_u_3177_ = lean_ctor_get(v_s_3174_, 2);
v_semiringInst_3178_ = lean_ctor_get(v_s_3174_, 3);
v_addFn_x3f_3179_ = lean_ctor_get(v_s_3174_, 4);
v_mulFn_x3f_3180_ = lean_ctor_get(v_s_3174_, 5);
v_powFn_x3f_3181_ = lean_ctor_get(v_s_3174_, 6);
v_natCastFn_x3f_3182_ = lean_ctor_get(v_s_3174_, 7);
v_denote_3183_ = lean_ctor_get(v_s_3174_, 8);
v_vars_3184_ = lean_ctor_get(v_s_3174_, 9);
v_varMap_3185_ = lean_ctor_get(v_s_3174_, 10);
v_isSharedCheck_3193_ = !lean_is_exclusive(v_s_3174_);
if (v_isSharedCheck_3193_ == 0)
{
v___x_3187_ = v_s_3174_;
v_isShared_3188_ = v_isSharedCheck_3193_;
goto v_resetjp_3186_;
}
else
{
lean_inc(v_varMap_3185_);
lean_inc(v_vars_3184_);
lean_inc(v_denote_3183_);
lean_inc(v_natCastFn_x3f_3182_);
lean_inc(v_powFn_x3f_3181_);
lean_inc(v_mulFn_x3f_3180_);
lean_inc(v_addFn_x3f_3179_);
lean_inc(v_semiringInst_3178_);
lean_inc(v_u_3177_);
lean_inc(v_type_3176_);
lean_inc(v_id_3175_);
lean_dec(v_s_3174_);
v___x_3187_ = lean_box(0);
v_isShared_3188_ = v_isSharedCheck_3193_;
goto v_resetjp_3186_;
}
v_resetjp_3186_:
{
lean_object* v___x_3189_; lean_object* v___x_3191_; 
v___x_3189_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0___redArg(v_denote_3183_, v_e_3172_, v_val_3173_);
if (v_isShared_3188_ == 0)
{
lean_ctor_set(v___x_3187_, 8, v___x_3189_);
v___x_3191_ = v___x_3187_;
goto v_reusejp_3190_;
}
else
{
lean_object* v_reuseFailAlloc_3192_; 
v_reuseFailAlloc_3192_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_3192_, 0, v_id_3175_);
lean_ctor_set(v_reuseFailAlloc_3192_, 1, v_type_3176_);
lean_ctor_set(v_reuseFailAlloc_3192_, 2, v_u_3177_);
lean_ctor_set(v_reuseFailAlloc_3192_, 3, v_semiringInst_3178_);
lean_ctor_set(v_reuseFailAlloc_3192_, 4, v_addFn_x3f_3179_);
lean_ctor_set(v_reuseFailAlloc_3192_, 5, v_mulFn_x3f_3180_);
lean_ctor_set(v_reuseFailAlloc_3192_, 6, v_powFn_x3f_3181_);
lean_ctor_set(v_reuseFailAlloc_3192_, 7, v_natCastFn_x3f_3182_);
lean_ctor_set(v_reuseFailAlloc_3192_, 8, v___x_3189_);
lean_ctor_set(v_reuseFailAlloc_3192_, 9, v_vars_3184_);
lean_ctor_set(v_reuseFailAlloc_3192_, 10, v_varMap_3185_);
v___x_3191_ = v_reuseFailAlloc_3192_;
goto v_reusejp_3190_;
}
v_reusejp_3190_:
{
return v___x_3191_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__1___redArg(lean_object* v_cls_3194_, lean_object* v_msg_3195_, lean_object* v___y_3196_, lean_object* v___y_3197_, lean_object* v___y_3198_, lean_object* v___y_3199_){
_start:
{
lean_object* v_ref_3201_; lean_object* v___x_3202_; lean_object* v_a_3203_; lean_object* v___x_3205_; uint8_t v_isShared_3206_; uint8_t v_isSharedCheck_3247_; 
v_ref_3201_ = lean_ctor_get(v___y_3198_, 2);
v___x_3202_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1_spec__5_spec__8_spec__9(v_msg_3195_, v___y_3196_, v___y_3197_, v___y_3198_, v___y_3199_);
v_a_3203_ = lean_ctor_get(v___x_3202_, 0);
v_isSharedCheck_3247_ = !lean_is_exclusive(v___x_3202_);
if (v_isSharedCheck_3247_ == 0)
{
v___x_3205_ = v___x_3202_;
v_isShared_3206_ = v_isSharedCheck_3247_;
goto v_resetjp_3204_;
}
else
{
lean_inc(v_a_3203_);
lean_dec(v___x_3202_);
v___x_3205_ = lean_box(0);
v_isShared_3206_ = v_isSharedCheck_3247_;
goto v_resetjp_3204_;
}
v_resetjp_3204_:
{
lean_object* v___x_3207_; lean_object* v_traceState_3208_; lean_object* v_env_3209_; lean_object* v_nextMacroScope_3210_; lean_object* v_ngen_3211_; lean_object* v_auxDeclNGen_3212_; lean_object* v_cache_3213_; lean_object* v_messages_3214_; lean_object* v_infoState_3215_; lean_object* v_snapshotTasks_3216_; lean_object* v___x_3218_; uint8_t v_isShared_3219_; uint8_t v_isSharedCheck_3246_; 
v___x_3207_ = lean_st_ref_take(v___y_3199_);
v_traceState_3208_ = lean_ctor_get(v___x_3207_, 4);
v_env_3209_ = lean_ctor_get(v___x_3207_, 0);
v_nextMacroScope_3210_ = lean_ctor_get(v___x_3207_, 1);
v_ngen_3211_ = lean_ctor_get(v___x_3207_, 2);
v_auxDeclNGen_3212_ = lean_ctor_get(v___x_3207_, 3);
v_cache_3213_ = lean_ctor_get(v___x_3207_, 5);
v_messages_3214_ = lean_ctor_get(v___x_3207_, 6);
v_infoState_3215_ = lean_ctor_get(v___x_3207_, 7);
v_snapshotTasks_3216_ = lean_ctor_get(v___x_3207_, 8);
v_isSharedCheck_3246_ = !lean_is_exclusive(v___x_3207_);
if (v_isSharedCheck_3246_ == 0)
{
v___x_3218_ = v___x_3207_;
v_isShared_3219_ = v_isSharedCheck_3246_;
goto v_resetjp_3217_;
}
else
{
lean_inc(v_snapshotTasks_3216_);
lean_inc(v_infoState_3215_);
lean_inc(v_messages_3214_);
lean_inc(v_cache_3213_);
lean_inc(v_traceState_3208_);
lean_inc(v_auxDeclNGen_3212_);
lean_inc(v_ngen_3211_);
lean_inc(v_nextMacroScope_3210_);
lean_inc(v_env_3209_);
lean_dec(v___x_3207_);
v___x_3218_ = lean_box(0);
v_isShared_3219_ = v_isSharedCheck_3246_;
goto v_resetjp_3217_;
}
v_resetjp_3217_:
{
uint64_t v_tid_3220_; lean_object* v_traces_3221_; lean_object* v___x_3223_; uint8_t v_isShared_3224_; uint8_t v_isSharedCheck_3245_; 
v_tid_3220_ = lean_ctor_get_uint64(v_traceState_3208_, sizeof(void*)*1);
v_traces_3221_ = lean_ctor_get(v_traceState_3208_, 0);
v_isSharedCheck_3245_ = !lean_is_exclusive(v_traceState_3208_);
if (v_isSharedCheck_3245_ == 0)
{
v___x_3223_ = v_traceState_3208_;
v_isShared_3224_ = v_isSharedCheck_3245_;
goto v_resetjp_3222_;
}
else
{
lean_inc(v_traces_3221_);
lean_dec(v_traceState_3208_);
v___x_3223_ = lean_box(0);
v_isShared_3224_ = v_isSharedCheck_3245_;
goto v_resetjp_3222_;
}
v_resetjp_3222_:
{
lean_object* v___x_3225_; double v___x_3226_; uint8_t v___x_3227_; lean_object* v___x_3228_; lean_object* v___x_3229_; lean_object* v___x_3230_; lean_object* v___x_3231_; lean_object* v___x_3232_; lean_object* v___x_3233_; lean_object* v___x_3235_; 
v___x_3225_ = lean_box(0);
v___x_3226_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg___closed__0);
v___x_3227_ = 0;
v___x_3228_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg___closed__1));
v___x_3229_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3229_, 0, v_cls_3194_);
lean_ctor_set(v___x_3229_, 1, v___x_3225_);
lean_ctor_set(v___x_3229_, 2, v___x_3228_);
lean_ctor_set_float(v___x_3229_, sizeof(void*)*3, v___x_3226_);
lean_ctor_set_float(v___x_3229_, sizeof(void*)*3 + 8, v___x_3226_);
lean_ctor_set_uint8(v___x_3229_, sizeof(void*)*3 + 16, v___x_3227_);
v___x_3230_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg___closed__2));
v___x_3231_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3231_, 0, v___x_3229_);
lean_ctor_set(v___x_3231_, 1, v_a_3203_);
lean_ctor_set(v___x_3231_, 2, v___x_3230_);
lean_inc(v_ref_3201_);
v___x_3232_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3232_, 0, v_ref_3201_);
lean_ctor_set(v___x_3232_, 1, v___x_3231_);
v___x_3233_ = l_Lean_PersistentArray_push___redArg(v_traces_3221_, v___x_3232_);
if (v_isShared_3224_ == 0)
{
lean_ctor_set(v___x_3223_, 0, v___x_3233_);
v___x_3235_ = v___x_3223_;
goto v_reusejp_3234_;
}
else
{
lean_object* v_reuseFailAlloc_3244_; 
v_reuseFailAlloc_3244_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3244_, 0, v___x_3233_);
lean_ctor_set_uint64(v_reuseFailAlloc_3244_, sizeof(void*)*1, v_tid_3220_);
v___x_3235_ = v_reuseFailAlloc_3244_;
goto v_reusejp_3234_;
}
v_reusejp_3234_:
{
lean_object* v___x_3237_; 
if (v_isShared_3219_ == 0)
{
lean_ctor_set(v___x_3218_, 4, v___x_3235_);
v___x_3237_ = v___x_3218_;
goto v_reusejp_3236_;
}
else
{
lean_object* v_reuseFailAlloc_3243_; 
v_reuseFailAlloc_3243_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3243_, 0, v_env_3209_);
lean_ctor_set(v_reuseFailAlloc_3243_, 1, v_nextMacroScope_3210_);
lean_ctor_set(v_reuseFailAlloc_3243_, 2, v_ngen_3211_);
lean_ctor_set(v_reuseFailAlloc_3243_, 3, v_auxDeclNGen_3212_);
lean_ctor_set(v_reuseFailAlloc_3243_, 4, v___x_3235_);
lean_ctor_set(v_reuseFailAlloc_3243_, 5, v_cache_3213_);
lean_ctor_set(v_reuseFailAlloc_3243_, 6, v_messages_3214_);
lean_ctor_set(v_reuseFailAlloc_3243_, 7, v_infoState_3215_);
lean_ctor_set(v_reuseFailAlloc_3243_, 8, v_snapshotTasks_3216_);
v___x_3237_ = v_reuseFailAlloc_3243_;
goto v_reusejp_3236_;
}
v_reusejp_3236_:
{
lean_object* v___x_3238_; lean_object* v___x_3239_; lean_object* v___x_3241_; 
v___x_3238_ = lean_st_ref_put(v___y_3199_, v___x_3237_);
v___x_3239_ = lean_box(0);
if (v_isShared_3206_ == 0)
{
lean_ctor_set(v___x_3205_, 0, v___x_3239_);
v___x_3241_ = v___x_3205_;
goto v_reusejp_3240_;
}
else
{
lean_object* v_reuseFailAlloc_3242_; 
v_reuseFailAlloc_3242_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3242_, 0, v___x_3239_);
v___x_3241_ = v_reuseFailAlloc_3242_;
goto v_reusejp_3240_;
}
v_reusejp_3240_:
{
return v___x_3241_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__1___redArg___boxed(lean_object* v_cls_3248_, lean_object* v_msg_3249_, lean_object* v___y_3250_, lean_object* v___y_3251_, lean_object* v___y_3252_, lean_object* v___y_3253_, lean_object* v___y_3254_){
_start:
{
lean_object* v_res_3255_; 
v_res_3255_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__1___redArg(v_cls_3248_, v_msg_3249_, v___y_3250_, v___y_3251_, v___y_3252_, v___y_3253_);
lean_dec(v___y_3253_);
lean_dec_ref(v___y_3252_);
lean_dec(v___y_3251_);
lean_dec_ref(v___y_3250_);
return v_res_3255_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__2___redArg(lean_object* v_cls_3256_, lean_object* v_msg_3257_, lean_object* v___y_3258_, lean_object* v___y_3259_, lean_object* v___y_3260_, lean_object* v___y_3261_){
_start:
{
lean_object* v_ref_3263_; lean_object* v___x_3264_; lean_object* v_a_3265_; lean_object* v___x_3267_; uint8_t v_isShared_3268_; uint8_t v_isSharedCheck_3309_; 
v_ref_3263_ = lean_ctor_get(v___y_3260_, 2);
v___x_3264_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1_spec__5_spec__8_spec__9(v_msg_3257_, v___y_3258_, v___y_3259_, v___y_3260_, v___y_3261_);
v_a_3265_ = lean_ctor_get(v___x_3264_, 0);
v_isSharedCheck_3309_ = !lean_is_exclusive(v___x_3264_);
if (v_isSharedCheck_3309_ == 0)
{
v___x_3267_ = v___x_3264_;
v_isShared_3268_ = v_isSharedCheck_3309_;
goto v_resetjp_3266_;
}
else
{
lean_inc(v_a_3265_);
lean_dec(v___x_3264_);
v___x_3267_ = lean_box(0);
v_isShared_3268_ = v_isSharedCheck_3309_;
goto v_resetjp_3266_;
}
v_resetjp_3266_:
{
lean_object* v___x_3269_; lean_object* v_traceState_3270_; lean_object* v_env_3271_; lean_object* v_nextMacroScope_3272_; lean_object* v_ngen_3273_; lean_object* v_auxDeclNGen_3274_; lean_object* v_cache_3275_; lean_object* v_messages_3276_; lean_object* v_infoState_3277_; lean_object* v_snapshotTasks_3278_; lean_object* v___x_3280_; uint8_t v_isShared_3281_; uint8_t v_isSharedCheck_3308_; 
v___x_3269_ = lean_st_ref_take(v___y_3261_);
v_traceState_3270_ = lean_ctor_get(v___x_3269_, 4);
v_env_3271_ = lean_ctor_get(v___x_3269_, 0);
v_nextMacroScope_3272_ = lean_ctor_get(v___x_3269_, 1);
v_ngen_3273_ = lean_ctor_get(v___x_3269_, 2);
v_auxDeclNGen_3274_ = lean_ctor_get(v___x_3269_, 3);
v_cache_3275_ = lean_ctor_get(v___x_3269_, 5);
v_messages_3276_ = lean_ctor_get(v___x_3269_, 6);
v_infoState_3277_ = lean_ctor_get(v___x_3269_, 7);
v_snapshotTasks_3278_ = lean_ctor_get(v___x_3269_, 8);
v_isSharedCheck_3308_ = !lean_is_exclusive(v___x_3269_);
if (v_isSharedCheck_3308_ == 0)
{
v___x_3280_ = v___x_3269_;
v_isShared_3281_ = v_isSharedCheck_3308_;
goto v_resetjp_3279_;
}
else
{
lean_inc(v_snapshotTasks_3278_);
lean_inc(v_infoState_3277_);
lean_inc(v_messages_3276_);
lean_inc(v_cache_3275_);
lean_inc(v_traceState_3270_);
lean_inc(v_auxDeclNGen_3274_);
lean_inc(v_ngen_3273_);
lean_inc(v_nextMacroScope_3272_);
lean_inc(v_env_3271_);
lean_dec(v___x_3269_);
v___x_3280_ = lean_box(0);
v_isShared_3281_ = v_isSharedCheck_3308_;
goto v_resetjp_3279_;
}
v_resetjp_3279_:
{
uint64_t v_tid_3282_; lean_object* v_traces_3283_; lean_object* v___x_3285_; uint8_t v_isShared_3286_; uint8_t v_isSharedCheck_3307_; 
v_tid_3282_ = lean_ctor_get_uint64(v_traceState_3270_, sizeof(void*)*1);
v_traces_3283_ = lean_ctor_get(v_traceState_3270_, 0);
v_isSharedCheck_3307_ = !lean_is_exclusive(v_traceState_3270_);
if (v_isSharedCheck_3307_ == 0)
{
v___x_3285_ = v_traceState_3270_;
v_isShared_3286_ = v_isSharedCheck_3307_;
goto v_resetjp_3284_;
}
else
{
lean_inc(v_traces_3283_);
lean_dec(v_traceState_3270_);
v___x_3285_ = lean_box(0);
v_isShared_3286_ = v_isSharedCheck_3307_;
goto v_resetjp_3284_;
}
v_resetjp_3284_:
{
lean_object* v___x_3287_; double v___x_3288_; uint8_t v___x_3289_; lean_object* v___x_3290_; lean_object* v___x_3291_; lean_object* v___x_3292_; lean_object* v___x_3293_; lean_object* v___x_3294_; lean_object* v___x_3295_; lean_object* v___x_3297_; 
v___x_3287_ = lean_box(0);
v___x_3288_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg___closed__0);
v___x_3289_ = 0;
v___x_3290_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg___closed__1));
v___x_3291_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3291_, 0, v_cls_3256_);
lean_ctor_set(v___x_3291_, 1, v___x_3287_);
lean_ctor_set(v___x_3291_, 2, v___x_3290_);
lean_ctor_set_float(v___x_3291_, sizeof(void*)*3, v___x_3288_);
lean_ctor_set_float(v___x_3291_, sizeof(void*)*3 + 8, v___x_3288_);
lean_ctor_set_uint8(v___x_3291_, sizeof(void*)*3 + 16, v___x_3289_);
v___x_3292_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg___closed__2));
v___x_3293_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3293_, 0, v___x_3291_);
lean_ctor_set(v___x_3293_, 1, v_a_3265_);
lean_ctor_set(v___x_3293_, 2, v___x_3292_);
lean_inc(v_ref_3263_);
v___x_3294_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3294_, 0, v_ref_3263_);
lean_ctor_set(v___x_3294_, 1, v___x_3293_);
v___x_3295_ = l_Lean_PersistentArray_push___redArg(v_traces_3283_, v___x_3294_);
if (v_isShared_3286_ == 0)
{
lean_ctor_set(v___x_3285_, 0, v___x_3295_);
v___x_3297_ = v___x_3285_;
goto v_reusejp_3296_;
}
else
{
lean_object* v_reuseFailAlloc_3306_; 
v_reuseFailAlloc_3306_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3306_, 0, v___x_3295_);
lean_ctor_set_uint64(v_reuseFailAlloc_3306_, sizeof(void*)*1, v_tid_3282_);
v___x_3297_ = v_reuseFailAlloc_3306_;
goto v_reusejp_3296_;
}
v_reusejp_3296_:
{
lean_object* v___x_3299_; 
if (v_isShared_3281_ == 0)
{
lean_ctor_set(v___x_3280_, 4, v___x_3297_);
v___x_3299_ = v___x_3280_;
goto v_reusejp_3298_;
}
else
{
lean_object* v_reuseFailAlloc_3305_; 
v_reuseFailAlloc_3305_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3305_, 0, v_env_3271_);
lean_ctor_set(v_reuseFailAlloc_3305_, 1, v_nextMacroScope_3272_);
lean_ctor_set(v_reuseFailAlloc_3305_, 2, v_ngen_3273_);
lean_ctor_set(v_reuseFailAlloc_3305_, 3, v_auxDeclNGen_3274_);
lean_ctor_set(v_reuseFailAlloc_3305_, 4, v___x_3297_);
lean_ctor_set(v_reuseFailAlloc_3305_, 5, v_cache_3275_);
lean_ctor_set(v_reuseFailAlloc_3305_, 6, v_messages_3276_);
lean_ctor_set(v_reuseFailAlloc_3305_, 7, v_infoState_3277_);
lean_ctor_set(v_reuseFailAlloc_3305_, 8, v_snapshotTasks_3278_);
v___x_3299_ = v_reuseFailAlloc_3305_;
goto v_reusejp_3298_;
}
v_reusejp_3298_:
{
lean_object* v___x_3300_; lean_object* v___x_3301_; lean_object* v___x_3303_; 
v___x_3300_ = lean_st_ref_put(v___y_3261_, v___x_3299_);
v___x_3301_ = lean_box(0);
if (v_isShared_3268_ == 0)
{
lean_ctor_set(v___x_3267_, 0, v___x_3301_);
v___x_3303_ = v___x_3267_;
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
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__2___redArg___boxed(lean_object* v_cls_3310_, lean_object* v_msg_3311_, lean_object* v___y_3312_, lean_object* v___y_3313_, lean_object* v___y_3314_, lean_object* v___y_3315_, lean_object* v___y_3316_){
_start:
{
lean_object* v_res_3317_; 
v_res_3317_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__2___redArg(v_cls_3310_, v_msg_3311_, v___y_3312_, v___y_3313_, v___y_3314_, v___y_3315_);
lean_dec(v___y_3315_);
lean_dec_ref(v___y_3314_);
lean_dec(v___y_3313_);
lean_dec_ref(v___y_3312_);
return v_res_3317_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__3___redArg(lean_object* v_cls_3318_, lean_object* v_msg_3319_, lean_object* v___y_3320_, lean_object* v___y_3321_, lean_object* v___y_3322_, lean_object* v___y_3323_){
_start:
{
lean_object* v_ref_3325_; lean_object* v___x_3326_; lean_object* v_a_3327_; lean_object* v___x_3329_; uint8_t v_isShared_3330_; uint8_t v_isSharedCheck_3371_; 
v_ref_3325_ = lean_ctor_get(v___y_3322_, 2);
v___x_3326_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00Lean_Meta_Grind_Arith_CommRing_mkUnaryFn___at___00Lean_Meta_Grind_Arith_CommRing_getNegFn___at___00Lean_Meta_Grind_Arith_CommRing_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__1_spec__5_spec__8_spec__9(v_msg_3319_, v___y_3320_, v___y_3321_, v___y_3322_, v___y_3323_);
v_a_3327_ = lean_ctor_get(v___x_3326_, 0);
v_isSharedCheck_3371_ = !lean_is_exclusive(v___x_3326_);
if (v_isSharedCheck_3371_ == 0)
{
v___x_3329_ = v___x_3326_;
v_isShared_3330_ = v_isSharedCheck_3371_;
goto v_resetjp_3328_;
}
else
{
lean_inc(v_a_3327_);
lean_dec(v___x_3326_);
v___x_3329_ = lean_box(0);
v_isShared_3330_ = v_isSharedCheck_3371_;
goto v_resetjp_3328_;
}
v_resetjp_3328_:
{
lean_object* v___x_3331_; lean_object* v_traceState_3332_; lean_object* v_env_3333_; lean_object* v_nextMacroScope_3334_; lean_object* v_ngen_3335_; lean_object* v_auxDeclNGen_3336_; lean_object* v_cache_3337_; lean_object* v_messages_3338_; lean_object* v_infoState_3339_; lean_object* v_snapshotTasks_3340_; lean_object* v___x_3342_; uint8_t v_isShared_3343_; uint8_t v_isSharedCheck_3370_; 
v___x_3331_ = lean_st_ref_take(v___y_3323_);
v_traceState_3332_ = lean_ctor_get(v___x_3331_, 4);
v_env_3333_ = lean_ctor_get(v___x_3331_, 0);
v_nextMacroScope_3334_ = lean_ctor_get(v___x_3331_, 1);
v_ngen_3335_ = lean_ctor_get(v___x_3331_, 2);
v_auxDeclNGen_3336_ = lean_ctor_get(v___x_3331_, 3);
v_cache_3337_ = lean_ctor_get(v___x_3331_, 5);
v_messages_3338_ = lean_ctor_get(v___x_3331_, 6);
v_infoState_3339_ = lean_ctor_get(v___x_3331_, 7);
v_snapshotTasks_3340_ = lean_ctor_get(v___x_3331_, 8);
v_isSharedCheck_3370_ = !lean_is_exclusive(v___x_3331_);
if (v_isSharedCheck_3370_ == 0)
{
v___x_3342_ = v___x_3331_;
v_isShared_3343_ = v_isSharedCheck_3370_;
goto v_resetjp_3341_;
}
else
{
lean_inc(v_snapshotTasks_3340_);
lean_inc(v_infoState_3339_);
lean_inc(v_messages_3338_);
lean_inc(v_cache_3337_);
lean_inc(v_traceState_3332_);
lean_inc(v_auxDeclNGen_3336_);
lean_inc(v_ngen_3335_);
lean_inc(v_nextMacroScope_3334_);
lean_inc(v_env_3333_);
lean_dec(v___x_3331_);
v___x_3342_ = lean_box(0);
v_isShared_3343_ = v_isSharedCheck_3370_;
goto v_resetjp_3341_;
}
v_resetjp_3341_:
{
uint64_t v_tid_3344_; lean_object* v_traces_3345_; lean_object* v___x_3347_; uint8_t v_isShared_3348_; uint8_t v_isSharedCheck_3369_; 
v_tid_3344_ = lean_ctor_get_uint64(v_traceState_3332_, sizeof(void*)*1);
v_traces_3345_ = lean_ctor_get(v_traceState_3332_, 0);
v_isSharedCheck_3369_ = !lean_is_exclusive(v_traceState_3332_);
if (v_isSharedCheck_3369_ == 0)
{
v___x_3347_ = v_traceState_3332_;
v_isShared_3348_ = v_isSharedCheck_3369_;
goto v_resetjp_3346_;
}
else
{
lean_inc(v_traces_3345_);
lean_dec(v_traceState_3332_);
v___x_3347_ = lean_box(0);
v_isShared_3348_ = v_isSharedCheck_3369_;
goto v_resetjp_3346_;
}
v_resetjp_3346_:
{
lean_object* v___x_3349_; double v___x_3350_; uint8_t v___x_3351_; lean_object* v___x_3352_; lean_object* v___x_3353_; lean_object* v___x_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; lean_object* v___x_3359_; 
v___x_3349_ = lean_box(0);
v___x_3350_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg___closed__0);
v___x_3351_ = 0;
v___x_3352_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg___closed__1));
v___x_3353_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3353_, 0, v_cls_3318_);
lean_ctor_set(v___x_3353_, 1, v___x_3349_);
lean_ctor_set(v___x_3353_, 2, v___x_3352_);
lean_ctor_set_float(v___x_3353_, sizeof(void*)*3, v___x_3350_);
lean_ctor_set_float(v___x_3353_, sizeof(void*)*3 + 8, v___x_3350_);
lean_ctor_set_uint8(v___x_3353_, sizeof(void*)*3 + 16, v___x_3351_);
v___x_3354_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg___closed__2));
v___x_3355_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3355_, 0, v___x_3353_);
lean_ctor_set(v___x_3355_, 1, v_a_3327_);
lean_ctor_set(v___x_3355_, 2, v___x_3354_);
lean_inc(v_ref_3325_);
v___x_3356_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3356_, 0, v_ref_3325_);
lean_ctor_set(v___x_3356_, 1, v___x_3355_);
v___x_3357_ = l_Lean_PersistentArray_push___redArg(v_traces_3345_, v___x_3356_);
if (v_isShared_3348_ == 0)
{
lean_ctor_set(v___x_3347_, 0, v___x_3357_);
v___x_3359_ = v___x_3347_;
goto v_reusejp_3358_;
}
else
{
lean_object* v_reuseFailAlloc_3368_; 
v_reuseFailAlloc_3368_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3368_, 0, v___x_3357_);
lean_ctor_set_uint64(v_reuseFailAlloc_3368_, sizeof(void*)*1, v_tid_3344_);
v___x_3359_ = v_reuseFailAlloc_3368_;
goto v_reusejp_3358_;
}
v_reusejp_3358_:
{
lean_object* v___x_3361_; 
if (v_isShared_3343_ == 0)
{
lean_ctor_set(v___x_3342_, 4, v___x_3359_);
v___x_3361_ = v___x_3342_;
goto v_reusejp_3360_;
}
else
{
lean_object* v_reuseFailAlloc_3367_; 
v_reuseFailAlloc_3367_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3367_, 0, v_env_3333_);
lean_ctor_set(v_reuseFailAlloc_3367_, 1, v_nextMacroScope_3334_);
lean_ctor_set(v_reuseFailAlloc_3367_, 2, v_ngen_3335_);
lean_ctor_set(v_reuseFailAlloc_3367_, 3, v_auxDeclNGen_3336_);
lean_ctor_set(v_reuseFailAlloc_3367_, 4, v___x_3359_);
lean_ctor_set(v_reuseFailAlloc_3367_, 5, v_cache_3337_);
lean_ctor_set(v_reuseFailAlloc_3367_, 6, v_messages_3338_);
lean_ctor_set(v_reuseFailAlloc_3367_, 7, v_infoState_3339_);
lean_ctor_set(v_reuseFailAlloc_3367_, 8, v_snapshotTasks_3340_);
v___x_3361_ = v_reuseFailAlloc_3367_;
goto v_reusejp_3360_;
}
v_reusejp_3360_:
{
lean_object* v___x_3362_; lean_object* v___x_3363_; lean_object* v___x_3365_; 
v___x_3362_ = lean_st_ref_put(v___y_3323_, v___x_3361_);
v___x_3363_ = lean_box(0);
if (v_isShared_3330_ == 0)
{
lean_ctor_set(v___x_3329_, 0, v___x_3363_);
v___x_3365_ = v___x_3329_;
goto v_reusejp_3364_;
}
else
{
lean_object* v_reuseFailAlloc_3366_; 
v_reuseFailAlloc_3366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3366_, 0, v___x_3363_);
v___x_3365_ = v_reuseFailAlloc_3366_;
goto v_reusejp_3364_;
}
v_reusejp_3364_:
{
return v___x_3365_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__3___redArg___boxed(lean_object* v_cls_3372_, lean_object* v_msg_3373_, lean_object* v___y_3374_, lean_object* v___y_3375_, lean_object* v___y_3376_, lean_object* v___y_3377_, lean_object* v___y_3378_){
_start:
{
lean_object* v_res_3379_; 
v_res_3379_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__3___redArg(v_cls_3372_, v_msg_3373_, v___y_3374_, v___y_3375_, v___y_3376_, v___y_3377_);
lean_dec(v___y_3377_);
lean_dec_ref(v___y_3376_);
lean_dec(v___y_3375_);
lean_dec_ref(v___y_3374_);
return v_res_3379_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__2(void){
_start:
{
lean_object* v___x_3385_; lean_object* v___x_3386_; lean_object* v___x_3387_; 
v___x_3385_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__1));
v___x_3386_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__7));
v___x_3387_ = l_Lean_Name_append(v___x_3386_, v___x_3385_);
return v___x_3387_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__4(void){
_start:
{
lean_object* v___x_3389_; lean_object* v___x_3390_; 
v___x_3389_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__3));
v___x_3390_ = l_Lean_stringToMessageData(v___x_3389_);
return v___x_3390_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__6(void){
_start:
{
lean_object* v___x_3392_; lean_object* v___x_3393_; 
v___x_3392_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__5));
v___x_3393_ = l_Lean_stringToMessageData(v___x_3392_);
return v___x_3393_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__8(void){
_start:
{
lean_object* v___x_3395_; lean_object* v___x_3396_; 
v___x_3395_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__7));
v___x_3396_ = l_Lean_stringToMessageData(v___x_3395_);
return v___x_3396_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__10(void){
_start:
{
lean_object* v___x_3398_; lean_object* v___x_3399_; 
v___x_3398_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__9));
v___x_3399_ = l_Lean_stringToMessageData(v___x_3398_);
return v___x_3399_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__12(void){
_start:
{
lean_object* v___x_3401_; lean_object* v___x_3402_; 
v___x_3401_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__11));
v___x_3402_ = l_Lean_stringToMessageData(v___x_3401_);
return v___x_3402_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_internalize(lean_object* v_e_3403_, lean_object* v_parent_x3f_3404_, lean_object* v_a_3405_, lean_object* v_a_3406_, lean_object* v_a_3407_, lean_object* v_a_3408_, lean_object* v_a_3409_, lean_object* v_a_3410_, lean_object* v_a_3411_, lean_object* v_a_3412_, lean_object* v_a_3413_, lean_object* v_a_3414_){
_start:
{
lean_object* v___x_3416_; 
v___x_3416_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_3407_);
if (lean_obj_tag(v___x_3416_) == 0)
{
lean_object* v_a_3417_; lean_object* v___x_3419_; uint8_t v_isShared_3420_; uint8_t v_isSharedCheck_3761_; 
v_a_3417_ = lean_ctor_get(v___x_3416_, 0);
v_isSharedCheck_3761_ = !lean_is_exclusive(v___x_3416_);
if (v_isSharedCheck_3761_ == 0)
{
v___x_3419_ = v___x_3416_;
v_isShared_3420_ = v_isSharedCheck_3761_;
goto v_resetjp_3418_;
}
else
{
lean_inc(v_a_3417_);
lean_dec(v___x_3416_);
v___x_3419_ = lean_box(0);
v_isShared_3420_ = v_isSharedCheck_3761_;
goto v_resetjp_3418_;
}
v_resetjp_3418_:
{
uint8_t v_ring_3421_; 
v_ring_3421_ = lean_ctor_get_uint8(v_a_3417_, sizeof(void*)*14 + 21);
lean_dec(v_a_3417_);
if (v_ring_3421_ == 0)
{
lean_object* v___x_3422_; lean_object* v___x_3424_; 
lean_dec(v_parent_x3f_3404_);
lean_dec_ref(v_e_3403_);
v___x_3422_ = lean_box(0);
if (v_isShared_3420_ == 0)
{
lean_ctor_set(v___x_3419_, 0, v___x_3422_);
v___x_3424_ = v___x_3419_;
goto v_reusejp_3423_;
}
else
{
lean_object* v_reuseFailAlloc_3425_; 
v_reuseFailAlloc_3425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3425_, 0, v___x_3422_);
v___x_3424_ = v_reuseFailAlloc_3425_;
goto v_reusejp_3423_;
}
v_reusejp_3423_:
{
return v___x_3424_;
}
}
else
{
uint8_t v___x_3426_; 
v___x_3426_ = l_Lean_Meta_Grind_Arith_isIntModuleVirtualParent(v_parent_x3f_3404_);
if (v___x_3426_ == 0)
{
lean_object* v___x_3427_; 
lean_del_object(v___x_3419_);
lean_inc_ref(v_e_3403_);
v___x_3427_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeInv(v_e_3403_, v_a_3405_, v_a_3406_, v_a_3407_, v_a_3408_, v_a_3409_, v_a_3410_, v_a_3411_, v_a_3412_, v_a_3413_, v_a_3414_);
if (lean_obj_tag(v___x_3427_) == 0)
{
lean_object* v_a_3428_; lean_object* v___x_3430_; uint8_t v_isShared_3431_; uint8_t v_isSharedCheck_3748_; 
v_a_3428_ = lean_ctor_get(v___x_3427_, 0);
v_isSharedCheck_3748_ = !lean_is_exclusive(v___x_3427_);
if (v_isSharedCheck_3748_ == 0)
{
v___x_3430_ = v___x_3427_;
v_isShared_3431_ = v_isSharedCheck_3748_;
goto v_resetjp_3429_;
}
else
{
lean_inc(v_a_3428_);
lean_dec(v___x_3427_);
v___x_3430_ = lean_box(0);
v_isShared_3431_ = v_isSharedCheck_3748_;
goto v_resetjp_3429_;
}
v_resetjp_3429_:
{
uint8_t v___x_3432_; 
v___x_3432_ = lean_unbox(v_a_3428_);
lean_dec(v_a_3428_);
if (v___x_3432_ == 0)
{
lean_object* v___x_3433_; 
lean_inc_ref(v_e_3403_);
v___x_3433_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f(v_e_3403_);
if (lean_obj_tag(v___x_3433_) == 1)
{
lean_object* v_val_3434_; uint8_t v___x_3435_; 
v_val_3434_ = lean_ctor_get(v___x_3433_, 0);
lean_inc(v_val_3434_);
lean_dec_ref_known(v___x_3433_, 1);
v___x_3435_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isForbiddenParent(v_parent_x3f_3404_);
if (v___x_3435_ == 0)
{
lean_object* v___x_3436_; 
lean_del_object(v___x_3430_);
lean_inc(v_val_3434_);
v___x_3436_ = l_Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f(v_val_3434_, v_a_3405_, v_a_3406_, v_a_3407_, v_a_3408_, v_a_3409_, v_a_3410_, v_a_3411_, v_a_3412_, v_a_3413_, v_a_3414_);
if (lean_obj_tag(v___x_3436_) == 0)
{
lean_object* v_a_3437_; 
v_a_3437_ = lean_ctor_get(v___x_3436_, 0);
lean_inc(v_a_3437_);
lean_dec_ref_known(v___x_3436_, 1);
if (lean_obj_tag(v_a_3437_) == 1)
{
lean_object* v_val_3438_; lean_object* v___x_3439_; lean_object* v___x_3440_; lean_object* v___x_3441_; 
lean_dec(v_val_3434_);
v_val_3438_ = lean_ctor_get(v_a_3437_, 0);
lean_inc_n(v_val_3438_, 2);
lean_dec_ref_known(v_a_3437_, 1);
v___x_3439_ = lean_unsigned_to_nat(0u);
v___x_3440_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3440_, 0, v_val_3438_);
lean_ctor_set_uint8(v___x_3440_, sizeof(void*)*1, v___x_3435_);
lean_inc_ref(v_e_3403_);
v___x_3441_ = l_Lean_Meta_Grind_Arith_CommRing_reify_x3f(v_e_3403_, v_ring_3421_, v___x_3439_, v___x_3440_, v_a_3405_, v_a_3406_, v_a_3407_, v_a_3408_, v_a_3409_, v_a_3410_, v_a_3411_, v_a_3412_, v_a_3413_, v_a_3414_);
if (lean_obj_tag(v___x_3441_) == 0)
{
lean_object* v_a_3442_; lean_object* v___x_3444_; uint8_t v_isShared_3445_; uint8_t v_isSharedCheck_3494_; 
v_a_3442_ = lean_ctor_get(v___x_3441_, 0);
v_isSharedCheck_3494_ = !lean_is_exclusive(v___x_3441_);
if (v_isSharedCheck_3494_ == 0)
{
v___x_3444_ = v___x_3441_;
v_isShared_3445_ = v_isSharedCheck_3494_;
goto v_resetjp_3443_;
}
else
{
lean_inc(v_a_3442_);
lean_dec(v___x_3441_);
v___x_3444_ = lean_box(0);
v_isShared_3445_ = v_isSharedCheck_3494_;
goto v_resetjp_3443_;
}
v_resetjp_3443_:
{
if (lean_obj_tag(v_a_3442_) == 1)
{
lean_object* v_toCold_3446_; lean_object* v_options_3447_; lean_object* v_val_3448_; lean_object* v_inheritedTraceOptions_3449_; uint8_t v_hasTrace_3450_; lean_object* v___f_3451_; lean_object* v___y_3453_; lean_object* v___y_3454_; lean_object* v___y_3455_; lean_object* v___y_3456_; lean_object* v___y_3457_; lean_object* v___y_3458_; lean_object* v___y_3459_; lean_object* v___y_3460_; lean_object* v___y_3461_; lean_object* v___y_3462_; lean_object* v___y_3463_; 
lean_del_object(v___x_3444_);
v_toCold_3446_ = lean_ctor_get(v_a_3413_, 0);
v_options_3447_ = lean_ctor_get(v_toCold_3446_, 2);
v_val_3448_ = lean_ctor_get(v_a_3442_, 0);
lean_inc(v_val_3448_);
lean_dec_ref_known(v_a_3442_, 1);
v_inheritedTraceOptions_3449_ = lean_ctor_get(v_toCold_3446_, 11);
v_hasTrace_3450_ = lean_ctor_get_uint8(v_options_3447_, sizeof(void*)*1);
lean_inc_ref(v_e_3403_);
v___f_3451_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_internalize___lam__0), 3, 2);
lean_closure_set(v___f_3451_, 0, v_e_3403_);
lean_closure_set(v___f_3451_, 1, v_val_3448_);
if (v_hasTrace_3450_ == 0)
{
lean_dec(v_val_3438_);
v___y_3453_ = v___x_3440_;
v___y_3454_ = v_a_3405_;
v___y_3455_ = v_a_3406_;
v___y_3456_ = v_a_3407_;
v___y_3457_ = v_a_3408_;
v___y_3458_ = v_a_3409_;
v___y_3459_ = v_a_3410_;
v___y_3460_ = v_a_3411_;
v___y_3461_ = v_a_3412_;
v___y_3462_ = v_a_3413_;
v___y_3463_ = v_a_3414_;
goto v___jp_3452_;
}
else
{
lean_object* v___x_3469_; lean_object* v___x_3470_; uint8_t v___x_3471_; 
v___x_3469_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__1));
v___x_3470_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__2, &l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__2_once, _init_l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__2);
v___x_3471_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3449_, v_options_3447_, v___x_3470_);
if (v___x_3471_ == 0)
{
lean_dec(v_val_3438_);
v___y_3453_ = v___x_3440_;
v___y_3454_ = v_a_3405_;
v___y_3455_ = v_a_3406_;
v___y_3456_ = v_a_3407_;
v___y_3457_ = v_a_3408_;
v___y_3458_ = v_a_3409_;
v___y_3459_ = v_a_3410_;
v___y_3460_ = v_a_3411_;
v___y_3461_ = v_a_3412_;
v___y_3462_ = v_a_3413_;
v___y_3463_ = v_a_3414_;
goto v___jp_3452_;
}
else
{
lean_object* v___x_3472_; 
v___x_3472_ = l_Lean_Meta_Grind_updateLastTag(v_a_3405_, v_a_3406_, v_a_3407_, v_a_3408_, v_a_3409_, v_a_3410_, v_a_3411_, v_a_3412_, v_a_3413_, v_a_3414_);
if (lean_obj_tag(v___x_3472_) == 0)
{
lean_object* v___x_3474_; uint8_t v_isShared_3475_; uint8_t v_isSharedCheck_3488_; 
v_isSharedCheck_3488_ = !lean_is_exclusive(v___x_3472_);
if (v_isSharedCheck_3488_ == 0)
{
lean_object* v_unused_3489_; 
v_unused_3489_ = lean_ctor_get(v___x_3472_, 0);
lean_dec(v_unused_3489_);
v___x_3474_ = v___x_3472_;
v_isShared_3475_ = v_isSharedCheck_3488_;
goto v_resetjp_3473_;
}
else
{
lean_dec(v___x_3472_);
v___x_3474_ = lean_box(0);
v_isShared_3475_ = v_isSharedCheck_3488_;
goto v_resetjp_3473_;
}
v_resetjp_3473_:
{
lean_object* v___x_3476_; lean_object* v___x_3477_; lean_object* v___x_3479_; 
v___x_3476_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__4, &l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__4_once, _init_l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__4);
v___x_3477_ = l_Nat_reprFast(v_val_3438_);
if (v_isShared_3475_ == 0)
{
lean_ctor_set_tag(v___x_3474_, 3);
lean_ctor_set(v___x_3474_, 0, v___x_3477_);
v___x_3479_ = v___x_3474_;
goto v_reusejp_3478_;
}
else
{
lean_object* v_reuseFailAlloc_3487_; 
v_reuseFailAlloc_3487_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3487_, 0, v___x_3477_);
v___x_3479_ = v_reuseFailAlloc_3487_;
goto v_reusejp_3478_;
}
v_reusejp_3478_:
{
lean_object* v___x_3480_; lean_object* v___x_3481_; lean_object* v___x_3482_; lean_object* v___x_3483_; lean_object* v___x_3484_; lean_object* v___x_3485_; lean_object* v___x_3486_; 
v___x_3480_ = l_Lean_MessageData_ofFormat(v___x_3479_);
v___x_3481_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3481_, 0, v___x_3476_);
lean_ctor_set(v___x_3481_, 1, v___x_3480_);
v___x_3482_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__6, &l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__6_once, _init_l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__6);
v___x_3483_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3483_, 0, v___x_3481_);
lean_ctor_set(v___x_3483_, 1, v___x_3482_);
lean_inc_ref(v_e_3403_);
v___x_3484_ = l_Lean_MessageData_ofExpr(v_e_3403_);
v___x_3485_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3485_, 0, v___x_3483_);
lean_ctor_set(v___x_3485_, 1, v___x_3484_);
v___x_3486_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg(v___x_3469_, v___x_3485_, v_a_3411_, v_a_3412_, v_a_3413_, v_a_3414_);
if (lean_obj_tag(v___x_3486_) == 0)
{
lean_dec_ref_known(v___x_3486_, 1);
v___y_3453_ = v___x_3440_;
v___y_3454_ = v_a_3405_;
v___y_3455_ = v_a_3406_;
v___y_3456_ = v_a_3407_;
v___y_3457_ = v_a_3408_;
v___y_3458_ = v_a_3409_;
v___y_3459_ = v_a_3410_;
v___y_3460_ = v_a_3411_;
v___y_3461_ = v_a_3412_;
v___y_3462_ = v_a_3413_;
v___y_3463_ = v_a_3414_;
goto v___jp_3452_;
}
else
{
lean_dec_ref(v___f_3451_);
lean_dec_ref_known(v___x_3440_, 1);
lean_dec_ref(v_e_3403_);
return v___x_3486_;
}
}
}
}
else
{
lean_dec_ref(v___f_3451_);
lean_dec_ref_known(v___x_3440_, 1);
lean_dec(v_val_3438_);
lean_dec_ref(v_e_3403_);
return v___x_3472_;
}
}
}
v___jp_3452_:
{
lean_object* v___x_3464_; 
lean_inc_ref(v_e_3403_);
v___x_3464_ = l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg(v_e_3403_, v___y_3453_, v___y_3454_, v___y_3458_, v___y_3459_, v___y_3460_, v___y_3461_, v___y_3462_, v___y_3463_);
if (lean_obj_tag(v___x_3464_) == 0)
{
lean_object* v___x_3465_; lean_object* v___x_3466_; 
lean_dec_ref_known(v___x_3464_, 1);
v___x_3465_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_3466_ = l_Lean_Meta_Grind_SolverExtension_markTerm___redArg(v___x_3465_, v_e_3403_, v___y_3454_, v___y_3455_, v___y_3456_, v___y_3457_, v___y_3458_, v___y_3459_, v___y_3460_, v___y_3461_, v___y_3462_, v___y_3463_);
if (lean_obj_tag(v___x_3466_) == 0)
{
lean_object* v___x_3467_; 
lean_dec_ref_known(v___x_3466_, 1);
v___x_3467_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(v___f_3451_, v___y_3453_, v___y_3454_);
if (lean_obj_tag(v___x_3467_) == 0)
{
lean_object* v___x_3468_; 
lean_dec_ref_known(v___x_3467_, 1);
v___x_3468_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars(v___y_3453_, v___y_3454_, v___y_3455_, v___y_3456_, v___y_3457_, v___y_3458_, v___y_3459_, v___y_3460_, v___y_3461_, v___y_3462_, v___y_3463_);
lean_dec_ref(v___y_3453_);
return v___x_3468_;
}
else
{
lean_dec_ref(v___y_3453_);
return v___x_3467_;
}
}
else
{
lean_dec_ref(v___y_3453_);
lean_dec_ref(v___f_3451_);
return v___x_3466_;
}
}
else
{
lean_dec_ref(v___y_3453_);
lean_dec_ref(v___f_3451_);
lean_dec_ref(v_e_3403_);
return v___x_3464_;
}
}
}
else
{
lean_object* v___x_3490_; lean_object* v___x_3492_; 
lean_dec(v_a_3442_);
lean_dec_ref_known(v___x_3440_, 1);
lean_dec(v_val_3438_);
lean_dec_ref(v_e_3403_);
v___x_3490_ = lean_box(0);
if (v_isShared_3445_ == 0)
{
lean_ctor_set(v___x_3444_, 0, v___x_3490_);
v___x_3492_ = v___x_3444_;
goto v_reusejp_3491_;
}
else
{
lean_object* v_reuseFailAlloc_3493_; 
v_reuseFailAlloc_3493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3493_, 0, v___x_3490_);
v___x_3492_ = v_reuseFailAlloc_3493_;
goto v_reusejp_3491_;
}
v_reusejp_3491_:
{
return v___x_3492_;
}
}
}
}
else
{
lean_object* v_a_3495_; lean_object* v___x_3497_; uint8_t v_isShared_3498_; uint8_t v_isSharedCheck_3502_; 
lean_dec_ref_known(v___x_3440_, 1);
lean_dec(v_val_3438_);
lean_dec_ref(v_e_3403_);
v_a_3495_ = lean_ctor_get(v___x_3441_, 0);
v_isSharedCheck_3502_ = !lean_is_exclusive(v___x_3441_);
if (v_isSharedCheck_3502_ == 0)
{
v___x_3497_ = v___x_3441_;
v_isShared_3498_ = v_isSharedCheck_3502_;
goto v_resetjp_3496_;
}
else
{
lean_inc(v_a_3495_);
lean_dec(v___x_3441_);
v___x_3497_ = lean_box(0);
v_isShared_3498_ = v_isSharedCheck_3502_;
goto v_resetjp_3496_;
}
v_resetjp_3496_:
{
lean_object* v___x_3500_; 
if (v_isShared_3498_ == 0)
{
v___x_3500_ = v___x_3497_;
goto v_reusejp_3499_;
}
else
{
lean_object* v_reuseFailAlloc_3501_; 
v_reuseFailAlloc_3501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3501_, 0, v_a_3495_);
v___x_3500_ = v_reuseFailAlloc_3501_;
goto v_reusejp_3499_;
}
v_reusejp_3499_:
{
return v___x_3500_;
}
}
}
}
else
{
lean_object* v___x_3503_; 
lean_dec(v_a_3437_);
lean_inc(v_val_3434_);
v___x_3503_ = l_Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f(v_val_3434_, v_a_3405_, v_a_3406_, v_a_3407_, v_a_3408_, v_a_3409_, v_a_3410_, v_a_3411_, v_a_3412_, v_a_3413_, v_a_3414_);
if (lean_obj_tag(v___x_3503_) == 0)
{
lean_object* v_a_3504_; 
v_a_3504_ = lean_ctor_get(v___x_3503_, 0);
lean_inc(v_a_3504_);
lean_dec_ref_known(v___x_3503_, 1);
if (lean_obj_tag(v_a_3504_) == 1)
{
lean_object* v_val_3505_; lean_object* v___x_3506_; 
lean_dec(v_val_3434_);
v_val_3505_ = lean_ctor_get(v_a_3504_, 0);
lean_inc(v_val_3505_);
lean_dec_ref_known(v_a_3504_, 1);
lean_inc_ref(v_e_3403_);
v___x_3506_ = l_Lean_Meta_Grind_Arith_CommRing_sreify_x3f(v_e_3403_, v_val_3505_, v_a_3405_, v_a_3406_, v_a_3407_, v_a_3408_, v_a_3409_, v_a_3410_, v_a_3411_, v_a_3412_, v_a_3413_, v_a_3414_);
if (lean_obj_tag(v___x_3506_) == 0)
{
lean_object* v_a_3507_; lean_object* v___x_3509_; uint8_t v_isShared_3510_; uint8_t v_isSharedCheck_3558_; 
v_a_3507_ = lean_ctor_get(v___x_3506_, 0);
v_isSharedCheck_3558_ = !lean_is_exclusive(v___x_3506_);
if (v_isSharedCheck_3558_ == 0)
{
v___x_3509_ = v___x_3506_;
v_isShared_3510_ = v_isSharedCheck_3558_;
goto v_resetjp_3508_;
}
else
{
lean_inc(v_a_3507_);
lean_dec(v___x_3506_);
v___x_3509_ = lean_box(0);
v_isShared_3510_ = v_isSharedCheck_3558_;
goto v_resetjp_3508_;
}
v_resetjp_3508_:
{
if (lean_obj_tag(v_a_3507_) == 1)
{
lean_object* v_val_3511_; lean_object* v___y_3513_; lean_object* v___y_3514_; lean_object* v___y_3515_; lean_object* v___y_3516_; lean_object* v___y_3517_; lean_object* v___y_3518_; lean_object* v___y_3519_; lean_object* v___y_3520_; lean_object* v___y_3521_; lean_object* v___y_3522_; lean_object* v___y_3523_; lean_object* v_toCold_3529_; lean_object* v_options_3530_; uint8_t v_hasTrace_3531_; 
lean_del_object(v___x_3509_);
v_val_3511_ = lean_ctor_get(v_a_3507_, 0);
lean_inc(v_val_3511_);
lean_dec_ref_known(v_a_3507_, 1);
v_toCold_3529_ = lean_ctor_get(v_a_3413_, 0);
v_options_3530_ = lean_ctor_get(v_toCold_3529_, 2);
v_hasTrace_3531_ = lean_ctor_get_uint8(v_options_3530_, sizeof(void*)*1);
if (v_hasTrace_3531_ == 0)
{
v___y_3513_ = v_val_3505_;
v___y_3514_ = v_a_3405_;
v___y_3515_ = v_a_3406_;
v___y_3516_ = v_a_3407_;
v___y_3517_ = v_a_3408_;
v___y_3518_ = v_a_3409_;
v___y_3519_ = v_a_3410_;
v___y_3520_ = v_a_3411_;
v___y_3521_ = v_a_3412_;
v___y_3522_ = v_a_3413_;
v___y_3523_ = v_a_3414_;
goto v___jp_3512_;
}
else
{
lean_object* v_inheritedTraceOptions_3532_; lean_object* v___x_3533_; lean_object* v___x_3534_; uint8_t v___x_3535_; 
v_inheritedTraceOptions_3532_ = lean_ctor_get(v_toCold_3529_, 11);
v___x_3533_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__1));
v___x_3534_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__2, &l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__2_once, _init_l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__2);
v___x_3535_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3532_, v_options_3530_, v___x_3534_);
if (v___x_3535_ == 0)
{
v___y_3513_ = v_val_3505_;
v___y_3514_ = v_a_3405_;
v___y_3515_ = v_a_3406_;
v___y_3516_ = v_a_3407_;
v___y_3517_ = v_a_3408_;
v___y_3518_ = v_a_3409_;
v___y_3519_ = v_a_3410_;
v___y_3520_ = v_a_3411_;
v___y_3521_ = v_a_3412_;
v___y_3522_ = v_a_3413_;
v___y_3523_ = v_a_3414_;
goto v___jp_3512_;
}
else
{
lean_object* v___x_3536_; 
v___x_3536_ = l_Lean_Meta_Grind_updateLastTag(v_a_3405_, v_a_3406_, v_a_3407_, v_a_3408_, v_a_3409_, v_a_3410_, v_a_3411_, v_a_3412_, v_a_3413_, v_a_3414_);
if (lean_obj_tag(v___x_3536_) == 0)
{
lean_object* v___x_3538_; uint8_t v_isShared_3539_; uint8_t v_isSharedCheck_3552_; 
v_isSharedCheck_3552_ = !lean_is_exclusive(v___x_3536_);
if (v_isSharedCheck_3552_ == 0)
{
lean_object* v_unused_3553_; 
v_unused_3553_ = lean_ctor_get(v___x_3536_, 0);
lean_dec(v_unused_3553_);
v___x_3538_ = v___x_3536_;
v_isShared_3539_ = v_isSharedCheck_3552_;
goto v_resetjp_3537_;
}
else
{
lean_dec(v___x_3536_);
v___x_3538_ = lean_box(0);
v_isShared_3539_ = v_isSharedCheck_3552_;
goto v_resetjp_3537_;
}
v_resetjp_3537_:
{
lean_object* v___x_3540_; lean_object* v___x_3541_; lean_object* v___x_3543_; 
v___x_3540_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__8, &l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__8_once, _init_l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__8);
lean_inc(v_val_3505_);
v___x_3541_ = l_Nat_reprFast(v_val_3505_);
if (v_isShared_3539_ == 0)
{
lean_ctor_set_tag(v___x_3538_, 3);
lean_ctor_set(v___x_3538_, 0, v___x_3541_);
v___x_3543_ = v___x_3538_;
goto v_reusejp_3542_;
}
else
{
lean_object* v_reuseFailAlloc_3551_; 
v_reuseFailAlloc_3551_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3551_, 0, v___x_3541_);
v___x_3543_ = v_reuseFailAlloc_3551_;
goto v_reusejp_3542_;
}
v_reusejp_3542_:
{
lean_object* v___x_3544_; lean_object* v___x_3545_; lean_object* v___x_3546_; lean_object* v___x_3547_; lean_object* v___x_3548_; lean_object* v___x_3549_; lean_object* v___x_3550_; 
v___x_3544_ = l_Lean_MessageData_ofFormat(v___x_3543_);
v___x_3545_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3545_, 0, v___x_3540_);
lean_ctor_set(v___x_3545_, 1, v___x_3544_);
v___x_3546_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__6, &l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__6_once, _init_l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__6);
v___x_3547_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3547_, 0, v___x_3545_);
lean_ctor_set(v___x_3547_, 1, v___x_3546_);
lean_inc_ref(v_e_3403_);
v___x_3548_ = l_Lean_MessageData_ofExpr(v_e_3403_);
v___x_3549_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3549_, 0, v___x_3547_);
lean_ctor_set(v___x_3549_, 1, v___x_3548_);
v___x_3550_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__1___redArg(v___x_3533_, v___x_3549_, v_a_3411_, v_a_3412_, v_a_3413_, v_a_3414_);
if (lean_obj_tag(v___x_3550_) == 0)
{
lean_dec_ref_known(v___x_3550_, 1);
v___y_3513_ = v_val_3505_;
v___y_3514_ = v_a_3405_;
v___y_3515_ = v_a_3406_;
v___y_3516_ = v_a_3407_;
v___y_3517_ = v_a_3408_;
v___y_3518_ = v_a_3409_;
v___y_3519_ = v_a_3410_;
v___y_3520_ = v_a_3411_;
v___y_3521_ = v_a_3412_;
v___y_3522_ = v_a_3413_;
v___y_3523_ = v_a_3414_;
goto v___jp_3512_;
}
else
{
lean_dec(v_val_3511_);
lean_dec(v_val_3505_);
lean_dec_ref(v_e_3403_);
return v___x_3550_;
}
}
}
}
else
{
lean_dec(v_val_3511_);
lean_dec(v_val_3505_);
lean_dec_ref(v_e_3403_);
return v___x_3536_;
}
}
}
v___jp_3512_:
{
lean_object* v___x_3524_; 
lean_inc_ref(v_e_3403_);
v___x_3524_ = l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg(v_e_3403_, v___y_3513_, v___y_3514_, v___y_3518_, v___y_3519_, v___y_3520_, v___y_3521_, v___y_3522_, v___y_3523_);
if (lean_obj_tag(v___x_3524_) == 0)
{
lean_object* v___x_3525_; lean_object* v___x_3526_; 
lean_dec_ref_known(v___x_3524_, 1);
v___x_3525_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
lean_inc_ref(v_e_3403_);
v___x_3526_ = l_Lean_Meta_Grind_SolverExtension_markTerm___redArg(v___x_3525_, v_e_3403_, v___y_3514_, v___y_3515_, v___y_3516_, v___y_3517_, v___y_3518_, v___y_3519_, v___y_3520_, v___y_3521_, v___y_3522_, v___y_3523_);
if (lean_obj_tag(v___x_3526_) == 0)
{
lean_object* v___f_3527_; lean_object* v___x_3528_; 
lean_dec_ref_known(v___x_3526_, 1);
v___f_3527_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_internalize___lam__1___boxed), 4, 3);
lean_closure_set(v___f_3527_, 0, v___y_3513_);
lean_closure_set(v___f_3527_, 1, v_e_3403_);
lean_closure_set(v___f_3527_, 2, v_val_3511_);
v___x_3528_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_3525_, v___f_3527_, v___y_3514_);
return v___x_3528_;
}
else
{
lean_dec(v___y_3513_);
lean_dec(v_val_3511_);
lean_dec_ref(v_e_3403_);
return v___x_3526_;
}
}
else
{
lean_dec(v___y_3513_);
lean_dec(v_val_3511_);
lean_dec_ref(v_e_3403_);
return v___x_3524_;
}
}
}
else
{
lean_object* v___x_3554_; lean_object* v___x_3556_; 
lean_dec(v_a_3507_);
lean_dec(v_val_3505_);
lean_dec_ref(v_e_3403_);
v___x_3554_ = lean_box(0);
if (v_isShared_3510_ == 0)
{
lean_ctor_set(v___x_3509_, 0, v___x_3554_);
v___x_3556_ = v___x_3509_;
goto v_reusejp_3555_;
}
else
{
lean_object* v_reuseFailAlloc_3557_; 
v_reuseFailAlloc_3557_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3557_, 0, v___x_3554_);
v___x_3556_ = v_reuseFailAlloc_3557_;
goto v_reusejp_3555_;
}
v_reusejp_3555_:
{
return v___x_3556_;
}
}
}
}
else
{
lean_object* v_a_3559_; lean_object* v___x_3561_; uint8_t v_isShared_3562_; uint8_t v_isSharedCheck_3566_; 
lean_dec(v_val_3505_);
lean_dec_ref(v_e_3403_);
v_a_3559_ = lean_ctor_get(v___x_3506_, 0);
v_isSharedCheck_3566_ = !lean_is_exclusive(v___x_3506_);
if (v_isSharedCheck_3566_ == 0)
{
v___x_3561_ = v___x_3506_;
v_isShared_3562_ = v_isSharedCheck_3566_;
goto v_resetjp_3560_;
}
else
{
lean_inc(v_a_3559_);
lean_dec(v___x_3506_);
v___x_3561_ = lean_box(0);
v_isShared_3562_ = v_isSharedCheck_3566_;
goto v_resetjp_3560_;
}
v_resetjp_3560_:
{
lean_object* v___x_3564_; 
if (v_isShared_3562_ == 0)
{
v___x_3564_ = v___x_3561_;
goto v_reusejp_3563_;
}
else
{
lean_object* v_reuseFailAlloc_3565_; 
v_reuseFailAlloc_3565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3565_, 0, v_a_3559_);
v___x_3564_ = v_reuseFailAlloc_3565_;
goto v_reusejp_3563_;
}
v_reusejp_3563_:
{
return v___x_3564_;
}
}
}
}
else
{
lean_object* v___x_3567_; 
lean_dec(v_a_3504_);
lean_inc(v_val_3434_);
v___x_3567_ = l_Lean_Meta_Grind_Arith_CommRing_getNonCommRingId_x3f(v_val_3434_, v_a_3405_, v_a_3406_, v_a_3407_, v_a_3408_, v_a_3409_, v_a_3410_, v_a_3411_, v_a_3412_, v_a_3413_, v_a_3414_);
if (lean_obj_tag(v___x_3567_) == 0)
{
lean_object* v_a_3568_; 
v_a_3568_ = lean_ctor_get(v___x_3567_, 0);
lean_inc(v_a_3568_);
lean_dec_ref_known(v___x_3567_, 1);
if (lean_obj_tag(v_a_3568_) == 1)
{
lean_object* v_val_3569_; lean_object* v___x_3570_; lean_object* v___x_3571_; 
lean_dec(v_val_3434_);
v_val_3569_ = lean_ctor_get(v_a_3568_, 0);
lean_inc(v_val_3569_);
lean_dec_ref_known(v_a_3568_, 1);
v___x_3570_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_e_3403_);
v___x_3571_ = l_Lean_Meta_Grind_Arith_CommRing_ncreify_x3f(v_e_3403_, v_ring_3421_, v___x_3570_, v_val_3569_, v_a_3405_, v_a_3406_, v_a_3407_, v_a_3408_, v_a_3409_, v_a_3410_, v_a_3411_, v_a_3412_, v_a_3413_, v_a_3414_);
if (lean_obj_tag(v___x_3571_) == 0)
{
lean_object* v_a_3572_; lean_object* v___x_3574_; uint8_t v_isShared_3575_; uint8_t v_isSharedCheck_3623_; 
v_a_3572_ = lean_ctor_get(v___x_3571_, 0);
v_isSharedCheck_3623_ = !lean_is_exclusive(v___x_3571_);
if (v_isSharedCheck_3623_ == 0)
{
v___x_3574_ = v___x_3571_;
v_isShared_3575_ = v_isSharedCheck_3623_;
goto v_resetjp_3573_;
}
else
{
lean_inc(v_a_3572_);
lean_dec(v___x_3571_);
v___x_3574_ = lean_box(0);
v_isShared_3575_ = v_isSharedCheck_3623_;
goto v_resetjp_3573_;
}
v_resetjp_3573_:
{
if (lean_obj_tag(v_a_3572_) == 1)
{
lean_object* v_toCold_3576_; lean_object* v_options_3577_; lean_object* v_val_3578_; lean_object* v_inheritedTraceOptions_3579_; uint8_t v_hasTrace_3580_; lean_object* v___f_3581_; lean_object* v___y_3583_; lean_object* v___y_3584_; lean_object* v___y_3585_; lean_object* v___y_3586_; lean_object* v___y_3587_; lean_object* v___y_3588_; lean_object* v___y_3589_; lean_object* v___y_3590_; lean_object* v___y_3591_; lean_object* v___y_3592_; lean_object* v___y_3593_; 
lean_del_object(v___x_3574_);
v_toCold_3576_ = lean_ctor_get(v_a_3413_, 0);
v_options_3577_ = lean_ctor_get(v_toCold_3576_, 2);
v_val_3578_ = lean_ctor_get(v_a_3572_, 0);
lean_inc(v_val_3578_);
lean_dec_ref_known(v_a_3572_, 1);
v_inheritedTraceOptions_3579_ = lean_ctor_get(v_toCold_3576_, 11);
v_hasTrace_3580_ = lean_ctor_get_uint8(v_options_3577_, sizeof(void*)*1);
lean_inc_ref(v_e_3403_);
v___f_3581_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_internalize___lam__2), 3, 2);
lean_closure_set(v___f_3581_, 0, v_e_3403_);
lean_closure_set(v___f_3581_, 1, v_val_3578_);
if (v_hasTrace_3580_ == 0)
{
v___y_3583_ = v_val_3569_;
v___y_3584_ = v_a_3405_;
v___y_3585_ = v_a_3406_;
v___y_3586_ = v_a_3407_;
v___y_3587_ = v_a_3408_;
v___y_3588_ = v_a_3409_;
v___y_3589_ = v_a_3410_;
v___y_3590_ = v_a_3411_;
v___y_3591_ = v_a_3412_;
v___y_3592_ = v_a_3413_;
v___y_3593_ = v_a_3414_;
goto v___jp_3582_;
}
else
{
lean_object* v___x_3598_; lean_object* v___x_3599_; uint8_t v___x_3600_; 
v___x_3598_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__1));
v___x_3599_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__2, &l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__2_once, _init_l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__2);
v___x_3600_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3579_, v_options_3577_, v___x_3599_);
if (v___x_3600_ == 0)
{
v___y_3583_ = v_val_3569_;
v___y_3584_ = v_a_3405_;
v___y_3585_ = v_a_3406_;
v___y_3586_ = v_a_3407_;
v___y_3587_ = v_a_3408_;
v___y_3588_ = v_a_3409_;
v___y_3589_ = v_a_3410_;
v___y_3590_ = v_a_3411_;
v___y_3591_ = v_a_3412_;
v___y_3592_ = v_a_3413_;
v___y_3593_ = v_a_3414_;
goto v___jp_3582_;
}
else
{
lean_object* v___x_3601_; 
v___x_3601_ = l_Lean_Meta_Grind_updateLastTag(v_a_3405_, v_a_3406_, v_a_3407_, v_a_3408_, v_a_3409_, v_a_3410_, v_a_3411_, v_a_3412_, v_a_3413_, v_a_3414_);
if (lean_obj_tag(v___x_3601_) == 0)
{
lean_object* v___x_3603_; uint8_t v_isShared_3604_; uint8_t v_isSharedCheck_3617_; 
v_isSharedCheck_3617_ = !lean_is_exclusive(v___x_3601_);
if (v_isSharedCheck_3617_ == 0)
{
lean_object* v_unused_3618_; 
v_unused_3618_ = lean_ctor_get(v___x_3601_, 0);
lean_dec(v_unused_3618_);
v___x_3603_ = v___x_3601_;
v_isShared_3604_ = v_isSharedCheck_3617_;
goto v_resetjp_3602_;
}
else
{
lean_dec(v___x_3601_);
v___x_3603_ = lean_box(0);
v_isShared_3604_ = v_isSharedCheck_3617_;
goto v_resetjp_3602_;
}
v_resetjp_3602_:
{
lean_object* v___x_3605_; lean_object* v___x_3606_; lean_object* v___x_3608_; 
v___x_3605_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__10, &l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__10_once, _init_l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__10);
lean_inc(v_val_3569_);
v___x_3606_ = l_Nat_reprFast(v_val_3569_);
if (v_isShared_3604_ == 0)
{
lean_ctor_set_tag(v___x_3603_, 3);
lean_ctor_set(v___x_3603_, 0, v___x_3606_);
v___x_3608_ = v___x_3603_;
goto v_reusejp_3607_;
}
else
{
lean_object* v_reuseFailAlloc_3616_; 
v_reuseFailAlloc_3616_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3616_, 0, v___x_3606_);
v___x_3608_ = v_reuseFailAlloc_3616_;
goto v_reusejp_3607_;
}
v_reusejp_3607_:
{
lean_object* v___x_3609_; lean_object* v___x_3610_; lean_object* v___x_3611_; lean_object* v___x_3612_; lean_object* v___x_3613_; lean_object* v___x_3614_; lean_object* v___x_3615_; 
v___x_3609_ = l_Lean_MessageData_ofFormat(v___x_3608_);
v___x_3610_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3610_, 0, v___x_3605_);
lean_ctor_set(v___x_3610_, 1, v___x_3609_);
v___x_3611_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__6, &l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__6_once, _init_l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__6);
v___x_3612_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3612_, 0, v___x_3610_);
lean_ctor_set(v___x_3612_, 1, v___x_3611_);
lean_inc_ref(v_e_3403_);
v___x_3613_ = l_Lean_MessageData_ofExpr(v_e_3403_);
v___x_3614_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3614_, 0, v___x_3612_);
lean_ctor_set(v___x_3614_, 1, v___x_3613_);
v___x_3615_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__2___redArg(v___x_3598_, v___x_3614_, v_a_3411_, v_a_3412_, v_a_3413_, v_a_3414_);
if (lean_obj_tag(v___x_3615_) == 0)
{
lean_dec_ref_known(v___x_3615_, 1);
v___y_3583_ = v_val_3569_;
v___y_3584_ = v_a_3405_;
v___y_3585_ = v_a_3406_;
v___y_3586_ = v_a_3407_;
v___y_3587_ = v_a_3408_;
v___y_3588_ = v_a_3409_;
v___y_3589_ = v_a_3410_;
v___y_3590_ = v_a_3411_;
v___y_3591_ = v_a_3412_;
v___y_3592_ = v_a_3413_;
v___y_3593_ = v_a_3414_;
goto v___jp_3582_;
}
else
{
lean_dec_ref(v___f_3581_);
lean_dec(v_val_3569_);
lean_dec_ref(v_e_3403_);
return v___x_3615_;
}
}
}
}
else
{
lean_dec_ref(v___f_3581_);
lean_dec(v_val_3569_);
lean_dec_ref(v_e_3403_);
return v___x_3601_;
}
}
}
v___jp_3582_:
{
lean_object* v___x_3594_; 
lean_inc_ref(v_e_3403_);
v___x_3594_ = l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId___redArg(v_e_3403_, v___y_3583_, v___y_3584_, v___y_3588_, v___y_3589_, v___y_3590_, v___y_3591_, v___y_3592_, v___y_3593_);
if (lean_obj_tag(v___x_3594_) == 0)
{
lean_object* v___x_3595_; lean_object* v___x_3596_; 
lean_dec_ref_known(v___x_3594_, 1);
v___x_3595_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_3596_ = l_Lean_Meta_Grind_SolverExtension_markTerm___redArg(v___x_3595_, v_e_3403_, v___y_3584_, v___y_3585_, v___y_3586_, v___y_3587_, v___y_3588_, v___y_3589_, v___y_3590_, v___y_3591_, v___y_3592_, v___y_3593_);
if (lean_obj_tag(v___x_3596_) == 0)
{
lean_object* v___x_3597_; 
lean_dec_ref_known(v___x_3596_, 1);
v___x_3597_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_modifyRing___redArg(v___f_3581_, v___y_3583_, v___y_3584_);
lean_dec(v___y_3583_);
return v___x_3597_;
}
else
{
lean_dec(v___y_3583_);
lean_dec_ref(v___f_3581_);
return v___x_3596_;
}
}
else
{
lean_dec(v___y_3583_);
lean_dec_ref(v___f_3581_);
lean_dec_ref(v_e_3403_);
return v___x_3594_;
}
}
}
else
{
lean_object* v___x_3619_; lean_object* v___x_3621_; 
lean_dec(v_a_3572_);
lean_dec(v_val_3569_);
lean_dec_ref(v_e_3403_);
v___x_3619_ = lean_box(0);
if (v_isShared_3575_ == 0)
{
lean_ctor_set(v___x_3574_, 0, v___x_3619_);
v___x_3621_ = v___x_3574_;
goto v_reusejp_3620_;
}
else
{
lean_object* v_reuseFailAlloc_3622_; 
v_reuseFailAlloc_3622_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3622_, 0, v___x_3619_);
v___x_3621_ = v_reuseFailAlloc_3622_;
goto v_reusejp_3620_;
}
v_reusejp_3620_:
{
return v___x_3621_;
}
}
}
}
else
{
lean_object* v_a_3624_; lean_object* v___x_3626_; uint8_t v_isShared_3627_; uint8_t v_isSharedCheck_3631_; 
lean_dec(v_val_3569_);
lean_dec_ref(v_e_3403_);
v_a_3624_ = lean_ctor_get(v___x_3571_, 0);
v_isSharedCheck_3631_ = !lean_is_exclusive(v___x_3571_);
if (v_isSharedCheck_3631_ == 0)
{
v___x_3626_ = v___x_3571_;
v_isShared_3627_ = v_isSharedCheck_3631_;
goto v_resetjp_3625_;
}
else
{
lean_inc(v_a_3624_);
lean_dec(v___x_3571_);
v___x_3626_ = lean_box(0);
v_isShared_3627_ = v_isSharedCheck_3631_;
goto v_resetjp_3625_;
}
v_resetjp_3625_:
{
lean_object* v___x_3629_; 
if (v_isShared_3627_ == 0)
{
v___x_3629_ = v___x_3626_;
goto v_reusejp_3628_;
}
else
{
lean_object* v_reuseFailAlloc_3630_; 
v_reuseFailAlloc_3630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3630_, 0, v_a_3624_);
v___x_3629_ = v_reuseFailAlloc_3630_;
goto v_reusejp_3628_;
}
v_reusejp_3628_:
{
return v___x_3629_;
}
}
}
}
else
{
lean_object* v___x_3632_; 
lean_dec(v_a_3568_);
v___x_3632_ = l_Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f___redArg(v_val_3434_, v_a_3405_, v_a_3410_, v_a_3411_, v_a_3412_, v_a_3413_, v_a_3414_);
if (lean_obj_tag(v___x_3632_) == 0)
{
lean_object* v_a_3633_; lean_object* v___x_3635_; uint8_t v_isShared_3636_; uint8_t v_isSharedCheck_3703_; 
v_a_3633_ = lean_ctor_get(v___x_3632_, 0);
v_isSharedCheck_3703_ = !lean_is_exclusive(v___x_3632_);
if (v_isSharedCheck_3703_ == 0)
{
v___x_3635_ = v___x_3632_;
v_isShared_3636_ = v_isSharedCheck_3703_;
goto v_resetjp_3634_;
}
else
{
lean_inc(v_a_3633_);
lean_dec(v___x_3632_);
v___x_3635_ = lean_box(0);
v_isShared_3636_ = v_isSharedCheck_3703_;
goto v_resetjp_3634_;
}
v_resetjp_3634_:
{
if (lean_obj_tag(v_a_3633_) == 1)
{
lean_object* v_val_3637_; lean_object* v___x_3638_; 
lean_del_object(v___x_3635_);
v_val_3637_ = lean_ctor_get(v_a_3633_, 0);
lean_inc(v_val_3637_);
lean_dec_ref_known(v_a_3633_, 1);
lean_inc_ref(v_e_3403_);
v___x_3638_ = l_Lean_Meta_Grind_Arith_CommRing_ncsreify_x3f(v_e_3403_, v_val_3637_, v_a_3405_, v_a_3406_, v_a_3407_, v_a_3408_, v_a_3409_, v_a_3410_, v_a_3411_, v_a_3412_, v_a_3413_, v_a_3414_);
if (lean_obj_tag(v___x_3638_) == 0)
{
lean_object* v_a_3639_; lean_object* v___x_3641_; uint8_t v_isShared_3642_; uint8_t v_isSharedCheck_3690_; 
v_a_3639_ = lean_ctor_get(v___x_3638_, 0);
v_isSharedCheck_3690_ = !lean_is_exclusive(v___x_3638_);
if (v_isSharedCheck_3690_ == 0)
{
v___x_3641_ = v___x_3638_;
v_isShared_3642_ = v_isSharedCheck_3690_;
goto v_resetjp_3640_;
}
else
{
lean_inc(v_a_3639_);
lean_dec(v___x_3638_);
v___x_3641_ = lean_box(0);
v_isShared_3642_ = v_isSharedCheck_3690_;
goto v_resetjp_3640_;
}
v_resetjp_3640_:
{
if (lean_obj_tag(v_a_3639_) == 1)
{
lean_object* v_toCold_3643_; lean_object* v_options_3644_; lean_object* v_val_3645_; lean_object* v_inheritedTraceOptions_3646_; uint8_t v_hasTrace_3647_; lean_object* v___f_3648_; lean_object* v___y_3650_; lean_object* v___y_3651_; lean_object* v___y_3652_; lean_object* v___y_3653_; lean_object* v___y_3654_; lean_object* v___y_3655_; lean_object* v___y_3656_; lean_object* v___y_3657_; lean_object* v___y_3658_; lean_object* v___y_3659_; lean_object* v___y_3660_; 
lean_del_object(v___x_3641_);
v_toCold_3643_ = lean_ctor_get(v_a_3413_, 0);
v_options_3644_ = lean_ctor_get(v_toCold_3643_, 2);
v_val_3645_ = lean_ctor_get(v_a_3639_, 0);
lean_inc(v_val_3645_);
lean_dec_ref_known(v_a_3639_, 1);
v_inheritedTraceOptions_3646_ = lean_ctor_get(v_toCold_3643_, 11);
v_hasTrace_3647_ = lean_ctor_get_uint8(v_options_3644_, sizeof(void*)*1);
lean_inc_ref(v_e_3403_);
v___f_3648_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_internalize___lam__3), 3, 2);
lean_closure_set(v___f_3648_, 0, v_e_3403_);
lean_closure_set(v___f_3648_, 1, v_val_3645_);
if (v_hasTrace_3647_ == 0)
{
v___y_3650_ = v_val_3637_;
v___y_3651_ = v_a_3405_;
v___y_3652_ = v_a_3406_;
v___y_3653_ = v_a_3407_;
v___y_3654_ = v_a_3408_;
v___y_3655_ = v_a_3409_;
v___y_3656_ = v_a_3410_;
v___y_3657_ = v_a_3411_;
v___y_3658_ = v_a_3412_;
v___y_3659_ = v_a_3413_;
v___y_3660_ = v_a_3414_;
goto v___jp_3649_;
}
else
{
lean_object* v___x_3665_; lean_object* v___x_3666_; uint8_t v___x_3667_; 
v___x_3665_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__1));
v___x_3666_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__2, &l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__2_once, _init_l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__2);
v___x_3667_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3646_, v_options_3644_, v___x_3666_);
if (v___x_3667_ == 0)
{
v___y_3650_ = v_val_3637_;
v___y_3651_ = v_a_3405_;
v___y_3652_ = v_a_3406_;
v___y_3653_ = v_a_3407_;
v___y_3654_ = v_a_3408_;
v___y_3655_ = v_a_3409_;
v___y_3656_ = v_a_3410_;
v___y_3657_ = v_a_3411_;
v___y_3658_ = v_a_3412_;
v___y_3659_ = v_a_3413_;
v___y_3660_ = v_a_3414_;
goto v___jp_3649_;
}
else
{
lean_object* v___x_3668_; 
v___x_3668_ = l_Lean_Meta_Grind_updateLastTag(v_a_3405_, v_a_3406_, v_a_3407_, v_a_3408_, v_a_3409_, v_a_3410_, v_a_3411_, v_a_3412_, v_a_3413_, v_a_3414_);
if (lean_obj_tag(v___x_3668_) == 0)
{
lean_object* v___x_3670_; uint8_t v_isShared_3671_; uint8_t v_isSharedCheck_3684_; 
v_isSharedCheck_3684_ = !lean_is_exclusive(v___x_3668_);
if (v_isSharedCheck_3684_ == 0)
{
lean_object* v_unused_3685_; 
v_unused_3685_ = lean_ctor_get(v___x_3668_, 0);
lean_dec(v_unused_3685_);
v___x_3670_ = v___x_3668_;
v_isShared_3671_ = v_isSharedCheck_3684_;
goto v_resetjp_3669_;
}
else
{
lean_dec(v___x_3668_);
v___x_3670_ = lean_box(0);
v_isShared_3671_ = v_isSharedCheck_3684_;
goto v_resetjp_3669_;
}
v_resetjp_3669_:
{
lean_object* v___x_3672_; lean_object* v___x_3673_; lean_object* v___x_3675_; 
v___x_3672_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__12, &l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__12_once, _init_l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__12);
lean_inc(v_val_3637_);
v___x_3673_ = l_Nat_reprFast(v_val_3637_);
if (v_isShared_3671_ == 0)
{
lean_ctor_set_tag(v___x_3670_, 3);
lean_ctor_set(v___x_3670_, 0, v___x_3673_);
v___x_3675_ = v___x_3670_;
goto v_reusejp_3674_;
}
else
{
lean_object* v_reuseFailAlloc_3683_; 
v_reuseFailAlloc_3683_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3683_, 0, v___x_3673_);
v___x_3675_ = v_reuseFailAlloc_3683_;
goto v_reusejp_3674_;
}
v_reusejp_3674_:
{
lean_object* v___x_3676_; lean_object* v___x_3677_; lean_object* v___x_3678_; lean_object* v___x_3679_; lean_object* v___x_3680_; lean_object* v___x_3681_; lean_object* v___x_3682_; 
v___x_3676_ = l_Lean_MessageData_ofFormat(v___x_3675_);
v___x_3677_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3677_, 0, v___x_3672_);
lean_ctor_set(v___x_3677_, 1, v___x_3676_);
v___x_3678_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__6, &l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__6_once, _init_l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__6);
v___x_3679_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3679_, 0, v___x_3677_);
lean_ctor_set(v___x_3679_, 1, v___x_3678_);
lean_inc_ref(v_e_3403_);
v___x_3680_ = l_Lean_MessageData_ofExpr(v_e_3403_);
v___x_3681_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3681_, 0, v___x_3679_);
lean_ctor_set(v___x_3681_, 1, v___x_3680_);
v___x_3682_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__3___redArg(v___x_3665_, v___x_3681_, v_a_3411_, v_a_3412_, v_a_3413_, v_a_3414_);
if (lean_obj_tag(v___x_3682_) == 0)
{
lean_dec_ref_known(v___x_3682_, 1);
v___y_3650_ = v_val_3637_;
v___y_3651_ = v_a_3405_;
v___y_3652_ = v_a_3406_;
v___y_3653_ = v_a_3407_;
v___y_3654_ = v_a_3408_;
v___y_3655_ = v_a_3409_;
v___y_3656_ = v_a_3410_;
v___y_3657_ = v_a_3411_;
v___y_3658_ = v_a_3412_;
v___y_3659_ = v_a_3413_;
v___y_3660_ = v_a_3414_;
goto v___jp_3649_;
}
else
{
lean_dec_ref(v___f_3648_);
lean_dec(v_val_3637_);
lean_dec_ref(v_e_3403_);
return v___x_3682_;
}
}
}
}
else
{
lean_dec_ref(v___f_3648_);
lean_dec(v_val_3637_);
lean_dec_ref(v_e_3403_);
return v___x_3668_;
}
}
}
v___jp_3649_:
{
lean_object* v___x_3661_; 
lean_inc_ref(v_e_3403_);
v___x_3661_ = l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId___redArg(v_e_3403_, v___y_3650_, v___y_3651_, v___y_3655_, v___y_3656_, v___y_3657_, v___y_3658_, v___y_3659_, v___y_3660_);
if (lean_obj_tag(v___x_3661_) == 0)
{
lean_object* v___x_3662_; lean_object* v___x_3663_; 
lean_dec_ref_known(v___x_3661_, 1);
v___x_3662_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_3663_ = l_Lean_Meta_Grind_SolverExtension_markTerm___redArg(v___x_3662_, v_e_3403_, v___y_3651_, v___y_3652_, v___y_3653_, v___y_3654_, v___y_3655_, v___y_3656_, v___y_3657_, v___y_3658_, v___y_3659_, v___y_3660_);
if (lean_obj_tag(v___x_3663_) == 0)
{
lean_object* v___x_3664_; 
lean_dec_ref_known(v___x_3663_, 1);
v___x_3664_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_modifySemiring___redArg(v___f_3648_, v___y_3650_, v___y_3651_);
lean_dec(v___y_3650_);
return v___x_3664_;
}
else
{
lean_dec(v___y_3650_);
lean_dec_ref(v___f_3648_);
return v___x_3663_;
}
}
else
{
lean_dec(v___y_3650_);
lean_dec_ref(v___f_3648_);
lean_dec_ref(v_e_3403_);
return v___x_3661_;
}
}
}
else
{
lean_object* v___x_3686_; lean_object* v___x_3688_; 
lean_dec(v_a_3639_);
lean_dec(v_val_3637_);
lean_dec_ref(v_e_3403_);
v___x_3686_ = lean_box(0);
if (v_isShared_3642_ == 0)
{
lean_ctor_set(v___x_3641_, 0, v___x_3686_);
v___x_3688_ = v___x_3641_;
goto v_reusejp_3687_;
}
else
{
lean_object* v_reuseFailAlloc_3689_; 
v_reuseFailAlloc_3689_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3689_, 0, v___x_3686_);
v___x_3688_ = v_reuseFailAlloc_3689_;
goto v_reusejp_3687_;
}
v_reusejp_3687_:
{
return v___x_3688_;
}
}
}
}
else
{
lean_object* v_a_3691_; lean_object* v___x_3693_; uint8_t v_isShared_3694_; uint8_t v_isSharedCheck_3698_; 
lean_dec(v_val_3637_);
lean_dec_ref(v_e_3403_);
v_a_3691_ = lean_ctor_get(v___x_3638_, 0);
v_isSharedCheck_3698_ = !lean_is_exclusive(v___x_3638_);
if (v_isSharedCheck_3698_ == 0)
{
v___x_3693_ = v___x_3638_;
v_isShared_3694_ = v_isSharedCheck_3698_;
goto v_resetjp_3692_;
}
else
{
lean_inc(v_a_3691_);
lean_dec(v___x_3638_);
v___x_3693_ = lean_box(0);
v_isShared_3694_ = v_isSharedCheck_3698_;
goto v_resetjp_3692_;
}
v_resetjp_3692_:
{
lean_object* v___x_3696_; 
if (v_isShared_3694_ == 0)
{
v___x_3696_ = v___x_3693_;
goto v_reusejp_3695_;
}
else
{
lean_object* v_reuseFailAlloc_3697_; 
v_reuseFailAlloc_3697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3697_, 0, v_a_3691_);
v___x_3696_ = v_reuseFailAlloc_3697_;
goto v_reusejp_3695_;
}
v_reusejp_3695_:
{
return v___x_3696_;
}
}
}
}
else
{
lean_object* v___x_3699_; lean_object* v___x_3701_; 
lean_dec(v_a_3633_);
lean_dec_ref(v_e_3403_);
v___x_3699_ = lean_box(0);
if (v_isShared_3636_ == 0)
{
lean_ctor_set(v___x_3635_, 0, v___x_3699_);
v___x_3701_ = v___x_3635_;
goto v_reusejp_3700_;
}
else
{
lean_object* v_reuseFailAlloc_3702_; 
v_reuseFailAlloc_3702_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3702_, 0, v___x_3699_);
v___x_3701_ = v_reuseFailAlloc_3702_;
goto v_reusejp_3700_;
}
v_reusejp_3700_:
{
return v___x_3701_;
}
}
}
}
else
{
lean_object* v_a_3704_; lean_object* v___x_3706_; uint8_t v_isShared_3707_; uint8_t v_isSharedCheck_3711_; 
lean_dec_ref(v_e_3403_);
v_a_3704_ = lean_ctor_get(v___x_3632_, 0);
v_isSharedCheck_3711_ = !lean_is_exclusive(v___x_3632_);
if (v_isSharedCheck_3711_ == 0)
{
v___x_3706_ = v___x_3632_;
v_isShared_3707_ = v_isSharedCheck_3711_;
goto v_resetjp_3705_;
}
else
{
lean_inc(v_a_3704_);
lean_dec(v___x_3632_);
v___x_3706_ = lean_box(0);
v_isShared_3707_ = v_isSharedCheck_3711_;
goto v_resetjp_3705_;
}
v_resetjp_3705_:
{
lean_object* v___x_3709_; 
if (v_isShared_3707_ == 0)
{
v___x_3709_ = v___x_3706_;
goto v_reusejp_3708_;
}
else
{
lean_object* v_reuseFailAlloc_3710_; 
v_reuseFailAlloc_3710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3710_, 0, v_a_3704_);
v___x_3709_ = v_reuseFailAlloc_3710_;
goto v_reusejp_3708_;
}
v_reusejp_3708_:
{
return v___x_3709_;
}
}
}
}
}
else
{
lean_object* v_a_3712_; lean_object* v___x_3714_; uint8_t v_isShared_3715_; uint8_t v_isSharedCheck_3719_; 
lean_dec(v_val_3434_);
lean_dec_ref(v_e_3403_);
v_a_3712_ = lean_ctor_get(v___x_3567_, 0);
v_isSharedCheck_3719_ = !lean_is_exclusive(v___x_3567_);
if (v_isSharedCheck_3719_ == 0)
{
v___x_3714_ = v___x_3567_;
v_isShared_3715_ = v_isSharedCheck_3719_;
goto v_resetjp_3713_;
}
else
{
lean_inc(v_a_3712_);
lean_dec(v___x_3567_);
v___x_3714_ = lean_box(0);
v_isShared_3715_ = v_isSharedCheck_3719_;
goto v_resetjp_3713_;
}
v_resetjp_3713_:
{
lean_object* v___x_3717_; 
if (v_isShared_3715_ == 0)
{
v___x_3717_ = v___x_3714_;
goto v_reusejp_3716_;
}
else
{
lean_object* v_reuseFailAlloc_3718_; 
v_reuseFailAlloc_3718_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3718_, 0, v_a_3712_);
v___x_3717_ = v_reuseFailAlloc_3718_;
goto v_reusejp_3716_;
}
v_reusejp_3716_:
{
return v___x_3717_;
}
}
}
}
}
else
{
lean_object* v_a_3720_; lean_object* v___x_3722_; uint8_t v_isShared_3723_; uint8_t v_isSharedCheck_3727_; 
lean_dec(v_val_3434_);
lean_dec_ref(v_e_3403_);
v_a_3720_ = lean_ctor_get(v___x_3503_, 0);
v_isSharedCheck_3727_ = !lean_is_exclusive(v___x_3503_);
if (v_isSharedCheck_3727_ == 0)
{
v___x_3722_ = v___x_3503_;
v_isShared_3723_ = v_isSharedCheck_3727_;
goto v_resetjp_3721_;
}
else
{
lean_inc(v_a_3720_);
lean_dec(v___x_3503_);
v___x_3722_ = lean_box(0);
v_isShared_3723_ = v_isSharedCheck_3727_;
goto v_resetjp_3721_;
}
v_resetjp_3721_:
{
lean_object* v___x_3725_; 
if (v_isShared_3723_ == 0)
{
v___x_3725_ = v___x_3722_;
goto v_reusejp_3724_;
}
else
{
lean_object* v_reuseFailAlloc_3726_; 
v_reuseFailAlloc_3726_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3726_, 0, v_a_3720_);
v___x_3725_ = v_reuseFailAlloc_3726_;
goto v_reusejp_3724_;
}
v_reusejp_3724_:
{
return v___x_3725_;
}
}
}
}
}
else
{
lean_object* v_a_3728_; lean_object* v___x_3730_; uint8_t v_isShared_3731_; uint8_t v_isSharedCheck_3735_; 
lean_dec(v_val_3434_);
lean_dec_ref(v_e_3403_);
v_a_3728_ = lean_ctor_get(v___x_3436_, 0);
v_isSharedCheck_3735_ = !lean_is_exclusive(v___x_3436_);
if (v_isSharedCheck_3735_ == 0)
{
v___x_3730_ = v___x_3436_;
v_isShared_3731_ = v_isSharedCheck_3735_;
goto v_resetjp_3729_;
}
else
{
lean_inc(v_a_3728_);
lean_dec(v___x_3436_);
v___x_3730_ = lean_box(0);
v_isShared_3731_ = v_isSharedCheck_3735_;
goto v_resetjp_3729_;
}
v_resetjp_3729_:
{
lean_object* v___x_3733_; 
if (v_isShared_3731_ == 0)
{
v___x_3733_ = v___x_3730_;
goto v_reusejp_3732_;
}
else
{
lean_object* v_reuseFailAlloc_3734_; 
v_reuseFailAlloc_3734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3734_, 0, v_a_3728_);
v___x_3733_ = v_reuseFailAlloc_3734_;
goto v_reusejp_3732_;
}
v_reusejp_3732_:
{
return v___x_3733_;
}
}
}
}
else
{
lean_object* v___x_3736_; lean_object* v___x_3738_; 
lean_dec(v_val_3434_);
lean_dec_ref(v_e_3403_);
v___x_3736_ = lean_box(0);
if (v_isShared_3431_ == 0)
{
lean_ctor_set(v___x_3430_, 0, v___x_3736_);
v___x_3738_ = v___x_3430_;
goto v_reusejp_3737_;
}
else
{
lean_object* v_reuseFailAlloc_3739_; 
v_reuseFailAlloc_3739_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3739_, 0, v___x_3736_);
v___x_3738_ = v_reuseFailAlloc_3739_;
goto v_reusejp_3737_;
}
v_reusejp_3737_:
{
return v___x_3738_;
}
}
}
else
{
lean_object* v___x_3740_; lean_object* v___x_3742_; 
lean_dec(v___x_3433_);
lean_dec(v_parent_x3f_3404_);
lean_dec_ref(v_e_3403_);
v___x_3740_ = lean_box(0);
if (v_isShared_3431_ == 0)
{
lean_ctor_set(v___x_3430_, 0, v___x_3740_);
v___x_3742_ = v___x_3430_;
goto v_reusejp_3741_;
}
else
{
lean_object* v_reuseFailAlloc_3743_; 
v_reuseFailAlloc_3743_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3743_, 0, v___x_3740_);
v___x_3742_ = v_reuseFailAlloc_3743_;
goto v_reusejp_3741_;
}
v_reusejp_3741_:
{
return v___x_3742_;
}
}
}
else
{
lean_object* v___x_3744_; lean_object* v___x_3746_; 
lean_dec(v_parent_x3f_3404_);
lean_dec_ref(v_e_3403_);
v___x_3744_ = lean_box(0);
if (v_isShared_3431_ == 0)
{
lean_ctor_set(v___x_3430_, 0, v___x_3744_);
v___x_3746_ = v___x_3430_;
goto v_reusejp_3745_;
}
else
{
lean_object* v_reuseFailAlloc_3747_; 
v_reuseFailAlloc_3747_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3747_, 0, v___x_3744_);
v___x_3746_ = v_reuseFailAlloc_3747_;
goto v_reusejp_3745_;
}
v_reusejp_3745_:
{
return v___x_3746_;
}
}
}
}
else
{
lean_object* v_a_3749_; lean_object* v___x_3751_; uint8_t v_isShared_3752_; uint8_t v_isSharedCheck_3756_; 
lean_dec(v_parent_x3f_3404_);
lean_dec_ref(v_e_3403_);
v_a_3749_ = lean_ctor_get(v___x_3427_, 0);
v_isSharedCheck_3756_ = !lean_is_exclusive(v___x_3427_);
if (v_isSharedCheck_3756_ == 0)
{
v___x_3751_ = v___x_3427_;
v_isShared_3752_ = v_isSharedCheck_3756_;
goto v_resetjp_3750_;
}
else
{
lean_inc(v_a_3749_);
lean_dec(v___x_3427_);
v___x_3751_ = lean_box(0);
v_isShared_3752_ = v_isSharedCheck_3756_;
goto v_resetjp_3750_;
}
v_resetjp_3750_:
{
lean_object* v___x_3754_; 
if (v_isShared_3752_ == 0)
{
v___x_3754_ = v___x_3751_;
goto v_reusejp_3753_;
}
else
{
lean_object* v_reuseFailAlloc_3755_; 
v_reuseFailAlloc_3755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3755_, 0, v_a_3749_);
v___x_3754_ = v_reuseFailAlloc_3755_;
goto v_reusejp_3753_;
}
v_reusejp_3753_:
{
return v___x_3754_;
}
}
}
}
else
{
lean_object* v___x_3757_; lean_object* v___x_3759_; 
lean_dec(v_parent_x3f_3404_);
lean_dec_ref(v_e_3403_);
v___x_3757_ = lean_box(0);
if (v_isShared_3420_ == 0)
{
lean_ctor_set(v___x_3419_, 0, v___x_3757_);
v___x_3759_ = v___x_3419_;
goto v_reusejp_3758_;
}
else
{
lean_object* v_reuseFailAlloc_3760_; 
v_reuseFailAlloc_3760_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3760_, 0, v___x_3757_);
v___x_3759_ = v_reuseFailAlloc_3760_;
goto v_reusejp_3758_;
}
v_reusejp_3758_:
{
return v___x_3759_;
}
}
}
}
}
else
{
lean_object* v_a_3762_; lean_object* v___x_3764_; uint8_t v_isShared_3765_; uint8_t v_isSharedCheck_3769_; 
lean_dec(v_parent_x3f_3404_);
lean_dec_ref(v_e_3403_);
v_a_3762_ = lean_ctor_get(v___x_3416_, 0);
v_isSharedCheck_3769_ = !lean_is_exclusive(v___x_3416_);
if (v_isSharedCheck_3769_ == 0)
{
v___x_3764_ = v___x_3416_;
v_isShared_3765_ = v_isSharedCheck_3769_;
goto v_resetjp_3763_;
}
else
{
lean_inc(v_a_3762_);
lean_dec(v___x_3416_);
v___x_3764_ = lean_box(0);
v_isShared_3765_ = v_isSharedCheck_3769_;
goto v_resetjp_3763_;
}
v_resetjp_3763_:
{
lean_object* v___x_3767_; 
if (v_isShared_3765_ == 0)
{
v___x_3767_ = v___x_3764_;
goto v_reusejp_3766_;
}
else
{
lean_object* v_reuseFailAlloc_3768_; 
v_reuseFailAlloc_3768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3768_, 0, v_a_3762_);
v___x_3767_ = v_reuseFailAlloc_3768_;
goto v_reusejp_3766_;
}
v_reusejp_3766_:
{
return v___x_3767_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_internalize___boxed(lean_object* v_e_3770_, lean_object* v_parent_x3f_3771_, lean_object* v_a_3772_, lean_object* v_a_3773_, lean_object* v_a_3774_, lean_object* v_a_3775_, lean_object* v_a_3776_, lean_object* v_a_3777_, lean_object* v_a_3778_, lean_object* v_a_3779_, lean_object* v_a_3780_, lean_object* v_a_3781_, lean_object* v_a_3782_){
_start:
{
lean_object* v_res_3783_; 
v_res_3783_ = l_Lean_Meta_Grind_Arith_CommRing_internalize(v_e_3770_, v_parent_x3f_3771_, v_a_3772_, v_a_3773_, v_a_3774_, v_a_3775_, v_a_3776_, v_a_3777_, v_a_3778_, v_a_3779_, v_a_3780_, v_a_3781_);
lean_dec(v_a_3781_);
lean_dec_ref(v_a_3780_);
lean_dec(v_a_3779_);
lean_dec_ref(v_a_3778_);
lean_dec(v_a_3777_);
lean_dec_ref(v_a_3776_);
lean_dec(v_a_3775_);
lean_dec_ref(v_a_3774_);
lean_dec(v_a_3773_);
lean_dec(v_a_3772_);
return v_res_3783_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0(lean_object* v_00_u03b2_3784_, lean_object* v_x_3785_, lean_object* v_x_3786_, lean_object* v_x_3787_){
_start:
{
lean_object* v___x_3788_; 
v___x_3788_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0___redArg(v_x_3785_, v_x_3786_, v_x_3787_);
return v___x_3788_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__1(lean_object* v_cls_3789_, lean_object* v_msg_3790_, lean_object* v___y_3791_, lean_object* v___y_3792_, lean_object* v___y_3793_, lean_object* v___y_3794_, lean_object* v___y_3795_, lean_object* v___y_3796_, lean_object* v___y_3797_, lean_object* v___y_3798_, lean_object* v___y_3799_, lean_object* v___y_3800_, lean_object* v___y_3801_){
_start:
{
lean_object* v___x_3803_; 
v___x_3803_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__1___redArg(v_cls_3789_, v_msg_3790_, v___y_3798_, v___y_3799_, v___y_3800_, v___y_3801_);
return v___x_3803_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__1___boxed(lean_object* v_cls_3804_, lean_object* v_msg_3805_, lean_object* v___y_3806_, lean_object* v___y_3807_, lean_object* v___y_3808_, lean_object* v___y_3809_, lean_object* v___y_3810_, lean_object* v___y_3811_, lean_object* v___y_3812_, lean_object* v___y_3813_, lean_object* v___y_3814_, lean_object* v___y_3815_, lean_object* v___y_3816_, lean_object* v___y_3817_){
_start:
{
lean_object* v_res_3818_; 
v_res_3818_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__1(v_cls_3804_, v_msg_3805_, v___y_3806_, v___y_3807_, v___y_3808_, v___y_3809_, v___y_3810_, v___y_3811_, v___y_3812_, v___y_3813_, v___y_3814_, v___y_3815_, v___y_3816_);
lean_dec(v___y_3816_);
lean_dec_ref(v___y_3815_);
lean_dec(v___y_3814_);
lean_dec_ref(v___y_3813_);
lean_dec(v___y_3812_);
lean_dec_ref(v___y_3811_);
lean_dec(v___y_3810_);
lean_dec_ref(v___y_3809_);
lean_dec(v___y_3808_);
lean_dec(v___y_3807_);
lean_dec(v___y_3806_);
return v_res_3818_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__2(lean_object* v_cls_3819_, lean_object* v_msg_3820_, lean_object* v___y_3821_, lean_object* v___y_3822_, lean_object* v___y_3823_, lean_object* v___y_3824_, lean_object* v___y_3825_, lean_object* v___y_3826_, lean_object* v___y_3827_, lean_object* v___y_3828_, lean_object* v___y_3829_, lean_object* v___y_3830_, lean_object* v___y_3831_){
_start:
{
lean_object* v___x_3833_; 
v___x_3833_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__2___redArg(v_cls_3819_, v_msg_3820_, v___y_3828_, v___y_3829_, v___y_3830_, v___y_3831_);
return v___x_3833_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__2___boxed(lean_object* v_cls_3834_, lean_object* v_msg_3835_, lean_object* v___y_3836_, lean_object* v___y_3837_, lean_object* v___y_3838_, lean_object* v___y_3839_, lean_object* v___y_3840_, lean_object* v___y_3841_, lean_object* v___y_3842_, lean_object* v___y_3843_, lean_object* v___y_3844_, lean_object* v___y_3845_, lean_object* v___y_3846_, lean_object* v___y_3847_){
_start:
{
lean_object* v_res_3848_; 
v_res_3848_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__2(v_cls_3834_, v_msg_3835_, v___y_3836_, v___y_3837_, v___y_3838_, v___y_3839_, v___y_3840_, v___y_3841_, v___y_3842_, v___y_3843_, v___y_3844_, v___y_3845_, v___y_3846_);
lean_dec(v___y_3846_);
lean_dec_ref(v___y_3845_);
lean_dec(v___y_3844_);
lean_dec_ref(v___y_3843_);
lean_dec(v___y_3842_);
lean_dec_ref(v___y_3841_);
lean_dec(v___y_3840_);
lean_dec_ref(v___y_3839_);
lean_dec(v___y_3838_);
lean_dec(v___y_3837_);
lean_dec(v___y_3836_);
return v_res_3848_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__3(lean_object* v_cls_3849_, lean_object* v_msg_3850_, lean_object* v___y_3851_, lean_object* v___y_3852_, lean_object* v___y_3853_, lean_object* v___y_3854_, lean_object* v___y_3855_, lean_object* v___y_3856_, lean_object* v___y_3857_, lean_object* v___y_3858_, lean_object* v___y_3859_, lean_object* v___y_3860_, lean_object* v___y_3861_){
_start:
{
lean_object* v___x_3863_; 
v___x_3863_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__3___redArg(v_cls_3849_, v_msg_3850_, v___y_3858_, v___y_3859_, v___y_3860_, v___y_3861_);
return v___x_3863_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__3___boxed(lean_object* v_cls_3864_, lean_object* v_msg_3865_, lean_object* v___y_3866_, lean_object* v___y_3867_, lean_object* v___y_3868_, lean_object* v___y_3869_, lean_object* v___y_3870_, lean_object* v___y_3871_, lean_object* v___y_3872_, lean_object* v___y_3873_, lean_object* v___y_3874_, lean_object* v___y_3875_, lean_object* v___y_3876_, lean_object* v___y_3877_){
_start:
{
lean_object* v_res_3878_; 
v_res_3878_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__3(v_cls_3864_, v_msg_3865_, v___y_3866_, v___y_3867_, v___y_3868_, v___y_3869_, v___y_3870_, v___y_3871_, v___y_3872_, v___y_3873_, v___y_3874_, v___y_3875_, v___y_3876_);
lean_dec(v___y_3876_);
lean_dec_ref(v___y_3875_);
lean_dec(v___y_3874_);
lean_dec_ref(v___y_3873_);
lean_dec(v___y_3872_);
lean_dec_ref(v___y_3871_);
lean_dec(v___y_3870_);
lean_dec_ref(v___y_3869_);
lean_dec(v___y_3868_);
lean_dec(v___y_3867_);
lean_dec(v___y_3866_);
return v_res_3878_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0(lean_object* v_00_u03b2_3879_, lean_object* v_x_3880_, size_t v_x_3881_, size_t v_x_3882_, lean_object* v_x_3883_, lean_object* v_x_3884_){
_start:
{
lean_object* v___x_3885_; 
v___x_3885_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0___redArg(v_x_3880_, v_x_3881_, v_x_3882_, v_x_3883_, v_x_3884_);
return v___x_3885_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3886_, lean_object* v_x_3887_, lean_object* v_x_3888_, lean_object* v_x_3889_, lean_object* v_x_3890_, lean_object* v_x_3891_){
_start:
{
size_t v_x_152738__boxed_3892_; size_t v_x_152739__boxed_3893_; lean_object* v_res_3894_; 
v_x_152738__boxed_3892_ = lean_unbox_usize(v_x_3888_);
lean_dec(v_x_3888_);
v_x_152739__boxed_3893_ = lean_unbox_usize(v_x_3889_);
lean_dec(v_x_3889_);
v_res_3894_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0(v_00_u03b2_3886_, v_x_3887_, v_x_152738__boxed_3892_, v_x_152739__boxed_3893_, v_x_3890_, v_x_3891_);
return v_res_3894_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_3895_, lean_object* v_n_3896_, lean_object* v_k_3897_, lean_object* v_v_3898_){
_start:
{
lean_object* v___x_3899_; 
v___x_3899_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0_spec__1___redArg(v_n_3896_, v_k_3897_, v_v_3898_);
return v___x_3899_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_3900_, size_t v_depth_3901_, lean_object* v_keys_3902_, lean_object* v_vals_3903_, lean_object* v_heq_3904_, lean_object* v_i_3905_, lean_object* v_entries_3906_){
_start:
{
lean_object* v___x_3907_; 
v___x_3907_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0_spec__2___redArg(v_depth_3901_, v_keys_3902_, v_vals_3903_, v_i_3905_, v_entries_3906_);
return v___x_3907_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_3908_, lean_object* v_depth_3909_, lean_object* v_keys_3910_, lean_object* v_vals_3911_, lean_object* v_heq_3912_, lean_object* v_i_3913_, lean_object* v_entries_3914_){
_start:
{
size_t v_depth_boxed_3915_; lean_object* v_res_3916_; 
v_depth_boxed_3915_ = lean_unbox_usize(v_depth_3909_);
lean_dec(v_depth_3909_);
v_res_3916_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0_spec__2(v_00_u03b2_3908_, v_depth_boxed_3915_, v_keys_3910_, v_vals_3911_, v_heq_3912_, v_i_3913_, v_entries_3914_);
lean_dec_ref(v_vals_3911_);
lean_dec_ref(v_keys_3910_);
return v_res_3916_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0_spec__1_spec__5(lean_object* v_00_u03b2_3917_, lean_object* v_x_3918_, lean_object* v_x_3919_, lean_object* v_x_3920_, lean_object* v_x_3921_){
_start:
{
lean_object* v___x_3922_; 
v___x_3922_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0_spec__1_spec__5___redArg(v_x_3918_, v_x_3919_, v_x_3920_, v_x_3921_);
return v___x_3922_;
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
