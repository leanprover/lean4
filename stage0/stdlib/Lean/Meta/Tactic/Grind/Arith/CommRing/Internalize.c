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
size_t lean_ptr_addr(lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
uint64_t lean_usize_to_uint64(size_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
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
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_synthInstance_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_canon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_Meta_getNatValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_int_neg(lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_pushNewFact(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRingState___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRingState___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_hasChar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_getCharInst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_int_emod(lean_object*, lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
lean_object* l_Lean_mkRawNatLit(lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
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
lean_object* l_Lean_Meta_Grind_Arith_CommRing_reify_x3f(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_sreify_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifySemiringState___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNonCommRingId_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_ncreify_x3f(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_modifyRingState___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_ncsreify_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_modifySemiringState___redArg(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__2_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__2_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__2_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "failed to find instance"};
static const lean_object* l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__2_spec__3___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__2_spec__3___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__2_spec__3___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__2_spec__3___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__2___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0___lam__0(lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0___closed__0_value;
static const lean_string_object l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Grind"};
static const lean_object* l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0___closed__1_value;
static const lean_string_object l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Ring"};
static const lean_object* l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0___closed__2 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0___closed__2_value;
static const lean_string_object l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "toNeg"};
static const lean_object* l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0___closed__3 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0___closed__3_value;
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0___closed__4_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0___closed__4_value_aux_1),((lean_object*)&l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(196, 225, 111, 69, 82, 38, 249, 149)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0___closed__4_value_aux_2),((lean_object*)&l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(100, 233, 103, 154, 53, 22, 86, 139)}};
static const lean_object* l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0___closed__4 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0___closed__4_value;
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__9_value),LEAN_SCALAR_PTR_LITERAL(94, 4, 109, 108, 64, 81, 153, 133)}};
static const lean_object* l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0___closed__5 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__2_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__2_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___lam__0(lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Sym_Arith_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Field"};
static const lean_object* l_Lean_Meta_Sym_Arith_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___closed__0_value;
static const lean_string_object l_Lean_Meta_Sym_Arith_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "toInv"};
static const lean_object* l_Lean_Meta_Sym_Arith_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___closed__2_value_aux_1),((lean_object*)&l_Lean_Meta_Sym_Arith_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(69, 164, 44, 189, 207, 226, 143, 119)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___closed__2_value_aux_2),((lean_object*)&l_Lean_Meta_Sym_Arith_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(101, 152, 64, 108, 234, 163, 46, 107)}};
static const lean_object* l_Lean_Meta_Sym_Arith_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___closed__2 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___closed__2_value;
static const lean_string_object l_Lean_Meta_Sym_Arith_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Inv"};
static const lean_object* l_Lean_Meta_Sym_Arith_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___closed__3 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___closed__3_value;
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Arith_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(142, 68, 231, 210, 96, 163, 154, 19)}};
static const lean_object* l_Lean_Meta_Sym_Arith_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___closed__4 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___closed__4_value;
static const lean_string_object l_Lean_Meta_Sym_Arith_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "inv"};
static const lean_object* l_Lean_Meta_Sym_Arith_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___closed__5 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___closed__5_value;
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Arith_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(142, 68, 231, 210, 96, 163, 154, 19)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___closed__6_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_Arith_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___closed__5_value),LEAN_SCALAR_PTR_LITERAL(63, 31, 248, 222, 13, 64, 40, 141)}};
static const lean_object* l_Lean_Meta_Sym_Arith_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___closed__6 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___closed__6_value;
static const lean_string_object l_Lean_Meta_Sym_Arith_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "internal error: type is not a field"};
static const lean_object* l_Lean_Meta_Sym_Arith_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___closed__7 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___closed__7_value;
static lean_once_cell_t l_Lean_Meta_Sym_Arith_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Arith_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___closed__8;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0_spec__1_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0_spec__2___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___lam__0(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1_spec__2_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1_spec__2___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___at___00Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___at___00Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__2_spec__4___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__2___lam__0(lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "instHMul"};
static const lean_object* l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__2___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__2___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(177, 107, 107, 59, 202, 230, 169, 251)}};
static const lean_object* l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__2___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__2___closed__1_value;
static const lean_string_object l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Semiring"};
static const lean_object* l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__2___closed__2 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__2___closed__2_value;
static const lean_string_object l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "toMul"};
static const lean_object* l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__2___closed__3 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__2___closed__3_value;
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__2___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__2___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__2___closed__4_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__2___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__2___closed__4_value_aux_1),((lean_object*)&l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__2___closed__2_value),LEAN_SCALAR_PTR_LITERAL(246, 150, 10, 46, 185, 54, 59, 167)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__2___closed__4_value_aux_2),((lean_object*)&l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__2___closed__3_value),LEAN_SCALAR_PTR_LITERAL(232, 23, 103, 115, 5, 120, 143, 98)}};
static const lean_object* l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__2___closed__4 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__2___closed__4_value;
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__2___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__18_value),LEAN_SCALAR_PTR_LITERAL(254, 113, 255, 140, 142, 9, 169, 40)}};
static const lean_object* l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__2___closed__5 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__2___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__6_value),LEAN_SCALAR_PTR_LITERAL(135, 241, 166, 108, 243, 216, 193, 244)}};
static const lean_object* l_Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__3___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__3___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__3___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__3___closed__1;
static const lean_ctor_object l_Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__3___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__3___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__3___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__3___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__3___closed__2_value_aux_1),((lean_object*)&l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__2___closed__2_value),LEAN_SCALAR_PTR_LITERAL(246, 150, 10, 46, 185, 54, 59, 167)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__3___closed__2_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__7_value),LEAN_SCALAR_PTR_LITERAL(103, 49, 23, 61, 125, 46, 165, 129)}};
static const lean_object* l_Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__3___closed__2 = (const lean_object*)&l_Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__3___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "CommRing"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "inv_split"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__0_value),LEAN_SCALAR_PTR_LITERAL(205, 3, 54, 198, 92, 149, 38, 227)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__2_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__1_value),LEAN_SCALAR_PTR_LITERAL(145, 213, 231, 249, 53, 164, 241, 56)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__3;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "inv_int_eqC"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__4_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__5_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__5_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__0_value),LEAN_SCALAR_PTR_LITERAL(205, 3, 54, 198, 92, 149, 38, 227)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__5_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__4_value),LEAN_SCALAR_PTR_LITERAL(153, 82, 86, 32, 91, 2, 111, 119)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__5_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "inv_zero_eqC"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__6_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__7_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__7_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__0_value),LEAN_SCALAR_PTR_LITERAL(205, 3, 54, 198, 92, 149, 38, 227)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__7_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__6_value),LEAN_SCALAR_PTR_LITERAL(59, 171, 80, 119, 126, 116, 37, 65)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__7_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "inv_int_eq"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__8_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__9_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__9_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__0_value),LEAN_SCALAR_PTR_LITERAL(205, 3, 54, 198, 92, 149, 38, 227)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__9_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__8_value),LEAN_SCALAR_PTR_LITERAL(187, 42, 227, 251, 174, 7, 5, 152)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__9_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "inv_zero"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__10 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__10_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__11_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__11_value_aux_1),((lean_object*)&l_Lean_Meta_Sym_Arith_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(69, 164, 44, 189, 207, 226, 143, 119)}};
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0_spec__2(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1_spec__2_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0_spec__1_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_internalize___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_internalize___lam__2(lean_object*, lean_object*, lean_object*);
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
uint8_t l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isForbiddenParent(lean_object* v_parent_x3f_134_){
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
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isForbiddenParent_0interp(lean_interpreter_value* stack)
{
lean_object* v_parent_x3f_134_ = stack[0].m_obj;
uint8_t v_res_161_;
v_res_161_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isForbiddenParent(v_parent_x3f_134_);
stack->m_num = v_res_161_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isForbiddenParent___boxed(lean_object* v_parent_x3f_162_){
_start:
{
uint8_t v_res_163_; lean_object* v_r_164_; 
v_res_163_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isForbiddenParent(v_parent_x3f_162_);
v_r_164_ = lean_box(v_res_163_);
return v_r_164_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__1(lean_object* v_a_165_){
_start:
{
lean_object* v___x_166_; 
v___x_166_ = lean_nat_to_int(v_a_165_);
return v___x_166_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5(lean_object* v_msgData_167_, lean_object* v___y_168_, lean_object* v___y_169_, lean_object* v___y_170_, lean_object* v___y_171_){
_start:
{
lean_object* v___x_173_; lean_object* v_env_174_; uint8_t v___x_175_; lean_object* v_env_176_; lean_object* v___x_177_; lean_object* v_toCold_178_; lean_object* v_mctx_179_; lean_object* v_lctx_180_; lean_object* v_options_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; 
v___x_173_ = lean_st_ref_get(v___y_171_);
v_env_174_ = lean_ctor_get(v___x_173_, 0);
lean_inc_ref(v_env_174_);
lean_dec(v___x_173_);
v___x_175_ = 0;
v_env_176_ = l_Lean_Environment_setRecordingDeps(v_env_174_, v___x_175_);
v___x_177_ = lean_st_ref_get(v___y_169_);
v_toCold_178_ = lean_ctor_get(v___y_170_, 0);
v_mctx_179_ = lean_ctor_get(v___x_177_, 0);
lean_inc_ref(v_mctx_179_);
lean_dec(v___x_177_);
v_lctx_180_ = lean_ctor_get(v___y_168_, 2);
v_options_181_ = lean_ctor_get(v_toCold_178_, 2);
lean_inc_ref(v_options_181_);
lean_inc_ref(v_lctx_180_);
v___x_182_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_182_, 0, v_env_176_);
lean_ctor_set(v___x_182_, 1, v_mctx_179_);
lean_ctor_set(v___x_182_, 2, v_lctx_180_);
lean_ctor_set(v___x_182_, 3, v_options_181_);
v___x_183_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_183_, 0, v___x_182_);
lean_ctor_set(v___x_183_, 1, v_msgData_167_);
v___x_184_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_184_, 0, v___x_183_);
return v___x_184_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_167_ = stack[0].m_obj;
lean_object* v___y_168_ = stack[1].m_obj;
lean_object* v___y_169_ = stack[2].m_obj;
lean_object* v___y_170_ = stack[3].m_obj;
lean_object* v___y_171_ = stack[4].m_obj;
lean_object* v_res_185_;
v_res_185_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5(v_msgData_167_, v___y_168_, v___y_169_, v___y_170_, v___y_171_);
stack->m_obj
 = v_res_185_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___boxed(lean_object* v_msgData_186_, lean_object* v___y_187_, lean_object* v___y_188_, lean_object* v___y_189_, lean_object* v___y_190_, lean_object* v___y_191_){
_start:
{
lean_object* v_res_192_; 
v_res_192_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5(v_msgData_186_, v___y_187_, v___y_188_, v___y_189_, v___y_190_);
lean_dec(v___y_190_);
lean_dec_ref(v___y_189_);
lean_dec(v___y_188_);
lean_dec_ref(v___y_187_);
return v_res_192_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__2_spec__3_spec__4___redArg(lean_object* v_msg_193_, lean_object* v___y_194_, lean_object* v___y_195_, lean_object* v___y_196_, lean_object* v___y_197_){
_start:
{
lean_object* v_ref_199_; lean_object* v___x_200_; lean_object* v_a_201_; lean_object* v___x_203_; uint8_t v_isShared_204_; uint8_t v_isSharedCheck_209_; 
v_ref_199_ = lean_ctor_get(v___y_196_, 2);
v___x_200_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5(v_msg_193_, v___y_194_, v___y_195_, v___y_196_, v___y_197_);
v_a_201_ = lean_ctor_get(v___x_200_, 0);
v_isSharedCheck_209_ = !lean_is_exclusive(v___x_200_);
if (v_isSharedCheck_209_ == 0)
{
v___x_203_ = v___x_200_;
v_isShared_204_ = v_isSharedCheck_209_;
goto v_resetjp_202_;
}
else
{
lean_inc(v_a_201_);
lean_dec(v___x_200_);
v___x_203_ = lean_box(0);
v_isShared_204_ = v_isSharedCheck_209_;
goto v_resetjp_202_;
}
v_resetjp_202_:
{
lean_object* v___x_205_; lean_object* v___x_207_; 
lean_inc(v_ref_199_);
v___x_205_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_205_, 0, v_ref_199_);
lean_ctor_set(v___x_205_, 1, v_a_201_);
if (v_isShared_204_ == 0)
{
lean_ctor_set_tag(v___x_203_, 1);
lean_ctor_set(v___x_203_, 0, v___x_205_);
v___x_207_ = v___x_203_;
goto v_reusejp_206_;
}
else
{
lean_object* v_reuseFailAlloc_208_; 
v_reuseFailAlloc_208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_208_, 0, v___x_205_);
v___x_207_ = v_reuseFailAlloc_208_;
goto v_reusejp_206_;
}
v_reusejp_206_:
{
return v___x_207_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__2_spec__3_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_193_ = stack[0].m_obj;
lean_object* v___y_194_ = stack[1].m_obj;
lean_object* v___y_195_ = stack[2].m_obj;
lean_object* v___y_196_ = stack[3].m_obj;
lean_object* v___y_197_ = stack[4].m_obj;
lean_object* v_res_210_;
v_res_210_ = l_Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__2_spec__3_spec__4___redArg(v_msg_193_, v___y_194_, v___y_195_, v___y_196_, v___y_197_);
stack->m_obj
 = v_res_210_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__2_spec__3_spec__4___redArg___boxed(lean_object* v_msg_211_, lean_object* v___y_212_, lean_object* v___y_213_, lean_object* v___y_214_, lean_object* v___y_215_, lean_object* v___y_216_){
_start:
{
lean_object* v_res_217_; 
v_res_217_ = l_Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__2_spec__3_spec__4___redArg(v_msg_211_, v___y_212_, v___y_213_, v___y_214_, v___y_215_);
lean_dec(v___y_215_);
lean_dec_ref(v___y_214_);
lean_dec(v___y_213_);
lean_dec_ref(v___y_212_);
return v_res_217_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__2_spec__3___closed__1(void){
_start:
{
lean_object* v___x_219_; lean_object* v___x_220_; 
v___x_219_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__2_spec__3___closed__0));
v___x_220_ = l_Lean_stringToMessageData(v___x_219_);
return v___x_220_;
}
}
lean_object* l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__2_spec__3(lean_object* v_type_221_, lean_object* v___y_222_, lean_object* v___y_223_, lean_object* v___y_224_, lean_object* v___y_225_, lean_object* v___y_226_, lean_object* v___y_227_, lean_object* v___y_228_, lean_object* v___y_229_, lean_object* v___y_230_, lean_object* v___y_231_, lean_object* v___y_232_){
_start:
{
lean_object* v___x_234_; 
lean_inc_ref(v_type_221_);
v___x_234_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v_type_221_, v___y_228_, v___y_229_, v___y_230_, v___y_231_, v___y_232_);
if (lean_obj_tag(v___x_234_) == 0)
{
lean_object* v_a_235_; lean_object* v___x_237_; uint8_t v_isShared_238_; uint8_t v_isSharedCheck_247_; 
v_a_235_ = lean_ctor_get(v___x_234_, 0);
v_isSharedCheck_247_ = !lean_is_exclusive(v___x_234_);
if (v_isSharedCheck_247_ == 0)
{
v___x_237_ = v___x_234_;
v_isShared_238_ = v_isSharedCheck_247_;
goto v_resetjp_236_;
}
else
{
lean_inc(v_a_235_);
lean_dec(v___x_234_);
v___x_237_ = lean_box(0);
v_isShared_238_ = v_isSharedCheck_247_;
goto v_resetjp_236_;
}
v_resetjp_236_:
{
if (lean_obj_tag(v_a_235_) == 1)
{
lean_object* v_val_239_; lean_object* v___x_241_; 
lean_dec_ref(v_type_221_);
v_val_239_ = lean_ctor_get(v_a_235_, 0);
lean_inc(v_val_239_);
lean_dec_ref_known(v_a_235_, 1);
if (v_isShared_238_ == 0)
{
lean_ctor_set(v___x_237_, 0, v_val_239_);
v___x_241_ = v___x_237_;
goto v_reusejp_240_;
}
else
{
lean_object* v_reuseFailAlloc_242_; 
v_reuseFailAlloc_242_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_242_, 0, v_val_239_);
v___x_241_ = v_reuseFailAlloc_242_;
goto v_reusejp_240_;
}
v_reusejp_240_:
{
return v___x_241_;
}
}
else
{
lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; 
lean_del_object(v___x_237_);
lean_dec(v_a_235_);
v___x_243_ = lean_obj_once(&l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__2_spec__3___closed__1, &l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__2_spec__3___closed__1_once, _init_l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__2_spec__3___closed__1);
v___x_244_ = l_Lean_indentExpr(v_type_221_);
v___x_245_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_245_, 0, v___x_243_);
lean_ctor_set(v___x_245_, 1, v___x_244_);
v___x_246_ = l_Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__2_spec__3_spec__4___redArg(v___x_245_, v___y_229_, v___y_230_, v___y_231_, v___y_232_);
return v___x_246_;
}
}
}
else
{
lean_object* v_a_248_; lean_object* v___x_250_; uint8_t v_isShared_251_; uint8_t v_isSharedCheck_255_; 
lean_dec_ref(v_type_221_);
v_a_248_ = lean_ctor_get(v___x_234_, 0);
v_isSharedCheck_255_ = !lean_is_exclusive(v___x_234_);
if (v_isSharedCheck_255_ == 0)
{
v___x_250_ = v___x_234_;
v_isShared_251_ = v_isSharedCheck_255_;
goto v_resetjp_249_;
}
else
{
lean_inc(v_a_248_);
lean_dec(v___x_234_);
v___x_250_ = lean_box(0);
v_isShared_251_ = v_isSharedCheck_255_;
goto v_resetjp_249_;
}
v_resetjp_249_:
{
lean_object* v___x_253_; 
if (v_isShared_251_ == 0)
{
v___x_253_ = v___x_250_;
goto v_reusejp_252_;
}
else
{
lean_object* v_reuseFailAlloc_254_; 
v_reuseFailAlloc_254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_254_, 0, v_a_248_);
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
}
LEAN_EXPORT void l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__2_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_221_ = stack[0].m_obj;
lean_object* v___y_222_ = stack[1].m_obj;
lean_object* v___y_223_ = stack[2].m_obj;
lean_object* v___y_224_ = stack[3].m_obj;
lean_object* v___y_225_ = stack[4].m_obj;
lean_object* v___y_226_ = stack[5].m_obj;
lean_object* v___y_227_ = stack[6].m_obj;
lean_object* v___y_228_ = stack[7].m_obj;
lean_object* v___y_229_ = stack[8].m_obj;
lean_object* v___y_230_ = stack[9].m_obj;
lean_object* v___y_231_ = stack[10].m_obj;
lean_object* v___y_232_ = stack[11].m_obj;
lean_object* v_res_256_;
v_res_256_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__2_spec__3(v_type_221_, v___y_222_, v___y_223_, v___y_224_, v___y_225_, v___y_226_, v___y_227_, v___y_228_, v___y_229_, v___y_230_, v___y_231_, v___y_232_);
stack->m_obj
 = v_res_256_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__2_spec__3___boxed(lean_object* v_type_257_, lean_object* v___y_258_, lean_object* v___y_259_, lean_object* v___y_260_, lean_object* v___y_261_, lean_object* v___y_262_, lean_object* v___y_263_, lean_object* v___y_264_, lean_object* v___y_265_, lean_object* v___y_266_, lean_object* v___y_267_, lean_object* v___y_268_, lean_object* v___y_269_){
_start:
{
lean_object* v_res_270_; 
v_res_270_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__2_spec__3(v_type_257_, v___y_258_, v___y_259_, v___y_260_, v___y_261_, v___y_262_, v___y_263_, v___y_264_, v___y_265_, v___y_266_, v___y_267_, v___y_268_);
lean_dec(v___y_268_);
lean_dec_ref(v___y_267_);
lean_dec(v___y_266_);
lean_dec_ref(v___y_265_);
lean_dec(v___y_264_);
lean_dec_ref(v___y_263_);
lean_dec(v___y_262_);
lean_dec_ref(v___y_261_);
lean_dec(v___y_260_);
lean_dec(v___y_259_);
lean_dec_ref(v___y_258_);
return v_res_270_;
}
}
lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__2(lean_object* v_type_271_, lean_object* v_u_272_, lean_object* v_instDeclName_273_, lean_object* v_declName_274_, lean_object* v_expectedInst_275_, lean_object* v___y_276_, lean_object* v___y_277_, lean_object* v___y_278_, lean_object* v___y_279_, lean_object* v___y_280_, lean_object* v___y_281_, lean_object* v___y_282_, lean_object* v___y_283_, lean_object* v___y_284_, lean_object* v___y_285_, lean_object* v___y_286_){
_start:
{
lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; 
v___x_288_ = lean_box(0);
v___x_289_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_289_, 0, v_u_272_);
lean_ctor_set(v___x_289_, 1, v___x_288_);
lean_inc_ref(v___x_289_);
v___x_290_ = l_Lean_mkConst(v_instDeclName_273_, v___x_289_);
lean_inc_ref(v_type_271_);
v___x_291_ = l_Lean_Expr_app___override(v___x_290_, v_type_271_);
v___x_292_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__2_spec__3(v___x_291_, v___y_276_, v___y_277_, v___y_278_, v___y_279_, v___y_280_, v___y_281_, v___y_282_, v___y_283_, v___y_284_, v___y_285_, v___y_286_);
if (lean_obj_tag(v___x_292_) == 0)
{
lean_object* v_a_293_; lean_object* v___x_294_; 
v_a_293_ = lean_ctor_get(v___x_292_, 0);
lean_inc_n(v_a_293_, 2);
lean_dec_ref_known(v___x_292_, 1);
lean_inc(v_declName_274_);
v___x_294_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst(v_declName_274_, v_a_293_, v_expectedInst_275_, v___y_283_, v___y_284_, v___y_285_, v___y_286_);
if (lean_obj_tag(v___x_294_) == 0)
{
lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; 
lean_dec_ref_known(v___x_294_, 1);
v___x_295_ = l_Lean_mkConst(v_declName_274_, v___x_289_);
v___x_296_ = l_Lean_mkAppB(v___x_295_, v_type_271_, v_a_293_);
v___x_297_ = l_Lean_Meta_Sym_canon(v___x_296_, v___y_281_, v___y_282_, v___y_283_, v___y_284_, v___y_285_, v___y_286_);
if (lean_obj_tag(v___x_297_) == 0)
{
lean_object* v_a_298_; lean_object* v___x_299_; 
v_a_298_ = lean_ctor_get(v___x_297_, 0);
lean_inc(v_a_298_);
lean_dec_ref_known(v___x_297_, 1);
v___x_299_ = l_Lean_Meta_Sym_shareCommon(v_a_298_, v___y_281_, v___y_282_, v___y_283_, v___y_284_, v___y_285_, v___y_286_);
return v___x_299_;
}
else
{
return v___x_297_;
}
}
else
{
lean_object* v_a_300_; lean_object* v___x_302_; uint8_t v_isShared_303_; uint8_t v_isSharedCheck_307_; 
lean_dec(v_a_293_);
lean_dec_ref_known(v___x_289_, 2);
lean_dec(v_declName_274_);
lean_dec_ref(v_type_271_);
v_a_300_ = lean_ctor_get(v___x_294_, 0);
v_isSharedCheck_307_ = !lean_is_exclusive(v___x_294_);
if (v_isSharedCheck_307_ == 0)
{
v___x_302_ = v___x_294_;
v_isShared_303_ = v_isSharedCheck_307_;
goto v_resetjp_301_;
}
else
{
lean_inc(v_a_300_);
lean_dec(v___x_294_);
v___x_302_ = lean_box(0);
v_isShared_303_ = v_isSharedCheck_307_;
goto v_resetjp_301_;
}
v_resetjp_301_:
{
lean_object* v___x_305_; 
if (v_isShared_303_ == 0)
{
v___x_305_ = v___x_302_;
goto v_reusejp_304_;
}
else
{
lean_object* v_reuseFailAlloc_306_; 
v_reuseFailAlloc_306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_306_, 0, v_a_300_);
v___x_305_ = v_reuseFailAlloc_306_;
goto v_reusejp_304_;
}
v_reusejp_304_:
{
return v___x_305_;
}
}
}
}
else
{
lean_dec_ref_known(v___x_289_, 2);
lean_dec_ref(v_expectedInst_275_);
lean_dec(v_declName_274_);
lean_dec_ref(v_type_271_);
return v___x_292_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_271_ = stack[0].m_obj;
lean_object* v_u_272_ = stack[1].m_obj;
lean_object* v_instDeclName_273_ = stack[2].m_obj;
lean_object* v_declName_274_ = stack[3].m_obj;
lean_object* v_expectedInst_275_ = stack[4].m_obj;
lean_object* v___y_276_ = stack[5].m_obj;
lean_object* v___y_277_ = stack[6].m_obj;
lean_object* v___y_278_ = stack[7].m_obj;
lean_object* v___y_279_ = stack[8].m_obj;
lean_object* v___y_280_ = stack[9].m_obj;
lean_object* v___y_281_ = stack[10].m_obj;
lean_object* v___y_282_ = stack[11].m_obj;
lean_object* v___y_283_ = stack[12].m_obj;
lean_object* v___y_284_ = stack[13].m_obj;
lean_object* v___y_285_ = stack[14].m_obj;
lean_object* v___y_286_ = stack[15].m_obj;
lean_object* v_res_308_;
v_res_308_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__2(v_type_271_, v_u_272_, v_instDeclName_273_, v_declName_274_, v_expectedInst_275_, v___y_276_, v___y_277_, v___y_278_, v___y_279_, v___y_280_, v___y_281_, v___y_282_, v___y_283_, v___y_284_, v___y_285_, v___y_286_);
stack->m_obj
 = v_res_308_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__2___boxed(lean_object** _args){
lean_object* v_type_309_ = _args[0];
lean_object* v_u_310_ = _args[1];
lean_object* v_instDeclName_311_ = _args[2];
lean_object* v_declName_312_ = _args[3];
lean_object* v_expectedInst_313_ = _args[4];
lean_object* v___y_314_ = _args[5];
lean_object* v___y_315_ = _args[6];
lean_object* v___y_316_ = _args[7];
lean_object* v___y_317_ = _args[8];
lean_object* v___y_318_ = _args[9];
lean_object* v___y_319_ = _args[10];
lean_object* v___y_320_ = _args[11];
lean_object* v___y_321_ = _args[12];
lean_object* v___y_322_ = _args[13];
lean_object* v___y_323_ = _args[14];
lean_object* v___y_324_ = _args[15];
lean_object* v___y_325_ = _args[16];
_start:
{
lean_object* v_res_326_; 
v_res_326_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__2(v_type_309_, v_u_310_, v_instDeclName_311_, v_declName_312_, v_expectedInst_313_, v___y_314_, v___y_315_, v___y_316_, v___y_317_, v___y_318_, v___y_319_, v___y_320_, v___y_321_, v___y_322_, v___y_323_, v___y_324_);
lean_dec(v___y_324_);
lean_dec_ref(v___y_323_);
lean_dec(v___y_322_);
lean_dec_ref(v___y_321_);
lean_dec(v___y_320_);
lean_dec_ref(v___y_319_);
lean_dec(v___y_318_);
lean_dec_ref(v___y_317_);
lean_dec(v___y_316_);
lean_dec(v___y_315_);
lean_dec_ref(v___y_314_);
return v_res_326_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0___lam__0(lean_object* v_a_327_, lean_object* v_s_328_){
_start:
{
lean_object* v_toRing_329_; lean_object* v_invFn_x3f_330_; lean_object* v_divFn_x3f_331_; lean_object* v_semiringId_x3f_332_; lean_object* v_commSemiringInst_333_; lean_object* v_commRingInst_334_; lean_object* v_noZeroDivInst_x3f_335_; lean_object* v_fieldInst_x3f_336_; lean_object* v_powIdentityInst_x3f_337_; lean_object* v___x_339_; uint8_t v_isShared_340_; uint8_t v_isSharedCheck_368_; 
v_toRing_329_ = lean_ctor_get(v_s_328_, 0);
v_invFn_x3f_330_ = lean_ctor_get(v_s_328_, 1);
v_divFn_x3f_331_ = lean_ctor_get(v_s_328_, 2);
v_semiringId_x3f_332_ = lean_ctor_get(v_s_328_, 3);
v_commSemiringInst_333_ = lean_ctor_get(v_s_328_, 4);
v_commRingInst_334_ = lean_ctor_get(v_s_328_, 5);
v_noZeroDivInst_x3f_335_ = lean_ctor_get(v_s_328_, 6);
v_fieldInst_x3f_336_ = lean_ctor_get(v_s_328_, 7);
v_powIdentityInst_x3f_337_ = lean_ctor_get(v_s_328_, 8);
v_isSharedCheck_368_ = !lean_is_exclusive(v_s_328_);
if (v_isSharedCheck_368_ == 0)
{
v___x_339_ = v_s_328_;
v_isShared_340_ = v_isSharedCheck_368_;
goto v_resetjp_338_;
}
else
{
lean_inc(v_powIdentityInst_x3f_337_);
lean_inc(v_fieldInst_x3f_336_);
lean_inc(v_noZeroDivInst_x3f_335_);
lean_inc(v_commRingInst_334_);
lean_inc(v_commSemiringInst_333_);
lean_inc(v_semiringId_x3f_332_);
lean_inc(v_divFn_x3f_331_);
lean_inc(v_invFn_x3f_330_);
lean_inc(v_toRing_329_);
lean_dec(v_s_328_);
v___x_339_ = lean_box(0);
v_isShared_340_ = v_isSharedCheck_368_;
goto v_resetjp_338_;
}
v_resetjp_338_:
{
lean_object* v_id_341_; lean_object* v_type_342_; lean_object* v_u_343_; lean_object* v_ringInst_344_; lean_object* v_semiringInst_345_; lean_object* v_charInst_x3f_346_; lean_object* v_addFn_x3f_347_; lean_object* v_mulFn_x3f_348_; lean_object* v_subFn_x3f_349_; lean_object* v_powFn_x3f_350_; lean_object* v_intCastFn_x3f_351_; lean_object* v_natCastFn_x3f_352_; lean_object* v_natSMulFn_x3f_353_; lean_object* v_intSMulFn_x3f_354_; lean_object* v_one_x3f_355_; lean_object* v___x_357_; uint8_t v_isShared_358_; uint8_t v_isSharedCheck_366_; 
v_id_341_ = lean_ctor_get(v_toRing_329_, 0);
v_type_342_ = lean_ctor_get(v_toRing_329_, 1);
v_u_343_ = lean_ctor_get(v_toRing_329_, 2);
v_ringInst_344_ = lean_ctor_get(v_toRing_329_, 3);
v_semiringInst_345_ = lean_ctor_get(v_toRing_329_, 4);
v_charInst_x3f_346_ = lean_ctor_get(v_toRing_329_, 5);
v_addFn_x3f_347_ = lean_ctor_get(v_toRing_329_, 6);
v_mulFn_x3f_348_ = lean_ctor_get(v_toRing_329_, 7);
v_subFn_x3f_349_ = lean_ctor_get(v_toRing_329_, 8);
v_powFn_x3f_350_ = lean_ctor_get(v_toRing_329_, 10);
v_intCastFn_x3f_351_ = lean_ctor_get(v_toRing_329_, 11);
v_natCastFn_x3f_352_ = lean_ctor_get(v_toRing_329_, 12);
v_natSMulFn_x3f_353_ = lean_ctor_get(v_toRing_329_, 13);
v_intSMulFn_x3f_354_ = lean_ctor_get(v_toRing_329_, 14);
v_one_x3f_355_ = lean_ctor_get(v_toRing_329_, 15);
v_isSharedCheck_366_ = !lean_is_exclusive(v_toRing_329_);
if (v_isSharedCheck_366_ == 0)
{
lean_object* v_unused_367_; 
v_unused_367_ = lean_ctor_get(v_toRing_329_, 9);
lean_dec(v_unused_367_);
v___x_357_ = v_toRing_329_;
v_isShared_358_ = v_isSharedCheck_366_;
goto v_resetjp_356_;
}
else
{
lean_inc(v_one_x3f_355_);
lean_inc(v_intSMulFn_x3f_354_);
lean_inc(v_natSMulFn_x3f_353_);
lean_inc(v_natCastFn_x3f_352_);
lean_inc(v_intCastFn_x3f_351_);
lean_inc(v_powFn_x3f_350_);
lean_inc(v_subFn_x3f_349_);
lean_inc(v_mulFn_x3f_348_);
lean_inc(v_addFn_x3f_347_);
lean_inc(v_charInst_x3f_346_);
lean_inc(v_semiringInst_345_);
lean_inc(v_ringInst_344_);
lean_inc(v_u_343_);
lean_inc(v_type_342_);
lean_inc(v_id_341_);
lean_dec(v_toRing_329_);
v___x_357_ = lean_box(0);
v_isShared_358_ = v_isSharedCheck_366_;
goto v_resetjp_356_;
}
v_resetjp_356_:
{
lean_object* v___x_359_; lean_object* v___x_361_; 
v___x_359_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_359_, 0, v_a_327_);
if (v_isShared_358_ == 0)
{
lean_ctor_set(v___x_357_, 9, v___x_359_);
v___x_361_ = v___x_357_;
goto v_reusejp_360_;
}
else
{
lean_object* v_reuseFailAlloc_365_; 
v_reuseFailAlloc_365_ = lean_alloc_ctor(0, 16, 0);
lean_ctor_set(v_reuseFailAlloc_365_, 0, v_id_341_);
lean_ctor_set(v_reuseFailAlloc_365_, 1, v_type_342_);
lean_ctor_set(v_reuseFailAlloc_365_, 2, v_u_343_);
lean_ctor_set(v_reuseFailAlloc_365_, 3, v_ringInst_344_);
lean_ctor_set(v_reuseFailAlloc_365_, 4, v_semiringInst_345_);
lean_ctor_set(v_reuseFailAlloc_365_, 5, v_charInst_x3f_346_);
lean_ctor_set(v_reuseFailAlloc_365_, 6, v_addFn_x3f_347_);
lean_ctor_set(v_reuseFailAlloc_365_, 7, v_mulFn_x3f_348_);
lean_ctor_set(v_reuseFailAlloc_365_, 8, v_subFn_x3f_349_);
lean_ctor_set(v_reuseFailAlloc_365_, 9, v___x_359_);
lean_ctor_set(v_reuseFailAlloc_365_, 10, v_powFn_x3f_350_);
lean_ctor_set(v_reuseFailAlloc_365_, 11, v_intCastFn_x3f_351_);
lean_ctor_set(v_reuseFailAlloc_365_, 12, v_natCastFn_x3f_352_);
lean_ctor_set(v_reuseFailAlloc_365_, 13, v_natSMulFn_x3f_353_);
lean_ctor_set(v_reuseFailAlloc_365_, 14, v_intSMulFn_x3f_354_);
lean_ctor_set(v_reuseFailAlloc_365_, 15, v_one_x3f_355_);
v___x_361_ = v_reuseFailAlloc_365_;
goto v_reusejp_360_;
}
v_reusejp_360_:
{
lean_object* v___x_363_; 
if (v_isShared_340_ == 0)
{
lean_ctor_set(v___x_339_, 0, v___x_361_);
v___x_363_ = v___x_339_;
goto v_reusejp_362_;
}
else
{
lean_object* v_reuseFailAlloc_364_; 
v_reuseFailAlloc_364_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_364_, 0, v___x_361_);
lean_ctor_set(v_reuseFailAlloc_364_, 1, v_invFn_x3f_330_);
lean_ctor_set(v_reuseFailAlloc_364_, 2, v_divFn_x3f_331_);
lean_ctor_set(v_reuseFailAlloc_364_, 3, v_semiringId_x3f_332_);
lean_ctor_set(v_reuseFailAlloc_364_, 4, v_commSemiringInst_333_);
lean_ctor_set(v_reuseFailAlloc_364_, 5, v_commRingInst_334_);
lean_ctor_set(v_reuseFailAlloc_364_, 6, v_noZeroDivInst_x3f_335_);
lean_ctor_set(v_reuseFailAlloc_364_, 7, v_fieldInst_x3f_336_);
lean_ctor_set(v_reuseFailAlloc_364_, 8, v_powIdentityInst_x3f_337_);
v___x_363_ = v_reuseFailAlloc_364_;
goto v_reusejp_362_;
}
v_reusejp_362_:
{
return v___x_363_;
}
}
}
}
}
}
lean_object* l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0(lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_){
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
lean_dec_ref_known(v_negFn_x3f_398_, 1);
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
v___x_406_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0___closed__4));
v___x_407_ = lean_box(0);
v___x_408_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_408_, 0, v_u_404_);
lean_ctor_set(v___x_408_, 1, v___x_407_);
v___x_409_ = l_Lean_mkConst(v___x_406_, v___x_408_);
v_expectedInst_410_ = l_Lean_mkAppB(v___x_409_, v_type_403_, v_ringInst_405_);
v___x_411_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0___closed__5));
v___x_412_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__11));
v___x_413_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__2(v_type_403_, v_u_404_, v___x_411_, v___x_412_, v_expectedInst_410_, v___y_380_, v___y_381_, v___y_382_, v___y_383_, v___y_384_, v___y_385_, v___y_386_, v___y_387_, v___y_388_, v___y_389_, v___y_390_);
if (lean_obj_tag(v___x_413_) == 0)
{
lean_object* v_a_414_; lean_object* v___f_415_; lean_object* v___x_416_; 
v_a_414_ = lean_ctor_get(v___x_413_, 0);
lean_inc_n(v_a_414_, 2);
lean_dec_ref_known(v___x_413_, 1);
v___f_415_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0___lam__0), 2, 1);
lean_closure_set(v___f_415_, 0, v_a_414_);
v___x_416_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(v___f_415_, v___y_380_, v___y_386_);
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
LEAN_EXPORT void l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_380_ = stack[0].m_obj;
lean_object* v___y_381_ = stack[1].m_obj;
lean_object* v___y_382_ = stack[2].m_obj;
lean_object* v___y_383_ = stack[3].m_obj;
lean_object* v___y_384_ = stack[4].m_obj;
lean_object* v___y_385_ = stack[5].m_obj;
lean_object* v___y_386_ = stack[6].m_obj;
lean_object* v___y_387_ = stack[7].m_obj;
lean_object* v___y_388_ = stack[8].m_obj;
lean_object* v___y_389_ = stack[9].m_obj;
lean_object* v___y_390_ = stack[10].m_obj;
lean_object* v_res_442_;
v_res_442_ = l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0(v___y_380_, v___y_381_, v___y_382_, v___y_383_, v___y_384_, v___y_385_, v___y_386_, v___y_387_, v___y_388_, v___y_389_, v___y_390_);
stack->m_obj
 = v_res_442_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0___boxed(lean_object* v___y_443_, lean_object* v___y_444_, lean_object* v___y_445_, lean_object* v___y_446_, lean_object* v___y_447_, lean_object* v___y_448_, lean_object* v___y_449_, lean_object* v___y_450_, lean_object* v___y_451_, lean_object* v___y_452_, lean_object* v___y_453_, lean_object* v___y_454_){
_start:
{
lean_object* v_res_455_; 
v_res_455_ = l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0(v___y_443_, v___y_444_, v___y_445_, v___y_446_, v___y_447_, v___y_448_, v___y_449_, v___y_450_, v___y_451_, v___y_452_, v___y_453_);
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
lean_object* l_Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0(lean_object* v_inst_456_, lean_object* v___y_457_, lean_object* v___y_458_, lean_object* v___y_459_, lean_object* v___y_460_, lean_object* v___y_461_, lean_object* v___y_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_){
_start:
{
lean_object* v___x_469_; 
v___x_469_ = l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0(v___y_457_, v___y_458_, v___y_459_, v___y_460_, v___y_461_, v___y_462_, v___y_463_, v___y_464_, v___y_465_, v___y_466_, v___y_467_);
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
LEAN_EXPORT void l_Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_456_ = stack[0].m_obj;
lean_object* v___y_457_ = stack[1].m_obj;
lean_object* v___y_458_ = stack[2].m_obj;
lean_object* v___y_459_ = stack[3].m_obj;
lean_object* v___y_460_ = stack[4].m_obj;
lean_object* v___y_461_ = stack[5].m_obj;
lean_object* v___y_462_ = stack[6].m_obj;
lean_object* v___y_463_ = stack[7].m_obj;
lean_object* v___y_464_ = stack[8].m_obj;
lean_object* v___y_465_ = stack[9].m_obj;
lean_object* v___y_466_ = stack[10].m_obj;
lean_object* v___y_467_ = stack[11].m_obj;
lean_object* v_res_491_;
v_res_491_ = l_Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0(v_inst_456_, v___y_457_, v___y_458_, v___y_459_, v___y_460_, v___y_461_, v___y_462_, v___y_463_, v___y_464_, v___y_465_, v___y_466_, v___y_467_);
stack->m_obj
 = v_res_491_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0___boxed(lean_object* v_inst_492_, lean_object* v___y_493_, lean_object* v___y_494_, lean_object* v___y_495_, lean_object* v___y_496_, lean_object* v___y_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_){
_start:
{
lean_object* v_res_505_; 
v_res_505_ = l_Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0(v_inst_492_, v___y_493_, v___y_494_, v___y_495_, v___y_496_, v___y_497_, v___y_498_, v___y_499_, v___y_500_, v___y_501_, v___y_502_, v___y_503_);
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
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f(lean_object* v_e_506_, lean_object* v_a_507_, lean_object* v_a_508_, lean_object* v_a_509_, lean_object* v_a_510_, lean_object* v_a_511_, lean_object* v_a_512_, lean_object* v_a_513_, lean_object* v_a_514_, lean_object* v_a_515_, lean_object* v_a_516_, lean_object* v_a_517_){
_start:
{
lean_object* v___x_525_; 
v___x_525_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_506_, v_a_515_);
if (lean_obj_tag(v___x_525_) == 0)
{
lean_object* v_a_526_; lean_object* v___x_527_; uint8_t v___x_528_; 
v_a_526_ = lean_ctor_get(v___x_525_, 0);
lean_inc(v_a_526_);
lean_dec_ref_known(v___x_525_, 1);
v___x_527_ = l_Lean_Expr_cleanupAnnotations(v_a_526_);
v___x_528_ = l_Lean_Expr_isApp(v___x_527_);
if (v___x_528_ == 0)
{
lean_dec_ref(v___x_527_);
goto v___jp_519_;
}
else
{
lean_object* v_arg_529_; lean_object* v___x_530_; uint8_t v___x_531_; 
v_arg_529_ = lean_ctor_get(v___x_527_, 1);
lean_inc_ref(v_arg_529_);
v___x_530_ = l_Lean_Expr_appFnCleanup___redArg(v___x_527_);
v___x_531_ = l_Lean_Expr_isApp(v___x_530_);
if (v___x_531_ == 0)
{
lean_dec_ref(v___x_530_);
lean_dec_ref(v_arg_529_);
goto v___jp_519_;
}
else
{
lean_object* v_arg_532_; lean_object* v___x_533_; uint8_t v___x_534_; 
v_arg_532_ = lean_ctor_get(v___x_530_, 1);
lean_inc_ref(v_arg_532_);
v___x_533_ = l_Lean_Expr_appFnCleanup___redArg(v___x_530_);
v___x_534_ = l_Lean_Expr_isApp(v___x_533_);
if (v___x_534_ == 0)
{
lean_dec_ref(v___x_533_);
lean_dec_ref(v_arg_532_);
lean_dec_ref(v_arg_529_);
goto v___jp_519_;
}
else
{
lean_object* v___x_535_; lean_object* v___x_536_; uint8_t v___x_537_; 
v___x_535_ = l_Lean_Expr_appFnCleanup___redArg(v___x_533_);
v___x_536_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__8));
v___x_537_ = l_Lean_Expr_isConstOf(v___x_535_, v___x_536_);
if (v___x_537_ == 0)
{
lean_object* v___x_538_; uint8_t v___x_539_; 
v___x_538_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__11));
v___x_539_ = l_Lean_Expr_isConstOf(v___x_535_, v___x_538_);
lean_dec_ref(v___x_535_);
if (v___x_539_ == 0)
{
lean_dec_ref(v_arg_532_);
lean_dec_ref(v_arg_529_);
goto v___jp_519_;
}
else
{
lean_object* v___x_540_; 
v___x_540_ = l_Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0(v_arg_532_, v_a_507_, v_a_508_, v_a_509_, v_a_510_, v_a_511_, v_a_512_, v_a_513_, v_a_514_, v_a_515_, v_a_516_, v_a_517_);
lean_dec_ref(v_arg_532_);
if (lean_obj_tag(v___x_540_) == 0)
{
lean_object* v_a_541_; lean_object* v___x_543_; uint8_t v_isShared_544_; uint8_t v_isSharedCheck_596_; 
v_a_541_ = lean_ctor_get(v___x_540_, 0);
v_isSharedCheck_596_ = !lean_is_exclusive(v___x_540_);
if (v_isSharedCheck_596_ == 0)
{
v___x_543_ = v___x_540_;
v_isShared_544_ = v_isSharedCheck_596_;
goto v_resetjp_542_;
}
else
{
lean_inc(v_a_541_);
lean_dec(v___x_540_);
v___x_543_ = lean_box(0);
v_isShared_544_ = v_isSharedCheck_596_;
goto v_resetjp_542_;
}
v_resetjp_542_:
{
uint8_t v___x_545_; 
v___x_545_ = lean_unbox(v_a_541_);
lean_dec(v_a_541_);
if (v___x_545_ == 0)
{
lean_object* v___x_546_; lean_object* v___x_548_; 
lean_dec_ref(v_arg_529_);
v___x_546_ = lean_box(0);
if (v_isShared_544_ == 0)
{
lean_ctor_set(v___x_543_, 0, v___x_546_);
v___x_548_ = v___x_543_;
goto v_reusejp_547_;
}
else
{
lean_object* v_reuseFailAlloc_549_; 
v_reuseFailAlloc_549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_549_, 0, v___x_546_);
v___x_548_ = v_reuseFailAlloc_549_;
goto v_reusejp_547_;
}
v_reusejp_547_:
{
return v___x_548_;
}
}
else
{
lean_object* v___x_550_; uint8_t v___x_551_; 
lean_del_object(v___x_543_);
v___x_550_ = l_Lean_Expr_cleanupAnnotations(v_arg_529_);
v___x_551_ = l_Lean_Expr_isApp(v___x_550_);
if (v___x_551_ == 0)
{
lean_dec_ref(v___x_550_);
goto v___jp_522_;
}
else
{
lean_object* v___x_552_; uint8_t v___x_553_; 
v___x_552_ = l_Lean_Expr_appFnCleanup___redArg(v___x_550_);
v___x_553_ = l_Lean_Expr_isApp(v___x_552_);
if (v___x_553_ == 0)
{
lean_dec_ref(v___x_552_);
goto v___jp_522_;
}
else
{
lean_object* v_arg_554_; lean_object* v___x_555_; uint8_t v___x_556_; 
v_arg_554_ = lean_ctor_get(v___x_552_, 1);
lean_inc_ref(v_arg_554_);
v___x_555_ = l_Lean_Expr_appFnCleanup___redArg(v___x_552_);
v___x_556_ = l_Lean_Expr_isApp(v___x_555_);
if (v___x_556_ == 0)
{
lean_dec_ref(v___x_555_);
lean_dec_ref(v_arg_554_);
goto v___jp_522_;
}
else
{
lean_object* v___x_557_; uint8_t v___x_558_; 
v___x_557_ = l_Lean_Expr_appFnCleanup___redArg(v___x_555_);
v___x_558_ = l_Lean_Expr_isConstOf(v___x_557_, v___x_536_);
lean_dec_ref(v___x_557_);
if (v___x_558_ == 0)
{
lean_dec_ref(v_arg_554_);
goto v___jp_522_;
}
else
{
lean_object* v___x_559_; 
v___x_559_ = l_Lean_Meta_getNatValue_x3f(v_arg_554_, v_a_514_, v_a_515_, v_a_516_, v_a_517_);
lean_dec_ref(v_arg_554_);
if (lean_obj_tag(v___x_559_) == 0)
{
lean_object* v_a_560_; lean_object* v___x_562_; uint8_t v_isShared_563_; uint8_t v_isSharedCheck_587_; 
v_a_560_ = lean_ctor_get(v___x_559_, 0);
v_isSharedCheck_587_ = !lean_is_exclusive(v___x_559_);
if (v_isSharedCheck_587_ == 0)
{
v___x_562_ = v___x_559_;
v_isShared_563_ = v_isSharedCheck_587_;
goto v_resetjp_561_;
}
else
{
lean_inc(v_a_560_);
lean_dec(v___x_559_);
v___x_562_ = lean_box(0);
v_isShared_563_ = v_isSharedCheck_587_;
goto v_resetjp_561_;
}
v_resetjp_561_:
{
if (lean_obj_tag(v_a_560_) == 1)
{
lean_object* v_val_564_; lean_object* v___x_566_; uint8_t v_isShared_567_; uint8_t v_isSharedCheck_582_; 
v_val_564_ = lean_ctor_get(v_a_560_, 0);
v_isSharedCheck_582_ = !lean_is_exclusive(v_a_560_);
if (v_isSharedCheck_582_ == 0)
{
v___x_566_ = v_a_560_;
v_isShared_567_ = v_isSharedCheck_582_;
goto v_resetjp_565_;
}
else
{
lean_inc(v_val_564_);
lean_dec(v_a_560_);
v___x_566_ = lean_box(0);
v_isShared_567_ = v_isSharedCheck_582_;
goto v_resetjp_565_;
}
v_resetjp_565_:
{
lean_object* v___x_568_; uint8_t v___x_569_; 
v___x_568_ = lean_unsigned_to_nat(0u);
v___x_569_ = lean_nat_dec_eq(v_val_564_, v___x_568_);
if (v___x_569_ == 0)
{
lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_573_; 
v___x_570_ = lean_nat_to_int(v_val_564_);
v___x_571_ = lean_int_neg(v___x_570_);
lean_dec(v___x_570_);
if (v_isShared_567_ == 0)
{
lean_ctor_set(v___x_566_, 0, v___x_571_);
v___x_573_ = v___x_566_;
goto v_reusejp_572_;
}
else
{
lean_object* v_reuseFailAlloc_577_; 
v_reuseFailAlloc_577_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_577_, 0, v___x_571_);
v___x_573_ = v_reuseFailAlloc_577_;
goto v_reusejp_572_;
}
v_reusejp_572_:
{
lean_object* v___x_575_; 
if (v_isShared_563_ == 0)
{
lean_ctor_set(v___x_562_, 0, v___x_573_);
v___x_575_ = v___x_562_;
goto v_reusejp_574_;
}
else
{
lean_object* v_reuseFailAlloc_576_; 
v_reuseFailAlloc_576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_576_, 0, v___x_573_);
v___x_575_ = v_reuseFailAlloc_576_;
goto v_reusejp_574_;
}
v_reusejp_574_:
{
return v___x_575_;
}
}
}
else
{
lean_object* v___x_578_; lean_object* v___x_580_; 
lean_del_object(v___x_566_);
lean_dec(v_val_564_);
v___x_578_ = lean_box(0);
if (v_isShared_563_ == 0)
{
lean_ctor_set(v___x_562_, 0, v___x_578_);
v___x_580_ = v___x_562_;
goto v_reusejp_579_;
}
else
{
lean_object* v_reuseFailAlloc_581_; 
v_reuseFailAlloc_581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_581_, 0, v___x_578_);
v___x_580_ = v_reuseFailAlloc_581_;
goto v_reusejp_579_;
}
v_reusejp_579_:
{
return v___x_580_;
}
}
}
}
else
{
lean_object* v___x_583_; lean_object* v___x_585_; 
lean_dec(v_a_560_);
v___x_583_ = lean_box(0);
if (v_isShared_563_ == 0)
{
lean_ctor_set(v___x_562_, 0, v___x_583_);
v___x_585_ = v___x_562_;
goto v_reusejp_584_;
}
else
{
lean_object* v_reuseFailAlloc_586_; 
v_reuseFailAlloc_586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_586_, 0, v___x_583_);
v___x_585_ = v_reuseFailAlloc_586_;
goto v_reusejp_584_;
}
v_reusejp_584_:
{
return v___x_585_;
}
}
}
}
else
{
lean_object* v_a_588_; lean_object* v___x_590_; uint8_t v_isShared_591_; uint8_t v_isSharedCheck_595_; 
v_a_588_ = lean_ctor_get(v___x_559_, 0);
v_isSharedCheck_595_ = !lean_is_exclusive(v___x_559_);
if (v_isSharedCheck_595_ == 0)
{
v___x_590_ = v___x_559_;
v_isShared_591_ = v_isSharedCheck_595_;
goto v_resetjp_589_;
}
else
{
lean_inc(v_a_588_);
lean_dec(v___x_559_);
v___x_590_ = lean_box(0);
v_isShared_591_ = v_isSharedCheck_595_;
goto v_resetjp_589_;
}
v_resetjp_589_:
{
lean_object* v___x_593_; 
if (v_isShared_591_ == 0)
{
v___x_593_ = v___x_590_;
goto v_reusejp_592_;
}
else
{
lean_object* v_reuseFailAlloc_594_; 
v_reuseFailAlloc_594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_594_, 0, v_a_588_);
v___x_593_ = v_reuseFailAlloc_594_;
goto v_reusejp_592_;
}
v_reusejp_592_:
{
return v___x_593_;
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
else
{
lean_object* v_a_597_; lean_object* v___x_599_; uint8_t v_isShared_600_; uint8_t v_isSharedCheck_604_; 
lean_dec_ref(v_arg_529_);
v_a_597_ = lean_ctor_get(v___x_540_, 0);
v_isSharedCheck_604_ = !lean_is_exclusive(v___x_540_);
if (v_isSharedCheck_604_ == 0)
{
v___x_599_ = v___x_540_;
v_isShared_600_ = v_isSharedCheck_604_;
goto v_resetjp_598_;
}
else
{
lean_inc(v_a_597_);
lean_dec(v___x_540_);
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
}
else
{
lean_object* v___x_605_; 
lean_dec_ref(v___x_535_);
lean_dec_ref(v_arg_529_);
v___x_605_ = l_Lean_Meta_getNatValue_x3f(v_arg_532_, v_a_514_, v_a_515_, v_a_516_, v_a_517_);
lean_dec_ref(v_arg_532_);
if (lean_obj_tag(v___x_605_) == 0)
{
lean_object* v_a_606_; lean_object* v___x_608_; uint8_t v_isShared_609_; uint8_t v_isSharedCheck_626_; 
v_a_606_ = lean_ctor_get(v___x_605_, 0);
v_isSharedCheck_626_ = !lean_is_exclusive(v___x_605_);
if (v_isSharedCheck_626_ == 0)
{
v___x_608_ = v___x_605_;
v_isShared_609_ = v_isSharedCheck_626_;
goto v_resetjp_607_;
}
else
{
lean_inc(v_a_606_);
lean_dec(v___x_605_);
v___x_608_ = lean_box(0);
v_isShared_609_ = v_isSharedCheck_626_;
goto v_resetjp_607_;
}
v_resetjp_607_:
{
if (lean_obj_tag(v_a_606_) == 1)
{
lean_object* v_val_610_; lean_object* v___x_612_; uint8_t v_isShared_613_; uint8_t v_isSharedCheck_621_; 
v_val_610_ = lean_ctor_get(v_a_606_, 0);
v_isSharedCheck_621_ = !lean_is_exclusive(v_a_606_);
if (v_isSharedCheck_621_ == 0)
{
v___x_612_ = v_a_606_;
v_isShared_613_ = v_isSharedCheck_621_;
goto v_resetjp_611_;
}
else
{
lean_inc(v_val_610_);
lean_dec(v_a_606_);
v___x_612_ = lean_box(0);
v_isShared_613_ = v_isSharedCheck_621_;
goto v_resetjp_611_;
}
v_resetjp_611_:
{
lean_object* v___x_614_; lean_object* v___x_616_; 
v___x_614_ = lean_nat_to_int(v_val_610_);
if (v_isShared_613_ == 0)
{
lean_ctor_set(v___x_612_, 0, v___x_614_);
v___x_616_ = v___x_612_;
goto v_reusejp_615_;
}
else
{
lean_object* v_reuseFailAlloc_620_; 
v_reuseFailAlloc_620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_620_, 0, v___x_614_);
v___x_616_ = v_reuseFailAlloc_620_;
goto v_reusejp_615_;
}
v_reusejp_615_:
{
lean_object* v___x_618_; 
if (v_isShared_609_ == 0)
{
lean_ctor_set(v___x_608_, 0, v___x_616_);
v___x_618_ = v___x_608_;
goto v_reusejp_617_;
}
else
{
lean_object* v_reuseFailAlloc_619_; 
v_reuseFailAlloc_619_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_619_, 0, v___x_616_);
v___x_618_ = v_reuseFailAlloc_619_;
goto v_reusejp_617_;
}
v_reusejp_617_:
{
return v___x_618_;
}
}
}
}
else
{
lean_object* v___x_622_; lean_object* v___x_624_; 
lean_dec(v_a_606_);
v___x_622_ = lean_box(0);
if (v_isShared_609_ == 0)
{
lean_ctor_set(v___x_608_, 0, v___x_622_);
v___x_624_ = v___x_608_;
goto v_reusejp_623_;
}
else
{
lean_object* v_reuseFailAlloc_625_; 
v_reuseFailAlloc_625_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_625_, 0, v___x_622_);
v___x_624_ = v_reuseFailAlloc_625_;
goto v_reusejp_623_;
}
v_reusejp_623_:
{
return v___x_624_;
}
}
}
}
else
{
lean_object* v_a_627_; lean_object* v___x_629_; uint8_t v_isShared_630_; uint8_t v_isSharedCheck_634_; 
v_a_627_ = lean_ctor_get(v___x_605_, 0);
v_isSharedCheck_634_ = !lean_is_exclusive(v___x_605_);
if (v_isSharedCheck_634_ == 0)
{
v___x_629_ = v___x_605_;
v_isShared_630_ = v_isSharedCheck_634_;
goto v_resetjp_628_;
}
else
{
lean_inc(v_a_627_);
lean_dec(v___x_605_);
v___x_629_ = lean_box(0);
v_isShared_630_ = v_isSharedCheck_634_;
goto v_resetjp_628_;
}
v_resetjp_628_:
{
lean_object* v___x_632_; 
if (v_isShared_630_ == 0)
{
v___x_632_ = v___x_629_;
goto v_reusejp_631_;
}
else
{
lean_object* v_reuseFailAlloc_633_; 
v_reuseFailAlloc_633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_633_, 0, v_a_627_);
v___x_632_ = v_reuseFailAlloc_633_;
goto v_reusejp_631_;
}
v_reusejp_631_:
{
return v___x_632_;
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
lean_object* v_a_635_; lean_object* v___x_637_; uint8_t v_isShared_638_; uint8_t v_isSharedCheck_642_; 
v_a_635_ = lean_ctor_get(v___x_525_, 0);
v_isSharedCheck_642_ = !lean_is_exclusive(v___x_525_);
if (v_isSharedCheck_642_ == 0)
{
v___x_637_ = v___x_525_;
v_isShared_638_ = v_isSharedCheck_642_;
goto v_resetjp_636_;
}
else
{
lean_inc(v_a_635_);
lean_dec(v___x_525_);
v___x_637_ = lean_box(0);
v_isShared_638_ = v_isSharedCheck_642_;
goto v_resetjp_636_;
}
v_resetjp_636_:
{
lean_object* v___x_640_; 
if (v_isShared_638_ == 0)
{
v___x_640_ = v___x_637_;
goto v_reusejp_639_;
}
else
{
lean_object* v_reuseFailAlloc_641_; 
v_reuseFailAlloc_641_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_641_, 0, v_a_635_);
v___x_640_ = v_reuseFailAlloc_641_;
goto v_reusejp_639_;
}
v_reusejp_639_:
{
return v___x_640_;
}
}
}
v___jp_519_:
{
lean_object* v___x_520_; lean_object* v___x_521_; 
v___x_520_ = lean_box(0);
v___x_521_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_521_, 0, v___x_520_);
return v___x_521_;
}
v___jp_522_:
{
lean_object* v___x_523_; lean_object* v___x_524_; 
v___x_523_ = lean_box(0);
v___x_524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_524_, 0, v___x_523_);
return v___x_524_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_506_ = stack[0].m_obj;
lean_object* v_a_507_ = stack[1].m_obj;
lean_object* v_a_508_ = stack[2].m_obj;
lean_object* v_a_509_ = stack[3].m_obj;
lean_object* v_a_510_ = stack[4].m_obj;
lean_object* v_a_511_ = stack[5].m_obj;
lean_object* v_a_512_ = stack[6].m_obj;
lean_object* v_a_513_ = stack[7].m_obj;
lean_object* v_a_514_ = stack[8].m_obj;
lean_object* v_a_515_ = stack[9].m_obj;
lean_object* v_a_516_ = stack[10].m_obj;
lean_object* v_a_517_ = stack[11].m_obj;
lean_object* v_res_643_;
v_res_643_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f(v_e_506_, v_a_507_, v_a_508_, v_a_509_, v_a_510_, v_a_511_, v_a_512_, v_a_513_, v_a_514_, v_a_515_, v_a_516_, v_a_517_);
stack->m_obj
 = v_res_643_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f___boxed(lean_object* v_e_644_, lean_object* v_a_645_, lean_object* v_a_646_, lean_object* v_a_647_, lean_object* v_a_648_, lean_object* v_a_649_, lean_object* v_a_650_, lean_object* v_a_651_, lean_object* v_a_652_, lean_object* v_a_653_, lean_object* v_a_654_, lean_object* v_a_655_, lean_object* v_a_656_){
_start:
{
lean_object* v_res_657_; 
v_res_657_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f(v_e_644_, v_a_645_, v_a_646_, v_a_647_, v_a_648_, v_a_649_, v_a_650_, v_a_651_, v_a_652_, v_a_653_, v_a_654_, v_a_655_);
lean_dec(v_a_655_);
lean_dec_ref(v_a_654_);
lean_dec(v_a_653_);
lean_dec_ref(v_a_652_);
lean_dec(v_a_651_);
lean_dec_ref(v_a_650_);
lean_dec(v_a_649_);
lean_dec_ref(v_a_648_);
lean_dec(v_a_647_);
lean_dec(v_a_646_);
lean_dec_ref(v_a_645_);
return v_res_657_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__2_spec__3_spec__4(lean_object* v_00_u03b1_658_, lean_object* v_msg_659_, lean_object* v___y_660_, lean_object* v___y_661_, lean_object* v___y_662_, lean_object* v___y_663_, lean_object* v___y_664_, lean_object* v___y_665_, lean_object* v___y_666_, lean_object* v___y_667_, lean_object* v___y_668_, lean_object* v___y_669_, lean_object* v___y_670_){
_start:
{
lean_object* v___x_672_; 
v___x_672_ = l_Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__2_spec__3_spec__4___redArg(v_msg_659_, v___y_667_, v___y_668_, v___y_669_, v___y_670_);
return v___x_672_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_659_ = stack[1].m_obj;
lean_object* v___y_660_ = stack[2].m_obj;
lean_object* v___y_661_ = stack[3].m_obj;
lean_object* v___y_662_ = stack[4].m_obj;
lean_object* v___y_663_ = stack[5].m_obj;
lean_object* v___y_664_ = stack[6].m_obj;
lean_object* v___y_665_ = stack[7].m_obj;
lean_object* v___y_666_ = stack[8].m_obj;
lean_object* v___y_667_ = stack[9].m_obj;
lean_object* v___y_668_ = stack[10].m_obj;
lean_object* v___y_669_ = stack[11].m_obj;
lean_object* v___y_670_ = stack[12].m_obj;
lean_object* v_res_673_;
v_res_673_ = l_Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__2_spec__3_spec__4(lean_box(0), v_msg_659_, v___y_660_, v___y_661_, v___y_662_, v___y_663_, v___y_664_, v___y_665_, v___y_666_, v___y_667_, v___y_668_, v___y_669_, v___y_670_);
stack->m_obj
 = v_res_673_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__2_spec__3_spec__4___boxed(lean_object* v_00_u03b1_674_, lean_object* v_msg_675_, lean_object* v___y_676_, lean_object* v___y_677_, lean_object* v___y_678_, lean_object* v___y_679_, lean_object* v___y_680_, lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_){
_start:
{
lean_object* v_res_688_; 
v_res_688_ = l_Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__2_spec__3_spec__4(v_00_u03b1_674_, v_msg_675_, v___y_676_, v___y_677_, v___y_678_, v___y_679_, v___y_680_, v___y_681_, v___y_682_, v___y_683_, v___y_684_, v___y_685_, v___y_686_);
lean_dec(v___y_686_);
lean_dec_ref(v___y_685_);
lean_dec(v___y_684_);
lean_dec_ref(v___y_683_);
lean_dec(v___y_682_);
lean_dec_ref(v___y_681_);
lean_dec(v___y_680_);
lean_dec_ref(v___y_679_);
lean_dec(v___y_678_);
lean_dec(v___y_677_);
lean_dec_ref(v___y_676_);
return v_res_688_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___lam__0(lean_object* v_a_689_, lean_object* v_s_690_){
_start:
{
lean_object* v_toRing_691_; lean_object* v_divFn_x3f_692_; lean_object* v_semiringId_x3f_693_; lean_object* v_commSemiringInst_694_; lean_object* v_commRingInst_695_; lean_object* v_noZeroDivInst_x3f_696_; lean_object* v_fieldInst_x3f_697_; lean_object* v_powIdentityInst_x3f_698_; lean_object* v___x_700_; uint8_t v_isShared_701_; uint8_t v_isSharedCheck_706_; 
v_toRing_691_ = lean_ctor_get(v_s_690_, 0);
v_divFn_x3f_692_ = lean_ctor_get(v_s_690_, 2);
v_semiringId_x3f_693_ = lean_ctor_get(v_s_690_, 3);
v_commSemiringInst_694_ = lean_ctor_get(v_s_690_, 4);
v_commRingInst_695_ = lean_ctor_get(v_s_690_, 5);
v_noZeroDivInst_x3f_696_ = lean_ctor_get(v_s_690_, 6);
v_fieldInst_x3f_697_ = lean_ctor_get(v_s_690_, 7);
v_powIdentityInst_x3f_698_ = lean_ctor_get(v_s_690_, 8);
v_isSharedCheck_706_ = !lean_is_exclusive(v_s_690_);
if (v_isSharedCheck_706_ == 0)
{
lean_object* v_unused_707_; 
v_unused_707_ = lean_ctor_get(v_s_690_, 1);
lean_dec(v_unused_707_);
v___x_700_ = v_s_690_;
v_isShared_701_ = v_isSharedCheck_706_;
goto v_resetjp_699_;
}
else
{
lean_inc(v_powIdentityInst_x3f_698_);
lean_inc(v_fieldInst_x3f_697_);
lean_inc(v_noZeroDivInst_x3f_696_);
lean_inc(v_commRingInst_695_);
lean_inc(v_commSemiringInst_694_);
lean_inc(v_semiringId_x3f_693_);
lean_inc(v_divFn_x3f_692_);
lean_inc(v_toRing_691_);
lean_dec(v_s_690_);
v___x_700_ = lean_box(0);
v_isShared_701_ = v_isSharedCheck_706_;
goto v_resetjp_699_;
}
v_resetjp_699_:
{
lean_object* v___x_702_; lean_object* v___x_704_; 
v___x_702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_702_, 0, v_a_689_);
if (v_isShared_701_ == 0)
{
lean_ctor_set(v___x_700_, 1, v___x_702_);
v___x_704_ = v___x_700_;
goto v_reusejp_703_;
}
else
{
lean_object* v_reuseFailAlloc_705_; 
v_reuseFailAlloc_705_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_705_, 0, v_toRing_691_);
lean_ctor_set(v_reuseFailAlloc_705_, 1, v___x_702_);
lean_ctor_set(v_reuseFailAlloc_705_, 2, v_divFn_x3f_692_);
lean_ctor_set(v_reuseFailAlloc_705_, 3, v_semiringId_x3f_693_);
lean_ctor_set(v_reuseFailAlloc_705_, 4, v_commSemiringInst_694_);
lean_ctor_set(v_reuseFailAlloc_705_, 5, v_commRingInst_695_);
lean_ctor_set(v_reuseFailAlloc_705_, 6, v_noZeroDivInst_x3f_696_);
lean_ctor_set(v_reuseFailAlloc_705_, 7, v_fieldInst_x3f_697_);
lean_ctor_set(v_reuseFailAlloc_705_, 8, v_powIdentityInst_x3f_698_);
v___x_704_ = v_reuseFailAlloc_705_;
goto v_reusejp_703_;
}
v_reusejp_703_:
{
return v___x_704_;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Sym_Arith_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___closed__8(void){
_start:
{
lean_object* v___x_723_; lean_object* v___x_724_; 
v___x_723_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___closed__7));
v___x_724_ = l_Lean_stringToMessageData(v___x_723_);
return v___x_724_;
}
}
lean_object* l_Lean_Meta_Sym_Arith_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0(lean_object* v___y_725_, lean_object* v___y_726_, lean_object* v___y_727_, lean_object* v___y_728_, lean_object* v___y_729_, lean_object* v___y_730_, lean_object* v___y_731_, lean_object* v___y_732_, lean_object* v___y_733_, lean_object* v___y_734_, lean_object* v___y_735_){
_start:
{
lean_object* v___x_737_; 
v___x_737_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v___y_725_, v___y_726_, v___y_727_, v___y_728_, v___y_729_, v___y_730_, v___y_731_, v___y_732_, v___y_733_, v___y_734_, v___y_735_);
if (lean_obj_tag(v___x_737_) == 0)
{
lean_object* v_a_738_; lean_object* v___x_740_; uint8_t v_isShared_741_; uint8_t v_isSharedCheck_785_; 
v_a_738_ = lean_ctor_get(v___x_737_, 0);
v_isSharedCheck_785_ = !lean_is_exclusive(v___x_737_);
if (v_isSharedCheck_785_ == 0)
{
v___x_740_ = v___x_737_;
v_isShared_741_ = v_isSharedCheck_785_;
goto v_resetjp_739_;
}
else
{
lean_inc(v_a_738_);
lean_dec(v___x_737_);
v___x_740_ = lean_box(0);
v_isShared_741_ = v_isSharedCheck_785_;
goto v_resetjp_739_;
}
v_resetjp_739_:
{
lean_object* v_fieldInst_x3f_742_; 
v_fieldInst_x3f_742_ = lean_ctor_get(v_a_738_, 7);
if (lean_obj_tag(v_fieldInst_x3f_742_) == 1)
{
lean_object* v_invFn_x3f_743_; 
lean_inc_ref(v_fieldInst_x3f_742_);
v_invFn_x3f_743_ = lean_ctor_get(v_a_738_, 1);
if (lean_obj_tag(v_invFn_x3f_743_) == 1)
{
lean_object* v_val_744_; lean_object* v___x_746_; 
lean_inc_ref(v_invFn_x3f_743_);
lean_dec_ref_known(v_fieldInst_x3f_742_, 1);
lean_dec(v_a_738_);
v_val_744_ = lean_ctor_get(v_invFn_x3f_743_, 0);
lean_inc(v_val_744_);
lean_dec_ref_known(v_invFn_x3f_743_, 1);
if (v_isShared_741_ == 0)
{
lean_ctor_set(v___x_740_, 0, v_val_744_);
v___x_746_ = v___x_740_;
goto v_reusejp_745_;
}
else
{
lean_object* v_reuseFailAlloc_747_; 
v_reuseFailAlloc_747_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_747_, 0, v_val_744_);
v___x_746_ = v_reuseFailAlloc_747_;
goto v_reusejp_745_;
}
v_reusejp_745_:
{
return v___x_746_;
}
}
else
{
lean_object* v_toRing_748_; lean_object* v_val_749_; lean_object* v_type_750_; lean_object* v_u_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v_expectedInst_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; 
lean_del_object(v___x_740_);
v_toRing_748_ = lean_ctor_get(v_a_738_, 0);
lean_inc_ref(v_toRing_748_);
lean_dec(v_a_738_);
v_val_749_ = lean_ctor_get(v_fieldInst_x3f_742_, 0);
lean_inc(v_val_749_);
lean_dec_ref_known(v_fieldInst_x3f_742_, 1);
v_type_750_ = lean_ctor_get(v_toRing_748_, 1);
lean_inc_ref_n(v_type_750_, 2);
v_u_751_ = lean_ctor_get(v_toRing_748_, 2);
lean_inc_n(v_u_751_, 2);
lean_dec_ref(v_toRing_748_);
v___x_752_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___closed__2));
v___x_753_ = lean_box(0);
v___x_754_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_754_, 0, v_u_751_);
lean_ctor_set(v___x_754_, 1, v___x_753_);
v___x_755_ = l_Lean_mkConst(v___x_752_, v___x_754_);
v_expectedInst_756_ = l_Lean_mkAppB(v___x_755_, v_type_750_, v_val_749_);
v___x_757_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___closed__4));
v___x_758_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___closed__6));
v___x_759_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__2(v_type_750_, v_u_751_, v___x_757_, v___x_758_, v_expectedInst_756_, v___y_725_, v___y_726_, v___y_727_, v___y_728_, v___y_729_, v___y_730_, v___y_731_, v___y_732_, v___y_733_, v___y_734_, v___y_735_);
if (lean_obj_tag(v___x_759_) == 0)
{
lean_object* v_a_760_; lean_object* v___f_761_; lean_object* v___x_762_; 
v_a_760_ = lean_ctor_get(v___x_759_, 0);
lean_inc_n(v_a_760_, 2);
lean_dec_ref_known(v___x_759_, 1);
v___f_761_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___lam__0), 2, 1);
lean_closure_set(v___f_761_, 0, v_a_760_);
v___x_762_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(v___f_761_, v___y_725_, v___y_731_);
if (lean_obj_tag(v___x_762_) == 0)
{
lean_object* v___x_764_; uint8_t v_isShared_765_; uint8_t v_isSharedCheck_769_; 
v_isSharedCheck_769_ = !lean_is_exclusive(v___x_762_);
if (v_isSharedCheck_769_ == 0)
{
lean_object* v_unused_770_; 
v_unused_770_ = lean_ctor_get(v___x_762_, 0);
lean_dec(v_unused_770_);
v___x_764_ = v___x_762_;
v_isShared_765_ = v_isSharedCheck_769_;
goto v_resetjp_763_;
}
else
{
lean_dec(v___x_762_);
v___x_764_ = lean_box(0);
v_isShared_765_ = v_isSharedCheck_769_;
goto v_resetjp_763_;
}
v_resetjp_763_:
{
lean_object* v___x_767_; 
if (v_isShared_765_ == 0)
{
lean_ctor_set(v___x_764_, 0, v_a_760_);
v___x_767_ = v___x_764_;
goto v_reusejp_766_;
}
else
{
lean_object* v_reuseFailAlloc_768_; 
v_reuseFailAlloc_768_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_768_, 0, v_a_760_);
v___x_767_ = v_reuseFailAlloc_768_;
goto v_reusejp_766_;
}
v_reusejp_766_:
{
return v___x_767_;
}
}
}
else
{
lean_object* v_a_771_; lean_object* v___x_773_; uint8_t v_isShared_774_; uint8_t v_isSharedCheck_778_; 
lean_dec(v_a_760_);
v_a_771_ = lean_ctor_get(v___x_762_, 0);
v_isSharedCheck_778_ = !lean_is_exclusive(v___x_762_);
if (v_isSharedCheck_778_ == 0)
{
v___x_773_ = v___x_762_;
v_isShared_774_ = v_isSharedCheck_778_;
goto v_resetjp_772_;
}
else
{
lean_inc(v_a_771_);
lean_dec(v___x_762_);
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
else
{
return v___x_759_;
}
}
}
else
{
lean_object* v_toRing_779_; lean_object* v_type_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; 
lean_del_object(v___x_740_);
v_toRing_779_ = lean_ctor_get(v_a_738_, 0);
lean_inc_ref(v_toRing_779_);
lean_dec(v_a_738_);
v_type_780_ = lean_ctor_get(v_toRing_779_, 1);
lean_inc_ref(v_type_780_);
lean_dec_ref(v_toRing_779_);
v___x_781_ = lean_obj_once(&l_Lean_Meta_Sym_Arith_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___closed__8, &l_Lean_Meta_Sym_Arith_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___closed__8_once, _init_l_Lean_Meta_Sym_Arith_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___closed__8);
v___x_782_ = l_Lean_indentExpr(v_type_780_);
v___x_783_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_783_, 0, v___x_781_);
lean_ctor_set(v___x_783_, 1, v___x_782_);
v___x_784_ = l_Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__2_spec__3_spec__4___redArg(v___x_783_, v___y_732_, v___y_733_, v___y_734_, v___y_735_);
return v___x_784_;
}
}
}
else
{
lean_object* v_a_786_; lean_object* v___x_788_; uint8_t v_isShared_789_; uint8_t v_isSharedCheck_793_; 
v_a_786_ = lean_ctor_get(v___x_737_, 0);
v_isSharedCheck_793_ = !lean_is_exclusive(v___x_737_);
if (v_isSharedCheck_793_ == 0)
{
v___x_788_ = v___x_737_;
v_isShared_789_ = v_isSharedCheck_793_;
goto v_resetjp_787_;
}
else
{
lean_inc(v_a_786_);
lean_dec(v___x_737_);
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
}
LEAN_EXPORT void l_Lean_Meta_Sym_Arith_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_725_ = stack[0].m_obj;
lean_object* v___y_726_ = stack[1].m_obj;
lean_object* v___y_727_ = stack[2].m_obj;
lean_object* v___y_728_ = stack[3].m_obj;
lean_object* v___y_729_ = stack[4].m_obj;
lean_object* v___y_730_ = stack[5].m_obj;
lean_object* v___y_731_ = stack[6].m_obj;
lean_object* v___y_732_ = stack[7].m_obj;
lean_object* v___y_733_ = stack[8].m_obj;
lean_object* v___y_734_ = stack[9].m_obj;
lean_object* v___y_735_ = stack[10].m_obj;
lean_object* v_res_794_;
v_res_794_ = l_Lean_Meta_Sym_Arith_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0(v___y_725_, v___y_726_, v___y_727_, v___y_728_, v___y_729_, v___y_730_, v___y_731_, v___y_732_, v___y_733_, v___y_734_, v___y_735_);
stack->m_obj
 = v_res_794_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___boxed(lean_object* v___y_795_, lean_object* v___y_796_, lean_object* v___y_797_, lean_object* v___y_798_, lean_object* v___y_799_, lean_object* v___y_800_, lean_object* v___y_801_, lean_object* v___y_802_, lean_object* v___y_803_, lean_object* v___y_804_, lean_object* v___y_805_, lean_object* v___y_806_){
_start:
{
lean_object* v_res_807_; 
v_res_807_ = l_Lean_Meta_Sym_Arith_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0(v___y_795_, v___y_796_, v___y_797_, v___y_798_, v___y_799_, v___y_800_, v___y_801_, v___y_802_, v___y_803_, v___y_804_, v___y_805_);
lean_dec(v___y_805_);
lean_dec_ref(v___y_804_);
lean_dec(v___y_803_);
lean_dec_ref(v___y_802_);
lean_dec(v___y_801_);
lean_dec_ref(v___y_800_);
lean_dec(v___y_799_);
lean_dec_ref(v___y_798_);
lean_dec(v___y_797_);
lean_dec(v___y_796_);
lean_dec_ref(v___y_795_);
return v_res_807_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst(lean_object* v_inst_808_, lean_object* v_a_809_, lean_object* v_a_810_, lean_object* v_a_811_, lean_object* v_a_812_, lean_object* v_a_813_, lean_object* v_a_814_, lean_object* v_a_815_, lean_object* v_a_816_, lean_object* v_a_817_, lean_object* v_a_818_, lean_object* v_a_819_){
_start:
{
lean_object* v___x_821_; 
v___x_821_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v_a_809_, v_a_810_, v_a_811_, v_a_812_, v_a_813_, v_a_814_, v_a_815_, v_a_816_, v_a_817_, v_a_818_, v_a_819_);
if (lean_obj_tag(v___x_821_) == 0)
{
lean_object* v_a_822_; lean_object* v___x_824_; uint8_t v_isShared_825_; uint8_t v_isSharedCheck_854_; 
v_a_822_ = lean_ctor_get(v___x_821_, 0);
v_isSharedCheck_854_ = !lean_is_exclusive(v___x_821_);
if (v_isSharedCheck_854_ == 0)
{
v___x_824_ = v___x_821_;
v_isShared_825_ = v_isSharedCheck_854_;
goto v_resetjp_823_;
}
else
{
lean_inc(v_a_822_);
lean_dec(v___x_821_);
v___x_824_ = lean_box(0);
v_isShared_825_ = v_isSharedCheck_854_;
goto v_resetjp_823_;
}
v_resetjp_823_:
{
lean_object* v_fieldInst_x3f_826_; 
v_fieldInst_x3f_826_ = lean_ctor_get(v_a_822_, 7);
lean_inc(v_fieldInst_x3f_826_);
lean_dec(v_a_822_);
if (lean_obj_tag(v_fieldInst_x3f_826_) == 0)
{
uint8_t v___x_827_; lean_object* v___x_828_; lean_object* v___x_830_; 
v___x_827_ = 0;
v___x_828_ = lean_box(v___x_827_);
if (v_isShared_825_ == 0)
{
lean_ctor_set(v___x_824_, 0, v___x_828_);
v___x_830_ = v___x_824_;
goto v_reusejp_829_;
}
else
{
lean_object* v_reuseFailAlloc_831_; 
v_reuseFailAlloc_831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_831_, 0, v___x_828_);
v___x_830_ = v_reuseFailAlloc_831_;
goto v_reusejp_829_;
}
v_reusejp_829_:
{
return v___x_830_;
}
}
else
{
lean_object* v___x_832_; 
lean_dec_ref_known(v_fieldInst_x3f_826_, 1);
lean_del_object(v___x_824_);
v___x_832_ = l_Lean_Meta_Sym_Arith_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0(v_a_809_, v_a_810_, v_a_811_, v_a_812_, v_a_813_, v_a_814_, v_a_815_, v_a_816_, v_a_817_, v_a_818_, v_a_819_);
if (lean_obj_tag(v___x_832_) == 0)
{
lean_object* v_a_833_; lean_object* v___x_835_; uint8_t v_isShared_836_; uint8_t v_isSharedCheck_845_; 
v_a_833_ = lean_ctor_get(v___x_832_, 0);
v_isSharedCheck_845_ = !lean_is_exclusive(v___x_832_);
if (v_isSharedCheck_845_ == 0)
{
v___x_835_ = v___x_832_;
v_isShared_836_ = v_isSharedCheck_845_;
goto v_resetjp_834_;
}
else
{
lean_inc(v_a_833_);
lean_dec(v___x_832_);
v___x_835_ = lean_box(0);
v_isShared_836_ = v_isSharedCheck_845_;
goto v_resetjp_834_;
}
v_resetjp_834_:
{
lean_object* v___x_837_; size_t v___x_838_; size_t v___x_839_; uint8_t v___x_840_; lean_object* v___x_841_; lean_object* v___x_843_; 
v___x_837_ = l_Lean_Expr_appArg_x21(v_a_833_);
lean_dec(v_a_833_);
v___x_838_ = lean_ptr_addr(v___x_837_);
lean_dec_ref(v___x_837_);
v___x_839_ = lean_ptr_addr(v_inst_808_);
v___x_840_ = lean_usize_dec_eq(v___x_838_, v___x_839_);
v___x_841_ = lean_box(v___x_840_);
if (v_isShared_836_ == 0)
{
lean_ctor_set(v___x_835_, 0, v___x_841_);
v___x_843_ = v___x_835_;
goto v_reusejp_842_;
}
else
{
lean_object* v_reuseFailAlloc_844_; 
v_reuseFailAlloc_844_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_844_, 0, v___x_841_);
v___x_843_ = v_reuseFailAlloc_844_;
goto v_reusejp_842_;
}
v_reusejp_842_:
{
return v___x_843_;
}
}
}
else
{
lean_object* v_a_846_; lean_object* v___x_848_; uint8_t v_isShared_849_; uint8_t v_isSharedCheck_853_; 
v_a_846_ = lean_ctor_get(v___x_832_, 0);
v_isSharedCheck_853_ = !lean_is_exclusive(v___x_832_);
if (v_isSharedCheck_853_ == 0)
{
v___x_848_ = v___x_832_;
v_isShared_849_ = v_isSharedCheck_853_;
goto v_resetjp_847_;
}
else
{
lean_inc(v_a_846_);
lean_dec(v___x_832_);
v___x_848_ = lean_box(0);
v_isShared_849_ = v_isSharedCheck_853_;
goto v_resetjp_847_;
}
v_resetjp_847_:
{
lean_object* v___x_851_; 
if (v_isShared_849_ == 0)
{
v___x_851_ = v___x_848_;
goto v_reusejp_850_;
}
else
{
lean_object* v_reuseFailAlloc_852_; 
v_reuseFailAlloc_852_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_852_, 0, v_a_846_);
v___x_851_ = v_reuseFailAlloc_852_;
goto v_reusejp_850_;
}
v_reusejp_850_:
{
return v___x_851_;
}
}
}
}
}
}
else
{
lean_object* v_a_855_; lean_object* v___x_857_; uint8_t v_isShared_858_; uint8_t v_isSharedCheck_862_; 
v_a_855_ = lean_ctor_get(v___x_821_, 0);
v_isSharedCheck_862_ = !lean_is_exclusive(v___x_821_);
if (v_isSharedCheck_862_ == 0)
{
v___x_857_ = v___x_821_;
v_isShared_858_ = v_isSharedCheck_862_;
goto v_resetjp_856_;
}
else
{
lean_inc(v_a_855_);
lean_dec(v___x_821_);
v___x_857_ = lean_box(0);
v_isShared_858_ = v_isSharedCheck_862_;
goto v_resetjp_856_;
}
v_resetjp_856_:
{
lean_object* v___x_860_; 
if (v_isShared_858_ == 0)
{
v___x_860_ = v___x_857_;
goto v_reusejp_859_;
}
else
{
lean_object* v_reuseFailAlloc_861_; 
v_reuseFailAlloc_861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_861_, 0, v_a_855_);
v___x_860_ = v_reuseFailAlloc_861_;
goto v_reusejp_859_;
}
v_reusejp_859_:
{
return v___x_860_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_808_ = stack[0].m_obj;
lean_object* v_a_809_ = stack[1].m_obj;
lean_object* v_a_810_ = stack[2].m_obj;
lean_object* v_a_811_ = stack[3].m_obj;
lean_object* v_a_812_ = stack[4].m_obj;
lean_object* v_a_813_ = stack[5].m_obj;
lean_object* v_a_814_ = stack[6].m_obj;
lean_object* v_a_815_ = stack[7].m_obj;
lean_object* v_a_816_ = stack[8].m_obj;
lean_object* v_a_817_ = stack[9].m_obj;
lean_object* v_a_818_ = stack[10].m_obj;
lean_object* v_a_819_ = stack[11].m_obj;
lean_object* v_res_863_;
v_res_863_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst(v_inst_808_, v_a_809_, v_a_810_, v_a_811_, v_a_812_, v_a_813_, v_a_814_, v_a_815_, v_a_816_, v_a_817_, v_a_818_, v_a_819_);
stack->m_obj
 = v_res_863_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst___boxed(lean_object* v_inst_864_, lean_object* v_a_865_, lean_object* v_a_866_, lean_object* v_a_867_, lean_object* v_a_868_, lean_object* v_a_869_, lean_object* v_a_870_, lean_object* v_a_871_, lean_object* v_a_872_, lean_object* v_a_873_, lean_object* v_a_874_, lean_object* v_a_875_, lean_object* v_a_876_){
_start:
{
lean_object* v_res_877_; 
v_res_877_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst(v_inst_864_, v_a_865_, v_a_866_, v_a_867_, v_a_868_, v_a_869_, v_a_870_, v_a_871_, v_a_872_, v_a_873_, v_a_874_, v_a_875_);
lean_dec(v_a_875_);
lean_dec_ref(v_a_874_);
lean_dec(v_a_873_);
lean_dec_ref(v_a_872_);
lean_dec(v_a_871_);
lean_dec_ref(v_a_870_);
lean_dec(v_a_869_);
lean_dec_ref(v_a_868_);
lean_dec(v_a_867_);
lean_dec(v_a_866_);
lean_dec_ref(v_a_865_);
lean_dec_ref(v_inst_864_);
return v_res_877_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0_spec__1_spec__5___redArg(lean_object* v_x_878_, lean_object* v_x_879_, lean_object* v_x_880_, lean_object* v_x_881_){
_start:
{
lean_object* v_ks_882_; lean_object* v_vs_883_; lean_object* v___x_885_; uint8_t v_isShared_886_; uint8_t v_isSharedCheck_907_; 
v_ks_882_ = lean_ctor_get(v_x_878_, 0);
v_vs_883_ = lean_ctor_get(v_x_878_, 1);
v_isSharedCheck_907_ = !lean_is_exclusive(v_x_878_);
if (v_isSharedCheck_907_ == 0)
{
v___x_885_ = v_x_878_;
v_isShared_886_ = v_isSharedCheck_907_;
goto v_resetjp_884_;
}
else
{
lean_inc(v_vs_883_);
lean_inc(v_ks_882_);
lean_dec(v_x_878_);
v___x_885_ = lean_box(0);
v_isShared_886_ = v_isSharedCheck_907_;
goto v_resetjp_884_;
}
v_resetjp_884_:
{
lean_object* v___x_887_; uint8_t v___x_888_; 
v___x_887_ = lean_array_get_size(v_ks_882_);
v___x_888_ = lean_nat_dec_lt(v_x_879_, v___x_887_);
if (v___x_888_ == 0)
{
lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_892_; 
lean_dec(v_x_879_);
v___x_889_ = lean_array_push(v_ks_882_, v_x_880_);
v___x_890_ = lean_array_push(v_vs_883_, v_x_881_);
if (v_isShared_886_ == 0)
{
lean_ctor_set(v___x_885_, 1, v___x_890_);
lean_ctor_set(v___x_885_, 0, v___x_889_);
v___x_892_ = v___x_885_;
goto v_reusejp_891_;
}
else
{
lean_object* v_reuseFailAlloc_893_; 
v_reuseFailAlloc_893_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_893_, 0, v___x_889_);
lean_ctor_set(v_reuseFailAlloc_893_, 1, v___x_890_);
v___x_892_ = v_reuseFailAlloc_893_;
goto v_reusejp_891_;
}
v_reusejp_891_:
{
return v___x_892_;
}
}
else
{
lean_object* v_k_x27_894_; uint8_t v___x_895_; 
v_k_x27_894_ = lean_array_fget_borrowed(v_ks_882_, v_x_879_);
v___x_895_ = lean_expr_eqv(v_x_880_, v_k_x27_894_);
if (v___x_895_ == 0)
{
lean_object* v___x_897_; 
if (v_isShared_886_ == 0)
{
v___x_897_ = v___x_885_;
goto v_reusejp_896_;
}
else
{
lean_object* v_reuseFailAlloc_901_; 
v_reuseFailAlloc_901_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_901_, 0, v_ks_882_);
lean_ctor_set(v_reuseFailAlloc_901_, 1, v_vs_883_);
v___x_897_ = v_reuseFailAlloc_901_;
goto v_reusejp_896_;
}
v_reusejp_896_:
{
lean_object* v___x_898_; lean_object* v___x_899_; 
v___x_898_ = lean_unsigned_to_nat(1u);
v___x_899_ = lean_nat_add(v_x_879_, v___x_898_);
lean_dec(v_x_879_);
v_x_878_ = v___x_897_;
v_x_879_ = v___x_899_;
goto _start;
}
}
else
{
lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_905_; 
v___x_902_ = lean_array_fset(v_ks_882_, v_x_879_, v_x_880_);
v___x_903_ = lean_array_fset(v_vs_883_, v_x_879_, v_x_881_);
lean_dec(v_x_879_);
if (v_isShared_886_ == 0)
{
lean_ctor_set(v___x_885_, 1, v___x_903_);
lean_ctor_set(v___x_885_, 0, v___x_902_);
v___x_905_ = v___x_885_;
goto v_reusejp_904_;
}
else
{
lean_object* v_reuseFailAlloc_906_; 
v_reuseFailAlloc_906_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_906_, 0, v___x_902_);
lean_ctor_set(v_reuseFailAlloc_906_, 1, v___x_903_);
v___x_905_ = v_reuseFailAlloc_906_;
goto v_reusejp_904_;
}
v_reusejp_904_:
{
return v___x_905_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0_spec__1___redArg(lean_object* v_n_908_, lean_object* v_k_909_, lean_object* v_v_910_){
_start:
{
lean_object* v___x_911_; lean_object* v___x_912_; 
v___x_911_ = lean_unsigned_to_nat(0u);
v___x_912_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0_spec__1_spec__5___redArg(v_n_908_, v___x_911_, v_k_909_, v_v_910_);
return v___x_912_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_913_; 
v___x_913_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_913_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg(lean_object* v_x_914_, size_t v_x_915_, size_t v_x_916_, lean_object* v_x_917_, lean_object* v_x_918_){
_start:
{
if (lean_obj_tag(v_x_914_) == 0)
{
lean_object* v_es_919_; size_t v___x_920_; size_t v___x_921_; lean_object* v_j_922_; lean_object* v___x_923_; uint8_t v___x_924_; 
v_es_919_ = lean_ctor_get(v_x_914_, 0);
v___x_920_ = ((size_t)31ULL);
v___x_921_ = lean_usize_land(v_x_915_, v___x_920_);
v_j_922_ = lean_usize_to_nat(v___x_921_);
v___x_923_ = lean_array_get_size(v_es_919_);
v___x_924_ = lean_nat_dec_lt(v_j_922_, v___x_923_);
if (v___x_924_ == 0)
{
lean_dec(v_j_922_);
lean_dec(v_x_918_);
lean_dec_ref(v_x_917_);
return v_x_914_;
}
else
{
lean_object* v___x_926_; uint8_t v_isShared_927_; uint8_t v_isSharedCheck_963_; 
lean_inc_ref(v_es_919_);
v_isSharedCheck_963_ = !lean_is_exclusive(v_x_914_);
if (v_isSharedCheck_963_ == 0)
{
lean_object* v_unused_964_; 
v_unused_964_ = lean_ctor_get(v_x_914_, 0);
lean_dec(v_unused_964_);
v___x_926_ = v_x_914_;
v_isShared_927_ = v_isSharedCheck_963_;
goto v_resetjp_925_;
}
else
{
lean_dec(v_x_914_);
v___x_926_ = lean_box(0);
v_isShared_927_ = v_isSharedCheck_963_;
goto v_resetjp_925_;
}
v_resetjp_925_:
{
lean_object* v_v_928_; lean_object* v___x_929_; lean_object* v_xs_x27_930_; lean_object* v___y_932_; 
v_v_928_ = lean_array_fget(v_es_919_, v_j_922_);
v___x_929_ = lean_box(0);
v_xs_x27_930_ = lean_array_fset(v_es_919_, v_j_922_, v___x_929_);
switch(lean_obj_tag(v_v_928_))
{
case 0:
{
lean_object* v_key_937_; lean_object* v_val_938_; lean_object* v___x_940_; uint8_t v_isShared_941_; uint8_t v_isSharedCheck_948_; 
v_key_937_ = lean_ctor_get(v_v_928_, 0);
v_val_938_ = lean_ctor_get(v_v_928_, 1);
v_isSharedCheck_948_ = !lean_is_exclusive(v_v_928_);
if (v_isSharedCheck_948_ == 0)
{
v___x_940_ = v_v_928_;
v_isShared_941_ = v_isSharedCheck_948_;
goto v_resetjp_939_;
}
else
{
lean_inc(v_val_938_);
lean_inc(v_key_937_);
lean_dec(v_v_928_);
v___x_940_ = lean_box(0);
v_isShared_941_ = v_isSharedCheck_948_;
goto v_resetjp_939_;
}
v_resetjp_939_:
{
uint8_t v___x_942_; 
v___x_942_ = lean_expr_eqv(v_x_917_, v_key_937_);
if (v___x_942_ == 0)
{
lean_object* v___x_943_; lean_object* v___x_944_; 
lean_del_object(v___x_940_);
v___x_943_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_937_, v_val_938_, v_x_917_, v_x_918_);
v___x_944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_944_, 0, v___x_943_);
v___y_932_ = v___x_944_;
goto v___jp_931_;
}
else
{
lean_object* v___x_946_; 
lean_dec(v_val_938_);
lean_dec(v_key_937_);
if (v_isShared_941_ == 0)
{
lean_ctor_set(v___x_940_, 1, v_x_918_);
lean_ctor_set(v___x_940_, 0, v_x_917_);
v___x_946_ = v___x_940_;
goto v_reusejp_945_;
}
else
{
lean_object* v_reuseFailAlloc_947_; 
v_reuseFailAlloc_947_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_947_, 0, v_x_917_);
lean_ctor_set(v_reuseFailAlloc_947_, 1, v_x_918_);
v___x_946_ = v_reuseFailAlloc_947_;
goto v_reusejp_945_;
}
v_reusejp_945_:
{
v___y_932_ = v___x_946_;
goto v___jp_931_;
}
}
}
}
case 1:
{
lean_object* v_node_949_; lean_object* v___x_951_; uint8_t v_isShared_952_; uint8_t v_isSharedCheck_961_; 
v_node_949_ = lean_ctor_get(v_v_928_, 0);
v_isSharedCheck_961_ = !lean_is_exclusive(v_v_928_);
if (v_isSharedCheck_961_ == 0)
{
v___x_951_ = v_v_928_;
v_isShared_952_ = v_isSharedCheck_961_;
goto v_resetjp_950_;
}
else
{
lean_inc(v_node_949_);
lean_dec(v_v_928_);
v___x_951_ = lean_box(0);
v_isShared_952_ = v_isSharedCheck_961_;
goto v_resetjp_950_;
}
v_resetjp_950_:
{
size_t v___x_953_; size_t v___x_954_; size_t v___x_955_; size_t v___x_956_; lean_object* v___x_957_; lean_object* v___x_959_; 
v___x_953_ = ((size_t)5ULL);
v___x_954_ = lean_usize_shift_right(v_x_915_, v___x_953_);
v___x_955_ = ((size_t)1ULL);
v___x_956_ = lean_usize_add(v_x_916_, v___x_955_);
v___x_957_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg(v_node_949_, v___x_954_, v___x_956_, v_x_917_, v_x_918_);
if (v_isShared_952_ == 0)
{
lean_ctor_set(v___x_951_, 0, v___x_957_);
v___x_959_ = v___x_951_;
goto v_reusejp_958_;
}
else
{
lean_object* v_reuseFailAlloc_960_; 
v_reuseFailAlloc_960_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_960_, 0, v___x_957_);
v___x_959_ = v_reuseFailAlloc_960_;
goto v_reusejp_958_;
}
v_reusejp_958_:
{
v___y_932_ = v___x_959_;
goto v___jp_931_;
}
}
}
default: 
{
lean_object* v___x_962_; 
v___x_962_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_962_, 0, v_x_917_);
lean_ctor_set(v___x_962_, 1, v_x_918_);
v___y_932_ = v___x_962_;
goto v___jp_931_;
}
}
v___jp_931_:
{
lean_object* v___x_933_; lean_object* v___x_935_; 
v___x_933_ = lean_array_fset(v_xs_x27_930_, v_j_922_, v___y_932_);
lean_dec(v_j_922_);
if (v_isShared_927_ == 0)
{
lean_ctor_set(v___x_926_, 0, v___x_933_);
v___x_935_ = v___x_926_;
goto v_reusejp_934_;
}
else
{
lean_object* v_reuseFailAlloc_936_; 
v_reuseFailAlloc_936_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_936_, 0, v___x_933_);
v___x_935_ = v_reuseFailAlloc_936_;
goto v_reusejp_934_;
}
v_reusejp_934_:
{
return v___x_935_;
}
}
}
}
}
else
{
lean_object* v_ks_965_; lean_object* v_vs_966_; lean_object* v___x_968_; uint8_t v_isShared_969_; uint8_t v_isSharedCheck_984_; 
v_ks_965_ = lean_ctor_get(v_x_914_, 0);
v_vs_966_ = lean_ctor_get(v_x_914_, 1);
v_isSharedCheck_984_ = !lean_is_exclusive(v_x_914_);
if (v_isSharedCheck_984_ == 0)
{
v___x_968_ = v_x_914_;
v_isShared_969_ = v_isSharedCheck_984_;
goto v_resetjp_967_;
}
else
{
lean_inc(v_vs_966_);
lean_inc(v_ks_965_);
lean_dec(v_x_914_);
v___x_968_ = lean_box(0);
v_isShared_969_ = v_isSharedCheck_984_;
goto v_resetjp_967_;
}
v_resetjp_967_:
{
lean_object* v___x_971_; 
if (v_isShared_969_ == 0)
{
v___x_971_ = v___x_968_;
goto v_reusejp_970_;
}
else
{
lean_object* v_reuseFailAlloc_983_; 
v_reuseFailAlloc_983_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_983_, 0, v_ks_965_);
lean_ctor_set(v_reuseFailAlloc_983_, 1, v_vs_966_);
v___x_971_ = v_reuseFailAlloc_983_;
goto v_reusejp_970_;
}
v_reusejp_970_:
{
lean_object* v_newNode_972_; size_t v___x_973_; uint8_t v___x_974_; 
v_newNode_972_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0_spec__1___redArg(v___x_971_, v_x_917_, v_x_918_);
v___x_973_ = ((size_t)7ULL);
v___x_974_ = lean_usize_dec_le(v___x_973_, v_x_916_);
if (v___x_974_ == 0)
{
lean_object* v___x_975_; lean_object* v___x_976_; uint8_t v___x_977_; 
v___x_975_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_972_);
v___x_976_ = lean_unsigned_to_nat(4u);
v___x_977_ = lean_nat_dec_lt(v___x_975_, v___x_976_);
lean_dec(v___x_975_);
if (v___x_977_ == 0)
{
lean_object* v_ks_978_; lean_object* v_vs_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; 
v_ks_978_ = lean_ctor_get(v_newNode_972_, 0);
lean_inc_ref(v_ks_978_);
v_vs_979_ = lean_ctor_get(v_newNode_972_, 1);
lean_inc_ref(v_vs_979_);
lean_dec_ref(v_newNode_972_);
v___x_980_ = lean_unsigned_to_nat(0u);
v___x_981_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg___closed__0);
v___x_982_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0_spec__2___redArg(v_x_916_, v_ks_978_, v_vs_979_, v___x_980_, v___x_981_);
lean_dec_ref(v_vs_979_);
lean_dec_ref(v_ks_978_);
return v___x_982_;
}
else
{
return v_newNode_972_;
}
}
else
{
return v_newNode_972_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_914_ = stack[0].m_obj;
size_t v_x_915_ = stack[1].m_num;
size_t v_x_916_ = stack[2].m_num;
lean_object* v_x_917_ = stack[3].m_obj;
lean_object* v_x_918_ = stack[4].m_obj;
lean_object* v_res_985_;
v_res_985_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg(v_x_914_, v_x_915_, v_x_916_, v_x_917_, v_x_918_);
stack->m_obj
 = v_res_985_;
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0_spec__2___redArg(size_t v_depth_986_, lean_object* v_keys_987_, lean_object* v_vals_988_, lean_object* v_i_989_, lean_object* v_entries_990_){
_start:
{
lean_object* v___x_991_; uint8_t v___x_992_; 
v___x_991_ = lean_array_get_size(v_keys_987_);
v___x_992_ = lean_nat_dec_lt(v_i_989_, v___x_991_);
if (v___x_992_ == 0)
{
lean_dec(v_i_989_);
return v_entries_990_;
}
else
{
lean_object* v_k_993_; lean_object* v_v_994_; uint64_t v___x_995_; size_t v_h_996_; size_t v___x_997_; lean_object* v___x_998_; size_t v___x_999_; size_t v___x_1000_; size_t v___x_1001_; size_t v_h_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; 
v_k_993_ = lean_array_fget_borrowed(v_keys_987_, v_i_989_);
v_v_994_ = lean_array_fget_borrowed(v_vals_988_, v_i_989_);
v___x_995_ = l_Lean_Expr_hash(v_k_993_);
v_h_996_ = lean_uint64_to_usize(v___x_995_);
v___x_997_ = ((size_t)5ULL);
v___x_998_ = lean_unsigned_to_nat(1u);
v___x_999_ = ((size_t)1ULL);
v___x_1000_ = lean_usize_sub(v_depth_986_, v___x_999_);
v___x_1001_ = lean_usize_mul(v___x_997_, v___x_1000_);
v_h_1002_ = lean_usize_shift_right(v_h_996_, v___x_1001_);
v___x_1003_ = lean_nat_add(v_i_989_, v___x_998_);
lean_dec(v_i_989_);
lean_inc(v_v_994_);
lean_inc(v_k_993_);
v___x_1004_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg(v_entries_990_, v_h_1002_, v_depth_986_, v_k_993_, v_v_994_);
v_i_989_ = v___x_1003_;
v_entries_990_ = v___x_1004_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_depth_986_ = stack[0].m_num;
lean_object* v_keys_987_ = stack[1].m_obj;
lean_object* v_vals_988_ = stack[2].m_obj;
lean_object* v_i_989_ = stack[3].m_obj;
lean_object* v_entries_990_ = stack[4].m_obj;
lean_object* v_res_1006_;
v_res_1006_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0_spec__2___redArg(v_depth_986_, v_keys_987_, v_vals_988_, v_i_989_, v_entries_990_);
stack->m_obj
 = v_res_1006_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_1007_, lean_object* v_keys_1008_, lean_object* v_vals_1009_, lean_object* v_i_1010_, lean_object* v_entries_1011_){
_start:
{
size_t v_depth_boxed_1012_; lean_object* v_res_1013_; 
v_depth_boxed_1012_ = lean_unbox_usize(v_depth_1007_);
lean_dec(v_depth_1007_);
v_res_1013_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0_spec__2___redArg(v_depth_boxed_1012_, v_keys_1008_, v_vals_1009_, v_i_1010_, v_entries_1011_);
lean_dec_ref(v_vals_1009_);
lean_dec_ref(v_keys_1008_);
return v_res_1013_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg___boxed(lean_object* v_x_1014_, lean_object* v_x_1015_, lean_object* v_x_1016_, lean_object* v_x_1017_, lean_object* v_x_1018_){
_start:
{
size_t v_x_79695__boxed_1019_; size_t v_x_79696__boxed_1020_; lean_object* v_res_1021_; 
v_x_79695__boxed_1019_ = lean_unbox_usize(v_x_1015_);
lean_dec(v_x_1015_);
v_x_79696__boxed_1020_ = lean_unbox_usize(v_x_1016_);
lean_dec(v_x_1016_);
v_res_1021_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg(v_x_1014_, v_x_79695__boxed_1019_, v_x_79696__boxed_1020_, v_x_1017_, v_x_1018_);
return v_res_1021_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0___redArg(lean_object* v_x_1022_, lean_object* v_x_1023_, lean_object* v_x_1024_){
_start:
{
uint64_t v___x_1025_; size_t v___x_1026_; size_t v___x_1027_; lean_object* v___x_1028_; 
v___x_1025_ = l_Lean_Expr_hash(v_x_1023_);
v___x_1026_ = lean_uint64_to_usize(v___x_1025_);
v___x_1027_ = ((size_t)1ULL);
v___x_1028_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg(v_x_1022_, v___x_1026_, v___x_1027_, v_x_1023_, v_x_1024_);
return v___x_1028_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___lam__0(lean_object* v_a_1029_, lean_object* v_s_1030_){
_start:
{
lean_object* v_toRingState_1031_; lean_object* v_denoteEntries_1032_; lean_object* v_nextId_1033_; lean_object* v_steps_1034_; lean_object* v_queue_1035_; lean_object* v_basis_1036_; lean_object* v_diseqs_1037_; uint8_t v_recheck_1038_; lean_object* v_invSet_1039_; lean_object* v_powIdentityVarCount_1040_; lean_object* v_numEq0_x3f_1041_; uint8_t v_numEq0Updated_1042_; lean_object* v___x_1044_; uint8_t v_isShared_1045_; uint8_t v_isSharedCheck_1051_; 
v_toRingState_1031_ = lean_ctor_get(v_s_1030_, 0);
v_denoteEntries_1032_ = lean_ctor_get(v_s_1030_, 1);
v_nextId_1033_ = lean_ctor_get(v_s_1030_, 2);
v_steps_1034_ = lean_ctor_get(v_s_1030_, 3);
v_queue_1035_ = lean_ctor_get(v_s_1030_, 4);
v_basis_1036_ = lean_ctor_get(v_s_1030_, 5);
v_diseqs_1037_ = lean_ctor_get(v_s_1030_, 6);
v_recheck_1038_ = lean_ctor_get_uint8(v_s_1030_, sizeof(void*)*10);
v_invSet_1039_ = lean_ctor_get(v_s_1030_, 7);
v_powIdentityVarCount_1040_ = lean_ctor_get(v_s_1030_, 8);
v_numEq0_x3f_1041_ = lean_ctor_get(v_s_1030_, 9);
v_numEq0Updated_1042_ = lean_ctor_get_uint8(v_s_1030_, sizeof(void*)*10 + 1);
v_isSharedCheck_1051_ = !lean_is_exclusive(v_s_1030_);
if (v_isSharedCheck_1051_ == 0)
{
v___x_1044_ = v_s_1030_;
v_isShared_1045_ = v_isSharedCheck_1051_;
goto v_resetjp_1043_;
}
else
{
lean_inc(v_numEq0_x3f_1041_);
lean_inc(v_powIdentityVarCount_1040_);
lean_inc(v_invSet_1039_);
lean_inc(v_diseqs_1037_);
lean_inc(v_basis_1036_);
lean_inc(v_queue_1035_);
lean_inc(v_steps_1034_);
lean_inc(v_nextId_1033_);
lean_inc(v_denoteEntries_1032_);
lean_inc(v_toRingState_1031_);
lean_dec(v_s_1030_);
v___x_1044_ = lean_box(0);
v_isShared_1045_ = v_isSharedCheck_1051_;
goto v_resetjp_1043_;
}
v_resetjp_1043_:
{
lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1049_; 
v___x_1046_ = lean_box(0);
v___x_1047_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0___redArg(v_invSet_1039_, v_a_1029_, v___x_1046_);
if (v_isShared_1045_ == 0)
{
lean_ctor_set(v___x_1044_, 7, v___x_1047_);
v___x_1049_ = v___x_1044_;
goto v_reusejp_1048_;
}
else
{
lean_object* v_reuseFailAlloc_1050_; 
v_reuseFailAlloc_1050_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v_reuseFailAlloc_1050_, 0, v_toRingState_1031_);
lean_ctor_set(v_reuseFailAlloc_1050_, 1, v_denoteEntries_1032_);
lean_ctor_set(v_reuseFailAlloc_1050_, 2, v_nextId_1033_);
lean_ctor_set(v_reuseFailAlloc_1050_, 3, v_steps_1034_);
lean_ctor_set(v_reuseFailAlloc_1050_, 4, v_queue_1035_);
lean_ctor_set(v_reuseFailAlloc_1050_, 5, v_basis_1036_);
lean_ctor_set(v_reuseFailAlloc_1050_, 6, v_diseqs_1037_);
lean_ctor_set(v_reuseFailAlloc_1050_, 7, v___x_1047_);
lean_ctor_set(v_reuseFailAlloc_1050_, 8, v_powIdentityVarCount_1040_);
lean_ctor_set(v_reuseFailAlloc_1050_, 9, v_numEq0_x3f_1041_);
lean_ctor_set_uint8(v_reuseFailAlloc_1050_, sizeof(void*)*10, v_recheck_1038_);
lean_ctor_set_uint8(v_reuseFailAlloc_1050_, sizeof(void*)*10 + 1, v_numEq0Updated_1042_);
v___x_1049_ = v_reuseFailAlloc_1050_;
goto v_reusejp_1048_;
}
v_reusejp_1048_:
{
return v___x_1049_;
}
}
}
}
uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1_spec__2_spec__5___redArg(lean_object* v_keys_1052_, lean_object* v_i_1053_, lean_object* v_k_1054_){
_start:
{
lean_object* v___x_1055_; uint8_t v___x_1056_; 
v___x_1055_ = lean_array_get_size(v_keys_1052_);
v___x_1056_ = lean_nat_dec_lt(v_i_1053_, v___x_1055_);
if (v___x_1056_ == 0)
{
lean_dec(v_i_1053_);
return v___x_1056_;
}
else
{
lean_object* v_k_x27_1057_; uint8_t v___x_1058_; 
v_k_x27_1057_ = lean_array_fget_borrowed(v_keys_1052_, v_i_1053_);
v___x_1058_ = lean_expr_eqv(v_k_1054_, v_k_x27_1057_);
if (v___x_1058_ == 0)
{
lean_object* v___x_1059_; lean_object* v___x_1060_; 
v___x_1059_ = lean_unsigned_to_nat(1u);
v___x_1060_ = lean_nat_add(v_i_1053_, v___x_1059_);
lean_dec(v_i_1053_);
v_i_1053_ = v___x_1060_;
goto _start;
}
else
{
lean_dec(v_i_1053_);
return v___x_1056_;
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1_spec__2_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_keys_1052_ = stack[0].m_obj;
lean_object* v_i_1053_ = stack[1].m_obj;
lean_object* v_k_1054_ = stack[2].m_obj;
uint8_t v_res_1062_;
v_res_1062_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1_spec__2_spec__5___redArg(v_keys_1052_, v_i_1053_, v_k_1054_);
stack->m_num = v_res_1062_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_keys_1063_, lean_object* v_i_1064_, lean_object* v_k_1065_){
_start:
{
uint8_t v_res_1066_; lean_object* v_r_1067_; 
v_res_1066_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1_spec__2_spec__5___redArg(v_keys_1063_, v_i_1064_, v_k_1065_);
lean_dec_ref(v_k_1065_);
lean_dec_ref(v_keys_1063_);
v_r_1067_ = lean_box(v_res_1066_);
return v_r_1067_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1_spec__2___redArg(lean_object* v_x_1068_, size_t v_x_1069_, lean_object* v_x_1070_){
_start:
{
if (lean_obj_tag(v_x_1068_) == 0)
{
lean_object* v_es_1071_; lean_object* v___x_1072_; size_t v___x_1073_; size_t v___x_1074_; lean_object* v_j_1075_; lean_object* v___x_1076_; 
v_es_1071_ = lean_ctor_get(v_x_1068_, 0);
v___x_1072_ = lean_box(2);
v___x_1073_ = ((size_t)31ULL);
v___x_1074_ = lean_usize_land(v_x_1069_, v___x_1073_);
v_j_1075_ = lean_usize_to_nat(v___x_1074_);
v___x_1076_ = lean_array_get_borrowed(v___x_1072_, v_es_1071_, v_j_1075_);
lean_dec(v_j_1075_);
switch(lean_obj_tag(v___x_1076_))
{
case 0:
{
lean_object* v_key_1077_; uint8_t v___x_1078_; 
v_key_1077_ = lean_ctor_get(v___x_1076_, 0);
v___x_1078_ = lean_expr_eqv(v_x_1070_, v_key_1077_);
return v___x_1078_;
}
case 1:
{
lean_object* v_node_1079_; size_t v___x_1080_; size_t v___x_1081_; 
v_node_1079_ = lean_ctor_get(v___x_1076_, 0);
v___x_1080_ = ((size_t)5ULL);
v___x_1081_ = lean_usize_shift_right(v_x_1069_, v___x_1080_);
v_x_1068_ = v_node_1079_;
v_x_1069_ = v___x_1081_;
goto _start;
}
default: 
{
uint8_t v___x_1083_; 
v___x_1083_ = 0;
return v___x_1083_;
}
}
}
else
{
lean_object* v_ks_1084_; lean_object* v___x_1085_; uint8_t v___x_1086_; 
v_ks_1084_ = lean_ctor_get(v_x_1068_, 0);
v___x_1085_ = lean_unsigned_to_nat(0u);
v___x_1086_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1_spec__2_spec__5___redArg(v_ks_1084_, v___x_1085_, v_x_1070_);
return v___x_1086_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1068_ = stack[0].m_obj;
size_t v_x_1069_ = stack[1].m_num;
lean_object* v_x_1070_ = stack[2].m_obj;
uint8_t v_res_1087_;
v_res_1087_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1_spec__2___redArg(v_x_1068_, v_x_1069_, v_x_1070_);
stack->m_num = v_res_1087_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1_spec__2___redArg___boxed(lean_object* v_x_1088_, lean_object* v_x_1089_, lean_object* v_x_1090_){
_start:
{
size_t v_x_79997__boxed_1091_; uint8_t v_res_1092_; lean_object* v_r_1093_; 
v_x_79997__boxed_1091_ = lean_unbox_usize(v_x_1089_);
lean_dec(v_x_1089_);
v_res_1092_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1_spec__2___redArg(v_x_1088_, v_x_79997__boxed_1091_, v_x_1090_);
lean_dec_ref(v_x_1090_);
lean_dec_ref(v_x_1088_);
v_r_1093_ = lean_box(v_res_1092_);
return v_r_1093_;
}
}
uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1___redArg(lean_object* v_x_1094_, lean_object* v_x_1095_){
_start:
{
uint64_t v___x_1096_; size_t v___x_1097_; uint8_t v___x_1098_; 
v___x_1096_ = l_Lean_Expr_hash(v_x_1095_);
v___x_1097_ = lean_uint64_to_usize(v___x_1096_);
v___x_1098_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1_spec__2___redArg(v_x_1094_, v___x_1097_, v_x_1095_);
return v___x_1098_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1094_ = stack[0].m_obj;
lean_object* v_x_1095_ = stack[1].m_obj;
uint8_t v_res_1099_;
v_res_1099_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1___redArg(v_x_1094_, v_x_1095_);
stack->m_num = v_res_1099_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1___redArg___boxed(lean_object* v_x_1100_, lean_object* v_x_1101_){
_start:
{
uint8_t v_res_1102_; lean_object* v_r_1103_; 
v_res_1102_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1___redArg(v_x_1100_, v_x_1101_);
lean_dec_ref(v_x_1101_);
lean_dec_ref(v_x_1100_);
v_r_1103_ = lean_box(v_res_1102_);
return v_r_1103_;
}
}
lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___at___00Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__2_spec__4(lean_object* v_type_1104_, lean_object* v_u_1105_, lean_object* v_instDeclName_1106_, lean_object* v_declName_1107_, lean_object* v_expectedInst_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_){
_start:
{
lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; 
v___x_1121_ = lean_box(0);
lean_inc_n(v_u_1105_, 2);
v___x_1122_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1122_, 0, v_u_1105_);
lean_ctor_set(v___x_1122_, 1, v___x_1121_);
v___x_1123_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1123_, 0, v_u_1105_);
lean_ctor_set(v___x_1123_, 1, v___x_1122_);
v___x_1124_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1124_, 0, v_u_1105_);
lean_ctor_set(v___x_1124_, 1, v___x_1123_);
lean_inc_ref(v___x_1124_);
v___x_1125_ = l_Lean_mkConst(v_instDeclName_1106_, v___x_1124_);
lean_inc_ref_n(v_type_1104_, 3);
v___x_1126_ = l_Lean_mkApp3(v___x_1125_, v_type_1104_, v_type_1104_, v_type_1104_);
v___x_1127_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__2_spec__3(v___x_1126_, v___y_1109_, v___y_1110_, v___y_1111_, v___y_1112_, v___y_1113_, v___y_1114_, v___y_1115_, v___y_1116_, v___y_1117_, v___y_1118_, v___y_1119_);
if (lean_obj_tag(v___x_1127_) == 0)
{
lean_object* v_a_1128_; lean_object* v___x_1129_; 
v_a_1128_ = lean_ctor_get(v___x_1127_, 0);
lean_inc_n(v_a_1128_, 2);
lean_dec_ref_known(v___x_1127_, 1);
lean_inc(v_declName_1107_);
v___x_1129_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst(v_declName_1107_, v_a_1128_, v_expectedInst_1108_, v___y_1116_, v___y_1117_, v___y_1118_, v___y_1119_);
if (lean_obj_tag(v___x_1129_) == 0)
{
lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; 
lean_dec_ref_known(v___x_1129_, 1);
v___x_1130_ = l_Lean_mkConst(v_declName_1107_, v___x_1124_);
lean_inc_ref_n(v_type_1104_, 2);
v___x_1131_ = l_Lean_mkApp4(v___x_1130_, v_type_1104_, v_type_1104_, v_type_1104_, v_a_1128_);
v___x_1132_ = l_Lean_Meta_Sym_canon(v___x_1131_, v___y_1114_, v___y_1115_, v___y_1116_, v___y_1117_, v___y_1118_, v___y_1119_);
if (lean_obj_tag(v___x_1132_) == 0)
{
lean_object* v_a_1133_; lean_object* v___x_1134_; 
v_a_1133_ = lean_ctor_get(v___x_1132_, 0);
lean_inc(v_a_1133_);
lean_dec_ref_known(v___x_1132_, 1);
v___x_1134_ = l_Lean_Meta_Sym_shareCommon(v_a_1133_, v___y_1114_, v___y_1115_, v___y_1116_, v___y_1117_, v___y_1118_, v___y_1119_);
return v___x_1134_;
}
else
{
return v___x_1132_;
}
}
else
{
lean_object* v_a_1135_; lean_object* v___x_1137_; uint8_t v_isShared_1138_; uint8_t v_isSharedCheck_1142_; 
lean_dec(v_a_1128_);
lean_dec_ref_known(v___x_1124_, 2);
lean_dec(v_declName_1107_);
lean_dec_ref(v_type_1104_);
v_a_1135_ = lean_ctor_get(v___x_1129_, 0);
v_isSharedCheck_1142_ = !lean_is_exclusive(v___x_1129_);
if (v_isSharedCheck_1142_ == 0)
{
v___x_1137_ = v___x_1129_;
v_isShared_1138_ = v_isSharedCheck_1142_;
goto v_resetjp_1136_;
}
else
{
lean_inc(v_a_1135_);
lean_dec(v___x_1129_);
v___x_1137_ = lean_box(0);
v_isShared_1138_ = v_isSharedCheck_1142_;
goto v_resetjp_1136_;
}
v_resetjp_1136_:
{
lean_object* v___x_1140_; 
if (v_isShared_1138_ == 0)
{
v___x_1140_ = v___x_1137_;
goto v_reusejp_1139_;
}
else
{
lean_object* v_reuseFailAlloc_1141_; 
v_reuseFailAlloc_1141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1141_, 0, v_a_1135_);
v___x_1140_ = v_reuseFailAlloc_1141_;
goto v_reusejp_1139_;
}
v_reusejp_1139_:
{
return v___x_1140_;
}
}
}
}
else
{
lean_dec_ref_known(v___x_1124_, 2);
lean_dec_ref(v_expectedInst_1108_);
lean_dec(v_declName_1107_);
lean_dec_ref(v_type_1104_);
return v___x_1127_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___at___00Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__2_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_1104_ = stack[0].m_obj;
lean_object* v_u_1105_ = stack[1].m_obj;
lean_object* v_instDeclName_1106_ = stack[2].m_obj;
lean_object* v_declName_1107_ = stack[3].m_obj;
lean_object* v_expectedInst_1108_ = stack[4].m_obj;
lean_object* v___y_1109_ = stack[5].m_obj;
lean_object* v___y_1110_ = stack[6].m_obj;
lean_object* v___y_1111_ = stack[7].m_obj;
lean_object* v___y_1112_ = stack[8].m_obj;
lean_object* v___y_1113_ = stack[9].m_obj;
lean_object* v___y_1114_ = stack[10].m_obj;
lean_object* v___y_1115_ = stack[11].m_obj;
lean_object* v___y_1116_ = stack[12].m_obj;
lean_object* v___y_1117_ = stack[13].m_obj;
lean_object* v___y_1118_ = stack[14].m_obj;
lean_object* v___y_1119_ = stack[15].m_obj;
lean_object* v_res_1143_;
v_res_1143_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___at___00Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__2_spec__4(v_type_1104_, v_u_1105_, v_instDeclName_1106_, v_declName_1107_, v_expectedInst_1108_, v___y_1109_, v___y_1110_, v___y_1111_, v___y_1112_, v___y_1113_, v___y_1114_, v___y_1115_, v___y_1116_, v___y_1117_, v___y_1118_, v___y_1119_);
stack->m_obj
 = v_res_1143_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___at___00Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__2_spec__4___boxed(lean_object** _args){
lean_object* v_type_1144_ = _args[0];
lean_object* v_u_1145_ = _args[1];
lean_object* v_instDeclName_1146_ = _args[2];
lean_object* v_declName_1147_ = _args[3];
lean_object* v_expectedInst_1148_ = _args[4];
lean_object* v___y_1149_ = _args[5];
lean_object* v___y_1150_ = _args[6];
lean_object* v___y_1151_ = _args[7];
lean_object* v___y_1152_ = _args[8];
lean_object* v___y_1153_ = _args[9];
lean_object* v___y_1154_ = _args[10];
lean_object* v___y_1155_ = _args[11];
lean_object* v___y_1156_ = _args[12];
lean_object* v___y_1157_ = _args[13];
lean_object* v___y_1158_ = _args[14];
lean_object* v___y_1159_ = _args[15];
lean_object* v___y_1160_ = _args[16];
_start:
{
lean_object* v_res_1161_; 
v_res_1161_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___at___00Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__2_spec__4(v_type_1144_, v_u_1145_, v_instDeclName_1146_, v_declName_1147_, v_expectedInst_1148_, v___y_1149_, v___y_1150_, v___y_1151_, v___y_1152_, v___y_1153_, v___y_1154_, v___y_1155_, v___y_1156_, v___y_1157_, v___y_1158_, v___y_1159_);
lean_dec(v___y_1159_);
lean_dec_ref(v___y_1158_);
lean_dec(v___y_1157_);
lean_dec_ref(v___y_1156_);
lean_dec(v___y_1155_);
lean_dec_ref(v___y_1154_);
lean_dec(v___y_1153_);
lean_dec_ref(v___y_1152_);
lean_dec(v___y_1151_);
lean_dec(v___y_1150_);
lean_dec_ref(v___y_1149_);
return v_res_1161_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__2___lam__0(lean_object* v_a_1162_, lean_object* v_s_1163_){
_start:
{
lean_object* v_toRing_1164_; lean_object* v_invFn_x3f_1165_; lean_object* v_divFn_x3f_1166_; lean_object* v_semiringId_x3f_1167_; lean_object* v_commSemiringInst_1168_; lean_object* v_commRingInst_1169_; lean_object* v_noZeroDivInst_x3f_1170_; lean_object* v_fieldInst_x3f_1171_; lean_object* v_powIdentityInst_x3f_1172_; lean_object* v___x_1174_; uint8_t v_isShared_1175_; uint8_t v_isSharedCheck_1203_; 
v_toRing_1164_ = lean_ctor_get(v_s_1163_, 0);
v_invFn_x3f_1165_ = lean_ctor_get(v_s_1163_, 1);
v_divFn_x3f_1166_ = lean_ctor_get(v_s_1163_, 2);
v_semiringId_x3f_1167_ = lean_ctor_get(v_s_1163_, 3);
v_commSemiringInst_1168_ = lean_ctor_get(v_s_1163_, 4);
v_commRingInst_1169_ = lean_ctor_get(v_s_1163_, 5);
v_noZeroDivInst_x3f_1170_ = lean_ctor_get(v_s_1163_, 6);
v_fieldInst_x3f_1171_ = lean_ctor_get(v_s_1163_, 7);
v_powIdentityInst_x3f_1172_ = lean_ctor_get(v_s_1163_, 8);
v_isSharedCheck_1203_ = !lean_is_exclusive(v_s_1163_);
if (v_isSharedCheck_1203_ == 0)
{
v___x_1174_ = v_s_1163_;
v_isShared_1175_ = v_isSharedCheck_1203_;
goto v_resetjp_1173_;
}
else
{
lean_inc(v_powIdentityInst_x3f_1172_);
lean_inc(v_fieldInst_x3f_1171_);
lean_inc(v_noZeroDivInst_x3f_1170_);
lean_inc(v_commRingInst_1169_);
lean_inc(v_commSemiringInst_1168_);
lean_inc(v_semiringId_x3f_1167_);
lean_inc(v_divFn_x3f_1166_);
lean_inc(v_invFn_x3f_1165_);
lean_inc(v_toRing_1164_);
lean_dec(v_s_1163_);
v___x_1174_ = lean_box(0);
v_isShared_1175_ = v_isSharedCheck_1203_;
goto v_resetjp_1173_;
}
v_resetjp_1173_:
{
lean_object* v_id_1176_; lean_object* v_type_1177_; lean_object* v_u_1178_; lean_object* v_ringInst_1179_; lean_object* v_semiringInst_1180_; lean_object* v_charInst_x3f_1181_; lean_object* v_addFn_x3f_1182_; lean_object* v_subFn_x3f_1183_; lean_object* v_negFn_x3f_1184_; lean_object* v_powFn_x3f_1185_; lean_object* v_intCastFn_x3f_1186_; lean_object* v_natCastFn_x3f_1187_; lean_object* v_natSMulFn_x3f_1188_; lean_object* v_intSMulFn_x3f_1189_; lean_object* v_one_x3f_1190_; lean_object* v___x_1192_; uint8_t v_isShared_1193_; uint8_t v_isSharedCheck_1201_; 
v_id_1176_ = lean_ctor_get(v_toRing_1164_, 0);
v_type_1177_ = lean_ctor_get(v_toRing_1164_, 1);
v_u_1178_ = lean_ctor_get(v_toRing_1164_, 2);
v_ringInst_1179_ = lean_ctor_get(v_toRing_1164_, 3);
v_semiringInst_1180_ = lean_ctor_get(v_toRing_1164_, 4);
v_charInst_x3f_1181_ = lean_ctor_get(v_toRing_1164_, 5);
v_addFn_x3f_1182_ = lean_ctor_get(v_toRing_1164_, 6);
v_subFn_x3f_1183_ = lean_ctor_get(v_toRing_1164_, 8);
v_negFn_x3f_1184_ = lean_ctor_get(v_toRing_1164_, 9);
v_powFn_x3f_1185_ = lean_ctor_get(v_toRing_1164_, 10);
v_intCastFn_x3f_1186_ = lean_ctor_get(v_toRing_1164_, 11);
v_natCastFn_x3f_1187_ = lean_ctor_get(v_toRing_1164_, 12);
v_natSMulFn_x3f_1188_ = lean_ctor_get(v_toRing_1164_, 13);
v_intSMulFn_x3f_1189_ = lean_ctor_get(v_toRing_1164_, 14);
v_one_x3f_1190_ = lean_ctor_get(v_toRing_1164_, 15);
v_isSharedCheck_1201_ = !lean_is_exclusive(v_toRing_1164_);
if (v_isSharedCheck_1201_ == 0)
{
lean_object* v_unused_1202_; 
v_unused_1202_ = lean_ctor_get(v_toRing_1164_, 7);
lean_dec(v_unused_1202_);
v___x_1192_ = v_toRing_1164_;
v_isShared_1193_ = v_isSharedCheck_1201_;
goto v_resetjp_1191_;
}
else
{
lean_inc(v_one_x3f_1190_);
lean_inc(v_intSMulFn_x3f_1189_);
lean_inc(v_natSMulFn_x3f_1188_);
lean_inc(v_natCastFn_x3f_1187_);
lean_inc(v_intCastFn_x3f_1186_);
lean_inc(v_powFn_x3f_1185_);
lean_inc(v_negFn_x3f_1184_);
lean_inc(v_subFn_x3f_1183_);
lean_inc(v_addFn_x3f_1182_);
lean_inc(v_charInst_x3f_1181_);
lean_inc(v_semiringInst_1180_);
lean_inc(v_ringInst_1179_);
lean_inc(v_u_1178_);
lean_inc(v_type_1177_);
lean_inc(v_id_1176_);
lean_dec(v_toRing_1164_);
v___x_1192_ = lean_box(0);
v_isShared_1193_ = v_isSharedCheck_1201_;
goto v_resetjp_1191_;
}
v_resetjp_1191_:
{
lean_object* v___x_1194_; lean_object* v___x_1196_; 
v___x_1194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1194_, 0, v_a_1162_);
if (v_isShared_1193_ == 0)
{
lean_ctor_set(v___x_1192_, 7, v___x_1194_);
v___x_1196_ = v___x_1192_;
goto v_reusejp_1195_;
}
else
{
lean_object* v_reuseFailAlloc_1200_; 
v_reuseFailAlloc_1200_ = lean_alloc_ctor(0, 16, 0);
lean_ctor_set(v_reuseFailAlloc_1200_, 0, v_id_1176_);
lean_ctor_set(v_reuseFailAlloc_1200_, 1, v_type_1177_);
lean_ctor_set(v_reuseFailAlloc_1200_, 2, v_u_1178_);
lean_ctor_set(v_reuseFailAlloc_1200_, 3, v_ringInst_1179_);
lean_ctor_set(v_reuseFailAlloc_1200_, 4, v_semiringInst_1180_);
lean_ctor_set(v_reuseFailAlloc_1200_, 5, v_charInst_x3f_1181_);
lean_ctor_set(v_reuseFailAlloc_1200_, 6, v_addFn_x3f_1182_);
lean_ctor_set(v_reuseFailAlloc_1200_, 7, v___x_1194_);
lean_ctor_set(v_reuseFailAlloc_1200_, 8, v_subFn_x3f_1183_);
lean_ctor_set(v_reuseFailAlloc_1200_, 9, v_negFn_x3f_1184_);
lean_ctor_set(v_reuseFailAlloc_1200_, 10, v_powFn_x3f_1185_);
lean_ctor_set(v_reuseFailAlloc_1200_, 11, v_intCastFn_x3f_1186_);
lean_ctor_set(v_reuseFailAlloc_1200_, 12, v_natCastFn_x3f_1187_);
lean_ctor_set(v_reuseFailAlloc_1200_, 13, v_natSMulFn_x3f_1188_);
lean_ctor_set(v_reuseFailAlloc_1200_, 14, v_intSMulFn_x3f_1189_);
lean_ctor_set(v_reuseFailAlloc_1200_, 15, v_one_x3f_1190_);
v___x_1196_ = v_reuseFailAlloc_1200_;
goto v_reusejp_1195_;
}
v_reusejp_1195_:
{
lean_object* v___x_1198_; 
if (v_isShared_1175_ == 0)
{
lean_ctor_set(v___x_1174_, 0, v___x_1196_);
v___x_1198_ = v___x_1174_;
goto v_reusejp_1197_;
}
else
{
lean_object* v_reuseFailAlloc_1199_; 
v_reuseFailAlloc_1199_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1199_, 0, v___x_1196_);
lean_ctor_set(v_reuseFailAlloc_1199_, 1, v_invFn_x3f_1165_);
lean_ctor_set(v_reuseFailAlloc_1199_, 2, v_divFn_x3f_1166_);
lean_ctor_set(v_reuseFailAlloc_1199_, 3, v_semiringId_x3f_1167_);
lean_ctor_set(v_reuseFailAlloc_1199_, 4, v_commSemiringInst_1168_);
lean_ctor_set(v_reuseFailAlloc_1199_, 5, v_commRingInst_1169_);
lean_ctor_set(v_reuseFailAlloc_1199_, 6, v_noZeroDivInst_x3f_1170_);
lean_ctor_set(v_reuseFailAlloc_1199_, 7, v_fieldInst_x3f_1171_);
lean_ctor_set(v_reuseFailAlloc_1199_, 8, v_powIdentityInst_x3f_1172_);
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
}
}
lean_object* l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__2(lean_object* v___y_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_){
_start:
{
lean_object* v___x_1228_; 
v___x_1228_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v___y_1216_, v___y_1217_, v___y_1218_, v___y_1219_, v___y_1220_, v___y_1221_, v___y_1222_, v___y_1223_, v___y_1224_, v___y_1225_, v___y_1226_);
if (lean_obj_tag(v___x_1228_) == 0)
{
lean_object* v_a_1229_; lean_object* v___x_1231_; uint8_t v_isShared_1232_; uint8_t v_isSharedCheck_1272_; 
v_a_1229_ = lean_ctor_get(v___x_1228_, 0);
v_isSharedCheck_1272_ = !lean_is_exclusive(v___x_1228_);
if (v_isSharedCheck_1272_ == 0)
{
v___x_1231_ = v___x_1228_;
v_isShared_1232_ = v_isSharedCheck_1272_;
goto v_resetjp_1230_;
}
else
{
lean_inc(v_a_1229_);
lean_dec(v___x_1228_);
v___x_1231_ = lean_box(0);
v_isShared_1232_ = v_isSharedCheck_1272_;
goto v_resetjp_1230_;
}
v_resetjp_1230_:
{
lean_object* v_toRing_1233_; lean_object* v_mulFn_x3f_1234_; 
v_toRing_1233_ = lean_ctor_get(v_a_1229_, 0);
lean_inc_ref(v_toRing_1233_);
lean_dec(v_a_1229_);
v_mulFn_x3f_1234_ = lean_ctor_get(v_toRing_1233_, 7);
if (lean_obj_tag(v_mulFn_x3f_1234_) == 1)
{
lean_object* v_val_1235_; lean_object* v___x_1237_; 
lean_inc_ref(v_mulFn_x3f_1234_);
lean_dec_ref(v_toRing_1233_);
v_val_1235_ = lean_ctor_get(v_mulFn_x3f_1234_, 0);
lean_inc(v_val_1235_);
lean_dec_ref_known(v_mulFn_x3f_1234_, 1);
if (v_isShared_1232_ == 0)
{
lean_ctor_set(v___x_1231_, 0, v_val_1235_);
v___x_1237_ = v___x_1231_;
goto v_reusejp_1236_;
}
else
{
lean_object* v_reuseFailAlloc_1238_; 
v_reuseFailAlloc_1238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1238_, 0, v_val_1235_);
v___x_1237_ = v_reuseFailAlloc_1238_;
goto v_reusejp_1236_;
}
v_reusejp_1236_:
{
return v___x_1237_;
}
}
else
{
lean_object* v_type_1239_; lean_object* v_u_1240_; lean_object* v_semiringInst_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v_expectedInst_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; 
lean_del_object(v___x_1231_);
v_type_1239_ = lean_ctor_get(v_toRing_1233_, 1);
lean_inc_ref_n(v_type_1239_, 3);
v_u_1240_ = lean_ctor_get(v_toRing_1233_, 2);
lean_inc_n(v_u_1240_, 2);
v_semiringInst_1241_ = lean_ctor_get(v_toRing_1233_, 4);
lean_inc_ref(v_semiringInst_1241_);
lean_dec_ref(v_toRing_1233_);
v___x_1242_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__2___closed__1));
v___x_1243_ = lean_box(0);
v___x_1244_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1244_, 0, v_u_1240_);
lean_ctor_set(v___x_1244_, 1, v___x_1243_);
lean_inc_ref(v___x_1244_);
v___x_1245_ = l_Lean_mkConst(v___x_1242_, v___x_1244_);
v___x_1246_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__2___closed__4));
v___x_1247_ = l_Lean_mkConst(v___x_1246_, v___x_1244_);
v___x_1248_ = l_Lean_mkAppB(v___x_1247_, v_type_1239_, v_semiringInst_1241_);
v_expectedInst_1249_ = l_Lean_mkAppB(v___x_1245_, v_type_1239_, v___x_1248_);
v___x_1250_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__2___closed__5));
v___x_1251_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__20));
v___x_1252_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___at___00Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__2_spec__4(v_type_1239_, v_u_1240_, v___x_1250_, v___x_1251_, v_expectedInst_1249_, v___y_1216_, v___y_1217_, v___y_1218_, v___y_1219_, v___y_1220_, v___y_1221_, v___y_1222_, v___y_1223_, v___y_1224_, v___y_1225_, v___y_1226_);
if (lean_obj_tag(v___x_1252_) == 0)
{
lean_object* v_a_1253_; lean_object* v___f_1254_; lean_object* v___x_1255_; 
v_a_1253_ = lean_ctor_get(v___x_1252_, 0);
lean_inc_n(v_a_1253_, 2);
lean_dec_ref_known(v___x_1252_, 1);
v___f_1254_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__2___lam__0), 2, 1);
lean_closure_set(v___f_1254_, 0, v_a_1253_);
v___x_1255_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(v___f_1254_, v___y_1216_, v___y_1222_);
if (lean_obj_tag(v___x_1255_) == 0)
{
lean_object* v___x_1257_; uint8_t v_isShared_1258_; uint8_t v_isSharedCheck_1262_; 
v_isSharedCheck_1262_ = !lean_is_exclusive(v___x_1255_);
if (v_isSharedCheck_1262_ == 0)
{
lean_object* v_unused_1263_; 
v_unused_1263_ = lean_ctor_get(v___x_1255_, 0);
lean_dec(v_unused_1263_);
v___x_1257_ = v___x_1255_;
v_isShared_1258_ = v_isSharedCheck_1262_;
goto v_resetjp_1256_;
}
else
{
lean_dec(v___x_1255_);
v___x_1257_ = lean_box(0);
v_isShared_1258_ = v_isSharedCheck_1262_;
goto v_resetjp_1256_;
}
v_resetjp_1256_:
{
lean_object* v___x_1260_; 
if (v_isShared_1258_ == 0)
{
lean_ctor_set(v___x_1257_, 0, v_a_1253_);
v___x_1260_ = v___x_1257_;
goto v_reusejp_1259_;
}
else
{
lean_object* v_reuseFailAlloc_1261_; 
v_reuseFailAlloc_1261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1261_, 0, v_a_1253_);
v___x_1260_ = v_reuseFailAlloc_1261_;
goto v_reusejp_1259_;
}
v_reusejp_1259_:
{
return v___x_1260_;
}
}
}
else
{
lean_object* v_a_1264_; lean_object* v___x_1266_; uint8_t v_isShared_1267_; uint8_t v_isSharedCheck_1271_; 
lean_dec(v_a_1253_);
v_a_1264_ = lean_ctor_get(v___x_1255_, 0);
v_isSharedCheck_1271_ = !lean_is_exclusive(v___x_1255_);
if (v_isSharedCheck_1271_ == 0)
{
v___x_1266_ = v___x_1255_;
v_isShared_1267_ = v_isSharedCheck_1271_;
goto v_resetjp_1265_;
}
else
{
lean_inc(v_a_1264_);
lean_dec(v___x_1255_);
v___x_1266_ = lean_box(0);
v_isShared_1267_ = v_isSharedCheck_1271_;
goto v_resetjp_1265_;
}
v_resetjp_1265_:
{
lean_object* v___x_1269_; 
if (v_isShared_1267_ == 0)
{
v___x_1269_ = v___x_1266_;
goto v_reusejp_1268_;
}
else
{
lean_object* v_reuseFailAlloc_1270_; 
v_reuseFailAlloc_1270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1270_, 0, v_a_1264_);
v___x_1269_ = v_reuseFailAlloc_1270_;
goto v_reusejp_1268_;
}
v_reusejp_1268_:
{
return v___x_1269_;
}
}
}
}
else
{
return v___x_1252_;
}
}
}
}
else
{
lean_object* v_a_1273_; lean_object* v___x_1275_; uint8_t v_isShared_1276_; uint8_t v_isSharedCheck_1280_; 
v_a_1273_ = lean_ctor_get(v___x_1228_, 0);
v_isSharedCheck_1280_ = !lean_is_exclusive(v___x_1228_);
if (v_isSharedCheck_1280_ == 0)
{
v___x_1275_ = v___x_1228_;
v_isShared_1276_ = v_isSharedCheck_1280_;
goto v_resetjp_1274_;
}
else
{
lean_inc(v_a_1273_);
lean_dec(v___x_1228_);
v___x_1275_ = lean_box(0);
v_isShared_1276_ = v_isSharedCheck_1280_;
goto v_resetjp_1274_;
}
v_resetjp_1274_:
{
lean_object* v___x_1278_; 
if (v_isShared_1276_ == 0)
{
v___x_1278_ = v___x_1275_;
goto v_reusejp_1277_;
}
else
{
lean_object* v_reuseFailAlloc_1279_; 
v_reuseFailAlloc_1279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1279_, 0, v_a_1273_);
v___x_1278_ = v_reuseFailAlloc_1279_;
goto v_reusejp_1277_;
}
v_reusejp_1277_:
{
return v___x_1278_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_1216_ = stack[0].m_obj;
lean_object* v___y_1217_ = stack[1].m_obj;
lean_object* v___y_1218_ = stack[2].m_obj;
lean_object* v___y_1219_ = stack[3].m_obj;
lean_object* v___y_1220_ = stack[4].m_obj;
lean_object* v___y_1221_ = stack[5].m_obj;
lean_object* v___y_1222_ = stack[6].m_obj;
lean_object* v___y_1223_ = stack[7].m_obj;
lean_object* v___y_1224_ = stack[8].m_obj;
lean_object* v___y_1225_ = stack[9].m_obj;
lean_object* v___y_1226_ = stack[10].m_obj;
lean_object* v_res_1281_;
v_res_1281_ = l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__2(v___y_1216_, v___y_1217_, v___y_1218_, v___y_1219_, v___y_1220_, v___y_1221_, v___y_1222_, v___y_1223_, v___y_1224_, v___y_1225_, v___y_1226_);
stack->m_obj
 = v_res_1281_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__2___boxed(lean_object* v___y_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_){
_start:
{
lean_object* v_res_1294_; 
v_res_1294_ = l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__2(v___y_1282_, v___y_1283_, v___y_1284_, v___y_1285_, v___y_1286_, v___y_1287_, v___y_1288_, v___y_1289_, v___y_1290_, v___y_1291_, v___y_1292_);
lean_dec(v___y_1292_);
lean_dec_ref(v___y_1291_);
lean_dec(v___y_1290_);
lean_dec_ref(v___y_1289_);
lean_dec(v___y_1288_);
lean_dec_ref(v___y_1287_);
lean_dec(v___y_1286_);
lean_dec_ref(v___y_1285_);
lean_dec(v___y_1284_);
lean_dec(v___y_1283_);
lean_dec_ref(v___y_1282_);
return v_res_1294_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__3___closed__1(void){
_start:
{
lean_object* v___x_1297_; lean_object* v___x_1298_; 
v___x_1297_ = lean_unsigned_to_nat(0u);
v___x_1298_ = lean_nat_to_int(v___x_1297_);
return v___x_1298_;
}
}
lean_object* l_Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__3(lean_object* v_k_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_){
_start:
{
lean_object* v___x_1317_; 
v___x_1317_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v___y_1305_, v___y_1306_, v___y_1307_, v___y_1308_, v___y_1309_, v___y_1310_, v___y_1311_, v___y_1312_, v___y_1313_, v___y_1314_, v___y_1315_);
if (lean_obj_tag(v___x_1317_) == 0)
{
lean_object* v_a_1318_; lean_object* v___x_1320_; uint8_t v_isShared_1321_; uint8_t v_isSharedCheck_1378_; 
v_a_1318_ = lean_ctor_get(v___x_1317_, 0);
v_isSharedCheck_1378_ = !lean_is_exclusive(v___x_1317_);
if (v_isSharedCheck_1378_ == 0)
{
v___x_1320_ = v___x_1317_;
v_isShared_1321_ = v_isSharedCheck_1378_;
goto v_resetjp_1319_;
}
else
{
lean_inc(v_a_1318_);
lean_dec(v___x_1317_);
v___x_1320_ = lean_box(0);
v_isShared_1321_ = v_isSharedCheck_1378_;
goto v_resetjp_1319_;
}
v_resetjp_1319_:
{
lean_object* v_toRing_1322_; lean_object* v_type_1323_; lean_object* v_u_1324_; lean_object* v_semiringInst_1325_; lean_object* v___x_1326_; lean_object* v_n_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v_ofNatInst_1332_; lean_object* v___y_1333_; lean_object* v___y_1334_; lean_object* v___y_1335_; lean_object* v___y_1336_; lean_object* v___y_1337_; lean_object* v___y_1338_; lean_object* v___y_1339_; lean_object* v___y_1340_; lean_object* v___y_1341_; lean_object* v___y_1342_; lean_object* v___y_1343_; lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; 
v_toRing_1322_ = lean_ctor_get(v_a_1318_, 0);
lean_inc_ref(v_toRing_1322_);
lean_dec(v_a_1318_);
v_type_1323_ = lean_ctor_get(v_toRing_1322_, 1);
lean_inc_ref_n(v_type_1323_, 2);
v_u_1324_ = lean_ctor_get(v_toRing_1322_, 2);
lean_inc(v_u_1324_);
v_semiringInst_1325_ = lean_ctor_get(v_toRing_1322_, 4);
lean_inc_ref(v_semiringInst_1325_);
lean_dec_ref(v_toRing_1322_);
v___x_1326_ = lean_nat_abs(v_k_1304_);
v_n_1327_ = l_Lean_mkRawNatLit(v___x_1326_);
v___x_1328_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__3___closed__0));
v___x_1329_ = lean_box(0);
v___x_1330_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1330_, 0, v_u_1324_);
lean_ctor_set(v___x_1330_, 1, v___x_1329_);
lean_inc_ref(v___x_1330_);
v___x_1362_ = l_Lean_mkConst(v___x_1328_, v___x_1330_);
lean_inc_ref(v_n_1327_);
v___x_1363_ = l_Lean_mkAppB(v___x_1362_, v_type_1323_, v_n_1327_);
v___x_1364_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_1363_, v___y_1311_, v___y_1312_, v___y_1313_, v___y_1314_, v___y_1315_);
if (lean_obj_tag(v___x_1364_) == 0)
{
lean_object* v_a_1365_; 
v_a_1365_ = lean_ctor_get(v___x_1364_, 0);
lean_inc(v_a_1365_);
lean_dec_ref_known(v___x_1364_, 1);
if (lean_obj_tag(v_a_1365_) == 1)
{
lean_object* v_val_1366_; 
lean_dec_ref(v_semiringInst_1325_);
v_val_1366_ = lean_ctor_get(v_a_1365_, 0);
lean_inc(v_val_1366_);
lean_dec_ref_known(v_a_1365_, 1);
v_ofNatInst_1332_ = v_val_1366_;
v___y_1333_ = v___y_1305_;
v___y_1334_ = v___y_1306_;
v___y_1335_ = v___y_1307_;
v___y_1336_ = v___y_1308_;
v___y_1337_ = v___y_1309_;
v___y_1338_ = v___y_1310_;
v___y_1339_ = v___y_1311_;
v___y_1340_ = v___y_1312_;
v___y_1341_ = v___y_1313_;
v___y_1342_ = v___y_1314_;
v___y_1343_ = v___y_1315_;
goto v___jp_1331_;
}
else
{
lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; 
lean_dec(v_a_1365_);
v___x_1367_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__3___closed__2));
lean_inc_ref(v___x_1330_);
v___x_1368_ = l_Lean_mkConst(v___x_1367_, v___x_1330_);
lean_inc_ref(v_n_1327_);
lean_inc_ref(v_type_1323_);
v___x_1369_ = l_Lean_mkApp3(v___x_1368_, v_type_1323_, v_semiringInst_1325_, v_n_1327_);
v_ofNatInst_1332_ = v___x_1369_;
v___y_1333_ = v___y_1305_;
v___y_1334_ = v___y_1306_;
v___y_1335_ = v___y_1307_;
v___y_1336_ = v___y_1308_;
v___y_1337_ = v___y_1309_;
v___y_1338_ = v___y_1310_;
v___y_1339_ = v___y_1311_;
v___y_1340_ = v___y_1312_;
v___y_1341_ = v___y_1313_;
v___y_1342_ = v___y_1314_;
v___y_1343_ = v___y_1315_;
goto v___jp_1331_;
}
}
else
{
lean_object* v_a_1370_; lean_object* v___x_1372_; uint8_t v_isShared_1373_; uint8_t v_isSharedCheck_1377_; 
lean_dec_ref_known(v___x_1330_, 2);
lean_dec_ref(v_n_1327_);
lean_dec_ref(v_semiringInst_1325_);
lean_dec_ref(v_type_1323_);
lean_del_object(v___x_1320_);
v_a_1370_ = lean_ctor_get(v___x_1364_, 0);
v_isSharedCheck_1377_ = !lean_is_exclusive(v___x_1364_);
if (v_isSharedCheck_1377_ == 0)
{
v___x_1372_ = v___x_1364_;
v_isShared_1373_ = v_isSharedCheck_1377_;
goto v_resetjp_1371_;
}
else
{
lean_inc(v_a_1370_);
lean_dec(v___x_1364_);
v___x_1372_ = lean_box(0);
v_isShared_1373_ = v_isSharedCheck_1377_;
goto v_resetjp_1371_;
}
v_resetjp_1371_:
{
lean_object* v___x_1375_; 
if (v_isShared_1373_ == 0)
{
v___x_1375_ = v___x_1372_;
goto v_reusejp_1374_;
}
else
{
lean_object* v_reuseFailAlloc_1376_; 
v_reuseFailAlloc_1376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1376_, 0, v_a_1370_);
v___x_1375_ = v_reuseFailAlloc_1376_;
goto v_reusejp_1374_;
}
v_reusejp_1374_:
{
return v___x_1375_;
}
}
}
v___jp_1331_:
{
lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v_e_1346_; lean_object* v___x_1347_; uint8_t v___x_1348_; 
v___x_1344_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__8));
v___x_1345_ = l_Lean_mkConst(v___x_1344_, v___x_1330_);
v_e_1346_ = l_Lean_mkApp3(v___x_1345_, v_type_1323_, v_n_1327_, v_ofNatInst_1332_);
v___x_1347_ = lean_obj_once(&l_Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__3___closed__1, &l_Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__3___closed__1_once, _init_l_Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__3___closed__1);
v___x_1348_ = lean_int_dec_lt(v_k_1304_, v___x_1347_);
if (v___x_1348_ == 0)
{
lean_object* v___x_1350_; 
if (v_isShared_1321_ == 0)
{
lean_ctor_set(v___x_1320_, 0, v_e_1346_);
v___x_1350_ = v___x_1320_;
goto v_reusejp_1349_;
}
else
{
lean_object* v_reuseFailAlloc_1351_; 
v_reuseFailAlloc_1351_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1351_, 0, v_e_1346_);
v___x_1350_ = v_reuseFailAlloc_1351_;
goto v_reusejp_1349_;
}
v_reusejp_1349_:
{
return v___x_1350_;
}
}
else
{
lean_object* v___x_1352_; 
lean_del_object(v___x_1320_);
v___x_1352_ = l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0(v___y_1333_, v___y_1334_, v___y_1335_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_, v___y_1342_, v___y_1343_);
if (lean_obj_tag(v___x_1352_) == 0)
{
lean_object* v_a_1353_; lean_object* v___x_1355_; uint8_t v_isShared_1356_; uint8_t v_isSharedCheck_1361_; 
v_a_1353_ = lean_ctor_get(v___x_1352_, 0);
v_isSharedCheck_1361_ = !lean_is_exclusive(v___x_1352_);
if (v_isSharedCheck_1361_ == 0)
{
v___x_1355_ = v___x_1352_;
v_isShared_1356_ = v_isSharedCheck_1361_;
goto v_resetjp_1354_;
}
else
{
lean_inc(v_a_1353_);
lean_dec(v___x_1352_);
v___x_1355_ = lean_box(0);
v_isShared_1356_ = v_isSharedCheck_1361_;
goto v_resetjp_1354_;
}
v_resetjp_1354_:
{
lean_object* v___x_1357_; lean_object* v___x_1359_; 
v___x_1357_ = l_Lean_Expr_app___override(v_a_1353_, v_e_1346_);
if (v_isShared_1356_ == 0)
{
lean_ctor_set(v___x_1355_, 0, v___x_1357_);
v___x_1359_ = v___x_1355_;
goto v_reusejp_1358_;
}
else
{
lean_object* v_reuseFailAlloc_1360_; 
v_reuseFailAlloc_1360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1360_, 0, v___x_1357_);
v___x_1359_ = v_reuseFailAlloc_1360_;
goto v_reusejp_1358_;
}
v_reusejp_1358_:
{
return v___x_1359_;
}
}
}
else
{
lean_dec_ref(v_e_1346_);
return v___x_1352_;
}
}
}
}
}
else
{
lean_object* v_a_1379_; lean_object* v___x_1381_; uint8_t v_isShared_1382_; uint8_t v_isSharedCheck_1386_; 
v_a_1379_ = lean_ctor_get(v___x_1317_, 0);
v_isSharedCheck_1386_ = !lean_is_exclusive(v___x_1317_);
if (v_isSharedCheck_1386_ == 0)
{
v___x_1381_ = v___x_1317_;
v_isShared_1382_ = v_isSharedCheck_1386_;
goto v_resetjp_1380_;
}
else
{
lean_inc(v_a_1379_);
lean_dec(v___x_1317_);
v___x_1381_ = lean_box(0);
v_isShared_1382_ = v_isSharedCheck_1386_;
goto v_resetjp_1380_;
}
v_resetjp_1380_:
{
lean_object* v___x_1384_; 
if (v_isShared_1382_ == 0)
{
v___x_1384_ = v___x_1381_;
goto v_reusejp_1383_;
}
else
{
lean_object* v_reuseFailAlloc_1385_; 
v_reuseFailAlloc_1385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1385_, 0, v_a_1379_);
v___x_1384_ = v_reuseFailAlloc_1385_;
goto v_reusejp_1383_;
}
v_reusejp_1383_:
{
return v___x_1384_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_1304_ = stack[0].m_obj;
lean_object* v___y_1305_ = stack[1].m_obj;
lean_object* v___y_1306_ = stack[2].m_obj;
lean_object* v___y_1307_ = stack[3].m_obj;
lean_object* v___y_1308_ = stack[4].m_obj;
lean_object* v___y_1309_ = stack[5].m_obj;
lean_object* v___y_1310_ = stack[6].m_obj;
lean_object* v___y_1311_ = stack[7].m_obj;
lean_object* v___y_1312_ = stack[8].m_obj;
lean_object* v___y_1313_ = stack[9].m_obj;
lean_object* v___y_1314_ = stack[10].m_obj;
lean_object* v___y_1315_ = stack[11].m_obj;
lean_object* v_res_1387_;
v_res_1387_ = l_Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__3(v_k_1304_, v___y_1305_, v___y_1306_, v___y_1307_, v___y_1308_, v___y_1309_, v___y_1310_, v___y_1311_, v___y_1312_, v___y_1313_, v___y_1314_, v___y_1315_);
stack->m_obj
 = v_res_1387_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__3___boxed(lean_object* v_k_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_){
_start:
{
lean_object* v_res_1401_; 
v_res_1401_ = l_Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__3(v_k_1388_, v___y_1389_, v___y_1390_, v___y_1391_, v___y_1392_, v___y_1393_, v___y_1394_, v___y_1395_, v___y_1396_, v___y_1397_, v___y_1398_, v___y_1399_);
lean_dec(v___y_1399_);
lean_dec_ref(v___y_1398_);
lean_dec(v___y_1397_);
lean_dec_ref(v___y_1396_);
lean_dec(v___y_1395_);
lean_dec_ref(v___y_1394_);
lean_dec(v___y_1393_);
lean_dec_ref(v___y_1392_);
lean_dec(v___y_1391_);
lean_dec(v___y_1390_);
lean_dec_ref(v___y_1389_);
lean_dec(v_k_1388_);
return v_res_1401_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__3(void){
_start:
{
lean_object* v___x_1409_; lean_object* v___x_1410_; 
v___x_1409_ = lean_unsigned_to_nat(1u);
v___x_1410_ = lean_nat_to_int(v___x_1409_);
return v___x_1410_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv(lean_object* v_e_1435_, lean_object* v_inst_1436_, lean_object* v_a_1437_, lean_object* v_a_1438_, lean_object* v_a_1439_, lean_object* v_a_1440_, lean_object* v_a_1441_, lean_object* v_a_1442_, lean_object* v_a_1443_, lean_object* v_a_1444_, lean_object* v_a_1445_, lean_object* v_a_1446_, lean_object* v_a_1447_, lean_object* v_a_1448_){
_start:
{
lean_object* v___f_1453_; lean_object* v___x_1454_; 
lean_inc_ref(v_a_1437_);
v___f_1453_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___lam__0), 2, 1);
lean_closure_set(v___f_1453_, 0, v_a_1437_);
v___x_1454_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst(v_inst_1436_, v_a_1438_, v_a_1439_, v_a_1440_, v_a_1441_, v_a_1442_, v_a_1443_, v_a_1444_, v_a_1445_, v_a_1446_, v_a_1447_, v_a_1448_);
if (lean_obj_tag(v___x_1454_) == 0)
{
lean_object* v_a_1455_; lean_object* v___x_1457_; uint8_t v_isShared_1458_; uint8_t v_isSharedCheck_1713_; 
v_a_1455_ = lean_ctor_get(v___x_1454_, 0);
v_isSharedCheck_1713_ = !lean_is_exclusive(v___x_1454_);
if (v_isSharedCheck_1713_ == 0)
{
v___x_1457_ = v___x_1454_;
v_isShared_1458_ = v_isSharedCheck_1713_;
goto v_resetjp_1456_;
}
else
{
lean_inc(v_a_1455_);
lean_dec(v___x_1454_);
v___x_1457_ = lean_box(0);
v_isShared_1458_ = v_isSharedCheck_1713_;
goto v_resetjp_1456_;
}
v_resetjp_1456_:
{
uint8_t v___x_1459_; 
v___x_1459_ = lean_unbox(v_a_1455_);
lean_dec(v_a_1455_);
if (v___x_1459_ == 0)
{
lean_object* v___x_1460_; lean_object* v___x_1462_; 
lean_dec_ref(v___f_1453_);
lean_dec_ref(v_a_1437_);
lean_dec_ref(v_e_1435_);
v___x_1460_ = lean_box(0);
if (v_isShared_1458_ == 0)
{
lean_ctor_set(v___x_1457_, 0, v___x_1460_);
v___x_1462_ = v___x_1457_;
goto v_reusejp_1461_;
}
else
{
lean_object* v_reuseFailAlloc_1463_; 
v_reuseFailAlloc_1463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1463_, 0, v___x_1460_);
v___x_1462_ = v_reuseFailAlloc_1463_;
goto v_reusejp_1461_;
}
v_reusejp_1461_:
{
return v___x_1462_;
}
}
else
{
lean_object* v___x_1464_; 
lean_del_object(v___x_1457_);
v___x_1464_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v_a_1438_, v_a_1439_, v_a_1440_, v_a_1441_, v_a_1442_, v_a_1443_, v_a_1444_, v_a_1445_, v_a_1446_, v_a_1447_, v_a_1448_);
if (lean_obj_tag(v___x_1464_) == 0)
{
lean_object* v_a_1465_; lean_object* v___x_1467_; uint8_t v_isShared_1468_; uint8_t v_isSharedCheck_1704_; 
v_a_1465_ = lean_ctor_get(v___x_1464_, 0);
v_isSharedCheck_1704_ = !lean_is_exclusive(v___x_1464_);
if (v_isSharedCheck_1704_ == 0)
{
v___x_1467_ = v___x_1464_;
v_isShared_1468_ = v_isSharedCheck_1704_;
goto v_resetjp_1466_;
}
else
{
lean_inc(v_a_1465_);
lean_dec(v___x_1464_);
v___x_1467_ = lean_box(0);
v_isShared_1468_ = v_isSharedCheck_1704_;
goto v_resetjp_1466_;
}
v_resetjp_1466_:
{
lean_object* v_fieldInst_x3f_1469_; 
v_fieldInst_x3f_1469_ = lean_ctor_get(v_a_1465_, 7);
lean_inc(v_fieldInst_x3f_1469_);
if (lean_obj_tag(v_fieldInst_x3f_1469_) == 1)
{
lean_object* v_toRing_1470_; lean_object* v_val_1471_; lean_object* v___y_1473_; lean_object* v___y_1474_; lean_object* v___y_1475_; lean_object* v___y_1476_; lean_object* v___y_1477_; lean_object* v___y_1478_; lean_object* v___y_1479_; lean_object* v___y_1480_; lean_object* v___y_1481_; lean_object* v___y_1482_; lean_object* v___x_1492_; 
lean_del_object(v___x_1467_);
v_toRing_1470_ = lean_ctor_get(v_a_1465_, 0);
lean_inc_ref(v_toRing_1470_);
lean_dec(v_a_1465_);
v_val_1471_ = lean_ctor_get(v_fieldInst_x3f_1469_, 0);
lean_inc(v_val_1471_);
lean_dec_ref_known(v_fieldInst_x3f_1469_, 1);
v___x_1492_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRingState___redArg(v_a_1438_, v_a_1439_, v_a_1447_);
if (lean_obj_tag(v___x_1492_) == 0)
{
lean_object* v_a_1493_; lean_object* v___x_1495_; uint8_t v_isShared_1496_; uint8_t v_isSharedCheck_1691_; 
v_a_1493_ = lean_ctor_get(v___x_1492_, 0);
v_isSharedCheck_1691_ = !lean_is_exclusive(v___x_1492_);
if (v_isSharedCheck_1691_ == 0)
{
v___x_1495_ = v___x_1492_;
v_isShared_1496_ = v_isSharedCheck_1691_;
goto v_resetjp_1494_;
}
else
{
lean_inc(v_a_1493_);
lean_dec(v___x_1492_);
v___x_1495_ = lean_box(0);
v_isShared_1496_ = v_isSharedCheck_1691_;
goto v_resetjp_1494_;
}
v_resetjp_1494_:
{
lean_object* v_invSet_1497_; uint8_t v___x_1498_; 
v_invSet_1497_ = lean_ctor_get(v_a_1493_, 7);
lean_inc_ref(v_invSet_1497_);
lean_dec(v_a_1493_);
v___x_1498_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1___redArg(v_invSet_1497_, v_a_1437_);
lean_dec_ref(v_invSet_1497_);
if (v___x_1498_ == 0)
{
lean_object* v___x_1499_; 
lean_del_object(v___x_1495_);
v___x_1499_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRingState___redArg(v___f_1453_, v_a_1438_, v_a_1439_);
if (lean_obj_tag(v___x_1499_) == 0)
{
lean_object* v___x_1500_; 
lean_dec_ref_known(v___x_1499_, 1);
lean_inc_ref(v_a_1437_);
v___x_1500_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f(v_a_1437_, v_a_1438_, v_a_1439_, v_a_1440_, v_a_1441_, v_a_1442_, v_a_1443_, v_a_1444_, v_a_1445_, v_a_1446_, v_a_1447_, v_a_1448_);
if (lean_obj_tag(v___x_1500_) == 0)
{
lean_object* v_a_1501_; 
v_a_1501_ = lean_ctor_get(v___x_1500_, 0);
lean_inc(v_a_1501_);
lean_dec_ref_known(v___x_1500_, 1);
if (lean_obj_tag(v_a_1501_) == 1)
{
lean_object* v_val_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; uint8_t v___x_1505_; 
v_val_1502_ = lean_ctor_get(v_a_1501_, 0);
lean_inc(v_val_1502_);
lean_dec_ref_known(v_a_1501_, 1);
v___x_1503_ = lean_unsigned_to_nat(0u);
v___x_1504_ = lean_obj_once(&l_Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__3___closed__1, &l_Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__3___closed__1_once, _init_l_Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__3___closed__1);
v___x_1505_ = lean_int_dec_eq(v_val_1502_, v___x_1504_);
if (v___x_1505_ == 0)
{
lean_object* v___x_1506_; 
v___x_1506_ = l_Lean_Meta_Grind_Arith_CommRing_hasChar(v_a_1438_, v_a_1439_, v_a_1440_, v_a_1441_, v_a_1442_, v_a_1443_, v_a_1444_, v_a_1445_, v_a_1446_, v_a_1447_, v_a_1448_);
if (lean_obj_tag(v___x_1506_) == 0)
{
lean_object* v_a_1507_; uint8_t v___x_1508_; 
v_a_1507_ = lean_ctor_get(v___x_1506_, 0);
lean_inc(v_a_1507_);
lean_dec_ref_known(v___x_1506_, 1);
v___x_1508_ = lean_unbox(v_a_1507_);
lean_dec(v_a_1507_);
if (v___x_1508_ == 0)
{
lean_dec(v_val_1502_);
lean_dec_ref(v_e_1435_);
v___y_1473_ = v_a_1439_;
v___y_1474_ = v_a_1440_;
v___y_1475_ = v_a_1441_;
v___y_1476_ = v_a_1442_;
v___y_1477_ = v_a_1443_;
v___y_1478_ = v_a_1444_;
v___y_1479_ = v_a_1445_;
v___y_1480_ = v_a_1446_;
v___y_1481_ = v_a_1447_;
v___y_1482_ = v_a_1448_;
goto v___jp_1472_;
}
else
{
lean_object* v___x_1509_; 
v___x_1509_ = l_Lean_Meta_Grind_Arith_CommRing_getCharInst(v_a_1438_, v_a_1439_, v_a_1440_, v_a_1441_, v_a_1442_, v_a_1443_, v_a_1444_, v_a_1445_, v_a_1446_, v_a_1447_, v_a_1448_);
if (lean_obj_tag(v___x_1509_) == 0)
{
lean_object* v_a_1510_; lean_object* v_fst_1511_; lean_object* v_snd_1512_; lean_object* v___x_1514_; uint8_t v_isShared_1515_; uint8_t v_isSharedCheck_1645_; 
v_a_1510_ = lean_ctor_get(v___x_1509_, 0);
lean_inc(v_a_1510_);
lean_dec_ref_known(v___x_1509_, 1);
v_fst_1511_ = lean_ctor_get(v_a_1510_, 0);
v_snd_1512_ = lean_ctor_get(v_a_1510_, 1);
v_isSharedCheck_1645_ = !lean_is_exclusive(v_a_1510_);
if (v_isSharedCheck_1645_ == 0)
{
v___x_1514_ = v_a_1510_;
v_isShared_1515_ = v_isSharedCheck_1645_;
goto v_resetjp_1513_;
}
else
{
lean_inc(v_snd_1512_);
lean_inc(v_fst_1511_);
lean_dec(v_a_1510_);
v___x_1514_ = lean_box(0);
v_isShared_1515_ = v_isSharedCheck_1645_;
goto v_resetjp_1513_;
}
v_resetjp_1513_:
{
uint8_t v___x_1516_; 
v___x_1516_ = lean_nat_dec_eq(v_snd_1512_, v___x_1503_);
if (v___x_1516_ == 0)
{
lean_object* v___x_1517_; lean_object* v___x_1518_; uint8_t v___x_1519_; 
lean_inc(v_snd_1512_);
v___x_1517_ = lean_nat_to_int(v_snd_1512_);
v___x_1518_ = lean_int_emod(v_val_1502_, v___x_1517_);
lean_dec(v___x_1517_);
v___x_1519_ = lean_int_dec_eq(v___x_1518_, v___x_1504_);
lean_dec(v___x_1518_);
if (v___x_1519_ == 0)
{
lean_object* v___x_1520_; 
v___x_1520_ = l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__2(v_a_1438_, v_a_1439_, v_a_1440_, v_a_1441_, v_a_1442_, v_a_1443_, v_a_1444_, v_a_1445_, v_a_1446_, v_a_1447_, v_a_1448_);
if (lean_obj_tag(v___x_1520_) == 0)
{
lean_object* v_a_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; 
v_a_1521_ = lean_ctor_get(v___x_1520_, 0);
lean_inc(v_a_1521_);
lean_dec_ref_known(v___x_1520_, 1);
v___x_1522_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__3, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__3);
v___x_1523_ = l_Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__3(v___x_1522_, v_a_1438_, v_a_1439_, v_a_1440_, v_a_1441_, v_a_1442_, v_a_1443_, v_a_1444_, v_a_1445_, v_a_1446_, v_a_1447_, v_a_1448_);
if (lean_obj_tag(v___x_1523_) == 0)
{
lean_object* v_a_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; 
v_a_1524_ = lean_ctor_get(v___x_1523_, 0);
lean_inc(v_a_1524_);
lean_dec_ref_known(v___x_1523_, 1);
v___x_1525_ = l_Lean_mkAppB(v_a_1521_, v_a_1437_, v_e_1435_);
v___x_1526_ = l_Lean_Meta_mkEq(v___x_1525_, v_a_1524_, v_a_1445_, v_a_1446_, v_a_1447_, v_a_1448_);
if (lean_obj_tag(v___x_1526_) == 0)
{
lean_object* v_a_1527_; lean_object* v_type_1528_; lean_object* v_u_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1533_; 
v_a_1527_ = lean_ctor_get(v___x_1526_, 0);
lean_inc(v_a_1527_);
lean_dec_ref_known(v___x_1526_, 1);
v_type_1528_ = lean_ctor_get(v_toRing_1470_, 1);
lean_inc_ref(v_type_1528_);
v_u_1529_ = lean_ctor_get(v_toRing_1470_, 2);
lean_inc(v_u_1529_);
lean_dec_ref(v_toRing_1470_);
v___x_1530_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__5));
v___x_1531_ = lean_box(0);
if (v_isShared_1515_ == 0)
{
lean_ctor_set_tag(v___x_1514_, 1);
lean_ctor_set(v___x_1514_, 1, v___x_1531_);
lean_ctor_set(v___x_1514_, 0, v_u_1529_);
v___x_1533_ = v___x_1514_;
goto v_reusejp_1532_;
}
else
{
lean_object* v_reuseFailAlloc_1541_; 
v_reuseFailAlloc_1541_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1541_, 0, v_u_1529_);
lean_ctor_set(v_reuseFailAlloc_1541_, 1, v___x_1531_);
v___x_1533_ = v_reuseFailAlloc_1541_;
goto v_reusejp_1532_;
}
v_reusejp_1532_:
{
lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; 
v___x_1534_ = l_Lean_mkConst(v___x_1530_, v___x_1533_);
v___x_1535_ = l_Lean_mkNatLit(v_snd_1512_);
v___x_1536_ = l_Lean_mkIntLit(v_val_1502_);
lean_dec(v_val_1502_);
v___x_1537_ = l_Lean_eagerReflBoolTrue;
v___x_1538_ = l_Lean_mkApp6(v___x_1534_, v_type_1528_, v___x_1535_, v_val_1471_, v_fst_1511_, v___x_1536_, v___x_1537_);
v___x_1539_ = l_Lean_Meta_mkExpectedPropHint(v___x_1538_, v_a_1527_);
v___x_1540_ = l_Lean_Meta_Grind_pushNewFact(v___x_1539_, v___x_1503_, v_a_1439_, v_a_1440_, v_a_1441_, v_a_1442_, v_a_1443_, v_a_1444_, v_a_1445_, v_a_1446_, v_a_1447_, v_a_1448_);
if (lean_obj_tag(v___x_1540_) == 0)
{
lean_dec_ref_known(v___x_1540_, 1);
goto v___jp_1450_;
}
else
{
return v___x_1540_;
}
}
}
else
{
lean_object* v_a_1542_; lean_object* v___x_1544_; uint8_t v_isShared_1545_; uint8_t v_isSharedCheck_1549_; 
lean_del_object(v___x_1514_);
lean_dec(v_snd_1512_);
lean_dec(v_fst_1511_);
lean_dec(v_val_1502_);
lean_dec(v_val_1471_);
lean_dec_ref(v_toRing_1470_);
v_a_1542_ = lean_ctor_get(v___x_1526_, 0);
v_isSharedCheck_1549_ = !lean_is_exclusive(v___x_1526_);
if (v_isSharedCheck_1549_ == 0)
{
v___x_1544_ = v___x_1526_;
v_isShared_1545_ = v_isSharedCheck_1549_;
goto v_resetjp_1543_;
}
else
{
lean_inc(v_a_1542_);
lean_dec(v___x_1526_);
v___x_1544_ = lean_box(0);
v_isShared_1545_ = v_isSharedCheck_1549_;
goto v_resetjp_1543_;
}
v_resetjp_1543_:
{
lean_object* v___x_1547_; 
if (v_isShared_1545_ == 0)
{
v___x_1547_ = v___x_1544_;
goto v_reusejp_1546_;
}
else
{
lean_object* v_reuseFailAlloc_1548_; 
v_reuseFailAlloc_1548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1548_, 0, v_a_1542_);
v___x_1547_ = v_reuseFailAlloc_1548_;
goto v_reusejp_1546_;
}
v_reusejp_1546_:
{
return v___x_1547_;
}
}
}
}
else
{
lean_object* v_a_1550_; lean_object* v___x_1552_; uint8_t v_isShared_1553_; uint8_t v_isSharedCheck_1557_; 
lean_dec(v_a_1521_);
lean_del_object(v___x_1514_);
lean_dec(v_snd_1512_);
lean_dec(v_fst_1511_);
lean_dec(v_val_1502_);
lean_dec(v_val_1471_);
lean_dec_ref(v_toRing_1470_);
lean_dec_ref(v_a_1437_);
lean_dec_ref(v_e_1435_);
v_a_1550_ = lean_ctor_get(v___x_1523_, 0);
v_isSharedCheck_1557_ = !lean_is_exclusive(v___x_1523_);
if (v_isSharedCheck_1557_ == 0)
{
v___x_1552_ = v___x_1523_;
v_isShared_1553_ = v_isSharedCheck_1557_;
goto v_resetjp_1551_;
}
else
{
lean_inc(v_a_1550_);
lean_dec(v___x_1523_);
v___x_1552_ = lean_box(0);
v_isShared_1553_ = v_isSharedCheck_1557_;
goto v_resetjp_1551_;
}
v_resetjp_1551_:
{
lean_object* v___x_1555_; 
if (v_isShared_1553_ == 0)
{
v___x_1555_ = v___x_1552_;
goto v_reusejp_1554_;
}
else
{
lean_object* v_reuseFailAlloc_1556_; 
v_reuseFailAlloc_1556_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1556_, 0, v_a_1550_);
v___x_1555_ = v_reuseFailAlloc_1556_;
goto v_reusejp_1554_;
}
v_reusejp_1554_:
{
return v___x_1555_;
}
}
}
}
else
{
lean_object* v_a_1558_; lean_object* v___x_1560_; uint8_t v_isShared_1561_; uint8_t v_isSharedCheck_1565_; 
lean_del_object(v___x_1514_);
lean_dec(v_snd_1512_);
lean_dec(v_fst_1511_);
lean_dec(v_val_1502_);
lean_dec(v_val_1471_);
lean_dec_ref(v_toRing_1470_);
lean_dec_ref(v_a_1437_);
lean_dec_ref(v_e_1435_);
v_a_1558_ = lean_ctor_get(v___x_1520_, 0);
v_isSharedCheck_1565_ = !lean_is_exclusive(v___x_1520_);
if (v_isSharedCheck_1565_ == 0)
{
v___x_1560_ = v___x_1520_;
v_isShared_1561_ = v_isSharedCheck_1565_;
goto v_resetjp_1559_;
}
else
{
lean_inc(v_a_1558_);
lean_dec(v___x_1520_);
v___x_1560_ = lean_box(0);
v_isShared_1561_ = v_isSharedCheck_1565_;
goto v_resetjp_1559_;
}
v_resetjp_1559_:
{
lean_object* v___x_1563_; 
if (v_isShared_1561_ == 0)
{
v___x_1563_ = v___x_1560_;
goto v_reusejp_1562_;
}
else
{
lean_object* v_reuseFailAlloc_1564_; 
v_reuseFailAlloc_1564_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1564_, 0, v_a_1558_);
v___x_1563_ = v_reuseFailAlloc_1564_;
goto v_reusejp_1562_;
}
v_reusejp_1562_:
{
return v___x_1563_;
}
}
}
}
else
{
lean_object* v___x_1566_; 
lean_dec_ref(v_a_1437_);
v___x_1566_ = l_Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__3(v___x_1504_, v_a_1438_, v_a_1439_, v_a_1440_, v_a_1441_, v_a_1442_, v_a_1443_, v_a_1444_, v_a_1445_, v_a_1446_, v_a_1447_, v_a_1448_);
if (lean_obj_tag(v___x_1566_) == 0)
{
lean_object* v_a_1567_; lean_object* v___x_1568_; 
v_a_1567_ = lean_ctor_get(v___x_1566_, 0);
lean_inc(v_a_1567_);
lean_dec_ref_known(v___x_1566_, 1);
v___x_1568_ = l_Lean_Meta_mkEq(v_e_1435_, v_a_1567_, v_a_1445_, v_a_1446_, v_a_1447_, v_a_1448_);
if (lean_obj_tag(v___x_1568_) == 0)
{
lean_object* v_a_1569_; lean_object* v_type_1570_; lean_object* v_u_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1575_; 
v_a_1569_ = lean_ctor_get(v___x_1568_, 0);
lean_inc(v_a_1569_);
lean_dec_ref_known(v___x_1568_, 1);
v_type_1570_ = lean_ctor_get(v_toRing_1470_, 1);
lean_inc_ref(v_type_1570_);
v_u_1571_ = lean_ctor_get(v_toRing_1470_, 2);
lean_inc(v_u_1571_);
lean_dec_ref(v_toRing_1470_);
v___x_1572_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__7));
v___x_1573_ = lean_box(0);
if (v_isShared_1515_ == 0)
{
lean_ctor_set_tag(v___x_1514_, 1);
lean_ctor_set(v___x_1514_, 1, v___x_1573_);
lean_ctor_set(v___x_1514_, 0, v_u_1571_);
v___x_1575_ = v___x_1514_;
goto v_reusejp_1574_;
}
else
{
lean_object* v_reuseFailAlloc_1583_; 
v_reuseFailAlloc_1583_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1583_, 0, v_u_1571_);
lean_ctor_set(v_reuseFailAlloc_1583_, 1, v___x_1573_);
v___x_1575_ = v_reuseFailAlloc_1583_;
goto v_reusejp_1574_;
}
v_reusejp_1574_:
{
lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; 
v___x_1576_ = l_Lean_mkConst(v___x_1572_, v___x_1575_);
v___x_1577_ = l_Lean_mkNatLit(v_snd_1512_);
v___x_1578_ = l_Lean_mkIntLit(v_val_1502_);
lean_dec(v_val_1502_);
v___x_1579_ = l_Lean_eagerReflBoolTrue;
v___x_1580_ = l_Lean_mkApp6(v___x_1576_, v_type_1570_, v___x_1577_, v_val_1471_, v_fst_1511_, v___x_1578_, v___x_1579_);
v___x_1581_ = l_Lean_Meta_mkExpectedPropHint(v___x_1580_, v_a_1569_);
v___x_1582_ = l_Lean_Meta_Grind_pushNewFact(v___x_1581_, v___x_1503_, v_a_1439_, v_a_1440_, v_a_1441_, v_a_1442_, v_a_1443_, v_a_1444_, v_a_1445_, v_a_1446_, v_a_1447_, v_a_1448_);
if (lean_obj_tag(v___x_1582_) == 0)
{
lean_dec_ref_known(v___x_1582_, 1);
goto v___jp_1450_;
}
else
{
return v___x_1582_;
}
}
}
else
{
lean_object* v_a_1584_; lean_object* v___x_1586_; uint8_t v_isShared_1587_; uint8_t v_isSharedCheck_1591_; 
lean_del_object(v___x_1514_);
lean_dec(v_snd_1512_);
lean_dec(v_fst_1511_);
lean_dec(v_val_1502_);
lean_dec(v_val_1471_);
lean_dec_ref(v_toRing_1470_);
v_a_1584_ = lean_ctor_get(v___x_1568_, 0);
v_isSharedCheck_1591_ = !lean_is_exclusive(v___x_1568_);
if (v_isSharedCheck_1591_ == 0)
{
v___x_1586_ = v___x_1568_;
v_isShared_1587_ = v_isSharedCheck_1591_;
goto v_resetjp_1585_;
}
else
{
lean_inc(v_a_1584_);
lean_dec(v___x_1568_);
v___x_1586_ = lean_box(0);
v_isShared_1587_ = v_isSharedCheck_1591_;
goto v_resetjp_1585_;
}
v_resetjp_1585_:
{
lean_object* v___x_1589_; 
if (v_isShared_1587_ == 0)
{
v___x_1589_ = v___x_1586_;
goto v_reusejp_1588_;
}
else
{
lean_object* v_reuseFailAlloc_1590_; 
v_reuseFailAlloc_1590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1590_, 0, v_a_1584_);
v___x_1589_ = v_reuseFailAlloc_1590_;
goto v_reusejp_1588_;
}
v_reusejp_1588_:
{
return v___x_1589_;
}
}
}
}
else
{
lean_object* v_a_1592_; lean_object* v___x_1594_; uint8_t v_isShared_1595_; uint8_t v_isSharedCheck_1599_; 
lean_del_object(v___x_1514_);
lean_dec(v_snd_1512_);
lean_dec(v_fst_1511_);
lean_dec(v_val_1502_);
lean_dec(v_val_1471_);
lean_dec_ref(v_toRing_1470_);
lean_dec_ref(v_e_1435_);
v_a_1592_ = lean_ctor_get(v___x_1566_, 0);
v_isSharedCheck_1599_ = !lean_is_exclusive(v___x_1566_);
if (v_isSharedCheck_1599_ == 0)
{
v___x_1594_ = v___x_1566_;
v_isShared_1595_ = v_isSharedCheck_1599_;
goto v_resetjp_1593_;
}
else
{
lean_inc(v_a_1592_);
lean_dec(v___x_1566_);
v___x_1594_ = lean_box(0);
v_isShared_1595_ = v_isSharedCheck_1599_;
goto v_resetjp_1593_;
}
v_resetjp_1593_:
{
lean_object* v___x_1597_; 
if (v_isShared_1595_ == 0)
{
v___x_1597_ = v___x_1594_;
goto v_reusejp_1596_;
}
else
{
lean_object* v_reuseFailAlloc_1598_; 
v_reuseFailAlloc_1598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1598_, 0, v_a_1592_);
v___x_1597_ = v_reuseFailAlloc_1598_;
goto v_reusejp_1596_;
}
v_reusejp_1596_:
{
return v___x_1597_;
}
}
}
}
}
else
{
lean_object* v___x_1600_; 
lean_dec(v_snd_1512_);
v___x_1600_ = l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__2(v_a_1438_, v_a_1439_, v_a_1440_, v_a_1441_, v_a_1442_, v_a_1443_, v_a_1444_, v_a_1445_, v_a_1446_, v_a_1447_, v_a_1448_);
if (lean_obj_tag(v___x_1600_) == 0)
{
lean_object* v_a_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; 
v_a_1601_ = lean_ctor_get(v___x_1600_, 0);
lean_inc(v_a_1601_);
lean_dec_ref_known(v___x_1600_, 1);
v___x_1602_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__3, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__3);
v___x_1603_ = l_Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__3(v___x_1602_, v_a_1438_, v_a_1439_, v_a_1440_, v_a_1441_, v_a_1442_, v_a_1443_, v_a_1444_, v_a_1445_, v_a_1446_, v_a_1447_, v_a_1448_);
if (lean_obj_tag(v___x_1603_) == 0)
{
lean_object* v_a_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; 
v_a_1604_ = lean_ctor_get(v___x_1603_, 0);
lean_inc(v_a_1604_);
lean_dec_ref_known(v___x_1603_, 1);
v___x_1605_ = l_Lean_mkAppB(v_a_1601_, v_a_1437_, v_e_1435_);
v___x_1606_ = l_Lean_Meta_mkEq(v___x_1605_, v_a_1604_, v_a_1445_, v_a_1446_, v_a_1447_, v_a_1448_);
if (lean_obj_tag(v___x_1606_) == 0)
{
lean_object* v_a_1607_; lean_object* v_type_1608_; lean_object* v_u_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1613_; 
v_a_1607_ = lean_ctor_get(v___x_1606_, 0);
lean_inc(v_a_1607_);
lean_dec_ref_known(v___x_1606_, 1);
v_type_1608_ = lean_ctor_get(v_toRing_1470_, 1);
lean_inc_ref(v_type_1608_);
v_u_1609_ = lean_ctor_get(v_toRing_1470_, 2);
lean_inc(v_u_1609_);
lean_dec_ref(v_toRing_1470_);
v___x_1610_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__9));
v___x_1611_ = lean_box(0);
if (v_isShared_1515_ == 0)
{
lean_ctor_set_tag(v___x_1514_, 1);
lean_ctor_set(v___x_1514_, 1, v___x_1611_);
lean_ctor_set(v___x_1514_, 0, v_u_1609_);
v___x_1613_ = v___x_1514_;
goto v_reusejp_1612_;
}
else
{
lean_object* v_reuseFailAlloc_1620_; 
v_reuseFailAlloc_1620_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1620_, 0, v_u_1609_);
lean_ctor_set(v_reuseFailAlloc_1620_, 1, v___x_1611_);
v___x_1613_ = v_reuseFailAlloc_1620_;
goto v_reusejp_1612_;
}
v_reusejp_1612_:
{
lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; 
v___x_1614_ = l_Lean_mkConst(v___x_1610_, v___x_1613_);
v___x_1615_ = l_Lean_mkIntLit(v_val_1502_);
lean_dec(v_val_1502_);
v___x_1616_ = l_Lean_eagerReflBoolTrue;
v___x_1617_ = l_Lean_mkApp5(v___x_1614_, v_type_1608_, v_val_1471_, v_fst_1511_, v___x_1615_, v___x_1616_);
v___x_1618_ = l_Lean_Meta_mkExpectedPropHint(v___x_1617_, v_a_1607_);
v___x_1619_ = l_Lean_Meta_Grind_pushNewFact(v___x_1618_, v___x_1503_, v_a_1439_, v_a_1440_, v_a_1441_, v_a_1442_, v_a_1443_, v_a_1444_, v_a_1445_, v_a_1446_, v_a_1447_, v_a_1448_);
if (lean_obj_tag(v___x_1619_) == 0)
{
lean_dec_ref_known(v___x_1619_, 1);
goto v___jp_1450_;
}
else
{
return v___x_1619_;
}
}
}
else
{
lean_object* v_a_1621_; lean_object* v___x_1623_; uint8_t v_isShared_1624_; uint8_t v_isSharedCheck_1628_; 
lean_del_object(v___x_1514_);
lean_dec(v_fst_1511_);
lean_dec(v_val_1502_);
lean_dec(v_val_1471_);
lean_dec_ref(v_toRing_1470_);
v_a_1621_ = lean_ctor_get(v___x_1606_, 0);
v_isSharedCheck_1628_ = !lean_is_exclusive(v___x_1606_);
if (v_isSharedCheck_1628_ == 0)
{
v___x_1623_ = v___x_1606_;
v_isShared_1624_ = v_isSharedCheck_1628_;
goto v_resetjp_1622_;
}
else
{
lean_inc(v_a_1621_);
lean_dec(v___x_1606_);
v___x_1623_ = lean_box(0);
v_isShared_1624_ = v_isSharedCheck_1628_;
goto v_resetjp_1622_;
}
v_resetjp_1622_:
{
lean_object* v___x_1626_; 
if (v_isShared_1624_ == 0)
{
v___x_1626_ = v___x_1623_;
goto v_reusejp_1625_;
}
else
{
lean_object* v_reuseFailAlloc_1627_; 
v_reuseFailAlloc_1627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1627_, 0, v_a_1621_);
v___x_1626_ = v_reuseFailAlloc_1627_;
goto v_reusejp_1625_;
}
v_reusejp_1625_:
{
return v___x_1626_;
}
}
}
}
else
{
lean_object* v_a_1629_; lean_object* v___x_1631_; uint8_t v_isShared_1632_; uint8_t v_isSharedCheck_1636_; 
lean_dec(v_a_1601_);
lean_del_object(v___x_1514_);
lean_dec(v_fst_1511_);
lean_dec(v_val_1502_);
lean_dec(v_val_1471_);
lean_dec_ref(v_toRing_1470_);
lean_dec_ref(v_a_1437_);
lean_dec_ref(v_e_1435_);
v_a_1629_ = lean_ctor_get(v___x_1603_, 0);
v_isSharedCheck_1636_ = !lean_is_exclusive(v___x_1603_);
if (v_isSharedCheck_1636_ == 0)
{
v___x_1631_ = v___x_1603_;
v_isShared_1632_ = v_isSharedCheck_1636_;
goto v_resetjp_1630_;
}
else
{
lean_inc(v_a_1629_);
lean_dec(v___x_1603_);
v___x_1631_ = lean_box(0);
v_isShared_1632_ = v_isSharedCheck_1636_;
goto v_resetjp_1630_;
}
v_resetjp_1630_:
{
lean_object* v___x_1634_; 
if (v_isShared_1632_ == 0)
{
v___x_1634_ = v___x_1631_;
goto v_reusejp_1633_;
}
else
{
lean_object* v_reuseFailAlloc_1635_; 
v_reuseFailAlloc_1635_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1635_, 0, v_a_1629_);
v___x_1634_ = v_reuseFailAlloc_1635_;
goto v_reusejp_1633_;
}
v_reusejp_1633_:
{
return v___x_1634_;
}
}
}
}
else
{
lean_object* v_a_1637_; lean_object* v___x_1639_; uint8_t v_isShared_1640_; uint8_t v_isSharedCheck_1644_; 
lean_del_object(v___x_1514_);
lean_dec(v_fst_1511_);
lean_dec(v_val_1502_);
lean_dec(v_val_1471_);
lean_dec_ref(v_toRing_1470_);
lean_dec_ref(v_a_1437_);
lean_dec_ref(v_e_1435_);
v_a_1637_ = lean_ctor_get(v___x_1600_, 0);
v_isSharedCheck_1644_ = !lean_is_exclusive(v___x_1600_);
if (v_isSharedCheck_1644_ == 0)
{
v___x_1639_ = v___x_1600_;
v_isShared_1640_ = v_isSharedCheck_1644_;
goto v_resetjp_1638_;
}
else
{
lean_inc(v_a_1637_);
lean_dec(v___x_1600_);
v___x_1639_ = lean_box(0);
v_isShared_1640_ = v_isSharedCheck_1644_;
goto v_resetjp_1638_;
}
v_resetjp_1638_:
{
lean_object* v___x_1642_; 
if (v_isShared_1640_ == 0)
{
v___x_1642_ = v___x_1639_;
goto v_reusejp_1641_;
}
else
{
lean_object* v_reuseFailAlloc_1643_; 
v_reuseFailAlloc_1643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1643_, 0, v_a_1637_);
v___x_1642_ = v_reuseFailAlloc_1643_;
goto v_reusejp_1641_;
}
v_reusejp_1641_:
{
return v___x_1642_;
}
}
}
}
}
}
else
{
lean_object* v_a_1646_; lean_object* v___x_1648_; uint8_t v_isShared_1649_; uint8_t v_isSharedCheck_1653_; 
lean_dec(v_val_1502_);
lean_dec(v_val_1471_);
lean_dec_ref(v_toRing_1470_);
lean_dec_ref(v_a_1437_);
lean_dec_ref(v_e_1435_);
v_a_1646_ = lean_ctor_get(v___x_1509_, 0);
v_isSharedCheck_1653_ = !lean_is_exclusive(v___x_1509_);
if (v_isSharedCheck_1653_ == 0)
{
v___x_1648_ = v___x_1509_;
v_isShared_1649_ = v_isSharedCheck_1653_;
goto v_resetjp_1647_;
}
else
{
lean_inc(v_a_1646_);
lean_dec(v___x_1509_);
v___x_1648_ = lean_box(0);
v_isShared_1649_ = v_isSharedCheck_1653_;
goto v_resetjp_1647_;
}
v_resetjp_1647_:
{
lean_object* v___x_1651_; 
if (v_isShared_1649_ == 0)
{
v___x_1651_ = v___x_1648_;
goto v_reusejp_1650_;
}
else
{
lean_object* v_reuseFailAlloc_1652_; 
v_reuseFailAlloc_1652_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1652_, 0, v_a_1646_);
v___x_1651_ = v_reuseFailAlloc_1652_;
goto v_reusejp_1650_;
}
v_reusejp_1650_:
{
return v___x_1651_;
}
}
}
}
}
else
{
lean_object* v_a_1654_; lean_object* v___x_1656_; uint8_t v_isShared_1657_; uint8_t v_isSharedCheck_1661_; 
lean_dec(v_val_1502_);
lean_dec(v_val_1471_);
lean_dec_ref(v_toRing_1470_);
lean_dec_ref(v_a_1437_);
lean_dec_ref(v_e_1435_);
v_a_1654_ = lean_ctor_get(v___x_1506_, 0);
v_isSharedCheck_1661_ = !lean_is_exclusive(v___x_1506_);
if (v_isSharedCheck_1661_ == 0)
{
v___x_1656_ = v___x_1506_;
v_isShared_1657_ = v_isSharedCheck_1661_;
goto v_resetjp_1655_;
}
else
{
lean_inc(v_a_1654_);
lean_dec(v___x_1506_);
v___x_1656_ = lean_box(0);
v_isShared_1657_ = v_isSharedCheck_1661_;
goto v_resetjp_1655_;
}
v_resetjp_1655_:
{
lean_object* v___x_1659_; 
if (v_isShared_1657_ == 0)
{
v___x_1659_ = v___x_1656_;
goto v_reusejp_1658_;
}
else
{
lean_object* v_reuseFailAlloc_1660_; 
v_reuseFailAlloc_1660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1660_, 0, v_a_1654_);
v___x_1659_ = v_reuseFailAlloc_1660_;
goto v_reusejp_1658_;
}
v_reusejp_1658_:
{
return v___x_1659_;
}
}
}
}
else
{
lean_object* v_type_1662_; lean_object* v_u_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; 
lean_dec(v_val_1502_);
v_type_1662_ = lean_ctor_get(v_toRing_1470_, 1);
lean_inc_ref(v_type_1662_);
v_u_1663_ = lean_ctor_get(v_toRing_1470_, 2);
lean_inc(v_u_1663_);
lean_dec_ref(v_toRing_1470_);
v___x_1664_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__11));
v___x_1665_ = lean_box(0);
v___x_1666_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1666_, 0, v_u_1663_);
lean_ctor_set(v___x_1666_, 1, v___x_1665_);
v___x_1667_ = l_Lean_mkConst(v___x_1664_, v___x_1666_);
v___x_1668_ = l_Lean_mkAppB(v___x_1667_, v_type_1662_, v_val_1471_);
v___x_1669_ = l_Lean_Meta_Grind_pushEqCore___redArg(v_e_1435_, v_a_1437_, v___x_1668_, v___x_1498_, v_a_1439_, v_a_1441_, v_a_1445_, v_a_1446_, v_a_1447_, v_a_1448_);
if (lean_obj_tag(v___x_1669_) == 0)
{
lean_object* v___x_1671_; uint8_t v_isShared_1672_; uint8_t v_isSharedCheck_1677_; 
v_isSharedCheck_1677_ = !lean_is_exclusive(v___x_1669_);
if (v_isSharedCheck_1677_ == 0)
{
lean_object* v_unused_1678_; 
v_unused_1678_ = lean_ctor_get(v___x_1669_, 0);
lean_dec(v_unused_1678_);
v___x_1671_ = v___x_1669_;
v_isShared_1672_ = v_isSharedCheck_1677_;
goto v_resetjp_1670_;
}
else
{
lean_dec(v___x_1669_);
v___x_1671_ = lean_box(0);
v_isShared_1672_ = v_isSharedCheck_1677_;
goto v_resetjp_1670_;
}
v_resetjp_1670_:
{
lean_object* v___x_1673_; lean_object* v___x_1675_; 
v___x_1673_ = lean_box(0);
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
return v___x_1669_;
}
}
}
else
{
lean_dec(v_a_1501_);
lean_dec_ref(v_e_1435_);
v___y_1473_ = v_a_1439_;
v___y_1474_ = v_a_1440_;
v___y_1475_ = v_a_1441_;
v___y_1476_ = v_a_1442_;
v___y_1477_ = v_a_1443_;
v___y_1478_ = v_a_1444_;
v___y_1479_ = v_a_1445_;
v___y_1480_ = v_a_1446_;
v___y_1481_ = v_a_1447_;
v___y_1482_ = v_a_1448_;
goto v___jp_1472_;
}
}
else
{
lean_object* v_a_1679_; lean_object* v___x_1681_; uint8_t v_isShared_1682_; uint8_t v_isSharedCheck_1686_; 
lean_dec(v_val_1471_);
lean_dec_ref(v_toRing_1470_);
lean_dec_ref(v_a_1437_);
lean_dec_ref(v_e_1435_);
v_a_1679_ = lean_ctor_get(v___x_1500_, 0);
v_isSharedCheck_1686_ = !lean_is_exclusive(v___x_1500_);
if (v_isSharedCheck_1686_ == 0)
{
v___x_1681_ = v___x_1500_;
v_isShared_1682_ = v_isSharedCheck_1686_;
goto v_resetjp_1680_;
}
else
{
lean_inc(v_a_1679_);
lean_dec(v___x_1500_);
v___x_1681_ = lean_box(0);
v_isShared_1682_ = v_isSharedCheck_1686_;
goto v_resetjp_1680_;
}
v_resetjp_1680_:
{
lean_object* v___x_1684_; 
if (v_isShared_1682_ == 0)
{
v___x_1684_ = v___x_1681_;
goto v_reusejp_1683_;
}
else
{
lean_object* v_reuseFailAlloc_1685_; 
v_reuseFailAlloc_1685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1685_, 0, v_a_1679_);
v___x_1684_ = v_reuseFailAlloc_1685_;
goto v_reusejp_1683_;
}
v_reusejp_1683_:
{
return v___x_1684_;
}
}
}
}
else
{
lean_dec(v_val_1471_);
lean_dec_ref(v_toRing_1470_);
lean_dec_ref(v_a_1437_);
lean_dec_ref(v_e_1435_);
return v___x_1499_;
}
}
else
{
lean_object* v___x_1687_; lean_object* v___x_1689_; 
lean_dec(v_val_1471_);
lean_dec_ref(v_toRing_1470_);
lean_dec_ref(v___f_1453_);
lean_dec_ref(v_a_1437_);
lean_dec_ref(v_e_1435_);
v___x_1687_ = lean_box(0);
if (v_isShared_1496_ == 0)
{
lean_ctor_set(v___x_1495_, 0, v___x_1687_);
v___x_1689_ = v___x_1495_;
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
}
else
{
lean_object* v_a_1692_; lean_object* v___x_1694_; uint8_t v_isShared_1695_; uint8_t v_isSharedCheck_1699_; 
lean_dec(v_val_1471_);
lean_dec_ref(v_toRing_1470_);
lean_dec_ref(v___f_1453_);
lean_dec_ref(v_a_1437_);
lean_dec_ref(v_e_1435_);
v_a_1692_ = lean_ctor_get(v___x_1492_, 0);
v_isSharedCheck_1699_ = !lean_is_exclusive(v___x_1492_);
if (v_isSharedCheck_1699_ == 0)
{
v___x_1694_ = v___x_1492_;
v_isShared_1695_ = v_isSharedCheck_1699_;
goto v_resetjp_1693_;
}
else
{
lean_inc(v_a_1692_);
lean_dec(v___x_1492_);
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
v___jp_1472_:
{
lean_object* v_type_1483_; lean_object* v_u_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; 
v_type_1483_ = lean_ctor_get(v_toRing_1470_, 1);
lean_inc_ref(v_type_1483_);
v_u_1484_ = lean_ctor_get(v_toRing_1470_, 2);
lean_inc(v_u_1484_);
lean_dec_ref(v_toRing_1470_);
v___x_1485_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__2));
v___x_1486_ = lean_box(0);
v___x_1487_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1487_, 0, v_u_1484_);
lean_ctor_set(v___x_1487_, 1, v___x_1486_);
v___x_1488_ = l_Lean_mkConst(v___x_1485_, v___x_1487_);
v___x_1489_ = l_Lean_mkApp3(v___x_1488_, v_type_1483_, v_val_1471_, v_a_1437_);
v___x_1490_ = lean_unsigned_to_nat(0u);
v___x_1491_ = l_Lean_Meta_Grind_pushNewFact(v___x_1489_, v___x_1490_, v___y_1473_, v___y_1474_, v___y_1475_, v___y_1476_, v___y_1477_, v___y_1478_, v___y_1479_, v___y_1480_, v___y_1481_, v___y_1482_);
return v___x_1491_;
}
}
else
{
lean_object* v___x_1700_; lean_object* v___x_1702_; 
lean_dec(v_fieldInst_x3f_1469_);
lean_dec(v_a_1465_);
lean_dec_ref(v___f_1453_);
lean_dec_ref(v_a_1437_);
lean_dec_ref(v_e_1435_);
v___x_1700_ = lean_box(0);
if (v_isShared_1468_ == 0)
{
lean_ctor_set(v___x_1467_, 0, v___x_1700_);
v___x_1702_ = v___x_1467_;
goto v_reusejp_1701_;
}
else
{
lean_object* v_reuseFailAlloc_1703_; 
v_reuseFailAlloc_1703_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1703_, 0, v___x_1700_);
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
lean_dec_ref(v___f_1453_);
lean_dec_ref(v_a_1437_);
lean_dec_ref(v_e_1435_);
v_a_1705_ = lean_ctor_get(v___x_1464_, 0);
v_isSharedCheck_1712_ = !lean_is_exclusive(v___x_1464_);
if (v_isSharedCheck_1712_ == 0)
{
v___x_1707_ = v___x_1464_;
v_isShared_1708_ = v_isSharedCheck_1712_;
goto v_resetjp_1706_;
}
else
{
lean_inc(v_a_1705_);
lean_dec(v___x_1464_);
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
}
else
{
lean_object* v_a_1714_; lean_object* v___x_1716_; uint8_t v_isShared_1717_; uint8_t v_isSharedCheck_1721_; 
lean_dec_ref(v___f_1453_);
lean_dec_ref(v_a_1437_);
lean_dec_ref(v_e_1435_);
v_a_1714_ = lean_ctor_get(v___x_1454_, 0);
v_isSharedCheck_1721_ = !lean_is_exclusive(v___x_1454_);
if (v_isSharedCheck_1721_ == 0)
{
v___x_1716_ = v___x_1454_;
v_isShared_1717_ = v_isSharedCheck_1721_;
goto v_resetjp_1715_;
}
else
{
lean_inc(v_a_1714_);
lean_dec(v___x_1454_);
v___x_1716_ = lean_box(0);
v_isShared_1717_ = v_isSharedCheck_1721_;
goto v_resetjp_1715_;
}
v_resetjp_1715_:
{
lean_object* v___x_1719_; 
if (v_isShared_1717_ == 0)
{
v___x_1719_ = v___x_1716_;
goto v_reusejp_1718_;
}
else
{
lean_object* v_reuseFailAlloc_1720_; 
v_reuseFailAlloc_1720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1720_, 0, v_a_1714_);
v___x_1719_ = v_reuseFailAlloc_1720_;
goto v_reusejp_1718_;
}
v_reusejp_1718_:
{
return v___x_1719_;
}
}
}
v___jp_1450_:
{
lean_object* v___x_1451_; lean_object* v___x_1452_; 
v___x_1451_ = lean_box(0);
v___x_1452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1452_, 0, v___x_1451_);
return v___x_1452_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1435_ = stack[0].m_obj;
lean_object* v_inst_1436_ = stack[1].m_obj;
lean_object* v_a_1437_ = stack[2].m_obj;
lean_object* v_a_1438_ = stack[3].m_obj;
lean_object* v_a_1439_ = stack[4].m_obj;
lean_object* v_a_1440_ = stack[5].m_obj;
lean_object* v_a_1441_ = stack[6].m_obj;
lean_object* v_a_1442_ = stack[7].m_obj;
lean_object* v_a_1443_ = stack[8].m_obj;
lean_object* v_a_1444_ = stack[9].m_obj;
lean_object* v_a_1445_ = stack[10].m_obj;
lean_object* v_a_1446_ = stack[11].m_obj;
lean_object* v_a_1447_ = stack[12].m_obj;
lean_object* v_a_1448_ = stack[13].m_obj;
lean_object* v_res_1722_;
v_res_1722_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv(v_e_1435_, v_inst_1436_, v_a_1437_, v_a_1438_, v_a_1439_, v_a_1440_, v_a_1441_, v_a_1442_, v_a_1443_, v_a_1444_, v_a_1445_, v_a_1446_, v_a_1447_, v_a_1448_);
stack->m_obj
 = v_res_1722_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___boxed(lean_object* v_e_1723_, lean_object* v_inst_1724_, lean_object* v_a_1725_, lean_object* v_a_1726_, lean_object* v_a_1727_, lean_object* v_a_1728_, lean_object* v_a_1729_, lean_object* v_a_1730_, lean_object* v_a_1731_, lean_object* v_a_1732_, lean_object* v_a_1733_, lean_object* v_a_1734_, lean_object* v_a_1735_, lean_object* v_a_1736_, lean_object* v_a_1737_){
_start:
{
lean_object* v_res_1738_; 
v_res_1738_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv(v_e_1723_, v_inst_1724_, v_a_1725_, v_a_1726_, v_a_1727_, v_a_1728_, v_a_1729_, v_a_1730_, v_a_1731_, v_a_1732_, v_a_1733_, v_a_1734_, v_a_1735_, v_a_1736_);
lean_dec(v_a_1736_);
lean_dec_ref(v_a_1735_);
lean_dec(v_a_1734_);
lean_dec_ref(v_a_1733_);
lean_dec(v_a_1732_);
lean_dec_ref(v_a_1731_);
lean_dec(v_a_1730_);
lean_dec_ref(v_a_1729_);
lean_dec(v_a_1728_);
lean_dec(v_a_1727_);
lean_dec_ref(v_a_1726_);
lean_dec_ref(v_inst_1724_);
return v_res_1738_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0(lean_object* v_00_u03b2_1739_, lean_object* v_x_1740_, lean_object* v_x_1741_, lean_object* v_x_1742_){
_start:
{
lean_object* v___x_1743_; 
v___x_1743_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0___redArg(v_x_1740_, v_x_1741_, v_x_1742_);
return v___x_1743_;
}
}
uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1(lean_object* v_00_u03b2_1744_, lean_object* v_x_1745_, lean_object* v_x_1746_){
_start:
{
uint8_t v___x_1747_; 
v___x_1747_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1___redArg(v_x_1745_, v_x_1746_);
return v___x_1747_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1745_ = stack[1].m_obj;
lean_object* v_x_1746_ = stack[2].m_obj;
uint8_t v_res_1748_;
v_res_1748_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1(lean_box(0), v_x_1745_, v_x_1746_);
stack->m_num = v_res_1748_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1___boxed(lean_object* v_00_u03b2_1749_, lean_object* v_x_1750_, lean_object* v_x_1751_){
_start:
{
uint8_t v_res_1752_; lean_object* v_r_1753_; 
v_res_1752_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1(v_00_u03b2_1749_, v_x_1750_, v_x_1751_);
lean_dec_ref(v_x_1751_);
lean_dec_ref(v_x_1750_);
v_r_1753_ = lean_box(v_res_1752_);
return v_r_1753_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0(lean_object* v_00_u03b2_1754_, lean_object* v_x_1755_, size_t v_x_1756_, size_t v_x_1757_, lean_object* v_x_1758_, lean_object* v_x_1759_){
_start:
{
lean_object* v___x_1760_; 
v___x_1760_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg(v_x_1755_, v_x_1756_, v_x_1757_, v_x_1758_, v_x_1759_);
return v___x_1760_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1755_ = stack[1].m_obj;
size_t v_x_1756_ = stack[2].m_num;
size_t v_x_1757_ = stack[3].m_num;
lean_object* v_x_1758_ = stack[4].m_obj;
lean_object* v_x_1759_ = stack[5].m_obj;
lean_object* v_res_1761_;
v_res_1761_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0(lean_box(0), v_x_1755_, v_x_1756_, v_x_1757_, v_x_1758_, v_x_1759_);
stack->m_obj
 = v_res_1761_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1762_, lean_object* v_x_1763_, lean_object* v_x_1764_, lean_object* v_x_1765_, lean_object* v_x_1766_, lean_object* v_x_1767_){
_start:
{
size_t v_x_81778__boxed_1768_; size_t v_x_81779__boxed_1769_; lean_object* v_res_1770_; 
v_x_81778__boxed_1768_ = lean_unbox_usize(v_x_1764_);
lean_dec(v_x_1764_);
v_x_81779__boxed_1769_ = lean_unbox_usize(v_x_1765_);
lean_dec(v_x_1765_);
v_res_1770_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0(v_00_u03b2_1762_, v_x_1763_, v_x_81778__boxed_1768_, v_x_81779__boxed_1769_, v_x_1766_, v_x_1767_);
return v_res_1770_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1_spec__2(lean_object* v_00_u03b2_1771_, lean_object* v_x_1772_, size_t v_x_1773_, lean_object* v_x_1774_){
_start:
{
uint8_t v___x_1775_; 
v___x_1775_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1_spec__2___redArg(v_x_1772_, v_x_1773_, v_x_1774_);
return v___x_1775_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1772_ = stack[1].m_obj;
size_t v_x_1773_ = stack[2].m_num;
lean_object* v_x_1774_ = stack[3].m_obj;
uint8_t v_res_1776_;
v_res_1776_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1_spec__2(lean_box(0), v_x_1772_, v_x_1773_, v_x_1774_);
stack->m_num = v_res_1776_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1777_, lean_object* v_x_1778_, lean_object* v_x_1779_, lean_object* v_x_1780_){
_start:
{
size_t v_x_81806__boxed_1781_; uint8_t v_res_1782_; lean_object* v_r_1783_; 
v_x_81806__boxed_1781_ = lean_unbox_usize(v_x_1779_);
lean_dec(v_x_1779_);
v_res_1782_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1_spec__2(v_00_u03b2_1777_, v_x_1778_, v_x_81806__boxed_1781_, v_x_1780_);
lean_dec_ref(v_x_1780_);
lean_dec_ref(v_x_1778_);
v_r_1783_ = lean_box(v_res_1782_);
return v_r_1783_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1784_, lean_object* v_n_1785_, lean_object* v_k_1786_, lean_object* v_v_1787_){
_start:
{
lean_object* v___x_1788_; 
v___x_1788_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0_spec__1___redArg(v_n_1785_, v_k_1786_, v_v_1787_);
return v___x_1788_;
}
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_1789_, size_t v_depth_1790_, lean_object* v_keys_1791_, lean_object* v_vals_1792_, lean_object* v_heq_1793_, lean_object* v_i_1794_, lean_object* v_entries_1795_){
_start:
{
lean_object* v___x_1796_; 
v___x_1796_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0_spec__2___redArg(v_depth_1790_, v_keys_1791_, v_vals_1792_, v_i_1794_, v_entries_1795_);
return v___x_1796_;
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0_spec__2_0interp(lean_interpreter_value* stack)
{
size_t v_depth_1790_ = stack[1].m_num;
lean_object* v_keys_1791_ = stack[2].m_obj;
lean_object* v_vals_1792_ = stack[3].m_obj;
lean_object* v_i_1794_ = stack[5].m_obj;
lean_object* v_entries_1795_ = stack[6].m_obj;
lean_object* v_res_1797_;
v_res_1797_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0_spec__2(lean_box(0), v_depth_1790_, v_keys_1791_, v_vals_1792_, lean_box(0), v_i_1794_, v_entries_1795_);
stack->m_obj
 = v_res_1797_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1798_, lean_object* v_depth_1799_, lean_object* v_keys_1800_, lean_object* v_vals_1801_, lean_object* v_heq_1802_, lean_object* v_i_1803_, lean_object* v_entries_1804_){
_start:
{
size_t v_depth_boxed_1805_; lean_object* v_res_1806_; 
v_depth_boxed_1805_ = lean_unbox_usize(v_depth_1799_);
lean_dec(v_depth_1799_);
v_res_1806_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0_spec__2(v_00_u03b2_1798_, v_depth_boxed_1805_, v_keys_1800_, v_vals_1801_, v_heq_1802_, v_i_1803_, v_entries_1804_);
lean_dec_ref(v_vals_1801_);
lean_dec_ref(v_keys_1800_);
return v_res_1806_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_1807_, lean_object* v_keys_1808_, lean_object* v_vals_1809_, lean_object* v_heq_1810_, lean_object* v_i_1811_, lean_object* v_k_1812_){
_start:
{
uint8_t v___x_1813_; 
v___x_1813_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1_spec__2_spec__5___redArg(v_keys_1808_, v_i_1811_, v_k_1812_);
return v___x_1813_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1_spec__2_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_keys_1808_ = stack[1].m_obj;
lean_object* v_vals_1809_ = stack[2].m_obj;
lean_object* v_i_1811_ = stack[4].m_obj;
lean_object* v_k_1812_ = stack[5].m_obj;
uint8_t v_res_1814_;
v_res_1814_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1_spec__2_spec__5(lean_box(0), v_keys_1808_, v_vals_1809_, lean_box(0), v_i_1811_, v_k_1812_);
stack->m_num = v_res_1814_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b2_1815_, lean_object* v_keys_1816_, lean_object* v_vals_1817_, lean_object* v_heq_1818_, lean_object* v_i_1819_, lean_object* v_k_1820_){
_start:
{
uint8_t v_res_1821_; lean_object* v_r_1822_; 
v_res_1821_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1_spec__2_spec__5(v_00_u03b2_1815_, v_keys_1816_, v_vals_1817_, v_heq_1818_, v_i_1819_, v_k_1820_);
lean_dec_ref(v_k_1820_);
lean_dec_ref(v_vals_1817_);
lean_dec_ref(v_keys_1816_);
v_r_1822_ = lean_box(v_res_1821_);
return v_r_1822_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0_spec__1_spec__5(lean_object* v_00_u03b2_1823_, lean_object* v_x_1824_, lean_object* v_x_1825_, lean_object* v_x_1826_, lean_object* v_x_1827_){
_start:
{
lean_object* v___x_1828_; 
v___x_1828_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0_spec__1_spec__5___redArg(v_x_1824_, v_x_1825_, v_x_1826_, v_x_1827_);
return v___x_1828_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars___lam__0(lean_object* v_size_1829_, lean_object* v_s_1830_){
_start:
{
lean_object* v_toRingState_1831_; lean_object* v_denoteEntries_1832_; lean_object* v_nextId_1833_; lean_object* v_steps_1834_; lean_object* v_queue_1835_; lean_object* v_basis_1836_; lean_object* v_diseqs_1837_; uint8_t v_recheck_1838_; lean_object* v_invSet_1839_; lean_object* v_numEq0_x3f_1840_; uint8_t v_numEq0Updated_1841_; lean_object* v___x_1843_; uint8_t v_isShared_1844_; uint8_t v_isSharedCheck_1848_; 
v_toRingState_1831_ = lean_ctor_get(v_s_1830_, 0);
v_denoteEntries_1832_ = lean_ctor_get(v_s_1830_, 1);
v_nextId_1833_ = lean_ctor_get(v_s_1830_, 2);
v_steps_1834_ = lean_ctor_get(v_s_1830_, 3);
v_queue_1835_ = lean_ctor_get(v_s_1830_, 4);
v_basis_1836_ = lean_ctor_get(v_s_1830_, 5);
v_diseqs_1837_ = lean_ctor_get(v_s_1830_, 6);
v_recheck_1838_ = lean_ctor_get_uint8(v_s_1830_, sizeof(void*)*10);
v_invSet_1839_ = lean_ctor_get(v_s_1830_, 7);
v_numEq0_x3f_1840_ = lean_ctor_get(v_s_1830_, 9);
v_numEq0Updated_1841_ = lean_ctor_get_uint8(v_s_1830_, sizeof(void*)*10 + 1);
v_isSharedCheck_1848_ = !lean_is_exclusive(v_s_1830_);
if (v_isSharedCheck_1848_ == 0)
{
lean_object* v_unused_1849_; 
v_unused_1849_ = lean_ctor_get(v_s_1830_, 8);
lean_dec(v_unused_1849_);
v___x_1843_ = v_s_1830_;
v_isShared_1844_ = v_isSharedCheck_1848_;
goto v_resetjp_1842_;
}
else
{
lean_inc(v_numEq0_x3f_1840_);
lean_inc(v_invSet_1839_);
lean_inc(v_diseqs_1837_);
lean_inc(v_basis_1836_);
lean_inc(v_queue_1835_);
lean_inc(v_steps_1834_);
lean_inc(v_nextId_1833_);
lean_inc(v_denoteEntries_1832_);
lean_inc(v_toRingState_1831_);
lean_dec(v_s_1830_);
v___x_1843_ = lean_box(0);
v_isShared_1844_ = v_isSharedCheck_1848_;
goto v_resetjp_1842_;
}
v_resetjp_1842_:
{
lean_object* v___x_1846_; 
if (v_isShared_1844_ == 0)
{
lean_ctor_set(v___x_1843_, 8, v_size_1829_);
v___x_1846_ = v___x_1843_;
goto v_reusejp_1845_;
}
else
{
lean_object* v_reuseFailAlloc_1847_; 
v_reuseFailAlloc_1847_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v_reuseFailAlloc_1847_, 0, v_toRingState_1831_);
lean_ctor_set(v_reuseFailAlloc_1847_, 1, v_denoteEntries_1832_);
lean_ctor_set(v_reuseFailAlloc_1847_, 2, v_nextId_1833_);
lean_ctor_set(v_reuseFailAlloc_1847_, 3, v_steps_1834_);
lean_ctor_set(v_reuseFailAlloc_1847_, 4, v_queue_1835_);
lean_ctor_set(v_reuseFailAlloc_1847_, 5, v_basis_1836_);
lean_ctor_set(v_reuseFailAlloc_1847_, 6, v_diseqs_1837_);
lean_ctor_set(v_reuseFailAlloc_1847_, 7, v_invSet_1839_);
lean_ctor_set(v_reuseFailAlloc_1847_, 8, v_size_1829_);
lean_ctor_set(v_reuseFailAlloc_1847_, 9, v_numEq0_x3f_1840_);
lean_ctor_set_uint8(v_reuseFailAlloc_1847_, sizeof(void*)*10, v_recheck_1838_);
lean_ctor_set_uint8(v_reuseFailAlloc_1847_, sizeof(void*)*10 + 1, v_numEq0Updated_1841_);
v___x_1846_ = v_reuseFailAlloc_1847_;
goto v_reusejp_1845_;
}
v_reusejp_1845_:
{
return v___x_1846_;
}
}
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1850_; double v___x_1851_; 
v___x_1850_ = lean_unsigned_to_nat(0u);
v___x_1851_ = lean_float_of_nat(v___x_1850_);
return v___x_1851_;
}
}
lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg(lean_object* v_cls_1855_, lean_object* v_msg_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_){
_start:
{
lean_object* v_ref_1862_; lean_object* v___x_1863_; lean_object* v_a_1864_; lean_object* v___x_1866_; uint8_t v_isShared_1867_; uint8_t v_isSharedCheck_1909_; 
v_ref_1862_ = lean_ctor_get(v___y_1859_, 2);
v___x_1863_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5(v_msg_1856_, v___y_1857_, v___y_1858_, v___y_1859_, v___y_1860_);
v_a_1864_ = lean_ctor_get(v___x_1863_, 0);
v_isSharedCheck_1909_ = !lean_is_exclusive(v___x_1863_);
if (v_isSharedCheck_1909_ == 0)
{
v___x_1866_ = v___x_1863_;
v_isShared_1867_ = v_isSharedCheck_1909_;
goto v_resetjp_1865_;
}
else
{
lean_inc(v_a_1864_);
lean_dec(v___x_1863_);
v___x_1866_ = lean_box(0);
v_isShared_1867_ = v_isSharedCheck_1909_;
goto v_resetjp_1865_;
}
v_resetjp_1865_:
{
lean_object* v___x_1868_; lean_object* v_traceState_1869_; lean_object* v_env_1870_; lean_object* v_nextMacroScope_1871_; lean_object* v_ngen_1872_; lean_object* v_auxDeclNGen_1873_; lean_object* v_cache_1874_; lean_object* v_recordedDeps_1875_; lean_object* v_messages_1876_; lean_object* v_infoState_1877_; lean_object* v_snapshotTasks_1878_; lean_object* v___x_1880_; uint8_t v_isShared_1881_; uint8_t v_isSharedCheck_1908_; 
v___x_1868_ = lean_st_ref_take(v___y_1860_);
v_traceState_1869_ = lean_ctor_get(v___x_1868_, 4);
v_env_1870_ = lean_ctor_get(v___x_1868_, 0);
v_nextMacroScope_1871_ = lean_ctor_get(v___x_1868_, 1);
v_ngen_1872_ = lean_ctor_get(v___x_1868_, 2);
v_auxDeclNGen_1873_ = lean_ctor_get(v___x_1868_, 3);
v_cache_1874_ = lean_ctor_get(v___x_1868_, 5);
v_recordedDeps_1875_ = lean_ctor_get(v___x_1868_, 6);
v_messages_1876_ = lean_ctor_get(v___x_1868_, 7);
v_infoState_1877_ = lean_ctor_get(v___x_1868_, 8);
v_snapshotTasks_1878_ = lean_ctor_get(v___x_1868_, 9);
v_isSharedCheck_1908_ = !lean_is_exclusive(v___x_1868_);
if (v_isSharedCheck_1908_ == 0)
{
v___x_1880_ = v___x_1868_;
v_isShared_1881_ = v_isSharedCheck_1908_;
goto v_resetjp_1879_;
}
else
{
lean_inc(v_snapshotTasks_1878_);
lean_inc(v_infoState_1877_);
lean_inc(v_messages_1876_);
lean_inc(v_recordedDeps_1875_);
lean_inc(v_cache_1874_);
lean_inc(v_traceState_1869_);
lean_inc(v_auxDeclNGen_1873_);
lean_inc(v_ngen_1872_);
lean_inc(v_nextMacroScope_1871_);
lean_inc(v_env_1870_);
lean_dec(v___x_1868_);
v___x_1880_ = lean_box(0);
v_isShared_1881_ = v_isSharedCheck_1908_;
goto v_resetjp_1879_;
}
v_resetjp_1879_:
{
uint64_t v_tid_1882_; lean_object* v_traces_1883_; lean_object* v___x_1885_; uint8_t v_isShared_1886_; uint8_t v_isSharedCheck_1907_; 
v_tid_1882_ = lean_ctor_get_uint64(v_traceState_1869_, sizeof(void*)*1);
v_traces_1883_ = lean_ctor_get(v_traceState_1869_, 0);
v_isSharedCheck_1907_ = !lean_is_exclusive(v_traceState_1869_);
if (v_isSharedCheck_1907_ == 0)
{
v___x_1885_ = v_traceState_1869_;
v_isShared_1886_ = v_isSharedCheck_1907_;
goto v_resetjp_1884_;
}
else
{
lean_inc(v_traces_1883_);
lean_dec(v_traceState_1869_);
v___x_1885_ = lean_box(0);
v_isShared_1886_ = v_isSharedCheck_1907_;
goto v_resetjp_1884_;
}
v_resetjp_1884_:
{
lean_object* v___x_1887_; lean_object* v___x_1888_; double v___x_1889_; uint8_t v___x_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; lean_object* v___x_1898_; 
v___x_1887_ = lean_box(0);
v___x_1888_ = lean_box(0);
v___x_1889_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg___closed__0);
v___x_1890_ = 0;
v___x_1891_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg___closed__1));
v___x_1892_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1892_, 0, v_cls_1855_);
lean_ctor_set(v___x_1892_, 1, v___x_1888_);
lean_ctor_set(v___x_1892_, 2, v___x_1891_);
lean_ctor_set_float(v___x_1892_, sizeof(void*)*3, v___x_1889_);
lean_ctor_set_float(v___x_1892_, sizeof(void*)*3 + 8, v___x_1889_);
lean_ctor_set_uint8(v___x_1892_, sizeof(void*)*3 + 16, v___x_1890_);
v___x_1893_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg___closed__2));
v___x_1894_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1894_, 0, v___x_1892_);
lean_ctor_set(v___x_1894_, 1, v_a_1864_);
lean_ctor_set(v___x_1894_, 2, v___x_1893_);
lean_inc(v_ref_1862_);
v___x_1895_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1895_, 0, v_ref_1862_);
lean_ctor_set(v___x_1895_, 1, v___x_1894_);
v___x_1896_ = l_Lean_PersistentArray_push___redArg(v_traces_1883_, v___x_1895_);
if (v_isShared_1886_ == 0)
{
lean_ctor_set(v___x_1885_, 0, v___x_1896_);
v___x_1898_ = v___x_1885_;
goto v_reusejp_1897_;
}
else
{
lean_object* v_reuseFailAlloc_1906_; 
v_reuseFailAlloc_1906_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1906_, 0, v___x_1896_);
lean_ctor_set_uint64(v_reuseFailAlloc_1906_, sizeof(void*)*1, v_tid_1882_);
v___x_1898_ = v_reuseFailAlloc_1906_;
goto v_reusejp_1897_;
}
v_reusejp_1897_:
{
lean_object* v___x_1900_; 
if (v_isShared_1881_ == 0)
{
lean_ctor_set(v___x_1880_, 4, v___x_1898_);
v___x_1900_ = v___x_1880_;
goto v_reusejp_1899_;
}
else
{
lean_object* v_reuseFailAlloc_1905_; 
v_reuseFailAlloc_1905_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1905_, 0, v_env_1870_);
lean_ctor_set(v_reuseFailAlloc_1905_, 1, v_nextMacroScope_1871_);
lean_ctor_set(v_reuseFailAlloc_1905_, 2, v_ngen_1872_);
lean_ctor_set(v_reuseFailAlloc_1905_, 3, v_auxDeclNGen_1873_);
lean_ctor_set(v_reuseFailAlloc_1905_, 4, v___x_1898_);
lean_ctor_set(v_reuseFailAlloc_1905_, 5, v_cache_1874_);
lean_ctor_set(v_reuseFailAlloc_1905_, 6, v_recordedDeps_1875_);
lean_ctor_set(v_reuseFailAlloc_1905_, 7, v_messages_1876_);
lean_ctor_set(v_reuseFailAlloc_1905_, 8, v_infoState_1877_);
lean_ctor_set(v_reuseFailAlloc_1905_, 9, v_snapshotTasks_1878_);
v___x_1900_ = v_reuseFailAlloc_1905_;
goto v_reusejp_1899_;
}
v_reusejp_1899_:
{
lean_object* v___x_1901_; lean_object* v___x_1903_; 
v___x_1901_ = lean_st_ref_put(v___y_1860_, v___x_1900_);
if (v_isShared_1867_ == 0)
{
lean_ctor_set(v___x_1866_, 0, v___x_1887_);
v___x_1903_ = v___x_1866_;
goto v_reusejp_1902_;
}
else
{
lean_object* v_reuseFailAlloc_1904_; 
v_reuseFailAlloc_1904_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1904_, 0, v___x_1887_);
v___x_1903_ = v_reuseFailAlloc_1904_;
goto v_reusejp_1902_;
}
v_reusejp_1902_:
{
return v___x_1903_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_1855_ = stack[0].m_obj;
lean_object* v_msg_1856_ = stack[1].m_obj;
lean_object* v___y_1857_ = stack[2].m_obj;
lean_object* v___y_1858_ = stack[3].m_obj;
lean_object* v___y_1859_ = stack[4].m_obj;
lean_object* v___y_1860_ = stack[5].m_obj;
lean_object* v_res_1910_;
v_res_1910_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg(v_cls_1855_, v_msg_1856_, v___y_1857_, v___y_1858_, v___y_1859_, v___y_1860_);
stack->m_obj
 = v_res_1910_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg___boxed(lean_object* v_cls_1911_, lean_object* v_msg_1912_, lean_object* v___y_1913_, lean_object* v___y_1914_, lean_object* v___y_1915_, lean_object* v___y_1916_, lean_object* v___y_1917_){
_start:
{
lean_object* v_res_1918_; 
v_res_1918_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg(v_cls_1911_, v_msg_1912_, v___y_1913_, v___y_1914_, v___y_1915_, v___y_1916_);
lean_dec(v___y_1916_);
lean_dec_ref(v___y_1915_);
lean_dec(v___y_1914_);
lean_dec_ref(v___y_1913_);
return v_res_1918_;
}
}
static lean_object* _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__8(void){
_start:
{
lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; 
v___x_1934_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__5));
v___x_1935_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__7));
v___x_1936_ = l_Lean_Name_append(v___x_1935_, v___x_1934_);
return v___x_1936_;
}
}
static lean_object* _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__10(void){
_start:
{
lean_object* v___x_1938_; lean_object* v___x_1939_; 
v___x_1938_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__9));
v___x_1939_ = l_Lean_stringToMessageData(v___x_1938_);
return v___x_1939_;
}
}
static lean_object* _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__12(void){
_start:
{
lean_object* v___x_1941_; lean_object* v___x_1942_; 
v___x_1941_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__11));
v___x_1942_ = l_Lean_stringToMessageData(v___x_1941_);
return v___x_1942_;
}
}
lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg(lean_object* v_a_1943_, lean_object* v_snd_1944_, lean_object* v_fst_1945_, lean_object* v_fst_1946_, lean_object* v___x_1947_, lean_object* v_range_1948_, lean_object* v_b_1949_, lean_object* v_i_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_){
_start:
{
lean_object* v_stop_1963_; lean_object* v_step_1964_; uint8_t v___x_1965_; 
v_stop_1963_ = lean_ctor_get(v_range_1948_, 1);
v_step_1964_ = lean_ctor_get(v_range_1948_, 2);
v___x_1965_ = lean_nat_dec_lt(v_i_1950_, v_stop_1963_);
if (v___x_1965_ == 0)
{
lean_object* v___x_1966_; 
lean_dec(v_i_1950_);
lean_dec_ref(v_fst_1946_);
lean_dec_ref(v_fst_1945_);
lean_dec(v_snd_1944_);
lean_dec_ref(v_a_1943_);
v___x_1966_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1966_, 0, v_b_1949_);
return v___x_1966_;
}
else
{
lean_object* v_size_1967_; lean_object* v___x_1968_; lean_object* v___y_1970_; lean_object* v___y_1971_; lean_object* v___y_1972_; lean_object* v___y_1973_; lean_object* v___y_1974_; lean_object* v___y_1975_; lean_object* v___y_1976_; lean_object* v___y_1977_; lean_object* v___y_1978_; lean_object* v___y_1979_; lean_object* v___y_1980_; lean_object* v___y_1995_; lean_object* v___x_2021_; uint8_t v___x_2022_; 
v_size_1967_ = lean_ctor_get(v___x_1947_, 2);
v___x_1968_ = lean_box(0);
v___x_2021_ = l_Lean_instInhabitedExpr;
v___x_2022_ = lean_nat_dec_lt(v_i_1950_, v_size_1967_);
if (v___x_2022_ == 0)
{
lean_object* v___x_2023_; 
v___x_2023_ = l_outOfBounds___redArg(v___x_2021_);
v___y_1995_ = v___x_2023_;
goto v___jp_1994_;
}
else
{
lean_object* v___x_2024_; 
v___x_2024_ = l_Lean_PersistentArray_get_x21___redArg(v___x_2021_, v___x_1947_, v_i_1950_);
v___y_1995_ = v___x_2024_;
goto v___jp_1994_;
}
v___jp_1969_:
{
lean_object* v_toRing_1981_; lean_object* v_type_1982_; lean_object* v_u_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; lean_object* v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; 
v_toRing_1981_ = lean_ctor_get(v_a_1943_, 0);
v_type_1982_ = lean_ctor_get(v_toRing_1981_, 1);
v_u_1983_ = lean_ctor_get(v_toRing_1981_, 2);
v___x_1984_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__2));
v___x_1985_ = lean_box(0);
lean_inc(v_u_1983_);
v___x_1986_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1986_, 0, v_u_1983_);
lean_ctor_set(v___x_1986_, 1, v___x_1985_);
v___x_1987_ = l_Lean_mkConst(v___x_1984_, v___x_1986_);
lean_inc(v_snd_1944_);
v___x_1988_ = l_Lean_mkNatLit(v_snd_1944_);
lean_inc_ref(v_fst_1946_);
lean_inc_ref(v_fst_1945_);
lean_inc_ref(v_type_1982_);
v___x_1989_ = l_Lean_mkApp5(v___x_1987_, v_type_1982_, v_fst_1945_, v___x_1988_, v_fst_1946_, v___y_1970_);
v___x_1990_ = lean_unsigned_to_nat(0u);
v___x_1991_ = l_Lean_Meta_Grind_pushNewFact(v___x_1989_, v___x_1990_, v___y_1971_, v___y_1972_, v___y_1973_, v___y_1974_, v___y_1975_, v___y_1976_, v___y_1977_, v___y_1978_, v___y_1979_, v___y_1980_);
if (lean_obj_tag(v___x_1991_) == 0)
{
lean_object* v___x_1992_; 
lean_dec_ref_known(v___x_1991_, 1);
v___x_1992_ = lean_nat_add(v_i_1950_, v_step_1964_);
lean_dec(v_i_1950_);
v_b_1949_ = v___x_1968_;
v_i_1950_ = v___x_1992_;
goto _start;
}
else
{
lean_dec(v_i_1950_);
lean_dec_ref(v_fst_1946_);
lean_dec_ref(v_fst_1945_);
lean_dec(v_snd_1944_);
lean_dec_ref(v_a_1943_);
return v___x_1991_;
}
}
v___jp_1994_:
{
lean_object* v_toCold_1996_; lean_object* v_options_1997_; uint8_t v_hasTrace_1998_; 
v_toCold_1996_ = lean_ctor_get(v___y_1960_, 0);
v_options_1997_ = lean_ctor_get(v_toCold_1996_, 2);
v_hasTrace_1998_ = lean_ctor_get_uint8(v_options_1997_, sizeof(void*)*1);
if (v_hasTrace_1998_ == 0)
{
v___y_1970_ = v___y_1995_;
v___y_1971_ = v___y_1952_;
v___y_1972_ = v___y_1953_;
v___y_1973_ = v___y_1954_;
v___y_1974_ = v___y_1955_;
v___y_1975_ = v___y_1956_;
v___y_1976_ = v___y_1957_;
v___y_1977_ = v___y_1958_;
v___y_1978_ = v___y_1959_;
v___y_1979_ = v___y_1960_;
v___y_1980_ = v___y_1961_;
goto v___jp_1969_;
}
else
{
lean_object* v_inheritedTraceOptions_1999_; lean_object* v___x_2000_; lean_object* v___x_2001_; uint8_t v___x_2002_; 
v_inheritedTraceOptions_1999_ = lean_ctor_get(v_toCold_1996_, 11);
v___x_2000_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__5));
v___x_2001_ = lean_obj_once(&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__8, &l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__8_once, _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__8);
v___x_2002_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1999_, v_options_1997_, v___x_2001_);
if (v___x_2002_ == 0)
{
v___y_1970_ = v___y_1995_;
v___y_1971_ = v___y_1952_;
v___y_1972_ = v___y_1953_;
v___y_1973_ = v___y_1954_;
v___y_1974_ = v___y_1955_;
v___y_1975_ = v___y_1956_;
v___y_1976_ = v___y_1957_;
v___y_1977_ = v___y_1958_;
v___y_1978_ = v___y_1959_;
v___y_1979_ = v___y_1960_;
v___y_1980_ = v___y_1961_;
goto v___jp_1969_;
}
else
{
lean_object* v___x_2003_; 
v___x_2003_ = l_Lean_Meta_Grind_updateLastTag(v___y_1952_, v___y_1953_, v___y_1954_, v___y_1955_, v___y_1956_, v___y_1957_, v___y_1958_, v___y_1959_, v___y_1960_, v___y_1961_);
if (lean_obj_tag(v___x_2003_) == 0)
{
lean_object* v___x_2005_; uint8_t v_isShared_2006_; uint8_t v_isSharedCheck_2019_; 
v_isSharedCheck_2019_ = !lean_is_exclusive(v___x_2003_);
if (v_isSharedCheck_2019_ == 0)
{
lean_object* v_unused_2020_; 
v_unused_2020_ = lean_ctor_get(v___x_2003_, 0);
lean_dec(v_unused_2020_);
v___x_2005_ = v___x_2003_;
v_isShared_2006_ = v_isSharedCheck_2019_;
goto v_resetjp_2004_;
}
else
{
lean_dec(v___x_2003_);
v___x_2005_ = lean_box(0);
v_isShared_2006_ = v_isSharedCheck_2019_;
goto v_resetjp_2004_;
}
v_resetjp_2004_:
{
lean_object* v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2010_; 
v___x_2007_ = lean_obj_once(&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__10, &l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__10_once, _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__10);
lean_inc(v_snd_1944_);
v___x_2008_ = l_Nat_reprFast(v_snd_1944_);
if (v_isShared_2006_ == 0)
{
lean_ctor_set_tag(v___x_2005_, 3);
lean_ctor_set(v___x_2005_, 0, v___x_2008_);
v___x_2010_ = v___x_2005_;
goto v_reusejp_2009_;
}
else
{
lean_object* v_reuseFailAlloc_2018_; 
v_reuseFailAlloc_2018_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2018_, 0, v___x_2008_);
v___x_2010_ = v_reuseFailAlloc_2018_;
goto v_reusejp_2009_;
}
v_reusejp_2009_:
{
lean_object* v___x_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; 
v___x_2011_ = l_Lean_MessageData_ofFormat(v___x_2010_);
v___x_2012_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2012_, 0, v___x_2007_);
lean_ctor_set(v___x_2012_, 1, v___x_2011_);
v___x_2013_ = lean_obj_once(&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__12, &l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__12_once, _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__12);
v___x_2014_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2014_, 0, v___x_2012_);
lean_ctor_set(v___x_2014_, 1, v___x_2013_);
lean_inc_ref(v___y_1995_);
v___x_2015_ = l_Lean_MessageData_ofExpr(v___y_1995_);
v___x_2016_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2016_, 0, v___x_2014_);
lean_ctor_set(v___x_2016_, 1, v___x_2015_);
v___x_2017_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg(v___x_2000_, v___x_2016_, v___y_1958_, v___y_1959_, v___y_1960_, v___y_1961_);
if (lean_obj_tag(v___x_2017_) == 0)
{
lean_dec_ref_known(v___x_2017_, 1);
v___y_1970_ = v___y_1995_;
v___y_1971_ = v___y_1952_;
v___y_1972_ = v___y_1953_;
v___y_1973_ = v___y_1954_;
v___y_1974_ = v___y_1955_;
v___y_1975_ = v___y_1956_;
v___y_1976_ = v___y_1957_;
v___y_1977_ = v___y_1958_;
v___y_1978_ = v___y_1959_;
v___y_1979_ = v___y_1960_;
v___y_1980_ = v___y_1961_;
goto v___jp_1969_;
}
else
{
lean_dec_ref(v___y_1995_);
lean_dec(v_i_1950_);
lean_dec_ref(v_fst_1946_);
lean_dec_ref(v_fst_1945_);
lean_dec(v_snd_1944_);
lean_dec_ref(v_a_1943_);
return v___x_2017_;
}
}
}
}
else
{
lean_dec_ref(v___y_1995_);
lean_dec(v_i_1950_);
lean_dec_ref(v_fst_1946_);
lean_dec_ref(v_fst_1945_);
lean_dec(v_snd_1944_);
lean_dec_ref(v_a_1943_);
return v___x_2003_;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1943_ = stack[0].m_obj;
lean_object* v_snd_1944_ = stack[1].m_obj;
lean_object* v_fst_1945_ = stack[2].m_obj;
lean_object* v_fst_1946_ = stack[3].m_obj;
lean_object* v___x_1947_ = stack[4].m_obj;
lean_object* v_range_1948_ = stack[5].m_obj;
lean_object* v_b_1949_ = stack[6].m_obj;
lean_object* v_i_1950_ = stack[7].m_obj;
lean_object* v___y_1951_ = stack[8].m_obj;
lean_object* v___y_1952_ = stack[9].m_obj;
lean_object* v___y_1953_ = stack[10].m_obj;
lean_object* v___y_1954_ = stack[11].m_obj;
lean_object* v___y_1955_ = stack[12].m_obj;
lean_object* v___y_1956_ = stack[13].m_obj;
lean_object* v___y_1957_ = stack[14].m_obj;
lean_object* v___y_1958_ = stack[15].m_obj;
lean_object* v___y_1959_ = stack[16].m_obj;
lean_object* v___y_1960_ = stack[17].m_obj;
lean_object* v___y_1961_ = stack[18].m_obj;
lean_object* v_res_2025_;
v_res_2025_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg(v_a_1943_, v_snd_1944_, v_fst_1945_, v_fst_1946_, v___x_1947_, v_range_1948_, v_b_1949_, v_i_1950_, v___y_1951_, v___y_1952_, v___y_1953_, v___y_1954_, v___y_1955_, v___y_1956_, v___y_1957_, v___y_1958_, v___y_1959_, v___y_1960_, v___y_1961_);
stack->m_obj
 = v_res_2025_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___boxed(lean_object** _args){
lean_object* v_a_2026_ = _args[0];
lean_object* v_snd_2027_ = _args[1];
lean_object* v_fst_2028_ = _args[2];
lean_object* v_fst_2029_ = _args[3];
lean_object* v___x_2030_ = _args[4];
lean_object* v_range_2031_ = _args[5];
lean_object* v_b_2032_ = _args[6];
lean_object* v_i_2033_ = _args[7];
lean_object* v___y_2034_ = _args[8];
lean_object* v___y_2035_ = _args[9];
lean_object* v___y_2036_ = _args[10];
lean_object* v___y_2037_ = _args[11];
lean_object* v___y_2038_ = _args[12];
lean_object* v___y_2039_ = _args[13];
lean_object* v___y_2040_ = _args[14];
lean_object* v___y_2041_ = _args[15];
lean_object* v___y_2042_ = _args[16];
lean_object* v___y_2043_ = _args[17];
lean_object* v___y_2044_ = _args[18];
lean_object* v___y_2045_ = _args[19];
_start:
{
lean_object* v_res_2046_; 
v_res_2046_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg(v_a_2026_, v_snd_2027_, v_fst_2028_, v_fst_2029_, v___x_2030_, v_range_2031_, v_b_2032_, v_i_2033_, v___y_2034_, v___y_2035_, v___y_2036_, v___y_2037_, v___y_2038_, v___y_2039_, v___y_2040_, v___y_2041_, v___y_2042_, v___y_2043_, v___y_2044_);
lean_dec(v___y_2044_);
lean_dec_ref(v___y_2043_);
lean_dec(v___y_2042_);
lean_dec_ref(v___y_2041_);
lean_dec(v___y_2040_);
lean_dec_ref(v___y_2039_);
lean_dec(v___y_2038_);
lean_dec_ref(v___y_2037_);
lean_dec(v___y_2036_);
lean_dec(v___y_2035_);
lean_dec_ref(v___y_2034_);
lean_dec_ref(v_range_2031_);
lean_dec_ref(v___x_2030_);
return v_res_2046_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars(lean_object* v_a_2047_, lean_object* v_a_2048_, lean_object* v_a_2049_, lean_object* v_a_2050_, lean_object* v_a_2051_, lean_object* v_a_2052_, lean_object* v_a_2053_, lean_object* v_a_2054_, lean_object* v_a_2055_, lean_object* v_a_2056_, lean_object* v_a_2057_){
_start:
{
lean_object* v___x_2059_; 
v___x_2059_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v_a_2047_, v_a_2048_, v_a_2049_, v_a_2050_, v_a_2051_, v_a_2052_, v_a_2053_, v_a_2054_, v_a_2055_, v_a_2056_, v_a_2057_);
if (lean_obj_tag(v___x_2059_) == 0)
{
lean_object* v_a_2060_; lean_object* v___x_2062_; uint8_t v_isShared_2063_; uint8_t v_isSharedCheck_2121_; 
v_a_2060_ = lean_ctor_get(v___x_2059_, 0);
v_isSharedCheck_2121_ = !lean_is_exclusive(v___x_2059_);
if (v_isSharedCheck_2121_ == 0)
{
v___x_2062_ = v___x_2059_;
v_isShared_2063_ = v_isSharedCheck_2121_;
goto v_resetjp_2061_;
}
else
{
lean_inc(v_a_2060_);
lean_dec(v___x_2059_);
v___x_2062_ = lean_box(0);
v_isShared_2063_ = v_isSharedCheck_2121_;
goto v_resetjp_2061_;
}
v_resetjp_2061_:
{
lean_object* v_powIdentityInst_x3f_2064_; 
v_powIdentityInst_x3f_2064_ = lean_ctor_get(v_a_2060_, 8);
if (lean_obj_tag(v_powIdentityInst_x3f_2064_) == 1)
{
lean_object* v_val_2065_; lean_object* v_snd_2066_; lean_object* v_fst_2067_; lean_object* v_fst_2068_; lean_object* v_snd_2069_; lean_object* v___x_2070_; 
lean_del_object(v___x_2062_);
v_val_2065_ = lean_ctor_get(v_powIdentityInst_x3f_2064_, 0);
v_snd_2066_ = lean_ctor_get(v_val_2065_, 1);
v_fst_2067_ = lean_ctor_get(v_val_2065_, 0);
lean_inc(v_fst_2067_);
v_fst_2068_ = lean_ctor_get(v_snd_2066_, 0);
lean_inc(v_fst_2068_);
v_snd_2069_ = lean_ctor_get(v_snd_2066_, 1);
lean_inc(v_snd_2069_);
v___x_2070_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRingState___redArg(v_a_2047_, v_a_2048_, v_a_2056_);
if (lean_obj_tag(v___x_2070_) == 0)
{
lean_object* v_a_2071_; lean_object* v_powIdentityVarCount_2072_; lean_object* v___x_2073_; 
v_a_2071_ = lean_ctor_get(v___x_2070_, 0);
lean_inc(v_a_2071_);
lean_dec_ref_known(v___x_2070_, 1);
v_powIdentityVarCount_2072_ = lean_ctor_get(v_a_2071_, 8);
lean_inc(v_powIdentityVarCount_2072_);
lean_dec(v_a_2071_);
v___x_2073_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRingState___redArg(v_a_2047_, v_a_2048_, v_a_2056_);
if (lean_obj_tag(v___x_2073_) == 0)
{
lean_object* v_a_2074_; lean_object* v___x_2076_; uint8_t v_isShared_2077_; uint8_t v_isSharedCheck_2100_; 
v_a_2074_ = lean_ctor_get(v___x_2073_, 0);
v_isSharedCheck_2100_ = !lean_is_exclusive(v___x_2073_);
if (v_isSharedCheck_2100_ == 0)
{
v___x_2076_ = v___x_2073_;
v_isShared_2077_ = v_isSharedCheck_2100_;
goto v_resetjp_2075_;
}
else
{
lean_inc(v_a_2074_);
lean_dec(v___x_2073_);
v___x_2076_ = lean_box(0);
v_isShared_2077_ = v_isSharedCheck_2100_;
goto v_resetjp_2075_;
}
v_resetjp_2075_:
{
lean_object* v_toRingState_2078_; lean_object* v_vars_2079_; lean_object* v___x_2081_; uint8_t v_isShared_2082_; uint8_t v_isSharedCheck_2097_; 
v_toRingState_2078_ = lean_ctor_get(v_a_2074_, 0);
lean_inc_ref(v_toRingState_2078_);
lean_dec(v_a_2074_);
v_vars_2079_ = lean_ctor_get(v_toRingState_2078_, 0);
v_isSharedCheck_2097_ = !lean_is_exclusive(v_toRingState_2078_);
if (v_isSharedCheck_2097_ == 0)
{
lean_object* v_unused_2098_; lean_object* v_unused_2099_; 
v_unused_2098_ = lean_ctor_get(v_toRingState_2078_, 2);
lean_dec(v_unused_2098_);
v_unused_2099_ = lean_ctor_get(v_toRingState_2078_, 1);
lean_dec(v_unused_2099_);
v___x_2081_ = v_toRingState_2078_;
v_isShared_2082_ = v_isSharedCheck_2097_;
goto v_resetjp_2080_;
}
else
{
lean_inc(v_vars_2079_);
lean_dec(v_toRingState_2078_);
v___x_2081_ = lean_box(0);
v_isShared_2082_ = v_isSharedCheck_2097_;
goto v_resetjp_2080_;
}
v_resetjp_2080_:
{
lean_object* v_size_2083_; uint8_t v___x_2084_; 
v_size_2083_ = lean_ctor_get(v_vars_2079_, 2);
v___x_2084_ = lean_nat_dec_le(v_size_2083_, v_powIdentityVarCount_2072_);
if (v___x_2084_ == 0)
{
lean_object* v___f_2085_; lean_object* v___x_2086_; lean_object* v___x_2088_; 
lean_del_object(v___x_2076_);
lean_inc_n(v_size_2083_, 2);
v___f_2085_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars___lam__0), 2, 1);
lean_closure_set(v___f_2085_, 0, v_size_2083_);
v___x_2086_ = lean_unsigned_to_nat(1u);
lean_inc(v_powIdentityVarCount_2072_);
if (v_isShared_2082_ == 0)
{
lean_ctor_set(v___x_2081_, 2, v___x_2086_);
lean_ctor_set(v___x_2081_, 1, v_size_2083_);
lean_ctor_set(v___x_2081_, 0, v_powIdentityVarCount_2072_);
v___x_2088_ = v___x_2081_;
goto v_reusejp_2087_;
}
else
{
lean_object* v_reuseFailAlloc_2092_; 
v_reuseFailAlloc_2092_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2092_, 0, v_powIdentityVarCount_2072_);
lean_ctor_set(v_reuseFailAlloc_2092_, 1, v_size_2083_);
lean_ctor_set(v_reuseFailAlloc_2092_, 2, v___x_2086_);
v___x_2088_ = v_reuseFailAlloc_2092_;
goto v_reusejp_2087_;
}
v_reusejp_2087_:
{
lean_object* v___x_2089_; lean_object* v___x_2090_; 
v___x_2089_ = lean_box(0);
v___x_2090_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg(v_a_2060_, v_snd_2069_, v_fst_2068_, v_fst_2067_, v_vars_2079_, v___x_2088_, v___x_2089_, v_powIdentityVarCount_2072_, v_a_2047_, v_a_2048_, v_a_2049_, v_a_2050_, v_a_2051_, v_a_2052_, v_a_2053_, v_a_2054_, v_a_2055_, v_a_2056_, v_a_2057_);
lean_dec_ref(v___x_2088_);
lean_dec_ref(v_vars_2079_);
if (lean_obj_tag(v___x_2090_) == 0)
{
lean_object* v___x_2091_; 
lean_dec_ref_known(v___x_2090_, 1);
v___x_2091_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRingState___redArg(v___f_2085_, v_a_2047_, v_a_2048_);
return v___x_2091_;
}
else
{
lean_dec_ref(v___f_2085_);
return v___x_2090_;
}
}
}
else
{
lean_object* v___x_2093_; lean_object* v___x_2095_; 
lean_del_object(v___x_2081_);
lean_dec_ref(v_vars_2079_);
lean_dec(v_powIdentityVarCount_2072_);
lean_dec(v_snd_2069_);
lean_dec(v_fst_2068_);
lean_dec(v_fst_2067_);
lean_dec(v_a_2060_);
v___x_2093_ = lean_box(0);
if (v_isShared_2077_ == 0)
{
lean_ctor_set(v___x_2076_, 0, v___x_2093_);
v___x_2095_ = v___x_2076_;
goto v_reusejp_2094_;
}
else
{
lean_object* v_reuseFailAlloc_2096_; 
v_reuseFailAlloc_2096_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2096_, 0, v___x_2093_);
v___x_2095_ = v_reuseFailAlloc_2096_;
goto v_reusejp_2094_;
}
v_reusejp_2094_:
{
return v___x_2095_;
}
}
}
}
}
else
{
lean_object* v_a_2101_; lean_object* v___x_2103_; uint8_t v_isShared_2104_; uint8_t v_isSharedCheck_2108_; 
lean_dec(v_powIdentityVarCount_2072_);
lean_dec(v_snd_2069_);
lean_dec(v_fst_2068_);
lean_dec(v_fst_2067_);
lean_dec(v_a_2060_);
v_a_2101_ = lean_ctor_get(v___x_2073_, 0);
v_isSharedCheck_2108_ = !lean_is_exclusive(v___x_2073_);
if (v_isSharedCheck_2108_ == 0)
{
v___x_2103_ = v___x_2073_;
v_isShared_2104_ = v_isSharedCheck_2108_;
goto v_resetjp_2102_;
}
else
{
lean_inc(v_a_2101_);
lean_dec(v___x_2073_);
v___x_2103_ = lean_box(0);
v_isShared_2104_ = v_isSharedCheck_2108_;
goto v_resetjp_2102_;
}
v_resetjp_2102_:
{
lean_object* v___x_2106_; 
if (v_isShared_2104_ == 0)
{
v___x_2106_ = v___x_2103_;
goto v_reusejp_2105_;
}
else
{
lean_object* v_reuseFailAlloc_2107_; 
v_reuseFailAlloc_2107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2107_, 0, v_a_2101_);
v___x_2106_ = v_reuseFailAlloc_2107_;
goto v_reusejp_2105_;
}
v_reusejp_2105_:
{
return v___x_2106_;
}
}
}
}
else
{
lean_object* v_a_2109_; lean_object* v___x_2111_; uint8_t v_isShared_2112_; uint8_t v_isSharedCheck_2116_; 
lean_dec(v_snd_2069_);
lean_dec(v_fst_2068_);
lean_dec(v_fst_2067_);
lean_dec(v_a_2060_);
v_a_2109_ = lean_ctor_get(v___x_2070_, 0);
v_isSharedCheck_2116_ = !lean_is_exclusive(v___x_2070_);
if (v_isSharedCheck_2116_ == 0)
{
v___x_2111_ = v___x_2070_;
v_isShared_2112_ = v_isSharedCheck_2116_;
goto v_resetjp_2110_;
}
else
{
lean_inc(v_a_2109_);
lean_dec(v___x_2070_);
v___x_2111_ = lean_box(0);
v_isShared_2112_ = v_isSharedCheck_2116_;
goto v_resetjp_2110_;
}
v_resetjp_2110_:
{
lean_object* v___x_2114_; 
if (v_isShared_2112_ == 0)
{
v___x_2114_ = v___x_2111_;
goto v_reusejp_2113_;
}
else
{
lean_object* v_reuseFailAlloc_2115_; 
v_reuseFailAlloc_2115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2115_, 0, v_a_2109_);
v___x_2114_ = v_reuseFailAlloc_2115_;
goto v_reusejp_2113_;
}
v_reusejp_2113_:
{
return v___x_2114_;
}
}
}
}
else
{
lean_object* v___x_2117_; lean_object* v___x_2119_; 
lean_dec(v_a_2060_);
v___x_2117_ = lean_box(0);
if (v_isShared_2063_ == 0)
{
lean_ctor_set(v___x_2062_, 0, v___x_2117_);
v___x_2119_ = v___x_2062_;
goto v_reusejp_2118_;
}
else
{
lean_object* v_reuseFailAlloc_2120_; 
v_reuseFailAlloc_2120_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2120_, 0, v___x_2117_);
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
v_a_2122_ = lean_ctor_get(v___x_2059_, 0);
v_isSharedCheck_2129_ = !lean_is_exclusive(v___x_2059_);
if (v_isSharedCheck_2129_ == 0)
{
v___x_2124_ = v___x_2059_;
v_isShared_2125_ = v_isSharedCheck_2129_;
goto v_resetjp_2123_;
}
else
{
lean_inc(v_a_2122_);
lean_dec(v___x_2059_);
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
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2047_ = stack[0].m_obj;
lean_object* v_a_2048_ = stack[1].m_obj;
lean_object* v_a_2049_ = stack[2].m_obj;
lean_object* v_a_2050_ = stack[3].m_obj;
lean_object* v_a_2051_ = stack[4].m_obj;
lean_object* v_a_2052_ = stack[5].m_obj;
lean_object* v_a_2053_ = stack[6].m_obj;
lean_object* v_a_2054_ = stack[7].m_obj;
lean_object* v_a_2055_ = stack[8].m_obj;
lean_object* v_a_2056_ = stack[9].m_obj;
lean_object* v_a_2057_ = stack[10].m_obj;
lean_object* v_res_2130_;
v_res_2130_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars(v_a_2047_, v_a_2048_, v_a_2049_, v_a_2050_, v_a_2051_, v_a_2052_, v_a_2053_, v_a_2054_, v_a_2055_, v_a_2056_, v_a_2057_);
stack->m_obj
 = v_res_2130_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars___boxed(lean_object* v_a_2131_, lean_object* v_a_2132_, lean_object* v_a_2133_, lean_object* v_a_2134_, lean_object* v_a_2135_, lean_object* v_a_2136_, lean_object* v_a_2137_, lean_object* v_a_2138_, lean_object* v_a_2139_, lean_object* v_a_2140_, lean_object* v_a_2141_, lean_object* v_a_2142_){
_start:
{
lean_object* v_res_2143_; 
v_res_2143_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars(v_a_2131_, v_a_2132_, v_a_2133_, v_a_2134_, v_a_2135_, v_a_2136_, v_a_2137_, v_a_2138_, v_a_2139_, v_a_2140_, v_a_2141_);
lean_dec(v_a_2141_);
lean_dec_ref(v_a_2140_);
lean_dec(v_a_2139_);
lean_dec_ref(v_a_2138_);
lean_dec(v_a_2137_);
lean_dec_ref(v_a_2136_);
lean_dec(v_a_2135_);
lean_dec_ref(v_a_2134_);
lean_dec(v_a_2133_);
lean_dec(v_a_2132_);
lean_dec_ref(v_a_2131_);
return v_res_2143_;
}
}
lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0(lean_object* v_cls_2144_, lean_object* v_msg_2145_, lean_object* v___y_2146_, lean_object* v___y_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_, lean_object* v___y_2153_, lean_object* v___y_2154_, lean_object* v___y_2155_, lean_object* v___y_2156_){
_start:
{
lean_object* v___x_2158_; 
v___x_2158_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg(v_cls_2144_, v_msg_2145_, v___y_2153_, v___y_2154_, v___y_2155_, v___y_2156_);
return v___x_2158_;
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_2144_ = stack[0].m_obj;
lean_object* v_msg_2145_ = stack[1].m_obj;
lean_object* v___y_2146_ = stack[2].m_obj;
lean_object* v___y_2147_ = stack[3].m_obj;
lean_object* v___y_2148_ = stack[4].m_obj;
lean_object* v___y_2149_ = stack[5].m_obj;
lean_object* v___y_2150_ = stack[6].m_obj;
lean_object* v___y_2151_ = stack[7].m_obj;
lean_object* v___y_2152_ = stack[8].m_obj;
lean_object* v___y_2153_ = stack[9].m_obj;
lean_object* v___y_2154_ = stack[10].m_obj;
lean_object* v___y_2155_ = stack[11].m_obj;
lean_object* v___y_2156_ = stack[12].m_obj;
lean_object* v_res_2159_;
v_res_2159_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0(v_cls_2144_, v_msg_2145_, v___y_2146_, v___y_2147_, v___y_2148_, v___y_2149_, v___y_2150_, v___y_2151_, v___y_2152_, v___y_2153_, v___y_2154_, v___y_2155_, v___y_2156_);
stack->m_obj
 = v_res_2159_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___boxed(lean_object* v_cls_2160_, lean_object* v_msg_2161_, lean_object* v___y_2162_, lean_object* v___y_2163_, lean_object* v___y_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_, lean_object* v___y_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_, lean_object* v___y_2171_, lean_object* v___y_2172_, lean_object* v___y_2173_){
_start:
{
lean_object* v_res_2174_; 
v_res_2174_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0(v_cls_2160_, v_msg_2161_, v___y_2162_, v___y_2163_, v___y_2164_, v___y_2165_, v___y_2166_, v___y_2167_, v___y_2168_, v___y_2169_, v___y_2170_, v___y_2171_, v___y_2172_);
lean_dec(v___y_2172_);
lean_dec_ref(v___y_2171_);
lean_dec(v___y_2170_);
lean_dec_ref(v___y_2169_);
lean_dec(v___y_2168_);
lean_dec_ref(v___y_2167_);
lean_dec(v___y_2166_);
lean_dec_ref(v___y_2165_);
lean_dec(v___y_2164_);
lean_dec(v___y_2163_);
lean_dec_ref(v___y_2162_);
return v_res_2174_;
}
}
lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1(lean_object* v_a_2175_, lean_object* v_snd_2176_, lean_object* v_fst_2177_, lean_object* v_fst_2178_, lean_object* v___x_2179_, lean_object* v_range_2180_, lean_object* v_b_2181_, lean_object* v_i_2182_, lean_object* v_hs_2183_, lean_object* v_hl_2184_, lean_object* v___y_2185_, lean_object* v___y_2186_, lean_object* v___y_2187_, lean_object* v___y_2188_, lean_object* v___y_2189_, lean_object* v___y_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_, lean_object* v___y_2194_, lean_object* v___y_2195_){
_start:
{
lean_object* v___x_2197_; 
v___x_2197_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg(v_a_2175_, v_snd_2176_, v_fst_2177_, v_fst_2178_, v___x_2179_, v_range_2180_, v_b_2181_, v_i_2182_, v___y_2185_, v___y_2186_, v___y_2187_, v___y_2188_, v___y_2189_, v___y_2190_, v___y_2191_, v___y_2192_, v___y_2193_, v___y_2194_, v___y_2195_);
return v___x_2197_;
}
}
LEAN_EXPORT void l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2175_ = stack[0].m_obj;
lean_object* v_snd_2176_ = stack[1].m_obj;
lean_object* v_fst_2177_ = stack[2].m_obj;
lean_object* v_fst_2178_ = stack[3].m_obj;
lean_object* v___x_2179_ = stack[4].m_obj;
lean_object* v_range_2180_ = stack[5].m_obj;
lean_object* v_b_2181_ = stack[6].m_obj;
lean_object* v_i_2182_ = stack[7].m_obj;
lean_object* v___y_2185_ = stack[10].m_obj;
lean_object* v___y_2186_ = stack[11].m_obj;
lean_object* v___y_2187_ = stack[12].m_obj;
lean_object* v___y_2188_ = stack[13].m_obj;
lean_object* v___y_2189_ = stack[14].m_obj;
lean_object* v___y_2190_ = stack[15].m_obj;
lean_object* v___y_2191_ = stack[16].m_obj;
lean_object* v___y_2192_ = stack[17].m_obj;
lean_object* v___y_2193_ = stack[18].m_obj;
lean_object* v___y_2194_ = stack[19].m_obj;
lean_object* v___y_2195_ = stack[20].m_obj;
lean_object* v_res_2198_;
v_res_2198_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1(v_a_2175_, v_snd_2176_, v_fst_2177_, v_fst_2178_, v___x_2179_, v_range_2180_, v_b_2181_, v_i_2182_, lean_box(0), lean_box(0), v___y_2185_, v___y_2186_, v___y_2187_, v___y_2188_, v___y_2189_, v___y_2190_, v___y_2191_, v___y_2192_, v___y_2193_, v___y_2194_, v___y_2195_);
stack->m_obj
 = v_res_2198_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___boxed(lean_object** _args){
lean_object* v_a_2199_ = _args[0];
lean_object* v_snd_2200_ = _args[1];
lean_object* v_fst_2201_ = _args[2];
lean_object* v_fst_2202_ = _args[3];
lean_object* v___x_2203_ = _args[4];
lean_object* v_range_2204_ = _args[5];
lean_object* v_b_2205_ = _args[6];
lean_object* v_i_2206_ = _args[7];
lean_object* v_hs_2207_ = _args[8];
lean_object* v_hl_2208_ = _args[9];
lean_object* v___y_2209_ = _args[10];
lean_object* v___y_2210_ = _args[11];
lean_object* v___y_2211_ = _args[12];
lean_object* v___y_2212_ = _args[13];
lean_object* v___y_2213_ = _args[14];
lean_object* v___y_2214_ = _args[15];
lean_object* v___y_2215_ = _args[16];
lean_object* v___y_2216_ = _args[17];
lean_object* v___y_2217_ = _args[18];
lean_object* v___y_2218_ = _args[19];
lean_object* v___y_2219_ = _args[20];
lean_object* v___y_2220_ = _args[21];
_start:
{
lean_object* v_res_2221_; 
v_res_2221_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1(v_a_2199_, v_snd_2200_, v_fst_2201_, v_fst_2202_, v___x_2203_, v_range_2204_, v_b_2205_, v_i_2206_, v_hs_2207_, v_hl_2208_, v___y_2209_, v___y_2210_, v___y_2211_, v___y_2212_, v___y_2213_, v___y_2214_, v___y_2215_, v___y_2216_, v___y_2217_, v___y_2218_, v___y_2219_);
lean_dec(v___y_2219_);
lean_dec_ref(v___y_2218_);
lean_dec(v___y_2217_);
lean_dec_ref(v___y_2216_);
lean_dec(v___y_2215_);
lean_dec_ref(v___y_2214_);
lean_dec(v___y_2213_);
lean_dec_ref(v___y_2212_);
lean_dec(v___y_2211_);
lean_dec(v___y_2210_);
lean_dec_ref(v___y_2209_);
lean_dec_ref(v_range_2204_);
lean_dec_ref(v___x_2203_);
return v_res_2221_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeInv(lean_object* v_e_2222_, lean_object* v_a_2223_, lean_object* v_a_2224_, lean_object* v_a_2225_, lean_object* v_a_2226_, lean_object* v_a_2227_, lean_object* v_a_2228_, lean_object* v_a_2229_, lean_object* v_a_2230_, lean_object* v_a_2231_, lean_object* v_a_2232_){
_start:
{
lean_object* v___x_2238_; 
lean_inc_ref(v_e_2222_);
v___x_2238_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_2222_, v_a_2230_);
if (lean_obj_tag(v___x_2238_) == 0)
{
lean_object* v_a_2239_; lean_object* v___x_2240_; uint8_t v___x_2241_; 
v_a_2239_ = lean_ctor_get(v___x_2238_, 0);
lean_inc(v_a_2239_);
lean_dec_ref_known(v___x_2238_, 1);
v___x_2240_ = l_Lean_Expr_cleanupAnnotations(v_a_2239_);
v___x_2241_ = l_Lean_Expr_isApp(v___x_2240_);
if (v___x_2241_ == 0)
{
lean_dec_ref(v___x_2240_);
lean_dec_ref(v_e_2222_);
goto v___jp_2234_;
}
else
{
lean_object* v_arg_2242_; lean_object* v___x_2243_; uint8_t v___x_2244_; 
v_arg_2242_ = lean_ctor_get(v___x_2240_, 1);
lean_inc_ref(v_arg_2242_);
v___x_2243_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2240_);
v___x_2244_ = l_Lean_Expr_isApp(v___x_2243_);
if (v___x_2244_ == 0)
{
lean_dec_ref(v___x_2243_);
lean_dec_ref(v_arg_2242_);
lean_dec_ref(v_e_2222_);
goto v___jp_2234_;
}
else
{
lean_object* v_arg_2245_; lean_object* v___x_2246_; uint8_t v___x_2247_; 
v_arg_2245_ = lean_ctor_get(v___x_2243_, 1);
lean_inc_ref(v_arg_2245_);
v___x_2246_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2243_);
v___x_2247_ = l_Lean_Expr_isApp(v___x_2246_);
if (v___x_2247_ == 0)
{
lean_dec_ref(v___x_2246_);
lean_dec_ref(v_arg_2245_);
lean_dec_ref(v_arg_2242_);
lean_dec_ref(v_e_2222_);
goto v___jp_2234_;
}
else
{
lean_object* v_arg_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; uint8_t v___x_2251_; 
v_arg_2248_ = lean_ctor_get(v___x_2246_, 1);
lean_inc_ref(v_arg_2248_);
v___x_2249_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2246_);
v___x_2250_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___closed__6));
v___x_2251_ = l_Lean_Expr_isConstOf(v___x_2249_, v___x_2250_);
lean_dec_ref(v___x_2249_);
if (v___x_2251_ == 0)
{
lean_dec_ref(v_arg_2248_);
lean_dec_ref(v_arg_2245_);
lean_dec_ref(v_arg_2242_);
lean_dec_ref(v_e_2222_);
goto v___jp_2234_;
}
else
{
lean_object* v___x_2252_; 
v___x_2252_ = l_Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f___redArg(v_arg_2248_, v_a_2227_, v_a_2228_, v_a_2229_, v_a_2230_, v_a_2231_, v_a_2232_);
if (lean_obj_tag(v___x_2252_) == 0)
{
lean_object* v_a_2253_; lean_object* v___x_2255_; uint8_t v_isShared_2256_; uint8_t v_isSharedCheck_2282_; 
v_a_2253_ = lean_ctor_get(v___x_2252_, 0);
v_isSharedCheck_2282_ = !lean_is_exclusive(v___x_2252_);
if (v_isSharedCheck_2282_ == 0)
{
v___x_2255_ = v___x_2252_;
v_isShared_2256_ = v_isSharedCheck_2282_;
goto v_resetjp_2254_;
}
else
{
lean_inc(v_a_2253_);
lean_dec(v___x_2252_);
v___x_2255_ = lean_box(0);
v_isShared_2256_ = v_isSharedCheck_2282_;
goto v_resetjp_2254_;
}
v_resetjp_2254_:
{
if (lean_obj_tag(v_a_2253_) == 1)
{
lean_object* v_val_2257_; uint8_t v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; 
lean_del_object(v___x_2255_);
v_val_2257_ = lean_ctor_get(v_a_2253_, 0);
lean_inc(v_val_2257_);
lean_dec_ref_known(v_a_2253_, 1);
v___x_2258_ = 0;
v___x_2259_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2259_, 0, v_val_2257_);
lean_ctor_set_uint8(v___x_2259_, sizeof(void*)*1, v___x_2258_);
v___x_2260_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv(v_e_2222_, v_arg_2245_, v_arg_2242_, v___x_2259_, v_a_2223_, v_a_2224_, v_a_2225_, v_a_2226_, v_a_2227_, v_a_2228_, v_a_2229_, v_a_2230_, v_a_2231_, v_a_2232_);
lean_dec_ref_known(v___x_2259_, 1);
lean_dec_ref(v_arg_2245_);
if (lean_obj_tag(v___x_2260_) == 0)
{
lean_object* v___x_2262_; uint8_t v_isShared_2263_; uint8_t v_isSharedCheck_2268_; 
v_isSharedCheck_2268_ = !lean_is_exclusive(v___x_2260_);
if (v_isSharedCheck_2268_ == 0)
{
lean_object* v_unused_2269_; 
v_unused_2269_ = lean_ctor_get(v___x_2260_, 0);
lean_dec(v_unused_2269_);
v___x_2262_ = v___x_2260_;
v_isShared_2263_ = v_isSharedCheck_2268_;
goto v_resetjp_2261_;
}
else
{
lean_dec(v___x_2260_);
v___x_2262_ = lean_box(0);
v_isShared_2263_ = v_isSharedCheck_2268_;
goto v_resetjp_2261_;
}
v_resetjp_2261_:
{
lean_object* v___x_2264_; lean_object* v___x_2266_; 
v___x_2264_ = lean_box(v___x_2251_);
if (v_isShared_2263_ == 0)
{
lean_ctor_set(v___x_2262_, 0, v___x_2264_);
v___x_2266_ = v___x_2262_;
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
else
{
lean_object* v_a_2270_; lean_object* v___x_2272_; uint8_t v_isShared_2273_; uint8_t v_isSharedCheck_2277_; 
v_a_2270_ = lean_ctor_get(v___x_2260_, 0);
v_isSharedCheck_2277_ = !lean_is_exclusive(v___x_2260_);
if (v_isSharedCheck_2277_ == 0)
{
v___x_2272_ = v___x_2260_;
v_isShared_2273_ = v_isSharedCheck_2277_;
goto v_resetjp_2271_;
}
else
{
lean_inc(v_a_2270_);
lean_dec(v___x_2260_);
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
}
else
{
lean_object* v___x_2278_; lean_object* v___x_2280_; 
lean_dec(v_a_2253_);
lean_dec_ref(v_arg_2245_);
lean_dec_ref(v_arg_2242_);
lean_dec_ref(v_e_2222_);
v___x_2278_ = lean_box(v___x_2251_);
if (v_isShared_2256_ == 0)
{
lean_ctor_set(v___x_2255_, 0, v___x_2278_);
v___x_2280_ = v___x_2255_;
goto v_reusejp_2279_;
}
else
{
lean_object* v_reuseFailAlloc_2281_; 
v_reuseFailAlloc_2281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2281_, 0, v___x_2278_);
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
else
{
lean_object* v_a_2283_; lean_object* v___x_2285_; uint8_t v_isShared_2286_; uint8_t v_isSharedCheck_2290_; 
lean_dec_ref(v_arg_2245_);
lean_dec_ref(v_arg_2242_);
lean_dec_ref(v_e_2222_);
v_a_2283_ = lean_ctor_get(v___x_2252_, 0);
v_isSharedCheck_2290_ = !lean_is_exclusive(v___x_2252_);
if (v_isSharedCheck_2290_ == 0)
{
v___x_2285_ = v___x_2252_;
v_isShared_2286_ = v_isSharedCheck_2290_;
goto v_resetjp_2284_;
}
else
{
lean_inc(v_a_2283_);
lean_dec(v___x_2252_);
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
}
}
}
}
}
else
{
lean_object* v_a_2291_; lean_object* v___x_2293_; uint8_t v_isShared_2294_; uint8_t v_isSharedCheck_2298_; 
lean_dec_ref(v_e_2222_);
v_a_2291_ = lean_ctor_get(v___x_2238_, 0);
v_isSharedCheck_2298_ = !lean_is_exclusive(v___x_2238_);
if (v_isSharedCheck_2298_ == 0)
{
v___x_2293_ = v___x_2238_;
v_isShared_2294_ = v_isSharedCheck_2298_;
goto v_resetjp_2292_;
}
else
{
lean_inc(v_a_2291_);
lean_dec(v___x_2238_);
v___x_2293_ = lean_box(0);
v_isShared_2294_ = v_isSharedCheck_2298_;
goto v_resetjp_2292_;
}
v_resetjp_2292_:
{
lean_object* v___x_2296_; 
if (v_isShared_2294_ == 0)
{
v___x_2296_ = v___x_2293_;
goto v_reusejp_2295_;
}
else
{
lean_object* v_reuseFailAlloc_2297_; 
v_reuseFailAlloc_2297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2297_, 0, v_a_2291_);
v___x_2296_ = v_reuseFailAlloc_2297_;
goto v_reusejp_2295_;
}
v_reusejp_2295_:
{
return v___x_2296_;
}
}
}
v___jp_2234_:
{
uint8_t v___x_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; 
v___x_2235_ = 0;
v___x_2236_ = lean_box(v___x_2235_);
v___x_2237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2237_, 0, v___x_2236_);
return v___x_2237_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeInv_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2222_ = stack[0].m_obj;
lean_object* v_a_2223_ = stack[1].m_obj;
lean_object* v_a_2224_ = stack[2].m_obj;
lean_object* v_a_2225_ = stack[3].m_obj;
lean_object* v_a_2226_ = stack[4].m_obj;
lean_object* v_a_2227_ = stack[5].m_obj;
lean_object* v_a_2228_ = stack[6].m_obj;
lean_object* v_a_2229_ = stack[7].m_obj;
lean_object* v_a_2230_ = stack[8].m_obj;
lean_object* v_a_2231_ = stack[9].m_obj;
lean_object* v_a_2232_ = stack[10].m_obj;
lean_object* v_res_2299_;
v_res_2299_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeInv(v_e_2222_, v_a_2223_, v_a_2224_, v_a_2225_, v_a_2226_, v_a_2227_, v_a_2228_, v_a_2229_, v_a_2230_, v_a_2231_, v_a_2232_);
stack->m_obj
 = v_res_2299_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeInv___boxed(lean_object* v_e_2300_, lean_object* v_a_2301_, lean_object* v_a_2302_, lean_object* v_a_2303_, lean_object* v_a_2304_, lean_object* v_a_2305_, lean_object* v_a_2306_, lean_object* v_a_2307_, lean_object* v_a_2308_, lean_object* v_a_2309_, lean_object* v_a_2310_, lean_object* v_a_2311_){
_start:
{
lean_object* v_res_2312_; 
v_res_2312_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeInv(v_e_2300_, v_a_2301_, v_a_2302_, v_a_2303_, v_a_2304_, v_a_2305_, v_a_2306_, v_a_2307_, v_a_2308_, v_a_2309_, v_a_2310_);
lean_dec(v_a_2310_);
lean_dec_ref(v_a_2309_);
lean_dec(v_a_2308_);
lean_dec_ref(v_a_2307_);
lean_dec(v_a_2306_);
lean_dec_ref(v_a_2305_);
lean_dec(v_a_2304_);
lean_dec_ref(v_a_2303_);
lean_dec(v_a_2302_);
lean_dec(v_a_2301_);
return v_res_2312_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0_spec__1_spec__5___redArg(lean_object* v_x_2313_, lean_object* v_x_2314_, lean_object* v_x_2315_, lean_object* v_x_2316_){
_start:
{
lean_object* v_ks_2317_; lean_object* v_vs_2318_; lean_object* v___x_2320_; uint8_t v_isShared_2321_; uint8_t v_isSharedCheck_2344_; 
v_ks_2317_ = lean_ctor_get(v_x_2313_, 0);
v_vs_2318_ = lean_ctor_get(v_x_2313_, 1);
v_isSharedCheck_2344_ = !lean_is_exclusive(v_x_2313_);
if (v_isSharedCheck_2344_ == 0)
{
v___x_2320_ = v_x_2313_;
v_isShared_2321_ = v_isSharedCheck_2344_;
goto v_resetjp_2319_;
}
else
{
lean_inc(v_vs_2318_);
lean_inc(v_ks_2317_);
lean_dec(v_x_2313_);
v___x_2320_ = lean_box(0);
v_isShared_2321_ = v_isSharedCheck_2344_;
goto v_resetjp_2319_;
}
v_resetjp_2319_:
{
lean_object* v___x_2322_; uint8_t v___x_2323_; 
v___x_2322_ = lean_array_get_size(v_ks_2317_);
v___x_2323_ = lean_nat_dec_lt(v_x_2314_, v___x_2322_);
if (v___x_2323_ == 0)
{
lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2327_; 
lean_dec(v_x_2314_);
v___x_2324_ = lean_array_push(v_ks_2317_, v_x_2315_);
v___x_2325_ = lean_array_push(v_vs_2318_, v_x_2316_);
if (v_isShared_2321_ == 0)
{
lean_ctor_set(v___x_2320_, 1, v___x_2325_);
lean_ctor_set(v___x_2320_, 0, v___x_2324_);
v___x_2327_ = v___x_2320_;
goto v_reusejp_2326_;
}
else
{
lean_object* v_reuseFailAlloc_2328_; 
v_reuseFailAlloc_2328_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2328_, 0, v___x_2324_);
lean_ctor_set(v_reuseFailAlloc_2328_, 1, v___x_2325_);
v___x_2327_ = v_reuseFailAlloc_2328_;
goto v_reusejp_2326_;
}
v_reusejp_2326_:
{
return v___x_2327_;
}
}
else
{
lean_object* v_k_x27_2329_; size_t v___x_2330_; size_t v___x_2331_; uint8_t v___x_2332_; 
v_k_x27_2329_ = lean_array_fget_borrowed(v_ks_2317_, v_x_2314_);
v___x_2330_ = lean_ptr_addr(v_x_2315_);
v___x_2331_ = lean_ptr_addr(v_k_x27_2329_);
v___x_2332_ = lean_usize_dec_eq(v___x_2330_, v___x_2331_);
if (v___x_2332_ == 0)
{
lean_object* v___x_2334_; 
if (v_isShared_2321_ == 0)
{
v___x_2334_ = v___x_2320_;
goto v_reusejp_2333_;
}
else
{
lean_object* v_reuseFailAlloc_2338_; 
v_reuseFailAlloc_2338_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2338_, 0, v_ks_2317_);
lean_ctor_set(v_reuseFailAlloc_2338_, 1, v_vs_2318_);
v___x_2334_ = v_reuseFailAlloc_2338_;
goto v_reusejp_2333_;
}
v_reusejp_2333_:
{
lean_object* v___x_2335_; lean_object* v___x_2336_; 
v___x_2335_ = lean_unsigned_to_nat(1u);
v___x_2336_ = lean_nat_add(v_x_2314_, v___x_2335_);
lean_dec(v_x_2314_);
v_x_2313_ = v___x_2334_;
v_x_2314_ = v___x_2336_;
goto _start;
}
}
else
{
lean_object* v___x_2339_; lean_object* v___x_2340_; lean_object* v___x_2342_; 
v___x_2339_ = lean_array_fset(v_ks_2317_, v_x_2314_, v_x_2315_);
v___x_2340_ = lean_array_fset(v_vs_2318_, v_x_2314_, v_x_2316_);
lean_dec(v_x_2314_);
if (v_isShared_2321_ == 0)
{
lean_ctor_set(v___x_2320_, 1, v___x_2340_);
lean_ctor_set(v___x_2320_, 0, v___x_2339_);
v___x_2342_ = v___x_2320_;
goto v_reusejp_2341_;
}
else
{
lean_object* v_reuseFailAlloc_2343_; 
v_reuseFailAlloc_2343_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2343_, 0, v___x_2339_);
lean_ctor_set(v_reuseFailAlloc_2343_, 1, v___x_2340_);
v___x_2342_ = v_reuseFailAlloc_2343_;
goto v_reusejp_2341_;
}
v_reusejp_2341_:
{
return v___x_2342_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0_spec__1___redArg(lean_object* v_n_2345_, lean_object* v_k_2346_, lean_object* v_v_2347_){
_start:
{
lean_object* v___x_2348_; lean_object* v___x_2349_; 
v___x_2348_ = lean_unsigned_to_nat(0u);
v___x_2349_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0_spec__1_spec__5___redArg(v_n_2345_, v___x_2348_, v_k_2346_, v_v_2347_);
return v___x_2349_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0___redArg(lean_object* v_x_2350_, size_t v_x_2351_, size_t v_x_2352_, lean_object* v_x_2353_, lean_object* v_x_2354_){
_start:
{
if (lean_obj_tag(v_x_2350_) == 0)
{
lean_object* v_es_2355_; size_t v___x_2356_; size_t v___x_2357_; lean_object* v_j_2358_; lean_object* v___x_2359_; uint8_t v___x_2360_; 
v_es_2355_ = lean_ctor_get(v_x_2350_, 0);
v___x_2356_ = ((size_t)31ULL);
v___x_2357_ = lean_usize_land(v_x_2351_, v___x_2356_);
v_j_2358_ = lean_usize_to_nat(v___x_2357_);
v___x_2359_ = lean_array_get_size(v_es_2355_);
v___x_2360_ = lean_nat_dec_lt(v_j_2358_, v___x_2359_);
if (v___x_2360_ == 0)
{
lean_dec(v_j_2358_);
lean_dec(v_x_2354_);
lean_dec_ref(v_x_2353_);
return v_x_2350_;
}
else
{
lean_object* v___x_2362_; uint8_t v_isShared_2363_; uint8_t v_isSharedCheck_2401_; 
lean_inc_ref(v_es_2355_);
v_isSharedCheck_2401_ = !lean_is_exclusive(v_x_2350_);
if (v_isSharedCheck_2401_ == 0)
{
lean_object* v_unused_2402_; 
v_unused_2402_ = lean_ctor_get(v_x_2350_, 0);
lean_dec(v_unused_2402_);
v___x_2362_ = v_x_2350_;
v_isShared_2363_ = v_isSharedCheck_2401_;
goto v_resetjp_2361_;
}
else
{
lean_dec(v_x_2350_);
v___x_2362_ = lean_box(0);
v_isShared_2363_ = v_isSharedCheck_2401_;
goto v_resetjp_2361_;
}
v_resetjp_2361_:
{
lean_object* v_v_2364_; lean_object* v___x_2365_; lean_object* v_xs_x27_2366_; lean_object* v___y_2368_; 
v_v_2364_ = lean_array_fget(v_es_2355_, v_j_2358_);
v___x_2365_ = lean_box(0);
v_xs_x27_2366_ = lean_array_fset(v_es_2355_, v_j_2358_, v___x_2365_);
switch(lean_obj_tag(v_v_2364_))
{
case 0:
{
lean_object* v_key_2373_; lean_object* v_val_2374_; lean_object* v___x_2376_; uint8_t v_isShared_2377_; uint8_t v_isSharedCheck_2386_; 
v_key_2373_ = lean_ctor_get(v_v_2364_, 0);
v_val_2374_ = lean_ctor_get(v_v_2364_, 1);
v_isSharedCheck_2386_ = !lean_is_exclusive(v_v_2364_);
if (v_isSharedCheck_2386_ == 0)
{
v___x_2376_ = v_v_2364_;
v_isShared_2377_ = v_isSharedCheck_2386_;
goto v_resetjp_2375_;
}
else
{
lean_inc(v_val_2374_);
lean_inc(v_key_2373_);
lean_dec(v_v_2364_);
v___x_2376_ = lean_box(0);
v_isShared_2377_ = v_isSharedCheck_2386_;
goto v_resetjp_2375_;
}
v_resetjp_2375_:
{
size_t v___x_2378_; size_t v___x_2379_; uint8_t v___x_2380_; 
v___x_2378_ = lean_ptr_addr(v_x_2353_);
v___x_2379_ = lean_ptr_addr(v_key_2373_);
v___x_2380_ = lean_usize_dec_eq(v___x_2378_, v___x_2379_);
if (v___x_2380_ == 0)
{
lean_object* v___x_2381_; lean_object* v___x_2382_; 
lean_del_object(v___x_2376_);
v___x_2381_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_2373_, v_val_2374_, v_x_2353_, v_x_2354_);
v___x_2382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2382_, 0, v___x_2381_);
v___y_2368_ = v___x_2382_;
goto v___jp_2367_;
}
else
{
lean_object* v___x_2384_; 
lean_dec(v_val_2374_);
lean_dec(v_key_2373_);
if (v_isShared_2377_ == 0)
{
lean_ctor_set(v___x_2376_, 1, v_x_2354_);
lean_ctor_set(v___x_2376_, 0, v_x_2353_);
v___x_2384_ = v___x_2376_;
goto v_reusejp_2383_;
}
else
{
lean_object* v_reuseFailAlloc_2385_; 
v_reuseFailAlloc_2385_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2385_, 0, v_x_2353_);
lean_ctor_set(v_reuseFailAlloc_2385_, 1, v_x_2354_);
v___x_2384_ = v_reuseFailAlloc_2385_;
goto v_reusejp_2383_;
}
v_reusejp_2383_:
{
v___y_2368_ = v___x_2384_;
goto v___jp_2367_;
}
}
}
}
case 1:
{
lean_object* v_node_2387_; lean_object* v___x_2389_; uint8_t v_isShared_2390_; uint8_t v_isSharedCheck_2399_; 
v_node_2387_ = lean_ctor_get(v_v_2364_, 0);
v_isSharedCheck_2399_ = !lean_is_exclusive(v_v_2364_);
if (v_isSharedCheck_2399_ == 0)
{
v___x_2389_ = v_v_2364_;
v_isShared_2390_ = v_isSharedCheck_2399_;
goto v_resetjp_2388_;
}
else
{
lean_inc(v_node_2387_);
lean_dec(v_v_2364_);
v___x_2389_ = lean_box(0);
v_isShared_2390_ = v_isSharedCheck_2399_;
goto v_resetjp_2388_;
}
v_resetjp_2388_:
{
size_t v___x_2391_; size_t v___x_2392_; size_t v___x_2393_; size_t v___x_2394_; lean_object* v___x_2395_; lean_object* v___x_2397_; 
v___x_2391_ = ((size_t)5ULL);
v___x_2392_ = lean_usize_shift_right(v_x_2351_, v___x_2391_);
v___x_2393_ = ((size_t)1ULL);
v___x_2394_ = lean_usize_add(v_x_2352_, v___x_2393_);
v___x_2395_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0___redArg(v_node_2387_, v___x_2392_, v___x_2394_, v_x_2353_, v_x_2354_);
if (v_isShared_2390_ == 0)
{
lean_ctor_set(v___x_2389_, 0, v___x_2395_);
v___x_2397_ = v___x_2389_;
goto v_reusejp_2396_;
}
else
{
lean_object* v_reuseFailAlloc_2398_; 
v_reuseFailAlloc_2398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2398_, 0, v___x_2395_);
v___x_2397_ = v_reuseFailAlloc_2398_;
goto v_reusejp_2396_;
}
v_reusejp_2396_:
{
v___y_2368_ = v___x_2397_;
goto v___jp_2367_;
}
}
}
default: 
{
lean_object* v___x_2400_; 
v___x_2400_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2400_, 0, v_x_2353_);
lean_ctor_set(v___x_2400_, 1, v_x_2354_);
v___y_2368_ = v___x_2400_;
goto v___jp_2367_;
}
}
v___jp_2367_:
{
lean_object* v___x_2369_; lean_object* v___x_2371_; 
v___x_2369_ = lean_array_fset(v_xs_x27_2366_, v_j_2358_, v___y_2368_);
lean_dec(v_j_2358_);
if (v_isShared_2363_ == 0)
{
lean_ctor_set(v___x_2362_, 0, v___x_2369_);
v___x_2371_ = v___x_2362_;
goto v_reusejp_2370_;
}
else
{
lean_object* v_reuseFailAlloc_2372_; 
v_reuseFailAlloc_2372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2372_, 0, v___x_2369_);
v___x_2371_ = v_reuseFailAlloc_2372_;
goto v_reusejp_2370_;
}
v_reusejp_2370_:
{
return v___x_2371_;
}
}
}
}
}
else
{
lean_object* v_ks_2403_; lean_object* v_vs_2404_; lean_object* v___x_2406_; uint8_t v_isShared_2407_; uint8_t v_isSharedCheck_2422_; 
v_ks_2403_ = lean_ctor_get(v_x_2350_, 0);
v_vs_2404_ = lean_ctor_get(v_x_2350_, 1);
v_isSharedCheck_2422_ = !lean_is_exclusive(v_x_2350_);
if (v_isSharedCheck_2422_ == 0)
{
v___x_2406_ = v_x_2350_;
v_isShared_2407_ = v_isSharedCheck_2422_;
goto v_resetjp_2405_;
}
else
{
lean_inc(v_vs_2404_);
lean_inc(v_ks_2403_);
lean_dec(v_x_2350_);
v___x_2406_ = lean_box(0);
v_isShared_2407_ = v_isSharedCheck_2422_;
goto v_resetjp_2405_;
}
v_resetjp_2405_:
{
lean_object* v___x_2409_; 
if (v_isShared_2407_ == 0)
{
v___x_2409_ = v___x_2406_;
goto v_reusejp_2408_;
}
else
{
lean_object* v_reuseFailAlloc_2421_; 
v_reuseFailAlloc_2421_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2421_, 0, v_ks_2403_);
lean_ctor_set(v_reuseFailAlloc_2421_, 1, v_vs_2404_);
v___x_2409_ = v_reuseFailAlloc_2421_;
goto v_reusejp_2408_;
}
v_reusejp_2408_:
{
lean_object* v_newNode_2410_; size_t v___x_2411_; uint8_t v___x_2412_; 
v_newNode_2410_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0_spec__1___redArg(v___x_2409_, v_x_2353_, v_x_2354_);
v___x_2411_ = ((size_t)7ULL);
v___x_2412_ = lean_usize_dec_le(v___x_2411_, v_x_2352_);
if (v___x_2412_ == 0)
{
lean_object* v___x_2413_; lean_object* v___x_2414_; uint8_t v___x_2415_; 
v___x_2413_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2410_);
v___x_2414_ = lean_unsigned_to_nat(4u);
v___x_2415_ = lean_nat_dec_lt(v___x_2413_, v___x_2414_);
lean_dec(v___x_2413_);
if (v___x_2415_ == 0)
{
lean_object* v_ks_2416_; lean_object* v_vs_2417_; lean_object* v___x_2418_; lean_object* v___x_2419_; lean_object* v___x_2420_; 
v_ks_2416_ = lean_ctor_get(v_newNode_2410_, 0);
lean_inc_ref(v_ks_2416_);
v_vs_2417_ = lean_ctor_get(v_newNode_2410_, 1);
lean_inc_ref(v_vs_2417_);
lean_dec_ref(v_newNode_2410_);
v___x_2418_ = lean_unsigned_to_nat(0u);
v___x_2419_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg___closed__0);
v___x_2420_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0_spec__2___redArg(v_x_2352_, v_ks_2416_, v_vs_2417_, v___x_2418_, v___x_2419_);
lean_dec_ref(v_vs_2417_);
lean_dec_ref(v_ks_2416_);
return v___x_2420_;
}
else
{
return v_newNode_2410_;
}
}
else
{
return v_newNode_2410_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2350_ = stack[0].m_obj;
size_t v_x_2351_ = stack[1].m_num;
size_t v_x_2352_ = stack[2].m_num;
lean_object* v_x_2353_ = stack[3].m_obj;
lean_object* v_x_2354_ = stack[4].m_obj;
lean_object* v_res_2423_;
v_res_2423_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0___redArg(v_x_2350_, v_x_2351_, v_x_2352_, v_x_2353_, v_x_2354_);
stack->m_obj
 = v_res_2423_;
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0_spec__2___redArg(size_t v_depth_2424_, lean_object* v_keys_2425_, lean_object* v_vals_2426_, lean_object* v_i_2427_, lean_object* v_entries_2428_){
_start:
{
lean_object* v___x_2429_; uint8_t v___x_2430_; 
v___x_2429_ = lean_array_get_size(v_keys_2425_);
v___x_2430_ = lean_nat_dec_lt(v_i_2427_, v___x_2429_);
if (v___x_2430_ == 0)
{
lean_dec(v_i_2427_);
return v_entries_2428_;
}
else
{
lean_object* v_k_2431_; lean_object* v_v_2432_; size_t v___x_2433_; size_t v___x_2434_; size_t v___x_2435_; uint64_t v___x_2436_; size_t v_h_2437_; size_t v___x_2438_; lean_object* v___x_2439_; size_t v___x_2440_; size_t v___x_2441_; size_t v___x_2442_; size_t v_h_2443_; lean_object* v___x_2444_; lean_object* v___x_2445_; 
v_k_2431_ = lean_array_fget_borrowed(v_keys_2425_, v_i_2427_);
v_v_2432_ = lean_array_fget_borrowed(v_vals_2426_, v_i_2427_);
v___x_2433_ = lean_ptr_addr(v_k_2431_);
v___x_2434_ = ((size_t)3ULL);
v___x_2435_ = lean_usize_shift_right(v___x_2433_, v___x_2434_);
v___x_2436_ = lean_usize_to_uint64(v___x_2435_);
v_h_2437_ = lean_uint64_to_usize(v___x_2436_);
v___x_2438_ = ((size_t)5ULL);
v___x_2439_ = lean_unsigned_to_nat(1u);
v___x_2440_ = ((size_t)1ULL);
v___x_2441_ = lean_usize_sub(v_depth_2424_, v___x_2440_);
v___x_2442_ = lean_usize_mul(v___x_2438_, v___x_2441_);
v_h_2443_ = lean_usize_shift_right(v_h_2437_, v___x_2442_);
v___x_2444_ = lean_nat_add(v_i_2427_, v___x_2439_);
lean_dec(v_i_2427_);
lean_inc(v_v_2432_);
lean_inc(v_k_2431_);
v___x_2445_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0___redArg(v_entries_2428_, v_h_2443_, v_depth_2424_, v_k_2431_, v_v_2432_);
v_i_2427_ = v___x_2444_;
v_entries_2428_ = v___x_2445_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_depth_2424_ = stack[0].m_num;
lean_object* v_keys_2425_ = stack[1].m_obj;
lean_object* v_vals_2426_ = stack[2].m_obj;
lean_object* v_i_2427_ = stack[3].m_obj;
lean_object* v_entries_2428_ = stack[4].m_obj;
lean_object* v_res_2447_;
v_res_2447_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0_spec__2___redArg(v_depth_2424_, v_keys_2425_, v_vals_2426_, v_i_2427_, v_entries_2428_);
stack->m_obj
 = v_res_2447_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_2448_, lean_object* v_keys_2449_, lean_object* v_vals_2450_, lean_object* v_i_2451_, lean_object* v_entries_2452_){
_start:
{
size_t v_depth_boxed_2453_; lean_object* v_res_2454_; 
v_depth_boxed_2453_ = lean_unbox_usize(v_depth_2448_);
lean_dec(v_depth_2448_);
v_res_2454_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0_spec__2___redArg(v_depth_boxed_2453_, v_keys_2449_, v_vals_2450_, v_i_2451_, v_entries_2452_);
lean_dec_ref(v_vals_2450_);
lean_dec_ref(v_keys_2449_);
return v_res_2454_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0___redArg___boxed(lean_object* v_x_2455_, lean_object* v_x_2456_, lean_object* v_x_2457_, lean_object* v_x_2458_, lean_object* v_x_2459_){
_start:
{
size_t v_x_131345__boxed_2460_; size_t v_x_131346__boxed_2461_; lean_object* v_res_2462_; 
v_x_131345__boxed_2460_ = lean_unbox_usize(v_x_2456_);
lean_dec(v_x_2456_);
v_x_131346__boxed_2461_ = lean_unbox_usize(v_x_2457_);
lean_dec(v_x_2457_);
v_res_2462_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0___redArg(v_x_2455_, v_x_131345__boxed_2460_, v_x_131346__boxed_2461_, v_x_2458_, v_x_2459_);
return v_res_2462_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0___redArg(lean_object* v_x_2463_, lean_object* v_x_2464_, lean_object* v_x_2465_){
_start:
{
size_t v___x_2466_; size_t v___x_2467_; size_t v___x_2468_; uint64_t v___x_2469_; size_t v___x_2470_; size_t v___x_2471_; lean_object* v___x_2472_; 
v___x_2466_ = lean_ptr_addr(v_x_2464_);
v___x_2467_ = ((size_t)3ULL);
v___x_2468_ = lean_usize_shift_right(v___x_2466_, v___x_2467_);
v___x_2469_ = lean_usize_to_uint64(v___x_2468_);
v___x_2470_ = lean_uint64_to_usize(v___x_2469_);
v___x_2471_ = ((size_t)1ULL);
v___x_2472_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0___redArg(v_x_2463_, v___x_2470_, v___x_2471_, v_x_2464_, v_x_2465_);
return v___x_2472_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_internalize___lam__0(lean_object* v_e_2473_, lean_object* v_val_2474_, lean_object* v_s_2475_){
_start:
{
lean_object* v_toRingState_2476_; lean_object* v_denoteEntries_2477_; lean_object* v_nextId_2478_; lean_object* v_steps_2479_; lean_object* v_queue_2480_; lean_object* v_basis_2481_; lean_object* v_diseqs_2482_; uint8_t v_recheck_2483_; lean_object* v_invSet_2484_; lean_object* v_powIdentityVarCount_2485_; lean_object* v_numEq0_x3f_2486_; uint8_t v_numEq0Updated_2487_; lean_object* v___x_2489_; uint8_t v_isShared_2490_; uint8_t v_isSharedCheck_2507_; 
v_toRingState_2476_ = lean_ctor_get(v_s_2475_, 0);
v_denoteEntries_2477_ = lean_ctor_get(v_s_2475_, 1);
v_nextId_2478_ = lean_ctor_get(v_s_2475_, 2);
v_steps_2479_ = lean_ctor_get(v_s_2475_, 3);
v_queue_2480_ = lean_ctor_get(v_s_2475_, 4);
v_basis_2481_ = lean_ctor_get(v_s_2475_, 5);
v_diseqs_2482_ = lean_ctor_get(v_s_2475_, 6);
v_recheck_2483_ = lean_ctor_get_uint8(v_s_2475_, sizeof(void*)*10);
v_invSet_2484_ = lean_ctor_get(v_s_2475_, 7);
v_powIdentityVarCount_2485_ = lean_ctor_get(v_s_2475_, 8);
v_numEq0_x3f_2486_ = lean_ctor_get(v_s_2475_, 9);
v_numEq0Updated_2487_ = lean_ctor_get_uint8(v_s_2475_, sizeof(void*)*10 + 1);
v_isSharedCheck_2507_ = !lean_is_exclusive(v_s_2475_);
if (v_isSharedCheck_2507_ == 0)
{
v___x_2489_ = v_s_2475_;
v_isShared_2490_ = v_isSharedCheck_2507_;
goto v_resetjp_2488_;
}
else
{
lean_inc(v_numEq0_x3f_2486_);
lean_inc(v_powIdentityVarCount_2485_);
lean_inc(v_invSet_2484_);
lean_inc(v_diseqs_2482_);
lean_inc(v_basis_2481_);
lean_inc(v_queue_2480_);
lean_inc(v_steps_2479_);
lean_inc(v_nextId_2478_);
lean_inc(v_denoteEntries_2477_);
lean_inc(v_toRingState_2476_);
lean_dec(v_s_2475_);
v___x_2489_ = lean_box(0);
v_isShared_2490_ = v_isSharedCheck_2507_;
goto v_resetjp_2488_;
}
v_resetjp_2488_:
{
lean_object* v_vars_2491_; lean_object* v_varMap_2492_; lean_object* v_denote_2493_; lean_object* v___x_2495_; uint8_t v_isShared_2496_; uint8_t v_isSharedCheck_2506_; 
v_vars_2491_ = lean_ctor_get(v_toRingState_2476_, 0);
v_varMap_2492_ = lean_ctor_get(v_toRingState_2476_, 1);
v_denote_2493_ = lean_ctor_get(v_toRingState_2476_, 2);
v_isSharedCheck_2506_ = !lean_is_exclusive(v_toRingState_2476_);
if (v_isSharedCheck_2506_ == 0)
{
v___x_2495_ = v_toRingState_2476_;
v_isShared_2496_ = v_isSharedCheck_2506_;
goto v_resetjp_2494_;
}
else
{
lean_inc(v_denote_2493_);
lean_inc(v_varMap_2492_);
lean_inc(v_vars_2491_);
lean_dec(v_toRingState_2476_);
v___x_2495_ = lean_box(0);
v_isShared_2496_ = v_isSharedCheck_2506_;
goto v_resetjp_2494_;
}
v_resetjp_2494_:
{
lean_object* v___x_2497_; lean_object* v___x_2499_; 
lean_inc_ref(v_val_2474_);
lean_inc_ref(v_e_2473_);
v___x_2497_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0___redArg(v_denote_2493_, v_e_2473_, v_val_2474_);
if (v_isShared_2496_ == 0)
{
lean_ctor_set(v___x_2495_, 2, v___x_2497_);
v___x_2499_ = v___x_2495_;
goto v_reusejp_2498_;
}
else
{
lean_object* v_reuseFailAlloc_2505_; 
v_reuseFailAlloc_2505_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2505_, 0, v_vars_2491_);
lean_ctor_set(v_reuseFailAlloc_2505_, 1, v_varMap_2492_);
lean_ctor_set(v_reuseFailAlloc_2505_, 2, v___x_2497_);
v___x_2499_ = v_reuseFailAlloc_2505_;
goto v_reusejp_2498_;
}
v_reusejp_2498_:
{
lean_object* v___x_2500_; lean_object* v___x_2501_; lean_object* v___x_2503_; 
v___x_2500_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2500_, 0, v_e_2473_);
lean_ctor_set(v___x_2500_, 1, v_val_2474_);
v___x_2501_ = l_Lean_PersistentArray_push___redArg(v_denoteEntries_2477_, v___x_2500_);
if (v_isShared_2490_ == 0)
{
lean_ctor_set(v___x_2489_, 1, v___x_2501_);
lean_ctor_set(v___x_2489_, 0, v___x_2499_);
v___x_2503_ = v___x_2489_;
goto v_reusejp_2502_;
}
else
{
lean_object* v_reuseFailAlloc_2504_; 
v_reuseFailAlloc_2504_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v_reuseFailAlloc_2504_, 0, v___x_2499_);
lean_ctor_set(v_reuseFailAlloc_2504_, 1, v___x_2501_);
lean_ctor_set(v_reuseFailAlloc_2504_, 2, v_nextId_2478_);
lean_ctor_set(v_reuseFailAlloc_2504_, 3, v_steps_2479_);
lean_ctor_set(v_reuseFailAlloc_2504_, 4, v_queue_2480_);
lean_ctor_set(v_reuseFailAlloc_2504_, 5, v_basis_2481_);
lean_ctor_set(v_reuseFailAlloc_2504_, 6, v_diseqs_2482_);
lean_ctor_set(v_reuseFailAlloc_2504_, 7, v_invSet_2484_);
lean_ctor_set(v_reuseFailAlloc_2504_, 8, v_powIdentityVarCount_2485_);
lean_ctor_set(v_reuseFailAlloc_2504_, 9, v_numEq0_x3f_2486_);
lean_ctor_set_uint8(v_reuseFailAlloc_2504_, sizeof(void*)*10, v_recheck_2483_);
lean_ctor_set_uint8(v_reuseFailAlloc_2504_, sizeof(void*)*10 + 1, v_numEq0Updated_2487_);
v___x_2503_ = v_reuseFailAlloc_2504_;
goto v_reusejp_2502_;
}
v_reusejp_2502_:
{
return v___x_2503_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_internalize___lam__1(lean_object* v_e_2508_, lean_object* v_val_2509_, lean_object* v_s_2510_){
_start:
{
lean_object* v_denote_2511_; lean_object* v_vars_2512_; lean_object* v_varMap_2513_; lean_object* v___x_2515_; uint8_t v_isShared_2516_; uint8_t v_isSharedCheck_2521_; 
v_denote_2511_ = lean_ctor_get(v_s_2510_, 0);
v_vars_2512_ = lean_ctor_get(v_s_2510_, 1);
v_varMap_2513_ = lean_ctor_get(v_s_2510_, 2);
v_isSharedCheck_2521_ = !lean_is_exclusive(v_s_2510_);
if (v_isSharedCheck_2521_ == 0)
{
v___x_2515_ = v_s_2510_;
v_isShared_2516_ = v_isSharedCheck_2521_;
goto v_resetjp_2514_;
}
else
{
lean_inc(v_varMap_2513_);
lean_inc(v_vars_2512_);
lean_inc(v_denote_2511_);
lean_dec(v_s_2510_);
v___x_2515_ = lean_box(0);
v_isShared_2516_ = v_isSharedCheck_2521_;
goto v_resetjp_2514_;
}
v_resetjp_2514_:
{
lean_object* v___x_2517_; lean_object* v___x_2519_; 
v___x_2517_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0___redArg(v_denote_2511_, v_e_2508_, v_val_2509_);
if (v_isShared_2516_ == 0)
{
lean_ctor_set(v___x_2515_, 0, v___x_2517_);
v___x_2519_ = v___x_2515_;
goto v_reusejp_2518_;
}
else
{
lean_object* v_reuseFailAlloc_2520_; 
v_reuseFailAlloc_2520_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2520_, 0, v___x_2517_);
lean_ctor_set(v_reuseFailAlloc_2520_, 1, v_vars_2512_);
lean_ctor_set(v_reuseFailAlloc_2520_, 2, v_varMap_2513_);
v___x_2519_ = v_reuseFailAlloc_2520_;
goto v_reusejp_2518_;
}
v_reusejp_2518_:
{
return v___x_2519_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_internalize___lam__2(lean_object* v_e_2522_, lean_object* v_val_2523_, lean_object* v_s_2524_){
_start:
{
lean_object* v_vars_2525_; lean_object* v_varMap_2526_; lean_object* v_denote_2527_; lean_object* v___x_2529_; uint8_t v_isShared_2530_; uint8_t v_isSharedCheck_2535_; 
v_vars_2525_ = lean_ctor_get(v_s_2524_, 0);
v_varMap_2526_ = lean_ctor_get(v_s_2524_, 1);
v_denote_2527_ = lean_ctor_get(v_s_2524_, 2);
v_isSharedCheck_2535_ = !lean_is_exclusive(v_s_2524_);
if (v_isSharedCheck_2535_ == 0)
{
v___x_2529_ = v_s_2524_;
v_isShared_2530_ = v_isSharedCheck_2535_;
goto v_resetjp_2528_;
}
else
{
lean_inc(v_denote_2527_);
lean_inc(v_varMap_2526_);
lean_inc(v_vars_2525_);
lean_dec(v_s_2524_);
v___x_2529_ = lean_box(0);
v_isShared_2530_ = v_isSharedCheck_2535_;
goto v_resetjp_2528_;
}
v_resetjp_2528_:
{
lean_object* v___x_2531_; lean_object* v___x_2533_; 
v___x_2531_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0___redArg(v_denote_2527_, v_e_2522_, v_val_2523_);
if (v_isShared_2530_ == 0)
{
lean_ctor_set(v___x_2529_, 2, v___x_2531_);
v___x_2533_ = v___x_2529_;
goto v_reusejp_2532_;
}
else
{
lean_object* v_reuseFailAlloc_2534_; 
v_reuseFailAlloc_2534_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2534_, 0, v_vars_2525_);
lean_ctor_set(v_reuseFailAlloc_2534_, 1, v_varMap_2526_);
lean_ctor_set(v_reuseFailAlloc_2534_, 2, v___x_2531_);
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
lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__1___redArg(lean_object* v_cls_2536_, lean_object* v_msg_2537_, lean_object* v___y_2538_, lean_object* v___y_2539_, lean_object* v___y_2540_, lean_object* v___y_2541_){
_start:
{
lean_object* v_ref_2543_; lean_object* v___x_2544_; lean_object* v_a_2545_; lean_object* v___x_2547_; uint8_t v_isShared_2548_; uint8_t v_isSharedCheck_2590_; 
v_ref_2543_ = lean_ctor_get(v___y_2540_, 2);
v___x_2544_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5(v_msg_2537_, v___y_2538_, v___y_2539_, v___y_2540_, v___y_2541_);
v_a_2545_ = lean_ctor_get(v___x_2544_, 0);
v_isSharedCheck_2590_ = !lean_is_exclusive(v___x_2544_);
if (v_isSharedCheck_2590_ == 0)
{
v___x_2547_ = v___x_2544_;
v_isShared_2548_ = v_isSharedCheck_2590_;
goto v_resetjp_2546_;
}
else
{
lean_inc(v_a_2545_);
lean_dec(v___x_2544_);
v___x_2547_ = lean_box(0);
v_isShared_2548_ = v_isSharedCheck_2590_;
goto v_resetjp_2546_;
}
v_resetjp_2546_:
{
lean_object* v___x_2549_; lean_object* v_traceState_2550_; lean_object* v_env_2551_; lean_object* v_nextMacroScope_2552_; lean_object* v_ngen_2553_; lean_object* v_auxDeclNGen_2554_; lean_object* v_cache_2555_; lean_object* v_recordedDeps_2556_; lean_object* v_messages_2557_; lean_object* v_infoState_2558_; lean_object* v_snapshotTasks_2559_; lean_object* v___x_2561_; uint8_t v_isShared_2562_; uint8_t v_isSharedCheck_2589_; 
v___x_2549_ = lean_st_ref_take(v___y_2541_);
v_traceState_2550_ = lean_ctor_get(v___x_2549_, 4);
v_env_2551_ = lean_ctor_get(v___x_2549_, 0);
v_nextMacroScope_2552_ = lean_ctor_get(v___x_2549_, 1);
v_ngen_2553_ = lean_ctor_get(v___x_2549_, 2);
v_auxDeclNGen_2554_ = lean_ctor_get(v___x_2549_, 3);
v_cache_2555_ = lean_ctor_get(v___x_2549_, 5);
v_recordedDeps_2556_ = lean_ctor_get(v___x_2549_, 6);
v_messages_2557_ = lean_ctor_get(v___x_2549_, 7);
v_infoState_2558_ = lean_ctor_get(v___x_2549_, 8);
v_snapshotTasks_2559_ = lean_ctor_get(v___x_2549_, 9);
v_isSharedCheck_2589_ = !lean_is_exclusive(v___x_2549_);
if (v_isSharedCheck_2589_ == 0)
{
v___x_2561_ = v___x_2549_;
v_isShared_2562_ = v_isSharedCheck_2589_;
goto v_resetjp_2560_;
}
else
{
lean_inc(v_snapshotTasks_2559_);
lean_inc(v_infoState_2558_);
lean_inc(v_messages_2557_);
lean_inc(v_recordedDeps_2556_);
lean_inc(v_cache_2555_);
lean_inc(v_traceState_2550_);
lean_inc(v_auxDeclNGen_2554_);
lean_inc(v_ngen_2553_);
lean_inc(v_nextMacroScope_2552_);
lean_inc(v_env_2551_);
lean_dec(v___x_2549_);
v___x_2561_ = lean_box(0);
v_isShared_2562_ = v_isSharedCheck_2589_;
goto v_resetjp_2560_;
}
v_resetjp_2560_:
{
uint64_t v_tid_2563_; lean_object* v_traces_2564_; lean_object* v___x_2566_; uint8_t v_isShared_2567_; uint8_t v_isSharedCheck_2588_; 
v_tid_2563_ = lean_ctor_get_uint64(v_traceState_2550_, sizeof(void*)*1);
v_traces_2564_ = lean_ctor_get(v_traceState_2550_, 0);
v_isSharedCheck_2588_ = !lean_is_exclusive(v_traceState_2550_);
if (v_isSharedCheck_2588_ == 0)
{
v___x_2566_ = v_traceState_2550_;
v_isShared_2567_ = v_isSharedCheck_2588_;
goto v_resetjp_2565_;
}
else
{
lean_inc(v_traces_2564_);
lean_dec(v_traceState_2550_);
v___x_2566_ = lean_box(0);
v_isShared_2567_ = v_isSharedCheck_2588_;
goto v_resetjp_2565_;
}
v_resetjp_2565_:
{
lean_object* v___x_2568_; lean_object* v___x_2569_; double v___x_2570_; uint8_t v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2579_; 
v___x_2568_ = lean_box(0);
v___x_2569_ = lean_box(0);
v___x_2570_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg___closed__0);
v___x_2571_ = 0;
v___x_2572_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg___closed__1));
v___x_2573_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2573_, 0, v_cls_2536_);
lean_ctor_set(v___x_2573_, 1, v___x_2569_);
lean_ctor_set(v___x_2573_, 2, v___x_2572_);
lean_ctor_set_float(v___x_2573_, sizeof(void*)*3, v___x_2570_);
lean_ctor_set_float(v___x_2573_, sizeof(void*)*3 + 8, v___x_2570_);
lean_ctor_set_uint8(v___x_2573_, sizeof(void*)*3 + 16, v___x_2571_);
v___x_2574_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg___closed__2));
v___x_2575_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2575_, 0, v___x_2573_);
lean_ctor_set(v___x_2575_, 1, v_a_2545_);
lean_ctor_set(v___x_2575_, 2, v___x_2574_);
lean_inc(v_ref_2543_);
v___x_2576_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2576_, 0, v_ref_2543_);
lean_ctor_set(v___x_2576_, 1, v___x_2575_);
v___x_2577_ = l_Lean_PersistentArray_push___redArg(v_traces_2564_, v___x_2576_);
if (v_isShared_2567_ == 0)
{
lean_ctor_set(v___x_2566_, 0, v___x_2577_);
v___x_2579_ = v___x_2566_;
goto v_reusejp_2578_;
}
else
{
lean_object* v_reuseFailAlloc_2587_; 
v_reuseFailAlloc_2587_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2587_, 0, v___x_2577_);
lean_ctor_set_uint64(v_reuseFailAlloc_2587_, sizeof(void*)*1, v_tid_2563_);
v___x_2579_ = v_reuseFailAlloc_2587_;
goto v_reusejp_2578_;
}
v_reusejp_2578_:
{
lean_object* v___x_2581_; 
if (v_isShared_2562_ == 0)
{
lean_ctor_set(v___x_2561_, 4, v___x_2579_);
v___x_2581_ = v___x_2561_;
goto v_reusejp_2580_;
}
else
{
lean_object* v_reuseFailAlloc_2586_; 
v_reuseFailAlloc_2586_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2586_, 0, v_env_2551_);
lean_ctor_set(v_reuseFailAlloc_2586_, 1, v_nextMacroScope_2552_);
lean_ctor_set(v_reuseFailAlloc_2586_, 2, v_ngen_2553_);
lean_ctor_set(v_reuseFailAlloc_2586_, 3, v_auxDeclNGen_2554_);
lean_ctor_set(v_reuseFailAlloc_2586_, 4, v___x_2579_);
lean_ctor_set(v_reuseFailAlloc_2586_, 5, v_cache_2555_);
lean_ctor_set(v_reuseFailAlloc_2586_, 6, v_recordedDeps_2556_);
lean_ctor_set(v_reuseFailAlloc_2586_, 7, v_messages_2557_);
lean_ctor_set(v_reuseFailAlloc_2586_, 8, v_infoState_2558_);
lean_ctor_set(v_reuseFailAlloc_2586_, 9, v_snapshotTasks_2559_);
v___x_2581_ = v_reuseFailAlloc_2586_;
goto v_reusejp_2580_;
}
v_reusejp_2580_:
{
lean_object* v___x_2582_; lean_object* v___x_2584_; 
v___x_2582_ = lean_st_ref_put(v___y_2541_, v___x_2581_);
if (v_isShared_2548_ == 0)
{
lean_ctor_set(v___x_2547_, 0, v___x_2568_);
v___x_2584_ = v___x_2547_;
goto v_reusejp_2583_;
}
else
{
lean_object* v_reuseFailAlloc_2585_; 
v_reuseFailAlloc_2585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2585_, 0, v___x_2568_);
v___x_2584_ = v_reuseFailAlloc_2585_;
goto v_reusejp_2583_;
}
v_reusejp_2583_:
{
return v___x_2584_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_2536_ = stack[0].m_obj;
lean_object* v_msg_2537_ = stack[1].m_obj;
lean_object* v___y_2538_ = stack[2].m_obj;
lean_object* v___y_2539_ = stack[3].m_obj;
lean_object* v___y_2540_ = stack[4].m_obj;
lean_object* v___y_2541_ = stack[5].m_obj;
lean_object* v_res_2591_;
v_res_2591_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__1___redArg(v_cls_2536_, v_msg_2537_, v___y_2538_, v___y_2539_, v___y_2540_, v___y_2541_);
stack->m_obj
 = v_res_2591_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__1___redArg___boxed(lean_object* v_cls_2592_, lean_object* v_msg_2593_, lean_object* v___y_2594_, lean_object* v___y_2595_, lean_object* v___y_2596_, lean_object* v___y_2597_, lean_object* v___y_2598_){
_start:
{
lean_object* v_res_2599_; 
v_res_2599_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__1___redArg(v_cls_2592_, v_msg_2593_, v___y_2594_, v___y_2595_, v___y_2596_, v___y_2597_);
lean_dec(v___y_2597_);
lean_dec_ref(v___y_2596_);
lean_dec(v___y_2595_);
lean_dec_ref(v___y_2594_);
return v_res_2599_;
}
}
lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__2___redArg(lean_object* v_cls_2600_, lean_object* v_msg_2601_, lean_object* v___y_2602_, lean_object* v___y_2603_, lean_object* v___y_2604_, lean_object* v___y_2605_){
_start:
{
lean_object* v_ref_2607_; lean_object* v___x_2608_; lean_object* v_a_2609_; lean_object* v___x_2611_; uint8_t v_isShared_2612_; uint8_t v_isSharedCheck_2654_; 
v_ref_2607_ = lean_ctor_get(v___y_2604_, 2);
v___x_2608_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5(v_msg_2601_, v___y_2602_, v___y_2603_, v___y_2604_, v___y_2605_);
v_a_2609_ = lean_ctor_get(v___x_2608_, 0);
v_isSharedCheck_2654_ = !lean_is_exclusive(v___x_2608_);
if (v_isSharedCheck_2654_ == 0)
{
v___x_2611_ = v___x_2608_;
v_isShared_2612_ = v_isSharedCheck_2654_;
goto v_resetjp_2610_;
}
else
{
lean_inc(v_a_2609_);
lean_dec(v___x_2608_);
v___x_2611_ = lean_box(0);
v_isShared_2612_ = v_isSharedCheck_2654_;
goto v_resetjp_2610_;
}
v_resetjp_2610_:
{
lean_object* v___x_2613_; lean_object* v_traceState_2614_; lean_object* v_env_2615_; lean_object* v_nextMacroScope_2616_; lean_object* v_ngen_2617_; lean_object* v_auxDeclNGen_2618_; lean_object* v_cache_2619_; lean_object* v_recordedDeps_2620_; lean_object* v_messages_2621_; lean_object* v_infoState_2622_; lean_object* v_snapshotTasks_2623_; lean_object* v___x_2625_; uint8_t v_isShared_2626_; uint8_t v_isSharedCheck_2653_; 
v___x_2613_ = lean_st_ref_take(v___y_2605_);
v_traceState_2614_ = lean_ctor_get(v___x_2613_, 4);
v_env_2615_ = lean_ctor_get(v___x_2613_, 0);
v_nextMacroScope_2616_ = lean_ctor_get(v___x_2613_, 1);
v_ngen_2617_ = lean_ctor_get(v___x_2613_, 2);
v_auxDeclNGen_2618_ = lean_ctor_get(v___x_2613_, 3);
v_cache_2619_ = lean_ctor_get(v___x_2613_, 5);
v_recordedDeps_2620_ = lean_ctor_get(v___x_2613_, 6);
v_messages_2621_ = lean_ctor_get(v___x_2613_, 7);
v_infoState_2622_ = lean_ctor_get(v___x_2613_, 8);
v_snapshotTasks_2623_ = lean_ctor_get(v___x_2613_, 9);
v_isSharedCheck_2653_ = !lean_is_exclusive(v___x_2613_);
if (v_isSharedCheck_2653_ == 0)
{
v___x_2625_ = v___x_2613_;
v_isShared_2626_ = v_isSharedCheck_2653_;
goto v_resetjp_2624_;
}
else
{
lean_inc(v_snapshotTasks_2623_);
lean_inc(v_infoState_2622_);
lean_inc(v_messages_2621_);
lean_inc(v_recordedDeps_2620_);
lean_inc(v_cache_2619_);
lean_inc(v_traceState_2614_);
lean_inc(v_auxDeclNGen_2618_);
lean_inc(v_ngen_2617_);
lean_inc(v_nextMacroScope_2616_);
lean_inc(v_env_2615_);
lean_dec(v___x_2613_);
v___x_2625_ = lean_box(0);
v_isShared_2626_ = v_isSharedCheck_2653_;
goto v_resetjp_2624_;
}
v_resetjp_2624_:
{
uint64_t v_tid_2627_; lean_object* v_traces_2628_; lean_object* v___x_2630_; uint8_t v_isShared_2631_; uint8_t v_isSharedCheck_2652_; 
v_tid_2627_ = lean_ctor_get_uint64(v_traceState_2614_, sizeof(void*)*1);
v_traces_2628_ = lean_ctor_get(v_traceState_2614_, 0);
v_isSharedCheck_2652_ = !lean_is_exclusive(v_traceState_2614_);
if (v_isSharedCheck_2652_ == 0)
{
v___x_2630_ = v_traceState_2614_;
v_isShared_2631_ = v_isSharedCheck_2652_;
goto v_resetjp_2629_;
}
else
{
lean_inc(v_traces_2628_);
lean_dec(v_traceState_2614_);
v___x_2630_ = lean_box(0);
v_isShared_2631_ = v_isSharedCheck_2652_;
goto v_resetjp_2629_;
}
v_resetjp_2629_:
{
lean_object* v___x_2632_; lean_object* v___x_2633_; double v___x_2634_; uint8_t v___x_2635_; lean_object* v___x_2636_; lean_object* v___x_2637_; lean_object* v___x_2638_; lean_object* v___x_2639_; lean_object* v___x_2640_; lean_object* v___x_2641_; lean_object* v___x_2643_; 
v___x_2632_ = lean_box(0);
v___x_2633_ = lean_box(0);
v___x_2634_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg___closed__0);
v___x_2635_ = 0;
v___x_2636_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg___closed__1));
v___x_2637_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2637_, 0, v_cls_2600_);
lean_ctor_set(v___x_2637_, 1, v___x_2633_);
lean_ctor_set(v___x_2637_, 2, v___x_2636_);
lean_ctor_set_float(v___x_2637_, sizeof(void*)*3, v___x_2634_);
lean_ctor_set_float(v___x_2637_, sizeof(void*)*3 + 8, v___x_2634_);
lean_ctor_set_uint8(v___x_2637_, sizeof(void*)*3 + 16, v___x_2635_);
v___x_2638_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg___closed__2));
v___x_2639_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2639_, 0, v___x_2637_);
lean_ctor_set(v___x_2639_, 1, v_a_2609_);
lean_ctor_set(v___x_2639_, 2, v___x_2638_);
lean_inc(v_ref_2607_);
v___x_2640_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2640_, 0, v_ref_2607_);
lean_ctor_set(v___x_2640_, 1, v___x_2639_);
v___x_2641_ = l_Lean_PersistentArray_push___redArg(v_traces_2628_, v___x_2640_);
if (v_isShared_2631_ == 0)
{
lean_ctor_set(v___x_2630_, 0, v___x_2641_);
v___x_2643_ = v___x_2630_;
goto v_reusejp_2642_;
}
else
{
lean_object* v_reuseFailAlloc_2651_; 
v_reuseFailAlloc_2651_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2651_, 0, v___x_2641_);
lean_ctor_set_uint64(v_reuseFailAlloc_2651_, sizeof(void*)*1, v_tid_2627_);
v___x_2643_ = v_reuseFailAlloc_2651_;
goto v_reusejp_2642_;
}
v_reusejp_2642_:
{
lean_object* v___x_2645_; 
if (v_isShared_2626_ == 0)
{
lean_ctor_set(v___x_2625_, 4, v___x_2643_);
v___x_2645_ = v___x_2625_;
goto v_reusejp_2644_;
}
else
{
lean_object* v_reuseFailAlloc_2650_; 
v_reuseFailAlloc_2650_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2650_, 0, v_env_2615_);
lean_ctor_set(v_reuseFailAlloc_2650_, 1, v_nextMacroScope_2616_);
lean_ctor_set(v_reuseFailAlloc_2650_, 2, v_ngen_2617_);
lean_ctor_set(v_reuseFailAlloc_2650_, 3, v_auxDeclNGen_2618_);
lean_ctor_set(v_reuseFailAlloc_2650_, 4, v___x_2643_);
lean_ctor_set(v_reuseFailAlloc_2650_, 5, v_cache_2619_);
lean_ctor_set(v_reuseFailAlloc_2650_, 6, v_recordedDeps_2620_);
lean_ctor_set(v_reuseFailAlloc_2650_, 7, v_messages_2621_);
lean_ctor_set(v_reuseFailAlloc_2650_, 8, v_infoState_2622_);
lean_ctor_set(v_reuseFailAlloc_2650_, 9, v_snapshotTasks_2623_);
v___x_2645_ = v_reuseFailAlloc_2650_;
goto v_reusejp_2644_;
}
v_reusejp_2644_:
{
lean_object* v___x_2646_; lean_object* v___x_2648_; 
v___x_2646_ = lean_st_ref_put(v___y_2605_, v___x_2645_);
if (v_isShared_2612_ == 0)
{
lean_ctor_set(v___x_2611_, 0, v___x_2632_);
v___x_2648_ = v___x_2611_;
goto v_reusejp_2647_;
}
else
{
lean_object* v_reuseFailAlloc_2649_; 
v_reuseFailAlloc_2649_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2649_, 0, v___x_2632_);
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
}
}
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_2600_ = stack[0].m_obj;
lean_object* v_msg_2601_ = stack[1].m_obj;
lean_object* v___y_2602_ = stack[2].m_obj;
lean_object* v___y_2603_ = stack[3].m_obj;
lean_object* v___y_2604_ = stack[4].m_obj;
lean_object* v___y_2605_ = stack[5].m_obj;
lean_object* v_res_2655_;
v_res_2655_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__2___redArg(v_cls_2600_, v_msg_2601_, v___y_2602_, v___y_2603_, v___y_2604_, v___y_2605_);
stack->m_obj
 = v_res_2655_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__2___redArg___boxed(lean_object* v_cls_2656_, lean_object* v_msg_2657_, lean_object* v___y_2658_, lean_object* v___y_2659_, lean_object* v___y_2660_, lean_object* v___y_2661_, lean_object* v___y_2662_){
_start:
{
lean_object* v_res_2663_; 
v_res_2663_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__2___redArg(v_cls_2656_, v_msg_2657_, v___y_2658_, v___y_2659_, v___y_2660_, v___y_2661_);
lean_dec(v___y_2661_);
lean_dec_ref(v___y_2660_);
lean_dec(v___y_2659_);
lean_dec_ref(v___y_2658_);
return v_res_2663_;
}
}
lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__3___redArg(lean_object* v_cls_2664_, lean_object* v_msg_2665_, lean_object* v___y_2666_, lean_object* v___y_2667_, lean_object* v___y_2668_, lean_object* v___y_2669_){
_start:
{
lean_object* v_ref_2671_; lean_object* v___x_2672_; lean_object* v_a_2673_; lean_object* v___x_2675_; uint8_t v_isShared_2676_; uint8_t v_isSharedCheck_2718_; 
v_ref_2671_ = lean_ctor_get(v___y_2668_, 2);
v___x_2672_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5(v_msg_2665_, v___y_2666_, v___y_2667_, v___y_2668_, v___y_2669_);
v_a_2673_ = lean_ctor_get(v___x_2672_, 0);
v_isSharedCheck_2718_ = !lean_is_exclusive(v___x_2672_);
if (v_isSharedCheck_2718_ == 0)
{
v___x_2675_ = v___x_2672_;
v_isShared_2676_ = v_isSharedCheck_2718_;
goto v_resetjp_2674_;
}
else
{
lean_inc(v_a_2673_);
lean_dec(v___x_2672_);
v___x_2675_ = lean_box(0);
v_isShared_2676_ = v_isSharedCheck_2718_;
goto v_resetjp_2674_;
}
v_resetjp_2674_:
{
lean_object* v___x_2677_; lean_object* v_traceState_2678_; lean_object* v_env_2679_; lean_object* v_nextMacroScope_2680_; lean_object* v_ngen_2681_; lean_object* v_auxDeclNGen_2682_; lean_object* v_cache_2683_; lean_object* v_recordedDeps_2684_; lean_object* v_messages_2685_; lean_object* v_infoState_2686_; lean_object* v_snapshotTasks_2687_; lean_object* v___x_2689_; uint8_t v_isShared_2690_; uint8_t v_isSharedCheck_2717_; 
v___x_2677_ = lean_st_ref_take(v___y_2669_);
v_traceState_2678_ = lean_ctor_get(v___x_2677_, 4);
v_env_2679_ = lean_ctor_get(v___x_2677_, 0);
v_nextMacroScope_2680_ = lean_ctor_get(v___x_2677_, 1);
v_ngen_2681_ = lean_ctor_get(v___x_2677_, 2);
v_auxDeclNGen_2682_ = lean_ctor_get(v___x_2677_, 3);
v_cache_2683_ = lean_ctor_get(v___x_2677_, 5);
v_recordedDeps_2684_ = lean_ctor_get(v___x_2677_, 6);
v_messages_2685_ = lean_ctor_get(v___x_2677_, 7);
v_infoState_2686_ = lean_ctor_get(v___x_2677_, 8);
v_snapshotTasks_2687_ = lean_ctor_get(v___x_2677_, 9);
v_isSharedCheck_2717_ = !lean_is_exclusive(v___x_2677_);
if (v_isSharedCheck_2717_ == 0)
{
v___x_2689_ = v___x_2677_;
v_isShared_2690_ = v_isSharedCheck_2717_;
goto v_resetjp_2688_;
}
else
{
lean_inc(v_snapshotTasks_2687_);
lean_inc(v_infoState_2686_);
lean_inc(v_messages_2685_);
lean_inc(v_recordedDeps_2684_);
lean_inc(v_cache_2683_);
lean_inc(v_traceState_2678_);
lean_inc(v_auxDeclNGen_2682_);
lean_inc(v_ngen_2681_);
lean_inc(v_nextMacroScope_2680_);
lean_inc(v_env_2679_);
lean_dec(v___x_2677_);
v___x_2689_ = lean_box(0);
v_isShared_2690_ = v_isSharedCheck_2717_;
goto v_resetjp_2688_;
}
v_resetjp_2688_:
{
uint64_t v_tid_2691_; lean_object* v_traces_2692_; lean_object* v___x_2694_; uint8_t v_isShared_2695_; uint8_t v_isSharedCheck_2716_; 
v_tid_2691_ = lean_ctor_get_uint64(v_traceState_2678_, sizeof(void*)*1);
v_traces_2692_ = lean_ctor_get(v_traceState_2678_, 0);
v_isSharedCheck_2716_ = !lean_is_exclusive(v_traceState_2678_);
if (v_isSharedCheck_2716_ == 0)
{
v___x_2694_ = v_traceState_2678_;
v_isShared_2695_ = v_isSharedCheck_2716_;
goto v_resetjp_2693_;
}
else
{
lean_inc(v_traces_2692_);
lean_dec(v_traceState_2678_);
v___x_2694_ = lean_box(0);
v_isShared_2695_ = v_isSharedCheck_2716_;
goto v_resetjp_2693_;
}
v_resetjp_2693_:
{
lean_object* v___x_2696_; lean_object* v___x_2697_; double v___x_2698_; uint8_t v___x_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; lean_object* v___x_2705_; lean_object* v___x_2707_; 
v___x_2696_ = lean_box(0);
v___x_2697_ = lean_box(0);
v___x_2698_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg___closed__0);
v___x_2699_ = 0;
v___x_2700_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg___closed__1));
v___x_2701_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2701_, 0, v_cls_2664_);
lean_ctor_set(v___x_2701_, 1, v___x_2697_);
lean_ctor_set(v___x_2701_, 2, v___x_2700_);
lean_ctor_set_float(v___x_2701_, sizeof(void*)*3, v___x_2698_);
lean_ctor_set_float(v___x_2701_, sizeof(void*)*3 + 8, v___x_2698_);
lean_ctor_set_uint8(v___x_2701_, sizeof(void*)*3 + 16, v___x_2699_);
v___x_2702_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg___closed__2));
v___x_2703_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2703_, 0, v___x_2701_);
lean_ctor_set(v___x_2703_, 1, v_a_2673_);
lean_ctor_set(v___x_2703_, 2, v___x_2702_);
lean_inc(v_ref_2671_);
v___x_2704_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2704_, 0, v_ref_2671_);
lean_ctor_set(v___x_2704_, 1, v___x_2703_);
v___x_2705_ = l_Lean_PersistentArray_push___redArg(v_traces_2692_, v___x_2704_);
if (v_isShared_2695_ == 0)
{
lean_ctor_set(v___x_2694_, 0, v___x_2705_);
v___x_2707_ = v___x_2694_;
goto v_reusejp_2706_;
}
else
{
lean_object* v_reuseFailAlloc_2715_; 
v_reuseFailAlloc_2715_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2715_, 0, v___x_2705_);
lean_ctor_set_uint64(v_reuseFailAlloc_2715_, sizeof(void*)*1, v_tid_2691_);
v___x_2707_ = v_reuseFailAlloc_2715_;
goto v_reusejp_2706_;
}
v_reusejp_2706_:
{
lean_object* v___x_2709_; 
if (v_isShared_2690_ == 0)
{
lean_ctor_set(v___x_2689_, 4, v___x_2707_);
v___x_2709_ = v___x_2689_;
goto v_reusejp_2708_;
}
else
{
lean_object* v_reuseFailAlloc_2714_; 
v_reuseFailAlloc_2714_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2714_, 0, v_env_2679_);
lean_ctor_set(v_reuseFailAlloc_2714_, 1, v_nextMacroScope_2680_);
lean_ctor_set(v_reuseFailAlloc_2714_, 2, v_ngen_2681_);
lean_ctor_set(v_reuseFailAlloc_2714_, 3, v_auxDeclNGen_2682_);
lean_ctor_set(v_reuseFailAlloc_2714_, 4, v___x_2707_);
lean_ctor_set(v_reuseFailAlloc_2714_, 5, v_cache_2683_);
lean_ctor_set(v_reuseFailAlloc_2714_, 6, v_recordedDeps_2684_);
lean_ctor_set(v_reuseFailAlloc_2714_, 7, v_messages_2685_);
lean_ctor_set(v_reuseFailAlloc_2714_, 8, v_infoState_2686_);
lean_ctor_set(v_reuseFailAlloc_2714_, 9, v_snapshotTasks_2687_);
v___x_2709_ = v_reuseFailAlloc_2714_;
goto v_reusejp_2708_;
}
v_reusejp_2708_:
{
lean_object* v___x_2710_; lean_object* v___x_2712_; 
v___x_2710_ = lean_st_ref_put(v___y_2669_, v___x_2709_);
if (v_isShared_2676_ == 0)
{
lean_ctor_set(v___x_2675_, 0, v___x_2696_);
v___x_2712_ = v___x_2675_;
goto v_reusejp_2711_;
}
else
{
lean_object* v_reuseFailAlloc_2713_; 
v_reuseFailAlloc_2713_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2713_, 0, v___x_2696_);
v___x_2712_ = v_reuseFailAlloc_2713_;
goto v_reusejp_2711_;
}
v_reusejp_2711_:
{
return v___x_2712_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_2664_ = stack[0].m_obj;
lean_object* v_msg_2665_ = stack[1].m_obj;
lean_object* v___y_2666_ = stack[2].m_obj;
lean_object* v___y_2667_ = stack[3].m_obj;
lean_object* v___y_2668_ = stack[4].m_obj;
lean_object* v___y_2669_ = stack[5].m_obj;
lean_object* v_res_2719_;
v_res_2719_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__3___redArg(v_cls_2664_, v_msg_2665_, v___y_2666_, v___y_2667_, v___y_2668_, v___y_2669_);
stack->m_obj
 = v_res_2719_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__3___redArg___boxed(lean_object* v_cls_2720_, lean_object* v_msg_2721_, lean_object* v___y_2722_, lean_object* v___y_2723_, lean_object* v___y_2724_, lean_object* v___y_2725_, lean_object* v___y_2726_){
_start:
{
lean_object* v_res_2727_; 
v_res_2727_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__3___redArg(v_cls_2720_, v_msg_2721_, v___y_2722_, v___y_2723_, v___y_2724_, v___y_2725_);
lean_dec(v___y_2725_);
lean_dec_ref(v___y_2724_);
lean_dec(v___y_2723_);
lean_dec_ref(v___y_2722_);
return v_res_2727_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__2(void){
_start:
{
lean_object* v___x_2733_; lean_object* v___x_2734_; lean_object* v___x_2735_; 
v___x_2733_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__1));
v___x_2734_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__7));
v___x_2735_ = l_Lean_Name_append(v___x_2734_, v___x_2733_);
return v___x_2735_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__4(void){
_start:
{
lean_object* v___x_2737_; lean_object* v___x_2738_; 
v___x_2737_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__3));
v___x_2738_ = l_Lean_stringToMessageData(v___x_2737_);
return v___x_2738_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__6(void){
_start:
{
lean_object* v___x_2740_; lean_object* v___x_2741_; 
v___x_2740_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__5));
v___x_2741_ = l_Lean_stringToMessageData(v___x_2740_);
return v___x_2741_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__8(void){
_start:
{
lean_object* v___x_2743_; lean_object* v___x_2744_; 
v___x_2743_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__7));
v___x_2744_ = l_Lean_stringToMessageData(v___x_2743_);
return v___x_2744_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__10(void){
_start:
{
lean_object* v___x_2746_; lean_object* v___x_2747_; 
v___x_2746_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__9));
v___x_2747_ = l_Lean_stringToMessageData(v___x_2746_);
return v___x_2747_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__12(void){
_start:
{
lean_object* v___x_2749_; lean_object* v___x_2750_; 
v___x_2749_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__11));
v___x_2750_ = l_Lean_stringToMessageData(v___x_2749_);
return v___x_2750_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_CommRing_internalize(lean_object* v_e_2751_, lean_object* v_parent_x3f_2752_, lean_object* v_a_2753_, lean_object* v_a_2754_, lean_object* v_a_2755_, lean_object* v_a_2756_, lean_object* v_a_2757_, lean_object* v_a_2758_, lean_object* v_a_2759_, lean_object* v_a_2760_, lean_object* v_a_2761_, lean_object* v_a_2762_){
_start:
{
lean_object* v___x_2764_; 
v___x_2764_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_2755_);
if (lean_obj_tag(v___x_2764_) == 0)
{
lean_object* v_a_2765_; lean_object* v___x_2767_; uint8_t v_isShared_2768_; uint8_t v_isSharedCheck_3107_; 
v_a_2765_ = lean_ctor_get(v___x_2764_, 0);
v_isSharedCheck_3107_ = !lean_is_exclusive(v___x_2764_);
if (v_isSharedCheck_3107_ == 0)
{
v___x_2767_ = v___x_2764_;
v_isShared_2768_ = v_isSharedCheck_3107_;
goto v_resetjp_2766_;
}
else
{
lean_inc(v_a_2765_);
lean_dec(v___x_2764_);
v___x_2767_ = lean_box(0);
v_isShared_2768_ = v_isSharedCheck_3107_;
goto v_resetjp_2766_;
}
v_resetjp_2766_:
{
uint8_t v_ring_2769_; 
v_ring_2769_ = lean_ctor_get_uint8(v_a_2765_, sizeof(void*)*14 + 21);
lean_dec(v_a_2765_);
if (v_ring_2769_ == 0)
{
lean_object* v___x_2770_; lean_object* v___x_2772_; 
lean_dec(v_parent_x3f_2752_);
lean_dec_ref(v_e_2751_);
v___x_2770_ = lean_box(0);
if (v_isShared_2768_ == 0)
{
lean_ctor_set(v___x_2767_, 0, v___x_2770_);
v___x_2772_ = v___x_2767_;
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
else
{
uint8_t v___x_2774_; 
v___x_2774_ = l_Lean_Meta_Grind_Arith_isIntModuleVirtualParent(v_parent_x3f_2752_);
if (v___x_2774_ == 0)
{
lean_object* v___x_2775_; 
lean_del_object(v___x_2767_);
lean_inc_ref(v_e_2751_);
v___x_2775_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeInv(v_e_2751_, v_a_2753_, v_a_2754_, v_a_2755_, v_a_2756_, v_a_2757_, v_a_2758_, v_a_2759_, v_a_2760_, v_a_2761_, v_a_2762_);
if (lean_obj_tag(v___x_2775_) == 0)
{
lean_object* v_a_2776_; lean_object* v___x_2778_; uint8_t v_isShared_2779_; uint8_t v_isSharedCheck_3094_; 
v_a_2776_ = lean_ctor_get(v___x_2775_, 0);
v_isSharedCheck_3094_ = !lean_is_exclusive(v___x_2775_);
if (v_isSharedCheck_3094_ == 0)
{
v___x_2778_ = v___x_2775_;
v_isShared_2779_ = v_isSharedCheck_3094_;
goto v_resetjp_2777_;
}
else
{
lean_inc(v_a_2776_);
lean_dec(v___x_2775_);
v___x_2778_ = lean_box(0);
v_isShared_2779_ = v_isSharedCheck_3094_;
goto v_resetjp_2777_;
}
v_resetjp_2777_:
{
uint8_t v___x_2780_; 
v___x_2780_ = lean_unbox(v_a_2776_);
lean_dec(v_a_2776_);
if (v___x_2780_ == 0)
{
lean_object* v___x_2781_; 
lean_inc_ref(v_e_2751_);
v___x_2781_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f(v_e_2751_);
if (lean_obj_tag(v___x_2781_) == 1)
{
lean_object* v_val_2782_; uint8_t v___x_2783_; 
v_val_2782_ = lean_ctor_get(v___x_2781_, 0);
lean_inc(v_val_2782_);
lean_dec_ref_known(v___x_2781_, 1);
v___x_2783_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isForbiddenParent(v_parent_x3f_2752_);
if (v___x_2783_ == 0)
{
lean_object* v___x_2784_; 
lean_del_object(v___x_2778_);
lean_inc(v_val_2782_);
v___x_2784_ = l_Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f___redArg(v_val_2782_, v_a_2757_, v_a_2758_, v_a_2759_, v_a_2760_, v_a_2761_, v_a_2762_);
if (lean_obj_tag(v___x_2784_) == 0)
{
lean_object* v_a_2785_; 
v_a_2785_ = lean_ctor_get(v___x_2784_, 0);
lean_inc(v_a_2785_);
lean_dec_ref_known(v___x_2784_, 1);
if (lean_obj_tag(v_a_2785_) == 1)
{
lean_object* v_val_2786_; lean_object* v___x_2787_; lean_object* v___x_2788_; 
lean_dec(v_val_2782_);
v_val_2786_ = lean_ctor_get(v_a_2785_, 0);
lean_inc_n(v_val_2786_, 2);
lean_dec_ref_known(v_a_2785_, 1);
v___x_2787_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2787_, 0, v_val_2786_);
lean_ctor_set_uint8(v___x_2787_, sizeof(void*)*1, v___x_2783_);
lean_inc_ref(v_e_2751_);
v___x_2788_ = l_Lean_Meta_Grind_Arith_CommRing_reify_x3f(v_e_2751_, v_ring_2769_, v___x_2787_, v_a_2753_, v_a_2754_, v_a_2755_, v_a_2756_, v_a_2757_, v_a_2758_, v_a_2759_, v_a_2760_, v_a_2761_, v_a_2762_);
if (lean_obj_tag(v___x_2788_) == 0)
{
lean_object* v_a_2789_; lean_object* v___x_2791_; uint8_t v_isShared_2792_; uint8_t v_isSharedCheck_2841_; 
v_a_2789_ = lean_ctor_get(v___x_2788_, 0);
v_isSharedCheck_2841_ = !lean_is_exclusive(v___x_2788_);
if (v_isSharedCheck_2841_ == 0)
{
v___x_2791_ = v___x_2788_;
v_isShared_2792_ = v_isSharedCheck_2841_;
goto v_resetjp_2790_;
}
else
{
lean_inc(v_a_2789_);
lean_dec(v___x_2788_);
v___x_2791_ = lean_box(0);
v_isShared_2792_ = v_isSharedCheck_2841_;
goto v_resetjp_2790_;
}
v_resetjp_2790_:
{
if (lean_obj_tag(v_a_2789_) == 1)
{
lean_object* v_toCold_2793_; lean_object* v_options_2794_; lean_object* v_val_2795_; lean_object* v_inheritedTraceOptions_2796_; uint8_t v_hasTrace_2797_; lean_object* v___f_2798_; lean_object* v___y_2800_; lean_object* v___y_2801_; lean_object* v___y_2802_; lean_object* v___y_2803_; lean_object* v___y_2804_; lean_object* v___y_2805_; lean_object* v___y_2806_; lean_object* v___y_2807_; lean_object* v___y_2808_; lean_object* v___y_2809_; lean_object* v___y_2810_; 
lean_del_object(v___x_2791_);
v_toCold_2793_ = lean_ctor_get(v_a_2761_, 0);
v_options_2794_ = lean_ctor_get(v_toCold_2793_, 2);
v_val_2795_ = lean_ctor_get(v_a_2789_, 0);
lean_inc(v_val_2795_);
lean_dec_ref_known(v_a_2789_, 1);
v_inheritedTraceOptions_2796_ = lean_ctor_get(v_toCold_2793_, 11);
v_hasTrace_2797_ = lean_ctor_get_uint8(v_options_2794_, sizeof(void*)*1);
lean_inc_ref(v_e_2751_);
v___f_2798_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_internalize___lam__0), 3, 2);
lean_closure_set(v___f_2798_, 0, v_e_2751_);
lean_closure_set(v___f_2798_, 1, v_val_2795_);
if (v_hasTrace_2797_ == 0)
{
lean_dec(v_val_2786_);
v___y_2800_ = v___x_2787_;
v___y_2801_ = v_a_2753_;
v___y_2802_ = v_a_2754_;
v___y_2803_ = v_a_2755_;
v___y_2804_ = v_a_2756_;
v___y_2805_ = v_a_2757_;
v___y_2806_ = v_a_2758_;
v___y_2807_ = v_a_2759_;
v___y_2808_ = v_a_2760_;
v___y_2809_ = v_a_2761_;
v___y_2810_ = v_a_2762_;
goto v___jp_2799_;
}
else
{
lean_object* v___x_2816_; lean_object* v___x_2817_; uint8_t v___x_2818_; 
v___x_2816_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__1));
v___x_2817_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__2, &l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__2_once, _init_l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__2);
v___x_2818_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2796_, v_options_2794_, v___x_2817_);
if (v___x_2818_ == 0)
{
lean_dec(v_val_2786_);
v___y_2800_ = v___x_2787_;
v___y_2801_ = v_a_2753_;
v___y_2802_ = v_a_2754_;
v___y_2803_ = v_a_2755_;
v___y_2804_ = v_a_2756_;
v___y_2805_ = v_a_2757_;
v___y_2806_ = v_a_2758_;
v___y_2807_ = v_a_2759_;
v___y_2808_ = v_a_2760_;
v___y_2809_ = v_a_2761_;
v___y_2810_ = v_a_2762_;
goto v___jp_2799_;
}
else
{
lean_object* v___x_2819_; 
v___x_2819_ = l_Lean_Meta_Grind_updateLastTag(v_a_2753_, v_a_2754_, v_a_2755_, v_a_2756_, v_a_2757_, v_a_2758_, v_a_2759_, v_a_2760_, v_a_2761_, v_a_2762_);
if (lean_obj_tag(v___x_2819_) == 0)
{
lean_object* v___x_2821_; uint8_t v_isShared_2822_; uint8_t v_isSharedCheck_2835_; 
v_isSharedCheck_2835_ = !lean_is_exclusive(v___x_2819_);
if (v_isSharedCheck_2835_ == 0)
{
lean_object* v_unused_2836_; 
v_unused_2836_ = lean_ctor_get(v___x_2819_, 0);
lean_dec(v_unused_2836_);
v___x_2821_ = v___x_2819_;
v_isShared_2822_ = v_isSharedCheck_2835_;
goto v_resetjp_2820_;
}
else
{
lean_dec(v___x_2819_);
v___x_2821_ = lean_box(0);
v_isShared_2822_ = v_isSharedCheck_2835_;
goto v_resetjp_2820_;
}
v_resetjp_2820_:
{
lean_object* v___x_2823_; lean_object* v___x_2824_; lean_object* v___x_2826_; 
v___x_2823_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__4, &l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__4_once, _init_l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__4);
v___x_2824_ = l_Nat_reprFast(v_val_2786_);
if (v_isShared_2822_ == 0)
{
lean_ctor_set_tag(v___x_2821_, 3);
lean_ctor_set(v___x_2821_, 0, v___x_2824_);
v___x_2826_ = v___x_2821_;
goto v_reusejp_2825_;
}
else
{
lean_object* v_reuseFailAlloc_2834_; 
v_reuseFailAlloc_2834_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2834_, 0, v___x_2824_);
v___x_2826_ = v_reuseFailAlloc_2834_;
goto v_reusejp_2825_;
}
v_reusejp_2825_:
{
lean_object* v___x_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; lean_object* v___x_2830_; lean_object* v___x_2831_; lean_object* v___x_2832_; lean_object* v___x_2833_; 
v___x_2827_ = l_Lean_MessageData_ofFormat(v___x_2826_);
v___x_2828_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2828_, 0, v___x_2823_);
lean_ctor_set(v___x_2828_, 1, v___x_2827_);
v___x_2829_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__6, &l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__6_once, _init_l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__6);
v___x_2830_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2830_, 0, v___x_2828_);
lean_ctor_set(v___x_2830_, 1, v___x_2829_);
lean_inc_ref(v_e_2751_);
v___x_2831_ = l_Lean_MessageData_ofExpr(v_e_2751_);
v___x_2832_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2832_, 0, v___x_2830_);
lean_ctor_set(v___x_2832_, 1, v___x_2831_);
v___x_2833_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg(v___x_2816_, v___x_2832_, v_a_2759_, v_a_2760_, v_a_2761_, v_a_2762_);
if (lean_obj_tag(v___x_2833_) == 0)
{
lean_dec_ref_known(v___x_2833_, 1);
v___y_2800_ = v___x_2787_;
v___y_2801_ = v_a_2753_;
v___y_2802_ = v_a_2754_;
v___y_2803_ = v_a_2755_;
v___y_2804_ = v_a_2756_;
v___y_2805_ = v_a_2757_;
v___y_2806_ = v_a_2758_;
v___y_2807_ = v_a_2759_;
v___y_2808_ = v_a_2760_;
v___y_2809_ = v_a_2761_;
v___y_2810_ = v_a_2762_;
goto v___jp_2799_;
}
else
{
lean_dec_ref(v___f_2798_);
lean_dec_ref_known(v___x_2787_, 1);
lean_dec_ref(v_e_2751_);
return v___x_2833_;
}
}
}
}
else
{
lean_dec_ref(v___f_2798_);
lean_dec_ref_known(v___x_2787_, 1);
lean_dec(v_val_2786_);
lean_dec_ref(v_e_2751_);
return v___x_2819_;
}
}
}
v___jp_2799_:
{
lean_object* v___x_2811_; 
lean_inc_ref(v_e_2751_);
v___x_2811_ = l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg(v_e_2751_, v___y_2800_, v___y_2801_, v___y_2805_, v___y_2806_, v___y_2807_, v___y_2808_, v___y_2809_, v___y_2810_);
if (lean_obj_tag(v___x_2811_) == 0)
{
lean_object* v___x_2812_; lean_object* v___x_2813_; 
lean_dec_ref_known(v___x_2811_, 1);
v___x_2812_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_2813_ = l_Lean_Meta_Grind_SolverExtension_markTerm___redArg(v___x_2812_, v_e_2751_, v___y_2801_, v___y_2802_, v___y_2803_, v___y_2804_, v___y_2805_, v___y_2806_, v___y_2807_, v___y_2808_, v___y_2809_, v___y_2810_);
if (lean_obj_tag(v___x_2813_) == 0)
{
lean_object* v___x_2814_; 
lean_dec_ref_known(v___x_2813_, 1);
v___x_2814_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRingState___redArg(v___f_2798_, v___y_2800_, v___y_2801_);
if (lean_obj_tag(v___x_2814_) == 0)
{
lean_object* v___x_2815_; 
lean_dec_ref_known(v___x_2814_, 1);
v___x_2815_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars(v___y_2800_, v___y_2801_, v___y_2802_, v___y_2803_, v___y_2804_, v___y_2805_, v___y_2806_, v___y_2807_, v___y_2808_, v___y_2809_, v___y_2810_);
lean_dec_ref(v___y_2800_);
return v___x_2815_;
}
else
{
lean_dec_ref(v___y_2800_);
return v___x_2814_;
}
}
else
{
lean_dec_ref(v___y_2800_);
lean_dec_ref(v___f_2798_);
return v___x_2813_;
}
}
else
{
lean_dec_ref(v___y_2800_);
lean_dec_ref(v___f_2798_);
lean_dec_ref(v_e_2751_);
return v___x_2811_;
}
}
}
else
{
lean_object* v___x_2837_; lean_object* v___x_2839_; 
lean_dec(v_a_2789_);
lean_dec_ref_known(v___x_2787_, 1);
lean_dec(v_val_2786_);
lean_dec_ref(v_e_2751_);
v___x_2837_ = lean_box(0);
if (v_isShared_2792_ == 0)
{
lean_ctor_set(v___x_2791_, 0, v___x_2837_);
v___x_2839_ = v___x_2791_;
goto v_reusejp_2838_;
}
else
{
lean_object* v_reuseFailAlloc_2840_; 
v_reuseFailAlloc_2840_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2840_, 0, v___x_2837_);
v___x_2839_ = v_reuseFailAlloc_2840_;
goto v_reusejp_2838_;
}
v_reusejp_2838_:
{
return v___x_2839_;
}
}
}
}
else
{
lean_object* v_a_2842_; lean_object* v___x_2844_; uint8_t v_isShared_2845_; uint8_t v_isSharedCheck_2849_; 
lean_dec_ref_known(v___x_2787_, 1);
lean_dec(v_val_2786_);
lean_dec_ref(v_e_2751_);
v_a_2842_ = lean_ctor_get(v___x_2788_, 0);
v_isSharedCheck_2849_ = !lean_is_exclusive(v___x_2788_);
if (v_isSharedCheck_2849_ == 0)
{
v___x_2844_ = v___x_2788_;
v_isShared_2845_ = v_isSharedCheck_2849_;
goto v_resetjp_2843_;
}
else
{
lean_inc(v_a_2842_);
lean_dec(v___x_2788_);
v___x_2844_ = lean_box(0);
v_isShared_2845_ = v_isSharedCheck_2849_;
goto v_resetjp_2843_;
}
v_resetjp_2843_:
{
lean_object* v___x_2847_; 
if (v_isShared_2845_ == 0)
{
v___x_2847_ = v___x_2844_;
goto v_reusejp_2846_;
}
else
{
lean_object* v_reuseFailAlloc_2848_; 
v_reuseFailAlloc_2848_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2848_, 0, v_a_2842_);
v___x_2847_ = v_reuseFailAlloc_2848_;
goto v_reusejp_2846_;
}
v_reusejp_2846_:
{
return v___x_2847_;
}
}
}
}
else
{
lean_object* v___x_2850_; 
lean_dec(v_a_2785_);
lean_inc(v_val_2782_);
v___x_2850_ = l_Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f___redArg(v_val_2782_, v_a_2757_, v_a_2758_, v_a_2759_, v_a_2760_, v_a_2761_, v_a_2762_);
if (lean_obj_tag(v___x_2850_) == 0)
{
lean_object* v_a_2851_; 
v_a_2851_ = lean_ctor_get(v___x_2850_, 0);
lean_inc(v_a_2851_);
lean_dec_ref_known(v___x_2850_, 1);
if (lean_obj_tag(v_a_2851_) == 1)
{
lean_object* v_val_2852_; lean_object* v___x_2853_; 
lean_dec(v_val_2782_);
v_val_2852_ = lean_ctor_get(v_a_2851_, 0);
lean_inc(v_val_2852_);
lean_dec_ref_known(v_a_2851_, 1);
lean_inc_ref(v_e_2751_);
v___x_2853_ = l_Lean_Meta_Grind_Arith_CommRing_sreify_x3f(v_e_2751_, v_val_2852_, v_a_2753_, v_a_2754_, v_a_2755_, v_a_2756_, v_a_2757_, v_a_2758_, v_a_2759_, v_a_2760_, v_a_2761_, v_a_2762_);
if (lean_obj_tag(v___x_2853_) == 0)
{
lean_object* v_a_2854_; lean_object* v___x_2856_; uint8_t v_isShared_2857_; uint8_t v_isSharedCheck_2905_; 
v_a_2854_ = lean_ctor_get(v___x_2853_, 0);
v_isSharedCheck_2905_ = !lean_is_exclusive(v___x_2853_);
if (v_isSharedCheck_2905_ == 0)
{
v___x_2856_ = v___x_2853_;
v_isShared_2857_ = v_isSharedCheck_2905_;
goto v_resetjp_2855_;
}
else
{
lean_inc(v_a_2854_);
lean_dec(v___x_2853_);
v___x_2856_ = lean_box(0);
v_isShared_2857_ = v_isSharedCheck_2905_;
goto v_resetjp_2855_;
}
v_resetjp_2855_:
{
if (lean_obj_tag(v_a_2854_) == 1)
{
lean_object* v_toCold_2858_; lean_object* v_options_2859_; lean_object* v_val_2860_; lean_object* v_inheritedTraceOptions_2861_; uint8_t v_hasTrace_2862_; lean_object* v___f_2863_; lean_object* v___y_2865_; lean_object* v___y_2866_; lean_object* v___y_2867_; lean_object* v___y_2868_; lean_object* v___y_2869_; lean_object* v___y_2870_; lean_object* v___y_2871_; lean_object* v___y_2872_; lean_object* v___y_2873_; lean_object* v___y_2874_; lean_object* v___y_2875_; 
lean_del_object(v___x_2856_);
v_toCold_2858_ = lean_ctor_get(v_a_2761_, 0);
v_options_2859_ = lean_ctor_get(v_toCold_2858_, 2);
v_val_2860_ = lean_ctor_get(v_a_2854_, 0);
lean_inc(v_val_2860_);
lean_dec_ref_known(v_a_2854_, 1);
v_inheritedTraceOptions_2861_ = lean_ctor_get(v_toCold_2858_, 11);
v_hasTrace_2862_ = lean_ctor_get_uint8(v_options_2859_, sizeof(void*)*1);
lean_inc_ref(v_e_2751_);
v___f_2863_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_internalize___lam__1), 3, 2);
lean_closure_set(v___f_2863_, 0, v_e_2751_);
lean_closure_set(v___f_2863_, 1, v_val_2860_);
if (v_hasTrace_2862_ == 0)
{
v___y_2865_ = v_val_2852_;
v___y_2866_ = v_a_2753_;
v___y_2867_ = v_a_2754_;
v___y_2868_ = v_a_2755_;
v___y_2869_ = v_a_2756_;
v___y_2870_ = v_a_2757_;
v___y_2871_ = v_a_2758_;
v___y_2872_ = v_a_2759_;
v___y_2873_ = v_a_2760_;
v___y_2874_ = v_a_2761_;
v___y_2875_ = v_a_2762_;
goto v___jp_2864_;
}
else
{
lean_object* v___x_2880_; lean_object* v___x_2881_; uint8_t v___x_2882_; 
v___x_2880_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__1));
v___x_2881_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__2, &l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__2_once, _init_l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__2);
v___x_2882_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2861_, v_options_2859_, v___x_2881_);
if (v___x_2882_ == 0)
{
v___y_2865_ = v_val_2852_;
v___y_2866_ = v_a_2753_;
v___y_2867_ = v_a_2754_;
v___y_2868_ = v_a_2755_;
v___y_2869_ = v_a_2756_;
v___y_2870_ = v_a_2757_;
v___y_2871_ = v_a_2758_;
v___y_2872_ = v_a_2759_;
v___y_2873_ = v_a_2760_;
v___y_2874_ = v_a_2761_;
v___y_2875_ = v_a_2762_;
goto v___jp_2864_;
}
else
{
lean_object* v___x_2883_; 
v___x_2883_ = l_Lean_Meta_Grind_updateLastTag(v_a_2753_, v_a_2754_, v_a_2755_, v_a_2756_, v_a_2757_, v_a_2758_, v_a_2759_, v_a_2760_, v_a_2761_, v_a_2762_);
if (lean_obj_tag(v___x_2883_) == 0)
{
lean_object* v___x_2885_; uint8_t v_isShared_2886_; uint8_t v_isSharedCheck_2899_; 
v_isSharedCheck_2899_ = !lean_is_exclusive(v___x_2883_);
if (v_isSharedCheck_2899_ == 0)
{
lean_object* v_unused_2900_; 
v_unused_2900_ = lean_ctor_get(v___x_2883_, 0);
lean_dec(v_unused_2900_);
v___x_2885_ = v___x_2883_;
v_isShared_2886_ = v_isSharedCheck_2899_;
goto v_resetjp_2884_;
}
else
{
lean_dec(v___x_2883_);
v___x_2885_ = lean_box(0);
v_isShared_2886_ = v_isSharedCheck_2899_;
goto v_resetjp_2884_;
}
v_resetjp_2884_:
{
lean_object* v___x_2887_; lean_object* v___x_2888_; lean_object* v___x_2890_; 
v___x_2887_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__8, &l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__8_once, _init_l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__8);
lean_inc(v_val_2852_);
v___x_2888_ = l_Nat_reprFast(v_val_2852_);
if (v_isShared_2886_ == 0)
{
lean_ctor_set_tag(v___x_2885_, 3);
lean_ctor_set(v___x_2885_, 0, v___x_2888_);
v___x_2890_ = v___x_2885_;
goto v_reusejp_2889_;
}
else
{
lean_object* v_reuseFailAlloc_2898_; 
v_reuseFailAlloc_2898_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2898_, 0, v___x_2888_);
v___x_2890_ = v_reuseFailAlloc_2898_;
goto v_reusejp_2889_;
}
v_reusejp_2889_:
{
lean_object* v___x_2891_; lean_object* v___x_2892_; lean_object* v___x_2893_; lean_object* v___x_2894_; lean_object* v___x_2895_; lean_object* v___x_2896_; lean_object* v___x_2897_; 
v___x_2891_ = l_Lean_MessageData_ofFormat(v___x_2890_);
v___x_2892_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2892_, 0, v___x_2887_);
lean_ctor_set(v___x_2892_, 1, v___x_2891_);
v___x_2893_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__6, &l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__6_once, _init_l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__6);
v___x_2894_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2894_, 0, v___x_2892_);
lean_ctor_set(v___x_2894_, 1, v___x_2893_);
lean_inc_ref(v_e_2751_);
v___x_2895_ = l_Lean_MessageData_ofExpr(v_e_2751_);
v___x_2896_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2896_, 0, v___x_2894_);
lean_ctor_set(v___x_2896_, 1, v___x_2895_);
v___x_2897_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__1___redArg(v___x_2880_, v___x_2896_, v_a_2759_, v_a_2760_, v_a_2761_, v_a_2762_);
if (lean_obj_tag(v___x_2897_) == 0)
{
lean_dec_ref_known(v___x_2897_, 1);
v___y_2865_ = v_val_2852_;
v___y_2866_ = v_a_2753_;
v___y_2867_ = v_a_2754_;
v___y_2868_ = v_a_2755_;
v___y_2869_ = v_a_2756_;
v___y_2870_ = v_a_2757_;
v___y_2871_ = v_a_2758_;
v___y_2872_ = v_a_2759_;
v___y_2873_ = v_a_2760_;
v___y_2874_ = v_a_2761_;
v___y_2875_ = v_a_2762_;
goto v___jp_2864_;
}
else
{
lean_dec_ref(v___f_2863_);
lean_dec(v_val_2852_);
lean_dec_ref(v_e_2751_);
return v___x_2897_;
}
}
}
}
else
{
lean_dec_ref(v___f_2863_);
lean_dec(v_val_2852_);
lean_dec_ref(v_e_2751_);
return v___x_2883_;
}
}
}
v___jp_2864_:
{
lean_object* v___x_2876_; 
lean_inc_ref(v_e_2751_);
v___x_2876_ = l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg(v_e_2751_, v___y_2865_, v___y_2866_, v___y_2870_, v___y_2871_, v___y_2872_, v___y_2873_, v___y_2874_, v___y_2875_);
if (lean_obj_tag(v___x_2876_) == 0)
{
lean_object* v___x_2877_; lean_object* v___x_2878_; 
lean_dec_ref_known(v___x_2876_, 1);
v___x_2877_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_2878_ = l_Lean_Meta_Grind_SolverExtension_markTerm___redArg(v___x_2877_, v_e_2751_, v___y_2866_, v___y_2867_, v___y_2868_, v___y_2869_, v___y_2870_, v___y_2871_, v___y_2872_, v___y_2873_, v___y_2874_, v___y_2875_);
if (lean_obj_tag(v___x_2878_) == 0)
{
lean_object* v___x_2879_; 
lean_dec_ref_known(v___x_2878_, 1);
v___x_2879_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifySemiringState___redArg(v___f_2863_, v___y_2865_, v___y_2866_);
lean_dec(v___y_2865_);
return v___x_2879_;
}
else
{
lean_dec(v___y_2865_);
lean_dec_ref(v___f_2863_);
return v___x_2878_;
}
}
else
{
lean_dec(v___y_2865_);
lean_dec_ref(v___f_2863_);
lean_dec_ref(v_e_2751_);
return v___x_2876_;
}
}
}
else
{
lean_object* v___x_2901_; lean_object* v___x_2903_; 
lean_dec(v_a_2854_);
lean_dec(v_val_2852_);
lean_dec_ref(v_e_2751_);
v___x_2901_ = lean_box(0);
if (v_isShared_2857_ == 0)
{
lean_ctor_set(v___x_2856_, 0, v___x_2901_);
v___x_2903_ = v___x_2856_;
goto v_reusejp_2902_;
}
else
{
lean_object* v_reuseFailAlloc_2904_; 
v_reuseFailAlloc_2904_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2904_, 0, v___x_2901_);
v___x_2903_ = v_reuseFailAlloc_2904_;
goto v_reusejp_2902_;
}
v_reusejp_2902_:
{
return v___x_2903_;
}
}
}
}
else
{
lean_object* v_a_2906_; lean_object* v___x_2908_; uint8_t v_isShared_2909_; uint8_t v_isSharedCheck_2913_; 
lean_dec(v_val_2852_);
lean_dec_ref(v_e_2751_);
v_a_2906_ = lean_ctor_get(v___x_2853_, 0);
v_isSharedCheck_2913_ = !lean_is_exclusive(v___x_2853_);
if (v_isSharedCheck_2913_ == 0)
{
v___x_2908_ = v___x_2853_;
v_isShared_2909_ = v_isSharedCheck_2913_;
goto v_resetjp_2907_;
}
else
{
lean_inc(v_a_2906_);
lean_dec(v___x_2853_);
v___x_2908_ = lean_box(0);
v_isShared_2909_ = v_isSharedCheck_2913_;
goto v_resetjp_2907_;
}
v_resetjp_2907_:
{
lean_object* v___x_2911_; 
if (v_isShared_2909_ == 0)
{
v___x_2911_ = v___x_2908_;
goto v_reusejp_2910_;
}
else
{
lean_object* v_reuseFailAlloc_2912_; 
v_reuseFailAlloc_2912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2912_, 0, v_a_2906_);
v___x_2911_ = v_reuseFailAlloc_2912_;
goto v_reusejp_2910_;
}
v_reusejp_2910_:
{
return v___x_2911_;
}
}
}
}
else
{
lean_object* v___x_2914_; 
lean_dec(v_a_2851_);
lean_inc(v_val_2782_);
v___x_2914_ = l_Lean_Meta_Grind_Arith_CommRing_getNonCommRingId_x3f___redArg(v_val_2782_, v_a_2757_, v_a_2758_, v_a_2759_, v_a_2760_, v_a_2761_, v_a_2762_);
if (lean_obj_tag(v___x_2914_) == 0)
{
lean_object* v_a_2915_; 
v_a_2915_ = lean_ctor_get(v___x_2914_, 0);
lean_inc(v_a_2915_);
lean_dec_ref_known(v___x_2914_, 1);
if (lean_obj_tag(v_a_2915_) == 1)
{
lean_object* v_val_2916_; lean_object* v___x_2917_; 
lean_dec(v_val_2782_);
v_val_2916_ = lean_ctor_get(v_a_2915_, 0);
lean_inc(v_val_2916_);
lean_dec_ref_known(v_a_2915_, 1);
lean_inc_ref(v_e_2751_);
v___x_2917_ = l_Lean_Meta_Grind_Arith_CommRing_ncreify_x3f(v_e_2751_, v_ring_2769_, v_val_2916_, v_a_2753_, v_a_2754_, v_a_2755_, v_a_2756_, v_a_2757_, v_a_2758_, v_a_2759_, v_a_2760_, v_a_2761_, v_a_2762_);
if (lean_obj_tag(v___x_2917_) == 0)
{
lean_object* v_a_2918_; lean_object* v___x_2920_; uint8_t v_isShared_2921_; uint8_t v_isSharedCheck_2969_; 
v_a_2918_ = lean_ctor_get(v___x_2917_, 0);
v_isSharedCheck_2969_ = !lean_is_exclusive(v___x_2917_);
if (v_isSharedCheck_2969_ == 0)
{
v___x_2920_ = v___x_2917_;
v_isShared_2921_ = v_isSharedCheck_2969_;
goto v_resetjp_2919_;
}
else
{
lean_inc(v_a_2918_);
lean_dec(v___x_2917_);
v___x_2920_ = lean_box(0);
v_isShared_2921_ = v_isSharedCheck_2969_;
goto v_resetjp_2919_;
}
v_resetjp_2919_:
{
if (lean_obj_tag(v_a_2918_) == 1)
{
lean_object* v_toCold_2922_; lean_object* v_options_2923_; lean_object* v_val_2924_; lean_object* v_inheritedTraceOptions_2925_; uint8_t v_hasTrace_2926_; lean_object* v___f_2927_; lean_object* v___y_2929_; lean_object* v___y_2930_; lean_object* v___y_2931_; lean_object* v___y_2932_; lean_object* v___y_2933_; lean_object* v___y_2934_; lean_object* v___y_2935_; lean_object* v___y_2936_; lean_object* v___y_2937_; lean_object* v___y_2938_; lean_object* v___y_2939_; 
lean_del_object(v___x_2920_);
v_toCold_2922_ = lean_ctor_get(v_a_2761_, 0);
v_options_2923_ = lean_ctor_get(v_toCold_2922_, 2);
v_val_2924_ = lean_ctor_get(v_a_2918_, 0);
lean_inc(v_val_2924_);
lean_dec_ref_known(v_a_2918_, 1);
v_inheritedTraceOptions_2925_ = lean_ctor_get(v_toCold_2922_, 11);
v_hasTrace_2926_ = lean_ctor_get_uint8(v_options_2923_, sizeof(void*)*1);
lean_inc_ref(v_e_2751_);
v___f_2927_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_internalize___lam__2), 3, 2);
lean_closure_set(v___f_2927_, 0, v_e_2751_);
lean_closure_set(v___f_2927_, 1, v_val_2924_);
if (v_hasTrace_2926_ == 0)
{
v___y_2929_ = v_val_2916_;
v___y_2930_ = v_a_2753_;
v___y_2931_ = v_a_2754_;
v___y_2932_ = v_a_2755_;
v___y_2933_ = v_a_2756_;
v___y_2934_ = v_a_2757_;
v___y_2935_ = v_a_2758_;
v___y_2936_ = v_a_2759_;
v___y_2937_ = v_a_2760_;
v___y_2938_ = v_a_2761_;
v___y_2939_ = v_a_2762_;
goto v___jp_2928_;
}
else
{
lean_object* v___x_2944_; lean_object* v___x_2945_; uint8_t v___x_2946_; 
v___x_2944_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__1));
v___x_2945_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__2, &l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__2_once, _init_l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__2);
v___x_2946_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2925_, v_options_2923_, v___x_2945_);
if (v___x_2946_ == 0)
{
v___y_2929_ = v_val_2916_;
v___y_2930_ = v_a_2753_;
v___y_2931_ = v_a_2754_;
v___y_2932_ = v_a_2755_;
v___y_2933_ = v_a_2756_;
v___y_2934_ = v_a_2757_;
v___y_2935_ = v_a_2758_;
v___y_2936_ = v_a_2759_;
v___y_2937_ = v_a_2760_;
v___y_2938_ = v_a_2761_;
v___y_2939_ = v_a_2762_;
goto v___jp_2928_;
}
else
{
lean_object* v___x_2947_; 
v___x_2947_ = l_Lean_Meta_Grind_updateLastTag(v_a_2753_, v_a_2754_, v_a_2755_, v_a_2756_, v_a_2757_, v_a_2758_, v_a_2759_, v_a_2760_, v_a_2761_, v_a_2762_);
if (lean_obj_tag(v___x_2947_) == 0)
{
lean_object* v___x_2949_; uint8_t v_isShared_2950_; uint8_t v_isSharedCheck_2963_; 
v_isSharedCheck_2963_ = !lean_is_exclusive(v___x_2947_);
if (v_isSharedCheck_2963_ == 0)
{
lean_object* v_unused_2964_; 
v_unused_2964_ = lean_ctor_get(v___x_2947_, 0);
lean_dec(v_unused_2964_);
v___x_2949_ = v___x_2947_;
v_isShared_2950_ = v_isSharedCheck_2963_;
goto v_resetjp_2948_;
}
else
{
lean_dec(v___x_2947_);
v___x_2949_ = lean_box(0);
v_isShared_2950_ = v_isSharedCheck_2963_;
goto v_resetjp_2948_;
}
v_resetjp_2948_:
{
lean_object* v___x_2951_; lean_object* v___x_2952_; lean_object* v___x_2954_; 
v___x_2951_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__10, &l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__10_once, _init_l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__10);
lean_inc(v_val_2916_);
v___x_2952_ = l_Nat_reprFast(v_val_2916_);
if (v_isShared_2950_ == 0)
{
lean_ctor_set_tag(v___x_2949_, 3);
lean_ctor_set(v___x_2949_, 0, v___x_2952_);
v___x_2954_ = v___x_2949_;
goto v_reusejp_2953_;
}
else
{
lean_object* v_reuseFailAlloc_2962_; 
v_reuseFailAlloc_2962_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2962_, 0, v___x_2952_);
v___x_2954_ = v_reuseFailAlloc_2962_;
goto v_reusejp_2953_;
}
v_reusejp_2953_:
{
lean_object* v___x_2955_; lean_object* v___x_2956_; lean_object* v___x_2957_; lean_object* v___x_2958_; lean_object* v___x_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; 
v___x_2955_ = l_Lean_MessageData_ofFormat(v___x_2954_);
v___x_2956_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2956_, 0, v___x_2951_);
lean_ctor_set(v___x_2956_, 1, v___x_2955_);
v___x_2957_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__6, &l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__6_once, _init_l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__6);
v___x_2958_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2958_, 0, v___x_2956_);
lean_ctor_set(v___x_2958_, 1, v___x_2957_);
lean_inc_ref(v_e_2751_);
v___x_2959_ = l_Lean_MessageData_ofExpr(v_e_2751_);
v___x_2960_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2960_, 0, v___x_2958_);
lean_ctor_set(v___x_2960_, 1, v___x_2959_);
v___x_2961_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__2___redArg(v___x_2944_, v___x_2960_, v_a_2759_, v_a_2760_, v_a_2761_, v_a_2762_);
if (lean_obj_tag(v___x_2961_) == 0)
{
lean_dec_ref_known(v___x_2961_, 1);
v___y_2929_ = v_val_2916_;
v___y_2930_ = v_a_2753_;
v___y_2931_ = v_a_2754_;
v___y_2932_ = v_a_2755_;
v___y_2933_ = v_a_2756_;
v___y_2934_ = v_a_2757_;
v___y_2935_ = v_a_2758_;
v___y_2936_ = v_a_2759_;
v___y_2937_ = v_a_2760_;
v___y_2938_ = v_a_2761_;
v___y_2939_ = v_a_2762_;
goto v___jp_2928_;
}
else
{
lean_dec_ref(v___f_2927_);
lean_dec(v_val_2916_);
lean_dec_ref(v_e_2751_);
return v___x_2961_;
}
}
}
}
else
{
lean_dec_ref(v___f_2927_);
lean_dec(v_val_2916_);
lean_dec_ref(v_e_2751_);
return v___x_2947_;
}
}
}
v___jp_2928_:
{
lean_object* v___x_2940_; 
lean_inc_ref(v_e_2751_);
v___x_2940_ = l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId___redArg(v_e_2751_, v___y_2929_, v___y_2930_, v___y_2934_, v___y_2935_, v___y_2936_, v___y_2937_, v___y_2938_, v___y_2939_);
if (lean_obj_tag(v___x_2940_) == 0)
{
lean_object* v___x_2941_; lean_object* v___x_2942_; 
lean_dec_ref_known(v___x_2940_, 1);
v___x_2941_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_2942_ = l_Lean_Meta_Grind_SolverExtension_markTerm___redArg(v___x_2941_, v_e_2751_, v___y_2930_, v___y_2931_, v___y_2932_, v___y_2933_, v___y_2934_, v___y_2935_, v___y_2936_, v___y_2937_, v___y_2938_, v___y_2939_);
if (lean_obj_tag(v___x_2942_) == 0)
{
lean_object* v___x_2943_; 
lean_dec_ref_known(v___x_2942_, 1);
v___x_2943_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_modifyRingState___redArg(v___f_2927_, v___y_2929_, v___y_2930_);
lean_dec(v___y_2929_);
return v___x_2943_;
}
else
{
lean_dec(v___y_2929_);
lean_dec_ref(v___f_2927_);
return v___x_2942_;
}
}
else
{
lean_dec(v___y_2929_);
lean_dec_ref(v___f_2927_);
lean_dec_ref(v_e_2751_);
return v___x_2940_;
}
}
}
else
{
lean_object* v___x_2965_; lean_object* v___x_2967_; 
lean_dec(v_a_2918_);
lean_dec(v_val_2916_);
lean_dec_ref(v_e_2751_);
v___x_2965_ = lean_box(0);
if (v_isShared_2921_ == 0)
{
lean_ctor_set(v___x_2920_, 0, v___x_2965_);
v___x_2967_ = v___x_2920_;
goto v_reusejp_2966_;
}
else
{
lean_object* v_reuseFailAlloc_2968_; 
v_reuseFailAlloc_2968_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2968_, 0, v___x_2965_);
v___x_2967_ = v_reuseFailAlloc_2968_;
goto v_reusejp_2966_;
}
v_reusejp_2966_:
{
return v___x_2967_;
}
}
}
}
else
{
lean_object* v_a_2970_; lean_object* v___x_2972_; uint8_t v_isShared_2973_; uint8_t v_isSharedCheck_2977_; 
lean_dec(v_val_2916_);
lean_dec_ref(v_e_2751_);
v_a_2970_ = lean_ctor_get(v___x_2917_, 0);
v_isSharedCheck_2977_ = !lean_is_exclusive(v___x_2917_);
if (v_isSharedCheck_2977_ == 0)
{
v___x_2972_ = v___x_2917_;
v_isShared_2973_ = v_isSharedCheck_2977_;
goto v_resetjp_2971_;
}
else
{
lean_inc(v_a_2970_);
lean_dec(v___x_2917_);
v___x_2972_ = lean_box(0);
v_isShared_2973_ = v_isSharedCheck_2977_;
goto v_resetjp_2971_;
}
v_resetjp_2971_:
{
lean_object* v___x_2975_; 
if (v_isShared_2973_ == 0)
{
v___x_2975_ = v___x_2972_;
goto v_reusejp_2974_;
}
else
{
lean_object* v_reuseFailAlloc_2976_; 
v_reuseFailAlloc_2976_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2976_, 0, v_a_2970_);
v___x_2975_ = v_reuseFailAlloc_2976_;
goto v_reusejp_2974_;
}
v_reusejp_2974_:
{
return v___x_2975_;
}
}
}
}
else
{
lean_object* v___x_2978_; 
lean_dec(v_a_2915_);
v___x_2978_ = l_Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f___redArg(v_val_2782_, v_a_2757_, v_a_2758_, v_a_2759_, v_a_2760_, v_a_2761_, v_a_2762_);
if (lean_obj_tag(v___x_2978_) == 0)
{
lean_object* v_a_2979_; lean_object* v___x_2981_; uint8_t v_isShared_2982_; uint8_t v_isSharedCheck_3049_; 
v_a_2979_ = lean_ctor_get(v___x_2978_, 0);
v_isSharedCheck_3049_ = !lean_is_exclusive(v___x_2978_);
if (v_isSharedCheck_3049_ == 0)
{
v___x_2981_ = v___x_2978_;
v_isShared_2982_ = v_isSharedCheck_3049_;
goto v_resetjp_2980_;
}
else
{
lean_inc(v_a_2979_);
lean_dec(v___x_2978_);
v___x_2981_ = lean_box(0);
v_isShared_2982_ = v_isSharedCheck_3049_;
goto v_resetjp_2980_;
}
v_resetjp_2980_:
{
if (lean_obj_tag(v_a_2979_) == 1)
{
lean_object* v_val_2983_; lean_object* v___x_2984_; 
lean_del_object(v___x_2981_);
v_val_2983_ = lean_ctor_get(v_a_2979_, 0);
lean_inc(v_val_2983_);
lean_dec_ref_known(v_a_2979_, 1);
lean_inc_ref(v_e_2751_);
v___x_2984_ = l_Lean_Meta_Grind_Arith_CommRing_ncsreify_x3f(v_e_2751_, v_val_2983_, v_a_2753_, v_a_2754_, v_a_2755_, v_a_2756_, v_a_2757_, v_a_2758_, v_a_2759_, v_a_2760_, v_a_2761_, v_a_2762_);
if (lean_obj_tag(v___x_2984_) == 0)
{
lean_object* v_a_2985_; lean_object* v___x_2987_; uint8_t v_isShared_2988_; uint8_t v_isSharedCheck_3036_; 
v_a_2985_ = lean_ctor_get(v___x_2984_, 0);
v_isSharedCheck_3036_ = !lean_is_exclusive(v___x_2984_);
if (v_isSharedCheck_3036_ == 0)
{
v___x_2987_ = v___x_2984_;
v_isShared_2988_ = v_isSharedCheck_3036_;
goto v_resetjp_2986_;
}
else
{
lean_inc(v_a_2985_);
lean_dec(v___x_2984_);
v___x_2987_ = lean_box(0);
v_isShared_2988_ = v_isSharedCheck_3036_;
goto v_resetjp_2986_;
}
v_resetjp_2986_:
{
if (lean_obj_tag(v_a_2985_) == 1)
{
lean_object* v_toCold_2989_; lean_object* v_options_2990_; lean_object* v_val_2991_; lean_object* v_inheritedTraceOptions_2992_; uint8_t v_hasTrace_2993_; lean_object* v___f_2994_; lean_object* v___y_2996_; lean_object* v___y_2997_; lean_object* v___y_2998_; lean_object* v___y_2999_; lean_object* v___y_3000_; lean_object* v___y_3001_; lean_object* v___y_3002_; lean_object* v___y_3003_; lean_object* v___y_3004_; lean_object* v___y_3005_; lean_object* v___y_3006_; 
lean_del_object(v___x_2987_);
v_toCold_2989_ = lean_ctor_get(v_a_2761_, 0);
v_options_2990_ = lean_ctor_get(v_toCold_2989_, 2);
v_val_2991_ = lean_ctor_get(v_a_2985_, 0);
lean_inc(v_val_2991_);
lean_dec_ref_known(v_a_2985_, 1);
v_inheritedTraceOptions_2992_ = lean_ctor_get(v_toCold_2989_, 11);
v_hasTrace_2993_ = lean_ctor_get_uint8(v_options_2990_, sizeof(void*)*1);
lean_inc_ref(v_e_2751_);
v___f_2994_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_internalize___lam__1), 3, 2);
lean_closure_set(v___f_2994_, 0, v_e_2751_);
lean_closure_set(v___f_2994_, 1, v_val_2991_);
if (v_hasTrace_2993_ == 0)
{
v___y_2996_ = v_val_2983_;
v___y_2997_ = v_a_2753_;
v___y_2998_ = v_a_2754_;
v___y_2999_ = v_a_2755_;
v___y_3000_ = v_a_2756_;
v___y_3001_ = v_a_2757_;
v___y_3002_ = v_a_2758_;
v___y_3003_ = v_a_2759_;
v___y_3004_ = v_a_2760_;
v___y_3005_ = v_a_2761_;
v___y_3006_ = v_a_2762_;
goto v___jp_2995_;
}
else
{
lean_object* v___x_3011_; lean_object* v___x_3012_; uint8_t v___x_3013_; 
v___x_3011_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__1));
v___x_3012_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__2, &l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__2_once, _init_l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__2);
v___x_3013_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2992_, v_options_2990_, v___x_3012_);
if (v___x_3013_ == 0)
{
v___y_2996_ = v_val_2983_;
v___y_2997_ = v_a_2753_;
v___y_2998_ = v_a_2754_;
v___y_2999_ = v_a_2755_;
v___y_3000_ = v_a_2756_;
v___y_3001_ = v_a_2757_;
v___y_3002_ = v_a_2758_;
v___y_3003_ = v_a_2759_;
v___y_3004_ = v_a_2760_;
v___y_3005_ = v_a_2761_;
v___y_3006_ = v_a_2762_;
goto v___jp_2995_;
}
else
{
lean_object* v___x_3014_; 
v___x_3014_ = l_Lean_Meta_Grind_updateLastTag(v_a_2753_, v_a_2754_, v_a_2755_, v_a_2756_, v_a_2757_, v_a_2758_, v_a_2759_, v_a_2760_, v_a_2761_, v_a_2762_);
if (lean_obj_tag(v___x_3014_) == 0)
{
lean_object* v___x_3016_; uint8_t v_isShared_3017_; uint8_t v_isSharedCheck_3030_; 
v_isSharedCheck_3030_ = !lean_is_exclusive(v___x_3014_);
if (v_isSharedCheck_3030_ == 0)
{
lean_object* v_unused_3031_; 
v_unused_3031_ = lean_ctor_get(v___x_3014_, 0);
lean_dec(v_unused_3031_);
v___x_3016_ = v___x_3014_;
v_isShared_3017_ = v_isSharedCheck_3030_;
goto v_resetjp_3015_;
}
else
{
lean_dec(v___x_3014_);
v___x_3016_ = lean_box(0);
v_isShared_3017_ = v_isSharedCheck_3030_;
goto v_resetjp_3015_;
}
v_resetjp_3015_:
{
lean_object* v___x_3018_; lean_object* v___x_3019_; lean_object* v___x_3021_; 
v___x_3018_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__12, &l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__12_once, _init_l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__12);
lean_inc(v_val_2983_);
v___x_3019_ = l_Nat_reprFast(v_val_2983_);
if (v_isShared_3017_ == 0)
{
lean_ctor_set_tag(v___x_3016_, 3);
lean_ctor_set(v___x_3016_, 0, v___x_3019_);
v___x_3021_ = v___x_3016_;
goto v_reusejp_3020_;
}
else
{
lean_object* v_reuseFailAlloc_3029_; 
v_reuseFailAlloc_3029_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3029_, 0, v___x_3019_);
v___x_3021_ = v_reuseFailAlloc_3029_;
goto v_reusejp_3020_;
}
v_reusejp_3020_:
{
lean_object* v___x_3022_; lean_object* v___x_3023_; lean_object* v___x_3024_; lean_object* v___x_3025_; lean_object* v___x_3026_; lean_object* v___x_3027_; lean_object* v___x_3028_; 
v___x_3022_ = l_Lean_MessageData_ofFormat(v___x_3021_);
v___x_3023_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3023_, 0, v___x_3018_);
lean_ctor_set(v___x_3023_, 1, v___x_3022_);
v___x_3024_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__6, &l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__6_once, _init_l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__6);
v___x_3025_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3025_, 0, v___x_3023_);
lean_ctor_set(v___x_3025_, 1, v___x_3024_);
lean_inc_ref(v_e_2751_);
v___x_3026_ = l_Lean_MessageData_ofExpr(v_e_2751_);
v___x_3027_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3027_, 0, v___x_3025_);
lean_ctor_set(v___x_3027_, 1, v___x_3026_);
v___x_3028_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__3___redArg(v___x_3011_, v___x_3027_, v_a_2759_, v_a_2760_, v_a_2761_, v_a_2762_);
if (lean_obj_tag(v___x_3028_) == 0)
{
lean_dec_ref_known(v___x_3028_, 1);
v___y_2996_ = v_val_2983_;
v___y_2997_ = v_a_2753_;
v___y_2998_ = v_a_2754_;
v___y_2999_ = v_a_2755_;
v___y_3000_ = v_a_2756_;
v___y_3001_ = v_a_2757_;
v___y_3002_ = v_a_2758_;
v___y_3003_ = v_a_2759_;
v___y_3004_ = v_a_2760_;
v___y_3005_ = v_a_2761_;
v___y_3006_ = v_a_2762_;
goto v___jp_2995_;
}
else
{
lean_dec_ref(v___f_2994_);
lean_dec(v_val_2983_);
lean_dec_ref(v_e_2751_);
return v___x_3028_;
}
}
}
}
else
{
lean_dec_ref(v___f_2994_);
lean_dec(v_val_2983_);
lean_dec_ref(v_e_2751_);
return v___x_3014_;
}
}
}
v___jp_2995_:
{
lean_object* v___x_3007_; 
lean_inc_ref(v_e_2751_);
v___x_3007_ = l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId___redArg(v_e_2751_, v___y_2996_, v___y_2997_, v___y_3001_, v___y_3002_, v___y_3003_, v___y_3004_, v___y_3005_, v___y_3006_);
if (lean_obj_tag(v___x_3007_) == 0)
{
lean_object* v___x_3008_; lean_object* v___x_3009_; 
lean_dec_ref_known(v___x_3007_, 1);
v___x_3008_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_3009_ = l_Lean_Meta_Grind_SolverExtension_markTerm___redArg(v___x_3008_, v_e_2751_, v___y_2997_, v___y_2998_, v___y_2999_, v___y_3000_, v___y_3001_, v___y_3002_, v___y_3003_, v___y_3004_, v___y_3005_, v___y_3006_);
if (lean_obj_tag(v___x_3009_) == 0)
{
lean_object* v___x_3010_; 
lean_dec_ref_known(v___x_3009_, 1);
v___x_3010_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_modifySemiringState___redArg(v___f_2994_, v___y_2996_, v___y_2997_);
lean_dec(v___y_2996_);
return v___x_3010_;
}
else
{
lean_dec(v___y_2996_);
lean_dec_ref(v___f_2994_);
return v___x_3009_;
}
}
else
{
lean_dec(v___y_2996_);
lean_dec_ref(v___f_2994_);
lean_dec_ref(v_e_2751_);
return v___x_3007_;
}
}
}
else
{
lean_object* v___x_3032_; lean_object* v___x_3034_; 
lean_dec(v_a_2985_);
lean_dec(v_val_2983_);
lean_dec_ref(v_e_2751_);
v___x_3032_ = lean_box(0);
if (v_isShared_2988_ == 0)
{
lean_ctor_set(v___x_2987_, 0, v___x_3032_);
v___x_3034_ = v___x_2987_;
goto v_reusejp_3033_;
}
else
{
lean_object* v_reuseFailAlloc_3035_; 
v_reuseFailAlloc_3035_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3035_, 0, v___x_3032_);
v___x_3034_ = v_reuseFailAlloc_3035_;
goto v_reusejp_3033_;
}
v_reusejp_3033_:
{
return v___x_3034_;
}
}
}
}
else
{
lean_object* v_a_3037_; lean_object* v___x_3039_; uint8_t v_isShared_3040_; uint8_t v_isSharedCheck_3044_; 
lean_dec(v_val_2983_);
lean_dec_ref(v_e_2751_);
v_a_3037_ = lean_ctor_get(v___x_2984_, 0);
v_isSharedCheck_3044_ = !lean_is_exclusive(v___x_2984_);
if (v_isSharedCheck_3044_ == 0)
{
v___x_3039_ = v___x_2984_;
v_isShared_3040_ = v_isSharedCheck_3044_;
goto v_resetjp_3038_;
}
else
{
lean_inc(v_a_3037_);
lean_dec(v___x_2984_);
v___x_3039_ = lean_box(0);
v_isShared_3040_ = v_isSharedCheck_3044_;
goto v_resetjp_3038_;
}
v_resetjp_3038_:
{
lean_object* v___x_3042_; 
if (v_isShared_3040_ == 0)
{
v___x_3042_ = v___x_3039_;
goto v_reusejp_3041_;
}
else
{
lean_object* v_reuseFailAlloc_3043_; 
v_reuseFailAlloc_3043_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3043_, 0, v_a_3037_);
v___x_3042_ = v_reuseFailAlloc_3043_;
goto v_reusejp_3041_;
}
v_reusejp_3041_:
{
return v___x_3042_;
}
}
}
}
else
{
lean_object* v___x_3045_; lean_object* v___x_3047_; 
lean_dec(v_a_2979_);
lean_dec_ref(v_e_2751_);
v___x_3045_ = lean_box(0);
if (v_isShared_2982_ == 0)
{
lean_ctor_set(v___x_2981_, 0, v___x_3045_);
v___x_3047_ = v___x_2981_;
goto v_reusejp_3046_;
}
else
{
lean_object* v_reuseFailAlloc_3048_; 
v_reuseFailAlloc_3048_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3048_, 0, v___x_3045_);
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
else
{
lean_object* v_a_3050_; lean_object* v___x_3052_; uint8_t v_isShared_3053_; uint8_t v_isSharedCheck_3057_; 
lean_dec_ref(v_e_2751_);
v_a_3050_ = lean_ctor_get(v___x_2978_, 0);
v_isSharedCheck_3057_ = !lean_is_exclusive(v___x_2978_);
if (v_isSharedCheck_3057_ == 0)
{
v___x_3052_ = v___x_2978_;
v_isShared_3053_ = v_isSharedCheck_3057_;
goto v_resetjp_3051_;
}
else
{
lean_inc(v_a_3050_);
lean_dec(v___x_2978_);
v___x_3052_ = lean_box(0);
v_isShared_3053_ = v_isSharedCheck_3057_;
goto v_resetjp_3051_;
}
v_resetjp_3051_:
{
lean_object* v___x_3055_; 
if (v_isShared_3053_ == 0)
{
v___x_3055_ = v___x_3052_;
goto v_reusejp_3054_;
}
else
{
lean_object* v_reuseFailAlloc_3056_; 
v_reuseFailAlloc_3056_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3056_, 0, v_a_3050_);
v___x_3055_ = v_reuseFailAlloc_3056_;
goto v_reusejp_3054_;
}
v_reusejp_3054_:
{
return v___x_3055_;
}
}
}
}
}
else
{
lean_object* v_a_3058_; lean_object* v___x_3060_; uint8_t v_isShared_3061_; uint8_t v_isSharedCheck_3065_; 
lean_dec(v_val_2782_);
lean_dec_ref(v_e_2751_);
v_a_3058_ = lean_ctor_get(v___x_2914_, 0);
v_isSharedCheck_3065_ = !lean_is_exclusive(v___x_2914_);
if (v_isSharedCheck_3065_ == 0)
{
v___x_3060_ = v___x_2914_;
v_isShared_3061_ = v_isSharedCheck_3065_;
goto v_resetjp_3059_;
}
else
{
lean_inc(v_a_3058_);
lean_dec(v___x_2914_);
v___x_3060_ = lean_box(0);
v_isShared_3061_ = v_isSharedCheck_3065_;
goto v_resetjp_3059_;
}
v_resetjp_3059_:
{
lean_object* v___x_3063_; 
if (v_isShared_3061_ == 0)
{
v___x_3063_ = v___x_3060_;
goto v_reusejp_3062_;
}
else
{
lean_object* v_reuseFailAlloc_3064_; 
v_reuseFailAlloc_3064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3064_, 0, v_a_3058_);
v___x_3063_ = v_reuseFailAlloc_3064_;
goto v_reusejp_3062_;
}
v_reusejp_3062_:
{
return v___x_3063_;
}
}
}
}
}
else
{
lean_object* v_a_3066_; lean_object* v___x_3068_; uint8_t v_isShared_3069_; uint8_t v_isSharedCheck_3073_; 
lean_dec(v_val_2782_);
lean_dec_ref(v_e_2751_);
v_a_3066_ = lean_ctor_get(v___x_2850_, 0);
v_isSharedCheck_3073_ = !lean_is_exclusive(v___x_2850_);
if (v_isSharedCheck_3073_ == 0)
{
v___x_3068_ = v___x_2850_;
v_isShared_3069_ = v_isSharedCheck_3073_;
goto v_resetjp_3067_;
}
else
{
lean_inc(v_a_3066_);
lean_dec(v___x_2850_);
v___x_3068_ = lean_box(0);
v_isShared_3069_ = v_isSharedCheck_3073_;
goto v_resetjp_3067_;
}
v_resetjp_3067_:
{
lean_object* v___x_3071_; 
if (v_isShared_3069_ == 0)
{
v___x_3071_ = v___x_3068_;
goto v_reusejp_3070_;
}
else
{
lean_object* v_reuseFailAlloc_3072_; 
v_reuseFailAlloc_3072_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3072_, 0, v_a_3066_);
v___x_3071_ = v_reuseFailAlloc_3072_;
goto v_reusejp_3070_;
}
v_reusejp_3070_:
{
return v___x_3071_;
}
}
}
}
}
else
{
lean_object* v_a_3074_; lean_object* v___x_3076_; uint8_t v_isShared_3077_; uint8_t v_isSharedCheck_3081_; 
lean_dec(v_val_2782_);
lean_dec_ref(v_e_2751_);
v_a_3074_ = lean_ctor_get(v___x_2784_, 0);
v_isSharedCheck_3081_ = !lean_is_exclusive(v___x_2784_);
if (v_isSharedCheck_3081_ == 0)
{
v___x_3076_ = v___x_2784_;
v_isShared_3077_ = v_isSharedCheck_3081_;
goto v_resetjp_3075_;
}
else
{
lean_inc(v_a_3074_);
lean_dec(v___x_2784_);
v___x_3076_ = lean_box(0);
v_isShared_3077_ = v_isSharedCheck_3081_;
goto v_resetjp_3075_;
}
v_resetjp_3075_:
{
lean_object* v___x_3079_; 
if (v_isShared_3077_ == 0)
{
v___x_3079_ = v___x_3076_;
goto v_reusejp_3078_;
}
else
{
lean_object* v_reuseFailAlloc_3080_; 
v_reuseFailAlloc_3080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3080_, 0, v_a_3074_);
v___x_3079_ = v_reuseFailAlloc_3080_;
goto v_reusejp_3078_;
}
v_reusejp_3078_:
{
return v___x_3079_;
}
}
}
}
else
{
lean_object* v___x_3082_; lean_object* v___x_3084_; 
lean_dec(v_val_2782_);
lean_dec_ref(v_e_2751_);
v___x_3082_ = lean_box(0);
if (v_isShared_2779_ == 0)
{
lean_ctor_set(v___x_2778_, 0, v___x_3082_);
v___x_3084_ = v___x_2778_;
goto v_reusejp_3083_;
}
else
{
lean_object* v_reuseFailAlloc_3085_; 
v_reuseFailAlloc_3085_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3085_, 0, v___x_3082_);
v___x_3084_ = v_reuseFailAlloc_3085_;
goto v_reusejp_3083_;
}
v_reusejp_3083_:
{
return v___x_3084_;
}
}
}
else
{
lean_object* v___x_3086_; lean_object* v___x_3088_; 
lean_dec(v___x_2781_);
lean_dec(v_parent_x3f_2752_);
lean_dec_ref(v_e_2751_);
v___x_3086_ = lean_box(0);
if (v_isShared_2779_ == 0)
{
lean_ctor_set(v___x_2778_, 0, v___x_3086_);
v___x_3088_ = v___x_2778_;
goto v_reusejp_3087_;
}
else
{
lean_object* v_reuseFailAlloc_3089_; 
v_reuseFailAlloc_3089_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3089_, 0, v___x_3086_);
v___x_3088_ = v_reuseFailAlloc_3089_;
goto v_reusejp_3087_;
}
v_reusejp_3087_:
{
return v___x_3088_;
}
}
}
else
{
lean_object* v___x_3090_; lean_object* v___x_3092_; 
lean_dec(v_parent_x3f_2752_);
lean_dec_ref(v_e_2751_);
v___x_3090_ = lean_box(0);
if (v_isShared_2779_ == 0)
{
lean_ctor_set(v___x_2778_, 0, v___x_3090_);
v___x_3092_ = v___x_2778_;
goto v_reusejp_3091_;
}
else
{
lean_object* v_reuseFailAlloc_3093_; 
v_reuseFailAlloc_3093_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3093_, 0, v___x_3090_);
v___x_3092_ = v_reuseFailAlloc_3093_;
goto v_reusejp_3091_;
}
v_reusejp_3091_:
{
return v___x_3092_;
}
}
}
}
else
{
lean_object* v_a_3095_; lean_object* v___x_3097_; uint8_t v_isShared_3098_; uint8_t v_isSharedCheck_3102_; 
lean_dec(v_parent_x3f_2752_);
lean_dec_ref(v_e_2751_);
v_a_3095_ = lean_ctor_get(v___x_2775_, 0);
v_isSharedCheck_3102_ = !lean_is_exclusive(v___x_2775_);
if (v_isSharedCheck_3102_ == 0)
{
v___x_3097_ = v___x_2775_;
v_isShared_3098_ = v_isSharedCheck_3102_;
goto v_resetjp_3096_;
}
else
{
lean_inc(v_a_3095_);
lean_dec(v___x_2775_);
v___x_3097_ = lean_box(0);
v_isShared_3098_ = v_isSharedCheck_3102_;
goto v_resetjp_3096_;
}
v_resetjp_3096_:
{
lean_object* v___x_3100_; 
if (v_isShared_3098_ == 0)
{
v___x_3100_ = v___x_3097_;
goto v_reusejp_3099_;
}
else
{
lean_object* v_reuseFailAlloc_3101_; 
v_reuseFailAlloc_3101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3101_, 0, v_a_3095_);
v___x_3100_ = v_reuseFailAlloc_3101_;
goto v_reusejp_3099_;
}
v_reusejp_3099_:
{
return v___x_3100_;
}
}
}
}
else
{
lean_object* v___x_3103_; lean_object* v___x_3105_; 
lean_dec(v_parent_x3f_2752_);
lean_dec_ref(v_e_2751_);
v___x_3103_ = lean_box(0);
if (v_isShared_2768_ == 0)
{
lean_ctor_set(v___x_2767_, 0, v___x_3103_);
v___x_3105_ = v___x_2767_;
goto v_reusejp_3104_;
}
else
{
lean_object* v_reuseFailAlloc_3106_; 
v_reuseFailAlloc_3106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3106_, 0, v___x_3103_);
v___x_3105_ = v_reuseFailAlloc_3106_;
goto v_reusejp_3104_;
}
v_reusejp_3104_:
{
return v___x_3105_;
}
}
}
}
}
else
{
lean_object* v_a_3108_; lean_object* v___x_3110_; uint8_t v_isShared_3111_; uint8_t v_isSharedCheck_3115_; 
lean_dec(v_parent_x3f_2752_);
lean_dec_ref(v_e_2751_);
v_a_3108_ = lean_ctor_get(v___x_2764_, 0);
v_isSharedCheck_3115_ = !lean_is_exclusive(v___x_2764_);
if (v_isSharedCheck_3115_ == 0)
{
v___x_3110_ = v___x_2764_;
v_isShared_3111_ = v_isSharedCheck_3115_;
goto v_resetjp_3109_;
}
else
{
lean_inc(v_a_3108_);
lean_dec(v___x_2764_);
v___x_3110_ = lean_box(0);
v_isShared_3111_ = v_isSharedCheck_3115_;
goto v_resetjp_3109_;
}
v_resetjp_3109_:
{
lean_object* v___x_3113_; 
if (v_isShared_3111_ == 0)
{
v___x_3113_ = v___x_3110_;
goto v_reusejp_3112_;
}
else
{
lean_object* v_reuseFailAlloc_3114_; 
v_reuseFailAlloc_3114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3114_, 0, v_a_3108_);
v___x_3113_ = v_reuseFailAlloc_3114_;
goto v_reusejp_3112_;
}
v_reusejp_3112_:
{
return v___x_3113_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_CommRing_internalize_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2751_ = stack[0].m_obj;
lean_object* v_parent_x3f_2752_ = stack[1].m_obj;
lean_object* v_a_2753_ = stack[2].m_obj;
lean_object* v_a_2754_ = stack[3].m_obj;
lean_object* v_a_2755_ = stack[4].m_obj;
lean_object* v_a_2756_ = stack[5].m_obj;
lean_object* v_a_2757_ = stack[6].m_obj;
lean_object* v_a_2758_ = stack[7].m_obj;
lean_object* v_a_2759_ = stack[8].m_obj;
lean_object* v_a_2760_ = stack[9].m_obj;
lean_object* v_a_2761_ = stack[10].m_obj;
lean_object* v_a_2762_ = stack[11].m_obj;
lean_object* v_res_3116_;
v_res_3116_ = l_Lean_Meta_Grind_Arith_CommRing_internalize(v_e_2751_, v_parent_x3f_2752_, v_a_2753_, v_a_2754_, v_a_2755_, v_a_2756_, v_a_2757_, v_a_2758_, v_a_2759_, v_a_2760_, v_a_2761_, v_a_2762_);
stack->m_obj
 = v_res_3116_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_internalize___boxed(lean_object* v_e_3117_, lean_object* v_parent_x3f_3118_, lean_object* v_a_3119_, lean_object* v_a_3120_, lean_object* v_a_3121_, lean_object* v_a_3122_, lean_object* v_a_3123_, lean_object* v_a_3124_, lean_object* v_a_3125_, lean_object* v_a_3126_, lean_object* v_a_3127_, lean_object* v_a_3128_, lean_object* v_a_3129_){
_start:
{
lean_object* v_res_3130_; 
v_res_3130_ = l_Lean_Meta_Grind_Arith_CommRing_internalize(v_e_3117_, v_parent_x3f_3118_, v_a_3119_, v_a_3120_, v_a_3121_, v_a_3122_, v_a_3123_, v_a_3124_, v_a_3125_, v_a_3126_, v_a_3127_, v_a_3128_);
lean_dec(v_a_3128_);
lean_dec_ref(v_a_3127_);
lean_dec(v_a_3126_);
lean_dec_ref(v_a_3125_);
lean_dec(v_a_3124_);
lean_dec_ref(v_a_3123_);
lean_dec(v_a_3122_);
lean_dec_ref(v_a_3121_);
lean_dec(v_a_3120_);
lean_dec(v_a_3119_);
return v_res_3130_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0(lean_object* v_00_u03b2_3131_, lean_object* v_x_3132_, lean_object* v_x_3133_, lean_object* v_x_3134_){
_start:
{
lean_object* v___x_3135_; 
v___x_3135_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0___redArg(v_x_3132_, v_x_3133_, v_x_3134_);
return v___x_3135_;
}
}
lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__1(lean_object* v_cls_3136_, lean_object* v_msg_3137_, lean_object* v___y_3138_, lean_object* v___y_3139_, lean_object* v___y_3140_, lean_object* v___y_3141_, lean_object* v___y_3142_, lean_object* v___y_3143_, lean_object* v___y_3144_, lean_object* v___y_3145_, lean_object* v___y_3146_, lean_object* v___y_3147_, lean_object* v___y_3148_){
_start:
{
lean_object* v___x_3150_; 
v___x_3150_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__1___redArg(v_cls_3136_, v_msg_3137_, v___y_3145_, v___y_3146_, v___y_3147_, v___y_3148_);
return v___x_3150_;
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_3136_ = stack[0].m_obj;
lean_object* v_msg_3137_ = stack[1].m_obj;
lean_object* v___y_3138_ = stack[2].m_obj;
lean_object* v___y_3139_ = stack[3].m_obj;
lean_object* v___y_3140_ = stack[4].m_obj;
lean_object* v___y_3141_ = stack[5].m_obj;
lean_object* v___y_3142_ = stack[6].m_obj;
lean_object* v___y_3143_ = stack[7].m_obj;
lean_object* v___y_3144_ = stack[8].m_obj;
lean_object* v___y_3145_ = stack[9].m_obj;
lean_object* v___y_3146_ = stack[10].m_obj;
lean_object* v___y_3147_ = stack[11].m_obj;
lean_object* v___y_3148_ = stack[12].m_obj;
lean_object* v_res_3151_;
v_res_3151_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__1(v_cls_3136_, v_msg_3137_, v___y_3138_, v___y_3139_, v___y_3140_, v___y_3141_, v___y_3142_, v___y_3143_, v___y_3144_, v___y_3145_, v___y_3146_, v___y_3147_, v___y_3148_);
stack->m_obj
 = v_res_3151_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__1___boxed(lean_object* v_cls_3152_, lean_object* v_msg_3153_, lean_object* v___y_3154_, lean_object* v___y_3155_, lean_object* v___y_3156_, lean_object* v___y_3157_, lean_object* v___y_3158_, lean_object* v___y_3159_, lean_object* v___y_3160_, lean_object* v___y_3161_, lean_object* v___y_3162_, lean_object* v___y_3163_, lean_object* v___y_3164_, lean_object* v___y_3165_){
_start:
{
lean_object* v_res_3166_; 
v_res_3166_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__1(v_cls_3152_, v_msg_3153_, v___y_3154_, v___y_3155_, v___y_3156_, v___y_3157_, v___y_3158_, v___y_3159_, v___y_3160_, v___y_3161_, v___y_3162_, v___y_3163_, v___y_3164_);
lean_dec(v___y_3164_);
lean_dec_ref(v___y_3163_);
lean_dec(v___y_3162_);
lean_dec_ref(v___y_3161_);
lean_dec(v___y_3160_);
lean_dec_ref(v___y_3159_);
lean_dec(v___y_3158_);
lean_dec_ref(v___y_3157_);
lean_dec(v___y_3156_);
lean_dec(v___y_3155_);
lean_dec(v___y_3154_);
return v_res_3166_;
}
}
lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__2(lean_object* v_cls_3167_, lean_object* v_msg_3168_, lean_object* v___y_3169_, lean_object* v___y_3170_, lean_object* v___y_3171_, lean_object* v___y_3172_, lean_object* v___y_3173_, lean_object* v___y_3174_, lean_object* v___y_3175_, lean_object* v___y_3176_, lean_object* v___y_3177_, lean_object* v___y_3178_, lean_object* v___y_3179_){
_start:
{
lean_object* v___x_3181_; 
v___x_3181_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__2___redArg(v_cls_3167_, v_msg_3168_, v___y_3176_, v___y_3177_, v___y_3178_, v___y_3179_);
return v___x_3181_;
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_3167_ = stack[0].m_obj;
lean_object* v_msg_3168_ = stack[1].m_obj;
lean_object* v___y_3169_ = stack[2].m_obj;
lean_object* v___y_3170_ = stack[3].m_obj;
lean_object* v___y_3171_ = stack[4].m_obj;
lean_object* v___y_3172_ = stack[5].m_obj;
lean_object* v___y_3173_ = stack[6].m_obj;
lean_object* v___y_3174_ = stack[7].m_obj;
lean_object* v___y_3175_ = stack[8].m_obj;
lean_object* v___y_3176_ = stack[9].m_obj;
lean_object* v___y_3177_ = stack[10].m_obj;
lean_object* v___y_3178_ = stack[11].m_obj;
lean_object* v___y_3179_ = stack[12].m_obj;
lean_object* v_res_3182_;
v_res_3182_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__2(v_cls_3167_, v_msg_3168_, v___y_3169_, v___y_3170_, v___y_3171_, v___y_3172_, v___y_3173_, v___y_3174_, v___y_3175_, v___y_3176_, v___y_3177_, v___y_3178_, v___y_3179_);
stack->m_obj
 = v_res_3182_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__2___boxed(lean_object* v_cls_3183_, lean_object* v_msg_3184_, lean_object* v___y_3185_, lean_object* v___y_3186_, lean_object* v___y_3187_, lean_object* v___y_3188_, lean_object* v___y_3189_, lean_object* v___y_3190_, lean_object* v___y_3191_, lean_object* v___y_3192_, lean_object* v___y_3193_, lean_object* v___y_3194_, lean_object* v___y_3195_, lean_object* v___y_3196_){
_start:
{
lean_object* v_res_3197_; 
v_res_3197_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__2(v_cls_3183_, v_msg_3184_, v___y_3185_, v___y_3186_, v___y_3187_, v___y_3188_, v___y_3189_, v___y_3190_, v___y_3191_, v___y_3192_, v___y_3193_, v___y_3194_, v___y_3195_);
lean_dec(v___y_3195_);
lean_dec_ref(v___y_3194_);
lean_dec(v___y_3193_);
lean_dec_ref(v___y_3192_);
lean_dec(v___y_3191_);
lean_dec_ref(v___y_3190_);
lean_dec(v___y_3189_);
lean_dec_ref(v___y_3188_);
lean_dec(v___y_3187_);
lean_dec(v___y_3186_);
lean_dec(v___y_3185_);
return v_res_3197_;
}
}
lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__3(lean_object* v_cls_3198_, lean_object* v_msg_3199_, lean_object* v___y_3200_, lean_object* v___y_3201_, lean_object* v___y_3202_, lean_object* v___y_3203_, lean_object* v___y_3204_, lean_object* v___y_3205_, lean_object* v___y_3206_, lean_object* v___y_3207_, lean_object* v___y_3208_, lean_object* v___y_3209_, lean_object* v___y_3210_){
_start:
{
lean_object* v___x_3212_; 
v___x_3212_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__3___redArg(v_cls_3198_, v_msg_3199_, v___y_3207_, v___y_3208_, v___y_3209_, v___y_3210_);
return v___x_3212_;
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_3198_ = stack[0].m_obj;
lean_object* v_msg_3199_ = stack[1].m_obj;
lean_object* v___y_3200_ = stack[2].m_obj;
lean_object* v___y_3201_ = stack[3].m_obj;
lean_object* v___y_3202_ = stack[4].m_obj;
lean_object* v___y_3203_ = stack[5].m_obj;
lean_object* v___y_3204_ = stack[6].m_obj;
lean_object* v___y_3205_ = stack[7].m_obj;
lean_object* v___y_3206_ = stack[8].m_obj;
lean_object* v___y_3207_ = stack[9].m_obj;
lean_object* v___y_3208_ = stack[10].m_obj;
lean_object* v___y_3209_ = stack[11].m_obj;
lean_object* v___y_3210_ = stack[12].m_obj;
lean_object* v_res_3213_;
v_res_3213_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__3(v_cls_3198_, v_msg_3199_, v___y_3200_, v___y_3201_, v___y_3202_, v___y_3203_, v___y_3204_, v___y_3205_, v___y_3206_, v___y_3207_, v___y_3208_, v___y_3209_, v___y_3210_);
stack->m_obj
 = v_res_3213_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__3___boxed(lean_object* v_cls_3214_, lean_object* v_msg_3215_, lean_object* v___y_3216_, lean_object* v___y_3217_, lean_object* v___y_3218_, lean_object* v___y_3219_, lean_object* v___y_3220_, lean_object* v___y_3221_, lean_object* v___y_3222_, lean_object* v___y_3223_, lean_object* v___y_3224_, lean_object* v___y_3225_, lean_object* v___y_3226_, lean_object* v___y_3227_){
_start:
{
lean_object* v_res_3228_; 
v_res_3228_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__3(v_cls_3214_, v_msg_3215_, v___y_3216_, v___y_3217_, v___y_3218_, v___y_3219_, v___y_3220_, v___y_3221_, v___y_3222_, v___y_3223_, v___y_3224_, v___y_3225_, v___y_3226_);
lean_dec(v___y_3226_);
lean_dec_ref(v___y_3225_);
lean_dec(v___y_3224_);
lean_dec_ref(v___y_3223_);
lean_dec(v___y_3222_);
lean_dec_ref(v___y_3221_);
lean_dec(v___y_3220_);
lean_dec_ref(v___y_3219_);
lean_dec(v___y_3218_);
lean_dec(v___y_3217_);
lean_dec(v___y_3216_);
return v_res_3228_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0(lean_object* v_00_u03b2_3229_, lean_object* v_x_3230_, size_t v_x_3231_, size_t v_x_3232_, lean_object* v_x_3233_, lean_object* v_x_3234_){
_start:
{
lean_object* v___x_3235_; 
v___x_3235_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0___redArg(v_x_3230_, v_x_3231_, v_x_3232_, v_x_3233_, v_x_3234_);
return v___x_3235_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3230_ = stack[1].m_obj;
size_t v_x_3231_ = stack[2].m_num;
size_t v_x_3232_ = stack[3].m_num;
lean_object* v_x_3233_ = stack[4].m_obj;
lean_object* v_x_3234_ = stack[5].m_obj;
lean_object* v_res_3236_;
v_res_3236_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0(lean_box(0), v_x_3230_, v_x_3231_, v_x_3232_, v_x_3233_, v_x_3234_);
stack->m_obj
 = v_res_3236_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3237_, lean_object* v_x_3238_, lean_object* v_x_3239_, lean_object* v_x_3240_, lean_object* v_x_3241_, lean_object* v_x_3242_){
_start:
{
size_t v_x_133530__boxed_3243_; size_t v_x_133531__boxed_3244_; lean_object* v_res_3245_; 
v_x_133530__boxed_3243_ = lean_unbox_usize(v_x_3239_);
lean_dec(v_x_3239_);
v_x_133531__boxed_3244_ = lean_unbox_usize(v_x_3240_);
lean_dec(v_x_3240_);
v_res_3245_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0(v_00_u03b2_3237_, v_x_3238_, v_x_133530__boxed_3243_, v_x_133531__boxed_3244_, v_x_3241_, v_x_3242_);
return v_res_3245_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_3246_, lean_object* v_n_3247_, lean_object* v_k_3248_, lean_object* v_v_3249_){
_start:
{
lean_object* v___x_3250_; 
v___x_3250_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0_spec__1___redArg(v_n_3247_, v_k_3248_, v_v_3249_);
return v___x_3250_;
}
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_3251_, size_t v_depth_3252_, lean_object* v_keys_3253_, lean_object* v_vals_3254_, lean_object* v_heq_3255_, lean_object* v_i_3256_, lean_object* v_entries_3257_){
_start:
{
lean_object* v___x_3258_; 
v___x_3258_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0_spec__2___redArg(v_depth_3252_, v_keys_3253_, v_vals_3254_, v_i_3256_, v_entries_3257_);
return v___x_3258_;
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0_spec__2_0interp(lean_interpreter_value* stack)
{
size_t v_depth_3252_ = stack[1].m_num;
lean_object* v_keys_3253_ = stack[2].m_obj;
lean_object* v_vals_3254_ = stack[3].m_obj;
lean_object* v_i_3256_ = stack[5].m_obj;
lean_object* v_entries_3257_ = stack[6].m_obj;
lean_object* v_res_3259_;
v_res_3259_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0_spec__2(lean_box(0), v_depth_3252_, v_keys_3253_, v_vals_3254_, lean_box(0), v_i_3256_, v_entries_3257_);
stack->m_obj
 = v_res_3259_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_3260_, lean_object* v_depth_3261_, lean_object* v_keys_3262_, lean_object* v_vals_3263_, lean_object* v_heq_3264_, lean_object* v_i_3265_, lean_object* v_entries_3266_){
_start:
{
size_t v_depth_boxed_3267_; lean_object* v_res_3268_; 
v_depth_boxed_3267_ = lean_unbox_usize(v_depth_3261_);
lean_dec(v_depth_3261_);
v_res_3268_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0_spec__2(v_00_u03b2_3260_, v_depth_boxed_3267_, v_keys_3262_, v_vals_3263_, v_heq_3264_, v_i_3265_, v_entries_3266_);
lean_dec_ref(v_vals_3263_);
lean_dec_ref(v_keys_3262_);
return v_res_3268_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0_spec__1_spec__5(lean_object* v_00_u03b2_3269_, lean_object* v_x_3270_, lean_object* v_x_3271_, lean_object* v_x_3272_, lean_object* v_x_3273_){
_start:
{
lean_object* v___x_3274_; 
v___x_3274_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0_spec__1_spec__5___redArg(v_x_3270_, v_x_3271_, v_x_3272_, v_x_3273_);
return v___x_3274_;
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
