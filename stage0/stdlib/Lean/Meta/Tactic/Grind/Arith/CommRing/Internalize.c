// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.CommRing.Internalize
// Imports: public import Lean.Meta.Tactic.Grind.Arith.CommRing.RingId import Lean.Meta.Tactic.Grind.Simp import Lean.Meta.Tactic.Grind.Arith.Util import Lean.Meta.Tactic.Grind.Arith.CommRing.Reify import Lean.Meta.Tactic.Grind.Arith.CommRing.DenoteExpr import Lean.Meta.Tactic.Grind.Arith.Cutsat.Util import Lean.Meta.Sym.Arith.Classify
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
lean_object* l_Lean_Meta_Grind_pushNewFactCore___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_pushEqCore___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Grind_Arith_CommRing_ringExt;
lean_object* l_Lean_Meta_Grind_SolverExtension_markTerm___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_modifySemiringState___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifySemiringState___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_modifyRingState___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getConfig___redArg(lean_object*);
uint8_t l_Lean_Meta_Grind_Arith_isIntModuleVirtualParent(lean_object*);
lean_object* l_Lean_Meta_Sym_Arith_homoType_x3f(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_reify_x3f(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_sreify_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNonCommRingId_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_ncreify_x3f(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_ncsreify_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isCutsatType___redArg(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___boxed(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isForbiddenParent___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HMod"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isForbiddenParent___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isForbiddenParent___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isForbiddenParent___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hMod"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isForbiddenParent___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isForbiddenParent___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isForbiddenParent___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isForbiddenParent___closed__0_value),LEAN_SCALAR_PTR_LITERAL(93, 4, 3, 35, 188, 254, 191, 190)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isForbiddenParent___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isForbiddenParent___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isForbiddenParent___closed__1_value),LEAN_SCALAR_PTR_LITERAL(120, 199, 142, 238, 9, 44, 94, 134)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isForbiddenParent___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isForbiddenParent___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isForbiddenParent___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HDiv"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isForbiddenParent___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isForbiddenParent___closed__3_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isForbiddenParent___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hDiv"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isForbiddenParent___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isForbiddenParent___closed__4_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isForbiddenParent___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isForbiddenParent___closed__3_value),LEAN_SCALAR_PTR_LITERAL(74, 223, 78, 88, 255, 236, 144, 164)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isForbiddenParent___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isForbiddenParent___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isForbiddenParent___closed__4_value),LEAN_SCALAR_PTR_LITERAL(26, 183, 188, 240, 156, 118, 170, 84)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isForbiddenParent___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isForbiddenParent___closed__5_value;
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isForbiddenParent(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isForbiddenParent___boxed(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isIneqParent___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "LT"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isIneqParent___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isIneqParent___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isIneqParent___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "lt"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isIneqParent___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isIneqParent___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isIneqParent___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isIneqParent___closed__0_value),LEAN_SCALAR_PTR_LITERAL(71, 235, 154, 184, 62, 135, 30, 248)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isIneqParent___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isIneqParent___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isIneqParent___closed__1_value),LEAN_SCALAR_PTR_LITERAL(54, 235, 251, 9, 4, 74, 57, 164)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isIneqParent___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isIneqParent___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isIneqParent___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "LE"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isIneqParent___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isIneqParent___closed__3_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isIneqParent___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "le"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isIneqParent___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isIneqParent___closed__4_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isIneqParent___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isIneqParent___closed__3_value),LEAN_SCALAR_PTR_LITERAL(216, 149, 183, 186, 191, 145, 216, 115)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isIneqParent___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isIneqParent___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isIneqParent___closed__4_value),LEAN_SCALAR_PTR_LITERAL(109, 14, 90, 172, 72, 170, 136, 101)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isIneqParent___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isIneqParent___closed__5_value;
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isIneqParent(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isIneqParent___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_pushInvFact___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_pushInvFact___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_pushInvFact(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_pushInvFact___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_dec_ref(v___x_53_);
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
lean_dec_ref(v___x_56_);
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
lean_dec_ref(v___x_59_);
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
lean_dec_ref(v___x_63_);
v___x_76_ = lean_box(0);
return v___x_76_;
}
else
{
lean_object* v___x_77_; uint8_t v___x_78_; 
v___x_77_ = l_Lean_Expr_appFnCleanup___redArg(v___x_74_);
v___x_78_ = l_Lean_Expr_isApp(v___x_77_);
if (v___x_78_ == 0)
{
lean_object* v___x_79_; 
lean_dec_ref(v___x_77_);
lean_dec_ref(v___x_74_);
lean_dec_ref(v___x_63_);
v___x_79_ = lean_box(0);
return v___x_79_;
}
else
{
lean_object* v_arg_80_; lean_object* v_arg_81_; lean_object* v_arg_82_; lean_object* v___x_83_; lean_object* v___x_84_; uint8_t v___x_85_; 
v_arg_80_ = lean_ctor_get(v___x_63_, 1);
lean_inc_ref(v_arg_80_);
lean_dec_ref(v___x_63_);
v_arg_81_ = lean_ctor_get(v___x_74_, 1);
lean_inc_ref(v_arg_81_);
lean_dec_ref(v___x_74_);
v_arg_82_ = lean_ctor_get(v___x_77_, 1);
lean_inc_ref(v_arg_82_);
v___x_83_ = l_Lean_Expr_appFnCleanup___redArg(v___x_77_);
lean_dec_ref(v___x_77_);
v___x_84_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__14));
v___x_85_ = l_Lean_Expr_isConstOf(v___x_83_, v___x_84_);
if (v___x_85_ == 0)
{
lean_object* v___x_86_; uint8_t v___x_87_; 
v___x_86_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__17));
v___x_87_ = l_Lean_Expr_isConstOf(v___x_83_, v___x_86_);
if (v___x_87_ == 0)
{
lean_object* v___x_88_; uint8_t v___x_89_; 
v___x_88_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__20));
v___x_89_ = l_Lean_Expr_isConstOf(v___x_83_, v___x_88_);
if (v___x_89_ == 0)
{
lean_object* v___x_90_; uint8_t v___x_91_; 
v___x_90_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__23));
v___x_91_ = l_Lean_Expr_isConstOf(v___x_83_, v___x_90_);
if (v___x_91_ == 0)
{
lean_object* v___x_92_; uint8_t v___x_93_; 
v___x_92_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__26));
v___x_93_ = l_Lean_Expr_isConstOf(v___x_83_, v___x_92_);
lean_dec_ref(v___x_83_);
if (v___x_93_ == 0)
{
lean_object* v___x_94_; 
lean_dec_ref(v_arg_82_);
lean_dec_ref(v_arg_81_);
lean_dec_ref(v_arg_80_);
v___x_94_ = lean_box(0);
return v___x_94_;
}
else
{
lean_object* v___x_95_; 
v___x_95_ = l_Lean_Meta_Sym_Arith_homoType_x3f(v_arg_82_, v_arg_81_, v_arg_80_);
lean_dec_ref(v_arg_80_);
lean_dec_ref(v_arg_81_);
return v___x_95_;
}
}
else
{
lean_object* v___x_96_; 
lean_dec_ref(v___x_83_);
v___x_96_ = l_Lean_Meta_Sym_Arith_homoType_x3f(v_arg_82_, v_arg_81_, v_arg_80_);
lean_dec_ref(v_arg_80_);
lean_dec_ref(v_arg_81_);
return v___x_96_;
}
}
else
{
lean_object* v___x_97_; 
lean_dec_ref(v___x_83_);
v___x_97_ = l_Lean_Meta_Sym_Arith_homoType_x3f(v_arg_82_, v_arg_81_, v_arg_80_);
lean_dec_ref(v_arg_80_);
lean_dec_ref(v_arg_81_);
return v___x_97_;
}
}
else
{
lean_object* v___x_98_; lean_object* v___x_99_; uint8_t v___x_100_; 
lean_dec_ref(v___x_83_);
v___x_98_ = l_Lean_Expr_cleanupAnnotations(v_arg_82_);
lean_dec_ref(v_arg_82_);
v___x_99_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__28));
v___x_100_ = l_Lean_Expr_isConstOf(v___x_98_, v___x_99_);
if (v___x_100_ == 0)
{
lean_object* v___x_101_; uint8_t v___x_102_; 
v___x_101_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__30));
v___x_102_ = l_Lean_Expr_isConstOf(v___x_98_, v___x_101_);
lean_dec_ref(v___x_98_);
if (v___x_102_ == 0)
{
lean_object* v___x_103_; 
lean_dec_ref(v_arg_81_);
lean_dec_ref(v_arg_80_);
v___x_103_ = lean_box(0);
return v___x_103_;
}
else
{
lean_object* v___x_104_; 
lean_inc_ref(v_arg_81_);
v___x_104_ = l_Lean_Meta_Sym_Arith_homoType_x3f(v_arg_81_, v_arg_81_, v_arg_80_);
lean_dec_ref(v_arg_80_);
lean_dec_ref(v_arg_81_);
return v___x_104_;
}
}
else
{
lean_object* v___x_105_; 
lean_dec_ref(v___x_98_);
lean_inc_ref(v_arg_81_);
v___x_105_ = l_Lean_Meta_Sym_Arith_homoType_x3f(v_arg_81_, v_arg_81_, v_arg_80_);
lean_dec_ref(v_arg_80_);
lean_dec_ref(v_arg_81_);
return v___x_105_;
}
}
}
else
{
lean_object* v___x_106_; lean_object* v___x_107_; uint8_t v___x_108_; 
lean_dec_ref(v___x_83_);
v___x_106_ = l_Lean_Expr_cleanupAnnotations(v_arg_81_);
lean_dec_ref(v_arg_81_);
v___x_107_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__30));
v___x_108_ = l_Lean_Expr_isConstOf(v___x_106_, v___x_107_);
lean_dec_ref(v___x_106_);
if (v___x_108_ == 0)
{
lean_object* v___x_109_; 
lean_dec_ref(v_arg_82_);
lean_dec_ref(v_arg_80_);
v___x_109_ = lean_box(0);
return v___x_109_;
}
else
{
lean_object* v___x_110_; 
lean_inc_ref(v_arg_82_);
v___x_110_ = l_Lean_Meta_Sym_Arith_homoType_x3f(v_arg_82_, v_arg_82_, v_arg_80_);
lean_dec_ref(v_arg_80_);
lean_dec_ref(v_arg_82_);
return v___x_110_;
}
}
}
}
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
else
{
lean_object* v___x_114_; 
lean_dec_ref(v___x_63_);
v___x_114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_114_, 0, v_arg_62_);
return v___x_114_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___boxed(lean_object* v_e_115_){
_start:
{
lean_object* v_res_116_; 
v_res_116_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f(v_e_115_);
lean_dec_ref(v_e_115_);
return v_res_116_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isForbiddenParent(lean_object* v_parent_x3f_127_){
_start:
{
if (lean_obj_tag(v_parent_x3f_127_) == 1)
{
lean_object* v_val_128_; lean_object* v___x_129_; 
v_val_128_ = lean_ctor_get(v_parent_x3f_127_, 0);
v___x_129_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f(v_val_128_);
if (lean_obj_tag(v___x_129_) == 0)
{
uint8_t v___x_130_; lean_object* v___x_131_; uint8_t v___x_132_; 
v___x_130_ = 0;
v___x_131_ = l_Lean_Expr_cleanupAnnotations(v_val_128_);
v___x_132_ = l_Lean_Expr_isApp(v___x_131_);
if (v___x_132_ == 0)
{
lean_dec_ref(v___x_131_);
return v___x_130_;
}
else
{
lean_object* v___x_133_; uint8_t v___x_134_; 
v___x_133_ = l_Lean_Expr_appFnCleanup___redArg(v___x_131_);
lean_dec_ref(v___x_131_);
v___x_134_ = l_Lean_Expr_isApp(v___x_133_);
if (v___x_134_ == 0)
{
lean_dec_ref(v___x_133_);
return v___x_130_;
}
else
{
lean_object* v___x_135_; uint8_t v___x_136_; 
v___x_135_ = l_Lean_Expr_appFnCleanup___redArg(v___x_133_);
lean_dec_ref(v___x_133_);
v___x_136_ = l_Lean_Expr_isApp(v___x_135_);
if (v___x_136_ == 0)
{
lean_dec_ref(v___x_135_);
return v___x_130_;
}
else
{
lean_object* v___x_137_; uint8_t v___x_138_; 
v___x_137_ = l_Lean_Expr_appFnCleanup___redArg(v___x_135_);
lean_dec_ref(v___x_135_);
v___x_138_ = l_Lean_Expr_isApp(v___x_137_);
if (v___x_138_ == 0)
{
lean_dec_ref(v___x_137_);
return v___x_130_;
}
else
{
lean_object* v___x_139_; uint8_t v___x_140_; 
v___x_139_ = l_Lean_Expr_appFnCleanup___redArg(v___x_137_);
lean_dec_ref(v___x_137_);
v___x_140_ = l_Lean_Expr_isApp(v___x_139_);
if (v___x_140_ == 0)
{
lean_dec_ref(v___x_139_);
return v___x_130_;
}
else
{
lean_object* v___x_141_; uint8_t v___x_142_; 
v___x_141_ = l_Lean_Expr_appFnCleanup___redArg(v___x_139_);
lean_dec_ref(v___x_139_);
v___x_142_ = l_Lean_Expr_isApp(v___x_141_);
if (v___x_142_ == 0)
{
lean_dec_ref(v___x_141_);
return v___x_130_;
}
else
{
lean_object* v___x_143_; lean_object* v___x_144_; uint8_t v___x_145_; 
v___x_143_ = l_Lean_Expr_appFnCleanup___redArg(v___x_141_);
lean_dec_ref(v___x_141_);
v___x_144_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isForbiddenParent___closed__2));
v___x_145_ = l_Lean_Expr_isConstOf(v___x_143_, v___x_144_);
if (v___x_145_ == 0)
{
lean_object* v___x_146_; uint8_t v___x_147_; 
v___x_146_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isForbiddenParent___closed__5));
v___x_147_ = l_Lean_Expr_isConstOf(v___x_143_, v___x_146_);
lean_dec_ref(v___x_143_);
if (v___x_147_ == 0)
{
return v___x_130_;
}
else
{
return v___x_142_;
}
}
else
{
lean_dec_ref(v___x_143_);
return v___x_142_;
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
uint8_t v___x_148_; 
lean_dec_ref_known(v___x_129_, 1);
v___x_148_ = 1;
return v___x_148_;
}
}
else
{
uint8_t v___x_149_; 
v___x_149_ = 0;
return v___x_149_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isForbiddenParent___boxed(lean_object* v_parent_x3f_150_){
_start:
{
uint8_t v_res_151_; lean_object* v_r_152_; 
v_res_151_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isForbiddenParent(v_parent_x3f_150_);
lean_dec(v_parent_x3f_150_);
v_r_152_ = lean_box(v_res_151_);
return v_r_152_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isIneqParent(lean_object* v_parent_x3f_163_){
_start:
{
if (lean_obj_tag(v_parent_x3f_163_) == 1)
{
lean_object* v_val_164_; lean_object* v___x_165_; uint8_t v___x_166_; 
v_val_164_ = lean_ctor_get(v_parent_x3f_163_, 0);
v___x_165_ = l_Lean_Expr_cleanupAnnotations(v_val_164_);
v___x_166_ = l_Lean_Expr_isApp(v___x_165_);
if (v___x_166_ == 0)
{
lean_dec_ref(v___x_165_);
return v___x_166_;
}
else
{
lean_object* v___x_167_; uint8_t v___x_168_; 
v___x_167_ = l_Lean_Expr_appFnCleanup___redArg(v___x_165_);
lean_dec_ref(v___x_165_);
v___x_168_ = l_Lean_Expr_isApp(v___x_167_);
if (v___x_168_ == 0)
{
lean_dec_ref(v___x_167_);
return v___x_168_;
}
else
{
lean_object* v___x_169_; uint8_t v___x_170_; 
v___x_169_ = l_Lean_Expr_appFnCleanup___redArg(v___x_167_);
lean_dec_ref(v___x_167_);
v___x_170_ = l_Lean_Expr_isApp(v___x_169_);
if (v___x_170_ == 0)
{
lean_dec_ref(v___x_169_);
return v___x_170_;
}
else
{
lean_object* v___x_171_; uint8_t v___x_172_; 
v___x_171_ = l_Lean_Expr_appFnCleanup___redArg(v___x_169_);
lean_dec_ref(v___x_169_);
v___x_172_ = l_Lean_Expr_isApp(v___x_171_);
if (v___x_172_ == 0)
{
lean_dec_ref(v___x_171_);
return v___x_172_;
}
else
{
lean_object* v___x_173_; lean_object* v___x_174_; uint8_t v___x_175_; 
v___x_173_ = l_Lean_Expr_appFnCleanup___redArg(v___x_171_);
lean_dec_ref(v___x_171_);
v___x_174_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isIneqParent___closed__2));
v___x_175_ = l_Lean_Expr_isConstOf(v___x_173_, v___x_174_);
if (v___x_175_ == 0)
{
lean_object* v___x_176_; uint8_t v___x_177_; 
v___x_176_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isIneqParent___closed__5));
v___x_177_ = l_Lean_Expr_isConstOf(v___x_173_, v___x_176_);
lean_dec_ref(v___x_173_);
return v___x_177_;
}
else
{
lean_dec_ref(v___x_173_);
return v___x_175_;
}
}
}
}
}
}
else
{
uint8_t v___x_178_; 
v___x_178_ = 0;
return v___x_178_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isIneqParent___boxed(lean_object* v_parent_x3f_179_){
_start:
{
uint8_t v_res_180_; lean_object* v_r_181_; 
v_res_180_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isIneqParent(v_parent_x3f_179_);
lean_dec(v_parent_x3f_179_);
v_r_181_ = lean_box(v_res_180_);
return v_r_181_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__1(lean_object* v_a_182_){
_start:
{
lean_object* v___x_183_; 
v___x_183_ = lean_nat_to_int(v_a_182_);
return v___x_183_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5(lean_object* v_msgData_184_, lean_object* v___y_185_, lean_object* v___y_186_, lean_object* v___y_187_, lean_object* v___y_188_){
_start:
{
lean_object* v___x_190_; lean_object* v_env_191_; uint8_t v___x_192_; lean_object* v_env_193_; lean_object* v___x_194_; lean_object* v_toCold_195_; lean_object* v_mctx_196_; lean_object* v_lctx_197_; lean_object* v_options_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; 
v___x_190_ = lean_st_ref_get(v___y_188_);
v_env_191_ = lean_ctor_get(v___x_190_, 0);
lean_inc_ref(v_env_191_);
lean_dec(v___x_190_);
v___x_192_ = 0;
v_env_193_ = l_Lean_Environment_setRecordingDeps(v_env_191_, v___x_192_);
v___x_194_ = lean_st_ref_get(v___y_186_);
v_toCold_195_ = lean_ctor_get(v___y_187_, 0);
v_mctx_196_ = lean_ctor_get(v___x_194_, 0);
lean_inc_ref(v_mctx_196_);
lean_dec(v___x_194_);
v_lctx_197_ = lean_ctor_get(v___y_185_, 2);
v_options_198_ = lean_ctor_get(v_toCold_195_, 2);
lean_inc_ref(v_options_198_);
lean_inc_ref(v_lctx_197_);
v___x_199_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_199_, 0, v_env_193_);
lean_ctor_set(v___x_199_, 1, v_mctx_196_);
lean_ctor_set(v___x_199_, 2, v_lctx_197_);
lean_ctor_set(v___x_199_, 3, v_options_198_);
v___x_200_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_200_, 0, v___x_199_);
lean_ctor_set(v___x_200_, 1, v_msgData_184_);
v___x_201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_201_, 0, v___x_200_);
return v___x_201_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___boxed(lean_object* v_msgData_202_, lean_object* v___y_203_, lean_object* v___y_204_, lean_object* v___y_205_, lean_object* v___y_206_, lean_object* v___y_207_){
_start:
{
lean_object* v_res_208_; 
v_res_208_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5(v_msgData_202_, v___y_203_, v___y_204_, v___y_205_, v___y_206_);
lean_dec(v___y_206_);
lean_dec_ref(v___y_205_);
lean_dec(v___y_204_);
lean_dec_ref(v___y_203_);
return v_res_208_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__2_spec__3_spec__4___redArg(lean_object* v_msg_209_, lean_object* v___y_210_, lean_object* v___y_211_, lean_object* v___y_212_, lean_object* v___y_213_){
_start:
{
lean_object* v_ref_215_; lean_object* v___x_216_; lean_object* v_a_217_; lean_object* v___x_219_; uint8_t v_isShared_220_; uint8_t v_isSharedCheck_225_; 
v_ref_215_ = lean_ctor_get(v___y_212_, 2);
v___x_216_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5(v_msg_209_, v___y_210_, v___y_211_, v___y_212_, v___y_213_);
v_a_217_ = lean_ctor_get(v___x_216_, 0);
v_isSharedCheck_225_ = !lean_is_exclusive(v___x_216_);
if (v_isSharedCheck_225_ == 0)
{
v___x_219_ = v___x_216_;
v_isShared_220_ = v_isSharedCheck_225_;
goto v_resetjp_218_;
}
else
{
lean_inc(v_a_217_);
lean_dec(v___x_216_);
v___x_219_ = lean_box(0);
v_isShared_220_ = v_isSharedCheck_225_;
goto v_resetjp_218_;
}
v_resetjp_218_:
{
lean_object* v___x_221_; lean_object* v___x_223_; 
lean_inc(v_ref_215_);
v___x_221_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_221_, 0, v_ref_215_);
lean_ctor_set(v___x_221_, 1, v_a_217_);
if (v_isShared_220_ == 0)
{
lean_ctor_set_tag(v___x_219_, 1);
lean_ctor_set(v___x_219_, 0, v___x_221_);
v___x_223_ = v___x_219_;
goto v_reusejp_222_;
}
else
{
lean_object* v_reuseFailAlloc_224_; 
v_reuseFailAlloc_224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_224_, 0, v___x_221_);
v___x_223_ = v_reuseFailAlloc_224_;
goto v_reusejp_222_;
}
v_reusejp_222_:
{
return v___x_223_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__2_spec__3_spec__4___redArg___boxed(lean_object* v_msg_226_, lean_object* v___y_227_, lean_object* v___y_228_, lean_object* v___y_229_, lean_object* v___y_230_, lean_object* v___y_231_){
_start:
{
lean_object* v_res_232_; 
v_res_232_ = l_Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__2_spec__3_spec__4___redArg(v_msg_226_, v___y_227_, v___y_228_, v___y_229_, v___y_230_);
lean_dec(v___y_230_);
lean_dec_ref(v___y_229_);
lean_dec(v___y_228_);
lean_dec_ref(v___y_227_);
return v_res_232_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__2_spec__3___closed__1(void){
_start:
{
lean_object* v___x_234_; lean_object* v___x_235_; 
v___x_234_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__2_spec__3___closed__0));
v___x_235_ = l_Lean_stringToMessageData(v___x_234_);
return v___x_235_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__2_spec__3(lean_object* v_type_236_, lean_object* v___y_237_, lean_object* v___y_238_, lean_object* v___y_239_, lean_object* v___y_240_, lean_object* v___y_241_, lean_object* v___y_242_, lean_object* v___y_243_, lean_object* v___y_244_, lean_object* v___y_245_, lean_object* v___y_246_, lean_object* v___y_247_){
_start:
{
lean_object* v___x_249_; 
lean_inc_ref(v_type_236_);
v___x_249_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v_type_236_, v___y_243_, v___y_244_, v___y_245_, v___y_246_, v___y_247_);
if (lean_obj_tag(v___x_249_) == 0)
{
lean_object* v_a_250_; lean_object* v___x_252_; uint8_t v_isShared_253_; uint8_t v_isSharedCheck_262_; 
v_a_250_ = lean_ctor_get(v___x_249_, 0);
v_isSharedCheck_262_ = !lean_is_exclusive(v___x_249_);
if (v_isSharedCheck_262_ == 0)
{
v___x_252_ = v___x_249_;
v_isShared_253_ = v_isSharedCheck_262_;
goto v_resetjp_251_;
}
else
{
lean_inc(v_a_250_);
lean_dec(v___x_249_);
v___x_252_ = lean_box(0);
v_isShared_253_ = v_isSharedCheck_262_;
goto v_resetjp_251_;
}
v_resetjp_251_:
{
if (lean_obj_tag(v_a_250_) == 1)
{
lean_object* v_val_254_; lean_object* v___x_256_; 
lean_dec_ref(v_type_236_);
v_val_254_ = lean_ctor_get(v_a_250_, 0);
lean_inc(v_val_254_);
lean_dec_ref_known(v_a_250_, 1);
if (v_isShared_253_ == 0)
{
lean_ctor_set(v___x_252_, 0, v_val_254_);
v___x_256_ = v___x_252_;
goto v_reusejp_255_;
}
else
{
lean_object* v_reuseFailAlloc_257_; 
v_reuseFailAlloc_257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_257_, 0, v_val_254_);
v___x_256_ = v_reuseFailAlloc_257_;
goto v_reusejp_255_;
}
v_reusejp_255_:
{
return v___x_256_;
}
}
else
{
lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; 
lean_del_object(v___x_252_);
lean_dec(v_a_250_);
v___x_258_ = lean_obj_once(&l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__2_spec__3___closed__1, &l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__2_spec__3___closed__1_once, _init_l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__2_spec__3___closed__1);
v___x_259_ = l_Lean_indentExpr(v_type_236_);
v___x_260_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_260_, 0, v___x_258_);
lean_ctor_set(v___x_260_, 1, v___x_259_);
v___x_261_ = l_Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__2_spec__3_spec__4___redArg(v___x_260_, v___y_244_, v___y_245_, v___y_246_, v___y_247_);
return v___x_261_;
}
}
}
else
{
lean_object* v_a_263_; lean_object* v___x_265_; uint8_t v_isShared_266_; uint8_t v_isSharedCheck_270_; 
lean_dec_ref(v_type_236_);
v_a_263_ = lean_ctor_get(v___x_249_, 0);
v_isSharedCheck_270_ = !lean_is_exclusive(v___x_249_);
if (v_isSharedCheck_270_ == 0)
{
v___x_265_ = v___x_249_;
v_isShared_266_ = v_isSharedCheck_270_;
goto v_resetjp_264_;
}
else
{
lean_inc(v_a_263_);
lean_dec(v___x_249_);
v___x_265_ = lean_box(0);
v_isShared_266_ = v_isSharedCheck_270_;
goto v_resetjp_264_;
}
v_resetjp_264_:
{
lean_object* v___x_268_; 
if (v_isShared_266_ == 0)
{
v___x_268_ = v___x_265_;
goto v_reusejp_267_;
}
else
{
lean_object* v_reuseFailAlloc_269_; 
v_reuseFailAlloc_269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_269_, 0, v_a_263_);
v___x_268_ = v_reuseFailAlloc_269_;
goto v_reusejp_267_;
}
v_reusejp_267_:
{
return v___x_268_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__2_spec__3___boxed(lean_object* v_type_271_, lean_object* v___y_272_, lean_object* v___y_273_, lean_object* v___y_274_, lean_object* v___y_275_, lean_object* v___y_276_, lean_object* v___y_277_, lean_object* v___y_278_, lean_object* v___y_279_, lean_object* v___y_280_, lean_object* v___y_281_, lean_object* v___y_282_, lean_object* v___y_283_){
_start:
{
lean_object* v_res_284_; 
v_res_284_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__2_spec__3(v_type_271_, v___y_272_, v___y_273_, v___y_274_, v___y_275_, v___y_276_, v___y_277_, v___y_278_, v___y_279_, v___y_280_, v___y_281_, v___y_282_);
lean_dec(v___y_282_);
lean_dec_ref(v___y_281_);
lean_dec(v___y_280_);
lean_dec_ref(v___y_279_);
lean_dec(v___y_278_);
lean_dec_ref(v___y_277_);
lean_dec(v___y_276_);
lean_dec_ref(v___y_275_);
lean_dec(v___y_274_);
lean_dec(v___y_273_);
lean_dec_ref(v___y_272_);
return v_res_284_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__2(lean_object* v_type_285_, lean_object* v_u_286_, lean_object* v_instDeclName_287_, lean_object* v_declName_288_, lean_object* v_expectedInst_289_, lean_object* v___y_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_, lean_object* v___y_294_, lean_object* v___y_295_, lean_object* v___y_296_, lean_object* v___y_297_, lean_object* v___y_298_, lean_object* v___y_299_, lean_object* v___y_300_){
_start:
{
lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; 
v___x_302_ = lean_box(0);
v___x_303_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_303_, 0, v_u_286_);
lean_ctor_set(v___x_303_, 1, v___x_302_);
lean_inc_ref(v___x_303_);
v___x_304_ = l_Lean_mkConst(v_instDeclName_287_, v___x_303_);
lean_inc_ref(v_type_285_);
v___x_305_ = l_Lean_Expr_app___override(v___x_304_, v_type_285_);
v___x_306_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__2_spec__3(v___x_305_, v___y_290_, v___y_291_, v___y_292_, v___y_293_, v___y_294_, v___y_295_, v___y_296_, v___y_297_, v___y_298_, v___y_299_, v___y_300_);
if (lean_obj_tag(v___x_306_) == 0)
{
lean_object* v_a_307_; lean_object* v___x_308_; 
v_a_307_ = lean_ctor_get(v___x_306_, 0);
lean_inc_n(v_a_307_, 2);
lean_dec_ref_known(v___x_306_, 1);
lean_inc(v_declName_288_);
v___x_308_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst(v_declName_288_, v_a_307_, v_expectedInst_289_, v___y_297_, v___y_298_, v___y_299_, v___y_300_);
if (lean_obj_tag(v___x_308_) == 0)
{
lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; 
lean_dec_ref_known(v___x_308_, 1);
v___x_309_ = l_Lean_mkConst(v_declName_288_, v___x_303_);
v___x_310_ = l_Lean_mkAppB(v___x_309_, v_type_285_, v_a_307_);
v___x_311_ = l_Lean_Meta_Sym_canon(v___x_310_, v___y_295_, v___y_296_, v___y_297_, v___y_298_, v___y_299_, v___y_300_);
if (lean_obj_tag(v___x_311_) == 0)
{
lean_object* v_a_312_; lean_object* v___x_313_; 
v_a_312_ = lean_ctor_get(v___x_311_, 0);
lean_inc(v_a_312_);
lean_dec_ref_known(v___x_311_, 1);
v___x_313_ = l_Lean_Meta_Sym_shareCommon(v_a_312_, v___y_295_, v___y_296_, v___y_297_, v___y_298_, v___y_299_, v___y_300_);
return v___x_313_;
}
else
{
return v___x_311_;
}
}
else
{
lean_object* v_a_314_; lean_object* v___x_316_; uint8_t v_isShared_317_; uint8_t v_isSharedCheck_321_; 
lean_dec(v_a_307_);
lean_dec_ref_known(v___x_303_, 2);
lean_dec(v_declName_288_);
lean_dec_ref(v_type_285_);
v_a_314_ = lean_ctor_get(v___x_308_, 0);
v_isSharedCheck_321_ = !lean_is_exclusive(v___x_308_);
if (v_isSharedCheck_321_ == 0)
{
v___x_316_ = v___x_308_;
v_isShared_317_ = v_isSharedCheck_321_;
goto v_resetjp_315_;
}
else
{
lean_inc(v_a_314_);
lean_dec(v___x_308_);
v___x_316_ = lean_box(0);
v_isShared_317_ = v_isSharedCheck_321_;
goto v_resetjp_315_;
}
v_resetjp_315_:
{
lean_object* v___x_319_; 
if (v_isShared_317_ == 0)
{
v___x_319_ = v___x_316_;
goto v_reusejp_318_;
}
else
{
lean_object* v_reuseFailAlloc_320_; 
v_reuseFailAlloc_320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_320_, 0, v_a_314_);
v___x_319_ = v_reuseFailAlloc_320_;
goto v_reusejp_318_;
}
v_reusejp_318_:
{
return v___x_319_;
}
}
}
}
else
{
lean_dec_ref_known(v___x_303_, 2);
lean_dec_ref(v_expectedInst_289_);
lean_dec(v_declName_288_);
lean_dec_ref(v_type_285_);
return v___x_306_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__2___boxed(lean_object** _args){
lean_object* v_type_322_ = _args[0];
lean_object* v_u_323_ = _args[1];
lean_object* v_instDeclName_324_ = _args[2];
lean_object* v_declName_325_ = _args[3];
lean_object* v_expectedInst_326_ = _args[4];
lean_object* v___y_327_ = _args[5];
lean_object* v___y_328_ = _args[6];
lean_object* v___y_329_ = _args[7];
lean_object* v___y_330_ = _args[8];
lean_object* v___y_331_ = _args[9];
lean_object* v___y_332_ = _args[10];
lean_object* v___y_333_ = _args[11];
lean_object* v___y_334_ = _args[12];
lean_object* v___y_335_ = _args[13];
lean_object* v___y_336_ = _args[14];
lean_object* v___y_337_ = _args[15];
lean_object* v___y_338_ = _args[16];
_start:
{
lean_object* v_res_339_; 
v_res_339_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__2(v_type_322_, v_u_323_, v_instDeclName_324_, v_declName_325_, v_expectedInst_326_, v___y_327_, v___y_328_, v___y_329_, v___y_330_, v___y_331_, v___y_332_, v___y_333_, v___y_334_, v___y_335_, v___y_336_, v___y_337_);
lean_dec(v___y_337_);
lean_dec_ref(v___y_336_);
lean_dec(v___y_335_);
lean_dec_ref(v___y_334_);
lean_dec(v___y_333_);
lean_dec_ref(v___y_332_);
lean_dec(v___y_331_);
lean_dec_ref(v___y_330_);
lean_dec(v___y_329_);
lean_dec(v___y_328_);
lean_dec_ref(v___y_327_);
return v_res_339_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0___lam__0(lean_object* v_a_340_, lean_object* v_s_341_){
_start:
{
lean_object* v_toRing_342_; lean_object* v_invFn_x3f_343_; lean_object* v_divFn_x3f_344_; lean_object* v_semiringId_x3f_345_; lean_object* v_commSemiringInst_346_; lean_object* v_commRingInst_347_; lean_object* v_noZeroDivInst_x3f_348_; lean_object* v_fieldInst_x3f_349_; lean_object* v_powIdentityInst_x3f_350_; lean_object* v___x_352_; uint8_t v_isShared_353_; uint8_t v_isSharedCheck_382_; 
v_toRing_342_ = lean_ctor_get(v_s_341_, 0);
v_invFn_x3f_343_ = lean_ctor_get(v_s_341_, 1);
v_divFn_x3f_344_ = lean_ctor_get(v_s_341_, 2);
v_semiringId_x3f_345_ = lean_ctor_get(v_s_341_, 3);
v_commSemiringInst_346_ = lean_ctor_get(v_s_341_, 4);
v_commRingInst_347_ = lean_ctor_get(v_s_341_, 5);
v_noZeroDivInst_x3f_348_ = lean_ctor_get(v_s_341_, 6);
v_fieldInst_x3f_349_ = lean_ctor_get(v_s_341_, 7);
v_powIdentityInst_x3f_350_ = lean_ctor_get(v_s_341_, 8);
v_isSharedCheck_382_ = !lean_is_exclusive(v_s_341_);
if (v_isSharedCheck_382_ == 0)
{
v___x_352_ = v_s_341_;
v_isShared_353_ = v_isSharedCheck_382_;
goto v_resetjp_351_;
}
else
{
lean_inc(v_powIdentityInst_x3f_350_);
lean_inc(v_fieldInst_x3f_349_);
lean_inc(v_noZeroDivInst_x3f_348_);
lean_inc(v_commRingInst_347_);
lean_inc(v_commSemiringInst_346_);
lean_inc(v_semiringId_x3f_345_);
lean_inc(v_divFn_x3f_344_);
lean_inc(v_invFn_x3f_343_);
lean_inc(v_toRing_342_);
lean_dec(v_s_341_);
v___x_352_ = lean_box(0);
v_isShared_353_ = v_isSharedCheck_382_;
goto v_resetjp_351_;
}
v_resetjp_351_:
{
lean_object* v_id_354_; lean_object* v_type_355_; lean_object* v_u_356_; lean_object* v_ringInst_357_; lean_object* v_semiringInst_358_; lean_object* v_charInst_x3f_359_; uint8_t v_symbolicChar_360_; lean_object* v_addFn_x3f_361_; lean_object* v_mulFn_x3f_362_; lean_object* v_subFn_x3f_363_; lean_object* v_powFn_x3f_364_; lean_object* v_intCastFn_x3f_365_; lean_object* v_natCastFn_x3f_366_; lean_object* v_natSMulFn_x3f_367_; lean_object* v_intSMulFn_x3f_368_; lean_object* v_one_x3f_369_; lean_object* v___x_371_; uint8_t v_isShared_372_; uint8_t v_isSharedCheck_380_; 
v_id_354_ = lean_ctor_get(v_toRing_342_, 0);
v_type_355_ = lean_ctor_get(v_toRing_342_, 1);
v_u_356_ = lean_ctor_get(v_toRing_342_, 2);
v_ringInst_357_ = lean_ctor_get(v_toRing_342_, 3);
v_semiringInst_358_ = lean_ctor_get(v_toRing_342_, 4);
v_charInst_x3f_359_ = lean_ctor_get(v_toRing_342_, 5);
v_symbolicChar_360_ = lean_ctor_get_uint8(v_toRing_342_, sizeof(void*)*16);
v_addFn_x3f_361_ = lean_ctor_get(v_toRing_342_, 6);
v_mulFn_x3f_362_ = lean_ctor_get(v_toRing_342_, 7);
v_subFn_x3f_363_ = lean_ctor_get(v_toRing_342_, 8);
v_powFn_x3f_364_ = lean_ctor_get(v_toRing_342_, 10);
v_intCastFn_x3f_365_ = lean_ctor_get(v_toRing_342_, 11);
v_natCastFn_x3f_366_ = lean_ctor_get(v_toRing_342_, 12);
v_natSMulFn_x3f_367_ = lean_ctor_get(v_toRing_342_, 13);
v_intSMulFn_x3f_368_ = lean_ctor_get(v_toRing_342_, 14);
v_one_x3f_369_ = lean_ctor_get(v_toRing_342_, 15);
v_isSharedCheck_380_ = !lean_is_exclusive(v_toRing_342_);
if (v_isSharedCheck_380_ == 0)
{
lean_object* v_unused_381_; 
v_unused_381_ = lean_ctor_get(v_toRing_342_, 9);
lean_dec(v_unused_381_);
v___x_371_ = v_toRing_342_;
v_isShared_372_ = v_isSharedCheck_380_;
goto v_resetjp_370_;
}
else
{
lean_inc(v_one_x3f_369_);
lean_inc(v_intSMulFn_x3f_368_);
lean_inc(v_natSMulFn_x3f_367_);
lean_inc(v_natCastFn_x3f_366_);
lean_inc(v_intCastFn_x3f_365_);
lean_inc(v_powFn_x3f_364_);
lean_inc(v_subFn_x3f_363_);
lean_inc(v_mulFn_x3f_362_);
lean_inc(v_addFn_x3f_361_);
lean_inc(v_charInst_x3f_359_);
lean_inc(v_semiringInst_358_);
lean_inc(v_ringInst_357_);
lean_inc(v_u_356_);
lean_inc(v_type_355_);
lean_inc(v_id_354_);
lean_dec(v_toRing_342_);
v___x_371_ = lean_box(0);
v_isShared_372_ = v_isSharedCheck_380_;
goto v_resetjp_370_;
}
v_resetjp_370_:
{
lean_object* v___x_373_; lean_object* v___x_375_; 
v___x_373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_373_, 0, v_a_340_);
if (v_isShared_372_ == 0)
{
lean_ctor_set(v___x_371_, 9, v___x_373_);
v___x_375_ = v___x_371_;
goto v_reusejp_374_;
}
else
{
lean_object* v_reuseFailAlloc_379_; 
v_reuseFailAlloc_379_ = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(v_reuseFailAlloc_379_, 0, v_id_354_);
lean_ctor_set(v_reuseFailAlloc_379_, 1, v_type_355_);
lean_ctor_set(v_reuseFailAlloc_379_, 2, v_u_356_);
lean_ctor_set(v_reuseFailAlloc_379_, 3, v_ringInst_357_);
lean_ctor_set(v_reuseFailAlloc_379_, 4, v_semiringInst_358_);
lean_ctor_set(v_reuseFailAlloc_379_, 5, v_charInst_x3f_359_);
lean_ctor_set(v_reuseFailAlloc_379_, 6, v_addFn_x3f_361_);
lean_ctor_set(v_reuseFailAlloc_379_, 7, v_mulFn_x3f_362_);
lean_ctor_set(v_reuseFailAlloc_379_, 8, v_subFn_x3f_363_);
lean_ctor_set(v_reuseFailAlloc_379_, 9, v___x_373_);
lean_ctor_set(v_reuseFailAlloc_379_, 10, v_powFn_x3f_364_);
lean_ctor_set(v_reuseFailAlloc_379_, 11, v_intCastFn_x3f_365_);
lean_ctor_set(v_reuseFailAlloc_379_, 12, v_natCastFn_x3f_366_);
lean_ctor_set(v_reuseFailAlloc_379_, 13, v_natSMulFn_x3f_367_);
lean_ctor_set(v_reuseFailAlloc_379_, 14, v_intSMulFn_x3f_368_);
lean_ctor_set(v_reuseFailAlloc_379_, 15, v_one_x3f_369_);
lean_ctor_set_uint8(v_reuseFailAlloc_379_, sizeof(void*)*16, v_symbolicChar_360_);
v___x_375_ = v_reuseFailAlloc_379_;
goto v_reusejp_374_;
}
v_reusejp_374_:
{
lean_object* v___x_377_; 
if (v_isShared_353_ == 0)
{
lean_ctor_set(v___x_352_, 0, v___x_375_);
v___x_377_ = v___x_352_;
goto v_reusejp_376_;
}
else
{
lean_object* v_reuseFailAlloc_378_; 
v_reuseFailAlloc_378_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_378_, 0, v___x_375_);
lean_ctor_set(v_reuseFailAlloc_378_, 1, v_invFn_x3f_343_);
lean_ctor_set(v_reuseFailAlloc_378_, 2, v_divFn_x3f_344_);
lean_ctor_set(v_reuseFailAlloc_378_, 3, v_semiringId_x3f_345_);
lean_ctor_set(v_reuseFailAlloc_378_, 4, v_commSemiringInst_346_);
lean_ctor_set(v_reuseFailAlloc_378_, 5, v_commRingInst_347_);
lean_ctor_set(v_reuseFailAlloc_378_, 6, v_noZeroDivInst_x3f_348_);
lean_ctor_set(v_reuseFailAlloc_378_, 7, v_fieldInst_x3f_349_);
lean_ctor_set(v_reuseFailAlloc_378_, 8, v_powIdentityInst_x3f_350_);
v___x_377_ = v_reuseFailAlloc_378_;
goto v_reusejp_376_;
}
v_reusejp_376_:
{
return v___x_377_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0(lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_, lean_object* v___y_397_, lean_object* v___y_398_, lean_object* v___y_399_, lean_object* v___y_400_, lean_object* v___y_401_, lean_object* v___y_402_, lean_object* v___y_403_, lean_object* v___y_404_){
_start:
{
lean_object* v___x_406_; 
v___x_406_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v___y_394_, v___y_395_, v___y_396_, v___y_397_, v___y_398_, v___y_399_, v___y_400_, v___y_401_, v___y_402_, v___y_403_, v___y_404_);
if (lean_obj_tag(v___x_406_) == 0)
{
lean_object* v_a_407_; lean_object* v___x_409_; uint8_t v_isShared_410_; uint8_t v_isSharedCheck_447_; 
v_a_407_ = lean_ctor_get(v___x_406_, 0);
v_isSharedCheck_447_ = !lean_is_exclusive(v___x_406_);
if (v_isSharedCheck_447_ == 0)
{
v___x_409_ = v___x_406_;
v_isShared_410_ = v_isSharedCheck_447_;
goto v_resetjp_408_;
}
else
{
lean_inc(v_a_407_);
lean_dec(v___x_406_);
v___x_409_ = lean_box(0);
v_isShared_410_ = v_isSharedCheck_447_;
goto v_resetjp_408_;
}
v_resetjp_408_:
{
lean_object* v_toRing_411_; lean_object* v_negFn_x3f_412_; 
v_toRing_411_ = lean_ctor_get(v_a_407_, 0);
lean_inc_ref(v_toRing_411_);
lean_dec(v_a_407_);
v_negFn_x3f_412_ = lean_ctor_get(v_toRing_411_, 9);
if (lean_obj_tag(v_negFn_x3f_412_) == 1)
{
lean_object* v_val_413_; lean_object* v___x_415_; 
lean_inc_ref(v_negFn_x3f_412_);
lean_dec_ref(v_toRing_411_);
v_val_413_ = lean_ctor_get(v_negFn_x3f_412_, 0);
lean_inc(v_val_413_);
lean_dec_ref_known(v_negFn_x3f_412_, 1);
if (v_isShared_410_ == 0)
{
lean_ctor_set(v___x_409_, 0, v_val_413_);
v___x_415_ = v___x_409_;
goto v_reusejp_414_;
}
else
{
lean_object* v_reuseFailAlloc_416_; 
v_reuseFailAlloc_416_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_416_, 0, v_val_413_);
v___x_415_ = v_reuseFailAlloc_416_;
goto v_reusejp_414_;
}
v_reusejp_414_:
{
return v___x_415_;
}
}
else
{
lean_object* v_type_417_; lean_object* v_u_418_; lean_object* v_ringInst_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v_expectedInst_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; 
lean_del_object(v___x_409_);
v_type_417_ = lean_ctor_get(v_toRing_411_, 1);
lean_inc_ref_n(v_type_417_, 2);
v_u_418_ = lean_ctor_get(v_toRing_411_, 2);
lean_inc_n(v_u_418_, 2);
v_ringInst_419_ = lean_ctor_get(v_toRing_411_, 3);
lean_inc_ref(v_ringInst_419_);
lean_dec_ref(v_toRing_411_);
v___x_420_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0___closed__4));
v___x_421_ = lean_box(0);
v___x_422_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_422_, 0, v_u_418_);
lean_ctor_set(v___x_422_, 1, v___x_421_);
v___x_423_ = l_Lean_mkConst(v___x_420_, v___x_422_);
v_expectedInst_424_ = l_Lean_mkAppB(v___x_423_, v_type_417_, v_ringInst_419_);
v___x_425_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0___closed__5));
v___x_426_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__11));
v___x_427_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__2(v_type_417_, v_u_418_, v___x_425_, v___x_426_, v_expectedInst_424_, v___y_394_, v___y_395_, v___y_396_, v___y_397_, v___y_398_, v___y_399_, v___y_400_, v___y_401_, v___y_402_, v___y_403_, v___y_404_);
if (lean_obj_tag(v___x_427_) == 0)
{
lean_object* v_a_428_; lean_object* v___f_429_; lean_object* v___x_430_; 
v_a_428_ = lean_ctor_get(v___x_427_, 0);
lean_inc_n(v_a_428_, 2);
lean_dec_ref_known(v___x_427_, 1);
v___f_429_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0___lam__0), 2, 1);
lean_closure_set(v___f_429_, 0, v_a_428_);
v___x_430_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(v___f_429_, v___y_394_, v___y_400_);
if (lean_obj_tag(v___x_430_) == 0)
{
lean_object* v___x_432_; uint8_t v_isShared_433_; uint8_t v_isSharedCheck_437_; 
v_isSharedCheck_437_ = !lean_is_exclusive(v___x_430_);
if (v_isSharedCheck_437_ == 0)
{
lean_object* v_unused_438_; 
v_unused_438_ = lean_ctor_get(v___x_430_, 0);
lean_dec(v_unused_438_);
v___x_432_ = v___x_430_;
v_isShared_433_ = v_isSharedCheck_437_;
goto v_resetjp_431_;
}
else
{
lean_dec(v___x_430_);
v___x_432_ = lean_box(0);
v_isShared_433_ = v_isSharedCheck_437_;
goto v_resetjp_431_;
}
v_resetjp_431_:
{
lean_object* v___x_435_; 
if (v_isShared_433_ == 0)
{
lean_ctor_set(v___x_432_, 0, v_a_428_);
v___x_435_ = v___x_432_;
goto v_reusejp_434_;
}
else
{
lean_object* v_reuseFailAlloc_436_; 
v_reuseFailAlloc_436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_436_, 0, v_a_428_);
v___x_435_ = v_reuseFailAlloc_436_;
goto v_reusejp_434_;
}
v_reusejp_434_:
{
return v___x_435_;
}
}
}
else
{
lean_object* v_a_439_; lean_object* v___x_441_; uint8_t v_isShared_442_; uint8_t v_isSharedCheck_446_; 
lean_dec(v_a_428_);
v_a_439_ = lean_ctor_get(v___x_430_, 0);
v_isSharedCheck_446_ = !lean_is_exclusive(v___x_430_);
if (v_isSharedCheck_446_ == 0)
{
v___x_441_ = v___x_430_;
v_isShared_442_ = v_isSharedCheck_446_;
goto v_resetjp_440_;
}
else
{
lean_inc(v_a_439_);
lean_dec(v___x_430_);
v___x_441_ = lean_box(0);
v_isShared_442_ = v_isSharedCheck_446_;
goto v_resetjp_440_;
}
v_resetjp_440_:
{
lean_object* v___x_444_; 
if (v_isShared_442_ == 0)
{
v___x_444_ = v___x_441_;
goto v_reusejp_443_;
}
else
{
lean_object* v_reuseFailAlloc_445_; 
v_reuseFailAlloc_445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_445_, 0, v_a_439_);
v___x_444_ = v_reuseFailAlloc_445_;
goto v_reusejp_443_;
}
v_reusejp_443_:
{
return v___x_444_;
}
}
}
}
else
{
return v___x_427_;
}
}
}
}
else
{
lean_object* v_a_448_; lean_object* v___x_450_; uint8_t v_isShared_451_; uint8_t v_isSharedCheck_455_; 
v_a_448_ = lean_ctor_get(v___x_406_, 0);
v_isSharedCheck_455_ = !lean_is_exclusive(v___x_406_);
if (v_isSharedCheck_455_ == 0)
{
v___x_450_ = v___x_406_;
v_isShared_451_ = v_isSharedCheck_455_;
goto v_resetjp_449_;
}
else
{
lean_inc(v_a_448_);
lean_dec(v___x_406_);
v___x_450_ = lean_box(0);
v_isShared_451_ = v_isSharedCheck_455_;
goto v_resetjp_449_;
}
v_resetjp_449_:
{
lean_object* v___x_453_; 
if (v_isShared_451_ == 0)
{
v___x_453_ = v___x_450_;
goto v_reusejp_452_;
}
else
{
lean_object* v_reuseFailAlloc_454_; 
v_reuseFailAlloc_454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_454_, 0, v_a_448_);
v___x_453_ = v_reuseFailAlloc_454_;
goto v_reusejp_452_;
}
v_reusejp_452_:
{
return v___x_453_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0___boxed(lean_object* v___y_456_, lean_object* v___y_457_, lean_object* v___y_458_, lean_object* v___y_459_, lean_object* v___y_460_, lean_object* v___y_461_, lean_object* v___y_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_){
_start:
{
lean_object* v_res_468_; 
v_res_468_ = l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0(v___y_456_, v___y_457_, v___y_458_, v___y_459_, v___y_460_, v___y_461_, v___y_462_, v___y_463_, v___y_464_, v___y_465_, v___y_466_);
lean_dec(v___y_466_);
lean_dec_ref(v___y_465_);
lean_dec(v___y_464_);
lean_dec_ref(v___y_463_);
lean_dec(v___y_462_);
lean_dec_ref(v___y_461_);
lean_dec(v___y_460_);
lean_dec_ref(v___y_459_);
lean_dec(v___y_458_);
lean_dec(v___y_457_);
lean_dec_ref(v___y_456_);
return v_res_468_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0(lean_object* v_inst_469_, lean_object* v___y_470_, lean_object* v___y_471_, lean_object* v___y_472_, lean_object* v___y_473_, lean_object* v___y_474_, lean_object* v___y_475_, lean_object* v___y_476_, lean_object* v___y_477_, lean_object* v___y_478_, lean_object* v___y_479_, lean_object* v___y_480_){
_start:
{
lean_object* v___x_482_; 
v___x_482_ = l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0(v___y_470_, v___y_471_, v___y_472_, v___y_473_, v___y_474_, v___y_475_, v___y_476_, v___y_477_, v___y_478_, v___y_479_, v___y_480_);
if (lean_obj_tag(v___x_482_) == 0)
{
lean_object* v_a_483_; lean_object* v___x_485_; uint8_t v_isShared_486_; uint8_t v_isSharedCheck_495_; 
v_a_483_ = lean_ctor_get(v___x_482_, 0);
v_isSharedCheck_495_ = !lean_is_exclusive(v___x_482_);
if (v_isSharedCheck_495_ == 0)
{
v___x_485_ = v___x_482_;
v_isShared_486_ = v_isSharedCheck_495_;
goto v_resetjp_484_;
}
else
{
lean_inc(v_a_483_);
lean_dec(v___x_482_);
v___x_485_ = lean_box(0);
v_isShared_486_ = v_isSharedCheck_495_;
goto v_resetjp_484_;
}
v_resetjp_484_:
{
lean_object* v___x_487_; size_t v___x_488_; size_t v___x_489_; uint8_t v___x_490_; lean_object* v___x_491_; lean_object* v___x_493_; 
v___x_487_ = l_Lean_Expr_appArg_x21(v_a_483_);
lean_dec(v_a_483_);
v___x_488_ = lean_ptr_addr(v___x_487_);
lean_dec_ref(v___x_487_);
v___x_489_ = lean_ptr_addr(v_inst_469_);
v___x_490_ = lean_usize_dec_eq(v___x_488_, v___x_489_);
v___x_491_ = lean_box(v___x_490_);
if (v_isShared_486_ == 0)
{
lean_ctor_set(v___x_485_, 0, v___x_491_);
v___x_493_ = v___x_485_;
goto v_reusejp_492_;
}
else
{
lean_object* v_reuseFailAlloc_494_; 
v_reuseFailAlloc_494_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_494_, 0, v___x_491_);
v___x_493_ = v_reuseFailAlloc_494_;
goto v_reusejp_492_;
}
v_reusejp_492_:
{
return v___x_493_;
}
}
}
else
{
lean_object* v_a_496_; lean_object* v___x_498_; uint8_t v_isShared_499_; uint8_t v_isSharedCheck_503_; 
v_a_496_ = lean_ctor_get(v___x_482_, 0);
v_isSharedCheck_503_ = !lean_is_exclusive(v___x_482_);
if (v_isSharedCheck_503_ == 0)
{
v___x_498_ = v___x_482_;
v_isShared_499_ = v_isSharedCheck_503_;
goto v_resetjp_497_;
}
else
{
lean_inc(v_a_496_);
lean_dec(v___x_482_);
v___x_498_ = lean_box(0);
v_isShared_499_ = v_isSharedCheck_503_;
goto v_resetjp_497_;
}
v_resetjp_497_:
{
lean_object* v___x_501_; 
if (v_isShared_499_ == 0)
{
v___x_501_ = v___x_498_;
goto v_reusejp_500_;
}
else
{
lean_object* v_reuseFailAlloc_502_; 
v_reuseFailAlloc_502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_502_, 0, v_a_496_);
v___x_501_ = v_reuseFailAlloc_502_;
goto v_reusejp_500_;
}
v_reusejp_500_:
{
return v___x_501_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0___boxed(lean_object* v_inst_504_, lean_object* v___y_505_, lean_object* v___y_506_, lean_object* v___y_507_, lean_object* v___y_508_, lean_object* v___y_509_, lean_object* v___y_510_, lean_object* v___y_511_, lean_object* v___y_512_, lean_object* v___y_513_, lean_object* v___y_514_, lean_object* v___y_515_, lean_object* v___y_516_){
_start:
{
lean_object* v_res_517_; 
v_res_517_ = l_Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0(v_inst_504_, v___y_505_, v___y_506_, v___y_507_, v___y_508_, v___y_509_, v___y_510_, v___y_511_, v___y_512_, v___y_513_, v___y_514_, v___y_515_);
lean_dec(v___y_515_);
lean_dec_ref(v___y_514_);
lean_dec(v___y_513_);
lean_dec_ref(v___y_512_);
lean_dec(v___y_511_);
lean_dec_ref(v___y_510_);
lean_dec(v___y_509_);
lean_dec_ref(v___y_508_);
lean_dec(v___y_507_);
lean_dec(v___y_506_);
lean_dec_ref(v___y_505_);
lean_dec_ref(v_inst_504_);
return v_res_517_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f(lean_object* v_e_518_, lean_object* v_a_519_, lean_object* v_a_520_, lean_object* v_a_521_, lean_object* v_a_522_, lean_object* v_a_523_, lean_object* v_a_524_, lean_object* v_a_525_, lean_object* v_a_526_, lean_object* v_a_527_, lean_object* v_a_528_, lean_object* v_a_529_){
_start:
{
lean_object* v___x_537_; 
v___x_537_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_518_, v_a_527_);
if (lean_obj_tag(v___x_537_) == 0)
{
lean_object* v_a_538_; lean_object* v___x_539_; uint8_t v___x_540_; 
v_a_538_ = lean_ctor_get(v___x_537_, 0);
lean_inc(v_a_538_);
lean_dec_ref_known(v___x_537_, 1);
v___x_539_ = l_Lean_Expr_cleanupAnnotations(v_a_538_);
lean_dec(v_a_538_);
v___x_540_ = l_Lean_Expr_isApp(v___x_539_);
if (v___x_540_ == 0)
{
lean_dec_ref(v___x_539_);
goto v___jp_531_;
}
else
{
lean_object* v___x_541_; uint8_t v___x_542_; 
v___x_541_ = l_Lean_Expr_appFnCleanup___redArg(v___x_539_);
v___x_542_ = l_Lean_Expr_isApp(v___x_541_);
if (v___x_542_ == 0)
{
lean_dec_ref(v___x_541_);
lean_dec_ref(v___x_539_);
goto v___jp_531_;
}
else
{
lean_object* v___x_543_; uint8_t v___x_544_; 
v___x_543_ = l_Lean_Expr_appFnCleanup___redArg(v___x_541_);
v___x_544_ = l_Lean_Expr_isApp(v___x_543_);
if (v___x_544_ == 0)
{
lean_dec_ref(v___x_543_);
lean_dec_ref(v___x_541_);
lean_dec_ref(v___x_539_);
goto v___jp_531_;
}
else
{
lean_object* v_arg_545_; lean_object* v___x_546_; lean_object* v___x_547_; uint8_t v___x_548_; 
v_arg_545_ = lean_ctor_get(v___x_541_, 1);
lean_inc_ref(v_arg_545_);
lean_dec_ref(v___x_541_);
v___x_546_ = l_Lean_Expr_appFnCleanup___redArg(v___x_543_);
lean_dec_ref(v___x_543_);
v___x_547_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__8));
v___x_548_ = l_Lean_Expr_isConstOf(v___x_546_, v___x_547_);
if (v___x_548_ == 0)
{
lean_object* v___x_549_; uint8_t v___x_550_; 
v___x_549_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__11));
v___x_550_ = l_Lean_Expr_isConstOf(v___x_546_, v___x_549_);
lean_dec_ref(v___x_546_);
if (v___x_550_ == 0)
{
lean_dec_ref(v_arg_545_);
lean_dec_ref(v___x_539_);
goto v___jp_531_;
}
else
{
lean_object* v_arg_551_; lean_object* v___x_552_; 
v_arg_551_ = lean_ctor_get(v___x_539_, 1);
lean_inc_ref(v_arg_551_);
lean_dec_ref(v___x_539_);
v___x_552_ = l_Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0(v_arg_545_, v_a_519_, v_a_520_, v_a_521_, v_a_522_, v_a_523_, v_a_524_, v_a_525_, v_a_526_, v_a_527_, v_a_528_, v_a_529_);
lean_dec_ref(v_arg_545_);
if (lean_obj_tag(v___x_552_) == 0)
{
lean_object* v_a_553_; lean_object* v___x_555_; uint8_t v_isShared_556_; uint8_t v_isSharedCheck_608_; 
v_a_553_ = lean_ctor_get(v___x_552_, 0);
v_isSharedCheck_608_ = !lean_is_exclusive(v___x_552_);
if (v_isSharedCheck_608_ == 0)
{
v___x_555_ = v___x_552_;
v_isShared_556_ = v_isSharedCheck_608_;
goto v_resetjp_554_;
}
else
{
lean_inc(v_a_553_);
lean_dec(v___x_552_);
v___x_555_ = lean_box(0);
v_isShared_556_ = v_isSharedCheck_608_;
goto v_resetjp_554_;
}
v_resetjp_554_:
{
uint8_t v___x_557_; 
v___x_557_ = lean_unbox(v_a_553_);
lean_dec(v_a_553_);
if (v___x_557_ == 0)
{
lean_object* v___x_558_; lean_object* v___x_560_; 
lean_dec_ref(v_arg_551_);
v___x_558_ = lean_box(0);
if (v_isShared_556_ == 0)
{
lean_ctor_set(v___x_555_, 0, v___x_558_);
v___x_560_ = v___x_555_;
goto v_reusejp_559_;
}
else
{
lean_object* v_reuseFailAlloc_561_; 
v_reuseFailAlloc_561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_561_, 0, v___x_558_);
v___x_560_ = v_reuseFailAlloc_561_;
goto v_reusejp_559_;
}
v_reusejp_559_:
{
return v___x_560_;
}
}
else
{
lean_object* v___x_562_; uint8_t v___x_563_; 
lean_del_object(v___x_555_);
v___x_562_ = l_Lean_Expr_cleanupAnnotations(v_arg_551_);
lean_dec_ref(v_arg_551_);
v___x_563_ = l_Lean_Expr_isApp(v___x_562_);
if (v___x_563_ == 0)
{
lean_dec_ref(v___x_562_);
goto v___jp_534_;
}
else
{
lean_object* v___x_564_; uint8_t v___x_565_; 
v___x_564_ = l_Lean_Expr_appFnCleanup___redArg(v___x_562_);
lean_dec_ref(v___x_562_);
v___x_565_ = l_Lean_Expr_isApp(v___x_564_);
if (v___x_565_ == 0)
{
lean_dec_ref(v___x_564_);
goto v___jp_534_;
}
else
{
lean_object* v___x_566_; uint8_t v___x_567_; 
v___x_566_ = l_Lean_Expr_appFnCleanup___redArg(v___x_564_);
v___x_567_ = l_Lean_Expr_isApp(v___x_566_);
if (v___x_567_ == 0)
{
lean_dec_ref(v___x_566_);
lean_dec_ref(v___x_564_);
goto v___jp_534_;
}
else
{
lean_object* v___x_568_; uint8_t v___x_569_; 
v___x_568_ = l_Lean_Expr_appFnCleanup___redArg(v___x_566_);
lean_dec_ref(v___x_566_);
v___x_569_ = l_Lean_Expr_isConstOf(v___x_568_, v___x_547_);
lean_dec_ref(v___x_568_);
if (v___x_569_ == 0)
{
lean_dec_ref(v___x_564_);
goto v___jp_534_;
}
else
{
lean_object* v_arg_570_; lean_object* v___x_571_; 
v_arg_570_ = lean_ctor_get(v___x_564_, 1);
lean_inc_ref(v_arg_570_);
lean_dec_ref(v___x_564_);
v___x_571_ = l_Lean_Meta_getNatValue_x3f(v_arg_570_, v_a_526_, v_a_527_, v_a_528_, v_a_529_);
lean_dec_ref(v_arg_570_);
if (lean_obj_tag(v___x_571_) == 0)
{
lean_object* v_a_572_; lean_object* v___x_574_; uint8_t v_isShared_575_; uint8_t v_isSharedCheck_599_; 
v_a_572_ = lean_ctor_get(v___x_571_, 0);
v_isSharedCheck_599_ = !lean_is_exclusive(v___x_571_);
if (v_isSharedCheck_599_ == 0)
{
v___x_574_ = v___x_571_;
v_isShared_575_ = v_isSharedCheck_599_;
goto v_resetjp_573_;
}
else
{
lean_inc(v_a_572_);
lean_dec(v___x_571_);
v___x_574_ = lean_box(0);
v_isShared_575_ = v_isSharedCheck_599_;
goto v_resetjp_573_;
}
v_resetjp_573_:
{
if (lean_obj_tag(v_a_572_) == 1)
{
lean_object* v_val_576_; lean_object* v___x_578_; uint8_t v_isShared_579_; uint8_t v_isSharedCheck_594_; 
v_val_576_ = lean_ctor_get(v_a_572_, 0);
v_isSharedCheck_594_ = !lean_is_exclusive(v_a_572_);
if (v_isSharedCheck_594_ == 0)
{
v___x_578_ = v_a_572_;
v_isShared_579_ = v_isSharedCheck_594_;
goto v_resetjp_577_;
}
else
{
lean_inc(v_val_576_);
lean_dec(v_a_572_);
v___x_578_ = lean_box(0);
v_isShared_579_ = v_isSharedCheck_594_;
goto v_resetjp_577_;
}
v_resetjp_577_:
{
lean_object* v___x_580_; uint8_t v___x_581_; 
v___x_580_ = lean_unsigned_to_nat(0u);
v___x_581_ = lean_nat_dec_eq(v_val_576_, v___x_580_);
if (v___x_581_ == 0)
{
lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_585_; 
v___x_582_ = lean_nat_to_int(v_val_576_);
v___x_583_ = lean_int_neg(v___x_582_);
lean_dec(v___x_582_);
if (v_isShared_579_ == 0)
{
lean_ctor_set(v___x_578_, 0, v___x_583_);
v___x_585_ = v___x_578_;
goto v_reusejp_584_;
}
else
{
lean_object* v_reuseFailAlloc_589_; 
v_reuseFailAlloc_589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_589_, 0, v___x_583_);
v___x_585_ = v_reuseFailAlloc_589_;
goto v_reusejp_584_;
}
v_reusejp_584_:
{
lean_object* v___x_587_; 
if (v_isShared_575_ == 0)
{
lean_ctor_set(v___x_574_, 0, v___x_585_);
v___x_587_ = v___x_574_;
goto v_reusejp_586_;
}
else
{
lean_object* v_reuseFailAlloc_588_; 
v_reuseFailAlloc_588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_588_, 0, v___x_585_);
v___x_587_ = v_reuseFailAlloc_588_;
goto v_reusejp_586_;
}
v_reusejp_586_:
{
return v___x_587_;
}
}
}
else
{
lean_object* v___x_590_; lean_object* v___x_592_; 
lean_del_object(v___x_578_);
lean_dec(v_val_576_);
v___x_590_ = lean_box(0);
if (v_isShared_575_ == 0)
{
lean_ctor_set(v___x_574_, 0, v___x_590_);
v___x_592_ = v___x_574_;
goto v_reusejp_591_;
}
else
{
lean_object* v_reuseFailAlloc_593_; 
v_reuseFailAlloc_593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_593_, 0, v___x_590_);
v___x_592_ = v_reuseFailAlloc_593_;
goto v_reusejp_591_;
}
v_reusejp_591_:
{
return v___x_592_;
}
}
}
}
else
{
lean_object* v___x_595_; lean_object* v___x_597_; 
lean_dec(v_a_572_);
v___x_595_ = lean_box(0);
if (v_isShared_575_ == 0)
{
lean_ctor_set(v___x_574_, 0, v___x_595_);
v___x_597_ = v___x_574_;
goto v_reusejp_596_;
}
else
{
lean_object* v_reuseFailAlloc_598_; 
v_reuseFailAlloc_598_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_598_, 0, v___x_595_);
v___x_597_ = v_reuseFailAlloc_598_;
goto v_reusejp_596_;
}
v_reusejp_596_:
{
return v___x_597_;
}
}
}
}
else
{
lean_object* v_a_600_; lean_object* v___x_602_; uint8_t v_isShared_603_; uint8_t v_isSharedCheck_607_; 
v_a_600_ = lean_ctor_get(v___x_571_, 0);
v_isSharedCheck_607_ = !lean_is_exclusive(v___x_571_);
if (v_isSharedCheck_607_ == 0)
{
v___x_602_ = v___x_571_;
v_isShared_603_ = v_isSharedCheck_607_;
goto v_resetjp_601_;
}
else
{
lean_inc(v_a_600_);
lean_dec(v___x_571_);
v___x_602_ = lean_box(0);
v_isShared_603_ = v_isSharedCheck_607_;
goto v_resetjp_601_;
}
v_resetjp_601_:
{
lean_object* v___x_605_; 
if (v_isShared_603_ == 0)
{
v___x_605_ = v___x_602_;
goto v_reusejp_604_;
}
else
{
lean_object* v_reuseFailAlloc_606_; 
v_reuseFailAlloc_606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_606_, 0, v_a_600_);
v___x_605_ = v_reuseFailAlloc_606_;
goto v_reusejp_604_;
}
v_reusejp_604_:
{
return v___x_605_;
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
lean_object* v_a_609_; lean_object* v___x_611_; uint8_t v_isShared_612_; uint8_t v_isSharedCheck_616_; 
lean_dec_ref(v_arg_551_);
v_a_609_ = lean_ctor_get(v___x_552_, 0);
v_isSharedCheck_616_ = !lean_is_exclusive(v___x_552_);
if (v_isSharedCheck_616_ == 0)
{
v___x_611_ = v___x_552_;
v_isShared_612_ = v_isSharedCheck_616_;
goto v_resetjp_610_;
}
else
{
lean_inc(v_a_609_);
lean_dec(v___x_552_);
v___x_611_ = lean_box(0);
v_isShared_612_ = v_isSharedCheck_616_;
goto v_resetjp_610_;
}
v_resetjp_610_:
{
lean_object* v___x_614_; 
if (v_isShared_612_ == 0)
{
v___x_614_ = v___x_611_;
goto v_reusejp_613_;
}
else
{
lean_object* v_reuseFailAlloc_615_; 
v_reuseFailAlloc_615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_615_, 0, v_a_609_);
v___x_614_ = v_reuseFailAlloc_615_;
goto v_reusejp_613_;
}
v_reusejp_613_:
{
return v___x_614_;
}
}
}
}
}
else
{
lean_object* v___x_617_; 
lean_dec_ref(v___x_546_);
lean_dec_ref(v___x_539_);
v___x_617_ = l_Lean_Meta_getNatValue_x3f(v_arg_545_, v_a_526_, v_a_527_, v_a_528_, v_a_529_);
lean_dec_ref(v_arg_545_);
if (lean_obj_tag(v___x_617_) == 0)
{
lean_object* v_a_618_; lean_object* v___x_620_; uint8_t v_isShared_621_; uint8_t v_isSharedCheck_638_; 
v_a_618_ = lean_ctor_get(v___x_617_, 0);
v_isSharedCheck_638_ = !lean_is_exclusive(v___x_617_);
if (v_isSharedCheck_638_ == 0)
{
v___x_620_ = v___x_617_;
v_isShared_621_ = v_isSharedCheck_638_;
goto v_resetjp_619_;
}
else
{
lean_inc(v_a_618_);
lean_dec(v___x_617_);
v___x_620_ = lean_box(0);
v_isShared_621_ = v_isSharedCheck_638_;
goto v_resetjp_619_;
}
v_resetjp_619_:
{
if (lean_obj_tag(v_a_618_) == 1)
{
lean_object* v_val_622_; lean_object* v___x_624_; uint8_t v_isShared_625_; uint8_t v_isSharedCheck_633_; 
v_val_622_ = lean_ctor_get(v_a_618_, 0);
v_isSharedCheck_633_ = !lean_is_exclusive(v_a_618_);
if (v_isSharedCheck_633_ == 0)
{
v___x_624_ = v_a_618_;
v_isShared_625_ = v_isSharedCheck_633_;
goto v_resetjp_623_;
}
else
{
lean_inc(v_val_622_);
lean_dec(v_a_618_);
v___x_624_ = lean_box(0);
v_isShared_625_ = v_isSharedCheck_633_;
goto v_resetjp_623_;
}
v_resetjp_623_:
{
lean_object* v___x_626_; lean_object* v___x_628_; 
v___x_626_ = lean_nat_to_int(v_val_622_);
if (v_isShared_625_ == 0)
{
lean_ctor_set(v___x_624_, 0, v___x_626_);
v___x_628_ = v___x_624_;
goto v_reusejp_627_;
}
else
{
lean_object* v_reuseFailAlloc_632_; 
v_reuseFailAlloc_632_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_632_, 0, v___x_626_);
v___x_628_ = v_reuseFailAlloc_632_;
goto v_reusejp_627_;
}
v_reusejp_627_:
{
lean_object* v___x_630_; 
if (v_isShared_621_ == 0)
{
lean_ctor_set(v___x_620_, 0, v___x_628_);
v___x_630_ = v___x_620_;
goto v_reusejp_629_;
}
else
{
lean_object* v_reuseFailAlloc_631_; 
v_reuseFailAlloc_631_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_631_, 0, v___x_628_);
v___x_630_ = v_reuseFailAlloc_631_;
goto v_reusejp_629_;
}
v_reusejp_629_:
{
return v___x_630_;
}
}
}
}
else
{
lean_object* v___x_634_; lean_object* v___x_636_; 
lean_dec(v_a_618_);
v___x_634_ = lean_box(0);
if (v_isShared_621_ == 0)
{
lean_ctor_set(v___x_620_, 0, v___x_634_);
v___x_636_ = v___x_620_;
goto v_reusejp_635_;
}
else
{
lean_object* v_reuseFailAlloc_637_; 
v_reuseFailAlloc_637_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_637_, 0, v___x_634_);
v___x_636_ = v_reuseFailAlloc_637_;
goto v_reusejp_635_;
}
v_reusejp_635_:
{
return v___x_636_;
}
}
}
}
else
{
lean_object* v_a_639_; lean_object* v___x_641_; uint8_t v_isShared_642_; uint8_t v_isSharedCheck_646_; 
v_a_639_ = lean_ctor_get(v___x_617_, 0);
v_isSharedCheck_646_ = !lean_is_exclusive(v___x_617_);
if (v_isSharedCheck_646_ == 0)
{
v___x_641_ = v___x_617_;
v_isShared_642_ = v_isSharedCheck_646_;
goto v_resetjp_640_;
}
else
{
lean_inc(v_a_639_);
lean_dec(v___x_617_);
v___x_641_ = lean_box(0);
v_isShared_642_ = v_isSharedCheck_646_;
goto v_resetjp_640_;
}
v_resetjp_640_:
{
lean_object* v___x_644_; 
if (v_isShared_642_ == 0)
{
v___x_644_ = v___x_641_;
goto v_reusejp_643_;
}
else
{
lean_object* v_reuseFailAlloc_645_; 
v_reuseFailAlloc_645_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_645_, 0, v_a_639_);
v___x_644_ = v_reuseFailAlloc_645_;
goto v_reusejp_643_;
}
v_reusejp_643_:
{
return v___x_644_;
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
lean_object* v_a_647_; lean_object* v___x_649_; uint8_t v_isShared_650_; uint8_t v_isSharedCheck_654_; 
v_a_647_ = lean_ctor_get(v___x_537_, 0);
v_isSharedCheck_654_ = !lean_is_exclusive(v___x_537_);
if (v_isSharedCheck_654_ == 0)
{
v___x_649_ = v___x_537_;
v_isShared_650_ = v_isSharedCheck_654_;
goto v_resetjp_648_;
}
else
{
lean_inc(v_a_647_);
lean_dec(v___x_537_);
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
v___jp_531_:
{
lean_object* v___x_532_; lean_object* v___x_533_; 
v___x_532_ = lean_box(0);
v___x_533_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_533_, 0, v___x_532_);
return v___x_533_;
}
v___jp_534_:
{
lean_object* v___x_535_; lean_object* v___x_536_; 
v___x_535_ = lean_box(0);
v___x_536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_536_, 0, v___x_535_);
return v___x_536_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f___boxed(lean_object* v_e_655_, lean_object* v_a_656_, lean_object* v_a_657_, lean_object* v_a_658_, lean_object* v_a_659_, lean_object* v_a_660_, lean_object* v_a_661_, lean_object* v_a_662_, lean_object* v_a_663_, lean_object* v_a_664_, lean_object* v_a_665_, lean_object* v_a_666_, lean_object* v_a_667_){
_start:
{
lean_object* v_res_668_; 
v_res_668_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f(v_e_655_, v_a_656_, v_a_657_, v_a_658_, v_a_659_, v_a_660_, v_a_661_, v_a_662_, v_a_663_, v_a_664_, v_a_665_, v_a_666_);
lean_dec(v_a_666_);
lean_dec_ref(v_a_665_);
lean_dec(v_a_664_);
lean_dec_ref(v_a_663_);
lean_dec(v_a_662_);
lean_dec_ref(v_a_661_);
lean_dec(v_a_660_);
lean_dec_ref(v_a_659_);
lean_dec(v_a_658_);
lean_dec(v_a_657_);
lean_dec_ref(v_a_656_);
return v_res_668_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__2_spec__3_spec__4(lean_object* v_00_u03b1_669_, lean_object* v_msg_670_, lean_object* v___y_671_, lean_object* v___y_672_, lean_object* v___y_673_, lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_, lean_object* v___y_677_, lean_object* v___y_678_, lean_object* v___y_679_, lean_object* v___y_680_, lean_object* v___y_681_){
_start:
{
lean_object* v___x_683_; 
v___x_683_ = l_Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__2_spec__3_spec__4___redArg(v_msg_670_, v___y_678_, v___y_679_, v___y_680_, v___y_681_);
return v___x_683_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__2_spec__3_spec__4___boxed(lean_object* v_00_u03b1_684_, lean_object* v_msg_685_, lean_object* v___y_686_, lean_object* v___y_687_, lean_object* v___y_688_, lean_object* v___y_689_, lean_object* v___y_690_, lean_object* v___y_691_, lean_object* v___y_692_, lean_object* v___y_693_, lean_object* v___y_694_, lean_object* v___y_695_, lean_object* v___y_696_, lean_object* v___y_697_){
_start:
{
lean_object* v_res_698_; 
v_res_698_ = l_Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__2_spec__3_spec__4(v_00_u03b1_684_, v_msg_685_, v___y_686_, v___y_687_, v___y_688_, v___y_689_, v___y_690_, v___y_691_, v___y_692_, v___y_693_, v___y_694_, v___y_695_, v___y_696_);
lean_dec(v___y_696_);
lean_dec_ref(v___y_695_);
lean_dec(v___y_694_);
lean_dec_ref(v___y_693_);
lean_dec(v___y_692_);
lean_dec_ref(v___y_691_);
lean_dec(v___y_690_);
lean_dec_ref(v___y_689_);
lean_dec(v___y_688_);
lean_dec(v___y_687_);
lean_dec_ref(v___y_686_);
return v_res_698_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___lam__0(lean_object* v_a_699_, lean_object* v_s_700_){
_start:
{
lean_object* v_toRing_701_; lean_object* v_divFn_x3f_702_; lean_object* v_semiringId_x3f_703_; lean_object* v_commSemiringInst_704_; lean_object* v_commRingInst_705_; lean_object* v_noZeroDivInst_x3f_706_; lean_object* v_fieldInst_x3f_707_; lean_object* v_powIdentityInst_x3f_708_; lean_object* v___x_710_; uint8_t v_isShared_711_; uint8_t v_isSharedCheck_716_; 
v_toRing_701_ = lean_ctor_get(v_s_700_, 0);
v_divFn_x3f_702_ = lean_ctor_get(v_s_700_, 2);
v_semiringId_x3f_703_ = lean_ctor_get(v_s_700_, 3);
v_commSemiringInst_704_ = lean_ctor_get(v_s_700_, 4);
v_commRingInst_705_ = lean_ctor_get(v_s_700_, 5);
v_noZeroDivInst_x3f_706_ = lean_ctor_get(v_s_700_, 6);
v_fieldInst_x3f_707_ = lean_ctor_get(v_s_700_, 7);
v_powIdentityInst_x3f_708_ = lean_ctor_get(v_s_700_, 8);
v_isSharedCheck_716_ = !lean_is_exclusive(v_s_700_);
if (v_isSharedCheck_716_ == 0)
{
lean_object* v_unused_717_; 
v_unused_717_ = lean_ctor_get(v_s_700_, 1);
lean_dec(v_unused_717_);
v___x_710_ = v_s_700_;
v_isShared_711_ = v_isSharedCheck_716_;
goto v_resetjp_709_;
}
else
{
lean_inc(v_powIdentityInst_x3f_708_);
lean_inc(v_fieldInst_x3f_707_);
lean_inc(v_noZeroDivInst_x3f_706_);
lean_inc(v_commRingInst_705_);
lean_inc(v_commSemiringInst_704_);
lean_inc(v_semiringId_x3f_703_);
lean_inc(v_divFn_x3f_702_);
lean_inc(v_toRing_701_);
lean_dec(v_s_700_);
v___x_710_ = lean_box(0);
v_isShared_711_ = v_isSharedCheck_716_;
goto v_resetjp_709_;
}
v_resetjp_709_:
{
lean_object* v___x_712_; lean_object* v___x_714_; 
v___x_712_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_712_, 0, v_a_699_);
if (v_isShared_711_ == 0)
{
lean_ctor_set(v___x_710_, 1, v___x_712_);
v___x_714_ = v___x_710_;
goto v_reusejp_713_;
}
else
{
lean_object* v_reuseFailAlloc_715_; 
v_reuseFailAlloc_715_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_715_, 0, v_toRing_701_);
lean_ctor_set(v_reuseFailAlloc_715_, 1, v___x_712_);
lean_ctor_set(v_reuseFailAlloc_715_, 2, v_divFn_x3f_702_);
lean_ctor_set(v_reuseFailAlloc_715_, 3, v_semiringId_x3f_703_);
lean_ctor_set(v_reuseFailAlloc_715_, 4, v_commSemiringInst_704_);
lean_ctor_set(v_reuseFailAlloc_715_, 5, v_commRingInst_705_);
lean_ctor_set(v_reuseFailAlloc_715_, 6, v_noZeroDivInst_x3f_706_);
lean_ctor_set(v_reuseFailAlloc_715_, 7, v_fieldInst_x3f_707_);
lean_ctor_set(v_reuseFailAlloc_715_, 8, v_powIdentityInst_x3f_708_);
v___x_714_ = v_reuseFailAlloc_715_;
goto v_reusejp_713_;
}
v_reusejp_713_:
{
return v___x_714_;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Sym_Arith_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___closed__8(void){
_start:
{
lean_object* v___x_733_; lean_object* v___x_734_; 
v___x_733_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___closed__7));
v___x_734_ = l_Lean_stringToMessageData(v___x_733_);
return v___x_734_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0(lean_object* v___y_735_, lean_object* v___y_736_, lean_object* v___y_737_, lean_object* v___y_738_, lean_object* v___y_739_, lean_object* v___y_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_, lean_object* v___y_744_, lean_object* v___y_745_){
_start:
{
lean_object* v___x_747_; 
v___x_747_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v___y_735_, v___y_736_, v___y_737_, v___y_738_, v___y_739_, v___y_740_, v___y_741_, v___y_742_, v___y_743_, v___y_744_, v___y_745_);
if (lean_obj_tag(v___x_747_) == 0)
{
lean_object* v_a_748_; lean_object* v___x_750_; uint8_t v_isShared_751_; uint8_t v_isSharedCheck_795_; 
v_a_748_ = lean_ctor_get(v___x_747_, 0);
v_isSharedCheck_795_ = !lean_is_exclusive(v___x_747_);
if (v_isSharedCheck_795_ == 0)
{
v___x_750_ = v___x_747_;
v_isShared_751_ = v_isSharedCheck_795_;
goto v_resetjp_749_;
}
else
{
lean_inc(v_a_748_);
lean_dec(v___x_747_);
v___x_750_ = lean_box(0);
v_isShared_751_ = v_isSharedCheck_795_;
goto v_resetjp_749_;
}
v_resetjp_749_:
{
lean_object* v_fieldInst_x3f_752_; 
v_fieldInst_x3f_752_ = lean_ctor_get(v_a_748_, 7);
if (lean_obj_tag(v_fieldInst_x3f_752_) == 1)
{
lean_object* v_invFn_x3f_753_; 
lean_inc_ref(v_fieldInst_x3f_752_);
v_invFn_x3f_753_ = lean_ctor_get(v_a_748_, 1);
if (lean_obj_tag(v_invFn_x3f_753_) == 1)
{
lean_object* v_val_754_; lean_object* v___x_756_; 
lean_inc_ref(v_invFn_x3f_753_);
lean_dec_ref_known(v_fieldInst_x3f_752_, 1);
lean_dec(v_a_748_);
v_val_754_ = lean_ctor_get(v_invFn_x3f_753_, 0);
lean_inc(v_val_754_);
lean_dec_ref_known(v_invFn_x3f_753_, 1);
if (v_isShared_751_ == 0)
{
lean_ctor_set(v___x_750_, 0, v_val_754_);
v___x_756_ = v___x_750_;
goto v_reusejp_755_;
}
else
{
lean_object* v_reuseFailAlloc_757_; 
v_reuseFailAlloc_757_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_757_, 0, v_val_754_);
v___x_756_ = v_reuseFailAlloc_757_;
goto v_reusejp_755_;
}
v_reusejp_755_:
{
return v___x_756_;
}
}
else
{
lean_object* v_toRing_758_; lean_object* v_val_759_; lean_object* v_type_760_; lean_object* v_u_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v_expectedInst_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; 
lean_del_object(v___x_750_);
v_toRing_758_ = lean_ctor_get(v_a_748_, 0);
lean_inc_ref(v_toRing_758_);
lean_dec(v_a_748_);
v_val_759_ = lean_ctor_get(v_fieldInst_x3f_752_, 0);
lean_inc(v_val_759_);
lean_dec_ref_known(v_fieldInst_x3f_752_, 1);
v_type_760_ = lean_ctor_get(v_toRing_758_, 1);
lean_inc_ref_n(v_type_760_, 2);
v_u_761_ = lean_ctor_get(v_toRing_758_, 2);
lean_inc_n(v_u_761_, 2);
lean_dec_ref(v_toRing_758_);
v___x_762_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___closed__2));
v___x_763_ = lean_box(0);
v___x_764_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_764_, 0, v_u_761_);
lean_ctor_set(v___x_764_, 1, v___x_763_);
v___x_765_ = l_Lean_mkConst(v___x_762_, v___x_764_);
v_expectedInst_766_ = l_Lean_mkAppB(v___x_765_, v_type_760_, v_val_759_);
v___x_767_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___closed__4));
v___x_768_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___closed__6));
v___x_769_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__2(v_type_760_, v_u_761_, v___x_767_, v___x_768_, v_expectedInst_766_, v___y_735_, v___y_736_, v___y_737_, v___y_738_, v___y_739_, v___y_740_, v___y_741_, v___y_742_, v___y_743_, v___y_744_, v___y_745_);
if (lean_obj_tag(v___x_769_) == 0)
{
lean_object* v_a_770_; lean_object* v___f_771_; lean_object* v___x_772_; 
v_a_770_ = lean_ctor_get(v___x_769_, 0);
lean_inc_n(v_a_770_, 2);
lean_dec_ref_known(v___x_769_, 1);
v___f_771_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___lam__0), 2, 1);
lean_closure_set(v___f_771_, 0, v_a_770_);
v___x_772_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(v___f_771_, v___y_735_, v___y_741_);
if (lean_obj_tag(v___x_772_) == 0)
{
lean_object* v___x_774_; uint8_t v_isShared_775_; uint8_t v_isSharedCheck_779_; 
v_isSharedCheck_779_ = !lean_is_exclusive(v___x_772_);
if (v_isSharedCheck_779_ == 0)
{
lean_object* v_unused_780_; 
v_unused_780_ = lean_ctor_get(v___x_772_, 0);
lean_dec(v_unused_780_);
v___x_774_ = v___x_772_;
v_isShared_775_ = v_isSharedCheck_779_;
goto v_resetjp_773_;
}
else
{
lean_dec(v___x_772_);
v___x_774_ = lean_box(0);
v_isShared_775_ = v_isSharedCheck_779_;
goto v_resetjp_773_;
}
v_resetjp_773_:
{
lean_object* v___x_777_; 
if (v_isShared_775_ == 0)
{
lean_ctor_set(v___x_774_, 0, v_a_770_);
v___x_777_ = v___x_774_;
goto v_reusejp_776_;
}
else
{
lean_object* v_reuseFailAlloc_778_; 
v_reuseFailAlloc_778_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_778_, 0, v_a_770_);
v___x_777_ = v_reuseFailAlloc_778_;
goto v_reusejp_776_;
}
v_reusejp_776_:
{
return v___x_777_;
}
}
}
else
{
lean_object* v_a_781_; lean_object* v___x_783_; uint8_t v_isShared_784_; uint8_t v_isSharedCheck_788_; 
lean_dec(v_a_770_);
v_a_781_ = lean_ctor_get(v___x_772_, 0);
v_isSharedCheck_788_ = !lean_is_exclusive(v___x_772_);
if (v_isSharedCheck_788_ == 0)
{
v___x_783_ = v___x_772_;
v_isShared_784_ = v_isSharedCheck_788_;
goto v_resetjp_782_;
}
else
{
lean_inc(v_a_781_);
lean_dec(v___x_772_);
v___x_783_ = lean_box(0);
v_isShared_784_ = v_isSharedCheck_788_;
goto v_resetjp_782_;
}
v_resetjp_782_:
{
lean_object* v___x_786_; 
if (v_isShared_784_ == 0)
{
v___x_786_ = v___x_783_;
goto v_reusejp_785_;
}
else
{
lean_object* v_reuseFailAlloc_787_; 
v_reuseFailAlloc_787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_787_, 0, v_a_781_);
v___x_786_ = v_reuseFailAlloc_787_;
goto v_reusejp_785_;
}
v_reusejp_785_:
{
return v___x_786_;
}
}
}
}
else
{
return v___x_769_;
}
}
}
else
{
lean_object* v_toRing_789_; lean_object* v_type_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; 
lean_del_object(v___x_750_);
v_toRing_789_ = lean_ctor_get(v_a_748_, 0);
lean_inc_ref(v_toRing_789_);
lean_dec(v_a_748_);
v_type_790_ = lean_ctor_get(v_toRing_789_, 1);
lean_inc_ref(v_type_790_);
lean_dec_ref(v_toRing_789_);
v___x_791_ = lean_obj_once(&l_Lean_Meta_Sym_Arith_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___closed__8, &l_Lean_Meta_Sym_Arith_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___closed__8_once, _init_l_Lean_Meta_Sym_Arith_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___closed__8);
v___x_792_ = l_Lean_indentExpr(v_type_790_);
v___x_793_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_793_, 0, v___x_791_);
lean_ctor_set(v___x_793_, 1, v___x_792_);
v___x_794_ = l_Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__2_spec__3_spec__4___redArg(v___x_793_, v___y_742_, v___y_743_, v___y_744_, v___y_745_);
return v___x_794_;
}
}
}
else
{
lean_object* v_a_796_; lean_object* v___x_798_; uint8_t v_isShared_799_; uint8_t v_isSharedCheck_803_; 
v_a_796_ = lean_ctor_get(v___x_747_, 0);
v_isSharedCheck_803_ = !lean_is_exclusive(v___x_747_);
if (v_isSharedCheck_803_ == 0)
{
v___x_798_ = v___x_747_;
v_isShared_799_ = v_isSharedCheck_803_;
goto v_resetjp_797_;
}
else
{
lean_inc(v_a_796_);
lean_dec(v___x_747_);
v___x_798_ = lean_box(0);
v_isShared_799_ = v_isSharedCheck_803_;
goto v_resetjp_797_;
}
v_resetjp_797_:
{
lean_object* v___x_801_; 
if (v_isShared_799_ == 0)
{
v___x_801_ = v___x_798_;
goto v_reusejp_800_;
}
else
{
lean_object* v_reuseFailAlloc_802_; 
v_reuseFailAlloc_802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_802_, 0, v_a_796_);
v___x_801_ = v_reuseFailAlloc_802_;
goto v_reusejp_800_;
}
v_reusejp_800_:
{
return v___x_801_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___boxed(lean_object* v___y_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_, lean_object* v___y_813_, lean_object* v___y_814_, lean_object* v___y_815_){
_start:
{
lean_object* v_res_816_; 
v_res_816_ = l_Lean_Meta_Sym_Arith_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0(v___y_804_, v___y_805_, v___y_806_, v___y_807_, v___y_808_, v___y_809_, v___y_810_, v___y_811_, v___y_812_, v___y_813_, v___y_814_);
lean_dec(v___y_814_);
lean_dec_ref(v___y_813_);
lean_dec(v___y_812_);
lean_dec_ref(v___y_811_);
lean_dec(v___y_810_);
lean_dec_ref(v___y_809_);
lean_dec(v___y_808_);
lean_dec_ref(v___y_807_);
lean_dec(v___y_806_);
lean_dec(v___y_805_);
lean_dec_ref(v___y_804_);
return v_res_816_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst(lean_object* v_inst_817_, lean_object* v_a_818_, lean_object* v_a_819_, lean_object* v_a_820_, lean_object* v_a_821_, lean_object* v_a_822_, lean_object* v_a_823_, lean_object* v_a_824_, lean_object* v_a_825_, lean_object* v_a_826_, lean_object* v_a_827_, lean_object* v_a_828_){
_start:
{
lean_object* v___x_830_; 
v___x_830_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v_a_818_, v_a_819_, v_a_820_, v_a_821_, v_a_822_, v_a_823_, v_a_824_, v_a_825_, v_a_826_, v_a_827_, v_a_828_);
if (lean_obj_tag(v___x_830_) == 0)
{
lean_object* v_a_831_; lean_object* v___x_833_; uint8_t v_isShared_834_; uint8_t v_isSharedCheck_863_; 
v_a_831_ = lean_ctor_get(v___x_830_, 0);
v_isSharedCheck_863_ = !lean_is_exclusive(v___x_830_);
if (v_isSharedCheck_863_ == 0)
{
v___x_833_ = v___x_830_;
v_isShared_834_ = v_isSharedCheck_863_;
goto v_resetjp_832_;
}
else
{
lean_inc(v_a_831_);
lean_dec(v___x_830_);
v___x_833_ = lean_box(0);
v_isShared_834_ = v_isSharedCheck_863_;
goto v_resetjp_832_;
}
v_resetjp_832_:
{
lean_object* v_fieldInst_x3f_835_; 
v_fieldInst_x3f_835_ = lean_ctor_get(v_a_831_, 7);
lean_inc(v_fieldInst_x3f_835_);
lean_dec(v_a_831_);
if (lean_obj_tag(v_fieldInst_x3f_835_) == 0)
{
uint8_t v___x_836_; lean_object* v___x_837_; lean_object* v___x_839_; 
v___x_836_ = 0;
v___x_837_ = lean_box(v___x_836_);
if (v_isShared_834_ == 0)
{
lean_ctor_set(v___x_833_, 0, v___x_837_);
v___x_839_ = v___x_833_;
goto v_reusejp_838_;
}
else
{
lean_object* v_reuseFailAlloc_840_; 
v_reuseFailAlloc_840_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_840_, 0, v___x_837_);
v___x_839_ = v_reuseFailAlloc_840_;
goto v_reusejp_838_;
}
v_reusejp_838_:
{
return v___x_839_;
}
}
else
{
lean_object* v___x_841_; 
lean_dec_ref_known(v_fieldInst_x3f_835_, 1);
lean_del_object(v___x_833_);
v___x_841_ = l_Lean_Meta_Sym_Arith_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0(v_a_818_, v_a_819_, v_a_820_, v_a_821_, v_a_822_, v_a_823_, v_a_824_, v_a_825_, v_a_826_, v_a_827_, v_a_828_);
if (lean_obj_tag(v___x_841_) == 0)
{
lean_object* v_a_842_; lean_object* v___x_844_; uint8_t v_isShared_845_; uint8_t v_isSharedCheck_854_; 
v_a_842_ = lean_ctor_get(v___x_841_, 0);
v_isSharedCheck_854_ = !lean_is_exclusive(v___x_841_);
if (v_isSharedCheck_854_ == 0)
{
v___x_844_ = v___x_841_;
v_isShared_845_ = v_isSharedCheck_854_;
goto v_resetjp_843_;
}
else
{
lean_inc(v_a_842_);
lean_dec(v___x_841_);
v___x_844_ = lean_box(0);
v_isShared_845_ = v_isSharedCheck_854_;
goto v_resetjp_843_;
}
v_resetjp_843_:
{
lean_object* v___x_846_; size_t v___x_847_; size_t v___x_848_; uint8_t v___x_849_; lean_object* v___x_850_; lean_object* v___x_852_; 
v___x_846_ = l_Lean_Expr_appArg_x21(v_a_842_);
lean_dec(v_a_842_);
v___x_847_ = lean_ptr_addr(v___x_846_);
lean_dec_ref(v___x_846_);
v___x_848_ = lean_ptr_addr(v_inst_817_);
v___x_849_ = lean_usize_dec_eq(v___x_847_, v___x_848_);
v___x_850_ = lean_box(v___x_849_);
if (v_isShared_845_ == 0)
{
lean_ctor_set(v___x_844_, 0, v___x_850_);
v___x_852_ = v___x_844_;
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
else
{
lean_object* v_a_855_; lean_object* v___x_857_; uint8_t v_isShared_858_; uint8_t v_isSharedCheck_862_; 
v_a_855_ = lean_ctor_get(v___x_841_, 0);
v_isSharedCheck_862_ = !lean_is_exclusive(v___x_841_);
if (v_isSharedCheck_862_ == 0)
{
v___x_857_ = v___x_841_;
v_isShared_858_ = v_isSharedCheck_862_;
goto v_resetjp_856_;
}
else
{
lean_inc(v_a_855_);
lean_dec(v___x_841_);
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
}
else
{
lean_object* v_a_864_; lean_object* v___x_866_; uint8_t v_isShared_867_; uint8_t v_isSharedCheck_871_; 
v_a_864_ = lean_ctor_get(v___x_830_, 0);
v_isSharedCheck_871_ = !lean_is_exclusive(v___x_830_);
if (v_isSharedCheck_871_ == 0)
{
v___x_866_ = v___x_830_;
v_isShared_867_ = v_isSharedCheck_871_;
goto v_resetjp_865_;
}
else
{
lean_inc(v_a_864_);
lean_dec(v___x_830_);
v___x_866_ = lean_box(0);
v_isShared_867_ = v_isSharedCheck_871_;
goto v_resetjp_865_;
}
v_resetjp_865_:
{
lean_object* v___x_869_; 
if (v_isShared_867_ == 0)
{
v___x_869_ = v___x_866_;
goto v_reusejp_868_;
}
else
{
lean_object* v_reuseFailAlloc_870_; 
v_reuseFailAlloc_870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_870_, 0, v_a_864_);
v___x_869_ = v_reuseFailAlloc_870_;
goto v_reusejp_868_;
}
v_reusejp_868_:
{
return v___x_869_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst___boxed(lean_object* v_inst_872_, lean_object* v_a_873_, lean_object* v_a_874_, lean_object* v_a_875_, lean_object* v_a_876_, lean_object* v_a_877_, lean_object* v_a_878_, lean_object* v_a_879_, lean_object* v_a_880_, lean_object* v_a_881_, lean_object* v_a_882_, lean_object* v_a_883_, lean_object* v_a_884_){
_start:
{
lean_object* v_res_885_; 
v_res_885_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst(v_inst_872_, v_a_873_, v_a_874_, v_a_875_, v_a_876_, v_a_877_, v_a_878_, v_a_879_, v_a_880_, v_a_881_, v_a_882_, v_a_883_);
lean_dec(v_a_883_);
lean_dec_ref(v_a_882_);
lean_dec(v_a_881_);
lean_dec_ref(v_a_880_);
lean_dec(v_a_879_);
lean_dec_ref(v_a_878_);
lean_dec(v_a_877_);
lean_dec_ref(v_a_876_);
lean_dec(v_a_875_);
lean_dec(v_a_874_);
lean_dec_ref(v_a_873_);
lean_dec_ref(v_inst_872_);
return v_res_885_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_pushInvFact___redArg(lean_object* v_expected_886_, lean_object* v_proof_887_, lean_object* v_a_888_, lean_object* v_a_889_, lean_object* v_a_890_, lean_object* v_a_891_, lean_object* v_a_892_, lean_object* v_a_893_, lean_object* v_a_894_){
_start:
{
lean_object* v___x_896_; 
v___x_896_ = l_Lean_Meta_Sym_canon(v_expected_886_, v_a_889_, v_a_890_, v_a_891_, v_a_892_, v_a_893_, v_a_894_);
if (lean_obj_tag(v___x_896_) == 0)
{
lean_object* v_a_897_; lean_object* v___x_898_; 
v_a_897_ = lean_ctor_get(v___x_896_, 0);
lean_inc(v_a_897_);
lean_dec_ref_known(v___x_896_, 1);
v___x_898_ = l_Lean_Meta_Sym_shareCommon(v_a_897_, v_a_889_, v_a_890_, v_a_891_, v_a_892_, v_a_893_, v_a_894_);
if (lean_obj_tag(v___x_898_) == 0)
{
lean_object* v_a_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; 
v_a_899_ = lean_ctor_get(v___x_898_, 0);
lean_inc_n(v_a_899_, 2);
lean_dec_ref_known(v___x_898_, 1);
v___x_900_ = l_Lean_Meta_mkExpectedPropHint(v_proof_887_, v_a_899_);
v___x_901_ = lean_unsigned_to_nat(0u);
v___x_902_ = l_Lean_Meta_Grind_pushNewFactCore___redArg(v_a_899_, v___x_900_, v___x_901_, v_a_888_);
return v___x_902_;
}
else
{
lean_object* v_a_903_; lean_object* v___x_905_; uint8_t v_isShared_906_; uint8_t v_isSharedCheck_910_; 
lean_dec_ref(v_proof_887_);
v_a_903_ = lean_ctor_get(v___x_898_, 0);
v_isSharedCheck_910_ = !lean_is_exclusive(v___x_898_);
if (v_isSharedCheck_910_ == 0)
{
v___x_905_ = v___x_898_;
v_isShared_906_ = v_isSharedCheck_910_;
goto v_resetjp_904_;
}
else
{
lean_inc(v_a_903_);
lean_dec(v___x_898_);
v___x_905_ = lean_box(0);
v_isShared_906_ = v_isSharedCheck_910_;
goto v_resetjp_904_;
}
v_resetjp_904_:
{
lean_object* v___x_908_; 
if (v_isShared_906_ == 0)
{
v___x_908_ = v___x_905_;
goto v_reusejp_907_;
}
else
{
lean_object* v_reuseFailAlloc_909_; 
v_reuseFailAlloc_909_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_909_, 0, v_a_903_);
v___x_908_ = v_reuseFailAlloc_909_;
goto v_reusejp_907_;
}
v_reusejp_907_:
{
return v___x_908_;
}
}
}
}
else
{
lean_object* v_a_911_; lean_object* v___x_913_; uint8_t v_isShared_914_; uint8_t v_isSharedCheck_918_; 
lean_dec_ref(v_proof_887_);
v_a_911_ = lean_ctor_get(v___x_896_, 0);
v_isSharedCheck_918_ = !lean_is_exclusive(v___x_896_);
if (v_isSharedCheck_918_ == 0)
{
v___x_913_ = v___x_896_;
v_isShared_914_ = v_isSharedCheck_918_;
goto v_resetjp_912_;
}
else
{
lean_inc(v_a_911_);
lean_dec(v___x_896_);
v___x_913_ = lean_box(0);
v_isShared_914_ = v_isSharedCheck_918_;
goto v_resetjp_912_;
}
v_resetjp_912_:
{
lean_object* v___x_916_; 
if (v_isShared_914_ == 0)
{
v___x_916_ = v___x_913_;
goto v_reusejp_915_;
}
else
{
lean_object* v_reuseFailAlloc_917_; 
v_reuseFailAlloc_917_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_917_, 0, v_a_911_);
v___x_916_ = v_reuseFailAlloc_917_;
goto v_reusejp_915_;
}
v_reusejp_915_:
{
return v___x_916_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_pushInvFact___redArg___boxed(lean_object* v_expected_919_, lean_object* v_proof_920_, lean_object* v_a_921_, lean_object* v_a_922_, lean_object* v_a_923_, lean_object* v_a_924_, lean_object* v_a_925_, lean_object* v_a_926_, lean_object* v_a_927_, lean_object* v_a_928_){
_start:
{
lean_object* v_res_929_; 
v_res_929_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_pushInvFact___redArg(v_expected_919_, v_proof_920_, v_a_921_, v_a_922_, v_a_923_, v_a_924_, v_a_925_, v_a_926_, v_a_927_);
lean_dec(v_a_927_);
lean_dec_ref(v_a_926_);
lean_dec(v_a_925_);
lean_dec_ref(v_a_924_);
lean_dec(v_a_923_);
lean_dec_ref(v_a_922_);
lean_dec(v_a_921_);
return v_res_929_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_pushInvFact(lean_object* v_expected_930_, lean_object* v_proof_931_, lean_object* v_a_932_, lean_object* v_a_933_, lean_object* v_a_934_, lean_object* v_a_935_, lean_object* v_a_936_, lean_object* v_a_937_, lean_object* v_a_938_, lean_object* v_a_939_, lean_object* v_a_940_, lean_object* v_a_941_, lean_object* v_a_942_){
_start:
{
lean_object* v___x_944_; 
v___x_944_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_pushInvFact___redArg(v_expected_930_, v_proof_931_, v_a_933_, v_a_937_, v_a_938_, v_a_939_, v_a_940_, v_a_941_, v_a_942_);
return v___x_944_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_pushInvFact___boxed(lean_object* v_expected_945_, lean_object* v_proof_946_, lean_object* v_a_947_, lean_object* v_a_948_, lean_object* v_a_949_, lean_object* v_a_950_, lean_object* v_a_951_, lean_object* v_a_952_, lean_object* v_a_953_, lean_object* v_a_954_, lean_object* v_a_955_, lean_object* v_a_956_, lean_object* v_a_957_, lean_object* v_a_958_){
_start:
{
lean_object* v_res_959_; 
v_res_959_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_pushInvFact(v_expected_945_, v_proof_946_, v_a_947_, v_a_948_, v_a_949_, v_a_950_, v_a_951_, v_a_952_, v_a_953_, v_a_954_, v_a_955_, v_a_956_, v_a_957_);
lean_dec(v_a_957_);
lean_dec_ref(v_a_956_);
lean_dec(v_a_955_);
lean_dec_ref(v_a_954_);
lean_dec(v_a_953_);
lean_dec_ref(v_a_952_);
lean_dec(v_a_951_);
lean_dec_ref(v_a_950_);
lean_dec(v_a_949_);
lean_dec(v_a_948_);
lean_dec_ref(v_a_947_);
return v_res_959_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0_spec__1_spec__5___redArg(lean_object* v_x_960_, lean_object* v_x_961_, lean_object* v_x_962_, lean_object* v_x_963_){
_start:
{
lean_object* v_ks_964_; lean_object* v_vs_965_; lean_object* v___x_967_; uint8_t v_isShared_968_; uint8_t v_isSharedCheck_989_; 
v_ks_964_ = lean_ctor_get(v_x_960_, 0);
v_vs_965_ = lean_ctor_get(v_x_960_, 1);
v_isSharedCheck_989_ = !lean_is_exclusive(v_x_960_);
if (v_isSharedCheck_989_ == 0)
{
v___x_967_ = v_x_960_;
v_isShared_968_ = v_isSharedCheck_989_;
goto v_resetjp_966_;
}
else
{
lean_inc(v_vs_965_);
lean_inc(v_ks_964_);
lean_dec(v_x_960_);
v___x_967_ = lean_box(0);
v_isShared_968_ = v_isSharedCheck_989_;
goto v_resetjp_966_;
}
v_resetjp_966_:
{
lean_object* v___x_969_; uint8_t v___x_970_; 
v___x_969_ = lean_array_get_size(v_ks_964_);
v___x_970_ = lean_nat_dec_lt(v_x_961_, v___x_969_);
if (v___x_970_ == 0)
{
lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_974_; 
lean_dec(v_x_961_);
v___x_971_ = lean_array_push(v_ks_964_, v_x_962_);
v___x_972_ = lean_array_push(v_vs_965_, v_x_963_);
if (v_isShared_968_ == 0)
{
lean_ctor_set(v___x_967_, 1, v___x_972_);
lean_ctor_set(v___x_967_, 0, v___x_971_);
v___x_974_ = v___x_967_;
goto v_reusejp_973_;
}
else
{
lean_object* v_reuseFailAlloc_975_; 
v_reuseFailAlloc_975_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_975_, 0, v___x_971_);
lean_ctor_set(v_reuseFailAlloc_975_, 1, v___x_972_);
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
lean_object* v_k_x27_976_; uint8_t v___x_977_; 
v_k_x27_976_ = lean_array_fget_borrowed(v_ks_964_, v_x_961_);
v___x_977_ = lean_expr_eqv(v_x_962_, v_k_x27_976_);
if (v___x_977_ == 0)
{
lean_object* v___x_979_; 
if (v_isShared_968_ == 0)
{
v___x_979_ = v___x_967_;
goto v_reusejp_978_;
}
else
{
lean_object* v_reuseFailAlloc_983_; 
v_reuseFailAlloc_983_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_983_, 0, v_ks_964_);
lean_ctor_set(v_reuseFailAlloc_983_, 1, v_vs_965_);
v___x_979_ = v_reuseFailAlloc_983_;
goto v_reusejp_978_;
}
v_reusejp_978_:
{
lean_object* v___x_980_; lean_object* v___x_981_; 
v___x_980_ = lean_unsigned_to_nat(1u);
v___x_981_ = lean_nat_add(v_x_961_, v___x_980_);
lean_dec(v_x_961_);
v_x_960_ = v___x_979_;
v_x_961_ = v___x_981_;
goto _start;
}
}
else
{
lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_987_; 
v___x_984_ = lean_array_fset(v_ks_964_, v_x_961_, v_x_962_);
v___x_985_ = lean_array_fset(v_vs_965_, v_x_961_, v_x_963_);
lean_dec(v_x_961_);
if (v_isShared_968_ == 0)
{
lean_ctor_set(v___x_967_, 1, v___x_985_);
lean_ctor_set(v___x_967_, 0, v___x_984_);
v___x_987_ = v___x_967_;
goto v_reusejp_986_;
}
else
{
lean_object* v_reuseFailAlloc_988_; 
v_reuseFailAlloc_988_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_988_, 0, v___x_984_);
lean_ctor_set(v_reuseFailAlloc_988_, 1, v___x_985_);
v___x_987_ = v_reuseFailAlloc_988_;
goto v_reusejp_986_;
}
v_reusejp_986_:
{
return v___x_987_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0_spec__1___redArg(lean_object* v_n_990_, lean_object* v_k_991_, lean_object* v_v_992_){
_start:
{
lean_object* v___x_993_; lean_object* v___x_994_; 
v___x_993_ = lean_unsigned_to_nat(0u);
v___x_994_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0_spec__1_spec__5___redArg(v_n_990_, v___x_993_, v_k_991_, v_v_992_);
return v___x_994_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_995_; 
v___x_995_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_995_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg(lean_object* v_x_996_, size_t v_x_997_, size_t v_x_998_, lean_object* v_x_999_, lean_object* v_x_1000_){
_start:
{
if (lean_obj_tag(v_x_996_) == 0)
{
lean_object* v_es_1001_; size_t v___x_1002_; size_t v___x_1003_; lean_object* v_j_1004_; lean_object* v___x_1005_; uint8_t v___x_1006_; 
v_es_1001_ = lean_ctor_get(v_x_996_, 0);
v___x_1002_ = ((size_t)31ULL);
v___x_1003_ = lean_usize_land(v_x_997_, v___x_1002_);
v_j_1004_ = lean_usize_to_nat(v___x_1003_);
v___x_1005_ = lean_array_get_size(v_es_1001_);
v___x_1006_ = lean_nat_dec_lt(v_j_1004_, v___x_1005_);
if (v___x_1006_ == 0)
{
lean_dec(v_j_1004_);
lean_dec(v_x_1000_);
lean_dec_ref(v_x_999_);
return v_x_996_;
}
else
{
lean_object* v___x_1008_; uint8_t v_isShared_1009_; uint8_t v_isSharedCheck_1045_; 
lean_inc_ref(v_es_1001_);
v_isSharedCheck_1045_ = !lean_is_exclusive(v_x_996_);
if (v_isSharedCheck_1045_ == 0)
{
lean_object* v_unused_1046_; 
v_unused_1046_ = lean_ctor_get(v_x_996_, 0);
lean_dec(v_unused_1046_);
v___x_1008_ = v_x_996_;
v_isShared_1009_ = v_isSharedCheck_1045_;
goto v_resetjp_1007_;
}
else
{
lean_dec(v_x_996_);
v___x_1008_ = lean_box(0);
v_isShared_1009_ = v_isSharedCheck_1045_;
goto v_resetjp_1007_;
}
v_resetjp_1007_:
{
lean_object* v_v_1010_; lean_object* v___x_1011_; lean_object* v_xs_x27_1012_; lean_object* v___y_1014_; 
v_v_1010_ = lean_array_fget(v_es_1001_, v_j_1004_);
v___x_1011_ = lean_box(0);
v_xs_x27_1012_ = lean_array_fset(v_es_1001_, v_j_1004_, v___x_1011_);
switch(lean_obj_tag(v_v_1010_))
{
case 0:
{
lean_object* v_key_1019_; lean_object* v_val_1020_; lean_object* v___x_1022_; uint8_t v_isShared_1023_; uint8_t v_isSharedCheck_1030_; 
v_key_1019_ = lean_ctor_get(v_v_1010_, 0);
v_val_1020_ = lean_ctor_get(v_v_1010_, 1);
v_isSharedCheck_1030_ = !lean_is_exclusive(v_v_1010_);
if (v_isSharedCheck_1030_ == 0)
{
v___x_1022_ = v_v_1010_;
v_isShared_1023_ = v_isSharedCheck_1030_;
goto v_resetjp_1021_;
}
else
{
lean_inc(v_val_1020_);
lean_inc(v_key_1019_);
lean_dec(v_v_1010_);
v___x_1022_ = lean_box(0);
v_isShared_1023_ = v_isSharedCheck_1030_;
goto v_resetjp_1021_;
}
v_resetjp_1021_:
{
uint8_t v___x_1024_; 
v___x_1024_ = lean_expr_eqv(v_x_999_, v_key_1019_);
if (v___x_1024_ == 0)
{
lean_object* v___x_1025_; lean_object* v___x_1026_; 
lean_del_object(v___x_1022_);
v___x_1025_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1019_, v_val_1020_, v_x_999_, v_x_1000_);
v___x_1026_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1026_, 0, v___x_1025_);
v___y_1014_ = v___x_1026_;
goto v___jp_1013_;
}
else
{
lean_object* v___x_1028_; 
lean_dec(v_val_1020_);
lean_dec(v_key_1019_);
if (v_isShared_1023_ == 0)
{
lean_ctor_set(v___x_1022_, 1, v_x_1000_);
lean_ctor_set(v___x_1022_, 0, v_x_999_);
v___x_1028_ = v___x_1022_;
goto v_reusejp_1027_;
}
else
{
lean_object* v_reuseFailAlloc_1029_; 
v_reuseFailAlloc_1029_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1029_, 0, v_x_999_);
lean_ctor_set(v_reuseFailAlloc_1029_, 1, v_x_1000_);
v___x_1028_ = v_reuseFailAlloc_1029_;
goto v_reusejp_1027_;
}
v_reusejp_1027_:
{
v___y_1014_ = v___x_1028_;
goto v___jp_1013_;
}
}
}
}
case 1:
{
lean_object* v_node_1031_; lean_object* v___x_1033_; uint8_t v_isShared_1034_; uint8_t v_isSharedCheck_1043_; 
v_node_1031_ = lean_ctor_get(v_v_1010_, 0);
v_isSharedCheck_1043_ = !lean_is_exclusive(v_v_1010_);
if (v_isSharedCheck_1043_ == 0)
{
v___x_1033_ = v_v_1010_;
v_isShared_1034_ = v_isSharedCheck_1043_;
goto v_resetjp_1032_;
}
else
{
lean_inc(v_node_1031_);
lean_dec(v_v_1010_);
v___x_1033_ = lean_box(0);
v_isShared_1034_ = v_isSharedCheck_1043_;
goto v_resetjp_1032_;
}
v_resetjp_1032_:
{
size_t v___x_1035_; size_t v___x_1036_; size_t v___x_1037_; size_t v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1041_; 
v___x_1035_ = ((size_t)5ULL);
v___x_1036_ = lean_usize_shift_right(v_x_997_, v___x_1035_);
v___x_1037_ = ((size_t)1ULL);
v___x_1038_ = lean_usize_add(v_x_998_, v___x_1037_);
v___x_1039_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg(v_node_1031_, v___x_1036_, v___x_1038_, v_x_999_, v_x_1000_);
if (v_isShared_1034_ == 0)
{
lean_ctor_set(v___x_1033_, 0, v___x_1039_);
v___x_1041_ = v___x_1033_;
goto v_reusejp_1040_;
}
else
{
lean_object* v_reuseFailAlloc_1042_; 
v_reuseFailAlloc_1042_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1042_, 0, v___x_1039_);
v___x_1041_ = v_reuseFailAlloc_1042_;
goto v_reusejp_1040_;
}
v_reusejp_1040_:
{
v___y_1014_ = v___x_1041_;
goto v___jp_1013_;
}
}
}
default: 
{
lean_object* v___x_1044_; 
v___x_1044_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1044_, 0, v_x_999_);
lean_ctor_set(v___x_1044_, 1, v_x_1000_);
v___y_1014_ = v___x_1044_;
goto v___jp_1013_;
}
}
v___jp_1013_:
{
lean_object* v___x_1015_; lean_object* v___x_1017_; 
v___x_1015_ = lean_array_fset(v_xs_x27_1012_, v_j_1004_, v___y_1014_);
lean_dec(v_j_1004_);
if (v_isShared_1009_ == 0)
{
lean_ctor_set(v___x_1008_, 0, v___x_1015_);
v___x_1017_ = v___x_1008_;
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
}
}
}
else
{
lean_object* v_ks_1047_; lean_object* v_vs_1048_; lean_object* v___x_1050_; uint8_t v_isShared_1051_; uint8_t v_isSharedCheck_1066_; 
v_ks_1047_ = lean_ctor_get(v_x_996_, 0);
v_vs_1048_ = lean_ctor_get(v_x_996_, 1);
v_isSharedCheck_1066_ = !lean_is_exclusive(v_x_996_);
if (v_isSharedCheck_1066_ == 0)
{
v___x_1050_ = v_x_996_;
v_isShared_1051_ = v_isSharedCheck_1066_;
goto v_resetjp_1049_;
}
else
{
lean_inc(v_vs_1048_);
lean_inc(v_ks_1047_);
lean_dec(v_x_996_);
v___x_1050_ = lean_box(0);
v_isShared_1051_ = v_isSharedCheck_1066_;
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
lean_object* v_reuseFailAlloc_1065_; 
v_reuseFailAlloc_1065_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1065_, 0, v_ks_1047_);
lean_ctor_set(v_reuseFailAlloc_1065_, 1, v_vs_1048_);
v___x_1053_ = v_reuseFailAlloc_1065_;
goto v_reusejp_1052_;
}
v_reusejp_1052_:
{
lean_object* v_newNode_1054_; size_t v___x_1055_; uint8_t v___x_1056_; 
v_newNode_1054_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0_spec__1___redArg(v___x_1053_, v_x_999_, v_x_1000_);
v___x_1055_ = ((size_t)7ULL);
v___x_1056_ = lean_usize_dec_le(v___x_1055_, v_x_998_);
if (v___x_1056_ == 0)
{
lean_object* v___x_1057_; lean_object* v___x_1058_; uint8_t v___x_1059_; 
v___x_1057_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1054_);
v___x_1058_ = lean_unsigned_to_nat(4u);
v___x_1059_ = lean_nat_dec_lt(v___x_1057_, v___x_1058_);
lean_dec(v___x_1057_);
if (v___x_1059_ == 0)
{
lean_object* v_ks_1060_; lean_object* v_vs_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; 
v_ks_1060_ = lean_ctor_get(v_newNode_1054_, 0);
lean_inc_ref(v_ks_1060_);
v_vs_1061_ = lean_ctor_get(v_newNode_1054_, 1);
lean_inc_ref(v_vs_1061_);
lean_dec_ref(v_newNode_1054_);
v___x_1062_ = lean_unsigned_to_nat(0u);
v___x_1063_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg___closed__0);
v___x_1064_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0_spec__2___redArg(v_x_998_, v_ks_1060_, v_vs_1061_, v___x_1062_, v___x_1063_);
lean_dec_ref(v_vs_1061_);
lean_dec_ref(v_ks_1060_);
return v___x_1064_;
}
else
{
return v_newNode_1054_;
}
}
else
{
return v_newNode_1054_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0_spec__2___redArg(size_t v_depth_1067_, lean_object* v_keys_1068_, lean_object* v_vals_1069_, lean_object* v_i_1070_, lean_object* v_entries_1071_){
_start:
{
lean_object* v___x_1072_; uint8_t v___x_1073_; 
v___x_1072_ = lean_array_get_size(v_keys_1068_);
v___x_1073_ = lean_nat_dec_lt(v_i_1070_, v___x_1072_);
if (v___x_1073_ == 0)
{
lean_dec(v_i_1070_);
return v_entries_1071_;
}
else
{
lean_object* v_k_1074_; lean_object* v_v_1075_; uint64_t v___x_1076_; size_t v_h_1077_; size_t v___x_1078_; lean_object* v___x_1079_; size_t v___x_1080_; size_t v___x_1081_; size_t v___x_1082_; size_t v_h_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; 
v_k_1074_ = lean_array_fget_borrowed(v_keys_1068_, v_i_1070_);
v_v_1075_ = lean_array_fget_borrowed(v_vals_1069_, v_i_1070_);
v___x_1076_ = l_Lean_Expr_hash(v_k_1074_);
v_h_1077_ = lean_uint64_to_usize(v___x_1076_);
v___x_1078_ = ((size_t)5ULL);
v___x_1079_ = lean_unsigned_to_nat(1u);
v___x_1080_ = ((size_t)1ULL);
v___x_1081_ = lean_usize_sub(v_depth_1067_, v___x_1080_);
v___x_1082_ = lean_usize_mul(v___x_1078_, v___x_1081_);
v_h_1083_ = lean_usize_shift_right(v_h_1077_, v___x_1082_);
v___x_1084_ = lean_nat_add(v_i_1070_, v___x_1079_);
lean_dec(v_i_1070_);
lean_inc(v_v_1075_);
lean_inc(v_k_1074_);
v___x_1085_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg(v_entries_1071_, v_h_1083_, v_depth_1067_, v_k_1074_, v_v_1075_);
v_i_1070_ = v___x_1084_;
v_entries_1071_ = v___x_1085_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_1087_, lean_object* v_keys_1088_, lean_object* v_vals_1089_, lean_object* v_i_1090_, lean_object* v_entries_1091_){
_start:
{
size_t v_depth_boxed_1092_; lean_object* v_res_1093_; 
v_depth_boxed_1092_ = lean_unbox_usize(v_depth_1087_);
lean_dec(v_depth_1087_);
v_res_1093_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0_spec__2___redArg(v_depth_boxed_1092_, v_keys_1088_, v_vals_1089_, v_i_1090_, v_entries_1091_);
lean_dec_ref(v_vals_1089_);
lean_dec_ref(v_keys_1088_);
return v_res_1093_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg___boxed(lean_object* v_x_1094_, lean_object* v_x_1095_, lean_object* v_x_1096_, lean_object* v_x_1097_, lean_object* v_x_1098_){
_start:
{
size_t v_x_78321__boxed_1099_; size_t v_x_78322__boxed_1100_; lean_object* v_res_1101_; 
v_x_78321__boxed_1099_ = lean_unbox_usize(v_x_1095_);
lean_dec(v_x_1095_);
v_x_78322__boxed_1100_ = lean_unbox_usize(v_x_1096_);
lean_dec(v_x_1096_);
v_res_1101_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg(v_x_1094_, v_x_78321__boxed_1099_, v_x_78322__boxed_1100_, v_x_1097_, v_x_1098_);
return v_res_1101_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0___redArg(lean_object* v_x_1102_, lean_object* v_x_1103_, lean_object* v_x_1104_){
_start:
{
uint64_t v___x_1105_; size_t v___x_1106_; size_t v___x_1107_; lean_object* v___x_1108_; 
v___x_1105_ = l_Lean_Expr_hash(v_x_1103_);
v___x_1106_ = lean_uint64_to_usize(v___x_1105_);
v___x_1107_ = ((size_t)1ULL);
v___x_1108_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg(v_x_1102_, v___x_1106_, v___x_1107_, v_x_1103_, v_x_1104_);
return v___x_1108_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___lam__0(lean_object* v_a_1109_, lean_object* v_s_1110_){
_start:
{
lean_object* v_toRingState_1111_; lean_object* v_denoteEntries_1112_; lean_object* v_nextId_1113_; lean_object* v_steps_1114_; lean_object* v_queue_1115_; lean_object* v_basis_1116_; lean_object* v_diseqs_1117_; uint8_t v_recheck_1118_; lean_object* v_invSet_1119_; lean_object* v_powIdentityVarCount_1120_; lean_object* v_numEq0_x3f_1121_; uint8_t v_numEq0Updated_1122_; lean_object* v___x_1124_; uint8_t v_isShared_1125_; uint8_t v_isSharedCheck_1131_; 
v_toRingState_1111_ = lean_ctor_get(v_s_1110_, 0);
v_denoteEntries_1112_ = lean_ctor_get(v_s_1110_, 1);
v_nextId_1113_ = lean_ctor_get(v_s_1110_, 2);
v_steps_1114_ = lean_ctor_get(v_s_1110_, 3);
v_queue_1115_ = lean_ctor_get(v_s_1110_, 4);
v_basis_1116_ = lean_ctor_get(v_s_1110_, 5);
v_diseqs_1117_ = lean_ctor_get(v_s_1110_, 6);
v_recheck_1118_ = lean_ctor_get_uint8(v_s_1110_, sizeof(void*)*10);
v_invSet_1119_ = lean_ctor_get(v_s_1110_, 7);
v_powIdentityVarCount_1120_ = lean_ctor_get(v_s_1110_, 8);
v_numEq0_x3f_1121_ = lean_ctor_get(v_s_1110_, 9);
v_numEq0Updated_1122_ = lean_ctor_get_uint8(v_s_1110_, sizeof(void*)*10 + 1);
v_isSharedCheck_1131_ = !lean_is_exclusive(v_s_1110_);
if (v_isSharedCheck_1131_ == 0)
{
v___x_1124_ = v_s_1110_;
v_isShared_1125_ = v_isSharedCheck_1131_;
goto v_resetjp_1123_;
}
else
{
lean_inc(v_numEq0_x3f_1121_);
lean_inc(v_powIdentityVarCount_1120_);
lean_inc(v_invSet_1119_);
lean_inc(v_diseqs_1117_);
lean_inc(v_basis_1116_);
lean_inc(v_queue_1115_);
lean_inc(v_steps_1114_);
lean_inc(v_nextId_1113_);
lean_inc(v_denoteEntries_1112_);
lean_inc(v_toRingState_1111_);
lean_dec(v_s_1110_);
v___x_1124_ = lean_box(0);
v_isShared_1125_ = v_isSharedCheck_1131_;
goto v_resetjp_1123_;
}
v_resetjp_1123_:
{
lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1129_; 
v___x_1126_ = lean_box(0);
v___x_1127_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0___redArg(v_invSet_1119_, v_a_1109_, v___x_1126_);
if (v_isShared_1125_ == 0)
{
lean_ctor_set(v___x_1124_, 7, v___x_1127_);
v___x_1129_ = v___x_1124_;
goto v_reusejp_1128_;
}
else
{
lean_object* v_reuseFailAlloc_1130_; 
v_reuseFailAlloc_1130_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v_reuseFailAlloc_1130_, 0, v_toRingState_1111_);
lean_ctor_set(v_reuseFailAlloc_1130_, 1, v_denoteEntries_1112_);
lean_ctor_set(v_reuseFailAlloc_1130_, 2, v_nextId_1113_);
lean_ctor_set(v_reuseFailAlloc_1130_, 3, v_steps_1114_);
lean_ctor_set(v_reuseFailAlloc_1130_, 4, v_queue_1115_);
lean_ctor_set(v_reuseFailAlloc_1130_, 5, v_basis_1116_);
lean_ctor_set(v_reuseFailAlloc_1130_, 6, v_diseqs_1117_);
lean_ctor_set(v_reuseFailAlloc_1130_, 7, v___x_1127_);
lean_ctor_set(v_reuseFailAlloc_1130_, 8, v_powIdentityVarCount_1120_);
lean_ctor_set(v_reuseFailAlloc_1130_, 9, v_numEq0_x3f_1121_);
lean_ctor_set_uint8(v_reuseFailAlloc_1130_, sizeof(void*)*10, v_recheck_1118_);
lean_ctor_set_uint8(v_reuseFailAlloc_1130_, sizeof(void*)*10 + 1, v_numEq0Updated_1122_);
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
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1_spec__2_spec__5___redArg(lean_object* v_keys_1132_, lean_object* v_i_1133_, lean_object* v_k_1134_){
_start:
{
lean_object* v___x_1135_; uint8_t v___x_1136_; 
v___x_1135_ = lean_array_get_size(v_keys_1132_);
v___x_1136_ = lean_nat_dec_lt(v_i_1133_, v___x_1135_);
if (v___x_1136_ == 0)
{
lean_dec(v_i_1133_);
return v___x_1136_;
}
else
{
lean_object* v_k_x27_1137_; uint8_t v___x_1138_; 
v_k_x27_1137_ = lean_array_fget_borrowed(v_keys_1132_, v_i_1133_);
v___x_1138_ = lean_expr_eqv(v_k_1134_, v_k_x27_1137_);
if (v___x_1138_ == 0)
{
lean_object* v___x_1139_; lean_object* v___x_1140_; 
v___x_1139_ = lean_unsigned_to_nat(1u);
v___x_1140_ = lean_nat_add(v_i_1133_, v___x_1139_);
lean_dec(v_i_1133_);
v_i_1133_ = v___x_1140_;
goto _start;
}
else
{
lean_dec(v_i_1133_);
return v___x_1136_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_keys_1142_, lean_object* v_i_1143_, lean_object* v_k_1144_){
_start:
{
uint8_t v_res_1145_; lean_object* v_r_1146_; 
v_res_1145_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1_spec__2_spec__5___redArg(v_keys_1142_, v_i_1143_, v_k_1144_);
lean_dec_ref(v_k_1144_);
lean_dec_ref(v_keys_1142_);
v_r_1146_ = lean_box(v_res_1145_);
return v_r_1146_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1_spec__2___redArg(lean_object* v_x_1147_, size_t v_x_1148_, lean_object* v_x_1149_){
_start:
{
if (lean_obj_tag(v_x_1147_) == 0)
{
lean_object* v_es_1150_; lean_object* v___x_1151_; size_t v___x_1152_; size_t v___x_1153_; lean_object* v_j_1154_; lean_object* v___x_1155_; 
v_es_1150_ = lean_ctor_get(v_x_1147_, 0);
v___x_1151_ = lean_box(2);
v___x_1152_ = ((size_t)31ULL);
v___x_1153_ = lean_usize_land(v_x_1148_, v___x_1152_);
v_j_1154_ = lean_usize_to_nat(v___x_1153_);
v___x_1155_ = lean_array_get_borrowed(v___x_1151_, v_es_1150_, v_j_1154_);
lean_dec(v_j_1154_);
switch(lean_obj_tag(v___x_1155_))
{
case 0:
{
lean_object* v_key_1156_; uint8_t v___x_1157_; 
v_key_1156_ = lean_ctor_get(v___x_1155_, 0);
v___x_1157_ = lean_expr_eqv(v_x_1149_, v_key_1156_);
return v___x_1157_;
}
case 1:
{
lean_object* v_node_1158_; size_t v___x_1159_; size_t v___x_1160_; 
v_node_1158_ = lean_ctor_get(v___x_1155_, 0);
v___x_1159_ = ((size_t)5ULL);
v___x_1160_ = lean_usize_shift_right(v_x_1148_, v___x_1159_);
v_x_1147_ = v_node_1158_;
v_x_1148_ = v___x_1160_;
goto _start;
}
default: 
{
uint8_t v___x_1162_; 
v___x_1162_ = 0;
return v___x_1162_;
}
}
}
else
{
lean_object* v_ks_1163_; lean_object* v___x_1164_; uint8_t v___x_1165_; 
v_ks_1163_ = lean_ctor_get(v_x_1147_, 0);
v___x_1164_ = lean_unsigned_to_nat(0u);
v___x_1165_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1_spec__2_spec__5___redArg(v_ks_1163_, v___x_1164_, v_x_1149_);
return v___x_1165_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1_spec__2___redArg___boxed(lean_object* v_x_1166_, lean_object* v_x_1167_, lean_object* v_x_1168_){
_start:
{
size_t v_x_78517__boxed_1169_; uint8_t v_res_1170_; lean_object* v_r_1171_; 
v_x_78517__boxed_1169_ = lean_unbox_usize(v_x_1167_);
lean_dec(v_x_1167_);
v_res_1170_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1_spec__2___redArg(v_x_1166_, v_x_78517__boxed_1169_, v_x_1168_);
lean_dec_ref(v_x_1168_);
lean_dec_ref(v_x_1166_);
v_r_1171_ = lean_box(v_res_1170_);
return v_r_1171_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1___redArg(lean_object* v_x_1172_, lean_object* v_x_1173_){
_start:
{
uint64_t v___x_1174_; size_t v___x_1175_; uint8_t v___x_1176_; 
v___x_1174_ = l_Lean_Expr_hash(v_x_1173_);
v___x_1175_ = lean_uint64_to_usize(v___x_1174_);
v___x_1176_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1_spec__2___redArg(v_x_1172_, v___x_1175_, v_x_1173_);
return v___x_1176_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1___redArg___boxed(lean_object* v_x_1177_, lean_object* v_x_1178_){
_start:
{
uint8_t v_res_1179_; lean_object* v_r_1180_; 
v_res_1179_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1___redArg(v_x_1177_, v_x_1178_);
lean_dec_ref(v_x_1178_);
lean_dec_ref(v_x_1177_);
v_r_1180_ = lean_box(v_res_1179_);
return v_r_1180_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___at___00Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__2_spec__4(lean_object* v_type_1181_, lean_object* v_u_1182_, lean_object* v_instDeclName_1183_, lean_object* v_declName_1184_, lean_object* v_expectedInst_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_){
_start:
{
lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; 
v___x_1198_ = lean_box(0);
lean_inc_n(v_u_1182_, 2);
v___x_1199_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1199_, 0, v_u_1182_);
lean_ctor_set(v___x_1199_, 1, v___x_1198_);
v___x_1200_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1200_, 0, v_u_1182_);
lean_ctor_set(v___x_1200_, 1, v___x_1199_);
v___x_1201_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1201_, 0, v_u_1182_);
lean_ctor_set(v___x_1201_, 1, v___x_1200_);
lean_inc_ref(v___x_1201_);
v___x_1202_ = l_Lean_mkConst(v_instDeclName_1183_, v___x_1201_);
lean_inc_ref_n(v_type_1181_, 3);
v___x_1203_ = l_Lean_mkApp3(v___x_1202_, v_type_1181_, v_type_1181_, v_type_1181_);
v___x_1204_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__2_spec__3(v___x_1203_, v___y_1186_, v___y_1187_, v___y_1188_, v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_, v___y_1193_, v___y_1194_, v___y_1195_, v___y_1196_);
if (lean_obj_tag(v___x_1204_) == 0)
{
lean_object* v_a_1205_; lean_object* v___x_1206_; 
v_a_1205_ = lean_ctor_get(v___x_1204_, 0);
lean_inc_n(v_a_1205_, 2);
lean_dec_ref_known(v___x_1204_, 1);
lean_inc(v_declName_1184_);
v___x_1206_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst(v_declName_1184_, v_a_1205_, v_expectedInst_1185_, v___y_1193_, v___y_1194_, v___y_1195_, v___y_1196_);
if (lean_obj_tag(v___x_1206_) == 0)
{
lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; 
lean_dec_ref_known(v___x_1206_, 1);
v___x_1207_ = l_Lean_mkConst(v_declName_1184_, v___x_1201_);
lean_inc_ref_n(v_type_1181_, 2);
v___x_1208_ = l_Lean_mkApp4(v___x_1207_, v_type_1181_, v_type_1181_, v_type_1181_, v_a_1205_);
v___x_1209_ = l_Lean_Meta_Sym_canon(v___x_1208_, v___y_1191_, v___y_1192_, v___y_1193_, v___y_1194_, v___y_1195_, v___y_1196_);
if (lean_obj_tag(v___x_1209_) == 0)
{
lean_object* v_a_1210_; lean_object* v___x_1211_; 
v_a_1210_ = lean_ctor_get(v___x_1209_, 0);
lean_inc(v_a_1210_);
lean_dec_ref_known(v___x_1209_, 1);
v___x_1211_ = l_Lean_Meta_Sym_shareCommon(v_a_1210_, v___y_1191_, v___y_1192_, v___y_1193_, v___y_1194_, v___y_1195_, v___y_1196_);
return v___x_1211_;
}
else
{
return v___x_1209_;
}
}
else
{
lean_object* v_a_1212_; lean_object* v___x_1214_; uint8_t v_isShared_1215_; uint8_t v_isSharedCheck_1219_; 
lean_dec(v_a_1205_);
lean_dec_ref_known(v___x_1201_, 2);
lean_dec(v_declName_1184_);
lean_dec_ref(v_type_1181_);
v_a_1212_ = lean_ctor_get(v___x_1206_, 0);
v_isSharedCheck_1219_ = !lean_is_exclusive(v___x_1206_);
if (v_isSharedCheck_1219_ == 0)
{
v___x_1214_ = v___x_1206_;
v_isShared_1215_ = v_isSharedCheck_1219_;
goto v_resetjp_1213_;
}
else
{
lean_inc(v_a_1212_);
lean_dec(v___x_1206_);
v___x_1214_ = lean_box(0);
v_isShared_1215_ = v_isSharedCheck_1219_;
goto v_resetjp_1213_;
}
v_resetjp_1213_:
{
lean_object* v___x_1217_; 
if (v_isShared_1215_ == 0)
{
v___x_1217_ = v___x_1214_;
goto v_reusejp_1216_;
}
else
{
lean_object* v_reuseFailAlloc_1218_; 
v_reuseFailAlloc_1218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1218_, 0, v_a_1212_);
v___x_1217_ = v_reuseFailAlloc_1218_;
goto v_reusejp_1216_;
}
v_reusejp_1216_:
{
return v___x_1217_;
}
}
}
}
else
{
lean_dec_ref_known(v___x_1201_, 2);
lean_dec_ref(v_expectedInst_1185_);
lean_dec(v_declName_1184_);
lean_dec_ref(v_type_1181_);
return v___x_1204_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___at___00Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__2_spec__4___boxed(lean_object** _args){
lean_object* v_type_1220_ = _args[0];
lean_object* v_u_1221_ = _args[1];
lean_object* v_instDeclName_1222_ = _args[2];
lean_object* v_declName_1223_ = _args[3];
lean_object* v_expectedInst_1224_ = _args[4];
lean_object* v___y_1225_ = _args[5];
lean_object* v___y_1226_ = _args[6];
lean_object* v___y_1227_ = _args[7];
lean_object* v___y_1228_ = _args[8];
lean_object* v___y_1229_ = _args[9];
lean_object* v___y_1230_ = _args[10];
lean_object* v___y_1231_ = _args[11];
lean_object* v___y_1232_ = _args[12];
lean_object* v___y_1233_ = _args[13];
lean_object* v___y_1234_ = _args[14];
lean_object* v___y_1235_ = _args[15];
lean_object* v___y_1236_ = _args[16];
_start:
{
lean_object* v_res_1237_; 
v_res_1237_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___at___00Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__2_spec__4(v_type_1220_, v_u_1221_, v_instDeclName_1222_, v_declName_1223_, v_expectedInst_1224_, v___y_1225_, v___y_1226_, v___y_1227_, v___y_1228_, v___y_1229_, v___y_1230_, v___y_1231_, v___y_1232_, v___y_1233_, v___y_1234_, v___y_1235_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__2___lam__0(lean_object* v_a_1238_, lean_object* v_s_1239_){
_start:
{
lean_object* v_toRing_1240_; lean_object* v_invFn_x3f_1241_; lean_object* v_divFn_x3f_1242_; lean_object* v_semiringId_x3f_1243_; lean_object* v_commSemiringInst_1244_; lean_object* v_commRingInst_1245_; lean_object* v_noZeroDivInst_x3f_1246_; lean_object* v_fieldInst_x3f_1247_; lean_object* v_powIdentityInst_x3f_1248_; lean_object* v___x_1250_; uint8_t v_isShared_1251_; uint8_t v_isSharedCheck_1280_; 
v_toRing_1240_ = lean_ctor_get(v_s_1239_, 0);
v_invFn_x3f_1241_ = lean_ctor_get(v_s_1239_, 1);
v_divFn_x3f_1242_ = lean_ctor_get(v_s_1239_, 2);
v_semiringId_x3f_1243_ = lean_ctor_get(v_s_1239_, 3);
v_commSemiringInst_1244_ = lean_ctor_get(v_s_1239_, 4);
v_commRingInst_1245_ = lean_ctor_get(v_s_1239_, 5);
v_noZeroDivInst_x3f_1246_ = lean_ctor_get(v_s_1239_, 6);
v_fieldInst_x3f_1247_ = lean_ctor_get(v_s_1239_, 7);
v_powIdentityInst_x3f_1248_ = lean_ctor_get(v_s_1239_, 8);
v_isSharedCheck_1280_ = !lean_is_exclusive(v_s_1239_);
if (v_isSharedCheck_1280_ == 0)
{
v___x_1250_ = v_s_1239_;
v_isShared_1251_ = v_isSharedCheck_1280_;
goto v_resetjp_1249_;
}
else
{
lean_inc(v_powIdentityInst_x3f_1248_);
lean_inc(v_fieldInst_x3f_1247_);
lean_inc(v_noZeroDivInst_x3f_1246_);
lean_inc(v_commRingInst_1245_);
lean_inc(v_commSemiringInst_1244_);
lean_inc(v_semiringId_x3f_1243_);
lean_inc(v_divFn_x3f_1242_);
lean_inc(v_invFn_x3f_1241_);
lean_inc(v_toRing_1240_);
lean_dec(v_s_1239_);
v___x_1250_ = lean_box(0);
v_isShared_1251_ = v_isSharedCheck_1280_;
goto v_resetjp_1249_;
}
v_resetjp_1249_:
{
lean_object* v_id_1252_; lean_object* v_type_1253_; lean_object* v_u_1254_; lean_object* v_ringInst_1255_; lean_object* v_semiringInst_1256_; lean_object* v_charInst_x3f_1257_; uint8_t v_symbolicChar_1258_; lean_object* v_addFn_x3f_1259_; lean_object* v_subFn_x3f_1260_; lean_object* v_negFn_x3f_1261_; lean_object* v_powFn_x3f_1262_; lean_object* v_intCastFn_x3f_1263_; lean_object* v_natCastFn_x3f_1264_; lean_object* v_natSMulFn_x3f_1265_; lean_object* v_intSMulFn_x3f_1266_; lean_object* v_one_x3f_1267_; lean_object* v___x_1269_; uint8_t v_isShared_1270_; uint8_t v_isSharedCheck_1278_; 
v_id_1252_ = lean_ctor_get(v_toRing_1240_, 0);
v_type_1253_ = lean_ctor_get(v_toRing_1240_, 1);
v_u_1254_ = lean_ctor_get(v_toRing_1240_, 2);
v_ringInst_1255_ = lean_ctor_get(v_toRing_1240_, 3);
v_semiringInst_1256_ = lean_ctor_get(v_toRing_1240_, 4);
v_charInst_x3f_1257_ = lean_ctor_get(v_toRing_1240_, 5);
v_symbolicChar_1258_ = lean_ctor_get_uint8(v_toRing_1240_, sizeof(void*)*16);
v_addFn_x3f_1259_ = lean_ctor_get(v_toRing_1240_, 6);
v_subFn_x3f_1260_ = lean_ctor_get(v_toRing_1240_, 8);
v_negFn_x3f_1261_ = lean_ctor_get(v_toRing_1240_, 9);
v_powFn_x3f_1262_ = lean_ctor_get(v_toRing_1240_, 10);
v_intCastFn_x3f_1263_ = lean_ctor_get(v_toRing_1240_, 11);
v_natCastFn_x3f_1264_ = lean_ctor_get(v_toRing_1240_, 12);
v_natSMulFn_x3f_1265_ = lean_ctor_get(v_toRing_1240_, 13);
v_intSMulFn_x3f_1266_ = lean_ctor_get(v_toRing_1240_, 14);
v_one_x3f_1267_ = lean_ctor_get(v_toRing_1240_, 15);
v_isSharedCheck_1278_ = !lean_is_exclusive(v_toRing_1240_);
if (v_isSharedCheck_1278_ == 0)
{
lean_object* v_unused_1279_; 
v_unused_1279_ = lean_ctor_get(v_toRing_1240_, 7);
lean_dec(v_unused_1279_);
v___x_1269_ = v_toRing_1240_;
v_isShared_1270_ = v_isSharedCheck_1278_;
goto v_resetjp_1268_;
}
else
{
lean_inc(v_one_x3f_1267_);
lean_inc(v_intSMulFn_x3f_1266_);
lean_inc(v_natSMulFn_x3f_1265_);
lean_inc(v_natCastFn_x3f_1264_);
lean_inc(v_intCastFn_x3f_1263_);
lean_inc(v_powFn_x3f_1262_);
lean_inc(v_negFn_x3f_1261_);
lean_inc(v_subFn_x3f_1260_);
lean_inc(v_addFn_x3f_1259_);
lean_inc(v_charInst_x3f_1257_);
lean_inc(v_semiringInst_1256_);
lean_inc(v_ringInst_1255_);
lean_inc(v_u_1254_);
lean_inc(v_type_1253_);
lean_inc(v_id_1252_);
lean_dec(v_toRing_1240_);
v___x_1269_ = lean_box(0);
v_isShared_1270_ = v_isSharedCheck_1278_;
goto v_resetjp_1268_;
}
v_resetjp_1268_:
{
lean_object* v___x_1271_; lean_object* v___x_1273_; 
v___x_1271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1271_, 0, v_a_1238_);
if (v_isShared_1270_ == 0)
{
lean_ctor_set(v___x_1269_, 7, v___x_1271_);
v___x_1273_ = v___x_1269_;
goto v_reusejp_1272_;
}
else
{
lean_object* v_reuseFailAlloc_1277_; 
v_reuseFailAlloc_1277_ = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(v_reuseFailAlloc_1277_, 0, v_id_1252_);
lean_ctor_set(v_reuseFailAlloc_1277_, 1, v_type_1253_);
lean_ctor_set(v_reuseFailAlloc_1277_, 2, v_u_1254_);
lean_ctor_set(v_reuseFailAlloc_1277_, 3, v_ringInst_1255_);
lean_ctor_set(v_reuseFailAlloc_1277_, 4, v_semiringInst_1256_);
lean_ctor_set(v_reuseFailAlloc_1277_, 5, v_charInst_x3f_1257_);
lean_ctor_set(v_reuseFailAlloc_1277_, 6, v_addFn_x3f_1259_);
lean_ctor_set(v_reuseFailAlloc_1277_, 7, v___x_1271_);
lean_ctor_set(v_reuseFailAlloc_1277_, 8, v_subFn_x3f_1260_);
lean_ctor_set(v_reuseFailAlloc_1277_, 9, v_negFn_x3f_1261_);
lean_ctor_set(v_reuseFailAlloc_1277_, 10, v_powFn_x3f_1262_);
lean_ctor_set(v_reuseFailAlloc_1277_, 11, v_intCastFn_x3f_1263_);
lean_ctor_set(v_reuseFailAlloc_1277_, 12, v_natCastFn_x3f_1264_);
lean_ctor_set(v_reuseFailAlloc_1277_, 13, v_natSMulFn_x3f_1265_);
lean_ctor_set(v_reuseFailAlloc_1277_, 14, v_intSMulFn_x3f_1266_);
lean_ctor_set(v_reuseFailAlloc_1277_, 15, v_one_x3f_1267_);
lean_ctor_set_uint8(v_reuseFailAlloc_1277_, sizeof(void*)*16, v_symbolicChar_1258_);
v___x_1273_ = v_reuseFailAlloc_1277_;
goto v_reusejp_1272_;
}
v_reusejp_1272_:
{
lean_object* v___x_1275_; 
if (v_isShared_1251_ == 0)
{
lean_ctor_set(v___x_1250_, 0, v___x_1273_);
v___x_1275_ = v___x_1250_;
goto v_reusejp_1274_;
}
else
{
lean_object* v_reuseFailAlloc_1276_; 
v_reuseFailAlloc_1276_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1276_, 0, v___x_1273_);
lean_ctor_set(v_reuseFailAlloc_1276_, 1, v_invFn_x3f_1241_);
lean_ctor_set(v_reuseFailAlloc_1276_, 2, v_divFn_x3f_1242_);
lean_ctor_set(v_reuseFailAlloc_1276_, 3, v_semiringId_x3f_1243_);
lean_ctor_set(v_reuseFailAlloc_1276_, 4, v_commSemiringInst_1244_);
lean_ctor_set(v_reuseFailAlloc_1276_, 5, v_commRingInst_1245_);
lean_ctor_set(v_reuseFailAlloc_1276_, 6, v_noZeroDivInst_x3f_1246_);
lean_ctor_set(v_reuseFailAlloc_1276_, 7, v_fieldInst_x3f_1247_);
lean_ctor_set(v_reuseFailAlloc_1276_, 8, v_powIdentityInst_x3f_1248_);
v___x_1275_ = v_reuseFailAlloc_1276_;
goto v_reusejp_1274_;
}
v_reusejp_1274_:
{
return v___x_1275_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__2(lean_object* v___y_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_){
_start:
{
lean_object* v___x_1305_; 
v___x_1305_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v___y_1293_, v___y_1294_, v___y_1295_, v___y_1296_, v___y_1297_, v___y_1298_, v___y_1299_, v___y_1300_, v___y_1301_, v___y_1302_, v___y_1303_);
if (lean_obj_tag(v___x_1305_) == 0)
{
lean_object* v_a_1306_; lean_object* v___x_1308_; uint8_t v_isShared_1309_; uint8_t v_isSharedCheck_1349_; 
v_a_1306_ = lean_ctor_get(v___x_1305_, 0);
v_isSharedCheck_1349_ = !lean_is_exclusive(v___x_1305_);
if (v_isSharedCheck_1349_ == 0)
{
v___x_1308_ = v___x_1305_;
v_isShared_1309_ = v_isSharedCheck_1349_;
goto v_resetjp_1307_;
}
else
{
lean_inc(v_a_1306_);
lean_dec(v___x_1305_);
v___x_1308_ = lean_box(0);
v_isShared_1309_ = v_isSharedCheck_1349_;
goto v_resetjp_1307_;
}
v_resetjp_1307_:
{
lean_object* v_toRing_1310_; lean_object* v_mulFn_x3f_1311_; 
v_toRing_1310_ = lean_ctor_get(v_a_1306_, 0);
lean_inc_ref(v_toRing_1310_);
lean_dec(v_a_1306_);
v_mulFn_x3f_1311_ = lean_ctor_get(v_toRing_1310_, 7);
if (lean_obj_tag(v_mulFn_x3f_1311_) == 1)
{
lean_object* v_val_1312_; lean_object* v___x_1314_; 
lean_inc_ref(v_mulFn_x3f_1311_);
lean_dec_ref(v_toRing_1310_);
v_val_1312_ = lean_ctor_get(v_mulFn_x3f_1311_, 0);
lean_inc(v_val_1312_);
lean_dec_ref_known(v_mulFn_x3f_1311_, 1);
if (v_isShared_1309_ == 0)
{
lean_ctor_set(v___x_1308_, 0, v_val_1312_);
v___x_1314_ = v___x_1308_;
goto v_reusejp_1313_;
}
else
{
lean_object* v_reuseFailAlloc_1315_; 
v_reuseFailAlloc_1315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1315_, 0, v_val_1312_);
v___x_1314_ = v_reuseFailAlloc_1315_;
goto v_reusejp_1313_;
}
v_reusejp_1313_:
{
return v___x_1314_;
}
}
else
{
lean_object* v_type_1316_; lean_object* v_u_1317_; lean_object* v_semiringInst_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v_expectedInst_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; 
lean_del_object(v___x_1308_);
v_type_1316_ = lean_ctor_get(v_toRing_1310_, 1);
lean_inc_ref_n(v_type_1316_, 3);
v_u_1317_ = lean_ctor_get(v_toRing_1310_, 2);
lean_inc_n(v_u_1317_, 2);
v_semiringInst_1318_ = lean_ctor_get(v_toRing_1310_, 4);
lean_inc_ref(v_semiringInst_1318_);
lean_dec_ref(v_toRing_1310_);
v___x_1319_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__2___closed__1));
v___x_1320_ = lean_box(0);
v___x_1321_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1321_, 0, v_u_1317_);
lean_ctor_set(v___x_1321_, 1, v___x_1320_);
lean_inc_ref(v___x_1321_);
v___x_1322_ = l_Lean_mkConst(v___x_1319_, v___x_1321_);
v___x_1323_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__2___closed__4));
v___x_1324_ = l_Lean_mkConst(v___x_1323_, v___x_1321_);
v___x_1325_ = l_Lean_mkAppB(v___x_1324_, v_type_1316_, v_semiringInst_1318_);
v_expectedInst_1326_ = l_Lean_mkAppB(v___x_1322_, v_type_1316_, v___x_1325_);
v___x_1327_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__2___closed__5));
v___x_1328_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__20));
v___x_1329_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___at___00Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__2_spec__4(v_type_1316_, v_u_1317_, v___x_1327_, v___x_1328_, v_expectedInst_1326_, v___y_1293_, v___y_1294_, v___y_1295_, v___y_1296_, v___y_1297_, v___y_1298_, v___y_1299_, v___y_1300_, v___y_1301_, v___y_1302_, v___y_1303_);
if (lean_obj_tag(v___x_1329_) == 0)
{
lean_object* v_a_1330_; lean_object* v___f_1331_; lean_object* v___x_1332_; 
v_a_1330_ = lean_ctor_get(v___x_1329_, 0);
lean_inc_n(v_a_1330_, 2);
lean_dec_ref_known(v___x_1329_, 1);
v___f_1331_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__2___lam__0), 2, 1);
lean_closure_set(v___f_1331_, 0, v_a_1330_);
v___x_1332_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(v___f_1331_, v___y_1293_, v___y_1299_);
if (lean_obj_tag(v___x_1332_) == 0)
{
lean_object* v___x_1334_; uint8_t v_isShared_1335_; uint8_t v_isSharedCheck_1339_; 
v_isSharedCheck_1339_ = !lean_is_exclusive(v___x_1332_);
if (v_isSharedCheck_1339_ == 0)
{
lean_object* v_unused_1340_; 
v_unused_1340_ = lean_ctor_get(v___x_1332_, 0);
lean_dec(v_unused_1340_);
v___x_1334_ = v___x_1332_;
v_isShared_1335_ = v_isSharedCheck_1339_;
goto v_resetjp_1333_;
}
else
{
lean_dec(v___x_1332_);
v___x_1334_ = lean_box(0);
v_isShared_1335_ = v_isSharedCheck_1339_;
goto v_resetjp_1333_;
}
v_resetjp_1333_:
{
lean_object* v___x_1337_; 
if (v_isShared_1335_ == 0)
{
lean_ctor_set(v___x_1334_, 0, v_a_1330_);
v___x_1337_ = v___x_1334_;
goto v_reusejp_1336_;
}
else
{
lean_object* v_reuseFailAlloc_1338_; 
v_reuseFailAlloc_1338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1338_, 0, v_a_1330_);
v___x_1337_ = v_reuseFailAlloc_1338_;
goto v_reusejp_1336_;
}
v_reusejp_1336_:
{
return v___x_1337_;
}
}
}
else
{
lean_object* v_a_1341_; lean_object* v___x_1343_; uint8_t v_isShared_1344_; uint8_t v_isSharedCheck_1348_; 
lean_dec(v_a_1330_);
v_a_1341_ = lean_ctor_get(v___x_1332_, 0);
v_isSharedCheck_1348_ = !lean_is_exclusive(v___x_1332_);
if (v_isSharedCheck_1348_ == 0)
{
v___x_1343_ = v___x_1332_;
v_isShared_1344_ = v_isSharedCheck_1348_;
goto v_resetjp_1342_;
}
else
{
lean_inc(v_a_1341_);
lean_dec(v___x_1332_);
v___x_1343_ = lean_box(0);
v_isShared_1344_ = v_isSharedCheck_1348_;
goto v_resetjp_1342_;
}
v_resetjp_1342_:
{
lean_object* v___x_1346_; 
if (v_isShared_1344_ == 0)
{
v___x_1346_ = v___x_1343_;
goto v_reusejp_1345_;
}
else
{
lean_object* v_reuseFailAlloc_1347_; 
v_reuseFailAlloc_1347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1347_, 0, v_a_1341_);
v___x_1346_ = v_reuseFailAlloc_1347_;
goto v_reusejp_1345_;
}
v_reusejp_1345_:
{
return v___x_1346_;
}
}
}
}
else
{
return v___x_1329_;
}
}
}
}
else
{
lean_object* v_a_1350_; lean_object* v___x_1352_; uint8_t v_isShared_1353_; uint8_t v_isSharedCheck_1357_; 
v_a_1350_ = lean_ctor_get(v___x_1305_, 0);
v_isSharedCheck_1357_ = !lean_is_exclusive(v___x_1305_);
if (v_isSharedCheck_1357_ == 0)
{
v___x_1352_ = v___x_1305_;
v_isShared_1353_ = v_isSharedCheck_1357_;
goto v_resetjp_1351_;
}
else
{
lean_inc(v_a_1350_);
lean_dec(v___x_1305_);
v___x_1352_ = lean_box(0);
v_isShared_1353_ = v_isSharedCheck_1357_;
goto v_resetjp_1351_;
}
v_resetjp_1351_:
{
lean_object* v___x_1355_; 
if (v_isShared_1353_ == 0)
{
v___x_1355_ = v___x_1352_;
goto v_reusejp_1354_;
}
else
{
lean_object* v_reuseFailAlloc_1356_; 
v_reuseFailAlloc_1356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1356_, 0, v_a_1350_);
v___x_1355_ = v_reuseFailAlloc_1356_;
goto v_reusejp_1354_;
}
v_reusejp_1354_:
{
return v___x_1355_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__2___boxed(lean_object* v___y_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_){
_start:
{
lean_object* v_res_1370_; 
v_res_1370_ = l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__2(v___y_1358_, v___y_1359_, v___y_1360_, v___y_1361_, v___y_1362_, v___y_1363_, v___y_1364_, v___y_1365_, v___y_1366_, v___y_1367_, v___y_1368_);
lean_dec(v___y_1368_);
lean_dec_ref(v___y_1367_);
lean_dec(v___y_1366_);
lean_dec_ref(v___y_1365_);
lean_dec(v___y_1364_);
lean_dec_ref(v___y_1363_);
lean_dec(v___y_1362_);
lean_dec_ref(v___y_1361_);
lean_dec(v___y_1360_);
lean_dec(v___y_1359_);
lean_dec_ref(v___y_1358_);
return v_res_1370_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__3___closed__1(void){
_start:
{
lean_object* v___x_1373_; lean_object* v___x_1374_; 
v___x_1373_ = lean_unsigned_to_nat(0u);
v___x_1374_ = lean_nat_to_int(v___x_1373_);
return v___x_1374_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__3(lean_object* v_k_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_){
_start:
{
lean_object* v___x_1393_; 
v___x_1393_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v___y_1381_, v___y_1382_, v___y_1383_, v___y_1384_, v___y_1385_, v___y_1386_, v___y_1387_, v___y_1388_, v___y_1389_, v___y_1390_, v___y_1391_);
if (lean_obj_tag(v___x_1393_) == 0)
{
lean_object* v_a_1394_; lean_object* v___x_1396_; uint8_t v_isShared_1397_; uint8_t v_isSharedCheck_1454_; 
v_a_1394_ = lean_ctor_get(v___x_1393_, 0);
v_isSharedCheck_1454_ = !lean_is_exclusive(v___x_1393_);
if (v_isSharedCheck_1454_ == 0)
{
v___x_1396_ = v___x_1393_;
v_isShared_1397_ = v_isSharedCheck_1454_;
goto v_resetjp_1395_;
}
else
{
lean_inc(v_a_1394_);
lean_dec(v___x_1393_);
v___x_1396_ = lean_box(0);
v_isShared_1397_ = v_isSharedCheck_1454_;
goto v_resetjp_1395_;
}
v_resetjp_1395_:
{
lean_object* v_toRing_1398_; lean_object* v_type_1399_; lean_object* v_u_1400_; lean_object* v_semiringInst_1401_; lean_object* v___x_1402_; lean_object* v_n_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v_ofNatInst_1408_; lean_object* v___y_1409_; lean_object* v___y_1410_; lean_object* v___y_1411_; lean_object* v___y_1412_; lean_object* v___y_1413_; lean_object* v___y_1414_; lean_object* v___y_1415_; lean_object* v___y_1416_; lean_object* v___y_1417_; lean_object* v___y_1418_; lean_object* v___y_1419_; lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; 
v_toRing_1398_ = lean_ctor_get(v_a_1394_, 0);
lean_inc_ref(v_toRing_1398_);
lean_dec(v_a_1394_);
v_type_1399_ = lean_ctor_get(v_toRing_1398_, 1);
lean_inc_ref_n(v_type_1399_, 2);
v_u_1400_ = lean_ctor_get(v_toRing_1398_, 2);
lean_inc(v_u_1400_);
v_semiringInst_1401_ = lean_ctor_get(v_toRing_1398_, 4);
lean_inc_ref(v_semiringInst_1401_);
lean_dec_ref(v_toRing_1398_);
v___x_1402_ = lean_nat_abs(v_k_1380_);
v_n_1403_ = l_Lean_mkRawNatLit(v___x_1402_);
v___x_1404_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__3___closed__0));
v___x_1405_ = lean_box(0);
v___x_1406_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1406_, 0, v_u_1400_);
lean_ctor_set(v___x_1406_, 1, v___x_1405_);
lean_inc_ref(v___x_1406_);
v___x_1438_ = l_Lean_mkConst(v___x_1404_, v___x_1406_);
lean_inc_ref(v_n_1403_);
v___x_1439_ = l_Lean_mkAppB(v___x_1438_, v_type_1399_, v_n_1403_);
v___x_1440_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_1439_, v___y_1387_, v___y_1388_, v___y_1389_, v___y_1390_, v___y_1391_);
if (lean_obj_tag(v___x_1440_) == 0)
{
lean_object* v_a_1441_; 
v_a_1441_ = lean_ctor_get(v___x_1440_, 0);
lean_inc(v_a_1441_);
lean_dec_ref_known(v___x_1440_, 1);
if (lean_obj_tag(v_a_1441_) == 1)
{
lean_object* v_val_1442_; 
lean_dec_ref(v_semiringInst_1401_);
v_val_1442_ = lean_ctor_get(v_a_1441_, 0);
lean_inc(v_val_1442_);
lean_dec_ref_known(v_a_1441_, 1);
v_ofNatInst_1408_ = v_val_1442_;
v___y_1409_ = v___y_1381_;
v___y_1410_ = v___y_1382_;
v___y_1411_ = v___y_1383_;
v___y_1412_ = v___y_1384_;
v___y_1413_ = v___y_1385_;
v___y_1414_ = v___y_1386_;
v___y_1415_ = v___y_1387_;
v___y_1416_ = v___y_1388_;
v___y_1417_ = v___y_1389_;
v___y_1418_ = v___y_1390_;
v___y_1419_ = v___y_1391_;
goto v___jp_1407_;
}
else
{
lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; 
lean_dec(v_a_1441_);
v___x_1443_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__3___closed__2));
lean_inc_ref(v___x_1406_);
v___x_1444_ = l_Lean_mkConst(v___x_1443_, v___x_1406_);
lean_inc_ref(v_n_1403_);
lean_inc_ref(v_type_1399_);
v___x_1445_ = l_Lean_mkApp3(v___x_1444_, v_type_1399_, v_semiringInst_1401_, v_n_1403_);
v_ofNatInst_1408_ = v___x_1445_;
v___y_1409_ = v___y_1381_;
v___y_1410_ = v___y_1382_;
v___y_1411_ = v___y_1383_;
v___y_1412_ = v___y_1384_;
v___y_1413_ = v___y_1385_;
v___y_1414_ = v___y_1386_;
v___y_1415_ = v___y_1387_;
v___y_1416_ = v___y_1388_;
v___y_1417_ = v___y_1389_;
v___y_1418_ = v___y_1390_;
v___y_1419_ = v___y_1391_;
goto v___jp_1407_;
}
}
else
{
lean_object* v_a_1446_; lean_object* v___x_1448_; uint8_t v_isShared_1449_; uint8_t v_isSharedCheck_1453_; 
lean_dec_ref_known(v___x_1406_, 2);
lean_dec_ref(v_n_1403_);
lean_dec_ref(v_semiringInst_1401_);
lean_dec_ref(v_type_1399_);
lean_del_object(v___x_1396_);
v_a_1446_ = lean_ctor_get(v___x_1440_, 0);
v_isSharedCheck_1453_ = !lean_is_exclusive(v___x_1440_);
if (v_isSharedCheck_1453_ == 0)
{
v___x_1448_ = v___x_1440_;
v_isShared_1449_ = v_isSharedCheck_1453_;
goto v_resetjp_1447_;
}
else
{
lean_inc(v_a_1446_);
lean_dec(v___x_1440_);
v___x_1448_ = lean_box(0);
v_isShared_1449_ = v_isSharedCheck_1453_;
goto v_resetjp_1447_;
}
v_resetjp_1447_:
{
lean_object* v___x_1451_; 
if (v_isShared_1449_ == 0)
{
v___x_1451_ = v___x_1448_;
goto v_reusejp_1450_;
}
else
{
lean_object* v_reuseFailAlloc_1452_; 
v_reuseFailAlloc_1452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1452_, 0, v_a_1446_);
v___x_1451_ = v_reuseFailAlloc_1452_;
goto v_reusejp_1450_;
}
v_reusejp_1450_:
{
return v___x_1451_;
}
}
}
v___jp_1407_:
{
lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v_e_1422_; lean_object* v___x_1423_; uint8_t v___x_1424_; 
v___x_1420_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__8));
v___x_1421_ = l_Lean_mkConst(v___x_1420_, v___x_1406_);
v_e_1422_ = l_Lean_mkApp3(v___x_1421_, v_type_1399_, v_n_1403_, v_ofNatInst_1408_);
v___x_1423_ = lean_obj_once(&l_Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__3___closed__1, &l_Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__3___closed__1_once, _init_l_Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__3___closed__1);
v___x_1424_ = lean_int_dec_lt(v_k_1380_, v___x_1423_);
if (v___x_1424_ == 0)
{
lean_object* v___x_1426_; 
if (v_isShared_1397_ == 0)
{
lean_ctor_set(v___x_1396_, 0, v_e_1422_);
v___x_1426_ = v___x_1396_;
goto v_reusejp_1425_;
}
else
{
lean_object* v_reuseFailAlloc_1427_; 
v_reuseFailAlloc_1427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1427_, 0, v_e_1422_);
v___x_1426_ = v_reuseFailAlloc_1427_;
goto v_reusejp_1425_;
}
v_reusejp_1425_:
{
return v___x_1426_;
}
}
else
{
lean_object* v___x_1428_; 
lean_del_object(v___x_1396_);
v___x_1428_ = l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0(v___y_1409_, v___y_1410_, v___y_1411_, v___y_1412_, v___y_1413_, v___y_1414_, v___y_1415_, v___y_1416_, v___y_1417_, v___y_1418_, v___y_1419_);
if (lean_obj_tag(v___x_1428_) == 0)
{
lean_object* v_a_1429_; lean_object* v___x_1431_; uint8_t v_isShared_1432_; uint8_t v_isSharedCheck_1437_; 
v_a_1429_ = lean_ctor_get(v___x_1428_, 0);
v_isSharedCheck_1437_ = !lean_is_exclusive(v___x_1428_);
if (v_isSharedCheck_1437_ == 0)
{
v___x_1431_ = v___x_1428_;
v_isShared_1432_ = v_isSharedCheck_1437_;
goto v_resetjp_1430_;
}
else
{
lean_inc(v_a_1429_);
lean_dec(v___x_1428_);
v___x_1431_ = lean_box(0);
v_isShared_1432_ = v_isSharedCheck_1437_;
goto v_resetjp_1430_;
}
v_resetjp_1430_:
{
lean_object* v___x_1433_; lean_object* v___x_1435_; 
v___x_1433_ = l_Lean_Expr_app___override(v_a_1429_, v_e_1422_);
if (v_isShared_1432_ == 0)
{
lean_ctor_set(v___x_1431_, 0, v___x_1433_);
v___x_1435_ = v___x_1431_;
goto v_reusejp_1434_;
}
else
{
lean_object* v_reuseFailAlloc_1436_; 
v_reuseFailAlloc_1436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1436_, 0, v___x_1433_);
v___x_1435_ = v_reuseFailAlloc_1436_;
goto v_reusejp_1434_;
}
v_reusejp_1434_:
{
return v___x_1435_;
}
}
}
else
{
lean_dec_ref(v_e_1422_);
return v___x_1428_;
}
}
}
}
}
else
{
lean_object* v_a_1455_; lean_object* v___x_1457_; uint8_t v_isShared_1458_; uint8_t v_isSharedCheck_1462_; 
v_a_1455_ = lean_ctor_get(v___x_1393_, 0);
v_isSharedCheck_1462_ = !lean_is_exclusive(v___x_1393_);
if (v_isSharedCheck_1462_ == 0)
{
v___x_1457_ = v___x_1393_;
v_isShared_1458_ = v_isSharedCheck_1462_;
goto v_resetjp_1456_;
}
else
{
lean_inc(v_a_1455_);
lean_dec(v___x_1393_);
v___x_1457_ = lean_box(0);
v_isShared_1458_ = v_isSharedCheck_1462_;
goto v_resetjp_1456_;
}
v_resetjp_1456_:
{
lean_object* v___x_1460_; 
if (v_isShared_1458_ == 0)
{
v___x_1460_ = v___x_1457_;
goto v_reusejp_1459_;
}
else
{
lean_object* v_reuseFailAlloc_1461_; 
v_reuseFailAlloc_1461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1461_, 0, v_a_1455_);
v___x_1460_ = v_reuseFailAlloc_1461_;
goto v_reusejp_1459_;
}
v_reusejp_1459_:
{
return v___x_1460_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__3___boxed(lean_object* v_k_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_){
_start:
{
lean_object* v_res_1476_; 
v_res_1476_ = l_Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__3(v_k_1463_, v___y_1464_, v___y_1465_, v___y_1466_, v___y_1467_, v___y_1468_, v___y_1469_, v___y_1470_, v___y_1471_, v___y_1472_, v___y_1473_, v___y_1474_);
lean_dec(v___y_1474_);
lean_dec_ref(v___y_1473_);
lean_dec(v___y_1472_);
lean_dec_ref(v___y_1471_);
lean_dec(v___y_1470_);
lean_dec_ref(v___y_1469_);
lean_dec(v___y_1468_);
lean_dec_ref(v___y_1467_);
lean_dec(v___y_1466_);
lean_dec(v___y_1465_);
lean_dec_ref(v___y_1464_);
lean_dec(v_k_1463_);
return v_res_1476_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__3(void){
_start:
{
lean_object* v___x_1484_; lean_object* v___x_1485_; 
v___x_1484_ = lean_unsigned_to_nat(1u);
v___x_1485_ = lean_nat_to_int(v___x_1484_);
return v___x_1485_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv(lean_object* v_e_1510_, lean_object* v_inst_1511_, lean_object* v_a_1512_, lean_object* v_a_1513_, lean_object* v_a_1514_, lean_object* v_a_1515_, lean_object* v_a_1516_, lean_object* v_a_1517_, lean_object* v_a_1518_, lean_object* v_a_1519_, lean_object* v_a_1520_, lean_object* v_a_1521_, lean_object* v_a_1522_, lean_object* v_a_1523_){
_start:
{
lean_object* v___f_1528_; lean_object* v___x_1529_; 
lean_inc_ref(v_a_1512_);
v___f_1528_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___lam__0), 2, 1);
lean_closure_set(v___f_1528_, 0, v_a_1512_);
v___x_1529_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst(v_inst_1511_, v_a_1513_, v_a_1514_, v_a_1515_, v_a_1516_, v_a_1517_, v_a_1518_, v_a_1519_, v_a_1520_, v_a_1521_, v_a_1522_, v_a_1523_);
if (lean_obj_tag(v___x_1529_) == 0)
{
lean_object* v_a_1530_; lean_object* v___x_1532_; uint8_t v_isShared_1533_; uint8_t v_isSharedCheck_1785_; 
v_a_1530_ = lean_ctor_get(v___x_1529_, 0);
v_isSharedCheck_1785_ = !lean_is_exclusive(v___x_1529_);
if (v_isSharedCheck_1785_ == 0)
{
v___x_1532_ = v___x_1529_;
v_isShared_1533_ = v_isSharedCheck_1785_;
goto v_resetjp_1531_;
}
else
{
lean_inc(v_a_1530_);
lean_dec(v___x_1529_);
v___x_1532_ = lean_box(0);
v_isShared_1533_ = v_isSharedCheck_1785_;
goto v_resetjp_1531_;
}
v_resetjp_1531_:
{
uint8_t v___x_1534_; 
v___x_1534_ = lean_unbox(v_a_1530_);
lean_dec(v_a_1530_);
if (v___x_1534_ == 0)
{
lean_object* v___x_1535_; lean_object* v___x_1537_; 
lean_dec_ref(v___f_1528_);
lean_dec_ref(v_a_1512_);
lean_dec_ref(v_e_1510_);
v___x_1535_ = lean_box(0);
if (v_isShared_1533_ == 0)
{
lean_ctor_set(v___x_1532_, 0, v___x_1535_);
v___x_1537_ = v___x_1532_;
goto v_reusejp_1536_;
}
else
{
lean_object* v_reuseFailAlloc_1538_; 
v_reuseFailAlloc_1538_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1538_, 0, v___x_1535_);
v___x_1537_ = v_reuseFailAlloc_1538_;
goto v_reusejp_1536_;
}
v_reusejp_1536_:
{
return v___x_1537_;
}
}
else
{
lean_object* v___x_1539_; 
lean_del_object(v___x_1532_);
v___x_1539_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v_a_1513_, v_a_1514_, v_a_1515_, v_a_1516_, v_a_1517_, v_a_1518_, v_a_1519_, v_a_1520_, v_a_1521_, v_a_1522_, v_a_1523_);
if (lean_obj_tag(v___x_1539_) == 0)
{
lean_object* v_a_1540_; lean_object* v___x_1542_; uint8_t v_isShared_1543_; uint8_t v_isSharedCheck_1776_; 
v_a_1540_ = lean_ctor_get(v___x_1539_, 0);
v_isSharedCheck_1776_ = !lean_is_exclusive(v___x_1539_);
if (v_isSharedCheck_1776_ == 0)
{
v___x_1542_ = v___x_1539_;
v_isShared_1543_ = v_isSharedCheck_1776_;
goto v_resetjp_1541_;
}
else
{
lean_inc(v_a_1540_);
lean_dec(v___x_1539_);
v___x_1542_ = lean_box(0);
v_isShared_1543_ = v_isSharedCheck_1776_;
goto v_resetjp_1541_;
}
v_resetjp_1541_:
{
lean_object* v_fieldInst_x3f_1544_; 
v_fieldInst_x3f_1544_ = lean_ctor_get(v_a_1540_, 7);
lean_inc(v_fieldInst_x3f_1544_);
if (lean_obj_tag(v_fieldInst_x3f_1544_) == 1)
{
lean_object* v_toRing_1545_; lean_object* v_val_1546_; lean_object* v___y_1548_; lean_object* v___y_1549_; lean_object* v___y_1550_; lean_object* v___y_1551_; lean_object* v___y_1552_; lean_object* v___y_1553_; lean_object* v___y_1554_; lean_object* v___y_1555_; lean_object* v___y_1556_; lean_object* v___y_1557_; lean_object* v___x_1567_; 
lean_del_object(v___x_1542_);
v_toRing_1545_ = lean_ctor_get(v_a_1540_, 0);
lean_inc_ref(v_toRing_1545_);
lean_dec(v_a_1540_);
v_val_1546_ = lean_ctor_get(v_fieldInst_x3f_1544_, 0);
lean_inc(v_val_1546_);
lean_dec_ref_known(v_fieldInst_x3f_1544_, 1);
v___x_1567_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRingState___redArg(v_a_1513_, v_a_1514_, v_a_1522_);
if (lean_obj_tag(v___x_1567_) == 0)
{
lean_object* v_a_1568_; lean_object* v___x_1570_; uint8_t v_isShared_1571_; uint8_t v_isSharedCheck_1763_; 
v_a_1568_ = lean_ctor_get(v___x_1567_, 0);
v_isSharedCheck_1763_ = !lean_is_exclusive(v___x_1567_);
if (v_isSharedCheck_1763_ == 0)
{
v___x_1570_ = v___x_1567_;
v_isShared_1571_ = v_isSharedCheck_1763_;
goto v_resetjp_1569_;
}
else
{
lean_inc(v_a_1568_);
lean_dec(v___x_1567_);
v___x_1570_ = lean_box(0);
v_isShared_1571_ = v_isSharedCheck_1763_;
goto v_resetjp_1569_;
}
v_resetjp_1569_:
{
lean_object* v_invSet_1572_; uint8_t v___x_1573_; 
v_invSet_1572_ = lean_ctor_get(v_a_1568_, 7);
lean_inc_ref(v_invSet_1572_);
lean_dec(v_a_1568_);
v___x_1573_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1___redArg(v_invSet_1572_, v_a_1512_);
lean_dec_ref(v_invSet_1572_);
if (v___x_1573_ == 0)
{
lean_object* v___x_1574_; 
lean_del_object(v___x_1570_);
v___x_1574_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRingState___redArg(v___f_1528_, v_a_1513_, v_a_1514_);
if (lean_obj_tag(v___x_1574_) == 0)
{
lean_object* v___x_1575_; 
lean_dec_ref_known(v___x_1574_, 1);
lean_inc_ref(v_a_1512_);
v___x_1575_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f(v_a_1512_, v_a_1513_, v_a_1514_, v_a_1515_, v_a_1516_, v_a_1517_, v_a_1518_, v_a_1519_, v_a_1520_, v_a_1521_, v_a_1522_, v_a_1523_);
if (lean_obj_tag(v___x_1575_) == 0)
{
lean_object* v_a_1576_; 
v_a_1576_ = lean_ctor_get(v___x_1575_, 0);
lean_inc(v_a_1576_);
lean_dec_ref_known(v___x_1575_, 1);
if (lean_obj_tag(v_a_1576_) == 1)
{
lean_object* v_val_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; uint8_t v___x_1580_; 
v_val_1577_ = lean_ctor_get(v_a_1576_, 0);
lean_inc(v_val_1577_);
lean_dec_ref_known(v_a_1576_, 1);
v___x_1578_ = lean_unsigned_to_nat(0u);
v___x_1579_ = lean_obj_once(&l_Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__3___closed__1, &l_Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__3___closed__1_once, _init_l_Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__3___closed__1);
v___x_1580_ = lean_int_dec_eq(v_val_1577_, v___x_1579_);
if (v___x_1580_ == 0)
{
lean_object* v___x_1581_; 
v___x_1581_ = l_Lean_Meta_Grind_Arith_CommRing_hasChar(v_a_1513_, v_a_1514_, v_a_1515_, v_a_1516_, v_a_1517_, v_a_1518_, v_a_1519_, v_a_1520_, v_a_1521_, v_a_1522_, v_a_1523_);
if (lean_obj_tag(v___x_1581_) == 0)
{
lean_object* v_a_1582_; uint8_t v___x_1583_; 
v_a_1582_ = lean_ctor_get(v___x_1581_, 0);
lean_inc(v_a_1582_);
lean_dec_ref_known(v___x_1581_, 1);
v___x_1583_ = lean_unbox(v_a_1582_);
lean_dec(v_a_1582_);
if (v___x_1583_ == 0)
{
lean_dec(v_val_1577_);
lean_dec_ref(v_e_1510_);
v___y_1548_ = v_a_1514_;
v___y_1549_ = v_a_1515_;
v___y_1550_ = v_a_1516_;
v___y_1551_ = v_a_1517_;
v___y_1552_ = v_a_1518_;
v___y_1553_ = v_a_1519_;
v___y_1554_ = v_a_1520_;
v___y_1555_ = v_a_1521_;
v___y_1556_ = v_a_1522_;
v___y_1557_ = v_a_1523_;
goto v___jp_1547_;
}
else
{
lean_object* v___x_1584_; 
v___x_1584_ = l_Lean_Meta_Grind_Arith_CommRing_getCharInst(v_a_1513_, v_a_1514_, v_a_1515_, v_a_1516_, v_a_1517_, v_a_1518_, v_a_1519_, v_a_1520_, v_a_1521_, v_a_1522_, v_a_1523_);
if (lean_obj_tag(v___x_1584_) == 0)
{
lean_object* v_a_1585_; lean_object* v_fst_1586_; lean_object* v_snd_1587_; lean_object* v___x_1589_; uint8_t v_isShared_1590_; uint8_t v_isSharedCheck_1717_; 
v_a_1585_ = lean_ctor_get(v___x_1584_, 0);
lean_inc(v_a_1585_);
lean_dec_ref_known(v___x_1584_, 1);
v_fst_1586_ = lean_ctor_get(v_a_1585_, 0);
v_snd_1587_ = lean_ctor_get(v_a_1585_, 1);
v_isSharedCheck_1717_ = !lean_is_exclusive(v_a_1585_);
if (v_isSharedCheck_1717_ == 0)
{
v___x_1589_ = v_a_1585_;
v_isShared_1590_ = v_isSharedCheck_1717_;
goto v_resetjp_1588_;
}
else
{
lean_inc(v_snd_1587_);
lean_inc(v_fst_1586_);
lean_dec(v_a_1585_);
v___x_1589_ = lean_box(0);
v_isShared_1590_ = v_isSharedCheck_1717_;
goto v_resetjp_1588_;
}
v_resetjp_1588_:
{
uint8_t v___x_1591_; 
v___x_1591_ = lean_nat_dec_eq(v_snd_1587_, v___x_1578_);
if (v___x_1591_ == 0)
{
lean_object* v___x_1592_; lean_object* v___x_1593_; uint8_t v___x_1594_; 
lean_inc(v_snd_1587_);
v___x_1592_ = lean_nat_to_int(v_snd_1587_);
v___x_1593_ = lean_int_emod(v_val_1577_, v___x_1592_);
lean_dec(v___x_1592_);
v___x_1594_ = lean_int_dec_eq(v___x_1593_, v___x_1579_);
lean_dec(v___x_1593_);
if (v___x_1594_ == 0)
{
lean_object* v___x_1595_; 
v___x_1595_ = l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__2(v_a_1513_, v_a_1514_, v_a_1515_, v_a_1516_, v_a_1517_, v_a_1518_, v_a_1519_, v_a_1520_, v_a_1521_, v_a_1522_, v_a_1523_);
if (lean_obj_tag(v___x_1595_) == 0)
{
lean_object* v_a_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; 
v_a_1596_ = lean_ctor_get(v___x_1595_, 0);
lean_inc(v_a_1596_);
lean_dec_ref_known(v___x_1595_, 1);
v___x_1597_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__3, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__3);
v___x_1598_ = l_Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__3(v___x_1597_, v_a_1513_, v_a_1514_, v_a_1515_, v_a_1516_, v_a_1517_, v_a_1518_, v_a_1519_, v_a_1520_, v_a_1521_, v_a_1522_, v_a_1523_);
if (lean_obj_tag(v___x_1598_) == 0)
{
lean_object* v_a_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; 
v_a_1599_ = lean_ctor_get(v___x_1598_, 0);
lean_inc(v_a_1599_);
lean_dec_ref_known(v___x_1598_, 1);
v___x_1600_ = l_Lean_mkAppB(v_a_1596_, v_a_1512_, v_e_1510_);
v___x_1601_ = l_Lean_Meta_mkEq(v___x_1600_, v_a_1599_, v_a_1520_, v_a_1521_, v_a_1522_, v_a_1523_);
if (lean_obj_tag(v___x_1601_) == 0)
{
lean_object* v_a_1602_; lean_object* v_type_1603_; lean_object* v_u_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1608_; 
v_a_1602_ = lean_ctor_get(v___x_1601_, 0);
lean_inc(v_a_1602_);
lean_dec_ref_known(v___x_1601_, 1);
v_type_1603_ = lean_ctor_get(v_toRing_1545_, 1);
lean_inc_ref(v_type_1603_);
v_u_1604_ = lean_ctor_get(v_toRing_1545_, 2);
lean_inc(v_u_1604_);
lean_dec_ref(v_toRing_1545_);
v___x_1605_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__5));
v___x_1606_ = lean_box(0);
if (v_isShared_1590_ == 0)
{
lean_ctor_set_tag(v___x_1589_, 1);
lean_ctor_set(v___x_1589_, 1, v___x_1606_);
lean_ctor_set(v___x_1589_, 0, v_u_1604_);
v___x_1608_ = v___x_1589_;
goto v_reusejp_1607_;
}
else
{
lean_object* v_reuseFailAlloc_1615_; 
v_reuseFailAlloc_1615_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1615_, 0, v_u_1604_);
lean_ctor_set(v_reuseFailAlloc_1615_, 1, v___x_1606_);
v___x_1608_ = v_reuseFailAlloc_1615_;
goto v_reusejp_1607_;
}
v_reusejp_1607_:
{
lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; 
v___x_1609_ = l_Lean_mkConst(v___x_1605_, v___x_1608_);
v___x_1610_ = l_Lean_mkNatLit(v_snd_1587_);
v___x_1611_ = l_Lean_mkIntLit(v_val_1577_);
lean_dec(v_val_1577_);
v___x_1612_ = l_Lean_eagerReflBoolTrue;
v___x_1613_ = l_Lean_mkApp6(v___x_1609_, v_type_1603_, v___x_1610_, v_val_1546_, v_fst_1586_, v___x_1611_, v___x_1612_);
v___x_1614_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_pushInvFact___redArg(v_a_1602_, v___x_1613_, v_a_1514_, v_a_1518_, v_a_1519_, v_a_1520_, v_a_1521_, v_a_1522_, v_a_1523_);
if (lean_obj_tag(v___x_1614_) == 0)
{
lean_dec_ref_known(v___x_1614_, 1);
goto v___jp_1525_;
}
else
{
return v___x_1614_;
}
}
}
else
{
lean_object* v_a_1616_; lean_object* v___x_1618_; uint8_t v_isShared_1619_; uint8_t v_isSharedCheck_1623_; 
lean_del_object(v___x_1589_);
lean_dec(v_snd_1587_);
lean_dec(v_fst_1586_);
lean_dec(v_val_1577_);
lean_dec(v_val_1546_);
lean_dec_ref(v_toRing_1545_);
v_a_1616_ = lean_ctor_get(v___x_1601_, 0);
v_isSharedCheck_1623_ = !lean_is_exclusive(v___x_1601_);
if (v_isSharedCheck_1623_ == 0)
{
v___x_1618_ = v___x_1601_;
v_isShared_1619_ = v_isSharedCheck_1623_;
goto v_resetjp_1617_;
}
else
{
lean_inc(v_a_1616_);
lean_dec(v___x_1601_);
v___x_1618_ = lean_box(0);
v_isShared_1619_ = v_isSharedCheck_1623_;
goto v_resetjp_1617_;
}
v_resetjp_1617_:
{
lean_object* v___x_1621_; 
if (v_isShared_1619_ == 0)
{
v___x_1621_ = v___x_1618_;
goto v_reusejp_1620_;
}
else
{
lean_object* v_reuseFailAlloc_1622_; 
v_reuseFailAlloc_1622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1622_, 0, v_a_1616_);
v___x_1621_ = v_reuseFailAlloc_1622_;
goto v_reusejp_1620_;
}
v_reusejp_1620_:
{
return v___x_1621_;
}
}
}
}
else
{
lean_object* v_a_1624_; lean_object* v___x_1626_; uint8_t v_isShared_1627_; uint8_t v_isSharedCheck_1631_; 
lean_dec(v_a_1596_);
lean_del_object(v___x_1589_);
lean_dec(v_snd_1587_);
lean_dec(v_fst_1586_);
lean_dec(v_val_1577_);
lean_dec(v_val_1546_);
lean_dec_ref(v_toRing_1545_);
lean_dec_ref(v_a_1512_);
lean_dec_ref(v_e_1510_);
v_a_1624_ = lean_ctor_get(v___x_1598_, 0);
v_isSharedCheck_1631_ = !lean_is_exclusive(v___x_1598_);
if (v_isSharedCheck_1631_ == 0)
{
v___x_1626_ = v___x_1598_;
v_isShared_1627_ = v_isSharedCheck_1631_;
goto v_resetjp_1625_;
}
else
{
lean_inc(v_a_1624_);
lean_dec(v___x_1598_);
v___x_1626_ = lean_box(0);
v_isShared_1627_ = v_isSharedCheck_1631_;
goto v_resetjp_1625_;
}
v_resetjp_1625_:
{
lean_object* v___x_1629_; 
if (v_isShared_1627_ == 0)
{
v___x_1629_ = v___x_1626_;
goto v_reusejp_1628_;
}
else
{
lean_object* v_reuseFailAlloc_1630_; 
v_reuseFailAlloc_1630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1630_, 0, v_a_1624_);
v___x_1629_ = v_reuseFailAlloc_1630_;
goto v_reusejp_1628_;
}
v_reusejp_1628_:
{
return v___x_1629_;
}
}
}
}
else
{
lean_object* v_a_1632_; lean_object* v___x_1634_; uint8_t v_isShared_1635_; uint8_t v_isSharedCheck_1639_; 
lean_del_object(v___x_1589_);
lean_dec(v_snd_1587_);
lean_dec(v_fst_1586_);
lean_dec(v_val_1577_);
lean_dec(v_val_1546_);
lean_dec_ref(v_toRing_1545_);
lean_dec_ref(v_a_1512_);
lean_dec_ref(v_e_1510_);
v_a_1632_ = lean_ctor_get(v___x_1595_, 0);
v_isSharedCheck_1639_ = !lean_is_exclusive(v___x_1595_);
if (v_isSharedCheck_1639_ == 0)
{
v___x_1634_ = v___x_1595_;
v_isShared_1635_ = v_isSharedCheck_1639_;
goto v_resetjp_1633_;
}
else
{
lean_inc(v_a_1632_);
lean_dec(v___x_1595_);
v___x_1634_ = lean_box(0);
v_isShared_1635_ = v_isSharedCheck_1639_;
goto v_resetjp_1633_;
}
v_resetjp_1633_:
{
lean_object* v___x_1637_; 
if (v_isShared_1635_ == 0)
{
v___x_1637_ = v___x_1634_;
goto v_reusejp_1636_;
}
else
{
lean_object* v_reuseFailAlloc_1638_; 
v_reuseFailAlloc_1638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1638_, 0, v_a_1632_);
v___x_1637_ = v_reuseFailAlloc_1638_;
goto v_reusejp_1636_;
}
v_reusejp_1636_:
{
return v___x_1637_;
}
}
}
}
else
{
lean_object* v___x_1640_; 
lean_dec_ref(v_a_1512_);
v___x_1640_ = l_Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__3(v___x_1579_, v_a_1513_, v_a_1514_, v_a_1515_, v_a_1516_, v_a_1517_, v_a_1518_, v_a_1519_, v_a_1520_, v_a_1521_, v_a_1522_, v_a_1523_);
if (lean_obj_tag(v___x_1640_) == 0)
{
lean_object* v_a_1641_; lean_object* v___x_1642_; 
v_a_1641_ = lean_ctor_get(v___x_1640_, 0);
lean_inc(v_a_1641_);
lean_dec_ref_known(v___x_1640_, 1);
v___x_1642_ = l_Lean_Meta_mkEq(v_e_1510_, v_a_1641_, v_a_1520_, v_a_1521_, v_a_1522_, v_a_1523_);
if (lean_obj_tag(v___x_1642_) == 0)
{
lean_object* v_a_1643_; lean_object* v_type_1644_; lean_object* v_u_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1649_; 
v_a_1643_ = lean_ctor_get(v___x_1642_, 0);
lean_inc(v_a_1643_);
lean_dec_ref_known(v___x_1642_, 1);
v_type_1644_ = lean_ctor_get(v_toRing_1545_, 1);
lean_inc_ref(v_type_1644_);
v_u_1645_ = lean_ctor_get(v_toRing_1545_, 2);
lean_inc(v_u_1645_);
lean_dec_ref(v_toRing_1545_);
v___x_1646_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__7));
v___x_1647_ = lean_box(0);
if (v_isShared_1590_ == 0)
{
lean_ctor_set_tag(v___x_1589_, 1);
lean_ctor_set(v___x_1589_, 1, v___x_1647_);
lean_ctor_set(v___x_1589_, 0, v_u_1645_);
v___x_1649_ = v___x_1589_;
goto v_reusejp_1648_;
}
else
{
lean_object* v_reuseFailAlloc_1656_; 
v_reuseFailAlloc_1656_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1656_, 0, v_u_1645_);
lean_ctor_set(v_reuseFailAlloc_1656_, 1, v___x_1647_);
v___x_1649_ = v_reuseFailAlloc_1656_;
goto v_reusejp_1648_;
}
v_reusejp_1648_:
{
lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; 
v___x_1650_ = l_Lean_mkConst(v___x_1646_, v___x_1649_);
v___x_1651_ = l_Lean_mkNatLit(v_snd_1587_);
v___x_1652_ = l_Lean_mkIntLit(v_val_1577_);
lean_dec(v_val_1577_);
v___x_1653_ = l_Lean_eagerReflBoolTrue;
v___x_1654_ = l_Lean_mkApp6(v___x_1650_, v_type_1644_, v___x_1651_, v_val_1546_, v_fst_1586_, v___x_1652_, v___x_1653_);
v___x_1655_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_pushInvFact___redArg(v_a_1643_, v___x_1654_, v_a_1514_, v_a_1518_, v_a_1519_, v_a_1520_, v_a_1521_, v_a_1522_, v_a_1523_);
if (lean_obj_tag(v___x_1655_) == 0)
{
lean_dec_ref_known(v___x_1655_, 1);
goto v___jp_1525_;
}
else
{
return v___x_1655_;
}
}
}
else
{
lean_object* v_a_1657_; lean_object* v___x_1659_; uint8_t v_isShared_1660_; uint8_t v_isSharedCheck_1664_; 
lean_del_object(v___x_1589_);
lean_dec(v_snd_1587_);
lean_dec(v_fst_1586_);
lean_dec(v_val_1577_);
lean_dec(v_val_1546_);
lean_dec_ref(v_toRing_1545_);
v_a_1657_ = lean_ctor_get(v___x_1642_, 0);
v_isSharedCheck_1664_ = !lean_is_exclusive(v___x_1642_);
if (v_isSharedCheck_1664_ == 0)
{
v___x_1659_ = v___x_1642_;
v_isShared_1660_ = v_isSharedCheck_1664_;
goto v_resetjp_1658_;
}
else
{
lean_inc(v_a_1657_);
lean_dec(v___x_1642_);
v___x_1659_ = lean_box(0);
v_isShared_1660_ = v_isSharedCheck_1664_;
goto v_resetjp_1658_;
}
v_resetjp_1658_:
{
lean_object* v___x_1662_; 
if (v_isShared_1660_ == 0)
{
v___x_1662_ = v___x_1659_;
goto v_reusejp_1661_;
}
else
{
lean_object* v_reuseFailAlloc_1663_; 
v_reuseFailAlloc_1663_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1663_, 0, v_a_1657_);
v___x_1662_ = v_reuseFailAlloc_1663_;
goto v_reusejp_1661_;
}
v_reusejp_1661_:
{
return v___x_1662_;
}
}
}
}
else
{
lean_object* v_a_1665_; lean_object* v___x_1667_; uint8_t v_isShared_1668_; uint8_t v_isSharedCheck_1672_; 
lean_del_object(v___x_1589_);
lean_dec(v_snd_1587_);
lean_dec(v_fst_1586_);
lean_dec(v_val_1577_);
lean_dec(v_val_1546_);
lean_dec_ref(v_toRing_1545_);
lean_dec_ref(v_e_1510_);
v_a_1665_ = lean_ctor_get(v___x_1640_, 0);
v_isSharedCheck_1672_ = !lean_is_exclusive(v___x_1640_);
if (v_isSharedCheck_1672_ == 0)
{
v___x_1667_ = v___x_1640_;
v_isShared_1668_ = v_isSharedCheck_1672_;
goto v_resetjp_1666_;
}
else
{
lean_inc(v_a_1665_);
lean_dec(v___x_1640_);
v___x_1667_ = lean_box(0);
v_isShared_1668_ = v_isSharedCheck_1672_;
goto v_resetjp_1666_;
}
v_resetjp_1666_:
{
lean_object* v___x_1670_; 
if (v_isShared_1668_ == 0)
{
v___x_1670_ = v___x_1667_;
goto v_reusejp_1669_;
}
else
{
lean_object* v_reuseFailAlloc_1671_; 
v_reuseFailAlloc_1671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1671_, 0, v_a_1665_);
v___x_1670_ = v_reuseFailAlloc_1671_;
goto v_reusejp_1669_;
}
v_reusejp_1669_:
{
return v___x_1670_;
}
}
}
}
}
else
{
lean_object* v___x_1673_; 
lean_dec(v_snd_1587_);
v___x_1673_ = l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__2(v_a_1513_, v_a_1514_, v_a_1515_, v_a_1516_, v_a_1517_, v_a_1518_, v_a_1519_, v_a_1520_, v_a_1521_, v_a_1522_, v_a_1523_);
if (lean_obj_tag(v___x_1673_) == 0)
{
lean_object* v_a_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; 
v_a_1674_ = lean_ctor_get(v___x_1673_, 0);
lean_inc(v_a_1674_);
lean_dec_ref_known(v___x_1673_, 1);
v___x_1675_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__3, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__3);
v___x_1676_ = l_Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__3(v___x_1675_, v_a_1513_, v_a_1514_, v_a_1515_, v_a_1516_, v_a_1517_, v_a_1518_, v_a_1519_, v_a_1520_, v_a_1521_, v_a_1522_, v_a_1523_);
if (lean_obj_tag(v___x_1676_) == 0)
{
lean_object* v_a_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; 
v_a_1677_ = lean_ctor_get(v___x_1676_, 0);
lean_inc(v_a_1677_);
lean_dec_ref_known(v___x_1676_, 1);
v___x_1678_ = l_Lean_mkAppB(v_a_1674_, v_a_1512_, v_e_1510_);
v___x_1679_ = l_Lean_Meta_mkEq(v___x_1678_, v_a_1677_, v_a_1520_, v_a_1521_, v_a_1522_, v_a_1523_);
if (lean_obj_tag(v___x_1679_) == 0)
{
lean_object* v_a_1680_; lean_object* v_type_1681_; lean_object* v_u_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1686_; 
v_a_1680_ = lean_ctor_get(v___x_1679_, 0);
lean_inc(v_a_1680_);
lean_dec_ref_known(v___x_1679_, 1);
v_type_1681_ = lean_ctor_get(v_toRing_1545_, 1);
lean_inc_ref(v_type_1681_);
v_u_1682_ = lean_ctor_get(v_toRing_1545_, 2);
lean_inc(v_u_1682_);
lean_dec_ref(v_toRing_1545_);
v___x_1683_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__9));
v___x_1684_ = lean_box(0);
if (v_isShared_1590_ == 0)
{
lean_ctor_set_tag(v___x_1589_, 1);
lean_ctor_set(v___x_1589_, 1, v___x_1684_);
lean_ctor_set(v___x_1589_, 0, v_u_1682_);
v___x_1686_ = v___x_1589_;
goto v_reusejp_1685_;
}
else
{
lean_object* v_reuseFailAlloc_1692_; 
v_reuseFailAlloc_1692_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1692_, 0, v_u_1682_);
lean_ctor_set(v_reuseFailAlloc_1692_, 1, v___x_1684_);
v___x_1686_ = v_reuseFailAlloc_1692_;
goto v_reusejp_1685_;
}
v_reusejp_1685_:
{
lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; 
v___x_1687_ = l_Lean_mkConst(v___x_1683_, v___x_1686_);
v___x_1688_ = l_Lean_mkIntLit(v_val_1577_);
lean_dec(v_val_1577_);
v___x_1689_ = l_Lean_eagerReflBoolTrue;
v___x_1690_ = l_Lean_mkApp5(v___x_1687_, v_type_1681_, v_val_1546_, v_fst_1586_, v___x_1688_, v___x_1689_);
v___x_1691_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_pushInvFact___redArg(v_a_1680_, v___x_1690_, v_a_1514_, v_a_1518_, v_a_1519_, v_a_1520_, v_a_1521_, v_a_1522_, v_a_1523_);
if (lean_obj_tag(v___x_1691_) == 0)
{
lean_dec_ref_known(v___x_1691_, 1);
goto v___jp_1525_;
}
else
{
return v___x_1691_;
}
}
}
else
{
lean_object* v_a_1693_; lean_object* v___x_1695_; uint8_t v_isShared_1696_; uint8_t v_isSharedCheck_1700_; 
lean_del_object(v___x_1589_);
lean_dec(v_fst_1586_);
lean_dec(v_val_1577_);
lean_dec(v_val_1546_);
lean_dec_ref(v_toRing_1545_);
v_a_1693_ = lean_ctor_get(v___x_1679_, 0);
v_isSharedCheck_1700_ = !lean_is_exclusive(v___x_1679_);
if (v_isSharedCheck_1700_ == 0)
{
v___x_1695_ = v___x_1679_;
v_isShared_1696_ = v_isSharedCheck_1700_;
goto v_resetjp_1694_;
}
else
{
lean_inc(v_a_1693_);
lean_dec(v___x_1679_);
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
lean_dec(v_a_1674_);
lean_del_object(v___x_1589_);
lean_dec(v_fst_1586_);
lean_dec(v_val_1577_);
lean_dec(v_val_1546_);
lean_dec_ref(v_toRing_1545_);
lean_dec_ref(v_a_1512_);
lean_dec_ref(v_e_1510_);
v_a_1701_ = lean_ctor_get(v___x_1676_, 0);
v_isSharedCheck_1708_ = !lean_is_exclusive(v___x_1676_);
if (v_isSharedCheck_1708_ == 0)
{
v___x_1703_ = v___x_1676_;
v_isShared_1704_ = v_isSharedCheck_1708_;
goto v_resetjp_1702_;
}
else
{
lean_inc(v_a_1701_);
lean_dec(v___x_1676_);
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
else
{
lean_object* v_a_1709_; lean_object* v___x_1711_; uint8_t v_isShared_1712_; uint8_t v_isSharedCheck_1716_; 
lean_del_object(v___x_1589_);
lean_dec(v_fst_1586_);
lean_dec(v_val_1577_);
lean_dec(v_val_1546_);
lean_dec_ref(v_toRing_1545_);
lean_dec_ref(v_a_1512_);
lean_dec_ref(v_e_1510_);
v_a_1709_ = lean_ctor_get(v___x_1673_, 0);
v_isSharedCheck_1716_ = !lean_is_exclusive(v___x_1673_);
if (v_isSharedCheck_1716_ == 0)
{
v___x_1711_ = v___x_1673_;
v_isShared_1712_ = v_isSharedCheck_1716_;
goto v_resetjp_1710_;
}
else
{
lean_inc(v_a_1709_);
lean_dec(v___x_1673_);
v___x_1711_ = lean_box(0);
v_isShared_1712_ = v_isSharedCheck_1716_;
goto v_resetjp_1710_;
}
v_resetjp_1710_:
{
lean_object* v___x_1714_; 
if (v_isShared_1712_ == 0)
{
v___x_1714_ = v___x_1711_;
goto v_reusejp_1713_;
}
else
{
lean_object* v_reuseFailAlloc_1715_; 
v_reuseFailAlloc_1715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1715_, 0, v_a_1709_);
v___x_1714_ = v_reuseFailAlloc_1715_;
goto v_reusejp_1713_;
}
v_reusejp_1713_:
{
return v___x_1714_;
}
}
}
}
}
}
else
{
lean_object* v_a_1718_; lean_object* v___x_1720_; uint8_t v_isShared_1721_; uint8_t v_isSharedCheck_1725_; 
lean_dec(v_val_1577_);
lean_dec(v_val_1546_);
lean_dec_ref(v_toRing_1545_);
lean_dec_ref(v_a_1512_);
lean_dec_ref(v_e_1510_);
v_a_1718_ = lean_ctor_get(v___x_1584_, 0);
v_isSharedCheck_1725_ = !lean_is_exclusive(v___x_1584_);
if (v_isSharedCheck_1725_ == 0)
{
v___x_1720_ = v___x_1584_;
v_isShared_1721_ = v_isSharedCheck_1725_;
goto v_resetjp_1719_;
}
else
{
lean_inc(v_a_1718_);
lean_dec(v___x_1584_);
v___x_1720_ = lean_box(0);
v_isShared_1721_ = v_isSharedCheck_1725_;
goto v_resetjp_1719_;
}
v_resetjp_1719_:
{
lean_object* v___x_1723_; 
if (v_isShared_1721_ == 0)
{
v___x_1723_ = v___x_1720_;
goto v_reusejp_1722_;
}
else
{
lean_object* v_reuseFailAlloc_1724_; 
v_reuseFailAlloc_1724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1724_, 0, v_a_1718_);
v___x_1723_ = v_reuseFailAlloc_1724_;
goto v_reusejp_1722_;
}
v_reusejp_1722_:
{
return v___x_1723_;
}
}
}
}
}
else
{
lean_object* v_a_1726_; lean_object* v___x_1728_; uint8_t v_isShared_1729_; uint8_t v_isSharedCheck_1733_; 
lean_dec(v_val_1577_);
lean_dec(v_val_1546_);
lean_dec_ref(v_toRing_1545_);
lean_dec_ref(v_a_1512_);
lean_dec_ref(v_e_1510_);
v_a_1726_ = lean_ctor_get(v___x_1581_, 0);
v_isSharedCheck_1733_ = !lean_is_exclusive(v___x_1581_);
if (v_isSharedCheck_1733_ == 0)
{
v___x_1728_ = v___x_1581_;
v_isShared_1729_ = v_isSharedCheck_1733_;
goto v_resetjp_1727_;
}
else
{
lean_inc(v_a_1726_);
lean_dec(v___x_1581_);
v___x_1728_ = lean_box(0);
v_isShared_1729_ = v_isSharedCheck_1733_;
goto v_resetjp_1727_;
}
v_resetjp_1727_:
{
lean_object* v___x_1731_; 
if (v_isShared_1729_ == 0)
{
v___x_1731_ = v___x_1728_;
goto v_reusejp_1730_;
}
else
{
lean_object* v_reuseFailAlloc_1732_; 
v_reuseFailAlloc_1732_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1732_, 0, v_a_1726_);
v___x_1731_ = v_reuseFailAlloc_1732_;
goto v_reusejp_1730_;
}
v_reusejp_1730_:
{
return v___x_1731_;
}
}
}
}
else
{
lean_object* v_type_1734_; lean_object* v_u_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; 
lean_dec(v_val_1577_);
v_type_1734_ = lean_ctor_get(v_toRing_1545_, 1);
lean_inc_ref(v_type_1734_);
v_u_1735_ = lean_ctor_get(v_toRing_1545_, 2);
lean_inc(v_u_1735_);
lean_dec_ref(v_toRing_1545_);
v___x_1736_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__11));
v___x_1737_ = lean_box(0);
v___x_1738_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1738_, 0, v_u_1735_);
lean_ctor_set(v___x_1738_, 1, v___x_1737_);
v___x_1739_ = l_Lean_mkConst(v___x_1736_, v___x_1738_);
v___x_1740_ = l_Lean_mkAppB(v___x_1739_, v_type_1734_, v_val_1546_);
v___x_1741_ = l_Lean_Meta_Grind_pushEqCore___redArg(v_e_1510_, v_a_1512_, v___x_1740_, v___x_1573_, v_a_1514_, v_a_1516_, v_a_1520_, v_a_1521_, v_a_1522_, v_a_1523_);
if (lean_obj_tag(v___x_1741_) == 0)
{
lean_object* v___x_1743_; uint8_t v_isShared_1744_; uint8_t v_isSharedCheck_1749_; 
v_isSharedCheck_1749_ = !lean_is_exclusive(v___x_1741_);
if (v_isSharedCheck_1749_ == 0)
{
lean_object* v_unused_1750_; 
v_unused_1750_ = lean_ctor_get(v___x_1741_, 0);
lean_dec(v_unused_1750_);
v___x_1743_ = v___x_1741_;
v_isShared_1744_ = v_isSharedCheck_1749_;
goto v_resetjp_1742_;
}
else
{
lean_dec(v___x_1741_);
v___x_1743_ = lean_box(0);
v_isShared_1744_ = v_isSharedCheck_1749_;
goto v_resetjp_1742_;
}
v_resetjp_1742_:
{
lean_object* v___x_1745_; lean_object* v___x_1747_; 
v___x_1745_ = lean_box(0);
if (v_isShared_1744_ == 0)
{
lean_ctor_set(v___x_1743_, 0, v___x_1745_);
v___x_1747_ = v___x_1743_;
goto v_reusejp_1746_;
}
else
{
lean_object* v_reuseFailAlloc_1748_; 
v_reuseFailAlloc_1748_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1748_, 0, v___x_1745_);
v___x_1747_ = v_reuseFailAlloc_1748_;
goto v_reusejp_1746_;
}
v_reusejp_1746_:
{
return v___x_1747_;
}
}
}
else
{
return v___x_1741_;
}
}
}
else
{
lean_dec(v_a_1576_);
lean_dec_ref(v_e_1510_);
v___y_1548_ = v_a_1514_;
v___y_1549_ = v_a_1515_;
v___y_1550_ = v_a_1516_;
v___y_1551_ = v_a_1517_;
v___y_1552_ = v_a_1518_;
v___y_1553_ = v_a_1519_;
v___y_1554_ = v_a_1520_;
v___y_1555_ = v_a_1521_;
v___y_1556_ = v_a_1522_;
v___y_1557_ = v_a_1523_;
goto v___jp_1547_;
}
}
else
{
lean_object* v_a_1751_; lean_object* v___x_1753_; uint8_t v_isShared_1754_; uint8_t v_isSharedCheck_1758_; 
lean_dec(v_val_1546_);
lean_dec_ref(v_toRing_1545_);
lean_dec_ref(v_a_1512_);
lean_dec_ref(v_e_1510_);
v_a_1751_ = lean_ctor_get(v___x_1575_, 0);
v_isSharedCheck_1758_ = !lean_is_exclusive(v___x_1575_);
if (v_isSharedCheck_1758_ == 0)
{
v___x_1753_ = v___x_1575_;
v_isShared_1754_ = v_isSharedCheck_1758_;
goto v_resetjp_1752_;
}
else
{
lean_inc(v_a_1751_);
lean_dec(v___x_1575_);
v___x_1753_ = lean_box(0);
v_isShared_1754_ = v_isSharedCheck_1758_;
goto v_resetjp_1752_;
}
v_resetjp_1752_:
{
lean_object* v___x_1756_; 
if (v_isShared_1754_ == 0)
{
v___x_1756_ = v___x_1753_;
goto v_reusejp_1755_;
}
else
{
lean_object* v_reuseFailAlloc_1757_; 
v_reuseFailAlloc_1757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1757_, 0, v_a_1751_);
v___x_1756_ = v_reuseFailAlloc_1757_;
goto v_reusejp_1755_;
}
v_reusejp_1755_:
{
return v___x_1756_;
}
}
}
}
else
{
lean_dec(v_val_1546_);
lean_dec_ref(v_toRing_1545_);
lean_dec_ref(v_a_1512_);
lean_dec_ref(v_e_1510_);
return v___x_1574_;
}
}
else
{
lean_object* v___x_1759_; lean_object* v___x_1761_; 
lean_dec(v_val_1546_);
lean_dec_ref(v_toRing_1545_);
lean_dec_ref(v___f_1528_);
lean_dec_ref(v_a_1512_);
lean_dec_ref(v_e_1510_);
v___x_1759_ = lean_box(0);
if (v_isShared_1571_ == 0)
{
lean_ctor_set(v___x_1570_, 0, v___x_1759_);
v___x_1761_ = v___x_1570_;
goto v_reusejp_1760_;
}
else
{
lean_object* v_reuseFailAlloc_1762_; 
v_reuseFailAlloc_1762_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1762_, 0, v___x_1759_);
v___x_1761_ = v_reuseFailAlloc_1762_;
goto v_reusejp_1760_;
}
v_reusejp_1760_:
{
return v___x_1761_;
}
}
}
}
else
{
lean_object* v_a_1764_; lean_object* v___x_1766_; uint8_t v_isShared_1767_; uint8_t v_isSharedCheck_1771_; 
lean_dec(v_val_1546_);
lean_dec_ref(v_toRing_1545_);
lean_dec_ref(v___f_1528_);
lean_dec_ref(v_a_1512_);
lean_dec_ref(v_e_1510_);
v_a_1764_ = lean_ctor_get(v___x_1567_, 0);
v_isSharedCheck_1771_ = !lean_is_exclusive(v___x_1567_);
if (v_isSharedCheck_1771_ == 0)
{
v___x_1766_ = v___x_1567_;
v_isShared_1767_ = v_isSharedCheck_1771_;
goto v_resetjp_1765_;
}
else
{
lean_inc(v_a_1764_);
lean_dec(v___x_1567_);
v___x_1766_ = lean_box(0);
v_isShared_1767_ = v_isSharedCheck_1771_;
goto v_resetjp_1765_;
}
v_resetjp_1765_:
{
lean_object* v___x_1769_; 
if (v_isShared_1767_ == 0)
{
v___x_1769_ = v___x_1766_;
goto v_reusejp_1768_;
}
else
{
lean_object* v_reuseFailAlloc_1770_; 
v_reuseFailAlloc_1770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1770_, 0, v_a_1764_);
v___x_1769_ = v_reuseFailAlloc_1770_;
goto v_reusejp_1768_;
}
v_reusejp_1768_:
{
return v___x_1769_;
}
}
}
v___jp_1547_:
{
lean_object* v_type_1558_; lean_object* v_u_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; 
v_type_1558_ = lean_ctor_get(v_toRing_1545_, 1);
lean_inc_ref(v_type_1558_);
v_u_1559_ = lean_ctor_get(v_toRing_1545_, 2);
lean_inc(v_u_1559_);
lean_dec_ref(v_toRing_1545_);
v___x_1560_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__2));
v___x_1561_ = lean_box(0);
v___x_1562_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1562_, 0, v_u_1559_);
lean_ctor_set(v___x_1562_, 1, v___x_1561_);
v___x_1563_ = l_Lean_mkConst(v___x_1560_, v___x_1562_);
v___x_1564_ = l_Lean_mkApp3(v___x_1563_, v_type_1558_, v_val_1546_, v_a_1512_);
v___x_1565_ = lean_unsigned_to_nat(0u);
v___x_1566_ = l_Lean_Meta_Grind_pushNewFact(v___x_1564_, v___x_1565_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_, v___y_1552_, v___y_1553_, v___y_1554_, v___y_1555_, v___y_1556_, v___y_1557_);
return v___x_1566_;
}
}
else
{
lean_object* v___x_1772_; lean_object* v___x_1774_; 
lean_dec(v_fieldInst_x3f_1544_);
lean_dec(v_a_1540_);
lean_dec_ref(v___f_1528_);
lean_dec_ref(v_a_1512_);
lean_dec_ref(v_e_1510_);
v___x_1772_ = lean_box(0);
if (v_isShared_1543_ == 0)
{
lean_ctor_set(v___x_1542_, 0, v___x_1772_);
v___x_1774_ = v___x_1542_;
goto v_reusejp_1773_;
}
else
{
lean_object* v_reuseFailAlloc_1775_; 
v_reuseFailAlloc_1775_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1775_, 0, v___x_1772_);
v___x_1774_ = v_reuseFailAlloc_1775_;
goto v_reusejp_1773_;
}
v_reusejp_1773_:
{
return v___x_1774_;
}
}
}
}
else
{
lean_object* v_a_1777_; lean_object* v___x_1779_; uint8_t v_isShared_1780_; uint8_t v_isSharedCheck_1784_; 
lean_dec_ref(v___f_1528_);
lean_dec_ref(v_a_1512_);
lean_dec_ref(v_e_1510_);
v_a_1777_ = lean_ctor_get(v___x_1539_, 0);
v_isSharedCheck_1784_ = !lean_is_exclusive(v___x_1539_);
if (v_isSharedCheck_1784_ == 0)
{
v___x_1779_ = v___x_1539_;
v_isShared_1780_ = v_isSharedCheck_1784_;
goto v_resetjp_1778_;
}
else
{
lean_inc(v_a_1777_);
lean_dec(v___x_1539_);
v___x_1779_ = lean_box(0);
v_isShared_1780_ = v_isSharedCheck_1784_;
goto v_resetjp_1778_;
}
v_resetjp_1778_:
{
lean_object* v___x_1782_; 
if (v_isShared_1780_ == 0)
{
v___x_1782_ = v___x_1779_;
goto v_reusejp_1781_;
}
else
{
lean_object* v_reuseFailAlloc_1783_; 
v_reuseFailAlloc_1783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1783_, 0, v_a_1777_);
v___x_1782_ = v_reuseFailAlloc_1783_;
goto v_reusejp_1781_;
}
v_reusejp_1781_:
{
return v___x_1782_;
}
}
}
}
}
}
else
{
lean_object* v_a_1786_; lean_object* v___x_1788_; uint8_t v_isShared_1789_; uint8_t v_isSharedCheck_1793_; 
lean_dec_ref(v___f_1528_);
lean_dec_ref(v_a_1512_);
lean_dec_ref(v_e_1510_);
v_a_1786_ = lean_ctor_get(v___x_1529_, 0);
v_isSharedCheck_1793_ = !lean_is_exclusive(v___x_1529_);
if (v_isSharedCheck_1793_ == 0)
{
v___x_1788_ = v___x_1529_;
v_isShared_1789_ = v_isSharedCheck_1793_;
goto v_resetjp_1787_;
}
else
{
lean_inc(v_a_1786_);
lean_dec(v___x_1529_);
v___x_1788_ = lean_box(0);
v_isShared_1789_ = v_isSharedCheck_1793_;
goto v_resetjp_1787_;
}
v_resetjp_1787_:
{
lean_object* v___x_1791_; 
if (v_isShared_1789_ == 0)
{
v___x_1791_ = v___x_1788_;
goto v_reusejp_1790_;
}
else
{
lean_object* v_reuseFailAlloc_1792_; 
v_reuseFailAlloc_1792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1792_, 0, v_a_1786_);
v___x_1791_ = v_reuseFailAlloc_1792_;
goto v_reusejp_1790_;
}
v_reusejp_1790_:
{
return v___x_1791_;
}
}
}
v___jp_1525_:
{
lean_object* v___x_1526_; lean_object* v___x_1527_; 
v___x_1526_ = lean_box(0);
v___x_1527_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1527_, 0, v___x_1526_);
return v___x_1527_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___boxed(lean_object* v_e_1794_, lean_object* v_inst_1795_, lean_object* v_a_1796_, lean_object* v_a_1797_, lean_object* v_a_1798_, lean_object* v_a_1799_, lean_object* v_a_1800_, lean_object* v_a_1801_, lean_object* v_a_1802_, lean_object* v_a_1803_, lean_object* v_a_1804_, lean_object* v_a_1805_, lean_object* v_a_1806_, lean_object* v_a_1807_, lean_object* v_a_1808_){
_start:
{
lean_object* v_res_1809_; 
v_res_1809_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv(v_e_1794_, v_inst_1795_, v_a_1796_, v_a_1797_, v_a_1798_, v_a_1799_, v_a_1800_, v_a_1801_, v_a_1802_, v_a_1803_, v_a_1804_, v_a_1805_, v_a_1806_, v_a_1807_);
lean_dec(v_a_1807_);
lean_dec_ref(v_a_1806_);
lean_dec(v_a_1805_);
lean_dec_ref(v_a_1804_);
lean_dec(v_a_1803_);
lean_dec_ref(v_a_1802_);
lean_dec(v_a_1801_);
lean_dec_ref(v_a_1800_);
lean_dec(v_a_1799_);
lean_dec(v_a_1798_);
lean_dec_ref(v_a_1797_);
lean_dec_ref(v_inst_1795_);
return v_res_1809_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0(lean_object* v_00_u03b2_1810_, lean_object* v_x_1811_, lean_object* v_x_1812_, lean_object* v_x_1813_){
_start:
{
lean_object* v___x_1814_; 
v___x_1814_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0___redArg(v_x_1811_, v_x_1812_, v_x_1813_);
return v___x_1814_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1(lean_object* v_00_u03b2_1815_, lean_object* v_x_1816_, lean_object* v_x_1817_){
_start:
{
uint8_t v___x_1818_; 
v___x_1818_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1___redArg(v_x_1816_, v_x_1817_);
return v___x_1818_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1___boxed(lean_object* v_00_u03b2_1819_, lean_object* v_x_1820_, lean_object* v_x_1821_){
_start:
{
uint8_t v_res_1822_; lean_object* v_r_1823_; 
v_res_1822_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1(v_00_u03b2_1819_, v_x_1820_, v_x_1821_);
lean_dec_ref(v_x_1821_);
lean_dec_ref(v_x_1820_);
v_r_1823_ = lean_box(v_res_1822_);
return v_r_1823_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0(lean_object* v_00_u03b2_1824_, lean_object* v_x_1825_, size_t v_x_1826_, size_t v_x_1827_, lean_object* v_x_1828_, lean_object* v_x_1829_){
_start:
{
lean_object* v___x_1830_; 
v___x_1830_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg(v_x_1825_, v_x_1826_, v_x_1827_, v_x_1828_, v_x_1829_);
return v___x_1830_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1831_, lean_object* v_x_1832_, lean_object* v_x_1833_, lean_object* v_x_1834_, lean_object* v_x_1835_, lean_object* v_x_1836_){
_start:
{
size_t v_x_79719__boxed_1837_; size_t v_x_79720__boxed_1838_; lean_object* v_res_1839_; 
v_x_79719__boxed_1837_ = lean_unbox_usize(v_x_1833_);
lean_dec(v_x_1833_);
v_x_79720__boxed_1838_ = lean_unbox_usize(v_x_1834_);
lean_dec(v_x_1834_);
v_res_1839_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0(v_00_u03b2_1831_, v_x_1832_, v_x_79719__boxed_1837_, v_x_79720__boxed_1838_, v_x_1835_, v_x_1836_);
return v_res_1839_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1_spec__2(lean_object* v_00_u03b2_1840_, lean_object* v_x_1841_, size_t v_x_1842_, lean_object* v_x_1843_){
_start:
{
uint8_t v___x_1844_; 
v___x_1844_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1_spec__2___redArg(v_x_1841_, v_x_1842_, v_x_1843_);
return v___x_1844_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1845_, lean_object* v_x_1846_, lean_object* v_x_1847_, lean_object* v_x_1848_){
_start:
{
size_t v_x_79736__boxed_1849_; uint8_t v_res_1850_; lean_object* v_r_1851_; 
v_x_79736__boxed_1849_ = lean_unbox_usize(v_x_1847_);
lean_dec(v_x_1847_);
v_res_1850_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1_spec__2(v_00_u03b2_1845_, v_x_1846_, v_x_79736__boxed_1849_, v_x_1848_);
lean_dec_ref(v_x_1848_);
lean_dec_ref(v_x_1846_);
v_r_1851_ = lean_box(v_res_1850_);
return v_r_1851_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1852_, lean_object* v_n_1853_, lean_object* v_k_1854_, lean_object* v_v_1855_){
_start:
{
lean_object* v___x_1856_; 
v___x_1856_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0_spec__1___redArg(v_n_1853_, v_k_1854_, v_v_1855_);
return v___x_1856_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_1857_, size_t v_depth_1858_, lean_object* v_keys_1859_, lean_object* v_vals_1860_, lean_object* v_heq_1861_, lean_object* v_i_1862_, lean_object* v_entries_1863_){
_start:
{
lean_object* v___x_1864_; 
v___x_1864_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0_spec__2___redArg(v_depth_1858_, v_keys_1859_, v_vals_1860_, v_i_1862_, v_entries_1863_);
return v___x_1864_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1865_, lean_object* v_depth_1866_, lean_object* v_keys_1867_, lean_object* v_vals_1868_, lean_object* v_heq_1869_, lean_object* v_i_1870_, lean_object* v_entries_1871_){
_start:
{
size_t v_depth_boxed_1872_; lean_object* v_res_1873_; 
v_depth_boxed_1872_ = lean_unbox_usize(v_depth_1866_);
lean_dec(v_depth_1866_);
v_res_1873_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0_spec__2(v_00_u03b2_1865_, v_depth_boxed_1872_, v_keys_1867_, v_vals_1868_, v_heq_1869_, v_i_1870_, v_entries_1871_);
lean_dec_ref(v_vals_1868_);
lean_dec_ref(v_keys_1867_);
return v_res_1873_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_1874_, lean_object* v_keys_1875_, lean_object* v_vals_1876_, lean_object* v_heq_1877_, lean_object* v_i_1878_, lean_object* v_k_1879_){
_start:
{
uint8_t v___x_1880_; 
v___x_1880_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1_spec__2_spec__5___redArg(v_keys_1875_, v_i_1878_, v_k_1879_);
return v___x_1880_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b2_1881_, lean_object* v_keys_1882_, lean_object* v_vals_1883_, lean_object* v_heq_1884_, lean_object* v_i_1885_, lean_object* v_k_1886_){
_start:
{
uint8_t v_res_1887_; lean_object* v_r_1888_; 
v_res_1887_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1_spec__2_spec__5(v_00_u03b2_1881_, v_keys_1882_, v_vals_1883_, v_heq_1884_, v_i_1885_, v_k_1886_);
lean_dec_ref(v_k_1886_);
lean_dec_ref(v_vals_1883_);
lean_dec_ref(v_keys_1882_);
v_r_1888_ = lean_box(v_res_1887_);
return v_r_1888_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0_spec__1_spec__5(lean_object* v_00_u03b2_1889_, lean_object* v_x_1890_, lean_object* v_x_1891_, lean_object* v_x_1892_, lean_object* v_x_1893_){
_start:
{
lean_object* v___x_1894_; 
v___x_1894_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0_spec__1_spec__5___redArg(v_x_1890_, v_x_1891_, v_x_1892_, v_x_1893_);
return v___x_1894_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars___lam__0(lean_object* v_size_1895_, lean_object* v_s_1896_){
_start:
{
lean_object* v_toRingState_1897_; lean_object* v_denoteEntries_1898_; lean_object* v_nextId_1899_; lean_object* v_steps_1900_; lean_object* v_queue_1901_; lean_object* v_basis_1902_; lean_object* v_diseqs_1903_; uint8_t v_recheck_1904_; lean_object* v_invSet_1905_; lean_object* v_numEq0_x3f_1906_; uint8_t v_numEq0Updated_1907_; lean_object* v___x_1909_; uint8_t v_isShared_1910_; uint8_t v_isSharedCheck_1914_; 
v_toRingState_1897_ = lean_ctor_get(v_s_1896_, 0);
v_denoteEntries_1898_ = lean_ctor_get(v_s_1896_, 1);
v_nextId_1899_ = lean_ctor_get(v_s_1896_, 2);
v_steps_1900_ = lean_ctor_get(v_s_1896_, 3);
v_queue_1901_ = lean_ctor_get(v_s_1896_, 4);
v_basis_1902_ = lean_ctor_get(v_s_1896_, 5);
v_diseqs_1903_ = lean_ctor_get(v_s_1896_, 6);
v_recheck_1904_ = lean_ctor_get_uint8(v_s_1896_, sizeof(void*)*10);
v_invSet_1905_ = lean_ctor_get(v_s_1896_, 7);
v_numEq0_x3f_1906_ = lean_ctor_get(v_s_1896_, 9);
v_numEq0Updated_1907_ = lean_ctor_get_uint8(v_s_1896_, sizeof(void*)*10 + 1);
v_isSharedCheck_1914_ = !lean_is_exclusive(v_s_1896_);
if (v_isSharedCheck_1914_ == 0)
{
lean_object* v_unused_1915_; 
v_unused_1915_ = lean_ctor_get(v_s_1896_, 8);
lean_dec(v_unused_1915_);
v___x_1909_ = v_s_1896_;
v_isShared_1910_ = v_isSharedCheck_1914_;
goto v_resetjp_1908_;
}
else
{
lean_inc(v_numEq0_x3f_1906_);
lean_inc(v_invSet_1905_);
lean_inc(v_diseqs_1903_);
lean_inc(v_basis_1902_);
lean_inc(v_queue_1901_);
lean_inc(v_steps_1900_);
lean_inc(v_nextId_1899_);
lean_inc(v_denoteEntries_1898_);
lean_inc(v_toRingState_1897_);
lean_dec(v_s_1896_);
v___x_1909_ = lean_box(0);
v_isShared_1910_ = v_isSharedCheck_1914_;
goto v_resetjp_1908_;
}
v_resetjp_1908_:
{
lean_object* v___x_1912_; 
if (v_isShared_1910_ == 0)
{
lean_ctor_set(v___x_1909_, 8, v_size_1895_);
v___x_1912_ = v___x_1909_;
goto v_reusejp_1911_;
}
else
{
lean_object* v_reuseFailAlloc_1913_; 
v_reuseFailAlloc_1913_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v_reuseFailAlloc_1913_, 0, v_toRingState_1897_);
lean_ctor_set(v_reuseFailAlloc_1913_, 1, v_denoteEntries_1898_);
lean_ctor_set(v_reuseFailAlloc_1913_, 2, v_nextId_1899_);
lean_ctor_set(v_reuseFailAlloc_1913_, 3, v_steps_1900_);
lean_ctor_set(v_reuseFailAlloc_1913_, 4, v_queue_1901_);
lean_ctor_set(v_reuseFailAlloc_1913_, 5, v_basis_1902_);
lean_ctor_set(v_reuseFailAlloc_1913_, 6, v_diseqs_1903_);
lean_ctor_set(v_reuseFailAlloc_1913_, 7, v_invSet_1905_);
lean_ctor_set(v_reuseFailAlloc_1913_, 8, v_size_1895_);
lean_ctor_set(v_reuseFailAlloc_1913_, 9, v_numEq0_x3f_1906_);
lean_ctor_set_uint8(v_reuseFailAlloc_1913_, sizeof(void*)*10, v_recheck_1904_);
lean_ctor_set_uint8(v_reuseFailAlloc_1913_, sizeof(void*)*10 + 1, v_numEq0Updated_1907_);
v___x_1912_ = v_reuseFailAlloc_1913_;
goto v_reusejp_1911_;
}
v_reusejp_1911_:
{
return v___x_1912_;
}
}
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1916_; double v___x_1917_; 
v___x_1916_ = lean_unsigned_to_nat(0u);
v___x_1917_ = lean_float_of_nat(v___x_1916_);
return v___x_1917_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg(lean_object* v_cls_1921_, lean_object* v_msg_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_){
_start:
{
lean_object* v_ref_1928_; lean_object* v___x_1929_; lean_object* v_a_1930_; lean_object* v___x_1932_; uint8_t v_isShared_1933_; uint8_t v_isSharedCheck_1975_; 
v_ref_1928_ = lean_ctor_get(v___y_1925_, 2);
v___x_1929_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5(v_msg_1922_, v___y_1923_, v___y_1924_, v___y_1925_, v___y_1926_);
v_a_1930_ = lean_ctor_get(v___x_1929_, 0);
v_isSharedCheck_1975_ = !lean_is_exclusive(v___x_1929_);
if (v_isSharedCheck_1975_ == 0)
{
v___x_1932_ = v___x_1929_;
v_isShared_1933_ = v_isSharedCheck_1975_;
goto v_resetjp_1931_;
}
else
{
lean_inc(v_a_1930_);
lean_dec(v___x_1929_);
v___x_1932_ = lean_box(0);
v_isShared_1933_ = v_isSharedCheck_1975_;
goto v_resetjp_1931_;
}
v_resetjp_1931_:
{
lean_object* v___x_1934_; lean_object* v_traceState_1935_; lean_object* v_env_1936_; lean_object* v_nextMacroScope_1937_; lean_object* v_ngen_1938_; lean_object* v_auxDeclNGen_1939_; lean_object* v_cache_1940_; lean_object* v_recordedDeps_1941_; lean_object* v_messages_1942_; lean_object* v_infoState_1943_; lean_object* v_snapshotTasks_1944_; lean_object* v___x_1946_; uint8_t v_isShared_1947_; uint8_t v_isSharedCheck_1974_; 
v___x_1934_ = lean_st_ref_take(v___y_1926_);
v_traceState_1935_ = lean_ctor_get(v___x_1934_, 4);
v_env_1936_ = lean_ctor_get(v___x_1934_, 0);
v_nextMacroScope_1937_ = lean_ctor_get(v___x_1934_, 1);
v_ngen_1938_ = lean_ctor_get(v___x_1934_, 2);
v_auxDeclNGen_1939_ = lean_ctor_get(v___x_1934_, 3);
v_cache_1940_ = lean_ctor_get(v___x_1934_, 5);
v_recordedDeps_1941_ = lean_ctor_get(v___x_1934_, 6);
v_messages_1942_ = lean_ctor_get(v___x_1934_, 7);
v_infoState_1943_ = lean_ctor_get(v___x_1934_, 8);
v_snapshotTasks_1944_ = lean_ctor_get(v___x_1934_, 9);
v_isSharedCheck_1974_ = !lean_is_exclusive(v___x_1934_);
if (v_isSharedCheck_1974_ == 0)
{
v___x_1946_ = v___x_1934_;
v_isShared_1947_ = v_isSharedCheck_1974_;
goto v_resetjp_1945_;
}
else
{
lean_inc(v_snapshotTasks_1944_);
lean_inc(v_infoState_1943_);
lean_inc(v_messages_1942_);
lean_inc(v_recordedDeps_1941_);
lean_inc(v_cache_1940_);
lean_inc(v_traceState_1935_);
lean_inc(v_auxDeclNGen_1939_);
lean_inc(v_ngen_1938_);
lean_inc(v_nextMacroScope_1937_);
lean_inc(v_env_1936_);
lean_dec(v___x_1934_);
v___x_1946_ = lean_box(0);
v_isShared_1947_ = v_isSharedCheck_1974_;
goto v_resetjp_1945_;
}
v_resetjp_1945_:
{
uint64_t v_tid_1948_; lean_object* v_traces_1949_; lean_object* v___x_1951_; uint8_t v_isShared_1952_; uint8_t v_isSharedCheck_1973_; 
v_tid_1948_ = lean_ctor_get_uint64(v_traceState_1935_, sizeof(void*)*1);
v_traces_1949_ = lean_ctor_get(v_traceState_1935_, 0);
v_isSharedCheck_1973_ = !lean_is_exclusive(v_traceState_1935_);
if (v_isSharedCheck_1973_ == 0)
{
v___x_1951_ = v_traceState_1935_;
v_isShared_1952_ = v_isSharedCheck_1973_;
goto v_resetjp_1950_;
}
else
{
lean_inc(v_traces_1949_);
lean_dec(v_traceState_1935_);
v___x_1951_ = lean_box(0);
v_isShared_1952_ = v_isSharedCheck_1973_;
goto v_resetjp_1950_;
}
v_resetjp_1950_:
{
lean_object* v___x_1953_; lean_object* v___x_1954_; double v___x_1955_; uint8_t v___x_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; lean_object* v___x_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1964_; 
v___x_1953_ = lean_box(0);
v___x_1954_ = lean_box(0);
v___x_1955_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg___closed__0);
v___x_1956_ = 0;
v___x_1957_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg___closed__1));
v___x_1958_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1958_, 0, v_cls_1921_);
lean_ctor_set(v___x_1958_, 1, v___x_1954_);
lean_ctor_set(v___x_1958_, 2, v___x_1957_);
lean_ctor_set_float(v___x_1958_, sizeof(void*)*3, v___x_1955_);
lean_ctor_set_float(v___x_1958_, sizeof(void*)*3 + 8, v___x_1955_);
lean_ctor_set_uint8(v___x_1958_, sizeof(void*)*3 + 16, v___x_1956_);
v___x_1959_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg___closed__2));
v___x_1960_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1960_, 0, v___x_1958_);
lean_ctor_set(v___x_1960_, 1, v_a_1930_);
lean_ctor_set(v___x_1960_, 2, v___x_1959_);
lean_inc(v_ref_1928_);
v___x_1961_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1961_, 0, v_ref_1928_);
lean_ctor_set(v___x_1961_, 1, v___x_1960_);
v___x_1962_ = l_Lean_PersistentArray_push___redArg(v_traces_1949_, v___x_1961_);
if (v_isShared_1952_ == 0)
{
lean_ctor_set(v___x_1951_, 0, v___x_1962_);
v___x_1964_ = v___x_1951_;
goto v_reusejp_1963_;
}
else
{
lean_object* v_reuseFailAlloc_1972_; 
v_reuseFailAlloc_1972_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1972_, 0, v___x_1962_);
lean_ctor_set_uint64(v_reuseFailAlloc_1972_, sizeof(void*)*1, v_tid_1948_);
v___x_1964_ = v_reuseFailAlloc_1972_;
goto v_reusejp_1963_;
}
v_reusejp_1963_:
{
lean_object* v___x_1966_; 
if (v_isShared_1947_ == 0)
{
lean_ctor_set(v___x_1946_, 4, v___x_1964_);
v___x_1966_ = v___x_1946_;
goto v_reusejp_1965_;
}
else
{
lean_object* v_reuseFailAlloc_1971_; 
v_reuseFailAlloc_1971_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1971_, 0, v_env_1936_);
lean_ctor_set(v_reuseFailAlloc_1971_, 1, v_nextMacroScope_1937_);
lean_ctor_set(v_reuseFailAlloc_1971_, 2, v_ngen_1938_);
lean_ctor_set(v_reuseFailAlloc_1971_, 3, v_auxDeclNGen_1939_);
lean_ctor_set(v_reuseFailAlloc_1971_, 4, v___x_1964_);
lean_ctor_set(v_reuseFailAlloc_1971_, 5, v_cache_1940_);
lean_ctor_set(v_reuseFailAlloc_1971_, 6, v_recordedDeps_1941_);
lean_ctor_set(v_reuseFailAlloc_1971_, 7, v_messages_1942_);
lean_ctor_set(v_reuseFailAlloc_1971_, 8, v_infoState_1943_);
lean_ctor_set(v_reuseFailAlloc_1971_, 9, v_snapshotTasks_1944_);
v___x_1966_ = v_reuseFailAlloc_1971_;
goto v_reusejp_1965_;
}
v_reusejp_1965_:
{
lean_object* v___x_1967_; lean_object* v___x_1969_; 
v___x_1967_ = lean_st_ref_put(v___y_1926_, v___x_1966_);
if (v_isShared_1933_ == 0)
{
lean_ctor_set(v___x_1932_, 0, v___x_1953_);
v___x_1969_ = v___x_1932_;
goto v_reusejp_1968_;
}
else
{
lean_object* v_reuseFailAlloc_1970_; 
v_reuseFailAlloc_1970_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1970_, 0, v___x_1953_);
v___x_1969_ = v_reuseFailAlloc_1970_;
goto v_reusejp_1968_;
}
v_reusejp_1968_:
{
return v___x_1969_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg___boxed(lean_object* v_cls_1976_, lean_object* v_msg_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_){
_start:
{
lean_object* v_res_1983_; 
v_res_1983_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg(v_cls_1976_, v_msg_1977_, v___y_1978_, v___y_1979_, v___y_1980_, v___y_1981_);
lean_dec(v___y_1981_);
lean_dec_ref(v___y_1980_);
lean_dec(v___y_1979_);
lean_dec_ref(v___y_1978_);
return v_res_1983_;
}
}
static lean_object* _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__8(void){
_start:
{
lean_object* v___x_1999_; lean_object* v___x_2000_; lean_object* v___x_2001_; 
v___x_1999_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__5));
v___x_2000_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__7));
v___x_2001_ = l_Lean_Name_append(v___x_2000_, v___x_1999_);
return v___x_2001_;
}
}
static lean_object* _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__10(void){
_start:
{
lean_object* v___x_2003_; lean_object* v___x_2004_; 
v___x_2003_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__9));
v___x_2004_ = l_Lean_stringToMessageData(v___x_2003_);
return v___x_2004_;
}
}
static lean_object* _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__12(void){
_start:
{
lean_object* v___x_2006_; lean_object* v___x_2007_; 
v___x_2006_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__11));
v___x_2007_ = l_Lean_stringToMessageData(v___x_2006_);
return v___x_2007_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg(lean_object* v_a_2008_, lean_object* v_snd_2009_, lean_object* v_fst_2010_, lean_object* v_fst_2011_, lean_object* v___x_2012_, lean_object* v_range_2013_, lean_object* v_b_2014_, lean_object* v_i_2015_, lean_object* v___y_2016_, lean_object* v___y_2017_, lean_object* v___y_2018_, lean_object* v___y_2019_, lean_object* v___y_2020_, lean_object* v___y_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_){
_start:
{
lean_object* v_stop_2028_; lean_object* v_step_2029_; uint8_t v___x_2030_; 
v_stop_2028_ = lean_ctor_get(v_range_2013_, 1);
v_step_2029_ = lean_ctor_get(v_range_2013_, 2);
v___x_2030_ = lean_nat_dec_lt(v_i_2015_, v_stop_2028_);
if (v___x_2030_ == 0)
{
lean_object* v___x_2031_; 
lean_dec(v_i_2015_);
lean_dec_ref(v_fst_2011_);
lean_dec_ref(v_fst_2010_);
lean_dec(v_snd_2009_);
lean_dec_ref(v_a_2008_);
v___x_2031_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2031_, 0, v_b_2014_);
return v___x_2031_;
}
else
{
lean_object* v_size_2032_; lean_object* v___x_2033_; lean_object* v___y_2035_; lean_object* v___y_2036_; lean_object* v___y_2037_; lean_object* v___y_2038_; lean_object* v___y_2039_; lean_object* v___y_2040_; lean_object* v___y_2041_; lean_object* v___y_2042_; lean_object* v___y_2043_; lean_object* v___y_2044_; lean_object* v___y_2045_; lean_object* v___y_2060_; lean_object* v___x_2086_; uint8_t v___x_2087_; 
v_size_2032_ = lean_ctor_get(v___x_2012_, 2);
v___x_2033_ = lean_box(0);
v___x_2086_ = l_Lean_instInhabitedExpr;
v___x_2087_ = lean_nat_dec_lt(v_i_2015_, v_size_2032_);
if (v___x_2087_ == 0)
{
lean_object* v___x_2088_; 
v___x_2088_ = l_outOfBounds___redArg(v___x_2086_);
v___y_2060_ = v___x_2088_;
goto v___jp_2059_;
}
else
{
lean_object* v___x_2089_; 
v___x_2089_ = l_Lean_PersistentArray_get_x21___redArg(v___x_2086_, v___x_2012_, v_i_2015_);
v___y_2060_ = v___x_2089_;
goto v___jp_2059_;
}
v___jp_2034_:
{
lean_object* v_toRing_2046_; lean_object* v_type_2047_; lean_object* v_u_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; 
v_toRing_2046_ = lean_ctor_get(v_a_2008_, 0);
v_type_2047_ = lean_ctor_get(v_toRing_2046_, 1);
v_u_2048_ = lean_ctor_get(v_toRing_2046_, 2);
v___x_2049_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__2));
v___x_2050_ = lean_box(0);
lean_inc(v_u_2048_);
v___x_2051_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2051_, 0, v_u_2048_);
lean_ctor_set(v___x_2051_, 1, v___x_2050_);
v___x_2052_ = l_Lean_mkConst(v___x_2049_, v___x_2051_);
lean_inc(v_snd_2009_);
v___x_2053_ = l_Lean_mkNatLit(v_snd_2009_);
lean_inc_ref(v_fst_2011_);
lean_inc_ref(v_fst_2010_);
lean_inc_ref(v_type_2047_);
v___x_2054_ = l_Lean_mkApp5(v___x_2052_, v_type_2047_, v_fst_2010_, v___x_2053_, v_fst_2011_, v___y_2035_);
v___x_2055_ = lean_unsigned_to_nat(0u);
v___x_2056_ = l_Lean_Meta_Grind_pushNewFact(v___x_2054_, v___x_2055_, v___y_2036_, v___y_2037_, v___y_2038_, v___y_2039_, v___y_2040_, v___y_2041_, v___y_2042_, v___y_2043_, v___y_2044_, v___y_2045_);
if (lean_obj_tag(v___x_2056_) == 0)
{
lean_object* v___x_2057_; 
lean_dec_ref_known(v___x_2056_, 1);
v___x_2057_ = lean_nat_add(v_i_2015_, v_step_2029_);
lean_dec(v_i_2015_);
v_b_2014_ = v___x_2033_;
v_i_2015_ = v___x_2057_;
goto _start;
}
else
{
lean_dec(v_i_2015_);
lean_dec_ref(v_fst_2011_);
lean_dec_ref(v_fst_2010_);
lean_dec(v_snd_2009_);
lean_dec_ref(v_a_2008_);
return v___x_2056_;
}
}
v___jp_2059_:
{
lean_object* v_toCold_2061_; lean_object* v_options_2062_; uint8_t v_hasTrace_2063_; 
v_toCold_2061_ = lean_ctor_get(v___y_2025_, 0);
v_options_2062_ = lean_ctor_get(v_toCold_2061_, 2);
v_hasTrace_2063_ = lean_ctor_get_uint8(v_options_2062_, sizeof(void*)*1);
if (v_hasTrace_2063_ == 0)
{
v___y_2035_ = v___y_2060_;
v___y_2036_ = v___y_2017_;
v___y_2037_ = v___y_2018_;
v___y_2038_ = v___y_2019_;
v___y_2039_ = v___y_2020_;
v___y_2040_ = v___y_2021_;
v___y_2041_ = v___y_2022_;
v___y_2042_ = v___y_2023_;
v___y_2043_ = v___y_2024_;
v___y_2044_ = v___y_2025_;
v___y_2045_ = v___y_2026_;
goto v___jp_2034_;
}
else
{
lean_object* v_inheritedTraceOptions_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; uint8_t v___x_2067_; 
v_inheritedTraceOptions_2064_ = lean_ctor_get(v_toCold_2061_, 11);
v___x_2065_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__5));
v___x_2066_ = lean_obj_once(&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__8, &l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__8_once, _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__8);
v___x_2067_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2064_, v_options_2062_, v___x_2066_);
if (v___x_2067_ == 0)
{
v___y_2035_ = v___y_2060_;
v___y_2036_ = v___y_2017_;
v___y_2037_ = v___y_2018_;
v___y_2038_ = v___y_2019_;
v___y_2039_ = v___y_2020_;
v___y_2040_ = v___y_2021_;
v___y_2041_ = v___y_2022_;
v___y_2042_ = v___y_2023_;
v___y_2043_ = v___y_2024_;
v___y_2044_ = v___y_2025_;
v___y_2045_ = v___y_2026_;
goto v___jp_2034_;
}
else
{
lean_object* v___x_2068_; 
v___x_2068_ = l_Lean_Meta_Grind_updateLastTag(v___y_2017_, v___y_2018_, v___y_2019_, v___y_2020_, v___y_2021_, v___y_2022_, v___y_2023_, v___y_2024_, v___y_2025_, v___y_2026_);
if (lean_obj_tag(v___x_2068_) == 0)
{
lean_object* v___x_2070_; uint8_t v_isShared_2071_; uint8_t v_isSharedCheck_2084_; 
v_isSharedCheck_2084_ = !lean_is_exclusive(v___x_2068_);
if (v_isSharedCheck_2084_ == 0)
{
lean_object* v_unused_2085_; 
v_unused_2085_ = lean_ctor_get(v___x_2068_, 0);
lean_dec(v_unused_2085_);
v___x_2070_ = v___x_2068_;
v_isShared_2071_ = v_isSharedCheck_2084_;
goto v_resetjp_2069_;
}
else
{
lean_dec(v___x_2068_);
v___x_2070_ = lean_box(0);
v_isShared_2071_ = v_isSharedCheck_2084_;
goto v_resetjp_2069_;
}
v_resetjp_2069_:
{
lean_object* v___x_2072_; lean_object* v___x_2073_; lean_object* v___x_2075_; 
v___x_2072_ = lean_obj_once(&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__10, &l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__10_once, _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__10);
lean_inc(v_snd_2009_);
v___x_2073_ = l_Nat_reprFast(v_snd_2009_);
if (v_isShared_2071_ == 0)
{
lean_ctor_set_tag(v___x_2070_, 3);
lean_ctor_set(v___x_2070_, 0, v___x_2073_);
v___x_2075_ = v___x_2070_;
goto v_reusejp_2074_;
}
else
{
lean_object* v_reuseFailAlloc_2083_; 
v_reuseFailAlloc_2083_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2083_, 0, v___x_2073_);
v___x_2075_ = v_reuseFailAlloc_2083_;
goto v_reusejp_2074_;
}
v_reusejp_2074_:
{
lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; 
v___x_2076_ = l_Lean_MessageData_ofFormat(v___x_2075_);
v___x_2077_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2077_, 0, v___x_2072_);
lean_ctor_set(v___x_2077_, 1, v___x_2076_);
v___x_2078_ = lean_obj_once(&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__12, &l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__12_once, _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__12);
v___x_2079_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2079_, 0, v___x_2077_);
lean_ctor_set(v___x_2079_, 1, v___x_2078_);
lean_inc_ref(v___y_2060_);
v___x_2080_ = l_Lean_MessageData_ofExpr(v___y_2060_);
v___x_2081_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2081_, 0, v___x_2079_);
lean_ctor_set(v___x_2081_, 1, v___x_2080_);
v___x_2082_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg(v___x_2065_, v___x_2081_, v___y_2023_, v___y_2024_, v___y_2025_, v___y_2026_);
if (lean_obj_tag(v___x_2082_) == 0)
{
lean_dec_ref_known(v___x_2082_, 1);
v___y_2035_ = v___y_2060_;
v___y_2036_ = v___y_2017_;
v___y_2037_ = v___y_2018_;
v___y_2038_ = v___y_2019_;
v___y_2039_ = v___y_2020_;
v___y_2040_ = v___y_2021_;
v___y_2041_ = v___y_2022_;
v___y_2042_ = v___y_2023_;
v___y_2043_ = v___y_2024_;
v___y_2044_ = v___y_2025_;
v___y_2045_ = v___y_2026_;
goto v___jp_2034_;
}
else
{
lean_dec_ref(v___y_2060_);
lean_dec(v_i_2015_);
lean_dec_ref(v_fst_2011_);
lean_dec_ref(v_fst_2010_);
lean_dec(v_snd_2009_);
lean_dec_ref(v_a_2008_);
return v___x_2082_;
}
}
}
}
else
{
lean_dec_ref(v___y_2060_);
lean_dec(v_i_2015_);
lean_dec_ref(v_fst_2011_);
lean_dec_ref(v_fst_2010_);
lean_dec(v_snd_2009_);
lean_dec_ref(v_a_2008_);
return v___x_2068_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___boxed(lean_object** _args){
lean_object* v_a_2090_ = _args[0];
lean_object* v_snd_2091_ = _args[1];
lean_object* v_fst_2092_ = _args[2];
lean_object* v_fst_2093_ = _args[3];
lean_object* v___x_2094_ = _args[4];
lean_object* v_range_2095_ = _args[5];
lean_object* v_b_2096_ = _args[6];
lean_object* v_i_2097_ = _args[7];
lean_object* v___y_2098_ = _args[8];
lean_object* v___y_2099_ = _args[9];
lean_object* v___y_2100_ = _args[10];
lean_object* v___y_2101_ = _args[11];
lean_object* v___y_2102_ = _args[12];
lean_object* v___y_2103_ = _args[13];
lean_object* v___y_2104_ = _args[14];
lean_object* v___y_2105_ = _args[15];
lean_object* v___y_2106_ = _args[16];
lean_object* v___y_2107_ = _args[17];
lean_object* v___y_2108_ = _args[18];
lean_object* v___y_2109_ = _args[19];
_start:
{
lean_object* v_res_2110_; 
v_res_2110_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg(v_a_2090_, v_snd_2091_, v_fst_2092_, v_fst_2093_, v___x_2094_, v_range_2095_, v_b_2096_, v_i_2097_, v___y_2098_, v___y_2099_, v___y_2100_, v___y_2101_, v___y_2102_, v___y_2103_, v___y_2104_, v___y_2105_, v___y_2106_, v___y_2107_, v___y_2108_);
lean_dec(v___y_2108_);
lean_dec_ref(v___y_2107_);
lean_dec(v___y_2106_);
lean_dec_ref(v___y_2105_);
lean_dec(v___y_2104_);
lean_dec_ref(v___y_2103_);
lean_dec(v___y_2102_);
lean_dec_ref(v___y_2101_);
lean_dec(v___y_2100_);
lean_dec(v___y_2099_);
lean_dec_ref(v___y_2098_);
lean_dec_ref(v_range_2095_);
lean_dec_ref(v___x_2094_);
return v_res_2110_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars(lean_object* v_a_2111_, lean_object* v_a_2112_, lean_object* v_a_2113_, lean_object* v_a_2114_, lean_object* v_a_2115_, lean_object* v_a_2116_, lean_object* v_a_2117_, lean_object* v_a_2118_, lean_object* v_a_2119_, lean_object* v_a_2120_, lean_object* v_a_2121_){
_start:
{
lean_object* v___x_2123_; 
v___x_2123_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v_a_2111_, v_a_2112_, v_a_2113_, v_a_2114_, v_a_2115_, v_a_2116_, v_a_2117_, v_a_2118_, v_a_2119_, v_a_2120_, v_a_2121_);
if (lean_obj_tag(v___x_2123_) == 0)
{
lean_object* v_a_2124_; lean_object* v___x_2126_; uint8_t v_isShared_2127_; uint8_t v_isSharedCheck_2185_; 
v_a_2124_ = lean_ctor_get(v___x_2123_, 0);
v_isSharedCheck_2185_ = !lean_is_exclusive(v___x_2123_);
if (v_isSharedCheck_2185_ == 0)
{
v___x_2126_ = v___x_2123_;
v_isShared_2127_ = v_isSharedCheck_2185_;
goto v_resetjp_2125_;
}
else
{
lean_inc(v_a_2124_);
lean_dec(v___x_2123_);
v___x_2126_ = lean_box(0);
v_isShared_2127_ = v_isSharedCheck_2185_;
goto v_resetjp_2125_;
}
v_resetjp_2125_:
{
lean_object* v_powIdentityInst_x3f_2128_; 
v_powIdentityInst_x3f_2128_ = lean_ctor_get(v_a_2124_, 8);
if (lean_obj_tag(v_powIdentityInst_x3f_2128_) == 1)
{
lean_object* v_val_2129_; lean_object* v_snd_2130_; lean_object* v_fst_2131_; lean_object* v_fst_2132_; lean_object* v_snd_2133_; lean_object* v___x_2134_; 
lean_del_object(v___x_2126_);
v_val_2129_ = lean_ctor_get(v_powIdentityInst_x3f_2128_, 0);
v_snd_2130_ = lean_ctor_get(v_val_2129_, 1);
v_fst_2131_ = lean_ctor_get(v_val_2129_, 0);
lean_inc(v_fst_2131_);
v_fst_2132_ = lean_ctor_get(v_snd_2130_, 0);
lean_inc(v_fst_2132_);
v_snd_2133_ = lean_ctor_get(v_snd_2130_, 1);
lean_inc(v_snd_2133_);
v___x_2134_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRingState___redArg(v_a_2111_, v_a_2112_, v_a_2120_);
if (lean_obj_tag(v___x_2134_) == 0)
{
lean_object* v_a_2135_; lean_object* v_powIdentityVarCount_2136_; lean_object* v___x_2137_; 
v_a_2135_ = lean_ctor_get(v___x_2134_, 0);
lean_inc(v_a_2135_);
lean_dec_ref_known(v___x_2134_, 1);
v_powIdentityVarCount_2136_ = lean_ctor_get(v_a_2135_, 8);
lean_inc(v_powIdentityVarCount_2136_);
lean_dec(v_a_2135_);
v___x_2137_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRingState___redArg(v_a_2111_, v_a_2112_, v_a_2120_);
if (lean_obj_tag(v___x_2137_) == 0)
{
lean_object* v_a_2138_; lean_object* v___x_2140_; uint8_t v_isShared_2141_; uint8_t v_isSharedCheck_2164_; 
v_a_2138_ = lean_ctor_get(v___x_2137_, 0);
v_isSharedCheck_2164_ = !lean_is_exclusive(v___x_2137_);
if (v_isSharedCheck_2164_ == 0)
{
v___x_2140_ = v___x_2137_;
v_isShared_2141_ = v_isSharedCheck_2164_;
goto v_resetjp_2139_;
}
else
{
lean_inc(v_a_2138_);
lean_dec(v___x_2137_);
v___x_2140_ = lean_box(0);
v_isShared_2141_ = v_isSharedCheck_2164_;
goto v_resetjp_2139_;
}
v_resetjp_2139_:
{
lean_object* v_toRingState_2142_; lean_object* v_vars_2143_; lean_object* v___x_2145_; uint8_t v_isShared_2146_; uint8_t v_isSharedCheck_2161_; 
v_toRingState_2142_ = lean_ctor_get(v_a_2138_, 0);
lean_inc_ref(v_toRingState_2142_);
lean_dec(v_a_2138_);
v_vars_2143_ = lean_ctor_get(v_toRingState_2142_, 0);
v_isSharedCheck_2161_ = !lean_is_exclusive(v_toRingState_2142_);
if (v_isSharedCheck_2161_ == 0)
{
lean_object* v_unused_2162_; lean_object* v_unused_2163_; 
v_unused_2162_ = lean_ctor_get(v_toRingState_2142_, 2);
lean_dec(v_unused_2162_);
v_unused_2163_ = lean_ctor_get(v_toRingState_2142_, 1);
lean_dec(v_unused_2163_);
v___x_2145_ = v_toRingState_2142_;
v_isShared_2146_ = v_isSharedCheck_2161_;
goto v_resetjp_2144_;
}
else
{
lean_inc(v_vars_2143_);
lean_dec(v_toRingState_2142_);
v___x_2145_ = lean_box(0);
v_isShared_2146_ = v_isSharedCheck_2161_;
goto v_resetjp_2144_;
}
v_resetjp_2144_:
{
lean_object* v_size_2147_; uint8_t v___x_2148_; 
v_size_2147_ = lean_ctor_get(v_vars_2143_, 2);
v___x_2148_ = lean_nat_dec_le(v_size_2147_, v_powIdentityVarCount_2136_);
if (v___x_2148_ == 0)
{
lean_object* v___f_2149_; lean_object* v___x_2150_; lean_object* v___x_2152_; 
lean_del_object(v___x_2140_);
lean_inc_n(v_size_2147_, 2);
v___f_2149_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars___lam__0), 2, 1);
lean_closure_set(v___f_2149_, 0, v_size_2147_);
v___x_2150_ = lean_unsigned_to_nat(1u);
lean_inc(v_powIdentityVarCount_2136_);
if (v_isShared_2146_ == 0)
{
lean_ctor_set(v___x_2145_, 2, v___x_2150_);
lean_ctor_set(v___x_2145_, 1, v_size_2147_);
lean_ctor_set(v___x_2145_, 0, v_powIdentityVarCount_2136_);
v___x_2152_ = v___x_2145_;
goto v_reusejp_2151_;
}
else
{
lean_object* v_reuseFailAlloc_2156_; 
v_reuseFailAlloc_2156_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2156_, 0, v_powIdentityVarCount_2136_);
lean_ctor_set(v_reuseFailAlloc_2156_, 1, v_size_2147_);
lean_ctor_set(v_reuseFailAlloc_2156_, 2, v___x_2150_);
v___x_2152_ = v_reuseFailAlloc_2156_;
goto v_reusejp_2151_;
}
v_reusejp_2151_:
{
lean_object* v___x_2153_; lean_object* v___x_2154_; 
v___x_2153_ = lean_box(0);
v___x_2154_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg(v_a_2124_, v_snd_2133_, v_fst_2132_, v_fst_2131_, v_vars_2143_, v___x_2152_, v___x_2153_, v_powIdentityVarCount_2136_, v_a_2111_, v_a_2112_, v_a_2113_, v_a_2114_, v_a_2115_, v_a_2116_, v_a_2117_, v_a_2118_, v_a_2119_, v_a_2120_, v_a_2121_);
lean_dec_ref(v___x_2152_);
lean_dec_ref(v_vars_2143_);
if (lean_obj_tag(v___x_2154_) == 0)
{
lean_object* v___x_2155_; 
lean_dec_ref_known(v___x_2154_, 1);
v___x_2155_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRingState___redArg(v___f_2149_, v_a_2111_, v_a_2112_);
return v___x_2155_;
}
else
{
lean_dec_ref(v___f_2149_);
return v___x_2154_;
}
}
}
else
{
lean_object* v___x_2157_; lean_object* v___x_2159_; 
lean_del_object(v___x_2145_);
lean_dec_ref(v_vars_2143_);
lean_dec(v_powIdentityVarCount_2136_);
lean_dec(v_snd_2133_);
lean_dec(v_fst_2132_);
lean_dec(v_fst_2131_);
lean_dec(v_a_2124_);
v___x_2157_ = lean_box(0);
if (v_isShared_2141_ == 0)
{
lean_ctor_set(v___x_2140_, 0, v___x_2157_);
v___x_2159_ = v___x_2140_;
goto v_reusejp_2158_;
}
else
{
lean_object* v_reuseFailAlloc_2160_; 
v_reuseFailAlloc_2160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2160_, 0, v___x_2157_);
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
}
else
{
lean_object* v_a_2165_; lean_object* v___x_2167_; uint8_t v_isShared_2168_; uint8_t v_isSharedCheck_2172_; 
lean_dec(v_powIdentityVarCount_2136_);
lean_dec(v_snd_2133_);
lean_dec(v_fst_2132_);
lean_dec(v_fst_2131_);
lean_dec(v_a_2124_);
v_a_2165_ = lean_ctor_get(v___x_2137_, 0);
v_isSharedCheck_2172_ = !lean_is_exclusive(v___x_2137_);
if (v_isSharedCheck_2172_ == 0)
{
v___x_2167_ = v___x_2137_;
v_isShared_2168_ = v_isSharedCheck_2172_;
goto v_resetjp_2166_;
}
else
{
lean_inc(v_a_2165_);
lean_dec(v___x_2137_);
v___x_2167_ = lean_box(0);
v_isShared_2168_ = v_isSharedCheck_2172_;
goto v_resetjp_2166_;
}
v_resetjp_2166_:
{
lean_object* v___x_2170_; 
if (v_isShared_2168_ == 0)
{
v___x_2170_ = v___x_2167_;
goto v_reusejp_2169_;
}
else
{
lean_object* v_reuseFailAlloc_2171_; 
v_reuseFailAlloc_2171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2171_, 0, v_a_2165_);
v___x_2170_ = v_reuseFailAlloc_2171_;
goto v_reusejp_2169_;
}
v_reusejp_2169_:
{
return v___x_2170_;
}
}
}
}
else
{
lean_object* v_a_2173_; lean_object* v___x_2175_; uint8_t v_isShared_2176_; uint8_t v_isSharedCheck_2180_; 
lean_dec(v_snd_2133_);
lean_dec(v_fst_2132_);
lean_dec(v_fst_2131_);
lean_dec(v_a_2124_);
v_a_2173_ = lean_ctor_get(v___x_2134_, 0);
v_isSharedCheck_2180_ = !lean_is_exclusive(v___x_2134_);
if (v_isSharedCheck_2180_ == 0)
{
v___x_2175_ = v___x_2134_;
v_isShared_2176_ = v_isSharedCheck_2180_;
goto v_resetjp_2174_;
}
else
{
lean_inc(v_a_2173_);
lean_dec(v___x_2134_);
v___x_2175_ = lean_box(0);
v_isShared_2176_ = v_isSharedCheck_2180_;
goto v_resetjp_2174_;
}
v_resetjp_2174_:
{
lean_object* v___x_2178_; 
if (v_isShared_2176_ == 0)
{
v___x_2178_ = v___x_2175_;
goto v_reusejp_2177_;
}
else
{
lean_object* v_reuseFailAlloc_2179_; 
v_reuseFailAlloc_2179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2179_, 0, v_a_2173_);
v___x_2178_ = v_reuseFailAlloc_2179_;
goto v_reusejp_2177_;
}
v_reusejp_2177_:
{
return v___x_2178_;
}
}
}
}
else
{
lean_object* v___x_2181_; lean_object* v___x_2183_; 
lean_dec(v_a_2124_);
v___x_2181_ = lean_box(0);
if (v_isShared_2127_ == 0)
{
lean_ctor_set(v___x_2126_, 0, v___x_2181_);
v___x_2183_ = v___x_2126_;
goto v_reusejp_2182_;
}
else
{
lean_object* v_reuseFailAlloc_2184_; 
v_reuseFailAlloc_2184_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2184_, 0, v___x_2181_);
v___x_2183_ = v_reuseFailAlloc_2184_;
goto v_reusejp_2182_;
}
v_reusejp_2182_:
{
return v___x_2183_;
}
}
}
}
else
{
lean_object* v_a_2186_; lean_object* v___x_2188_; uint8_t v_isShared_2189_; uint8_t v_isSharedCheck_2193_; 
v_a_2186_ = lean_ctor_get(v___x_2123_, 0);
v_isSharedCheck_2193_ = !lean_is_exclusive(v___x_2123_);
if (v_isSharedCheck_2193_ == 0)
{
v___x_2188_ = v___x_2123_;
v_isShared_2189_ = v_isSharedCheck_2193_;
goto v_resetjp_2187_;
}
else
{
lean_inc(v_a_2186_);
lean_dec(v___x_2123_);
v___x_2188_ = lean_box(0);
v_isShared_2189_ = v_isSharedCheck_2193_;
goto v_resetjp_2187_;
}
v_resetjp_2187_:
{
lean_object* v___x_2191_; 
if (v_isShared_2189_ == 0)
{
v___x_2191_ = v___x_2188_;
goto v_reusejp_2190_;
}
else
{
lean_object* v_reuseFailAlloc_2192_; 
v_reuseFailAlloc_2192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2192_, 0, v_a_2186_);
v___x_2191_ = v_reuseFailAlloc_2192_;
goto v_reusejp_2190_;
}
v_reusejp_2190_:
{
return v___x_2191_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars___boxed(lean_object* v_a_2194_, lean_object* v_a_2195_, lean_object* v_a_2196_, lean_object* v_a_2197_, lean_object* v_a_2198_, lean_object* v_a_2199_, lean_object* v_a_2200_, lean_object* v_a_2201_, lean_object* v_a_2202_, lean_object* v_a_2203_, lean_object* v_a_2204_, lean_object* v_a_2205_){
_start:
{
lean_object* v_res_2206_; 
v_res_2206_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars(v_a_2194_, v_a_2195_, v_a_2196_, v_a_2197_, v_a_2198_, v_a_2199_, v_a_2200_, v_a_2201_, v_a_2202_, v_a_2203_, v_a_2204_);
lean_dec(v_a_2204_);
lean_dec_ref(v_a_2203_);
lean_dec(v_a_2202_);
lean_dec_ref(v_a_2201_);
lean_dec(v_a_2200_);
lean_dec_ref(v_a_2199_);
lean_dec(v_a_2198_);
lean_dec_ref(v_a_2197_);
lean_dec(v_a_2196_);
lean_dec(v_a_2195_);
lean_dec_ref(v_a_2194_);
return v_res_2206_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0(lean_object* v_cls_2207_, lean_object* v_msg_2208_, lean_object* v___y_2209_, lean_object* v___y_2210_, lean_object* v___y_2211_, lean_object* v___y_2212_, lean_object* v___y_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_, lean_object* v___y_2219_){
_start:
{
lean_object* v___x_2221_; 
v___x_2221_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg(v_cls_2207_, v_msg_2208_, v___y_2216_, v___y_2217_, v___y_2218_, v___y_2219_);
return v___x_2221_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___boxed(lean_object* v_cls_2222_, lean_object* v_msg_2223_, lean_object* v___y_2224_, lean_object* v___y_2225_, lean_object* v___y_2226_, lean_object* v___y_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_){
_start:
{
lean_object* v_res_2236_; 
v_res_2236_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0(v_cls_2222_, v_msg_2223_, v___y_2224_, v___y_2225_, v___y_2226_, v___y_2227_, v___y_2228_, v___y_2229_, v___y_2230_, v___y_2231_, v___y_2232_, v___y_2233_, v___y_2234_);
lean_dec(v___y_2234_);
lean_dec_ref(v___y_2233_);
lean_dec(v___y_2232_);
lean_dec_ref(v___y_2231_);
lean_dec(v___y_2230_);
lean_dec_ref(v___y_2229_);
lean_dec(v___y_2228_);
lean_dec_ref(v___y_2227_);
lean_dec(v___y_2226_);
lean_dec(v___y_2225_);
lean_dec_ref(v___y_2224_);
return v_res_2236_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1(lean_object* v_a_2237_, lean_object* v_snd_2238_, lean_object* v_fst_2239_, lean_object* v_fst_2240_, lean_object* v___x_2241_, lean_object* v_range_2242_, lean_object* v_b_2243_, lean_object* v_i_2244_, lean_object* v_hs_2245_, lean_object* v_hl_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_, lean_object* v___y_2257_){
_start:
{
lean_object* v___x_2259_; 
v___x_2259_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg(v_a_2237_, v_snd_2238_, v_fst_2239_, v_fst_2240_, v___x_2241_, v_range_2242_, v_b_2243_, v_i_2244_, v___y_2247_, v___y_2248_, v___y_2249_, v___y_2250_, v___y_2251_, v___y_2252_, v___y_2253_, v___y_2254_, v___y_2255_, v___y_2256_, v___y_2257_);
return v___x_2259_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___boxed(lean_object** _args){
lean_object* v_a_2260_ = _args[0];
lean_object* v_snd_2261_ = _args[1];
lean_object* v_fst_2262_ = _args[2];
lean_object* v_fst_2263_ = _args[3];
lean_object* v___x_2264_ = _args[4];
lean_object* v_range_2265_ = _args[5];
lean_object* v_b_2266_ = _args[6];
lean_object* v_i_2267_ = _args[7];
lean_object* v_hs_2268_ = _args[8];
lean_object* v_hl_2269_ = _args[9];
lean_object* v___y_2270_ = _args[10];
lean_object* v___y_2271_ = _args[11];
lean_object* v___y_2272_ = _args[12];
lean_object* v___y_2273_ = _args[13];
lean_object* v___y_2274_ = _args[14];
lean_object* v___y_2275_ = _args[15];
lean_object* v___y_2276_ = _args[16];
lean_object* v___y_2277_ = _args[17];
lean_object* v___y_2278_ = _args[18];
lean_object* v___y_2279_ = _args[19];
lean_object* v___y_2280_ = _args[20];
lean_object* v___y_2281_ = _args[21];
_start:
{
lean_object* v_res_2282_; 
v_res_2282_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1(v_a_2260_, v_snd_2261_, v_fst_2262_, v_fst_2263_, v___x_2264_, v_range_2265_, v_b_2266_, v_i_2267_, v_hs_2268_, v_hl_2269_, v___y_2270_, v___y_2271_, v___y_2272_, v___y_2273_, v___y_2274_, v___y_2275_, v___y_2276_, v___y_2277_, v___y_2278_, v___y_2279_, v___y_2280_);
lean_dec(v___y_2280_);
lean_dec_ref(v___y_2279_);
lean_dec(v___y_2278_);
lean_dec_ref(v___y_2277_);
lean_dec(v___y_2276_);
lean_dec_ref(v___y_2275_);
lean_dec(v___y_2274_);
lean_dec_ref(v___y_2273_);
lean_dec(v___y_2272_);
lean_dec(v___y_2271_);
lean_dec_ref(v___y_2270_);
lean_dec_ref(v_range_2265_);
lean_dec_ref(v___x_2264_);
return v_res_2282_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeInv(lean_object* v_e_2283_, lean_object* v_a_2284_, lean_object* v_a_2285_, lean_object* v_a_2286_, lean_object* v_a_2287_, lean_object* v_a_2288_, lean_object* v_a_2289_, lean_object* v_a_2290_, lean_object* v_a_2291_, lean_object* v_a_2292_, lean_object* v_a_2293_){
_start:
{
lean_object* v___x_2299_; 
lean_inc_ref(v_e_2283_);
v___x_2299_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_2283_, v_a_2291_);
if (lean_obj_tag(v___x_2299_) == 0)
{
lean_object* v_a_2300_; lean_object* v___x_2301_; uint8_t v___x_2302_; 
v_a_2300_ = lean_ctor_get(v___x_2299_, 0);
lean_inc(v_a_2300_);
lean_dec_ref_known(v___x_2299_, 1);
v___x_2301_ = l_Lean_Expr_cleanupAnnotations(v_a_2300_);
lean_dec(v_a_2300_);
v___x_2302_ = l_Lean_Expr_isApp(v___x_2301_);
if (v___x_2302_ == 0)
{
lean_dec_ref(v___x_2301_);
lean_dec_ref(v_e_2283_);
goto v___jp_2295_;
}
else
{
lean_object* v___x_2303_; uint8_t v___x_2304_; 
v___x_2303_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2301_);
v___x_2304_ = l_Lean_Expr_isApp(v___x_2303_);
if (v___x_2304_ == 0)
{
lean_dec_ref(v___x_2303_);
lean_dec_ref(v___x_2301_);
lean_dec_ref(v_e_2283_);
goto v___jp_2295_;
}
else
{
lean_object* v___x_2305_; uint8_t v___x_2306_; 
v___x_2305_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2303_);
v___x_2306_ = l_Lean_Expr_isApp(v___x_2305_);
if (v___x_2306_ == 0)
{
lean_dec_ref(v___x_2305_);
lean_dec_ref(v___x_2303_);
lean_dec_ref(v___x_2301_);
lean_dec_ref(v_e_2283_);
goto v___jp_2295_;
}
else
{
lean_object* v___x_2307_; lean_object* v___x_2308_; uint8_t v___x_2309_; 
v___x_2307_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2305_);
v___x_2308_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___closed__6));
v___x_2309_ = l_Lean_Expr_isConstOf(v___x_2307_, v___x_2308_);
lean_dec_ref(v___x_2307_);
if (v___x_2309_ == 0)
{
lean_dec_ref(v___x_2305_);
lean_dec_ref(v___x_2303_);
lean_dec_ref(v___x_2301_);
lean_dec_ref(v_e_2283_);
goto v___jp_2295_;
}
else
{
lean_object* v_arg_2310_; lean_object* v_arg_2311_; lean_object* v_arg_2312_; lean_object* v___x_2313_; 
v_arg_2310_ = lean_ctor_get(v___x_2301_, 1);
lean_inc_ref(v_arg_2310_);
lean_dec_ref(v___x_2301_);
v_arg_2311_ = lean_ctor_get(v___x_2303_, 1);
lean_inc_ref(v_arg_2311_);
lean_dec_ref(v___x_2303_);
v_arg_2312_ = lean_ctor_get(v___x_2305_, 1);
lean_inc_ref(v_arg_2312_);
lean_dec_ref(v___x_2305_);
v___x_2313_ = l_Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f___redArg(v_arg_2312_, v_a_2288_, v_a_2289_, v_a_2290_, v_a_2291_, v_a_2292_, v_a_2293_);
if (lean_obj_tag(v___x_2313_) == 0)
{
lean_object* v_a_2314_; lean_object* v___x_2316_; uint8_t v_isShared_2317_; uint8_t v_isSharedCheck_2343_; 
v_a_2314_ = lean_ctor_get(v___x_2313_, 0);
v_isSharedCheck_2343_ = !lean_is_exclusive(v___x_2313_);
if (v_isSharedCheck_2343_ == 0)
{
v___x_2316_ = v___x_2313_;
v_isShared_2317_ = v_isSharedCheck_2343_;
goto v_resetjp_2315_;
}
else
{
lean_inc(v_a_2314_);
lean_dec(v___x_2313_);
v___x_2316_ = lean_box(0);
v_isShared_2317_ = v_isSharedCheck_2343_;
goto v_resetjp_2315_;
}
v_resetjp_2315_:
{
if (lean_obj_tag(v_a_2314_) == 1)
{
lean_object* v_val_2318_; uint8_t v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; 
lean_del_object(v___x_2316_);
v_val_2318_ = lean_ctor_get(v_a_2314_, 0);
lean_inc(v_val_2318_);
lean_dec_ref_known(v_a_2314_, 1);
v___x_2319_ = 0;
v___x_2320_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2320_, 0, v_val_2318_);
lean_ctor_set_uint8(v___x_2320_, sizeof(void*)*1, v___x_2319_);
v___x_2321_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv(v_e_2283_, v_arg_2311_, v_arg_2310_, v___x_2320_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_, v_a_2288_, v_a_2289_, v_a_2290_, v_a_2291_, v_a_2292_, v_a_2293_);
lean_dec_ref_known(v___x_2320_, 1);
lean_dec_ref(v_arg_2311_);
if (lean_obj_tag(v___x_2321_) == 0)
{
lean_object* v___x_2323_; uint8_t v_isShared_2324_; uint8_t v_isSharedCheck_2329_; 
v_isSharedCheck_2329_ = !lean_is_exclusive(v___x_2321_);
if (v_isSharedCheck_2329_ == 0)
{
lean_object* v_unused_2330_; 
v_unused_2330_ = lean_ctor_get(v___x_2321_, 0);
lean_dec(v_unused_2330_);
v___x_2323_ = v___x_2321_;
v_isShared_2324_ = v_isSharedCheck_2329_;
goto v_resetjp_2322_;
}
else
{
lean_dec(v___x_2321_);
v___x_2323_ = lean_box(0);
v_isShared_2324_ = v_isSharedCheck_2329_;
goto v_resetjp_2322_;
}
v_resetjp_2322_:
{
lean_object* v___x_2325_; lean_object* v___x_2327_; 
v___x_2325_ = lean_box(v___x_2309_);
if (v_isShared_2324_ == 0)
{
lean_ctor_set(v___x_2323_, 0, v___x_2325_);
v___x_2327_ = v___x_2323_;
goto v_reusejp_2326_;
}
else
{
lean_object* v_reuseFailAlloc_2328_; 
v_reuseFailAlloc_2328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2328_, 0, v___x_2325_);
v___x_2327_ = v_reuseFailAlloc_2328_;
goto v_reusejp_2326_;
}
v_reusejp_2326_:
{
return v___x_2327_;
}
}
}
else
{
lean_object* v_a_2331_; lean_object* v___x_2333_; uint8_t v_isShared_2334_; uint8_t v_isSharedCheck_2338_; 
v_a_2331_ = lean_ctor_get(v___x_2321_, 0);
v_isSharedCheck_2338_ = !lean_is_exclusive(v___x_2321_);
if (v_isSharedCheck_2338_ == 0)
{
v___x_2333_ = v___x_2321_;
v_isShared_2334_ = v_isSharedCheck_2338_;
goto v_resetjp_2332_;
}
else
{
lean_inc(v_a_2331_);
lean_dec(v___x_2321_);
v___x_2333_ = lean_box(0);
v_isShared_2334_ = v_isSharedCheck_2338_;
goto v_resetjp_2332_;
}
v_resetjp_2332_:
{
lean_object* v___x_2336_; 
if (v_isShared_2334_ == 0)
{
v___x_2336_ = v___x_2333_;
goto v_reusejp_2335_;
}
else
{
lean_object* v_reuseFailAlloc_2337_; 
v_reuseFailAlloc_2337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2337_, 0, v_a_2331_);
v___x_2336_ = v_reuseFailAlloc_2337_;
goto v_reusejp_2335_;
}
v_reusejp_2335_:
{
return v___x_2336_;
}
}
}
}
else
{
lean_object* v___x_2339_; lean_object* v___x_2341_; 
lean_dec(v_a_2314_);
lean_dec_ref(v_arg_2311_);
lean_dec_ref(v_arg_2310_);
lean_dec_ref(v_e_2283_);
v___x_2339_ = lean_box(v___x_2309_);
if (v_isShared_2317_ == 0)
{
lean_ctor_set(v___x_2316_, 0, v___x_2339_);
v___x_2341_ = v___x_2316_;
goto v_reusejp_2340_;
}
else
{
lean_object* v_reuseFailAlloc_2342_; 
v_reuseFailAlloc_2342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2342_, 0, v___x_2339_);
v___x_2341_ = v_reuseFailAlloc_2342_;
goto v_reusejp_2340_;
}
v_reusejp_2340_:
{
return v___x_2341_;
}
}
}
}
else
{
lean_object* v_a_2344_; lean_object* v___x_2346_; uint8_t v_isShared_2347_; uint8_t v_isSharedCheck_2351_; 
lean_dec_ref(v_arg_2311_);
lean_dec_ref(v_arg_2310_);
lean_dec_ref(v_e_2283_);
v_a_2344_ = lean_ctor_get(v___x_2313_, 0);
v_isSharedCheck_2351_ = !lean_is_exclusive(v___x_2313_);
if (v_isSharedCheck_2351_ == 0)
{
v___x_2346_ = v___x_2313_;
v_isShared_2347_ = v_isSharedCheck_2351_;
goto v_resetjp_2345_;
}
else
{
lean_inc(v_a_2344_);
lean_dec(v___x_2313_);
v___x_2346_ = lean_box(0);
v_isShared_2347_ = v_isSharedCheck_2351_;
goto v_resetjp_2345_;
}
v_resetjp_2345_:
{
lean_object* v___x_2349_; 
if (v_isShared_2347_ == 0)
{
v___x_2349_ = v___x_2346_;
goto v_reusejp_2348_;
}
else
{
lean_object* v_reuseFailAlloc_2350_; 
v_reuseFailAlloc_2350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2350_, 0, v_a_2344_);
v___x_2349_ = v_reuseFailAlloc_2350_;
goto v_reusejp_2348_;
}
v_reusejp_2348_:
{
return v___x_2349_;
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
lean_object* v_a_2352_; lean_object* v___x_2354_; uint8_t v_isShared_2355_; uint8_t v_isSharedCheck_2359_; 
lean_dec_ref(v_e_2283_);
v_a_2352_ = lean_ctor_get(v___x_2299_, 0);
v_isSharedCheck_2359_ = !lean_is_exclusive(v___x_2299_);
if (v_isSharedCheck_2359_ == 0)
{
v___x_2354_ = v___x_2299_;
v_isShared_2355_ = v_isSharedCheck_2359_;
goto v_resetjp_2353_;
}
else
{
lean_inc(v_a_2352_);
lean_dec(v___x_2299_);
v___x_2354_ = lean_box(0);
v_isShared_2355_ = v_isSharedCheck_2359_;
goto v_resetjp_2353_;
}
v_resetjp_2353_:
{
lean_object* v___x_2357_; 
if (v_isShared_2355_ == 0)
{
v___x_2357_ = v___x_2354_;
goto v_reusejp_2356_;
}
else
{
lean_object* v_reuseFailAlloc_2358_; 
v_reuseFailAlloc_2358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2358_, 0, v_a_2352_);
v___x_2357_ = v_reuseFailAlloc_2358_;
goto v_reusejp_2356_;
}
v_reusejp_2356_:
{
return v___x_2357_;
}
}
}
v___jp_2295_:
{
uint8_t v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; 
v___x_2296_ = 0;
v___x_2297_ = lean_box(v___x_2296_);
v___x_2298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2298_, 0, v___x_2297_);
return v___x_2298_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeInv___boxed(lean_object* v_e_2360_, lean_object* v_a_2361_, lean_object* v_a_2362_, lean_object* v_a_2363_, lean_object* v_a_2364_, lean_object* v_a_2365_, lean_object* v_a_2366_, lean_object* v_a_2367_, lean_object* v_a_2368_, lean_object* v_a_2369_, lean_object* v_a_2370_, lean_object* v_a_2371_){
_start:
{
lean_object* v_res_2372_; 
v_res_2372_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeInv(v_e_2360_, v_a_2361_, v_a_2362_, v_a_2363_, v_a_2364_, v_a_2365_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_);
lean_dec(v_a_2370_);
lean_dec_ref(v_a_2369_);
lean_dec(v_a_2368_);
lean_dec_ref(v_a_2367_);
lean_dec(v_a_2366_);
lean_dec_ref(v_a_2365_);
lean_dec(v_a_2364_);
lean_dec_ref(v_a_2363_);
lean_dec(v_a_2362_);
lean_dec(v_a_2361_);
return v_res_2372_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0_spec__1_spec__5___redArg(lean_object* v_x_2373_, lean_object* v_x_2374_, lean_object* v_x_2375_, lean_object* v_x_2376_){
_start:
{
lean_object* v_ks_2377_; lean_object* v_vs_2378_; lean_object* v___x_2380_; uint8_t v_isShared_2381_; uint8_t v_isSharedCheck_2404_; 
v_ks_2377_ = lean_ctor_get(v_x_2373_, 0);
v_vs_2378_ = lean_ctor_get(v_x_2373_, 1);
v_isSharedCheck_2404_ = !lean_is_exclusive(v_x_2373_);
if (v_isSharedCheck_2404_ == 0)
{
v___x_2380_ = v_x_2373_;
v_isShared_2381_ = v_isSharedCheck_2404_;
goto v_resetjp_2379_;
}
else
{
lean_inc(v_vs_2378_);
lean_inc(v_ks_2377_);
lean_dec(v_x_2373_);
v___x_2380_ = lean_box(0);
v_isShared_2381_ = v_isSharedCheck_2404_;
goto v_resetjp_2379_;
}
v_resetjp_2379_:
{
lean_object* v___x_2382_; uint8_t v___x_2383_; 
v___x_2382_ = lean_array_get_size(v_ks_2377_);
v___x_2383_ = lean_nat_dec_lt(v_x_2374_, v___x_2382_);
if (v___x_2383_ == 0)
{
lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2387_; 
lean_dec(v_x_2374_);
v___x_2384_ = lean_array_push(v_ks_2377_, v_x_2375_);
v___x_2385_ = lean_array_push(v_vs_2378_, v_x_2376_);
if (v_isShared_2381_ == 0)
{
lean_ctor_set(v___x_2380_, 1, v___x_2385_);
lean_ctor_set(v___x_2380_, 0, v___x_2384_);
v___x_2387_ = v___x_2380_;
goto v_reusejp_2386_;
}
else
{
lean_object* v_reuseFailAlloc_2388_; 
v_reuseFailAlloc_2388_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2388_, 0, v___x_2384_);
lean_ctor_set(v_reuseFailAlloc_2388_, 1, v___x_2385_);
v___x_2387_ = v_reuseFailAlloc_2388_;
goto v_reusejp_2386_;
}
v_reusejp_2386_:
{
return v___x_2387_;
}
}
else
{
lean_object* v_k_x27_2389_; size_t v___x_2390_; size_t v___x_2391_; uint8_t v___x_2392_; 
v_k_x27_2389_ = lean_array_fget_borrowed(v_ks_2377_, v_x_2374_);
v___x_2390_ = lean_ptr_addr(v_x_2375_);
v___x_2391_ = lean_ptr_addr(v_k_x27_2389_);
v___x_2392_ = lean_usize_dec_eq(v___x_2390_, v___x_2391_);
if (v___x_2392_ == 0)
{
lean_object* v___x_2394_; 
if (v_isShared_2381_ == 0)
{
v___x_2394_ = v___x_2380_;
goto v_reusejp_2393_;
}
else
{
lean_object* v_reuseFailAlloc_2398_; 
v_reuseFailAlloc_2398_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2398_, 0, v_ks_2377_);
lean_ctor_set(v_reuseFailAlloc_2398_, 1, v_vs_2378_);
v___x_2394_ = v_reuseFailAlloc_2398_;
goto v_reusejp_2393_;
}
v_reusejp_2393_:
{
lean_object* v___x_2395_; lean_object* v___x_2396_; 
v___x_2395_ = lean_unsigned_to_nat(1u);
v___x_2396_ = lean_nat_add(v_x_2374_, v___x_2395_);
lean_dec(v_x_2374_);
v_x_2373_ = v___x_2394_;
v_x_2374_ = v___x_2396_;
goto _start;
}
}
else
{
lean_object* v___x_2399_; lean_object* v___x_2400_; lean_object* v___x_2402_; 
v___x_2399_ = lean_array_fset(v_ks_2377_, v_x_2374_, v_x_2375_);
v___x_2400_ = lean_array_fset(v_vs_2378_, v_x_2374_, v_x_2376_);
lean_dec(v_x_2374_);
if (v_isShared_2381_ == 0)
{
lean_ctor_set(v___x_2380_, 1, v___x_2400_);
lean_ctor_set(v___x_2380_, 0, v___x_2399_);
v___x_2402_ = v___x_2380_;
goto v_reusejp_2401_;
}
else
{
lean_object* v_reuseFailAlloc_2403_; 
v_reuseFailAlloc_2403_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2403_, 0, v___x_2399_);
lean_ctor_set(v_reuseFailAlloc_2403_, 1, v___x_2400_);
v___x_2402_ = v_reuseFailAlloc_2403_;
goto v_reusejp_2401_;
}
v_reusejp_2401_:
{
return v___x_2402_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0_spec__1___redArg(lean_object* v_n_2405_, lean_object* v_k_2406_, lean_object* v_v_2407_){
_start:
{
lean_object* v___x_2408_; lean_object* v___x_2409_; 
v___x_2408_ = lean_unsigned_to_nat(0u);
v___x_2409_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0_spec__1_spec__5___redArg(v_n_2405_, v___x_2408_, v_k_2406_, v_v_2407_);
return v___x_2409_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0___redArg(lean_object* v_x_2410_, size_t v_x_2411_, size_t v_x_2412_, lean_object* v_x_2413_, lean_object* v_x_2414_){
_start:
{
if (lean_obj_tag(v_x_2410_) == 0)
{
lean_object* v_es_2415_; size_t v___x_2416_; size_t v___x_2417_; lean_object* v_j_2418_; lean_object* v___x_2419_; uint8_t v___x_2420_; 
v_es_2415_ = lean_ctor_get(v_x_2410_, 0);
v___x_2416_ = ((size_t)31ULL);
v___x_2417_ = lean_usize_land(v_x_2411_, v___x_2416_);
v_j_2418_ = lean_usize_to_nat(v___x_2417_);
v___x_2419_ = lean_array_get_size(v_es_2415_);
v___x_2420_ = lean_nat_dec_lt(v_j_2418_, v___x_2419_);
if (v___x_2420_ == 0)
{
lean_dec(v_j_2418_);
lean_dec(v_x_2414_);
lean_dec_ref(v_x_2413_);
return v_x_2410_;
}
else
{
lean_object* v___x_2422_; uint8_t v_isShared_2423_; uint8_t v_isSharedCheck_2461_; 
lean_inc_ref(v_es_2415_);
v_isSharedCheck_2461_ = !lean_is_exclusive(v_x_2410_);
if (v_isSharedCheck_2461_ == 0)
{
lean_object* v_unused_2462_; 
v_unused_2462_ = lean_ctor_get(v_x_2410_, 0);
lean_dec(v_unused_2462_);
v___x_2422_ = v_x_2410_;
v_isShared_2423_ = v_isSharedCheck_2461_;
goto v_resetjp_2421_;
}
else
{
lean_dec(v_x_2410_);
v___x_2422_ = lean_box(0);
v_isShared_2423_ = v_isSharedCheck_2461_;
goto v_resetjp_2421_;
}
v_resetjp_2421_:
{
lean_object* v_v_2424_; lean_object* v___x_2425_; lean_object* v_xs_x27_2426_; lean_object* v___y_2428_; 
v_v_2424_ = lean_array_fget(v_es_2415_, v_j_2418_);
v___x_2425_ = lean_box(0);
v_xs_x27_2426_ = lean_array_fset(v_es_2415_, v_j_2418_, v___x_2425_);
switch(lean_obj_tag(v_v_2424_))
{
case 0:
{
lean_object* v_key_2433_; lean_object* v_val_2434_; lean_object* v___x_2436_; uint8_t v_isShared_2437_; uint8_t v_isSharedCheck_2446_; 
v_key_2433_ = lean_ctor_get(v_v_2424_, 0);
v_val_2434_ = lean_ctor_get(v_v_2424_, 1);
v_isSharedCheck_2446_ = !lean_is_exclusive(v_v_2424_);
if (v_isSharedCheck_2446_ == 0)
{
v___x_2436_ = v_v_2424_;
v_isShared_2437_ = v_isSharedCheck_2446_;
goto v_resetjp_2435_;
}
else
{
lean_inc(v_val_2434_);
lean_inc(v_key_2433_);
lean_dec(v_v_2424_);
v___x_2436_ = lean_box(0);
v_isShared_2437_ = v_isSharedCheck_2446_;
goto v_resetjp_2435_;
}
v_resetjp_2435_:
{
size_t v___x_2438_; size_t v___x_2439_; uint8_t v___x_2440_; 
v___x_2438_ = lean_ptr_addr(v_x_2413_);
v___x_2439_ = lean_ptr_addr(v_key_2433_);
v___x_2440_ = lean_usize_dec_eq(v___x_2438_, v___x_2439_);
if (v___x_2440_ == 0)
{
lean_object* v___x_2441_; lean_object* v___x_2442_; 
lean_del_object(v___x_2436_);
v___x_2441_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_2433_, v_val_2434_, v_x_2413_, v_x_2414_);
v___x_2442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2442_, 0, v___x_2441_);
v___y_2428_ = v___x_2442_;
goto v___jp_2427_;
}
else
{
lean_object* v___x_2444_; 
lean_dec(v_val_2434_);
lean_dec(v_key_2433_);
if (v_isShared_2437_ == 0)
{
lean_ctor_set(v___x_2436_, 1, v_x_2414_);
lean_ctor_set(v___x_2436_, 0, v_x_2413_);
v___x_2444_ = v___x_2436_;
goto v_reusejp_2443_;
}
else
{
lean_object* v_reuseFailAlloc_2445_; 
v_reuseFailAlloc_2445_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2445_, 0, v_x_2413_);
lean_ctor_set(v_reuseFailAlloc_2445_, 1, v_x_2414_);
v___x_2444_ = v_reuseFailAlloc_2445_;
goto v_reusejp_2443_;
}
v_reusejp_2443_:
{
v___y_2428_ = v___x_2444_;
goto v___jp_2427_;
}
}
}
}
case 1:
{
lean_object* v_node_2447_; lean_object* v___x_2449_; uint8_t v_isShared_2450_; uint8_t v_isSharedCheck_2459_; 
v_node_2447_ = lean_ctor_get(v_v_2424_, 0);
v_isSharedCheck_2459_ = !lean_is_exclusive(v_v_2424_);
if (v_isSharedCheck_2459_ == 0)
{
v___x_2449_ = v_v_2424_;
v_isShared_2450_ = v_isSharedCheck_2459_;
goto v_resetjp_2448_;
}
else
{
lean_inc(v_node_2447_);
lean_dec(v_v_2424_);
v___x_2449_ = lean_box(0);
v_isShared_2450_ = v_isSharedCheck_2459_;
goto v_resetjp_2448_;
}
v_resetjp_2448_:
{
size_t v___x_2451_; size_t v___x_2452_; size_t v___x_2453_; size_t v___x_2454_; lean_object* v___x_2455_; lean_object* v___x_2457_; 
v___x_2451_ = ((size_t)5ULL);
v___x_2452_ = lean_usize_shift_right(v_x_2411_, v___x_2451_);
v___x_2453_ = ((size_t)1ULL);
v___x_2454_ = lean_usize_add(v_x_2412_, v___x_2453_);
v___x_2455_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0___redArg(v_node_2447_, v___x_2452_, v___x_2454_, v_x_2413_, v_x_2414_);
if (v_isShared_2450_ == 0)
{
lean_ctor_set(v___x_2449_, 0, v___x_2455_);
v___x_2457_ = v___x_2449_;
goto v_reusejp_2456_;
}
else
{
lean_object* v_reuseFailAlloc_2458_; 
v_reuseFailAlloc_2458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2458_, 0, v___x_2455_);
v___x_2457_ = v_reuseFailAlloc_2458_;
goto v_reusejp_2456_;
}
v_reusejp_2456_:
{
v___y_2428_ = v___x_2457_;
goto v___jp_2427_;
}
}
}
default: 
{
lean_object* v___x_2460_; 
v___x_2460_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2460_, 0, v_x_2413_);
lean_ctor_set(v___x_2460_, 1, v_x_2414_);
v___y_2428_ = v___x_2460_;
goto v___jp_2427_;
}
}
v___jp_2427_:
{
lean_object* v___x_2429_; lean_object* v___x_2431_; 
v___x_2429_ = lean_array_fset(v_xs_x27_2426_, v_j_2418_, v___y_2428_);
lean_dec(v_j_2418_);
if (v_isShared_2423_ == 0)
{
lean_ctor_set(v___x_2422_, 0, v___x_2429_);
v___x_2431_ = v___x_2422_;
goto v_reusejp_2430_;
}
else
{
lean_object* v_reuseFailAlloc_2432_; 
v_reuseFailAlloc_2432_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2432_, 0, v___x_2429_);
v___x_2431_ = v_reuseFailAlloc_2432_;
goto v_reusejp_2430_;
}
v_reusejp_2430_:
{
return v___x_2431_;
}
}
}
}
}
else
{
lean_object* v_ks_2463_; lean_object* v_vs_2464_; lean_object* v___x_2466_; uint8_t v_isShared_2467_; uint8_t v_isSharedCheck_2482_; 
v_ks_2463_ = lean_ctor_get(v_x_2410_, 0);
v_vs_2464_ = lean_ctor_get(v_x_2410_, 1);
v_isSharedCheck_2482_ = !lean_is_exclusive(v_x_2410_);
if (v_isSharedCheck_2482_ == 0)
{
v___x_2466_ = v_x_2410_;
v_isShared_2467_ = v_isSharedCheck_2482_;
goto v_resetjp_2465_;
}
else
{
lean_inc(v_vs_2464_);
lean_inc(v_ks_2463_);
lean_dec(v_x_2410_);
v___x_2466_ = lean_box(0);
v_isShared_2467_ = v_isSharedCheck_2482_;
goto v_resetjp_2465_;
}
v_resetjp_2465_:
{
lean_object* v___x_2469_; 
if (v_isShared_2467_ == 0)
{
v___x_2469_ = v___x_2466_;
goto v_reusejp_2468_;
}
else
{
lean_object* v_reuseFailAlloc_2481_; 
v_reuseFailAlloc_2481_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2481_, 0, v_ks_2463_);
lean_ctor_set(v_reuseFailAlloc_2481_, 1, v_vs_2464_);
v___x_2469_ = v_reuseFailAlloc_2481_;
goto v_reusejp_2468_;
}
v_reusejp_2468_:
{
lean_object* v_newNode_2470_; size_t v___x_2471_; uint8_t v___x_2472_; 
v_newNode_2470_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0_spec__1___redArg(v___x_2469_, v_x_2413_, v_x_2414_);
v___x_2471_ = ((size_t)7ULL);
v___x_2472_ = lean_usize_dec_le(v___x_2471_, v_x_2412_);
if (v___x_2472_ == 0)
{
lean_object* v___x_2473_; lean_object* v___x_2474_; uint8_t v___x_2475_; 
v___x_2473_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2470_);
v___x_2474_ = lean_unsigned_to_nat(4u);
v___x_2475_ = lean_nat_dec_lt(v___x_2473_, v___x_2474_);
lean_dec(v___x_2473_);
if (v___x_2475_ == 0)
{
lean_object* v_ks_2476_; lean_object* v_vs_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; 
v_ks_2476_ = lean_ctor_get(v_newNode_2470_, 0);
lean_inc_ref(v_ks_2476_);
v_vs_2477_ = lean_ctor_get(v_newNode_2470_, 1);
lean_inc_ref(v_vs_2477_);
lean_dec_ref(v_newNode_2470_);
v___x_2478_ = lean_unsigned_to_nat(0u);
v___x_2479_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg___closed__0);
v___x_2480_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0_spec__2___redArg(v_x_2412_, v_ks_2476_, v_vs_2477_, v___x_2478_, v___x_2479_);
lean_dec_ref(v_vs_2477_);
lean_dec_ref(v_ks_2476_);
return v___x_2480_;
}
else
{
return v_newNode_2470_;
}
}
else
{
return v_newNode_2470_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0_spec__2___redArg(size_t v_depth_2483_, lean_object* v_keys_2484_, lean_object* v_vals_2485_, lean_object* v_i_2486_, lean_object* v_entries_2487_){
_start:
{
lean_object* v___x_2488_; uint8_t v___x_2489_; 
v___x_2488_ = lean_array_get_size(v_keys_2484_);
v___x_2489_ = lean_nat_dec_lt(v_i_2486_, v___x_2488_);
if (v___x_2489_ == 0)
{
lean_dec(v_i_2486_);
return v_entries_2487_;
}
else
{
lean_object* v_k_2490_; lean_object* v_v_2491_; size_t v___x_2492_; size_t v___x_2493_; size_t v___x_2494_; uint64_t v___x_2495_; size_t v_h_2496_; size_t v___x_2497_; lean_object* v___x_2498_; size_t v___x_2499_; size_t v___x_2500_; size_t v___x_2501_; size_t v_h_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; 
v_k_2490_ = lean_array_fget_borrowed(v_keys_2484_, v_i_2486_);
v_v_2491_ = lean_array_fget_borrowed(v_vals_2485_, v_i_2486_);
v___x_2492_ = lean_ptr_addr(v_k_2490_);
v___x_2493_ = ((size_t)3ULL);
v___x_2494_ = lean_usize_shift_right(v___x_2492_, v___x_2493_);
v___x_2495_ = lean_usize_to_uint64(v___x_2494_);
v_h_2496_ = lean_uint64_to_usize(v___x_2495_);
v___x_2497_ = ((size_t)5ULL);
v___x_2498_ = lean_unsigned_to_nat(1u);
v___x_2499_ = ((size_t)1ULL);
v___x_2500_ = lean_usize_sub(v_depth_2483_, v___x_2499_);
v___x_2501_ = lean_usize_mul(v___x_2497_, v___x_2500_);
v_h_2502_ = lean_usize_shift_right(v_h_2496_, v___x_2501_);
v___x_2503_ = lean_nat_add(v_i_2486_, v___x_2498_);
lean_dec(v_i_2486_);
lean_inc(v_v_2491_);
lean_inc(v_k_2490_);
v___x_2504_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0___redArg(v_entries_2487_, v_h_2502_, v_depth_2483_, v_k_2490_, v_v_2491_);
v_i_2486_ = v___x_2503_;
v_entries_2487_ = v___x_2504_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_2506_, lean_object* v_keys_2507_, lean_object* v_vals_2508_, lean_object* v_i_2509_, lean_object* v_entries_2510_){
_start:
{
size_t v_depth_boxed_2511_; lean_object* v_res_2512_; 
v_depth_boxed_2511_ = lean_unbox_usize(v_depth_2506_);
lean_dec(v_depth_2506_);
v_res_2512_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0_spec__2___redArg(v_depth_boxed_2511_, v_keys_2507_, v_vals_2508_, v_i_2509_, v_entries_2510_);
lean_dec_ref(v_vals_2508_);
lean_dec_ref(v_keys_2507_);
return v_res_2512_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0___redArg___boxed(lean_object* v_x_2513_, lean_object* v_x_2514_, lean_object* v_x_2515_, lean_object* v_x_2516_, lean_object* v_x_2517_){
_start:
{
size_t v_x_146628__boxed_2518_; size_t v_x_146629__boxed_2519_; lean_object* v_res_2520_; 
v_x_146628__boxed_2518_ = lean_unbox_usize(v_x_2514_);
lean_dec(v_x_2514_);
v_x_146629__boxed_2519_ = lean_unbox_usize(v_x_2515_);
lean_dec(v_x_2515_);
v_res_2520_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0___redArg(v_x_2513_, v_x_146628__boxed_2518_, v_x_146629__boxed_2519_, v_x_2516_, v_x_2517_);
return v_res_2520_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0___redArg(lean_object* v_x_2521_, lean_object* v_x_2522_, lean_object* v_x_2523_){
_start:
{
size_t v___x_2524_; size_t v___x_2525_; size_t v___x_2526_; uint64_t v___x_2527_; size_t v___x_2528_; size_t v___x_2529_; lean_object* v___x_2530_; 
v___x_2524_ = lean_ptr_addr(v_x_2522_);
v___x_2525_ = ((size_t)3ULL);
v___x_2526_ = lean_usize_shift_right(v___x_2524_, v___x_2525_);
v___x_2527_ = lean_usize_to_uint64(v___x_2526_);
v___x_2528_ = lean_uint64_to_usize(v___x_2527_);
v___x_2529_ = ((size_t)1ULL);
v___x_2530_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0___redArg(v_x_2521_, v___x_2528_, v___x_2529_, v_x_2522_, v_x_2523_);
return v___x_2530_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_internalize___lam__0(lean_object* v_e_2531_, lean_object* v_val_2532_, lean_object* v_s_2533_){
_start:
{
lean_object* v_toRingState_2534_; lean_object* v_denoteEntries_2535_; lean_object* v_nextId_2536_; lean_object* v_steps_2537_; lean_object* v_queue_2538_; lean_object* v_basis_2539_; lean_object* v_diseqs_2540_; uint8_t v_recheck_2541_; lean_object* v_invSet_2542_; lean_object* v_powIdentityVarCount_2543_; lean_object* v_numEq0_x3f_2544_; uint8_t v_numEq0Updated_2545_; lean_object* v___x_2547_; uint8_t v_isShared_2548_; uint8_t v_isSharedCheck_2565_; 
v_toRingState_2534_ = lean_ctor_get(v_s_2533_, 0);
v_denoteEntries_2535_ = lean_ctor_get(v_s_2533_, 1);
v_nextId_2536_ = lean_ctor_get(v_s_2533_, 2);
v_steps_2537_ = lean_ctor_get(v_s_2533_, 3);
v_queue_2538_ = lean_ctor_get(v_s_2533_, 4);
v_basis_2539_ = lean_ctor_get(v_s_2533_, 5);
v_diseqs_2540_ = lean_ctor_get(v_s_2533_, 6);
v_recheck_2541_ = lean_ctor_get_uint8(v_s_2533_, sizeof(void*)*10);
v_invSet_2542_ = lean_ctor_get(v_s_2533_, 7);
v_powIdentityVarCount_2543_ = lean_ctor_get(v_s_2533_, 8);
v_numEq0_x3f_2544_ = lean_ctor_get(v_s_2533_, 9);
v_numEq0Updated_2545_ = lean_ctor_get_uint8(v_s_2533_, sizeof(void*)*10 + 1);
v_isSharedCheck_2565_ = !lean_is_exclusive(v_s_2533_);
if (v_isSharedCheck_2565_ == 0)
{
v___x_2547_ = v_s_2533_;
v_isShared_2548_ = v_isSharedCheck_2565_;
goto v_resetjp_2546_;
}
else
{
lean_inc(v_numEq0_x3f_2544_);
lean_inc(v_powIdentityVarCount_2543_);
lean_inc(v_invSet_2542_);
lean_inc(v_diseqs_2540_);
lean_inc(v_basis_2539_);
lean_inc(v_queue_2538_);
lean_inc(v_steps_2537_);
lean_inc(v_nextId_2536_);
lean_inc(v_denoteEntries_2535_);
lean_inc(v_toRingState_2534_);
lean_dec(v_s_2533_);
v___x_2547_ = lean_box(0);
v_isShared_2548_ = v_isSharedCheck_2565_;
goto v_resetjp_2546_;
}
v_resetjp_2546_:
{
lean_object* v_vars_2549_; lean_object* v_varMap_2550_; lean_object* v_denote_2551_; lean_object* v___x_2553_; uint8_t v_isShared_2554_; uint8_t v_isSharedCheck_2564_; 
v_vars_2549_ = lean_ctor_get(v_toRingState_2534_, 0);
v_varMap_2550_ = lean_ctor_get(v_toRingState_2534_, 1);
v_denote_2551_ = lean_ctor_get(v_toRingState_2534_, 2);
v_isSharedCheck_2564_ = !lean_is_exclusive(v_toRingState_2534_);
if (v_isSharedCheck_2564_ == 0)
{
v___x_2553_ = v_toRingState_2534_;
v_isShared_2554_ = v_isSharedCheck_2564_;
goto v_resetjp_2552_;
}
else
{
lean_inc(v_denote_2551_);
lean_inc(v_varMap_2550_);
lean_inc(v_vars_2549_);
lean_dec(v_toRingState_2534_);
v___x_2553_ = lean_box(0);
v_isShared_2554_ = v_isSharedCheck_2564_;
goto v_resetjp_2552_;
}
v_resetjp_2552_:
{
lean_object* v___x_2555_; lean_object* v___x_2557_; 
lean_inc_ref(v_val_2532_);
lean_inc_ref(v_e_2531_);
v___x_2555_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0___redArg(v_denote_2551_, v_e_2531_, v_val_2532_);
if (v_isShared_2554_ == 0)
{
lean_ctor_set(v___x_2553_, 2, v___x_2555_);
v___x_2557_ = v___x_2553_;
goto v_reusejp_2556_;
}
else
{
lean_object* v_reuseFailAlloc_2563_; 
v_reuseFailAlloc_2563_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2563_, 0, v_vars_2549_);
lean_ctor_set(v_reuseFailAlloc_2563_, 1, v_varMap_2550_);
lean_ctor_set(v_reuseFailAlloc_2563_, 2, v___x_2555_);
v___x_2557_ = v_reuseFailAlloc_2563_;
goto v_reusejp_2556_;
}
v_reusejp_2556_:
{
lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2561_; 
v___x_2558_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2558_, 0, v_e_2531_);
lean_ctor_set(v___x_2558_, 1, v_val_2532_);
v___x_2559_ = l_Lean_PersistentArray_push___redArg(v_denoteEntries_2535_, v___x_2558_);
if (v_isShared_2548_ == 0)
{
lean_ctor_set(v___x_2547_, 1, v___x_2559_);
lean_ctor_set(v___x_2547_, 0, v___x_2557_);
v___x_2561_ = v___x_2547_;
goto v_reusejp_2560_;
}
else
{
lean_object* v_reuseFailAlloc_2562_; 
v_reuseFailAlloc_2562_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v_reuseFailAlloc_2562_, 0, v___x_2557_);
lean_ctor_set(v_reuseFailAlloc_2562_, 1, v___x_2559_);
lean_ctor_set(v_reuseFailAlloc_2562_, 2, v_nextId_2536_);
lean_ctor_set(v_reuseFailAlloc_2562_, 3, v_steps_2537_);
lean_ctor_set(v_reuseFailAlloc_2562_, 4, v_queue_2538_);
lean_ctor_set(v_reuseFailAlloc_2562_, 5, v_basis_2539_);
lean_ctor_set(v_reuseFailAlloc_2562_, 6, v_diseqs_2540_);
lean_ctor_set(v_reuseFailAlloc_2562_, 7, v_invSet_2542_);
lean_ctor_set(v_reuseFailAlloc_2562_, 8, v_powIdentityVarCount_2543_);
lean_ctor_set(v_reuseFailAlloc_2562_, 9, v_numEq0_x3f_2544_);
lean_ctor_set_uint8(v_reuseFailAlloc_2562_, sizeof(void*)*10, v_recheck_2541_);
lean_ctor_set_uint8(v_reuseFailAlloc_2562_, sizeof(void*)*10 + 1, v_numEq0Updated_2545_);
v___x_2561_ = v_reuseFailAlloc_2562_;
goto v_reusejp_2560_;
}
v_reusejp_2560_:
{
return v___x_2561_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_internalize___lam__1(lean_object* v_e_2566_, lean_object* v_val_2567_, lean_object* v_s_2568_){
_start:
{
lean_object* v_denote_2569_; lean_object* v_vars_2570_; lean_object* v_varMap_2571_; lean_object* v___x_2573_; uint8_t v_isShared_2574_; uint8_t v_isSharedCheck_2579_; 
v_denote_2569_ = lean_ctor_get(v_s_2568_, 0);
v_vars_2570_ = lean_ctor_get(v_s_2568_, 1);
v_varMap_2571_ = lean_ctor_get(v_s_2568_, 2);
v_isSharedCheck_2579_ = !lean_is_exclusive(v_s_2568_);
if (v_isSharedCheck_2579_ == 0)
{
v___x_2573_ = v_s_2568_;
v_isShared_2574_ = v_isSharedCheck_2579_;
goto v_resetjp_2572_;
}
else
{
lean_inc(v_varMap_2571_);
lean_inc(v_vars_2570_);
lean_inc(v_denote_2569_);
lean_dec(v_s_2568_);
v___x_2573_ = lean_box(0);
v_isShared_2574_ = v_isSharedCheck_2579_;
goto v_resetjp_2572_;
}
v_resetjp_2572_:
{
lean_object* v___x_2575_; lean_object* v___x_2577_; 
v___x_2575_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0___redArg(v_denote_2569_, v_e_2566_, v_val_2567_);
if (v_isShared_2574_ == 0)
{
lean_ctor_set(v___x_2573_, 0, v___x_2575_);
v___x_2577_ = v___x_2573_;
goto v_reusejp_2576_;
}
else
{
lean_object* v_reuseFailAlloc_2578_; 
v_reuseFailAlloc_2578_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2578_, 0, v___x_2575_);
lean_ctor_set(v_reuseFailAlloc_2578_, 1, v_vars_2570_);
lean_ctor_set(v_reuseFailAlloc_2578_, 2, v_varMap_2571_);
v___x_2577_ = v_reuseFailAlloc_2578_;
goto v_reusejp_2576_;
}
v_reusejp_2576_:
{
return v___x_2577_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_internalize___lam__2(lean_object* v_e_2580_, lean_object* v_val_2581_, lean_object* v_s_2582_){
_start:
{
lean_object* v_vars_2583_; lean_object* v_varMap_2584_; lean_object* v_denote_2585_; lean_object* v___x_2587_; uint8_t v_isShared_2588_; uint8_t v_isSharedCheck_2593_; 
v_vars_2583_ = lean_ctor_get(v_s_2582_, 0);
v_varMap_2584_ = lean_ctor_get(v_s_2582_, 1);
v_denote_2585_ = lean_ctor_get(v_s_2582_, 2);
v_isSharedCheck_2593_ = !lean_is_exclusive(v_s_2582_);
if (v_isSharedCheck_2593_ == 0)
{
v___x_2587_ = v_s_2582_;
v_isShared_2588_ = v_isSharedCheck_2593_;
goto v_resetjp_2586_;
}
else
{
lean_inc(v_denote_2585_);
lean_inc(v_varMap_2584_);
lean_inc(v_vars_2583_);
lean_dec(v_s_2582_);
v___x_2587_ = lean_box(0);
v_isShared_2588_ = v_isSharedCheck_2593_;
goto v_resetjp_2586_;
}
v_resetjp_2586_:
{
lean_object* v___x_2589_; lean_object* v___x_2591_; 
v___x_2589_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0___redArg(v_denote_2585_, v_e_2580_, v_val_2581_);
if (v_isShared_2588_ == 0)
{
lean_ctor_set(v___x_2587_, 2, v___x_2589_);
v___x_2591_ = v___x_2587_;
goto v_reusejp_2590_;
}
else
{
lean_object* v_reuseFailAlloc_2592_; 
v_reuseFailAlloc_2592_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2592_, 0, v_vars_2583_);
lean_ctor_set(v_reuseFailAlloc_2592_, 1, v_varMap_2584_);
lean_ctor_set(v_reuseFailAlloc_2592_, 2, v___x_2589_);
v___x_2591_ = v_reuseFailAlloc_2592_;
goto v_reusejp_2590_;
}
v_reusejp_2590_:
{
return v___x_2591_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__1___redArg(lean_object* v_cls_2594_, lean_object* v_msg_2595_, lean_object* v___y_2596_, lean_object* v___y_2597_, lean_object* v___y_2598_, lean_object* v___y_2599_){
_start:
{
lean_object* v_ref_2601_; lean_object* v___x_2602_; lean_object* v_a_2603_; lean_object* v___x_2605_; uint8_t v_isShared_2606_; uint8_t v_isSharedCheck_2648_; 
v_ref_2601_ = lean_ctor_get(v___y_2598_, 2);
v___x_2602_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5(v_msg_2595_, v___y_2596_, v___y_2597_, v___y_2598_, v___y_2599_);
v_a_2603_ = lean_ctor_get(v___x_2602_, 0);
v_isSharedCheck_2648_ = !lean_is_exclusive(v___x_2602_);
if (v_isSharedCheck_2648_ == 0)
{
v___x_2605_ = v___x_2602_;
v_isShared_2606_ = v_isSharedCheck_2648_;
goto v_resetjp_2604_;
}
else
{
lean_inc(v_a_2603_);
lean_dec(v___x_2602_);
v___x_2605_ = lean_box(0);
v_isShared_2606_ = v_isSharedCheck_2648_;
goto v_resetjp_2604_;
}
v_resetjp_2604_:
{
lean_object* v___x_2607_; lean_object* v_traceState_2608_; lean_object* v_env_2609_; lean_object* v_nextMacroScope_2610_; lean_object* v_ngen_2611_; lean_object* v_auxDeclNGen_2612_; lean_object* v_cache_2613_; lean_object* v_recordedDeps_2614_; lean_object* v_messages_2615_; lean_object* v_infoState_2616_; lean_object* v_snapshotTasks_2617_; lean_object* v___x_2619_; uint8_t v_isShared_2620_; uint8_t v_isSharedCheck_2647_; 
v___x_2607_ = lean_st_ref_take(v___y_2599_);
v_traceState_2608_ = lean_ctor_get(v___x_2607_, 4);
v_env_2609_ = lean_ctor_get(v___x_2607_, 0);
v_nextMacroScope_2610_ = lean_ctor_get(v___x_2607_, 1);
v_ngen_2611_ = lean_ctor_get(v___x_2607_, 2);
v_auxDeclNGen_2612_ = lean_ctor_get(v___x_2607_, 3);
v_cache_2613_ = lean_ctor_get(v___x_2607_, 5);
v_recordedDeps_2614_ = lean_ctor_get(v___x_2607_, 6);
v_messages_2615_ = lean_ctor_get(v___x_2607_, 7);
v_infoState_2616_ = lean_ctor_get(v___x_2607_, 8);
v_snapshotTasks_2617_ = lean_ctor_get(v___x_2607_, 9);
v_isSharedCheck_2647_ = !lean_is_exclusive(v___x_2607_);
if (v_isSharedCheck_2647_ == 0)
{
v___x_2619_ = v___x_2607_;
v_isShared_2620_ = v_isSharedCheck_2647_;
goto v_resetjp_2618_;
}
else
{
lean_inc(v_snapshotTasks_2617_);
lean_inc(v_infoState_2616_);
lean_inc(v_messages_2615_);
lean_inc(v_recordedDeps_2614_);
lean_inc(v_cache_2613_);
lean_inc(v_traceState_2608_);
lean_inc(v_auxDeclNGen_2612_);
lean_inc(v_ngen_2611_);
lean_inc(v_nextMacroScope_2610_);
lean_inc(v_env_2609_);
lean_dec(v___x_2607_);
v___x_2619_ = lean_box(0);
v_isShared_2620_ = v_isSharedCheck_2647_;
goto v_resetjp_2618_;
}
v_resetjp_2618_:
{
uint64_t v_tid_2621_; lean_object* v_traces_2622_; lean_object* v___x_2624_; uint8_t v_isShared_2625_; uint8_t v_isSharedCheck_2646_; 
v_tid_2621_ = lean_ctor_get_uint64(v_traceState_2608_, sizeof(void*)*1);
v_traces_2622_ = lean_ctor_get(v_traceState_2608_, 0);
v_isSharedCheck_2646_ = !lean_is_exclusive(v_traceState_2608_);
if (v_isSharedCheck_2646_ == 0)
{
v___x_2624_ = v_traceState_2608_;
v_isShared_2625_ = v_isSharedCheck_2646_;
goto v_resetjp_2623_;
}
else
{
lean_inc(v_traces_2622_);
lean_dec(v_traceState_2608_);
v___x_2624_ = lean_box(0);
v_isShared_2625_ = v_isSharedCheck_2646_;
goto v_resetjp_2623_;
}
v_resetjp_2623_:
{
lean_object* v___x_2626_; lean_object* v___x_2627_; double v___x_2628_; uint8_t v___x_2629_; lean_object* v___x_2630_; lean_object* v___x_2631_; lean_object* v___x_2632_; lean_object* v___x_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; lean_object* v___x_2637_; 
v___x_2626_ = lean_box(0);
v___x_2627_ = lean_box(0);
v___x_2628_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg___closed__0);
v___x_2629_ = 0;
v___x_2630_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg___closed__1));
v___x_2631_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2631_, 0, v_cls_2594_);
lean_ctor_set(v___x_2631_, 1, v___x_2627_);
lean_ctor_set(v___x_2631_, 2, v___x_2630_);
lean_ctor_set_float(v___x_2631_, sizeof(void*)*3, v___x_2628_);
lean_ctor_set_float(v___x_2631_, sizeof(void*)*3 + 8, v___x_2628_);
lean_ctor_set_uint8(v___x_2631_, sizeof(void*)*3 + 16, v___x_2629_);
v___x_2632_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg___closed__2));
v___x_2633_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2633_, 0, v___x_2631_);
lean_ctor_set(v___x_2633_, 1, v_a_2603_);
lean_ctor_set(v___x_2633_, 2, v___x_2632_);
lean_inc(v_ref_2601_);
v___x_2634_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2634_, 0, v_ref_2601_);
lean_ctor_set(v___x_2634_, 1, v___x_2633_);
v___x_2635_ = l_Lean_PersistentArray_push___redArg(v_traces_2622_, v___x_2634_);
if (v_isShared_2625_ == 0)
{
lean_ctor_set(v___x_2624_, 0, v___x_2635_);
v___x_2637_ = v___x_2624_;
goto v_reusejp_2636_;
}
else
{
lean_object* v_reuseFailAlloc_2645_; 
v_reuseFailAlloc_2645_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2645_, 0, v___x_2635_);
lean_ctor_set_uint64(v_reuseFailAlloc_2645_, sizeof(void*)*1, v_tid_2621_);
v___x_2637_ = v_reuseFailAlloc_2645_;
goto v_reusejp_2636_;
}
v_reusejp_2636_:
{
lean_object* v___x_2639_; 
if (v_isShared_2620_ == 0)
{
lean_ctor_set(v___x_2619_, 4, v___x_2637_);
v___x_2639_ = v___x_2619_;
goto v_reusejp_2638_;
}
else
{
lean_object* v_reuseFailAlloc_2644_; 
v_reuseFailAlloc_2644_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2644_, 0, v_env_2609_);
lean_ctor_set(v_reuseFailAlloc_2644_, 1, v_nextMacroScope_2610_);
lean_ctor_set(v_reuseFailAlloc_2644_, 2, v_ngen_2611_);
lean_ctor_set(v_reuseFailAlloc_2644_, 3, v_auxDeclNGen_2612_);
lean_ctor_set(v_reuseFailAlloc_2644_, 4, v___x_2637_);
lean_ctor_set(v_reuseFailAlloc_2644_, 5, v_cache_2613_);
lean_ctor_set(v_reuseFailAlloc_2644_, 6, v_recordedDeps_2614_);
lean_ctor_set(v_reuseFailAlloc_2644_, 7, v_messages_2615_);
lean_ctor_set(v_reuseFailAlloc_2644_, 8, v_infoState_2616_);
lean_ctor_set(v_reuseFailAlloc_2644_, 9, v_snapshotTasks_2617_);
v___x_2639_ = v_reuseFailAlloc_2644_;
goto v_reusejp_2638_;
}
v_reusejp_2638_:
{
lean_object* v___x_2640_; lean_object* v___x_2642_; 
v___x_2640_ = lean_st_ref_put(v___y_2599_, v___x_2639_);
if (v_isShared_2606_ == 0)
{
lean_ctor_set(v___x_2605_, 0, v___x_2626_);
v___x_2642_ = v___x_2605_;
goto v_reusejp_2641_;
}
else
{
lean_object* v_reuseFailAlloc_2643_; 
v_reuseFailAlloc_2643_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2643_, 0, v___x_2626_);
v___x_2642_ = v_reuseFailAlloc_2643_;
goto v_reusejp_2641_;
}
v_reusejp_2641_:
{
return v___x_2642_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__1___redArg___boxed(lean_object* v_cls_2649_, lean_object* v_msg_2650_, lean_object* v___y_2651_, lean_object* v___y_2652_, lean_object* v___y_2653_, lean_object* v___y_2654_, lean_object* v___y_2655_){
_start:
{
lean_object* v_res_2656_; 
v_res_2656_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__1___redArg(v_cls_2649_, v_msg_2650_, v___y_2651_, v___y_2652_, v___y_2653_, v___y_2654_);
lean_dec(v___y_2654_);
lean_dec_ref(v___y_2653_);
lean_dec(v___y_2652_);
lean_dec_ref(v___y_2651_);
return v_res_2656_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__2___redArg(lean_object* v_cls_2657_, lean_object* v_msg_2658_, lean_object* v___y_2659_, lean_object* v___y_2660_, lean_object* v___y_2661_, lean_object* v___y_2662_){
_start:
{
lean_object* v_ref_2664_; lean_object* v___x_2665_; lean_object* v_a_2666_; lean_object* v___x_2668_; uint8_t v_isShared_2669_; uint8_t v_isSharedCheck_2711_; 
v_ref_2664_ = lean_ctor_get(v___y_2661_, 2);
v___x_2665_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5(v_msg_2658_, v___y_2659_, v___y_2660_, v___y_2661_, v___y_2662_);
v_a_2666_ = lean_ctor_get(v___x_2665_, 0);
v_isSharedCheck_2711_ = !lean_is_exclusive(v___x_2665_);
if (v_isSharedCheck_2711_ == 0)
{
v___x_2668_ = v___x_2665_;
v_isShared_2669_ = v_isSharedCheck_2711_;
goto v_resetjp_2667_;
}
else
{
lean_inc(v_a_2666_);
lean_dec(v___x_2665_);
v___x_2668_ = lean_box(0);
v_isShared_2669_ = v_isSharedCheck_2711_;
goto v_resetjp_2667_;
}
v_resetjp_2667_:
{
lean_object* v___x_2670_; lean_object* v_traceState_2671_; lean_object* v_env_2672_; lean_object* v_nextMacroScope_2673_; lean_object* v_ngen_2674_; lean_object* v_auxDeclNGen_2675_; lean_object* v_cache_2676_; lean_object* v_recordedDeps_2677_; lean_object* v_messages_2678_; lean_object* v_infoState_2679_; lean_object* v_snapshotTasks_2680_; lean_object* v___x_2682_; uint8_t v_isShared_2683_; uint8_t v_isSharedCheck_2710_; 
v___x_2670_ = lean_st_ref_take(v___y_2662_);
v_traceState_2671_ = lean_ctor_get(v___x_2670_, 4);
v_env_2672_ = lean_ctor_get(v___x_2670_, 0);
v_nextMacroScope_2673_ = lean_ctor_get(v___x_2670_, 1);
v_ngen_2674_ = lean_ctor_get(v___x_2670_, 2);
v_auxDeclNGen_2675_ = lean_ctor_get(v___x_2670_, 3);
v_cache_2676_ = lean_ctor_get(v___x_2670_, 5);
v_recordedDeps_2677_ = lean_ctor_get(v___x_2670_, 6);
v_messages_2678_ = lean_ctor_get(v___x_2670_, 7);
v_infoState_2679_ = lean_ctor_get(v___x_2670_, 8);
v_snapshotTasks_2680_ = lean_ctor_get(v___x_2670_, 9);
v_isSharedCheck_2710_ = !lean_is_exclusive(v___x_2670_);
if (v_isSharedCheck_2710_ == 0)
{
v___x_2682_ = v___x_2670_;
v_isShared_2683_ = v_isSharedCheck_2710_;
goto v_resetjp_2681_;
}
else
{
lean_inc(v_snapshotTasks_2680_);
lean_inc(v_infoState_2679_);
lean_inc(v_messages_2678_);
lean_inc(v_recordedDeps_2677_);
lean_inc(v_cache_2676_);
lean_inc(v_traceState_2671_);
lean_inc(v_auxDeclNGen_2675_);
lean_inc(v_ngen_2674_);
lean_inc(v_nextMacroScope_2673_);
lean_inc(v_env_2672_);
lean_dec(v___x_2670_);
v___x_2682_ = lean_box(0);
v_isShared_2683_ = v_isSharedCheck_2710_;
goto v_resetjp_2681_;
}
v_resetjp_2681_:
{
uint64_t v_tid_2684_; lean_object* v_traces_2685_; lean_object* v___x_2687_; uint8_t v_isShared_2688_; uint8_t v_isSharedCheck_2709_; 
v_tid_2684_ = lean_ctor_get_uint64(v_traceState_2671_, sizeof(void*)*1);
v_traces_2685_ = lean_ctor_get(v_traceState_2671_, 0);
v_isSharedCheck_2709_ = !lean_is_exclusive(v_traceState_2671_);
if (v_isSharedCheck_2709_ == 0)
{
v___x_2687_ = v_traceState_2671_;
v_isShared_2688_ = v_isSharedCheck_2709_;
goto v_resetjp_2686_;
}
else
{
lean_inc(v_traces_2685_);
lean_dec(v_traceState_2671_);
v___x_2687_ = lean_box(0);
v_isShared_2688_ = v_isSharedCheck_2709_;
goto v_resetjp_2686_;
}
v_resetjp_2686_:
{
lean_object* v___x_2689_; lean_object* v___x_2690_; double v___x_2691_; uint8_t v___x_2692_; lean_object* v___x_2693_; lean_object* v___x_2694_; lean_object* v___x_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; lean_object* v___x_2700_; 
v___x_2689_ = lean_box(0);
v___x_2690_ = lean_box(0);
v___x_2691_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg___closed__0);
v___x_2692_ = 0;
v___x_2693_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg___closed__1));
v___x_2694_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2694_, 0, v_cls_2657_);
lean_ctor_set(v___x_2694_, 1, v___x_2690_);
lean_ctor_set(v___x_2694_, 2, v___x_2693_);
lean_ctor_set_float(v___x_2694_, sizeof(void*)*3, v___x_2691_);
lean_ctor_set_float(v___x_2694_, sizeof(void*)*3 + 8, v___x_2691_);
lean_ctor_set_uint8(v___x_2694_, sizeof(void*)*3 + 16, v___x_2692_);
v___x_2695_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg___closed__2));
v___x_2696_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2696_, 0, v___x_2694_);
lean_ctor_set(v___x_2696_, 1, v_a_2666_);
lean_ctor_set(v___x_2696_, 2, v___x_2695_);
lean_inc(v_ref_2664_);
v___x_2697_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2697_, 0, v_ref_2664_);
lean_ctor_set(v___x_2697_, 1, v___x_2696_);
v___x_2698_ = l_Lean_PersistentArray_push___redArg(v_traces_2685_, v___x_2697_);
if (v_isShared_2688_ == 0)
{
lean_ctor_set(v___x_2687_, 0, v___x_2698_);
v___x_2700_ = v___x_2687_;
goto v_reusejp_2699_;
}
else
{
lean_object* v_reuseFailAlloc_2708_; 
v_reuseFailAlloc_2708_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2708_, 0, v___x_2698_);
lean_ctor_set_uint64(v_reuseFailAlloc_2708_, sizeof(void*)*1, v_tid_2684_);
v___x_2700_ = v_reuseFailAlloc_2708_;
goto v_reusejp_2699_;
}
v_reusejp_2699_:
{
lean_object* v___x_2702_; 
if (v_isShared_2683_ == 0)
{
lean_ctor_set(v___x_2682_, 4, v___x_2700_);
v___x_2702_ = v___x_2682_;
goto v_reusejp_2701_;
}
else
{
lean_object* v_reuseFailAlloc_2707_; 
v_reuseFailAlloc_2707_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2707_, 0, v_env_2672_);
lean_ctor_set(v_reuseFailAlloc_2707_, 1, v_nextMacroScope_2673_);
lean_ctor_set(v_reuseFailAlloc_2707_, 2, v_ngen_2674_);
lean_ctor_set(v_reuseFailAlloc_2707_, 3, v_auxDeclNGen_2675_);
lean_ctor_set(v_reuseFailAlloc_2707_, 4, v___x_2700_);
lean_ctor_set(v_reuseFailAlloc_2707_, 5, v_cache_2676_);
lean_ctor_set(v_reuseFailAlloc_2707_, 6, v_recordedDeps_2677_);
lean_ctor_set(v_reuseFailAlloc_2707_, 7, v_messages_2678_);
lean_ctor_set(v_reuseFailAlloc_2707_, 8, v_infoState_2679_);
lean_ctor_set(v_reuseFailAlloc_2707_, 9, v_snapshotTasks_2680_);
v___x_2702_ = v_reuseFailAlloc_2707_;
goto v_reusejp_2701_;
}
v_reusejp_2701_:
{
lean_object* v___x_2703_; lean_object* v___x_2705_; 
v___x_2703_ = lean_st_ref_put(v___y_2662_, v___x_2702_);
if (v_isShared_2669_ == 0)
{
lean_ctor_set(v___x_2668_, 0, v___x_2689_);
v___x_2705_ = v___x_2668_;
goto v_reusejp_2704_;
}
else
{
lean_object* v_reuseFailAlloc_2706_; 
v_reuseFailAlloc_2706_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2706_, 0, v___x_2689_);
v___x_2705_ = v_reuseFailAlloc_2706_;
goto v_reusejp_2704_;
}
v_reusejp_2704_:
{
return v___x_2705_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__2___redArg___boxed(lean_object* v_cls_2712_, lean_object* v_msg_2713_, lean_object* v___y_2714_, lean_object* v___y_2715_, lean_object* v___y_2716_, lean_object* v___y_2717_, lean_object* v___y_2718_){
_start:
{
lean_object* v_res_2719_; 
v_res_2719_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__2___redArg(v_cls_2712_, v_msg_2713_, v___y_2714_, v___y_2715_, v___y_2716_, v___y_2717_);
lean_dec(v___y_2717_);
lean_dec_ref(v___y_2716_);
lean_dec(v___y_2715_);
lean_dec_ref(v___y_2714_);
return v_res_2719_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__3___redArg(lean_object* v_cls_2720_, lean_object* v_msg_2721_, lean_object* v___y_2722_, lean_object* v___y_2723_, lean_object* v___y_2724_, lean_object* v___y_2725_){
_start:
{
lean_object* v_ref_2727_; lean_object* v___x_2728_; lean_object* v_a_2729_; lean_object* v___x_2731_; uint8_t v_isShared_2732_; uint8_t v_isSharedCheck_2774_; 
v_ref_2727_ = lean_ctor_get(v___y_2724_, 2);
v___x_2728_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5(v_msg_2721_, v___y_2722_, v___y_2723_, v___y_2724_, v___y_2725_);
v_a_2729_ = lean_ctor_get(v___x_2728_, 0);
v_isSharedCheck_2774_ = !lean_is_exclusive(v___x_2728_);
if (v_isSharedCheck_2774_ == 0)
{
v___x_2731_ = v___x_2728_;
v_isShared_2732_ = v_isSharedCheck_2774_;
goto v_resetjp_2730_;
}
else
{
lean_inc(v_a_2729_);
lean_dec(v___x_2728_);
v___x_2731_ = lean_box(0);
v_isShared_2732_ = v_isSharedCheck_2774_;
goto v_resetjp_2730_;
}
v_resetjp_2730_:
{
lean_object* v___x_2733_; lean_object* v_traceState_2734_; lean_object* v_env_2735_; lean_object* v_nextMacroScope_2736_; lean_object* v_ngen_2737_; lean_object* v_auxDeclNGen_2738_; lean_object* v_cache_2739_; lean_object* v_recordedDeps_2740_; lean_object* v_messages_2741_; lean_object* v_infoState_2742_; lean_object* v_snapshotTasks_2743_; lean_object* v___x_2745_; uint8_t v_isShared_2746_; uint8_t v_isSharedCheck_2773_; 
v___x_2733_ = lean_st_ref_take(v___y_2725_);
v_traceState_2734_ = lean_ctor_get(v___x_2733_, 4);
v_env_2735_ = lean_ctor_get(v___x_2733_, 0);
v_nextMacroScope_2736_ = lean_ctor_get(v___x_2733_, 1);
v_ngen_2737_ = lean_ctor_get(v___x_2733_, 2);
v_auxDeclNGen_2738_ = lean_ctor_get(v___x_2733_, 3);
v_cache_2739_ = lean_ctor_get(v___x_2733_, 5);
v_recordedDeps_2740_ = lean_ctor_get(v___x_2733_, 6);
v_messages_2741_ = lean_ctor_get(v___x_2733_, 7);
v_infoState_2742_ = lean_ctor_get(v___x_2733_, 8);
v_snapshotTasks_2743_ = lean_ctor_get(v___x_2733_, 9);
v_isSharedCheck_2773_ = !lean_is_exclusive(v___x_2733_);
if (v_isSharedCheck_2773_ == 0)
{
v___x_2745_ = v___x_2733_;
v_isShared_2746_ = v_isSharedCheck_2773_;
goto v_resetjp_2744_;
}
else
{
lean_inc(v_snapshotTasks_2743_);
lean_inc(v_infoState_2742_);
lean_inc(v_messages_2741_);
lean_inc(v_recordedDeps_2740_);
lean_inc(v_cache_2739_);
lean_inc(v_traceState_2734_);
lean_inc(v_auxDeclNGen_2738_);
lean_inc(v_ngen_2737_);
lean_inc(v_nextMacroScope_2736_);
lean_inc(v_env_2735_);
lean_dec(v___x_2733_);
v___x_2745_ = lean_box(0);
v_isShared_2746_ = v_isSharedCheck_2773_;
goto v_resetjp_2744_;
}
v_resetjp_2744_:
{
uint64_t v_tid_2747_; lean_object* v_traces_2748_; lean_object* v___x_2750_; uint8_t v_isShared_2751_; uint8_t v_isSharedCheck_2772_; 
v_tid_2747_ = lean_ctor_get_uint64(v_traceState_2734_, sizeof(void*)*1);
v_traces_2748_ = lean_ctor_get(v_traceState_2734_, 0);
v_isSharedCheck_2772_ = !lean_is_exclusive(v_traceState_2734_);
if (v_isSharedCheck_2772_ == 0)
{
v___x_2750_ = v_traceState_2734_;
v_isShared_2751_ = v_isSharedCheck_2772_;
goto v_resetjp_2749_;
}
else
{
lean_inc(v_traces_2748_);
lean_dec(v_traceState_2734_);
v___x_2750_ = lean_box(0);
v_isShared_2751_ = v_isSharedCheck_2772_;
goto v_resetjp_2749_;
}
v_resetjp_2749_:
{
lean_object* v___x_2752_; lean_object* v___x_2753_; double v___x_2754_; uint8_t v___x_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; lean_object* v___x_2759_; lean_object* v___x_2760_; lean_object* v___x_2761_; lean_object* v___x_2763_; 
v___x_2752_ = lean_box(0);
v___x_2753_ = lean_box(0);
v___x_2754_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg___closed__0);
v___x_2755_ = 0;
v___x_2756_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg___closed__1));
v___x_2757_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2757_, 0, v_cls_2720_);
lean_ctor_set(v___x_2757_, 1, v___x_2753_);
lean_ctor_set(v___x_2757_, 2, v___x_2756_);
lean_ctor_set_float(v___x_2757_, sizeof(void*)*3, v___x_2754_);
lean_ctor_set_float(v___x_2757_, sizeof(void*)*3 + 8, v___x_2754_);
lean_ctor_set_uint8(v___x_2757_, sizeof(void*)*3 + 16, v___x_2755_);
v___x_2758_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg___closed__2));
v___x_2759_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2759_, 0, v___x_2757_);
lean_ctor_set(v___x_2759_, 1, v_a_2729_);
lean_ctor_set(v___x_2759_, 2, v___x_2758_);
lean_inc(v_ref_2727_);
v___x_2760_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2760_, 0, v_ref_2727_);
lean_ctor_set(v___x_2760_, 1, v___x_2759_);
v___x_2761_ = l_Lean_PersistentArray_push___redArg(v_traces_2748_, v___x_2760_);
if (v_isShared_2751_ == 0)
{
lean_ctor_set(v___x_2750_, 0, v___x_2761_);
v___x_2763_ = v___x_2750_;
goto v_reusejp_2762_;
}
else
{
lean_object* v_reuseFailAlloc_2771_; 
v_reuseFailAlloc_2771_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2771_, 0, v___x_2761_);
lean_ctor_set_uint64(v_reuseFailAlloc_2771_, sizeof(void*)*1, v_tid_2747_);
v___x_2763_ = v_reuseFailAlloc_2771_;
goto v_reusejp_2762_;
}
v_reusejp_2762_:
{
lean_object* v___x_2765_; 
if (v_isShared_2746_ == 0)
{
lean_ctor_set(v___x_2745_, 4, v___x_2763_);
v___x_2765_ = v___x_2745_;
goto v_reusejp_2764_;
}
else
{
lean_object* v_reuseFailAlloc_2770_; 
v_reuseFailAlloc_2770_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2770_, 0, v_env_2735_);
lean_ctor_set(v_reuseFailAlloc_2770_, 1, v_nextMacroScope_2736_);
lean_ctor_set(v_reuseFailAlloc_2770_, 2, v_ngen_2737_);
lean_ctor_set(v_reuseFailAlloc_2770_, 3, v_auxDeclNGen_2738_);
lean_ctor_set(v_reuseFailAlloc_2770_, 4, v___x_2763_);
lean_ctor_set(v_reuseFailAlloc_2770_, 5, v_cache_2739_);
lean_ctor_set(v_reuseFailAlloc_2770_, 6, v_recordedDeps_2740_);
lean_ctor_set(v_reuseFailAlloc_2770_, 7, v_messages_2741_);
lean_ctor_set(v_reuseFailAlloc_2770_, 8, v_infoState_2742_);
lean_ctor_set(v_reuseFailAlloc_2770_, 9, v_snapshotTasks_2743_);
v___x_2765_ = v_reuseFailAlloc_2770_;
goto v_reusejp_2764_;
}
v_reusejp_2764_:
{
lean_object* v___x_2766_; lean_object* v___x_2768_; 
v___x_2766_ = lean_st_ref_put(v___y_2725_, v___x_2765_);
if (v_isShared_2732_ == 0)
{
lean_ctor_set(v___x_2731_, 0, v___x_2752_);
v___x_2768_ = v___x_2731_;
goto v_reusejp_2767_;
}
else
{
lean_object* v_reuseFailAlloc_2769_; 
v_reuseFailAlloc_2769_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2769_, 0, v___x_2752_);
v___x_2768_ = v_reuseFailAlloc_2769_;
goto v_reusejp_2767_;
}
v_reusejp_2767_:
{
return v___x_2768_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__3___redArg___boxed(lean_object* v_cls_2775_, lean_object* v_msg_2776_, lean_object* v___y_2777_, lean_object* v___y_2778_, lean_object* v___y_2779_, lean_object* v___y_2780_, lean_object* v___y_2781_){
_start:
{
lean_object* v_res_2782_; 
v_res_2782_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__3___redArg(v_cls_2775_, v_msg_2776_, v___y_2777_, v___y_2778_, v___y_2779_, v___y_2780_);
lean_dec(v___y_2780_);
lean_dec_ref(v___y_2779_);
lean_dec(v___y_2778_);
lean_dec_ref(v___y_2777_);
return v_res_2782_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__2(void){
_start:
{
lean_object* v___x_2788_; lean_object* v___x_2789_; lean_object* v___x_2790_; 
v___x_2788_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__1));
v___x_2789_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__7));
v___x_2790_ = l_Lean_Name_append(v___x_2789_, v___x_2788_);
return v___x_2790_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__4(void){
_start:
{
lean_object* v___x_2792_; lean_object* v___x_2793_; 
v___x_2792_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__3));
v___x_2793_ = l_Lean_stringToMessageData(v___x_2792_);
return v___x_2793_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__6(void){
_start:
{
lean_object* v___x_2795_; lean_object* v___x_2796_; 
v___x_2795_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__5));
v___x_2796_ = l_Lean_stringToMessageData(v___x_2795_);
return v___x_2796_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__8(void){
_start:
{
lean_object* v___x_2798_; lean_object* v___x_2799_; 
v___x_2798_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__7));
v___x_2799_ = l_Lean_stringToMessageData(v___x_2798_);
return v___x_2799_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__10(void){
_start:
{
lean_object* v___x_2801_; lean_object* v___x_2802_; 
v___x_2801_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__9));
v___x_2802_ = l_Lean_stringToMessageData(v___x_2801_);
return v___x_2802_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__12(void){
_start:
{
lean_object* v___x_2804_; lean_object* v___x_2805_; 
v___x_2804_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__11));
v___x_2805_ = l_Lean_stringToMessageData(v___x_2804_);
return v___x_2805_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_internalize(lean_object* v_e_2806_, lean_object* v_parent_x3f_2807_, lean_object* v_a_2808_, lean_object* v_a_2809_, lean_object* v_a_2810_, lean_object* v_a_2811_, lean_object* v_a_2812_, lean_object* v_a_2813_, lean_object* v_a_2814_, lean_object* v_a_2815_, lean_object* v_a_2816_, lean_object* v_a_2817_){
_start:
{
lean_object* v___y_2820_; lean_object* v___y_2821_; lean_object* v___y_2822_; lean_object* v___y_2823_; lean_object* v___y_2824_; lean_object* v___y_2825_; lean_object* v___y_2826_; lean_object* v___y_2827_; lean_object* v___y_2828_; lean_object* v___y_2829_; lean_object* v___y_2830_; lean_object* v___y_2831_; lean_object* v___y_2837_; lean_object* v___y_2838_; lean_object* v___y_2839_; lean_object* v___y_2840_; lean_object* v___y_2841_; lean_object* v___y_2842_; lean_object* v___y_2843_; lean_object* v___y_2844_; lean_object* v___y_2845_; lean_object* v___y_2846_; lean_object* v___y_2847_; lean_object* v___y_2848_; lean_object* v___y_2854_; lean_object* v___y_2855_; lean_object* v___y_2856_; lean_object* v___y_2857_; lean_object* v___y_2858_; lean_object* v___y_2859_; lean_object* v___y_2860_; lean_object* v___y_2861_; lean_object* v___y_2862_; lean_object* v___y_2863_; lean_object* v___y_2864_; lean_object* v___y_2865_; lean_object* v___y_2872_; lean_object* v___y_2873_; lean_object* v___y_2874_; lean_object* v___y_2875_; lean_object* v___y_2876_; lean_object* v___y_2877_; lean_object* v___y_2878_; lean_object* v___y_2879_; lean_object* v___y_2880_; lean_object* v___y_2881_; lean_object* v___y_2882_; lean_object* v___y_2883_; lean_object* v___x_2888_; 
v___x_2888_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_2810_);
if (lean_obj_tag(v___x_2888_) == 0)
{
lean_object* v_a_2889_; lean_object* v___x_2891_; uint8_t v_isShared_2892_; uint8_t v_isSharedCheck_3189_; 
v_a_2889_ = lean_ctor_get(v___x_2888_, 0);
v_isSharedCheck_3189_ = !lean_is_exclusive(v___x_2888_);
if (v_isSharedCheck_3189_ == 0)
{
v___x_2891_ = v___x_2888_;
v_isShared_2892_ = v_isSharedCheck_3189_;
goto v_resetjp_2890_;
}
else
{
lean_inc(v_a_2889_);
lean_dec(v___x_2888_);
v___x_2891_ = lean_box(0);
v_isShared_2892_ = v_isSharedCheck_3189_;
goto v_resetjp_2890_;
}
v_resetjp_2890_:
{
uint8_t v_ring_2893_; 
v_ring_2893_ = lean_ctor_get_uint8(v_a_2889_, sizeof(void*)*17 + 22);
lean_dec(v_a_2889_);
if (v_ring_2893_ == 0)
{
lean_object* v___x_2894_; lean_object* v___x_2896_; 
lean_dec_ref(v_e_2806_);
v___x_2894_ = lean_box(0);
if (v_isShared_2892_ == 0)
{
lean_ctor_set(v___x_2891_, 0, v___x_2894_);
v___x_2896_ = v___x_2891_;
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
else
{
uint8_t v___x_2898_; 
v___x_2898_ = l_Lean_Meta_Grind_Arith_isIntModuleVirtualParent(v_parent_x3f_2807_);
if (v___x_2898_ == 0)
{
lean_object* v___x_2899_; 
lean_del_object(v___x_2891_);
lean_inc_ref(v_e_2806_);
v___x_2899_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeInv(v_e_2806_, v_a_2808_, v_a_2809_, v_a_2810_, v_a_2811_, v_a_2812_, v_a_2813_, v_a_2814_, v_a_2815_, v_a_2816_, v_a_2817_);
if (lean_obj_tag(v___x_2899_) == 0)
{
lean_object* v_a_2900_; lean_object* v___x_2902_; uint8_t v_isShared_2903_; uint8_t v_isSharedCheck_3176_; 
v_a_2900_ = lean_ctor_get(v___x_2899_, 0);
v_isSharedCheck_3176_ = !lean_is_exclusive(v___x_2899_);
if (v_isSharedCheck_3176_ == 0)
{
v___x_2902_ = v___x_2899_;
v_isShared_2903_ = v_isSharedCheck_3176_;
goto v_resetjp_2901_;
}
else
{
lean_inc(v_a_2900_);
lean_dec(v___x_2899_);
v___x_2902_ = lean_box(0);
v_isShared_2903_ = v_isSharedCheck_3176_;
goto v_resetjp_2901_;
}
v_resetjp_2901_:
{
uint8_t v___x_2904_; 
v___x_2904_ = lean_unbox(v_a_2900_);
lean_dec(v_a_2900_);
if (v___x_2904_ == 0)
{
lean_object* v___x_2905_; 
v___x_2905_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f(v_e_2806_);
if (lean_obj_tag(v___x_2905_) == 1)
{
lean_object* v_val_2906_; uint8_t v_a_2908_; uint8_t v___x_3142_; 
v_val_2906_ = lean_ctor_get(v___x_2905_, 0);
lean_inc(v_val_2906_);
lean_dec_ref_known(v___x_2905_, 1);
v___x_3142_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isForbiddenParent(v_parent_x3f_2807_);
if (v___x_3142_ == 0)
{
uint8_t v___x_3143_; 
lean_del_object(v___x_2902_);
v___x_3143_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isIneqParent(v_parent_x3f_2807_);
if (v___x_3143_ == 0)
{
v_a_2908_ = v___x_3143_;
goto v___jp_2907_;
}
else
{
lean_object* v___x_3144_; 
lean_inc(v_val_2906_);
v___x_3144_ = l_Lean_Meta_Grind_Arith_Cutsat_isCutsatType___redArg(v_val_2906_, v_a_2810_, v_a_2815_);
if (lean_obj_tag(v___x_3144_) == 0)
{
lean_object* v_a_3145_; lean_object* v___x_3147_; uint8_t v_isShared_3148_; uint8_t v_isSharedCheck_3155_; 
v_a_3145_ = lean_ctor_get(v___x_3144_, 0);
v_isSharedCheck_3155_ = !lean_is_exclusive(v___x_3144_);
if (v_isSharedCheck_3155_ == 0)
{
v___x_3147_ = v___x_3144_;
v_isShared_3148_ = v_isSharedCheck_3155_;
goto v_resetjp_3146_;
}
else
{
lean_inc(v_a_3145_);
lean_dec(v___x_3144_);
v___x_3147_ = lean_box(0);
v_isShared_3148_ = v_isSharedCheck_3155_;
goto v_resetjp_3146_;
}
v_resetjp_3146_:
{
uint8_t v___x_3149_; 
v___x_3149_ = lean_unbox(v_a_3145_);
if (v___x_3149_ == 0)
{
uint8_t v___x_3150_; 
lean_del_object(v___x_3147_);
v___x_3150_ = lean_unbox(v_a_3145_);
lean_dec(v_a_3145_);
v_a_2908_ = v___x_3150_;
goto v___jp_2907_;
}
else
{
lean_object* v___x_3151_; lean_object* v___x_3153_; 
lean_dec(v_a_3145_);
lean_dec(v_val_2906_);
lean_dec_ref(v_e_2806_);
v___x_3151_ = lean_box(0);
if (v_isShared_3148_ == 0)
{
lean_ctor_set(v___x_3147_, 0, v___x_3151_);
v___x_3153_ = v___x_3147_;
goto v_reusejp_3152_;
}
else
{
lean_object* v_reuseFailAlloc_3154_; 
v_reuseFailAlloc_3154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3154_, 0, v___x_3151_);
v___x_3153_ = v_reuseFailAlloc_3154_;
goto v_reusejp_3152_;
}
v_reusejp_3152_:
{
return v___x_3153_;
}
}
}
}
else
{
lean_object* v_a_3156_; lean_object* v___x_3158_; uint8_t v_isShared_3159_; uint8_t v_isSharedCheck_3163_; 
lean_dec(v_val_2906_);
lean_dec_ref(v_e_2806_);
v_a_3156_ = lean_ctor_get(v___x_3144_, 0);
v_isSharedCheck_3163_ = !lean_is_exclusive(v___x_3144_);
if (v_isSharedCheck_3163_ == 0)
{
v___x_3158_ = v___x_3144_;
v_isShared_3159_ = v_isSharedCheck_3163_;
goto v_resetjp_3157_;
}
else
{
lean_inc(v_a_3156_);
lean_dec(v___x_3144_);
v___x_3158_ = lean_box(0);
v_isShared_3159_ = v_isSharedCheck_3163_;
goto v_resetjp_3157_;
}
v_resetjp_3157_:
{
lean_object* v___x_3161_; 
if (v_isShared_3159_ == 0)
{
v___x_3161_ = v___x_3158_;
goto v_reusejp_3160_;
}
else
{
lean_object* v_reuseFailAlloc_3162_; 
v_reuseFailAlloc_3162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3162_, 0, v_a_3156_);
v___x_3161_ = v_reuseFailAlloc_3162_;
goto v_reusejp_3160_;
}
v_reusejp_3160_:
{
return v___x_3161_;
}
}
}
}
}
else
{
lean_object* v___x_3164_; lean_object* v___x_3166_; 
lean_dec(v_val_2906_);
lean_dec_ref(v_e_2806_);
v___x_3164_ = lean_box(0);
if (v_isShared_2903_ == 0)
{
lean_ctor_set(v___x_2902_, 0, v___x_3164_);
v___x_3166_ = v___x_2902_;
goto v_reusejp_3165_;
}
else
{
lean_object* v_reuseFailAlloc_3167_; 
v_reuseFailAlloc_3167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3167_, 0, v___x_3164_);
v___x_3166_ = v_reuseFailAlloc_3167_;
goto v_reusejp_3165_;
}
v_reusejp_3165_:
{
return v___x_3166_;
}
}
v___jp_2907_:
{
lean_object* v___x_2909_; 
lean_inc(v_val_2906_);
v___x_2909_ = l_Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f___redArg(v_val_2906_, v_a_2812_, v_a_2813_, v_a_2814_, v_a_2815_, v_a_2816_, v_a_2817_);
if (lean_obj_tag(v___x_2909_) == 0)
{
lean_object* v_a_2910_; 
v_a_2910_ = lean_ctor_get(v___x_2909_, 0);
lean_inc(v_a_2910_);
lean_dec_ref_known(v___x_2909_, 1);
if (lean_obj_tag(v_a_2910_) == 1)
{
lean_object* v_val_2911_; lean_object* v___x_2912_; lean_object* v___x_2913_; 
lean_dec(v_val_2906_);
v_val_2911_ = lean_ctor_get(v_a_2910_, 0);
lean_inc_n(v_val_2911_, 2);
lean_dec_ref_known(v_a_2910_, 1);
v___x_2912_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2912_, 0, v_val_2911_);
lean_ctor_set_uint8(v___x_2912_, sizeof(void*)*1, v_a_2908_);
lean_inc_ref(v_e_2806_);
v___x_2913_ = l_Lean_Meta_Grind_Arith_CommRing_reify_x3f(v_e_2806_, v_ring_2893_, v___x_2912_, v_a_2808_, v_a_2809_, v_a_2810_, v_a_2811_, v_a_2812_, v_a_2813_, v_a_2814_, v_a_2815_, v_a_2816_, v_a_2817_);
if (lean_obj_tag(v___x_2913_) == 0)
{
lean_object* v_a_2914_; lean_object* v___x_2916_; uint8_t v_isShared_2917_; uint8_t v_isSharedCheck_2949_; 
v_a_2914_ = lean_ctor_get(v___x_2913_, 0);
v_isSharedCheck_2949_ = !lean_is_exclusive(v___x_2913_);
if (v_isSharedCheck_2949_ == 0)
{
v___x_2916_ = v___x_2913_;
v_isShared_2917_ = v_isSharedCheck_2949_;
goto v_resetjp_2915_;
}
else
{
lean_inc(v_a_2914_);
lean_dec(v___x_2913_);
v___x_2916_ = lean_box(0);
v_isShared_2917_ = v_isSharedCheck_2949_;
goto v_resetjp_2915_;
}
v_resetjp_2915_:
{
if (lean_obj_tag(v_a_2914_) == 1)
{
lean_object* v_toCold_2918_; lean_object* v_options_2919_; lean_object* v_val_2920_; lean_object* v_inheritedTraceOptions_2921_; uint8_t v_hasTrace_2922_; lean_object* v___f_2923_; 
lean_del_object(v___x_2916_);
v_toCold_2918_ = lean_ctor_get(v_a_2816_, 0);
v_options_2919_ = lean_ctor_get(v_toCold_2918_, 2);
v_val_2920_ = lean_ctor_get(v_a_2914_, 0);
lean_inc(v_val_2920_);
lean_dec_ref_known(v_a_2914_, 1);
v_inheritedTraceOptions_2921_ = lean_ctor_get(v_toCold_2918_, 11);
v_hasTrace_2922_ = lean_ctor_get_uint8(v_options_2919_, sizeof(void*)*1);
lean_inc_ref(v_e_2806_);
v___f_2923_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_internalize___lam__0), 3, 2);
lean_closure_set(v___f_2923_, 0, v_e_2806_);
lean_closure_set(v___f_2923_, 1, v_val_2920_);
if (v_hasTrace_2922_ == 0)
{
lean_dec(v_val_2911_);
v___y_2854_ = v___f_2923_;
v___y_2855_ = v___x_2912_;
v___y_2856_ = v_a_2808_;
v___y_2857_ = v_a_2809_;
v___y_2858_ = v_a_2810_;
v___y_2859_ = v_a_2811_;
v___y_2860_ = v_a_2812_;
v___y_2861_ = v_a_2813_;
v___y_2862_ = v_a_2814_;
v___y_2863_ = v_a_2815_;
v___y_2864_ = v_a_2816_;
v___y_2865_ = v_a_2817_;
goto v___jp_2853_;
}
else
{
lean_object* v___x_2924_; lean_object* v___x_2925_; uint8_t v___x_2926_; 
v___x_2924_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__1));
v___x_2925_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__2, &l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__2_once, _init_l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__2);
v___x_2926_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2921_, v_options_2919_, v___x_2925_);
if (v___x_2926_ == 0)
{
lean_dec(v_val_2911_);
v___y_2854_ = v___f_2923_;
v___y_2855_ = v___x_2912_;
v___y_2856_ = v_a_2808_;
v___y_2857_ = v_a_2809_;
v___y_2858_ = v_a_2810_;
v___y_2859_ = v_a_2811_;
v___y_2860_ = v_a_2812_;
v___y_2861_ = v_a_2813_;
v___y_2862_ = v_a_2814_;
v___y_2863_ = v_a_2815_;
v___y_2864_ = v_a_2816_;
v___y_2865_ = v_a_2817_;
goto v___jp_2853_;
}
else
{
lean_object* v___x_2927_; 
v___x_2927_ = l_Lean_Meta_Grind_updateLastTag(v_a_2808_, v_a_2809_, v_a_2810_, v_a_2811_, v_a_2812_, v_a_2813_, v_a_2814_, v_a_2815_, v_a_2816_, v_a_2817_);
if (lean_obj_tag(v___x_2927_) == 0)
{
lean_object* v___x_2929_; uint8_t v_isShared_2930_; uint8_t v_isSharedCheck_2943_; 
v_isSharedCheck_2943_ = !lean_is_exclusive(v___x_2927_);
if (v_isSharedCheck_2943_ == 0)
{
lean_object* v_unused_2944_; 
v_unused_2944_ = lean_ctor_get(v___x_2927_, 0);
lean_dec(v_unused_2944_);
v___x_2929_ = v___x_2927_;
v_isShared_2930_ = v_isSharedCheck_2943_;
goto v_resetjp_2928_;
}
else
{
lean_dec(v___x_2927_);
v___x_2929_ = lean_box(0);
v_isShared_2930_ = v_isSharedCheck_2943_;
goto v_resetjp_2928_;
}
v_resetjp_2928_:
{
lean_object* v___x_2931_; lean_object* v___x_2932_; lean_object* v___x_2934_; 
v___x_2931_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__4, &l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__4_once, _init_l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__4);
v___x_2932_ = l_Nat_reprFast(v_val_2911_);
if (v_isShared_2930_ == 0)
{
lean_ctor_set_tag(v___x_2929_, 3);
lean_ctor_set(v___x_2929_, 0, v___x_2932_);
v___x_2934_ = v___x_2929_;
goto v_reusejp_2933_;
}
else
{
lean_object* v_reuseFailAlloc_2942_; 
v_reuseFailAlloc_2942_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2942_, 0, v___x_2932_);
v___x_2934_ = v_reuseFailAlloc_2942_;
goto v_reusejp_2933_;
}
v_reusejp_2933_:
{
lean_object* v___x_2935_; lean_object* v___x_2936_; lean_object* v___x_2937_; lean_object* v___x_2938_; lean_object* v___x_2939_; lean_object* v___x_2940_; lean_object* v___x_2941_; 
v___x_2935_ = l_Lean_MessageData_ofFormat(v___x_2934_);
v___x_2936_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2936_, 0, v___x_2931_);
lean_ctor_set(v___x_2936_, 1, v___x_2935_);
v___x_2937_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__6, &l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__6_once, _init_l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__6);
v___x_2938_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2938_, 0, v___x_2936_);
lean_ctor_set(v___x_2938_, 1, v___x_2937_);
lean_inc_ref(v_e_2806_);
v___x_2939_ = l_Lean_MessageData_ofExpr(v_e_2806_);
v___x_2940_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2940_, 0, v___x_2938_);
lean_ctor_set(v___x_2940_, 1, v___x_2939_);
v___x_2941_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg(v___x_2924_, v___x_2940_, v_a_2814_, v_a_2815_, v_a_2816_, v_a_2817_);
if (lean_obj_tag(v___x_2941_) == 0)
{
lean_dec_ref_known(v___x_2941_, 1);
v___y_2854_ = v___f_2923_;
v___y_2855_ = v___x_2912_;
v___y_2856_ = v_a_2808_;
v___y_2857_ = v_a_2809_;
v___y_2858_ = v_a_2810_;
v___y_2859_ = v_a_2811_;
v___y_2860_ = v_a_2812_;
v___y_2861_ = v_a_2813_;
v___y_2862_ = v_a_2814_;
v___y_2863_ = v_a_2815_;
v___y_2864_ = v_a_2816_;
v___y_2865_ = v_a_2817_;
goto v___jp_2853_;
}
else
{
lean_dec_ref(v___f_2923_);
lean_dec_ref_known(v___x_2912_, 1);
lean_dec_ref(v_e_2806_);
return v___x_2941_;
}
}
}
}
else
{
lean_dec_ref(v___f_2923_);
lean_dec_ref_known(v___x_2912_, 1);
lean_dec(v_val_2911_);
lean_dec_ref(v_e_2806_);
return v___x_2927_;
}
}
}
}
else
{
lean_object* v___x_2945_; lean_object* v___x_2947_; 
lean_dec(v_a_2914_);
lean_dec_ref_known(v___x_2912_, 1);
lean_dec(v_val_2911_);
lean_dec_ref(v_e_2806_);
v___x_2945_ = lean_box(0);
if (v_isShared_2917_ == 0)
{
lean_ctor_set(v___x_2916_, 0, v___x_2945_);
v___x_2947_ = v___x_2916_;
goto v_reusejp_2946_;
}
else
{
lean_object* v_reuseFailAlloc_2948_; 
v_reuseFailAlloc_2948_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2948_, 0, v___x_2945_);
v___x_2947_ = v_reuseFailAlloc_2948_;
goto v_reusejp_2946_;
}
v_reusejp_2946_:
{
return v___x_2947_;
}
}
}
}
else
{
lean_object* v_a_2950_; lean_object* v___x_2952_; uint8_t v_isShared_2953_; uint8_t v_isSharedCheck_2957_; 
lean_dec_ref_known(v___x_2912_, 1);
lean_dec(v_val_2911_);
lean_dec_ref(v_e_2806_);
v_a_2950_ = lean_ctor_get(v___x_2913_, 0);
v_isSharedCheck_2957_ = !lean_is_exclusive(v___x_2913_);
if (v_isSharedCheck_2957_ == 0)
{
v___x_2952_ = v___x_2913_;
v_isShared_2953_ = v_isSharedCheck_2957_;
goto v_resetjp_2951_;
}
else
{
lean_inc(v_a_2950_);
lean_dec(v___x_2913_);
v___x_2952_ = lean_box(0);
v_isShared_2953_ = v_isSharedCheck_2957_;
goto v_resetjp_2951_;
}
v_resetjp_2951_:
{
lean_object* v___x_2955_; 
if (v_isShared_2953_ == 0)
{
v___x_2955_ = v___x_2952_;
goto v_reusejp_2954_;
}
else
{
lean_object* v_reuseFailAlloc_2956_; 
v_reuseFailAlloc_2956_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2956_, 0, v_a_2950_);
v___x_2955_ = v_reuseFailAlloc_2956_;
goto v_reusejp_2954_;
}
v_reusejp_2954_:
{
return v___x_2955_;
}
}
}
}
else
{
lean_object* v___x_2958_; 
lean_dec(v_a_2910_);
lean_inc(v_val_2906_);
v___x_2958_ = l_Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f___redArg(v_val_2906_, v_a_2812_, v_a_2813_, v_a_2814_, v_a_2815_, v_a_2816_, v_a_2817_);
if (lean_obj_tag(v___x_2958_) == 0)
{
lean_object* v_a_2959_; 
v_a_2959_ = lean_ctor_get(v___x_2958_, 0);
lean_inc(v_a_2959_);
lean_dec_ref_known(v___x_2958_, 1);
if (lean_obj_tag(v_a_2959_) == 1)
{
lean_object* v_val_2960_; lean_object* v___x_2961_; 
lean_dec(v_val_2906_);
v_val_2960_ = lean_ctor_get(v_a_2959_, 0);
lean_inc(v_val_2960_);
lean_dec_ref_known(v_a_2959_, 1);
lean_inc_ref(v_e_2806_);
v___x_2961_ = l_Lean_Meta_Grind_Arith_CommRing_sreify_x3f(v_e_2806_, v_val_2960_, v_a_2808_, v_a_2809_, v_a_2810_, v_a_2811_, v_a_2812_, v_a_2813_, v_a_2814_, v_a_2815_, v_a_2816_, v_a_2817_);
if (lean_obj_tag(v___x_2961_) == 0)
{
lean_object* v_a_2962_; lean_object* v___x_2964_; uint8_t v_isShared_2965_; uint8_t v_isSharedCheck_2997_; 
v_a_2962_ = lean_ctor_get(v___x_2961_, 0);
v_isSharedCheck_2997_ = !lean_is_exclusive(v___x_2961_);
if (v_isSharedCheck_2997_ == 0)
{
v___x_2964_ = v___x_2961_;
v_isShared_2965_ = v_isSharedCheck_2997_;
goto v_resetjp_2963_;
}
else
{
lean_inc(v_a_2962_);
lean_dec(v___x_2961_);
v___x_2964_ = lean_box(0);
v_isShared_2965_ = v_isSharedCheck_2997_;
goto v_resetjp_2963_;
}
v_resetjp_2963_:
{
if (lean_obj_tag(v_a_2962_) == 1)
{
lean_object* v_toCold_2966_; lean_object* v_options_2967_; lean_object* v_val_2968_; lean_object* v_inheritedTraceOptions_2969_; uint8_t v_hasTrace_2970_; lean_object* v___f_2971_; 
lean_del_object(v___x_2964_);
v_toCold_2966_ = lean_ctor_get(v_a_2816_, 0);
v_options_2967_ = lean_ctor_get(v_toCold_2966_, 2);
v_val_2968_ = lean_ctor_get(v_a_2962_, 0);
lean_inc(v_val_2968_);
lean_dec_ref_known(v_a_2962_, 1);
v_inheritedTraceOptions_2969_ = lean_ctor_get(v_toCold_2966_, 11);
v_hasTrace_2970_ = lean_ctor_get_uint8(v_options_2967_, sizeof(void*)*1);
lean_inc_ref(v_e_2806_);
v___f_2971_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_internalize___lam__1), 3, 2);
lean_closure_set(v___f_2971_, 0, v_e_2806_);
lean_closure_set(v___f_2971_, 1, v_val_2968_);
if (v_hasTrace_2970_ == 0)
{
v___y_2837_ = v___f_2971_;
v___y_2838_ = v_val_2960_;
v___y_2839_ = v_a_2808_;
v___y_2840_ = v_a_2809_;
v___y_2841_ = v_a_2810_;
v___y_2842_ = v_a_2811_;
v___y_2843_ = v_a_2812_;
v___y_2844_ = v_a_2813_;
v___y_2845_ = v_a_2814_;
v___y_2846_ = v_a_2815_;
v___y_2847_ = v_a_2816_;
v___y_2848_ = v_a_2817_;
goto v___jp_2836_;
}
else
{
lean_object* v___x_2972_; lean_object* v___x_2973_; uint8_t v___x_2974_; 
v___x_2972_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__1));
v___x_2973_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__2, &l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__2_once, _init_l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__2);
v___x_2974_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2969_, v_options_2967_, v___x_2973_);
if (v___x_2974_ == 0)
{
v___y_2837_ = v___f_2971_;
v___y_2838_ = v_val_2960_;
v___y_2839_ = v_a_2808_;
v___y_2840_ = v_a_2809_;
v___y_2841_ = v_a_2810_;
v___y_2842_ = v_a_2811_;
v___y_2843_ = v_a_2812_;
v___y_2844_ = v_a_2813_;
v___y_2845_ = v_a_2814_;
v___y_2846_ = v_a_2815_;
v___y_2847_ = v_a_2816_;
v___y_2848_ = v_a_2817_;
goto v___jp_2836_;
}
else
{
lean_object* v___x_2975_; 
v___x_2975_ = l_Lean_Meta_Grind_updateLastTag(v_a_2808_, v_a_2809_, v_a_2810_, v_a_2811_, v_a_2812_, v_a_2813_, v_a_2814_, v_a_2815_, v_a_2816_, v_a_2817_);
if (lean_obj_tag(v___x_2975_) == 0)
{
lean_object* v___x_2977_; uint8_t v_isShared_2978_; uint8_t v_isSharedCheck_2991_; 
v_isSharedCheck_2991_ = !lean_is_exclusive(v___x_2975_);
if (v_isSharedCheck_2991_ == 0)
{
lean_object* v_unused_2992_; 
v_unused_2992_ = lean_ctor_get(v___x_2975_, 0);
lean_dec(v_unused_2992_);
v___x_2977_ = v___x_2975_;
v_isShared_2978_ = v_isSharedCheck_2991_;
goto v_resetjp_2976_;
}
else
{
lean_dec(v___x_2975_);
v___x_2977_ = lean_box(0);
v_isShared_2978_ = v_isSharedCheck_2991_;
goto v_resetjp_2976_;
}
v_resetjp_2976_:
{
lean_object* v___x_2979_; lean_object* v___x_2980_; lean_object* v___x_2982_; 
v___x_2979_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__8, &l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__8_once, _init_l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__8);
lean_inc(v_val_2960_);
v___x_2980_ = l_Nat_reprFast(v_val_2960_);
if (v_isShared_2978_ == 0)
{
lean_ctor_set_tag(v___x_2977_, 3);
lean_ctor_set(v___x_2977_, 0, v___x_2980_);
v___x_2982_ = v___x_2977_;
goto v_reusejp_2981_;
}
else
{
lean_object* v_reuseFailAlloc_2990_; 
v_reuseFailAlloc_2990_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2990_, 0, v___x_2980_);
v___x_2982_ = v_reuseFailAlloc_2990_;
goto v_reusejp_2981_;
}
v_reusejp_2981_:
{
lean_object* v___x_2983_; lean_object* v___x_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; lean_object* v___x_2987_; lean_object* v___x_2988_; lean_object* v___x_2989_; 
v___x_2983_ = l_Lean_MessageData_ofFormat(v___x_2982_);
v___x_2984_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2984_, 0, v___x_2979_);
lean_ctor_set(v___x_2984_, 1, v___x_2983_);
v___x_2985_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__6, &l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__6_once, _init_l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__6);
v___x_2986_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2986_, 0, v___x_2984_);
lean_ctor_set(v___x_2986_, 1, v___x_2985_);
lean_inc_ref(v_e_2806_);
v___x_2987_ = l_Lean_MessageData_ofExpr(v_e_2806_);
v___x_2988_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2988_, 0, v___x_2986_);
lean_ctor_set(v___x_2988_, 1, v___x_2987_);
v___x_2989_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__1___redArg(v___x_2972_, v___x_2988_, v_a_2814_, v_a_2815_, v_a_2816_, v_a_2817_);
if (lean_obj_tag(v___x_2989_) == 0)
{
lean_dec_ref_known(v___x_2989_, 1);
v___y_2837_ = v___f_2971_;
v___y_2838_ = v_val_2960_;
v___y_2839_ = v_a_2808_;
v___y_2840_ = v_a_2809_;
v___y_2841_ = v_a_2810_;
v___y_2842_ = v_a_2811_;
v___y_2843_ = v_a_2812_;
v___y_2844_ = v_a_2813_;
v___y_2845_ = v_a_2814_;
v___y_2846_ = v_a_2815_;
v___y_2847_ = v_a_2816_;
v___y_2848_ = v_a_2817_;
goto v___jp_2836_;
}
else
{
lean_dec_ref(v___f_2971_);
lean_dec(v_val_2960_);
lean_dec_ref(v_e_2806_);
return v___x_2989_;
}
}
}
}
else
{
lean_dec_ref(v___f_2971_);
lean_dec(v_val_2960_);
lean_dec_ref(v_e_2806_);
return v___x_2975_;
}
}
}
}
else
{
lean_object* v___x_2993_; lean_object* v___x_2995_; 
lean_dec(v_a_2962_);
lean_dec(v_val_2960_);
lean_dec_ref(v_e_2806_);
v___x_2993_ = lean_box(0);
if (v_isShared_2965_ == 0)
{
lean_ctor_set(v___x_2964_, 0, v___x_2993_);
v___x_2995_ = v___x_2964_;
goto v_reusejp_2994_;
}
else
{
lean_object* v_reuseFailAlloc_2996_; 
v_reuseFailAlloc_2996_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2996_, 0, v___x_2993_);
v___x_2995_ = v_reuseFailAlloc_2996_;
goto v_reusejp_2994_;
}
v_reusejp_2994_:
{
return v___x_2995_;
}
}
}
}
else
{
lean_object* v_a_2998_; lean_object* v___x_3000_; uint8_t v_isShared_3001_; uint8_t v_isSharedCheck_3005_; 
lean_dec(v_val_2960_);
lean_dec_ref(v_e_2806_);
v_a_2998_ = lean_ctor_get(v___x_2961_, 0);
v_isSharedCheck_3005_ = !lean_is_exclusive(v___x_2961_);
if (v_isSharedCheck_3005_ == 0)
{
v___x_3000_ = v___x_2961_;
v_isShared_3001_ = v_isSharedCheck_3005_;
goto v_resetjp_2999_;
}
else
{
lean_inc(v_a_2998_);
lean_dec(v___x_2961_);
v___x_3000_ = lean_box(0);
v_isShared_3001_ = v_isSharedCheck_3005_;
goto v_resetjp_2999_;
}
v_resetjp_2999_:
{
lean_object* v___x_3003_; 
if (v_isShared_3001_ == 0)
{
v___x_3003_ = v___x_3000_;
goto v_reusejp_3002_;
}
else
{
lean_object* v_reuseFailAlloc_3004_; 
v_reuseFailAlloc_3004_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3004_, 0, v_a_2998_);
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
else
{
lean_object* v___x_3006_; 
lean_dec(v_a_2959_);
lean_inc(v_val_2906_);
v___x_3006_ = l_Lean_Meta_Grind_Arith_CommRing_getNonCommRingId_x3f___redArg(v_val_2906_, v_a_2812_, v_a_2813_, v_a_2814_, v_a_2815_, v_a_2816_, v_a_2817_);
if (lean_obj_tag(v___x_3006_) == 0)
{
lean_object* v_a_3007_; 
v_a_3007_ = lean_ctor_get(v___x_3006_, 0);
lean_inc(v_a_3007_);
lean_dec_ref_known(v___x_3006_, 1);
if (lean_obj_tag(v_a_3007_) == 1)
{
lean_object* v_val_3008_; lean_object* v___x_3009_; 
lean_dec(v_val_2906_);
v_val_3008_ = lean_ctor_get(v_a_3007_, 0);
lean_inc(v_val_3008_);
lean_dec_ref_known(v_a_3007_, 1);
lean_inc_ref(v_e_2806_);
v___x_3009_ = l_Lean_Meta_Grind_Arith_CommRing_ncreify_x3f(v_e_2806_, v_ring_2893_, v_val_3008_, v_a_2808_, v_a_2809_, v_a_2810_, v_a_2811_, v_a_2812_, v_a_2813_, v_a_2814_, v_a_2815_, v_a_2816_, v_a_2817_);
if (lean_obj_tag(v___x_3009_) == 0)
{
lean_object* v_a_3010_; lean_object* v___x_3012_; uint8_t v_isShared_3013_; uint8_t v_isSharedCheck_3045_; 
v_a_3010_ = lean_ctor_get(v___x_3009_, 0);
v_isSharedCheck_3045_ = !lean_is_exclusive(v___x_3009_);
if (v_isSharedCheck_3045_ == 0)
{
v___x_3012_ = v___x_3009_;
v_isShared_3013_ = v_isSharedCheck_3045_;
goto v_resetjp_3011_;
}
else
{
lean_inc(v_a_3010_);
lean_dec(v___x_3009_);
v___x_3012_ = lean_box(0);
v_isShared_3013_ = v_isSharedCheck_3045_;
goto v_resetjp_3011_;
}
v_resetjp_3011_:
{
if (lean_obj_tag(v_a_3010_) == 1)
{
lean_object* v_toCold_3014_; lean_object* v_options_3015_; lean_object* v_val_3016_; lean_object* v_inheritedTraceOptions_3017_; uint8_t v_hasTrace_3018_; lean_object* v___f_3019_; 
lean_del_object(v___x_3012_);
v_toCold_3014_ = lean_ctor_get(v_a_2816_, 0);
v_options_3015_ = lean_ctor_get(v_toCold_3014_, 2);
v_val_3016_ = lean_ctor_get(v_a_3010_, 0);
lean_inc(v_val_3016_);
lean_dec_ref_known(v_a_3010_, 1);
v_inheritedTraceOptions_3017_ = lean_ctor_get(v_toCold_3014_, 11);
v_hasTrace_3018_ = lean_ctor_get_uint8(v_options_3015_, sizeof(void*)*1);
lean_inc_ref(v_e_2806_);
v___f_3019_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_internalize___lam__2), 3, 2);
lean_closure_set(v___f_3019_, 0, v_e_2806_);
lean_closure_set(v___f_3019_, 1, v_val_3016_);
if (v_hasTrace_3018_ == 0)
{
v___y_2872_ = v___f_3019_;
v___y_2873_ = v_val_3008_;
v___y_2874_ = v_a_2808_;
v___y_2875_ = v_a_2809_;
v___y_2876_ = v_a_2810_;
v___y_2877_ = v_a_2811_;
v___y_2878_ = v_a_2812_;
v___y_2879_ = v_a_2813_;
v___y_2880_ = v_a_2814_;
v___y_2881_ = v_a_2815_;
v___y_2882_ = v_a_2816_;
v___y_2883_ = v_a_2817_;
goto v___jp_2871_;
}
else
{
lean_object* v___x_3020_; lean_object* v___x_3021_; uint8_t v___x_3022_; 
v___x_3020_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__1));
v___x_3021_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__2, &l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__2_once, _init_l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__2);
v___x_3022_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3017_, v_options_3015_, v___x_3021_);
if (v___x_3022_ == 0)
{
v___y_2872_ = v___f_3019_;
v___y_2873_ = v_val_3008_;
v___y_2874_ = v_a_2808_;
v___y_2875_ = v_a_2809_;
v___y_2876_ = v_a_2810_;
v___y_2877_ = v_a_2811_;
v___y_2878_ = v_a_2812_;
v___y_2879_ = v_a_2813_;
v___y_2880_ = v_a_2814_;
v___y_2881_ = v_a_2815_;
v___y_2882_ = v_a_2816_;
v___y_2883_ = v_a_2817_;
goto v___jp_2871_;
}
else
{
lean_object* v___x_3023_; 
v___x_3023_ = l_Lean_Meta_Grind_updateLastTag(v_a_2808_, v_a_2809_, v_a_2810_, v_a_2811_, v_a_2812_, v_a_2813_, v_a_2814_, v_a_2815_, v_a_2816_, v_a_2817_);
if (lean_obj_tag(v___x_3023_) == 0)
{
lean_object* v___x_3025_; uint8_t v_isShared_3026_; uint8_t v_isSharedCheck_3039_; 
v_isSharedCheck_3039_ = !lean_is_exclusive(v___x_3023_);
if (v_isSharedCheck_3039_ == 0)
{
lean_object* v_unused_3040_; 
v_unused_3040_ = lean_ctor_get(v___x_3023_, 0);
lean_dec(v_unused_3040_);
v___x_3025_ = v___x_3023_;
v_isShared_3026_ = v_isSharedCheck_3039_;
goto v_resetjp_3024_;
}
else
{
lean_dec(v___x_3023_);
v___x_3025_ = lean_box(0);
v_isShared_3026_ = v_isSharedCheck_3039_;
goto v_resetjp_3024_;
}
v_resetjp_3024_:
{
lean_object* v___x_3027_; lean_object* v___x_3028_; lean_object* v___x_3030_; 
v___x_3027_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__10, &l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__10_once, _init_l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__10);
lean_inc(v_val_3008_);
v___x_3028_ = l_Nat_reprFast(v_val_3008_);
if (v_isShared_3026_ == 0)
{
lean_ctor_set_tag(v___x_3025_, 3);
lean_ctor_set(v___x_3025_, 0, v___x_3028_);
v___x_3030_ = v___x_3025_;
goto v_reusejp_3029_;
}
else
{
lean_object* v_reuseFailAlloc_3038_; 
v_reuseFailAlloc_3038_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3038_, 0, v___x_3028_);
v___x_3030_ = v_reuseFailAlloc_3038_;
goto v_reusejp_3029_;
}
v_reusejp_3029_:
{
lean_object* v___x_3031_; lean_object* v___x_3032_; lean_object* v___x_3033_; lean_object* v___x_3034_; lean_object* v___x_3035_; lean_object* v___x_3036_; lean_object* v___x_3037_; 
v___x_3031_ = l_Lean_MessageData_ofFormat(v___x_3030_);
v___x_3032_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3032_, 0, v___x_3027_);
lean_ctor_set(v___x_3032_, 1, v___x_3031_);
v___x_3033_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__6, &l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__6_once, _init_l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__6);
v___x_3034_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3034_, 0, v___x_3032_);
lean_ctor_set(v___x_3034_, 1, v___x_3033_);
lean_inc_ref(v_e_2806_);
v___x_3035_ = l_Lean_MessageData_ofExpr(v_e_2806_);
v___x_3036_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3036_, 0, v___x_3034_);
lean_ctor_set(v___x_3036_, 1, v___x_3035_);
v___x_3037_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__2___redArg(v___x_3020_, v___x_3036_, v_a_2814_, v_a_2815_, v_a_2816_, v_a_2817_);
if (lean_obj_tag(v___x_3037_) == 0)
{
lean_dec_ref_known(v___x_3037_, 1);
v___y_2872_ = v___f_3019_;
v___y_2873_ = v_val_3008_;
v___y_2874_ = v_a_2808_;
v___y_2875_ = v_a_2809_;
v___y_2876_ = v_a_2810_;
v___y_2877_ = v_a_2811_;
v___y_2878_ = v_a_2812_;
v___y_2879_ = v_a_2813_;
v___y_2880_ = v_a_2814_;
v___y_2881_ = v_a_2815_;
v___y_2882_ = v_a_2816_;
v___y_2883_ = v_a_2817_;
goto v___jp_2871_;
}
else
{
lean_dec_ref(v___f_3019_);
lean_dec(v_val_3008_);
lean_dec_ref(v_e_2806_);
return v___x_3037_;
}
}
}
}
else
{
lean_dec_ref(v___f_3019_);
lean_dec(v_val_3008_);
lean_dec_ref(v_e_2806_);
return v___x_3023_;
}
}
}
}
else
{
lean_object* v___x_3041_; lean_object* v___x_3043_; 
lean_dec(v_a_3010_);
lean_dec(v_val_3008_);
lean_dec_ref(v_e_2806_);
v___x_3041_ = lean_box(0);
if (v_isShared_3013_ == 0)
{
lean_ctor_set(v___x_3012_, 0, v___x_3041_);
v___x_3043_ = v___x_3012_;
goto v_reusejp_3042_;
}
else
{
lean_object* v_reuseFailAlloc_3044_; 
v_reuseFailAlloc_3044_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3044_, 0, v___x_3041_);
v___x_3043_ = v_reuseFailAlloc_3044_;
goto v_reusejp_3042_;
}
v_reusejp_3042_:
{
return v___x_3043_;
}
}
}
}
else
{
lean_object* v_a_3046_; lean_object* v___x_3048_; uint8_t v_isShared_3049_; uint8_t v_isSharedCheck_3053_; 
lean_dec(v_val_3008_);
lean_dec_ref(v_e_2806_);
v_a_3046_ = lean_ctor_get(v___x_3009_, 0);
v_isSharedCheck_3053_ = !lean_is_exclusive(v___x_3009_);
if (v_isSharedCheck_3053_ == 0)
{
v___x_3048_ = v___x_3009_;
v_isShared_3049_ = v_isSharedCheck_3053_;
goto v_resetjp_3047_;
}
else
{
lean_inc(v_a_3046_);
lean_dec(v___x_3009_);
v___x_3048_ = lean_box(0);
v_isShared_3049_ = v_isSharedCheck_3053_;
goto v_resetjp_3047_;
}
v_resetjp_3047_:
{
lean_object* v___x_3051_; 
if (v_isShared_3049_ == 0)
{
v___x_3051_ = v___x_3048_;
goto v_reusejp_3050_;
}
else
{
lean_object* v_reuseFailAlloc_3052_; 
v_reuseFailAlloc_3052_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3052_, 0, v_a_3046_);
v___x_3051_ = v_reuseFailAlloc_3052_;
goto v_reusejp_3050_;
}
v_reusejp_3050_:
{
return v___x_3051_;
}
}
}
}
else
{
lean_object* v___x_3054_; 
lean_dec(v_a_3007_);
v___x_3054_ = l_Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f___redArg(v_val_2906_, v_a_2812_, v_a_2813_, v_a_2814_, v_a_2815_, v_a_2816_, v_a_2817_);
if (lean_obj_tag(v___x_3054_) == 0)
{
lean_object* v_a_3055_; lean_object* v___x_3057_; uint8_t v_isShared_3058_; uint8_t v_isSharedCheck_3109_; 
v_a_3055_ = lean_ctor_get(v___x_3054_, 0);
v_isSharedCheck_3109_ = !lean_is_exclusive(v___x_3054_);
if (v_isSharedCheck_3109_ == 0)
{
v___x_3057_ = v___x_3054_;
v_isShared_3058_ = v_isSharedCheck_3109_;
goto v_resetjp_3056_;
}
else
{
lean_inc(v_a_3055_);
lean_dec(v___x_3054_);
v___x_3057_ = lean_box(0);
v_isShared_3058_ = v_isSharedCheck_3109_;
goto v_resetjp_3056_;
}
v_resetjp_3056_:
{
if (lean_obj_tag(v_a_3055_) == 1)
{
lean_object* v_val_3059_; lean_object* v___x_3060_; 
lean_del_object(v___x_3057_);
v_val_3059_ = lean_ctor_get(v_a_3055_, 0);
lean_inc(v_val_3059_);
lean_dec_ref_known(v_a_3055_, 1);
lean_inc_ref(v_e_2806_);
v___x_3060_ = l_Lean_Meta_Grind_Arith_CommRing_ncsreify_x3f(v_e_2806_, v_val_3059_, v_a_2808_, v_a_2809_, v_a_2810_, v_a_2811_, v_a_2812_, v_a_2813_, v_a_2814_, v_a_2815_, v_a_2816_, v_a_2817_);
if (lean_obj_tag(v___x_3060_) == 0)
{
lean_object* v_a_3061_; lean_object* v___x_3063_; uint8_t v_isShared_3064_; uint8_t v_isSharedCheck_3096_; 
v_a_3061_ = lean_ctor_get(v___x_3060_, 0);
v_isSharedCheck_3096_ = !lean_is_exclusive(v___x_3060_);
if (v_isSharedCheck_3096_ == 0)
{
v___x_3063_ = v___x_3060_;
v_isShared_3064_ = v_isSharedCheck_3096_;
goto v_resetjp_3062_;
}
else
{
lean_inc(v_a_3061_);
lean_dec(v___x_3060_);
v___x_3063_ = lean_box(0);
v_isShared_3064_ = v_isSharedCheck_3096_;
goto v_resetjp_3062_;
}
v_resetjp_3062_:
{
if (lean_obj_tag(v_a_3061_) == 1)
{
lean_object* v_toCold_3065_; lean_object* v_options_3066_; lean_object* v_val_3067_; lean_object* v_inheritedTraceOptions_3068_; uint8_t v_hasTrace_3069_; lean_object* v___f_3070_; 
lean_del_object(v___x_3063_);
v_toCold_3065_ = lean_ctor_get(v_a_2816_, 0);
v_options_3066_ = lean_ctor_get(v_toCold_3065_, 2);
v_val_3067_ = lean_ctor_get(v_a_3061_, 0);
lean_inc(v_val_3067_);
lean_dec_ref_known(v_a_3061_, 1);
v_inheritedTraceOptions_3068_ = lean_ctor_get(v_toCold_3065_, 11);
v_hasTrace_3069_ = lean_ctor_get_uint8(v_options_3066_, sizeof(void*)*1);
lean_inc_ref(v_e_2806_);
v___f_3070_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_internalize___lam__1), 3, 2);
lean_closure_set(v___f_3070_, 0, v_e_2806_);
lean_closure_set(v___f_3070_, 1, v_val_3067_);
if (v_hasTrace_3069_ == 0)
{
v___y_2820_ = v___f_3070_;
v___y_2821_ = v_val_3059_;
v___y_2822_ = v_a_2808_;
v___y_2823_ = v_a_2809_;
v___y_2824_ = v_a_2810_;
v___y_2825_ = v_a_2811_;
v___y_2826_ = v_a_2812_;
v___y_2827_ = v_a_2813_;
v___y_2828_ = v_a_2814_;
v___y_2829_ = v_a_2815_;
v___y_2830_ = v_a_2816_;
v___y_2831_ = v_a_2817_;
goto v___jp_2819_;
}
else
{
lean_object* v___x_3071_; lean_object* v___x_3072_; uint8_t v___x_3073_; 
v___x_3071_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__1));
v___x_3072_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__2, &l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__2_once, _init_l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__2);
v___x_3073_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3068_, v_options_3066_, v___x_3072_);
if (v___x_3073_ == 0)
{
v___y_2820_ = v___f_3070_;
v___y_2821_ = v_val_3059_;
v___y_2822_ = v_a_2808_;
v___y_2823_ = v_a_2809_;
v___y_2824_ = v_a_2810_;
v___y_2825_ = v_a_2811_;
v___y_2826_ = v_a_2812_;
v___y_2827_ = v_a_2813_;
v___y_2828_ = v_a_2814_;
v___y_2829_ = v_a_2815_;
v___y_2830_ = v_a_2816_;
v___y_2831_ = v_a_2817_;
goto v___jp_2819_;
}
else
{
lean_object* v___x_3074_; 
v___x_3074_ = l_Lean_Meta_Grind_updateLastTag(v_a_2808_, v_a_2809_, v_a_2810_, v_a_2811_, v_a_2812_, v_a_2813_, v_a_2814_, v_a_2815_, v_a_2816_, v_a_2817_);
if (lean_obj_tag(v___x_3074_) == 0)
{
lean_object* v___x_3076_; uint8_t v_isShared_3077_; uint8_t v_isSharedCheck_3090_; 
v_isSharedCheck_3090_ = !lean_is_exclusive(v___x_3074_);
if (v_isSharedCheck_3090_ == 0)
{
lean_object* v_unused_3091_; 
v_unused_3091_ = lean_ctor_get(v___x_3074_, 0);
lean_dec(v_unused_3091_);
v___x_3076_ = v___x_3074_;
v_isShared_3077_ = v_isSharedCheck_3090_;
goto v_resetjp_3075_;
}
else
{
lean_dec(v___x_3074_);
v___x_3076_ = lean_box(0);
v_isShared_3077_ = v_isSharedCheck_3090_;
goto v_resetjp_3075_;
}
v_resetjp_3075_:
{
lean_object* v___x_3078_; lean_object* v___x_3079_; lean_object* v___x_3081_; 
v___x_3078_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__12, &l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__12_once, _init_l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__12);
lean_inc(v_val_3059_);
v___x_3079_ = l_Nat_reprFast(v_val_3059_);
if (v_isShared_3077_ == 0)
{
lean_ctor_set_tag(v___x_3076_, 3);
lean_ctor_set(v___x_3076_, 0, v___x_3079_);
v___x_3081_ = v___x_3076_;
goto v_reusejp_3080_;
}
else
{
lean_object* v_reuseFailAlloc_3089_; 
v_reuseFailAlloc_3089_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3089_, 0, v___x_3079_);
v___x_3081_ = v_reuseFailAlloc_3089_;
goto v_reusejp_3080_;
}
v_reusejp_3080_:
{
lean_object* v___x_3082_; lean_object* v___x_3083_; lean_object* v___x_3084_; lean_object* v___x_3085_; lean_object* v___x_3086_; lean_object* v___x_3087_; lean_object* v___x_3088_; 
v___x_3082_ = l_Lean_MessageData_ofFormat(v___x_3081_);
v___x_3083_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3083_, 0, v___x_3078_);
lean_ctor_set(v___x_3083_, 1, v___x_3082_);
v___x_3084_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__6, &l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__6_once, _init_l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__6);
v___x_3085_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3085_, 0, v___x_3083_);
lean_ctor_set(v___x_3085_, 1, v___x_3084_);
lean_inc_ref(v_e_2806_);
v___x_3086_ = l_Lean_MessageData_ofExpr(v_e_2806_);
v___x_3087_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3087_, 0, v___x_3085_);
lean_ctor_set(v___x_3087_, 1, v___x_3086_);
v___x_3088_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__3___redArg(v___x_3071_, v___x_3087_, v_a_2814_, v_a_2815_, v_a_2816_, v_a_2817_);
if (lean_obj_tag(v___x_3088_) == 0)
{
lean_dec_ref_known(v___x_3088_, 1);
v___y_2820_ = v___f_3070_;
v___y_2821_ = v_val_3059_;
v___y_2822_ = v_a_2808_;
v___y_2823_ = v_a_2809_;
v___y_2824_ = v_a_2810_;
v___y_2825_ = v_a_2811_;
v___y_2826_ = v_a_2812_;
v___y_2827_ = v_a_2813_;
v___y_2828_ = v_a_2814_;
v___y_2829_ = v_a_2815_;
v___y_2830_ = v_a_2816_;
v___y_2831_ = v_a_2817_;
goto v___jp_2819_;
}
else
{
lean_dec_ref(v___f_3070_);
lean_dec(v_val_3059_);
lean_dec_ref(v_e_2806_);
return v___x_3088_;
}
}
}
}
else
{
lean_dec_ref(v___f_3070_);
lean_dec(v_val_3059_);
lean_dec_ref(v_e_2806_);
return v___x_3074_;
}
}
}
}
else
{
lean_object* v___x_3092_; lean_object* v___x_3094_; 
lean_dec(v_a_3061_);
lean_dec(v_val_3059_);
lean_dec_ref(v_e_2806_);
v___x_3092_ = lean_box(0);
if (v_isShared_3064_ == 0)
{
lean_ctor_set(v___x_3063_, 0, v___x_3092_);
v___x_3094_ = v___x_3063_;
goto v_reusejp_3093_;
}
else
{
lean_object* v_reuseFailAlloc_3095_; 
v_reuseFailAlloc_3095_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3095_, 0, v___x_3092_);
v___x_3094_ = v_reuseFailAlloc_3095_;
goto v_reusejp_3093_;
}
v_reusejp_3093_:
{
return v___x_3094_;
}
}
}
}
else
{
lean_object* v_a_3097_; lean_object* v___x_3099_; uint8_t v_isShared_3100_; uint8_t v_isSharedCheck_3104_; 
lean_dec(v_val_3059_);
lean_dec_ref(v_e_2806_);
v_a_3097_ = lean_ctor_get(v___x_3060_, 0);
v_isSharedCheck_3104_ = !lean_is_exclusive(v___x_3060_);
if (v_isSharedCheck_3104_ == 0)
{
v___x_3099_ = v___x_3060_;
v_isShared_3100_ = v_isSharedCheck_3104_;
goto v_resetjp_3098_;
}
else
{
lean_inc(v_a_3097_);
lean_dec(v___x_3060_);
v___x_3099_ = lean_box(0);
v_isShared_3100_ = v_isSharedCheck_3104_;
goto v_resetjp_3098_;
}
v_resetjp_3098_:
{
lean_object* v___x_3102_; 
if (v_isShared_3100_ == 0)
{
v___x_3102_ = v___x_3099_;
goto v_reusejp_3101_;
}
else
{
lean_object* v_reuseFailAlloc_3103_; 
v_reuseFailAlloc_3103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3103_, 0, v_a_3097_);
v___x_3102_ = v_reuseFailAlloc_3103_;
goto v_reusejp_3101_;
}
v_reusejp_3101_:
{
return v___x_3102_;
}
}
}
}
else
{
lean_object* v___x_3105_; lean_object* v___x_3107_; 
lean_dec(v_a_3055_);
lean_dec_ref(v_e_2806_);
v___x_3105_ = lean_box(0);
if (v_isShared_3058_ == 0)
{
lean_ctor_set(v___x_3057_, 0, v___x_3105_);
v___x_3107_ = v___x_3057_;
goto v_reusejp_3106_;
}
else
{
lean_object* v_reuseFailAlloc_3108_; 
v_reuseFailAlloc_3108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3108_, 0, v___x_3105_);
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
else
{
lean_object* v_a_3110_; lean_object* v___x_3112_; uint8_t v_isShared_3113_; uint8_t v_isSharedCheck_3117_; 
lean_dec_ref(v_e_2806_);
v_a_3110_ = lean_ctor_get(v___x_3054_, 0);
v_isSharedCheck_3117_ = !lean_is_exclusive(v___x_3054_);
if (v_isSharedCheck_3117_ == 0)
{
v___x_3112_ = v___x_3054_;
v_isShared_3113_ = v_isSharedCheck_3117_;
goto v_resetjp_3111_;
}
else
{
lean_inc(v_a_3110_);
lean_dec(v___x_3054_);
v___x_3112_ = lean_box(0);
v_isShared_3113_ = v_isSharedCheck_3117_;
goto v_resetjp_3111_;
}
v_resetjp_3111_:
{
lean_object* v___x_3115_; 
if (v_isShared_3113_ == 0)
{
v___x_3115_ = v___x_3112_;
goto v_reusejp_3114_;
}
else
{
lean_object* v_reuseFailAlloc_3116_; 
v_reuseFailAlloc_3116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3116_, 0, v_a_3110_);
v___x_3115_ = v_reuseFailAlloc_3116_;
goto v_reusejp_3114_;
}
v_reusejp_3114_:
{
return v___x_3115_;
}
}
}
}
}
else
{
lean_object* v_a_3118_; lean_object* v___x_3120_; uint8_t v_isShared_3121_; uint8_t v_isSharedCheck_3125_; 
lean_dec(v_val_2906_);
lean_dec_ref(v_e_2806_);
v_a_3118_ = lean_ctor_get(v___x_3006_, 0);
v_isSharedCheck_3125_ = !lean_is_exclusive(v___x_3006_);
if (v_isSharedCheck_3125_ == 0)
{
v___x_3120_ = v___x_3006_;
v_isShared_3121_ = v_isSharedCheck_3125_;
goto v_resetjp_3119_;
}
else
{
lean_inc(v_a_3118_);
lean_dec(v___x_3006_);
v___x_3120_ = lean_box(0);
v_isShared_3121_ = v_isSharedCheck_3125_;
goto v_resetjp_3119_;
}
v_resetjp_3119_:
{
lean_object* v___x_3123_; 
if (v_isShared_3121_ == 0)
{
v___x_3123_ = v___x_3120_;
goto v_reusejp_3122_;
}
else
{
lean_object* v_reuseFailAlloc_3124_; 
v_reuseFailAlloc_3124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3124_, 0, v_a_3118_);
v___x_3123_ = v_reuseFailAlloc_3124_;
goto v_reusejp_3122_;
}
v_reusejp_3122_:
{
return v___x_3123_;
}
}
}
}
}
else
{
lean_object* v_a_3126_; lean_object* v___x_3128_; uint8_t v_isShared_3129_; uint8_t v_isSharedCheck_3133_; 
lean_dec(v_val_2906_);
lean_dec_ref(v_e_2806_);
v_a_3126_ = lean_ctor_get(v___x_2958_, 0);
v_isSharedCheck_3133_ = !lean_is_exclusive(v___x_2958_);
if (v_isSharedCheck_3133_ == 0)
{
v___x_3128_ = v___x_2958_;
v_isShared_3129_ = v_isSharedCheck_3133_;
goto v_resetjp_3127_;
}
else
{
lean_inc(v_a_3126_);
lean_dec(v___x_2958_);
v___x_3128_ = lean_box(0);
v_isShared_3129_ = v_isSharedCheck_3133_;
goto v_resetjp_3127_;
}
v_resetjp_3127_:
{
lean_object* v___x_3131_; 
if (v_isShared_3129_ == 0)
{
v___x_3131_ = v___x_3128_;
goto v_reusejp_3130_;
}
else
{
lean_object* v_reuseFailAlloc_3132_; 
v_reuseFailAlloc_3132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3132_, 0, v_a_3126_);
v___x_3131_ = v_reuseFailAlloc_3132_;
goto v_reusejp_3130_;
}
v_reusejp_3130_:
{
return v___x_3131_;
}
}
}
}
}
else
{
lean_object* v_a_3134_; lean_object* v___x_3136_; uint8_t v_isShared_3137_; uint8_t v_isSharedCheck_3141_; 
lean_dec(v_val_2906_);
lean_dec_ref(v_e_2806_);
v_a_3134_ = lean_ctor_get(v___x_2909_, 0);
v_isSharedCheck_3141_ = !lean_is_exclusive(v___x_2909_);
if (v_isSharedCheck_3141_ == 0)
{
v___x_3136_ = v___x_2909_;
v_isShared_3137_ = v_isSharedCheck_3141_;
goto v_resetjp_3135_;
}
else
{
lean_inc(v_a_3134_);
lean_dec(v___x_2909_);
v___x_3136_ = lean_box(0);
v_isShared_3137_ = v_isSharedCheck_3141_;
goto v_resetjp_3135_;
}
v_resetjp_3135_:
{
lean_object* v___x_3139_; 
if (v_isShared_3137_ == 0)
{
v___x_3139_ = v___x_3136_;
goto v_reusejp_3138_;
}
else
{
lean_object* v_reuseFailAlloc_3140_; 
v_reuseFailAlloc_3140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3140_, 0, v_a_3134_);
v___x_3139_ = v_reuseFailAlloc_3140_;
goto v_reusejp_3138_;
}
v_reusejp_3138_:
{
return v___x_3139_;
}
}
}
}
}
else
{
lean_object* v___x_3168_; lean_object* v___x_3170_; 
lean_dec(v___x_2905_);
lean_dec_ref(v_e_2806_);
v___x_3168_ = lean_box(0);
if (v_isShared_2903_ == 0)
{
lean_ctor_set(v___x_2902_, 0, v___x_3168_);
v___x_3170_ = v___x_2902_;
goto v_reusejp_3169_;
}
else
{
lean_object* v_reuseFailAlloc_3171_; 
v_reuseFailAlloc_3171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3171_, 0, v___x_3168_);
v___x_3170_ = v_reuseFailAlloc_3171_;
goto v_reusejp_3169_;
}
v_reusejp_3169_:
{
return v___x_3170_;
}
}
}
else
{
lean_object* v___x_3172_; lean_object* v___x_3174_; 
lean_dec_ref(v_e_2806_);
v___x_3172_ = lean_box(0);
if (v_isShared_2903_ == 0)
{
lean_ctor_set(v___x_2902_, 0, v___x_3172_);
v___x_3174_ = v___x_2902_;
goto v_reusejp_3173_;
}
else
{
lean_object* v_reuseFailAlloc_3175_; 
v_reuseFailAlloc_3175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3175_, 0, v___x_3172_);
v___x_3174_ = v_reuseFailAlloc_3175_;
goto v_reusejp_3173_;
}
v_reusejp_3173_:
{
return v___x_3174_;
}
}
}
}
else
{
lean_object* v_a_3177_; lean_object* v___x_3179_; uint8_t v_isShared_3180_; uint8_t v_isSharedCheck_3184_; 
lean_dec_ref(v_e_2806_);
v_a_3177_ = lean_ctor_get(v___x_2899_, 0);
v_isSharedCheck_3184_ = !lean_is_exclusive(v___x_2899_);
if (v_isSharedCheck_3184_ == 0)
{
v___x_3179_ = v___x_2899_;
v_isShared_3180_ = v_isSharedCheck_3184_;
goto v_resetjp_3178_;
}
else
{
lean_inc(v_a_3177_);
lean_dec(v___x_2899_);
v___x_3179_ = lean_box(0);
v_isShared_3180_ = v_isSharedCheck_3184_;
goto v_resetjp_3178_;
}
v_resetjp_3178_:
{
lean_object* v___x_3182_; 
if (v_isShared_3180_ == 0)
{
v___x_3182_ = v___x_3179_;
goto v_reusejp_3181_;
}
else
{
lean_object* v_reuseFailAlloc_3183_; 
v_reuseFailAlloc_3183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3183_, 0, v_a_3177_);
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
else
{
lean_object* v___x_3185_; lean_object* v___x_3187_; 
lean_dec_ref(v_e_2806_);
v___x_3185_ = lean_box(0);
if (v_isShared_2892_ == 0)
{
lean_ctor_set(v___x_2891_, 0, v___x_3185_);
v___x_3187_ = v___x_2891_;
goto v_reusejp_3186_;
}
else
{
lean_object* v_reuseFailAlloc_3188_; 
v_reuseFailAlloc_3188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3188_, 0, v___x_3185_);
v___x_3187_ = v_reuseFailAlloc_3188_;
goto v_reusejp_3186_;
}
v_reusejp_3186_:
{
return v___x_3187_;
}
}
}
}
}
else
{
lean_object* v_a_3190_; lean_object* v___x_3192_; uint8_t v_isShared_3193_; uint8_t v_isSharedCheck_3197_; 
lean_dec_ref(v_e_2806_);
v_a_3190_ = lean_ctor_get(v___x_2888_, 0);
v_isSharedCheck_3197_ = !lean_is_exclusive(v___x_2888_);
if (v_isSharedCheck_3197_ == 0)
{
v___x_3192_ = v___x_2888_;
v_isShared_3193_ = v_isSharedCheck_3197_;
goto v_resetjp_3191_;
}
else
{
lean_inc(v_a_3190_);
lean_dec(v___x_2888_);
v___x_3192_ = lean_box(0);
v_isShared_3193_ = v_isSharedCheck_3197_;
goto v_resetjp_3191_;
}
v_resetjp_3191_:
{
lean_object* v___x_3195_; 
if (v_isShared_3193_ == 0)
{
v___x_3195_ = v___x_3192_;
goto v_reusejp_3194_;
}
else
{
lean_object* v_reuseFailAlloc_3196_; 
v_reuseFailAlloc_3196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3196_, 0, v_a_3190_);
v___x_3195_ = v_reuseFailAlloc_3196_;
goto v_reusejp_3194_;
}
v_reusejp_3194_:
{
return v___x_3195_;
}
}
}
v___jp_2819_:
{
lean_object* v___x_2832_; 
lean_inc_ref(v_e_2806_);
v___x_2832_ = l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId___redArg(v_e_2806_, v___y_2821_, v___y_2822_, v___y_2826_, v___y_2827_, v___y_2828_, v___y_2829_, v___y_2830_, v___y_2831_);
if (lean_obj_tag(v___x_2832_) == 0)
{
lean_object* v___x_2833_; lean_object* v___x_2834_; 
lean_dec_ref_known(v___x_2832_, 1);
v___x_2833_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_2834_ = l_Lean_Meta_Grind_SolverExtension_markTerm___redArg(v___x_2833_, v_e_2806_, v___y_2822_, v___y_2823_, v___y_2824_, v___y_2825_, v___y_2826_, v___y_2827_, v___y_2828_, v___y_2829_, v___y_2830_, v___y_2831_);
if (lean_obj_tag(v___x_2834_) == 0)
{
lean_object* v___x_2835_; 
lean_dec_ref_known(v___x_2834_, 1);
v___x_2835_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_modifySemiringState___redArg(v___y_2820_, v___y_2821_, v___y_2822_);
lean_dec(v___y_2821_);
return v___x_2835_;
}
else
{
lean_dec(v___y_2821_);
lean_dec_ref(v___y_2820_);
return v___x_2834_;
}
}
else
{
lean_dec(v___y_2821_);
lean_dec_ref(v___y_2820_);
lean_dec_ref(v_e_2806_);
return v___x_2832_;
}
}
v___jp_2836_:
{
lean_object* v___x_2849_; 
lean_inc_ref(v_e_2806_);
v___x_2849_ = l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg(v_e_2806_, v___y_2838_, v___y_2839_, v___y_2843_, v___y_2844_, v___y_2845_, v___y_2846_, v___y_2847_, v___y_2848_);
if (lean_obj_tag(v___x_2849_) == 0)
{
lean_object* v___x_2850_; lean_object* v___x_2851_; 
lean_dec_ref_known(v___x_2849_, 1);
v___x_2850_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_2851_ = l_Lean_Meta_Grind_SolverExtension_markTerm___redArg(v___x_2850_, v_e_2806_, v___y_2839_, v___y_2840_, v___y_2841_, v___y_2842_, v___y_2843_, v___y_2844_, v___y_2845_, v___y_2846_, v___y_2847_, v___y_2848_);
if (lean_obj_tag(v___x_2851_) == 0)
{
lean_object* v___x_2852_; 
lean_dec_ref_known(v___x_2851_, 1);
v___x_2852_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifySemiringState___redArg(v___y_2837_, v___y_2838_, v___y_2839_);
lean_dec(v___y_2838_);
return v___x_2852_;
}
else
{
lean_dec(v___y_2838_);
lean_dec_ref(v___y_2837_);
return v___x_2851_;
}
}
else
{
lean_dec(v___y_2838_);
lean_dec_ref(v___y_2837_);
lean_dec_ref(v_e_2806_);
return v___x_2849_;
}
}
v___jp_2853_:
{
lean_object* v___x_2866_; 
lean_inc_ref(v_e_2806_);
v___x_2866_ = l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg(v_e_2806_, v___y_2855_, v___y_2856_, v___y_2860_, v___y_2861_, v___y_2862_, v___y_2863_, v___y_2864_, v___y_2865_);
if (lean_obj_tag(v___x_2866_) == 0)
{
lean_object* v___x_2867_; lean_object* v___x_2868_; 
lean_dec_ref_known(v___x_2866_, 1);
v___x_2867_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_2868_ = l_Lean_Meta_Grind_SolverExtension_markTerm___redArg(v___x_2867_, v_e_2806_, v___y_2856_, v___y_2857_, v___y_2858_, v___y_2859_, v___y_2860_, v___y_2861_, v___y_2862_, v___y_2863_, v___y_2864_, v___y_2865_);
if (lean_obj_tag(v___x_2868_) == 0)
{
lean_object* v___x_2869_; 
lean_dec_ref_known(v___x_2868_, 1);
v___x_2869_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRingState___redArg(v___y_2854_, v___y_2855_, v___y_2856_);
if (lean_obj_tag(v___x_2869_) == 0)
{
lean_object* v___x_2870_; 
lean_dec_ref_known(v___x_2869_, 1);
v___x_2870_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars(v___y_2855_, v___y_2856_, v___y_2857_, v___y_2858_, v___y_2859_, v___y_2860_, v___y_2861_, v___y_2862_, v___y_2863_, v___y_2864_, v___y_2865_);
lean_dec_ref(v___y_2855_);
return v___x_2870_;
}
else
{
lean_dec_ref(v___y_2855_);
return v___x_2869_;
}
}
else
{
lean_dec_ref(v___y_2855_);
lean_dec_ref(v___y_2854_);
return v___x_2868_;
}
}
else
{
lean_dec_ref(v___y_2855_);
lean_dec_ref(v___y_2854_);
lean_dec_ref(v_e_2806_);
return v___x_2866_;
}
}
v___jp_2871_:
{
lean_object* v___x_2884_; 
lean_inc_ref(v_e_2806_);
v___x_2884_ = l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId___redArg(v_e_2806_, v___y_2873_, v___y_2874_, v___y_2878_, v___y_2879_, v___y_2880_, v___y_2881_, v___y_2882_, v___y_2883_);
if (lean_obj_tag(v___x_2884_) == 0)
{
lean_object* v___x_2885_; lean_object* v___x_2886_; 
lean_dec_ref_known(v___x_2884_, 1);
v___x_2885_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_2886_ = l_Lean_Meta_Grind_SolverExtension_markTerm___redArg(v___x_2885_, v_e_2806_, v___y_2874_, v___y_2875_, v___y_2876_, v___y_2877_, v___y_2878_, v___y_2879_, v___y_2880_, v___y_2881_, v___y_2882_, v___y_2883_);
if (lean_obj_tag(v___x_2886_) == 0)
{
lean_object* v___x_2887_; 
lean_dec_ref_known(v___x_2886_, 1);
v___x_2887_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_modifyRingState___redArg(v___y_2872_, v___y_2873_, v___y_2874_);
lean_dec(v___y_2873_);
return v___x_2887_;
}
else
{
lean_dec(v___y_2873_);
lean_dec_ref(v___y_2872_);
return v___x_2886_;
}
}
else
{
lean_dec(v___y_2873_);
lean_dec_ref(v___y_2872_);
lean_dec_ref(v_e_2806_);
return v___x_2884_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_internalize___boxed(lean_object* v_e_3198_, lean_object* v_parent_x3f_3199_, lean_object* v_a_3200_, lean_object* v_a_3201_, lean_object* v_a_3202_, lean_object* v_a_3203_, lean_object* v_a_3204_, lean_object* v_a_3205_, lean_object* v_a_3206_, lean_object* v_a_3207_, lean_object* v_a_3208_, lean_object* v_a_3209_, lean_object* v_a_3210_){
_start:
{
lean_object* v_res_3211_; 
v_res_3211_ = l_Lean_Meta_Grind_Arith_CommRing_internalize(v_e_3198_, v_parent_x3f_3199_, v_a_3200_, v_a_3201_, v_a_3202_, v_a_3203_, v_a_3204_, v_a_3205_, v_a_3206_, v_a_3207_, v_a_3208_, v_a_3209_);
lean_dec(v_a_3209_);
lean_dec_ref(v_a_3208_);
lean_dec(v_a_3207_);
lean_dec_ref(v_a_3206_);
lean_dec(v_a_3205_);
lean_dec_ref(v_a_3204_);
lean_dec(v_a_3203_);
lean_dec_ref(v_a_3202_);
lean_dec(v_a_3201_);
lean_dec(v_a_3200_);
lean_dec(v_parent_x3f_3199_);
return v_res_3211_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0(lean_object* v_00_u03b2_3212_, lean_object* v_x_3213_, lean_object* v_x_3214_, lean_object* v_x_3215_){
_start:
{
lean_object* v___x_3216_; 
v___x_3216_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0___redArg(v_x_3213_, v_x_3214_, v_x_3215_);
return v___x_3216_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__1(lean_object* v_cls_3217_, lean_object* v_msg_3218_, lean_object* v___y_3219_, lean_object* v___y_3220_, lean_object* v___y_3221_, lean_object* v___y_3222_, lean_object* v___y_3223_, lean_object* v___y_3224_, lean_object* v___y_3225_, lean_object* v___y_3226_, lean_object* v___y_3227_, lean_object* v___y_3228_, lean_object* v___y_3229_){
_start:
{
lean_object* v___x_3231_; 
v___x_3231_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__1___redArg(v_cls_3217_, v_msg_3218_, v___y_3226_, v___y_3227_, v___y_3228_, v___y_3229_);
return v___x_3231_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__1___boxed(lean_object* v_cls_3232_, lean_object* v_msg_3233_, lean_object* v___y_3234_, lean_object* v___y_3235_, lean_object* v___y_3236_, lean_object* v___y_3237_, lean_object* v___y_3238_, lean_object* v___y_3239_, lean_object* v___y_3240_, lean_object* v___y_3241_, lean_object* v___y_3242_, lean_object* v___y_3243_, lean_object* v___y_3244_, lean_object* v___y_3245_){
_start:
{
lean_object* v_res_3246_; 
v_res_3246_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__1(v_cls_3232_, v_msg_3233_, v___y_3234_, v___y_3235_, v___y_3236_, v___y_3237_, v___y_3238_, v___y_3239_, v___y_3240_, v___y_3241_, v___y_3242_, v___y_3243_, v___y_3244_);
lean_dec(v___y_3244_);
lean_dec_ref(v___y_3243_);
lean_dec(v___y_3242_);
lean_dec_ref(v___y_3241_);
lean_dec(v___y_3240_);
lean_dec_ref(v___y_3239_);
lean_dec(v___y_3238_);
lean_dec_ref(v___y_3237_);
lean_dec(v___y_3236_);
lean_dec(v___y_3235_);
lean_dec(v___y_3234_);
return v_res_3246_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__2(lean_object* v_cls_3247_, lean_object* v_msg_3248_, lean_object* v___y_3249_, lean_object* v___y_3250_, lean_object* v___y_3251_, lean_object* v___y_3252_, lean_object* v___y_3253_, lean_object* v___y_3254_, lean_object* v___y_3255_, lean_object* v___y_3256_, lean_object* v___y_3257_, lean_object* v___y_3258_, lean_object* v___y_3259_){
_start:
{
lean_object* v___x_3261_; 
v___x_3261_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__2___redArg(v_cls_3247_, v_msg_3248_, v___y_3256_, v___y_3257_, v___y_3258_, v___y_3259_);
return v___x_3261_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__2___boxed(lean_object* v_cls_3262_, lean_object* v_msg_3263_, lean_object* v___y_3264_, lean_object* v___y_3265_, lean_object* v___y_3266_, lean_object* v___y_3267_, lean_object* v___y_3268_, lean_object* v___y_3269_, lean_object* v___y_3270_, lean_object* v___y_3271_, lean_object* v___y_3272_, lean_object* v___y_3273_, lean_object* v___y_3274_, lean_object* v___y_3275_){
_start:
{
lean_object* v_res_3276_; 
v_res_3276_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__2(v_cls_3262_, v_msg_3263_, v___y_3264_, v___y_3265_, v___y_3266_, v___y_3267_, v___y_3268_, v___y_3269_, v___y_3270_, v___y_3271_, v___y_3272_, v___y_3273_, v___y_3274_);
lean_dec(v___y_3274_);
lean_dec_ref(v___y_3273_);
lean_dec(v___y_3272_);
lean_dec_ref(v___y_3271_);
lean_dec(v___y_3270_);
lean_dec_ref(v___y_3269_);
lean_dec(v___y_3268_);
lean_dec_ref(v___y_3267_);
lean_dec(v___y_3266_);
lean_dec(v___y_3265_);
lean_dec(v___y_3264_);
return v_res_3276_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__3(lean_object* v_cls_3277_, lean_object* v_msg_3278_, lean_object* v___y_3279_, lean_object* v___y_3280_, lean_object* v___y_3281_, lean_object* v___y_3282_, lean_object* v___y_3283_, lean_object* v___y_3284_, lean_object* v___y_3285_, lean_object* v___y_3286_, lean_object* v___y_3287_, lean_object* v___y_3288_, lean_object* v___y_3289_){
_start:
{
lean_object* v___x_3291_; 
v___x_3291_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__3___redArg(v_cls_3277_, v_msg_3278_, v___y_3286_, v___y_3287_, v___y_3288_, v___y_3289_);
return v___x_3291_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__3___boxed(lean_object* v_cls_3292_, lean_object* v_msg_3293_, lean_object* v___y_3294_, lean_object* v___y_3295_, lean_object* v___y_3296_, lean_object* v___y_3297_, lean_object* v___y_3298_, lean_object* v___y_3299_, lean_object* v___y_3300_, lean_object* v___y_3301_, lean_object* v___y_3302_, lean_object* v___y_3303_, lean_object* v___y_3304_, lean_object* v___y_3305_){
_start:
{
lean_object* v_res_3306_; 
v_res_3306_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__3(v_cls_3292_, v_msg_3293_, v___y_3294_, v___y_3295_, v___y_3296_, v___y_3297_, v___y_3298_, v___y_3299_, v___y_3300_, v___y_3301_, v___y_3302_, v___y_3303_, v___y_3304_);
lean_dec(v___y_3304_);
lean_dec_ref(v___y_3303_);
lean_dec(v___y_3302_);
lean_dec_ref(v___y_3301_);
lean_dec(v___y_3300_);
lean_dec_ref(v___y_3299_);
lean_dec(v___y_3298_);
lean_dec_ref(v___y_3297_);
lean_dec(v___y_3296_);
lean_dec(v___y_3295_);
lean_dec(v___y_3294_);
return v_res_3306_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0(lean_object* v_00_u03b2_3307_, lean_object* v_x_3308_, size_t v_x_3309_, size_t v_x_3310_, lean_object* v_x_3311_, lean_object* v_x_3312_){
_start:
{
lean_object* v___x_3313_; 
v___x_3313_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0___redArg(v_x_3308_, v_x_3309_, v_x_3310_, v_x_3311_, v_x_3312_);
return v___x_3313_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3314_, lean_object* v_x_3315_, lean_object* v_x_3316_, lean_object* v_x_3317_, lean_object* v_x_3318_, lean_object* v_x_3319_){
_start:
{
size_t v_x_148159__boxed_3320_; size_t v_x_148160__boxed_3321_; lean_object* v_res_3322_; 
v_x_148159__boxed_3320_ = lean_unbox_usize(v_x_3316_);
lean_dec(v_x_3316_);
v_x_148160__boxed_3321_ = lean_unbox_usize(v_x_3317_);
lean_dec(v_x_3317_);
v_res_3322_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0(v_00_u03b2_3314_, v_x_3315_, v_x_148159__boxed_3320_, v_x_148160__boxed_3321_, v_x_3318_, v_x_3319_);
return v_res_3322_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_3323_, lean_object* v_n_3324_, lean_object* v_k_3325_, lean_object* v_v_3326_){
_start:
{
lean_object* v___x_3327_; 
v___x_3327_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0_spec__1___redArg(v_n_3324_, v_k_3325_, v_v_3326_);
return v___x_3327_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_3328_, size_t v_depth_3329_, lean_object* v_keys_3330_, lean_object* v_vals_3331_, lean_object* v_heq_3332_, lean_object* v_i_3333_, lean_object* v_entries_3334_){
_start:
{
lean_object* v___x_3335_; 
v___x_3335_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0_spec__2___redArg(v_depth_3329_, v_keys_3330_, v_vals_3331_, v_i_3333_, v_entries_3334_);
return v___x_3335_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_3336_, lean_object* v_depth_3337_, lean_object* v_keys_3338_, lean_object* v_vals_3339_, lean_object* v_heq_3340_, lean_object* v_i_3341_, lean_object* v_entries_3342_){
_start:
{
size_t v_depth_boxed_3343_; lean_object* v_res_3344_; 
v_depth_boxed_3343_ = lean_unbox_usize(v_depth_3337_);
lean_dec(v_depth_3337_);
v_res_3344_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0_spec__2(v_00_u03b2_3336_, v_depth_boxed_3343_, v_keys_3338_, v_vals_3339_, v_heq_3340_, v_i_3341_, v_entries_3342_);
lean_dec_ref(v_vals_3339_);
lean_dec_ref(v_keys_3338_);
return v_res_3344_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0_spec__1_spec__5(lean_object* v_00_u03b2_3345_, lean_object* v_x_3346_, lean_object* v_x_3347_, lean_object* v_x_3348_, lean_object* v_x_3349_){
_start:
{
lean_object* v___x_3350_; 
v___x_3350_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0_spec__0_spec__1_spec__5___redArg(v_x_3346_, v_x_3347_, v_x_3348_, v_x_3349_);
return v___x_3350_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Simp(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Util(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Reify(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Arith_Classify(uint8_t builtin);
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
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Arith_Classify(builtin);
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
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Arith_Classify(uint8_t builtin);
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
res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Arith_Classify(builtin);
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
