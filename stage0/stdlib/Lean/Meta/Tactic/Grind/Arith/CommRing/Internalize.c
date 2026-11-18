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
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Level_ofNat(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
extern lean_object* l_Lean_Int_mkType;
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_canon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getGeneration___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkExpectedPropHint(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_pushNewFactCore___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_synthInstance_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
size_t lean_ptr_addr(lean_object*);
lean_object* l_Lean_Meta_getNatValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_int_neg(lean_object*);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_modifyRing___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instInhabitedPersistentArrayNode_default___redArg();
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
uint64_t l_Lean_Expr_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_mul(size_t, size_t);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_forM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_pushNewFact(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRingState___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRingState___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_hasChar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_getCharInst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_int_emod(lean_object*, lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
lean_object* l_Lean_mkRawNatLit(lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_mkNatLit(lean_object*);
lean_object* l_Lean_mkIntLit(lean_object*);
extern lean_object* l_Lean_eagerReflBoolTrue;
lean_object* l_Lean_mkApp6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_pushEqCore___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_getIntValue_x3f(lean_object*);
lean_object* l_Lean_Meta_Sym_Arith_getIntCastFn___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_usize_to_uint64(size_t);
uint8_t l_Lean_PersistentHashMap_contains___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Arith_getNatCastFn___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_instBEqExprPtr___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_instHashableExprPtr___lam__0___boxed(lean_object*);
lean_object* l_Lean_PersistentHashMap_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_Sym_isNatValue(lean_object*);
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
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNonCommRingId_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRingState___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Arith_homoType_x3f(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_reify_x3f(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_sreify_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_pushNatCastFact___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_pushNatCastFact___redArg___closed__0;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_pushNatCastFact___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_pushNatCastFact___redArg___closed__1;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_pushNatCastFact___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_pushNatCastFact___redArg___closed__2;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_pushNatCastFact___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "instNatCastInt"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_pushNatCastFact___redArg___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_pushNatCastFact___redArg___closed__3_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_pushNatCastFact___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_pushNatCastFact___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(116, 224, 75, 57, 255, 108, 159, 197)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_pushNatCastFact___redArg___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_pushNatCastFact___redArg___closed__4_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_pushNatCastFact___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_pushNatCastFact___redArg___closed__5;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_pushNatCastFact___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "intCast_natCast"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_pushNatCastFact___redArg___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_pushNatCastFact___redArg___closed__6_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_pushNatCastFact___redArg___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_pushNatCastFact___redArg___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_pushNatCastFact___redArg___closed__7_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_pushNatCastFact___redArg___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_pushNatCastFact___redArg___closed__7_value_aux_1),((lean_object*)&l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(196, 225, 111, 69, 82, 38, 249, 149)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_pushNatCastFact___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_pushNatCastFact___redArg___closed__7_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_pushNatCastFact___redArg___closed__6_value),LEAN_SCALAR_PTR_LITERAL(45, 152, 136, 100, 130, 220, 111, 17)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_pushNatCastFact___redArg___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_pushNatCastFact___redArg___closed__7_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_pushNatCastFact___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_pushNatCastFact___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_pushNatCastFact(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_pushNatCastFact___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___redArg___lam__8___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___redArg___lam__8___closed__0;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___redArg___lam__8___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___redArg___lam__8___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___redArg___lam__8(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___redArg___lam__8___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___redArg___lam__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___redArg___lam__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___redArg___lam__12(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___redArg___lam__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___redArg___lam__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___redArg___lam__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___redArg___lam__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___redArg___lam__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___redArg___lam__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___redArg___lam__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_instBEqExprPtr___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___redArg___closed__0_value;
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_instHashableExprPtr___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___redArg___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___redArg___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__1_spec__8_spec__17___redArg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__1_spec__8_spec__17___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__1_spec__8_spec__16_spec__22(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__1_spec__8_spec__16_spec__23(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__1_spec__8_spec__16_spec__23___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__1_spec__8_spec__16_spec__22___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__1_spec__8_spec__16___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__1_spec__8_spec__16___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__1_spec__8_spec__16(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__1_spec__8_spec__16___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__1_spec__8_spec__18(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__1_spec__8_spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__1_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__1_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0_spec__0_spec__1_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0_spec__0_spec__1_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0_spec__0_spec__1___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getIntCastFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__1_spec__7___lam__0(lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getIntCastFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__1_spec__7___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getIntCastFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__1_spec__7___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_getIntCastFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__1_spec__7___closed__0_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getIntCastFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__1_spec__7___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_getIntCastFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__1_spec__7___closed__0_value_aux_1),((lean_object*)&l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(196, 225, 111, 69, 82, 38, 249, 149)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getIntCastFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__1_spec__7___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_getIntCastFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__1_spec__7___closed__0_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(1, 189, 244, 99, 68, 50, 19, 202)}};
static const lean_object* l_Lean_Meta_Sym_Arith_getIntCastFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__1_spec__7___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getIntCastFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__1_spec__7___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getIntCastFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__1_spec__7___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(63, 186, 193, 83, 149, 255, 18, 69)}};
static const lean_object* l_Lean_Meta_Sym_Arith_getIntCastFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__1_spec__7___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getIntCastFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__1_spec__7___closed__1_value;
static const lean_string_object l_Lean_Meta_Sym_Arith_getIntCastFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__1_spec__7___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "cast"};
static const lean_object* l_Lean_Meta_Sym_Arith_getIntCastFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__1_spec__7___closed__2 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getIntCastFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__1_spec__7___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getIntCastFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__1_spec__7___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__27_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_getIntCastFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__1_spec__7___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_getIntCastFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__1_spec__7___closed__3_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_Arith_getIntCastFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__1_spec__7___closed__2_value),LEAN_SCALAR_PTR_LITERAL(181, 4, 252, 84, 28, 16, 24, 6)}};
static const lean_object* l_Lean_Meta_Sym_Arith_getIntCastFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__1_spec__7___closed__3 = (const lean_object*)&l_Lean_Meta_Sym_Arith_getIntCastFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__1_spec__7___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getIntCastFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__1_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getIntCastFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__1_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatCastFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__1_spec__6___lam__0(lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___at___00Lean_Meta_Sym_Arith_getNatCastFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__1_spec__6_spec__13___redArg___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___at___00Lean_Meta_Sym_Arith_getNatCastFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__1_spec__6_spec__13___redArg___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___at___00Lean_Meta_Sym_Arith_getNatCastFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__1_spec__6_spec__13___redArg___closed__0_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___at___00Lean_Meta_Sym_Arith_getNatCastFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__1_spec__6_spec__13___redArg___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___at___00Lean_Meta_Sym_Arith_getNatCastFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__1_spec__6_spec__13___redArg___closed__0_value_aux_1),((lean_object*)&l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__2___closed__2_value),LEAN_SCALAR_PTR_LITERAL(246, 150, 10, 46, 185, 54, 59, 167)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___at___00Lean_Meta_Sym_Arith_getNatCastFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__1_spec__6_spec__13___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___at___00Lean_Meta_Sym_Arith_getNatCastFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__1_spec__6_spec__13___redArg___closed__0_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__4_value),LEAN_SCALAR_PTR_LITERAL(84, 97, 73, 37, 143, 22, 233, 204)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___at___00Lean_Meta_Sym_Arith_getNatCastFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__1_spec__6_spec__13___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___at___00Lean_Meta_Sym_Arith_getNatCastFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__1_spec__6_spec__13___redArg___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___at___00Lean_Meta_Sym_Arith_getNatCastFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__1_spec__6_spec__13___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__3_value),LEAN_SCALAR_PTR_LITERAL(65, 128, 63, 191, 243, 154, 52, 80)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___at___00Lean_Meta_Sym_Arith_getNatCastFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__1_spec__6_spec__13___redArg___closed__1 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___at___00Lean_Meta_Sym_Arith_getNatCastFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__1_spec__6_spec__13___redArg___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___at___00Lean_Meta_Sym_Arith_getNatCastFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__1_spec__6_spec__13___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___at___00Lean_Meta_Sym_Arith_getNatCastFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__1_spec__6_spec__13___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatCastFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__1_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatCastFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__1_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0_spec__2_spec__5_spec__10_spec__15___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0_spec__2_spec__5_spec__10___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0_spec__2_spec__5___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0_spec__2_spec__5_spec__11___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0_spec__2_spec__5_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__1___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getIntCastFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0_spec__3___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getIntCastFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getIntCastFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0___lam__4(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0___lam__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___at___00Lean_Meta_Sym_Arith_getNatCastFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___at___00Lean_Meta_Sym_Arith_getNatCastFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatCastFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0_spec__1___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatCastFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatCastFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0_spec__4_spec__9___redArg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0_spec__4_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0_spec__4_spec__8_spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0_spec__4_spec__8_spec__15(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0_spec__4_spec__8_spec__15___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0_spec__4_spec__8_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0_spec__4_spec__8(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0_spec__4_spec__8___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0_spec__4_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0_spec__4_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___at___00Lean_Meta_Sym_Arith_getNatCastFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___at___00Lean_Meta_Sym_Arith_getNatCastFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___at___00Lean_Meta_Sym_Arith_getNatCastFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__1_spec__6_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___at___00Lean_Meta_Sym_Arith_getNatCastFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__1_spec__6_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0_spec__0_spec__1(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0_spec__2_spec__5(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0_spec__4_spec__9(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0_spec__4_spec__9___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__1_spec__8_spec__17(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__1_spec__8_spec__17___boxed(lean_object**);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0_spec__0_spec__1_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0_spec__0_spec__1_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0_spec__2_spec__5_spec__10(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0_spec__2_spec__5_spec__11(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0_spec__2_spec__5_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0_spec__2_spec__5_spec__10_spec__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeInv(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeInv___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_internalize___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_internalize___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_internalize___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v_toRing_342_; lean_object* v_invFn_x3f_343_; lean_object* v_divFn_x3f_344_; lean_object* v_zpowFn_x3f_345_; lean_object* v_semiringId_x3f_346_; lean_object* v_commSemiringInst_347_; lean_object* v_commRingInst_348_; lean_object* v_noZeroDivInst_x3f_349_; lean_object* v_fieldInst_x3f_350_; lean_object* v_powIdentityInst_x3f_351_; lean_object* v___x_353_; uint8_t v_isShared_354_; uint8_t v_isSharedCheck_383_; 
v_toRing_342_ = lean_ctor_get(v_s_341_, 0);
v_invFn_x3f_343_ = lean_ctor_get(v_s_341_, 1);
v_divFn_x3f_344_ = lean_ctor_get(v_s_341_, 2);
v_zpowFn_x3f_345_ = lean_ctor_get(v_s_341_, 3);
v_semiringId_x3f_346_ = lean_ctor_get(v_s_341_, 4);
v_commSemiringInst_347_ = lean_ctor_get(v_s_341_, 5);
v_commRingInst_348_ = lean_ctor_get(v_s_341_, 6);
v_noZeroDivInst_x3f_349_ = lean_ctor_get(v_s_341_, 7);
v_fieldInst_x3f_350_ = lean_ctor_get(v_s_341_, 8);
v_powIdentityInst_x3f_351_ = lean_ctor_get(v_s_341_, 9);
v_isSharedCheck_383_ = !lean_is_exclusive(v_s_341_);
if (v_isSharedCheck_383_ == 0)
{
v___x_353_ = v_s_341_;
v_isShared_354_ = v_isSharedCheck_383_;
goto v_resetjp_352_;
}
else
{
lean_inc(v_powIdentityInst_x3f_351_);
lean_inc(v_fieldInst_x3f_350_);
lean_inc(v_noZeroDivInst_x3f_349_);
lean_inc(v_commRingInst_348_);
lean_inc(v_commSemiringInst_347_);
lean_inc(v_semiringId_x3f_346_);
lean_inc(v_zpowFn_x3f_345_);
lean_inc(v_divFn_x3f_344_);
lean_inc(v_invFn_x3f_343_);
lean_inc(v_toRing_342_);
lean_dec(v_s_341_);
v___x_353_ = lean_box(0);
v_isShared_354_ = v_isSharedCheck_383_;
goto v_resetjp_352_;
}
v_resetjp_352_:
{
lean_object* v_id_355_; lean_object* v_type_356_; lean_object* v_u_357_; lean_object* v_ringInst_358_; lean_object* v_semiringInst_359_; lean_object* v_charInst_x3f_360_; uint8_t v_symbolicChar_361_; lean_object* v_addFn_x3f_362_; lean_object* v_mulFn_x3f_363_; lean_object* v_subFn_x3f_364_; lean_object* v_powFn_x3f_365_; lean_object* v_intCastFn_x3f_366_; lean_object* v_natCastFn_x3f_367_; lean_object* v_natSMulFn_x3f_368_; lean_object* v_intSMulFn_x3f_369_; lean_object* v_one_x3f_370_; lean_object* v___x_372_; uint8_t v_isShared_373_; uint8_t v_isSharedCheck_381_; 
v_id_355_ = lean_ctor_get(v_toRing_342_, 0);
v_type_356_ = lean_ctor_get(v_toRing_342_, 1);
v_u_357_ = lean_ctor_get(v_toRing_342_, 2);
v_ringInst_358_ = lean_ctor_get(v_toRing_342_, 3);
v_semiringInst_359_ = lean_ctor_get(v_toRing_342_, 4);
v_charInst_x3f_360_ = lean_ctor_get(v_toRing_342_, 5);
v_symbolicChar_361_ = lean_ctor_get_uint8(v_toRing_342_, sizeof(void*)*16);
v_addFn_x3f_362_ = lean_ctor_get(v_toRing_342_, 6);
v_mulFn_x3f_363_ = lean_ctor_get(v_toRing_342_, 7);
v_subFn_x3f_364_ = lean_ctor_get(v_toRing_342_, 8);
v_powFn_x3f_365_ = lean_ctor_get(v_toRing_342_, 10);
v_intCastFn_x3f_366_ = lean_ctor_get(v_toRing_342_, 11);
v_natCastFn_x3f_367_ = lean_ctor_get(v_toRing_342_, 12);
v_natSMulFn_x3f_368_ = lean_ctor_get(v_toRing_342_, 13);
v_intSMulFn_x3f_369_ = lean_ctor_get(v_toRing_342_, 14);
v_one_x3f_370_ = lean_ctor_get(v_toRing_342_, 15);
v_isSharedCheck_381_ = !lean_is_exclusive(v_toRing_342_);
if (v_isSharedCheck_381_ == 0)
{
lean_object* v_unused_382_; 
v_unused_382_ = lean_ctor_get(v_toRing_342_, 9);
lean_dec(v_unused_382_);
v___x_372_ = v_toRing_342_;
v_isShared_373_ = v_isSharedCheck_381_;
goto v_resetjp_371_;
}
else
{
lean_inc(v_one_x3f_370_);
lean_inc(v_intSMulFn_x3f_369_);
lean_inc(v_natSMulFn_x3f_368_);
lean_inc(v_natCastFn_x3f_367_);
lean_inc(v_intCastFn_x3f_366_);
lean_inc(v_powFn_x3f_365_);
lean_inc(v_subFn_x3f_364_);
lean_inc(v_mulFn_x3f_363_);
lean_inc(v_addFn_x3f_362_);
lean_inc(v_charInst_x3f_360_);
lean_inc(v_semiringInst_359_);
lean_inc(v_ringInst_358_);
lean_inc(v_u_357_);
lean_inc(v_type_356_);
lean_inc(v_id_355_);
lean_dec(v_toRing_342_);
v___x_372_ = lean_box(0);
v_isShared_373_ = v_isSharedCheck_381_;
goto v_resetjp_371_;
}
v_resetjp_371_:
{
lean_object* v___x_374_; lean_object* v___x_376_; 
v___x_374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_374_, 0, v_a_340_);
if (v_isShared_373_ == 0)
{
lean_ctor_set(v___x_372_, 9, v___x_374_);
v___x_376_ = v___x_372_;
goto v_reusejp_375_;
}
else
{
lean_object* v_reuseFailAlloc_380_; 
v_reuseFailAlloc_380_ = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(v_reuseFailAlloc_380_, 0, v_id_355_);
lean_ctor_set(v_reuseFailAlloc_380_, 1, v_type_356_);
lean_ctor_set(v_reuseFailAlloc_380_, 2, v_u_357_);
lean_ctor_set(v_reuseFailAlloc_380_, 3, v_ringInst_358_);
lean_ctor_set(v_reuseFailAlloc_380_, 4, v_semiringInst_359_);
lean_ctor_set(v_reuseFailAlloc_380_, 5, v_charInst_x3f_360_);
lean_ctor_set(v_reuseFailAlloc_380_, 6, v_addFn_x3f_362_);
lean_ctor_set(v_reuseFailAlloc_380_, 7, v_mulFn_x3f_363_);
lean_ctor_set(v_reuseFailAlloc_380_, 8, v_subFn_x3f_364_);
lean_ctor_set(v_reuseFailAlloc_380_, 9, v___x_374_);
lean_ctor_set(v_reuseFailAlloc_380_, 10, v_powFn_x3f_365_);
lean_ctor_set(v_reuseFailAlloc_380_, 11, v_intCastFn_x3f_366_);
lean_ctor_set(v_reuseFailAlloc_380_, 12, v_natCastFn_x3f_367_);
lean_ctor_set(v_reuseFailAlloc_380_, 13, v_natSMulFn_x3f_368_);
lean_ctor_set(v_reuseFailAlloc_380_, 14, v_intSMulFn_x3f_369_);
lean_ctor_set(v_reuseFailAlloc_380_, 15, v_one_x3f_370_);
lean_ctor_set_uint8(v_reuseFailAlloc_380_, sizeof(void*)*16, v_symbolicChar_361_);
v___x_376_ = v_reuseFailAlloc_380_;
goto v_reusejp_375_;
}
v_reusejp_375_:
{
lean_object* v___x_378_; 
if (v_isShared_354_ == 0)
{
lean_ctor_set(v___x_353_, 0, v___x_376_);
v___x_378_ = v___x_353_;
goto v_reusejp_377_;
}
else
{
lean_object* v_reuseFailAlloc_379_; 
v_reuseFailAlloc_379_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_379_, 0, v___x_376_);
lean_ctor_set(v_reuseFailAlloc_379_, 1, v_invFn_x3f_343_);
lean_ctor_set(v_reuseFailAlloc_379_, 2, v_divFn_x3f_344_);
lean_ctor_set(v_reuseFailAlloc_379_, 3, v_zpowFn_x3f_345_);
lean_ctor_set(v_reuseFailAlloc_379_, 4, v_semiringId_x3f_346_);
lean_ctor_set(v_reuseFailAlloc_379_, 5, v_commSemiringInst_347_);
lean_ctor_set(v_reuseFailAlloc_379_, 6, v_commRingInst_348_);
lean_ctor_set(v_reuseFailAlloc_379_, 7, v_noZeroDivInst_x3f_349_);
lean_ctor_set(v_reuseFailAlloc_379_, 8, v_fieldInst_x3f_350_);
lean_ctor_set(v_reuseFailAlloc_379_, 9, v_powIdentityInst_x3f_351_);
v___x_378_ = v_reuseFailAlloc_379_;
goto v_reusejp_377_;
}
v_reusejp_377_:
{
return v___x_378_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0(lean_object* v___y_395_, lean_object* v___y_396_, lean_object* v___y_397_, lean_object* v___y_398_, lean_object* v___y_399_, lean_object* v___y_400_, lean_object* v___y_401_, lean_object* v___y_402_, lean_object* v___y_403_, lean_object* v___y_404_, lean_object* v___y_405_){
_start:
{
lean_object* v___x_407_; 
v___x_407_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v___y_395_, v___y_396_, v___y_397_, v___y_398_, v___y_399_, v___y_400_, v___y_401_, v___y_402_, v___y_403_, v___y_404_, v___y_405_);
if (lean_obj_tag(v___x_407_) == 0)
{
lean_object* v_a_408_; lean_object* v___x_410_; uint8_t v_isShared_411_; uint8_t v_isSharedCheck_448_; 
v_a_408_ = lean_ctor_get(v___x_407_, 0);
v_isSharedCheck_448_ = !lean_is_exclusive(v___x_407_);
if (v_isSharedCheck_448_ == 0)
{
v___x_410_ = v___x_407_;
v_isShared_411_ = v_isSharedCheck_448_;
goto v_resetjp_409_;
}
else
{
lean_inc(v_a_408_);
lean_dec(v___x_407_);
v___x_410_ = lean_box(0);
v_isShared_411_ = v_isSharedCheck_448_;
goto v_resetjp_409_;
}
v_resetjp_409_:
{
lean_object* v_toRing_412_; lean_object* v_negFn_x3f_413_; 
v_toRing_412_ = lean_ctor_get(v_a_408_, 0);
lean_inc_ref(v_toRing_412_);
lean_dec(v_a_408_);
v_negFn_x3f_413_ = lean_ctor_get(v_toRing_412_, 9);
if (lean_obj_tag(v_negFn_x3f_413_) == 1)
{
lean_object* v_val_414_; lean_object* v___x_416_; 
lean_inc_ref(v_negFn_x3f_413_);
lean_dec_ref(v_toRing_412_);
v_val_414_ = lean_ctor_get(v_negFn_x3f_413_, 0);
lean_inc(v_val_414_);
lean_dec_ref_known(v_negFn_x3f_413_, 1);
if (v_isShared_411_ == 0)
{
lean_ctor_set(v___x_410_, 0, v_val_414_);
v___x_416_ = v___x_410_;
goto v_reusejp_415_;
}
else
{
lean_object* v_reuseFailAlloc_417_; 
v_reuseFailAlloc_417_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_417_, 0, v_val_414_);
v___x_416_ = v_reuseFailAlloc_417_;
goto v_reusejp_415_;
}
v_reusejp_415_:
{
return v___x_416_;
}
}
else
{
lean_object* v_type_418_; lean_object* v_u_419_; lean_object* v_ringInst_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v_expectedInst_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; 
lean_del_object(v___x_410_);
v_type_418_ = lean_ctor_get(v_toRing_412_, 1);
lean_inc_ref_n(v_type_418_, 2);
v_u_419_ = lean_ctor_get(v_toRing_412_, 2);
lean_inc_n(v_u_419_, 2);
v_ringInst_420_ = lean_ctor_get(v_toRing_412_, 3);
lean_inc_ref(v_ringInst_420_);
lean_dec_ref(v_toRing_412_);
v___x_421_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0___closed__4));
v___x_422_ = lean_box(0);
v___x_423_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_423_, 0, v_u_419_);
lean_ctor_set(v___x_423_, 1, v___x_422_);
v___x_424_ = l_Lean_mkConst(v___x_421_, v___x_423_);
v_expectedInst_425_ = l_Lean_mkAppB(v___x_424_, v_type_418_, v_ringInst_420_);
v___x_426_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0___closed__5));
v___x_427_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__11));
v___x_428_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__2(v_type_418_, v_u_419_, v___x_426_, v___x_427_, v_expectedInst_425_, v___y_395_, v___y_396_, v___y_397_, v___y_398_, v___y_399_, v___y_400_, v___y_401_, v___y_402_, v___y_403_, v___y_404_, v___y_405_);
if (lean_obj_tag(v___x_428_) == 0)
{
lean_object* v_a_429_; lean_object* v___f_430_; lean_object* v___x_431_; 
v_a_429_ = lean_ctor_get(v___x_428_, 0);
lean_inc_n(v_a_429_, 2);
lean_dec_ref_known(v___x_428_, 1);
v___f_430_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0___lam__0), 2, 1);
lean_closure_set(v___f_430_, 0, v_a_429_);
v___x_431_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(v___f_430_, v___y_395_, v___y_401_);
if (lean_obj_tag(v___x_431_) == 0)
{
lean_object* v___x_433_; uint8_t v_isShared_434_; uint8_t v_isSharedCheck_438_; 
v_isSharedCheck_438_ = !lean_is_exclusive(v___x_431_);
if (v_isSharedCheck_438_ == 0)
{
lean_object* v_unused_439_; 
v_unused_439_ = lean_ctor_get(v___x_431_, 0);
lean_dec(v_unused_439_);
v___x_433_ = v___x_431_;
v_isShared_434_ = v_isSharedCheck_438_;
goto v_resetjp_432_;
}
else
{
lean_dec(v___x_431_);
v___x_433_ = lean_box(0);
v_isShared_434_ = v_isSharedCheck_438_;
goto v_resetjp_432_;
}
v_resetjp_432_:
{
lean_object* v___x_436_; 
if (v_isShared_434_ == 0)
{
lean_ctor_set(v___x_433_, 0, v_a_429_);
v___x_436_ = v___x_433_;
goto v_reusejp_435_;
}
else
{
lean_object* v_reuseFailAlloc_437_; 
v_reuseFailAlloc_437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_437_, 0, v_a_429_);
v___x_436_ = v_reuseFailAlloc_437_;
goto v_reusejp_435_;
}
v_reusejp_435_:
{
return v___x_436_;
}
}
}
else
{
lean_object* v_a_440_; lean_object* v___x_442_; uint8_t v_isShared_443_; uint8_t v_isSharedCheck_447_; 
lean_dec(v_a_429_);
v_a_440_ = lean_ctor_get(v___x_431_, 0);
v_isSharedCheck_447_ = !lean_is_exclusive(v___x_431_);
if (v_isSharedCheck_447_ == 0)
{
v___x_442_ = v___x_431_;
v_isShared_443_ = v_isSharedCheck_447_;
goto v_resetjp_441_;
}
else
{
lean_inc(v_a_440_);
lean_dec(v___x_431_);
v___x_442_ = lean_box(0);
v_isShared_443_ = v_isSharedCheck_447_;
goto v_resetjp_441_;
}
v_resetjp_441_:
{
lean_object* v___x_445_; 
if (v_isShared_443_ == 0)
{
v___x_445_ = v___x_442_;
goto v_reusejp_444_;
}
else
{
lean_object* v_reuseFailAlloc_446_; 
v_reuseFailAlloc_446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_446_, 0, v_a_440_);
v___x_445_ = v_reuseFailAlloc_446_;
goto v_reusejp_444_;
}
v_reusejp_444_:
{
return v___x_445_;
}
}
}
}
else
{
return v___x_428_;
}
}
}
}
else
{
lean_object* v_a_449_; lean_object* v___x_451_; uint8_t v_isShared_452_; uint8_t v_isSharedCheck_456_; 
v_a_449_ = lean_ctor_get(v___x_407_, 0);
v_isSharedCheck_456_ = !lean_is_exclusive(v___x_407_);
if (v_isSharedCheck_456_ == 0)
{
v___x_451_ = v___x_407_;
v_isShared_452_ = v_isSharedCheck_456_;
goto v_resetjp_450_;
}
else
{
lean_inc(v_a_449_);
lean_dec(v___x_407_);
v___x_451_ = lean_box(0);
v_isShared_452_ = v_isSharedCheck_456_;
goto v_resetjp_450_;
}
v_resetjp_450_:
{
lean_object* v___x_454_; 
if (v_isShared_452_ == 0)
{
v___x_454_ = v___x_451_;
goto v_reusejp_453_;
}
else
{
lean_object* v_reuseFailAlloc_455_; 
v_reuseFailAlloc_455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_455_, 0, v_a_449_);
v___x_454_ = v_reuseFailAlloc_455_;
goto v_reusejp_453_;
}
v_reusejp_453_:
{
return v___x_454_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0___boxed(lean_object* v___y_457_, lean_object* v___y_458_, lean_object* v___y_459_, lean_object* v___y_460_, lean_object* v___y_461_, lean_object* v___y_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_, lean_object* v___y_468_){
_start:
{
lean_object* v_res_469_; 
v_res_469_ = l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0(v___y_457_, v___y_458_, v___y_459_, v___y_460_, v___y_461_, v___y_462_, v___y_463_, v___y_464_, v___y_465_, v___y_466_, v___y_467_);
lean_dec(v___y_467_);
lean_dec_ref(v___y_466_);
lean_dec(v___y_465_);
lean_dec_ref(v___y_464_);
lean_dec(v___y_463_);
lean_dec_ref(v___y_462_);
lean_dec(v___y_461_);
lean_dec_ref(v___y_460_);
lean_dec(v___y_459_);
lean_dec(v___y_458_);
lean_dec_ref(v___y_457_);
return v_res_469_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0(lean_object* v_inst_470_, lean_object* v___y_471_, lean_object* v___y_472_, lean_object* v___y_473_, lean_object* v___y_474_, lean_object* v___y_475_, lean_object* v___y_476_, lean_object* v___y_477_, lean_object* v___y_478_, lean_object* v___y_479_, lean_object* v___y_480_, lean_object* v___y_481_){
_start:
{
lean_object* v___x_483_; 
v___x_483_ = l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0(v___y_471_, v___y_472_, v___y_473_, v___y_474_, v___y_475_, v___y_476_, v___y_477_, v___y_478_, v___y_479_, v___y_480_, v___y_481_);
if (lean_obj_tag(v___x_483_) == 0)
{
lean_object* v_a_484_; lean_object* v___x_486_; uint8_t v_isShared_487_; uint8_t v_isSharedCheck_496_; 
v_a_484_ = lean_ctor_get(v___x_483_, 0);
v_isSharedCheck_496_ = !lean_is_exclusive(v___x_483_);
if (v_isSharedCheck_496_ == 0)
{
v___x_486_ = v___x_483_;
v_isShared_487_ = v_isSharedCheck_496_;
goto v_resetjp_485_;
}
else
{
lean_inc(v_a_484_);
lean_dec(v___x_483_);
v___x_486_ = lean_box(0);
v_isShared_487_ = v_isSharedCheck_496_;
goto v_resetjp_485_;
}
v_resetjp_485_:
{
lean_object* v___x_488_; size_t v___x_489_; size_t v___x_490_; uint8_t v___x_491_; lean_object* v___x_492_; lean_object* v___x_494_; 
v___x_488_ = l_Lean_Expr_appArg_x21(v_a_484_);
lean_dec(v_a_484_);
v___x_489_ = lean_ptr_addr(v___x_488_);
lean_dec_ref(v___x_488_);
v___x_490_ = lean_ptr_addr(v_inst_470_);
v___x_491_ = lean_usize_dec_eq(v___x_489_, v___x_490_);
v___x_492_ = lean_box(v___x_491_);
if (v_isShared_487_ == 0)
{
lean_ctor_set(v___x_486_, 0, v___x_492_);
v___x_494_ = v___x_486_;
goto v_reusejp_493_;
}
else
{
lean_object* v_reuseFailAlloc_495_; 
v_reuseFailAlloc_495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_495_, 0, v___x_492_);
v___x_494_ = v_reuseFailAlloc_495_;
goto v_reusejp_493_;
}
v_reusejp_493_:
{
return v___x_494_;
}
}
}
else
{
lean_object* v_a_497_; lean_object* v___x_499_; uint8_t v_isShared_500_; uint8_t v_isSharedCheck_504_; 
v_a_497_ = lean_ctor_get(v___x_483_, 0);
v_isSharedCheck_504_ = !lean_is_exclusive(v___x_483_);
if (v_isSharedCheck_504_ == 0)
{
v___x_499_ = v___x_483_;
v_isShared_500_ = v_isSharedCheck_504_;
goto v_resetjp_498_;
}
else
{
lean_inc(v_a_497_);
lean_dec(v___x_483_);
v___x_499_ = lean_box(0);
v_isShared_500_ = v_isSharedCheck_504_;
goto v_resetjp_498_;
}
v_resetjp_498_:
{
lean_object* v___x_502_; 
if (v_isShared_500_ == 0)
{
v___x_502_ = v___x_499_;
goto v_reusejp_501_;
}
else
{
lean_object* v_reuseFailAlloc_503_; 
v_reuseFailAlloc_503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_503_, 0, v_a_497_);
v___x_502_ = v_reuseFailAlloc_503_;
goto v_reusejp_501_;
}
v_reusejp_501_:
{
return v___x_502_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0___boxed(lean_object* v_inst_505_, lean_object* v___y_506_, lean_object* v___y_507_, lean_object* v___y_508_, lean_object* v___y_509_, lean_object* v___y_510_, lean_object* v___y_511_, lean_object* v___y_512_, lean_object* v___y_513_, lean_object* v___y_514_, lean_object* v___y_515_, lean_object* v___y_516_, lean_object* v___y_517_){
_start:
{
lean_object* v_res_518_; 
v_res_518_ = l_Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0(v_inst_505_, v___y_506_, v___y_507_, v___y_508_, v___y_509_, v___y_510_, v___y_511_, v___y_512_, v___y_513_, v___y_514_, v___y_515_, v___y_516_);
lean_dec(v___y_516_);
lean_dec_ref(v___y_515_);
lean_dec(v___y_514_);
lean_dec_ref(v___y_513_);
lean_dec(v___y_512_);
lean_dec_ref(v___y_511_);
lean_dec(v___y_510_);
lean_dec_ref(v___y_509_);
lean_dec(v___y_508_);
lean_dec(v___y_507_);
lean_dec_ref(v___y_506_);
lean_dec_ref(v_inst_505_);
return v_res_518_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f(lean_object* v_e_519_, lean_object* v_a_520_, lean_object* v_a_521_, lean_object* v_a_522_, lean_object* v_a_523_, lean_object* v_a_524_, lean_object* v_a_525_, lean_object* v_a_526_, lean_object* v_a_527_, lean_object* v_a_528_, lean_object* v_a_529_, lean_object* v_a_530_){
_start:
{
lean_object* v___x_538_; 
v___x_538_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_519_, v_a_528_);
if (lean_obj_tag(v___x_538_) == 0)
{
lean_object* v_a_539_; lean_object* v___x_540_; uint8_t v___x_541_; 
v_a_539_ = lean_ctor_get(v___x_538_, 0);
lean_inc(v_a_539_);
lean_dec_ref_known(v___x_538_, 1);
v___x_540_ = l_Lean_Expr_cleanupAnnotations(v_a_539_);
lean_dec(v_a_539_);
v___x_541_ = l_Lean_Expr_isApp(v___x_540_);
if (v___x_541_ == 0)
{
lean_dec_ref(v___x_540_);
goto v___jp_532_;
}
else
{
lean_object* v___x_542_; uint8_t v___x_543_; 
v___x_542_ = l_Lean_Expr_appFnCleanup___redArg(v___x_540_);
v___x_543_ = l_Lean_Expr_isApp(v___x_542_);
if (v___x_543_ == 0)
{
lean_dec_ref(v___x_542_);
lean_dec_ref(v___x_540_);
goto v___jp_532_;
}
else
{
lean_object* v___x_544_; uint8_t v___x_545_; 
v___x_544_ = l_Lean_Expr_appFnCleanup___redArg(v___x_542_);
v___x_545_ = l_Lean_Expr_isApp(v___x_544_);
if (v___x_545_ == 0)
{
lean_dec_ref(v___x_544_);
lean_dec_ref(v___x_542_);
lean_dec_ref(v___x_540_);
goto v___jp_532_;
}
else
{
lean_object* v_arg_546_; lean_object* v___x_547_; lean_object* v___x_548_; uint8_t v___x_549_; 
v_arg_546_ = lean_ctor_get(v___x_542_, 1);
lean_inc_ref(v_arg_546_);
lean_dec_ref(v___x_542_);
v___x_547_ = l_Lean_Expr_appFnCleanup___redArg(v___x_544_);
lean_dec_ref(v___x_544_);
v___x_548_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__8));
v___x_549_ = l_Lean_Expr_isConstOf(v___x_547_, v___x_548_);
if (v___x_549_ == 0)
{
lean_object* v___x_550_; uint8_t v___x_551_; 
v___x_550_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__11));
v___x_551_ = l_Lean_Expr_isConstOf(v___x_547_, v___x_550_);
lean_dec_ref(v___x_547_);
if (v___x_551_ == 0)
{
lean_dec_ref(v_arg_546_);
lean_dec_ref(v___x_540_);
goto v___jp_532_;
}
else
{
lean_object* v_arg_552_; lean_object* v___x_553_; 
v_arg_552_ = lean_ctor_get(v___x_540_, 1);
lean_inc_ref(v_arg_552_);
lean_dec_ref(v___x_540_);
v___x_553_ = l_Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0(v_arg_546_, v_a_520_, v_a_521_, v_a_522_, v_a_523_, v_a_524_, v_a_525_, v_a_526_, v_a_527_, v_a_528_, v_a_529_, v_a_530_);
lean_dec_ref(v_arg_546_);
if (lean_obj_tag(v___x_553_) == 0)
{
lean_object* v_a_554_; lean_object* v___x_556_; uint8_t v_isShared_557_; uint8_t v_isSharedCheck_609_; 
v_a_554_ = lean_ctor_get(v___x_553_, 0);
v_isSharedCheck_609_ = !lean_is_exclusive(v___x_553_);
if (v_isSharedCheck_609_ == 0)
{
v___x_556_ = v___x_553_;
v_isShared_557_ = v_isSharedCheck_609_;
goto v_resetjp_555_;
}
else
{
lean_inc(v_a_554_);
lean_dec(v___x_553_);
v___x_556_ = lean_box(0);
v_isShared_557_ = v_isSharedCheck_609_;
goto v_resetjp_555_;
}
v_resetjp_555_:
{
uint8_t v___x_558_; 
v___x_558_ = lean_unbox(v_a_554_);
lean_dec(v_a_554_);
if (v___x_558_ == 0)
{
lean_object* v___x_559_; lean_object* v___x_561_; 
lean_dec_ref(v_arg_552_);
v___x_559_ = lean_box(0);
if (v_isShared_557_ == 0)
{
lean_ctor_set(v___x_556_, 0, v___x_559_);
v___x_561_ = v___x_556_;
goto v_reusejp_560_;
}
else
{
lean_object* v_reuseFailAlloc_562_; 
v_reuseFailAlloc_562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_562_, 0, v___x_559_);
v___x_561_ = v_reuseFailAlloc_562_;
goto v_reusejp_560_;
}
v_reusejp_560_:
{
return v___x_561_;
}
}
else
{
lean_object* v___x_563_; uint8_t v___x_564_; 
lean_del_object(v___x_556_);
v___x_563_ = l_Lean_Expr_cleanupAnnotations(v_arg_552_);
lean_dec_ref(v_arg_552_);
v___x_564_ = l_Lean_Expr_isApp(v___x_563_);
if (v___x_564_ == 0)
{
lean_dec_ref(v___x_563_);
goto v___jp_535_;
}
else
{
lean_object* v___x_565_; uint8_t v___x_566_; 
v___x_565_ = l_Lean_Expr_appFnCleanup___redArg(v___x_563_);
lean_dec_ref(v___x_563_);
v___x_566_ = l_Lean_Expr_isApp(v___x_565_);
if (v___x_566_ == 0)
{
lean_dec_ref(v___x_565_);
goto v___jp_535_;
}
else
{
lean_object* v___x_567_; uint8_t v___x_568_; 
v___x_567_ = l_Lean_Expr_appFnCleanup___redArg(v___x_565_);
v___x_568_ = l_Lean_Expr_isApp(v___x_567_);
if (v___x_568_ == 0)
{
lean_dec_ref(v___x_567_);
lean_dec_ref(v___x_565_);
goto v___jp_535_;
}
else
{
lean_object* v___x_569_; uint8_t v___x_570_; 
v___x_569_ = l_Lean_Expr_appFnCleanup___redArg(v___x_567_);
lean_dec_ref(v___x_567_);
v___x_570_ = l_Lean_Expr_isConstOf(v___x_569_, v___x_548_);
lean_dec_ref(v___x_569_);
if (v___x_570_ == 0)
{
lean_dec_ref(v___x_565_);
goto v___jp_535_;
}
else
{
lean_object* v_arg_571_; lean_object* v___x_572_; 
v_arg_571_ = lean_ctor_get(v___x_565_, 1);
lean_inc_ref(v_arg_571_);
lean_dec_ref(v___x_565_);
v___x_572_ = l_Lean_Meta_getNatValue_x3f(v_arg_571_, v_a_527_, v_a_528_, v_a_529_, v_a_530_);
lean_dec_ref(v_arg_571_);
if (lean_obj_tag(v___x_572_) == 0)
{
lean_object* v_a_573_; lean_object* v___x_575_; uint8_t v_isShared_576_; uint8_t v_isSharedCheck_600_; 
v_a_573_ = lean_ctor_get(v___x_572_, 0);
v_isSharedCheck_600_ = !lean_is_exclusive(v___x_572_);
if (v_isSharedCheck_600_ == 0)
{
v___x_575_ = v___x_572_;
v_isShared_576_ = v_isSharedCheck_600_;
goto v_resetjp_574_;
}
else
{
lean_inc(v_a_573_);
lean_dec(v___x_572_);
v___x_575_ = lean_box(0);
v_isShared_576_ = v_isSharedCheck_600_;
goto v_resetjp_574_;
}
v_resetjp_574_:
{
if (lean_obj_tag(v_a_573_) == 1)
{
lean_object* v_val_577_; lean_object* v___x_579_; uint8_t v_isShared_580_; uint8_t v_isSharedCheck_595_; 
v_val_577_ = lean_ctor_get(v_a_573_, 0);
v_isSharedCheck_595_ = !lean_is_exclusive(v_a_573_);
if (v_isSharedCheck_595_ == 0)
{
v___x_579_ = v_a_573_;
v_isShared_580_ = v_isSharedCheck_595_;
goto v_resetjp_578_;
}
else
{
lean_inc(v_val_577_);
lean_dec(v_a_573_);
v___x_579_ = lean_box(0);
v_isShared_580_ = v_isSharedCheck_595_;
goto v_resetjp_578_;
}
v_resetjp_578_:
{
lean_object* v___x_581_; uint8_t v___x_582_; 
v___x_581_ = lean_unsigned_to_nat(0u);
v___x_582_ = lean_nat_dec_eq(v_val_577_, v___x_581_);
if (v___x_582_ == 0)
{
lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_586_; 
v___x_583_ = lean_nat_to_int(v_val_577_);
v___x_584_ = lean_int_neg(v___x_583_);
lean_dec(v___x_583_);
if (v_isShared_580_ == 0)
{
lean_ctor_set(v___x_579_, 0, v___x_584_);
v___x_586_ = v___x_579_;
goto v_reusejp_585_;
}
else
{
lean_object* v_reuseFailAlloc_590_; 
v_reuseFailAlloc_590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_590_, 0, v___x_584_);
v___x_586_ = v_reuseFailAlloc_590_;
goto v_reusejp_585_;
}
v_reusejp_585_:
{
lean_object* v___x_588_; 
if (v_isShared_576_ == 0)
{
lean_ctor_set(v___x_575_, 0, v___x_586_);
v___x_588_ = v___x_575_;
goto v_reusejp_587_;
}
else
{
lean_object* v_reuseFailAlloc_589_; 
v_reuseFailAlloc_589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_589_, 0, v___x_586_);
v___x_588_ = v_reuseFailAlloc_589_;
goto v_reusejp_587_;
}
v_reusejp_587_:
{
return v___x_588_;
}
}
}
else
{
lean_object* v___x_591_; lean_object* v___x_593_; 
lean_del_object(v___x_579_);
lean_dec(v_val_577_);
v___x_591_ = lean_box(0);
if (v_isShared_576_ == 0)
{
lean_ctor_set(v___x_575_, 0, v___x_591_);
v___x_593_ = v___x_575_;
goto v_reusejp_592_;
}
else
{
lean_object* v_reuseFailAlloc_594_; 
v_reuseFailAlloc_594_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_594_, 0, v___x_591_);
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
else
{
lean_object* v___x_596_; lean_object* v___x_598_; 
lean_dec(v_a_573_);
v___x_596_ = lean_box(0);
if (v_isShared_576_ == 0)
{
lean_ctor_set(v___x_575_, 0, v___x_596_);
v___x_598_ = v___x_575_;
goto v_reusejp_597_;
}
else
{
lean_object* v_reuseFailAlloc_599_; 
v_reuseFailAlloc_599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_599_, 0, v___x_596_);
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
lean_object* v_a_601_; lean_object* v___x_603_; uint8_t v_isShared_604_; uint8_t v_isSharedCheck_608_; 
v_a_601_ = lean_ctor_get(v___x_572_, 0);
v_isSharedCheck_608_ = !lean_is_exclusive(v___x_572_);
if (v_isSharedCheck_608_ == 0)
{
v___x_603_ = v___x_572_;
v_isShared_604_ = v_isSharedCheck_608_;
goto v_resetjp_602_;
}
else
{
lean_inc(v_a_601_);
lean_dec(v___x_572_);
v___x_603_ = lean_box(0);
v_isShared_604_ = v_isSharedCheck_608_;
goto v_resetjp_602_;
}
v_resetjp_602_:
{
lean_object* v___x_606_; 
if (v_isShared_604_ == 0)
{
v___x_606_ = v___x_603_;
goto v_reusejp_605_;
}
else
{
lean_object* v_reuseFailAlloc_607_; 
v_reuseFailAlloc_607_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_607_, 0, v_a_601_);
v___x_606_ = v_reuseFailAlloc_607_;
goto v_reusejp_605_;
}
v_reusejp_605_:
{
return v___x_606_;
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
lean_object* v_a_610_; lean_object* v___x_612_; uint8_t v_isShared_613_; uint8_t v_isSharedCheck_617_; 
lean_dec_ref(v_arg_552_);
v_a_610_ = lean_ctor_get(v___x_553_, 0);
v_isSharedCheck_617_ = !lean_is_exclusive(v___x_553_);
if (v_isSharedCheck_617_ == 0)
{
v___x_612_ = v___x_553_;
v_isShared_613_ = v_isSharedCheck_617_;
goto v_resetjp_611_;
}
else
{
lean_inc(v_a_610_);
lean_dec(v___x_553_);
v___x_612_ = lean_box(0);
v_isShared_613_ = v_isSharedCheck_617_;
goto v_resetjp_611_;
}
v_resetjp_611_:
{
lean_object* v___x_615_; 
if (v_isShared_613_ == 0)
{
v___x_615_ = v___x_612_;
goto v_reusejp_614_;
}
else
{
lean_object* v_reuseFailAlloc_616_; 
v_reuseFailAlloc_616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_616_, 0, v_a_610_);
v___x_615_ = v_reuseFailAlloc_616_;
goto v_reusejp_614_;
}
v_reusejp_614_:
{
return v___x_615_;
}
}
}
}
}
else
{
lean_object* v___x_618_; 
lean_dec_ref(v___x_547_);
lean_dec_ref(v___x_540_);
v___x_618_ = l_Lean_Meta_getNatValue_x3f(v_arg_546_, v_a_527_, v_a_528_, v_a_529_, v_a_530_);
lean_dec_ref(v_arg_546_);
if (lean_obj_tag(v___x_618_) == 0)
{
lean_object* v_a_619_; lean_object* v___x_621_; uint8_t v_isShared_622_; uint8_t v_isSharedCheck_639_; 
v_a_619_ = lean_ctor_get(v___x_618_, 0);
v_isSharedCheck_639_ = !lean_is_exclusive(v___x_618_);
if (v_isSharedCheck_639_ == 0)
{
v___x_621_ = v___x_618_;
v_isShared_622_ = v_isSharedCheck_639_;
goto v_resetjp_620_;
}
else
{
lean_inc(v_a_619_);
lean_dec(v___x_618_);
v___x_621_ = lean_box(0);
v_isShared_622_ = v_isSharedCheck_639_;
goto v_resetjp_620_;
}
v_resetjp_620_:
{
if (lean_obj_tag(v_a_619_) == 1)
{
lean_object* v_val_623_; lean_object* v___x_625_; uint8_t v_isShared_626_; uint8_t v_isSharedCheck_634_; 
v_val_623_ = lean_ctor_get(v_a_619_, 0);
v_isSharedCheck_634_ = !lean_is_exclusive(v_a_619_);
if (v_isSharedCheck_634_ == 0)
{
v___x_625_ = v_a_619_;
v_isShared_626_ = v_isSharedCheck_634_;
goto v_resetjp_624_;
}
else
{
lean_inc(v_val_623_);
lean_dec(v_a_619_);
v___x_625_ = lean_box(0);
v_isShared_626_ = v_isSharedCheck_634_;
goto v_resetjp_624_;
}
v_resetjp_624_:
{
lean_object* v___x_627_; lean_object* v___x_629_; 
v___x_627_ = lean_nat_to_int(v_val_623_);
if (v_isShared_626_ == 0)
{
lean_ctor_set(v___x_625_, 0, v___x_627_);
v___x_629_ = v___x_625_;
goto v_reusejp_628_;
}
else
{
lean_object* v_reuseFailAlloc_633_; 
v_reuseFailAlloc_633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_633_, 0, v___x_627_);
v___x_629_ = v_reuseFailAlloc_633_;
goto v_reusejp_628_;
}
v_reusejp_628_:
{
lean_object* v___x_631_; 
if (v_isShared_622_ == 0)
{
lean_ctor_set(v___x_621_, 0, v___x_629_);
v___x_631_ = v___x_621_;
goto v_reusejp_630_;
}
else
{
lean_object* v_reuseFailAlloc_632_; 
v_reuseFailAlloc_632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_632_, 0, v___x_629_);
v___x_631_ = v_reuseFailAlloc_632_;
goto v_reusejp_630_;
}
v_reusejp_630_:
{
return v___x_631_;
}
}
}
}
else
{
lean_object* v___x_635_; lean_object* v___x_637_; 
lean_dec(v_a_619_);
v___x_635_ = lean_box(0);
if (v_isShared_622_ == 0)
{
lean_ctor_set(v___x_621_, 0, v___x_635_);
v___x_637_ = v___x_621_;
goto v_reusejp_636_;
}
else
{
lean_object* v_reuseFailAlloc_638_; 
v_reuseFailAlloc_638_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_638_, 0, v___x_635_);
v___x_637_ = v_reuseFailAlloc_638_;
goto v_reusejp_636_;
}
v_reusejp_636_:
{
return v___x_637_;
}
}
}
}
else
{
lean_object* v_a_640_; lean_object* v___x_642_; uint8_t v_isShared_643_; uint8_t v_isSharedCheck_647_; 
v_a_640_ = lean_ctor_get(v___x_618_, 0);
v_isSharedCheck_647_ = !lean_is_exclusive(v___x_618_);
if (v_isSharedCheck_647_ == 0)
{
v___x_642_ = v___x_618_;
v_isShared_643_ = v_isSharedCheck_647_;
goto v_resetjp_641_;
}
else
{
lean_inc(v_a_640_);
lean_dec(v___x_618_);
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
}
}
}
else
{
lean_object* v_a_648_; lean_object* v___x_650_; uint8_t v_isShared_651_; uint8_t v_isSharedCheck_655_; 
v_a_648_ = lean_ctor_get(v___x_538_, 0);
v_isSharedCheck_655_ = !lean_is_exclusive(v___x_538_);
if (v_isSharedCheck_655_ == 0)
{
v___x_650_ = v___x_538_;
v_isShared_651_ = v_isSharedCheck_655_;
goto v_resetjp_649_;
}
else
{
lean_inc(v_a_648_);
lean_dec(v___x_538_);
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
v___jp_532_:
{
lean_object* v___x_533_; lean_object* v___x_534_; 
v___x_533_ = lean_box(0);
v___x_534_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_534_, 0, v___x_533_);
return v___x_534_;
}
v___jp_535_:
{
lean_object* v___x_536_; lean_object* v___x_537_; 
v___x_536_ = lean_box(0);
v___x_537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_537_, 0, v___x_536_);
return v___x_537_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f___boxed(lean_object* v_e_656_, lean_object* v_a_657_, lean_object* v_a_658_, lean_object* v_a_659_, lean_object* v_a_660_, lean_object* v_a_661_, lean_object* v_a_662_, lean_object* v_a_663_, lean_object* v_a_664_, lean_object* v_a_665_, lean_object* v_a_666_, lean_object* v_a_667_, lean_object* v_a_668_){
_start:
{
lean_object* v_res_669_; 
v_res_669_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f(v_e_656_, v_a_657_, v_a_658_, v_a_659_, v_a_660_, v_a_661_, v_a_662_, v_a_663_, v_a_664_, v_a_665_, v_a_666_, v_a_667_);
lean_dec(v_a_667_);
lean_dec_ref(v_a_666_);
lean_dec(v_a_665_);
lean_dec_ref(v_a_664_);
lean_dec(v_a_663_);
lean_dec_ref(v_a_662_);
lean_dec(v_a_661_);
lean_dec_ref(v_a_660_);
lean_dec(v_a_659_);
lean_dec(v_a_658_);
lean_dec_ref(v_a_657_);
return v_res_669_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__2_spec__3_spec__4(lean_object* v_00_u03b1_670_, lean_object* v_msg_671_, lean_object* v___y_672_, lean_object* v___y_673_, lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_, lean_object* v___y_677_, lean_object* v___y_678_, lean_object* v___y_679_, lean_object* v___y_680_, lean_object* v___y_681_, lean_object* v___y_682_){
_start:
{
lean_object* v___x_684_; 
v___x_684_ = l_Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__2_spec__3_spec__4___redArg(v_msg_671_, v___y_679_, v___y_680_, v___y_681_, v___y_682_);
return v___x_684_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__2_spec__3_spec__4___boxed(lean_object* v_00_u03b1_685_, lean_object* v_msg_686_, lean_object* v___y_687_, lean_object* v___y_688_, lean_object* v___y_689_, lean_object* v___y_690_, lean_object* v___y_691_, lean_object* v___y_692_, lean_object* v___y_693_, lean_object* v___y_694_, lean_object* v___y_695_, lean_object* v___y_696_, lean_object* v___y_697_, lean_object* v___y_698_){
_start:
{
lean_object* v_res_699_; 
v_res_699_ = l_Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__2_spec__3_spec__4(v_00_u03b1_685_, v_msg_686_, v___y_687_, v___y_688_, v___y_689_, v___y_690_, v___y_691_, v___y_692_, v___y_693_, v___y_694_, v___y_695_, v___y_696_, v___y_697_);
lean_dec(v___y_697_);
lean_dec_ref(v___y_696_);
lean_dec(v___y_695_);
lean_dec_ref(v___y_694_);
lean_dec(v___y_693_);
lean_dec_ref(v___y_692_);
lean_dec(v___y_691_);
lean_dec_ref(v___y_690_);
lean_dec(v___y_689_);
lean_dec(v___y_688_);
lean_dec_ref(v___y_687_);
return v_res_699_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___lam__0(lean_object* v_a_700_, lean_object* v_s_701_){
_start:
{
lean_object* v_toRing_702_; lean_object* v_divFn_x3f_703_; lean_object* v_zpowFn_x3f_704_; lean_object* v_semiringId_x3f_705_; lean_object* v_commSemiringInst_706_; lean_object* v_commRingInst_707_; lean_object* v_noZeroDivInst_x3f_708_; lean_object* v_fieldInst_x3f_709_; lean_object* v_powIdentityInst_x3f_710_; lean_object* v___x_712_; uint8_t v_isShared_713_; uint8_t v_isSharedCheck_718_; 
v_toRing_702_ = lean_ctor_get(v_s_701_, 0);
v_divFn_x3f_703_ = lean_ctor_get(v_s_701_, 2);
v_zpowFn_x3f_704_ = lean_ctor_get(v_s_701_, 3);
v_semiringId_x3f_705_ = lean_ctor_get(v_s_701_, 4);
v_commSemiringInst_706_ = lean_ctor_get(v_s_701_, 5);
v_commRingInst_707_ = lean_ctor_get(v_s_701_, 6);
v_noZeroDivInst_x3f_708_ = lean_ctor_get(v_s_701_, 7);
v_fieldInst_x3f_709_ = lean_ctor_get(v_s_701_, 8);
v_powIdentityInst_x3f_710_ = lean_ctor_get(v_s_701_, 9);
v_isSharedCheck_718_ = !lean_is_exclusive(v_s_701_);
if (v_isSharedCheck_718_ == 0)
{
lean_object* v_unused_719_; 
v_unused_719_ = lean_ctor_get(v_s_701_, 1);
lean_dec(v_unused_719_);
v___x_712_ = v_s_701_;
v_isShared_713_ = v_isSharedCheck_718_;
goto v_resetjp_711_;
}
else
{
lean_inc(v_powIdentityInst_x3f_710_);
lean_inc(v_fieldInst_x3f_709_);
lean_inc(v_noZeroDivInst_x3f_708_);
lean_inc(v_commRingInst_707_);
lean_inc(v_commSemiringInst_706_);
lean_inc(v_semiringId_x3f_705_);
lean_inc(v_zpowFn_x3f_704_);
lean_inc(v_divFn_x3f_703_);
lean_inc(v_toRing_702_);
lean_dec(v_s_701_);
v___x_712_ = lean_box(0);
v_isShared_713_ = v_isSharedCheck_718_;
goto v_resetjp_711_;
}
v_resetjp_711_:
{
lean_object* v___x_714_; lean_object* v___x_716_; 
v___x_714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_714_, 0, v_a_700_);
if (v_isShared_713_ == 0)
{
lean_ctor_set(v___x_712_, 1, v___x_714_);
v___x_716_ = v___x_712_;
goto v_reusejp_715_;
}
else
{
lean_object* v_reuseFailAlloc_717_; 
v_reuseFailAlloc_717_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_717_, 0, v_toRing_702_);
lean_ctor_set(v_reuseFailAlloc_717_, 1, v___x_714_);
lean_ctor_set(v_reuseFailAlloc_717_, 2, v_divFn_x3f_703_);
lean_ctor_set(v_reuseFailAlloc_717_, 3, v_zpowFn_x3f_704_);
lean_ctor_set(v_reuseFailAlloc_717_, 4, v_semiringId_x3f_705_);
lean_ctor_set(v_reuseFailAlloc_717_, 5, v_commSemiringInst_706_);
lean_ctor_set(v_reuseFailAlloc_717_, 6, v_commRingInst_707_);
lean_ctor_set(v_reuseFailAlloc_717_, 7, v_noZeroDivInst_x3f_708_);
lean_ctor_set(v_reuseFailAlloc_717_, 8, v_fieldInst_x3f_709_);
lean_ctor_set(v_reuseFailAlloc_717_, 9, v_powIdentityInst_x3f_710_);
v___x_716_ = v_reuseFailAlloc_717_;
goto v_reusejp_715_;
}
v_reusejp_715_:
{
return v___x_716_;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Sym_Arith_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___closed__8(void){
_start:
{
lean_object* v___x_735_; lean_object* v___x_736_; 
v___x_735_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___closed__7));
v___x_736_ = l_Lean_stringToMessageData(v___x_735_);
return v___x_736_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0(lean_object* v___y_737_, lean_object* v___y_738_, lean_object* v___y_739_, lean_object* v___y_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_, lean_object* v___y_744_, lean_object* v___y_745_, lean_object* v___y_746_, lean_object* v___y_747_){
_start:
{
lean_object* v___x_749_; 
v___x_749_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v___y_737_, v___y_738_, v___y_739_, v___y_740_, v___y_741_, v___y_742_, v___y_743_, v___y_744_, v___y_745_, v___y_746_, v___y_747_);
if (lean_obj_tag(v___x_749_) == 0)
{
lean_object* v_a_750_; lean_object* v___x_752_; uint8_t v_isShared_753_; uint8_t v_isSharedCheck_797_; 
v_a_750_ = lean_ctor_get(v___x_749_, 0);
v_isSharedCheck_797_ = !lean_is_exclusive(v___x_749_);
if (v_isSharedCheck_797_ == 0)
{
v___x_752_ = v___x_749_;
v_isShared_753_ = v_isSharedCheck_797_;
goto v_resetjp_751_;
}
else
{
lean_inc(v_a_750_);
lean_dec(v___x_749_);
v___x_752_ = lean_box(0);
v_isShared_753_ = v_isSharedCheck_797_;
goto v_resetjp_751_;
}
v_resetjp_751_:
{
lean_object* v_fieldInst_x3f_754_; 
v_fieldInst_x3f_754_ = lean_ctor_get(v_a_750_, 8);
if (lean_obj_tag(v_fieldInst_x3f_754_) == 1)
{
lean_object* v_invFn_x3f_755_; 
lean_inc_ref(v_fieldInst_x3f_754_);
v_invFn_x3f_755_ = lean_ctor_get(v_a_750_, 1);
if (lean_obj_tag(v_invFn_x3f_755_) == 1)
{
lean_object* v_val_756_; lean_object* v___x_758_; 
lean_inc_ref(v_invFn_x3f_755_);
lean_dec_ref_known(v_fieldInst_x3f_754_, 1);
lean_dec(v_a_750_);
v_val_756_ = lean_ctor_get(v_invFn_x3f_755_, 0);
lean_inc(v_val_756_);
lean_dec_ref_known(v_invFn_x3f_755_, 1);
if (v_isShared_753_ == 0)
{
lean_ctor_set(v___x_752_, 0, v_val_756_);
v___x_758_ = v___x_752_;
goto v_reusejp_757_;
}
else
{
lean_object* v_reuseFailAlloc_759_; 
v_reuseFailAlloc_759_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_759_, 0, v_val_756_);
v___x_758_ = v_reuseFailAlloc_759_;
goto v_reusejp_757_;
}
v_reusejp_757_:
{
return v___x_758_;
}
}
else
{
lean_object* v_toRing_760_; lean_object* v_val_761_; lean_object* v_type_762_; lean_object* v_u_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v_expectedInst_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; 
lean_del_object(v___x_752_);
v_toRing_760_ = lean_ctor_get(v_a_750_, 0);
lean_inc_ref(v_toRing_760_);
lean_dec(v_a_750_);
v_val_761_ = lean_ctor_get(v_fieldInst_x3f_754_, 0);
lean_inc(v_val_761_);
lean_dec_ref_known(v_fieldInst_x3f_754_, 1);
v_type_762_ = lean_ctor_get(v_toRing_760_, 1);
lean_inc_ref_n(v_type_762_, 2);
v_u_763_ = lean_ctor_get(v_toRing_760_, 2);
lean_inc_n(v_u_763_, 2);
lean_dec_ref(v_toRing_760_);
v___x_764_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___closed__2));
v___x_765_ = lean_box(0);
v___x_766_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_766_, 0, v_u_763_);
lean_ctor_set(v___x_766_, 1, v___x_765_);
v___x_767_ = l_Lean_mkConst(v___x_764_, v___x_766_);
v_expectedInst_768_ = l_Lean_mkAppB(v___x_767_, v_type_762_, v_val_761_);
v___x_769_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___closed__4));
v___x_770_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___closed__6));
v___x_771_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__2(v_type_762_, v_u_763_, v___x_769_, v___x_770_, v_expectedInst_768_, v___y_737_, v___y_738_, v___y_739_, v___y_740_, v___y_741_, v___y_742_, v___y_743_, v___y_744_, v___y_745_, v___y_746_, v___y_747_);
if (lean_obj_tag(v___x_771_) == 0)
{
lean_object* v_a_772_; lean_object* v___f_773_; lean_object* v___x_774_; 
v_a_772_ = lean_ctor_get(v___x_771_, 0);
lean_inc_n(v_a_772_, 2);
lean_dec_ref_known(v___x_771_, 1);
v___f_773_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___lam__0), 2, 1);
lean_closure_set(v___f_773_, 0, v_a_772_);
v___x_774_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(v___f_773_, v___y_737_, v___y_743_);
if (lean_obj_tag(v___x_774_) == 0)
{
lean_object* v___x_776_; uint8_t v_isShared_777_; uint8_t v_isSharedCheck_781_; 
v_isSharedCheck_781_ = !lean_is_exclusive(v___x_774_);
if (v_isSharedCheck_781_ == 0)
{
lean_object* v_unused_782_; 
v_unused_782_ = lean_ctor_get(v___x_774_, 0);
lean_dec(v_unused_782_);
v___x_776_ = v___x_774_;
v_isShared_777_ = v_isSharedCheck_781_;
goto v_resetjp_775_;
}
else
{
lean_dec(v___x_774_);
v___x_776_ = lean_box(0);
v_isShared_777_ = v_isSharedCheck_781_;
goto v_resetjp_775_;
}
v_resetjp_775_:
{
lean_object* v___x_779_; 
if (v_isShared_777_ == 0)
{
lean_ctor_set(v___x_776_, 0, v_a_772_);
v___x_779_ = v___x_776_;
goto v_reusejp_778_;
}
else
{
lean_object* v_reuseFailAlloc_780_; 
v_reuseFailAlloc_780_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_780_, 0, v_a_772_);
v___x_779_ = v_reuseFailAlloc_780_;
goto v_reusejp_778_;
}
v_reusejp_778_:
{
return v___x_779_;
}
}
}
else
{
lean_object* v_a_783_; lean_object* v___x_785_; uint8_t v_isShared_786_; uint8_t v_isSharedCheck_790_; 
lean_dec(v_a_772_);
v_a_783_ = lean_ctor_get(v___x_774_, 0);
v_isSharedCheck_790_ = !lean_is_exclusive(v___x_774_);
if (v_isSharedCheck_790_ == 0)
{
v___x_785_ = v___x_774_;
v_isShared_786_ = v_isSharedCheck_790_;
goto v_resetjp_784_;
}
else
{
lean_inc(v_a_783_);
lean_dec(v___x_774_);
v___x_785_ = lean_box(0);
v_isShared_786_ = v_isSharedCheck_790_;
goto v_resetjp_784_;
}
v_resetjp_784_:
{
lean_object* v___x_788_; 
if (v_isShared_786_ == 0)
{
v___x_788_ = v___x_785_;
goto v_reusejp_787_;
}
else
{
lean_object* v_reuseFailAlloc_789_; 
v_reuseFailAlloc_789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_789_, 0, v_a_783_);
v___x_788_ = v_reuseFailAlloc_789_;
goto v_reusejp_787_;
}
v_reusejp_787_:
{
return v___x_788_;
}
}
}
}
else
{
return v___x_771_;
}
}
}
else
{
lean_object* v_toRing_791_; lean_object* v_type_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; 
lean_del_object(v___x_752_);
v_toRing_791_ = lean_ctor_get(v_a_750_, 0);
lean_inc_ref(v_toRing_791_);
lean_dec(v_a_750_);
v_type_792_ = lean_ctor_get(v_toRing_791_, 1);
lean_inc_ref(v_type_792_);
lean_dec_ref(v_toRing_791_);
v___x_793_ = lean_obj_once(&l_Lean_Meta_Sym_Arith_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___closed__8, &l_Lean_Meta_Sym_Arith_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___closed__8_once, _init_l_Lean_Meta_Sym_Arith_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___closed__8);
v___x_794_ = l_Lean_indentExpr(v_type_792_);
v___x_795_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_795_, 0, v___x_793_);
lean_ctor_set(v___x_795_, 1, v___x_794_);
v___x_796_ = l_Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__2_spec__3_spec__4___redArg(v___x_795_, v___y_744_, v___y_745_, v___y_746_, v___y_747_);
return v___x_796_;
}
}
}
else
{
lean_object* v_a_798_; lean_object* v___x_800_; uint8_t v_isShared_801_; uint8_t v_isSharedCheck_805_; 
v_a_798_ = lean_ctor_get(v___x_749_, 0);
v_isSharedCheck_805_ = !lean_is_exclusive(v___x_749_);
if (v_isSharedCheck_805_ == 0)
{
v___x_800_ = v___x_749_;
v_isShared_801_ = v_isSharedCheck_805_;
goto v_resetjp_799_;
}
else
{
lean_inc(v_a_798_);
lean_dec(v___x_749_);
v___x_800_ = lean_box(0);
v_isShared_801_ = v_isSharedCheck_805_;
goto v_resetjp_799_;
}
v_resetjp_799_:
{
lean_object* v___x_803_; 
if (v_isShared_801_ == 0)
{
v___x_803_ = v___x_800_;
goto v_reusejp_802_;
}
else
{
lean_object* v_reuseFailAlloc_804_; 
v_reuseFailAlloc_804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_804_, 0, v_a_798_);
v___x_803_ = v_reuseFailAlloc_804_;
goto v_reusejp_802_;
}
v_reusejp_802_:
{
return v___x_803_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___boxed(lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_, lean_object* v___y_813_, lean_object* v___y_814_, lean_object* v___y_815_, lean_object* v___y_816_, lean_object* v___y_817_){
_start:
{
lean_object* v_res_818_; 
v_res_818_ = l_Lean_Meta_Sym_Arith_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0(v___y_806_, v___y_807_, v___y_808_, v___y_809_, v___y_810_, v___y_811_, v___y_812_, v___y_813_, v___y_814_, v___y_815_, v___y_816_);
lean_dec(v___y_816_);
lean_dec_ref(v___y_815_);
lean_dec(v___y_814_);
lean_dec_ref(v___y_813_);
lean_dec(v___y_812_);
lean_dec_ref(v___y_811_);
lean_dec(v___y_810_);
lean_dec_ref(v___y_809_);
lean_dec(v___y_808_);
lean_dec(v___y_807_);
lean_dec_ref(v___y_806_);
return v_res_818_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst(lean_object* v_inst_819_, lean_object* v_a_820_, lean_object* v_a_821_, lean_object* v_a_822_, lean_object* v_a_823_, lean_object* v_a_824_, lean_object* v_a_825_, lean_object* v_a_826_, lean_object* v_a_827_, lean_object* v_a_828_, lean_object* v_a_829_, lean_object* v_a_830_){
_start:
{
lean_object* v___x_832_; 
v___x_832_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v_a_820_, v_a_821_, v_a_822_, v_a_823_, v_a_824_, v_a_825_, v_a_826_, v_a_827_, v_a_828_, v_a_829_, v_a_830_);
if (lean_obj_tag(v___x_832_) == 0)
{
lean_object* v_a_833_; lean_object* v___x_835_; uint8_t v_isShared_836_; uint8_t v_isSharedCheck_865_; 
v_a_833_ = lean_ctor_get(v___x_832_, 0);
v_isSharedCheck_865_ = !lean_is_exclusive(v___x_832_);
if (v_isSharedCheck_865_ == 0)
{
v___x_835_ = v___x_832_;
v_isShared_836_ = v_isSharedCheck_865_;
goto v_resetjp_834_;
}
else
{
lean_inc(v_a_833_);
lean_dec(v___x_832_);
v___x_835_ = lean_box(0);
v_isShared_836_ = v_isSharedCheck_865_;
goto v_resetjp_834_;
}
v_resetjp_834_:
{
lean_object* v_fieldInst_x3f_837_; 
v_fieldInst_x3f_837_ = lean_ctor_get(v_a_833_, 8);
lean_inc(v_fieldInst_x3f_837_);
lean_dec(v_a_833_);
if (lean_obj_tag(v_fieldInst_x3f_837_) == 0)
{
uint8_t v___x_838_; lean_object* v___x_839_; lean_object* v___x_841_; 
v___x_838_ = 0;
v___x_839_ = lean_box(v___x_838_);
if (v_isShared_836_ == 0)
{
lean_ctor_set(v___x_835_, 0, v___x_839_);
v___x_841_ = v___x_835_;
goto v_reusejp_840_;
}
else
{
lean_object* v_reuseFailAlloc_842_; 
v_reuseFailAlloc_842_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_842_, 0, v___x_839_);
v___x_841_ = v_reuseFailAlloc_842_;
goto v_reusejp_840_;
}
v_reusejp_840_:
{
return v___x_841_;
}
}
else
{
lean_object* v___x_843_; 
lean_dec_ref_known(v_fieldInst_x3f_837_, 1);
lean_del_object(v___x_835_);
v___x_843_ = l_Lean_Meta_Sym_Arith_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0(v_a_820_, v_a_821_, v_a_822_, v_a_823_, v_a_824_, v_a_825_, v_a_826_, v_a_827_, v_a_828_, v_a_829_, v_a_830_);
if (lean_obj_tag(v___x_843_) == 0)
{
lean_object* v_a_844_; lean_object* v___x_846_; uint8_t v_isShared_847_; uint8_t v_isSharedCheck_856_; 
v_a_844_ = lean_ctor_get(v___x_843_, 0);
v_isSharedCheck_856_ = !lean_is_exclusive(v___x_843_);
if (v_isSharedCheck_856_ == 0)
{
v___x_846_ = v___x_843_;
v_isShared_847_ = v_isSharedCheck_856_;
goto v_resetjp_845_;
}
else
{
lean_inc(v_a_844_);
lean_dec(v___x_843_);
v___x_846_ = lean_box(0);
v_isShared_847_ = v_isSharedCheck_856_;
goto v_resetjp_845_;
}
v_resetjp_845_:
{
lean_object* v___x_848_; size_t v___x_849_; size_t v___x_850_; uint8_t v___x_851_; lean_object* v___x_852_; lean_object* v___x_854_; 
v___x_848_ = l_Lean_Expr_appArg_x21(v_a_844_);
lean_dec(v_a_844_);
v___x_849_ = lean_ptr_addr(v___x_848_);
lean_dec_ref(v___x_848_);
v___x_850_ = lean_ptr_addr(v_inst_819_);
v___x_851_ = lean_usize_dec_eq(v___x_849_, v___x_850_);
v___x_852_ = lean_box(v___x_851_);
if (v_isShared_847_ == 0)
{
lean_ctor_set(v___x_846_, 0, v___x_852_);
v___x_854_ = v___x_846_;
goto v_reusejp_853_;
}
else
{
lean_object* v_reuseFailAlloc_855_; 
v_reuseFailAlloc_855_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_855_, 0, v___x_852_);
v___x_854_ = v_reuseFailAlloc_855_;
goto v_reusejp_853_;
}
v_reusejp_853_:
{
return v___x_854_;
}
}
}
else
{
lean_object* v_a_857_; lean_object* v___x_859_; uint8_t v_isShared_860_; uint8_t v_isSharedCheck_864_; 
v_a_857_ = lean_ctor_get(v___x_843_, 0);
v_isSharedCheck_864_ = !lean_is_exclusive(v___x_843_);
if (v_isSharedCheck_864_ == 0)
{
v___x_859_ = v___x_843_;
v_isShared_860_ = v_isSharedCheck_864_;
goto v_resetjp_858_;
}
else
{
lean_inc(v_a_857_);
lean_dec(v___x_843_);
v___x_859_ = lean_box(0);
v_isShared_860_ = v_isSharedCheck_864_;
goto v_resetjp_858_;
}
v_resetjp_858_:
{
lean_object* v___x_862_; 
if (v_isShared_860_ == 0)
{
v___x_862_ = v___x_859_;
goto v_reusejp_861_;
}
else
{
lean_object* v_reuseFailAlloc_863_; 
v_reuseFailAlloc_863_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_863_, 0, v_a_857_);
v___x_862_ = v_reuseFailAlloc_863_;
goto v_reusejp_861_;
}
v_reusejp_861_:
{
return v___x_862_;
}
}
}
}
}
}
else
{
lean_object* v_a_866_; lean_object* v___x_868_; uint8_t v_isShared_869_; uint8_t v_isSharedCheck_873_; 
v_a_866_ = lean_ctor_get(v___x_832_, 0);
v_isSharedCheck_873_ = !lean_is_exclusive(v___x_832_);
if (v_isSharedCheck_873_ == 0)
{
v___x_868_ = v___x_832_;
v_isShared_869_ = v_isSharedCheck_873_;
goto v_resetjp_867_;
}
else
{
lean_inc(v_a_866_);
lean_dec(v___x_832_);
v___x_868_ = lean_box(0);
v_isShared_869_ = v_isSharedCheck_873_;
goto v_resetjp_867_;
}
v_resetjp_867_:
{
lean_object* v___x_871_; 
if (v_isShared_869_ == 0)
{
v___x_871_ = v___x_868_;
goto v_reusejp_870_;
}
else
{
lean_object* v_reuseFailAlloc_872_; 
v_reuseFailAlloc_872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_872_, 0, v_a_866_);
v___x_871_ = v_reuseFailAlloc_872_;
goto v_reusejp_870_;
}
v_reusejp_870_:
{
return v___x_871_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst___boxed(lean_object* v_inst_874_, lean_object* v_a_875_, lean_object* v_a_876_, lean_object* v_a_877_, lean_object* v_a_878_, lean_object* v_a_879_, lean_object* v_a_880_, lean_object* v_a_881_, lean_object* v_a_882_, lean_object* v_a_883_, lean_object* v_a_884_, lean_object* v_a_885_, lean_object* v_a_886_){
_start:
{
lean_object* v_res_887_; 
v_res_887_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst(v_inst_874_, v_a_875_, v_a_876_, v_a_877_, v_a_878_, v_a_879_, v_a_880_, v_a_881_, v_a_882_, v_a_883_, v_a_884_, v_a_885_);
lean_dec(v_a_885_);
lean_dec_ref(v_a_884_);
lean_dec(v_a_883_);
lean_dec_ref(v_a_882_);
lean_dec(v_a_881_);
lean_dec_ref(v_a_880_);
lean_dec(v_a_879_);
lean_dec_ref(v_a_878_);
lean_dec(v_a_877_);
lean_dec(v_a_876_);
lean_dec_ref(v_a_875_);
lean_dec_ref(v_inst_874_);
return v_res_887_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_pushInvFact___redArg(lean_object* v_expected_888_, lean_object* v_proof_889_, lean_object* v_a_890_, lean_object* v_a_891_, lean_object* v_a_892_, lean_object* v_a_893_, lean_object* v_a_894_, lean_object* v_a_895_, lean_object* v_a_896_){
_start:
{
lean_object* v___x_898_; 
v___x_898_ = l_Lean_Meta_Sym_canon(v_expected_888_, v_a_891_, v_a_892_, v_a_893_, v_a_894_, v_a_895_, v_a_896_);
if (lean_obj_tag(v___x_898_) == 0)
{
lean_object* v_a_899_; lean_object* v___x_900_; 
v_a_899_ = lean_ctor_get(v___x_898_, 0);
lean_inc(v_a_899_);
lean_dec_ref_known(v___x_898_, 1);
v___x_900_ = l_Lean_Meta_Sym_shareCommon(v_a_899_, v_a_891_, v_a_892_, v_a_893_, v_a_894_, v_a_895_, v_a_896_);
if (lean_obj_tag(v___x_900_) == 0)
{
lean_object* v_a_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; 
v_a_901_ = lean_ctor_get(v___x_900_, 0);
lean_inc_n(v_a_901_, 2);
lean_dec_ref_known(v___x_900_, 1);
v___x_902_ = l_Lean_Meta_mkExpectedPropHint(v_proof_889_, v_a_901_);
v___x_903_ = lean_unsigned_to_nat(0u);
v___x_904_ = l_Lean_Meta_Grind_pushNewFactCore___redArg(v_a_901_, v___x_902_, v___x_903_, v_a_890_);
return v___x_904_;
}
else
{
lean_object* v_a_905_; lean_object* v___x_907_; uint8_t v_isShared_908_; uint8_t v_isSharedCheck_912_; 
lean_dec_ref(v_proof_889_);
v_a_905_ = lean_ctor_get(v___x_900_, 0);
v_isSharedCheck_912_ = !lean_is_exclusive(v___x_900_);
if (v_isSharedCheck_912_ == 0)
{
v___x_907_ = v___x_900_;
v_isShared_908_ = v_isSharedCheck_912_;
goto v_resetjp_906_;
}
else
{
lean_inc(v_a_905_);
lean_dec(v___x_900_);
v___x_907_ = lean_box(0);
v_isShared_908_ = v_isSharedCheck_912_;
goto v_resetjp_906_;
}
v_resetjp_906_:
{
lean_object* v___x_910_; 
if (v_isShared_908_ == 0)
{
v___x_910_ = v___x_907_;
goto v_reusejp_909_;
}
else
{
lean_object* v_reuseFailAlloc_911_; 
v_reuseFailAlloc_911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_911_, 0, v_a_905_);
v___x_910_ = v_reuseFailAlloc_911_;
goto v_reusejp_909_;
}
v_reusejp_909_:
{
return v___x_910_;
}
}
}
}
else
{
lean_object* v_a_913_; lean_object* v___x_915_; uint8_t v_isShared_916_; uint8_t v_isSharedCheck_920_; 
lean_dec_ref(v_proof_889_);
v_a_913_ = lean_ctor_get(v___x_898_, 0);
v_isSharedCheck_920_ = !lean_is_exclusive(v___x_898_);
if (v_isSharedCheck_920_ == 0)
{
v___x_915_ = v___x_898_;
v_isShared_916_ = v_isSharedCheck_920_;
goto v_resetjp_914_;
}
else
{
lean_inc(v_a_913_);
lean_dec(v___x_898_);
v___x_915_ = lean_box(0);
v_isShared_916_ = v_isSharedCheck_920_;
goto v_resetjp_914_;
}
v_resetjp_914_:
{
lean_object* v___x_918_; 
if (v_isShared_916_ == 0)
{
v___x_918_ = v___x_915_;
goto v_reusejp_917_;
}
else
{
lean_object* v_reuseFailAlloc_919_; 
v_reuseFailAlloc_919_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_919_, 0, v_a_913_);
v___x_918_ = v_reuseFailAlloc_919_;
goto v_reusejp_917_;
}
v_reusejp_917_:
{
return v___x_918_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_pushInvFact___redArg___boxed(lean_object* v_expected_921_, lean_object* v_proof_922_, lean_object* v_a_923_, lean_object* v_a_924_, lean_object* v_a_925_, lean_object* v_a_926_, lean_object* v_a_927_, lean_object* v_a_928_, lean_object* v_a_929_, lean_object* v_a_930_){
_start:
{
lean_object* v_res_931_; 
v_res_931_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_pushInvFact___redArg(v_expected_921_, v_proof_922_, v_a_923_, v_a_924_, v_a_925_, v_a_926_, v_a_927_, v_a_928_, v_a_929_);
lean_dec(v_a_929_);
lean_dec_ref(v_a_928_);
lean_dec(v_a_927_);
lean_dec_ref(v_a_926_);
lean_dec(v_a_925_);
lean_dec_ref(v_a_924_);
lean_dec(v_a_923_);
return v_res_931_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_pushInvFact(lean_object* v_expected_932_, lean_object* v_proof_933_, lean_object* v_a_934_, lean_object* v_a_935_, lean_object* v_a_936_, lean_object* v_a_937_, lean_object* v_a_938_, lean_object* v_a_939_, lean_object* v_a_940_, lean_object* v_a_941_, lean_object* v_a_942_, lean_object* v_a_943_, lean_object* v_a_944_){
_start:
{
lean_object* v___x_946_; 
v___x_946_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_pushInvFact___redArg(v_expected_932_, v_proof_933_, v_a_935_, v_a_939_, v_a_940_, v_a_941_, v_a_942_, v_a_943_, v_a_944_);
return v___x_946_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_pushInvFact___boxed(lean_object* v_expected_947_, lean_object* v_proof_948_, lean_object* v_a_949_, lean_object* v_a_950_, lean_object* v_a_951_, lean_object* v_a_952_, lean_object* v_a_953_, lean_object* v_a_954_, lean_object* v_a_955_, lean_object* v_a_956_, lean_object* v_a_957_, lean_object* v_a_958_, lean_object* v_a_959_, lean_object* v_a_960_){
_start:
{
lean_object* v_res_961_; 
v_res_961_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_pushInvFact(v_expected_947_, v_proof_948_, v_a_949_, v_a_950_, v_a_951_, v_a_952_, v_a_953_, v_a_954_, v_a_955_, v_a_956_, v_a_957_, v_a_958_, v_a_959_);
lean_dec(v_a_959_);
lean_dec_ref(v_a_958_);
lean_dec(v_a_957_);
lean_dec_ref(v_a_956_);
lean_dec(v_a_955_);
lean_dec_ref(v_a_954_);
lean_dec(v_a_953_);
lean_dec_ref(v_a_952_);
lean_dec(v_a_951_);
lean_dec(v_a_950_);
lean_dec_ref(v_a_949_);
return v_res_961_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0_spec__1_spec__5___redArg(lean_object* v_x_962_, lean_object* v_x_963_, lean_object* v_x_964_, lean_object* v_x_965_){
_start:
{
lean_object* v_ks_966_; lean_object* v_vs_967_; lean_object* v___x_969_; uint8_t v_isShared_970_; uint8_t v_isSharedCheck_991_; 
v_ks_966_ = lean_ctor_get(v_x_962_, 0);
v_vs_967_ = lean_ctor_get(v_x_962_, 1);
v_isSharedCheck_991_ = !lean_is_exclusive(v_x_962_);
if (v_isSharedCheck_991_ == 0)
{
v___x_969_ = v_x_962_;
v_isShared_970_ = v_isSharedCheck_991_;
goto v_resetjp_968_;
}
else
{
lean_inc(v_vs_967_);
lean_inc(v_ks_966_);
lean_dec(v_x_962_);
v___x_969_ = lean_box(0);
v_isShared_970_ = v_isSharedCheck_991_;
goto v_resetjp_968_;
}
v_resetjp_968_:
{
lean_object* v___x_971_; uint8_t v___x_972_; 
v___x_971_ = lean_array_get_size(v_ks_966_);
v___x_972_ = lean_nat_dec_lt(v_x_963_, v___x_971_);
if (v___x_972_ == 0)
{
lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_976_; 
lean_dec(v_x_963_);
v___x_973_ = lean_array_push(v_ks_966_, v_x_964_);
v___x_974_ = lean_array_push(v_vs_967_, v_x_965_);
if (v_isShared_970_ == 0)
{
lean_ctor_set(v___x_969_, 1, v___x_974_);
lean_ctor_set(v___x_969_, 0, v___x_973_);
v___x_976_ = v___x_969_;
goto v_reusejp_975_;
}
else
{
lean_object* v_reuseFailAlloc_977_; 
v_reuseFailAlloc_977_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_977_, 0, v___x_973_);
lean_ctor_set(v_reuseFailAlloc_977_, 1, v___x_974_);
v___x_976_ = v_reuseFailAlloc_977_;
goto v_reusejp_975_;
}
v_reusejp_975_:
{
return v___x_976_;
}
}
else
{
lean_object* v_k_x27_978_; uint8_t v___x_979_; 
v_k_x27_978_ = lean_array_fget_borrowed(v_ks_966_, v_x_963_);
v___x_979_ = lean_expr_eqv(v_x_964_, v_k_x27_978_);
if (v___x_979_ == 0)
{
lean_object* v___x_981_; 
if (v_isShared_970_ == 0)
{
v___x_981_ = v___x_969_;
goto v_reusejp_980_;
}
else
{
lean_object* v_reuseFailAlloc_985_; 
v_reuseFailAlloc_985_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_985_, 0, v_ks_966_);
lean_ctor_set(v_reuseFailAlloc_985_, 1, v_vs_967_);
v___x_981_ = v_reuseFailAlloc_985_;
goto v_reusejp_980_;
}
v_reusejp_980_:
{
lean_object* v___x_982_; lean_object* v___x_983_; 
v___x_982_ = lean_unsigned_to_nat(1u);
v___x_983_ = lean_nat_add(v_x_963_, v___x_982_);
lean_dec(v_x_963_);
v_x_962_ = v___x_981_;
v_x_963_ = v___x_983_;
goto _start;
}
}
else
{
lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_989_; 
v___x_986_ = lean_array_fset(v_ks_966_, v_x_963_, v_x_964_);
v___x_987_ = lean_array_fset(v_vs_967_, v_x_963_, v_x_965_);
lean_dec(v_x_963_);
if (v_isShared_970_ == 0)
{
lean_ctor_set(v___x_969_, 1, v___x_987_);
lean_ctor_set(v___x_969_, 0, v___x_986_);
v___x_989_ = v___x_969_;
goto v_reusejp_988_;
}
else
{
lean_object* v_reuseFailAlloc_990_; 
v_reuseFailAlloc_990_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_990_, 0, v___x_986_);
lean_ctor_set(v_reuseFailAlloc_990_, 1, v___x_987_);
v___x_989_ = v_reuseFailAlloc_990_;
goto v_reusejp_988_;
}
v_reusejp_988_:
{
return v___x_989_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0_spec__1___redArg(lean_object* v_n_992_, lean_object* v_k_993_, lean_object* v_v_994_){
_start:
{
lean_object* v___x_995_; lean_object* v___x_996_; 
v___x_995_ = lean_unsigned_to_nat(0u);
v___x_996_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0_spec__1_spec__5___redArg(v_n_992_, v___x_995_, v_k_993_, v_v_994_);
return v___x_996_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_997_; 
v___x_997_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_997_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg(lean_object* v_x_998_, size_t v_x_999_, size_t v_x_1000_, lean_object* v_x_1001_, lean_object* v_x_1002_){
_start:
{
if (lean_obj_tag(v_x_998_) == 0)
{
lean_object* v_es_1003_; size_t v___x_1004_; size_t v___x_1005_; lean_object* v_j_1006_; lean_object* v___x_1007_; uint8_t v___x_1008_; 
v_es_1003_ = lean_ctor_get(v_x_998_, 0);
v___x_1004_ = ((size_t)31ULL);
v___x_1005_ = lean_usize_land(v_x_999_, v___x_1004_);
v_j_1006_ = lean_usize_to_nat(v___x_1005_);
v___x_1007_ = lean_array_get_size(v_es_1003_);
v___x_1008_ = lean_nat_dec_lt(v_j_1006_, v___x_1007_);
if (v___x_1008_ == 0)
{
lean_dec(v_j_1006_);
lean_dec(v_x_1002_);
lean_dec_ref(v_x_1001_);
return v_x_998_;
}
else
{
lean_object* v___x_1010_; uint8_t v_isShared_1011_; uint8_t v_isSharedCheck_1047_; 
lean_inc_ref(v_es_1003_);
v_isSharedCheck_1047_ = !lean_is_exclusive(v_x_998_);
if (v_isSharedCheck_1047_ == 0)
{
lean_object* v_unused_1048_; 
v_unused_1048_ = lean_ctor_get(v_x_998_, 0);
lean_dec(v_unused_1048_);
v___x_1010_ = v_x_998_;
v_isShared_1011_ = v_isSharedCheck_1047_;
goto v_resetjp_1009_;
}
else
{
lean_dec(v_x_998_);
v___x_1010_ = lean_box(0);
v_isShared_1011_ = v_isSharedCheck_1047_;
goto v_resetjp_1009_;
}
v_resetjp_1009_:
{
lean_object* v_v_1012_; lean_object* v___x_1013_; lean_object* v_xs_x27_1014_; lean_object* v___y_1016_; 
v_v_1012_ = lean_array_fget(v_es_1003_, v_j_1006_);
v___x_1013_ = lean_box(0);
v_xs_x27_1014_ = lean_array_fset(v_es_1003_, v_j_1006_, v___x_1013_);
switch(lean_obj_tag(v_v_1012_))
{
case 0:
{
lean_object* v_key_1021_; lean_object* v_val_1022_; lean_object* v___x_1024_; uint8_t v_isShared_1025_; uint8_t v_isSharedCheck_1032_; 
v_key_1021_ = lean_ctor_get(v_v_1012_, 0);
v_val_1022_ = lean_ctor_get(v_v_1012_, 1);
v_isSharedCheck_1032_ = !lean_is_exclusive(v_v_1012_);
if (v_isSharedCheck_1032_ == 0)
{
v___x_1024_ = v_v_1012_;
v_isShared_1025_ = v_isSharedCheck_1032_;
goto v_resetjp_1023_;
}
else
{
lean_inc(v_val_1022_);
lean_inc(v_key_1021_);
lean_dec(v_v_1012_);
v___x_1024_ = lean_box(0);
v_isShared_1025_ = v_isSharedCheck_1032_;
goto v_resetjp_1023_;
}
v_resetjp_1023_:
{
uint8_t v___x_1026_; 
v___x_1026_ = lean_expr_eqv(v_x_1001_, v_key_1021_);
if (v___x_1026_ == 0)
{
lean_object* v___x_1027_; lean_object* v___x_1028_; 
lean_del_object(v___x_1024_);
v___x_1027_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1021_, v_val_1022_, v_x_1001_, v_x_1002_);
v___x_1028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1028_, 0, v___x_1027_);
v___y_1016_ = v___x_1028_;
goto v___jp_1015_;
}
else
{
lean_object* v___x_1030_; 
lean_dec(v_val_1022_);
lean_dec(v_key_1021_);
if (v_isShared_1025_ == 0)
{
lean_ctor_set(v___x_1024_, 1, v_x_1002_);
lean_ctor_set(v___x_1024_, 0, v_x_1001_);
v___x_1030_ = v___x_1024_;
goto v_reusejp_1029_;
}
else
{
lean_object* v_reuseFailAlloc_1031_; 
v_reuseFailAlloc_1031_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1031_, 0, v_x_1001_);
lean_ctor_set(v_reuseFailAlloc_1031_, 1, v_x_1002_);
v___x_1030_ = v_reuseFailAlloc_1031_;
goto v_reusejp_1029_;
}
v_reusejp_1029_:
{
v___y_1016_ = v___x_1030_;
goto v___jp_1015_;
}
}
}
}
case 1:
{
lean_object* v_node_1033_; lean_object* v___x_1035_; uint8_t v_isShared_1036_; uint8_t v_isSharedCheck_1045_; 
v_node_1033_ = lean_ctor_get(v_v_1012_, 0);
v_isSharedCheck_1045_ = !lean_is_exclusive(v_v_1012_);
if (v_isSharedCheck_1045_ == 0)
{
v___x_1035_ = v_v_1012_;
v_isShared_1036_ = v_isSharedCheck_1045_;
goto v_resetjp_1034_;
}
else
{
lean_inc(v_node_1033_);
lean_dec(v_v_1012_);
v___x_1035_ = lean_box(0);
v_isShared_1036_ = v_isSharedCheck_1045_;
goto v_resetjp_1034_;
}
v_resetjp_1034_:
{
size_t v___x_1037_; size_t v___x_1038_; size_t v___x_1039_; size_t v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1043_; 
v___x_1037_ = ((size_t)5ULL);
v___x_1038_ = lean_usize_shift_right(v_x_999_, v___x_1037_);
v___x_1039_ = ((size_t)1ULL);
v___x_1040_ = lean_usize_add(v_x_1000_, v___x_1039_);
v___x_1041_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg(v_node_1033_, v___x_1038_, v___x_1040_, v_x_1001_, v_x_1002_);
if (v_isShared_1036_ == 0)
{
lean_ctor_set(v___x_1035_, 0, v___x_1041_);
v___x_1043_ = v___x_1035_;
goto v_reusejp_1042_;
}
else
{
lean_object* v_reuseFailAlloc_1044_; 
v_reuseFailAlloc_1044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1044_, 0, v___x_1041_);
v___x_1043_ = v_reuseFailAlloc_1044_;
goto v_reusejp_1042_;
}
v_reusejp_1042_:
{
v___y_1016_ = v___x_1043_;
goto v___jp_1015_;
}
}
}
default: 
{
lean_object* v___x_1046_; 
v___x_1046_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1046_, 0, v_x_1001_);
lean_ctor_set(v___x_1046_, 1, v_x_1002_);
v___y_1016_ = v___x_1046_;
goto v___jp_1015_;
}
}
v___jp_1015_:
{
lean_object* v___x_1017_; lean_object* v___x_1019_; 
v___x_1017_ = lean_array_fset(v_xs_x27_1014_, v_j_1006_, v___y_1016_);
lean_dec(v_j_1006_);
if (v_isShared_1011_ == 0)
{
lean_ctor_set(v___x_1010_, 0, v___x_1017_);
v___x_1019_ = v___x_1010_;
goto v_reusejp_1018_;
}
else
{
lean_object* v_reuseFailAlloc_1020_; 
v_reuseFailAlloc_1020_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1020_, 0, v___x_1017_);
v___x_1019_ = v_reuseFailAlloc_1020_;
goto v_reusejp_1018_;
}
v_reusejp_1018_:
{
return v___x_1019_;
}
}
}
}
}
else
{
lean_object* v_ks_1049_; lean_object* v_vs_1050_; lean_object* v___x_1052_; uint8_t v_isShared_1053_; uint8_t v_isSharedCheck_1068_; 
v_ks_1049_ = lean_ctor_get(v_x_998_, 0);
v_vs_1050_ = lean_ctor_get(v_x_998_, 1);
v_isSharedCheck_1068_ = !lean_is_exclusive(v_x_998_);
if (v_isSharedCheck_1068_ == 0)
{
v___x_1052_ = v_x_998_;
v_isShared_1053_ = v_isSharedCheck_1068_;
goto v_resetjp_1051_;
}
else
{
lean_inc(v_vs_1050_);
lean_inc(v_ks_1049_);
lean_dec(v_x_998_);
v___x_1052_ = lean_box(0);
v_isShared_1053_ = v_isSharedCheck_1068_;
goto v_resetjp_1051_;
}
v_resetjp_1051_:
{
lean_object* v___x_1055_; 
if (v_isShared_1053_ == 0)
{
v___x_1055_ = v___x_1052_;
goto v_reusejp_1054_;
}
else
{
lean_object* v_reuseFailAlloc_1067_; 
v_reuseFailAlloc_1067_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1067_, 0, v_ks_1049_);
lean_ctor_set(v_reuseFailAlloc_1067_, 1, v_vs_1050_);
v___x_1055_ = v_reuseFailAlloc_1067_;
goto v_reusejp_1054_;
}
v_reusejp_1054_:
{
lean_object* v_newNode_1056_; size_t v___x_1057_; uint8_t v___x_1058_; 
v_newNode_1056_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0_spec__1___redArg(v___x_1055_, v_x_1001_, v_x_1002_);
v___x_1057_ = ((size_t)7ULL);
v___x_1058_ = lean_usize_dec_le(v___x_1057_, v_x_1000_);
if (v___x_1058_ == 0)
{
lean_object* v___x_1059_; lean_object* v___x_1060_; uint8_t v___x_1061_; 
v___x_1059_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1056_);
v___x_1060_ = lean_unsigned_to_nat(4u);
v___x_1061_ = lean_nat_dec_lt(v___x_1059_, v___x_1060_);
lean_dec(v___x_1059_);
if (v___x_1061_ == 0)
{
lean_object* v_ks_1062_; lean_object* v_vs_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; 
v_ks_1062_ = lean_ctor_get(v_newNode_1056_, 0);
lean_inc_ref(v_ks_1062_);
v_vs_1063_ = lean_ctor_get(v_newNode_1056_, 1);
lean_inc_ref(v_vs_1063_);
lean_dec_ref(v_newNode_1056_);
v___x_1064_ = lean_unsigned_to_nat(0u);
v___x_1065_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg___closed__0);
v___x_1066_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0_spec__2___redArg(v_x_1000_, v_ks_1062_, v_vs_1063_, v___x_1064_, v___x_1065_);
lean_dec_ref(v_vs_1063_);
lean_dec_ref(v_ks_1062_);
return v___x_1066_;
}
else
{
return v_newNode_1056_;
}
}
else
{
return v_newNode_1056_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0_spec__2___redArg(size_t v_depth_1069_, lean_object* v_keys_1070_, lean_object* v_vals_1071_, lean_object* v_i_1072_, lean_object* v_entries_1073_){
_start:
{
lean_object* v___x_1074_; uint8_t v___x_1075_; 
v___x_1074_ = lean_array_get_size(v_keys_1070_);
v___x_1075_ = lean_nat_dec_lt(v_i_1072_, v___x_1074_);
if (v___x_1075_ == 0)
{
lean_dec(v_i_1072_);
return v_entries_1073_;
}
else
{
lean_object* v_k_1076_; lean_object* v_v_1077_; uint64_t v___x_1078_; size_t v_h_1079_; size_t v___x_1080_; lean_object* v___x_1081_; size_t v___x_1082_; size_t v___x_1083_; size_t v___x_1084_; size_t v_h_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; 
v_k_1076_ = lean_array_fget_borrowed(v_keys_1070_, v_i_1072_);
v_v_1077_ = lean_array_fget_borrowed(v_vals_1071_, v_i_1072_);
v___x_1078_ = l_Lean_Expr_hash(v_k_1076_);
v_h_1079_ = lean_uint64_to_usize(v___x_1078_);
v___x_1080_ = ((size_t)5ULL);
v___x_1081_ = lean_unsigned_to_nat(1u);
v___x_1082_ = ((size_t)1ULL);
v___x_1083_ = lean_usize_sub(v_depth_1069_, v___x_1082_);
v___x_1084_ = lean_usize_mul(v___x_1080_, v___x_1083_);
v_h_1085_ = lean_usize_shift_right(v_h_1079_, v___x_1084_);
v___x_1086_ = lean_nat_add(v_i_1072_, v___x_1081_);
lean_dec(v_i_1072_);
lean_inc(v_v_1077_);
lean_inc(v_k_1076_);
v___x_1087_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg(v_entries_1073_, v_h_1085_, v_depth_1069_, v_k_1076_, v_v_1077_);
v_i_1072_ = v___x_1086_;
v_entries_1073_ = v___x_1087_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_1089_, lean_object* v_keys_1090_, lean_object* v_vals_1091_, lean_object* v_i_1092_, lean_object* v_entries_1093_){
_start:
{
size_t v_depth_boxed_1094_; lean_object* v_res_1095_; 
v_depth_boxed_1094_ = lean_unbox_usize(v_depth_1089_);
lean_dec(v_depth_1089_);
v_res_1095_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0_spec__2___redArg(v_depth_boxed_1094_, v_keys_1090_, v_vals_1091_, v_i_1092_, v_entries_1093_);
lean_dec_ref(v_vals_1091_);
lean_dec_ref(v_keys_1090_);
return v_res_1095_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg___boxed(lean_object* v_x_1096_, lean_object* v_x_1097_, lean_object* v_x_1098_, lean_object* v_x_1099_, lean_object* v_x_1100_){
_start:
{
size_t v_x_78376__boxed_1101_; size_t v_x_78377__boxed_1102_; lean_object* v_res_1103_; 
v_x_78376__boxed_1101_ = lean_unbox_usize(v_x_1097_);
lean_dec(v_x_1097_);
v_x_78377__boxed_1102_ = lean_unbox_usize(v_x_1098_);
lean_dec(v_x_1098_);
v_res_1103_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg(v_x_1096_, v_x_78376__boxed_1101_, v_x_78377__boxed_1102_, v_x_1099_, v_x_1100_);
return v_res_1103_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0___redArg(lean_object* v_x_1104_, lean_object* v_x_1105_, lean_object* v_x_1106_){
_start:
{
uint64_t v___x_1107_; size_t v___x_1108_; size_t v___x_1109_; lean_object* v___x_1110_; 
v___x_1107_ = l_Lean_Expr_hash(v_x_1105_);
v___x_1108_ = lean_uint64_to_usize(v___x_1107_);
v___x_1109_ = ((size_t)1ULL);
v___x_1110_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg(v_x_1104_, v___x_1108_, v___x_1109_, v_x_1105_, v_x_1106_);
return v___x_1110_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___lam__0(lean_object* v_a_1111_, lean_object* v_s_1112_){
_start:
{
lean_object* v_toRingState_1113_; lean_object* v_denoteEntries_1114_; lean_object* v_nextId_1115_; lean_object* v_steps_1116_; lean_object* v_queue_1117_; lean_object* v_basis_1118_; lean_object* v_diseqs_1119_; uint8_t v_recheck_1120_; lean_object* v_invSet_1121_; lean_object* v_powIdentityVarCount_1122_; lean_object* v_numEq0_x3f_1123_; uint8_t v_numEq0Updated_1124_; lean_object* v___x_1126_; uint8_t v_isShared_1127_; uint8_t v_isSharedCheck_1133_; 
v_toRingState_1113_ = lean_ctor_get(v_s_1112_, 0);
v_denoteEntries_1114_ = lean_ctor_get(v_s_1112_, 1);
v_nextId_1115_ = lean_ctor_get(v_s_1112_, 2);
v_steps_1116_ = lean_ctor_get(v_s_1112_, 3);
v_queue_1117_ = lean_ctor_get(v_s_1112_, 4);
v_basis_1118_ = lean_ctor_get(v_s_1112_, 5);
v_diseqs_1119_ = lean_ctor_get(v_s_1112_, 6);
v_recheck_1120_ = lean_ctor_get_uint8(v_s_1112_, sizeof(void*)*10);
v_invSet_1121_ = lean_ctor_get(v_s_1112_, 7);
v_powIdentityVarCount_1122_ = lean_ctor_get(v_s_1112_, 8);
v_numEq0_x3f_1123_ = lean_ctor_get(v_s_1112_, 9);
v_numEq0Updated_1124_ = lean_ctor_get_uint8(v_s_1112_, sizeof(void*)*10 + 1);
v_isSharedCheck_1133_ = !lean_is_exclusive(v_s_1112_);
if (v_isSharedCheck_1133_ == 0)
{
v___x_1126_ = v_s_1112_;
v_isShared_1127_ = v_isSharedCheck_1133_;
goto v_resetjp_1125_;
}
else
{
lean_inc(v_numEq0_x3f_1123_);
lean_inc(v_powIdentityVarCount_1122_);
lean_inc(v_invSet_1121_);
lean_inc(v_diseqs_1119_);
lean_inc(v_basis_1118_);
lean_inc(v_queue_1117_);
lean_inc(v_steps_1116_);
lean_inc(v_nextId_1115_);
lean_inc(v_denoteEntries_1114_);
lean_inc(v_toRingState_1113_);
lean_dec(v_s_1112_);
v___x_1126_ = lean_box(0);
v_isShared_1127_ = v_isSharedCheck_1133_;
goto v_resetjp_1125_;
}
v_resetjp_1125_:
{
lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1131_; 
v___x_1128_ = lean_box(0);
v___x_1129_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0___redArg(v_invSet_1121_, v_a_1111_, v___x_1128_);
if (v_isShared_1127_ == 0)
{
lean_ctor_set(v___x_1126_, 7, v___x_1129_);
v___x_1131_ = v___x_1126_;
goto v_reusejp_1130_;
}
else
{
lean_object* v_reuseFailAlloc_1132_; 
v_reuseFailAlloc_1132_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v_reuseFailAlloc_1132_, 0, v_toRingState_1113_);
lean_ctor_set(v_reuseFailAlloc_1132_, 1, v_denoteEntries_1114_);
lean_ctor_set(v_reuseFailAlloc_1132_, 2, v_nextId_1115_);
lean_ctor_set(v_reuseFailAlloc_1132_, 3, v_steps_1116_);
lean_ctor_set(v_reuseFailAlloc_1132_, 4, v_queue_1117_);
lean_ctor_set(v_reuseFailAlloc_1132_, 5, v_basis_1118_);
lean_ctor_set(v_reuseFailAlloc_1132_, 6, v_diseqs_1119_);
lean_ctor_set(v_reuseFailAlloc_1132_, 7, v___x_1129_);
lean_ctor_set(v_reuseFailAlloc_1132_, 8, v_powIdentityVarCount_1122_);
lean_ctor_set(v_reuseFailAlloc_1132_, 9, v_numEq0_x3f_1123_);
lean_ctor_set_uint8(v_reuseFailAlloc_1132_, sizeof(void*)*10, v_recheck_1120_);
lean_ctor_set_uint8(v_reuseFailAlloc_1132_, sizeof(void*)*10 + 1, v_numEq0Updated_1124_);
v___x_1131_ = v_reuseFailAlloc_1132_;
goto v_reusejp_1130_;
}
v_reusejp_1130_:
{
return v___x_1131_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1_spec__2_spec__5___redArg(lean_object* v_keys_1134_, lean_object* v_i_1135_, lean_object* v_k_1136_){
_start:
{
lean_object* v___x_1137_; uint8_t v___x_1138_; 
v___x_1137_ = lean_array_get_size(v_keys_1134_);
v___x_1138_ = lean_nat_dec_lt(v_i_1135_, v___x_1137_);
if (v___x_1138_ == 0)
{
lean_dec(v_i_1135_);
return v___x_1138_;
}
else
{
lean_object* v_k_x27_1139_; uint8_t v___x_1140_; 
v_k_x27_1139_ = lean_array_fget_borrowed(v_keys_1134_, v_i_1135_);
v___x_1140_ = lean_expr_eqv(v_k_1136_, v_k_x27_1139_);
if (v___x_1140_ == 0)
{
lean_object* v___x_1141_; lean_object* v___x_1142_; 
v___x_1141_ = lean_unsigned_to_nat(1u);
v___x_1142_ = lean_nat_add(v_i_1135_, v___x_1141_);
lean_dec(v_i_1135_);
v_i_1135_ = v___x_1142_;
goto _start;
}
else
{
lean_dec(v_i_1135_);
return v___x_1138_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_keys_1144_, lean_object* v_i_1145_, lean_object* v_k_1146_){
_start:
{
uint8_t v_res_1147_; lean_object* v_r_1148_; 
v_res_1147_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1_spec__2_spec__5___redArg(v_keys_1144_, v_i_1145_, v_k_1146_);
lean_dec_ref(v_k_1146_);
lean_dec_ref(v_keys_1144_);
v_r_1148_ = lean_box(v_res_1147_);
return v_r_1148_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1_spec__2___redArg(lean_object* v_x_1149_, size_t v_x_1150_, lean_object* v_x_1151_){
_start:
{
if (lean_obj_tag(v_x_1149_) == 0)
{
lean_object* v_es_1152_; lean_object* v___x_1153_; size_t v___x_1154_; size_t v___x_1155_; lean_object* v_j_1156_; lean_object* v___x_1157_; 
v_es_1152_ = lean_ctor_get(v_x_1149_, 0);
v___x_1153_ = lean_box(2);
v___x_1154_ = ((size_t)31ULL);
v___x_1155_ = lean_usize_land(v_x_1150_, v___x_1154_);
v_j_1156_ = lean_usize_to_nat(v___x_1155_);
v___x_1157_ = lean_array_get_borrowed(v___x_1153_, v_es_1152_, v_j_1156_);
lean_dec(v_j_1156_);
switch(lean_obj_tag(v___x_1157_))
{
case 0:
{
lean_object* v_key_1158_; uint8_t v___x_1159_; 
v_key_1158_ = lean_ctor_get(v___x_1157_, 0);
v___x_1159_ = lean_expr_eqv(v_x_1151_, v_key_1158_);
return v___x_1159_;
}
case 1:
{
lean_object* v_node_1160_; size_t v___x_1161_; size_t v___x_1162_; 
v_node_1160_ = lean_ctor_get(v___x_1157_, 0);
v___x_1161_ = ((size_t)5ULL);
v___x_1162_ = lean_usize_shift_right(v_x_1150_, v___x_1161_);
v_x_1149_ = v_node_1160_;
v_x_1150_ = v___x_1162_;
goto _start;
}
default: 
{
uint8_t v___x_1164_; 
v___x_1164_ = 0;
return v___x_1164_;
}
}
}
else
{
lean_object* v_ks_1165_; lean_object* v___x_1166_; uint8_t v___x_1167_; 
v_ks_1165_ = lean_ctor_get(v_x_1149_, 0);
v___x_1166_ = lean_unsigned_to_nat(0u);
v___x_1167_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1_spec__2_spec__5___redArg(v_ks_1165_, v___x_1166_, v_x_1151_);
return v___x_1167_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1_spec__2___redArg___boxed(lean_object* v_x_1168_, lean_object* v_x_1169_, lean_object* v_x_1170_){
_start:
{
size_t v_x_78572__boxed_1171_; uint8_t v_res_1172_; lean_object* v_r_1173_; 
v_x_78572__boxed_1171_ = lean_unbox_usize(v_x_1169_);
lean_dec(v_x_1169_);
v_res_1172_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1_spec__2___redArg(v_x_1168_, v_x_78572__boxed_1171_, v_x_1170_);
lean_dec_ref(v_x_1170_);
lean_dec_ref(v_x_1168_);
v_r_1173_ = lean_box(v_res_1172_);
return v_r_1173_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1___redArg(lean_object* v_x_1174_, lean_object* v_x_1175_){
_start:
{
uint64_t v___x_1176_; size_t v___x_1177_; uint8_t v___x_1178_; 
v___x_1176_ = l_Lean_Expr_hash(v_x_1175_);
v___x_1177_ = lean_uint64_to_usize(v___x_1176_);
v___x_1178_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1_spec__2___redArg(v_x_1174_, v___x_1177_, v_x_1175_);
return v___x_1178_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1___redArg___boxed(lean_object* v_x_1179_, lean_object* v_x_1180_){
_start:
{
uint8_t v_res_1181_; lean_object* v_r_1182_; 
v_res_1181_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1___redArg(v_x_1179_, v_x_1180_);
lean_dec_ref(v_x_1180_);
lean_dec_ref(v_x_1179_);
v_r_1182_ = lean_box(v_res_1181_);
return v_r_1182_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___at___00Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__2_spec__4(lean_object* v_type_1183_, lean_object* v_u_1184_, lean_object* v_instDeclName_1185_, lean_object* v_declName_1186_, lean_object* v_expectedInst_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_){
_start:
{
lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; 
v___x_1200_ = lean_box(0);
lean_inc_n(v_u_1184_, 2);
v___x_1201_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1201_, 0, v_u_1184_);
lean_ctor_set(v___x_1201_, 1, v___x_1200_);
v___x_1202_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1202_, 0, v_u_1184_);
lean_ctor_set(v___x_1202_, 1, v___x_1201_);
v___x_1203_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1203_, 0, v_u_1184_);
lean_ctor_set(v___x_1203_, 1, v___x_1202_);
lean_inc_ref(v___x_1203_);
v___x_1204_ = l_Lean_mkConst(v_instDeclName_1185_, v___x_1203_);
lean_inc_ref_n(v_type_1183_, 3);
v___x_1205_ = l_Lean_mkApp3(v___x_1204_, v_type_1183_, v_type_1183_, v_type_1183_);
v___x_1206_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__2_spec__3(v___x_1205_, v___y_1188_, v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_, v___y_1193_, v___y_1194_, v___y_1195_, v___y_1196_, v___y_1197_, v___y_1198_);
if (lean_obj_tag(v___x_1206_) == 0)
{
lean_object* v_a_1207_; lean_object* v___x_1208_; 
v_a_1207_ = lean_ctor_get(v___x_1206_, 0);
lean_inc_n(v_a_1207_, 2);
lean_dec_ref_known(v___x_1206_, 1);
lean_inc(v_declName_1186_);
v___x_1208_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst(v_declName_1186_, v_a_1207_, v_expectedInst_1187_, v___y_1195_, v___y_1196_, v___y_1197_, v___y_1198_);
if (lean_obj_tag(v___x_1208_) == 0)
{
lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; 
lean_dec_ref_known(v___x_1208_, 1);
v___x_1209_ = l_Lean_mkConst(v_declName_1186_, v___x_1203_);
lean_inc_ref_n(v_type_1183_, 2);
v___x_1210_ = l_Lean_mkApp4(v___x_1209_, v_type_1183_, v_type_1183_, v_type_1183_, v_a_1207_);
v___x_1211_ = l_Lean_Meta_Sym_canon(v___x_1210_, v___y_1193_, v___y_1194_, v___y_1195_, v___y_1196_, v___y_1197_, v___y_1198_);
if (lean_obj_tag(v___x_1211_) == 0)
{
lean_object* v_a_1212_; lean_object* v___x_1213_; 
v_a_1212_ = lean_ctor_get(v___x_1211_, 0);
lean_inc(v_a_1212_);
lean_dec_ref_known(v___x_1211_, 1);
v___x_1213_ = l_Lean_Meta_Sym_shareCommon(v_a_1212_, v___y_1193_, v___y_1194_, v___y_1195_, v___y_1196_, v___y_1197_, v___y_1198_);
return v___x_1213_;
}
else
{
return v___x_1211_;
}
}
else
{
lean_object* v_a_1214_; lean_object* v___x_1216_; uint8_t v_isShared_1217_; uint8_t v_isSharedCheck_1221_; 
lean_dec(v_a_1207_);
lean_dec_ref_known(v___x_1203_, 2);
lean_dec(v_declName_1186_);
lean_dec_ref(v_type_1183_);
v_a_1214_ = lean_ctor_get(v___x_1208_, 0);
v_isSharedCheck_1221_ = !lean_is_exclusive(v___x_1208_);
if (v_isSharedCheck_1221_ == 0)
{
v___x_1216_ = v___x_1208_;
v_isShared_1217_ = v_isSharedCheck_1221_;
goto v_resetjp_1215_;
}
else
{
lean_inc(v_a_1214_);
lean_dec(v___x_1208_);
v___x_1216_ = lean_box(0);
v_isShared_1217_ = v_isSharedCheck_1221_;
goto v_resetjp_1215_;
}
v_resetjp_1215_:
{
lean_object* v___x_1219_; 
if (v_isShared_1217_ == 0)
{
v___x_1219_ = v___x_1216_;
goto v_reusejp_1218_;
}
else
{
lean_object* v_reuseFailAlloc_1220_; 
v_reuseFailAlloc_1220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1220_, 0, v_a_1214_);
v___x_1219_ = v_reuseFailAlloc_1220_;
goto v_reusejp_1218_;
}
v_reusejp_1218_:
{
return v___x_1219_;
}
}
}
}
else
{
lean_dec_ref_known(v___x_1203_, 2);
lean_dec_ref(v_expectedInst_1187_);
lean_dec(v_declName_1186_);
lean_dec_ref(v_type_1183_);
return v___x_1206_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___at___00Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__2_spec__4___boxed(lean_object** _args){
lean_object* v_type_1222_ = _args[0];
lean_object* v_u_1223_ = _args[1];
lean_object* v_instDeclName_1224_ = _args[2];
lean_object* v_declName_1225_ = _args[3];
lean_object* v_expectedInst_1226_ = _args[4];
lean_object* v___y_1227_ = _args[5];
lean_object* v___y_1228_ = _args[6];
lean_object* v___y_1229_ = _args[7];
lean_object* v___y_1230_ = _args[8];
lean_object* v___y_1231_ = _args[9];
lean_object* v___y_1232_ = _args[10];
lean_object* v___y_1233_ = _args[11];
lean_object* v___y_1234_ = _args[12];
lean_object* v___y_1235_ = _args[13];
lean_object* v___y_1236_ = _args[14];
lean_object* v___y_1237_ = _args[15];
lean_object* v___y_1238_ = _args[16];
_start:
{
lean_object* v_res_1239_; 
v_res_1239_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___at___00Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__2_spec__4(v_type_1222_, v_u_1223_, v_instDeclName_1224_, v_declName_1225_, v_expectedInst_1226_, v___y_1227_, v___y_1228_, v___y_1229_, v___y_1230_, v___y_1231_, v___y_1232_, v___y_1233_, v___y_1234_, v___y_1235_, v___y_1236_, v___y_1237_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__2___lam__0(lean_object* v_a_1240_, lean_object* v_s_1241_){
_start:
{
lean_object* v_toRing_1242_; lean_object* v_invFn_x3f_1243_; lean_object* v_divFn_x3f_1244_; lean_object* v_zpowFn_x3f_1245_; lean_object* v_semiringId_x3f_1246_; lean_object* v_commSemiringInst_1247_; lean_object* v_commRingInst_1248_; lean_object* v_noZeroDivInst_x3f_1249_; lean_object* v_fieldInst_x3f_1250_; lean_object* v_powIdentityInst_x3f_1251_; lean_object* v___x_1253_; uint8_t v_isShared_1254_; uint8_t v_isSharedCheck_1283_; 
v_toRing_1242_ = lean_ctor_get(v_s_1241_, 0);
v_invFn_x3f_1243_ = lean_ctor_get(v_s_1241_, 1);
v_divFn_x3f_1244_ = lean_ctor_get(v_s_1241_, 2);
v_zpowFn_x3f_1245_ = lean_ctor_get(v_s_1241_, 3);
v_semiringId_x3f_1246_ = lean_ctor_get(v_s_1241_, 4);
v_commSemiringInst_1247_ = lean_ctor_get(v_s_1241_, 5);
v_commRingInst_1248_ = lean_ctor_get(v_s_1241_, 6);
v_noZeroDivInst_x3f_1249_ = lean_ctor_get(v_s_1241_, 7);
v_fieldInst_x3f_1250_ = lean_ctor_get(v_s_1241_, 8);
v_powIdentityInst_x3f_1251_ = lean_ctor_get(v_s_1241_, 9);
v_isSharedCheck_1283_ = !lean_is_exclusive(v_s_1241_);
if (v_isSharedCheck_1283_ == 0)
{
v___x_1253_ = v_s_1241_;
v_isShared_1254_ = v_isSharedCheck_1283_;
goto v_resetjp_1252_;
}
else
{
lean_inc(v_powIdentityInst_x3f_1251_);
lean_inc(v_fieldInst_x3f_1250_);
lean_inc(v_noZeroDivInst_x3f_1249_);
lean_inc(v_commRingInst_1248_);
lean_inc(v_commSemiringInst_1247_);
lean_inc(v_semiringId_x3f_1246_);
lean_inc(v_zpowFn_x3f_1245_);
lean_inc(v_divFn_x3f_1244_);
lean_inc(v_invFn_x3f_1243_);
lean_inc(v_toRing_1242_);
lean_dec(v_s_1241_);
v___x_1253_ = lean_box(0);
v_isShared_1254_ = v_isSharedCheck_1283_;
goto v_resetjp_1252_;
}
v_resetjp_1252_:
{
lean_object* v_id_1255_; lean_object* v_type_1256_; lean_object* v_u_1257_; lean_object* v_ringInst_1258_; lean_object* v_semiringInst_1259_; lean_object* v_charInst_x3f_1260_; uint8_t v_symbolicChar_1261_; lean_object* v_addFn_x3f_1262_; lean_object* v_subFn_x3f_1263_; lean_object* v_negFn_x3f_1264_; lean_object* v_powFn_x3f_1265_; lean_object* v_intCastFn_x3f_1266_; lean_object* v_natCastFn_x3f_1267_; lean_object* v_natSMulFn_x3f_1268_; lean_object* v_intSMulFn_x3f_1269_; lean_object* v_one_x3f_1270_; lean_object* v___x_1272_; uint8_t v_isShared_1273_; uint8_t v_isSharedCheck_1281_; 
v_id_1255_ = lean_ctor_get(v_toRing_1242_, 0);
v_type_1256_ = lean_ctor_get(v_toRing_1242_, 1);
v_u_1257_ = lean_ctor_get(v_toRing_1242_, 2);
v_ringInst_1258_ = lean_ctor_get(v_toRing_1242_, 3);
v_semiringInst_1259_ = lean_ctor_get(v_toRing_1242_, 4);
v_charInst_x3f_1260_ = lean_ctor_get(v_toRing_1242_, 5);
v_symbolicChar_1261_ = lean_ctor_get_uint8(v_toRing_1242_, sizeof(void*)*16);
v_addFn_x3f_1262_ = lean_ctor_get(v_toRing_1242_, 6);
v_subFn_x3f_1263_ = lean_ctor_get(v_toRing_1242_, 8);
v_negFn_x3f_1264_ = lean_ctor_get(v_toRing_1242_, 9);
v_powFn_x3f_1265_ = lean_ctor_get(v_toRing_1242_, 10);
v_intCastFn_x3f_1266_ = lean_ctor_get(v_toRing_1242_, 11);
v_natCastFn_x3f_1267_ = lean_ctor_get(v_toRing_1242_, 12);
v_natSMulFn_x3f_1268_ = lean_ctor_get(v_toRing_1242_, 13);
v_intSMulFn_x3f_1269_ = lean_ctor_get(v_toRing_1242_, 14);
v_one_x3f_1270_ = lean_ctor_get(v_toRing_1242_, 15);
v_isSharedCheck_1281_ = !lean_is_exclusive(v_toRing_1242_);
if (v_isSharedCheck_1281_ == 0)
{
lean_object* v_unused_1282_; 
v_unused_1282_ = lean_ctor_get(v_toRing_1242_, 7);
lean_dec(v_unused_1282_);
v___x_1272_ = v_toRing_1242_;
v_isShared_1273_ = v_isSharedCheck_1281_;
goto v_resetjp_1271_;
}
else
{
lean_inc(v_one_x3f_1270_);
lean_inc(v_intSMulFn_x3f_1269_);
lean_inc(v_natSMulFn_x3f_1268_);
lean_inc(v_natCastFn_x3f_1267_);
lean_inc(v_intCastFn_x3f_1266_);
lean_inc(v_powFn_x3f_1265_);
lean_inc(v_negFn_x3f_1264_);
lean_inc(v_subFn_x3f_1263_);
lean_inc(v_addFn_x3f_1262_);
lean_inc(v_charInst_x3f_1260_);
lean_inc(v_semiringInst_1259_);
lean_inc(v_ringInst_1258_);
lean_inc(v_u_1257_);
lean_inc(v_type_1256_);
lean_inc(v_id_1255_);
lean_dec(v_toRing_1242_);
v___x_1272_ = lean_box(0);
v_isShared_1273_ = v_isSharedCheck_1281_;
goto v_resetjp_1271_;
}
v_resetjp_1271_:
{
lean_object* v___x_1274_; lean_object* v___x_1276_; 
v___x_1274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1274_, 0, v_a_1240_);
if (v_isShared_1273_ == 0)
{
lean_ctor_set(v___x_1272_, 7, v___x_1274_);
v___x_1276_ = v___x_1272_;
goto v_reusejp_1275_;
}
else
{
lean_object* v_reuseFailAlloc_1280_; 
v_reuseFailAlloc_1280_ = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(v_reuseFailAlloc_1280_, 0, v_id_1255_);
lean_ctor_set(v_reuseFailAlloc_1280_, 1, v_type_1256_);
lean_ctor_set(v_reuseFailAlloc_1280_, 2, v_u_1257_);
lean_ctor_set(v_reuseFailAlloc_1280_, 3, v_ringInst_1258_);
lean_ctor_set(v_reuseFailAlloc_1280_, 4, v_semiringInst_1259_);
lean_ctor_set(v_reuseFailAlloc_1280_, 5, v_charInst_x3f_1260_);
lean_ctor_set(v_reuseFailAlloc_1280_, 6, v_addFn_x3f_1262_);
lean_ctor_set(v_reuseFailAlloc_1280_, 7, v___x_1274_);
lean_ctor_set(v_reuseFailAlloc_1280_, 8, v_subFn_x3f_1263_);
lean_ctor_set(v_reuseFailAlloc_1280_, 9, v_negFn_x3f_1264_);
lean_ctor_set(v_reuseFailAlloc_1280_, 10, v_powFn_x3f_1265_);
lean_ctor_set(v_reuseFailAlloc_1280_, 11, v_intCastFn_x3f_1266_);
lean_ctor_set(v_reuseFailAlloc_1280_, 12, v_natCastFn_x3f_1267_);
lean_ctor_set(v_reuseFailAlloc_1280_, 13, v_natSMulFn_x3f_1268_);
lean_ctor_set(v_reuseFailAlloc_1280_, 14, v_intSMulFn_x3f_1269_);
lean_ctor_set(v_reuseFailAlloc_1280_, 15, v_one_x3f_1270_);
lean_ctor_set_uint8(v_reuseFailAlloc_1280_, sizeof(void*)*16, v_symbolicChar_1261_);
v___x_1276_ = v_reuseFailAlloc_1280_;
goto v_reusejp_1275_;
}
v_reusejp_1275_:
{
lean_object* v___x_1278_; 
if (v_isShared_1254_ == 0)
{
lean_ctor_set(v___x_1253_, 0, v___x_1276_);
v___x_1278_ = v___x_1253_;
goto v_reusejp_1277_;
}
else
{
lean_object* v_reuseFailAlloc_1279_; 
v_reuseFailAlloc_1279_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1279_, 0, v___x_1276_);
lean_ctor_set(v_reuseFailAlloc_1279_, 1, v_invFn_x3f_1243_);
lean_ctor_set(v_reuseFailAlloc_1279_, 2, v_divFn_x3f_1244_);
lean_ctor_set(v_reuseFailAlloc_1279_, 3, v_zpowFn_x3f_1245_);
lean_ctor_set(v_reuseFailAlloc_1279_, 4, v_semiringId_x3f_1246_);
lean_ctor_set(v_reuseFailAlloc_1279_, 5, v_commSemiringInst_1247_);
lean_ctor_set(v_reuseFailAlloc_1279_, 6, v_commRingInst_1248_);
lean_ctor_set(v_reuseFailAlloc_1279_, 7, v_noZeroDivInst_x3f_1249_);
lean_ctor_set(v_reuseFailAlloc_1279_, 8, v_fieldInst_x3f_1250_);
lean_ctor_set(v_reuseFailAlloc_1279_, 9, v_powIdentityInst_x3f_1251_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__2(lean_object* v___y_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_){
_start:
{
lean_object* v___x_1308_; 
v___x_1308_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v___y_1296_, v___y_1297_, v___y_1298_, v___y_1299_, v___y_1300_, v___y_1301_, v___y_1302_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_);
if (lean_obj_tag(v___x_1308_) == 0)
{
lean_object* v_a_1309_; lean_object* v___x_1311_; uint8_t v_isShared_1312_; uint8_t v_isSharedCheck_1352_; 
v_a_1309_ = lean_ctor_get(v___x_1308_, 0);
v_isSharedCheck_1352_ = !lean_is_exclusive(v___x_1308_);
if (v_isSharedCheck_1352_ == 0)
{
v___x_1311_ = v___x_1308_;
v_isShared_1312_ = v_isSharedCheck_1352_;
goto v_resetjp_1310_;
}
else
{
lean_inc(v_a_1309_);
lean_dec(v___x_1308_);
v___x_1311_ = lean_box(0);
v_isShared_1312_ = v_isSharedCheck_1352_;
goto v_resetjp_1310_;
}
v_resetjp_1310_:
{
lean_object* v_toRing_1313_; lean_object* v_mulFn_x3f_1314_; 
v_toRing_1313_ = lean_ctor_get(v_a_1309_, 0);
lean_inc_ref(v_toRing_1313_);
lean_dec(v_a_1309_);
v_mulFn_x3f_1314_ = lean_ctor_get(v_toRing_1313_, 7);
if (lean_obj_tag(v_mulFn_x3f_1314_) == 1)
{
lean_object* v_val_1315_; lean_object* v___x_1317_; 
lean_inc_ref(v_mulFn_x3f_1314_);
lean_dec_ref(v_toRing_1313_);
v_val_1315_ = lean_ctor_get(v_mulFn_x3f_1314_, 0);
lean_inc(v_val_1315_);
lean_dec_ref_known(v_mulFn_x3f_1314_, 1);
if (v_isShared_1312_ == 0)
{
lean_ctor_set(v___x_1311_, 0, v_val_1315_);
v___x_1317_ = v___x_1311_;
goto v_reusejp_1316_;
}
else
{
lean_object* v_reuseFailAlloc_1318_; 
v_reuseFailAlloc_1318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1318_, 0, v_val_1315_);
v___x_1317_ = v_reuseFailAlloc_1318_;
goto v_reusejp_1316_;
}
v_reusejp_1316_:
{
return v___x_1317_;
}
}
else
{
lean_object* v_type_1319_; lean_object* v_u_1320_; lean_object* v_semiringInst_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v_expectedInst_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; 
lean_del_object(v___x_1311_);
v_type_1319_ = lean_ctor_get(v_toRing_1313_, 1);
lean_inc_ref_n(v_type_1319_, 3);
v_u_1320_ = lean_ctor_get(v_toRing_1313_, 2);
lean_inc_n(v_u_1320_, 2);
v_semiringInst_1321_ = lean_ctor_get(v_toRing_1313_, 4);
lean_inc_ref(v_semiringInst_1321_);
lean_dec_ref(v_toRing_1313_);
v___x_1322_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__2___closed__1));
v___x_1323_ = lean_box(0);
v___x_1324_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1324_, 0, v_u_1320_);
lean_ctor_set(v___x_1324_, 1, v___x_1323_);
lean_inc_ref(v___x_1324_);
v___x_1325_ = l_Lean_mkConst(v___x_1322_, v___x_1324_);
v___x_1326_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__2___closed__4));
v___x_1327_ = l_Lean_mkConst(v___x_1326_, v___x_1324_);
v___x_1328_ = l_Lean_mkAppB(v___x_1327_, v_type_1319_, v_semiringInst_1321_);
v_expectedInst_1329_ = l_Lean_mkAppB(v___x_1325_, v_type_1319_, v___x_1328_);
v___x_1330_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__2___closed__5));
v___x_1331_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__20));
v___x_1332_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___at___00Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__2_spec__4(v_type_1319_, v_u_1320_, v___x_1330_, v___x_1331_, v_expectedInst_1329_, v___y_1296_, v___y_1297_, v___y_1298_, v___y_1299_, v___y_1300_, v___y_1301_, v___y_1302_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_);
if (lean_obj_tag(v___x_1332_) == 0)
{
lean_object* v_a_1333_; lean_object* v___f_1334_; lean_object* v___x_1335_; 
v_a_1333_ = lean_ctor_get(v___x_1332_, 0);
lean_inc_n(v_a_1333_, 2);
lean_dec_ref_known(v___x_1332_, 1);
v___f_1334_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__2___lam__0), 2, 1);
lean_closure_set(v___f_1334_, 0, v_a_1333_);
v___x_1335_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(v___f_1334_, v___y_1296_, v___y_1302_);
if (lean_obj_tag(v___x_1335_) == 0)
{
lean_object* v___x_1337_; uint8_t v_isShared_1338_; uint8_t v_isSharedCheck_1342_; 
v_isSharedCheck_1342_ = !lean_is_exclusive(v___x_1335_);
if (v_isSharedCheck_1342_ == 0)
{
lean_object* v_unused_1343_; 
v_unused_1343_ = lean_ctor_get(v___x_1335_, 0);
lean_dec(v_unused_1343_);
v___x_1337_ = v___x_1335_;
v_isShared_1338_ = v_isSharedCheck_1342_;
goto v_resetjp_1336_;
}
else
{
lean_dec(v___x_1335_);
v___x_1337_ = lean_box(0);
v_isShared_1338_ = v_isSharedCheck_1342_;
goto v_resetjp_1336_;
}
v_resetjp_1336_:
{
lean_object* v___x_1340_; 
if (v_isShared_1338_ == 0)
{
lean_ctor_set(v___x_1337_, 0, v_a_1333_);
v___x_1340_ = v___x_1337_;
goto v_reusejp_1339_;
}
else
{
lean_object* v_reuseFailAlloc_1341_; 
v_reuseFailAlloc_1341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1341_, 0, v_a_1333_);
v___x_1340_ = v_reuseFailAlloc_1341_;
goto v_reusejp_1339_;
}
v_reusejp_1339_:
{
return v___x_1340_;
}
}
}
else
{
lean_object* v_a_1344_; lean_object* v___x_1346_; uint8_t v_isShared_1347_; uint8_t v_isSharedCheck_1351_; 
lean_dec(v_a_1333_);
v_a_1344_ = lean_ctor_get(v___x_1335_, 0);
v_isSharedCheck_1351_ = !lean_is_exclusive(v___x_1335_);
if (v_isSharedCheck_1351_ == 0)
{
v___x_1346_ = v___x_1335_;
v_isShared_1347_ = v_isSharedCheck_1351_;
goto v_resetjp_1345_;
}
else
{
lean_inc(v_a_1344_);
lean_dec(v___x_1335_);
v___x_1346_ = lean_box(0);
v_isShared_1347_ = v_isSharedCheck_1351_;
goto v_resetjp_1345_;
}
v_resetjp_1345_:
{
lean_object* v___x_1349_; 
if (v_isShared_1347_ == 0)
{
v___x_1349_ = v___x_1346_;
goto v_reusejp_1348_;
}
else
{
lean_object* v_reuseFailAlloc_1350_; 
v_reuseFailAlloc_1350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1350_, 0, v_a_1344_);
v___x_1349_ = v_reuseFailAlloc_1350_;
goto v_reusejp_1348_;
}
v_reusejp_1348_:
{
return v___x_1349_;
}
}
}
}
else
{
return v___x_1332_;
}
}
}
}
else
{
lean_object* v_a_1353_; lean_object* v___x_1355_; uint8_t v_isShared_1356_; uint8_t v_isSharedCheck_1360_; 
v_a_1353_ = lean_ctor_get(v___x_1308_, 0);
v_isSharedCheck_1360_ = !lean_is_exclusive(v___x_1308_);
if (v_isSharedCheck_1360_ == 0)
{
v___x_1355_ = v___x_1308_;
v_isShared_1356_ = v_isSharedCheck_1360_;
goto v_resetjp_1354_;
}
else
{
lean_inc(v_a_1353_);
lean_dec(v___x_1308_);
v___x_1355_ = lean_box(0);
v_isShared_1356_ = v_isSharedCheck_1360_;
goto v_resetjp_1354_;
}
v_resetjp_1354_:
{
lean_object* v___x_1358_; 
if (v_isShared_1356_ == 0)
{
v___x_1358_ = v___x_1355_;
goto v_reusejp_1357_;
}
else
{
lean_object* v_reuseFailAlloc_1359_; 
v_reuseFailAlloc_1359_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1359_, 0, v_a_1353_);
v___x_1358_ = v_reuseFailAlloc_1359_;
goto v_reusejp_1357_;
}
v_reusejp_1357_:
{
return v___x_1358_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__2___boxed(lean_object* v___y_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_){
_start:
{
lean_object* v_res_1373_; 
v_res_1373_ = l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__2(v___y_1361_, v___y_1362_, v___y_1363_, v___y_1364_, v___y_1365_, v___y_1366_, v___y_1367_, v___y_1368_, v___y_1369_, v___y_1370_, v___y_1371_);
lean_dec(v___y_1371_);
lean_dec_ref(v___y_1370_);
lean_dec(v___y_1369_);
lean_dec_ref(v___y_1368_);
lean_dec(v___y_1367_);
lean_dec_ref(v___y_1366_);
lean_dec(v___y_1365_);
lean_dec_ref(v___y_1364_);
lean_dec(v___y_1363_);
lean_dec(v___y_1362_);
lean_dec_ref(v___y_1361_);
return v_res_1373_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__3___closed__1(void){
_start:
{
lean_object* v___x_1376_; lean_object* v___x_1377_; 
v___x_1376_ = lean_unsigned_to_nat(0u);
v___x_1377_ = lean_nat_to_int(v___x_1376_);
return v___x_1377_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__3(lean_object* v_k_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_){
_start:
{
lean_object* v___x_1396_; 
v___x_1396_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v___y_1384_, v___y_1385_, v___y_1386_, v___y_1387_, v___y_1388_, v___y_1389_, v___y_1390_, v___y_1391_, v___y_1392_, v___y_1393_, v___y_1394_);
if (lean_obj_tag(v___x_1396_) == 0)
{
lean_object* v_a_1397_; lean_object* v___x_1399_; uint8_t v_isShared_1400_; uint8_t v_isSharedCheck_1457_; 
v_a_1397_ = lean_ctor_get(v___x_1396_, 0);
v_isSharedCheck_1457_ = !lean_is_exclusive(v___x_1396_);
if (v_isSharedCheck_1457_ == 0)
{
v___x_1399_ = v___x_1396_;
v_isShared_1400_ = v_isSharedCheck_1457_;
goto v_resetjp_1398_;
}
else
{
lean_inc(v_a_1397_);
lean_dec(v___x_1396_);
v___x_1399_ = lean_box(0);
v_isShared_1400_ = v_isSharedCheck_1457_;
goto v_resetjp_1398_;
}
v_resetjp_1398_:
{
lean_object* v_toRing_1401_; lean_object* v_type_1402_; lean_object* v_u_1403_; lean_object* v_semiringInst_1404_; lean_object* v___x_1405_; lean_object* v_n_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v_ofNatInst_1411_; lean_object* v___y_1412_; lean_object* v___y_1413_; lean_object* v___y_1414_; lean_object* v___y_1415_; lean_object* v___y_1416_; lean_object* v___y_1417_; lean_object* v___y_1418_; lean_object* v___y_1419_; lean_object* v___y_1420_; lean_object* v___y_1421_; lean_object* v___y_1422_; lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; 
v_toRing_1401_ = lean_ctor_get(v_a_1397_, 0);
lean_inc_ref(v_toRing_1401_);
lean_dec(v_a_1397_);
v_type_1402_ = lean_ctor_get(v_toRing_1401_, 1);
lean_inc_ref_n(v_type_1402_, 2);
v_u_1403_ = lean_ctor_get(v_toRing_1401_, 2);
lean_inc(v_u_1403_);
v_semiringInst_1404_ = lean_ctor_get(v_toRing_1401_, 4);
lean_inc_ref(v_semiringInst_1404_);
lean_dec_ref(v_toRing_1401_);
v___x_1405_ = lean_nat_abs(v_k_1383_);
v_n_1406_ = l_Lean_mkRawNatLit(v___x_1405_);
v___x_1407_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__3___closed__0));
v___x_1408_ = lean_box(0);
v___x_1409_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1409_, 0, v_u_1403_);
lean_ctor_set(v___x_1409_, 1, v___x_1408_);
lean_inc_ref(v___x_1409_);
v___x_1441_ = l_Lean_mkConst(v___x_1407_, v___x_1409_);
lean_inc_ref(v_n_1406_);
v___x_1442_ = l_Lean_mkAppB(v___x_1441_, v_type_1402_, v_n_1406_);
v___x_1443_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v___x_1442_, v___y_1390_, v___y_1391_, v___y_1392_, v___y_1393_, v___y_1394_);
if (lean_obj_tag(v___x_1443_) == 0)
{
lean_object* v_a_1444_; 
v_a_1444_ = lean_ctor_get(v___x_1443_, 0);
lean_inc(v_a_1444_);
lean_dec_ref_known(v___x_1443_, 1);
if (lean_obj_tag(v_a_1444_) == 1)
{
lean_object* v_val_1445_; 
lean_dec_ref(v_semiringInst_1404_);
v_val_1445_ = lean_ctor_get(v_a_1444_, 0);
lean_inc(v_val_1445_);
lean_dec_ref_known(v_a_1444_, 1);
v_ofNatInst_1411_ = v_val_1445_;
v___y_1412_ = v___y_1384_;
v___y_1413_ = v___y_1385_;
v___y_1414_ = v___y_1386_;
v___y_1415_ = v___y_1387_;
v___y_1416_ = v___y_1388_;
v___y_1417_ = v___y_1389_;
v___y_1418_ = v___y_1390_;
v___y_1419_ = v___y_1391_;
v___y_1420_ = v___y_1392_;
v___y_1421_ = v___y_1393_;
v___y_1422_ = v___y_1394_;
goto v___jp_1410_;
}
else
{
lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; 
lean_dec(v_a_1444_);
v___x_1446_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__3___closed__2));
lean_inc_ref(v___x_1409_);
v___x_1447_ = l_Lean_mkConst(v___x_1446_, v___x_1409_);
lean_inc_ref(v_n_1406_);
lean_inc_ref(v_type_1402_);
v___x_1448_ = l_Lean_mkApp3(v___x_1447_, v_type_1402_, v_semiringInst_1404_, v_n_1406_);
v_ofNatInst_1411_ = v___x_1448_;
v___y_1412_ = v___y_1384_;
v___y_1413_ = v___y_1385_;
v___y_1414_ = v___y_1386_;
v___y_1415_ = v___y_1387_;
v___y_1416_ = v___y_1388_;
v___y_1417_ = v___y_1389_;
v___y_1418_ = v___y_1390_;
v___y_1419_ = v___y_1391_;
v___y_1420_ = v___y_1392_;
v___y_1421_ = v___y_1393_;
v___y_1422_ = v___y_1394_;
goto v___jp_1410_;
}
}
else
{
lean_object* v_a_1449_; lean_object* v___x_1451_; uint8_t v_isShared_1452_; uint8_t v_isSharedCheck_1456_; 
lean_dec_ref_known(v___x_1409_, 2);
lean_dec_ref(v_n_1406_);
lean_dec_ref(v_semiringInst_1404_);
lean_dec_ref(v_type_1402_);
lean_del_object(v___x_1399_);
v_a_1449_ = lean_ctor_get(v___x_1443_, 0);
v_isSharedCheck_1456_ = !lean_is_exclusive(v___x_1443_);
if (v_isSharedCheck_1456_ == 0)
{
v___x_1451_ = v___x_1443_;
v_isShared_1452_ = v_isSharedCheck_1456_;
goto v_resetjp_1450_;
}
else
{
lean_inc(v_a_1449_);
lean_dec(v___x_1443_);
v___x_1451_ = lean_box(0);
v_isShared_1452_ = v_isSharedCheck_1456_;
goto v_resetjp_1450_;
}
v_resetjp_1450_:
{
lean_object* v___x_1454_; 
if (v_isShared_1452_ == 0)
{
v___x_1454_ = v___x_1451_;
goto v_reusejp_1453_;
}
else
{
lean_object* v_reuseFailAlloc_1455_; 
v_reuseFailAlloc_1455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1455_, 0, v_a_1449_);
v___x_1454_ = v_reuseFailAlloc_1455_;
goto v_reusejp_1453_;
}
v_reusejp_1453_:
{
return v___x_1454_;
}
}
}
v___jp_1410_:
{
lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v_e_1425_; lean_object* v___x_1426_; uint8_t v___x_1427_; 
v___x_1423_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__8));
v___x_1424_ = l_Lean_mkConst(v___x_1423_, v___x_1409_);
v_e_1425_ = l_Lean_mkApp3(v___x_1424_, v_type_1402_, v_n_1406_, v_ofNatInst_1411_);
v___x_1426_ = lean_obj_once(&l_Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__3___closed__1, &l_Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__3___closed__1_once, _init_l_Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__3___closed__1);
v___x_1427_ = lean_int_dec_lt(v_k_1383_, v___x_1426_);
if (v___x_1427_ == 0)
{
lean_object* v___x_1429_; 
if (v_isShared_1400_ == 0)
{
lean_ctor_set(v___x_1399_, 0, v_e_1425_);
v___x_1429_ = v___x_1399_;
goto v_reusejp_1428_;
}
else
{
lean_object* v_reuseFailAlloc_1430_; 
v_reuseFailAlloc_1430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1430_, 0, v_e_1425_);
v___x_1429_ = v_reuseFailAlloc_1430_;
goto v_reusejp_1428_;
}
v_reusejp_1428_:
{
return v___x_1429_;
}
}
else
{
lean_object* v___x_1431_; 
lean_del_object(v___x_1399_);
v___x_1431_ = l_Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0(v___y_1412_, v___y_1413_, v___y_1414_, v___y_1415_, v___y_1416_, v___y_1417_, v___y_1418_, v___y_1419_, v___y_1420_, v___y_1421_, v___y_1422_);
if (lean_obj_tag(v___x_1431_) == 0)
{
lean_object* v_a_1432_; lean_object* v___x_1434_; uint8_t v_isShared_1435_; uint8_t v_isSharedCheck_1440_; 
v_a_1432_ = lean_ctor_get(v___x_1431_, 0);
v_isSharedCheck_1440_ = !lean_is_exclusive(v___x_1431_);
if (v_isSharedCheck_1440_ == 0)
{
v___x_1434_ = v___x_1431_;
v_isShared_1435_ = v_isSharedCheck_1440_;
goto v_resetjp_1433_;
}
else
{
lean_inc(v_a_1432_);
lean_dec(v___x_1431_);
v___x_1434_ = lean_box(0);
v_isShared_1435_ = v_isSharedCheck_1440_;
goto v_resetjp_1433_;
}
v_resetjp_1433_:
{
lean_object* v___x_1436_; lean_object* v___x_1438_; 
v___x_1436_ = l_Lean_Expr_app___override(v_a_1432_, v_e_1425_);
if (v_isShared_1435_ == 0)
{
lean_ctor_set(v___x_1434_, 0, v___x_1436_);
v___x_1438_ = v___x_1434_;
goto v_reusejp_1437_;
}
else
{
lean_object* v_reuseFailAlloc_1439_; 
v_reuseFailAlloc_1439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1439_, 0, v___x_1436_);
v___x_1438_ = v_reuseFailAlloc_1439_;
goto v_reusejp_1437_;
}
v_reusejp_1437_:
{
return v___x_1438_;
}
}
}
else
{
lean_dec_ref(v_e_1425_);
return v___x_1431_;
}
}
}
}
}
else
{
lean_object* v_a_1458_; lean_object* v___x_1460_; uint8_t v_isShared_1461_; uint8_t v_isSharedCheck_1465_; 
v_a_1458_ = lean_ctor_get(v___x_1396_, 0);
v_isSharedCheck_1465_ = !lean_is_exclusive(v___x_1396_);
if (v_isSharedCheck_1465_ == 0)
{
v___x_1460_ = v___x_1396_;
v_isShared_1461_ = v_isSharedCheck_1465_;
goto v_resetjp_1459_;
}
else
{
lean_inc(v_a_1458_);
lean_dec(v___x_1396_);
v___x_1460_ = lean_box(0);
v_isShared_1461_ = v_isSharedCheck_1465_;
goto v_resetjp_1459_;
}
v_resetjp_1459_:
{
lean_object* v___x_1463_; 
if (v_isShared_1461_ == 0)
{
v___x_1463_ = v___x_1460_;
goto v_reusejp_1462_;
}
else
{
lean_object* v_reuseFailAlloc_1464_; 
v_reuseFailAlloc_1464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1464_, 0, v_a_1458_);
v___x_1463_ = v_reuseFailAlloc_1464_;
goto v_reusejp_1462_;
}
v_reusejp_1462_:
{
return v___x_1463_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__3___boxed(lean_object* v_k_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_){
_start:
{
lean_object* v_res_1479_; 
v_res_1479_ = l_Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__3(v_k_1466_, v___y_1467_, v___y_1468_, v___y_1469_, v___y_1470_, v___y_1471_, v___y_1472_, v___y_1473_, v___y_1474_, v___y_1475_, v___y_1476_, v___y_1477_);
lean_dec(v___y_1477_);
lean_dec_ref(v___y_1476_);
lean_dec(v___y_1475_);
lean_dec_ref(v___y_1474_);
lean_dec(v___y_1473_);
lean_dec_ref(v___y_1472_);
lean_dec(v___y_1471_);
lean_dec_ref(v___y_1470_);
lean_dec(v___y_1469_);
lean_dec(v___y_1468_);
lean_dec_ref(v___y_1467_);
lean_dec(v_k_1466_);
return v_res_1479_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__3(void){
_start:
{
lean_object* v___x_1487_; lean_object* v___x_1488_; 
v___x_1487_ = lean_unsigned_to_nat(1u);
v___x_1488_ = lean_nat_to_int(v___x_1487_);
return v___x_1488_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv(lean_object* v_e_1513_, lean_object* v_inst_1514_, lean_object* v_a_1515_, lean_object* v_a_1516_, lean_object* v_a_1517_, lean_object* v_a_1518_, lean_object* v_a_1519_, lean_object* v_a_1520_, lean_object* v_a_1521_, lean_object* v_a_1522_, lean_object* v_a_1523_, lean_object* v_a_1524_, lean_object* v_a_1525_, lean_object* v_a_1526_){
_start:
{
lean_object* v___f_1531_; lean_object* v___x_1532_; 
lean_inc_ref(v_a_1515_);
v___f_1531_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___lam__0), 2, 1);
lean_closure_set(v___f_1531_, 0, v_a_1515_);
v___x_1532_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst(v_inst_1514_, v_a_1516_, v_a_1517_, v_a_1518_, v_a_1519_, v_a_1520_, v_a_1521_, v_a_1522_, v_a_1523_, v_a_1524_, v_a_1525_, v_a_1526_);
if (lean_obj_tag(v___x_1532_) == 0)
{
lean_object* v_a_1533_; lean_object* v___x_1535_; uint8_t v_isShared_1536_; uint8_t v_isSharedCheck_1788_; 
v_a_1533_ = lean_ctor_get(v___x_1532_, 0);
v_isSharedCheck_1788_ = !lean_is_exclusive(v___x_1532_);
if (v_isSharedCheck_1788_ == 0)
{
v___x_1535_ = v___x_1532_;
v_isShared_1536_ = v_isSharedCheck_1788_;
goto v_resetjp_1534_;
}
else
{
lean_inc(v_a_1533_);
lean_dec(v___x_1532_);
v___x_1535_ = lean_box(0);
v_isShared_1536_ = v_isSharedCheck_1788_;
goto v_resetjp_1534_;
}
v_resetjp_1534_:
{
uint8_t v___x_1537_; 
v___x_1537_ = lean_unbox(v_a_1533_);
lean_dec(v_a_1533_);
if (v___x_1537_ == 0)
{
lean_object* v___x_1538_; lean_object* v___x_1540_; 
lean_dec_ref(v___f_1531_);
lean_dec_ref(v_a_1515_);
lean_dec_ref(v_e_1513_);
v___x_1538_ = lean_box(0);
if (v_isShared_1536_ == 0)
{
lean_ctor_set(v___x_1535_, 0, v___x_1538_);
v___x_1540_ = v___x_1535_;
goto v_reusejp_1539_;
}
else
{
lean_object* v_reuseFailAlloc_1541_; 
v_reuseFailAlloc_1541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1541_, 0, v___x_1538_);
v___x_1540_ = v_reuseFailAlloc_1541_;
goto v_reusejp_1539_;
}
v_reusejp_1539_:
{
return v___x_1540_;
}
}
else
{
lean_object* v___x_1542_; 
lean_del_object(v___x_1535_);
v___x_1542_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v_a_1516_, v_a_1517_, v_a_1518_, v_a_1519_, v_a_1520_, v_a_1521_, v_a_1522_, v_a_1523_, v_a_1524_, v_a_1525_, v_a_1526_);
if (lean_obj_tag(v___x_1542_) == 0)
{
lean_object* v_a_1543_; lean_object* v___x_1545_; uint8_t v_isShared_1546_; uint8_t v_isSharedCheck_1779_; 
v_a_1543_ = lean_ctor_get(v___x_1542_, 0);
v_isSharedCheck_1779_ = !lean_is_exclusive(v___x_1542_);
if (v_isSharedCheck_1779_ == 0)
{
v___x_1545_ = v___x_1542_;
v_isShared_1546_ = v_isSharedCheck_1779_;
goto v_resetjp_1544_;
}
else
{
lean_inc(v_a_1543_);
lean_dec(v___x_1542_);
v___x_1545_ = lean_box(0);
v_isShared_1546_ = v_isSharedCheck_1779_;
goto v_resetjp_1544_;
}
v_resetjp_1544_:
{
lean_object* v_fieldInst_x3f_1547_; 
v_fieldInst_x3f_1547_ = lean_ctor_get(v_a_1543_, 8);
lean_inc(v_fieldInst_x3f_1547_);
if (lean_obj_tag(v_fieldInst_x3f_1547_) == 1)
{
lean_object* v_toRing_1548_; lean_object* v_val_1549_; lean_object* v___y_1551_; lean_object* v___y_1552_; lean_object* v___y_1553_; lean_object* v___y_1554_; lean_object* v___y_1555_; lean_object* v___y_1556_; lean_object* v___y_1557_; lean_object* v___y_1558_; lean_object* v___y_1559_; lean_object* v___y_1560_; lean_object* v___x_1570_; 
lean_del_object(v___x_1545_);
v_toRing_1548_ = lean_ctor_get(v_a_1543_, 0);
lean_inc_ref(v_toRing_1548_);
lean_dec(v_a_1543_);
v_val_1549_ = lean_ctor_get(v_fieldInst_x3f_1547_, 0);
lean_inc(v_val_1549_);
lean_dec_ref_known(v_fieldInst_x3f_1547_, 1);
v___x_1570_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRingState___redArg(v_a_1516_, v_a_1517_, v_a_1525_);
if (lean_obj_tag(v___x_1570_) == 0)
{
lean_object* v_a_1571_; lean_object* v___x_1573_; uint8_t v_isShared_1574_; uint8_t v_isSharedCheck_1766_; 
v_a_1571_ = lean_ctor_get(v___x_1570_, 0);
v_isSharedCheck_1766_ = !lean_is_exclusive(v___x_1570_);
if (v_isSharedCheck_1766_ == 0)
{
v___x_1573_ = v___x_1570_;
v_isShared_1574_ = v_isSharedCheck_1766_;
goto v_resetjp_1572_;
}
else
{
lean_inc(v_a_1571_);
lean_dec(v___x_1570_);
v___x_1573_ = lean_box(0);
v_isShared_1574_ = v_isSharedCheck_1766_;
goto v_resetjp_1572_;
}
v_resetjp_1572_:
{
lean_object* v_invSet_1575_; uint8_t v___x_1576_; 
v_invSet_1575_ = lean_ctor_get(v_a_1571_, 7);
lean_inc_ref(v_invSet_1575_);
lean_dec(v_a_1571_);
v___x_1576_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1___redArg(v_invSet_1575_, v_a_1515_);
lean_dec_ref(v_invSet_1575_);
if (v___x_1576_ == 0)
{
lean_object* v___x_1577_; 
lean_del_object(v___x_1573_);
v___x_1577_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRingState___redArg(v___f_1531_, v_a_1516_, v_a_1517_);
if (lean_obj_tag(v___x_1577_) == 0)
{
lean_object* v___x_1578_; 
lean_dec_ref_known(v___x_1577_, 1);
lean_inc_ref(v_a_1515_);
v___x_1578_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f(v_a_1515_, v_a_1516_, v_a_1517_, v_a_1518_, v_a_1519_, v_a_1520_, v_a_1521_, v_a_1522_, v_a_1523_, v_a_1524_, v_a_1525_, v_a_1526_);
if (lean_obj_tag(v___x_1578_) == 0)
{
lean_object* v_a_1579_; 
v_a_1579_ = lean_ctor_get(v___x_1578_, 0);
lean_inc(v_a_1579_);
lean_dec_ref_known(v___x_1578_, 1);
if (lean_obj_tag(v_a_1579_) == 1)
{
lean_object* v_val_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; uint8_t v___x_1583_; 
v_val_1580_ = lean_ctor_get(v_a_1579_, 0);
lean_inc(v_val_1580_);
lean_dec_ref_known(v_a_1579_, 1);
v___x_1581_ = lean_unsigned_to_nat(0u);
v___x_1582_ = lean_obj_once(&l_Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__3___closed__1, &l_Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__3___closed__1_once, _init_l_Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__3___closed__1);
v___x_1583_ = lean_int_dec_eq(v_val_1580_, v___x_1582_);
if (v___x_1583_ == 0)
{
lean_object* v___x_1584_; 
v___x_1584_ = l_Lean_Meta_Grind_Arith_CommRing_hasChar(v_a_1516_, v_a_1517_, v_a_1518_, v_a_1519_, v_a_1520_, v_a_1521_, v_a_1522_, v_a_1523_, v_a_1524_, v_a_1525_, v_a_1526_);
if (lean_obj_tag(v___x_1584_) == 0)
{
lean_object* v_a_1585_; uint8_t v___x_1586_; 
v_a_1585_ = lean_ctor_get(v___x_1584_, 0);
lean_inc(v_a_1585_);
lean_dec_ref_known(v___x_1584_, 1);
v___x_1586_ = lean_unbox(v_a_1585_);
lean_dec(v_a_1585_);
if (v___x_1586_ == 0)
{
lean_dec(v_val_1580_);
lean_dec_ref(v_e_1513_);
v___y_1551_ = v_a_1517_;
v___y_1552_ = v_a_1518_;
v___y_1553_ = v_a_1519_;
v___y_1554_ = v_a_1520_;
v___y_1555_ = v_a_1521_;
v___y_1556_ = v_a_1522_;
v___y_1557_ = v_a_1523_;
v___y_1558_ = v_a_1524_;
v___y_1559_ = v_a_1525_;
v___y_1560_ = v_a_1526_;
goto v___jp_1550_;
}
else
{
lean_object* v___x_1587_; 
v___x_1587_ = l_Lean_Meta_Grind_Arith_CommRing_getCharInst(v_a_1516_, v_a_1517_, v_a_1518_, v_a_1519_, v_a_1520_, v_a_1521_, v_a_1522_, v_a_1523_, v_a_1524_, v_a_1525_, v_a_1526_);
if (lean_obj_tag(v___x_1587_) == 0)
{
lean_object* v_a_1588_; lean_object* v_fst_1589_; lean_object* v_snd_1590_; lean_object* v___x_1592_; uint8_t v_isShared_1593_; uint8_t v_isSharedCheck_1720_; 
v_a_1588_ = lean_ctor_get(v___x_1587_, 0);
lean_inc(v_a_1588_);
lean_dec_ref_known(v___x_1587_, 1);
v_fst_1589_ = lean_ctor_get(v_a_1588_, 0);
v_snd_1590_ = lean_ctor_get(v_a_1588_, 1);
v_isSharedCheck_1720_ = !lean_is_exclusive(v_a_1588_);
if (v_isSharedCheck_1720_ == 0)
{
v___x_1592_ = v_a_1588_;
v_isShared_1593_ = v_isSharedCheck_1720_;
goto v_resetjp_1591_;
}
else
{
lean_inc(v_snd_1590_);
lean_inc(v_fst_1589_);
lean_dec(v_a_1588_);
v___x_1592_ = lean_box(0);
v_isShared_1593_ = v_isSharedCheck_1720_;
goto v_resetjp_1591_;
}
v_resetjp_1591_:
{
uint8_t v___x_1594_; 
v___x_1594_ = lean_nat_dec_eq(v_snd_1590_, v___x_1581_);
if (v___x_1594_ == 0)
{
lean_object* v___x_1595_; lean_object* v___x_1596_; uint8_t v___x_1597_; 
lean_inc(v_snd_1590_);
v___x_1595_ = lean_nat_to_int(v_snd_1590_);
v___x_1596_ = lean_int_emod(v_val_1580_, v___x_1595_);
lean_dec(v___x_1595_);
v___x_1597_ = lean_int_dec_eq(v___x_1596_, v___x_1582_);
lean_dec(v___x_1596_);
if (v___x_1597_ == 0)
{
lean_object* v___x_1598_; 
v___x_1598_ = l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__2(v_a_1516_, v_a_1517_, v_a_1518_, v_a_1519_, v_a_1520_, v_a_1521_, v_a_1522_, v_a_1523_, v_a_1524_, v_a_1525_, v_a_1526_);
if (lean_obj_tag(v___x_1598_) == 0)
{
lean_object* v_a_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; 
v_a_1599_ = lean_ctor_get(v___x_1598_, 0);
lean_inc(v_a_1599_);
lean_dec_ref_known(v___x_1598_, 1);
v___x_1600_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__3, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__3);
v___x_1601_ = l_Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__3(v___x_1600_, v_a_1516_, v_a_1517_, v_a_1518_, v_a_1519_, v_a_1520_, v_a_1521_, v_a_1522_, v_a_1523_, v_a_1524_, v_a_1525_, v_a_1526_);
if (lean_obj_tag(v___x_1601_) == 0)
{
lean_object* v_a_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; 
v_a_1602_ = lean_ctor_get(v___x_1601_, 0);
lean_inc(v_a_1602_);
lean_dec_ref_known(v___x_1601_, 1);
v___x_1603_ = l_Lean_mkAppB(v_a_1599_, v_a_1515_, v_e_1513_);
v___x_1604_ = l_Lean_Meta_mkEq(v___x_1603_, v_a_1602_, v_a_1523_, v_a_1524_, v_a_1525_, v_a_1526_);
if (lean_obj_tag(v___x_1604_) == 0)
{
lean_object* v_a_1605_; lean_object* v_type_1606_; lean_object* v_u_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1611_; 
v_a_1605_ = lean_ctor_get(v___x_1604_, 0);
lean_inc(v_a_1605_);
lean_dec_ref_known(v___x_1604_, 1);
v_type_1606_ = lean_ctor_get(v_toRing_1548_, 1);
lean_inc_ref(v_type_1606_);
v_u_1607_ = lean_ctor_get(v_toRing_1548_, 2);
lean_inc(v_u_1607_);
lean_dec_ref(v_toRing_1548_);
v___x_1608_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__5));
v___x_1609_ = lean_box(0);
if (v_isShared_1593_ == 0)
{
lean_ctor_set_tag(v___x_1592_, 1);
lean_ctor_set(v___x_1592_, 1, v___x_1609_);
lean_ctor_set(v___x_1592_, 0, v_u_1607_);
v___x_1611_ = v___x_1592_;
goto v_reusejp_1610_;
}
else
{
lean_object* v_reuseFailAlloc_1618_; 
v_reuseFailAlloc_1618_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1618_, 0, v_u_1607_);
lean_ctor_set(v_reuseFailAlloc_1618_, 1, v___x_1609_);
v___x_1611_ = v_reuseFailAlloc_1618_;
goto v_reusejp_1610_;
}
v_reusejp_1610_:
{
lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; 
v___x_1612_ = l_Lean_mkConst(v___x_1608_, v___x_1611_);
v___x_1613_ = l_Lean_mkNatLit(v_snd_1590_);
v___x_1614_ = l_Lean_mkIntLit(v_val_1580_);
lean_dec(v_val_1580_);
v___x_1615_ = l_Lean_eagerReflBoolTrue;
v___x_1616_ = l_Lean_mkApp6(v___x_1612_, v_type_1606_, v___x_1613_, v_val_1549_, v_fst_1589_, v___x_1614_, v___x_1615_);
v___x_1617_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_pushInvFact___redArg(v_a_1605_, v___x_1616_, v_a_1517_, v_a_1521_, v_a_1522_, v_a_1523_, v_a_1524_, v_a_1525_, v_a_1526_);
if (lean_obj_tag(v___x_1617_) == 0)
{
lean_dec_ref_known(v___x_1617_, 1);
goto v___jp_1528_;
}
else
{
return v___x_1617_;
}
}
}
else
{
lean_object* v_a_1619_; lean_object* v___x_1621_; uint8_t v_isShared_1622_; uint8_t v_isSharedCheck_1626_; 
lean_del_object(v___x_1592_);
lean_dec(v_snd_1590_);
lean_dec(v_fst_1589_);
lean_dec(v_val_1580_);
lean_dec(v_val_1549_);
lean_dec_ref(v_toRing_1548_);
v_a_1619_ = lean_ctor_get(v___x_1604_, 0);
v_isSharedCheck_1626_ = !lean_is_exclusive(v___x_1604_);
if (v_isSharedCheck_1626_ == 0)
{
v___x_1621_ = v___x_1604_;
v_isShared_1622_ = v_isSharedCheck_1626_;
goto v_resetjp_1620_;
}
else
{
lean_inc(v_a_1619_);
lean_dec(v___x_1604_);
v___x_1621_ = lean_box(0);
v_isShared_1622_ = v_isSharedCheck_1626_;
goto v_resetjp_1620_;
}
v_resetjp_1620_:
{
lean_object* v___x_1624_; 
if (v_isShared_1622_ == 0)
{
v___x_1624_ = v___x_1621_;
goto v_reusejp_1623_;
}
else
{
lean_object* v_reuseFailAlloc_1625_; 
v_reuseFailAlloc_1625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1625_, 0, v_a_1619_);
v___x_1624_ = v_reuseFailAlloc_1625_;
goto v_reusejp_1623_;
}
v_reusejp_1623_:
{
return v___x_1624_;
}
}
}
}
else
{
lean_object* v_a_1627_; lean_object* v___x_1629_; uint8_t v_isShared_1630_; uint8_t v_isSharedCheck_1634_; 
lean_dec(v_a_1599_);
lean_del_object(v___x_1592_);
lean_dec(v_snd_1590_);
lean_dec(v_fst_1589_);
lean_dec(v_val_1580_);
lean_dec(v_val_1549_);
lean_dec_ref(v_toRing_1548_);
lean_dec_ref(v_a_1515_);
lean_dec_ref(v_e_1513_);
v_a_1627_ = lean_ctor_get(v___x_1601_, 0);
v_isSharedCheck_1634_ = !lean_is_exclusive(v___x_1601_);
if (v_isSharedCheck_1634_ == 0)
{
v___x_1629_ = v___x_1601_;
v_isShared_1630_ = v_isSharedCheck_1634_;
goto v_resetjp_1628_;
}
else
{
lean_inc(v_a_1627_);
lean_dec(v___x_1601_);
v___x_1629_ = lean_box(0);
v_isShared_1630_ = v_isSharedCheck_1634_;
goto v_resetjp_1628_;
}
v_resetjp_1628_:
{
lean_object* v___x_1632_; 
if (v_isShared_1630_ == 0)
{
v___x_1632_ = v___x_1629_;
goto v_reusejp_1631_;
}
else
{
lean_object* v_reuseFailAlloc_1633_; 
v_reuseFailAlloc_1633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1633_, 0, v_a_1627_);
v___x_1632_ = v_reuseFailAlloc_1633_;
goto v_reusejp_1631_;
}
v_reusejp_1631_:
{
return v___x_1632_;
}
}
}
}
else
{
lean_object* v_a_1635_; lean_object* v___x_1637_; uint8_t v_isShared_1638_; uint8_t v_isSharedCheck_1642_; 
lean_del_object(v___x_1592_);
lean_dec(v_snd_1590_);
lean_dec(v_fst_1589_);
lean_dec(v_val_1580_);
lean_dec(v_val_1549_);
lean_dec_ref(v_toRing_1548_);
lean_dec_ref(v_a_1515_);
lean_dec_ref(v_e_1513_);
v_a_1635_ = lean_ctor_get(v___x_1598_, 0);
v_isSharedCheck_1642_ = !lean_is_exclusive(v___x_1598_);
if (v_isSharedCheck_1642_ == 0)
{
v___x_1637_ = v___x_1598_;
v_isShared_1638_ = v_isSharedCheck_1642_;
goto v_resetjp_1636_;
}
else
{
lean_inc(v_a_1635_);
lean_dec(v___x_1598_);
v___x_1637_ = lean_box(0);
v_isShared_1638_ = v_isSharedCheck_1642_;
goto v_resetjp_1636_;
}
v_resetjp_1636_:
{
lean_object* v___x_1640_; 
if (v_isShared_1638_ == 0)
{
v___x_1640_ = v___x_1637_;
goto v_reusejp_1639_;
}
else
{
lean_object* v_reuseFailAlloc_1641_; 
v_reuseFailAlloc_1641_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1641_, 0, v_a_1635_);
v___x_1640_ = v_reuseFailAlloc_1641_;
goto v_reusejp_1639_;
}
v_reusejp_1639_:
{
return v___x_1640_;
}
}
}
}
else
{
lean_object* v___x_1643_; 
lean_dec_ref(v_a_1515_);
v___x_1643_ = l_Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__3(v___x_1582_, v_a_1516_, v_a_1517_, v_a_1518_, v_a_1519_, v_a_1520_, v_a_1521_, v_a_1522_, v_a_1523_, v_a_1524_, v_a_1525_, v_a_1526_);
if (lean_obj_tag(v___x_1643_) == 0)
{
lean_object* v_a_1644_; lean_object* v___x_1645_; 
v_a_1644_ = lean_ctor_get(v___x_1643_, 0);
lean_inc(v_a_1644_);
lean_dec_ref_known(v___x_1643_, 1);
v___x_1645_ = l_Lean_Meta_mkEq(v_e_1513_, v_a_1644_, v_a_1523_, v_a_1524_, v_a_1525_, v_a_1526_);
if (lean_obj_tag(v___x_1645_) == 0)
{
lean_object* v_a_1646_; lean_object* v_type_1647_; lean_object* v_u_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1652_; 
v_a_1646_ = lean_ctor_get(v___x_1645_, 0);
lean_inc(v_a_1646_);
lean_dec_ref_known(v___x_1645_, 1);
v_type_1647_ = lean_ctor_get(v_toRing_1548_, 1);
lean_inc_ref(v_type_1647_);
v_u_1648_ = lean_ctor_get(v_toRing_1548_, 2);
lean_inc(v_u_1648_);
lean_dec_ref(v_toRing_1548_);
v___x_1649_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__7));
v___x_1650_ = lean_box(0);
if (v_isShared_1593_ == 0)
{
lean_ctor_set_tag(v___x_1592_, 1);
lean_ctor_set(v___x_1592_, 1, v___x_1650_);
lean_ctor_set(v___x_1592_, 0, v_u_1648_);
v___x_1652_ = v___x_1592_;
goto v_reusejp_1651_;
}
else
{
lean_object* v_reuseFailAlloc_1659_; 
v_reuseFailAlloc_1659_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1659_, 0, v_u_1648_);
lean_ctor_set(v_reuseFailAlloc_1659_, 1, v___x_1650_);
v___x_1652_ = v_reuseFailAlloc_1659_;
goto v_reusejp_1651_;
}
v_reusejp_1651_:
{
lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; 
v___x_1653_ = l_Lean_mkConst(v___x_1649_, v___x_1652_);
v___x_1654_ = l_Lean_mkNatLit(v_snd_1590_);
v___x_1655_ = l_Lean_mkIntLit(v_val_1580_);
lean_dec(v_val_1580_);
v___x_1656_ = l_Lean_eagerReflBoolTrue;
v___x_1657_ = l_Lean_mkApp6(v___x_1653_, v_type_1647_, v___x_1654_, v_val_1549_, v_fst_1589_, v___x_1655_, v___x_1656_);
v___x_1658_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_pushInvFact___redArg(v_a_1646_, v___x_1657_, v_a_1517_, v_a_1521_, v_a_1522_, v_a_1523_, v_a_1524_, v_a_1525_, v_a_1526_);
if (lean_obj_tag(v___x_1658_) == 0)
{
lean_dec_ref_known(v___x_1658_, 1);
goto v___jp_1528_;
}
else
{
return v___x_1658_;
}
}
}
else
{
lean_object* v_a_1660_; lean_object* v___x_1662_; uint8_t v_isShared_1663_; uint8_t v_isSharedCheck_1667_; 
lean_del_object(v___x_1592_);
lean_dec(v_snd_1590_);
lean_dec(v_fst_1589_);
lean_dec(v_val_1580_);
lean_dec(v_val_1549_);
lean_dec_ref(v_toRing_1548_);
v_a_1660_ = lean_ctor_get(v___x_1645_, 0);
v_isSharedCheck_1667_ = !lean_is_exclusive(v___x_1645_);
if (v_isSharedCheck_1667_ == 0)
{
v___x_1662_ = v___x_1645_;
v_isShared_1663_ = v_isSharedCheck_1667_;
goto v_resetjp_1661_;
}
else
{
lean_inc(v_a_1660_);
lean_dec(v___x_1645_);
v___x_1662_ = lean_box(0);
v_isShared_1663_ = v_isSharedCheck_1667_;
goto v_resetjp_1661_;
}
v_resetjp_1661_:
{
lean_object* v___x_1665_; 
if (v_isShared_1663_ == 0)
{
v___x_1665_ = v___x_1662_;
goto v_reusejp_1664_;
}
else
{
lean_object* v_reuseFailAlloc_1666_; 
v_reuseFailAlloc_1666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1666_, 0, v_a_1660_);
v___x_1665_ = v_reuseFailAlloc_1666_;
goto v_reusejp_1664_;
}
v_reusejp_1664_:
{
return v___x_1665_;
}
}
}
}
else
{
lean_object* v_a_1668_; lean_object* v___x_1670_; uint8_t v_isShared_1671_; uint8_t v_isSharedCheck_1675_; 
lean_del_object(v___x_1592_);
lean_dec(v_snd_1590_);
lean_dec(v_fst_1589_);
lean_dec(v_val_1580_);
lean_dec(v_val_1549_);
lean_dec_ref(v_toRing_1548_);
lean_dec_ref(v_e_1513_);
v_a_1668_ = lean_ctor_get(v___x_1643_, 0);
v_isSharedCheck_1675_ = !lean_is_exclusive(v___x_1643_);
if (v_isSharedCheck_1675_ == 0)
{
v___x_1670_ = v___x_1643_;
v_isShared_1671_ = v_isSharedCheck_1675_;
goto v_resetjp_1669_;
}
else
{
lean_inc(v_a_1668_);
lean_dec(v___x_1643_);
v___x_1670_ = lean_box(0);
v_isShared_1671_ = v_isSharedCheck_1675_;
goto v_resetjp_1669_;
}
v_resetjp_1669_:
{
lean_object* v___x_1673_; 
if (v_isShared_1671_ == 0)
{
v___x_1673_ = v___x_1670_;
goto v_reusejp_1672_;
}
else
{
lean_object* v_reuseFailAlloc_1674_; 
v_reuseFailAlloc_1674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1674_, 0, v_a_1668_);
v___x_1673_ = v_reuseFailAlloc_1674_;
goto v_reusejp_1672_;
}
v_reusejp_1672_:
{
return v___x_1673_;
}
}
}
}
}
else
{
lean_object* v___x_1676_; 
lean_dec(v_snd_1590_);
v___x_1676_ = l_Lean_Meta_Sym_Arith_getMulFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__2(v_a_1516_, v_a_1517_, v_a_1518_, v_a_1519_, v_a_1520_, v_a_1521_, v_a_1522_, v_a_1523_, v_a_1524_, v_a_1525_, v_a_1526_);
if (lean_obj_tag(v___x_1676_) == 0)
{
lean_object* v_a_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; 
v_a_1677_ = lean_ctor_get(v___x_1676_, 0);
lean_inc(v_a_1677_);
lean_dec_ref_known(v___x_1676_, 1);
v___x_1678_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__3, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__3);
v___x_1679_ = l_Lean_Meta_Sym_Arith_denoteNum___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__3(v___x_1678_, v_a_1516_, v_a_1517_, v_a_1518_, v_a_1519_, v_a_1520_, v_a_1521_, v_a_1522_, v_a_1523_, v_a_1524_, v_a_1525_, v_a_1526_);
if (lean_obj_tag(v___x_1679_) == 0)
{
lean_object* v_a_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; 
v_a_1680_ = lean_ctor_get(v___x_1679_, 0);
lean_inc(v_a_1680_);
lean_dec_ref_known(v___x_1679_, 1);
v___x_1681_ = l_Lean_mkAppB(v_a_1677_, v_a_1515_, v_e_1513_);
v___x_1682_ = l_Lean_Meta_mkEq(v___x_1681_, v_a_1680_, v_a_1523_, v_a_1524_, v_a_1525_, v_a_1526_);
if (lean_obj_tag(v___x_1682_) == 0)
{
lean_object* v_a_1683_; lean_object* v_type_1684_; lean_object* v_u_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1689_; 
v_a_1683_ = lean_ctor_get(v___x_1682_, 0);
lean_inc(v_a_1683_);
lean_dec_ref_known(v___x_1682_, 1);
v_type_1684_ = lean_ctor_get(v_toRing_1548_, 1);
lean_inc_ref(v_type_1684_);
v_u_1685_ = lean_ctor_get(v_toRing_1548_, 2);
lean_inc(v_u_1685_);
lean_dec_ref(v_toRing_1548_);
v___x_1686_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__9));
v___x_1687_ = lean_box(0);
if (v_isShared_1593_ == 0)
{
lean_ctor_set_tag(v___x_1592_, 1);
lean_ctor_set(v___x_1592_, 1, v___x_1687_);
lean_ctor_set(v___x_1592_, 0, v_u_1685_);
v___x_1689_ = v___x_1592_;
goto v_reusejp_1688_;
}
else
{
lean_object* v_reuseFailAlloc_1695_; 
v_reuseFailAlloc_1695_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1695_, 0, v_u_1685_);
lean_ctor_set(v_reuseFailAlloc_1695_, 1, v___x_1687_);
v___x_1689_ = v_reuseFailAlloc_1695_;
goto v_reusejp_1688_;
}
v_reusejp_1688_:
{
lean_object* v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; 
v___x_1690_ = l_Lean_mkConst(v___x_1686_, v___x_1689_);
v___x_1691_ = l_Lean_mkIntLit(v_val_1580_);
lean_dec(v_val_1580_);
v___x_1692_ = l_Lean_eagerReflBoolTrue;
v___x_1693_ = l_Lean_mkApp5(v___x_1690_, v_type_1684_, v_val_1549_, v_fst_1589_, v___x_1691_, v___x_1692_);
v___x_1694_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_pushInvFact___redArg(v_a_1683_, v___x_1693_, v_a_1517_, v_a_1521_, v_a_1522_, v_a_1523_, v_a_1524_, v_a_1525_, v_a_1526_);
if (lean_obj_tag(v___x_1694_) == 0)
{
lean_dec_ref_known(v___x_1694_, 1);
goto v___jp_1528_;
}
else
{
return v___x_1694_;
}
}
}
else
{
lean_object* v_a_1696_; lean_object* v___x_1698_; uint8_t v_isShared_1699_; uint8_t v_isSharedCheck_1703_; 
lean_del_object(v___x_1592_);
lean_dec(v_fst_1589_);
lean_dec(v_val_1580_);
lean_dec(v_val_1549_);
lean_dec_ref(v_toRing_1548_);
v_a_1696_ = lean_ctor_get(v___x_1682_, 0);
v_isSharedCheck_1703_ = !lean_is_exclusive(v___x_1682_);
if (v_isSharedCheck_1703_ == 0)
{
v___x_1698_ = v___x_1682_;
v_isShared_1699_ = v_isSharedCheck_1703_;
goto v_resetjp_1697_;
}
else
{
lean_inc(v_a_1696_);
lean_dec(v___x_1682_);
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
else
{
lean_object* v_a_1704_; lean_object* v___x_1706_; uint8_t v_isShared_1707_; uint8_t v_isSharedCheck_1711_; 
lean_dec(v_a_1677_);
lean_del_object(v___x_1592_);
lean_dec(v_fst_1589_);
lean_dec(v_val_1580_);
lean_dec(v_val_1549_);
lean_dec_ref(v_toRing_1548_);
lean_dec_ref(v_a_1515_);
lean_dec_ref(v_e_1513_);
v_a_1704_ = lean_ctor_get(v___x_1679_, 0);
v_isSharedCheck_1711_ = !lean_is_exclusive(v___x_1679_);
if (v_isSharedCheck_1711_ == 0)
{
v___x_1706_ = v___x_1679_;
v_isShared_1707_ = v_isSharedCheck_1711_;
goto v_resetjp_1705_;
}
else
{
lean_inc(v_a_1704_);
lean_dec(v___x_1679_);
v___x_1706_ = lean_box(0);
v_isShared_1707_ = v_isSharedCheck_1711_;
goto v_resetjp_1705_;
}
v_resetjp_1705_:
{
lean_object* v___x_1709_; 
if (v_isShared_1707_ == 0)
{
v___x_1709_ = v___x_1706_;
goto v_reusejp_1708_;
}
else
{
lean_object* v_reuseFailAlloc_1710_; 
v_reuseFailAlloc_1710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1710_, 0, v_a_1704_);
v___x_1709_ = v_reuseFailAlloc_1710_;
goto v_reusejp_1708_;
}
v_reusejp_1708_:
{
return v___x_1709_;
}
}
}
}
else
{
lean_object* v_a_1712_; lean_object* v___x_1714_; uint8_t v_isShared_1715_; uint8_t v_isSharedCheck_1719_; 
lean_del_object(v___x_1592_);
lean_dec(v_fst_1589_);
lean_dec(v_val_1580_);
lean_dec(v_val_1549_);
lean_dec_ref(v_toRing_1548_);
lean_dec_ref(v_a_1515_);
lean_dec_ref(v_e_1513_);
v_a_1712_ = lean_ctor_get(v___x_1676_, 0);
v_isSharedCheck_1719_ = !lean_is_exclusive(v___x_1676_);
if (v_isSharedCheck_1719_ == 0)
{
v___x_1714_ = v___x_1676_;
v_isShared_1715_ = v_isSharedCheck_1719_;
goto v_resetjp_1713_;
}
else
{
lean_inc(v_a_1712_);
lean_dec(v___x_1676_);
v___x_1714_ = lean_box(0);
v_isShared_1715_ = v_isSharedCheck_1719_;
goto v_resetjp_1713_;
}
v_resetjp_1713_:
{
lean_object* v___x_1717_; 
if (v_isShared_1715_ == 0)
{
v___x_1717_ = v___x_1714_;
goto v_reusejp_1716_;
}
else
{
lean_object* v_reuseFailAlloc_1718_; 
v_reuseFailAlloc_1718_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1718_, 0, v_a_1712_);
v___x_1717_ = v_reuseFailAlloc_1718_;
goto v_reusejp_1716_;
}
v_reusejp_1716_:
{
return v___x_1717_;
}
}
}
}
}
}
else
{
lean_object* v_a_1721_; lean_object* v___x_1723_; uint8_t v_isShared_1724_; uint8_t v_isSharedCheck_1728_; 
lean_dec(v_val_1580_);
lean_dec(v_val_1549_);
lean_dec_ref(v_toRing_1548_);
lean_dec_ref(v_a_1515_);
lean_dec_ref(v_e_1513_);
v_a_1721_ = lean_ctor_get(v___x_1587_, 0);
v_isSharedCheck_1728_ = !lean_is_exclusive(v___x_1587_);
if (v_isSharedCheck_1728_ == 0)
{
v___x_1723_ = v___x_1587_;
v_isShared_1724_ = v_isSharedCheck_1728_;
goto v_resetjp_1722_;
}
else
{
lean_inc(v_a_1721_);
lean_dec(v___x_1587_);
v___x_1723_ = lean_box(0);
v_isShared_1724_ = v_isSharedCheck_1728_;
goto v_resetjp_1722_;
}
v_resetjp_1722_:
{
lean_object* v___x_1726_; 
if (v_isShared_1724_ == 0)
{
v___x_1726_ = v___x_1723_;
goto v_reusejp_1725_;
}
else
{
lean_object* v_reuseFailAlloc_1727_; 
v_reuseFailAlloc_1727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1727_, 0, v_a_1721_);
v___x_1726_ = v_reuseFailAlloc_1727_;
goto v_reusejp_1725_;
}
v_reusejp_1725_:
{
return v___x_1726_;
}
}
}
}
}
else
{
lean_object* v_a_1729_; lean_object* v___x_1731_; uint8_t v_isShared_1732_; uint8_t v_isSharedCheck_1736_; 
lean_dec(v_val_1580_);
lean_dec(v_val_1549_);
lean_dec_ref(v_toRing_1548_);
lean_dec_ref(v_a_1515_);
lean_dec_ref(v_e_1513_);
v_a_1729_ = lean_ctor_get(v___x_1584_, 0);
v_isSharedCheck_1736_ = !lean_is_exclusive(v___x_1584_);
if (v_isSharedCheck_1736_ == 0)
{
v___x_1731_ = v___x_1584_;
v_isShared_1732_ = v_isSharedCheck_1736_;
goto v_resetjp_1730_;
}
else
{
lean_inc(v_a_1729_);
lean_dec(v___x_1584_);
v___x_1731_ = lean_box(0);
v_isShared_1732_ = v_isSharedCheck_1736_;
goto v_resetjp_1730_;
}
v_resetjp_1730_:
{
lean_object* v___x_1734_; 
if (v_isShared_1732_ == 0)
{
v___x_1734_ = v___x_1731_;
goto v_reusejp_1733_;
}
else
{
lean_object* v_reuseFailAlloc_1735_; 
v_reuseFailAlloc_1735_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1735_, 0, v_a_1729_);
v___x_1734_ = v_reuseFailAlloc_1735_;
goto v_reusejp_1733_;
}
v_reusejp_1733_:
{
return v___x_1734_;
}
}
}
}
else
{
lean_object* v_type_1737_; lean_object* v_u_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; 
lean_dec(v_val_1580_);
v_type_1737_ = lean_ctor_get(v_toRing_1548_, 1);
lean_inc_ref(v_type_1737_);
v_u_1738_ = lean_ctor_get(v_toRing_1548_, 2);
lean_inc(v_u_1738_);
lean_dec_ref(v_toRing_1548_);
v___x_1739_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__11));
v___x_1740_ = lean_box(0);
v___x_1741_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1741_, 0, v_u_1738_);
lean_ctor_set(v___x_1741_, 1, v___x_1740_);
v___x_1742_ = l_Lean_mkConst(v___x_1739_, v___x_1741_);
v___x_1743_ = l_Lean_mkAppB(v___x_1742_, v_type_1737_, v_val_1549_);
v___x_1744_ = l_Lean_Meta_Grind_pushEqCore___redArg(v_e_1513_, v_a_1515_, v___x_1743_, v___x_1576_, v_a_1517_, v_a_1519_, v_a_1523_, v_a_1524_, v_a_1525_, v_a_1526_);
if (lean_obj_tag(v___x_1744_) == 0)
{
lean_object* v___x_1746_; uint8_t v_isShared_1747_; uint8_t v_isSharedCheck_1752_; 
v_isSharedCheck_1752_ = !lean_is_exclusive(v___x_1744_);
if (v_isSharedCheck_1752_ == 0)
{
lean_object* v_unused_1753_; 
v_unused_1753_ = lean_ctor_get(v___x_1744_, 0);
lean_dec(v_unused_1753_);
v___x_1746_ = v___x_1744_;
v_isShared_1747_ = v_isSharedCheck_1752_;
goto v_resetjp_1745_;
}
else
{
lean_dec(v___x_1744_);
v___x_1746_ = lean_box(0);
v_isShared_1747_ = v_isSharedCheck_1752_;
goto v_resetjp_1745_;
}
v_resetjp_1745_:
{
lean_object* v___x_1748_; lean_object* v___x_1750_; 
v___x_1748_ = lean_box(0);
if (v_isShared_1747_ == 0)
{
lean_ctor_set(v___x_1746_, 0, v___x_1748_);
v___x_1750_ = v___x_1746_;
goto v_reusejp_1749_;
}
else
{
lean_object* v_reuseFailAlloc_1751_; 
v_reuseFailAlloc_1751_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1751_, 0, v___x_1748_);
v___x_1750_ = v_reuseFailAlloc_1751_;
goto v_reusejp_1749_;
}
v_reusejp_1749_:
{
return v___x_1750_;
}
}
}
else
{
return v___x_1744_;
}
}
}
else
{
lean_dec(v_a_1579_);
lean_dec_ref(v_e_1513_);
v___y_1551_ = v_a_1517_;
v___y_1552_ = v_a_1518_;
v___y_1553_ = v_a_1519_;
v___y_1554_ = v_a_1520_;
v___y_1555_ = v_a_1521_;
v___y_1556_ = v_a_1522_;
v___y_1557_ = v_a_1523_;
v___y_1558_ = v_a_1524_;
v___y_1559_ = v_a_1525_;
v___y_1560_ = v_a_1526_;
goto v___jp_1550_;
}
}
else
{
lean_object* v_a_1754_; lean_object* v___x_1756_; uint8_t v_isShared_1757_; uint8_t v_isSharedCheck_1761_; 
lean_dec(v_val_1549_);
lean_dec_ref(v_toRing_1548_);
lean_dec_ref(v_a_1515_);
lean_dec_ref(v_e_1513_);
v_a_1754_ = lean_ctor_get(v___x_1578_, 0);
v_isSharedCheck_1761_ = !lean_is_exclusive(v___x_1578_);
if (v_isSharedCheck_1761_ == 0)
{
v___x_1756_ = v___x_1578_;
v_isShared_1757_ = v_isSharedCheck_1761_;
goto v_resetjp_1755_;
}
else
{
lean_inc(v_a_1754_);
lean_dec(v___x_1578_);
v___x_1756_ = lean_box(0);
v_isShared_1757_ = v_isSharedCheck_1761_;
goto v_resetjp_1755_;
}
v_resetjp_1755_:
{
lean_object* v___x_1759_; 
if (v_isShared_1757_ == 0)
{
v___x_1759_ = v___x_1756_;
goto v_reusejp_1758_;
}
else
{
lean_object* v_reuseFailAlloc_1760_; 
v_reuseFailAlloc_1760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1760_, 0, v_a_1754_);
v___x_1759_ = v_reuseFailAlloc_1760_;
goto v_reusejp_1758_;
}
v_reusejp_1758_:
{
return v___x_1759_;
}
}
}
}
else
{
lean_dec(v_val_1549_);
lean_dec_ref(v_toRing_1548_);
lean_dec_ref(v_a_1515_);
lean_dec_ref(v_e_1513_);
return v___x_1577_;
}
}
else
{
lean_object* v___x_1762_; lean_object* v___x_1764_; 
lean_dec(v_val_1549_);
lean_dec_ref(v_toRing_1548_);
lean_dec_ref(v___f_1531_);
lean_dec_ref(v_a_1515_);
lean_dec_ref(v_e_1513_);
v___x_1762_ = lean_box(0);
if (v_isShared_1574_ == 0)
{
lean_ctor_set(v___x_1573_, 0, v___x_1762_);
v___x_1764_ = v___x_1573_;
goto v_reusejp_1763_;
}
else
{
lean_object* v_reuseFailAlloc_1765_; 
v_reuseFailAlloc_1765_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1765_, 0, v___x_1762_);
v___x_1764_ = v_reuseFailAlloc_1765_;
goto v_reusejp_1763_;
}
v_reusejp_1763_:
{
return v___x_1764_;
}
}
}
}
else
{
lean_object* v_a_1767_; lean_object* v___x_1769_; uint8_t v_isShared_1770_; uint8_t v_isSharedCheck_1774_; 
lean_dec(v_val_1549_);
lean_dec_ref(v_toRing_1548_);
lean_dec_ref(v___f_1531_);
lean_dec_ref(v_a_1515_);
lean_dec_ref(v_e_1513_);
v_a_1767_ = lean_ctor_get(v___x_1570_, 0);
v_isSharedCheck_1774_ = !lean_is_exclusive(v___x_1570_);
if (v_isSharedCheck_1774_ == 0)
{
v___x_1769_ = v___x_1570_;
v_isShared_1770_ = v_isSharedCheck_1774_;
goto v_resetjp_1768_;
}
else
{
lean_inc(v_a_1767_);
lean_dec(v___x_1570_);
v___x_1769_ = lean_box(0);
v_isShared_1770_ = v_isSharedCheck_1774_;
goto v_resetjp_1768_;
}
v_resetjp_1768_:
{
lean_object* v___x_1772_; 
if (v_isShared_1770_ == 0)
{
v___x_1772_ = v___x_1769_;
goto v_reusejp_1771_;
}
else
{
lean_object* v_reuseFailAlloc_1773_; 
v_reuseFailAlloc_1773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1773_, 0, v_a_1767_);
v___x_1772_ = v_reuseFailAlloc_1773_;
goto v_reusejp_1771_;
}
v_reusejp_1771_:
{
return v___x_1772_;
}
}
}
v___jp_1550_:
{
lean_object* v_type_1561_; lean_object* v_u_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; 
v_type_1561_ = lean_ctor_get(v_toRing_1548_, 1);
lean_inc_ref(v_type_1561_);
v_u_1562_ = lean_ctor_get(v_toRing_1548_, 2);
lean_inc(v_u_1562_);
lean_dec_ref(v_toRing_1548_);
v___x_1563_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___closed__2));
v___x_1564_ = lean_box(0);
v___x_1565_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1565_, 0, v_u_1562_);
lean_ctor_set(v___x_1565_, 1, v___x_1564_);
v___x_1566_ = l_Lean_mkConst(v___x_1563_, v___x_1565_);
v___x_1567_ = l_Lean_mkApp3(v___x_1566_, v_type_1561_, v_val_1549_, v_a_1515_);
v___x_1568_ = lean_unsigned_to_nat(0u);
v___x_1569_ = l_Lean_Meta_Grind_pushNewFact(v___x_1567_, v___x_1568_, v___y_1551_, v___y_1552_, v___y_1553_, v___y_1554_, v___y_1555_, v___y_1556_, v___y_1557_, v___y_1558_, v___y_1559_, v___y_1560_);
return v___x_1569_;
}
}
else
{
lean_object* v___x_1775_; lean_object* v___x_1777_; 
lean_dec(v_fieldInst_x3f_1547_);
lean_dec(v_a_1543_);
lean_dec_ref(v___f_1531_);
lean_dec_ref(v_a_1515_);
lean_dec_ref(v_e_1513_);
v___x_1775_ = lean_box(0);
if (v_isShared_1546_ == 0)
{
lean_ctor_set(v___x_1545_, 0, v___x_1775_);
v___x_1777_ = v___x_1545_;
goto v_reusejp_1776_;
}
else
{
lean_object* v_reuseFailAlloc_1778_; 
v_reuseFailAlloc_1778_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1778_, 0, v___x_1775_);
v___x_1777_ = v_reuseFailAlloc_1778_;
goto v_reusejp_1776_;
}
v_reusejp_1776_:
{
return v___x_1777_;
}
}
}
}
else
{
lean_object* v_a_1780_; lean_object* v___x_1782_; uint8_t v_isShared_1783_; uint8_t v_isSharedCheck_1787_; 
lean_dec_ref(v___f_1531_);
lean_dec_ref(v_a_1515_);
lean_dec_ref(v_e_1513_);
v_a_1780_ = lean_ctor_get(v___x_1542_, 0);
v_isSharedCheck_1787_ = !lean_is_exclusive(v___x_1542_);
if (v_isSharedCheck_1787_ == 0)
{
v___x_1782_ = v___x_1542_;
v_isShared_1783_ = v_isSharedCheck_1787_;
goto v_resetjp_1781_;
}
else
{
lean_inc(v_a_1780_);
lean_dec(v___x_1542_);
v___x_1782_ = lean_box(0);
v_isShared_1783_ = v_isSharedCheck_1787_;
goto v_resetjp_1781_;
}
v_resetjp_1781_:
{
lean_object* v___x_1785_; 
if (v_isShared_1783_ == 0)
{
v___x_1785_ = v___x_1782_;
goto v_reusejp_1784_;
}
else
{
lean_object* v_reuseFailAlloc_1786_; 
v_reuseFailAlloc_1786_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1786_, 0, v_a_1780_);
v___x_1785_ = v_reuseFailAlloc_1786_;
goto v_reusejp_1784_;
}
v_reusejp_1784_:
{
return v___x_1785_;
}
}
}
}
}
}
else
{
lean_object* v_a_1789_; lean_object* v___x_1791_; uint8_t v_isShared_1792_; uint8_t v_isSharedCheck_1796_; 
lean_dec_ref(v___f_1531_);
lean_dec_ref(v_a_1515_);
lean_dec_ref(v_e_1513_);
v_a_1789_ = lean_ctor_get(v___x_1532_, 0);
v_isSharedCheck_1796_ = !lean_is_exclusive(v___x_1532_);
if (v_isSharedCheck_1796_ == 0)
{
v___x_1791_ = v___x_1532_;
v_isShared_1792_ = v_isSharedCheck_1796_;
goto v_resetjp_1790_;
}
else
{
lean_inc(v_a_1789_);
lean_dec(v___x_1532_);
v___x_1791_ = lean_box(0);
v_isShared_1792_ = v_isSharedCheck_1796_;
goto v_resetjp_1790_;
}
v_resetjp_1790_:
{
lean_object* v___x_1794_; 
if (v_isShared_1792_ == 0)
{
v___x_1794_ = v___x_1791_;
goto v_reusejp_1793_;
}
else
{
lean_object* v_reuseFailAlloc_1795_; 
v_reuseFailAlloc_1795_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1795_, 0, v_a_1789_);
v___x_1794_ = v_reuseFailAlloc_1795_;
goto v_reusejp_1793_;
}
v_reusejp_1793_:
{
return v___x_1794_;
}
}
}
v___jp_1528_:
{
lean_object* v___x_1529_; lean_object* v___x_1530_; 
v___x_1529_ = lean_box(0);
v___x_1530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1530_, 0, v___x_1529_);
return v___x_1530_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv___boxed(lean_object* v_e_1797_, lean_object* v_inst_1798_, lean_object* v_a_1799_, lean_object* v_a_1800_, lean_object* v_a_1801_, lean_object* v_a_1802_, lean_object* v_a_1803_, lean_object* v_a_1804_, lean_object* v_a_1805_, lean_object* v_a_1806_, lean_object* v_a_1807_, lean_object* v_a_1808_, lean_object* v_a_1809_, lean_object* v_a_1810_, lean_object* v_a_1811_){
_start:
{
lean_object* v_res_1812_; 
v_res_1812_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv(v_e_1797_, v_inst_1798_, v_a_1799_, v_a_1800_, v_a_1801_, v_a_1802_, v_a_1803_, v_a_1804_, v_a_1805_, v_a_1806_, v_a_1807_, v_a_1808_, v_a_1809_, v_a_1810_);
lean_dec(v_a_1810_);
lean_dec_ref(v_a_1809_);
lean_dec(v_a_1808_);
lean_dec_ref(v_a_1807_);
lean_dec(v_a_1806_);
lean_dec_ref(v_a_1805_);
lean_dec(v_a_1804_);
lean_dec_ref(v_a_1803_);
lean_dec(v_a_1802_);
lean_dec(v_a_1801_);
lean_dec_ref(v_a_1800_);
lean_dec_ref(v_inst_1798_);
return v_res_1812_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0(lean_object* v_00_u03b2_1813_, lean_object* v_x_1814_, lean_object* v_x_1815_, lean_object* v_x_1816_){
_start:
{
lean_object* v___x_1817_; 
v___x_1817_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0___redArg(v_x_1814_, v_x_1815_, v_x_1816_);
return v___x_1817_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1(lean_object* v_00_u03b2_1818_, lean_object* v_x_1819_, lean_object* v_x_1820_){
_start:
{
uint8_t v___x_1821_; 
v___x_1821_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1___redArg(v_x_1819_, v_x_1820_);
return v___x_1821_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1___boxed(lean_object* v_00_u03b2_1822_, lean_object* v_x_1823_, lean_object* v_x_1824_){
_start:
{
uint8_t v_res_1825_; lean_object* v_r_1826_; 
v_res_1825_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1(v_00_u03b2_1822_, v_x_1823_, v_x_1824_);
lean_dec_ref(v_x_1824_);
lean_dec_ref(v_x_1823_);
v_r_1826_ = lean_box(v_res_1825_);
return v_r_1826_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0(lean_object* v_00_u03b2_1827_, lean_object* v_x_1828_, size_t v_x_1829_, size_t v_x_1830_, lean_object* v_x_1831_, lean_object* v_x_1832_){
_start:
{
lean_object* v___x_1833_; 
v___x_1833_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg(v_x_1828_, v_x_1829_, v_x_1830_, v_x_1831_, v_x_1832_);
return v___x_1833_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1834_, lean_object* v_x_1835_, lean_object* v_x_1836_, lean_object* v_x_1837_, lean_object* v_x_1838_, lean_object* v_x_1839_){
_start:
{
size_t v_x_79774__boxed_1840_; size_t v_x_79775__boxed_1841_; lean_object* v_res_1842_; 
v_x_79774__boxed_1840_ = lean_unbox_usize(v_x_1836_);
lean_dec(v_x_1836_);
v_x_79775__boxed_1841_ = lean_unbox_usize(v_x_1837_);
lean_dec(v_x_1837_);
v_res_1842_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0(v_00_u03b2_1834_, v_x_1835_, v_x_79774__boxed_1840_, v_x_79775__boxed_1841_, v_x_1838_, v_x_1839_);
return v_res_1842_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1_spec__2(lean_object* v_00_u03b2_1843_, lean_object* v_x_1844_, size_t v_x_1845_, lean_object* v_x_1846_){
_start:
{
uint8_t v___x_1847_; 
v___x_1847_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1_spec__2___redArg(v_x_1844_, v_x_1845_, v_x_1846_);
return v___x_1847_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1848_, lean_object* v_x_1849_, lean_object* v_x_1850_, lean_object* v_x_1851_){
_start:
{
size_t v_x_79791__boxed_1852_; uint8_t v_res_1853_; lean_object* v_r_1854_; 
v_x_79791__boxed_1852_ = lean_unbox_usize(v_x_1850_);
lean_dec(v_x_1850_);
v_res_1853_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1_spec__2(v_00_u03b2_1848_, v_x_1849_, v_x_79791__boxed_1852_, v_x_1851_);
lean_dec_ref(v_x_1851_);
lean_dec_ref(v_x_1849_);
v_r_1854_ = lean_box(v_res_1853_);
return v_r_1854_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1855_, lean_object* v_n_1856_, lean_object* v_k_1857_, lean_object* v_v_1858_){
_start:
{
lean_object* v___x_1859_; 
v___x_1859_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0_spec__1___redArg(v_n_1856_, v_k_1857_, v_v_1858_);
return v___x_1859_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_1860_, size_t v_depth_1861_, lean_object* v_keys_1862_, lean_object* v_vals_1863_, lean_object* v_heq_1864_, lean_object* v_i_1865_, lean_object* v_entries_1866_){
_start:
{
lean_object* v___x_1867_; 
v___x_1867_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0_spec__2___redArg(v_depth_1861_, v_keys_1862_, v_vals_1863_, v_i_1865_, v_entries_1866_);
return v___x_1867_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1868_, lean_object* v_depth_1869_, lean_object* v_keys_1870_, lean_object* v_vals_1871_, lean_object* v_heq_1872_, lean_object* v_i_1873_, lean_object* v_entries_1874_){
_start:
{
size_t v_depth_boxed_1875_; lean_object* v_res_1876_; 
v_depth_boxed_1875_ = lean_unbox_usize(v_depth_1869_);
lean_dec(v_depth_1869_);
v_res_1876_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0_spec__2(v_00_u03b2_1868_, v_depth_boxed_1875_, v_keys_1870_, v_vals_1871_, v_heq_1872_, v_i_1873_, v_entries_1874_);
lean_dec_ref(v_vals_1871_);
lean_dec_ref(v_keys_1870_);
return v_res_1876_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_1877_, lean_object* v_keys_1878_, lean_object* v_vals_1879_, lean_object* v_heq_1880_, lean_object* v_i_1881_, lean_object* v_k_1882_){
_start:
{
uint8_t v___x_1883_; 
v___x_1883_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1_spec__2_spec__5___redArg(v_keys_1878_, v_i_1881_, v_k_1882_);
return v___x_1883_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b2_1884_, lean_object* v_keys_1885_, lean_object* v_vals_1886_, lean_object* v_heq_1887_, lean_object* v_i_1888_, lean_object* v_k_1889_){
_start:
{
uint8_t v_res_1890_; lean_object* v_r_1891_; 
v_res_1890_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__1_spec__2_spec__5(v_00_u03b2_1884_, v_keys_1885_, v_vals_1886_, v_heq_1887_, v_i_1888_, v_k_1889_);
lean_dec_ref(v_k_1889_);
lean_dec_ref(v_vals_1886_);
lean_dec_ref(v_keys_1885_);
v_r_1891_ = lean_box(v_res_1890_);
return v_r_1891_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0_spec__1_spec__5(lean_object* v_00_u03b2_1892_, lean_object* v_x_1893_, lean_object* v_x_1894_, lean_object* v_x_1895_, lean_object* v_x_1896_){
_start:
{
lean_object* v___x_1897_; 
v___x_1897_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0_spec__1_spec__5___redArg(v_x_1893_, v_x_1894_, v_x_1895_, v_x_1896_);
return v___x_1897_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars___lam__0(lean_object* v_size_1898_, lean_object* v_s_1899_){
_start:
{
lean_object* v_toRingState_1900_; lean_object* v_denoteEntries_1901_; lean_object* v_nextId_1902_; lean_object* v_steps_1903_; lean_object* v_queue_1904_; lean_object* v_basis_1905_; lean_object* v_diseqs_1906_; uint8_t v_recheck_1907_; lean_object* v_invSet_1908_; lean_object* v_numEq0_x3f_1909_; uint8_t v_numEq0Updated_1910_; lean_object* v___x_1912_; uint8_t v_isShared_1913_; uint8_t v_isSharedCheck_1917_; 
v_toRingState_1900_ = lean_ctor_get(v_s_1899_, 0);
v_denoteEntries_1901_ = lean_ctor_get(v_s_1899_, 1);
v_nextId_1902_ = lean_ctor_get(v_s_1899_, 2);
v_steps_1903_ = lean_ctor_get(v_s_1899_, 3);
v_queue_1904_ = lean_ctor_get(v_s_1899_, 4);
v_basis_1905_ = lean_ctor_get(v_s_1899_, 5);
v_diseqs_1906_ = lean_ctor_get(v_s_1899_, 6);
v_recheck_1907_ = lean_ctor_get_uint8(v_s_1899_, sizeof(void*)*10);
v_invSet_1908_ = lean_ctor_get(v_s_1899_, 7);
v_numEq0_x3f_1909_ = lean_ctor_get(v_s_1899_, 9);
v_numEq0Updated_1910_ = lean_ctor_get_uint8(v_s_1899_, sizeof(void*)*10 + 1);
v_isSharedCheck_1917_ = !lean_is_exclusive(v_s_1899_);
if (v_isSharedCheck_1917_ == 0)
{
lean_object* v_unused_1918_; 
v_unused_1918_ = lean_ctor_get(v_s_1899_, 8);
lean_dec(v_unused_1918_);
v___x_1912_ = v_s_1899_;
v_isShared_1913_ = v_isSharedCheck_1917_;
goto v_resetjp_1911_;
}
else
{
lean_inc(v_numEq0_x3f_1909_);
lean_inc(v_invSet_1908_);
lean_inc(v_diseqs_1906_);
lean_inc(v_basis_1905_);
lean_inc(v_queue_1904_);
lean_inc(v_steps_1903_);
lean_inc(v_nextId_1902_);
lean_inc(v_denoteEntries_1901_);
lean_inc(v_toRingState_1900_);
lean_dec(v_s_1899_);
v___x_1912_ = lean_box(0);
v_isShared_1913_ = v_isSharedCheck_1917_;
goto v_resetjp_1911_;
}
v_resetjp_1911_:
{
lean_object* v___x_1915_; 
if (v_isShared_1913_ == 0)
{
lean_ctor_set(v___x_1912_, 8, v_size_1898_);
v___x_1915_ = v___x_1912_;
goto v_reusejp_1914_;
}
else
{
lean_object* v_reuseFailAlloc_1916_; 
v_reuseFailAlloc_1916_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v_reuseFailAlloc_1916_, 0, v_toRingState_1900_);
lean_ctor_set(v_reuseFailAlloc_1916_, 1, v_denoteEntries_1901_);
lean_ctor_set(v_reuseFailAlloc_1916_, 2, v_nextId_1902_);
lean_ctor_set(v_reuseFailAlloc_1916_, 3, v_steps_1903_);
lean_ctor_set(v_reuseFailAlloc_1916_, 4, v_queue_1904_);
lean_ctor_set(v_reuseFailAlloc_1916_, 5, v_basis_1905_);
lean_ctor_set(v_reuseFailAlloc_1916_, 6, v_diseqs_1906_);
lean_ctor_set(v_reuseFailAlloc_1916_, 7, v_invSet_1908_);
lean_ctor_set(v_reuseFailAlloc_1916_, 8, v_size_1898_);
lean_ctor_set(v_reuseFailAlloc_1916_, 9, v_numEq0_x3f_1909_);
lean_ctor_set_uint8(v_reuseFailAlloc_1916_, sizeof(void*)*10, v_recheck_1907_);
lean_ctor_set_uint8(v_reuseFailAlloc_1916_, sizeof(void*)*10 + 1, v_numEq0Updated_1910_);
v___x_1915_ = v_reuseFailAlloc_1916_;
goto v_reusejp_1914_;
}
v_reusejp_1914_:
{
return v___x_1915_;
}
}
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1919_; double v___x_1920_; 
v___x_1919_ = lean_unsigned_to_nat(0u);
v___x_1920_ = lean_float_of_nat(v___x_1919_);
return v___x_1920_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg(lean_object* v_cls_1924_, lean_object* v_msg_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_){
_start:
{
lean_object* v_ref_1931_; lean_object* v___x_1932_; lean_object* v_a_1933_; lean_object* v___x_1935_; uint8_t v_isShared_1936_; uint8_t v_isSharedCheck_1978_; 
v_ref_1931_ = lean_ctor_get(v___y_1928_, 2);
v___x_1932_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5(v_msg_1925_, v___y_1926_, v___y_1927_, v___y_1928_, v___y_1929_);
v_a_1933_ = lean_ctor_get(v___x_1932_, 0);
v_isSharedCheck_1978_ = !lean_is_exclusive(v___x_1932_);
if (v_isSharedCheck_1978_ == 0)
{
v___x_1935_ = v___x_1932_;
v_isShared_1936_ = v_isSharedCheck_1978_;
goto v_resetjp_1934_;
}
else
{
lean_inc(v_a_1933_);
lean_dec(v___x_1932_);
v___x_1935_ = lean_box(0);
v_isShared_1936_ = v_isSharedCheck_1978_;
goto v_resetjp_1934_;
}
v_resetjp_1934_:
{
lean_object* v___x_1937_; lean_object* v_traceState_1938_; lean_object* v_env_1939_; lean_object* v_nextMacroScope_1940_; lean_object* v_ngen_1941_; lean_object* v_auxDeclNGen_1942_; lean_object* v_cache_1943_; lean_object* v_recordedDeps_1944_; lean_object* v_messages_1945_; lean_object* v_infoState_1946_; lean_object* v_snapshotTasks_1947_; lean_object* v___x_1949_; uint8_t v_isShared_1950_; uint8_t v_isSharedCheck_1977_; 
v___x_1937_ = lean_st_ref_take(v___y_1929_);
v_traceState_1938_ = lean_ctor_get(v___x_1937_, 4);
v_env_1939_ = lean_ctor_get(v___x_1937_, 0);
v_nextMacroScope_1940_ = lean_ctor_get(v___x_1937_, 1);
v_ngen_1941_ = lean_ctor_get(v___x_1937_, 2);
v_auxDeclNGen_1942_ = lean_ctor_get(v___x_1937_, 3);
v_cache_1943_ = lean_ctor_get(v___x_1937_, 5);
v_recordedDeps_1944_ = lean_ctor_get(v___x_1937_, 6);
v_messages_1945_ = lean_ctor_get(v___x_1937_, 7);
v_infoState_1946_ = lean_ctor_get(v___x_1937_, 8);
v_snapshotTasks_1947_ = lean_ctor_get(v___x_1937_, 9);
v_isSharedCheck_1977_ = !lean_is_exclusive(v___x_1937_);
if (v_isSharedCheck_1977_ == 0)
{
v___x_1949_ = v___x_1937_;
v_isShared_1950_ = v_isSharedCheck_1977_;
goto v_resetjp_1948_;
}
else
{
lean_inc(v_snapshotTasks_1947_);
lean_inc(v_infoState_1946_);
lean_inc(v_messages_1945_);
lean_inc(v_recordedDeps_1944_);
lean_inc(v_cache_1943_);
lean_inc(v_traceState_1938_);
lean_inc(v_auxDeclNGen_1942_);
lean_inc(v_ngen_1941_);
lean_inc(v_nextMacroScope_1940_);
lean_inc(v_env_1939_);
lean_dec(v___x_1937_);
v___x_1949_ = lean_box(0);
v_isShared_1950_ = v_isSharedCheck_1977_;
goto v_resetjp_1948_;
}
v_resetjp_1948_:
{
uint64_t v_tid_1951_; lean_object* v_traces_1952_; lean_object* v___x_1954_; uint8_t v_isShared_1955_; uint8_t v_isSharedCheck_1976_; 
v_tid_1951_ = lean_ctor_get_uint64(v_traceState_1938_, sizeof(void*)*1);
v_traces_1952_ = lean_ctor_get(v_traceState_1938_, 0);
v_isSharedCheck_1976_ = !lean_is_exclusive(v_traceState_1938_);
if (v_isSharedCheck_1976_ == 0)
{
v___x_1954_ = v_traceState_1938_;
v_isShared_1955_ = v_isSharedCheck_1976_;
goto v_resetjp_1953_;
}
else
{
lean_inc(v_traces_1952_);
lean_dec(v_traceState_1938_);
v___x_1954_ = lean_box(0);
v_isShared_1955_ = v_isSharedCheck_1976_;
goto v_resetjp_1953_;
}
v_resetjp_1953_:
{
lean_object* v___x_1956_; lean_object* v___x_1957_; double v___x_1958_; uint8_t v___x_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; lean_object* v___x_1967_; 
v___x_1956_ = lean_box(0);
v___x_1957_ = lean_box(0);
v___x_1958_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg___closed__0);
v___x_1959_ = 0;
v___x_1960_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg___closed__1));
v___x_1961_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1961_, 0, v_cls_1924_);
lean_ctor_set(v___x_1961_, 1, v___x_1957_);
lean_ctor_set(v___x_1961_, 2, v___x_1960_);
lean_ctor_set_float(v___x_1961_, sizeof(void*)*3, v___x_1958_);
lean_ctor_set_float(v___x_1961_, sizeof(void*)*3 + 8, v___x_1958_);
lean_ctor_set_uint8(v___x_1961_, sizeof(void*)*3 + 16, v___x_1959_);
v___x_1962_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg___closed__2));
v___x_1963_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1963_, 0, v___x_1961_);
lean_ctor_set(v___x_1963_, 1, v_a_1933_);
lean_ctor_set(v___x_1963_, 2, v___x_1962_);
lean_inc(v_ref_1931_);
v___x_1964_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1964_, 0, v_ref_1931_);
lean_ctor_set(v___x_1964_, 1, v___x_1963_);
v___x_1965_ = l_Lean_PersistentArray_push___redArg(v_traces_1952_, v___x_1964_);
if (v_isShared_1955_ == 0)
{
lean_ctor_set(v___x_1954_, 0, v___x_1965_);
v___x_1967_ = v___x_1954_;
goto v_reusejp_1966_;
}
else
{
lean_object* v_reuseFailAlloc_1975_; 
v_reuseFailAlloc_1975_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1975_, 0, v___x_1965_);
lean_ctor_set_uint64(v_reuseFailAlloc_1975_, sizeof(void*)*1, v_tid_1951_);
v___x_1967_ = v_reuseFailAlloc_1975_;
goto v_reusejp_1966_;
}
v_reusejp_1966_:
{
lean_object* v___x_1969_; 
if (v_isShared_1950_ == 0)
{
lean_ctor_set(v___x_1949_, 4, v___x_1967_);
v___x_1969_ = v___x_1949_;
goto v_reusejp_1968_;
}
else
{
lean_object* v_reuseFailAlloc_1974_; 
v_reuseFailAlloc_1974_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1974_, 0, v_env_1939_);
lean_ctor_set(v_reuseFailAlloc_1974_, 1, v_nextMacroScope_1940_);
lean_ctor_set(v_reuseFailAlloc_1974_, 2, v_ngen_1941_);
lean_ctor_set(v_reuseFailAlloc_1974_, 3, v_auxDeclNGen_1942_);
lean_ctor_set(v_reuseFailAlloc_1974_, 4, v___x_1967_);
lean_ctor_set(v_reuseFailAlloc_1974_, 5, v_cache_1943_);
lean_ctor_set(v_reuseFailAlloc_1974_, 6, v_recordedDeps_1944_);
lean_ctor_set(v_reuseFailAlloc_1974_, 7, v_messages_1945_);
lean_ctor_set(v_reuseFailAlloc_1974_, 8, v_infoState_1946_);
lean_ctor_set(v_reuseFailAlloc_1974_, 9, v_snapshotTasks_1947_);
v___x_1969_ = v_reuseFailAlloc_1974_;
goto v_reusejp_1968_;
}
v_reusejp_1968_:
{
lean_object* v___x_1970_; lean_object* v___x_1972_; 
v___x_1970_ = lean_st_ref_put(v___y_1929_, v___x_1969_);
if (v_isShared_1936_ == 0)
{
lean_ctor_set(v___x_1935_, 0, v___x_1956_);
v___x_1972_ = v___x_1935_;
goto v_reusejp_1971_;
}
else
{
lean_object* v_reuseFailAlloc_1973_; 
v_reuseFailAlloc_1973_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1973_, 0, v___x_1956_);
v___x_1972_ = v_reuseFailAlloc_1973_;
goto v_reusejp_1971_;
}
v_reusejp_1971_:
{
return v___x_1972_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg___boxed(lean_object* v_cls_1979_, lean_object* v_msg_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_){
_start:
{
lean_object* v_res_1986_; 
v_res_1986_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg(v_cls_1979_, v_msg_1980_, v___y_1981_, v___y_1982_, v___y_1983_, v___y_1984_);
lean_dec(v___y_1984_);
lean_dec_ref(v___y_1983_);
lean_dec(v___y_1982_);
lean_dec_ref(v___y_1981_);
return v_res_1986_;
}
}
static lean_object* _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__8(void){
_start:
{
lean_object* v___x_2002_; lean_object* v___x_2003_; lean_object* v___x_2004_; 
v___x_2002_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__5));
v___x_2003_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__7));
v___x_2004_ = l_Lean_Name_append(v___x_2003_, v___x_2002_);
return v___x_2004_;
}
}
static lean_object* _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__10(void){
_start:
{
lean_object* v___x_2006_; lean_object* v___x_2007_; 
v___x_2006_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__9));
v___x_2007_ = l_Lean_stringToMessageData(v___x_2006_);
return v___x_2007_;
}
}
static lean_object* _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__12(void){
_start:
{
lean_object* v___x_2009_; lean_object* v___x_2010_; 
v___x_2009_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__11));
v___x_2010_ = l_Lean_stringToMessageData(v___x_2009_);
return v___x_2010_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg(lean_object* v_a_2011_, lean_object* v_snd_2012_, lean_object* v_fst_2013_, lean_object* v_fst_2014_, lean_object* v___x_2015_, lean_object* v_range_2016_, lean_object* v_b_2017_, lean_object* v_i_2018_, lean_object* v___y_2019_, lean_object* v___y_2020_, lean_object* v___y_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_, lean_object* v___y_2029_){
_start:
{
lean_object* v_stop_2031_; lean_object* v_step_2032_; uint8_t v___x_2033_; 
v_stop_2031_ = lean_ctor_get(v_range_2016_, 1);
v_step_2032_ = lean_ctor_get(v_range_2016_, 2);
v___x_2033_ = lean_nat_dec_lt(v_i_2018_, v_stop_2031_);
if (v___x_2033_ == 0)
{
lean_object* v___x_2034_; 
lean_dec(v_i_2018_);
lean_dec_ref(v_fst_2014_);
lean_dec_ref(v_fst_2013_);
lean_dec(v_snd_2012_);
lean_dec_ref(v_a_2011_);
v___x_2034_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2034_, 0, v_b_2017_);
return v___x_2034_;
}
else
{
lean_object* v_size_2035_; lean_object* v___x_2036_; lean_object* v___y_2038_; lean_object* v___y_2039_; lean_object* v___y_2040_; lean_object* v___y_2041_; lean_object* v___y_2042_; lean_object* v___y_2043_; lean_object* v___y_2044_; lean_object* v___y_2045_; lean_object* v___y_2046_; lean_object* v___y_2047_; lean_object* v___y_2048_; lean_object* v___y_2063_; lean_object* v___x_2089_; uint8_t v___x_2090_; 
v_size_2035_ = lean_ctor_get(v___x_2015_, 2);
v___x_2036_ = lean_box(0);
v___x_2089_ = l_Lean_instInhabitedExpr;
v___x_2090_ = lean_nat_dec_lt(v_i_2018_, v_size_2035_);
if (v___x_2090_ == 0)
{
lean_object* v___x_2091_; 
v___x_2091_ = l_outOfBounds___redArg(v___x_2089_);
v___y_2063_ = v___x_2091_;
goto v___jp_2062_;
}
else
{
lean_object* v___x_2092_; 
v___x_2092_ = l_Lean_PersistentArray_get_x21___redArg(v___x_2089_, v___x_2015_, v_i_2018_);
v___y_2063_ = v___x_2092_;
goto v___jp_2062_;
}
v___jp_2037_:
{
lean_object* v_toRing_2049_; lean_object* v_type_2050_; lean_object* v_u_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; 
v_toRing_2049_ = lean_ctor_get(v_a_2011_, 0);
v_type_2050_ = lean_ctor_get(v_toRing_2049_, 1);
v_u_2051_ = lean_ctor_get(v_toRing_2049_, 2);
v___x_2052_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__2));
v___x_2053_ = lean_box(0);
lean_inc(v_u_2051_);
v___x_2054_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2054_, 0, v_u_2051_);
lean_ctor_set(v___x_2054_, 1, v___x_2053_);
v___x_2055_ = l_Lean_mkConst(v___x_2052_, v___x_2054_);
lean_inc(v_snd_2012_);
v___x_2056_ = l_Lean_mkNatLit(v_snd_2012_);
lean_inc_ref(v_fst_2014_);
lean_inc_ref(v_fst_2013_);
lean_inc_ref(v_type_2050_);
v___x_2057_ = l_Lean_mkApp5(v___x_2055_, v_type_2050_, v_fst_2013_, v___x_2056_, v_fst_2014_, v___y_2038_);
v___x_2058_ = lean_unsigned_to_nat(0u);
v___x_2059_ = l_Lean_Meta_Grind_pushNewFact(v___x_2057_, v___x_2058_, v___y_2039_, v___y_2040_, v___y_2041_, v___y_2042_, v___y_2043_, v___y_2044_, v___y_2045_, v___y_2046_, v___y_2047_, v___y_2048_);
if (lean_obj_tag(v___x_2059_) == 0)
{
lean_object* v___x_2060_; 
lean_dec_ref_known(v___x_2059_, 1);
v___x_2060_ = lean_nat_add(v_i_2018_, v_step_2032_);
lean_dec(v_i_2018_);
v_b_2017_ = v___x_2036_;
v_i_2018_ = v___x_2060_;
goto _start;
}
else
{
lean_dec(v_i_2018_);
lean_dec_ref(v_fst_2014_);
lean_dec_ref(v_fst_2013_);
lean_dec(v_snd_2012_);
lean_dec_ref(v_a_2011_);
return v___x_2059_;
}
}
v___jp_2062_:
{
lean_object* v_toCold_2064_; lean_object* v_options_2065_; uint8_t v_hasTrace_2066_; 
v_toCold_2064_ = lean_ctor_get(v___y_2028_, 0);
v_options_2065_ = lean_ctor_get(v_toCold_2064_, 2);
v_hasTrace_2066_ = lean_ctor_get_uint8(v_options_2065_, sizeof(void*)*1);
if (v_hasTrace_2066_ == 0)
{
v___y_2038_ = v___y_2063_;
v___y_2039_ = v___y_2020_;
v___y_2040_ = v___y_2021_;
v___y_2041_ = v___y_2022_;
v___y_2042_ = v___y_2023_;
v___y_2043_ = v___y_2024_;
v___y_2044_ = v___y_2025_;
v___y_2045_ = v___y_2026_;
v___y_2046_ = v___y_2027_;
v___y_2047_ = v___y_2028_;
v___y_2048_ = v___y_2029_;
goto v___jp_2037_;
}
else
{
lean_object* v_inheritedTraceOptions_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; uint8_t v___x_2070_; 
v_inheritedTraceOptions_2067_ = lean_ctor_get(v_toCold_2064_, 11);
v___x_2068_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__5));
v___x_2069_ = lean_obj_once(&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__8, &l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__8_once, _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__8);
v___x_2070_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2067_, v_options_2065_, v___x_2069_);
if (v___x_2070_ == 0)
{
v___y_2038_ = v___y_2063_;
v___y_2039_ = v___y_2020_;
v___y_2040_ = v___y_2021_;
v___y_2041_ = v___y_2022_;
v___y_2042_ = v___y_2023_;
v___y_2043_ = v___y_2024_;
v___y_2044_ = v___y_2025_;
v___y_2045_ = v___y_2026_;
v___y_2046_ = v___y_2027_;
v___y_2047_ = v___y_2028_;
v___y_2048_ = v___y_2029_;
goto v___jp_2037_;
}
else
{
lean_object* v___x_2071_; 
v___x_2071_ = l_Lean_Meta_Grind_updateLastTag(v___y_2020_, v___y_2021_, v___y_2022_, v___y_2023_, v___y_2024_, v___y_2025_, v___y_2026_, v___y_2027_, v___y_2028_, v___y_2029_);
if (lean_obj_tag(v___x_2071_) == 0)
{
lean_object* v___x_2073_; uint8_t v_isShared_2074_; uint8_t v_isSharedCheck_2087_; 
v_isSharedCheck_2087_ = !lean_is_exclusive(v___x_2071_);
if (v_isSharedCheck_2087_ == 0)
{
lean_object* v_unused_2088_; 
v_unused_2088_ = lean_ctor_get(v___x_2071_, 0);
lean_dec(v_unused_2088_);
v___x_2073_ = v___x_2071_;
v_isShared_2074_ = v_isSharedCheck_2087_;
goto v_resetjp_2072_;
}
else
{
lean_dec(v___x_2071_);
v___x_2073_ = lean_box(0);
v_isShared_2074_ = v_isSharedCheck_2087_;
goto v_resetjp_2072_;
}
v_resetjp_2072_:
{
lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2078_; 
v___x_2075_ = lean_obj_once(&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__10, &l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__10_once, _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__10);
lean_inc(v_snd_2012_);
v___x_2076_ = l_Nat_reprFast(v_snd_2012_);
if (v_isShared_2074_ == 0)
{
lean_ctor_set_tag(v___x_2073_, 3);
lean_ctor_set(v___x_2073_, 0, v___x_2076_);
v___x_2078_ = v___x_2073_;
goto v_reusejp_2077_;
}
else
{
lean_object* v_reuseFailAlloc_2086_; 
v_reuseFailAlloc_2086_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2086_, 0, v___x_2076_);
v___x_2078_ = v_reuseFailAlloc_2086_;
goto v_reusejp_2077_;
}
v_reusejp_2077_:
{
lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; 
v___x_2079_ = l_Lean_MessageData_ofFormat(v___x_2078_);
v___x_2080_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2080_, 0, v___x_2075_);
lean_ctor_set(v___x_2080_, 1, v___x_2079_);
v___x_2081_ = lean_obj_once(&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__12, &l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__12_once, _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__12);
v___x_2082_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2082_, 0, v___x_2080_);
lean_ctor_set(v___x_2082_, 1, v___x_2081_);
lean_inc_ref(v___y_2063_);
v___x_2083_ = l_Lean_MessageData_ofExpr(v___y_2063_);
v___x_2084_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2084_, 0, v___x_2082_);
lean_ctor_set(v___x_2084_, 1, v___x_2083_);
v___x_2085_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg(v___x_2068_, v___x_2084_, v___y_2026_, v___y_2027_, v___y_2028_, v___y_2029_);
if (lean_obj_tag(v___x_2085_) == 0)
{
lean_dec_ref_known(v___x_2085_, 1);
v___y_2038_ = v___y_2063_;
v___y_2039_ = v___y_2020_;
v___y_2040_ = v___y_2021_;
v___y_2041_ = v___y_2022_;
v___y_2042_ = v___y_2023_;
v___y_2043_ = v___y_2024_;
v___y_2044_ = v___y_2025_;
v___y_2045_ = v___y_2026_;
v___y_2046_ = v___y_2027_;
v___y_2047_ = v___y_2028_;
v___y_2048_ = v___y_2029_;
goto v___jp_2037_;
}
else
{
lean_dec_ref(v___y_2063_);
lean_dec(v_i_2018_);
lean_dec_ref(v_fst_2014_);
lean_dec_ref(v_fst_2013_);
lean_dec(v_snd_2012_);
lean_dec_ref(v_a_2011_);
return v___x_2085_;
}
}
}
}
else
{
lean_dec_ref(v___y_2063_);
lean_dec(v_i_2018_);
lean_dec_ref(v_fst_2014_);
lean_dec_ref(v_fst_2013_);
lean_dec(v_snd_2012_);
lean_dec_ref(v_a_2011_);
return v___x_2071_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___boxed(lean_object** _args){
lean_object* v_a_2093_ = _args[0];
lean_object* v_snd_2094_ = _args[1];
lean_object* v_fst_2095_ = _args[2];
lean_object* v_fst_2096_ = _args[3];
lean_object* v___x_2097_ = _args[4];
lean_object* v_range_2098_ = _args[5];
lean_object* v_b_2099_ = _args[6];
lean_object* v_i_2100_ = _args[7];
lean_object* v___y_2101_ = _args[8];
lean_object* v___y_2102_ = _args[9];
lean_object* v___y_2103_ = _args[10];
lean_object* v___y_2104_ = _args[11];
lean_object* v___y_2105_ = _args[12];
lean_object* v___y_2106_ = _args[13];
lean_object* v___y_2107_ = _args[14];
lean_object* v___y_2108_ = _args[15];
lean_object* v___y_2109_ = _args[16];
lean_object* v___y_2110_ = _args[17];
lean_object* v___y_2111_ = _args[18];
lean_object* v___y_2112_ = _args[19];
_start:
{
lean_object* v_res_2113_; 
v_res_2113_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg(v_a_2093_, v_snd_2094_, v_fst_2095_, v_fst_2096_, v___x_2097_, v_range_2098_, v_b_2099_, v_i_2100_, v___y_2101_, v___y_2102_, v___y_2103_, v___y_2104_, v___y_2105_, v___y_2106_, v___y_2107_, v___y_2108_, v___y_2109_, v___y_2110_, v___y_2111_);
lean_dec(v___y_2111_);
lean_dec_ref(v___y_2110_);
lean_dec(v___y_2109_);
lean_dec_ref(v___y_2108_);
lean_dec(v___y_2107_);
lean_dec_ref(v___y_2106_);
lean_dec(v___y_2105_);
lean_dec_ref(v___y_2104_);
lean_dec(v___y_2103_);
lean_dec(v___y_2102_);
lean_dec_ref(v___y_2101_);
lean_dec_ref(v_range_2098_);
lean_dec_ref(v___x_2097_);
return v_res_2113_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars(lean_object* v_a_2114_, lean_object* v_a_2115_, lean_object* v_a_2116_, lean_object* v_a_2117_, lean_object* v_a_2118_, lean_object* v_a_2119_, lean_object* v_a_2120_, lean_object* v_a_2121_, lean_object* v_a_2122_, lean_object* v_a_2123_, lean_object* v_a_2124_){
_start:
{
lean_object* v___x_2126_; 
v___x_2126_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v_a_2114_, v_a_2115_, v_a_2116_, v_a_2117_, v_a_2118_, v_a_2119_, v_a_2120_, v_a_2121_, v_a_2122_, v_a_2123_, v_a_2124_);
if (lean_obj_tag(v___x_2126_) == 0)
{
lean_object* v_a_2127_; lean_object* v___x_2129_; uint8_t v_isShared_2130_; uint8_t v_isSharedCheck_2180_; 
v_a_2127_ = lean_ctor_get(v___x_2126_, 0);
v_isSharedCheck_2180_ = !lean_is_exclusive(v___x_2126_);
if (v_isSharedCheck_2180_ == 0)
{
v___x_2129_ = v___x_2126_;
v_isShared_2130_ = v_isSharedCheck_2180_;
goto v_resetjp_2128_;
}
else
{
lean_inc(v_a_2127_);
lean_dec(v___x_2126_);
v___x_2129_ = lean_box(0);
v_isShared_2130_ = v_isSharedCheck_2180_;
goto v_resetjp_2128_;
}
v_resetjp_2128_:
{
lean_object* v_powIdentityInst_x3f_2131_; 
v_powIdentityInst_x3f_2131_ = lean_ctor_get(v_a_2127_, 9);
if (lean_obj_tag(v_powIdentityInst_x3f_2131_) == 1)
{
lean_object* v_val_2132_; lean_object* v_snd_2133_; lean_object* v_fst_2134_; lean_object* v_fst_2135_; lean_object* v_snd_2136_; lean_object* v___x_2137_; 
lean_del_object(v___x_2129_);
v_val_2132_ = lean_ctor_get(v_powIdentityInst_x3f_2131_, 0);
v_snd_2133_ = lean_ctor_get(v_val_2132_, 1);
v_fst_2134_ = lean_ctor_get(v_val_2132_, 0);
lean_inc(v_fst_2134_);
v_fst_2135_ = lean_ctor_get(v_snd_2133_, 0);
lean_inc(v_fst_2135_);
v_snd_2136_ = lean_ctor_get(v_snd_2133_, 1);
lean_inc(v_snd_2136_);
v___x_2137_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRingState___redArg(v_a_2114_, v_a_2115_, v_a_2123_);
if (lean_obj_tag(v___x_2137_) == 0)
{
lean_object* v_a_2138_; lean_object* v_powIdentityVarCount_2139_; lean_object* v___x_2140_; 
v_a_2138_ = lean_ctor_get(v___x_2137_, 0);
lean_inc(v_a_2138_);
lean_dec_ref_known(v___x_2137_, 1);
v_powIdentityVarCount_2139_ = lean_ctor_get(v_a_2138_, 8);
lean_inc(v_powIdentityVarCount_2139_);
lean_dec(v_a_2138_);
v___x_2140_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRingState___redArg(v_a_2114_, v_a_2115_, v_a_2123_);
if (lean_obj_tag(v___x_2140_) == 0)
{
lean_object* v_a_2141_; lean_object* v___x_2143_; uint8_t v_isShared_2144_; uint8_t v_isSharedCheck_2159_; 
v_a_2141_ = lean_ctor_get(v___x_2140_, 0);
v_isSharedCheck_2159_ = !lean_is_exclusive(v___x_2140_);
if (v_isSharedCheck_2159_ == 0)
{
v___x_2143_ = v___x_2140_;
v_isShared_2144_ = v_isSharedCheck_2159_;
goto v_resetjp_2142_;
}
else
{
lean_inc(v_a_2141_);
lean_dec(v___x_2140_);
v___x_2143_ = lean_box(0);
v_isShared_2144_ = v_isSharedCheck_2159_;
goto v_resetjp_2142_;
}
v_resetjp_2142_:
{
lean_object* v_toRingState_2145_; lean_object* v_vars_2146_; lean_object* v_size_2147_; uint8_t v___x_2148_; 
v_toRingState_2145_ = lean_ctor_get(v_a_2141_, 0);
lean_inc_ref(v_toRingState_2145_);
lean_dec(v_a_2141_);
v_vars_2146_ = lean_ctor_get(v_toRingState_2145_, 0);
lean_inc_ref(v_vars_2146_);
lean_dec_ref(v_toRingState_2145_);
v_size_2147_ = lean_ctor_get(v_vars_2146_, 2);
v___x_2148_ = lean_nat_dec_le(v_size_2147_, v_powIdentityVarCount_2139_);
if (v___x_2148_ == 0)
{
lean_object* v___f_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; 
lean_del_object(v___x_2143_);
lean_inc_n(v_size_2147_, 2);
v___f_2149_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars___lam__0), 2, 1);
lean_closure_set(v___f_2149_, 0, v_size_2147_);
v___x_2150_ = lean_unsigned_to_nat(1u);
lean_inc(v_powIdentityVarCount_2139_);
v___x_2151_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2151_, 0, v_powIdentityVarCount_2139_);
lean_ctor_set(v___x_2151_, 1, v_size_2147_);
lean_ctor_set(v___x_2151_, 2, v___x_2150_);
v___x_2152_ = lean_box(0);
v___x_2153_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg(v_a_2127_, v_snd_2136_, v_fst_2135_, v_fst_2134_, v_vars_2146_, v___x_2151_, v___x_2152_, v_powIdentityVarCount_2139_, v_a_2114_, v_a_2115_, v_a_2116_, v_a_2117_, v_a_2118_, v_a_2119_, v_a_2120_, v_a_2121_, v_a_2122_, v_a_2123_, v_a_2124_);
lean_dec_ref_known(v___x_2151_, 3);
lean_dec_ref(v_vars_2146_);
if (lean_obj_tag(v___x_2153_) == 0)
{
lean_object* v___x_2154_; 
lean_dec_ref_known(v___x_2153_, 1);
v___x_2154_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRingState___redArg(v___f_2149_, v_a_2114_, v_a_2115_);
return v___x_2154_;
}
else
{
lean_dec_ref(v___f_2149_);
return v___x_2153_;
}
}
else
{
lean_object* v___x_2155_; lean_object* v___x_2157_; 
lean_dec_ref(v_vars_2146_);
lean_dec(v_powIdentityVarCount_2139_);
lean_dec(v_snd_2136_);
lean_dec(v_fst_2135_);
lean_dec(v_fst_2134_);
lean_dec(v_a_2127_);
v___x_2155_ = lean_box(0);
if (v_isShared_2144_ == 0)
{
lean_ctor_set(v___x_2143_, 0, v___x_2155_);
v___x_2157_ = v___x_2143_;
goto v_reusejp_2156_;
}
else
{
lean_object* v_reuseFailAlloc_2158_; 
v_reuseFailAlloc_2158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2158_, 0, v___x_2155_);
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
lean_dec(v_powIdentityVarCount_2139_);
lean_dec(v_snd_2136_);
lean_dec(v_fst_2135_);
lean_dec(v_fst_2134_);
lean_dec(v_a_2127_);
v_a_2160_ = lean_ctor_get(v___x_2140_, 0);
v_isSharedCheck_2167_ = !lean_is_exclusive(v___x_2140_);
if (v_isSharedCheck_2167_ == 0)
{
v___x_2162_ = v___x_2140_;
v_isShared_2163_ = v_isSharedCheck_2167_;
goto v_resetjp_2161_;
}
else
{
lean_inc(v_a_2160_);
lean_dec(v___x_2140_);
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
else
{
lean_object* v_a_2168_; lean_object* v___x_2170_; uint8_t v_isShared_2171_; uint8_t v_isSharedCheck_2175_; 
lean_dec(v_snd_2136_);
lean_dec(v_fst_2135_);
lean_dec(v_fst_2134_);
lean_dec(v_a_2127_);
v_a_2168_ = lean_ctor_get(v___x_2137_, 0);
v_isSharedCheck_2175_ = !lean_is_exclusive(v___x_2137_);
if (v_isSharedCheck_2175_ == 0)
{
v___x_2170_ = v___x_2137_;
v_isShared_2171_ = v_isSharedCheck_2175_;
goto v_resetjp_2169_;
}
else
{
lean_inc(v_a_2168_);
lean_dec(v___x_2137_);
v___x_2170_ = lean_box(0);
v_isShared_2171_ = v_isSharedCheck_2175_;
goto v_resetjp_2169_;
}
v_resetjp_2169_:
{
lean_object* v___x_2173_; 
if (v_isShared_2171_ == 0)
{
v___x_2173_ = v___x_2170_;
goto v_reusejp_2172_;
}
else
{
lean_object* v_reuseFailAlloc_2174_; 
v_reuseFailAlloc_2174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2174_, 0, v_a_2168_);
v___x_2173_ = v_reuseFailAlloc_2174_;
goto v_reusejp_2172_;
}
v_reusejp_2172_:
{
return v___x_2173_;
}
}
}
}
else
{
lean_object* v___x_2176_; lean_object* v___x_2178_; 
lean_dec(v_a_2127_);
v___x_2176_ = lean_box(0);
if (v_isShared_2130_ == 0)
{
lean_ctor_set(v___x_2129_, 0, v___x_2176_);
v___x_2178_ = v___x_2129_;
goto v_reusejp_2177_;
}
else
{
lean_object* v_reuseFailAlloc_2179_; 
v_reuseFailAlloc_2179_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2179_, 0, v___x_2176_);
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
lean_object* v_a_2181_; lean_object* v___x_2183_; uint8_t v_isShared_2184_; uint8_t v_isSharedCheck_2188_; 
v_a_2181_ = lean_ctor_get(v___x_2126_, 0);
v_isSharedCheck_2188_ = !lean_is_exclusive(v___x_2126_);
if (v_isSharedCheck_2188_ == 0)
{
v___x_2183_ = v___x_2126_;
v_isShared_2184_ = v_isSharedCheck_2188_;
goto v_resetjp_2182_;
}
else
{
lean_inc(v_a_2181_);
lean_dec(v___x_2126_);
v___x_2183_ = lean_box(0);
v_isShared_2184_ = v_isSharedCheck_2188_;
goto v_resetjp_2182_;
}
v_resetjp_2182_:
{
lean_object* v___x_2186_; 
if (v_isShared_2184_ == 0)
{
v___x_2186_ = v___x_2183_;
goto v_reusejp_2185_;
}
else
{
lean_object* v_reuseFailAlloc_2187_; 
v_reuseFailAlloc_2187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2187_, 0, v_a_2181_);
v___x_2186_ = v_reuseFailAlloc_2187_;
goto v_reusejp_2185_;
}
v_reusejp_2185_:
{
return v___x_2186_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars___boxed(lean_object* v_a_2189_, lean_object* v_a_2190_, lean_object* v_a_2191_, lean_object* v_a_2192_, lean_object* v_a_2193_, lean_object* v_a_2194_, lean_object* v_a_2195_, lean_object* v_a_2196_, lean_object* v_a_2197_, lean_object* v_a_2198_, lean_object* v_a_2199_, lean_object* v_a_2200_){
_start:
{
lean_object* v_res_2201_; 
v_res_2201_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars(v_a_2189_, v_a_2190_, v_a_2191_, v_a_2192_, v_a_2193_, v_a_2194_, v_a_2195_, v_a_2196_, v_a_2197_, v_a_2198_, v_a_2199_);
lean_dec(v_a_2199_);
lean_dec_ref(v_a_2198_);
lean_dec(v_a_2197_);
lean_dec_ref(v_a_2196_);
lean_dec(v_a_2195_);
lean_dec_ref(v_a_2194_);
lean_dec(v_a_2193_);
lean_dec_ref(v_a_2192_);
lean_dec(v_a_2191_);
lean_dec(v_a_2190_);
lean_dec_ref(v_a_2189_);
return v_res_2201_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0(lean_object* v_cls_2202_, lean_object* v_msg_2203_, lean_object* v___y_2204_, lean_object* v___y_2205_, lean_object* v___y_2206_, lean_object* v___y_2207_, lean_object* v___y_2208_, lean_object* v___y_2209_, lean_object* v___y_2210_, lean_object* v___y_2211_, lean_object* v___y_2212_, lean_object* v___y_2213_, lean_object* v___y_2214_){
_start:
{
lean_object* v___x_2216_; 
v___x_2216_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg(v_cls_2202_, v_msg_2203_, v___y_2211_, v___y_2212_, v___y_2213_, v___y_2214_);
return v___x_2216_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___boxed(lean_object* v_cls_2217_, lean_object* v_msg_2218_, lean_object* v___y_2219_, lean_object* v___y_2220_, lean_object* v___y_2221_, lean_object* v___y_2222_, lean_object* v___y_2223_, lean_object* v___y_2224_, lean_object* v___y_2225_, lean_object* v___y_2226_, lean_object* v___y_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_){
_start:
{
lean_object* v_res_2231_; 
v_res_2231_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0(v_cls_2217_, v_msg_2218_, v___y_2219_, v___y_2220_, v___y_2221_, v___y_2222_, v___y_2223_, v___y_2224_, v___y_2225_, v___y_2226_, v___y_2227_, v___y_2228_, v___y_2229_);
lean_dec(v___y_2229_);
lean_dec_ref(v___y_2228_);
lean_dec(v___y_2227_);
lean_dec_ref(v___y_2226_);
lean_dec(v___y_2225_);
lean_dec_ref(v___y_2224_);
lean_dec(v___y_2223_);
lean_dec_ref(v___y_2222_);
lean_dec(v___y_2221_);
lean_dec(v___y_2220_);
lean_dec_ref(v___y_2219_);
return v_res_2231_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1(lean_object* v_a_2232_, lean_object* v_snd_2233_, lean_object* v_fst_2234_, lean_object* v_fst_2235_, lean_object* v___x_2236_, lean_object* v_range_2237_, lean_object* v_b_2238_, lean_object* v_i_2239_, lean_object* v_hs_2240_, lean_object* v_hl_2241_, lean_object* v___y_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_){
_start:
{
lean_object* v___x_2254_; 
v___x_2254_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg(v_a_2232_, v_snd_2233_, v_fst_2234_, v_fst_2235_, v___x_2236_, v_range_2237_, v_b_2238_, v_i_2239_, v___y_2242_, v___y_2243_, v___y_2244_, v___y_2245_, v___y_2246_, v___y_2247_, v___y_2248_, v___y_2249_, v___y_2250_, v___y_2251_, v___y_2252_);
return v___x_2254_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___boxed(lean_object** _args){
lean_object* v_a_2255_ = _args[0];
lean_object* v_snd_2256_ = _args[1];
lean_object* v_fst_2257_ = _args[2];
lean_object* v_fst_2258_ = _args[3];
lean_object* v___x_2259_ = _args[4];
lean_object* v_range_2260_ = _args[5];
lean_object* v_b_2261_ = _args[6];
lean_object* v_i_2262_ = _args[7];
lean_object* v_hs_2263_ = _args[8];
lean_object* v_hl_2264_ = _args[9];
lean_object* v___y_2265_ = _args[10];
lean_object* v___y_2266_ = _args[11];
lean_object* v___y_2267_ = _args[12];
lean_object* v___y_2268_ = _args[13];
lean_object* v___y_2269_ = _args[14];
lean_object* v___y_2270_ = _args[15];
lean_object* v___y_2271_ = _args[16];
lean_object* v___y_2272_ = _args[17];
lean_object* v___y_2273_ = _args[18];
lean_object* v___y_2274_ = _args[19];
lean_object* v___y_2275_ = _args[20];
lean_object* v___y_2276_ = _args[21];
_start:
{
lean_object* v_res_2277_; 
v_res_2277_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1(v_a_2255_, v_snd_2256_, v_fst_2257_, v_fst_2258_, v___x_2259_, v_range_2260_, v_b_2261_, v_i_2262_, v_hs_2263_, v_hl_2264_, v___y_2265_, v___y_2266_, v___y_2267_, v___y_2268_, v___y_2269_, v___y_2270_, v___y_2271_, v___y_2272_, v___y_2273_, v___y_2274_, v___y_2275_);
lean_dec(v___y_2275_);
lean_dec_ref(v___y_2274_);
lean_dec(v___y_2273_);
lean_dec_ref(v___y_2272_);
lean_dec(v___y_2271_);
lean_dec_ref(v___y_2270_);
lean_dec(v___y_2269_);
lean_dec_ref(v___y_2268_);
lean_dec(v___y_2267_);
lean_dec(v___y_2266_);
lean_dec_ref(v___y_2265_);
lean_dec_ref(v_range_2260_);
lean_dec_ref(v___x_2259_);
return v_res_2277_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_pushNatCastFact___redArg___closed__0(void){
_start:
{
lean_object* v___x_2278_; lean_object* v___x_2279_; 
v___x_2278_ = lean_unsigned_to_nat(0u);
v___x_2279_ = l_Lean_Level_ofNat(v___x_2278_);
return v___x_2279_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_pushNatCastFact___redArg___closed__1(void){
_start:
{
lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; 
v___x_2280_ = lean_box(0);
v___x_2281_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_pushNatCastFact___redArg___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_pushNatCastFact___redArg___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_pushNatCastFact___redArg___closed__0);
v___x_2282_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2282_, 0, v___x_2281_);
lean_ctor_set(v___x_2282_, 1, v___x_2280_);
return v___x_2282_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_pushNatCastFact___redArg___closed__2(void){
_start:
{
lean_object* v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; 
v___x_2283_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_pushNatCastFact___redArg___closed__1, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_pushNatCastFact___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_pushNatCastFact___redArg___closed__1);
v___x_2284_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__5));
v___x_2285_ = l_Lean_mkConst(v___x_2284_, v___x_2283_);
return v___x_2285_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_pushNatCastFact___redArg___closed__5(void){
_start:
{
lean_object* v___x_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; 
v___x_2289_ = lean_box(0);
v___x_2290_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_pushNatCastFact___redArg___closed__4));
v___x_2291_ = l_Lean_mkConst(v___x_2290_, v___x_2289_);
return v___x_2291_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_pushNatCastFact___redArg(lean_object* v_ring_2298_, lean_object* v_intCastFn_2299_, lean_object* v_e_2300_, lean_object* v_a_2301_, lean_object* v_a_2302_, lean_object* v_a_2303_, lean_object* v_a_2304_, lean_object* v_a_2305_, lean_object* v_a_2306_, lean_object* v_a_2307_){
_start:
{
lean_object* v___x_2312_; uint8_t v___x_2313_; 
v___x_2312_ = l_Lean_Expr_cleanupAnnotations(v_e_2300_);
v___x_2313_ = l_Lean_Expr_isApp(v___x_2312_);
if (v___x_2313_ == 0)
{
lean_dec_ref(v___x_2312_);
lean_dec_ref(v_e_2300_);
lean_dec_ref(v_intCastFn_2299_);
lean_dec_ref(v_ring_2298_);
goto v___jp_2309_;
}
else
{
lean_object* v___x_2314_; uint8_t v___x_2315_; 
v___x_2314_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2312_);
v___x_2315_ = l_Lean_Expr_isApp(v___x_2314_);
if (v___x_2315_ == 0)
{
lean_dec_ref(v___x_2314_);
lean_dec_ref(v___x_2312_);
lean_dec_ref(v_e_2300_);
lean_dec_ref(v_intCastFn_2299_);
lean_dec_ref(v_ring_2298_);
goto v___jp_2309_;
}
else
{
lean_object* v___x_2316_; uint8_t v___x_2317_; 
v___x_2316_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2314_);
lean_dec_ref(v___x_2314_);
v___x_2317_ = l_Lean_Expr_isApp(v___x_2316_);
if (v___x_2317_ == 0)
{
lean_dec_ref(v___x_2316_);
lean_dec_ref(v___x_2312_);
lean_dec_ref(v_e_2300_);
lean_dec_ref(v_intCastFn_2299_);
lean_dec_ref(v_ring_2298_);
goto v___jp_2309_;
}
else
{
lean_object* v___x_2318_; lean_object* v___x_2319_; uint8_t v___x_2320_; 
v___x_2318_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2316_);
lean_dec_ref(v___x_2316_);
v___x_2319_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__5));
v___x_2320_ = l_Lean_Expr_isConstOf(v___x_2318_, v___x_2319_);
lean_dec_ref(v___x_2318_);
if (v___x_2320_ == 0)
{
lean_dec_ref(v___x_2312_);
lean_dec_ref(v_e_2300_);
lean_dec_ref(v_intCastFn_2299_);
lean_dec_ref(v_ring_2298_);
goto v___jp_2309_;
}
else
{
lean_object* v_arg_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v_natCastInt_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; 
v_arg_2321_ = lean_ctor_get(v___x_2312_, 1);
lean_inc_ref_n(v_arg_2321_, 2);
lean_dec_ref(v___x_2312_);
v___x_2322_ = lean_box(0);
v___x_2323_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_pushNatCastFact___redArg___closed__2, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_pushNatCastFact___redArg___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_pushNatCastFact___redArg___closed__2);
v___x_2324_ = l_Lean_Int_mkType;
v___x_2325_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_pushNatCastFact___redArg___closed__5, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_pushNatCastFact___redArg___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_pushNatCastFact___redArg___closed__5);
v_natCastInt_2326_ = l_Lean_mkApp3(v___x_2323_, v___x_2324_, v___x_2325_, v_arg_2321_);
v___x_2327_ = l_Lean_Expr_app___override(v_intCastFn_2299_, v_natCastInt_2326_);
lean_inc_ref(v_e_2300_);
v___x_2328_ = l_Lean_Meta_mkEq(v___x_2327_, v_e_2300_, v_a_2304_, v_a_2305_, v_a_2306_, v_a_2307_);
if (lean_obj_tag(v___x_2328_) == 0)
{
lean_object* v_a_2329_; lean_object* v___x_2330_; 
v_a_2329_ = lean_ctor_get(v___x_2328_, 0);
lean_inc(v_a_2329_);
lean_dec_ref_known(v___x_2328_, 1);
v___x_2330_ = l_Lean_Meta_Sym_canon(v_a_2329_, v_a_2302_, v_a_2303_, v_a_2304_, v_a_2305_, v_a_2306_, v_a_2307_);
if (lean_obj_tag(v___x_2330_) == 0)
{
lean_object* v_a_2331_; lean_object* v___x_2332_; 
v_a_2331_ = lean_ctor_get(v___x_2330_, 0);
lean_inc(v_a_2331_);
lean_dec_ref_known(v___x_2330_, 1);
v___x_2332_ = l_Lean_Meta_Sym_shareCommon(v_a_2331_, v_a_2302_, v_a_2303_, v_a_2304_, v_a_2305_, v_a_2306_, v_a_2307_);
if (lean_obj_tag(v___x_2332_) == 0)
{
lean_object* v_a_2333_; lean_object* v_type_2334_; lean_object* v_u_2335_; lean_object* v_ringInst_2336_; lean_object* v___x_2337_; lean_object* v___x_2338_; lean_object* v___x_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; 
v_a_2333_ = lean_ctor_get(v___x_2332_, 0);
lean_inc(v_a_2333_);
lean_dec_ref_known(v___x_2332_, 1);
v_type_2334_ = lean_ctor_get(v_ring_2298_, 1);
lean_inc_ref(v_type_2334_);
v_u_2335_ = lean_ctor_get(v_ring_2298_, 2);
lean_inc(v_u_2335_);
v_ringInst_2336_ = lean_ctor_get(v_ring_2298_, 3);
lean_inc_ref(v_ringInst_2336_);
lean_dec_ref(v_ring_2298_);
v___x_2337_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_pushNatCastFact___redArg___closed__7));
v___x_2338_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2338_, 0, v_u_2335_);
lean_ctor_set(v___x_2338_, 1, v___x_2322_);
v___x_2339_ = l_Lean_mkConst(v___x_2337_, v___x_2338_);
v___x_2340_ = l_Lean_mkApp3(v___x_2339_, v_type_2334_, v_ringInst_2336_, v_arg_2321_);
v___x_2341_ = l_Lean_Meta_Grind_getGeneration___redArg(v_e_2300_, v_a_2301_);
lean_dec_ref(v_e_2300_);
if (lean_obj_tag(v___x_2341_) == 0)
{
lean_object* v_a_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; 
v_a_2342_ = lean_ctor_get(v___x_2341_, 0);
lean_inc(v_a_2342_);
lean_dec_ref_known(v___x_2341_, 1);
lean_inc(v_a_2333_);
v___x_2343_ = l_Lean_Meta_mkExpectedPropHint(v___x_2340_, v_a_2333_);
v___x_2344_ = l_Lean_Meta_Grind_pushNewFactCore___redArg(v_a_2333_, v___x_2343_, v_a_2342_, v_a_2301_);
return v___x_2344_;
}
else
{
lean_object* v_a_2345_; lean_object* v___x_2347_; uint8_t v_isShared_2348_; uint8_t v_isSharedCheck_2352_; 
lean_dec_ref(v___x_2340_);
lean_dec(v_a_2333_);
v_a_2345_ = lean_ctor_get(v___x_2341_, 0);
v_isSharedCheck_2352_ = !lean_is_exclusive(v___x_2341_);
if (v_isSharedCheck_2352_ == 0)
{
v___x_2347_ = v___x_2341_;
v_isShared_2348_ = v_isSharedCheck_2352_;
goto v_resetjp_2346_;
}
else
{
lean_inc(v_a_2345_);
lean_dec(v___x_2341_);
v___x_2347_ = lean_box(0);
v_isShared_2348_ = v_isSharedCheck_2352_;
goto v_resetjp_2346_;
}
v_resetjp_2346_:
{
lean_object* v___x_2350_; 
if (v_isShared_2348_ == 0)
{
v___x_2350_ = v___x_2347_;
goto v_reusejp_2349_;
}
else
{
lean_object* v_reuseFailAlloc_2351_; 
v_reuseFailAlloc_2351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2351_, 0, v_a_2345_);
v___x_2350_ = v_reuseFailAlloc_2351_;
goto v_reusejp_2349_;
}
v_reusejp_2349_:
{
return v___x_2350_;
}
}
}
}
else
{
lean_object* v_a_2353_; lean_object* v___x_2355_; uint8_t v_isShared_2356_; uint8_t v_isSharedCheck_2360_; 
lean_dec_ref(v_arg_2321_);
lean_dec_ref(v_e_2300_);
lean_dec_ref(v_ring_2298_);
v_a_2353_ = lean_ctor_get(v___x_2332_, 0);
v_isSharedCheck_2360_ = !lean_is_exclusive(v___x_2332_);
if (v_isSharedCheck_2360_ == 0)
{
v___x_2355_ = v___x_2332_;
v_isShared_2356_ = v_isSharedCheck_2360_;
goto v_resetjp_2354_;
}
else
{
lean_inc(v_a_2353_);
lean_dec(v___x_2332_);
v___x_2355_ = lean_box(0);
v_isShared_2356_ = v_isSharedCheck_2360_;
goto v_resetjp_2354_;
}
v_resetjp_2354_:
{
lean_object* v___x_2358_; 
if (v_isShared_2356_ == 0)
{
v___x_2358_ = v___x_2355_;
goto v_reusejp_2357_;
}
else
{
lean_object* v_reuseFailAlloc_2359_; 
v_reuseFailAlloc_2359_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2359_, 0, v_a_2353_);
v___x_2358_ = v_reuseFailAlloc_2359_;
goto v_reusejp_2357_;
}
v_reusejp_2357_:
{
return v___x_2358_;
}
}
}
}
else
{
lean_object* v_a_2361_; lean_object* v___x_2363_; uint8_t v_isShared_2364_; uint8_t v_isSharedCheck_2368_; 
lean_dec_ref(v_arg_2321_);
lean_dec_ref(v_e_2300_);
lean_dec_ref(v_ring_2298_);
v_a_2361_ = lean_ctor_get(v___x_2330_, 0);
v_isSharedCheck_2368_ = !lean_is_exclusive(v___x_2330_);
if (v_isSharedCheck_2368_ == 0)
{
v___x_2363_ = v___x_2330_;
v_isShared_2364_ = v_isSharedCheck_2368_;
goto v_resetjp_2362_;
}
else
{
lean_inc(v_a_2361_);
lean_dec(v___x_2330_);
v___x_2363_ = lean_box(0);
v_isShared_2364_ = v_isSharedCheck_2368_;
goto v_resetjp_2362_;
}
v_resetjp_2362_:
{
lean_object* v___x_2366_; 
if (v_isShared_2364_ == 0)
{
v___x_2366_ = v___x_2363_;
goto v_reusejp_2365_;
}
else
{
lean_object* v_reuseFailAlloc_2367_; 
v_reuseFailAlloc_2367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2367_, 0, v_a_2361_);
v___x_2366_ = v_reuseFailAlloc_2367_;
goto v_reusejp_2365_;
}
v_reusejp_2365_:
{
return v___x_2366_;
}
}
}
}
else
{
lean_object* v_a_2369_; lean_object* v___x_2371_; uint8_t v_isShared_2372_; uint8_t v_isSharedCheck_2376_; 
lean_dec_ref(v_arg_2321_);
lean_dec_ref(v_e_2300_);
lean_dec_ref(v_ring_2298_);
v_a_2369_ = lean_ctor_get(v___x_2328_, 0);
v_isSharedCheck_2376_ = !lean_is_exclusive(v___x_2328_);
if (v_isSharedCheck_2376_ == 0)
{
v___x_2371_ = v___x_2328_;
v_isShared_2372_ = v_isSharedCheck_2376_;
goto v_resetjp_2370_;
}
else
{
lean_inc(v_a_2369_);
lean_dec(v___x_2328_);
v___x_2371_ = lean_box(0);
v_isShared_2372_ = v_isSharedCheck_2376_;
goto v_resetjp_2370_;
}
v_resetjp_2370_:
{
lean_object* v___x_2374_; 
if (v_isShared_2372_ == 0)
{
v___x_2374_ = v___x_2371_;
goto v_reusejp_2373_;
}
else
{
lean_object* v_reuseFailAlloc_2375_; 
v_reuseFailAlloc_2375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2375_, 0, v_a_2369_);
v___x_2374_ = v_reuseFailAlloc_2375_;
goto v_reusejp_2373_;
}
v_reusejp_2373_:
{
return v___x_2374_;
}
}
}
}
}
}
}
v___jp_2309_:
{
lean_object* v___x_2310_; lean_object* v___x_2311_; 
v___x_2310_ = lean_box(0);
v___x_2311_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2311_, 0, v___x_2310_);
return v___x_2311_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_pushNatCastFact___redArg___boxed(lean_object* v_ring_2377_, lean_object* v_intCastFn_2378_, lean_object* v_e_2379_, lean_object* v_a_2380_, lean_object* v_a_2381_, lean_object* v_a_2382_, lean_object* v_a_2383_, lean_object* v_a_2384_, lean_object* v_a_2385_, lean_object* v_a_2386_, lean_object* v_a_2387_){
_start:
{
lean_object* v_res_2388_; 
v_res_2388_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_pushNatCastFact___redArg(v_ring_2377_, v_intCastFn_2378_, v_e_2379_, v_a_2380_, v_a_2381_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_);
lean_dec(v_a_2386_);
lean_dec_ref(v_a_2385_);
lean_dec(v_a_2384_);
lean_dec_ref(v_a_2383_);
lean_dec(v_a_2382_);
lean_dec_ref(v_a_2381_);
lean_dec(v_a_2380_);
return v_res_2388_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_pushNatCastFact(lean_object* v_ring_2389_, lean_object* v_intCastFn_2390_, lean_object* v_e_2391_, lean_object* v_a_2392_, lean_object* v_a_2393_, lean_object* v_a_2394_, lean_object* v_a_2395_, lean_object* v_a_2396_, lean_object* v_a_2397_, lean_object* v_a_2398_, lean_object* v_a_2399_, lean_object* v_a_2400_, lean_object* v_a_2401_){
_start:
{
lean_object* v___x_2403_; 
v___x_2403_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_pushNatCastFact___redArg(v_ring_2389_, v_intCastFn_2390_, v_e_2391_, v_a_2392_, v_a_2396_, v_a_2397_, v_a_2398_, v_a_2399_, v_a_2400_, v_a_2401_);
return v___x_2403_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_pushNatCastFact___boxed(lean_object* v_ring_2404_, lean_object* v_intCastFn_2405_, lean_object* v_e_2406_, lean_object* v_a_2407_, lean_object* v_a_2408_, lean_object* v_a_2409_, lean_object* v_a_2410_, lean_object* v_a_2411_, lean_object* v_a_2412_, lean_object* v_a_2413_, lean_object* v_a_2414_, lean_object* v_a_2415_, lean_object* v_a_2416_, lean_object* v_a_2417_){
_start:
{
lean_object* v_res_2418_; 
v_res_2418_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_pushNatCastFact(v_ring_2404_, v_intCastFn_2405_, v_e_2406_, v_a_2407_, v_a_2408_, v_a_2409_, v_a_2410_, v_a_2411_, v_a_2412_, v_a_2413_, v_a_2414_, v_a_2415_, v_a_2416_);
lean_dec(v_a_2416_);
lean_dec_ref(v_a_2415_);
lean_dec(v_a_2414_);
lean_dec_ref(v_a_2413_);
lean_dec(v_a_2412_);
lean_dec_ref(v_a_2411_);
lean_dec(v_a_2410_);
lean_dec_ref(v_a_2409_);
lean_dec(v_a_2408_);
lean_dec(v_a_2407_);
return v_res_2418_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___redArg___lam__0(lean_object* v_e_2419_, lean_object* v_s_2420_){
_start:
{
lean_object* v_vars_2421_; lean_object* v_varMap_2422_; lean_object* v_denote_2423_; lean_object* v_natCastSet_2424_; lean_object* v_natCasts_2425_; uint8_t v_hasIntCast_2426_; lean_object* v___x_2428_; uint8_t v_isShared_2429_; uint8_t v_isSharedCheck_2434_; 
v_vars_2421_ = lean_ctor_get(v_s_2420_, 0);
v_varMap_2422_ = lean_ctor_get(v_s_2420_, 1);
v_denote_2423_ = lean_ctor_get(v_s_2420_, 2);
v_natCastSet_2424_ = lean_ctor_get(v_s_2420_, 3);
v_natCasts_2425_ = lean_ctor_get(v_s_2420_, 4);
v_hasIntCast_2426_ = lean_ctor_get_uint8(v_s_2420_, sizeof(void*)*5);
v_isSharedCheck_2434_ = !lean_is_exclusive(v_s_2420_);
if (v_isSharedCheck_2434_ == 0)
{
v___x_2428_ = v_s_2420_;
v_isShared_2429_ = v_isSharedCheck_2434_;
goto v_resetjp_2427_;
}
else
{
lean_inc(v_natCasts_2425_);
lean_inc(v_natCastSet_2424_);
lean_inc(v_denote_2423_);
lean_inc(v_varMap_2422_);
lean_inc(v_vars_2421_);
lean_dec(v_s_2420_);
v___x_2428_ = lean_box(0);
v_isShared_2429_ = v_isSharedCheck_2434_;
goto v_resetjp_2427_;
}
v_resetjp_2427_:
{
lean_object* v___x_2430_; lean_object* v___x_2432_; 
v___x_2430_ = l_Lean_PersistentArray_push___redArg(v_natCasts_2425_, v_e_2419_);
if (v_isShared_2429_ == 0)
{
lean_ctor_set(v___x_2428_, 4, v___x_2430_);
v___x_2432_ = v___x_2428_;
goto v_reusejp_2431_;
}
else
{
lean_object* v_reuseFailAlloc_2433_; 
v_reuseFailAlloc_2433_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_2433_, 0, v_vars_2421_);
lean_ctor_set(v_reuseFailAlloc_2433_, 1, v_varMap_2422_);
lean_ctor_set(v_reuseFailAlloc_2433_, 2, v_denote_2423_);
lean_ctor_set(v_reuseFailAlloc_2433_, 3, v_natCastSet_2424_);
lean_ctor_set(v_reuseFailAlloc_2433_, 4, v___x_2430_);
lean_ctor_set_uint8(v_reuseFailAlloc_2433_, sizeof(void*)*5, v_hasIntCast_2426_);
v___x_2432_ = v_reuseFailAlloc_2433_;
goto v_reusejp_2431_;
}
v_reusejp_2431_:
{
return v___x_2432_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___redArg___lam__1(lean_object* v___f_2435_, lean_object* v___f_2436_, lean_object* v_e_2437_, lean_object* v_s_2438_){
_start:
{
lean_object* v_vars_2439_; lean_object* v_varMap_2440_; lean_object* v_denote_2441_; lean_object* v_natCastSet_2442_; lean_object* v_natCasts_2443_; uint8_t v_hasIntCast_2444_; lean_object* v___x_2446_; uint8_t v_isShared_2447_; uint8_t v_isSharedCheck_2453_; 
v_vars_2439_ = lean_ctor_get(v_s_2438_, 0);
v_varMap_2440_ = lean_ctor_get(v_s_2438_, 1);
v_denote_2441_ = lean_ctor_get(v_s_2438_, 2);
v_natCastSet_2442_ = lean_ctor_get(v_s_2438_, 3);
v_natCasts_2443_ = lean_ctor_get(v_s_2438_, 4);
v_hasIntCast_2444_ = lean_ctor_get_uint8(v_s_2438_, sizeof(void*)*5);
v_isSharedCheck_2453_ = !lean_is_exclusive(v_s_2438_);
if (v_isSharedCheck_2453_ == 0)
{
v___x_2446_ = v_s_2438_;
v_isShared_2447_ = v_isSharedCheck_2453_;
goto v_resetjp_2445_;
}
else
{
lean_inc(v_natCasts_2443_);
lean_inc(v_natCastSet_2442_);
lean_inc(v_denote_2441_);
lean_inc(v_varMap_2440_);
lean_inc(v_vars_2439_);
lean_dec(v_s_2438_);
v___x_2446_ = lean_box(0);
v_isShared_2447_ = v_isSharedCheck_2453_;
goto v_resetjp_2445_;
}
v_resetjp_2445_:
{
lean_object* v___x_2448_; lean_object* v___x_2449_; lean_object* v___x_2451_; 
v___x_2448_ = lean_box(0);
v___x_2449_ = l_Lean_PersistentHashMap_insert___redArg(v___f_2435_, v___f_2436_, v_natCastSet_2442_, v_e_2437_, v___x_2448_);
if (v_isShared_2447_ == 0)
{
lean_ctor_set(v___x_2446_, 3, v___x_2449_);
v___x_2451_ = v___x_2446_;
goto v_reusejp_2450_;
}
else
{
lean_object* v_reuseFailAlloc_2452_; 
v_reuseFailAlloc_2452_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_2452_, 0, v_vars_2439_);
lean_ctor_set(v_reuseFailAlloc_2452_, 1, v_varMap_2440_);
lean_ctor_set(v_reuseFailAlloc_2452_, 2, v_denote_2441_);
lean_ctor_set(v_reuseFailAlloc_2452_, 3, v___x_2449_);
lean_ctor_set(v_reuseFailAlloc_2452_, 4, v_natCasts_2443_);
lean_ctor_set_uint8(v_reuseFailAlloc_2452_, sizeof(void*)*5, v_hasIntCast_2444_);
v___x_2451_ = v_reuseFailAlloc_2452_;
goto v_reusejp_2450_;
}
v_reusejp_2450_:
{
return v___x_2451_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___redArg___lam__2(lean_object* v_____do__lift_2454_, lean_object* v_e_2455_, lean_object* v_inst_2456_, lean_object* v_____do__lift_2457_){
_start:
{
lean_object* v___x_2458_; lean_object* v___x_2459_; 
v___x_2458_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_pushNatCastFact___boxed), 14, 3);
lean_closure_set(v___x_2458_, 0, v_____do__lift_2454_);
lean_closure_set(v___x_2458_, 1, v_____do__lift_2457_);
lean_closure_set(v___x_2458_, 2, v_e_2455_);
v___x_2459_ = lean_apply_2(v_inst_2456_, lean_box(0), v___x_2458_);
return v___x_2459_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___redArg___lam__3(lean_object* v_e_2460_, lean_object* v_inst_2461_, lean_object* v_inst_2462_, lean_object* v_inst_2463_, lean_object* v_inst_2464_, lean_object* v_inst_2465_, lean_object* v_toBind_2466_, lean_object* v_____do__lift_2467_){
_start:
{
lean_object* v___f_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; 
v___f_2468_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___redArg___lam__2), 4, 3);
lean_closure_set(v___f_2468_, 0, v_____do__lift_2467_);
lean_closure_set(v___f_2468_, 1, v_e_2460_);
lean_closure_set(v___f_2468_, 2, v_inst_2461_);
v___x_2469_ = l_Lean_Meta_Sym_Arith_getIntCastFn___redArg(v_inst_2462_, v_inst_2463_, v_inst_2464_, v_inst_2465_);
v___x_2470_ = lean_apply_4(v_toBind_2466_, lean_box(0), lean_box(0), v___x_2469_, v___f_2468_);
return v___x_2470_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___redArg___lam__4(lean_object* v_modifyRingState_2471_, lean_object* v___f_2472_, lean_object* v_inst_2473_, lean_object* v_toBind_2474_, lean_object* v___f_2475_, lean_object* v_____do__lift_2476_){
_start:
{
uint8_t v_hasIntCast_2477_; 
v_hasIntCast_2477_ = lean_ctor_get_uint8(v_____do__lift_2476_, sizeof(void*)*5);
if (v_hasIntCast_2477_ == 0)
{
lean_object* v___x_2478_; 
lean_dec(v___f_2475_);
lean_dec(v_toBind_2474_);
lean_dec_ref(v_inst_2473_);
v___x_2478_ = lean_apply_1(v_modifyRingState_2471_, v___f_2472_);
return v___x_2478_;
}
else
{
lean_object* v_getRing_2479_; lean_object* v___x_2480_; 
lean_dec_ref(v___f_2472_);
lean_dec(v_modifyRingState_2471_);
v_getRing_2479_ = lean_ctor_get(v_inst_2473_, 0);
lean_inc(v_getRing_2479_);
lean_dec_ref(v_inst_2473_);
v___x_2480_ = lean_apply_4(v_toBind_2474_, lean_box(0), lean_box(0), v_getRing_2479_, v___f_2475_);
return v___x_2480_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___redArg___lam__4___boxed(lean_object* v_modifyRingState_2481_, lean_object* v___f_2482_, lean_object* v_inst_2483_, lean_object* v_toBind_2484_, lean_object* v___f_2485_, lean_object* v_____do__lift_2486_){
_start:
{
lean_object* v_res_2487_; 
v_res_2487_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___redArg___lam__4(v_modifyRingState_2481_, v___f_2482_, v_inst_2483_, v_toBind_2484_, v___f_2485_, v_____do__lift_2486_);
lean_dec_ref(v_____do__lift_2486_);
return v_res_2487_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___redArg___lam__5(lean_object* v_toBind_2488_, lean_object* v_getRingState_2489_, lean_object* v___f_2490_, lean_object* v_____r_2491_){
_start:
{
lean_object* v___x_2492_; 
v___x_2492_ = lean_apply_4(v_toBind_2488_, lean_box(0), lean_box(0), v_getRingState_2489_, v___f_2490_);
return v___x_2492_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___redArg___lam__6(lean_object* v_arg_2493_, lean_object* v_toPure_2494_, lean_object* v_modifyRingState_2495_, lean_object* v___f_2496_, lean_object* v_toBind_2497_, lean_object* v___f_2498_, lean_object* v_____do__lift_2499_){
_start:
{
lean_object* v___x_2500_; size_t v___x_2501_; size_t v___x_2502_; uint8_t v___x_2503_; 
v___x_2500_ = l_Lean_Expr_appArg_x21(v_____do__lift_2499_);
v___x_2501_ = lean_ptr_addr(v___x_2500_);
lean_dec_ref(v___x_2500_);
v___x_2502_ = lean_ptr_addr(v_arg_2493_);
v___x_2503_ = lean_usize_dec_eq(v___x_2501_, v___x_2502_);
if (v___x_2503_ == 0)
{
lean_object* v___x_2504_; lean_object* v___x_2505_; 
lean_dec(v___f_2498_);
lean_dec(v_toBind_2497_);
lean_dec_ref(v___f_2496_);
lean_dec(v_modifyRingState_2495_);
v___x_2504_ = lean_box(0);
v___x_2505_ = lean_apply_2(v_toPure_2494_, lean_box(0), v___x_2504_);
return v___x_2505_;
}
else
{
lean_object* v___x_2506_; lean_object* v___x_2507_; 
lean_dec(v_toPure_2494_);
v___x_2506_ = lean_apply_1(v_modifyRingState_2495_, v___f_2496_);
v___x_2507_ = lean_apply_4(v_toBind_2497_, lean_box(0), lean_box(0), v___x_2506_, v___f_2498_);
return v___x_2507_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___redArg___lam__6___boxed(lean_object* v_arg_2508_, lean_object* v_toPure_2509_, lean_object* v_modifyRingState_2510_, lean_object* v___f_2511_, lean_object* v_toBind_2512_, lean_object* v___f_2513_, lean_object* v_____do__lift_2514_){
_start:
{
lean_object* v_res_2515_; 
v_res_2515_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___redArg___lam__6(v_arg_2508_, v_toPure_2509_, v_modifyRingState_2510_, v___f_2511_, v_toBind_2512_, v___f_2513_, v_____do__lift_2514_);
lean_dec_ref(v_____do__lift_2514_);
lean_dec_ref(v_arg_2508_);
return v_res_2515_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___redArg___lam__7(lean_object* v___f_2516_, lean_object* v___f_2517_, lean_object* v_e_2518_, lean_object* v_inst_2519_, lean_object* v_inst_2520_, lean_object* v_inst_2521_, lean_object* v_inst_2522_, lean_object* v_toBind_2523_, lean_object* v___f_2524_, lean_object* v_toPure_2525_, lean_object* v_____do__lift_2526_){
_start:
{
lean_object* v_natCastSet_2527_; uint8_t v___x_2528_; 
v_natCastSet_2527_ = lean_ctor_get(v_____do__lift_2526_, 3);
lean_inc_ref(v_natCastSet_2527_);
lean_dec_ref(v_____do__lift_2526_);
v___x_2528_ = l_Lean_PersistentHashMap_contains___redArg(v___f_2516_, v___f_2517_, v_natCastSet_2527_, v_e_2518_);
if (v___x_2528_ == 0)
{
lean_object* v___x_2529_; lean_object* v___x_2530_; 
lean_dec(v_toPure_2525_);
v___x_2529_ = l_Lean_Meta_Sym_Arith_getNatCastFn___redArg(v_inst_2519_, v_inst_2520_, v_inst_2521_, v_inst_2522_);
v___x_2530_ = lean_apply_4(v_toBind_2523_, lean_box(0), lean_box(0), v___x_2529_, v___f_2524_);
return v___x_2530_;
}
else
{
lean_object* v___x_2531_; lean_object* v___x_2532_; 
lean_dec(v___f_2524_);
lean_dec(v_toBind_2523_);
lean_dec_ref(v_inst_2522_);
lean_dec_ref(v_inst_2521_);
lean_dec_ref(v_inst_2520_);
lean_dec(v_inst_2519_);
v___x_2531_ = lean_box(0);
v___x_2532_ = lean_apply_2(v_toPure_2525_, lean_box(0), v___x_2531_);
return v___x_2532_;
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___redArg___lam__8___closed__0(void){
_start:
{
lean_object* v___x_2533_; lean_object* v___x_2534_; lean_object* v___x_2535_; 
v___x_2533_ = lean_unsigned_to_nat(32u);
v___x_2534_ = lean_mk_empty_array_with_capacity(v___x_2533_);
v___x_2535_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2535_, 0, v___x_2534_);
return v___x_2535_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___redArg___lam__8___closed__1(void){
_start:
{
size_t v___x_2536_; lean_object* v___x_2537_; lean_object* v___x_2538_; lean_object* v___x_2539_; lean_object* v___x_2540_; lean_object* v___x_2541_; 
v___x_2536_ = ((size_t)5ULL);
v___x_2537_ = lean_unsigned_to_nat(0u);
v___x_2538_ = lean_unsigned_to_nat(32u);
v___x_2539_ = lean_mk_empty_array_with_capacity(v___x_2538_);
v___x_2540_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___redArg___lam__8___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___redArg___lam__8___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___redArg___lam__8___closed__0);
v___x_2541_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2541_, 0, v___x_2540_);
lean_ctor_set(v___x_2541_, 1, v___x_2539_);
lean_ctor_set(v___x_2541_, 2, v___x_2537_);
lean_ctor_set(v___x_2541_, 3, v___x_2537_);
lean_ctor_set_usize(v___x_2541_, 4, v___x_2536_);
return v___x_2541_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___redArg___lam__8(uint8_t v___x_2542_, lean_object* v_s_2543_){
_start:
{
lean_object* v_vars_2544_; lean_object* v_varMap_2545_; lean_object* v_denote_2546_; lean_object* v_natCastSet_2547_; lean_object* v___x_2549_; uint8_t v_isShared_2550_; uint8_t v_isSharedCheck_2555_; 
v_vars_2544_ = lean_ctor_get(v_s_2543_, 0);
v_varMap_2545_ = lean_ctor_get(v_s_2543_, 1);
v_denote_2546_ = lean_ctor_get(v_s_2543_, 2);
v_natCastSet_2547_ = lean_ctor_get(v_s_2543_, 3);
v_isSharedCheck_2555_ = !lean_is_exclusive(v_s_2543_);
if (v_isSharedCheck_2555_ == 0)
{
lean_object* v_unused_2556_; 
v_unused_2556_ = lean_ctor_get(v_s_2543_, 4);
lean_dec(v_unused_2556_);
v___x_2549_ = v_s_2543_;
v_isShared_2550_ = v_isSharedCheck_2555_;
goto v_resetjp_2548_;
}
else
{
lean_inc(v_natCastSet_2547_);
lean_inc(v_denote_2546_);
lean_inc(v_varMap_2545_);
lean_inc(v_vars_2544_);
lean_dec(v_s_2543_);
v___x_2549_ = lean_box(0);
v_isShared_2550_ = v_isSharedCheck_2555_;
goto v_resetjp_2548_;
}
v_resetjp_2548_:
{
lean_object* v___x_2551_; lean_object* v___x_2553_; 
v___x_2551_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___redArg___lam__8___closed__1, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___redArg___lam__8___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___redArg___lam__8___closed__1);
if (v_isShared_2550_ == 0)
{
lean_ctor_set(v___x_2549_, 4, v___x_2551_);
v___x_2553_ = v___x_2549_;
goto v_reusejp_2552_;
}
else
{
lean_object* v_reuseFailAlloc_2554_; 
v_reuseFailAlloc_2554_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_2554_, 0, v_vars_2544_);
lean_ctor_set(v_reuseFailAlloc_2554_, 1, v_varMap_2545_);
lean_ctor_set(v_reuseFailAlloc_2554_, 2, v_denote_2546_);
lean_ctor_set(v_reuseFailAlloc_2554_, 3, v_natCastSet_2547_);
lean_ctor_set(v_reuseFailAlloc_2554_, 4, v___x_2551_);
v___x_2553_ = v_reuseFailAlloc_2554_;
goto v_reusejp_2552_;
}
v_reusejp_2552_:
{
lean_ctor_set_uint8(v___x_2553_, sizeof(void*)*5, v___x_2542_);
return v___x_2553_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___redArg___lam__8___boxed(lean_object* v___x_2557_, lean_object* v_s_2558_){
_start:
{
uint8_t v___x_1155__boxed_2559_; lean_object* v_res_2560_; 
v___x_1155__boxed_2559_ = lean_unbox(v___x_2557_);
v_res_2560_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___redArg___lam__8(v___x_1155__boxed_2559_, v_s_2558_);
return v_res_2560_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___redArg___lam__9(lean_object* v_ring_2561_, lean_object* v_intCastFn_2562_, lean_object* v_inst_2563_, lean_object* v_e_2564_){
_start:
{
lean_object* v___x_2565_; lean_object* v___x_2566_; 
v___x_2565_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_pushNatCastFact___boxed), 14, 3);
lean_closure_set(v___x_2565_, 0, v_ring_2561_);
lean_closure_set(v___x_2565_, 1, v_intCastFn_2562_);
lean_closure_set(v___x_2565_, 2, v_e_2564_);
v___x_2566_ = lean_apply_2(v_inst_2563_, lean_box(0), v___x_2565_);
return v___x_2566_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___redArg___lam__10(lean_object* v_ring_2567_, lean_object* v_inst_2568_, lean_object* v_inst_2569_, lean_object* v_natCasts_2570_, lean_object* v_intCastFn_2571_){
_start:
{
lean_object* v___f_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; 
v___f_2572_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___redArg___lam__9), 4, 3);
lean_closure_set(v___f_2572_, 0, v_ring_2567_);
lean_closure_set(v___f_2572_, 1, v_intCastFn_2571_);
lean_closure_set(v___f_2572_, 2, v_inst_2568_);
v___x_2573_ = lean_unsigned_to_nat(0u);
v___x_2574_ = l_Lean_PersistentArray_forM___redArg(v_inst_2569_, v_natCasts_2570_, v___f_2572_, v___x_2573_);
return v___x_2574_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___redArg___lam__11(lean_object* v_inst_2575_, lean_object* v_inst_2576_, lean_object* v_natCasts_2577_, lean_object* v_toBind_2578_, lean_object* v___x_2579_, lean_object* v_ring_2580_){
_start:
{
lean_object* v___f_2581_; lean_object* v___x_2582_; 
v___f_2581_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___redArg___lam__10), 5, 4);
lean_closure_set(v___f_2581_, 0, v_ring_2580_);
lean_closure_set(v___f_2581_, 1, v_inst_2575_);
lean_closure_set(v___f_2581_, 2, v_inst_2576_);
lean_closure_set(v___f_2581_, 3, v_natCasts_2577_);
v___x_2582_ = lean_apply_4(v_toBind_2578_, lean_box(0), lean_box(0), v___x_2579_, v___f_2581_);
return v___x_2582_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___redArg___lam__12(lean_object* v_inst_2583_, lean_object* v_toBind_2584_, lean_object* v___f_2585_, lean_object* v_____r_2586_){
_start:
{
lean_object* v_getRing_2587_; lean_object* v___x_2588_; 
v_getRing_2587_ = lean_ctor_get(v_inst_2583_, 0);
lean_inc(v_getRing_2587_);
lean_dec_ref(v_inst_2583_);
v___x_2588_ = lean_apply_4(v_toBind_2584_, lean_box(0), lean_box(0), v_getRing_2587_, v___f_2585_);
return v___x_2588_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___redArg___lam__13(lean_object* v_inst_2589_, lean_object* v_inst_2590_, lean_object* v_toBind_2591_, lean_object* v___x_2592_, lean_object* v_inst_2593_, lean_object* v_modifyRingState_2594_, lean_object* v___f_2595_, lean_object* v_____do__lift_2596_){
_start:
{
lean_object* v_natCasts_2597_; lean_object* v___f_2598_; lean_object* v___f_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; 
v_natCasts_2597_ = lean_ctor_get(v_____do__lift_2596_, 4);
lean_inc_ref(v_natCasts_2597_);
lean_dec_ref(v_____do__lift_2596_);
lean_inc_n(v_toBind_2591_, 2);
v___f_2598_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___redArg___lam__11), 6, 5);
lean_closure_set(v___f_2598_, 0, v_inst_2589_);
lean_closure_set(v___f_2598_, 1, v_inst_2590_);
lean_closure_set(v___f_2598_, 2, v_natCasts_2597_);
lean_closure_set(v___f_2598_, 3, v_toBind_2591_);
lean_closure_set(v___f_2598_, 4, v___x_2592_);
v___f_2599_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___redArg___lam__12), 4, 3);
lean_closure_set(v___f_2599_, 0, v_inst_2593_);
lean_closure_set(v___f_2599_, 1, v_toBind_2591_);
lean_closure_set(v___f_2599_, 2, v___f_2598_);
v___x_2600_ = lean_apply_1(v_modifyRingState_2594_, v___f_2595_);
v___x_2601_ = lean_apply_4(v_toBind_2591_, lean_box(0), lean_box(0), v___x_2600_, v___f_2599_);
return v___x_2601_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___redArg___lam__14(lean_object* v_arg_2602_, lean_object* v_toPure_2603_, lean_object* v_toBind_2604_, lean_object* v_getRingState_2605_, lean_object* v___f_2606_, lean_object* v_____do__lift_2607_){
_start:
{
lean_object* v___x_2608_; size_t v___x_2609_; size_t v___x_2610_; uint8_t v___x_2611_; 
v___x_2608_ = l_Lean_Expr_appArg_x21(v_____do__lift_2607_);
v___x_2609_ = lean_ptr_addr(v___x_2608_);
lean_dec_ref(v___x_2608_);
v___x_2610_ = lean_ptr_addr(v_arg_2602_);
v___x_2611_ = lean_usize_dec_eq(v___x_2609_, v___x_2610_);
if (v___x_2611_ == 0)
{
lean_object* v___x_2612_; lean_object* v___x_2613_; 
lean_dec(v___f_2606_);
lean_dec(v_getRingState_2605_);
lean_dec(v_toBind_2604_);
v___x_2612_ = lean_box(0);
v___x_2613_ = lean_apply_2(v_toPure_2603_, lean_box(0), v___x_2612_);
return v___x_2613_;
}
else
{
lean_object* v___x_2614_; 
lean_dec(v_toPure_2603_);
v___x_2614_ = lean_apply_4(v_toBind_2604_, lean_box(0), lean_box(0), v_getRingState_2605_, v___f_2606_);
return v___x_2614_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___redArg___lam__14___boxed(lean_object* v_arg_2615_, lean_object* v_toPure_2616_, lean_object* v_toBind_2617_, lean_object* v_getRingState_2618_, lean_object* v___f_2619_, lean_object* v_____do__lift_2620_){
_start:
{
lean_object* v_res_2621_; 
v_res_2621_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___redArg___lam__14(v_arg_2615_, v_toPure_2616_, v_toBind_2617_, v_getRingState_2618_, v___f_2619_, v_____do__lift_2620_);
lean_dec_ref(v_____do__lift_2620_);
lean_dec_ref(v_arg_2615_);
return v_res_2621_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___redArg___lam__15(lean_object* v_arg_2622_, lean_object* v_inst_2623_, lean_object* v_inst_2624_, lean_object* v_inst_2625_, lean_object* v_inst_2626_, lean_object* v_inst_2627_, lean_object* v_toBind_2628_, lean_object* v_modifyRingState_2629_, lean_object* v___f_2630_, lean_object* v_arg_2631_, lean_object* v_toPure_2632_, lean_object* v_getRingState_2633_, lean_object* v_____do__lift_2634_){
_start:
{
uint8_t v_hasIntCast_2635_; 
v_hasIntCast_2635_ = lean_ctor_get_uint8(v_____do__lift_2634_, sizeof(void*)*5);
if (v_hasIntCast_2635_ == 0)
{
lean_object* v___x_2636_; 
v___x_2636_ = l_Lean_Meta_Sym_getIntValue_x3f(v_arg_2622_);
if (lean_obj_tag(v___x_2636_) == 0)
{
lean_object* v___x_2637_; lean_object* v___f_2638_; lean_object* v___f_2639_; lean_object* v___x_2640_; 
lean_inc_ref(v_inst_2626_);
lean_inc_ref(v_inst_2624_);
v___x_2637_ = l_Lean_Meta_Sym_Arith_getIntCastFn___redArg(v_inst_2623_, v_inst_2624_, v_inst_2625_, v_inst_2626_);
lean_inc(v___x_2637_);
lean_inc_n(v_toBind_2628_, 2);
v___f_2638_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___redArg___lam__13), 8, 7);
lean_closure_set(v___f_2638_, 0, v_inst_2627_);
lean_closure_set(v___f_2638_, 1, v_inst_2624_);
lean_closure_set(v___f_2638_, 2, v_toBind_2628_);
lean_closure_set(v___f_2638_, 3, v___x_2637_);
lean_closure_set(v___f_2638_, 4, v_inst_2626_);
lean_closure_set(v___f_2638_, 5, v_modifyRingState_2629_);
lean_closure_set(v___f_2638_, 6, v___f_2630_);
v___f_2639_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___redArg___lam__14___boxed), 6, 5);
lean_closure_set(v___f_2639_, 0, v_arg_2631_);
lean_closure_set(v___f_2639_, 1, v_toPure_2632_);
lean_closure_set(v___f_2639_, 2, v_toBind_2628_);
lean_closure_set(v___f_2639_, 3, v_getRingState_2633_);
lean_closure_set(v___f_2639_, 4, v___f_2638_);
v___x_2640_ = lean_apply_4(v_toBind_2628_, lean_box(0), lean_box(0), v___x_2637_, v___f_2639_);
return v___x_2640_;
}
else
{
lean_object* v___x_2641_; lean_object* v___x_2642_; 
lean_dec_ref_known(v___x_2636_, 1);
lean_dec(v_getRingState_2633_);
lean_dec_ref(v_arg_2631_);
lean_dec_ref(v___f_2630_);
lean_dec(v_modifyRingState_2629_);
lean_dec(v_toBind_2628_);
lean_dec(v_inst_2627_);
lean_dec_ref(v_inst_2626_);
lean_dec_ref(v_inst_2625_);
lean_dec_ref(v_inst_2624_);
lean_dec(v_inst_2623_);
v___x_2641_ = lean_box(0);
v___x_2642_ = lean_apply_2(v_toPure_2632_, lean_box(0), v___x_2641_);
return v___x_2642_;
}
}
else
{
lean_object* v___x_2643_; lean_object* v___x_2644_; 
lean_dec(v_getRingState_2633_);
lean_dec_ref(v_arg_2631_);
lean_dec_ref(v___f_2630_);
lean_dec(v_modifyRingState_2629_);
lean_dec(v_toBind_2628_);
lean_dec(v_inst_2627_);
lean_dec_ref(v_inst_2626_);
lean_dec_ref(v_inst_2625_);
lean_dec_ref(v_inst_2624_);
lean_dec(v_inst_2623_);
v___x_2643_ = lean_box(0);
v___x_2644_ = lean_apply_2(v_toPure_2632_, lean_box(0), v___x_2643_);
return v___x_2644_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___redArg___lam__15___boxed(lean_object* v_arg_2645_, lean_object* v_inst_2646_, lean_object* v_inst_2647_, lean_object* v_inst_2648_, lean_object* v_inst_2649_, lean_object* v_inst_2650_, lean_object* v_toBind_2651_, lean_object* v_modifyRingState_2652_, lean_object* v___f_2653_, lean_object* v_arg_2654_, lean_object* v_toPure_2655_, lean_object* v_getRingState_2656_, lean_object* v_____do__lift_2657_){
_start:
{
lean_object* v_res_2658_; 
v_res_2658_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___redArg___lam__15(v_arg_2645_, v_inst_2646_, v_inst_2647_, v_inst_2648_, v_inst_2649_, v_inst_2650_, v_toBind_2651_, v_modifyRingState_2652_, v___f_2653_, v_arg_2654_, v_toPure_2655_, v_getRingState_2656_, v_____do__lift_2657_);
lean_dec_ref(v_____do__lift_2657_);
lean_dec_ref(v_arg_2645_);
return v_res_2658_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___redArg___lam__16(lean_object* v_toPure_2659_, lean_object* v_inst_2660_, lean_object* v___f_2661_, lean_object* v_inst_2662_, lean_object* v_toBind_2663_, lean_object* v___f_2664_, lean_object* v___f_2665_, lean_object* v___f_2666_, lean_object* v___f_2667_, lean_object* v_e_2668_, lean_object* v_inst_2669_, lean_object* v_inst_2670_, lean_object* v_inst_2671_, lean_object* v_inst_2672_, lean_object* v_____x_2673_){
_start:
{
lean_object* v___x_2677_; uint8_t v___x_2678_; 
v___x_2677_ = l_Lean_Expr_cleanupAnnotations(v_____x_2673_);
v___x_2678_ = l_Lean_Expr_isApp(v___x_2677_);
if (v___x_2678_ == 0)
{
lean_dec_ref(v___x_2677_);
lean_dec(v_inst_2672_);
lean_dec_ref(v_inst_2671_);
lean_dec_ref(v_inst_2670_);
lean_dec(v_inst_2669_);
lean_dec_ref(v_e_2668_);
lean_dec_ref(v___f_2667_);
lean_dec_ref(v___f_2666_);
lean_dec_ref(v___f_2665_);
lean_dec(v___f_2664_);
lean_dec(v_toBind_2663_);
lean_dec_ref(v_inst_2662_);
lean_dec_ref(v___f_2661_);
lean_dec_ref(v_inst_2660_);
goto v___jp_2674_;
}
else
{
lean_object* v___x_2679_; uint8_t v___x_2680_; 
v___x_2679_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2677_);
v___x_2680_ = l_Lean_Expr_isApp(v___x_2679_);
if (v___x_2680_ == 0)
{
lean_dec_ref(v___x_2679_);
lean_dec_ref(v___x_2677_);
lean_dec(v_inst_2672_);
lean_dec_ref(v_inst_2671_);
lean_dec_ref(v_inst_2670_);
lean_dec(v_inst_2669_);
lean_dec_ref(v_e_2668_);
lean_dec_ref(v___f_2667_);
lean_dec_ref(v___f_2666_);
lean_dec_ref(v___f_2665_);
lean_dec(v___f_2664_);
lean_dec(v_toBind_2663_);
lean_dec_ref(v_inst_2662_);
lean_dec_ref(v___f_2661_);
lean_dec_ref(v_inst_2660_);
goto v___jp_2674_;
}
else
{
lean_object* v___x_2681_; uint8_t v___x_2682_; 
v___x_2681_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2679_);
v___x_2682_ = l_Lean_Expr_isApp(v___x_2681_);
if (v___x_2682_ == 0)
{
lean_dec_ref(v___x_2681_);
lean_dec_ref(v___x_2679_);
lean_dec_ref(v___x_2677_);
lean_dec(v_inst_2672_);
lean_dec_ref(v_inst_2671_);
lean_dec_ref(v_inst_2670_);
lean_dec(v_inst_2669_);
lean_dec_ref(v_e_2668_);
lean_dec_ref(v___f_2667_);
lean_dec_ref(v___f_2666_);
lean_dec_ref(v___f_2665_);
lean_dec(v___f_2664_);
lean_dec(v_toBind_2663_);
lean_dec_ref(v_inst_2662_);
lean_dec_ref(v___f_2661_);
lean_dec_ref(v_inst_2660_);
goto v___jp_2674_;
}
else
{
lean_object* v_arg_2683_; lean_object* v_arg_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; uint8_t v___x_2687_; 
v_arg_2683_ = lean_ctor_get(v___x_2677_, 1);
lean_inc_ref(v_arg_2683_);
lean_dec_ref(v___x_2677_);
v_arg_2684_ = lean_ctor_get(v___x_2679_, 1);
lean_inc_ref(v_arg_2684_);
lean_dec_ref(v___x_2679_);
v___x_2685_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2681_);
lean_dec_ref(v___x_2681_);
v___x_2686_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__2));
v___x_2687_ = l_Lean_Expr_isConstOf(v___x_2685_, v___x_2686_);
if (v___x_2687_ == 0)
{
lean_object* v___x_2688_; uint8_t v___x_2689_; 
lean_dec(v_inst_2672_);
v___x_2688_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__5));
v___x_2689_ = l_Lean_Expr_isConstOf(v___x_2685_, v___x_2688_);
lean_dec_ref(v___x_2685_);
if (v___x_2689_ == 0)
{
lean_dec_ref(v_arg_2684_);
lean_dec_ref(v_arg_2683_);
lean_dec_ref(v_inst_2671_);
lean_dec_ref(v_inst_2670_);
lean_dec(v_inst_2669_);
lean_dec_ref(v_e_2668_);
lean_dec_ref(v___f_2667_);
lean_dec_ref(v___f_2666_);
lean_dec_ref(v___f_2665_);
lean_dec(v___f_2664_);
lean_dec(v_toBind_2663_);
lean_dec_ref(v_inst_2662_);
lean_dec_ref(v___f_2661_);
lean_dec_ref(v_inst_2660_);
goto v___jp_2674_;
}
else
{
uint8_t v___x_2690_; 
v___x_2690_ = l_Lean_Meta_Sym_isNatValue(v_arg_2683_);
lean_dec_ref(v_arg_2683_);
if (v___x_2690_ == 0)
{
lean_object* v_getRingState_2691_; lean_object* v_modifyRingState_2692_; lean_object* v___f_2693_; lean_object* v___f_2694_; lean_object* v___f_2695_; lean_object* v___f_2696_; lean_object* v___x_2697_; 
v_getRingState_2691_ = lean_ctor_get(v_inst_2660_, 0);
lean_inc_n(v_getRingState_2691_, 2);
v_modifyRingState_2692_ = lean_ctor_get(v_inst_2660_, 1);
lean_inc_n(v_modifyRingState_2692_, 2);
lean_dec_ref(v_inst_2660_);
lean_inc_n(v_toBind_2663_, 4);
lean_inc_ref(v_inst_2662_);
v___f_2693_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___redArg___lam__4___boxed), 6, 5);
lean_closure_set(v___f_2693_, 0, v_modifyRingState_2692_);
lean_closure_set(v___f_2693_, 1, v___f_2661_);
lean_closure_set(v___f_2693_, 2, v_inst_2662_);
lean_closure_set(v___f_2693_, 3, v_toBind_2663_);
lean_closure_set(v___f_2693_, 4, v___f_2664_);
v___f_2694_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___redArg___lam__5), 4, 3);
lean_closure_set(v___f_2694_, 0, v_toBind_2663_);
lean_closure_set(v___f_2694_, 1, v_getRingState_2691_);
lean_closure_set(v___f_2694_, 2, v___f_2693_);
lean_inc(v_toPure_2659_);
v___f_2695_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___redArg___lam__6___boxed), 7, 6);
lean_closure_set(v___f_2695_, 0, v_arg_2684_);
lean_closure_set(v___f_2695_, 1, v_toPure_2659_);
lean_closure_set(v___f_2695_, 2, v_modifyRingState_2692_);
lean_closure_set(v___f_2695_, 3, v___f_2665_);
lean_closure_set(v___f_2695_, 4, v_toBind_2663_);
lean_closure_set(v___f_2695_, 5, v___f_2694_);
v___f_2696_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___redArg___lam__7), 11, 10);
lean_closure_set(v___f_2696_, 0, v___f_2666_);
lean_closure_set(v___f_2696_, 1, v___f_2667_);
lean_closure_set(v___f_2696_, 2, v_e_2668_);
lean_closure_set(v___f_2696_, 3, v_inst_2669_);
lean_closure_set(v___f_2696_, 4, v_inst_2670_);
lean_closure_set(v___f_2696_, 5, v_inst_2671_);
lean_closure_set(v___f_2696_, 6, v_inst_2662_);
lean_closure_set(v___f_2696_, 7, v_toBind_2663_);
lean_closure_set(v___f_2696_, 8, v___f_2695_);
lean_closure_set(v___f_2696_, 9, v_toPure_2659_);
v___x_2697_ = lean_apply_4(v_toBind_2663_, lean_box(0), lean_box(0), v_getRingState_2691_, v___f_2696_);
return v___x_2697_;
}
else
{
lean_object* v___x_2698_; lean_object* v___x_2699_; 
lean_dec_ref(v_arg_2684_);
lean_dec_ref(v_inst_2671_);
lean_dec_ref(v_inst_2670_);
lean_dec(v_inst_2669_);
lean_dec_ref(v_e_2668_);
lean_dec_ref(v___f_2667_);
lean_dec_ref(v___f_2666_);
lean_dec_ref(v___f_2665_);
lean_dec(v___f_2664_);
lean_dec(v_toBind_2663_);
lean_dec_ref(v_inst_2662_);
lean_dec_ref(v___f_2661_);
lean_dec_ref(v_inst_2660_);
v___x_2698_ = lean_box(0);
v___x_2699_ = lean_apply_2(v_toPure_2659_, lean_box(0), v___x_2698_);
return v___x_2699_;
}
}
}
else
{
lean_object* v_getRingState_2700_; lean_object* v_modifyRingState_2701_; lean_object* v___x_2702_; lean_object* v___f_2703_; lean_object* v___f_2704_; lean_object* v___x_2705_; 
lean_dec_ref(v___x_2685_);
lean_dec_ref(v_e_2668_);
lean_dec_ref(v___f_2667_);
lean_dec_ref(v___f_2666_);
lean_dec_ref(v___f_2665_);
lean_dec(v___f_2664_);
lean_dec_ref(v___f_2661_);
v_getRingState_2700_ = lean_ctor_get(v_inst_2660_, 0);
lean_inc_n(v_getRingState_2700_, 2);
v_modifyRingState_2701_ = lean_ctor_get(v_inst_2660_, 1);
lean_inc(v_modifyRingState_2701_);
lean_dec_ref(v_inst_2660_);
v___x_2702_ = lean_box(v___x_2687_);
v___f_2703_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___redArg___lam__8___boxed), 2, 1);
lean_closure_set(v___f_2703_, 0, v___x_2702_);
lean_inc(v_toBind_2663_);
v___f_2704_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___redArg___lam__15___boxed), 13, 12);
lean_closure_set(v___f_2704_, 0, v_arg_2683_);
lean_closure_set(v___f_2704_, 1, v_inst_2669_);
lean_closure_set(v___f_2704_, 2, v_inst_2670_);
lean_closure_set(v___f_2704_, 3, v_inst_2671_);
lean_closure_set(v___f_2704_, 4, v_inst_2662_);
lean_closure_set(v___f_2704_, 5, v_inst_2672_);
lean_closure_set(v___f_2704_, 6, v_toBind_2663_);
lean_closure_set(v___f_2704_, 7, v_modifyRingState_2701_);
lean_closure_set(v___f_2704_, 8, v___f_2703_);
lean_closure_set(v___f_2704_, 9, v_arg_2684_);
lean_closure_set(v___f_2704_, 10, v_toPure_2659_);
lean_closure_set(v___f_2704_, 11, v_getRingState_2700_);
v___x_2705_ = lean_apply_4(v_toBind_2663_, lean_box(0), lean_box(0), v_getRingState_2700_, v___f_2704_);
return v___x_2705_;
}
}
}
}
v___jp_2674_:
{
lean_object* v___x_2675_; lean_object* v___x_2676_; 
v___x_2675_ = lean_box(0);
v___x_2676_ = lean_apply_2(v_toPure_2659_, lean_box(0), v___x_2675_);
return v___x_2676_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___redArg___lam__16___boxed(lean_object* v_toPure_2706_, lean_object* v_inst_2707_, lean_object* v___f_2708_, lean_object* v_inst_2709_, lean_object* v_toBind_2710_, lean_object* v___f_2711_, lean_object* v___f_2712_, lean_object* v___f_2713_, lean_object* v___f_2714_, lean_object* v_e_2715_, lean_object* v_inst_2716_, lean_object* v_inst_2717_, lean_object* v_inst_2718_, lean_object* v_inst_2719_, lean_object* v_____x_2720_){
_start:
{
lean_object* v_res_2721_; 
v_res_2721_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___redArg___lam__16(v_toPure_2706_, v_inst_2707_, v___f_2708_, v_inst_2709_, v_toBind_2710_, v___f_2711_, v___f_2712_, v___f_2713_, v___f_2714_, v_e_2715_, v_inst_2716_, v_inst_2717_, v_inst_2718_, v_inst_2719_, v_____x_2720_);
lean_dec_ref(v_____x_2720_);
return v_res_2721_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___redArg(lean_object* v_inst_2724_, lean_object* v_inst_2725_, lean_object* v_inst_2726_, lean_object* v_inst_2727_, lean_object* v_inst_2728_, lean_object* v_inst_2729_, lean_object* v_e_2730_){
_start:
{
lean_object* v_toApplicative_2731_; lean_object* v_toBind_2732_; lean_object* v_toPure_2733_; lean_object* v___f_2734_; lean_object* v___f_2735_; lean_object* v___f_2736_; lean_object* v___f_2737_; lean_object* v___f_2738_; lean_object* v___x_2739_; lean_object* v___x_2740_; lean_object* v___f_2741_; lean_object* v___x_2742_; 
v_toApplicative_2731_ = lean_ctor_get(v_inst_2726_, 0);
v_toBind_2732_ = lean_ctor_get(v_inst_2726_, 1);
lean_inc_n(v_toBind_2732_, 3);
v_toPure_2733_ = lean_ctor_get(v_toApplicative_2731_, 1);
lean_inc(v_toPure_2733_);
lean_inc_ref_n(v_e_2730_, 4);
v___f_2734_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2734_, 0, v_e_2730_);
v___f_2735_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___redArg___closed__0));
v___f_2736_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___redArg___closed__1));
v___f_2737_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___redArg___lam__1), 4, 3);
lean_closure_set(v___f_2737_, 0, v___f_2735_);
lean_closure_set(v___f_2737_, 1, v___f_2736_);
lean_closure_set(v___f_2737_, 2, v_e_2730_);
lean_inc_ref(v_inst_2728_);
lean_inc_ref(v_inst_2727_);
lean_inc_ref(v_inst_2726_);
lean_inc_n(v_inst_2725_, 2);
lean_inc(v_inst_2724_);
v___f_2738_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___redArg___lam__3), 8, 7);
lean_closure_set(v___f_2738_, 0, v_e_2730_);
lean_closure_set(v___f_2738_, 1, v_inst_2724_);
lean_closure_set(v___f_2738_, 2, v_inst_2725_);
lean_closure_set(v___f_2738_, 3, v_inst_2726_);
lean_closure_set(v___f_2738_, 4, v_inst_2727_);
lean_closure_set(v___f_2738_, 5, v_inst_2728_);
lean_closure_set(v___f_2738_, 6, v_toBind_2732_);
v___x_2739_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateMVarsIfMVarApp___boxed), 6, 1);
lean_closure_set(v___x_2739_, 0, v_e_2730_);
v___x_2740_ = lean_apply_2(v_inst_2725_, lean_box(0), v___x_2739_);
v___f_2741_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___redArg___lam__16___boxed), 15, 14);
lean_closure_set(v___f_2741_, 0, v_toPure_2733_);
lean_closure_set(v___f_2741_, 1, v_inst_2729_);
lean_closure_set(v___f_2741_, 2, v___f_2734_);
lean_closure_set(v___f_2741_, 3, v_inst_2728_);
lean_closure_set(v___f_2741_, 4, v_toBind_2732_);
lean_closure_set(v___f_2741_, 5, v___f_2738_);
lean_closure_set(v___f_2741_, 6, v___f_2737_);
lean_closure_set(v___f_2741_, 7, v___f_2735_);
lean_closure_set(v___f_2741_, 8, v___f_2736_);
lean_closure_set(v___f_2741_, 9, v_e_2730_);
lean_closure_set(v___f_2741_, 10, v_inst_2725_);
lean_closure_set(v___f_2741_, 11, v_inst_2726_);
lean_closure_set(v___f_2741_, 12, v_inst_2727_);
lean_closure_set(v___f_2741_, 13, v_inst_2724_);
v___x_2742_ = lean_apply_4(v_toBind_2732_, lean_box(0), lean_box(0), v___x_2740_, v___f_2741_);
return v___x_2742_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast(lean_object* v_m_2743_, lean_object* v_inst_2744_, lean_object* v_inst_2745_, lean_object* v_inst_2746_, lean_object* v_inst_2747_, lean_object* v_inst_2748_, lean_object* v_inst_2749_, lean_object* v_inst_2750_, lean_object* v_e_2751_){
_start:
{
lean_object* v___x_2752_; 
v___x_2752_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___redArg(v_inst_2744_, v_inst_2745_, v_inst_2747_, v_inst_2748_, v_inst_2749_, v_inst_2750_, v_e_2751_);
return v___x_2752_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___boxed(lean_object* v_m_2753_, lean_object* v_inst_2754_, lean_object* v_inst_2755_, lean_object* v_inst_2756_, lean_object* v_inst_2757_, lean_object* v_inst_2758_, lean_object* v_inst_2759_, lean_object* v_inst_2760_, lean_object* v_e_2761_){
_start:
{
lean_object* v_res_2762_; 
v_res_2762_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast(v_m_2753_, v_inst_2754_, v_inst_2755_, v_inst_2756_, v_inst_2757_, v_inst_2758_, v_inst_2759_, v_inst_2760_, v_e_2761_);
lean_dec_ref(v_inst_2756_);
return v_res_2762_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__1_spec__8_spec__17___redArg(lean_object* v_a_2763_, lean_object* v_a_2764_, lean_object* v_as_2765_, size_t v_i_2766_, size_t v_stop_2767_, lean_object* v_b_2768_, lean_object* v___y_2769_, lean_object* v___y_2770_, lean_object* v___y_2771_, lean_object* v___y_2772_, lean_object* v___y_2773_, lean_object* v___y_2774_, lean_object* v___y_2775_){
_start:
{
uint8_t v___x_2777_; 
v___x_2777_ = lean_usize_dec_eq(v_i_2766_, v_stop_2767_);
if (v___x_2777_ == 0)
{
lean_object* v___x_2778_; lean_object* v___x_2779_; 
v___x_2778_ = lean_array_uget_borrowed(v_as_2765_, v_i_2766_);
lean_inc(v___x_2778_);
lean_inc_ref(v_a_2764_);
lean_inc_ref(v_a_2763_);
v___x_2779_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_pushNatCastFact___redArg(v_a_2763_, v_a_2764_, v___x_2778_, v___y_2769_, v___y_2770_, v___y_2771_, v___y_2772_, v___y_2773_, v___y_2774_, v___y_2775_);
if (lean_obj_tag(v___x_2779_) == 0)
{
lean_object* v_a_2780_; size_t v___x_2781_; size_t v___x_2782_; 
v_a_2780_ = lean_ctor_get(v___x_2779_, 0);
lean_inc(v_a_2780_);
lean_dec_ref_known(v___x_2779_, 1);
v___x_2781_ = ((size_t)1ULL);
v___x_2782_ = lean_usize_add(v_i_2766_, v___x_2781_);
v_i_2766_ = v___x_2782_;
v_b_2768_ = v_a_2780_;
goto _start;
}
else
{
lean_dec_ref(v_a_2764_);
lean_dec_ref(v_a_2763_);
return v___x_2779_;
}
}
else
{
lean_object* v___x_2784_; 
lean_dec_ref(v_a_2764_);
lean_dec_ref(v_a_2763_);
v___x_2784_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2784_, 0, v_b_2768_);
return v___x_2784_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__1_spec__8_spec__17___redArg___boxed(lean_object* v_a_2785_, lean_object* v_a_2786_, lean_object* v_as_2787_, lean_object* v_i_2788_, lean_object* v_stop_2789_, lean_object* v_b_2790_, lean_object* v___y_2791_, lean_object* v___y_2792_, lean_object* v___y_2793_, lean_object* v___y_2794_, lean_object* v___y_2795_, lean_object* v___y_2796_, lean_object* v___y_2797_, lean_object* v___y_2798_){
_start:
{
size_t v_i_boxed_2799_; size_t v_stop_boxed_2800_; lean_object* v_res_2801_; 
v_i_boxed_2799_ = lean_unbox_usize(v_i_2788_);
lean_dec(v_i_2788_);
v_stop_boxed_2800_ = lean_unbox_usize(v_stop_2789_);
lean_dec(v_stop_2789_);
v_res_2801_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__1_spec__8_spec__17___redArg(v_a_2785_, v_a_2786_, v_as_2787_, v_i_boxed_2799_, v_stop_boxed_2800_, v_b_2790_, v___y_2791_, v___y_2792_, v___y_2793_, v___y_2794_, v___y_2795_, v___y_2796_, v___y_2797_);
lean_dec(v___y_2797_);
lean_dec_ref(v___y_2796_);
lean_dec(v___y_2795_);
lean_dec_ref(v___y_2794_);
lean_dec(v___y_2793_);
lean_dec_ref(v___y_2792_);
lean_dec(v___y_2791_);
lean_dec_ref(v_as_2787_);
return v_res_2801_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__1_spec__8_spec__16_spec__22(lean_object* v_a_2802_, lean_object* v_a_2803_, lean_object* v_x_2804_, lean_object* v___y_2805_, lean_object* v___y_2806_, lean_object* v___y_2807_, lean_object* v___y_2808_, lean_object* v___y_2809_, lean_object* v___y_2810_, lean_object* v___y_2811_, lean_object* v___y_2812_, lean_object* v___y_2813_, lean_object* v___y_2814_, lean_object* v___y_2815_){
_start:
{
if (lean_obj_tag(v_x_2804_) == 0)
{
lean_object* v_cs_2817_; lean_object* v___x_2819_; uint8_t v_isShared_2820_; uint8_t v_isSharedCheck_2831_; 
v_cs_2817_ = lean_ctor_get(v_x_2804_, 0);
v_isSharedCheck_2831_ = !lean_is_exclusive(v_x_2804_);
if (v_isSharedCheck_2831_ == 0)
{
v___x_2819_ = v_x_2804_;
v_isShared_2820_ = v_isSharedCheck_2831_;
goto v_resetjp_2818_;
}
else
{
lean_inc(v_cs_2817_);
lean_dec(v_x_2804_);
v___x_2819_ = lean_box(0);
v_isShared_2820_ = v_isSharedCheck_2831_;
goto v_resetjp_2818_;
}
v_resetjp_2818_:
{
lean_object* v___x_2821_; lean_object* v___x_2822_; lean_object* v___x_2823_; uint8_t v___x_2824_; 
v___x_2821_ = lean_unsigned_to_nat(0u);
v___x_2822_ = lean_array_get_size(v_cs_2817_);
v___x_2823_ = lean_box(0);
v___x_2824_ = lean_nat_dec_lt(v___x_2821_, v___x_2822_);
if (v___x_2824_ == 0)
{
lean_object* v___x_2826_; 
lean_dec_ref(v_cs_2817_);
lean_dec_ref(v_a_2803_);
lean_dec_ref(v_a_2802_);
if (v_isShared_2820_ == 0)
{
lean_ctor_set(v___x_2819_, 0, v___x_2823_);
v___x_2826_ = v___x_2819_;
goto v_reusejp_2825_;
}
else
{
lean_object* v_reuseFailAlloc_2827_; 
v_reuseFailAlloc_2827_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2827_, 0, v___x_2823_);
v___x_2826_ = v_reuseFailAlloc_2827_;
goto v_reusejp_2825_;
}
v_reusejp_2825_:
{
return v___x_2826_;
}
}
else
{
size_t v___x_2828_; size_t v___x_2829_; lean_object* v___x_2830_; 
lean_del_object(v___x_2819_);
v___x_2828_ = ((size_t)0ULL);
v___x_2829_ = lean_usize_of_nat(v___x_2822_);
v___x_2830_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__1_spec__8_spec__16_spec__23(v_a_2802_, v_a_2803_, v_cs_2817_, v___x_2828_, v___x_2829_, v___x_2823_, v___y_2805_, v___y_2806_, v___y_2807_, v___y_2808_, v___y_2809_, v___y_2810_, v___y_2811_, v___y_2812_, v___y_2813_, v___y_2814_, v___y_2815_);
lean_dec_ref(v_cs_2817_);
return v___x_2830_;
}
}
}
else
{
lean_object* v_vs_2832_; lean_object* v___x_2834_; uint8_t v_isShared_2835_; uint8_t v_isSharedCheck_2846_; 
v_vs_2832_ = lean_ctor_get(v_x_2804_, 0);
v_isSharedCheck_2846_ = !lean_is_exclusive(v_x_2804_);
if (v_isSharedCheck_2846_ == 0)
{
v___x_2834_ = v_x_2804_;
v_isShared_2835_ = v_isSharedCheck_2846_;
goto v_resetjp_2833_;
}
else
{
lean_inc(v_vs_2832_);
lean_dec(v_x_2804_);
v___x_2834_ = lean_box(0);
v_isShared_2835_ = v_isSharedCheck_2846_;
goto v_resetjp_2833_;
}
v_resetjp_2833_:
{
lean_object* v___x_2836_; lean_object* v___x_2837_; lean_object* v___x_2838_; uint8_t v___x_2839_; 
v___x_2836_ = lean_unsigned_to_nat(0u);
v___x_2837_ = lean_array_get_size(v_vs_2832_);
v___x_2838_ = lean_box(0);
v___x_2839_ = lean_nat_dec_lt(v___x_2836_, v___x_2837_);
if (v___x_2839_ == 0)
{
lean_object* v___x_2841_; 
lean_dec_ref(v_vs_2832_);
lean_dec_ref(v_a_2803_);
lean_dec_ref(v_a_2802_);
if (v_isShared_2835_ == 0)
{
lean_ctor_set_tag(v___x_2834_, 0);
lean_ctor_set(v___x_2834_, 0, v___x_2838_);
v___x_2841_ = v___x_2834_;
goto v_reusejp_2840_;
}
else
{
lean_object* v_reuseFailAlloc_2842_; 
v_reuseFailAlloc_2842_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2842_, 0, v___x_2838_);
v___x_2841_ = v_reuseFailAlloc_2842_;
goto v_reusejp_2840_;
}
v_reusejp_2840_:
{
return v___x_2841_;
}
}
else
{
size_t v___x_2843_; size_t v___x_2844_; lean_object* v___x_2845_; 
lean_del_object(v___x_2834_);
v___x_2843_ = ((size_t)0ULL);
v___x_2844_ = lean_usize_of_nat(v___x_2837_);
v___x_2845_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__1_spec__8_spec__17___redArg(v_a_2802_, v_a_2803_, v_vs_2832_, v___x_2843_, v___x_2844_, v___x_2838_, v___y_2806_, v___y_2810_, v___y_2811_, v___y_2812_, v___y_2813_, v___y_2814_, v___y_2815_);
lean_dec_ref(v_vs_2832_);
return v___x_2845_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__1_spec__8_spec__16_spec__23(lean_object* v_a_2847_, lean_object* v_a_2848_, lean_object* v_as_2849_, size_t v_i_2850_, size_t v_stop_2851_, lean_object* v_b_2852_, lean_object* v___y_2853_, lean_object* v___y_2854_, lean_object* v___y_2855_, lean_object* v___y_2856_, lean_object* v___y_2857_, lean_object* v___y_2858_, lean_object* v___y_2859_, lean_object* v___y_2860_, lean_object* v___y_2861_, lean_object* v___y_2862_, lean_object* v___y_2863_){
_start:
{
uint8_t v___x_2865_; 
v___x_2865_ = lean_usize_dec_eq(v_i_2850_, v_stop_2851_);
if (v___x_2865_ == 0)
{
lean_object* v___x_2866_; lean_object* v___x_2867_; 
v___x_2866_ = lean_array_uget_borrowed(v_as_2849_, v_i_2850_);
lean_inc(v___x_2866_);
lean_inc_ref(v_a_2848_);
lean_inc_ref(v_a_2847_);
v___x_2867_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__1_spec__8_spec__16_spec__22(v_a_2847_, v_a_2848_, v___x_2866_, v___y_2853_, v___y_2854_, v___y_2855_, v___y_2856_, v___y_2857_, v___y_2858_, v___y_2859_, v___y_2860_, v___y_2861_, v___y_2862_, v___y_2863_);
if (lean_obj_tag(v___x_2867_) == 0)
{
lean_object* v_a_2868_; size_t v___x_2869_; size_t v___x_2870_; 
v_a_2868_ = lean_ctor_get(v___x_2867_, 0);
lean_inc(v_a_2868_);
lean_dec_ref_known(v___x_2867_, 1);
v___x_2869_ = ((size_t)1ULL);
v___x_2870_ = lean_usize_add(v_i_2850_, v___x_2869_);
v_i_2850_ = v___x_2870_;
v_b_2852_ = v_a_2868_;
goto _start;
}
else
{
lean_dec_ref(v_a_2848_);
lean_dec_ref(v_a_2847_);
return v___x_2867_;
}
}
else
{
lean_object* v___x_2872_; 
lean_dec_ref(v_a_2848_);
lean_dec_ref(v_a_2847_);
v___x_2872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2872_, 0, v_b_2852_);
return v___x_2872_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__1_spec__8_spec__16_spec__23___boxed(lean_object** _args){
lean_object* v_a_2873_ = _args[0];
lean_object* v_a_2874_ = _args[1];
lean_object* v_as_2875_ = _args[2];
lean_object* v_i_2876_ = _args[3];
lean_object* v_stop_2877_ = _args[4];
lean_object* v_b_2878_ = _args[5];
lean_object* v___y_2879_ = _args[6];
lean_object* v___y_2880_ = _args[7];
lean_object* v___y_2881_ = _args[8];
lean_object* v___y_2882_ = _args[9];
lean_object* v___y_2883_ = _args[10];
lean_object* v___y_2884_ = _args[11];
lean_object* v___y_2885_ = _args[12];
lean_object* v___y_2886_ = _args[13];
lean_object* v___y_2887_ = _args[14];
lean_object* v___y_2888_ = _args[15];
lean_object* v___y_2889_ = _args[16];
lean_object* v___y_2890_ = _args[17];
_start:
{
size_t v_i_boxed_2891_; size_t v_stop_boxed_2892_; lean_object* v_res_2893_; 
v_i_boxed_2891_ = lean_unbox_usize(v_i_2876_);
lean_dec(v_i_2876_);
v_stop_boxed_2892_ = lean_unbox_usize(v_stop_2877_);
lean_dec(v_stop_2877_);
v_res_2893_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__1_spec__8_spec__16_spec__23(v_a_2873_, v_a_2874_, v_as_2875_, v_i_boxed_2891_, v_stop_boxed_2892_, v_b_2878_, v___y_2879_, v___y_2880_, v___y_2881_, v___y_2882_, v___y_2883_, v___y_2884_, v___y_2885_, v___y_2886_, v___y_2887_, v___y_2888_, v___y_2889_);
lean_dec(v___y_2889_);
lean_dec_ref(v___y_2888_);
lean_dec(v___y_2887_);
lean_dec_ref(v___y_2886_);
lean_dec(v___y_2885_);
lean_dec_ref(v___y_2884_);
lean_dec(v___y_2883_);
lean_dec_ref(v___y_2882_);
lean_dec(v___y_2881_);
lean_dec(v___y_2880_);
lean_dec(v___y_2879_);
lean_dec_ref(v_as_2875_);
return v_res_2893_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__1_spec__8_spec__16_spec__22___boxed(lean_object* v_a_2894_, lean_object* v_a_2895_, lean_object* v_x_2896_, lean_object* v___y_2897_, lean_object* v___y_2898_, lean_object* v___y_2899_, lean_object* v___y_2900_, lean_object* v___y_2901_, lean_object* v___y_2902_, lean_object* v___y_2903_, lean_object* v___y_2904_, lean_object* v___y_2905_, lean_object* v___y_2906_, lean_object* v___y_2907_, lean_object* v___y_2908_){
_start:
{
lean_object* v_res_2909_; 
v_res_2909_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__1_spec__8_spec__16_spec__22(v_a_2894_, v_a_2895_, v_x_2896_, v___y_2897_, v___y_2898_, v___y_2899_, v___y_2900_, v___y_2901_, v___y_2902_, v___y_2903_, v___y_2904_, v___y_2905_, v___y_2906_, v___y_2907_);
lean_dec(v___y_2907_);
lean_dec_ref(v___y_2906_);
lean_dec(v___y_2905_);
lean_dec_ref(v___y_2904_);
lean_dec(v___y_2903_);
lean_dec_ref(v___y_2902_);
lean_dec(v___y_2901_);
lean_dec_ref(v___y_2900_);
lean_dec(v___y_2899_);
lean_dec(v___y_2898_);
lean_dec(v___y_2897_);
return v_res_2909_;
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__1_spec__8_spec__16___closed__0(void){
_start:
{
lean_object* v___x_2910_; 
v___x_2910_ = l_Lean_instInhabitedPersistentArrayNode_default___redArg();
return v___x_2910_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__1_spec__8_spec__16(lean_object* v_a_2911_, lean_object* v_a_2912_, lean_object* v_x_2913_, size_t v_x_2914_, size_t v_x_2915_, lean_object* v___y_2916_, lean_object* v___y_2917_, lean_object* v___y_2918_, lean_object* v___y_2919_, lean_object* v___y_2920_, lean_object* v___y_2921_, lean_object* v___y_2922_, lean_object* v___y_2923_, lean_object* v___y_2924_, lean_object* v___y_2925_, lean_object* v___y_2926_){
_start:
{
if (lean_obj_tag(v_x_2913_) == 0)
{
lean_object* v_cs_2928_; lean_object* v___x_2929_; size_t v___x_2930_; lean_object* v_j_2931_; lean_object* v___x_2932_; size_t v___x_2933_; size_t v___x_2934_; size_t v___x_2935_; size_t v___x_2936_; size_t v___x_2937_; size_t v___x_2938_; lean_object* v___x_2939_; 
v_cs_2928_ = lean_ctor_get(v_x_2913_, 0);
lean_inc_ref(v_cs_2928_);
lean_dec_ref_known(v_x_2913_, 1);
v___x_2929_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__1_spec__8_spec__16___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__1_spec__8_spec__16___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__1_spec__8_spec__16___closed__0);
v___x_2930_ = lean_usize_shift_right(v_x_2914_, v_x_2915_);
v_j_2931_ = lean_usize_to_nat(v___x_2930_);
v___x_2932_ = lean_array_get_borrowed(v___x_2929_, v_cs_2928_, v_j_2931_);
v___x_2933_ = ((size_t)1ULL);
v___x_2934_ = lean_usize_shift_left(v___x_2933_, v_x_2915_);
v___x_2935_ = lean_usize_sub(v___x_2934_, v___x_2933_);
v___x_2936_ = lean_usize_land(v_x_2914_, v___x_2935_);
v___x_2937_ = ((size_t)5ULL);
v___x_2938_ = lean_usize_sub(v_x_2915_, v___x_2937_);
lean_inc(v___x_2932_);
lean_inc_ref(v_a_2912_);
lean_inc_ref(v_a_2911_);
v___x_2939_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__1_spec__8_spec__16(v_a_2911_, v_a_2912_, v___x_2932_, v___x_2936_, v___x_2938_, v___y_2916_, v___y_2917_, v___y_2918_, v___y_2919_, v___y_2920_, v___y_2921_, v___y_2922_, v___y_2923_, v___y_2924_, v___y_2925_, v___y_2926_);
if (lean_obj_tag(v___x_2939_) == 0)
{
lean_object* v___x_2941_; uint8_t v_isShared_2942_; uint8_t v_isSharedCheck_2954_; 
v_isSharedCheck_2954_ = !lean_is_exclusive(v___x_2939_);
if (v_isSharedCheck_2954_ == 0)
{
lean_object* v_unused_2955_; 
v_unused_2955_ = lean_ctor_get(v___x_2939_, 0);
lean_dec(v_unused_2955_);
v___x_2941_ = v___x_2939_;
v_isShared_2942_ = v_isSharedCheck_2954_;
goto v_resetjp_2940_;
}
else
{
lean_dec(v___x_2939_);
v___x_2941_ = lean_box(0);
v_isShared_2942_ = v_isSharedCheck_2954_;
goto v_resetjp_2940_;
}
v_resetjp_2940_:
{
lean_object* v___x_2943_; lean_object* v___x_2944_; lean_object* v___x_2945_; lean_object* v___x_2946_; uint8_t v___x_2947_; 
v___x_2943_ = lean_unsigned_to_nat(1u);
v___x_2944_ = lean_nat_add(v_j_2931_, v___x_2943_);
lean_dec(v_j_2931_);
v___x_2945_ = lean_array_get_size(v_cs_2928_);
v___x_2946_ = lean_box(0);
v___x_2947_ = lean_nat_dec_lt(v___x_2944_, v___x_2945_);
if (v___x_2947_ == 0)
{
lean_object* v___x_2949_; 
lean_dec(v___x_2944_);
lean_dec_ref(v_cs_2928_);
lean_dec_ref(v_a_2912_);
lean_dec_ref(v_a_2911_);
if (v_isShared_2942_ == 0)
{
lean_ctor_set(v___x_2941_, 0, v___x_2946_);
v___x_2949_ = v___x_2941_;
goto v_reusejp_2948_;
}
else
{
lean_object* v_reuseFailAlloc_2950_; 
v_reuseFailAlloc_2950_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2950_, 0, v___x_2946_);
v___x_2949_ = v_reuseFailAlloc_2950_;
goto v_reusejp_2948_;
}
v_reusejp_2948_:
{
return v___x_2949_;
}
}
else
{
size_t v___x_2951_; size_t v___x_2952_; lean_object* v___x_2953_; 
lean_del_object(v___x_2941_);
v___x_2951_ = lean_usize_of_nat(v___x_2944_);
lean_dec(v___x_2944_);
v___x_2952_ = lean_usize_of_nat(v___x_2945_);
v___x_2953_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__1_spec__8_spec__16_spec__23(v_a_2911_, v_a_2912_, v_cs_2928_, v___x_2951_, v___x_2952_, v___x_2946_, v___y_2916_, v___y_2917_, v___y_2918_, v___y_2919_, v___y_2920_, v___y_2921_, v___y_2922_, v___y_2923_, v___y_2924_, v___y_2925_, v___y_2926_);
lean_dec_ref(v_cs_2928_);
return v___x_2953_;
}
}
}
else
{
lean_dec(v_j_2931_);
lean_dec_ref(v_cs_2928_);
lean_dec_ref(v_a_2912_);
lean_dec_ref(v_a_2911_);
return v___x_2939_;
}
}
else
{
lean_object* v_vs_2956_; lean_object* v___x_2958_; uint8_t v_isShared_2959_; uint8_t v_isSharedCheck_2970_; 
v_vs_2956_ = lean_ctor_get(v_x_2913_, 0);
v_isSharedCheck_2970_ = !lean_is_exclusive(v_x_2913_);
if (v_isSharedCheck_2970_ == 0)
{
v___x_2958_ = v_x_2913_;
v_isShared_2959_ = v_isSharedCheck_2970_;
goto v_resetjp_2957_;
}
else
{
lean_inc(v_vs_2956_);
lean_dec(v_x_2913_);
v___x_2958_ = lean_box(0);
v_isShared_2959_ = v_isSharedCheck_2970_;
goto v_resetjp_2957_;
}
v_resetjp_2957_:
{
lean_object* v___x_2960_; lean_object* v___x_2961_; lean_object* v___x_2962_; uint8_t v___x_2963_; 
v___x_2960_ = lean_usize_to_nat(v_x_2914_);
v___x_2961_ = lean_array_get_size(v_vs_2956_);
v___x_2962_ = lean_box(0);
v___x_2963_ = lean_nat_dec_lt(v___x_2960_, v___x_2961_);
if (v___x_2963_ == 0)
{
lean_object* v___x_2965_; 
lean_dec(v___x_2960_);
lean_dec_ref(v_vs_2956_);
lean_dec_ref(v_a_2912_);
lean_dec_ref(v_a_2911_);
if (v_isShared_2959_ == 0)
{
lean_ctor_set_tag(v___x_2958_, 0);
lean_ctor_set(v___x_2958_, 0, v___x_2962_);
v___x_2965_ = v___x_2958_;
goto v_reusejp_2964_;
}
else
{
lean_object* v_reuseFailAlloc_2966_; 
v_reuseFailAlloc_2966_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2966_, 0, v___x_2962_);
v___x_2965_ = v_reuseFailAlloc_2966_;
goto v_reusejp_2964_;
}
v_reusejp_2964_:
{
return v___x_2965_;
}
}
else
{
size_t v___x_2967_; size_t v___x_2968_; lean_object* v___x_2969_; 
lean_del_object(v___x_2958_);
v___x_2967_ = lean_usize_of_nat(v___x_2960_);
lean_dec(v___x_2960_);
v___x_2968_ = lean_usize_of_nat(v___x_2961_);
v___x_2969_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__1_spec__8_spec__17___redArg(v_a_2911_, v_a_2912_, v_vs_2956_, v___x_2967_, v___x_2968_, v___x_2962_, v___y_2917_, v___y_2921_, v___y_2922_, v___y_2923_, v___y_2924_, v___y_2925_, v___y_2926_);
lean_dec_ref(v_vs_2956_);
return v___x_2969_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__1_spec__8_spec__16___boxed(lean_object** _args){
lean_object* v_a_2971_ = _args[0];
lean_object* v_a_2972_ = _args[1];
lean_object* v_x_2973_ = _args[2];
lean_object* v_x_2974_ = _args[3];
lean_object* v_x_2975_ = _args[4];
lean_object* v___y_2976_ = _args[5];
lean_object* v___y_2977_ = _args[6];
lean_object* v___y_2978_ = _args[7];
lean_object* v___y_2979_ = _args[8];
lean_object* v___y_2980_ = _args[9];
lean_object* v___y_2981_ = _args[10];
lean_object* v___y_2982_ = _args[11];
lean_object* v___y_2983_ = _args[12];
lean_object* v___y_2984_ = _args[13];
lean_object* v___y_2985_ = _args[14];
lean_object* v___y_2986_ = _args[15];
lean_object* v___y_2987_ = _args[16];
_start:
{
size_t v_x_130788__boxed_2988_; size_t v_x_130789__boxed_2989_; lean_object* v_res_2990_; 
v_x_130788__boxed_2988_ = lean_unbox_usize(v_x_2974_);
lean_dec(v_x_2974_);
v_x_130789__boxed_2989_ = lean_unbox_usize(v_x_2975_);
lean_dec(v_x_2975_);
v_res_2990_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__1_spec__8_spec__16(v_a_2971_, v_a_2972_, v_x_2973_, v_x_130788__boxed_2988_, v_x_130789__boxed_2989_, v___y_2976_, v___y_2977_, v___y_2978_, v___y_2979_, v___y_2980_, v___y_2981_, v___y_2982_, v___y_2983_, v___y_2984_, v___y_2985_, v___y_2986_);
lean_dec(v___y_2986_);
lean_dec_ref(v___y_2985_);
lean_dec(v___y_2984_);
lean_dec_ref(v___y_2983_);
lean_dec(v___y_2982_);
lean_dec_ref(v___y_2981_);
lean_dec(v___y_2980_);
lean_dec_ref(v___y_2979_);
lean_dec(v___y_2978_);
lean_dec(v___y_2977_);
lean_dec(v___y_2976_);
return v_res_2990_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__1_spec__8_spec__18(lean_object* v_a_2991_, lean_object* v_a_2992_, lean_object* v_t_2993_, lean_object* v___y_2994_, lean_object* v___y_2995_, lean_object* v___y_2996_, lean_object* v___y_2997_, lean_object* v___y_2998_, lean_object* v___y_2999_, lean_object* v___y_3000_, lean_object* v___y_3001_, lean_object* v___y_3002_, lean_object* v___y_3003_, lean_object* v___y_3004_){
_start:
{
lean_object* v_root_3006_; lean_object* v_tail_3007_; lean_object* v___x_3008_; 
v_root_3006_ = lean_ctor_get(v_t_2993_, 0);
lean_inc_ref(v_root_3006_);
v_tail_3007_ = lean_ctor_get(v_t_2993_, 1);
lean_inc_ref(v_tail_3007_);
lean_dec_ref(v_t_2993_);
lean_inc_ref(v_a_2992_);
lean_inc_ref(v_a_2991_);
v___x_3008_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__1_spec__8_spec__16_spec__22(v_a_2991_, v_a_2992_, v_root_3006_, v___y_2994_, v___y_2995_, v___y_2996_, v___y_2997_, v___y_2998_, v___y_2999_, v___y_3000_, v___y_3001_, v___y_3002_, v___y_3003_, v___y_3004_);
if (lean_obj_tag(v___x_3008_) == 0)
{
lean_object* v___x_3010_; uint8_t v_isShared_3011_; uint8_t v_isSharedCheck_3022_; 
v_isSharedCheck_3022_ = !lean_is_exclusive(v___x_3008_);
if (v_isSharedCheck_3022_ == 0)
{
lean_object* v_unused_3023_; 
v_unused_3023_ = lean_ctor_get(v___x_3008_, 0);
lean_dec(v_unused_3023_);
v___x_3010_ = v___x_3008_;
v_isShared_3011_ = v_isSharedCheck_3022_;
goto v_resetjp_3009_;
}
else
{
lean_dec(v___x_3008_);
v___x_3010_ = lean_box(0);
v_isShared_3011_ = v_isSharedCheck_3022_;
goto v_resetjp_3009_;
}
v_resetjp_3009_:
{
lean_object* v___x_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; uint8_t v___x_3015_; 
v___x_3012_ = lean_unsigned_to_nat(0u);
v___x_3013_ = lean_array_get_size(v_tail_3007_);
v___x_3014_ = lean_box(0);
v___x_3015_ = lean_nat_dec_lt(v___x_3012_, v___x_3013_);
if (v___x_3015_ == 0)
{
lean_object* v___x_3017_; 
lean_dec_ref(v_tail_3007_);
lean_dec_ref(v_a_2992_);
lean_dec_ref(v_a_2991_);
if (v_isShared_3011_ == 0)
{
lean_ctor_set(v___x_3010_, 0, v___x_3014_);
v___x_3017_ = v___x_3010_;
goto v_reusejp_3016_;
}
else
{
lean_object* v_reuseFailAlloc_3018_; 
v_reuseFailAlloc_3018_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3018_, 0, v___x_3014_);
v___x_3017_ = v_reuseFailAlloc_3018_;
goto v_reusejp_3016_;
}
v_reusejp_3016_:
{
return v___x_3017_;
}
}
else
{
size_t v___x_3019_; size_t v___x_3020_; lean_object* v___x_3021_; 
lean_del_object(v___x_3010_);
v___x_3019_ = ((size_t)0ULL);
v___x_3020_ = lean_usize_of_nat(v___x_3013_);
v___x_3021_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__1_spec__8_spec__17___redArg(v_a_2991_, v_a_2992_, v_tail_3007_, v___x_3019_, v___x_3020_, v___x_3014_, v___y_2995_, v___y_2999_, v___y_3000_, v___y_3001_, v___y_3002_, v___y_3003_, v___y_3004_);
lean_dec_ref(v_tail_3007_);
return v___x_3021_;
}
}
}
else
{
lean_dec_ref(v_tail_3007_);
lean_dec_ref(v_a_2992_);
lean_dec_ref(v_a_2991_);
return v___x_3008_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__1_spec__8_spec__18___boxed(lean_object* v_a_3024_, lean_object* v_a_3025_, lean_object* v_t_3026_, lean_object* v___y_3027_, lean_object* v___y_3028_, lean_object* v___y_3029_, lean_object* v___y_3030_, lean_object* v___y_3031_, lean_object* v___y_3032_, lean_object* v___y_3033_, lean_object* v___y_3034_, lean_object* v___y_3035_, lean_object* v___y_3036_, lean_object* v___y_3037_, lean_object* v___y_3038_){
_start:
{
lean_object* v_res_3039_; 
v_res_3039_ = l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__1_spec__8_spec__18(v_a_3024_, v_a_3025_, v_t_3026_, v___y_3027_, v___y_3028_, v___y_3029_, v___y_3030_, v___y_3031_, v___y_3032_, v___y_3033_, v___y_3034_, v___y_3035_, v___y_3036_, v___y_3037_);
lean_dec(v___y_3037_);
lean_dec_ref(v___y_3036_);
lean_dec(v___y_3035_);
lean_dec_ref(v___y_3034_);
lean_dec(v___y_3033_);
lean_dec_ref(v___y_3032_);
lean_dec(v___y_3031_);
lean_dec_ref(v___y_3030_);
lean_dec(v___y_3029_);
lean_dec(v___y_3028_);
lean_dec(v___y_3027_);
return v_res_3039_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__1_spec__8(lean_object* v_a_3040_, lean_object* v_a_3041_, lean_object* v_t_3042_, lean_object* v_start_3043_, lean_object* v___y_3044_, lean_object* v___y_3045_, lean_object* v___y_3046_, lean_object* v___y_3047_, lean_object* v___y_3048_, lean_object* v___y_3049_, lean_object* v___y_3050_, lean_object* v___y_3051_, lean_object* v___y_3052_, lean_object* v___y_3053_, lean_object* v___y_3054_){
_start:
{
lean_object* v___x_3056_; uint8_t v___x_3057_; 
v___x_3056_ = lean_unsigned_to_nat(0u);
v___x_3057_ = lean_nat_dec_eq(v_start_3043_, v___x_3056_);
if (v___x_3057_ == 0)
{
lean_object* v_root_3058_; lean_object* v_tail_3059_; size_t v_shift_3060_; lean_object* v_tailOff_3061_; uint8_t v___x_3062_; 
v_root_3058_ = lean_ctor_get(v_t_3042_, 0);
lean_inc_ref(v_root_3058_);
v_tail_3059_ = lean_ctor_get(v_t_3042_, 1);
lean_inc_ref(v_tail_3059_);
v_shift_3060_ = lean_ctor_get_usize(v_t_3042_, 4);
v_tailOff_3061_ = lean_ctor_get(v_t_3042_, 3);
lean_inc(v_tailOff_3061_);
lean_dec_ref(v_t_3042_);
v___x_3062_ = lean_nat_dec_le(v_tailOff_3061_, v_start_3043_);
if (v___x_3062_ == 0)
{
size_t v___x_3063_; lean_object* v___x_3064_; 
lean_dec(v_tailOff_3061_);
v___x_3063_ = lean_usize_of_nat(v_start_3043_);
lean_inc_ref(v_a_3041_);
lean_inc_ref(v_a_3040_);
v___x_3064_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__1_spec__8_spec__16(v_a_3040_, v_a_3041_, v_root_3058_, v___x_3063_, v_shift_3060_, v___y_3044_, v___y_3045_, v___y_3046_, v___y_3047_, v___y_3048_, v___y_3049_, v___y_3050_, v___y_3051_, v___y_3052_, v___y_3053_, v___y_3054_);
if (lean_obj_tag(v___x_3064_) == 0)
{
lean_object* v___x_3066_; uint8_t v_isShared_3067_; uint8_t v_isSharedCheck_3077_; 
v_isSharedCheck_3077_ = !lean_is_exclusive(v___x_3064_);
if (v_isSharedCheck_3077_ == 0)
{
lean_object* v_unused_3078_; 
v_unused_3078_ = lean_ctor_get(v___x_3064_, 0);
lean_dec(v_unused_3078_);
v___x_3066_ = v___x_3064_;
v_isShared_3067_ = v_isSharedCheck_3077_;
goto v_resetjp_3065_;
}
else
{
lean_dec(v___x_3064_);
v___x_3066_ = lean_box(0);
v_isShared_3067_ = v_isSharedCheck_3077_;
goto v_resetjp_3065_;
}
v_resetjp_3065_:
{
lean_object* v___x_3068_; lean_object* v___x_3069_; uint8_t v___x_3070_; 
v___x_3068_ = lean_array_get_size(v_tail_3059_);
v___x_3069_ = lean_box(0);
v___x_3070_ = lean_nat_dec_lt(v___x_3056_, v___x_3068_);
if (v___x_3070_ == 0)
{
lean_object* v___x_3072_; 
lean_dec_ref(v_tail_3059_);
lean_dec_ref(v_a_3041_);
lean_dec_ref(v_a_3040_);
if (v_isShared_3067_ == 0)
{
lean_ctor_set(v___x_3066_, 0, v___x_3069_);
v___x_3072_ = v___x_3066_;
goto v_reusejp_3071_;
}
else
{
lean_object* v_reuseFailAlloc_3073_; 
v_reuseFailAlloc_3073_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3073_, 0, v___x_3069_);
v___x_3072_ = v_reuseFailAlloc_3073_;
goto v_reusejp_3071_;
}
v_reusejp_3071_:
{
return v___x_3072_;
}
}
else
{
size_t v___x_3074_; size_t v___x_3075_; lean_object* v___x_3076_; 
lean_del_object(v___x_3066_);
v___x_3074_ = ((size_t)0ULL);
v___x_3075_ = lean_usize_of_nat(v___x_3068_);
v___x_3076_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__1_spec__8_spec__17___redArg(v_a_3040_, v_a_3041_, v_tail_3059_, v___x_3074_, v___x_3075_, v___x_3069_, v___y_3045_, v___y_3049_, v___y_3050_, v___y_3051_, v___y_3052_, v___y_3053_, v___y_3054_);
lean_dec_ref(v_tail_3059_);
return v___x_3076_;
}
}
}
else
{
lean_dec_ref(v_tail_3059_);
lean_dec_ref(v_a_3041_);
lean_dec_ref(v_a_3040_);
return v___x_3064_;
}
}
else
{
lean_object* v___x_3079_; lean_object* v___x_3080_; lean_object* v___x_3081_; uint8_t v___x_3082_; 
lean_dec_ref(v_root_3058_);
v___x_3079_ = lean_nat_sub(v_start_3043_, v_tailOff_3061_);
lean_dec(v_tailOff_3061_);
v___x_3080_ = lean_array_get_size(v_tail_3059_);
v___x_3081_ = lean_box(0);
v___x_3082_ = lean_nat_dec_lt(v___x_3079_, v___x_3080_);
if (v___x_3082_ == 0)
{
lean_object* v___x_3083_; 
lean_dec(v___x_3079_);
lean_dec_ref(v_tail_3059_);
lean_dec_ref(v_a_3041_);
lean_dec_ref(v_a_3040_);
v___x_3083_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3083_, 0, v___x_3081_);
return v___x_3083_;
}
else
{
size_t v___x_3084_; size_t v___x_3085_; lean_object* v___x_3086_; 
v___x_3084_ = lean_usize_of_nat(v___x_3079_);
lean_dec(v___x_3079_);
v___x_3085_ = lean_usize_of_nat(v___x_3080_);
v___x_3086_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__1_spec__8_spec__17___redArg(v_a_3040_, v_a_3041_, v_tail_3059_, v___x_3084_, v___x_3085_, v___x_3081_, v___y_3045_, v___y_3049_, v___y_3050_, v___y_3051_, v___y_3052_, v___y_3053_, v___y_3054_);
lean_dec_ref(v_tail_3059_);
return v___x_3086_;
}
}
}
else
{
lean_object* v___x_3087_; 
v___x_3087_ = l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__1_spec__8_spec__18(v_a_3040_, v_a_3041_, v_t_3042_, v___y_3044_, v___y_3045_, v___y_3046_, v___y_3047_, v___y_3048_, v___y_3049_, v___y_3050_, v___y_3051_, v___y_3052_, v___y_3053_, v___y_3054_);
return v___x_3087_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__1_spec__8___boxed(lean_object* v_a_3088_, lean_object* v_a_3089_, lean_object* v_t_3090_, lean_object* v_start_3091_, lean_object* v___y_3092_, lean_object* v___y_3093_, lean_object* v___y_3094_, lean_object* v___y_3095_, lean_object* v___y_3096_, lean_object* v___y_3097_, lean_object* v___y_3098_, lean_object* v___y_3099_, lean_object* v___y_3100_, lean_object* v___y_3101_, lean_object* v___y_3102_, lean_object* v___y_3103_){
_start:
{
lean_object* v_res_3104_; 
v_res_3104_ = l_Lean_PersistentArray_forM___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__1_spec__8(v_a_3088_, v_a_3089_, v_t_3090_, v_start_3091_, v___y_3092_, v___y_3093_, v___y_3094_, v___y_3095_, v___y_3096_, v___y_3097_, v___y_3098_, v___y_3099_, v___y_3100_, v___y_3101_, v___y_3102_);
lean_dec(v___y_3102_);
lean_dec_ref(v___y_3101_);
lean_dec(v___y_3100_);
lean_dec_ref(v___y_3099_);
lean_dec(v___y_3098_);
lean_dec_ref(v___y_3097_);
lean_dec(v___y_3096_);
lean_dec_ref(v___y_3095_);
lean_dec(v___y_3094_);
lean_dec(v___y_3093_);
lean_dec(v___y_3092_);
lean_dec(v_start_3091_);
return v_res_3104_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0_spec__0_spec__1_spec__5___redArg(lean_object* v_keys_3105_, lean_object* v_i_3106_, lean_object* v_k_3107_){
_start:
{
lean_object* v___x_3108_; uint8_t v___x_3109_; 
v___x_3108_ = lean_array_get_size(v_keys_3105_);
v___x_3109_ = lean_nat_dec_lt(v_i_3106_, v___x_3108_);
if (v___x_3109_ == 0)
{
lean_dec(v_i_3106_);
return v___x_3109_;
}
else
{
lean_object* v_k_x27_3110_; size_t v___x_3111_; size_t v___x_3112_; uint8_t v___x_3113_; 
v_k_x27_3110_ = lean_array_fget_borrowed(v_keys_3105_, v_i_3106_);
v___x_3111_ = lean_ptr_addr(v_k_3107_);
v___x_3112_ = lean_ptr_addr(v_k_x27_3110_);
v___x_3113_ = lean_usize_dec_eq(v___x_3111_, v___x_3112_);
if (v___x_3113_ == 0)
{
lean_object* v___x_3114_; lean_object* v___x_3115_; 
v___x_3114_ = lean_unsigned_to_nat(1u);
v___x_3115_ = lean_nat_add(v_i_3106_, v___x_3114_);
lean_dec(v_i_3106_);
v_i_3106_ = v___x_3115_;
goto _start;
}
else
{
lean_dec(v_i_3106_);
return v___x_3109_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0_spec__0_spec__1_spec__5___redArg___boxed(lean_object* v_keys_3117_, lean_object* v_i_3118_, lean_object* v_k_3119_){
_start:
{
uint8_t v_res_3120_; lean_object* v_r_3121_; 
v_res_3120_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0_spec__0_spec__1_spec__5___redArg(v_keys_3117_, v_i_3118_, v_k_3119_);
lean_dec_ref(v_k_3119_);
lean_dec_ref(v_keys_3117_);
v_r_3121_ = lean_box(v_res_3120_);
return v_r_3121_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0_spec__0_spec__1___redArg(lean_object* v_x_3122_, size_t v_x_3123_, lean_object* v_x_3124_){
_start:
{
if (lean_obj_tag(v_x_3122_) == 0)
{
lean_object* v_es_3125_; lean_object* v___x_3126_; size_t v___x_3127_; size_t v___x_3128_; lean_object* v_j_3129_; lean_object* v___x_3130_; 
v_es_3125_ = lean_ctor_get(v_x_3122_, 0);
v___x_3126_ = lean_box(2);
v___x_3127_ = ((size_t)31ULL);
v___x_3128_ = lean_usize_land(v_x_3123_, v___x_3127_);
v_j_3129_ = lean_usize_to_nat(v___x_3128_);
v___x_3130_ = lean_array_get_borrowed(v___x_3126_, v_es_3125_, v_j_3129_);
lean_dec(v_j_3129_);
switch(lean_obj_tag(v___x_3130_))
{
case 0:
{
lean_object* v_key_3131_; size_t v___x_3132_; size_t v___x_3133_; uint8_t v___x_3134_; 
v_key_3131_ = lean_ctor_get(v___x_3130_, 0);
v___x_3132_ = lean_ptr_addr(v_x_3124_);
v___x_3133_ = lean_ptr_addr(v_key_3131_);
v___x_3134_ = lean_usize_dec_eq(v___x_3132_, v___x_3133_);
return v___x_3134_;
}
case 1:
{
lean_object* v_node_3135_; size_t v___x_3136_; size_t v___x_3137_; 
v_node_3135_ = lean_ctor_get(v___x_3130_, 0);
v___x_3136_ = ((size_t)5ULL);
v___x_3137_ = lean_usize_shift_right(v_x_3123_, v___x_3136_);
v_x_3122_ = v_node_3135_;
v_x_3123_ = v___x_3137_;
goto _start;
}
default: 
{
uint8_t v___x_3139_; 
v___x_3139_ = 0;
return v___x_3139_;
}
}
}
else
{
lean_object* v_ks_3140_; lean_object* v___x_3141_; uint8_t v___x_3142_; 
v_ks_3140_ = lean_ctor_get(v_x_3122_, 0);
v___x_3141_ = lean_unsigned_to_nat(0u);
v___x_3142_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0_spec__0_spec__1_spec__5___redArg(v_ks_3140_, v___x_3141_, v_x_3124_);
return v___x_3142_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_3143_, lean_object* v_x_3144_, lean_object* v_x_3145_){
_start:
{
size_t v_x_131116__boxed_3146_; uint8_t v_res_3147_; lean_object* v_r_3148_; 
v_x_131116__boxed_3146_ = lean_unbox_usize(v_x_3144_);
lean_dec(v_x_3144_);
v_res_3147_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0_spec__0_spec__1___redArg(v_x_3143_, v_x_131116__boxed_3146_, v_x_3145_);
lean_dec_ref(v_x_3145_);
lean_dec_ref(v_x_3143_);
v_r_3148_ = lean_box(v_res_3147_);
return v_r_3148_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0_spec__0___redArg(lean_object* v_x_3149_, lean_object* v_x_3150_){
_start:
{
size_t v___x_3151_; size_t v___x_3152_; size_t v___x_3153_; uint64_t v___x_3154_; size_t v___x_3155_; uint8_t v___x_3156_; 
v___x_3151_ = lean_ptr_addr(v_x_3150_);
v___x_3152_ = ((size_t)3ULL);
v___x_3153_ = lean_usize_shift_right(v___x_3151_, v___x_3152_);
v___x_3154_ = lean_usize_to_uint64(v___x_3153_);
v___x_3155_ = lean_uint64_to_usize(v___x_3154_);
v___x_3156_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0_spec__0_spec__1___redArg(v_x_3149_, v___x_3155_, v_x_3150_);
return v___x_3156_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0_spec__0___redArg___boxed(lean_object* v_x_3157_, lean_object* v_x_3158_){
_start:
{
uint8_t v_res_3159_; lean_object* v_r_3160_; 
v_res_3159_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0_spec__0___redArg(v_x_3157_, v_x_3158_);
lean_dec_ref(v_x_3158_);
lean_dec_ref(v_x_3157_);
v_r_3160_ = lean_box(v_res_3159_);
return v_r_3160_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getIntCastFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__1_spec__7___lam__0(lean_object* v_a_3161_, lean_object* v_s_3162_){
_start:
{
lean_object* v_id_3163_; lean_object* v_type_3164_; lean_object* v_u_3165_; lean_object* v_ringInst_3166_; lean_object* v_semiringInst_3167_; lean_object* v_charInst_x3f_3168_; uint8_t v_symbolicChar_3169_; lean_object* v_addFn_x3f_3170_; lean_object* v_mulFn_x3f_3171_; lean_object* v_subFn_x3f_3172_; lean_object* v_negFn_x3f_3173_; lean_object* v_powFn_x3f_3174_; lean_object* v_natCastFn_x3f_3175_; lean_object* v_natSMulFn_x3f_3176_; lean_object* v_intSMulFn_x3f_3177_; lean_object* v_one_x3f_3178_; lean_object* v___x_3180_; uint8_t v_isShared_3181_; uint8_t v_isSharedCheck_3186_; 
v_id_3163_ = lean_ctor_get(v_s_3162_, 0);
v_type_3164_ = lean_ctor_get(v_s_3162_, 1);
v_u_3165_ = lean_ctor_get(v_s_3162_, 2);
v_ringInst_3166_ = lean_ctor_get(v_s_3162_, 3);
v_semiringInst_3167_ = lean_ctor_get(v_s_3162_, 4);
v_charInst_x3f_3168_ = lean_ctor_get(v_s_3162_, 5);
v_symbolicChar_3169_ = lean_ctor_get_uint8(v_s_3162_, sizeof(void*)*16);
v_addFn_x3f_3170_ = lean_ctor_get(v_s_3162_, 6);
v_mulFn_x3f_3171_ = lean_ctor_get(v_s_3162_, 7);
v_subFn_x3f_3172_ = lean_ctor_get(v_s_3162_, 8);
v_negFn_x3f_3173_ = lean_ctor_get(v_s_3162_, 9);
v_powFn_x3f_3174_ = lean_ctor_get(v_s_3162_, 10);
v_natCastFn_x3f_3175_ = lean_ctor_get(v_s_3162_, 12);
v_natSMulFn_x3f_3176_ = lean_ctor_get(v_s_3162_, 13);
v_intSMulFn_x3f_3177_ = lean_ctor_get(v_s_3162_, 14);
v_one_x3f_3178_ = lean_ctor_get(v_s_3162_, 15);
v_isSharedCheck_3186_ = !lean_is_exclusive(v_s_3162_);
if (v_isSharedCheck_3186_ == 0)
{
lean_object* v_unused_3187_; 
v_unused_3187_ = lean_ctor_get(v_s_3162_, 11);
lean_dec(v_unused_3187_);
v___x_3180_ = v_s_3162_;
v_isShared_3181_ = v_isSharedCheck_3186_;
goto v_resetjp_3179_;
}
else
{
lean_inc(v_one_x3f_3178_);
lean_inc(v_intSMulFn_x3f_3177_);
lean_inc(v_natSMulFn_x3f_3176_);
lean_inc(v_natCastFn_x3f_3175_);
lean_inc(v_powFn_x3f_3174_);
lean_inc(v_negFn_x3f_3173_);
lean_inc(v_subFn_x3f_3172_);
lean_inc(v_mulFn_x3f_3171_);
lean_inc(v_addFn_x3f_3170_);
lean_inc(v_charInst_x3f_3168_);
lean_inc(v_semiringInst_3167_);
lean_inc(v_ringInst_3166_);
lean_inc(v_u_3165_);
lean_inc(v_type_3164_);
lean_inc(v_id_3163_);
lean_dec(v_s_3162_);
v___x_3180_ = lean_box(0);
v_isShared_3181_ = v_isSharedCheck_3186_;
goto v_resetjp_3179_;
}
v_resetjp_3179_:
{
lean_object* v___x_3182_; lean_object* v___x_3184_; 
v___x_3182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3182_, 0, v_a_3161_);
if (v_isShared_3181_ == 0)
{
lean_ctor_set(v___x_3180_, 11, v___x_3182_);
v___x_3184_ = v___x_3180_;
goto v_reusejp_3183_;
}
else
{
lean_object* v_reuseFailAlloc_3185_; 
v_reuseFailAlloc_3185_ = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(v_reuseFailAlloc_3185_, 0, v_id_3163_);
lean_ctor_set(v_reuseFailAlloc_3185_, 1, v_type_3164_);
lean_ctor_set(v_reuseFailAlloc_3185_, 2, v_u_3165_);
lean_ctor_set(v_reuseFailAlloc_3185_, 3, v_ringInst_3166_);
lean_ctor_set(v_reuseFailAlloc_3185_, 4, v_semiringInst_3167_);
lean_ctor_set(v_reuseFailAlloc_3185_, 5, v_charInst_x3f_3168_);
lean_ctor_set(v_reuseFailAlloc_3185_, 6, v_addFn_x3f_3170_);
lean_ctor_set(v_reuseFailAlloc_3185_, 7, v_mulFn_x3f_3171_);
lean_ctor_set(v_reuseFailAlloc_3185_, 8, v_subFn_x3f_3172_);
lean_ctor_set(v_reuseFailAlloc_3185_, 9, v_negFn_x3f_3173_);
lean_ctor_set(v_reuseFailAlloc_3185_, 10, v_powFn_x3f_3174_);
lean_ctor_set(v_reuseFailAlloc_3185_, 11, v___x_3182_);
lean_ctor_set(v_reuseFailAlloc_3185_, 12, v_natCastFn_x3f_3175_);
lean_ctor_set(v_reuseFailAlloc_3185_, 13, v_natSMulFn_x3f_3176_);
lean_ctor_set(v_reuseFailAlloc_3185_, 14, v_intSMulFn_x3f_3177_);
lean_ctor_set(v_reuseFailAlloc_3185_, 15, v_one_x3f_3178_);
lean_ctor_set_uint8(v_reuseFailAlloc_3185_, sizeof(void*)*16, v_symbolicChar_3169_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getIntCastFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__1_spec__7(lean_object* v___y_3199_, lean_object* v___y_3200_, lean_object* v___y_3201_, lean_object* v___y_3202_, lean_object* v___y_3203_, lean_object* v___y_3204_, lean_object* v___y_3205_, lean_object* v___y_3206_, lean_object* v___y_3207_, lean_object* v___y_3208_, lean_object* v___y_3209_){
_start:
{
lean_object* v___x_3211_; 
v___x_3211_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing(v___y_3199_, v___y_3200_, v___y_3201_, v___y_3202_, v___y_3203_, v___y_3204_, v___y_3205_, v___y_3206_, v___y_3207_, v___y_3208_, v___y_3209_);
if (lean_obj_tag(v___x_3211_) == 0)
{
lean_object* v_a_3212_; lean_object* v___x_3214_; uint8_t v_isShared_3215_; uint8_t v_isSharedCheck_3287_; 
v_a_3212_ = lean_ctor_get(v___x_3211_, 0);
v_isSharedCheck_3287_ = !lean_is_exclusive(v___x_3211_);
if (v_isSharedCheck_3287_ == 0)
{
v___x_3214_ = v___x_3211_;
v_isShared_3215_ = v_isSharedCheck_3287_;
goto v_resetjp_3213_;
}
else
{
lean_inc(v_a_3212_);
lean_dec(v___x_3211_);
v___x_3214_ = lean_box(0);
v_isShared_3215_ = v_isSharedCheck_3287_;
goto v_resetjp_3213_;
}
v_resetjp_3213_:
{
lean_object* v_intCastFn_x3f_3216_; 
v_intCastFn_x3f_3216_ = lean_ctor_get(v_a_3212_, 11);
if (lean_obj_tag(v_intCastFn_x3f_3216_) == 1)
{
lean_object* v_val_3217_; lean_object* v___x_3219_; 
lean_inc_ref(v_intCastFn_x3f_3216_);
lean_dec(v_a_3212_);
v_val_3217_ = lean_ctor_get(v_intCastFn_x3f_3216_, 0);
lean_inc(v_val_3217_);
lean_dec_ref_known(v_intCastFn_x3f_3216_, 1);
if (v_isShared_3215_ == 0)
{
lean_ctor_set(v___x_3214_, 0, v_val_3217_);
v___x_3219_ = v___x_3214_;
goto v_reusejp_3218_;
}
else
{
lean_object* v_reuseFailAlloc_3220_; 
v_reuseFailAlloc_3220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3220_, 0, v_val_3217_);
v___x_3219_ = v_reuseFailAlloc_3220_;
goto v_reusejp_3218_;
}
v_reusejp_3218_:
{
return v___x_3219_;
}
}
else
{
lean_object* v_type_3221_; lean_object* v_u_3222_; lean_object* v_ringInst_3223_; lean_object* v___x_3224_; lean_object* v___x_3225_; lean_object* v___x_3226_; lean_object* v___x_3227_; lean_object* v_inst_x27_3228_; lean_object* v_inst_3230_; lean_object* v___y_3231_; lean_object* v___y_3232_; lean_object* v___y_3233_; lean_object* v___y_3234_; lean_object* v___y_3235_; lean_object* v___y_3236_; lean_object* v___y_3237_; lean_object* v___x_3263_; lean_object* v___x_3264_; lean_object* v_instType_3265_; lean_object* v___x_3266_; 
lean_del_object(v___x_3214_);
v_type_3221_ = lean_ctor_get(v_a_3212_, 1);
lean_inc_ref_n(v_type_3221_, 3);
v_u_3222_ = lean_ctor_get(v_a_3212_, 2);
lean_inc(v_u_3222_);
v_ringInst_3223_ = lean_ctor_get(v_a_3212_, 3);
lean_inc_ref(v_ringInst_3223_);
lean_dec(v_a_3212_);
v___x_3224_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getIntCastFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__1_spec__7___closed__0));
v___x_3225_ = lean_box(0);
v___x_3226_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3226_, 0, v_u_3222_);
lean_ctor_set(v___x_3226_, 1, v___x_3225_);
lean_inc_ref_n(v___x_3226_, 2);
v___x_3227_ = l_Lean_mkConst(v___x_3224_, v___x_3226_);
v_inst_x27_3228_ = l_Lean_mkAppB(v___x_3227_, v_type_3221_, v_ringInst_3223_);
v___x_3263_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getIntCastFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__1_spec__7___closed__1));
v___x_3264_ = l_Lean_mkConst(v___x_3263_, v___x_3226_);
v_instType_3265_ = l_Lean_Expr_app___override(v___x_3264_, v_type_3221_);
v___x_3266_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v_instType_3265_, v___y_3205_, v___y_3206_, v___y_3207_, v___y_3208_, v___y_3209_);
if (lean_obj_tag(v___x_3266_) == 0)
{
lean_object* v_a_3267_; 
v_a_3267_ = lean_ctor_get(v___x_3266_, 0);
lean_inc(v_a_3267_);
lean_dec_ref_known(v___x_3266_, 1);
if (lean_obj_tag(v_a_3267_) == 0)
{
v_inst_3230_ = v_inst_x27_3228_;
v___y_3231_ = v___y_3199_;
v___y_3232_ = v___y_3204_;
v___y_3233_ = v___y_3205_;
v___y_3234_ = v___y_3206_;
v___y_3235_ = v___y_3207_;
v___y_3236_ = v___y_3208_;
v___y_3237_ = v___y_3209_;
goto v___jp_3229_;
}
else
{
lean_object* v_val_3268_; lean_object* v___x_3269_; lean_object* v___x_3270_; 
v_val_3268_ = lean_ctor_get(v_a_3267_, 0);
lean_inc_n(v_val_3268_, 2);
lean_dec_ref_known(v_a_3267_, 1);
v___x_3269_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getIntCastFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__1_spec__7___closed__3));
v___x_3270_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst(v___x_3269_, v_val_3268_, v_inst_x27_3228_, v___y_3206_, v___y_3207_, v___y_3208_, v___y_3209_);
if (lean_obj_tag(v___x_3270_) == 0)
{
lean_dec_ref_known(v___x_3270_, 1);
v_inst_3230_ = v_val_3268_;
v___y_3231_ = v___y_3199_;
v___y_3232_ = v___y_3204_;
v___y_3233_ = v___y_3205_;
v___y_3234_ = v___y_3206_;
v___y_3235_ = v___y_3207_;
v___y_3236_ = v___y_3208_;
v___y_3237_ = v___y_3209_;
goto v___jp_3229_;
}
else
{
lean_object* v_a_3271_; lean_object* v___x_3273_; uint8_t v_isShared_3274_; uint8_t v_isSharedCheck_3278_; 
lean_dec(v_val_3268_);
lean_dec_ref_known(v___x_3226_, 2);
lean_dec_ref(v_type_3221_);
v_a_3271_ = lean_ctor_get(v___x_3270_, 0);
v_isSharedCheck_3278_ = !lean_is_exclusive(v___x_3270_);
if (v_isSharedCheck_3278_ == 0)
{
v___x_3273_ = v___x_3270_;
v_isShared_3274_ = v_isSharedCheck_3278_;
goto v_resetjp_3272_;
}
else
{
lean_inc(v_a_3271_);
lean_dec(v___x_3270_);
v___x_3273_ = lean_box(0);
v_isShared_3274_ = v_isSharedCheck_3278_;
goto v_resetjp_3272_;
}
v_resetjp_3272_:
{
lean_object* v___x_3276_; 
if (v_isShared_3274_ == 0)
{
v___x_3276_ = v___x_3273_;
goto v_reusejp_3275_;
}
else
{
lean_object* v_reuseFailAlloc_3277_; 
v_reuseFailAlloc_3277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3277_, 0, v_a_3271_);
v___x_3276_ = v_reuseFailAlloc_3277_;
goto v_reusejp_3275_;
}
v_reusejp_3275_:
{
return v___x_3276_;
}
}
}
}
}
else
{
lean_object* v_a_3279_; lean_object* v___x_3281_; uint8_t v_isShared_3282_; uint8_t v_isSharedCheck_3286_; 
lean_dec_ref(v_inst_x27_3228_);
lean_dec_ref_known(v___x_3226_, 2);
lean_dec_ref(v_type_3221_);
v_a_3279_ = lean_ctor_get(v___x_3266_, 0);
v_isSharedCheck_3286_ = !lean_is_exclusive(v___x_3266_);
if (v_isSharedCheck_3286_ == 0)
{
v___x_3281_ = v___x_3266_;
v_isShared_3282_ = v_isSharedCheck_3286_;
goto v_resetjp_3280_;
}
else
{
lean_inc(v_a_3279_);
lean_dec(v___x_3266_);
v___x_3281_ = lean_box(0);
v_isShared_3282_ = v_isSharedCheck_3286_;
goto v_resetjp_3280_;
}
v_resetjp_3280_:
{
lean_object* v___x_3284_; 
if (v_isShared_3282_ == 0)
{
v___x_3284_ = v___x_3281_;
goto v_reusejp_3283_;
}
else
{
lean_object* v_reuseFailAlloc_3285_; 
v_reuseFailAlloc_3285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3285_, 0, v_a_3279_);
v___x_3284_ = v_reuseFailAlloc_3285_;
goto v_reusejp_3283_;
}
v_reusejp_3283_:
{
return v___x_3284_;
}
}
}
v___jp_3229_:
{
lean_object* v___x_3238_; lean_object* v___x_3239_; lean_object* v___x_3240_; lean_object* v___x_3241_; 
v___x_3238_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__2));
v___x_3239_ = l_Lean_mkConst(v___x_3238_, v___x_3226_);
v___x_3240_ = l_Lean_mkAppB(v___x_3239_, v_type_3221_, v_inst_3230_);
v___x_3241_ = l_Lean_Meta_Sym_canon(v___x_3240_, v___y_3232_, v___y_3233_, v___y_3234_, v___y_3235_, v___y_3236_, v___y_3237_);
if (lean_obj_tag(v___x_3241_) == 0)
{
lean_object* v_a_3242_; lean_object* v___x_3243_; 
v_a_3242_ = lean_ctor_get(v___x_3241_, 0);
lean_inc(v_a_3242_);
lean_dec_ref_known(v___x_3241_, 1);
v___x_3243_ = l_Lean_Meta_Sym_shareCommon(v_a_3242_, v___y_3232_, v___y_3233_, v___y_3234_, v___y_3235_, v___y_3236_, v___y_3237_);
if (lean_obj_tag(v___x_3243_) == 0)
{
lean_object* v_a_3244_; lean_object* v___f_3245_; lean_object* v___x_3246_; 
v_a_3244_ = lean_ctor_get(v___x_3243_, 0);
lean_inc_n(v_a_3244_, 2);
lean_dec_ref_known(v___x_3243_, 1);
v___f_3245_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getIntCastFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__1_spec__7___lam__0), 2, 1);
lean_closure_set(v___f_3245_, 0, v_a_3244_);
v___x_3246_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_modifyRing___redArg(v___f_3245_, v___y_3231_, v___y_3233_);
if (lean_obj_tag(v___x_3246_) == 0)
{
lean_object* v___x_3248_; uint8_t v_isShared_3249_; uint8_t v_isSharedCheck_3253_; 
v_isSharedCheck_3253_ = !lean_is_exclusive(v___x_3246_);
if (v_isSharedCheck_3253_ == 0)
{
lean_object* v_unused_3254_; 
v_unused_3254_ = lean_ctor_get(v___x_3246_, 0);
lean_dec(v_unused_3254_);
v___x_3248_ = v___x_3246_;
v_isShared_3249_ = v_isSharedCheck_3253_;
goto v_resetjp_3247_;
}
else
{
lean_dec(v___x_3246_);
v___x_3248_ = lean_box(0);
v_isShared_3249_ = v_isSharedCheck_3253_;
goto v_resetjp_3247_;
}
v_resetjp_3247_:
{
lean_object* v___x_3251_; 
if (v_isShared_3249_ == 0)
{
lean_ctor_set(v___x_3248_, 0, v_a_3244_);
v___x_3251_ = v___x_3248_;
goto v_reusejp_3250_;
}
else
{
lean_object* v_reuseFailAlloc_3252_; 
v_reuseFailAlloc_3252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3252_, 0, v_a_3244_);
v___x_3251_ = v_reuseFailAlloc_3252_;
goto v_reusejp_3250_;
}
v_reusejp_3250_:
{
return v___x_3251_;
}
}
}
else
{
lean_object* v_a_3255_; lean_object* v___x_3257_; uint8_t v_isShared_3258_; uint8_t v_isSharedCheck_3262_; 
lean_dec(v_a_3244_);
v_a_3255_ = lean_ctor_get(v___x_3246_, 0);
v_isSharedCheck_3262_ = !lean_is_exclusive(v___x_3246_);
if (v_isSharedCheck_3262_ == 0)
{
v___x_3257_ = v___x_3246_;
v_isShared_3258_ = v_isSharedCheck_3262_;
goto v_resetjp_3256_;
}
else
{
lean_inc(v_a_3255_);
lean_dec(v___x_3246_);
v___x_3257_ = lean_box(0);
v_isShared_3258_ = v_isSharedCheck_3262_;
goto v_resetjp_3256_;
}
v_resetjp_3256_:
{
lean_object* v___x_3260_; 
if (v_isShared_3258_ == 0)
{
v___x_3260_ = v___x_3257_;
goto v_reusejp_3259_;
}
else
{
lean_object* v_reuseFailAlloc_3261_; 
v_reuseFailAlloc_3261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3261_, 0, v_a_3255_);
v___x_3260_ = v_reuseFailAlloc_3261_;
goto v_reusejp_3259_;
}
v_reusejp_3259_:
{
return v___x_3260_;
}
}
}
}
else
{
return v___x_3243_;
}
}
else
{
return v___x_3241_;
}
}
}
}
}
else
{
lean_object* v_a_3288_; lean_object* v___x_3290_; uint8_t v_isShared_3291_; uint8_t v_isSharedCheck_3295_; 
v_a_3288_ = lean_ctor_get(v___x_3211_, 0);
v_isSharedCheck_3295_ = !lean_is_exclusive(v___x_3211_);
if (v_isSharedCheck_3295_ == 0)
{
v___x_3290_ = v___x_3211_;
v_isShared_3291_ = v_isSharedCheck_3295_;
goto v_resetjp_3289_;
}
else
{
lean_inc(v_a_3288_);
lean_dec(v___x_3211_);
v___x_3290_ = lean_box(0);
v_isShared_3291_ = v_isSharedCheck_3295_;
goto v_resetjp_3289_;
}
v_resetjp_3289_:
{
lean_object* v___x_3293_; 
if (v_isShared_3291_ == 0)
{
v___x_3293_ = v___x_3290_;
goto v_reusejp_3292_;
}
else
{
lean_object* v_reuseFailAlloc_3294_; 
v_reuseFailAlloc_3294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3294_, 0, v_a_3288_);
v___x_3293_ = v_reuseFailAlloc_3294_;
goto v_reusejp_3292_;
}
v_reusejp_3292_:
{
return v___x_3293_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getIntCastFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__1_spec__7___boxed(lean_object* v___y_3296_, lean_object* v___y_3297_, lean_object* v___y_3298_, lean_object* v___y_3299_, lean_object* v___y_3300_, lean_object* v___y_3301_, lean_object* v___y_3302_, lean_object* v___y_3303_, lean_object* v___y_3304_, lean_object* v___y_3305_, lean_object* v___y_3306_, lean_object* v___y_3307_){
_start:
{
lean_object* v_res_3308_; 
v_res_3308_ = l_Lean_Meta_Sym_Arith_getIntCastFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__1_spec__7(v___y_3296_, v___y_3297_, v___y_3298_, v___y_3299_, v___y_3300_, v___y_3301_, v___y_3302_, v___y_3303_, v___y_3304_, v___y_3305_, v___y_3306_);
lean_dec(v___y_3306_);
lean_dec_ref(v___y_3305_);
lean_dec(v___y_3304_);
lean_dec_ref(v___y_3303_);
lean_dec(v___y_3302_);
lean_dec_ref(v___y_3301_);
lean_dec(v___y_3300_);
lean_dec_ref(v___y_3299_);
lean_dec(v___y_3298_);
lean_dec(v___y_3297_);
lean_dec(v___y_3296_);
return v_res_3308_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatCastFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__1_spec__6___lam__0(lean_object* v_a_3309_, lean_object* v_s_3310_){
_start:
{
lean_object* v_id_3311_; lean_object* v_type_3312_; lean_object* v_u_3313_; lean_object* v_ringInst_3314_; lean_object* v_semiringInst_3315_; lean_object* v_charInst_x3f_3316_; uint8_t v_symbolicChar_3317_; lean_object* v_addFn_x3f_3318_; lean_object* v_mulFn_x3f_3319_; lean_object* v_subFn_x3f_3320_; lean_object* v_negFn_x3f_3321_; lean_object* v_powFn_x3f_3322_; lean_object* v_intCastFn_x3f_3323_; lean_object* v_natSMulFn_x3f_3324_; lean_object* v_intSMulFn_x3f_3325_; lean_object* v_one_x3f_3326_; lean_object* v___x_3328_; uint8_t v_isShared_3329_; uint8_t v_isSharedCheck_3334_; 
v_id_3311_ = lean_ctor_get(v_s_3310_, 0);
v_type_3312_ = lean_ctor_get(v_s_3310_, 1);
v_u_3313_ = lean_ctor_get(v_s_3310_, 2);
v_ringInst_3314_ = lean_ctor_get(v_s_3310_, 3);
v_semiringInst_3315_ = lean_ctor_get(v_s_3310_, 4);
v_charInst_x3f_3316_ = lean_ctor_get(v_s_3310_, 5);
v_symbolicChar_3317_ = lean_ctor_get_uint8(v_s_3310_, sizeof(void*)*16);
v_addFn_x3f_3318_ = lean_ctor_get(v_s_3310_, 6);
v_mulFn_x3f_3319_ = lean_ctor_get(v_s_3310_, 7);
v_subFn_x3f_3320_ = lean_ctor_get(v_s_3310_, 8);
v_negFn_x3f_3321_ = lean_ctor_get(v_s_3310_, 9);
v_powFn_x3f_3322_ = lean_ctor_get(v_s_3310_, 10);
v_intCastFn_x3f_3323_ = lean_ctor_get(v_s_3310_, 11);
v_natSMulFn_x3f_3324_ = lean_ctor_get(v_s_3310_, 13);
v_intSMulFn_x3f_3325_ = lean_ctor_get(v_s_3310_, 14);
v_one_x3f_3326_ = lean_ctor_get(v_s_3310_, 15);
v_isSharedCheck_3334_ = !lean_is_exclusive(v_s_3310_);
if (v_isSharedCheck_3334_ == 0)
{
lean_object* v_unused_3335_; 
v_unused_3335_ = lean_ctor_get(v_s_3310_, 12);
lean_dec(v_unused_3335_);
v___x_3328_ = v_s_3310_;
v_isShared_3329_ = v_isSharedCheck_3334_;
goto v_resetjp_3327_;
}
else
{
lean_inc(v_one_x3f_3326_);
lean_inc(v_intSMulFn_x3f_3325_);
lean_inc(v_natSMulFn_x3f_3324_);
lean_inc(v_intCastFn_x3f_3323_);
lean_inc(v_powFn_x3f_3322_);
lean_inc(v_negFn_x3f_3321_);
lean_inc(v_subFn_x3f_3320_);
lean_inc(v_mulFn_x3f_3319_);
lean_inc(v_addFn_x3f_3318_);
lean_inc(v_charInst_x3f_3316_);
lean_inc(v_semiringInst_3315_);
lean_inc(v_ringInst_3314_);
lean_inc(v_u_3313_);
lean_inc(v_type_3312_);
lean_inc(v_id_3311_);
lean_dec(v_s_3310_);
v___x_3328_ = lean_box(0);
v_isShared_3329_ = v_isSharedCheck_3334_;
goto v_resetjp_3327_;
}
v_resetjp_3327_:
{
lean_object* v___x_3330_; lean_object* v___x_3332_; 
v___x_3330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3330_, 0, v_a_3309_);
if (v_isShared_3329_ == 0)
{
lean_ctor_set(v___x_3328_, 12, v___x_3330_);
v___x_3332_ = v___x_3328_;
goto v_reusejp_3331_;
}
else
{
lean_object* v_reuseFailAlloc_3333_; 
v_reuseFailAlloc_3333_ = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(v_reuseFailAlloc_3333_, 0, v_id_3311_);
lean_ctor_set(v_reuseFailAlloc_3333_, 1, v_type_3312_);
lean_ctor_set(v_reuseFailAlloc_3333_, 2, v_u_3313_);
lean_ctor_set(v_reuseFailAlloc_3333_, 3, v_ringInst_3314_);
lean_ctor_set(v_reuseFailAlloc_3333_, 4, v_semiringInst_3315_);
lean_ctor_set(v_reuseFailAlloc_3333_, 5, v_charInst_x3f_3316_);
lean_ctor_set(v_reuseFailAlloc_3333_, 6, v_addFn_x3f_3318_);
lean_ctor_set(v_reuseFailAlloc_3333_, 7, v_mulFn_x3f_3319_);
lean_ctor_set(v_reuseFailAlloc_3333_, 8, v_subFn_x3f_3320_);
lean_ctor_set(v_reuseFailAlloc_3333_, 9, v_negFn_x3f_3321_);
lean_ctor_set(v_reuseFailAlloc_3333_, 10, v_powFn_x3f_3322_);
lean_ctor_set(v_reuseFailAlloc_3333_, 11, v_intCastFn_x3f_3323_);
lean_ctor_set(v_reuseFailAlloc_3333_, 12, v___x_3330_);
lean_ctor_set(v_reuseFailAlloc_3333_, 13, v_natSMulFn_x3f_3324_);
lean_ctor_set(v_reuseFailAlloc_3333_, 14, v_intSMulFn_x3f_3325_);
lean_ctor_set(v_reuseFailAlloc_3333_, 15, v_one_x3f_3326_);
lean_ctor_set_uint8(v_reuseFailAlloc_3333_, sizeof(void*)*16, v_symbolicChar_3317_);
v___x_3332_ = v_reuseFailAlloc_3333_;
goto v_reusejp_3331_;
}
v_reusejp_3331_:
{
return v___x_3332_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___at___00Lean_Meta_Sym_Arith_getNatCastFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__1_spec__6_spec__13___redArg(lean_object* v_u_3343_, lean_object* v_type_3344_, lean_object* v_semiringInst_3345_, lean_object* v___y_3346_, lean_object* v___y_3347_, lean_object* v___y_3348_, lean_object* v___y_3349_, lean_object* v___y_3350_, lean_object* v___y_3351_){
_start:
{
lean_object* v___x_3353_; lean_object* v___x_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; lean_object* v_inst_x27_3357_; lean_object* v_inst_3359_; lean_object* v___y_3360_; lean_object* v___y_3361_; lean_object* v___y_3362_; lean_object* v___y_3363_; lean_object* v___y_3364_; lean_object* v___y_3365_; lean_object* v___x_3372_; lean_object* v___x_3373_; lean_object* v_instType_3374_; lean_object* v___x_3375_; 
v___x_3353_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___at___00Lean_Meta_Sym_Arith_getNatCastFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__1_spec__6_spec__13___redArg___closed__0));
v___x_3354_ = lean_box(0);
v___x_3355_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3355_, 0, v_u_3343_);
lean_ctor_set(v___x_3355_, 1, v___x_3354_);
lean_inc_ref_n(v___x_3355_, 2);
v___x_3356_ = l_Lean_mkConst(v___x_3353_, v___x_3355_);
lean_inc_ref_n(v_type_3344_, 2);
v_inst_x27_3357_ = l_Lean_mkAppB(v___x_3356_, v_type_3344_, v_semiringInst_3345_);
v___x_3372_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___at___00Lean_Meta_Sym_Arith_getNatCastFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__1_spec__6_spec__13___redArg___closed__1));
v___x_3373_ = l_Lean_mkConst(v___x_3372_, v___x_3355_);
v_instType_3374_ = l_Lean_Expr_app___override(v___x_3373_, v_type_3344_);
v___x_3375_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v_instType_3374_, v___y_3347_, v___y_3348_, v___y_3349_, v___y_3350_, v___y_3351_);
if (lean_obj_tag(v___x_3375_) == 0)
{
lean_object* v_a_3376_; 
v_a_3376_ = lean_ctor_get(v___x_3375_, 0);
lean_inc(v_a_3376_);
lean_dec_ref_known(v___x_3375_, 1);
if (lean_obj_tag(v_a_3376_) == 0)
{
v_inst_3359_ = v_inst_x27_3357_;
v___y_3360_ = v___y_3346_;
v___y_3361_ = v___y_3347_;
v___y_3362_ = v___y_3348_;
v___y_3363_ = v___y_3349_;
v___y_3364_ = v___y_3350_;
v___y_3365_ = v___y_3351_;
goto v___jp_3358_;
}
else
{
lean_object* v_val_3377_; lean_object* v___x_3378_; lean_object* v___x_3379_; 
v_val_3377_ = lean_ctor_get(v_a_3376_, 0);
lean_inc_n(v_val_3377_, 2);
lean_dec_ref_known(v_a_3376_, 1);
v___x_3378_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__5));
v___x_3379_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst(v___x_3378_, v_val_3377_, v_inst_x27_3357_, v___y_3348_, v___y_3349_, v___y_3350_, v___y_3351_);
if (lean_obj_tag(v___x_3379_) == 0)
{
lean_dec_ref_known(v___x_3379_, 1);
v_inst_3359_ = v_val_3377_;
v___y_3360_ = v___y_3346_;
v___y_3361_ = v___y_3347_;
v___y_3362_ = v___y_3348_;
v___y_3363_ = v___y_3349_;
v___y_3364_ = v___y_3350_;
v___y_3365_ = v___y_3351_;
goto v___jp_3358_;
}
else
{
lean_object* v_a_3380_; lean_object* v___x_3382_; uint8_t v_isShared_3383_; uint8_t v_isSharedCheck_3387_; 
lean_dec(v_val_3377_);
lean_dec_ref_known(v___x_3355_, 2);
lean_dec_ref(v_type_3344_);
v_a_3380_ = lean_ctor_get(v___x_3379_, 0);
v_isSharedCheck_3387_ = !lean_is_exclusive(v___x_3379_);
if (v_isSharedCheck_3387_ == 0)
{
v___x_3382_ = v___x_3379_;
v_isShared_3383_ = v_isSharedCheck_3387_;
goto v_resetjp_3381_;
}
else
{
lean_inc(v_a_3380_);
lean_dec(v___x_3379_);
v___x_3382_ = lean_box(0);
v_isShared_3383_ = v_isSharedCheck_3387_;
goto v_resetjp_3381_;
}
v_resetjp_3381_:
{
lean_object* v___x_3385_; 
if (v_isShared_3383_ == 0)
{
v___x_3385_ = v___x_3382_;
goto v_reusejp_3384_;
}
else
{
lean_object* v_reuseFailAlloc_3386_; 
v_reuseFailAlloc_3386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3386_, 0, v_a_3380_);
v___x_3385_ = v_reuseFailAlloc_3386_;
goto v_reusejp_3384_;
}
v_reusejp_3384_:
{
return v___x_3385_;
}
}
}
}
}
else
{
lean_object* v_a_3388_; lean_object* v___x_3390_; uint8_t v_isShared_3391_; uint8_t v_isSharedCheck_3395_; 
lean_dec_ref(v_inst_x27_3357_);
lean_dec_ref_known(v___x_3355_, 2);
lean_dec_ref(v_type_3344_);
v_a_3388_ = lean_ctor_get(v___x_3375_, 0);
v_isSharedCheck_3395_ = !lean_is_exclusive(v___x_3375_);
if (v_isSharedCheck_3395_ == 0)
{
v___x_3390_ = v___x_3375_;
v_isShared_3391_ = v_isSharedCheck_3395_;
goto v_resetjp_3389_;
}
else
{
lean_inc(v_a_3388_);
lean_dec(v___x_3375_);
v___x_3390_ = lean_box(0);
v_isShared_3391_ = v_isSharedCheck_3395_;
goto v_resetjp_3389_;
}
v_resetjp_3389_:
{
lean_object* v___x_3393_; 
if (v_isShared_3391_ == 0)
{
v___x_3393_ = v___x_3390_;
goto v_reusejp_3392_;
}
else
{
lean_object* v_reuseFailAlloc_3394_; 
v_reuseFailAlloc_3394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3394_, 0, v_a_3388_);
v___x_3393_ = v_reuseFailAlloc_3394_;
goto v_reusejp_3392_;
}
v_reusejp_3392_:
{
return v___x_3393_;
}
}
}
v___jp_3358_:
{
lean_object* v___x_3366_; lean_object* v___x_3367_; lean_object* v___x_3368_; lean_object* v___x_3369_; 
v___x_3366_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__5));
v___x_3367_ = l_Lean_mkConst(v___x_3366_, v___x_3355_);
v___x_3368_ = l_Lean_mkAppB(v___x_3367_, v_type_3344_, v_inst_3359_);
v___x_3369_ = l_Lean_Meta_Sym_canon(v___x_3368_, v___y_3360_, v___y_3361_, v___y_3362_, v___y_3363_, v___y_3364_, v___y_3365_);
if (lean_obj_tag(v___x_3369_) == 0)
{
lean_object* v_a_3370_; lean_object* v___x_3371_; 
v_a_3370_ = lean_ctor_get(v___x_3369_, 0);
lean_inc(v_a_3370_);
lean_dec_ref_known(v___x_3369_, 1);
v___x_3371_ = l_Lean_Meta_Sym_shareCommon(v_a_3370_, v___y_3360_, v___y_3361_, v___y_3362_, v___y_3363_, v___y_3364_, v___y_3365_);
return v___x_3371_;
}
else
{
return v___x_3369_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___at___00Lean_Meta_Sym_Arith_getNatCastFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__1_spec__6_spec__13___redArg___boxed(lean_object* v_u_3396_, lean_object* v_type_3397_, lean_object* v_semiringInst_3398_, lean_object* v___y_3399_, lean_object* v___y_3400_, lean_object* v___y_3401_, lean_object* v___y_3402_, lean_object* v___y_3403_, lean_object* v___y_3404_, lean_object* v___y_3405_){
_start:
{
lean_object* v_res_3406_; 
v_res_3406_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___at___00Lean_Meta_Sym_Arith_getNatCastFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__1_spec__6_spec__13___redArg(v_u_3396_, v_type_3397_, v_semiringInst_3398_, v___y_3399_, v___y_3400_, v___y_3401_, v___y_3402_, v___y_3403_, v___y_3404_);
lean_dec(v___y_3404_);
lean_dec_ref(v___y_3403_);
lean_dec(v___y_3402_);
lean_dec_ref(v___y_3401_);
lean_dec(v___y_3400_);
lean_dec_ref(v___y_3399_);
return v_res_3406_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatCastFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__1_spec__6(lean_object* v___y_3407_, lean_object* v___y_3408_, lean_object* v___y_3409_, lean_object* v___y_3410_, lean_object* v___y_3411_, lean_object* v___y_3412_, lean_object* v___y_3413_, lean_object* v___y_3414_, lean_object* v___y_3415_, lean_object* v___y_3416_, lean_object* v___y_3417_){
_start:
{
lean_object* v___x_3419_; 
v___x_3419_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing(v___y_3407_, v___y_3408_, v___y_3409_, v___y_3410_, v___y_3411_, v___y_3412_, v___y_3413_, v___y_3414_, v___y_3415_, v___y_3416_, v___y_3417_);
if (lean_obj_tag(v___x_3419_) == 0)
{
lean_object* v_a_3420_; lean_object* v___x_3422_; uint8_t v_isShared_3423_; uint8_t v_isSharedCheck_3452_; 
v_a_3420_ = lean_ctor_get(v___x_3419_, 0);
v_isSharedCheck_3452_ = !lean_is_exclusive(v___x_3419_);
if (v_isSharedCheck_3452_ == 0)
{
v___x_3422_ = v___x_3419_;
v_isShared_3423_ = v_isSharedCheck_3452_;
goto v_resetjp_3421_;
}
else
{
lean_inc(v_a_3420_);
lean_dec(v___x_3419_);
v___x_3422_ = lean_box(0);
v_isShared_3423_ = v_isSharedCheck_3452_;
goto v_resetjp_3421_;
}
v_resetjp_3421_:
{
lean_object* v_natCastFn_x3f_3424_; 
v_natCastFn_x3f_3424_ = lean_ctor_get(v_a_3420_, 12);
if (lean_obj_tag(v_natCastFn_x3f_3424_) == 1)
{
lean_object* v_val_3425_; lean_object* v___x_3427_; 
lean_inc_ref(v_natCastFn_x3f_3424_);
lean_dec(v_a_3420_);
v_val_3425_ = lean_ctor_get(v_natCastFn_x3f_3424_, 0);
lean_inc(v_val_3425_);
lean_dec_ref_known(v_natCastFn_x3f_3424_, 1);
if (v_isShared_3423_ == 0)
{
lean_ctor_set(v___x_3422_, 0, v_val_3425_);
v___x_3427_ = v___x_3422_;
goto v_reusejp_3426_;
}
else
{
lean_object* v_reuseFailAlloc_3428_; 
v_reuseFailAlloc_3428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3428_, 0, v_val_3425_);
v___x_3427_ = v_reuseFailAlloc_3428_;
goto v_reusejp_3426_;
}
v_reusejp_3426_:
{
return v___x_3427_;
}
}
else
{
lean_object* v_type_3429_; lean_object* v_u_3430_; lean_object* v_semiringInst_3431_; lean_object* v___x_3432_; 
lean_del_object(v___x_3422_);
v_type_3429_ = lean_ctor_get(v_a_3420_, 1);
lean_inc_ref(v_type_3429_);
v_u_3430_ = lean_ctor_get(v_a_3420_, 2);
lean_inc(v_u_3430_);
v_semiringInst_3431_ = lean_ctor_get(v_a_3420_, 4);
lean_inc_ref(v_semiringInst_3431_);
lean_dec(v_a_3420_);
v___x_3432_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___at___00Lean_Meta_Sym_Arith_getNatCastFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__1_spec__6_spec__13___redArg(v_u_3430_, v_type_3429_, v_semiringInst_3431_, v___y_3412_, v___y_3413_, v___y_3414_, v___y_3415_, v___y_3416_, v___y_3417_);
if (lean_obj_tag(v___x_3432_) == 0)
{
lean_object* v_a_3433_; lean_object* v___f_3434_; lean_object* v___x_3435_; 
v_a_3433_ = lean_ctor_get(v___x_3432_, 0);
lean_inc_n(v_a_3433_, 2);
lean_dec_ref_known(v___x_3432_, 1);
v___f_3434_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getNatCastFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__1_spec__6___lam__0), 2, 1);
lean_closure_set(v___f_3434_, 0, v_a_3433_);
v___x_3435_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_modifyRing___redArg(v___f_3434_, v___y_3407_, v___y_3413_);
if (lean_obj_tag(v___x_3435_) == 0)
{
lean_object* v___x_3437_; uint8_t v_isShared_3438_; uint8_t v_isSharedCheck_3442_; 
v_isSharedCheck_3442_ = !lean_is_exclusive(v___x_3435_);
if (v_isSharedCheck_3442_ == 0)
{
lean_object* v_unused_3443_; 
v_unused_3443_ = lean_ctor_get(v___x_3435_, 0);
lean_dec(v_unused_3443_);
v___x_3437_ = v___x_3435_;
v_isShared_3438_ = v_isSharedCheck_3442_;
goto v_resetjp_3436_;
}
else
{
lean_dec(v___x_3435_);
v___x_3437_ = lean_box(0);
v_isShared_3438_ = v_isSharedCheck_3442_;
goto v_resetjp_3436_;
}
v_resetjp_3436_:
{
lean_object* v___x_3440_; 
if (v_isShared_3438_ == 0)
{
lean_ctor_set(v___x_3437_, 0, v_a_3433_);
v___x_3440_ = v___x_3437_;
goto v_reusejp_3439_;
}
else
{
lean_object* v_reuseFailAlloc_3441_; 
v_reuseFailAlloc_3441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3441_, 0, v_a_3433_);
v___x_3440_ = v_reuseFailAlloc_3441_;
goto v_reusejp_3439_;
}
v_reusejp_3439_:
{
return v___x_3440_;
}
}
}
else
{
lean_object* v_a_3444_; lean_object* v___x_3446_; uint8_t v_isShared_3447_; uint8_t v_isSharedCheck_3451_; 
lean_dec(v_a_3433_);
v_a_3444_ = lean_ctor_get(v___x_3435_, 0);
v_isSharedCheck_3451_ = !lean_is_exclusive(v___x_3435_);
if (v_isSharedCheck_3451_ == 0)
{
v___x_3446_ = v___x_3435_;
v_isShared_3447_ = v_isSharedCheck_3451_;
goto v_resetjp_3445_;
}
else
{
lean_inc(v_a_3444_);
lean_dec(v___x_3435_);
v___x_3446_ = lean_box(0);
v_isShared_3447_ = v_isSharedCheck_3451_;
goto v_resetjp_3445_;
}
v_resetjp_3445_:
{
lean_object* v___x_3449_; 
if (v_isShared_3447_ == 0)
{
v___x_3449_ = v___x_3446_;
goto v_reusejp_3448_;
}
else
{
lean_object* v_reuseFailAlloc_3450_; 
v_reuseFailAlloc_3450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3450_, 0, v_a_3444_);
v___x_3449_ = v_reuseFailAlloc_3450_;
goto v_reusejp_3448_;
}
v_reusejp_3448_:
{
return v___x_3449_;
}
}
}
}
else
{
return v___x_3432_;
}
}
}
}
else
{
lean_object* v_a_3453_; lean_object* v___x_3455_; uint8_t v_isShared_3456_; uint8_t v_isSharedCheck_3460_; 
v_a_3453_ = lean_ctor_get(v___x_3419_, 0);
v_isSharedCheck_3460_ = !lean_is_exclusive(v___x_3419_);
if (v_isSharedCheck_3460_ == 0)
{
v___x_3455_ = v___x_3419_;
v_isShared_3456_ = v_isSharedCheck_3460_;
goto v_resetjp_3454_;
}
else
{
lean_inc(v_a_3453_);
lean_dec(v___x_3419_);
v___x_3455_ = lean_box(0);
v_isShared_3456_ = v_isSharedCheck_3460_;
goto v_resetjp_3454_;
}
v_resetjp_3454_:
{
lean_object* v___x_3458_; 
if (v_isShared_3456_ == 0)
{
v___x_3458_ = v___x_3455_;
goto v_reusejp_3457_;
}
else
{
lean_object* v_reuseFailAlloc_3459_; 
v_reuseFailAlloc_3459_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3459_, 0, v_a_3453_);
v___x_3458_ = v_reuseFailAlloc_3459_;
goto v_reusejp_3457_;
}
v_reusejp_3457_:
{
return v___x_3458_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatCastFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__1_spec__6___boxed(lean_object* v___y_3461_, lean_object* v___y_3462_, lean_object* v___y_3463_, lean_object* v___y_3464_, lean_object* v___y_3465_, lean_object* v___y_3466_, lean_object* v___y_3467_, lean_object* v___y_3468_, lean_object* v___y_3469_, lean_object* v___y_3470_, lean_object* v___y_3471_, lean_object* v___y_3472_){
_start:
{
lean_object* v_res_3473_; 
v_res_3473_ = l_Lean_Meta_Sym_Arith_getNatCastFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__1_spec__6(v___y_3461_, v___y_3462_, v___y_3463_, v___y_3464_, v___y_3465_, v___y_3466_, v___y_3467_, v___y_3468_, v___y_3469_, v___y_3470_, v___y_3471_);
lean_dec(v___y_3471_);
lean_dec_ref(v___y_3470_);
lean_dec(v___y_3469_);
lean_dec_ref(v___y_3468_);
lean_dec(v___y_3467_);
lean_dec_ref(v___y_3466_);
lean_dec(v___y_3465_);
lean_dec_ref(v___y_3464_);
lean_dec(v___y_3463_);
lean_dec(v___y_3462_);
lean_dec(v___y_3461_);
return v_res_3473_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0_spec__2_spec__5_spec__10_spec__15___redArg(lean_object* v_x_3474_, lean_object* v_x_3475_, lean_object* v_x_3476_, lean_object* v_x_3477_){
_start:
{
lean_object* v_ks_3478_; lean_object* v_vs_3479_; lean_object* v___x_3481_; uint8_t v_isShared_3482_; uint8_t v_isSharedCheck_3505_; 
v_ks_3478_ = lean_ctor_get(v_x_3474_, 0);
v_vs_3479_ = lean_ctor_get(v_x_3474_, 1);
v_isSharedCheck_3505_ = !lean_is_exclusive(v_x_3474_);
if (v_isSharedCheck_3505_ == 0)
{
v___x_3481_ = v_x_3474_;
v_isShared_3482_ = v_isSharedCheck_3505_;
goto v_resetjp_3480_;
}
else
{
lean_inc(v_vs_3479_);
lean_inc(v_ks_3478_);
lean_dec(v_x_3474_);
v___x_3481_ = lean_box(0);
v_isShared_3482_ = v_isSharedCheck_3505_;
goto v_resetjp_3480_;
}
v_resetjp_3480_:
{
lean_object* v___x_3483_; uint8_t v___x_3484_; 
v___x_3483_ = lean_array_get_size(v_ks_3478_);
v___x_3484_ = lean_nat_dec_lt(v_x_3475_, v___x_3483_);
if (v___x_3484_ == 0)
{
lean_object* v___x_3485_; lean_object* v___x_3486_; lean_object* v___x_3488_; 
lean_dec(v_x_3475_);
v___x_3485_ = lean_array_push(v_ks_3478_, v_x_3476_);
v___x_3486_ = lean_array_push(v_vs_3479_, v_x_3477_);
if (v_isShared_3482_ == 0)
{
lean_ctor_set(v___x_3481_, 1, v___x_3486_);
lean_ctor_set(v___x_3481_, 0, v___x_3485_);
v___x_3488_ = v___x_3481_;
goto v_reusejp_3487_;
}
else
{
lean_object* v_reuseFailAlloc_3489_; 
v_reuseFailAlloc_3489_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3489_, 0, v___x_3485_);
lean_ctor_set(v_reuseFailAlloc_3489_, 1, v___x_3486_);
v___x_3488_ = v_reuseFailAlloc_3489_;
goto v_reusejp_3487_;
}
v_reusejp_3487_:
{
return v___x_3488_;
}
}
else
{
lean_object* v_k_x27_3490_; size_t v___x_3491_; size_t v___x_3492_; uint8_t v___x_3493_; 
v_k_x27_3490_ = lean_array_fget_borrowed(v_ks_3478_, v_x_3475_);
v___x_3491_ = lean_ptr_addr(v_x_3476_);
v___x_3492_ = lean_ptr_addr(v_k_x27_3490_);
v___x_3493_ = lean_usize_dec_eq(v___x_3491_, v___x_3492_);
if (v___x_3493_ == 0)
{
lean_object* v___x_3495_; 
if (v_isShared_3482_ == 0)
{
v___x_3495_ = v___x_3481_;
goto v_reusejp_3494_;
}
else
{
lean_object* v_reuseFailAlloc_3499_; 
v_reuseFailAlloc_3499_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3499_, 0, v_ks_3478_);
lean_ctor_set(v_reuseFailAlloc_3499_, 1, v_vs_3479_);
v___x_3495_ = v_reuseFailAlloc_3499_;
goto v_reusejp_3494_;
}
v_reusejp_3494_:
{
lean_object* v___x_3496_; lean_object* v___x_3497_; 
v___x_3496_ = lean_unsigned_to_nat(1u);
v___x_3497_ = lean_nat_add(v_x_3475_, v___x_3496_);
lean_dec(v_x_3475_);
v_x_3474_ = v___x_3495_;
v_x_3475_ = v___x_3497_;
goto _start;
}
}
else
{
lean_object* v___x_3500_; lean_object* v___x_3501_; lean_object* v___x_3503_; 
v___x_3500_ = lean_array_fset(v_ks_3478_, v_x_3475_, v_x_3476_);
v___x_3501_ = lean_array_fset(v_vs_3479_, v_x_3475_, v_x_3477_);
lean_dec(v_x_3475_);
if (v_isShared_3482_ == 0)
{
lean_ctor_set(v___x_3481_, 1, v___x_3501_);
lean_ctor_set(v___x_3481_, 0, v___x_3500_);
v___x_3503_ = v___x_3481_;
goto v_reusejp_3502_;
}
else
{
lean_object* v_reuseFailAlloc_3504_; 
v_reuseFailAlloc_3504_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3504_, 0, v___x_3500_);
lean_ctor_set(v_reuseFailAlloc_3504_, 1, v___x_3501_);
v___x_3503_ = v_reuseFailAlloc_3504_;
goto v_reusejp_3502_;
}
v_reusejp_3502_:
{
return v___x_3503_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0_spec__2_spec__5_spec__10___redArg(lean_object* v_n_3506_, lean_object* v_k_3507_, lean_object* v_v_3508_){
_start:
{
lean_object* v___x_3509_; lean_object* v___x_3510_; 
v___x_3509_ = lean_unsigned_to_nat(0u);
v___x_3510_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0_spec__2_spec__5_spec__10_spec__15___redArg(v_n_3506_, v___x_3509_, v_k_3507_, v_v_3508_);
return v___x_3510_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0_spec__2_spec__5___redArg(lean_object* v_x_3511_, size_t v_x_3512_, size_t v_x_3513_, lean_object* v_x_3514_, lean_object* v_x_3515_){
_start:
{
if (lean_obj_tag(v_x_3511_) == 0)
{
lean_object* v_es_3516_; size_t v___x_3517_; size_t v___x_3518_; lean_object* v_j_3519_; lean_object* v___x_3520_; uint8_t v___x_3521_; 
v_es_3516_ = lean_ctor_get(v_x_3511_, 0);
v___x_3517_ = ((size_t)31ULL);
v___x_3518_ = lean_usize_land(v_x_3512_, v___x_3517_);
v_j_3519_ = lean_usize_to_nat(v___x_3518_);
v___x_3520_ = lean_array_get_size(v_es_3516_);
v___x_3521_ = lean_nat_dec_lt(v_j_3519_, v___x_3520_);
if (v___x_3521_ == 0)
{
lean_dec(v_j_3519_);
lean_dec(v_x_3515_);
lean_dec_ref(v_x_3514_);
return v_x_3511_;
}
else
{
lean_object* v___x_3523_; uint8_t v_isShared_3524_; uint8_t v_isSharedCheck_3562_; 
lean_inc_ref(v_es_3516_);
v_isSharedCheck_3562_ = !lean_is_exclusive(v_x_3511_);
if (v_isSharedCheck_3562_ == 0)
{
lean_object* v_unused_3563_; 
v_unused_3563_ = lean_ctor_get(v_x_3511_, 0);
lean_dec(v_unused_3563_);
v___x_3523_ = v_x_3511_;
v_isShared_3524_ = v_isSharedCheck_3562_;
goto v_resetjp_3522_;
}
else
{
lean_dec(v_x_3511_);
v___x_3523_ = lean_box(0);
v_isShared_3524_ = v_isSharedCheck_3562_;
goto v_resetjp_3522_;
}
v_resetjp_3522_:
{
lean_object* v_v_3525_; lean_object* v___x_3526_; lean_object* v_xs_x27_3527_; lean_object* v___y_3529_; 
v_v_3525_ = lean_array_fget(v_es_3516_, v_j_3519_);
v___x_3526_ = lean_box(0);
v_xs_x27_3527_ = lean_array_fset(v_es_3516_, v_j_3519_, v___x_3526_);
switch(lean_obj_tag(v_v_3525_))
{
case 0:
{
lean_object* v_key_3534_; lean_object* v_val_3535_; lean_object* v___x_3537_; uint8_t v_isShared_3538_; uint8_t v_isSharedCheck_3547_; 
v_key_3534_ = lean_ctor_get(v_v_3525_, 0);
v_val_3535_ = lean_ctor_get(v_v_3525_, 1);
v_isSharedCheck_3547_ = !lean_is_exclusive(v_v_3525_);
if (v_isSharedCheck_3547_ == 0)
{
v___x_3537_ = v_v_3525_;
v_isShared_3538_ = v_isSharedCheck_3547_;
goto v_resetjp_3536_;
}
else
{
lean_inc(v_val_3535_);
lean_inc(v_key_3534_);
lean_dec(v_v_3525_);
v___x_3537_ = lean_box(0);
v_isShared_3538_ = v_isSharedCheck_3547_;
goto v_resetjp_3536_;
}
v_resetjp_3536_:
{
size_t v___x_3539_; size_t v___x_3540_; uint8_t v___x_3541_; 
v___x_3539_ = lean_ptr_addr(v_x_3514_);
v___x_3540_ = lean_ptr_addr(v_key_3534_);
v___x_3541_ = lean_usize_dec_eq(v___x_3539_, v___x_3540_);
if (v___x_3541_ == 0)
{
lean_object* v___x_3542_; lean_object* v___x_3543_; 
lean_del_object(v___x_3537_);
v___x_3542_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_3534_, v_val_3535_, v_x_3514_, v_x_3515_);
v___x_3543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3543_, 0, v___x_3542_);
v___y_3529_ = v___x_3543_;
goto v___jp_3528_;
}
else
{
lean_object* v___x_3545_; 
lean_dec(v_val_3535_);
lean_dec(v_key_3534_);
if (v_isShared_3538_ == 0)
{
lean_ctor_set(v___x_3537_, 1, v_x_3515_);
lean_ctor_set(v___x_3537_, 0, v_x_3514_);
v___x_3545_ = v___x_3537_;
goto v_reusejp_3544_;
}
else
{
lean_object* v_reuseFailAlloc_3546_; 
v_reuseFailAlloc_3546_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3546_, 0, v_x_3514_);
lean_ctor_set(v_reuseFailAlloc_3546_, 1, v_x_3515_);
v___x_3545_ = v_reuseFailAlloc_3546_;
goto v_reusejp_3544_;
}
v_reusejp_3544_:
{
v___y_3529_ = v___x_3545_;
goto v___jp_3528_;
}
}
}
}
case 1:
{
lean_object* v_node_3548_; lean_object* v___x_3550_; uint8_t v_isShared_3551_; uint8_t v_isSharedCheck_3560_; 
v_node_3548_ = lean_ctor_get(v_v_3525_, 0);
v_isSharedCheck_3560_ = !lean_is_exclusive(v_v_3525_);
if (v_isSharedCheck_3560_ == 0)
{
v___x_3550_ = v_v_3525_;
v_isShared_3551_ = v_isSharedCheck_3560_;
goto v_resetjp_3549_;
}
else
{
lean_inc(v_node_3548_);
lean_dec(v_v_3525_);
v___x_3550_ = lean_box(0);
v_isShared_3551_ = v_isSharedCheck_3560_;
goto v_resetjp_3549_;
}
v_resetjp_3549_:
{
size_t v___x_3552_; size_t v___x_3553_; size_t v___x_3554_; size_t v___x_3555_; lean_object* v___x_3556_; lean_object* v___x_3558_; 
v___x_3552_ = ((size_t)5ULL);
v___x_3553_ = lean_usize_shift_right(v_x_3512_, v___x_3552_);
v___x_3554_ = ((size_t)1ULL);
v___x_3555_ = lean_usize_add(v_x_3513_, v___x_3554_);
v___x_3556_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0_spec__2_spec__5___redArg(v_node_3548_, v___x_3553_, v___x_3555_, v_x_3514_, v_x_3515_);
if (v_isShared_3551_ == 0)
{
lean_ctor_set(v___x_3550_, 0, v___x_3556_);
v___x_3558_ = v___x_3550_;
goto v_reusejp_3557_;
}
else
{
lean_object* v_reuseFailAlloc_3559_; 
v_reuseFailAlloc_3559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3559_, 0, v___x_3556_);
v___x_3558_ = v_reuseFailAlloc_3559_;
goto v_reusejp_3557_;
}
v_reusejp_3557_:
{
v___y_3529_ = v___x_3558_;
goto v___jp_3528_;
}
}
}
default: 
{
lean_object* v___x_3561_; 
v___x_3561_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3561_, 0, v_x_3514_);
lean_ctor_set(v___x_3561_, 1, v_x_3515_);
v___y_3529_ = v___x_3561_;
goto v___jp_3528_;
}
}
v___jp_3528_:
{
lean_object* v___x_3530_; lean_object* v___x_3532_; 
v___x_3530_ = lean_array_fset(v_xs_x27_3527_, v_j_3519_, v___y_3529_);
lean_dec(v_j_3519_);
if (v_isShared_3524_ == 0)
{
lean_ctor_set(v___x_3523_, 0, v___x_3530_);
v___x_3532_ = v___x_3523_;
goto v_reusejp_3531_;
}
else
{
lean_object* v_reuseFailAlloc_3533_; 
v_reuseFailAlloc_3533_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3533_, 0, v___x_3530_);
v___x_3532_ = v_reuseFailAlloc_3533_;
goto v_reusejp_3531_;
}
v_reusejp_3531_:
{
return v___x_3532_;
}
}
}
}
}
else
{
lean_object* v_ks_3564_; lean_object* v_vs_3565_; lean_object* v___x_3567_; uint8_t v_isShared_3568_; uint8_t v_isSharedCheck_3583_; 
v_ks_3564_ = lean_ctor_get(v_x_3511_, 0);
v_vs_3565_ = lean_ctor_get(v_x_3511_, 1);
v_isSharedCheck_3583_ = !lean_is_exclusive(v_x_3511_);
if (v_isSharedCheck_3583_ == 0)
{
v___x_3567_ = v_x_3511_;
v_isShared_3568_ = v_isSharedCheck_3583_;
goto v_resetjp_3566_;
}
else
{
lean_inc(v_vs_3565_);
lean_inc(v_ks_3564_);
lean_dec(v_x_3511_);
v___x_3567_ = lean_box(0);
v_isShared_3568_ = v_isSharedCheck_3583_;
goto v_resetjp_3566_;
}
v_resetjp_3566_:
{
lean_object* v___x_3570_; 
if (v_isShared_3568_ == 0)
{
v___x_3570_ = v___x_3567_;
goto v_reusejp_3569_;
}
else
{
lean_object* v_reuseFailAlloc_3582_; 
v_reuseFailAlloc_3582_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3582_, 0, v_ks_3564_);
lean_ctor_set(v_reuseFailAlloc_3582_, 1, v_vs_3565_);
v___x_3570_ = v_reuseFailAlloc_3582_;
goto v_reusejp_3569_;
}
v_reusejp_3569_:
{
lean_object* v_newNode_3571_; size_t v___x_3572_; uint8_t v___x_3573_; 
v_newNode_3571_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0_spec__2_spec__5_spec__10___redArg(v___x_3570_, v_x_3514_, v_x_3515_);
v___x_3572_ = ((size_t)7ULL);
v___x_3573_ = lean_usize_dec_le(v___x_3572_, v_x_3513_);
if (v___x_3573_ == 0)
{
lean_object* v___x_3574_; lean_object* v___x_3575_; uint8_t v___x_3576_; 
v___x_3574_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_3571_);
v___x_3575_ = lean_unsigned_to_nat(4u);
v___x_3576_ = lean_nat_dec_lt(v___x_3574_, v___x_3575_);
lean_dec(v___x_3574_);
if (v___x_3576_ == 0)
{
lean_object* v_ks_3577_; lean_object* v_vs_3578_; lean_object* v___x_3579_; lean_object* v___x_3580_; lean_object* v___x_3581_; 
v_ks_3577_ = lean_ctor_get(v_newNode_3571_, 0);
lean_inc_ref(v_ks_3577_);
v_vs_3578_ = lean_ctor_get(v_newNode_3571_, 1);
lean_inc_ref(v_vs_3578_);
lean_dec_ref(v_newNode_3571_);
v___x_3579_ = lean_unsigned_to_nat(0u);
v___x_3580_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv_spec__0_spec__0___redArg___closed__0);
v___x_3581_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0_spec__2_spec__5_spec__11___redArg(v_x_3513_, v_ks_3577_, v_vs_3578_, v___x_3579_, v___x_3580_);
lean_dec_ref(v_vs_3578_);
lean_dec_ref(v_ks_3577_);
return v___x_3581_;
}
else
{
return v_newNode_3571_;
}
}
else
{
return v_newNode_3571_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0_spec__2_spec__5_spec__11___redArg(size_t v_depth_3584_, lean_object* v_keys_3585_, lean_object* v_vals_3586_, lean_object* v_i_3587_, lean_object* v_entries_3588_){
_start:
{
lean_object* v___x_3589_; uint8_t v___x_3590_; 
v___x_3589_ = lean_array_get_size(v_keys_3585_);
v___x_3590_ = lean_nat_dec_lt(v_i_3587_, v___x_3589_);
if (v___x_3590_ == 0)
{
lean_dec(v_i_3587_);
return v_entries_3588_;
}
else
{
lean_object* v_k_3591_; lean_object* v_v_3592_; size_t v___x_3593_; size_t v___x_3594_; size_t v___x_3595_; uint64_t v___x_3596_; size_t v_h_3597_; size_t v___x_3598_; lean_object* v___x_3599_; size_t v___x_3600_; size_t v___x_3601_; size_t v___x_3602_; size_t v_h_3603_; lean_object* v___x_3604_; lean_object* v___x_3605_; 
v_k_3591_ = lean_array_fget_borrowed(v_keys_3585_, v_i_3587_);
v_v_3592_ = lean_array_fget_borrowed(v_vals_3586_, v_i_3587_);
v___x_3593_ = lean_ptr_addr(v_k_3591_);
v___x_3594_ = ((size_t)3ULL);
v___x_3595_ = lean_usize_shift_right(v___x_3593_, v___x_3594_);
v___x_3596_ = lean_usize_to_uint64(v___x_3595_);
v_h_3597_ = lean_uint64_to_usize(v___x_3596_);
v___x_3598_ = ((size_t)5ULL);
v___x_3599_ = lean_unsigned_to_nat(1u);
v___x_3600_ = ((size_t)1ULL);
v___x_3601_ = lean_usize_sub(v_depth_3584_, v___x_3600_);
v___x_3602_ = lean_usize_mul(v___x_3598_, v___x_3601_);
v_h_3603_ = lean_usize_shift_right(v_h_3597_, v___x_3602_);
v___x_3604_ = lean_nat_add(v_i_3587_, v___x_3599_);
lean_dec(v_i_3587_);
lean_inc(v_v_3592_);
lean_inc(v_k_3591_);
v___x_3605_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0_spec__2_spec__5___redArg(v_entries_3588_, v_h_3603_, v_depth_3584_, v_k_3591_, v_v_3592_);
v_i_3587_ = v___x_3604_;
v_entries_3588_ = v___x_3605_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0_spec__2_spec__5_spec__11___redArg___boxed(lean_object* v_depth_3607_, lean_object* v_keys_3608_, lean_object* v_vals_3609_, lean_object* v_i_3610_, lean_object* v_entries_3611_){
_start:
{
size_t v_depth_boxed_3612_; lean_object* v_res_3613_; 
v_depth_boxed_3612_ = lean_unbox_usize(v_depth_3607_);
lean_dec(v_depth_3607_);
v_res_3613_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0_spec__2_spec__5_spec__11___redArg(v_depth_boxed_3612_, v_keys_3608_, v_vals_3609_, v_i_3610_, v_entries_3611_);
lean_dec_ref(v_vals_3609_);
lean_dec_ref(v_keys_3608_);
return v_res_3613_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0_spec__2_spec__5___redArg___boxed(lean_object* v_x_3614_, lean_object* v_x_3615_, lean_object* v_x_3616_, lean_object* v_x_3617_, lean_object* v_x_3618_){
_start:
{
size_t v_x_131788__boxed_3619_; size_t v_x_131789__boxed_3620_; lean_object* v_res_3621_; 
v_x_131788__boxed_3619_ = lean_unbox_usize(v_x_3615_);
lean_dec(v_x_3615_);
v_x_131789__boxed_3620_ = lean_unbox_usize(v_x_3616_);
lean_dec(v_x_3616_);
v_res_3621_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0_spec__2_spec__5___redArg(v_x_3614_, v_x_131788__boxed_3619_, v_x_131789__boxed_3620_, v_x_3617_, v_x_3618_);
return v_res_3621_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0_spec__2___redArg(lean_object* v_x_3622_, lean_object* v_x_3623_, lean_object* v_x_3624_){
_start:
{
size_t v___x_3625_; size_t v___x_3626_; size_t v___x_3627_; uint64_t v___x_3628_; size_t v___x_3629_; size_t v___x_3630_; lean_object* v___x_3631_; 
v___x_3625_ = lean_ptr_addr(v_x_3623_);
v___x_3626_ = ((size_t)3ULL);
v___x_3627_ = lean_usize_shift_right(v___x_3625_, v___x_3626_);
v___x_3628_ = lean_usize_to_uint64(v___x_3627_);
v___x_3629_ = lean_uint64_to_usize(v___x_3628_);
v___x_3630_ = ((size_t)1ULL);
v___x_3631_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0_spec__2_spec__5___redArg(v_x_3622_, v___x_3629_, v___x_3630_, v_x_3623_, v_x_3624_);
return v___x_3631_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__1___lam__1(lean_object* v_e_3632_, lean_object* v_s_3633_){
_start:
{
lean_object* v_vars_3634_; lean_object* v_varMap_3635_; lean_object* v_denote_3636_; lean_object* v_natCastSet_3637_; lean_object* v_natCasts_3638_; uint8_t v_hasIntCast_3639_; lean_object* v___x_3641_; uint8_t v_isShared_3642_; uint8_t v_isSharedCheck_3648_; 
v_vars_3634_ = lean_ctor_get(v_s_3633_, 0);
v_varMap_3635_ = lean_ctor_get(v_s_3633_, 1);
v_denote_3636_ = lean_ctor_get(v_s_3633_, 2);
v_natCastSet_3637_ = lean_ctor_get(v_s_3633_, 3);
v_natCasts_3638_ = lean_ctor_get(v_s_3633_, 4);
v_hasIntCast_3639_ = lean_ctor_get_uint8(v_s_3633_, sizeof(void*)*5);
v_isSharedCheck_3648_ = !lean_is_exclusive(v_s_3633_);
if (v_isSharedCheck_3648_ == 0)
{
v___x_3641_ = v_s_3633_;
v_isShared_3642_ = v_isSharedCheck_3648_;
goto v_resetjp_3640_;
}
else
{
lean_inc(v_natCasts_3638_);
lean_inc(v_natCastSet_3637_);
lean_inc(v_denote_3636_);
lean_inc(v_varMap_3635_);
lean_inc(v_vars_3634_);
lean_dec(v_s_3633_);
v___x_3641_ = lean_box(0);
v_isShared_3642_ = v_isSharedCheck_3648_;
goto v_resetjp_3640_;
}
v_resetjp_3640_:
{
lean_object* v___x_3643_; lean_object* v___x_3644_; lean_object* v___x_3646_; 
v___x_3643_ = lean_box(0);
v___x_3644_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0_spec__2___redArg(v_natCastSet_3637_, v_e_3632_, v___x_3643_);
if (v_isShared_3642_ == 0)
{
lean_ctor_set(v___x_3641_, 3, v___x_3644_);
v___x_3646_ = v___x_3641_;
goto v_reusejp_3645_;
}
else
{
lean_object* v_reuseFailAlloc_3647_; 
v_reuseFailAlloc_3647_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_3647_, 0, v_vars_3634_);
lean_ctor_set(v_reuseFailAlloc_3647_, 1, v_varMap_3635_);
lean_ctor_set(v_reuseFailAlloc_3647_, 2, v_denote_3636_);
lean_ctor_set(v_reuseFailAlloc_3647_, 3, v___x_3644_);
lean_ctor_set(v_reuseFailAlloc_3647_, 4, v_natCasts_3638_);
lean_ctor_set_uint8(v_reuseFailAlloc_3647_, sizeof(void*)*5, v_hasIntCast_3639_);
v___x_3646_ = v_reuseFailAlloc_3647_;
goto v_reusejp_3645_;
}
v_reusejp_3645_:
{
return v___x_3646_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__1(lean_object* v_e_3649_, lean_object* v___y_3650_, lean_object* v___y_3651_, lean_object* v___y_3652_, lean_object* v___y_3653_, lean_object* v___y_3654_, lean_object* v___y_3655_, lean_object* v___y_3656_, lean_object* v___y_3657_, lean_object* v___y_3658_, lean_object* v___y_3659_, lean_object* v___y_3660_){
_start:
{
lean_object* v___f_3662_; lean_object* v___f_3663_; lean_object* v___x_3664_; 
lean_inc_ref_n(v_e_3649_, 3);
v___f_3662_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3662_, 0, v_e_3649_);
v___f_3663_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__1___lam__1), 2, 1);
lean_closure_set(v___f_3663_, 0, v_e_3649_);
v___x_3664_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_3649_, v___y_3658_);
if (lean_obj_tag(v___x_3664_) == 0)
{
lean_object* v_a_3665_; lean_object* v___x_3667_; uint8_t v_isShared_3668_; uint8_t v_isSharedCheck_3848_; 
v_a_3665_ = lean_ctor_get(v___x_3664_, 0);
v_isSharedCheck_3848_ = !lean_is_exclusive(v___x_3664_);
if (v_isSharedCheck_3848_ == 0)
{
v___x_3667_ = v___x_3664_;
v_isShared_3668_ = v_isSharedCheck_3848_;
goto v_resetjp_3666_;
}
else
{
lean_inc(v_a_3665_);
lean_dec(v___x_3664_);
v___x_3667_ = lean_box(0);
v_isShared_3668_ = v_isSharedCheck_3848_;
goto v_resetjp_3666_;
}
v_resetjp_3666_:
{
lean_object* v___x_3674_; uint8_t v___x_3675_; 
v___x_3674_ = l_Lean_Expr_cleanupAnnotations(v_a_3665_);
lean_dec(v_a_3665_);
v___x_3675_ = l_Lean_Expr_isApp(v___x_3674_);
if (v___x_3675_ == 0)
{
lean_dec_ref(v___x_3674_);
lean_dec_ref(v___f_3663_);
lean_dec_ref(v___f_3662_);
lean_dec_ref(v_e_3649_);
goto v___jp_3669_;
}
else
{
lean_object* v___x_3676_; uint8_t v___x_3677_; 
v___x_3676_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3674_);
v___x_3677_ = l_Lean_Expr_isApp(v___x_3676_);
if (v___x_3677_ == 0)
{
lean_dec_ref(v___x_3676_);
lean_dec_ref(v___x_3674_);
lean_dec_ref(v___f_3663_);
lean_dec_ref(v___f_3662_);
lean_dec_ref(v_e_3649_);
goto v___jp_3669_;
}
else
{
lean_object* v___x_3678_; uint8_t v___x_3679_; 
v___x_3678_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3676_);
v___x_3679_ = l_Lean_Expr_isApp(v___x_3678_);
if (v___x_3679_ == 0)
{
lean_dec_ref(v___x_3678_);
lean_dec_ref(v___x_3676_);
lean_dec_ref(v___x_3674_);
lean_dec_ref(v___f_3663_);
lean_dec_ref(v___f_3662_);
lean_dec_ref(v_e_3649_);
goto v___jp_3669_;
}
else
{
lean_object* v_arg_3680_; lean_object* v_arg_3681_; lean_object* v___x_3682_; lean_object* v___x_3683_; uint8_t v___x_3684_; 
v_arg_3680_ = lean_ctor_get(v___x_3674_, 1);
lean_inc_ref(v_arg_3680_);
lean_dec_ref(v___x_3674_);
v_arg_3681_ = lean_ctor_get(v___x_3676_, 1);
lean_inc_ref(v_arg_3681_);
lean_dec_ref(v___x_3676_);
v___x_3682_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3678_);
lean_dec_ref(v___x_3678_);
v___x_3683_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__2));
v___x_3684_ = l_Lean_Expr_isConstOf(v___x_3682_, v___x_3683_);
if (v___x_3684_ == 0)
{
lean_object* v___x_3685_; uint8_t v___x_3686_; 
v___x_3685_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__5));
v___x_3686_ = l_Lean_Expr_isConstOf(v___x_3682_, v___x_3685_);
lean_dec_ref(v___x_3682_);
if (v___x_3686_ == 0)
{
lean_dec_ref(v_arg_3681_);
lean_dec_ref(v_arg_3680_);
lean_dec_ref(v___f_3663_);
lean_dec_ref(v___f_3662_);
lean_dec_ref(v_e_3649_);
goto v___jp_3669_;
}
else
{
uint8_t v___x_3687_; 
lean_del_object(v___x_3667_);
v___x_3687_ = l_Lean_Meta_Sym_isNatValue(v_arg_3680_);
lean_dec_ref(v_arg_3680_);
if (v___x_3687_ == 0)
{
lean_object* v___x_3688_; 
v___x_3688_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRingState___redArg(v___y_3650_, v___y_3651_, v___y_3659_);
if (lean_obj_tag(v___x_3688_) == 0)
{
lean_object* v_a_3689_; lean_object* v___x_3691_; uint8_t v_isShared_3692_; uint8_t v_isSharedCheck_3755_; 
v_a_3689_ = lean_ctor_get(v___x_3688_, 0);
v_isSharedCheck_3755_ = !lean_is_exclusive(v___x_3688_);
if (v_isSharedCheck_3755_ == 0)
{
v___x_3691_ = v___x_3688_;
v_isShared_3692_ = v_isSharedCheck_3755_;
goto v_resetjp_3690_;
}
else
{
lean_inc(v_a_3689_);
lean_dec(v___x_3688_);
v___x_3691_ = lean_box(0);
v_isShared_3692_ = v_isSharedCheck_3755_;
goto v_resetjp_3690_;
}
v_resetjp_3690_:
{
lean_object* v_natCastSet_3693_; uint8_t v___x_3694_; 
v_natCastSet_3693_ = lean_ctor_get(v_a_3689_, 3);
lean_inc_ref(v_natCastSet_3693_);
lean_dec(v_a_3689_);
v___x_3694_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0_spec__0___redArg(v_natCastSet_3693_, v_e_3649_);
lean_dec_ref(v_natCastSet_3693_);
if (v___x_3694_ == 0)
{
lean_object* v___x_3695_; 
lean_del_object(v___x_3691_);
v___x_3695_ = l_Lean_Meta_Sym_Arith_getNatCastFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__1_spec__6(v___y_3650_, v___y_3651_, v___y_3652_, v___y_3653_, v___y_3654_, v___y_3655_, v___y_3656_, v___y_3657_, v___y_3658_, v___y_3659_, v___y_3660_);
if (lean_obj_tag(v___x_3695_) == 0)
{
lean_object* v_a_3696_; lean_object* v___x_3698_; uint8_t v_isShared_3699_; uint8_t v_isSharedCheck_3742_; 
v_a_3696_ = lean_ctor_get(v___x_3695_, 0);
v_isSharedCheck_3742_ = !lean_is_exclusive(v___x_3695_);
if (v_isSharedCheck_3742_ == 0)
{
v___x_3698_ = v___x_3695_;
v_isShared_3699_ = v_isSharedCheck_3742_;
goto v_resetjp_3697_;
}
else
{
lean_inc(v_a_3696_);
lean_dec(v___x_3695_);
v___x_3698_ = lean_box(0);
v_isShared_3699_ = v_isSharedCheck_3742_;
goto v_resetjp_3697_;
}
v_resetjp_3697_:
{
lean_object* v___x_3700_; size_t v___x_3701_; size_t v___x_3702_; uint8_t v___x_3703_; 
v___x_3700_ = l_Lean_Expr_appArg_x21(v_a_3696_);
lean_dec(v_a_3696_);
v___x_3701_ = lean_ptr_addr(v___x_3700_);
lean_dec_ref(v___x_3700_);
v___x_3702_ = lean_ptr_addr(v_arg_3681_);
lean_dec_ref(v_arg_3681_);
v___x_3703_ = lean_usize_dec_eq(v___x_3701_, v___x_3702_);
if (v___x_3703_ == 0)
{
lean_object* v___x_3704_; lean_object* v___x_3706_; 
lean_dec_ref(v___f_3663_);
lean_dec_ref(v___f_3662_);
lean_dec_ref(v_e_3649_);
v___x_3704_ = lean_box(0);
if (v_isShared_3699_ == 0)
{
lean_ctor_set(v___x_3698_, 0, v___x_3704_);
v___x_3706_ = v___x_3698_;
goto v_reusejp_3705_;
}
else
{
lean_object* v_reuseFailAlloc_3707_; 
v_reuseFailAlloc_3707_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3707_, 0, v___x_3704_);
v___x_3706_ = v_reuseFailAlloc_3707_;
goto v_reusejp_3705_;
}
v_reusejp_3705_:
{
return v___x_3706_;
}
}
else
{
lean_object* v___x_3708_; 
lean_del_object(v___x_3698_);
v___x_3708_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_modifyRingState___redArg(v___f_3663_, v___y_3650_, v___y_3651_);
if (lean_obj_tag(v___x_3708_) == 0)
{
lean_object* v___x_3709_; 
lean_dec_ref_known(v___x_3708_, 1);
v___x_3709_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRingState___redArg(v___y_3650_, v___y_3651_, v___y_3659_);
if (lean_obj_tag(v___x_3709_) == 0)
{
lean_object* v_a_3710_; uint8_t v_hasIntCast_3711_; 
v_a_3710_ = lean_ctor_get(v___x_3709_, 0);
lean_inc(v_a_3710_);
lean_dec_ref_known(v___x_3709_, 1);
v_hasIntCast_3711_ = lean_ctor_get_uint8(v_a_3710_, sizeof(void*)*5);
lean_dec(v_a_3710_);
if (v_hasIntCast_3711_ == 0)
{
lean_object* v___x_3712_; 
lean_dec_ref(v_e_3649_);
v___x_3712_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_modifyRingState___redArg(v___f_3662_, v___y_3650_, v___y_3651_);
return v___x_3712_;
}
else
{
lean_object* v___x_3713_; 
lean_dec_ref(v___f_3662_);
v___x_3713_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing(v___y_3650_, v___y_3651_, v___y_3652_, v___y_3653_, v___y_3654_, v___y_3655_, v___y_3656_, v___y_3657_, v___y_3658_, v___y_3659_, v___y_3660_);
if (lean_obj_tag(v___x_3713_) == 0)
{
lean_object* v_a_3714_; lean_object* v___x_3715_; 
v_a_3714_ = lean_ctor_get(v___x_3713_, 0);
lean_inc(v_a_3714_);
lean_dec_ref_known(v___x_3713_, 1);
v___x_3715_ = l_Lean_Meta_Sym_Arith_getIntCastFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__1_spec__7(v___y_3650_, v___y_3651_, v___y_3652_, v___y_3653_, v___y_3654_, v___y_3655_, v___y_3656_, v___y_3657_, v___y_3658_, v___y_3659_, v___y_3660_);
if (lean_obj_tag(v___x_3715_) == 0)
{
lean_object* v_a_3716_; lean_object* v___x_3717_; 
v_a_3716_ = lean_ctor_get(v___x_3715_, 0);
lean_inc(v_a_3716_);
lean_dec_ref_known(v___x_3715_, 1);
v___x_3717_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_pushNatCastFact___redArg(v_a_3714_, v_a_3716_, v_e_3649_, v___y_3651_, v___y_3655_, v___y_3656_, v___y_3657_, v___y_3658_, v___y_3659_, v___y_3660_);
return v___x_3717_;
}
else
{
lean_object* v_a_3718_; lean_object* v___x_3720_; uint8_t v_isShared_3721_; uint8_t v_isSharedCheck_3725_; 
lean_dec(v_a_3714_);
lean_dec_ref(v_e_3649_);
v_a_3718_ = lean_ctor_get(v___x_3715_, 0);
v_isSharedCheck_3725_ = !lean_is_exclusive(v___x_3715_);
if (v_isSharedCheck_3725_ == 0)
{
v___x_3720_ = v___x_3715_;
v_isShared_3721_ = v_isSharedCheck_3725_;
goto v_resetjp_3719_;
}
else
{
lean_inc(v_a_3718_);
lean_dec(v___x_3715_);
v___x_3720_ = lean_box(0);
v_isShared_3721_ = v_isSharedCheck_3725_;
goto v_resetjp_3719_;
}
v_resetjp_3719_:
{
lean_object* v___x_3723_; 
if (v_isShared_3721_ == 0)
{
v___x_3723_ = v___x_3720_;
goto v_reusejp_3722_;
}
else
{
lean_object* v_reuseFailAlloc_3724_; 
v_reuseFailAlloc_3724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3724_, 0, v_a_3718_);
v___x_3723_ = v_reuseFailAlloc_3724_;
goto v_reusejp_3722_;
}
v_reusejp_3722_:
{
return v___x_3723_;
}
}
}
}
else
{
lean_object* v_a_3726_; lean_object* v___x_3728_; uint8_t v_isShared_3729_; uint8_t v_isSharedCheck_3733_; 
lean_dec_ref(v_e_3649_);
v_a_3726_ = lean_ctor_get(v___x_3713_, 0);
v_isSharedCheck_3733_ = !lean_is_exclusive(v___x_3713_);
if (v_isSharedCheck_3733_ == 0)
{
v___x_3728_ = v___x_3713_;
v_isShared_3729_ = v_isSharedCheck_3733_;
goto v_resetjp_3727_;
}
else
{
lean_inc(v_a_3726_);
lean_dec(v___x_3713_);
v___x_3728_ = lean_box(0);
v_isShared_3729_ = v_isSharedCheck_3733_;
goto v_resetjp_3727_;
}
v_resetjp_3727_:
{
lean_object* v___x_3731_; 
if (v_isShared_3729_ == 0)
{
v___x_3731_ = v___x_3728_;
goto v_reusejp_3730_;
}
else
{
lean_object* v_reuseFailAlloc_3732_; 
v_reuseFailAlloc_3732_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3732_, 0, v_a_3726_);
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
}
else
{
lean_object* v_a_3734_; lean_object* v___x_3736_; uint8_t v_isShared_3737_; uint8_t v_isSharedCheck_3741_; 
lean_dec_ref(v___f_3662_);
lean_dec_ref(v_e_3649_);
v_a_3734_ = lean_ctor_get(v___x_3709_, 0);
v_isSharedCheck_3741_ = !lean_is_exclusive(v___x_3709_);
if (v_isSharedCheck_3741_ == 0)
{
v___x_3736_ = v___x_3709_;
v_isShared_3737_ = v_isSharedCheck_3741_;
goto v_resetjp_3735_;
}
else
{
lean_inc(v_a_3734_);
lean_dec(v___x_3709_);
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
lean_dec_ref(v___f_3662_);
lean_dec_ref(v_e_3649_);
return v___x_3708_;
}
}
}
}
else
{
lean_object* v_a_3743_; lean_object* v___x_3745_; uint8_t v_isShared_3746_; uint8_t v_isSharedCheck_3750_; 
lean_dec_ref(v_arg_3681_);
lean_dec_ref(v___f_3663_);
lean_dec_ref(v___f_3662_);
lean_dec_ref(v_e_3649_);
v_a_3743_ = lean_ctor_get(v___x_3695_, 0);
v_isSharedCheck_3750_ = !lean_is_exclusive(v___x_3695_);
if (v_isSharedCheck_3750_ == 0)
{
v___x_3745_ = v___x_3695_;
v_isShared_3746_ = v_isSharedCheck_3750_;
goto v_resetjp_3744_;
}
else
{
lean_inc(v_a_3743_);
lean_dec(v___x_3695_);
v___x_3745_ = lean_box(0);
v_isShared_3746_ = v_isSharedCheck_3750_;
goto v_resetjp_3744_;
}
v_resetjp_3744_:
{
lean_object* v___x_3748_; 
if (v_isShared_3746_ == 0)
{
v___x_3748_ = v___x_3745_;
goto v_reusejp_3747_;
}
else
{
lean_object* v_reuseFailAlloc_3749_; 
v_reuseFailAlloc_3749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3749_, 0, v_a_3743_);
v___x_3748_ = v_reuseFailAlloc_3749_;
goto v_reusejp_3747_;
}
v_reusejp_3747_:
{
return v___x_3748_;
}
}
}
}
else
{
lean_object* v___x_3751_; lean_object* v___x_3753_; 
lean_dec_ref(v_arg_3681_);
lean_dec_ref(v___f_3663_);
lean_dec_ref(v___f_3662_);
lean_dec_ref(v_e_3649_);
v___x_3751_ = lean_box(0);
if (v_isShared_3692_ == 0)
{
lean_ctor_set(v___x_3691_, 0, v___x_3751_);
v___x_3753_ = v___x_3691_;
goto v_reusejp_3752_;
}
else
{
lean_object* v_reuseFailAlloc_3754_; 
v_reuseFailAlloc_3754_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3754_, 0, v___x_3751_);
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
lean_object* v_a_3756_; lean_object* v___x_3758_; uint8_t v_isShared_3759_; uint8_t v_isSharedCheck_3763_; 
lean_dec_ref(v_arg_3681_);
lean_dec_ref(v___f_3663_);
lean_dec_ref(v___f_3662_);
lean_dec_ref(v_e_3649_);
v_a_3756_ = lean_ctor_get(v___x_3688_, 0);
v_isSharedCheck_3763_ = !lean_is_exclusive(v___x_3688_);
if (v_isSharedCheck_3763_ == 0)
{
v___x_3758_ = v___x_3688_;
v_isShared_3759_ = v_isSharedCheck_3763_;
goto v_resetjp_3757_;
}
else
{
lean_inc(v_a_3756_);
lean_dec(v___x_3688_);
v___x_3758_ = lean_box(0);
v_isShared_3759_ = v_isSharedCheck_3763_;
goto v_resetjp_3757_;
}
v_resetjp_3757_:
{
lean_object* v___x_3761_; 
if (v_isShared_3759_ == 0)
{
v___x_3761_ = v___x_3758_;
goto v_reusejp_3760_;
}
else
{
lean_object* v_reuseFailAlloc_3762_; 
v_reuseFailAlloc_3762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3762_, 0, v_a_3756_);
v___x_3761_ = v_reuseFailAlloc_3762_;
goto v_reusejp_3760_;
}
v_reusejp_3760_:
{
return v___x_3761_;
}
}
}
}
else
{
lean_object* v___x_3764_; lean_object* v___x_3765_; 
lean_dec_ref(v_arg_3681_);
lean_dec_ref(v___f_3663_);
lean_dec_ref(v___f_3662_);
lean_dec_ref(v_e_3649_);
v___x_3764_ = lean_box(0);
v___x_3765_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3765_, 0, v___x_3764_);
return v___x_3765_;
}
}
}
else
{
lean_object* v___x_3766_; lean_object* v___f_3767_; lean_object* v___x_3768_; 
lean_dec_ref(v___x_3682_);
lean_del_object(v___x_3667_);
lean_dec_ref(v___f_3663_);
lean_dec_ref(v___f_3662_);
lean_dec_ref(v_e_3649_);
v___x_3766_ = lean_box(v___x_3684_);
v___f_3767_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___redArg___lam__8___boxed), 2, 1);
lean_closure_set(v___f_3767_, 0, v___x_3766_);
v___x_3768_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRingState___redArg(v___y_3650_, v___y_3651_, v___y_3659_);
if (lean_obj_tag(v___x_3768_) == 0)
{
lean_object* v_a_3769_; lean_object* v___x_3771_; uint8_t v_isShared_3772_; uint8_t v_isSharedCheck_3839_; 
v_a_3769_ = lean_ctor_get(v___x_3768_, 0);
v_isSharedCheck_3839_ = !lean_is_exclusive(v___x_3768_);
if (v_isSharedCheck_3839_ == 0)
{
v___x_3771_ = v___x_3768_;
v_isShared_3772_ = v_isSharedCheck_3839_;
goto v_resetjp_3770_;
}
else
{
lean_inc(v_a_3769_);
lean_dec(v___x_3768_);
v___x_3771_ = lean_box(0);
v_isShared_3772_ = v_isSharedCheck_3839_;
goto v_resetjp_3770_;
}
v_resetjp_3770_:
{
uint8_t v_hasIntCast_3773_; 
v_hasIntCast_3773_ = lean_ctor_get_uint8(v_a_3769_, sizeof(void*)*5);
lean_dec(v_a_3769_);
if (v_hasIntCast_3773_ == 0)
{
lean_object* v___x_3774_; 
v___x_3774_ = l_Lean_Meta_Sym_getIntValue_x3f(v_arg_3680_);
lean_dec_ref(v_arg_3680_);
if (lean_obj_tag(v___x_3774_) == 0)
{
lean_object* v___x_3775_; 
lean_del_object(v___x_3771_);
v___x_3775_ = l_Lean_Meta_Sym_Arith_getIntCastFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__1_spec__7(v___y_3650_, v___y_3651_, v___y_3652_, v___y_3653_, v___y_3654_, v___y_3655_, v___y_3656_, v___y_3657_, v___y_3658_, v___y_3659_, v___y_3660_);
if (lean_obj_tag(v___x_3775_) == 0)
{
lean_object* v_a_3776_; lean_object* v___x_3778_; uint8_t v_isShared_3779_; uint8_t v_isSharedCheck_3822_; 
v_a_3776_ = lean_ctor_get(v___x_3775_, 0);
v_isSharedCheck_3822_ = !lean_is_exclusive(v___x_3775_);
if (v_isSharedCheck_3822_ == 0)
{
v___x_3778_ = v___x_3775_;
v_isShared_3779_ = v_isSharedCheck_3822_;
goto v_resetjp_3777_;
}
else
{
lean_inc(v_a_3776_);
lean_dec(v___x_3775_);
v___x_3778_ = lean_box(0);
v_isShared_3779_ = v_isSharedCheck_3822_;
goto v_resetjp_3777_;
}
v_resetjp_3777_:
{
lean_object* v___x_3780_; size_t v___x_3781_; size_t v___x_3782_; uint8_t v___x_3783_; 
v___x_3780_ = l_Lean_Expr_appArg_x21(v_a_3776_);
lean_dec(v_a_3776_);
v___x_3781_ = lean_ptr_addr(v___x_3780_);
lean_dec_ref(v___x_3780_);
v___x_3782_ = lean_ptr_addr(v_arg_3681_);
lean_dec_ref(v_arg_3681_);
v___x_3783_ = lean_usize_dec_eq(v___x_3781_, v___x_3782_);
if (v___x_3783_ == 0)
{
lean_object* v___x_3784_; lean_object* v___x_3786_; 
lean_dec_ref(v___f_3767_);
v___x_3784_ = lean_box(0);
if (v_isShared_3779_ == 0)
{
lean_ctor_set(v___x_3778_, 0, v___x_3784_);
v___x_3786_ = v___x_3778_;
goto v_reusejp_3785_;
}
else
{
lean_object* v_reuseFailAlloc_3787_; 
v_reuseFailAlloc_3787_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3787_, 0, v___x_3784_);
v___x_3786_ = v_reuseFailAlloc_3787_;
goto v_reusejp_3785_;
}
v_reusejp_3785_:
{
return v___x_3786_;
}
}
else
{
lean_object* v___x_3788_; 
lean_del_object(v___x_3778_);
v___x_3788_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRingState___redArg(v___y_3650_, v___y_3651_, v___y_3659_);
if (lean_obj_tag(v___x_3788_) == 0)
{
lean_object* v_a_3789_; lean_object* v_natCasts_3790_; lean_object* v___x_3791_; 
v_a_3789_ = lean_ctor_get(v___x_3788_, 0);
lean_inc(v_a_3789_);
lean_dec_ref_known(v___x_3788_, 1);
v_natCasts_3790_ = lean_ctor_get(v_a_3789_, 4);
lean_inc_ref(v_natCasts_3790_);
lean_dec(v_a_3789_);
v___x_3791_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_modifyRingState___redArg(v___f_3767_, v___y_3650_, v___y_3651_);
if (lean_obj_tag(v___x_3791_) == 0)
{
lean_object* v___x_3792_; 
lean_dec_ref_known(v___x_3791_, 1);
v___x_3792_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing(v___y_3650_, v___y_3651_, v___y_3652_, v___y_3653_, v___y_3654_, v___y_3655_, v___y_3656_, v___y_3657_, v___y_3658_, v___y_3659_, v___y_3660_);
if (lean_obj_tag(v___x_3792_) == 0)
{
lean_object* v_a_3793_; lean_object* v___x_3794_; 
v_a_3793_ = lean_ctor_get(v___x_3792_, 0);
lean_inc(v_a_3793_);
lean_dec_ref_known(v___x_3792_, 1);
v___x_3794_ = l_Lean_Meta_Sym_Arith_getIntCastFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__1_spec__7(v___y_3650_, v___y_3651_, v___y_3652_, v___y_3653_, v___y_3654_, v___y_3655_, v___y_3656_, v___y_3657_, v___y_3658_, v___y_3659_, v___y_3660_);
if (lean_obj_tag(v___x_3794_) == 0)
{
lean_object* v_a_3795_; lean_object* v___x_3796_; lean_object* v___x_3797_; 
v_a_3795_ = lean_ctor_get(v___x_3794_, 0);
lean_inc(v_a_3795_);
lean_dec_ref_known(v___x_3794_, 1);
v___x_3796_ = lean_unsigned_to_nat(0u);
v___x_3797_ = l_Lean_PersistentArray_forM___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__1_spec__8(v_a_3793_, v_a_3795_, v_natCasts_3790_, v___x_3796_, v___y_3650_, v___y_3651_, v___y_3652_, v___y_3653_, v___y_3654_, v___y_3655_, v___y_3656_, v___y_3657_, v___y_3658_, v___y_3659_, v___y_3660_);
return v___x_3797_;
}
else
{
lean_object* v_a_3798_; lean_object* v___x_3800_; uint8_t v_isShared_3801_; uint8_t v_isSharedCheck_3805_; 
lean_dec(v_a_3793_);
lean_dec_ref(v_natCasts_3790_);
v_a_3798_ = lean_ctor_get(v___x_3794_, 0);
v_isSharedCheck_3805_ = !lean_is_exclusive(v___x_3794_);
if (v_isSharedCheck_3805_ == 0)
{
v___x_3800_ = v___x_3794_;
v_isShared_3801_ = v_isSharedCheck_3805_;
goto v_resetjp_3799_;
}
else
{
lean_inc(v_a_3798_);
lean_dec(v___x_3794_);
v___x_3800_ = lean_box(0);
v_isShared_3801_ = v_isSharedCheck_3805_;
goto v_resetjp_3799_;
}
v_resetjp_3799_:
{
lean_object* v___x_3803_; 
if (v_isShared_3801_ == 0)
{
v___x_3803_ = v___x_3800_;
goto v_reusejp_3802_;
}
else
{
lean_object* v_reuseFailAlloc_3804_; 
v_reuseFailAlloc_3804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3804_, 0, v_a_3798_);
v___x_3803_ = v_reuseFailAlloc_3804_;
goto v_reusejp_3802_;
}
v_reusejp_3802_:
{
return v___x_3803_;
}
}
}
}
else
{
lean_object* v_a_3806_; lean_object* v___x_3808_; uint8_t v_isShared_3809_; uint8_t v_isSharedCheck_3813_; 
lean_dec_ref(v_natCasts_3790_);
v_a_3806_ = lean_ctor_get(v___x_3792_, 0);
v_isSharedCheck_3813_ = !lean_is_exclusive(v___x_3792_);
if (v_isSharedCheck_3813_ == 0)
{
v___x_3808_ = v___x_3792_;
v_isShared_3809_ = v_isSharedCheck_3813_;
goto v_resetjp_3807_;
}
else
{
lean_inc(v_a_3806_);
lean_dec(v___x_3792_);
v___x_3808_ = lean_box(0);
v_isShared_3809_ = v_isSharedCheck_3813_;
goto v_resetjp_3807_;
}
v_resetjp_3807_:
{
lean_object* v___x_3811_; 
if (v_isShared_3809_ == 0)
{
v___x_3811_ = v___x_3808_;
goto v_reusejp_3810_;
}
else
{
lean_object* v_reuseFailAlloc_3812_; 
v_reuseFailAlloc_3812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3812_, 0, v_a_3806_);
v___x_3811_ = v_reuseFailAlloc_3812_;
goto v_reusejp_3810_;
}
v_reusejp_3810_:
{
return v___x_3811_;
}
}
}
}
else
{
lean_dec_ref(v_natCasts_3790_);
return v___x_3791_;
}
}
else
{
lean_object* v_a_3814_; lean_object* v___x_3816_; uint8_t v_isShared_3817_; uint8_t v_isSharedCheck_3821_; 
lean_dec_ref(v___f_3767_);
v_a_3814_ = lean_ctor_get(v___x_3788_, 0);
v_isSharedCheck_3821_ = !lean_is_exclusive(v___x_3788_);
if (v_isSharedCheck_3821_ == 0)
{
v___x_3816_ = v___x_3788_;
v_isShared_3817_ = v_isSharedCheck_3821_;
goto v_resetjp_3815_;
}
else
{
lean_inc(v_a_3814_);
lean_dec(v___x_3788_);
v___x_3816_ = lean_box(0);
v_isShared_3817_ = v_isSharedCheck_3821_;
goto v_resetjp_3815_;
}
v_resetjp_3815_:
{
lean_object* v___x_3819_; 
if (v_isShared_3817_ == 0)
{
v___x_3819_ = v___x_3816_;
goto v_reusejp_3818_;
}
else
{
lean_object* v_reuseFailAlloc_3820_; 
v_reuseFailAlloc_3820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3820_, 0, v_a_3814_);
v___x_3819_ = v_reuseFailAlloc_3820_;
goto v_reusejp_3818_;
}
v_reusejp_3818_:
{
return v___x_3819_;
}
}
}
}
}
}
else
{
lean_object* v_a_3823_; lean_object* v___x_3825_; uint8_t v_isShared_3826_; uint8_t v_isSharedCheck_3830_; 
lean_dec_ref(v___f_3767_);
lean_dec_ref(v_arg_3681_);
v_a_3823_ = lean_ctor_get(v___x_3775_, 0);
v_isSharedCheck_3830_ = !lean_is_exclusive(v___x_3775_);
if (v_isSharedCheck_3830_ == 0)
{
v___x_3825_ = v___x_3775_;
v_isShared_3826_ = v_isSharedCheck_3830_;
goto v_resetjp_3824_;
}
else
{
lean_inc(v_a_3823_);
lean_dec(v___x_3775_);
v___x_3825_ = lean_box(0);
v_isShared_3826_ = v_isSharedCheck_3830_;
goto v_resetjp_3824_;
}
v_resetjp_3824_:
{
lean_object* v___x_3828_; 
if (v_isShared_3826_ == 0)
{
v___x_3828_ = v___x_3825_;
goto v_reusejp_3827_;
}
else
{
lean_object* v_reuseFailAlloc_3829_; 
v_reuseFailAlloc_3829_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3829_, 0, v_a_3823_);
v___x_3828_ = v_reuseFailAlloc_3829_;
goto v_reusejp_3827_;
}
v_reusejp_3827_:
{
return v___x_3828_;
}
}
}
}
else
{
lean_object* v___x_3831_; lean_object* v___x_3833_; 
lean_dec_ref_known(v___x_3774_, 1);
lean_dec_ref(v___f_3767_);
lean_dec_ref(v_arg_3681_);
v___x_3831_ = lean_box(0);
if (v_isShared_3772_ == 0)
{
lean_ctor_set(v___x_3771_, 0, v___x_3831_);
v___x_3833_ = v___x_3771_;
goto v_reusejp_3832_;
}
else
{
lean_object* v_reuseFailAlloc_3834_; 
v_reuseFailAlloc_3834_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3834_, 0, v___x_3831_);
v___x_3833_ = v_reuseFailAlloc_3834_;
goto v_reusejp_3832_;
}
v_reusejp_3832_:
{
return v___x_3833_;
}
}
}
else
{
lean_object* v___x_3835_; lean_object* v___x_3837_; 
lean_dec_ref(v___f_3767_);
lean_dec_ref(v_arg_3681_);
lean_dec_ref(v_arg_3680_);
v___x_3835_ = lean_box(0);
if (v_isShared_3772_ == 0)
{
lean_ctor_set(v___x_3771_, 0, v___x_3835_);
v___x_3837_ = v___x_3771_;
goto v_reusejp_3836_;
}
else
{
lean_object* v_reuseFailAlloc_3838_; 
v_reuseFailAlloc_3838_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3838_, 0, v___x_3835_);
v___x_3837_ = v_reuseFailAlloc_3838_;
goto v_reusejp_3836_;
}
v_reusejp_3836_:
{
return v___x_3837_;
}
}
}
}
else
{
lean_object* v_a_3840_; lean_object* v___x_3842_; uint8_t v_isShared_3843_; uint8_t v_isSharedCheck_3847_; 
lean_dec_ref(v___f_3767_);
lean_dec_ref(v_arg_3681_);
lean_dec_ref(v_arg_3680_);
v_a_3840_ = lean_ctor_get(v___x_3768_, 0);
v_isSharedCheck_3847_ = !lean_is_exclusive(v___x_3768_);
if (v_isSharedCheck_3847_ == 0)
{
v___x_3842_ = v___x_3768_;
v_isShared_3843_ = v_isSharedCheck_3847_;
goto v_resetjp_3841_;
}
else
{
lean_inc(v_a_3840_);
lean_dec(v___x_3768_);
v___x_3842_ = lean_box(0);
v_isShared_3843_ = v_isSharedCheck_3847_;
goto v_resetjp_3841_;
}
v_resetjp_3841_:
{
lean_object* v___x_3845_; 
if (v_isShared_3843_ == 0)
{
v___x_3845_ = v___x_3842_;
goto v_reusejp_3844_;
}
else
{
lean_object* v_reuseFailAlloc_3846_; 
v_reuseFailAlloc_3846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3846_, 0, v_a_3840_);
v___x_3845_ = v_reuseFailAlloc_3846_;
goto v_reusejp_3844_;
}
v_reusejp_3844_:
{
return v___x_3845_;
}
}
}
}
}
}
}
v___jp_3669_:
{
lean_object* v___x_3670_; lean_object* v___x_3672_; 
v___x_3670_ = lean_box(0);
if (v_isShared_3668_ == 0)
{
lean_ctor_set(v___x_3667_, 0, v___x_3670_);
v___x_3672_ = v___x_3667_;
goto v_reusejp_3671_;
}
else
{
lean_object* v_reuseFailAlloc_3673_; 
v_reuseFailAlloc_3673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3673_, 0, v___x_3670_);
v___x_3672_ = v_reuseFailAlloc_3673_;
goto v_reusejp_3671_;
}
v_reusejp_3671_:
{
return v___x_3672_;
}
}
}
}
else
{
lean_object* v_a_3849_; lean_object* v___x_3851_; uint8_t v_isShared_3852_; uint8_t v_isSharedCheck_3856_; 
lean_dec_ref(v___f_3663_);
lean_dec_ref(v___f_3662_);
lean_dec_ref(v_e_3649_);
v_a_3849_ = lean_ctor_get(v___x_3664_, 0);
v_isSharedCheck_3856_ = !lean_is_exclusive(v___x_3664_);
if (v_isSharedCheck_3856_ == 0)
{
v___x_3851_ = v___x_3664_;
v_isShared_3852_ = v_isSharedCheck_3856_;
goto v_resetjp_3850_;
}
else
{
lean_inc(v_a_3849_);
lean_dec(v___x_3664_);
v___x_3851_ = lean_box(0);
v_isShared_3852_ = v_isSharedCheck_3856_;
goto v_resetjp_3850_;
}
v_resetjp_3850_:
{
lean_object* v___x_3854_; 
if (v_isShared_3852_ == 0)
{
v___x_3854_ = v___x_3851_;
goto v_reusejp_3853_;
}
else
{
lean_object* v_reuseFailAlloc_3855_; 
v_reuseFailAlloc_3855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3855_, 0, v_a_3849_);
v___x_3854_ = v_reuseFailAlloc_3855_;
goto v_reusejp_3853_;
}
v_reusejp_3853_:
{
return v___x_3854_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__1___boxed(lean_object* v_e_3857_, lean_object* v___y_3858_, lean_object* v___y_3859_, lean_object* v___y_3860_, lean_object* v___y_3861_, lean_object* v___y_3862_, lean_object* v___y_3863_, lean_object* v___y_3864_, lean_object* v___y_3865_, lean_object* v___y_3866_, lean_object* v___y_3867_, lean_object* v___y_3868_, lean_object* v___y_3869_){
_start:
{
lean_object* v_res_3870_; 
v_res_3870_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__1(v_e_3857_, v___y_3858_, v___y_3859_, v___y_3860_, v___y_3861_, v___y_3862_, v___y_3863_, v___y_3864_, v___y_3865_, v___y_3866_, v___y_3867_, v___y_3868_);
lean_dec(v___y_3868_);
lean_dec_ref(v___y_3867_);
lean_dec(v___y_3866_);
lean_dec_ref(v___y_3865_);
lean_dec(v___y_3864_);
lean_dec_ref(v___y_3863_);
lean_dec(v___y_3862_);
lean_dec_ref(v___y_3861_);
lean_dec(v___y_3860_);
lean_dec(v___y_3859_);
lean_dec(v___y_3858_);
return v_res_3870_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getIntCastFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0_spec__3___lam__0(lean_object* v_a_3871_, lean_object* v_s_3872_){
_start:
{
lean_object* v_toRing_3873_; lean_object* v_invFn_x3f_3874_; lean_object* v_divFn_x3f_3875_; lean_object* v_zpowFn_x3f_3876_; lean_object* v_semiringId_x3f_3877_; lean_object* v_commSemiringInst_3878_; lean_object* v_commRingInst_3879_; lean_object* v_noZeroDivInst_x3f_3880_; lean_object* v_fieldInst_x3f_3881_; lean_object* v_powIdentityInst_x3f_3882_; lean_object* v___x_3884_; uint8_t v_isShared_3885_; uint8_t v_isSharedCheck_3914_; 
v_toRing_3873_ = lean_ctor_get(v_s_3872_, 0);
v_invFn_x3f_3874_ = lean_ctor_get(v_s_3872_, 1);
v_divFn_x3f_3875_ = lean_ctor_get(v_s_3872_, 2);
v_zpowFn_x3f_3876_ = lean_ctor_get(v_s_3872_, 3);
v_semiringId_x3f_3877_ = lean_ctor_get(v_s_3872_, 4);
v_commSemiringInst_3878_ = lean_ctor_get(v_s_3872_, 5);
v_commRingInst_3879_ = lean_ctor_get(v_s_3872_, 6);
v_noZeroDivInst_x3f_3880_ = lean_ctor_get(v_s_3872_, 7);
v_fieldInst_x3f_3881_ = lean_ctor_get(v_s_3872_, 8);
v_powIdentityInst_x3f_3882_ = lean_ctor_get(v_s_3872_, 9);
v_isSharedCheck_3914_ = !lean_is_exclusive(v_s_3872_);
if (v_isSharedCheck_3914_ == 0)
{
v___x_3884_ = v_s_3872_;
v_isShared_3885_ = v_isSharedCheck_3914_;
goto v_resetjp_3883_;
}
else
{
lean_inc(v_powIdentityInst_x3f_3882_);
lean_inc(v_fieldInst_x3f_3881_);
lean_inc(v_noZeroDivInst_x3f_3880_);
lean_inc(v_commRingInst_3879_);
lean_inc(v_commSemiringInst_3878_);
lean_inc(v_semiringId_x3f_3877_);
lean_inc(v_zpowFn_x3f_3876_);
lean_inc(v_divFn_x3f_3875_);
lean_inc(v_invFn_x3f_3874_);
lean_inc(v_toRing_3873_);
lean_dec(v_s_3872_);
v___x_3884_ = lean_box(0);
v_isShared_3885_ = v_isSharedCheck_3914_;
goto v_resetjp_3883_;
}
v_resetjp_3883_:
{
lean_object* v_id_3886_; lean_object* v_type_3887_; lean_object* v_u_3888_; lean_object* v_ringInst_3889_; lean_object* v_semiringInst_3890_; lean_object* v_charInst_x3f_3891_; uint8_t v_symbolicChar_3892_; lean_object* v_addFn_x3f_3893_; lean_object* v_mulFn_x3f_3894_; lean_object* v_subFn_x3f_3895_; lean_object* v_negFn_x3f_3896_; lean_object* v_powFn_x3f_3897_; lean_object* v_natCastFn_x3f_3898_; lean_object* v_natSMulFn_x3f_3899_; lean_object* v_intSMulFn_x3f_3900_; lean_object* v_one_x3f_3901_; lean_object* v___x_3903_; uint8_t v_isShared_3904_; uint8_t v_isSharedCheck_3912_; 
v_id_3886_ = lean_ctor_get(v_toRing_3873_, 0);
v_type_3887_ = lean_ctor_get(v_toRing_3873_, 1);
v_u_3888_ = lean_ctor_get(v_toRing_3873_, 2);
v_ringInst_3889_ = lean_ctor_get(v_toRing_3873_, 3);
v_semiringInst_3890_ = lean_ctor_get(v_toRing_3873_, 4);
v_charInst_x3f_3891_ = lean_ctor_get(v_toRing_3873_, 5);
v_symbolicChar_3892_ = lean_ctor_get_uint8(v_toRing_3873_, sizeof(void*)*16);
v_addFn_x3f_3893_ = lean_ctor_get(v_toRing_3873_, 6);
v_mulFn_x3f_3894_ = lean_ctor_get(v_toRing_3873_, 7);
v_subFn_x3f_3895_ = lean_ctor_get(v_toRing_3873_, 8);
v_negFn_x3f_3896_ = lean_ctor_get(v_toRing_3873_, 9);
v_powFn_x3f_3897_ = lean_ctor_get(v_toRing_3873_, 10);
v_natCastFn_x3f_3898_ = lean_ctor_get(v_toRing_3873_, 12);
v_natSMulFn_x3f_3899_ = lean_ctor_get(v_toRing_3873_, 13);
v_intSMulFn_x3f_3900_ = lean_ctor_get(v_toRing_3873_, 14);
v_one_x3f_3901_ = lean_ctor_get(v_toRing_3873_, 15);
v_isSharedCheck_3912_ = !lean_is_exclusive(v_toRing_3873_);
if (v_isSharedCheck_3912_ == 0)
{
lean_object* v_unused_3913_; 
v_unused_3913_ = lean_ctor_get(v_toRing_3873_, 11);
lean_dec(v_unused_3913_);
v___x_3903_ = v_toRing_3873_;
v_isShared_3904_ = v_isSharedCheck_3912_;
goto v_resetjp_3902_;
}
else
{
lean_inc(v_one_x3f_3901_);
lean_inc(v_intSMulFn_x3f_3900_);
lean_inc(v_natSMulFn_x3f_3899_);
lean_inc(v_natCastFn_x3f_3898_);
lean_inc(v_powFn_x3f_3897_);
lean_inc(v_negFn_x3f_3896_);
lean_inc(v_subFn_x3f_3895_);
lean_inc(v_mulFn_x3f_3894_);
lean_inc(v_addFn_x3f_3893_);
lean_inc(v_charInst_x3f_3891_);
lean_inc(v_semiringInst_3890_);
lean_inc(v_ringInst_3889_);
lean_inc(v_u_3888_);
lean_inc(v_type_3887_);
lean_inc(v_id_3886_);
lean_dec(v_toRing_3873_);
v___x_3903_ = lean_box(0);
v_isShared_3904_ = v_isSharedCheck_3912_;
goto v_resetjp_3902_;
}
v_resetjp_3902_:
{
lean_object* v___x_3905_; lean_object* v___x_3907_; 
v___x_3905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3905_, 0, v_a_3871_);
if (v_isShared_3904_ == 0)
{
lean_ctor_set(v___x_3903_, 11, v___x_3905_);
v___x_3907_ = v___x_3903_;
goto v_reusejp_3906_;
}
else
{
lean_object* v_reuseFailAlloc_3911_; 
v_reuseFailAlloc_3911_ = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(v_reuseFailAlloc_3911_, 0, v_id_3886_);
lean_ctor_set(v_reuseFailAlloc_3911_, 1, v_type_3887_);
lean_ctor_set(v_reuseFailAlloc_3911_, 2, v_u_3888_);
lean_ctor_set(v_reuseFailAlloc_3911_, 3, v_ringInst_3889_);
lean_ctor_set(v_reuseFailAlloc_3911_, 4, v_semiringInst_3890_);
lean_ctor_set(v_reuseFailAlloc_3911_, 5, v_charInst_x3f_3891_);
lean_ctor_set(v_reuseFailAlloc_3911_, 6, v_addFn_x3f_3893_);
lean_ctor_set(v_reuseFailAlloc_3911_, 7, v_mulFn_x3f_3894_);
lean_ctor_set(v_reuseFailAlloc_3911_, 8, v_subFn_x3f_3895_);
lean_ctor_set(v_reuseFailAlloc_3911_, 9, v_negFn_x3f_3896_);
lean_ctor_set(v_reuseFailAlloc_3911_, 10, v_powFn_x3f_3897_);
lean_ctor_set(v_reuseFailAlloc_3911_, 11, v___x_3905_);
lean_ctor_set(v_reuseFailAlloc_3911_, 12, v_natCastFn_x3f_3898_);
lean_ctor_set(v_reuseFailAlloc_3911_, 13, v_natSMulFn_x3f_3899_);
lean_ctor_set(v_reuseFailAlloc_3911_, 14, v_intSMulFn_x3f_3900_);
lean_ctor_set(v_reuseFailAlloc_3911_, 15, v_one_x3f_3901_);
lean_ctor_set_uint8(v_reuseFailAlloc_3911_, sizeof(void*)*16, v_symbolicChar_3892_);
v___x_3907_ = v_reuseFailAlloc_3911_;
goto v_reusejp_3906_;
}
v_reusejp_3906_:
{
lean_object* v___x_3909_; 
if (v_isShared_3885_ == 0)
{
lean_ctor_set(v___x_3884_, 0, v___x_3907_);
v___x_3909_ = v___x_3884_;
goto v_reusejp_3908_;
}
else
{
lean_object* v_reuseFailAlloc_3910_; 
v_reuseFailAlloc_3910_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3910_, 0, v___x_3907_);
lean_ctor_set(v_reuseFailAlloc_3910_, 1, v_invFn_x3f_3874_);
lean_ctor_set(v_reuseFailAlloc_3910_, 2, v_divFn_x3f_3875_);
lean_ctor_set(v_reuseFailAlloc_3910_, 3, v_zpowFn_x3f_3876_);
lean_ctor_set(v_reuseFailAlloc_3910_, 4, v_semiringId_x3f_3877_);
lean_ctor_set(v_reuseFailAlloc_3910_, 5, v_commSemiringInst_3878_);
lean_ctor_set(v_reuseFailAlloc_3910_, 6, v_commRingInst_3879_);
lean_ctor_set(v_reuseFailAlloc_3910_, 7, v_noZeroDivInst_x3f_3880_);
lean_ctor_set(v_reuseFailAlloc_3910_, 8, v_fieldInst_x3f_3881_);
lean_ctor_set(v_reuseFailAlloc_3910_, 9, v_powIdentityInst_x3f_3882_);
v___x_3909_ = v_reuseFailAlloc_3910_;
goto v_reusejp_3908_;
}
v_reusejp_3908_:
{
return v___x_3909_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getIntCastFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0_spec__3(lean_object* v___y_3915_, lean_object* v___y_3916_, lean_object* v___y_3917_, lean_object* v___y_3918_, lean_object* v___y_3919_, lean_object* v___y_3920_, lean_object* v___y_3921_, lean_object* v___y_3922_, lean_object* v___y_3923_, lean_object* v___y_3924_, lean_object* v___y_3925_){
_start:
{
lean_object* v___x_3927_; 
v___x_3927_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v___y_3915_, v___y_3916_, v___y_3917_, v___y_3918_, v___y_3919_, v___y_3920_, v___y_3921_, v___y_3922_, v___y_3923_, v___y_3924_, v___y_3925_);
if (lean_obj_tag(v___x_3927_) == 0)
{
lean_object* v_a_3928_; lean_object* v___x_3930_; uint8_t v_isShared_3931_; uint8_t v_isSharedCheck_4004_; 
v_a_3928_ = lean_ctor_get(v___x_3927_, 0);
v_isSharedCheck_4004_ = !lean_is_exclusive(v___x_3927_);
if (v_isSharedCheck_4004_ == 0)
{
v___x_3930_ = v___x_3927_;
v_isShared_3931_ = v_isSharedCheck_4004_;
goto v_resetjp_3929_;
}
else
{
lean_inc(v_a_3928_);
lean_dec(v___x_3927_);
v___x_3930_ = lean_box(0);
v_isShared_3931_ = v_isSharedCheck_4004_;
goto v_resetjp_3929_;
}
v_resetjp_3929_:
{
lean_object* v_toRing_3932_; lean_object* v_intCastFn_x3f_3933_; 
v_toRing_3932_ = lean_ctor_get(v_a_3928_, 0);
lean_inc_ref(v_toRing_3932_);
lean_dec(v_a_3928_);
v_intCastFn_x3f_3933_ = lean_ctor_get(v_toRing_3932_, 11);
if (lean_obj_tag(v_intCastFn_x3f_3933_) == 1)
{
lean_object* v_val_3934_; lean_object* v___x_3936_; 
lean_inc_ref(v_intCastFn_x3f_3933_);
lean_dec_ref(v_toRing_3932_);
v_val_3934_ = lean_ctor_get(v_intCastFn_x3f_3933_, 0);
lean_inc(v_val_3934_);
lean_dec_ref_known(v_intCastFn_x3f_3933_, 1);
if (v_isShared_3931_ == 0)
{
lean_ctor_set(v___x_3930_, 0, v_val_3934_);
v___x_3936_ = v___x_3930_;
goto v_reusejp_3935_;
}
else
{
lean_object* v_reuseFailAlloc_3937_; 
v_reuseFailAlloc_3937_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3937_, 0, v_val_3934_);
v___x_3936_ = v_reuseFailAlloc_3937_;
goto v_reusejp_3935_;
}
v_reusejp_3935_:
{
return v___x_3936_;
}
}
else
{
lean_object* v_type_3938_; lean_object* v_u_3939_; lean_object* v_ringInst_3940_; lean_object* v___x_3941_; lean_object* v___x_3942_; lean_object* v___x_3943_; lean_object* v___x_3944_; lean_object* v_inst_x27_3945_; lean_object* v_inst_3947_; lean_object* v___y_3948_; lean_object* v___y_3949_; lean_object* v___y_3950_; lean_object* v___y_3951_; lean_object* v___y_3952_; lean_object* v___y_3953_; lean_object* v___y_3954_; lean_object* v___x_3980_; lean_object* v___x_3981_; lean_object* v_instType_3982_; lean_object* v___x_3983_; 
lean_del_object(v___x_3930_);
v_type_3938_ = lean_ctor_get(v_toRing_3932_, 1);
lean_inc_ref_n(v_type_3938_, 3);
v_u_3939_ = lean_ctor_get(v_toRing_3932_, 2);
lean_inc(v_u_3939_);
v_ringInst_3940_ = lean_ctor_get(v_toRing_3932_, 3);
lean_inc_ref(v_ringInst_3940_);
lean_dec_ref(v_toRing_3932_);
v___x_3941_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getIntCastFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__1_spec__7___closed__0));
v___x_3942_ = lean_box(0);
v___x_3943_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3943_, 0, v_u_3939_);
lean_ctor_set(v___x_3943_, 1, v___x_3942_);
lean_inc_ref_n(v___x_3943_, 2);
v___x_3944_ = l_Lean_mkConst(v___x_3941_, v___x_3943_);
v_inst_x27_3945_ = l_Lean_mkAppB(v___x_3944_, v_type_3938_, v_ringInst_3940_);
v___x_3980_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getIntCastFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__1_spec__7___closed__1));
v___x_3981_ = l_Lean_mkConst(v___x_3980_, v___x_3943_);
v_instType_3982_ = l_Lean_Expr_app___override(v___x_3981_, v_type_3938_);
v___x_3983_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v_instType_3982_, v___y_3921_, v___y_3922_, v___y_3923_, v___y_3924_, v___y_3925_);
if (lean_obj_tag(v___x_3983_) == 0)
{
lean_object* v_a_3984_; 
v_a_3984_ = lean_ctor_get(v___x_3983_, 0);
lean_inc(v_a_3984_);
lean_dec_ref_known(v___x_3983_, 1);
if (lean_obj_tag(v_a_3984_) == 0)
{
v_inst_3947_ = v_inst_x27_3945_;
v___y_3948_ = v___y_3915_;
v___y_3949_ = v___y_3920_;
v___y_3950_ = v___y_3921_;
v___y_3951_ = v___y_3922_;
v___y_3952_ = v___y_3923_;
v___y_3953_ = v___y_3924_;
v___y_3954_ = v___y_3925_;
goto v___jp_3946_;
}
else
{
lean_object* v_val_3985_; lean_object* v___x_3986_; lean_object* v___x_3987_; 
v_val_3985_ = lean_ctor_get(v_a_3984_, 0);
lean_inc_n(v_val_3985_, 2);
lean_dec_ref_known(v_a_3984_, 1);
v___x_3986_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getIntCastFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__1_spec__7___closed__3));
v___x_3987_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst(v___x_3986_, v_val_3985_, v_inst_x27_3945_, v___y_3922_, v___y_3923_, v___y_3924_, v___y_3925_);
if (lean_obj_tag(v___x_3987_) == 0)
{
lean_dec_ref_known(v___x_3987_, 1);
v_inst_3947_ = v_val_3985_;
v___y_3948_ = v___y_3915_;
v___y_3949_ = v___y_3920_;
v___y_3950_ = v___y_3921_;
v___y_3951_ = v___y_3922_;
v___y_3952_ = v___y_3923_;
v___y_3953_ = v___y_3924_;
v___y_3954_ = v___y_3925_;
goto v___jp_3946_;
}
else
{
lean_object* v_a_3988_; lean_object* v___x_3990_; uint8_t v_isShared_3991_; uint8_t v_isSharedCheck_3995_; 
lean_dec(v_val_3985_);
lean_dec_ref_known(v___x_3943_, 2);
lean_dec_ref(v_type_3938_);
v_a_3988_ = lean_ctor_get(v___x_3987_, 0);
v_isSharedCheck_3995_ = !lean_is_exclusive(v___x_3987_);
if (v_isSharedCheck_3995_ == 0)
{
v___x_3990_ = v___x_3987_;
v_isShared_3991_ = v_isSharedCheck_3995_;
goto v_resetjp_3989_;
}
else
{
lean_inc(v_a_3988_);
lean_dec(v___x_3987_);
v___x_3990_ = lean_box(0);
v_isShared_3991_ = v_isSharedCheck_3995_;
goto v_resetjp_3989_;
}
v_resetjp_3989_:
{
lean_object* v___x_3993_; 
if (v_isShared_3991_ == 0)
{
v___x_3993_ = v___x_3990_;
goto v_reusejp_3992_;
}
else
{
lean_object* v_reuseFailAlloc_3994_; 
v_reuseFailAlloc_3994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3994_, 0, v_a_3988_);
v___x_3993_ = v_reuseFailAlloc_3994_;
goto v_reusejp_3992_;
}
v_reusejp_3992_:
{
return v___x_3993_;
}
}
}
}
}
else
{
lean_object* v_a_3996_; lean_object* v___x_3998_; uint8_t v_isShared_3999_; uint8_t v_isSharedCheck_4003_; 
lean_dec_ref(v_inst_x27_3945_);
lean_dec_ref_known(v___x_3943_, 2);
lean_dec_ref(v_type_3938_);
v_a_3996_ = lean_ctor_get(v___x_3983_, 0);
v_isSharedCheck_4003_ = !lean_is_exclusive(v___x_3983_);
if (v_isSharedCheck_4003_ == 0)
{
v___x_3998_ = v___x_3983_;
v_isShared_3999_ = v_isSharedCheck_4003_;
goto v_resetjp_3997_;
}
else
{
lean_inc(v_a_3996_);
lean_dec(v___x_3983_);
v___x_3998_ = lean_box(0);
v_isShared_3999_ = v_isSharedCheck_4003_;
goto v_resetjp_3997_;
}
v_resetjp_3997_:
{
lean_object* v___x_4001_; 
if (v_isShared_3999_ == 0)
{
v___x_4001_ = v___x_3998_;
goto v_reusejp_4000_;
}
else
{
lean_object* v_reuseFailAlloc_4002_; 
v_reuseFailAlloc_4002_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4002_, 0, v_a_3996_);
v___x_4001_ = v_reuseFailAlloc_4002_;
goto v_reusejp_4000_;
}
v_reusejp_4000_:
{
return v___x_4001_;
}
}
}
v___jp_3946_:
{
lean_object* v___x_3955_; lean_object* v___x_3956_; lean_object* v___x_3957_; lean_object* v___x_3958_; 
v___x_3955_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__2));
v___x_3956_ = l_Lean_mkConst(v___x_3955_, v___x_3943_);
v___x_3957_ = l_Lean_mkAppB(v___x_3956_, v_type_3938_, v_inst_3947_);
v___x_3958_ = l_Lean_Meta_Sym_canon(v___x_3957_, v___y_3949_, v___y_3950_, v___y_3951_, v___y_3952_, v___y_3953_, v___y_3954_);
if (lean_obj_tag(v___x_3958_) == 0)
{
lean_object* v_a_3959_; lean_object* v___x_3960_; 
v_a_3959_ = lean_ctor_get(v___x_3958_, 0);
lean_inc(v_a_3959_);
lean_dec_ref_known(v___x_3958_, 1);
v___x_3960_ = l_Lean_Meta_Sym_shareCommon(v_a_3959_, v___y_3949_, v___y_3950_, v___y_3951_, v___y_3952_, v___y_3953_, v___y_3954_);
if (lean_obj_tag(v___x_3960_) == 0)
{
lean_object* v_a_3961_; lean_object* v___f_3962_; lean_object* v___x_3963_; 
v_a_3961_ = lean_ctor_get(v___x_3960_, 0);
lean_inc_n(v_a_3961_, 2);
lean_dec_ref_known(v___x_3960_, 1);
v___f_3962_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getIntCastFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0_spec__3___lam__0), 2, 1);
lean_closure_set(v___f_3962_, 0, v_a_3961_);
v___x_3963_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(v___f_3962_, v___y_3948_, v___y_3950_);
if (lean_obj_tag(v___x_3963_) == 0)
{
lean_object* v___x_3965_; uint8_t v_isShared_3966_; uint8_t v_isSharedCheck_3970_; 
v_isSharedCheck_3970_ = !lean_is_exclusive(v___x_3963_);
if (v_isSharedCheck_3970_ == 0)
{
lean_object* v_unused_3971_; 
v_unused_3971_ = lean_ctor_get(v___x_3963_, 0);
lean_dec(v_unused_3971_);
v___x_3965_ = v___x_3963_;
v_isShared_3966_ = v_isSharedCheck_3970_;
goto v_resetjp_3964_;
}
else
{
lean_dec(v___x_3963_);
v___x_3965_ = lean_box(0);
v_isShared_3966_ = v_isSharedCheck_3970_;
goto v_resetjp_3964_;
}
v_resetjp_3964_:
{
lean_object* v___x_3968_; 
if (v_isShared_3966_ == 0)
{
lean_ctor_set(v___x_3965_, 0, v_a_3961_);
v___x_3968_ = v___x_3965_;
goto v_reusejp_3967_;
}
else
{
lean_object* v_reuseFailAlloc_3969_; 
v_reuseFailAlloc_3969_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3969_, 0, v_a_3961_);
v___x_3968_ = v_reuseFailAlloc_3969_;
goto v_reusejp_3967_;
}
v_reusejp_3967_:
{
return v___x_3968_;
}
}
}
else
{
lean_object* v_a_3972_; lean_object* v___x_3974_; uint8_t v_isShared_3975_; uint8_t v_isSharedCheck_3979_; 
lean_dec(v_a_3961_);
v_a_3972_ = lean_ctor_get(v___x_3963_, 0);
v_isSharedCheck_3979_ = !lean_is_exclusive(v___x_3963_);
if (v_isSharedCheck_3979_ == 0)
{
v___x_3974_ = v___x_3963_;
v_isShared_3975_ = v_isSharedCheck_3979_;
goto v_resetjp_3973_;
}
else
{
lean_inc(v_a_3972_);
lean_dec(v___x_3963_);
v___x_3974_ = lean_box(0);
v_isShared_3975_ = v_isSharedCheck_3979_;
goto v_resetjp_3973_;
}
v_resetjp_3973_:
{
lean_object* v___x_3977_; 
if (v_isShared_3975_ == 0)
{
v___x_3977_ = v___x_3974_;
goto v_reusejp_3976_;
}
else
{
lean_object* v_reuseFailAlloc_3978_; 
v_reuseFailAlloc_3978_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3978_, 0, v_a_3972_);
v___x_3977_ = v_reuseFailAlloc_3978_;
goto v_reusejp_3976_;
}
v_reusejp_3976_:
{
return v___x_3977_;
}
}
}
}
else
{
return v___x_3960_;
}
}
else
{
return v___x_3958_;
}
}
}
}
}
else
{
lean_object* v_a_4005_; lean_object* v___x_4007_; uint8_t v_isShared_4008_; uint8_t v_isSharedCheck_4012_; 
v_a_4005_ = lean_ctor_get(v___x_3927_, 0);
v_isSharedCheck_4012_ = !lean_is_exclusive(v___x_3927_);
if (v_isSharedCheck_4012_ == 0)
{
v___x_4007_ = v___x_3927_;
v_isShared_4008_ = v_isSharedCheck_4012_;
goto v_resetjp_4006_;
}
else
{
lean_inc(v_a_4005_);
lean_dec(v___x_3927_);
v___x_4007_ = lean_box(0);
v_isShared_4008_ = v_isSharedCheck_4012_;
goto v_resetjp_4006_;
}
v_resetjp_4006_:
{
lean_object* v___x_4010_; 
if (v_isShared_4008_ == 0)
{
v___x_4010_ = v___x_4007_;
goto v_reusejp_4009_;
}
else
{
lean_object* v_reuseFailAlloc_4011_; 
v_reuseFailAlloc_4011_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4011_, 0, v_a_4005_);
v___x_4010_ = v_reuseFailAlloc_4011_;
goto v_reusejp_4009_;
}
v_reusejp_4009_:
{
return v___x_4010_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getIntCastFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0_spec__3___boxed(lean_object* v___y_4013_, lean_object* v___y_4014_, lean_object* v___y_4015_, lean_object* v___y_4016_, lean_object* v___y_4017_, lean_object* v___y_4018_, lean_object* v___y_4019_, lean_object* v___y_4020_, lean_object* v___y_4021_, lean_object* v___y_4022_, lean_object* v___y_4023_, lean_object* v___y_4024_){
_start:
{
lean_object* v_res_4025_; 
v_res_4025_ = l_Lean_Meta_Sym_Arith_getIntCastFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0_spec__3(v___y_4013_, v___y_4014_, v___y_4015_, v___y_4016_, v___y_4017_, v___y_4018_, v___y_4019_, v___y_4020_, v___y_4021_, v___y_4022_, v___y_4023_);
lean_dec(v___y_4023_);
lean_dec_ref(v___y_4022_);
lean_dec(v___y_4021_);
lean_dec_ref(v___y_4020_);
lean_dec(v___y_4019_);
lean_dec_ref(v___y_4018_);
lean_dec(v___y_4017_);
lean_dec_ref(v___y_4016_);
lean_dec(v___y_4015_);
lean_dec(v___y_4014_);
lean_dec_ref(v___y_4013_);
return v_res_4025_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0___lam__4(uint8_t v___x_4026_, lean_object* v_s_4027_){
_start:
{
lean_object* v_toRingState_4028_; lean_object* v_denoteEntries_4029_; lean_object* v_nextId_4030_; lean_object* v_steps_4031_; lean_object* v_queue_4032_; lean_object* v_basis_4033_; lean_object* v_diseqs_4034_; uint8_t v_recheck_4035_; lean_object* v_invSet_4036_; lean_object* v_powIdentityVarCount_4037_; lean_object* v_numEq0_x3f_4038_; uint8_t v_numEq0Updated_4039_; lean_object* v___x_4041_; uint8_t v_isShared_4042_; uint8_t v_isSharedCheck_4061_; 
v_toRingState_4028_ = lean_ctor_get(v_s_4027_, 0);
v_denoteEntries_4029_ = lean_ctor_get(v_s_4027_, 1);
v_nextId_4030_ = lean_ctor_get(v_s_4027_, 2);
v_steps_4031_ = lean_ctor_get(v_s_4027_, 3);
v_queue_4032_ = lean_ctor_get(v_s_4027_, 4);
v_basis_4033_ = lean_ctor_get(v_s_4027_, 5);
v_diseqs_4034_ = lean_ctor_get(v_s_4027_, 6);
v_recheck_4035_ = lean_ctor_get_uint8(v_s_4027_, sizeof(void*)*10);
v_invSet_4036_ = lean_ctor_get(v_s_4027_, 7);
v_powIdentityVarCount_4037_ = lean_ctor_get(v_s_4027_, 8);
v_numEq0_x3f_4038_ = lean_ctor_get(v_s_4027_, 9);
v_numEq0Updated_4039_ = lean_ctor_get_uint8(v_s_4027_, sizeof(void*)*10 + 1);
v_isSharedCheck_4061_ = !lean_is_exclusive(v_s_4027_);
if (v_isSharedCheck_4061_ == 0)
{
v___x_4041_ = v_s_4027_;
v_isShared_4042_ = v_isSharedCheck_4061_;
goto v_resetjp_4040_;
}
else
{
lean_inc(v_numEq0_x3f_4038_);
lean_inc(v_powIdentityVarCount_4037_);
lean_inc(v_invSet_4036_);
lean_inc(v_diseqs_4034_);
lean_inc(v_basis_4033_);
lean_inc(v_queue_4032_);
lean_inc(v_steps_4031_);
lean_inc(v_nextId_4030_);
lean_inc(v_denoteEntries_4029_);
lean_inc(v_toRingState_4028_);
lean_dec(v_s_4027_);
v___x_4041_ = lean_box(0);
v_isShared_4042_ = v_isSharedCheck_4061_;
goto v_resetjp_4040_;
}
v_resetjp_4040_:
{
lean_object* v_vars_4043_; lean_object* v_varMap_4044_; lean_object* v_denote_4045_; lean_object* v_natCastSet_4046_; lean_object* v___x_4048_; uint8_t v_isShared_4049_; uint8_t v_isSharedCheck_4059_; 
v_vars_4043_ = lean_ctor_get(v_toRingState_4028_, 0);
v_varMap_4044_ = lean_ctor_get(v_toRingState_4028_, 1);
v_denote_4045_ = lean_ctor_get(v_toRingState_4028_, 2);
v_natCastSet_4046_ = lean_ctor_get(v_toRingState_4028_, 3);
v_isSharedCheck_4059_ = !lean_is_exclusive(v_toRingState_4028_);
if (v_isSharedCheck_4059_ == 0)
{
lean_object* v_unused_4060_; 
v_unused_4060_ = lean_ctor_get(v_toRingState_4028_, 4);
lean_dec(v_unused_4060_);
v___x_4048_ = v_toRingState_4028_;
v_isShared_4049_ = v_isSharedCheck_4059_;
goto v_resetjp_4047_;
}
else
{
lean_inc(v_natCastSet_4046_);
lean_inc(v_denote_4045_);
lean_inc(v_varMap_4044_);
lean_inc(v_vars_4043_);
lean_dec(v_toRingState_4028_);
v___x_4048_ = lean_box(0);
v_isShared_4049_ = v_isSharedCheck_4059_;
goto v_resetjp_4047_;
}
v_resetjp_4047_:
{
lean_object* v___x_4050_; lean_object* v___x_4051_; lean_object* v___x_4052_; lean_object* v___x_4054_; 
v___x_4050_ = lean_unsigned_to_nat(32u);
v___x_4051_ = lean_mk_empty_array_with_capacity(v___x_4050_);
lean_dec_ref(v___x_4051_);
v___x_4052_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___redArg___lam__8___closed__1, &l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___redArg___lam__8___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___redArg___lam__8___closed__1);
if (v_isShared_4049_ == 0)
{
lean_ctor_set(v___x_4048_, 4, v___x_4052_);
v___x_4054_ = v___x_4048_;
goto v_reusejp_4053_;
}
else
{
lean_object* v_reuseFailAlloc_4058_; 
v_reuseFailAlloc_4058_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_4058_, 0, v_vars_4043_);
lean_ctor_set(v_reuseFailAlloc_4058_, 1, v_varMap_4044_);
lean_ctor_set(v_reuseFailAlloc_4058_, 2, v_denote_4045_);
lean_ctor_set(v_reuseFailAlloc_4058_, 3, v_natCastSet_4046_);
lean_ctor_set(v_reuseFailAlloc_4058_, 4, v___x_4052_);
v___x_4054_ = v_reuseFailAlloc_4058_;
goto v_reusejp_4053_;
}
v_reusejp_4053_:
{
lean_object* v___x_4056_; 
lean_ctor_set_uint8(v___x_4054_, sizeof(void*)*5, v___x_4026_);
if (v_isShared_4042_ == 0)
{
lean_ctor_set(v___x_4041_, 0, v___x_4054_);
v___x_4056_ = v___x_4041_;
goto v_reusejp_4055_;
}
else
{
lean_object* v_reuseFailAlloc_4057_; 
v_reuseFailAlloc_4057_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v_reuseFailAlloc_4057_, 0, v___x_4054_);
lean_ctor_set(v_reuseFailAlloc_4057_, 1, v_denoteEntries_4029_);
lean_ctor_set(v_reuseFailAlloc_4057_, 2, v_nextId_4030_);
lean_ctor_set(v_reuseFailAlloc_4057_, 3, v_steps_4031_);
lean_ctor_set(v_reuseFailAlloc_4057_, 4, v_queue_4032_);
lean_ctor_set(v_reuseFailAlloc_4057_, 5, v_basis_4033_);
lean_ctor_set(v_reuseFailAlloc_4057_, 6, v_diseqs_4034_);
lean_ctor_set(v_reuseFailAlloc_4057_, 7, v_invSet_4036_);
lean_ctor_set(v_reuseFailAlloc_4057_, 8, v_powIdentityVarCount_4037_);
lean_ctor_set(v_reuseFailAlloc_4057_, 9, v_numEq0_x3f_4038_);
lean_ctor_set_uint8(v_reuseFailAlloc_4057_, sizeof(void*)*10, v_recheck_4035_);
lean_ctor_set_uint8(v_reuseFailAlloc_4057_, sizeof(void*)*10 + 1, v_numEq0Updated_4039_);
v___x_4056_ = v_reuseFailAlloc_4057_;
goto v_reusejp_4055_;
}
v_reusejp_4055_:
{
return v___x_4056_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0___lam__4___boxed(lean_object* v___x_4062_, lean_object* v_s_4063_){
_start:
{
uint8_t v___x_132688__boxed_4064_; lean_object* v_res_4065_; 
v___x_132688__boxed_4064_ = lean_unbox(v___x_4062_);
v_res_4065_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0___lam__4(v___x_132688__boxed_4064_, v_s_4063_);
return v_res_4065_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___at___00Lean_Meta_Sym_Arith_getNatCastFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0_spec__1_spec__3___redArg(lean_object* v_u_4066_, lean_object* v_type_4067_, lean_object* v_semiringInst_4068_, lean_object* v___y_4069_, lean_object* v___y_4070_, lean_object* v___y_4071_, lean_object* v___y_4072_, lean_object* v___y_4073_, lean_object* v___y_4074_){
_start:
{
lean_object* v___x_4076_; lean_object* v___x_4077_; lean_object* v___x_4078_; lean_object* v___x_4079_; lean_object* v_inst_x27_4080_; lean_object* v_inst_4082_; lean_object* v___y_4083_; lean_object* v___y_4084_; lean_object* v___y_4085_; lean_object* v___y_4086_; lean_object* v___y_4087_; lean_object* v___y_4088_; lean_object* v___x_4095_; lean_object* v___x_4096_; lean_object* v_instType_4097_; lean_object* v___x_4098_; 
v___x_4076_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___at___00Lean_Meta_Sym_Arith_getNatCastFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__1_spec__6_spec__13___redArg___closed__0));
v___x_4077_ = lean_box(0);
v___x_4078_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4078_, 0, v_u_4066_);
lean_ctor_set(v___x_4078_, 1, v___x_4077_);
lean_inc_ref_n(v___x_4078_, 2);
v___x_4079_ = l_Lean_mkConst(v___x_4076_, v___x_4078_);
lean_inc_ref_n(v_type_4067_, 2);
v_inst_x27_4080_ = l_Lean_mkAppB(v___x_4079_, v_type_4067_, v_semiringInst_4068_);
v___x_4095_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___at___00Lean_Meta_Sym_Arith_getNatCastFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__1_spec__6_spec__13___redArg___closed__1));
v___x_4096_ = l_Lean_mkConst(v___x_4095_, v___x_4078_);
v_instType_4097_ = l_Lean_Expr_app___override(v___x_4096_, v_type_4067_);
v___x_4098_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v_instType_4097_, v___y_4070_, v___y_4071_, v___y_4072_, v___y_4073_, v___y_4074_);
if (lean_obj_tag(v___x_4098_) == 0)
{
lean_object* v_a_4099_; 
v_a_4099_ = lean_ctor_get(v___x_4098_, 0);
lean_inc(v_a_4099_);
lean_dec_ref_known(v___x_4098_, 1);
if (lean_obj_tag(v_a_4099_) == 0)
{
v_inst_4082_ = v_inst_x27_4080_;
v___y_4083_ = v___y_4069_;
v___y_4084_ = v___y_4070_;
v___y_4085_ = v___y_4071_;
v___y_4086_ = v___y_4072_;
v___y_4087_ = v___y_4073_;
v___y_4088_ = v___y_4074_;
goto v___jp_4081_;
}
else
{
lean_object* v_val_4100_; lean_object* v___x_4101_; lean_object* v___x_4102_; 
v_val_4100_ = lean_ctor_get(v_a_4099_, 0);
lean_inc_n(v_val_4100_, 2);
lean_dec_ref_known(v_a_4099_, 1);
v___x_4101_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__5));
v___x_4102_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst(v___x_4101_, v_val_4100_, v_inst_x27_4080_, v___y_4071_, v___y_4072_, v___y_4073_, v___y_4074_);
if (lean_obj_tag(v___x_4102_) == 0)
{
lean_dec_ref_known(v___x_4102_, 1);
v_inst_4082_ = v_val_4100_;
v___y_4083_ = v___y_4069_;
v___y_4084_ = v___y_4070_;
v___y_4085_ = v___y_4071_;
v___y_4086_ = v___y_4072_;
v___y_4087_ = v___y_4073_;
v___y_4088_ = v___y_4074_;
goto v___jp_4081_;
}
else
{
lean_object* v_a_4103_; lean_object* v___x_4105_; uint8_t v_isShared_4106_; uint8_t v_isSharedCheck_4110_; 
lean_dec(v_val_4100_);
lean_dec_ref_known(v___x_4078_, 2);
lean_dec_ref(v_type_4067_);
v_a_4103_ = lean_ctor_get(v___x_4102_, 0);
v_isSharedCheck_4110_ = !lean_is_exclusive(v___x_4102_);
if (v_isSharedCheck_4110_ == 0)
{
v___x_4105_ = v___x_4102_;
v_isShared_4106_ = v_isSharedCheck_4110_;
goto v_resetjp_4104_;
}
else
{
lean_inc(v_a_4103_);
lean_dec(v___x_4102_);
v___x_4105_ = lean_box(0);
v_isShared_4106_ = v_isSharedCheck_4110_;
goto v_resetjp_4104_;
}
v_resetjp_4104_:
{
lean_object* v___x_4108_; 
if (v_isShared_4106_ == 0)
{
v___x_4108_ = v___x_4105_;
goto v_reusejp_4107_;
}
else
{
lean_object* v_reuseFailAlloc_4109_; 
v_reuseFailAlloc_4109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4109_, 0, v_a_4103_);
v___x_4108_ = v_reuseFailAlloc_4109_;
goto v_reusejp_4107_;
}
v_reusejp_4107_:
{
return v___x_4108_;
}
}
}
}
}
else
{
lean_object* v_a_4111_; lean_object* v___x_4113_; uint8_t v_isShared_4114_; uint8_t v_isSharedCheck_4118_; 
lean_dec_ref(v_inst_x27_4080_);
lean_dec_ref_known(v___x_4078_, 2);
lean_dec_ref(v_type_4067_);
v_a_4111_ = lean_ctor_get(v___x_4098_, 0);
v_isSharedCheck_4118_ = !lean_is_exclusive(v___x_4098_);
if (v_isSharedCheck_4118_ == 0)
{
v___x_4113_ = v___x_4098_;
v_isShared_4114_ = v_isSharedCheck_4118_;
goto v_resetjp_4112_;
}
else
{
lean_inc(v_a_4111_);
lean_dec(v___x_4098_);
v___x_4113_ = lean_box(0);
v_isShared_4114_ = v_isSharedCheck_4118_;
goto v_resetjp_4112_;
}
v_resetjp_4112_:
{
lean_object* v___x_4116_; 
if (v_isShared_4114_ == 0)
{
v___x_4116_ = v___x_4113_;
goto v_reusejp_4115_;
}
else
{
lean_object* v_reuseFailAlloc_4117_; 
v_reuseFailAlloc_4117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4117_, 0, v_a_4111_);
v___x_4116_ = v_reuseFailAlloc_4117_;
goto v_reusejp_4115_;
}
v_reusejp_4115_:
{
return v___x_4116_;
}
}
}
v___jp_4081_:
{
lean_object* v___x_4089_; lean_object* v___x_4090_; lean_object* v___x_4091_; lean_object* v___x_4092_; 
v___x_4089_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__5));
v___x_4090_ = l_Lean_mkConst(v___x_4089_, v___x_4078_);
v___x_4091_ = l_Lean_mkAppB(v___x_4090_, v_type_4067_, v_inst_4082_);
v___x_4092_ = l_Lean_Meta_Sym_canon(v___x_4091_, v___y_4083_, v___y_4084_, v___y_4085_, v___y_4086_, v___y_4087_, v___y_4088_);
if (lean_obj_tag(v___x_4092_) == 0)
{
lean_object* v_a_4093_; lean_object* v___x_4094_; 
v_a_4093_ = lean_ctor_get(v___x_4092_, 0);
lean_inc(v_a_4093_);
lean_dec_ref_known(v___x_4092_, 1);
v___x_4094_ = l_Lean_Meta_Sym_shareCommon(v_a_4093_, v___y_4083_, v___y_4084_, v___y_4085_, v___y_4086_, v___y_4087_, v___y_4088_);
return v___x_4094_;
}
else
{
return v___x_4092_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___at___00Lean_Meta_Sym_Arith_getNatCastFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_u_4119_, lean_object* v_type_4120_, lean_object* v_semiringInst_4121_, lean_object* v___y_4122_, lean_object* v___y_4123_, lean_object* v___y_4124_, lean_object* v___y_4125_, lean_object* v___y_4126_, lean_object* v___y_4127_, lean_object* v___y_4128_){
_start:
{
lean_object* v_res_4129_; 
v_res_4129_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___at___00Lean_Meta_Sym_Arith_getNatCastFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0_spec__1_spec__3___redArg(v_u_4119_, v_type_4120_, v_semiringInst_4121_, v___y_4122_, v___y_4123_, v___y_4124_, v___y_4125_, v___y_4126_, v___y_4127_);
lean_dec(v___y_4127_);
lean_dec_ref(v___y_4126_);
lean_dec(v___y_4125_);
lean_dec_ref(v___y_4124_);
lean_dec(v___y_4123_);
lean_dec_ref(v___y_4122_);
return v_res_4129_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatCastFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0_spec__1___lam__0(lean_object* v_a_4130_, lean_object* v_s_4131_){
_start:
{
lean_object* v_toRing_4132_; lean_object* v_invFn_x3f_4133_; lean_object* v_divFn_x3f_4134_; lean_object* v_zpowFn_x3f_4135_; lean_object* v_semiringId_x3f_4136_; lean_object* v_commSemiringInst_4137_; lean_object* v_commRingInst_4138_; lean_object* v_noZeroDivInst_x3f_4139_; lean_object* v_fieldInst_x3f_4140_; lean_object* v_powIdentityInst_x3f_4141_; lean_object* v___x_4143_; uint8_t v_isShared_4144_; uint8_t v_isSharedCheck_4173_; 
v_toRing_4132_ = lean_ctor_get(v_s_4131_, 0);
v_invFn_x3f_4133_ = lean_ctor_get(v_s_4131_, 1);
v_divFn_x3f_4134_ = lean_ctor_get(v_s_4131_, 2);
v_zpowFn_x3f_4135_ = lean_ctor_get(v_s_4131_, 3);
v_semiringId_x3f_4136_ = lean_ctor_get(v_s_4131_, 4);
v_commSemiringInst_4137_ = lean_ctor_get(v_s_4131_, 5);
v_commRingInst_4138_ = lean_ctor_get(v_s_4131_, 6);
v_noZeroDivInst_x3f_4139_ = lean_ctor_get(v_s_4131_, 7);
v_fieldInst_x3f_4140_ = lean_ctor_get(v_s_4131_, 8);
v_powIdentityInst_x3f_4141_ = lean_ctor_get(v_s_4131_, 9);
v_isSharedCheck_4173_ = !lean_is_exclusive(v_s_4131_);
if (v_isSharedCheck_4173_ == 0)
{
v___x_4143_ = v_s_4131_;
v_isShared_4144_ = v_isSharedCheck_4173_;
goto v_resetjp_4142_;
}
else
{
lean_inc(v_powIdentityInst_x3f_4141_);
lean_inc(v_fieldInst_x3f_4140_);
lean_inc(v_noZeroDivInst_x3f_4139_);
lean_inc(v_commRingInst_4138_);
lean_inc(v_commSemiringInst_4137_);
lean_inc(v_semiringId_x3f_4136_);
lean_inc(v_zpowFn_x3f_4135_);
lean_inc(v_divFn_x3f_4134_);
lean_inc(v_invFn_x3f_4133_);
lean_inc(v_toRing_4132_);
lean_dec(v_s_4131_);
v___x_4143_ = lean_box(0);
v_isShared_4144_ = v_isSharedCheck_4173_;
goto v_resetjp_4142_;
}
v_resetjp_4142_:
{
lean_object* v_id_4145_; lean_object* v_type_4146_; lean_object* v_u_4147_; lean_object* v_ringInst_4148_; lean_object* v_semiringInst_4149_; lean_object* v_charInst_x3f_4150_; uint8_t v_symbolicChar_4151_; lean_object* v_addFn_x3f_4152_; lean_object* v_mulFn_x3f_4153_; lean_object* v_subFn_x3f_4154_; lean_object* v_negFn_x3f_4155_; lean_object* v_powFn_x3f_4156_; lean_object* v_intCastFn_x3f_4157_; lean_object* v_natSMulFn_x3f_4158_; lean_object* v_intSMulFn_x3f_4159_; lean_object* v_one_x3f_4160_; lean_object* v___x_4162_; uint8_t v_isShared_4163_; uint8_t v_isSharedCheck_4171_; 
v_id_4145_ = lean_ctor_get(v_toRing_4132_, 0);
v_type_4146_ = lean_ctor_get(v_toRing_4132_, 1);
v_u_4147_ = lean_ctor_get(v_toRing_4132_, 2);
v_ringInst_4148_ = lean_ctor_get(v_toRing_4132_, 3);
v_semiringInst_4149_ = lean_ctor_get(v_toRing_4132_, 4);
v_charInst_x3f_4150_ = lean_ctor_get(v_toRing_4132_, 5);
v_symbolicChar_4151_ = lean_ctor_get_uint8(v_toRing_4132_, sizeof(void*)*16);
v_addFn_x3f_4152_ = lean_ctor_get(v_toRing_4132_, 6);
v_mulFn_x3f_4153_ = lean_ctor_get(v_toRing_4132_, 7);
v_subFn_x3f_4154_ = lean_ctor_get(v_toRing_4132_, 8);
v_negFn_x3f_4155_ = lean_ctor_get(v_toRing_4132_, 9);
v_powFn_x3f_4156_ = lean_ctor_get(v_toRing_4132_, 10);
v_intCastFn_x3f_4157_ = lean_ctor_get(v_toRing_4132_, 11);
v_natSMulFn_x3f_4158_ = lean_ctor_get(v_toRing_4132_, 13);
v_intSMulFn_x3f_4159_ = lean_ctor_get(v_toRing_4132_, 14);
v_one_x3f_4160_ = lean_ctor_get(v_toRing_4132_, 15);
v_isSharedCheck_4171_ = !lean_is_exclusive(v_toRing_4132_);
if (v_isSharedCheck_4171_ == 0)
{
lean_object* v_unused_4172_; 
v_unused_4172_ = lean_ctor_get(v_toRing_4132_, 12);
lean_dec(v_unused_4172_);
v___x_4162_ = v_toRing_4132_;
v_isShared_4163_ = v_isSharedCheck_4171_;
goto v_resetjp_4161_;
}
else
{
lean_inc(v_one_x3f_4160_);
lean_inc(v_intSMulFn_x3f_4159_);
lean_inc(v_natSMulFn_x3f_4158_);
lean_inc(v_intCastFn_x3f_4157_);
lean_inc(v_powFn_x3f_4156_);
lean_inc(v_negFn_x3f_4155_);
lean_inc(v_subFn_x3f_4154_);
lean_inc(v_mulFn_x3f_4153_);
lean_inc(v_addFn_x3f_4152_);
lean_inc(v_charInst_x3f_4150_);
lean_inc(v_semiringInst_4149_);
lean_inc(v_ringInst_4148_);
lean_inc(v_u_4147_);
lean_inc(v_type_4146_);
lean_inc(v_id_4145_);
lean_dec(v_toRing_4132_);
v___x_4162_ = lean_box(0);
v_isShared_4163_ = v_isSharedCheck_4171_;
goto v_resetjp_4161_;
}
v_resetjp_4161_:
{
lean_object* v___x_4164_; lean_object* v___x_4166_; 
v___x_4164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4164_, 0, v_a_4130_);
if (v_isShared_4163_ == 0)
{
lean_ctor_set(v___x_4162_, 12, v___x_4164_);
v___x_4166_ = v___x_4162_;
goto v_reusejp_4165_;
}
else
{
lean_object* v_reuseFailAlloc_4170_; 
v_reuseFailAlloc_4170_ = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(v_reuseFailAlloc_4170_, 0, v_id_4145_);
lean_ctor_set(v_reuseFailAlloc_4170_, 1, v_type_4146_);
lean_ctor_set(v_reuseFailAlloc_4170_, 2, v_u_4147_);
lean_ctor_set(v_reuseFailAlloc_4170_, 3, v_ringInst_4148_);
lean_ctor_set(v_reuseFailAlloc_4170_, 4, v_semiringInst_4149_);
lean_ctor_set(v_reuseFailAlloc_4170_, 5, v_charInst_x3f_4150_);
lean_ctor_set(v_reuseFailAlloc_4170_, 6, v_addFn_x3f_4152_);
lean_ctor_set(v_reuseFailAlloc_4170_, 7, v_mulFn_x3f_4153_);
lean_ctor_set(v_reuseFailAlloc_4170_, 8, v_subFn_x3f_4154_);
lean_ctor_set(v_reuseFailAlloc_4170_, 9, v_negFn_x3f_4155_);
lean_ctor_set(v_reuseFailAlloc_4170_, 10, v_powFn_x3f_4156_);
lean_ctor_set(v_reuseFailAlloc_4170_, 11, v_intCastFn_x3f_4157_);
lean_ctor_set(v_reuseFailAlloc_4170_, 12, v___x_4164_);
lean_ctor_set(v_reuseFailAlloc_4170_, 13, v_natSMulFn_x3f_4158_);
lean_ctor_set(v_reuseFailAlloc_4170_, 14, v_intSMulFn_x3f_4159_);
lean_ctor_set(v_reuseFailAlloc_4170_, 15, v_one_x3f_4160_);
lean_ctor_set_uint8(v_reuseFailAlloc_4170_, sizeof(void*)*16, v_symbolicChar_4151_);
v___x_4166_ = v_reuseFailAlloc_4170_;
goto v_reusejp_4165_;
}
v_reusejp_4165_:
{
lean_object* v___x_4168_; 
if (v_isShared_4144_ == 0)
{
lean_ctor_set(v___x_4143_, 0, v___x_4166_);
v___x_4168_ = v___x_4143_;
goto v_reusejp_4167_;
}
else
{
lean_object* v_reuseFailAlloc_4169_; 
v_reuseFailAlloc_4169_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4169_, 0, v___x_4166_);
lean_ctor_set(v_reuseFailAlloc_4169_, 1, v_invFn_x3f_4133_);
lean_ctor_set(v_reuseFailAlloc_4169_, 2, v_divFn_x3f_4134_);
lean_ctor_set(v_reuseFailAlloc_4169_, 3, v_zpowFn_x3f_4135_);
lean_ctor_set(v_reuseFailAlloc_4169_, 4, v_semiringId_x3f_4136_);
lean_ctor_set(v_reuseFailAlloc_4169_, 5, v_commSemiringInst_4137_);
lean_ctor_set(v_reuseFailAlloc_4169_, 6, v_commRingInst_4138_);
lean_ctor_set(v_reuseFailAlloc_4169_, 7, v_noZeroDivInst_x3f_4139_);
lean_ctor_set(v_reuseFailAlloc_4169_, 8, v_fieldInst_x3f_4140_);
lean_ctor_set(v_reuseFailAlloc_4169_, 9, v_powIdentityInst_x3f_4141_);
v___x_4168_ = v_reuseFailAlloc_4169_;
goto v_reusejp_4167_;
}
v_reusejp_4167_:
{
return v___x_4168_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatCastFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0_spec__1(lean_object* v___y_4174_, lean_object* v___y_4175_, lean_object* v___y_4176_, lean_object* v___y_4177_, lean_object* v___y_4178_, lean_object* v___y_4179_, lean_object* v___y_4180_, lean_object* v___y_4181_, lean_object* v___y_4182_, lean_object* v___y_4183_, lean_object* v___y_4184_){
_start:
{
lean_object* v___x_4186_; 
v___x_4186_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v___y_4174_, v___y_4175_, v___y_4176_, v___y_4177_, v___y_4178_, v___y_4179_, v___y_4180_, v___y_4181_, v___y_4182_, v___y_4183_, v___y_4184_);
if (lean_obj_tag(v___x_4186_) == 0)
{
lean_object* v_a_4187_; lean_object* v___x_4189_; uint8_t v_isShared_4190_; uint8_t v_isSharedCheck_4220_; 
v_a_4187_ = lean_ctor_get(v___x_4186_, 0);
v_isSharedCheck_4220_ = !lean_is_exclusive(v___x_4186_);
if (v_isSharedCheck_4220_ == 0)
{
v___x_4189_ = v___x_4186_;
v_isShared_4190_ = v_isSharedCheck_4220_;
goto v_resetjp_4188_;
}
else
{
lean_inc(v_a_4187_);
lean_dec(v___x_4186_);
v___x_4189_ = lean_box(0);
v_isShared_4190_ = v_isSharedCheck_4220_;
goto v_resetjp_4188_;
}
v_resetjp_4188_:
{
lean_object* v_toRing_4191_; lean_object* v_natCastFn_x3f_4192_; 
v_toRing_4191_ = lean_ctor_get(v_a_4187_, 0);
lean_inc_ref(v_toRing_4191_);
lean_dec(v_a_4187_);
v_natCastFn_x3f_4192_ = lean_ctor_get(v_toRing_4191_, 12);
if (lean_obj_tag(v_natCastFn_x3f_4192_) == 1)
{
lean_object* v_val_4193_; lean_object* v___x_4195_; 
lean_inc_ref(v_natCastFn_x3f_4192_);
lean_dec_ref(v_toRing_4191_);
v_val_4193_ = lean_ctor_get(v_natCastFn_x3f_4192_, 0);
lean_inc(v_val_4193_);
lean_dec_ref_known(v_natCastFn_x3f_4192_, 1);
if (v_isShared_4190_ == 0)
{
lean_ctor_set(v___x_4189_, 0, v_val_4193_);
v___x_4195_ = v___x_4189_;
goto v_reusejp_4194_;
}
else
{
lean_object* v_reuseFailAlloc_4196_; 
v_reuseFailAlloc_4196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4196_, 0, v_val_4193_);
v___x_4195_ = v_reuseFailAlloc_4196_;
goto v_reusejp_4194_;
}
v_reusejp_4194_:
{
return v___x_4195_;
}
}
else
{
lean_object* v_type_4197_; lean_object* v_u_4198_; lean_object* v_semiringInst_4199_; lean_object* v___x_4200_; 
lean_del_object(v___x_4189_);
v_type_4197_ = lean_ctor_get(v_toRing_4191_, 1);
lean_inc_ref(v_type_4197_);
v_u_4198_ = lean_ctor_get(v_toRing_4191_, 2);
lean_inc(v_u_4198_);
v_semiringInst_4199_ = lean_ctor_get(v_toRing_4191_, 4);
lean_inc_ref(v_semiringInst_4199_);
lean_dec_ref(v_toRing_4191_);
v___x_4200_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___at___00Lean_Meta_Sym_Arith_getNatCastFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0_spec__1_spec__3___redArg(v_u_4198_, v_type_4197_, v_semiringInst_4199_, v___y_4179_, v___y_4180_, v___y_4181_, v___y_4182_, v___y_4183_, v___y_4184_);
if (lean_obj_tag(v___x_4200_) == 0)
{
lean_object* v_a_4201_; lean_object* v___f_4202_; lean_object* v___x_4203_; 
v_a_4201_ = lean_ctor_get(v___x_4200_, 0);
lean_inc_n(v_a_4201_, 2);
lean_dec_ref_known(v___x_4200_, 1);
v___f_4202_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getNatCastFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0_spec__1___lam__0), 2, 1);
lean_closure_set(v___f_4202_, 0, v_a_4201_);
v___x_4203_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(v___f_4202_, v___y_4174_, v___y_4180_);
if (lean_obj_tag(v___x_4203_) == 0)
{
lean_object* v___x_4205_; uint8_t v_isShared_4206_; uint8_t v_isSharedCheck_4210_; 
v_isSharedCheck_4210_ = !lean_is_exclusive(v___x_4203_);
if (v_isSharedCheck_4210_ == 0)
{
lean_object* v_unused_4211_; 
v_unused_4211_ = lean_ctor_get(v___x_4203_, 0);
lean_dec(v_unused_4211_);
v___x_4205_ = v___x_4203_;
v_isShared_4206_ = v_isSharedCheck_4210_;
goto v_resetjp_4204_;
}
else
{
lean_dec(v___x_4203_);
v___x_4205_ = lean_box(0);
v_isShared_4206_ = v_isSharedCheck_4210_;
goto v_resetjp_4204_;
}
v_resetjp_4204_:
{
lean_object* v___x_4208_; 
if (v_isShared_4206_ == 0)
{
lean_ctor_set(v___x_4205_, 0, v_a_4201_);
v___x_4208_ = v___x_4205_;
goto v_reusejp_4207_;
}
else
{
lean_object* v_reuseFailAlloc_4209_; 
v_reuseFailAlloc_4209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4209_, 0, v_a_4201_);
v___x_4208_ = v_reuseFailAlloc_4209_;
goto v_reusejp_4207_;
}
v_reusejp_4207_:
{
return v___x_4208_;
}
}
}
else
{
lean_object* v_a_4212_; lean_object* v___x_4214_; uint8_t v_isShared_4215_; uint8_t v_isSharedCheck_4219_; 
lean_dec(v_a_4201_);
v_a_4212_ = lean_ctor_get(v___x_4203_, 0);
v_isSharedCheck_4219_ = !lean_is_exclusive(v___x_4203_);
if (v_isSharedCheck_4219_ == 0)
{
v___x_4214_ = v___x_4203_;
v_isShared_4215_ = v_isSharedCheck_4219_;
goto v_resetjp_4213_;
}
else
{
lean_inc(v_a_4212_);
lean_dec(v___x_4203_);
v___x_4214_ = lean_box(0);
v_isShared_4215_ = v_isSharedCheck_4219_;
goto v_resetjp_4213_;
}
v_resetjp_4213_:
{
lean_object* v___x_4217_; 
if (v_isShared_4215_ == 0)
{
v___x_4217_ = v___x_4214_;
goto v_reusejp_4216_;
}
else
{
lean_object* v_reuseFailAlloc_4218_; 
v_reuseFailAlloc_4218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4218_, 0, v_a_4212_);
v___x_4217_ = v_reuseFailAlloc_4218_;
goto v_reusejp_4216_;
}
v_reusejp_4216_:
{
return v___x_4217_;
}
}
}
}
else
{
return v___x_4200_;
}
}
}
}
else
{
lean_object* v_a_4221_; lean_object* v___x_4223_; uint8_t v_isShared_4224_; uint8_t v_isSharedCheck_4228_; 
v_a_4221_ = lean_ctor_get(v___x_4186_, 0);
v_isSharedCheck_4228_ = !lean_is_exclusive(v___x_4186_);
if (v_isSharedCheck_4228_ == 0)
{
v___x_4223_ = v___x_4186_;
v_isShared_4224_ = v_isSharedCheck_4228_;
goto v_resetjp_4222_;
}
else
{
lean_inc(v_a_4221_);
lean_dec(v___x_4186_);
v___x_4223_ = lean_box(0);
v_isShared_4224_ = v_isSharedCheck_4228_;
goto v_resetjp_4222_;
}
v_resetjp_4222_:
{
lean_object* v___x_4226_; 
if (v_isShared_4224_ == 0)
{
v___x_4226_ = v___x_4223_;
goto v_reusejp_4225_;
}
else
{
lean_object* v_reuseFailAlloc_4227_; 
v_reuseFailAlloc_4227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4227_, 0, v_a_4221_);
v___x_4226_ = v_reuseFailAlloc_4227_;
goto v_reusejp_4225_;
}
v_reusejp_4225_:
{
return v___x_4226_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatCastFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0_spec__1___boxed(lean_object* v___y_4229_, lean_object* v___y_4230_, lean_object* v___y_4231_, lean_object* v___y_4232_, lean_object* v___y_4233_, lean_object* v___y_4234_, lean_object* v___y_4235_, lean_object* v___y_4236_, lean_object* v___y_4237_, lean_object* v___y_4238_, lean_object* v___y_4239_, lean_object* v___y_4240_){
_start:
{
lean_object* v_res_4241_; 
v_res_4241_ = l_Lean_Meta_Sym_Arith_getNatCastFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0_spec__1(v___y_4229_, v___y_4230_, v___y_4231_, v___y_4232_, v___y_4233_, v___y_4234_, v___y_4235_, v___y_4236_, v___y_4237_, v___y_4238_, v___y_4239_);
lean_dec(v___y_4239_);
lean_dec_ref(v___y_4238_);
lean_dec(v___y_4237_);
lean_dec_ref(v___y_4236_);
lean_dec(v___y_4235_);
lean_dec_ref(v___y_4234_);
lean_dec(v___y_4233_);
lean_dec_ref(v___y_4232_);
lean_dec(v___y_4231_);
lean_dec(v___y_4230_);
lean_dec_ref(v___y_4229_);
return v_res_4241_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0___lam__2(lean_object* v_e_4242_, lean_object* v_s_4243_){
_start:
{
lean_object* v_toRingState_4244_; lean_object* v_denoteEntries_4245_; lean_object* v_nextId_4246_; lean_object* v_steps_4247_; lean_object* v_queue_4248_; lean_object* v_basis_4249_; lean_object* v_diseqs_4250_; uint8_t v_recheck_4251_; lean_object* v_invSet_4252_; lean_object* v_powIdentityVarCount_4253_; lean_object* v_numEq0_x3f_4254_; uint8_t v_numEq0Updated_4255_; lean_object* v___x_4257_; uint8_t v_isShared_4258_; uint8_t v_isSharedCheck_4276_; 
v_toRingState_4244_ = lean_ctor_get(v_s_4243_, 0);
v_denoteEntries_4245_ = lean_ctor_get(v_s_4243_, 1);
v_nextId_4246_ = lean_ctor_get(v_s_4243_, 2);
v_steps_4247_ = lean_ctor_get(v_s_4243_, 3);
v_queue_4248_ = lean_ctor_get(v_s_4243_, 4);
v_basis_4249_ = lean_ctor_get(v_s_4243_, 5);
v_diseqs_4250_ = lean_ctor_get(v_s_4243_, 6);
v_recheck_4251_ = lean_ctor_get_uint8(v_s_4243_, sizeof(void*)*10);
v_invSet_4252_ = lean_ctor_get(v_s_4243_, 7);
v_powIdentityVarCount_4253_ = lean_ctor_get(v_s_4243_, 8);
v_numEq0_x3f_4254_ = lean_ctor_get(v_s_4243_, 9);
v_numEq0Updated_4255_ = lean_ctor_get_uint8(v_s_4243_, sizeof(void*)*10 + 1);
v_isSharedCheck_4276_ = !lean_is_exclusive(v_s_4243_);
if (v_isSharedCheck_4276_ == 0)
{
v___x_4257_ = v_s_4243_;
v_isShared_4258_ = v_isSharedCheck_4276_;
goto v_resetjp_4256_;
}
else
{
lean_inc(v_numEq0_x3f_4254_);
lean_inc(v_powIdentityVarCount_4253_);
lean_inc(v_invSet_4252_);
lean_inc(v_diseqs_4250_);
lean_inc(v_basis_4249_);
lean_inc(v_queue_4248_);
lean_inc(v_steps_4247_);
lean_inc(v_nextId_4246_);
lean_inc(v_denoteEntries_4245_);
lean_inc(v_toRingState_4244_);
lean_dec(v_s_4243_);
v___x_4257_ = lean_box(0);
v_isShared_4258_ = v_isSharedCheck_4276_;
goto v_resetjp_4256_;
}
v_resetjp_4256_:
{
lean_object* v_vars_4259_; lean_object* v_varMap_4260_; lean_object* v_denote_4261_; lean_object* v_natCastSet_4262_; lean_object* v_natCasts_4263_; uint8_t v_hasIntCast_4264_; lean_object* v___x_4266_; uint8_t v_isShared_4267_; uint8_t v_isSharedCheck_4275_; 
v_vars_4259_ = lean_ctor_get(v_toRingState_4244_, 0);
v_varMap_4260_ = lean_ctor_get(v_toRingState_4244_, 1);
v_denote_4261_ = lean_ctor_get(v_toRingState_4244_, 2);
v_natCastSet_4262_ = lean_ctor_get(v_toRingState_4244_, 3);
v_natCasts_4263_ = lean_ctor_get(v_toRingState_4244_, 4);
v_hasIntCast_4264_ = lean_ctor_get_uint8(v_toRingState_4244_, sizeof(void*)*5);
v_isSharedCheck_4275_ = !lean_is_exclusive(v_toRingState_4244_);
if (v_isSharedCheck_4275_ == 0)
{
v___x_4266_ = v_toRingState_4244_;
v_isShared_4267_ = v_isSharedCheck_4275_;
goto v_resetjp_4265_;
}
else
{
lean_inc(v_natCasts_4263_);
lean_inc(v_natCastSet_4262_);
lean_inc(v_denote_4261_);
lean_inc(v_varMap_4260_);
lean_inc(v_vars_4259_);
lean_dec(v_toRingState_4244_);
v___x_4266_ = lean_box(0);
v_isShared_4267_ = v_isSharedCheck_4275_;
goto v_resetjp_4265_;
}
v_resetjp_4265_:
{
lean_object* v___x_4268_; lean_object* v___x_4270_; 
v___x_4268_ = l_Lean_PersistentArray_push___redArg(v_natCasts_4263_, v_e_4242_);
if (v_isShared_4267_ == 0)
{
lean_ctor_set(v___x_4266_, 4, v___x_4268_);
v___x_4270_ = v___x_4266_;
goto v_reusejp_4269_;
}
else
{
lean_object* v_reuseFailAlloc_4274_; 
v_reuseFailAlloc_4274_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_4274_, 0, v_vars_4259_);
lean_ctor_set(v_reuseFailAlloc_4274_, 1, v_varMap_4260_);
lean_ctor_set(v_reuseFailAlloc_4274_, 2, v_denote_4261_);
lean_ctor_set(v_reuseFailAlloc_4274_, 3, v_natCastSet_4262_);
lean_ctor_set(v_reuseFailAlloc_4274_, 4, v___x_4268_);
lean_ctor_set_uint8(v_reuseFailAlloc_4274_, sizeof(void*)*5, v_hasIntCast_4264_);
v___x_4270_ = v_reuseFailAlloc_4274_;
goto v_reusejp_4269_;
}
v_reusejp_4269_:
{
lean_object* v___x_4272_; 
if (v_isShared_4258_ == 0)
{
lean_ctor_set(v___x_4257_, 0, v___x_4270_);
v___x_4272_ = v___x_4257_;
goto v_reusejp_4271_;
}
else
{
lean_object* v_reuseFailAlloc_4273_; 
v_reuseFailAlloc_4273_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v_reuseFailAlloc_4273_, 0, v___x_4270_);
lean_ctor_set(v_reuseFailAlloc_4273_, 1, v_denoteEntries_4245_);
lean_ctor_set(v_reuseFailAlloc_4273_, 2, v_nextId_4246_);
lean_ctor_set(v_reuseFailAlloc_4273_, 3, v_steps_4247_);
lean_ctor_set(v_reuseFailAlloc_4273_, 4, v_queue_4248_);
lean_ctor_set(v_reuseFailAlloc_4273_, 5, v_basis_4249_);
lean_ctor_set(v_reuseFailAlloc_4273_, 6, v_diseqs_4250_);
lean_ctor_set(v_reuseFailAlloc_4273_, 7, v_invSet_4252_);
lean_ctor_set(v_reuseFailAlloc_4273_, 8, v_powIdentityVarCount_4253_);
lean_ctor_set(v_reuseFailAlloc_4273_, 9, v_numEq0_x3f_4254_);
lean_ctor_set_uint8(v_reuseFailAlloc_4273_, sizeof(void*)*10, v_recheck_4251_);
lean_ctor_set_uint8(v_reuseFailAlloc_4273_, sizeof(void*)*10 + 1, v_numEq0Updated_4255_);
v___x_4272_ = v_reuseFailAlloc_4273_;
goto v_reusejp_4271_;
}
v_reusejp_4271_:
{
return v___x_4272_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0___lam__0(lean_object* v_____do__lift_4277_, lean_object* v___y_4278_, lean_object* v___y_4279_, lean_object* v___y_4280_, lean_object* v___y_4281_, lean_object* v___y_4282_, lean_object* v___y_4283_, lean_object* v___y_4284_, lean_object* v___y_4285_, lean_object* v___y_4286_, lean_object* v___y_4287_, lean_object* v___y_4288_){
_start:
{
lean_object* v_toRingState_4290_; lean_object* v___x_4291_; 
v_toRingState_4290_ = lean_ctor_get(v_____do__lift_4277_, 0);
lean_inc_ref(v_toRingState_4290_);
v___x_4291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4291_, 0, v_toRingState_4290_);
return v___x_4291_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0___lam__0___boxed(lean_object* v_____do__lift_4292_, lean_object* v___y_4293_, lean_object* v___y_4294_, lean_object* v___y_4295_, lean_object* v___y_4296_, lean_object* v___y_4297_, lean_object* v___y_4298_, lean_object* v___y_4299_, lean_object* v___y_4300_, lean_object* v___y_4301_, lean_object* v___y_4302_, lean_object* v___y_4303_, lean_object* v___y_4304_){
_start:
{
lean_object* v_res_4305_; 
v_res_4305_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0___lam__0(v_____do__lift_4292_, v___y_4293_, v___y_4294_, v___y_4295_, v___y_4296_, v___y_4297_, v___y_4298_, v___y_4299_, v___y_4300_, v___y_4301_, v___y_4302_, v___y_4303_);
lean_dec(v___y_4303_);
lean_dec_ref(v___y_4302_);
lean_dec(v___y_4301_);
lean_dec_ref(v___y_4300_);
lean_dec(v___y_4299_);
lean_dec_ref(v___y_4298_);
lean_dec(v___y_4297_);
lean_dec_ref(v___y_4296_);
lean_dec(v___y_4295_);
lean_dec(v___y_4294_);
lean_dec_ref(v___y_4293_);
lean_dec_ref(v_____do__lift_4292_);
return v_res_4305_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0_spec__4_spec__9___redArg(lean_object* v___x_4306_, lean_object* v_a_4307_, lean_object* v_as_4308_, size_t v_i_4309_, size_t v_stop_4310_, lean_object* v_b_4311_, lean_object* v___y_4312_, lean_object* v___y_4313_, lean_object* v___y_4314_, lean_object* v___y_4315_, lean_object* v___y_4316_, lean_object* v___y_4317_, lean_object* v___y_4318_){
_start:
{
uint8_t v___x_4320_; 
v___x_4320_ = lean_usize_dec_eq(v_i_4309_, v_stop_4310_);
if (v___x_4320_ == 0)
{
lean_object* v___x_4321_; lean_object* v___x_4322_; 
v___x_4321_ = lean_array_uget_borrowed(v_as_4308_, v_i_4309_);
lean_inc(v___x_4321_);
lean_inc_ref(v_a_4307_);
lean_inc_ref(v___x_4306_);
v___x_4322_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_pushNatCastFact___redArg(v___x_4306_, v_a_4307_, v___x_4321_, v___y_4312_, v___y_4313_, v___y_4314_, v___y_4315_, v___y_4316_, v___y_4317_, v___y_4318_);
if (lean_obj_tag(v___x_4322_) == 0)
{
lean_object* v_a_4323_; size_t v___x_4324_; size_t v___x_4325_; 
v_a_4323_ = lean_ctor_get(v___x_4322_, 0);
lean_inc(v_a_4323_);
lean_dec_ref_known(v___x_4322_, 1);
v___x_4324_ = ((size_t)1ULL);
v___x_4325_ = lean_usize_add(v_i_4309_, v___x_4324_);
v_i_4309_ = v___x_4325_;
v_b_4311_ = v_a_4323_;
goto _start;
}
else
{
lean_dec_ref(v_a_4307_);
lean_dec_ref(v___x_4306_);
return v___x_4322_;
}
}
else
{
lean_object* v___x_4327_; 
lean_dec_ref(v_a_4307_);
lean_dec_ref(v___x_4306_);
v___x_4327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4327_, 0, v_b_4311_);
return v___x_4327_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0_spec__4_spec__9___redArg___boxed(lean_object* v___x_4328_, lean_object* v_a_4329_, lean_object* v_as_4330_, lean_object* v_i_4331_, lean_object* v_stop_4332_, lean_object* v_b_4333_, lean_object* v___y_4334_, lean_object* v___y_4335_, lean_object* v___y_4336_, lean_object* v___y_4337_, lean_object* v___y_4338_, lean_object* v___y_4339_, lean_object* v___y_4340_, lean_object* v___y_4341_){
_start:
{
size_t v_i_boxed_4342_; size_t v_stop_boxed_4343_; lean_object* v_res_4344_; 
v_i_boxed_4342_ = lean_unbox_usize(v_i_4331_);
lean_dec(v_i_4331_);
v_stop_boxed_4343_ = lean_unbox_usize(v_stop_4332_);
lean_dec(v_stop_4332_);
v_res_4344_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0_spec__4_spec__9___redArg(v___x_4328_, v_a_4329_, v_as_4330_, v_i_boxed_4342_, v_stop_boxed_4343_, v_b_4333_, v___y_4334_, v___y_4335_, v___y_4336_, v___y_4337_, v___y_4338_, v___y_4339_, v___y_4340_);
lean_dec(v___y_4340_);
lean_dec_ref(v___y_4339_);
lean_dec(v___y_4338_);
lean_dec_ref(v___y_4337_);
lean_dec(v___y_4336_);
lean_dec_ref(v___y_4335_);
lean_dec(v___y_4334_);
lean_dec_ref(v_as_4330_);
return v_res_4344_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0_spec__4_spec__8_spec__14(lean_object* v___x_4345_, lean_object* v_a_4346_, lean_object* v_x_4347_, lean_object* v___y_4348_, lean_object* v___y_4349_, lean_object* v___y_4350_, lean_object* v___y_4351_, lean_object* v___y_4352_, lean_object* v___y_4353_, lean_object* v___y_4354_, lean_object* v___y_4355_, lean_object* v___y_4356_, lean_object* v___y_4357_, lean_object* v___y_4358_){
_start:
{
if (lean_obj_tag(v_x_4347_) == 0)
{
lean_object* v_cs_4360_; lean_object* v___x_4362_; uint8_t v_isShared_4363_; uint8_t v_isSharedCheck_4374_; 
v_cs_4360_ = lean_ctor_get(v_x_4347_, 0);
v_isSharedCheck_4374_ = !lean_is_exclusive(v_x_4347_);
if (v_isSharedCheck_4374_ == 0)
{
v___x_4362_ = v_x_4347_;
v_isShared_4363_ = v_isSharedCheck_4374_;
goto v_resetjp_4361_;
}
else
{
lean_inc(v_cs_4360_);
lean_dec(v_x_4347_);
v___x_4362_ = lean_box(0);
v_isShared_4363_ = v_isSharedCheck_4374_;
goto v_resetjp_4361_;
}
v_resetjp_4361_:
{
lean_object* v___x_4364_; lean_object* v___x_4365_; lean_object* v___x_4366_; uint8_t v___x_4367_; 
v___x_4364_ = lean_unsigned_to_nat(0u);
v___x_4365_ = lean_array_get_size(v_cs_4360_);
v___x_4366_ = lean_box(0);
v___x_4367_ = lean_nat_dec_lt(v___x_4364_, v___x_4365_);
if (v___x_4367_ == 0)
{
lean_object* v___x_4369_; 
lean_dec_ref(v_cs_4360_);
lean_dec_ref(v_a_4346_);
lean_dec_ref(v___x_4345_);
if (v_isShared_4363_ == 0)
{
lean_ctor_set(v___x_4362_, 0, v___x_4366_);
v___x_4369_ = v___x_4362_;
goto v_reusejp_4368_;
}
else
{
lean_object* v_reuseFailAlloc_4370_; 
v_reuseFailAlloc_4370_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4370_, 0, v___x_4366_);
v___x_4369_ = v_reuseFailAlloc_4370_;
goto v_reusejp_4368_;
}
v_reusejp_4368_:
{
return v___x_4369_;
}
}
else
{
size_t v___x_4371_; size_t v___x_4372_; lean_object* v___x_4373_; 
lean_del_object(v___x_4362_);
v___x_4371_ = ((size_t)0ULL);
v___x_4372_ = lean_usize_of_nat(v___x_4365_);
v___x_4373_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0_spec__4_spec__8_spec__15(v___x_4345_, v_a_4346_, v_cs_4360_, v___x_4371_, v___x_4372_, v___x_4366_, v___y_4348_, v___y_4349_, v___y_4350_, v___y_4351_, v___y_4352_, v___y_4353_, v___y_4354_, v___y_4355_, v___y_4356_, v___y_4357_, v___y_4358_);
lean_dec_ref(v_cs_4360_);
return v___x_4373_;
}
}
}
else
{
lean_object* v_vs_4375_; lean_object* v___x_4377_; uint8_t v_isShared_4378_; uint8_t v_isSharedCheck_4389_; 
v_vs_4375_ = lean_ctor_get(v_x_4347_, 0);
v_isSharedCheck_4389_ = !lean_is_exclusive(v_x_4347_);
if (v_isSharedCheck_4389_ == 0)
{
v___x_4377_ = v_x_4347_;
v_isShared_4378_ = v_isSharedCheck_4389_;
goto v_resetjp_4376_;
}
else
{
lean_inc(v_vs_4375_);
lean_dec(v_x_4347_);
v___x_4377_ = lean_box(0);
v_isShared_4378_ = v_isSharedCheck_4389_;
goto v_resetjp_4376_;
}
v_resetjp_4376_:
{
lean_object* v___x_4379_; lean_object* v___x_4380_; lean_object* v___x_4381_; uint8_t v___x_4382_; 
v___x_4379_ = lean_unsigned_to_nat(0u);
v___x_4380_ = lean_array_get_size(v_vs_4375_);
v___x_4381_ = lean_box(0);
v___x_4382_ = lean_nat_dec_lt(v___x_4379_, v___x_4380_);
if (v___x_4382_ == 0)
{
lean_object* v___x_4384_; 
lean_dec_ref(v_vs_4375_);
lean_dec_ref(v_a_4346_);
lean_dec_ref(v___x_4345_);
if (v_isShared_4378_ == 0)
{
lean_ctor_set_tag(v___x_4377_, 0);
lean_ctor_set(v___x_4377_, 0, v___x_4381_);
v___x_4384_ = v___x_4377_;
goto v_reusejp_4383_;
}
else
{
lean_object* v_reuseFailAlloc_4385_; 
v_reuseFailAlloc_4385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4385_, 0, v___x_4381_);
v___x_4384_ = v_reuseFailAlloc_4385_;
goto v_reusejp_4383_;
}
v_reusejp_4383_:
{
return v___x_4384_;
}
}
else
{
size_t v___x_4386_; size_t v___x_4387_; lean_object* v___x_4388_; 
lean_del_object(v___x_4377_);
v___x_4386_ = ((size_t)0ULL);
v___x_4387_ = lean_usize_of_nat(v___x_4380_);
v___x_4388_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0_spec__4_spec__9___redArg(v___x_4345_, v_a_4346_, v_vs_4375_, v___x_4386_, v___x_4387_, v___x_4381_, v___y_4349_, v___y_4353_, v___y_4354_, v___y_4355_, v___y_4356_, v___y_4357_, v___y_4358_);
lean_dec_ref(v_vs_4375_);
return v___x_4388_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0_spec__4_spec__8_spec__15(lean_object* v___x_4390_, lean_object* v_a_4391_, lean_object* v_as_4392_, size_t v_i_4393_, size_t v_stop_4394_, lean_object* v_b_4395_, lean_object* v___y_4396_, lean_object* v___y_4397_, lean_object* v___y_4398_, lean_object* v___y_4399_, lean_object* v___y_4400_, lean_object* v___y_4401_, lean_object* v___y_4402_, lean_object* v___y_4403_, lean_object* v___y_4404_, lean_object* v___y_4405_, lean_object* v___y_4406_){
_start:
{
uint8_t v___x_4408_; 
v___x_4408_ = lean_usize_dec_eq(v_i_4393_, v_stop_4394_);
if (v___x_4408_ == 0)
{
lean_object* v___x_4409_; lean_object* v___x_4410_; 
v___x_4409_ = lean_array_uget_borrowed(v_as_4392_, v_i_4393_);
lean_inc(v___x_4409_);
lean_inc_ref(v_a_4391_);
lean_inc_ref(v___x_4390_);
v___x_4410_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0_spec__4_spec__8_spec__14(v___x_4390_, v_a_4391_, v___x_4409_, v___y_4396_, v___y_4397_, v___y_4398_, v___y_4399_, v___y_4400_, v___y_4401_, v___y_4402_, v___y_4403_, v___y_4404_, v___y_4405_, v___y_4406_);
if (lean_obj_tag(v___x_4410_) == 0)
{
lean_object* v_a_4411_; size_t v___x_4412_; size_t v___x_4413_; 
v_a_4411_ = lean_ctor_get(v___x_4410_, 0);
lean_inc(v_a_4411_);
lean_dec_ref_known(v___x_4410_, 1);
v___x_4412_ = ((size_t)1ULL);
v___x_4413_ = lean_usize_add(v_i_4393_, v___x_4412_);
v_i_4393_ = v___x_4413_;
v_b_4395_ = v_a_4411_;
goto _start;
}
else
{
lean_dec_ref(v_a_4391_);
lean_dec_ref(v___x_4390_);
return v___x_4410_;
}
}
else
{
lean_object* v___x_4415_; 
lean_dec_ref(v_a_4391_);
lean_dec_ref(v___x_4390_);
v___x_4415_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4415_, 0, v_b_4395_);
return v___x_4415_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0_spec__4_spec__8_spec__15___boxed(lean_object** _args){
lean_object* v___x_4416_ = _args[0];
lean_object* v_a_4417_ = _args[1];
lean_object* v_as_4418_ = _args[2];
lean_object* v_i_4419_ = _args[3];
lean_object* v_stop_4420_ = _args[4];
lean_object* v_b_4421_ = _args[5];
lean_object* v___y_4422_ = _args[6];
lean_object* v___y_4423_ = _args[7];
lean_object* v___y_4424_ = _args[8];
lean_object* v___y_4425_ = _args[9];
lean_object* v___y_4426_ = _args[10];
lean_object* v___y_4427_ = _args[11];
lean_object* v___y_4428_ = _args[12];
lean_object* v___y_4429_ = _args[13];
lean_object* v___y_4430_ = _args[14];
lean_object* v___y_4431_ = _args[15];
lean_object* v___y_4432_ = _args[16];
lean_object* v___y_4433_ = _args[17];
_start:
{
size_t v_i_boxed_4434_; size_t v_stop_boxed_4435_; lean_object* v_res_4436_; 
v_i_boxed_4434_ = lean_unbox_usize(v_i_4419_);
lean_dec(v_i_4419_);
v_stop_boxed_4435_ = lean_unbox_usize(v_stop_4420_);
lean_dec(v_stop_4420_);
v_res_4436_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0_spec__4_spec__8_spec__15(v___x_4416_, v_a_4417_, v_as_4418_, v_i_boxed_4434_, v_stop_boxed_4435_, v_b_4421_, v___y_4422_, v___y_4423_, v___y_4424_, v___y_4425_, v___y_4426_, v___y_4427_, v___y_4428_, v___y_4429_, v___y_4430_, v___y_4431_, v___y_4432_);
lean_dec(v___y_4432_);
lean_dec_ref(v___y_4431_);
lean_dec(v___y_4430_);
lean_dec_ref(v___y_4429_);
lean_dec(v___y_4428_);
lean_dec_ref(v___y_4427_);
lean_dec(v___y_4426_);
lean_dec_ref(v___y_4425_);
lean_dec(v___y_4424_);
lean_dec(v___y_4423_);
lean_dec_ref(v___y_4422_);
lean_dec_ref(v_as_4418_);
return v_res_4436_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0_spec__4_spec__8_spec__14___boxed(lean_object* v___x_4437_, lean_object* v_a_4438_, lean_object* v_x_4439_, lean_object* v___y_4440_, lean_object* v___y_4441_, lean_object* v___y_4442_, lean_object* v___y_4443_, lean_object* v___y_4444_, lean_object* v___y_4445_, lean_object* v___y_4446_, lean_object* v___y_4447_, lean_object* v___y_4448_, lean_object* v___y_4449_, lean_object* v___y_4450_, lean_object* v___y_4451_){
_start:
{
lean_object* v_res_4452_; 
v_res_4452_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0_spec__4_spec__8_spec__14(v___x_4437_, v_a_4438_, v_x_4439_, v___y_4440_, v___y_4441_, v___y_4442_, v___y_4443_, v___y_4444_, v___y_4445_, v___y_4446_, v___y_4447_, v___y_4448_, v___y_4449_, v___y_4450_);
lean_dec(v___y_4450_);
lean_dec_ref(v___y_4449_);
lean_dec(v___y_4448_);
lean_dec_ref(v___y_4447_);
lean_dec(v___y_4446_);
lean_dec_ref(v___y_4445_);
lean_dec(v___y_4444_);
lean_dec_ref(v___y_4443_);
lean_dec(v___y_4442_);
lean_dec(v___y_4441_);
lean_dec_ref(v___y_4440_);
return v_res_4452_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0_spec__4_spec__8(lean_object* v___x_4453_, lean_object* v_a_4454_, lean_object* v_x_4455_, size_t v_x_4456_, size_t v_x_4457_, lean_object* v___y_4458_, lean_object* v___y_4459_, lean_object* v___y_4460_, lean_object* v___y_4461_, lean_object* v___y_4462_, lean_object* v___y_4463_, lean_object* v___y_4464_, lean_object* v___y_4465_, lean_object* v___y_4466_, lean_object* v___y_4467_, lean_object* v___y_4468_){
_start:
{
if (lean_obj_tag(v_x_4455_) == 0)
{
lean_object* v_cs_4470_; lean_object* v___x_4471_; size_t v___x_4472_; lean_object* v_j_4473_; lean_object* v___x_4474_; size_t v___x_4475_; size_t v___x_4476_; size_t v___x_4477_; size_t v___x_4478_; size_t v___x_4479_; size_t v___x_4480_; lean_object* v___x_4481_; 
v_cs_4470_ = lean_ctor_get(v_x_4455_, 0);
lean_inc_ref(v_cs_4470_);
lean_dec_ref_known(v_x_4455_, 1);
v___x_4471_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__1_spec__8_spec__16___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__1_spec__8_spec__16___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__1_spec__8_spec__16___closed__0);
v___x_4472_ = lean_usize_shift_right(v_x_4456_, v_x_4457_);
v_j_4473_ = lean_usize_to_nat(v___x_4472_);
v___x_4474_ = lean_array_get_borrowed(v___x_4471_, v_cs_4470_, v_j_4473_);
v___x_4475_ = ((size_t)1ULL);
v___x_4476_ = lean_usize_shift_left(v___x_4475_, v_x_4457_);
v___x_4477_ = lean_usize_sub(v___x_4476_, v___x_4475_);
v___x_4478_ = lean_usize_land(v_x_4456_, v___x_4477_);
v___x_4479_ = ((size_t)5ULL);
v___x_4480_ = lean_usize_sub(v_x_4457_, v___x_4479_);
lean_inc(v___x_4474_);
lean_inc_ref(v_a_4454_);
lean_inc_ref(v___x_4453_);
v___x_4481_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0_spec__4_spec__8(v___x_4453_, v_a_4454_, v___x_4474_, v___x_4478_, v___x_4480_, v___y_4458_, v___y_4459_, v___y_4460_, v___y_4461_, v___y_4462_, v___y_4463_, v___y_4464_, v___y_4465_, v___y_4466_, v___y_4467_, v___y_4468_);
if (lean_obj_tag(v___x_4481_) == 0)
{
lean_object* v___x_4483_; uint8_t v_isShared_4484_; uint8_t v_isSharedCheck_4496_; 
v_isSharedCheck_4496_ = !lean_is_exclusive(v___x_4481_);
if (v_isSharedCheck_4496_ == 0)
{
lean_object* v_unused_4497_; 
v_unused_4497_ = lean_ctor_get(v___x_4481_, 0);
lean_dec(v_unused_4497_);
v___x_4483_ = v___x_4481_;
v_isShared_4484_ = v_isSharedCheck_4496_;
goto v_resetjp_4482_;
}
else
{
lean_dec(v___x_4481_);
v___x_4483_ = lean_box(0);
v_isShared_4484_ = v_isSharedCheck_4496_;
goto v_resetjp_4482_;
}
v_resetjp_4482_:
{
lean_object* v___x_4485_; lean_object* v___x_4486_; lean_object* v___x_4487_; lean_object* v___x_4488_; uint8_t v___x_4489_; 
v___x_4485_ = lean_unsigned_to_nat(1u);
v___x_4486_ = lean_nat_add(v_j_4473_, v___x_4485_);
lean_dec(v_j_4473_);
v___x_4487_ = lean_array_get_size(v_cs_4470_);
v___x_4488_ = lean_box(0);
v___x_4489_ = lean_nat_dec_lt(v___x_4486_, v___x_4487_);
if (v___x_4489_ == 0)
{
lean_object* v___x_4491_; 
lean_dec(v___x_4486_);
lean_dec_ref(v_cs_4470_);
lean_dec_ref(v_a_4454_);
lean_dec_ref(v___x_4453_);
if (v_isShared_4484_ == 0)
{
lean_ctor_set(v___x_4483_, 0, v___x_4488_);
v___x_4491_ = v___x_4483_;
goto v_reusejp_4490_;
}
else
{
lean_object* v_reuseFailAlloc_4492_; 
v_reuseFailAlloc_4492_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4492_, 0, v___x_4488_);
v___x_4491_ = v_reuseFailAlloc_4492_;
goto v_reusejp_4490_;
}
v_reusejp_4490_:
{
return v___x_4491_;
}
}
else
{
size_t v___x_4493_; size_t v___x_4494_; lean_object* v___x_4495_; 
lean_del_object(v___x_4483_);
v___x_4493_ = lean_usize_of_nat(v___x_4486_);
lean_dec(v___x_4486_);
v___x_4494_ = lean_usize_of_nat(v___x_4487_);
v___x_4495_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0_spec__4_spec__8_spec__15(v___x_4453_, v_a_4454_, v_cs_4470_, v___x_4493_, v___x_4494_, v___x_4488_, v___y_4458_, v___y_4459_, v___y_4460_, v___y_4461_, v___y_4462_, v___y_4463_, v___y_4464_, v___y_4465_, v___y_4466_, v___y_4467_, v___y_4468_);
lean_dec_ref(v_cs_4470_);
return v___x_4495_;
}
}
}
else
{
lean_dec(v_j_4473_);
lean_dec_ref(v_cs_4470_);
lean_dec_ref(v_a_4454_);
lean_dec_ref(v___x_4453_);
return v___x_4481_;
}
}
else
{
lean_object* v_vs_4498_; lean_object* v___x_4500_; uint8_t v_isShared_4501_; uint8_t v_isSharedCheck_4512_; 
v_vs_4498_ = lean_ctor_get(v_x_4455_, 0);
v_isSharedCheck_4512_ = !lean_is_exclusive(v_x_4455_);
if (v_isSharedCheck_4512_ == 0)
{
v___x_4500_ = v_x_4455_;
v_isShared_4501_ = v_isSharedCheck_4512_;
goto v_resetjp_4499_;
}
else
{
lean_inc(v_vs_4498_);
lean_dec(v_x_4455_);
v___x_4500_ = lean_box(0);
v_isShared_4501_ = v_isSharedCheck_4512_;
goto v_resetjp_4499_;
}
v_resetjp_4499_:
{
lean_object* v___x_4502_; lean_object* v___x_4503_; lean_object* v___x_4504_; uint8_t v___x_4505_; 
v___x_4502_ = lean_usize_to_nat(v_x_4456_);
v___x_4503_ = lean_array_get_size(v_vs_4498_);
v___x_4504_ = lean_box(0);
v___x_4505_ = lean_nat_dec_lt(v___x_4502_, v___x_4503_);
if (v___x_4505_ == 0)
{
lean_object* v___x_4507_; 
lean_dec(v___x_4502_);
lean_dec_ref(v_vs_4498_);
lean_dec_ref(v_a_4454_);
lean_dec_ref(v___x_4453_);
if (v_isShared_4501_ == 0)
{
lean_ctor_set_tag(v___x_4500_, 0);
lean_ctor_set(v___x_4500_, 0, v___x_4504_);
v___x_4507_ = v___x_4500_;
goto v_reusejp_4506_;
}
else
{
lean_object* v_reuseFailAlloc_4508_; 
v_reuseFailAlloc_4508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4508_, 0, v___x_4504_);
v___x_4507_ = v_reuseFailAlloc_4508_;
goto v_reusejp_4506_;
}
v_reusejp_4506_:
{
return v___x_4507_;
}
}
else
{
size_t v___x_4509_; size_t v___x_4510_; lean_object* v___x_4511_; 
lean_del_object(v___x_4500_);
v___x_4509_ = lean_usize_of_nat(v___x_4502_);
lean_dec(v___x_4502_);
v___x_4510_ = lean_usize_of_nat(v___x_4503_);
v___x_4511_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0_spec__4_spec__9___redArg(v___x_4453_, v_a_4454_, v_vs_4498_, v___x_4509_, v___x_4510_, v___x_4504_, v___y_4459_, v___y_4463_, v___y_4464_, v___y_4465_, v___y_4466_, v___y_4467_, v___y_4468_);
lean_dec_ref(v_vs_4498_);
return v___x_4511_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0_spec__4_spec__8___boxed(lean_object** _args){
lean_object* v___x_4513_ = _args[0];
lean_object* v_a_4514_ = _args[1];
lean_object* v_x_4515_ = _args[2];
lean_object* v_x_4516_ = _args[3];
lean_object* v_x_4517_ = _args[4];
lean_object* v___y_4518_ = _args[5];
lean_object* v___y_4519_ = _args[6];
lean_object* v___y_4520_ = _args[7];
lean_object* v___y_4521_ = _args[8];
lean_object* v___y_4522_ = _args[9];
lean_object* v___y_4523_ = _args[10];
lean_object* v___y_4524_ = _args[11];
lean_object* v___y_4525_ = _args[12];
lean_object* v___y_4526_ = _args[13];
lean_object* v___y_4527_ = _args[14];
lean_object* v___y_4528_ = _args[15];
lean_object* v___y_4529_ = _args[16];
_start:
{
size_t v_x_133290__boxed_4530_; size_t v_x_133291__boxed_4531_; lean_object* v_res_4532_; 
v_x_133290__boxed_4530_ = lean_unbox_usize(v_x_4516_);
lean_dec(v_x_4516_);
v_x_133291__boxed_4531_ = lean_unbox_usize(v_x_4517_);
lean_dec(v_x_4517_);
v_res_4532_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0_spec__4_spec__8(v___x_4513_, v_a_4514_, v_x_4515_, v_x_133290__boxed_4530_, v_x_133291__boxed_4531_, v___y_4518_, v___y_4519_, v___y_4520_, v___y_4521_, v___y_4522_, v___y_4523_, v___y_4524_, v___y_4525_, v___y_4526_, v___y_4527_, v___y_4528_);
lean_dec(v___y_4528_);
lean_dec_ref(v___y_4527_);
lean_dec(v___y_4526_);
lean_dec_ref(v___y_4525_);
lean_dec(v___y_4524_);
lean_dec_ref(v___y_4523_);
lean_dec(v___y_4522_);
lean_dec_ref(v___y_4521_);
lean_dec(v___y_4520_);
lean_dec(v___y_4519_);
lean_dec_ref(v___y_4518_);
return v_res_4532_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0_spec__4_spec__10(lean_object* v___x_4533_, lean_object* v_a_4534_, lean_object* v_t_4535_, lean_object* v___y_4536_, lean_object* v___y_4537_, lean_object* v___y_4538_, lean_object* v___y_4539_, lean_object* v___y_4540_, lean_object* v___y_4541_, lean_object* v___y_4542_, lean_object* v___y_4543_, lean_object* v___y_4544_, lean_object* v___y_4545_, lean_object* v___y_4546_){
_start:
{
lean_object* v_root_4548_; lean_object* v_tail_4549_; lean_object* v___x_4550_; 
v_root_4548_ = lean_ctor_get(v_t_4535_, 0);
lean_inc_ref(v_root_4548_);
v_tail_4549_ = lean_ctor_get(v_t_4535_, 1);
lean_inc_ref(v_tail_4549_);
lean_dec_ref(v_t_4535_);
lean_inc_ref(v_a_4534_);
lean_inc_ref(v___x_4533_);
v___x_4550_ = l_Lean_PersistentArray_forMAux___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0_spec__4_spec__8_spec__14(v___x_4533_, v_a_4534_, v_root_4548_, v___y_4536_, v___y_4537_, v___y_4538_, v___y_4539_, v___y_4540_, v___y_4541_, v___y_4542_, v___y_4543_, v___y_4544_, v___y_4545_, v___y_4546_);
if (lean_obj_tag(v___x_4550_) == 0)
{
lean_object* v___x_4552_; uint8_t v_isShared_4553_; uint8_t v_isSharedCheck_4564_; 
v_isSharedCheck_4564_ = !lean_is_exclusive(v___x_4550_);
if (v_isSharedCheck_4564_ == 0)
{
lean_object* v_unused_4565_; 
v_unused_4565_ = lean_ctor_get(v___x_4550_, 0);
lean_dec(v_unused_4565_);
v___x_4552_ = v___x_4550_;
v_isShared_4553_ = v_isSharedCheck_4564_;
goto v_resetjp_4551_;
}
else
{
lean_dec(v___x_4550_);
v___x_4552_ = lean_box(0);
v_isShared_4553_ = v_isSharedCheck_4564_;
goto v_resetjp_4551_;
}
v_resetjp_4551_:
{
lean_object* v___x_4554_; lean_object* v___x_4555_; lean_object* v___x_4556_; uint8_t v___x_4557_; 
v___x_4554_ = lean_unsigned_to_nat(0u);
v___x_4555_ = lean_array_get_size(v_tail_4549_);
v___x_4556_ = lean_box(0);
v___x_4557_ = lean_nat_dec_lt(v___x_4554_, v___x_4555_);
if (v___x_4557_ == 0)
{
lean_object* v___x_4559_; 
lean_dec_ref(v_tail_4549_);
lean_dec_ref(v_a_4534_);
lean_dec_ref(v___x_4533_);
if (v_isShared_4553_ == 0)
{
lean_ctor_set(v___x_4552_, 0, v___x_4556_);
v___x_4559_ = v___x_4552_;
goto v_reusejp_4558_;
}
else
{
lean_object* v_reuseFailAlloc_4560_; 
v_reuseFailAlloc_4560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4560_, 0, v___x_4556_);
v___x_4559_ = v_reuseFailAlloc_4560_;
goto v_reusejp_4558_;
}
v_reusejp_4558_:
{
return v___x_4559_;
}
}
else
{
size_t v___x_4561_; size_t v___x_4562_; lean_object* v___x_4563_; 
lean_del_object(v___x_4552_);
v___x_4561_ = ((size_t)0ULL);
v___x_4562_ = lean_usize_of_nat(v___x_4555_);
v___x_4563_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0_spec__4_spec__9___redArg(v___x_4533_, v_a_4534_, v_tail_4549_, v___x_4561_, v___x_4562_, v___x_4556_, v___y_4537_, v___y_4541_, v___y_4542_, v___y_4543_, v___y_4544_, v___y_4545_, v___y_4546_);
lean_dec_ref(v_tail_4549_);
return v___x_4563_;
}
}
}
else
{
lean_dec_ref(v_tail_4549_);
lean_dec_ref(v_a_4534_);
lean_dec_ref(v___x_4533_);
return v___x_4550_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0_spec__4_spec__10___boxed(lean_object* v___x_4566_, lean_object* v_a_4567_, lean_object* v_t_4568_, lean_object* v___y_4569_, lean_object* v___y_4570_, lean_object* v___y_4571_, lean_object* v___y_4572_, lean_object* v___y_4573_, lean_object* v___y_4574_, lean_object* v___y_4575_, lean_object* v___y_4576_, lean_object* v___y_4577_, lean_object* v___y_4578_, lean_object* v___y_4579_, lean_object* v___y_4580_){
_start:
{
lean_object* v_res_4581_; 
v_res_4581_ = l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0_spec__4_spec__10(v___x_4566_, v_a_4567_, v_t_4568_, v___y_4569_, v___y_4570_, v___y_4571_, v___y_4572_, v___y_4573_, v___y_4574_, v___y_4575_, v___y_4576_, v___y_4577_, v___y_4578_, v___y_4579_);
lean_dec(v___y_4579_);
lean_dec_ref(v___y_4578_);
lean_dec(v___y_4577_);
lean_dec_ref(v___y_4576_);
lean_dec(v___y_4575_);
lean_dec_ref(v___y_4574_);
lean_dec(v___y_4573_);
lean_dec_ref(v___y_4572_);
lean_dec(v___y_4571_);
lean_dec(v___y_4570_);
lean_dec_ref(v___y_4569_);
return v_res_4581_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0_spec__4(lean_object* v___x_4582_, lean_object* v_a_4583_, lean_object* v_t_4584_, lean_object* v_start_4585_, lean_object* v___y_4586_, lean_object* v___y_4587_, lean_object* v___y_4588_, lean_object* v___y_4589_, lean_object* v___y_4590_, lean_object* v___y_4591_, lean_object* v___y_4592_, lean_object* v___y_4593_, lean_object* v___y_4594_, lean_object* v___y_4595_, lean_object* v___y_4596_){
_start:
{
lean_object* v___x_4598_; uint8_t v___x_4599_; 
v___x_4598_ = lean_unsigned_to_nat(0u);
v___x_4599_ = lean_nat_dec_eq(v_start_4585_, v___x_4598_);
if (v___x_4599_ == 0)
{
lean_object* v_root_4600_; lean_object* v_tail_4601_; size_t v_shift_4602_; lean_object* v_tailOff_4603_; uint8_t v___x_4604_; 
v_root_4600_ = lean_ctor_get(v_t_4584_, 0);
lean_inc_ref(v_root_4600_);
v_tail_4601_ = lean_ctor_get(v_t_4584_, 1);
lean_inc_ref(v_tail_4601_);
v_shift_4602_ = lean_ctor_get_usize(v_t_4584_, 4);
v_tailOff_4603_ = lean_ctor_get(v_t_4584_, 3);
lean_inc(v_tailOff_4603_);
lean_dec_ref(v_t_4584_);
v___x_4604_ = lean_nat_dec_le(v_tailOff_4603_, v_start_4585_);
if (v___x_4604_ == 0)
{
size_t v___x_4605_; lean_object* v___x_4606_; 
lean_dec(v_tailOff_4603_);
v___x_4605_ = lean_usize_of_nat(v_start_4585_);
lean_inc_ref(v_a_4583_);
lean_inc_ref(v___x_4582_);
v___x_4606_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___at___00Lean_PersistentArray_forM___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0_spec__4_spec__8(v___x_4582_, v_a_4583_, v_root_4600_, v___x_4605_, v_shift_4602_, v___y_4586_, v___y_4587_, v___y_4588_, v___y_4589_, v___y_4590_, v___y_4591_, v___y_4592_, v___y_4593_, v___y_4594_, v___y_4595_, v___y_4596_);
if (lean_obj_tag(v___x_4606_) == 0)
{
lean_object* v___x_4608_; uint8_t v_isShared_4609_; uint8_t v_isSharedCheck_4619_; 
v_isSharedCheck_4619_ = !lean_is_exclusive(v___x_4606_);
if (v_isSharedCheck_4619_ == 0)
{
lean_object* v_unused_4620_; 
v_unused_4620_ = lean_ctor_get(v___x_4606_, 0);
lean_dec(v_unused_4620_);
v___x_4608_ = v___x_4606_;
v_isShared_4609_ = v_isSharedCheck_4619_;
goto v_resetjp_4607_;
}
else
{
lean_dec(v___x_4606_);
v___x_4608_ = lean_box(0);
v_isShared_4609_ = v_isSharedCheck_4619_;
goto v_resetjp_4607_;
}
v_resetjp_4607_:
{
lean_object* v___x_4610_; lean_object* v___x_4611_; uint8_t v___x_4612_; 
v___x_4610_ = lean_array_get_size(v_tail_4601_);
v___x_4611_ = lean_box(0);
v___x_4612_ = lean_nat_dec_lt(v___x_4598_, v___x_4610_);
if (v___x_4612_ == 0)
{
lean_object* v___x_4614_; 
lean_dec_ref(v_tail_4601_);
lean_dec_ref(v_a_4583_);
lean_dec_ref(v___x_4582_);
if (v_isShared_4609_ == 0)
{
lean_ctor_set(v___x_4608_, 0, v___x_4611_);
v___x_4614_ = v___x_4608_;
goto v_reusejp_4613_;
}
else
{
lean_object* v_reuseFailAlloc_4615_; 
v_reuseFailAlloc_4615_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4615_, 0, v___x_4611_);
v___x_4614_ = v_reuseFailAlloc_4615_;
goto v_reusejp_4613_;
}
v_reusejp_4613_:
{
return v___x_4614_;
}
}
else
{
size_t v___x_4616_; size_t v___x_4617_; lean_object* v___x_4618_; 
lean_del_object(v___x_4608_);
v___x_4616_ = ((size_t)0ULL);
v___x_4617_ = lean_usize_of_nat(v___x_4610_);
v___x_4618_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0_spec__4_spec__9___redArg(v___x_4582_, v_a_4583_, v_tail_4601_, v___x_4616_, v___x_4617_, v___x_4611_, v___y_4587_, v___y_4591_, v___y_4592_, v___y_4593_, v___y_4594_, v___y_4595_, v___y_4596_);
lean_dec_ref(v_tail_4601_);
return v___x_4618_;
}
}
}
else
{
lean_dec_ref(v_tail_4601_);
lean_dec_ref(v_a_4583_);
lean_dec_ref(v___x_4582_);
return v___x_4606_;
}
}
else
{
lean_object* v___x_4621_; lean_object* v___x_4622_; lean_object* v___x_4623_; uint8_t v___x_4624_; 
lean_dec_ref(v_root_4600_);
v___x_4621_ = lean_nat_sub(v_start_4585_, v_tailOff_4603_);
lean_dec(v_tailOff_4603_);
v___x_4622_ = lean_array_get_size(v_tail_4601_);
v___x_4623_ = lean_box(0);
v___x_4624_ = lean_nat_dec_lt(v___x_4621_, v___x_4622_);
if (v___x_4624_ == 0)
{
lean_object* v___x_4625_; 
lean_dec(v___x_4621_);
lean_dec_ref(v_tail_4601_);
lean_dec_ref(v_a_4583_);
lean_dec_ref(v___x_4582_);
v___x_4625_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4625_, 0, v___x_4623_);
return v___x_4625_;
}
else
{
size_t v___x_4626_; size_t v___x_4627_; lean_object* v___x_4628_; 
v___x_4626_ = lean_usize_of_nat(v___x_4621_);
lean_dec(v___x_4621_);
v___x_4627_ = lean_usize_of_nat(v___x_4622_);
v___x_4628_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0_spec__4_spec__9___redArg(v___x_4582_, v_a_4583_, v_tail_4601_, v___x_4626_, v___x_4627_, v___x_4623_, v___y_4587_, v___y_4591_, v___y_4592_, v___y_4593_, v___y_4594_, v___y_4595_, v___y_4596_);
lean_dec_ref(v_tail_4601_);
return v___x_4628_;
}
}
}
else
{
lean_object* v___x_4629_; 
v___x_4629_ = l_Lean_PersistentArray_forMFrom0___at___00Lean_PersistentArray_forM___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0_spec__4_spec__10(v___x_4582_, v_a_4583_, v_t_4584_, v___y_4586_, v___y_4587_, v___y_4588_, v___y_4589_, v___y_4590_, v___y_4591_, v___y_4592_, v___y_4593_, v___y_4594_, v___y_4595_, v___y_4596_);
return v___x_4629_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0_spec__4___boxed(lean_object* v___x_4630_, lean_object* v_a_4631_, lean_object* v_t_4632_, lean_object* v_start_4633_, lean_object* v___y_4634_, lean_object* v___y_4635_, lean_object* v___y_4636_, lean_object* v___y_4637_, lean_object* v___y_4638_, lean_object* v___y_4639_, lean_object* v___y_4640_, lean_object* v___y_4641_, lean_object* v___y_4642_, lean_object* v___y_4643_, lean_object* v___y_4644_, lean_object* v___y_4645_){
_start:
{
lean_object* v_res_4646_; 
v_res_4646_ = l_Lean_PersistentArray_forM___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0_spec__4(v___x_4630_, v_a_4631_, v_t_4632_, v_start_4633_, v___y_4634_, v___y_4635_, v___y_4636_, v___y_4637_, v___y_4638_, v___y_4639_, v___y_4640_, v___y_4641_, v___y_4642_, v___y_4643_, v___y_4644_);
lean_dec(v___y_4644_);
lean_dec_ref(v___y_4643_);
lean_dec(v___y_4642_);
lean_dec_ref(v___y_4641_);
lean_dec(v___y_4640_);
lean_dec_ref(v___y_4639_);
lean_dec(v___y_4638_);
lean_dec_ref(v___y_4637_);
lean_dec(v___y_4636_);
lean_dec(v___y_4635_);
lean_dec_ref(v___y_4634_);
lean_dec(v_start_4633_);
return v_res_4646_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0___lam__1(lean_object* v_e_4647_, lean_object* v_s_4648_){
_start:
{
lean_object* v_toRingState_4649_; lean_object* v_denoteEntries_4650_; lean_object* v_nextId_4651_; lean_object* v_steps_4652_; lean_object* v_queue_4653_; lean_object* v_basis_4654_; lean_object* v_diseqs_4655_; uint8_t v_recheck_4656_; lean_object* v_invSet_4657_; lean_object* v_powIdentityVarCount_4658_; lean_object* v_numEq0_x3f_4659_; uint8_t v_numEq0Updated_4660_; lean_object* v___x_4662_; uint8_t v_isShared_4663_; uint8_t v_isSharedCheck_4682_; 
v_toRingState_4649_ = lean_ctor_get(v_s_4648_, 0);
v_denoteEntries_4650_ = lean_ctor_get(v_s_4648_, 1);
v_nextId_4651_ = lean_ctor_get(v_s_4648_, 2);
v_steps_4652_ = lean_ctor_get(v_s_4648_, 3);
v_queue_4653_ = lean_ctor_get(v_s_4648_, 4);
v_basis_4654_ = lean_ctor_get(v_s_4648_, 5);
v_diseqs_4655_ = lean_ctor_get(v_s_4648_, 6);
v_recheck_4656_ = lean_ctor_get_uint8(v_s_4648_, sizeof(void*)*10);
v_invSet_4657_ = lean_ctor_get(v_s_4648_, 7);
v_powIdentityVarCount_4658_ = lean_ctor_get(v_s_4648_, 8);
v_numEq0_x3f_4659_ = lean_ctor_get(v_s_4648_, 9);
v_numEq0Updated_4660_ = lean_ctor_get_uint8(v_s_4648_, sizeof(void*)*10 + 1);
v_isSharedCheck_4682_ = !lean_is_exclusive(v_s_4648_);
if (v_isSharedCheck_4682_ == 0)
{
v___x_4662_ = v_s_4648_;
v_isShared_4663_ = v_isSharedCheck_4682_;
goto v_resetjp_4661_;
}
else
{
lean_inc(v_numEq0_x3f_4659_);
lean_inc(v_powIdentityVarCount_4658_);
lean_inc(v_invSet_4657_);
lean_inc(v_diseqs_4655_);
lean_inc(v_basis_4654_);
lean_inc(v_queue_4653_);
lean_inc(v_steps_4652_);
lean_inc(v_nextId_4651_);
lean_inc(v_denoteEntries_4650_);
lean_inc(v_toRingState_4649_);
lean_dec(v_s_4648_);
v___x_4662_ = lean_box(0);
v_isShared_4663_ = v_isSharedCheck_4682_;
goto v_resetjp_4661_;
}
v_resetjp_4661_:
{
lean_object* v_vars_4664_; lean_object* v_varMap_4665_; lean_object* v_denote_4666_; lean_object* v_natCastSet_4667_; lean_object* v_natCasts_4668_; uint8_t v_hasIntCast_4669_; lean_object* v___x_4671_; uint8_t v_isShared_4672_; uint8_t v_isSharedCheck_4681_; 
v_vars_4664_ = lean_ctor_get(v_toRingState_4649_, 0);
v_varMap_4665_ = lean_ctor_get(v_toRingState_4649_, 1);
v_denote_4666_ = lean_ctor_get(v_toRingState_4649_, 2);
v_natCastSet_4667_ = lean_ctor_get(v_toRingState_4649_, 3);
v_natCasts_4668_ = lean_ctor_get(v_toRingState_4649_, 4);
v_hasIntCast_4669_ = lean_ctor_get_uint8(v_toRingState_4649_, sizeof(void*)*5);
v_isSharedCheck_4681_ = !lean_is_exclusive(v_toRingState_4649_);
if (v_isSharedCheck_4681_ == 0)
{
v___x_4671_ = v_toRingState_4649_;
v_isShared_4672_ = v_isSharedCheck_4681_;
goto v_resetjp_4670_;
}
else
{
lean_inc(v_natCasts_4668_);
lean_inc(v_natCastSet_4667_);
lean_inc(v_denote_4666_);
lean_inc(v_varMap_4665_);
lean_inc(v_vars_4664_);
lean_dec(v_toRingState_4649_);
v___x_4671_ = lean_box(0);
v_isShared_4672_ = v_isSharedCheck_4681_;
goto v_resetjp_4670_;
}
v_resetjp_4670_:
{
lean_object* v___x_4673_; lean_object* v___x_4674_; lean_object* v___x_4676_; 
v___x_4673_ = lean_box(0);
v___x_4674_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0_spec__2___redArg(v_natCastSet_4667_, v_e_4647_, v___x_4673_);
if (v_isShared_4672_ == 0)
{
lean_ctor_set(v___x_4671_, 3, v___x_4674_);
v___x_4676_ = v___x_4671_;
goto v_reusejp_4675_;
}
else
{
lean_object* v_reuseFailAlloc_4680_; 
v_reuseFailAlloc_4680_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_4680_, 0, v_vars_4664_);
lean_ctor_set(v_reuseFailAlloc_4680_, 1, v_varMap_4665_);
lean_ctor_set(v_reuseFailAlloc_4680_, 2, v_denote_4666_);
lean_ctor_set(v_reuseFailAlloc_4680_, 3, v___x_4674_);
lean_ctor_set(v_reuseFailAlloc_4680_, 4, v_natCasts_4668_);
lean_ctor_set_uint8(v_reuseFailAlloc_4680_, sizeof(void*)*5, v_hasIntCast_4669_);
v___x_4676_ = v_reuseFailAlloc_4680_;
goto v_reusejp_4675_;
}
v_reusejp_4675_:
{
lean_object* v___x_4678_; 
if (v_isShared_4663_ == 0)
{
lean_ctor_set(v___x_4662_, 0, v___x_4676_);
v___x_4678_ = v___x_4662_;
goto v_reusejp_4677_;
}
else
{
lean_object* v_reuseFailAlloc_4679_; 
v_reuseFailAlloc_4679_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v_reuseFailAlloc_4679_, 0, v___x_4676_);
lean_ctor_set(v_reuseFailAlloc_4679_, 1, v_denoteEntries_4650_);
lean_ctor_set(v_reuseFailAlloc_4679_, 2, v_nextId_4651_);
lean_ctor_set(v_reuseFailAlloc_4679_, 3, v_steps_4652_);
lean_ctor_set(v_reuseFailAlloc_4679_, 4, v_queue_4653_);
lean_ctor_set(v_reuseFailAlloc_4679_, 5, v_basis_4654_);
lean_ctor_set(v_reuseFailAlloc_4679_, 6, v_diseqs_4655_);
lean_ctor_set(v_reuseFailAlloc_4679_, 7, v_invSet_4657_);
lean_ctor_set(v_reuseFailAlloc_4679_, 8, v_powIdentityVarCount_4658_);
lean_ctor_set(v_reuseFailAlloc_4679_, 9, v_numEq0_x3f_4659_);
lean_ctor_set_uint8(v_reuseFailAlloc_4679_, sizeof(void*)*10, v_recheck_4656_);
lean_ctor_set_uint8(v_reuseFailAlloc_4679_, sizeof(void*)*10 + 1, v_numEq0Updated_4660_);
v___x_4678_ = v_reuseFailAlloc_4679_;
goto v_reusejp_4677_;
}
v_reusejp_4677_:
{
return v___x_4678_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0(lean_object* v_e_4683_, lean_object* v___y_4684_, lean_object* v___y_4685_, lean_object* v___y_4686_, lean_object* v___y_4687_, lean_object* v___y_4688_, lean_object* v___y_4689_, lean_object* v___y_4690_, lean_object* v___y_4691_, lean_object* v___y_4692_, lean_object* v___y_4693_, lean_object* v___y_4694_){
_start:
{
lean_object* v___f_4696_; lean_object* v___f_4697_; lean_object* v___x_4698_; 
lean_inc_ref_n(v_e_4683_, 3);
v___f_4696_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0___lam__1), 2, 1);
lean_closure_set(v___f_4696_, 0, v_e_4683_);
v___f_4697_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0___lam__2), 2, 1);
lean_closure_set(v___f_4697_, 0, v_e_4683_);
v___x_4698_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_4683_, v___y_4692_);
if (lean_obj_tag(v___x_4698_) == 0)
{
lean_object* v_a_4699_; lean_object* v___x_4701_; uint8_t v_isShared_4702_; uint8_t v_isSharedCheck_4892_; 
v_a_4699_ = lean_ctor_get(v___x_4698_, 0);
v_isSharedCheck_4892_ = !lean_is_exclusive(v___x_4698_);
if (v_isSharedCheck_4892_ == 0)
{
v___x_4701_ = v___x_4698_;
v_isShared_4702_ = v_isSharedCheck_4892_;
goto v_resetjp_4700_;
}
else
{
lean_inc(v_a_4699_);
lean_dec(v___x_4698_);
v___x_4701_ = lean_box(0);
v_isShared_4702_ = v_isSharedCheck_4892_;
goto v_resetjp_4700_;
}
v_resetjp_4700_:
{
lean_object* v___x_4708_; uint8_t v___x_4709_; 
v___x_4708_ = l_Lean_Expr_cleanupAnnotations(v_a_4699_);
lean_dec(v_a_4699_);
v___x_4709_ = l_Lean_Expr_isApp(v___x_4708_);
if (v___x_4709_ == 0)
{
lean_dec_ref(v___x_4708_);
lean_dec_ref(v___f_4697_);
lean_dec_ref(v___f_4696_);
lean_dec_ref(v_e_4683_);
goto v___jp_4703_;
}
else
{
lean_object* v___x_4710_; uint8_t v___x_4711_; 
v___x_4710_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4708_);
v___x_4711_ = l_Lean_Expr_isApp(v___x_4710_);
if (v___x_4711_ == 0)
{
lean_dec_ref(v___x_4710_);
lean_dec_ref(v___x_4708_);
lean_dec_ref(v___f_4697_);
lean_dec_ref(v___f_4696_);
lean_dec_ref(v_e_4683_);
goto v___jp_4703_;
}
else
{
lean_object* v___x_4712_; uint8_t v___x_4713_; 
v___x_4712_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4710_);
v___x_4713_ = l_Lean_Expr_isApp(v___x_4712_);
if (v___x_4713_ == 0)
{
lean_dec_ref(v___x_4712_);
lean_dec_ref(v___x_4710_);
lean_dec_ref(v___x_4708_);
lean_dec_ref(v___f_4697_);
lean_dec_ref(v___f_4696_);
lean_dec_ref(v_e_4683_);
goto v___jp_4703_;
}
else
{
lean_object* v_arg_4714_; lean_object* v_arg_4715_; lean_object* v___x_4716_; lean_object* v___x_4717_; uint8_t v___x_4718_; 
v_arg_4714_ = lean_ctor_get(v___x_4708_, 1);
lean_inc_ref(v_arg_4714_);
lean_dec_ref(v___x_4708_);
v_arg_4715_ = lean_ctor_get(v___x_4710_, 1);
lean_inc_ref(v_arg_4715_);
lean_dec_ref(v___x_4710_);
v___x_4716_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4712_);
lean_dec_ref(v___x_4712_);
v___x_4717_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__2));
v___x_4718_ = l_Lean_Expr_isConstOf(v___x_4716_, v___x_4717_);
if (v___x_4718_ == 0)
{
lean_object* v___x_4719_; uint8_t v___x_4720_; 
v___x_4719_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__5));
v___x_4720_ = l_Lean_Expr_isConstOf(v___x_4716_, v___x_4719_);
lean_dec_ref(v___x_4716_);
if (v___x_4720_ == 0)
{
lean_dec_ref(v_arg_4715_);
lean_dec_ref(v_arg_4714_);
lean_dec_ref(v___f_4697_);
lean_dec_ref(v___f_4696_);
lean_dec_ref(v_e_4683_);
goto v___jp_4703_;
}
else
{
uint8_t v___x_4721_; 
lean_del_object(v___x_4701_);
v___x_4721_ = l_Lean_Meta_Sym_isNatValue(v_arg_4714_);
lean_dec_ref(v_arg_4714_);
if (v___x_4721_ == 0)
{
lean_object* v___x_4722_; 
v___x_4722_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRingState___redArg(v___y_4684_, v___y_4685_, v___y_4693_);
if (lean_obj_tag(v___x_4722_) == 0)
{
lean_object* v_a_4723_; lean_object* v___x_4724_; lean_object* v_a_4725_; lean_object* v___x_4727_; uint8_t v_isShared_4728_; uint8_t v_isSharedCheck_4794_; 
v_a_4723_ = lean_ctor_get(v___x_4722_, 0);
lean_inc(v_a_4723_);
lean_dec_ref_known(v___x_4722_, 1);
v___x_4724_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0___lam__0(v_a_4723_, v___y_4684_, v___y_4685_, v___y_4686_, v___y_4687_, v___y_4688_, v___y_4689_, v___y_4690_, v___y_4691_, v___y_4692_, v___y_4693_, v___y_4694_);
lean_dec(v_a_4723_);
v_a_4725_ = lean_ctor_get(v___x_4724_, 0);
v_isSharedCheck_4794_ = !lean_is_exclusive(v___x_4724_);
if (v_isSharedCheck_4794_ == 0)
{
v___x_4727_ = v___x_4724_;
v_isShared_4728_ = v_isSharedCheck_4794_;
goto v_resetjp_4726_;
}
else
{
lean_inc(v_a_4725_);
lean_dec(v___x_4724_);
v___x_4727_ = lean_box(0);
v_isShared_4728_ = v_isSharedCheck_4794_;
goto v_resetjp_4726_;
}
v_resetjp_4726_:
{
lean_object* v_natCastSet_4729_; uint8_t v___x_4730_; 
v_natCastSet_4729_ = lean_ctor_get(v_a_4725_, 3);
lean_inc_ref(v_natCastSet_4729_);
lean_dec(v_a_4725_);
v___x_4730_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0_spec__0___redArg(v_natCastSet_4729_, v_e_4683_);
lean_dec_ref(v_natCastSet_4729_);
if (v___x_4730_ == 0)
{
lean_object* v___x_4731_; 
lean_del_object(v___x_4727_);
v___x_4731_ = l_Lean_Meta_Sym_Arith_getNatCastFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0_spec__1(v___y_4684_, v___y_4685_, v___y_4686_, v___y_4687_, v___y_4688_, v___y_4689_, v___y_4690_, v___y_4691_, v___y_4692_, v___y_4693_, v___y_4694_);
if (lean_obj_tag(v___x_4731_) == 0)
{
lean_object* v_a_4732_; lean_object* v___x_4734_; uint8_t v_isShared_4735_; uint8_t v_isSharedCheck_4781_; 
v_a_4732_ = lean_ctor_get(v___x_4731_, 0);
v_isSharedCheck_4781_ = !lean_is_exclusive(v___x_4731_);
if (v_isSharedCheck_4781_ == 0)
{
v___x_4734_ = v___x_4731_;
v_isShared_4735_ = v_isSharedCheck_4781_;
goto v_resetjp_4733_;
}
else
{
lean_inc(v_a_4732_);
lean_dec(v___x_4731_);
v___x_4734_ = lean_box(0);
v_isShared_4735_ = v_isSharedCheck_4781_;
goto v_resetjp_4733_;
}
v_resetjp_4733_:
{
lean_object* v___x_4736_; size_t v___x_4737_; size_t v___x_4738_; uint8_t v___x_4739_; 
v___x_4736_ = l_Lean_Expr_appArg_x21(v_a_4732_);
lean_dec(v_a_4732_);
v___x_4737_ = lean_ptr_addr(v___x_4736_);
lean_dec_ref(v___x_4736_);
v___x_4738_ = lean_ptr_addr(v_arg_4715_);
lean_dec_ref(v_arg_4715_);
v___x_4739_ = lean_usize_dec_eq(v___x_4737_, v___x_4738_);
if (v___x_4739_ == 0)
{
lean_object* v___x_4740_; lean_object* v___x_4742_; 
lean_dec_ref(v___f_4697_);
lean_dec_ref(v___f_4696_);
lean_dec_ref(v_e_4683_);
v___x_4740_ = lean_box(0);
if (v_isShared_4735_ == 0)
{
lean_ctor_set(v___x_4734_, 0, v___x_4740_);
v___x_4742_ = v___x_4734_;
goto v_reusejp_4741_;
}
else
{
lean_object* v_reuseFailAlloc_4743_; 
v_reuseFailAlloc_4743_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4743_, 0, v___x_4740_);
v___x_4742_ = v_reuseFailAlloc_4743_;
goto v_reusejp_4741_;
}
v_reusejp_4741_:
{
return v___x_4742_;
}
}
else
{
lean_object* v___x_4744_; 
lean_del_object(v___x_4734_);
v___x_4744_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRingState___redArg(v___f_4696_, v___y_4684_, v___y_4685_);
if (lean_obj_tag(v___x_4744_) == 0)
{
lean_object* v___x_4745_; 
lean_dec_ref_known(v___x_4744_, 1);
v___x_4745_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRingState___redArg(v___y_4684_, v___y_4685_, v___y_4693_);
if (lean_obj_tag(v___x_4745_) == 0)
{
lean_object* v_a_4746_; lean_object* v___x_4747_; lean_object* v_a_4748_; uint8_t v_hasIntCast_4749_; 
v_a_4746_ = lean_ctor_get(v___x_4745_, 0);
lean_inc(v_a_4746_);
lean_dec_ref_known(v___x_4745_, 1);
v___x_4747_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0___lam__0(v_a_4746_, v___y_4684_, v___y_4685_, v___y_4686_, v___y_4687_, v___y_4688_, v___y_4689_, v___y_4690_, v___y_4691_, v___y_4692_, v___y_4693_, v___y_4694_);
lean_dec(v_a_4746_);
v_a_4748_ = lean_ctor_get(v___x_4747_, 0);
lean_inc(v_a_4748_);
lean_dec_ref(v___x_4747_);
v_hasIntCast_4749_ = lean_ctor_get_uint8(v_a_4748_, sizeof(void*)*5);
lean_dec(v_a_4748_);
if (v_hasIntCast_4749_ == 0)
{
lean_object* v___x_4750_; 
lean_dec_ref(v_e_4683_);
v___x_4750_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRingState___redArg(v___f_4697_, v___y_4684_, v___y_4685_);
return v___x_4750_;
}
else
{
lean_object* v___x_4751_; 
lean_dec_ref(v___f_4697_);
v___x_4751_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v___y_4684_, v___y_4685_, v___y_4686_, v___y_4687_, v___y_4688_, v___y_4689_, v___y_4690_, v___y_4691_, v___y_4692_, v___y_4693_, v___y_4694_);
if (lean_obj_tag(v___x_4751_) == 0)
{
lean_object* v_a_4752_; lean_object* v_toRing_4753_; lean_object* v___x_4754_; 
v_a_4752_ = lean_ctor_get(v___x_4751_, 0);
lean_inc(v_a_4752_);
lean_dec_ref_known(v___x_4751_, 1);
v_toRing_4753_ = lean_ctor_get(v_a_4752_, 0);
lean_inc_ref(v_toRing_4753_);
lean_dec(v_a_4752_);
v___x_4754_ = l_Lean_Meta_Sym_Arith_getIntCastFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0_spec__3(v___y_4684_, v___y_4685_, v___y_4686_, v___y_4687_, v___y_4688_, v___y_4689_, v___y_4690_, v___y_4691_, v___y_4692_, v___y_4693_, v___y_4694_);
if (lean_obj_tag(v___x_4754_) == 0)
{
lean_object* v_a_4755_; lean_object* v___x_4756_; 
v_a_4755_ = lean_ctor_get(v___x_4754_, 0);
lean_inc(v_a_4755_);
lean_dec_ref_known(v___x_4754_, 1);
v___x_4756_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_pushNatCastFact___redArg(v_toRing_4753_, v_a_4755_, v_e_4683_, v___y_4685_, v___y_4689_, v___y_4690_, v___y_4691_, v___y_4692_, v___y_4693_, v___y_4694_);
return v___x_4756_;
}
else
{
lean_object* v_a_4757_; lean_object* v___x_4759_; uint8_t v_isShared_4760_; uint8_t v_isSharedCheck_4764_; 
lean_dec_ref(v_toRing_4753_);
lean_dec_ref(v_e_4683_);
v_a_4757_ = lean_ctor_get(v___x_4754_, 0);
v_isSharedCheck_4764_ = !lean_is_exclusive(v___x_4754_);
if (v_isSharedCheck_4764_ == 0)
{
v___x_4759_ = v___x_4754_;
v_isShared_4760_ = v_isSharedCheck_4764_;
goto v_resetjp_4758_;
}
else
{
lean_inc(v_a_4757_);
lean_dec(v___x_4754_);
v___x_4759_ = lean_box(0);
v_isShared_4760_ = v_isSharedCheck_4764_;
goto v_resetjp_4758_;
}
v_resetjp_4758_:
{
lean_object* v___x_4762_; 
if (v_isShared_4760_ == 0)
{
v___x_4762_ = v___x_4759_;
goto v_reusejp_4761_;
}
else
{
lean_object* v_reuseFailAlloc_4763_; 
v_reuseFailAlloc_4763_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4763_, 0, v_a_4757_);
v___x_4762_ = v_reuseFailAlloc_4763_;
goto v_reusejp_4761_;
}
v_reusejp_4761_:
{
return v___x_4762_;
}
}
}
}
else
{
lean_object* v_a_4765_; lean_object* v___x_4767_; uint8_t v_isShared_4768_; uint8_t v_isSharedCheck_4772_; 
lean_dec_ref(v_e_4683_);
v_a_4765_ = lean_ctor_get(v___x_4751_, 0);
v_isSharedCheck_4772_ = !lean_is_exclusive(v___x_4751_);
if (v_isSharedCheck_4772_ == 0)
{
v___x_4767_ = v___x_4751_;
v_isShared_4768_ = v_isSharedCheck_4772_;
goto v_resetjp_4766_;
}
else
{
lean_inc(v_a_4765_);
lean_dec(v___x_4751_);
v___x_4767_ = lean_box(0);
v_isShared_4768_ = v_isSharedCheck_4772_;
goto v_resetjp_4766_;
}
v_resetjp_4766_:
{
lean_object* v___x_4770_; 
if (v_isShared_4768_ == 0)
{
v___x_4770_ = v___x_4767_;
goto v_reusejp_4769_;
}
else
{
lean_object* v_reuseFailAlloc_4771_; 
v_reuseFailAlloc_4771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4771_, 0, v_a_4765_);
v___x_4770_ = v_reuseFailAlloc_4771_;
goto v_reusejp_4769_;
}
v_reusejp_4769_:
{
return v___x_4770_;
}
}
}
}
}
else
{
lean_object* v_a_4773_; lean_object* v___x_4775_; uint8_t v_isShared_4776_; uint8_t v_isSharedCheck_4780_; 
lean_dec_ref(v___f_4697_);
lean_dec_ref(v_e_4683_);
v_a_4773_ = lean_ctor_get(v___x_4745_, 0);
v_isSharedCheck_4780_ = !lean_is_exclusive(v___x_4745_);
if (v_isSharedCheck_4780_ == 0)
{
v___x_4775_ = v___x_4745_;
v_isShared_4776_ = v_isSharedCheck_4780_;
goto v_resetjp_4774_;
}
else
{
lean_inc(v_a_4773_);
lean_dec(v___x_4745_);
v___x_4775_ = lean_box(0);
v_isShared_4776_ = v_isSharedCheck_4780_;
goto v_resetjp_4774_;
}
v_resetjp_4774_:
{
lean_object* v___x_4778_; 
if (v_isShared_4776_ == 0)
{
v___x_4778_ = v___x_4775_;
goto v_reusejp_4777_;
}
else
{
lean_object* v_reuseFailAlloc_4779_; 
v_reuseFailAlloc_4779_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4779_, 0, v_a_4773_);
v___x_4778_ = v_reuseFailAlloc_4779_;
goto v_reusejp_4777_;
}
v_reusejp_4777_:
{
return v___x_4778_;
}
}
}
}
else
{
lean_dec_ref(v___f_4697_);
lean_dec_ref(v_e_4683_);
return v___x_4744_;
}
}
}
}
else
{
lean_object* v_a_4782_; lean_object* v___x_4784_; uint8_t v_isShared_4785_; uint8_t v_isSharedCheck_4789_; 
lean_dec_ref(v_arg_4715_);
lean_dec_ref(v___f_4697_);
lean_dec_ref(v___f_4696_);
lean_dec_ref(v_e_4683_);
v_a_4782_ = lean_ctor_get(v___x_4731_, 0);
v_isSharedCheck_4789_ = !lean_is_exclusive(v___x_4731_);
if (v_isSharedCheck_4789_ == 0)
{
v___x_4784_ = v___x_4731_;
v_isShared_4785_ = v_isSharedCheck_4789_;
goto v_resetjp_4783_;
}
else
{
lean_inc(v_a_4782_);
lean_dec(v___x_4731_);
v___x_4784_ = lean_box(0);
v_isShared_4785_ = v_isSharedCheck_4789_;
goto v_resetjp_4783_;
}
v_resetjp_4783_:
{
lean_object* v___x_4787_; 
if (v_isShared_4785_ == 0)
{
v___x_4787_ = v___x_4784_;
goto v_reusejp_4786_;
}
else
{
lean_object* v_reuseFailAlloc_4788_; 
v_reuseFailAlloc_4788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4788_, 0, v_a_4782_);
v___x_4787_ = v_reuseFailAlloc_4788_;
goto v_reusejp_4786_;
}
v_reusejp_4786_:
{
return v___x_4787_;
}
}
}
}
else
{
lean_object* v___x_4790_; lean_object* v___x_4792_; 
lean_dec_ref(v_arg_4715_);
lean_dec_ref(v___f_4697_);
lean_dec_ref(v___f_4696_);
lean_dec_ref(v_e_4683_);
v___x_4790_ = lean_box(0);
if (v_isShared_4728_ == 0)
{
lean_ctor_set(v___x_4727_, 0, v___x_4790_);
v___x_4792_ = v___x_4727_;
goto v_reusejp_4791_;
}
else
{
lean_object* v_reuseFailAlloc_4793_; 
v_reuseFailAlloc_4793_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4793_, 0, v___x_4790_);
v___x_4792_ = v_reuseFailAlloc_4793_;
goto v_reusejp_4791_;
}
v_reusejp_4791_:
{
return v___x_4792_;
}
}
}
}
else
{
lean_object* v_a_4795_; lean_object* v___x_4797_; uint8_t v_isShared_4798_; uint8_t v_isSharedCheck_4802_; 
lean_dec_ref(v_arg_4715_);
lean_dec_ref(v___f_4697_);
lean_dec_ref(v___f_4696_);
lean_dec_ref(v_e_4683_);
v_a_4795_ = lean_ctor_get(v___x_4722_, 0);
v_isSharedCheck_4802_ = !lean_is_exclusive(v___x_4722_);
if (v_isSharedCheck_4802_ == 0)
{
v___x_4797_ = v___x_4722_;
v_isShared_4798_ = v_isSharedCheck_4802_;
goto v_resetjp_4796_;
}
else
{
lean_inc(v_a_4795_);
lean_dec(v___x_4722_);
v___x_4797_ = lean_box(0);
v_isShared_4798_ = v_isSharedCheck_4802_;
goto v_resetjp_4796_;
}
v_resetjp_4796_:
{
lean_object* v___x_4800_; 
if (v_isShared_4798_ == 0)
{
v___x_4800_ = v___x_4797_;
goto v_reusejp_4799_;
}
else
{
lean_object* v_reuseFailAlloc_4801_; 
v_reuseFailAlloc_4801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4801_, 0, v_a_4795_);
v___x_4800_ = v_reuseFailAlloc_4801_;
goto v_reusejp_4799_;
}
v_reusejp_4799_:
{
return v___x_4800_;
}
}
}
}
else
{
lean_object* v___x_4803_; lean_object* v___x_4804_; 
lean_dec_ref(v_arg_4715_);
lean_dec_ref(v___f_4697_);
lean_dec_ref(v___f_4696_);
lean_dec_ref(v_e_4683_);
v___x_4803_ = lean_box(0);
v___x_4804_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4804_, 0, v___x_4803_);
return v___x_4804_;
}
}
}
else
{
lean_object* v___x_4805_; lean_object* v___f_4806_; lean_object* v___x_4807_; 
lean_dec_ref(v___x_4716_);
lean_del_object(v___x_4701_);
lean_dec_ref(v___f_4697_);
lean_dec_ref(v___f_4696_);
lean_dec_ref(v_e_4683_);
v___x_4805_ = lean_box(v___x_4718_);
v___f_4806_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0___lam__4___boxed), 2, 1);
lean_closure_set(v___f_4806_, 0, v___x_4805_);
v___x_4807_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRingState___redArg(v___y_4684_, v___y_4685_, v___y_4693_);
if (lean_obj_tag(v___x_4807_) == 0)
{
lean_object* v_a_4808_; lean_object* v___x_4809_; lean_object* v_a_4810_; lean_object* v___x_4812_; uint8_t v_isShared_4813_; uint8_t v_isSharedCheck_4883_; 
v_a_4808_ = lean_ctor_get(v___x_4807_, 0);
lean_inc(v_a_4808_);
lean_dec_ref_known(v___x_4807_, 1);
v___x_4809_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0___lam__0(v_a_4808_, v___y_4684_, v___y_4685_, v___y_4686_, v___y_4687_, v___y_4688_, v___y_4689_, v___y_4690_, v___y_4691_, v___y_4692_, v___y_4693_, v___y_4694_);
lean_dec(v_a_4808_);
v_a_4810_ = lean_ctor_get(v___x_4809_, 0);
v_isSharedCheck_4883_ = !lean_is_exclusive(v___x_4809_);
if (v_isSharedCheck_4883_ == 0)
{
v___x_4812_ = v___x_4809_;
v_isShared_4813_ = v_isSharedCheck_4883_;
goto v_resetjp_4811_;
}
else
{
lean_inc(v_a_4810_);
lean_dec(v___x_4809_);
v___x_4812_ = lean_box(0);
v_isShared_4813_ = v_isSharedCheck_4883_;
goto v_resetjp_4811_;
}
v_resetjp_4811_:
{
uint8_t v_hasIntCast_4814_; 
v_hasIntCast_4814_ = lean_ctor_get_uint8(v_a_4810_, sizeof(void*)*5);
lean_dec(v_a_4810_);
if (v_hasIntCast_4814_ == 0)
{
lean_object* v___x_4815_; 
v___x_4815_ = l_Lean_Meta_Sym_getIntValue_x3f(v_arg_4714_);
lean_dec_ref(v_arg_4714_);
if (lean_obj_tag(v___x_4815_) == 0)
{
lean_object* v___x_4816_; 
lean_del_object(v___x_4812_);
v___x_4816_ = l_Lean_Meta_Sym_Arith_getIntCastFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0_spec__3(v___y_4684_, v___y_4685_, v___y_4686_, v___y_4687_, v___y_4688_, v___y_4689_, v___y_4690_, v___y_4691_, v___y_4692_, v___y_4693_, v___y_4694_);
if (lean_obj_tag(v___x_4816_) == 0)
{
lean_object* v_a_4817_; lean_object* v___x_4819_; uint8_t v_isShared_4820_; uint8_t v_isSharedCheck_4866_; 
v_a_4817_ = lean_ctor_get(v___x_4816_, 0);
v_isSharedCheck_4866_ = !lean_is_exclusive(v___x_4816_);
if (v_isSharedCheck_4866_ == 0)
{
v___x_4819_ = v___x_4816_;
v_isShared_4820_ = v_isSharedCheck_4866_;
goto v_resetjp_4818_;
}
else
{
lean_inc(v_a_4817_);
lean_dec(v___x_4816_);
v___x_4819_ = lean_box(0);
v_isShared_4820_ = v_isSharedCheck_4866_;
goto v_resetjp_4818_;
}
v_resetjp_4818_:
{
lean_object* v___x_4821_; size_t v___x_4822_; size_t v___x_4823_; uint8_t v___x_4824_; 
v___x_4821_ = l_Lean_Expr_appArg_x21(v_a_4817_);
lean_dec(v_a_4817_);
v___x_4822_ = lean_ptr_addr(v___x_4821_);
lean_dec_ref(v___x_4821_);
v___x_4823_ = lean_ptr_addr(v_arg_4715_);
lean_dec_ref(v_arg_4715_);
v___x_4824_ = lean_usize_dec_eq(v___x_4822_, v___x_4823_);
if (v___x_4824_ == 0)
{
lean_object* v___x_4825_; lean_object* v___x_4827_; 
lean_dec_ref(v___f_4806_);
v___x_4825_ = lean_box(0);
if (v_isShared_4820_ == 0)
{
lean_ctor_set(v___x_4819_, 0, v___x_4825_);
v___x_4827_ = v___x_4819_;
goto v_reusejp_4826_;
}
else
{
lean_object* v_reuseFailAlloc_4828_; 
v_reuseFailAlloc_4828_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4828_, 0, v___x_4825_);
v___x_4827_ = v_reuseFailAlloc_4828_;
goto v_reusejp_4826_;
}
v_reusejp_4826_:
{
return v___x_4827_;
}
}
else
{
lean_object* v___x_4829_; 
lean_del_object(v___x_4819_);
v___x_4829_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRingState___redArg(v___y_4684_, v___y_4685_, v___y_4693_);
if (lean_obj_tag(v___x_4829_) == 0)
{
lean_object* v_a_4830_; lean_object* v___x_4831_; lean_object* v_a_4832_; lean_object* v_natCasts_4833_; lean_object* v___x_4834_; 
v_a_4830_ = lean_ctor_get(v___x_4829_, 0);
lean_inc(v_a_4830_);
lean_dec_ref_known(v___x_4829_, 1);
v___x_4831_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0___lam__0(v_a_4830_, v___y_4684_, v___y_4685_, v___y_4686_, v___y_4687_, v___y_4688_, v___y_4689_, v___y_4690_, v___y_4691_, v___y_4692_, v___y_4693_, v___y_4694_);
lean_dec(v_a_4830_);
v_a_4832_ = lean_ctor_get(v___x_4831_, 0);
lean_inc(v_a_4832_);
lean_dec_ref(v___x_4831_);
v_natCasts_4833_ = lean_ctor_get(v_a_4832_, 4);
lean_inc_ref(v_natCasts_4833_);
lean_dec(v_a_4832_);
v___x_4834_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRingState___redArg(v___f_4806_, v___y_4684_, v___y_4685_);
if (lean_obj_tag(v___x_4834_) == 0)
{
lean_object* v___x_4835_; 
lean_dec_ref_known(v___x_4834_, 1);
v___x_4835_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v___y_4684_, v___y_4685_, v___y_4686_, v___y_4687_, v___y_4688_, v___y_4689_, v___y_4690_, v___y_4691_, v___y_4692_, v___y_4693_, v___y_4694_);
if (lean_obj_tag(v___x_4835_) == 0)
{
lean_object* v_a_4836_; lean_object* v_toRing_4837_; lean_object* v___x_4838_; 
v_a_4836_ = lean_ctor_get(v___x_4835_, 0);
lean_inc(v_a_4836_);
lean_dec_ref_known(v___x_4835_, 1);
v_toRing_4837_ = lean_ctor_get(v_a_4836_, 0);
lean_inc_ref(v_toRing_4837_);
lean_dec(v_a_4836_);
v___x_4838_ = l_Lean_Meta_Sym_Arith_getIntCastFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0_spec__3(v___y_4684_, v___y_4685_, v___y_4686_, v___y_4687_, v___y_4688_, v___y_4689_, v___y_4690_, v___y_4691_, v___y_4692_, v___y_4693_, v___y_4694_);
if (lean_obj_tag(v___x_4838_) == 0)
{
lean_object* v_a_4839_; lean_object* v___x_4840_; lean_object* v___x_4841_; 
v_a_4839_ = lean_ctor_get(v___x_4838_, 0);
lean_inc(v_a_4839_);
lean_dec_ref_known(v___x_4838_, 1);
v___x_4840_ = lean_unsigned_to_nat(0u);
v___x_4841_ = l_Lean_PersistentArray_forM___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0_spec__4(v_toRing_4837_, v_a_4839_, v_natCasts_4833_, v___x_4840_, v___y_4684_, v___y_4685_, v___y_4686_, v___y_4687_, v___y_4688_, v___y_4689_, v___y_4690_, v___y_4691_, v___y_4692_, v___y_4693_, v___y_4694_);
return v___x_4841_;
}
else
{
lean_object* v_a_4842_; lean_object* v___x_4844_; uint8_t v_isShared_4845_; uint8_t v_isSharedCheck_4849_; 
lean_dec_ref(v_toRing_4837_);
lean_dec_ref(v_natCasts_4833_);
v_a_4842_ = lean_ctor_get(v___x_4838_, 0);
v_isSharedCheck_4849_ = !lean_is_exclusive(v___x_4838_);
if (v_isSharedCheck_4849_ == 0)
{
v___x_4844_ = v___x_4838_;
v_isShared_4845_ = v_isSharedCheck_4849_;
goto v_resetjp_4843_;
}
else
{
lean_inc(v_a_4842_);
lean_dec(v___x_4838_);
v___x_4844_ = lean_box(0);
v_isShared_4845_ = v_isSharedCheck_4849_;
goto v_resetjp_4843_;
}
v_resetjp_4843_:
{
lean_object* v___x_4847_; 
if (v_isShared_4845_ == 0)
{
v___x_4847_ = v___x_4844_;
goto v_reusejp_4846_;
}
else
{
lean_object* v_reuseFailAlloc_4848_; 
v_reuseFailAlloc_4848_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4848_, 0, v_a_4842_);
v___x_4847_ = v_reuseFailAlloc_4848_;
goto v_reusejp_4846_;
}
v_reusejp_4846_:
{
return v___x_4847_;
}
}
}
}
else
{
lean_object* v_a_4850_; lean_object* v___x_4852_; uint8_t v_isShared_4853_; uint8_t v_isSharedCheck_4857_; 
lean_dec_ref(v_natCasts_4833_);
v_a_4850_ = lean_ctor_get(v___x_4835_, 0);
v_isSharedCheck_4857_ = !lean_is_exclusive(v___x_4835_);
if (v_isSharedCheck_4857_ == 0)
{
v___x_4852_ = v___x_4835_;
v_isShared_4853_ = v_isSharedCheck_4857_;
goto v_resetjp_4851_;
}
else
{
lean_inc(v_a_4850_);
lean_dec(v___x_4835_);
v___x_4852_ = lean_box(0);
v_isShared_4853_ = v_isSharedCheck_4857_;
goto v_resetjp_4851_;
}
v_resetjp_4851_:
{
lean_object* v___x_4855_; 
if (v_isShared_4853_ == 0)
{
v___x_4855_ = v___x_4852_;
goto v_reusejp_4854_;
}
else
{
lean_object* v_reuseFailAlloc_4856_; 
v_reuseFailAlloc_4856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4856_, 0, v_a_4850_);
v___x_4855_ = v_reuseFailAlloc_4856_;
goto v_reusejp_4854_;
}
v_reusejp_4854_:
{
return v___x_4855_;
}
}
}
}
else
{
lean_dec_ref(v_natCasts_4833_);
return v___x_4834_;
}
}
else
{
lean_object* v_a_4858_; lean_object* v___x_4860_; uint8_t v_isShared_4861_; uint8_t v_isSharedCheck_4865_; 
lean_dec_ref(v___f_4806_);
v_a_4858_ = lean_ctor_get(v___x_4829_, 0);
v_isSharedCheck_4865_ = !lean_is_exclusive(v___x_4829_);
if (v_isSharedCheck_4865_ == 0)
{
v___x_4860_ = v___x_4829_;
v_isShared_4861_ = v_isSharedCheck_4865_;
goto v_resetjp_4859_;
}
else
{
lean_inc(v_a_4858_);
lean_dec(v___x_4829_);
v___x_4860_ = lean_box(0);
v_isShared_4861_ = v_isSharedCheck_4865_;
goto v_resetjp_4859_;
}
v_resetjp_4859_:
{
lean_object* v___x_4863_; 
if (v_isShared_4861_ == 0)
{
v___x_4863_ = v___x_4860_;
goto v_reusejp_4862_;
}
else
{
lean_object* v_reuseFailAlloc_4864_; 
v_reuseFailAlloc_4864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4864_, 0, v_a_4858_);
v___x_4863_ = v_reuseFailAlloc_4864_;
goto v_reusejp_4862_;
}
v_reusejp_4862_:
{
return v___x_4863_;
}
}
}
}
}
}
else
{
lean_object* v_a_4867_; lean_object* v___x_4869_; uint8_t v_isShared_4870_; uint8_t v_isSharedCheck_4874_; 
lean_dec_ref(v___f_4806_);
lean_dec_ref(v_arg_4715_);
v_a_4867_ = lean_ctor_get(v___x_4816_, 0);
v_isSharedCheck_4874_ = !lean_is_exclusive(v___x_4816_);
if (v_isSharedCheck_4874_ == 0)
{
v___x_4869_ = v___x_4816_;
v_isShared_4870_ = v_isSharedCheck_4874_;
goto v_resetjp_4868_;
}
else
{
lean_inc(v_a_4867_);
lean_dec(v___x_4816_);
v___x_4869_ = lean_box(0);
v_isShared_4870_ = v_isSharedCheck_4874_;
goto v_resetjp_4868_;
}
v_resetjp_4868_:
{
lean_object* v___x_4872_; 
if (v_isShared_4870_ == 0)
{
v___x_4872_ = v___x_4869_;
goto v_reusejp_4871_;
}
else
{
lean_object* v_reuseFailAlloc_4873_; 
v_reuseFailAlloc_4873_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4873_, 0, v_a_4867_);
v___x_4872_ = v_reuseFailAlloc_4873_;
goto v_reusejp_4871_;
}
v_reusejp_4871_:
{
return v___x_4872_;
}
}
}
}
else
{
lean_object* v___x_4875_; lean_object* v___x_4877_; 
lean_dec_ref_known(v___x_4815_, 1);
lean_dec_ref(v___f_4806_);
lean_dec_ref(v_arg_4715_);
v___x_4875_ = lean_box(0);
if (v_isShared_4813_ == 0)
{
lean_ctor_set(v___x_4812_, 0, v___x_4875_);
v___x_4877_ = v___x_4812_;
goto v_reusejp_4876_;
}
else
{
lean_object* v_reuseFailAlloc_4878_; 
v_reuseFailAlloc_4878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4878_, 0, v___x_4875_);
v___x_4877_ = v_reuseFailAlloc_4878_;
goto v_reusejp_4876_;
}
v_reusejp_4876_:
{
return v___x_4877_;
}
}
}
else
{
lean_object* v___x_4879_; lean_object* v___x_4881_; 
lean_dec_ref(v___f_4806_);
lean_dec_ref(v_arg_4715_);
lean_dec_ref(v_arg_4714_);
v___x_4879_ = lean_box(0);
if (v_isShared_4813_ == 0)
{
lean_ctor_set(v___x_4812_, 0, v___x_4879_);
v___x_4881_ = v___x_4812_;
goto v_reusejp_4880_;
}
else
{
lean_object* v_reuseFailAlloc_4882_; 
v_reuseFailAlloc_4882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4882_, 0, v___x_4879_);
v___x_4881_ = v_reuseFailAlloc_4882_;
goto v_reusejp_4880_;
}
v_reusejp_4880_:
{
return v___x_4881_;
}
}
}
}
else
{
lean_object* v_a_4884_; lean_object* v___x_4886_; uint8_t v_isShared_4887_; uint8_t v_isSharedCheck_4891_; 
lean_dec_ref(v___f_4806_);
lean_dec_ref(v_arg_4715_);
lean_dec_ref(v_arg_4714_);
v_a_4884_ = lean_ctor_get(v___x_4807_, 0);
v_isSharedCheck_4891_ = !lean_is_exclusive(v___x_4807_);
if (v_isSharedCheck_4891_ == 0)
{
v___x_4886_ = v___x_4807_;
v_isShared_4887_ = v_isSharedCheck_4891_;
goto v_resetjp_4885_;
}
else
{
lean_inc(v_a_4884_);
lean_dec(v___x_4807_);
v___x_4886_ = lean_box(0);
v_isShared_4887_ = v_isSharedCheck_4891_;
goto v_resetjp_4885_;
}
v_resetjp_4885_:
{
lean_object* v___x_4889_; 
if (v_isShared_4887_ == 0)
{
v___x_4889_ = v___x_4886_;
goto v_reusejp_4888_;
}
else
{
lean_object* v_reuseFailAlloc_4890_; 
v_reuseFailAlloc_4890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4890_, 0, v_a_4884_);
v___x_4889_ = v_reuseFailAlloc_4890_;
goto v_reusejp_4888_;
}
v_reusejp_4888_:
{
return v___x_4889_;
}
}
}
}
}
}
}
v___jp_4703_:
{
lean_object* v___x_4704_; lean_object* v___x_4706_; 
v___x_4704_ = lean_box(0);
if (v_isShared_4702_ == 0)
{
lean_ctor_set(v___x_4701_, 0, v___x_4704_);
v___x_4706_ = v___x_4701_;
goto v_reusejp_4705_;
}
else
{
lean_object* v_reuseFailAlloc_4707_; 
v_reuseFailAlloc_4707_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4707_, 0, v___x_4704_);
v___x_4706_ = v_reuseFailAlloc_4707_;
goto v_reusejp_4705_;
}
v_reusejp_4705_:
{
return v___x_4706_;
}
}
}
}
else
{
lean_object* v_a_4893_; lean_object* v___x_4895_; uint8_t v_isShared_4896_; uint8_t v_isSharedCheck_4900_; 
lean_dec_ref(v___f_4697_);
lean_dec_ref(v___f_4696_);
lean_dec_ref(v_e_4683_);
v_a_4893_ = lean_ctor_get(v___x_4698_, 0);
v_isSharedCheck_4900_ = !lean_is_exclusive(v___x_4698_);
if (v_isSharedCheck_4900_ == 0)
{
v___x_4895_ = v___x_4698_;
v_isShared_4896_ = v_isSharedCheck_4900_;
goto v_resetjp_4894_;
}
else
{
lean_inc(v_a_4893_);
lean_dec(v___x_4698_);
v___x_4895_ = lean_box(0);
v_isShared_4896_ = v_isSharedCheck_4900_;
goto v_resetjp_4894_;
}
v_resetjp_4894_:
{
lean_object* v___x_4898_; 
if (v_isShared_4896_ == 0)
{
v___x_4898_ = v___x_4895_;
goto v_reusejp_4897_;
}
else
{
lean_object* v_reuseFailAlloc_4899_; 
v_reuseFailAlloc_4899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4899_, 0, v_a_4893_);
v___x_4898_ = v_reuseFailAlloc_4899_;
goto v_reusejp_4897_;
}
v_reusejp_4897_:
{
return v___x_4898_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0___boxed(lean_object* v_e_4901_, lean_object* v___y_4902_, lean_object* v___y_4903_, lean_object* v___y_4904_, lean_object* v___y_4905_, lean_object* v___y_4906_, lean_object* v___y_4907_, lean_object* v___y_4908_, lean_object* v___y_4909_, lean_object* v___y_4910_, lean_object* v___y_4911_, lean_object* v___y_4912_, lean_object* v___y_4913_){
_start:
{
lean_object* v_res_4914_; 
v_res_4914_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0(v_e_4901_, v___y_4902_, v___y_4903_, v___y_4904_, v___y_4905_, v___y_4906_, v___y_4907_, v___y_4908_, v___y_4909_, v___y_4910_, v___y_4911_, v___y_4912_);
lean_dec(v___y_4912_);
lean_dec_ref(v___y_4911_);
lean_dec(v___y_4910_);
lean_dec_ref(v___y_4909_);
lean_dec(v___y_4908_);
lean_dec_ref(v___y_4907_);
lean_dec(v___y_4906_);
lean_dec_ref(v___y_4905_);
lean_dec(v___y_4904_);
lean_dec(v___y_4903_);
lean_dec_ref(v___y_4902_);
return v_res_4914_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast(lean_object* v_e_4915_, lean_object* v_a_4916_, lean_object* v_a_4917_, lean_object* v_a_4918_, lean_object* v_a_4919_, lean_object* v_a_4920_, lean_object* v_a_4921_, lean_object* v_a_4922_, lean_object* v_a_4923_, lean_object* v_a_4924_, lean_object* v_a_4925_){
_start:
{
lean_object* v_00_u03b1_4931_; lean_object* v___y_4932_; lean_object* v___y_4933_; lean_object* v___y_4934_; lean_object* v___y_4935_; lean_object* v___y_4936_; lean_object* v___y_4937_; lean_object* v___y_4938_; lean_object* v___y_4939_; lean_object* v___y_4940_; lean_object* v___y_4941_; lean_object* v___x_4979_; 
lean_inc_ref(v_e_4915_);
v___x_4979_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_4915_, v_a_4923_);
if (lean_obj_tag(v___x_4979_) == 0)
{
lean_object* v_a_4980_; lean_object* v___x_4981_; uint8_t v___x_4982_; 
v_a_4980_ = lean_ctor_get(v___x_4979_, 0);
lean_inc(v_a_4980_);
lean_dec_ref_known(v___x_4979_, 1);
v___x_4981_ = l_Lean_Expr_cleanupAnnotations(v_a_4980_);
lean_dec(v_a_4980_);
v___x_4982_ = l_Lean_Expr_isApp(v___x_4981_);
if (v___x_4982_ == 0)
{
lean_dec_ref(v___x_4981_);
lean_dec_ref(v_e_4915_);
goto v___jp_4927_;
}
else
{
lean_object* v___x_4983_; uint8_t v___x_4984_; 
v___x_4983_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4981_);
lean_dec_ref(v___x_4981_);
v___x_4984_ = l_Lean_Expr_isApp(v___x_4983_);
if (v___x_4984_ == 0)
{
lean_dec_ref(v___x_4983_);
lean_dec_ref(v_e_4915_);
goto v___jp_4927_;
}
else
{
lean_object* v___x_4985_; uint8_t v___x_4986_; 
v___x_4985_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4983_);
lean_dec_ref(v___x_4983_);
v___x_4986_ = l_Lean_Expr_isApp(v___x_4985_);
if (v___x_4986_ == 0)
{
lean_dec_ref(v___x_4985_);
lean_dec_ref(v_e_4915_);
goto v___jp_4927_;
}
else
{
lean_object* v_arg_4987_; lean_object* v___x_4988_; lean_object* v___x_4989_; uint8_t v___x_4990_; 
v_arg_4987_ = lean_ctor_get(v___x_4985_, 1);
lean_inc_ref(v_arg_4987_);
v___x_4988_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4985_);
lean_dec_ref(v___x_4985_);
v___x_4989_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__2));
v___x_4990_ = l_Lean_Expr_isConstOf(v___x_4988_, v___x_4989_);
if (v___x_4990_ == 0)
{
lean_object* v___x_4991_; uint8_t v___x_4992_; 
v___x_4991_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__5));
v___x_4992_ = l_Lean_Expr_isConstOf(v___x_4988_, v___x_4991_);
lean_dec_ref(v___x_4988_);
if (v___x_4992_ == 0)
{
lean_dec_ref(v_arg_4987_);
lean_dec_ref(v_e_4915_);
goto v___jp_4927_;
}
else
{
v_00_u03b1_4931_ = v_arg_4987_;
v___y_4932_ = v_a_4916_;
v___y_4933_ = v_a_4917_;
v___y_4934_ = v_a_4918_;
v___y_4935_ = v_a_4919_;
v___y_4936_ = v_a_4920_;
v___y_4937_ = v_a_4921_;
v___y_4938_ = v_a_4922_;
v___y_4939_ = v_a_4923_;
v___y_4940_ = v_a_4924_;
v___y_4941_ = v_a_4925_;
goto v___jp_4930_;
}
}
else
{
lean_dec_ref(v___x_4988_);
v_00_u03b1_4931_ = v_arg_4987_;
v___y_4932_ = v_a_4916_;
v___y_4933_ = v_a_4917_;
v___y_4934_ = v_a_4918_;
v___y_4935_ = v_a_4919_;
v___y_4936_ = v_a_4920_;
v___y_4937_ = v_a_4921_;
v___y_4938_ = v_a_4922_;
v___y_4939_ = v_a_4923_;
v___y_4940_ = v_a_4924_;
v___y_4941_ = v_a_4925_;
goto v___jp_4930_;
}
}
}
}
}
else
{
lean_object* v_a_4993_; lean_object* v___x_4995_; uint8_t v_isShared_4996_; uint8_t v_isSharedCheck_5000_; 
lean_dec_ref(v_e_4915_);
v_a_4993_ = lean_ctor_get(v___x_4979_, 0);
v_isSharedCheck_5000_ = !lean_is_exclusive(v___x_4979_);
if (v_isSharedCheck_5000_ == 0)
{
v___x_4995_ = v___x_4979_;
v_isShared_4996_ = v_isSharedCheck_5000_;
goto v_resetjp_4994_;
}
else
{
lean_inc(v_a_4993_);
lean_dec(v___x_4979_);
v___x_4995_ = lean_box(0);
v_isShared_4996_ = v_isSharedCheck_5000_;
goto v_resetjp_4994_;
}
v_resetjp_4994_:
{
lean_object* v___x_4998_; 
if (v_isShared_4996_ == 0)
{
v___x_4998_ = v___x_4995_;
goto v_reusejp_4997_;
}
else
{
lean_object* v_reuseFailAlloc_4999_; 
v_reuseFailAlloc_4999_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4999_, 0, v_a_4993_);
v___x_4998_ = v_reuseFailAlloc_4999_;
goto v_reusejp_4997_;
}
v_reusejp_4997_:
{
return v___x_4998_;
}
}
}
v___jp_4927_:
{
lean_object* v___x_4928_; lean_object* v___x_4929_; 
v___x_4928_ = lean_box(0);
v___x_4929_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4929_, 0, v___x_4928_);
return v___x_4929_;
}
v___jp_4930_:
{
lean_object* v___x_4942_; uint8_t v___x_4943_; 
v___x_4942_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f___closed__28));
v___x_4943_ = l_Lean_Expr_isConstOf(v_00_u03b1_4931_, v___x_4942_);
if (v___x_4943_ == 0)
{
lean_object* v___x_4944_; 
lean_inc_ref(v_00_u03b1_4931_);
v___x_4944_ = l_Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f___redArg(v_00_u03b1_4931_, v___y_4936_, v___y_4937_, v___y_4938_, v___y_4939_, v___y_4940_, v___y_4941_);
if (lean_obj_tag(v___x_4944_) == 0)
{
lean_object* v_a_4945_; 
v_a_4945_ = lean_ctor_get(v___x_4944_, 0);
lean_inc(v_a_4945_);
lean_dec_ref_known(v___x_4944_, 1);
if (lean_obj_tag(v_a_4945_) == 1)
{
lean_object* v_val_4946_; lean_object* v___x_4947_; lean_object* v___x_4948_; 
lean_dec_ref(v_00_u03b1_4931_);
v_val_4946_ = lean_ctor_get(v_a_4945_, 0);
lean_inc(v_val_4946_);
lean_dec_ref_known(v_a_4945_, 1);
v___x_4947_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4947_, 0, v_val_4946_);
lean_ctor_set_uint8(v___x_4947_, sizeof(void*)*1, v___x_4943_);
v___x_4948_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0(v_e_4915_, v___x_4947_, v___y_4932_, v___y_4933_, v___y_4934_, v___y_4935_, v___y_4936_, v___y_4937_, v___y_4938_, v___y_4939_, v___y_4940_, v___y_4941_);
lean_dec_ref_known(v___x_4947_, 1);
return v___x_4948_;
}
else
{
lean_object* v___x_4949_; 
lean_dec(v_a_4945_);
v___x_4949_ = l_Lean_Meta_Grind_Arith_CommRing_getNonCommRingId_x3f___redArg(v_00_u03b1_4931_, v___y_4936_, v___y_4937_, v___y_4938_, v___y_4939_, v___y_4940_, v___y_4941_);
if (lean_obj_tag(v___x_4949_) == 0)
{
lean_object* v_a_4950_; lean_object* v___x_4952_; uint8_t v_isShared_4953_; uint8_t v_isSharedCheck_4960_; 
v_a_4950_ = lean_ctor_get(v___x_4949_, 0);
v_isSharedCheck_4960_ = !lean_is_exclusive(v___x_4949_);
if (v_isSharedCheck_4960_ == 0)
{
v___x_4952_ = v___x_4949_;
v_isShared_4953_ = v_isSharedCheck_4960_;
goto v_resetjp_4951_;
}
else
{
lean_inc(v_a_4950_);
lean_dec(v___x_4949_);
v___x_4952_ = lean_box(0);
v_isShared_4953_ = v_isSharedCheck_4960_;
goto v_resetjp_4951_;
}
v_resetjp_4951_:
{
if (lean_obj_tag(v_a_4950_) == 1)
{
lean_object* v_val_4954_; lean_object* v___x_4955_; 
lean_del_object(v___x_4952_);
v_val_4954_ = lean_ctor_get(v_a_4950_, 0);
lean_inc(v_val_4954_);
lean_dec_ref_known(v_a_4950_, 1);
v___x_4955_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__1(v_e_4915_, v_val_4954_, v___y_4932_, v___y_4933_, v___y_4934_, v___y_4935_, v___y_4936_, v___y_4937_, v___y_4938_, v___y_4939_, v___y_4940_, v___y_4941_);
lean_dec(v_val_4954_);
return v___x_4955_;
}
else
{
lean_object* v___x_4956_; lean_object* v___x_4958_; 
lean_dec(v_a_4950_);
lean_dec_ref(v_e_4915_);
v___x_4956_ = lean_box(0);
if (v_isShared_4953_ == 0)
{
lean_ctor_set(v___x_4952_, 0, v___x_4956_);
v___x_4958_ = v___x_4952_;
goto v_reusejp_4957_;
}
else
{
lean_object* v_reuseFailAlloc_4959_; 
v_reuseFailAlloc_4959_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4959_, 0, v___x_4956_);
v___x_4958_ = v_reuseFailAlloc_4959_;
goto v_reusejp_4957_;
}
v_reusejp_4957_:
{
return v___x_4958_;
}
}
}
}
else
{
lean_object* v_a_4961_; lean_object* v___x_4963_; uint8_t v_isShared_4964_; uint8_t v_isSharedCheck_4968_; 
lean_dec_ref(v_e_4915_);
v_a_4961_ = lean_ctor_get(v___x_4949_, 0);
v_isSharedCheck_4968_ = !lean_is_exclusive(v___x_4949_);
if (v_isSharedCheck_4968_ == 0)
{
v___x_4963_ = v___x_4949_;
v_isShared_4964_ = v_isSharedCheck_4968_;
goto v_resetjp_4962_;
}
else
{
lean_inc(v_a_4961_);
lean_dec(v___x_4949_);
v___x_4963_ = lean_box(0);
v_isShared_4964_ = v_isSharedCheck_4968_;
goto v_resetjp_4962_;
}
v_resetjp_4962_:
{
lean_object* v___x_4966_; 
if (v_isShared_4964_ == 0)
{
v___x_4966_ = v___x_4963_;
goto v_reusejp_4965_;
}
else
{
lean_object* v_reuseFailAlloc_4967_; 
v_reuseFailAlloc_4967_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4967_, 0, v_a_4961_);
v___x_4966_ = v_reuseFailAlloc_4967_;
goto v_reusejp_4965_;
}
v_reusejp_4965_:
{
return v___x_4966_;
}
}
}
}
}
else
{
lean_object* v_a_4969_; lean_object* v___x_4971_; uint8_t v_isShared_4972_; uint8_t v_isSharedCheck_4976_; 
lean_dec_ref(v_00_u03b1_4931_);
lean_dec_ref(v_e_4915_);
v_a_4969_ = lean_ctor_get(v___x_4944_, 0);
v_isSharedCheck_4976_ = !lean_is_exclusive(v___x_4944_);
if (v_isSharedCheck_4976_ == 0)
{
v___x_4971_ = v___x_4944_;
v_isShared_4972_ = v_isSharedCheck_4976_;
goto v_resetjp_4970_;
}
else
{
lean_inc(v_a_4969_);
lean_dec(v___x_4944_);
v___x_4971_ = lean_box(0);
v_isShared_4972_ = v_isSharedCheck_4976_;
goto v_resetjp_4970_;
}
v_resetjp_4970_:
{
lean_object* v___x_4974_; 
if (v_isShared_4972_ == 0)
{
v___x_4974_ = v___x_4971_;
goto v_reusejp_4973_;
}
else
{
lean_object* v_reuseFailAlloc_4975_; 
v_reuseFailAlloc_4975_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4975_, 0, v_a_4969_);
v___x_4974_ = v_reuseFailAlloc_4975_;
goto v_reusejp_4973_;
}
v_reusejp_4973_:
{
return v___x_4974_;
}
}
}
}
else
{
lean_object* v___x_4977_; lean_object* v___x_4978_; 
lean_dec_ref(v_00_u03b1_4931_);
lean_dec_ref(v_e_4915_);
v___x_4977_ = lean_box(0);
v___x_4978_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4978_, 0, v___x_4977_);
return v___x_4978_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast___boxed(lean_object* v_e_5001_, lean_object* v_a_5002_, lean_object* v_a_5003_, lean_object* v_a_5004_, lean_object* v_a_5005_, lean_object* v_a_5006_, lean_object* v_a_5007_, lean_object* v_a_5008_, lean_object* v_a_5009_, lean_object* v_a_5010_, lean_object* v_a_5011_, lean_object* v_a_5012_){
_start:
{
lean_object* v_res_5013_; 
v_res_5013_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast(v_e_5001_, v_a_5002_, v_a_5003_, v_a_5004_, v_a_5005_, v_a_5006_, v_a_5007_, v_a_5008_, v_a_5009_, v_a_5010_, v_a_5011_);
lean_dec(v_a_5011_);
lean_dec_ref(v_a_5010_);
lean_dec(v_a_5009_);
lean_dec_ref(v_a_5008_);
lean_dec(v_a_5007_);
lean_dec_ref(v_a_5006_);
lean_dec(v_a_5005_);
lean_dec_ref(v_a_5004_);
lean_dec(v_a_5003_);
lean_dec(v_a_5002_);
return v_res_5013_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0_spec__0(lean_object* v_00_u03b2_5014_, lean_object* v_x_5015_, lean_object* v_x_5016_){
_start:
{
uint8_t v___x_5017_; 
v___x_5017_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0_spec__0___redArg(v_x_5015_, v_x_5016_);
return v___x_5017_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0_spec__0___boxed(lean_object* v_00_u03b2_5018_, lean_object* v_x_5019_, lean_object* v_x_5020_){
_start:
{
uint8_t v_res_5021_; lean_object* v_r_5022_; 
v_res_5021_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0_spec__0(v_00_u03b2_5018_, v_x_5019_, v_x_5020_);
lean_dec_ref(v_x_5020_);
lean_dec_ref(v_x_5019_);
v_r_5022_ = lean_box(v_res_5021_);
return v_r_5022_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___at___00Lean_Meta_Sym_Arith_getNatCastFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0_spec__1_spec__3(lean_object* v_u_5023_, lean_object* v_type_5024_, lean_object* v_semiringInst_5025_, lean_object* v___y_5026_, lean_object* v___y_5027_, lean_object* v___y_5028_, lean_object* v___y_5029_, lean_object* v___y_5030_, lean_object* v___y_5031_, lean_object* v___y_5032_, lean_object* v___y_5033_, lean_object* v___y_5034_, lean_object* v___y_5035_, lean_object* v___y_5036_){
_start:
{
lean_object* v___x_5038_; 
v___x_5038_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___at___00Lean_Meta_Sym_Arith_getNatCastFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0_spec__1_spec__3___redArg(v_u_5023_, v_type_5024_, v_semiringInst_5025_, v___y_5031_, v___y_5032_, v___y_5033_, v___y_5034_, v___y_5035_, v___y_5036_);
return v___x_5038_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___at___00Lean_Meta_Sym_Arith_getNatCastFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0_spec__1_spec__3___boxed(lean_object* v_u_5039_, lean_object* v_type_5040_, lean_object* v_semiringInst_5041_, lean_object* v___y_5042_, lean_object* v___y_5043_, lean_object* v___y_5044_, lean_object* v___y_5045_, lean_object* v___y_5046_, lean_object* v___y_5047_, lean_object* v___y_5048_, lean_object* v___y_5049_, lean_object* v___y_5050_, lean_object* v___y_5051_, lean_object* v___y_5052_, lean_object* v___y_5053_){
_start:
{
lean_object* v_res_5054_; 
v_res_5054_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___at___00Lean_Meta_Sym_Arith_getNatCastFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0_spec__1_spec__3(v_u_5039_, v_type_5040_, v_semiringInst_5041_, v___y_5042_, v___y_5043_, v___y_5044_, v___y_5045_, v___y_5046_, v___y_5047_, v___y_5048_, v___y_5049_, v___y_5050_, v___y_5051_, v___y_5052_);
lean_dec(v___y_5052_);
lean_dec_ref(v___y_5051_);
lean_dec(v___y_5050_);
lean_dec_ref(v___y_5049_);
lean_dec(v___y_5048_);
lean_dec_ref(v___y_5047_);
lean_dec(v___y_5046_);
lean_dec_ref(v___y_5045_);
lean_dec(v___y_5044_);
lean_dec(v___y_5043_);
lean_dec_ref(v___y_5042_);
return v_res_5054_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0_spec__2(lean_object* v_00_u03b2_5055_, lean_object* v_x_5056_, lean_object* v_x_5057_, lean_object* v_x_5058_){
_start:
{
lean_object* v___x_5059_; 
v___x_5059_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0_spec__2___redArg(v_x_5056_, v_x_5057_, v_x_5058_);
return v___x_5059_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___at___00Lean_Meta_Sym_Arith_getNatCastFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__1_spec__6_spec__13(lean_object* v_u_5060_, lean_object* v_type_5061_, lean_object* v_semiringInst_5062_, lean_object* v___y_5063_, lean_object* v___y_5064_, lean_object* v___y_5065_, lean_object* v___y_5066_, lean_object* v___y_5067_, lean_object* v___y_5068_, lean_object* v___y_5069_, lean_object* v___y_5070_, lean_object* v___y_5071_, lean_object* v___y_5072_, lean_object* v___y_5073_){
_start:
{
lean_object* v___x_5075_; 
v___x_5075_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___at___00Lean_Meta_Sym_Arith_getNatCastFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__1_spec__6_spec__13___redArg(v_u_5060_, v_type_5061_, v_semiringInst_5062_, v___y_5068_, v___y_5069_, v___y_5070_, v___y_5071_, v___y_5072_, v___y_5073_);
return v___x_5075_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___at___00Lean_Meta_Sym_Arith_getNatCastFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__1_spec__6_spec__13___boxed(lean_object* v_u_5076_, lean_object* v_type_5077_, lean_object* v_semiringInst_5078_, lean_object* v___y_5079_, lean_object* v___y_5080_, lean_object* v___y_5081_, lean_object* v___y_5082_, lean_object* v___y_5083_, lean_object* v___y_5084_, lean_object* v___y_5085_, lean_object* v___y_5086_, lean_object* v___y_5087_, lean_object* v___y_5088_, lean_object* v___y_5089_, lean_object* v___y_5090_){
_start:
{
lean_object* v_res_5091_; 
v_res_5091_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___at___00Lean_Meta_Sym_Arith_getNatCastFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__1_spec__6_spec__13(v_u_5076_, v_type_5077_, v_semiringInst_5078_, v___y_5079_, v___y_5080_, v___y_5081_, v___y_5082_, v___y_5083_, v___y_5084_, v___y_5085_, v___y_5086_, v___y_5087_, v___y_5088_, v___y_5089_);
lean_dec(v___y_5089_);
lean_dec_ref(v___y_5088_);
lean_dec(v___y_5087_);
lean_dec_ref(v___y_5086_);
lean_dec(v___y_5085_);
lean_dec_ref(v___y_5084_);
lean_dec(v___y_5083_);
lean_dec_ref(v___y_5082_);
lean_dec(v___y_5081_);
lean_dec(v___y_5080_);
lean_dec(v___y_5079_);
return v_res_5091_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_5092_, lean_object* v_x_5093_, size_t v_x_5094_, lean_object* v_x_5095_){
_start:
{
uint8_t v___x_5096_; 
v___x_5096_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0_spec__0_spec__1___redArg(v_x_5093_, v_x_5094_, v_x_5095_);
return v___x_5096_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_5097_, lean_object* v_x_5098_, lean_object* v_x_5099_, lean_object* v_x_5100_){
_start:
{
size_t v_x_134351__boxed_5101_; uint8_t v_res_5102_; lean_object* v_r_5103_; 
v_x_134351__boxed_5101_ = lean_unbox_usize(v_x_5099_);
lean_dec(v_x_5099_);
v_res_5102_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0_spec__0_spec__1(v_00_u03b2_5097_, v_x_5098_, v_x_134351__boxed_5101_, v_x_5100_);
lean_dec_ref(v_x_5100_);
lean_dec_ref(v_x_5098_);
v_r_5103_ = lean_box(v_res_5102_);
return v_r_5103_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0_spec__2_spec__5(lean_object* v_00_u03b2_5104_, lean_object* v_x_5105_, size_t v_x_5106_, size_t v_x_5107_, lean_object* v_x_5108_, lean_object* v_x_5109_){
_start:
{
lean_object* v___x_5110_; 
v___x_5110_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0_spec__2_spec__5___redArg(v_x_5105_, v_x_5106_, v_x_5107_, v_x_5108_, v_x_5109_);
return v___x_5110_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0_spec__2_spec__5___boxed(lean_object* v_00_u03b2_5111_, lean_object* v_x_5112_, lean_object* v_x_5113_, lean_object* v_x_5114_, lean_object* v_x_5115_, lean_object* v_x_5116_){
_start:
{
size_t v_x_134362__boxed_5117_; size_t v_x_134363__boxed_5118_; lean_object* v_res_5119_; 
v_x_134362__boxed_5117_ = lean_unbox_usize(v_x_5113_);
lean_dec(v_x_5113_);
v_x_134363__boxed_5118_ = lean_unbox_usize(v_x_5114_);
lean_dec(v_x_5114_);
v_res_5119_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0_spec__2_spec__5(v_00_u03b2_5111_, v_x_5112_, v_x_134362__boxed_5117_, v_x_134363__boxed_5118_, v_x_5115_, v_x_5116_);
return v_res_5119_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0_spec__4_spec__9(lean_object* v___x_5120_, lean_object* v_a_5121_, lean_object* v_as_5122_, size_t v_i_5123_, size_t v_stop_5124_, lean_object* v_b_5125_, lean_object* v___y_5126_, lean_object* v___y_5127_, lean_object* v___y_5128_, lean_object* v___y_5129_, lean_object* v___y_5130_, lean_object* v___y_5131_, lean_object* v___y_5132_, lean_object* v___y_5133_, lean_object* v___y_5134_, lean_object* v___y_5135_, lean_object* v___y_5136_){
_start:
{
lean_object* v___x_5138_; 
v___x_5138_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0_spec__4_spec__9___redArg(v___x_5120_, v_a_5121_, v_as_5122_, v_i_5123_, v_stop_5124_, v_b_5125_, v___y_5127_, v___y_5131_, v___y_5132_, v___y_5133_, v___y_5134_, v___y_5135_, v___y_5136_);
return v___x_5138_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0_spec__4_spec__9___boxed(lean_object** _args){
lean_object* v___x_5139_ = _args[0];
lean_object* v_a_5140_ = _args[1];
lean_object* v_as_5141_ = _args[2];
lean_object* v_i_5142_ = _args[3];
lean_object* v_stop_5143_ = _args[4];
lean_object* v_b_5144_ = _args[5];
lean_object* v___y_5145_ = _args[6];
lean_object* v___y_5146_ = _args[7];
lean_object* v___y_5147_ = _args[8];
lean_object* v___y_5148_ = _args[9];
lean_object* v___y_5149_ = _args[10];
lean_object* v___y_5150_ = _args[11];
lean_object* v___y_5151_ = _args[12];
lean_object* v___y_5152_ = _args[13];
lean_object* v___y_5153_ = _args[14];
lean_object* v___y_5154_ = _args[15];
lean_object* v___y_5155_ = _args[16];
lean_object* v___y_5156_ = _args[17];
_start:
{
size_t v_i_boxed_5157_; size_t v_stop_boxed_5158_; lean_object* v_res_5159_; 
v_i_boxed_5157_ = lean_unbox_usize(v_i_5142_);
lean_dec(v_i_5142_);
v_stop_boxed_5158_ = lean_unbox_usize(v_stop_5143_);
lean_dec(v_stop_5143_);
v_res_5159_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0_spec__4_spec__9(v___x_5139_, v_a_5140_, v_as_5141_, v_i_boxed_5157_, v_stop_boxed_5158_, v_b_5144_, v___y_5145_, v___y_5146_, v___y_5147_, v___y_5148_, v___y_5149_, v___y_5150_, v___y_5151_, v___y_5152_, v___y_5153_, v___y_5154_, v___y_5155_);
lean_dec(v___y_5155_);
lean_dec_ref(v___y_5154_);
lean_dec(v___y_5153_);
lean_dec_ref(v___y_5152_);
lean_dec(v___y_5151_);
lean_dec_ref(v___y_5150_);
lean_dec(v___y_5149_);
lean_dec_ref(v___y_5148_);
lean_dec(v___y_5147_);
lean_dec(v___y_5146_);
lean_dec_ref(v___y_5145_);
lean_dec_ref(v_as_5141_);
return v_res_5159_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__1_spec__8_spec__17(lean_object* v_a_5160_, lean_object* v_a_5161_, lean_object* v_as_5162_, size_t v_i_5163_, size_t v_stop_5164_, lean_object* v_b_5165_, lean_object* v___y_5166_, lean_object* v___y_5167_, lean_object* v___y_5168_, lean_object* v___y_5169_, lean_object* v___y_5170_, lean_object* v___y_5171_, lean_object* v___y_5172_, lean_object* v___y_5173_, lean_object* v___y_5174_, lean_object* v___y_5175_, lean_object* v___y_5176_){
_start:
{
lean_object* v___x_5178_; 
v___x_5178_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__1_spec__8_spec__17___redArg(v_a_5160_, v_a_5161_, v_as_5162_, v_i_5163_, v_stop_5164_, v_b_5165_, v___y_5167_, v___y_5171_, v___y_5172_, v___y_5173_, v___y_5174_, v___y_5175_, v___y_5176_);
return v___x_5178_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__1_spec__8_spec__17___boxed(lean_object** _args){
lean_object* v_a_5179_ = _args[0];
lean_object* v_a_5180_ = _args[1];
lean_object* v_as_5181_ = _args[2];
lean_object* v_i_5182_ = _args[3];
lean_object* v_stop_5183_ = _args[4];
lean_object* v_b_5184_ = _args[5];
lean_object* v___y_5185_ = _args[6];
lean_object* v___y_5186_ = _args[7];
lean_object* v___y_5187_ = _args[8];
lean_object* v___y_5188_ = _args[9];
lean_object* v___y_5189_ = _args[10];
lean_object* v___y_5190_ = _args[11];
lean_object* v___y_5191_ = _args[12];
lean_object* v___y_5192_ = _args[13];
lean_object* v___y_5193_ = _args[14];
lean_object* v___y_5194_ = _args[15];
lean_object* v___y_5195_ = _args[16];
lean_object* v___y_5196_ = _args[17];
_start:
{
size_t v_i_boxed_5197_; size_t v_stop_boxed_5198_; lean_object* v_res_5199_; 
v_i_boxed_5197_ = lean_unbox_usize(v_i_5182_);
lean_dec(v_i_5182_);
v_stop_boxed_5198_ = lean_unbox_usize(v_stop_5183_);
lean_dec(v_stop_5183_);
v_res_5199_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_forM___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__1_spec__8_spec__17(v_a_5179_, v_a_5180_, v_as_5181_, v_i_boxed_5197_, v_stop_boxed_5198_, v_b_5184_, v___y_5185_, v___y_5186_, v___y_5187_, v___y_5188_, v___y_5189_, v___y_5190_, v___y_5191_, v___y_5192_, v___y_5193_, v___y_5194_, v___y_5195_);
lean_dec(v___y_5195_);
lean_dec_ref(v___y_5194_);
lean_dec(v___y_5193_);
lean_dec_ref(v___y_5192_);
lean_dec(v___y_5191_);
lean_dec_ref(v___y_5190_);
lean_dec(v___y_5189_);
lean_dec_ref(v___y_5188_);
lean_dec(v___y_5187_);
lean_dec(v___y_5186_);
lean_dec(v___y_5185_);
lean_dec_ref(v_as_5181_);
return v_res_5199_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0_spec__0_spec__1_spec__5(lean_object* v_00_u03b2_5200_, lean_object* v_keys_5201_, lean_object* v_vals_5202_, lean_object* v_heq_5203_, lean_object* v_i_5204_, lean_object* v_k_5205_){
_start:
{
uint8_t v___x_5206_; 
v___x_5206_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0_spec__0_spec__1_spec__5___redArg(v_keys_5201_, v_i_5204_, v_k_5205_);
return v___x_5206_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0_spec__0_spec__1_spec__5___boxed(lean_object* v_00_u03b2_5207_, lean_object* v_keys_5208_, lean_object* v_vals_5209_, lean_object* v_heq_5210_, lean_object* v_i_5211_, lean_object* v_k_5212_){
_start:
{
uint8_t v_res_5213_; lean_object* v_r_5214_; 
v_res_5213_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0_spec__0_spec__1_spec__5(v_00_u03b2_5207_, v_keys_5208_, v_vals_5209_, v_heq_5210_, v_i_5211_, v_k_5212_);
lean_dec_ref(v_k_5212_);
lean_dec_ref(v_vals_5209_);
lean_dec_ref(v_keys_5208_);
v_r_5214_ = lean_box(v_res_5213_);
return v_r_5214_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0_spec__2_spec__5_spec__10(lean_object* v_00_u03b2_5215_, lean_object* v_n_5216_, lean_object* v_k_5217_, lean_object* v_v_5218_){
_start:
{
lean_object* v___x_5219_; 
v___x_5219_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0_spec__2_spec__5_spec__10___redArg(v_n_5216_, v_k_5217_, v_v_5218_);
return v___x_5219_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0_spec__2_spec__5_spec__11(lean_object* v_00_u03b2_5220_, size_t v_depth_5221_, lean_object* v_keys_5222_, lean_object* v_vals_5223_, lean_object* v_heq_5224_, lean_object* v_i_5225_, lean_object* v_entries_5226_){
_start:
{
lean_object* v___x_5227_; 
v___x_5227_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0_spec__2_spec__5_spec__11___redArg(v_depth_5221_, v_keys_5222_, v_vals_5223_, v_i_5225_, v_entries_5226_);
return v___x_5227_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0_spec__2_spec__5_spec__11___boxed(lean_object* v_00_u03b2_5228_, lean_object* v_depth_5229_, lean_object* v_keys_5230_, lean_object* v_vals_5231_, lean_object* v_heq_5232_, lean_object* v_i_5233_, lean_object* v_entries_5234_){
_start:
{
size_t v_depth_boxed_5235_; lean_object* v_res_5236_; 
v_depth_boxed_5235_ = lean_unbox_usize(v_depth_5229_);
lean_dec(v_depth_5229_);
v_res_5236_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0_spec__2_spec__5_spec__11(v_00_u03b2_5228_, v_depth_boxed_5235_, v_keys_5230_, v_vals_5231_, v_heq_5232_, v_i_5233_, v_entries_5234_);
lean_dec_ref(v_vals_5231_);
lean_dec_ref(v_keys_5230_);
return v_res_5236_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0_spec__2_spec__5_spec__10_spec__15(lean_object* v_00_u03b2_5237_, lean_object* v_x_5238_, lean_object* v_x_5239_, lean_object* v_x_5240_, lean_object* v_x_5241_){
_start:
{
lean_object* v___x_5242_; 
v___x_5242_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0_spec__2_spec__5_spec__10_spec__15___redArg(v_x_5238_, v_x_5239_, v_x_5240_, v_x_5241_);
return v___x_5242_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeInv(lean_object* v_e_5243_, lean_object* v_a_5244_, lean_object* v_a_5245_, lean_object* v_a_5246_, lean_object* v_a_5247_, lean_object* v_a_5248_, lean_object* v_a_5249_, lean_object* v_a_5250_, lean_object* v_a_5251_, lean_object* v_a_5252_, lean_object* v_a_5253_){
_start:
{
lean_object* v___x_5259_; 
lean_inc_ref(v_e_5243_);
v___x_5259_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_5243_, v_a_5251_);
if (lean_obj_tag(v___x_5259_) == 0)
{
lean_object* v_a_5260_; lean_object* v___x_5261_; uint8_t v___x_5262_; 
v_a_5260_ = lean_ctor_get(v___x_5259_, 0);
lean_inc(v_a_5260_);
lean_dec_ref_known(v___x_5259_, 1);
v___x_5261_ = l_Lean_Expr_cleanupAnnotations(v_a_5260_);
lean_dec(v_a_5260_);
v___x_5262_ = l_Lean_Expr_isApp(v___x_5261_);
if (v___x_5262_ == 0)
{
lean_dec_ref(v___x_5261_);
lean_dec_ref(v_e_5243_);
goto v___jp_5255_;
}
else
{
lean_object* v___x_5263_; uint8_t v___x_5264_; 
v___x_5263_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5261_);
v___x_5264_ = l_Lean_Expr_isApp(v___x_5263_);
if (v___x_5264_ == 0)
{
lean_dec_ref(v___x_5263_);
lean_dec_ref(v___x_5261_);
lean_dec_ref(v_e_5243_);
goto v___jp_5255_;
}
else
{
lean_object* v___x_5265_; uint8_t v___x_5266_; 
v___x_5265_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5263_);
v___x_5266_ = l_Lean_Expr_isApp(v___x_5265_);
if (v___x_5266_ == 0)
{
lean_dec_ref(v___x_5265_);
lean_dec_ref(v___x_5263_);
lean_dec_ref(v___x_5261_);
lean_dec_ref(v_e_5243_);
goto v___jp_5255_;
}
else
{
lean_object* v___x_5267_; lean_object* v___x_5268_; uint8_t v___x_5269_; 
v___x_5267_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5265_);
v___x_5268_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getInvFn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isInvInst_spec__0___closed__6));
v___x_5269_ = l_Lean_Expr_isConstOf(v___x_5267_, v___x_5268_);
lean_dec_ref(v___x_5267_);
if (v___x_5269_ == 0)
{
lean_dec_ref(v___x_5265_);
lean_dec_ref(v___x_5263_);
lean_dec_ref(v___x_5261_);
lean_dec_ref(v_e_5243_);
goto v___jp_5255_;
}
else
{
lean_object* v_arg_5270_; lean_object* v_arg_5271_; lean_object* v_arg_5272_; lean_object* v___x_5273_; 
v_arg_5270_ = lean_ctor_get(v___x_5261_, 1);
lean_inc_ref(v_arg_5270_);
lean_dec_ref(v___x_5261_);
v_arg_5271_ = lean_ctor_get(v___x_5263_, 1);
lean_inc_ref(v_arg_5271_);
lean_dec_ref(v___x_5263_);
v_arg_5272_ = lean_ctor_get(v___x_5265_, 1);
lean_inc_ref(v_arg_5272_);
lean_dec_ref(v___x_5265_);
v___x_5273_ = l_Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f___redArg(v_arg_5272_, v_a_5248_, v_a_5249_, v_a_5250_, v_a_5251_, v_a_5252_, v_a_5253_);
if (lean_obj_tag(v___x_5273_) == 0)
{
lean_object* v_a_5274_; lean_object* v___x_5276_; uint8_t v_isShared_5277_; uint8_t v_isSharedCheck_5303_; 
v_a_5274_ = lean_ctor_get(v___x_5273_, 0);
v_isSharedCheck_5303_ = !lean_is_exclusive(v___x_5273_);
if (v_isSharedCheck_5303_ == 0)
{
v___x_5276_ = v___x_5273_;
v_isShared_5277_ = v_isSharedCheck_5303_;
goto v_resetjp_5275_;
}
else
{
lean_inc(v_a_5274_);
lean_dec(v___x_5273_);
v___x_5276_ = lean_box(0);
v_isShared_5277_ = v_isSharedCheck_5303_;
goto v_resetjp_5275_;
}
v_resetjp_5275_:
{
if (lean_obj_tag(v_a_5274_) == 1)
{
lean_object* v_val_5278_; uint8_t v___x_5279_; lean_object* v___x_5280_; lean_object* v___x_5281_; 
lean_del_object(v___x_5276_);
v_val_5278_ = lean_ctor_get(v_a_5274_, 0);
lean_inc(v_val_5278_);
lean_dec_ref_known(v_a_5274_, 1);
v___x_5279_ = 0;
v___x_5280_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5280_, 0, v_val_5278_);
lean_ctor_set_uint8(v___x_5280_, sizeof(void*)*1, v___x_5279_);
v___x_5281_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processInv(v_e_5243_, v_arg_5271_, v_arg_5270_, v___x_5280_, v_a_5244_, v_a_5245_, v_a_5246_, v_a_5247_, v_a_5248_, v_a_5249_, v_a_5250_, v_a_5251_, v_a_5252_, v_a_5253_);
lean_dec_ref_known(v___x_5280_, 1);
lean_dec_ref(v_arg_5271_);
if (lean_obj_tag(v___x_5281_) == 0)
{
lean_object* v___x_5283_; uint8_t v_isShared_5284_; uint8_t v_isSharedCheck_5289_; 
v_isSharedCheck_5289_ = !lean_is_exclusive(v___x_5281_);
if (v_isSharedCheck_5289_ == 0)
{
lean_object* v_unused_5290_; 
v_unused_5290_ = lean_ctor_get(v___x_5281_, 0);
lean_dec(v_unused_5290_);
v___x_5283_ = v___x_5281_;
v_isShared_5284_ = v_isSharedCheck_5289_;
goto v_resetjp_5282_;
}
else
{
lean_dec(v___x_5281_);
v___x_5283_ = lean_box(0);
v_isShared_5284_ = v_isSharedCheck_5289_;
goto v_resetjp_5282_;
}
v_resetjp_5282_:
{
lean_object* v___x_5285_; lean_object* v___x_5287_; 
v___x_5285_ = lean_box(v___x_5269_);
if (v_isShared_5284_ == 0)
{
lean_ctor_set(v___x_5283_, 0, v___x_5285_);
v___x_5287_ = v___x_5283_;
goto v_reusejp_5286_;
}
else
{
lean_object* v_reuseFailAlloc_5288_; 
v_reuseFailAlloc_5288_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5288_, 0, v___x_5285_);
v___x_5287_ = v_reuseFailAlloc_5288_;
goto v_reusejp_5286_;
}
v_reusejp_5286_:
{
return v___x_5287_;
}
}
}
else
{
lean_object* v_a_5291_; lean_object* v___x_5293_; uint8_t v_isShared_5294_; uint8_t v_isSharedCheck_5298_; 
v_a_5291_ = lean_ctor_get(v___x_5281_, 0);
v_isSharedCheck_5298_ = !lean_is_exclusive(v___x_5281_);
if (v_isSharedCheck_5298_ == 0)
{
v___x_5293_ = v___x_5281_;
v_isShared_5294_ = v_isSharedCheck_5298_;
goto v_resetjp_5292_;
}
else
{
lean_inc(v_a_5291_);
lean_dec(v___x_5281_);
v___x_5293_ = lean_box(0);
v_isShared_5294_ = v_isSharedCheck_5298_;
goto v_resetjp_5292_;
}
v_resetjp_5292_:
{
lean_object* v___x_5296_; 
if (v_isShared_5294_ == 0)
{
v___x_5296_ = v___x_5293_;
goto v_reusejp_5295_;
}
else
{
lean_object* v_reuseFailAlloc_5297_; 
v_reuseFailAlloc_5297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5297_, 0, v_a_5291_);
v___x_5296_ = v_reuseFailAlloc_5297_;
goto v_reusejp_5295_;
}
v_reusejp_5295_:
{
return v___x_5296_;
}
}
}
}
else
{
lean_object* v___x_5299_; lean_object* v___x_5301_; 
lean_dec(v_a_5274_);
lean_dec_ref(v_arg_5271_);
lean_dec_ref(v_arg_5270_);
lean_dec_ref(v_e_5243_);
v___x_5299_ = lean_box(v___x_5269_);
if (v_isShared_5277_ == 0)
{
lean_ctor_set(v___x_5276_, 0, v___x_5299_);
v___x_5301_ = v___x_5276_;
goto v_reusejp_5300_;
}
else
{
lean_object* v_reuseFailAlloc_5302_; 
v_reuseFailAlloc_5302_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5302_, 0, v___x_5299_);
v___x_5301_ = v_reuseFailAlloc_5302_;
goto v_reusejp_5300_;
}
v_reusejp_5300_:
{
return v___x_5301_;
}
}
}
}
else
{
lean_object* v_a_5304_; lean_object* v___x_5306_; uint8_t v_isShared_5307_; uint8_t v_isSharedCheck_5311_; 
lean_dec_ref(v_arg_5271_);
lean_dec_ref(v_arg_5270_);
lean_dec_ref(v_e_5243_);
v_a_5304_ = lean_ctor_get(v___x_5273_, 0);
v_isSharedCheck_5311_ = !lean_is_exclusive(v___x_5273_);
if (v_isSharedCheck_5311_ == 0)
{
v___x_5306_ = v___x_5273_;
v_isShared_5307_ = v_isSharedCheck_5311_;
goto v_resetjp_5305_;
}
else
{
lean_inc(v_a_5304_);
lean_dec(v___x_5273_);
v___x_5306_ = lean_box(0);
v_isShared_5307_ = v_isSharedCheck_5311_;
goto v_resetjp_5305_;
}
v_resetjp_5305_:
{
lean_object* v___x_5309_; 
if (v_isShared_5307_ == 0)
{
v___x_5309_ = v___x_5306_;
goto v_reusejp_5308_;
}
else
{
lean_object* v_reuseFailAlloc_5310_; 
v_reuseFailAlloc_5310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5310_, 0, v_a_5304_);
v___x_5309_ = v_reuseFailAlloc_5310_;
goto v_reusejp_5308_;
}
v_reusejp_5308_:
{
return v___x_5309_;
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
lean_object* v_a_5312_; lean_object* v___x_5314_; uint8_t v_isShared_5315_; uint8_t v_isSharedCheck_5319_; 
lean_dec_ref(v_e_5243_);
v_a_5312_ = lean_ctor_get(v___x_5259_, 0);
v_isSharedCheck_5319_ = !lean_is_exclusive(v___x_5259_);
if (v_isSharedCheck_5319_ == 0)
{
v___x_5314_ = v___x_5259_;
v_isShared_5315_ = v_isSharedCheck_5319_;
goto v_resetjp_5313_;
}
else
{
lean_inc(v_a_5312_);
lean_dec(v___x_5259_);
v___x_5314_ = lean_box(0);
v_isShared_5315_ = v_isSharedCheck_5319_;
goto v_resetjp_5313_;
}
v_resetjp_5313_:
{
lean_object* v___x_5317_; 
if (v_isShared_5315_ == 0)
{
v___x_5317_ = v___x_5314_;
goto v_reusejp_5316_;
}
else
{
lean_object* v_reuseFailAlloc_5318_; 
v_reuseFailAlloc_5318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5318_, 0, v_a_5312_);
v___x_5317_ = v_reuseFailAlloc_5318_;
goto v_reusejp_5316_;
}
v_reusejp_5316_:
{
return v___x_5317_;
}
}
}
v___jp_5255_:
{
uint8_t v___x_5256_; lean_object* v___x_5257_; lean_object* v___x_5258_; 
v___x_5256_ = 0;
v___x_5257_ = lean_box(v___x_5256_);
v___x_5258_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5258_, 0, v___x_5257_);
return v___x_5258_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeInv___boxed(lean_object* v_e_5320_, lean_object* v_a_5321_, lean_object* v_a_5322_, lean_object* v_a_5323_, lean_object* v_a_5324_, lean_object* v_a_5325_, lean_object* v_a_5326_, lean_object* v_a_5327_, lean_object* v_a_5328_, lean_object* v_a_5329_, lean_object* v_a_5330_, lean_object* v_a_5331_){
_start:
{
lean_object* v_res_5332_; 
v_res_5332_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeInv(v_e_5320_, v_a_5321_, v_a_5322_, v_a_5323_, v_a_5324_, v_a_5325_, v_a_5326_, v_a_5327_, v_a_5328_, v_a_5329_, v_a_5330_);
lean_dec(v_a_5330_);
lean_dec_ref(v_a_5329_);
lean_dec(v_a_5328_);
lean_dec_ref(v_a_5327_);
lean_dec(v_a_5326_);
lean_dec_ref(v_a_5325_);
lean_dec(v_a_5324_);
lean_dec_ref(v_a_5323_);
lean_dec(v_a_5322_);
lean_dec(v_a_5321_);
return v_res_5332_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_internalize___lam__0(lean_object* v_e_5333_, lean_object* v_val_5334_, lean_object* v_s_5335_){
_start:
{
lean_object* v_toRingState_5336_; lean_object* v_denoteEntries_5337_; lean_object* v_nextId_5338_; lean_object* v_steps_5339_; lean_object* v_queue_5340_; lean_object* v_basis_5341_; lean_object* v_diseqs_5342_; uint8_t v_recheck_5343_; lean_object* v_invSet_5344_; lean_object* v_powIdentityVarCount_5345_; lean_object* v_numEq0_x3f_5346_; uint8_t v_numEq0Updated_5347_; lean_object* v___x_5349_; uint8_t v_isShared_5350_; uint8_t v_isSharedCheck_5370_; 
v_toRingState_5336_ = lean_ctor_get(v_s_5335_, 0);
v_denoteEntries_5337_ = lean_ctor_get(v_s_5335_, 1);
v_nextId_5338_ = lean_ctor_get(v_s_5335_, 2);
v_steps_5339_ = lean_ctor_get(v_s_5335_, 3);
v_queue_5340_ = lean_ctor_get(v_s_5335_, 4);
v_basis_5341_ = lean_ctor_get(v_s_5335_, 5);
v_diseqs_5342_ = lean_ctor_get(v_s_5335_, 6);
v_recheck_5343_ = lean_ctor_get_uint8(v_s_5335_, sizeof(void*)*10);
v_invSet_5344_ = lean_ctor_get(v_s_5335_, 7);
v_powIdentityVarCount_5345_ = lean_ctor_get(v_s_5335_, 8);
v_numEq0_x3f_5346_ = lean_ctor_get(v_s_5335_, 9);
v_numEq0Updated_5347_ = lean_ctor_get_uint8(v_s_5335_, sizeof(void*)*10 + 1);
v_isSharedCheck_5370_ = !lean_is_exclusive(v_s_5335_);
if (v_isSharedCheck_5370_ == 0)
{
v___x_5349_ = v_s_5335_;
v_isShared_5350_ = v_isSharedCheck_5370_;
goto v_resetjp_5348_;
}
else
{
lean_inc(v_numEq0_x3f_5346_);
lean_inc(v_powIdentityVarCount_5345_);
lean_inc(v_invSet_5344_);
lean_inc(v_diseqs_5342_);
lean_inc(v_basis_5341_);
lean_inc(v_queue_5340_);
lean_inc(v_steps_5339_);
lean_inc(v_nextId_5338_);
lean_inc(v_denoteEntries_5337_);
lean_inc(v_toRingState_5336_);
lean_dec(v_s_5335_);
v___x_5349_ = lean_box(0);
v_isShared_5350_ = v_isSharedCheck_5370_;
goto v_resetjp_5348_;
}
v_resetjp_5348_:
{
lean_object* v_vars_5351_; lean_object* v_varMap_5352_; lean_object* v_denote_5353_; lean_object* v_natCastSet_5354_; lean_object* v_natCasts_5355_; uint8_t v_hasIntCast_5356_; lean_object* v___x_5358_; uint8_t v_isShared_5359_; uint8_t v_isSharedCheck_5369_; 
v_vars_5351_ = lean_ctor_get(v_toRingState_5336_, 0);
v_varMap_5352_ = lean_ctor_get(v_toRingState_5336_, 1);
v_denote_5353_ = lean_ctor_get(v_toRingState_5336_, 2);
v_natCastSet_5354_ = lean_ctor_get(v_toRingState_5336_, 3);
v_natCasts_5355_ = lean_ctor_get(v_toRingState_5336_, 4);
v_hasIntCast_5356_ = lean_ctor_get_uint8(v_toRingState_5336_, sizeof(void*)*5);
v_isSharedCheck_5369_ = !lean_is_exclusive(v_toRingState_5336_);
if (v_isSharedCheck_5369_ == 0)
{
v___x_5358_ = v_toRingState_5336_;
v_isShared_5359_ = v_isSharedCheck_5369_;
goto v_resetjp_5357_;
}
else
{
lean_inc(v_natCasts_5355_);
lean_inc(v_natCastSet_5354_);
lean_inc(v_denote_5353_);
lean_inc(v_varMap_5352_);
lean_inc(v_vars_5351_);
lean_dec(v_toRingState_5336_);
v___x_5358_ = lean_box(0);
v_isShared_5359_ = v_isSharedCheck_5369_;
goto v_resetjp_5357_;
}
v_resetjp_5357_:
{
lean_object* v___x_5360_; lean_object* v___x_5362_; 
lean_inc_ref(v_val_5334_);
lean_inc_ref(v_e_5333_);
v___x_5360_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0_spec__2___redArg(v_denote_5353_, v_e_5333_, v_val_5334_);
if (v_isShared_5359_ == 0)
{
lean_ctor_set(v___x_5358_, 2, v___x_5360_);
v___x_5362_ = v___x_5358_;
goto v_reusejp_5361_;
}
else
{
lean_object* v_reuseFailAlloc_5368_; 
v_reuseFailAlloc_5368_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_5368_, 0, v_vars_5351_);
lean_ctor_set(v_reuseFailAlloc_5368_, 1, v_varMap_5352_);
lean_ctor_set(v_reuseFailAlloc_5368_, 2, v___x_5360_);
lean_ctor_set(v_reuseFailAlloc_5368_, 3, v_natCastSet_5354_);
lean_ctor_set(v_reuseFailAlloc_5368_, 4, v_natCasts_5355_);
lean_ctor_set_uint8(v_reuseFailAlloc_5368_, sizeof(void*)*5, v_hasIntCast_5356_);
v___x_5362_ = v_reuseFailAlloc_5368_;
goto v_reusejp_5361_;
}
v_reusejp_5361_:
{
lean_object* v___x_5363_; lean_object* v___x_5364_; lean_object* v___x_5366_; 
v___x_5363_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5363_, 0, v_e_5333_);
lean_ctor_set(v___x_5363_, 1, v_val_5334_);
v___x_5364_ = l_Lean_PersistentArray_push___redArg(v_denoteEntries_5337_, v___x_5363_);
if (v_isShared_5350_ == 0)
{
lean_ctor_set(v___x_5349_, 1, v___x_5364_);
lean_ctor_set(v___x_5349_, 0, v___x_5362_);
v___x_5366_ = v___x_5349_;
goto v_reusejp_5365_;
}
else
{
lean_object* v_reuseFailAlloc_5367_; 
v_reuseFailAlloc_5367_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v_reuseFailAlloc_5367_, 0, v___x_5362_);
lean_ctor_set(v_reuseFailAlloc_5367_, 1, v___x_5364_);
lean_ctor_set(v_reuseFailAlloc_5367_, 2, v_nextId_5338_);
lean_ctor_set(v_reuseFailAlloc_5367_, 3, v_steps_5339_);
lean_ctor_set(v_reuseFailAlloc_5367_, 4, v_queue_5340_);
lean_ctor_set(v_reuseFailAlloc_5367_, 5, v_basis_5341_);
lean_ctor_set(v_reuseFailAlloc_5367_, 6, v_diseqs_5342_);
lean_ctor_set(v_reuseFailAlloc_5367_, 7, v_invSet_5344_);
lean_ctor_set(v_reuseFailAlloc_5367_, 8, v_powIdentityVarCount_5345_);
lean_ctor_set(v_reuseFailAlloc_5367_, 9, v_numEq0_x3f_5346_);
lean_ctor_set_uint8(v_reuseFailAlloc_5367_, sizeof(void*)*10, v_recheck_5343_);
lean_ctor_set_uint8(v_reuseFailAlloc_5367_, sizeof(void*)*10 + 1, v_numEq0Updated_5347_);
v___x_5366_ = v_reuseFailAlloc_5367_;
goto v_reusejp_5365_;
}
v_reusejp_5365_:
{
return v___x_5366_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_internalize___lam__1(lean_object* v_e_5371_, lean_object* v_val_5372_, lean_object* v_s_5373_){
_start:
{
lean_object* v_denote_5374_; lean_object* v_vars_5375_; lean_object* v_varMap_5376_; lean_object* v___x_5378_; uint8_t v_isShared_5379_; uint8_t v_isSharedCheck_5384_; 
v_denote_5374_ = lean_ctor_get(v_s_5373_, 0);
v_vars_5375_ = lean_ctor_get(v_s_5373_, 1);
v_varMap_5376_ = lean_ctor_get(v_s_5373_, 2);
v_isSharedCheck_5384_ = !lean_is_exclusive(v_s_5373_);
if (v_isSharedCheck_5384_ == 0)
{
v___x_5378_ = v_s_5373_;
v_isShared_5379_ = v_isSharedCheck_5384_;
goto v_resetjp_5377_;
}
else
{
lean_inc(v_varMap_5376_);
lean_inc(v_vars_5375_);
lean_inc(v_denote_5374_);
lean_dec(v_s_5373_);
v___x_5378_ = lean_box(0);
v_isShared_5379_ = v_isSharedCheck_5384_;
goto v_resetjp_5377_;
}
v_resetjp_5377_:
{
lean_object* v___x_5380_; lean_object* v___x_5382_; 
v___x_5380_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0_spec__2___redArg(v_denote_5374_, v_e_5371_, v_val_5372_);
if (v_isShared_5379_ == 0)
{
lean_ctor_set(v___x_5378_, 0, v___x_5380_);
v___x_5382_ = v___x_5378_;
goto v_reusejp_5381_;
}
else
{
lean_object* v_reuseFailAlloc_5383_; 
v_reuseFailAlloc_5383_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5383_, 0, v___x_5380_);
lean_ctor_set(v_reuseFailAlloc_5383_, 1, v_vars_5375_);
lean_ctor_set(v_reuseFailAlloc_5383_, 2, v_varMap_5376_);
v___x_5382_ = v_reuseFailAlloc_5383_;
goto v_reusejp_5381_;
}
v_reusejp_5381_:
{
return v___x_5382_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_internalize___lam__2(lean_object* v_e_5385_, lean_object* v_val_5386_, lean_object* v_s_5387_){
_start:
{
lean_object* v_vars_5388_; lean_object* v_varMap_5389_; lean_object* v_denote_5390_; lean_object* v_natCastSet_5391_; lean_object* v_natCasts_5392_; uint8_t v_hasIntCast_5393_; lean_object* v___x_5395_; uint8_t v_isShared_5396_; uint8_t v_isSharedCheck_5401_; 
v_vars_5388_ = lean_ctor_get(v_s_5387_, 0);
v_varMap_5389_ = lean_ctor_get(v_s_5387_, 1);
v_denote_5390_ = lean_ctor_get(v_s_5387_, 2);
v_natCastSet_5391_ = lean_ctor_get(v_s_5387_, 3);
v_natCasts_5392_ = lean_ctor_get(v_s_5387_, 4);
v_hasIntCast_5393_ = lean_ctor_get_uint8(v_s_5387_, sizeof(void*)*5);
v_isSharedCheck_5401_ = !lean_is_exclusive(v_s_5387_);
if (v_isSharedCheck_5401_ == 0)
{
v___x_5395_ = v_s_5387_;
v_isShared_5396_ = v_isSharedCheck_5401_;
goto v_resetjp_5394_;
}
else
{
lean_inc(v_natCasts_5392_);
lean_inc(v_natCastSet_5391_);
lean_inc(v_denote_5390_);
lean_inc(v_varMap_5389_);
lean_inc(v_vars_5388_);
lean_dec(v_s_5387_);
v___x_5395_ = lean_box(0);
v_isShared_5396_ = v_isSharedCheck_5401_;
goto v_resetjp_5394_;
}
v_resetjp_5394_:
{
lean_object* v___x_5397_; lean_object* v___x_5399_; 
v___x_5397_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processCast___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast_spec__0_spec__2___redArg(v_denote_5390_, v_e_5385_, v_val_5386_);
if (v_isShared_5396_ == 0)
{
lean_ctor_set(v___x_5395_, 2, v___x_5397_);
v___x_5399_ = v___x_5395_;
goto v_reusejp_5398_;
}
else
{
lean_object* v_reuseFailAlloc_5400_; 
v_reuseFailAlloc_5400_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_5400_, 0, v_vars_5388_);
lean_ctor_set(v_reuseFailAlloc_5400_, 1, v_varMap_5389_);
lean_ctor_set(v_reuseFailAlloc_5400_, 2, v___x_5397_);
lean_ctor_set(v_reuseFailAlloc_5400_, 3, v_natCastSet_5391_);
lean_ctor_set(v_reuseFailAlloc_5400_, 4, v_natCasts_5392_);
lean_ctor_set_uint8(v_reuseFailAlloc_5400_, sizeof(void*)*5, v_hasIntCast_5393_);
v___x_5399_ = v_reuseFailAlloc_5400_;
goto v_reusejp_5398_;
}
v_reusejp_5398_:
{
return v___x_5399_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0___redArg(lean_object* v_cls_5402_, lean_object* v_msg_5403_, lean_object* v___y_5404_, lean_object* v___y_5405_, lean_object* v___y_5406_, lean_object* v___y_5407_){
_start:
{
lean_object* v_ref_5409_; lean_object* v___x_5410_; lean_object* v_a_5411_; lean_object* v___x_5413_; uint8_t v_isShared_5414_; uint8_t v_isSharedCheck_5456_; 
v_ref_5409_ = lean_ctor_get(v___y_5406_, 2);
v___x_5410_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5(v_msg_5403_, v___y_5404_, v___y_5405_, v___y_5406_, v___y_5407_);
v_a_5411_ = lean_ctor_get(v___x_5410_, 0);
v_isSharedCheck_5456_ = !lean_is_exclusive(v___x_5410_);
if (v_isSharedCheck_5456_ == 0)
{
v___x_5413_ = v___x_5410_;
v_isShared_5414_ = v_isSharedCheck_5456_;
goto v_resetjp_5412_;
}
else
{
lean_inc(v_a_5411_);
lean_dec(v___x_5410_);
v___x_5413_ = lean_box(0);
v_isShared_5414_ = v_isSharedCheck_5456_;
goto v_resetjp_5412_;
}
v_resetjp_5412_:
{
lean_object* v___x_5415_; lean_object* v_traceState_5416_; lean_object* v_env_5417_; lean_object* v_nextMacroScope_5418_; lean_object* v_ngen_5419_; lean_object* v_auxDeclNGen_5420_; lean_object* v_cache_5421_; lean_object* v_recordedDeps_5422_; lean_object* v_messages_5423_; lean_object* v_infoState_5424_; lean_object* v_snapshotTasks_5425_; lean_object* v___x_5427_; uint8_t v_isShared_5428_; uint8_t v_isSharedCheck_5455_; 
v___x_5415_ = lean_st_ref_take(v___y_5407_);
v_traceState_5416_ = lean_ctor_get(v___x_5415_, 4);
v_env_5417_ = lean_ctor_get(v___x_5415_, 0);
v_nextMacroScope_5418_ = lean_ctor_get(v___x_5415_, 1);
v_ngen_5419_ = lean_ctor_get(v___x_5415_, 2);
v_auxDeclNGen_5420_ = lean_ctor_get(v___x_5415_, 3);
v_cache_5421_ = lean_ctor_get(v___x_5415_, 5);
v_recordedDeps_5422_ = lean_ctor_get(v___x_5415_, 6);
v_messages_5423_ = lean_ctor_get(v___x_5415_, 7);
v_infoState_5424_ = lean_ctor_get(v___x_5415_, 8);
v_snapshotTasks_5425_ = lean_ctor_get(v___x_5415_, 9);
v_isSharedCheck_5455_ = !lean_is_exclusive(v___x_5415_);
if (v_isSharedCheck_5455_ == 0)
{
v___x_5427_ = v___x_5415_;
v_isShared_5428_ = v_isSharedCheck_5455_;
goto v_resetjp_5426_;
}
else
{
lean_inc(v_snapshotTasks_5425_);
lean_inc(v_infoState_5424_);
lean_inc(v_messages_5423_);
lean_inc(v_recordedDeps_5422_);
lean_inc(v_cache_5421_);
lean_inc(v_traceState_5416_);
lean_inc(v_auxDeclNGen_5420_);
lean_inc(v_ngen_5419_);
lean_inc(v_nextMacroScope_5418_);
lean_inc(v_env_5417_);
lean_dec(v___x_5415_);
v___x_5427_ = lean_box(0);
v_isShared_5428_ = v_isSharedCheck_5455_;
goto v_resetjp_5426_;
}
v_resetjp_5426_:
{
uint64_t v_tid_5429_; lean_object* v_traces_5430_; lean_object* v___x_5432_; uint8_t v_isShared_5433_; uint8_t v_isSharedCheck_5454_; 
v_tid_5429_ = lean_ctor_get_uint64(v_traceState_5416_, sizeof(void*)*1);
v_traces_5430_ = lean_ctor_get(v_traceState_5416_, 0);
v_isSharedCheck_5454_ = !lean_is_exclusive(v_traceState_5416_);
if (v_isSharedCheck_5454_ == 0)
{
v___x_5432_ = v_traceState_5416_;
v_isShared_5433_ = v_isSharedCheck_5454_;
goto v_resetjp_5431_;
}
else
{
lean_inc(v_traces_5430_);
lean_dec(v_traceState_5416_);
v___x_5432_ = lean_box(0);
v_isShared_5433_ = v_isSharedCheck_5454_;
goto v_resetjp_5431_;
}
v_resetjp_5431_:
{
lean_object* v___x_5434_; lean_object* v___x_5435_; double v___x_5436_; uint8_t v___x_5437_; lean_object* v___x_5438_; lean_object* v___x_5439_; lean_object* v___x_5440_; lean_object* v___x_5441_; lean_object* v___x_5442_; lean_object* v___x_5443_; lean_object* v___x_5445_; 
v___x_5434_ = lean_box(0);
v___x_5435_ = lean_box(0);
v___x_5436_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg___closed__0);
v___x_5437_ = 0;
v___x_5438_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg___closed__1));
v___x_5439_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_5439_, 0, v_cls_5402_);
lean_ctor_set(v___x_5439_, 1, v___x_5435_);
lean_ctor_set(v___x_5439_, 2, v___x_5438_);
lean_ctor_set_float(v___x_5439_, sizeof(void*)*3, v___x_5436_);
lean_ctor_set_float(v___x_5439_, sizeof(void*)*3 + 8, v___x_5436_);
lean_ctor_set_uint8(v___x_5439_, sizeof(void*)*3 + 16, v___x_5437_);
v___x_5440_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg___closed__2));
v___x_5441_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_5441_, 0, v___x_5439_);
lean_ctor_set(v___x_5441_, 1, v_a_5411_);
lean_ctor_set(v___x_5441_, 2, v___x_5440_);
lean_inc(v_ref_5409_);
v___x_5442_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5442_, 0, v_ref_5409_);
lean_ctor_set(v___x_5442_, 1, v___x_5441_);
v___x_5443_ = l_Lean_PersistentArray_push___redArg(v_traces_5430_, v___x_5442_);
if (v_isShared_5433_ == 0)
{
lean_ctor_set(v___x_5432_, 0, v___x_5443_);
v___x_5445_ = v___x_5432_;
goto v_reusejp_5444_;
}
else
{
lean_object* v_reuseFailAlloc_5453_; 
v_reuseFailAlloc_5453_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_5453_, 0, v___x_5443_);
lean_ctor_set_uint64(v_reuseFailAlloc_5453_, sizeof(void*)*1, v_tid_5429_);
v___x_5445_ = v_reuseFailAlloc_5453_;
goto v_reusejp_5444_;
}
v_reusejp_5444_:
{
lean_object* v___x_5447_; 
if (v_isShared_5428_ == 0)
{
lean_ctor_set(v___x_5427_, 4, v___x_5445_);
v___x_5447_ = v___x_5427_;
goto v_reusejp_5446_;
}
else
{
lean_object* v_reuseFailAlloc_5452_; 
v_reuseFailAlloc_5452_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_5452_, 0, v_env_5417_);
lean_ctor_set(v_reuseFailAlloc_5452_, 1, v_nextMacroScope_5418_);
lean_ctor_set(v_reuseFailAlloc_5452_, 2, v_ngen_5419_);
lean_ctor_set(v_reuseFailAlloc_5452_, 3, v_auxDeclNGen_5420_);
lean_ctor_set(v_reuseFailAlloc_5452_, 4, v___x_5445_);
lean_ctor_set(v_reuseFailAlloc_5452_, 5, v_cache_5421_);
lean_ctor_set(v_reuseFailAlloc_5452_, 6, v_recordedDeps_5422_);
lean_ctor_set(v_reuseFailAlloc_5452_, 7, v_messages_5423_);
lean_ctor_set(v_reuseFailAlloc_5452_, 8, v_infoState_5424_);
lean_ctor_set(v_reuseFailAlloc_5452_, 9, v_snapshotTasks_5425_);
v___x_5447_ = v_reuseFailAlloc_5452_;
goto v_reusejp_5446_;
}
v_reusejp_5446_:
{
lean_object* v___x_5448_; lean_object* v___x_5450_; 
v___x_5448_ = lean_st_ref_put(v___y_5407_, v___x_5447_);
if (v_isShared_5414_ == 0)
{
lean_ctor_set(v___x_5413_, 0, v___x_5434_);
v___x_5450_ = v___x_5413_;
goto v_reusejp_5449_;
}
else
{
lean_object* v_reuseFailAlloc_5451_; 
v_reuseFailAlloc_5451_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5451_, 0, v___x_5434_);
v___x_5450_ = v_reuseFailAlloc_5451_;
goto v_reusejp_5449_;
}
v_reusejp_5449_:
{
return v___x_5450_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0___redArg___boxed(lean_object* v_cls_5457_, lean_object* v_msg_5458_, lean_object* v___y_5459_, lean_object* v___y_5460_, lean_object* v___y_5461_, lean_object* v___y_5462_, lean_object* v___y_5463_){
_start:
{
lean_object* v_res_5464_; 
v_res_5464_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0___redArg(v_cls_5457_, v_msg_5458_, v___y_5459_, v___y_5460_, v___y_5461_, v___y_5462_);
lean_dec(v___y_5462_);
lean_dec_ref(v___y_5461_);
lean_dec(v___y_5460_);
lean_dec_ref(v___y_5459_);
return v_res_5464_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__1___redArg(lean_object* v_cls_5465_, lean_object* v_msg_5466_, lean_object* v___y_5467_, lean_object* v___y_5468_, lean_object* v___y_5469_, lean_object* v___y_5470_){
_start:
{
lean_object* v_ref_5472_; lean_object* v___x_5473_; lean_object* v_a_5474_; lean_object* v___x_5476_; uint8_t v_isShared_5477_; uint8_t v_isSharedCheck_5519_; 
v_ref_5472_ = lean_ctor_get(v___y_5469_, 2);
v___x_5473_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5(v_msg_5466_, v___y_5467_, v___y_5468_, v___y_5469_, v___y_5470_);
v_a_5474_ = lean_ctor_get(v___x_5473_, 0);
v_isSharedCheck_5519_ = !lean_is_exclusive(v___x_5473_);
if (v_isSharedCheck_5519_ == 0)
{
v___x_5476_ = v___x_5473_;
v_isShared_5477_ = v_isSharedCheck_5519_;
goto v_resetjp_5475_;
}
else
{
lean_inc(v_a_5474_);
lean_dec(v___x_5473_);
v___x_5476_ = lean_box(0);
v_isShared_5477_ = v_isSharedCheck_5519_;
goto v_resetjp_5475_;
}
v_resetjp_5475_:
{
lean_object* v___x_5478_; lean_object* v_traceState_5479_; lean_object* v_env_5480_; lean_object* v_nextMacroScope_5481_; lean_object* v_ngen_5482_; lean_object* v_auxDeclNGen_5483_; lean_object* v_cache_5484_; lean_object* v_recordedDeps_5485_; lean_object* v_messages_5486_; lean_object* v_infoState_5487_; lean_object* v_snapshotTasks_5488_; lean_object* v___x_5490_; uint8_t v_isShared_5491_; uint8_t v_isSharedCheck_5518_; 
v___x_5478_ = lean_st_ref_take(v___y_5470_);
v_traceState_5479_ = lean_ctor_get(v___x_5478_, 4);
v_env_5480_ = lean_ctor_get(v___x_5478_, 0);
v_nextMacroScope_5481_ = lean_ctor_get(v___x_5478_, 1);
v_ngen_5482_ = lean_ctor_get(v___x_5478_, 2);
v_auxDeclNGen_5483_ = lean_ctor_get(v___x_5478_, 3);
v_cache_5484_ = lean_ctor_get(v___x_5478_, 5);
v_recordedDeps_5485_ = lean_ctor_get(v___x_5478_, 6);
v_messages_5486_ = lean_ctor_get(v___x_5478_, 7);
v_infoState_5487_ = lean_ctor_get(v___x_5478_, 8);
v_snapshotTasks_5488_ = lean_ctor_get(v___x_5478_, 9);
v_isSharedCheck_5518_ = !lean_is_exclusive(v___x_5478_);
if (v_isSharedCheck_5518_ == 0)
{
v___x_5490_ = v___x_5478_;
v_isShared_5491_ = v_isSharedCheck_5518_;
goto v_resetjp_5489_;
}
else
{
lean_inc(v_snapshotTasks_5488_);
lean_inc(v_infoState_5487_);
lean_inc(v_messages_5486_);
lean_inc(v_recordedDeps_5485_);
lean_inc(v_cache_5484_);
lean_inc(v_traceState_5479_);
lean_inc(v_auxDeclNGen_5483_);
lean_inc(v_ngen_5482_);
lean_inc(v_nextMacroScope_5481_);
lean_inc(v_env_5480_);
lean_dec(v___x_5478_);
v___x_5490_ = lean_box(0);
v_isShared_5491_ = v_isSharedCheck_5518_;
goto v_resetjp_5489_;
}
v_resetjp_5489_:
{
uint64_t v_tid_5492_; lean_object* v_traces_5493_; lean_object* v___x_5495_; uint8_t v_isShared_5496_; uint8_t v_isSharedCheck_5517_; 
v_tid_5492_ = lean_ctor_get_uint64(v_traceState_5479_, sizeof(void*)*1);
v_traces_5493_ = lean_ctor_get(v_traceState_5479_, 0);
v_isSharedCheck_5517_ = !lean_is_exclusive(v_traceState_5479_);
if (v_isSharedCheck_5517_ == 0)
{
v___x_5495_ = v_traceState_5479_;
v_isShared_5496_ = v_isSharedCheck_5517_;
goto v_resetjp_5494_;
}
else
{
lean_inc(v_traces_5493_);
lean_dec(v_traceState_5479_);
v___x_5495_ = lean_box(0);
v_isShared_5496_ = v_isSharedCheck_5517_;
goto v_resetjp_5494_;
}
v_resetjp_5494_:
{
lean_object* v___x_5497_; lean_object* v___x_5498_; double v___x_5499_; uint8_t v___x_5500_; lean_object* v___x_5501_; lean_object* v___x_5502_; lean_object* v___x_5503_; lean_object* v___x_5504_; lean_object* v___x_5505_; lean_object* v___x_5506_; lean_object* v___x_5508_; 
v___x_5497_ = lean_box(0);
v___x_5498_ = lean_box(0);
v___x_5499_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg___closed__0);
v___x_5500_ = 0;
v___x_5501_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg___closed__1));
v___x_5502_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_5502_, 0, v_cls_5465_);
lean_ctor_set(v___x_5502_, 1, v___x_5498_);
lean_ctor_set(v___x_5502_, 2, v___x_5501_);
lean_ctor_set_float(v___x_5502_, sizeof(void*)*3, v___x_5499_);
lean_ctor_set_float(v___x_5502_, sizeof(void*)*3 + 8, v___x_5499_);
lean_ctor_set_uint8(v___x_5502_, sizeof(void*)*3 + 16, v___x_5500_);
v___x_5503_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg___closed__2));
v___x_5504_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_5504_, 0, v___x_5502_);
lean_ctor_set(v___x_5504_, 1, v_a_5474_);
lean_ctor_set(v___x_5504_, 2, v___x_5503_);
lean_inc(v_ref_5472_);
v___x_5505_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5505_, 0, v_ref_5472_);
lean_ctor_set(v___x_5505_, 1, v___x_5504_);
v___x_5506_ = l_Lean_PersistentArray_push___redArg(v_traces_5493_, v___x_5505_);
if (v_isShared_5496_ == 0)
{
lean_ctor_set(v___x_5495_, 0, v___x_5506_);
v___x_5508_ = v___x_5495_;
goto v_reusejp_5507_;
}
else
{
lean_object* v_reuseFailAlloc_5516_; 
v_reuseFailAlloc_5516_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_5516_, 0, v___x_5506_);
lean_ctor_set_uint64(v_reuseFailAlloc_5516_, sizeof(void*)*1, v_tid_5492_);
v___x_5508_ = v_reuseFailAlloc_5516_;
goto v_reusejp_5507_;
}
v_reusejp_5507_:
{
lean_object* v___x_5510_; 
if (v_isShared_5491_ == 0)
{
lean_ctor_set(v___x_5490_, 4, v___x_5508_);
v___x_5510_ = v___x_5490_;
goto v_reusejp_5509_;
}
else
{
lean_object* v_reuseFailAlloc_5515_; 
v_reuseFailAlloc_5515_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_5515_, 0, v_env_5480_);
lean_ctor_set(v_reuseFailAlloc_5515_, 1, v_nextMacroScope_5481_);
lean_ctor_set(v_reuseFailAlloc_5515_, 2, v_ngen_5482_);
lean_ctor_set(v_reuseFailAlloc_5515_, 3, v_auxDeclNGen_5483_);
lean_ctor_set(v_reuseFailAlloc_5515_, 4, v___x_5508_);
lean_ctor_set(v_reuseFailAlloc_5515_, 5, v_cache_5484_);
lean_ctor_set(v_reuseFailAlloc_5515_, 6, v_recordedDeps_5485_);
lean_ctor_set(v_reuseFailAlloc_5515_, 7, v_messages_5486_);
lean_ctor_set(v_reuseFailAlloc_5515_, 8, v_infoState_5487_);
lean_ctor_set(v_reuseFailAlloc_5515_, 9, v_snapshotTasks_5488_);
v___x_5510_ = v_reuseFailAlloc_5515_;
goto v_reusejp_5509_;
}
v_reusejp_5509_:
{
lean_object* v___x_5511_; lean_object* v___x_5513_; 
v___x_5511_ = lean_st_ref_put(v___y_5470_, v___x_5510_);
if (v_isShared_5477_ == 0)
{
lean_ctor_set(v___x_5476_, 0, v___x_5497_);
v___x_5513_ = v___x_5476_;
goto v_reusejp_5512_;
}
else
{
lean_object* v_reuseFailAlloc_5514_; 
v_reuseFailAlloc_5514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5514_, 0, v___x_5497_);
v___x_5513_ = v_reuseFailAlloc_5514_;
goto v_reusejp_5512_;
}
v_reusejp_5512_:
{
return v___x_5513_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__1___redArg___boxed(lean_object* v_cls_5520_, lean_object* v_msg_5521_, lean_object* v___y_5522_, lean_object* v___y_5523_, lean_object* v___y_5524_, lean_object* v___y_5525_, lean_object* v___y_5526_){
_start:
{
lean_object* v_res_5527_; 
v_res_5527_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__1___redArg(v_cls_5520_, v_msg_5521_, v___y_5522_, v___y_5523_, v___y_5524_, v___y_5525_);
lean_dec(v___y_5525_);
lean_dec_ref(v___y_5524_);
lean_dec(v___y_5523_);
lean_dec_ref(v___y_5522_);
return v_res_5527_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__2___redArg(lean_object* v_cls_5528_, lean_object* v_msg_5529_, lean_object* v___y_5530_, lean_object* v___y_5531_, lean_object* v___y_5532_, lean_object* v___y_5533_){
_start:
{
lean_object* v_ref_5535_; lean_object* v___x_5536_; lean_object* v_a_5537_; lean_object* v___x_5539_; uint8_t v_isShared_5540_; uint8_t v_isSharedCheck_5582_; 
v_ref_5535_ = lean_ctor_get(v___y_5532_, 2);
v___x_5536_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Sym_Arith_MonadCanon_synthInstance___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___at___00Lean_Meta_Sym_Arith_getNegFn___at___00Lean_Meta_Sym_Arith_isNegInst___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_toInt_x3f_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5(v_msg_5529_, v___y_5530_, v___y_5531_, v___y_5532_, v___y_5533_);
v_a_5537_ = lean_ctor_get(v___x_5536_, 0);
v_isSharedCheck_5582_ = !lean_is_exclusive(v___x_5536_);
if (v_isSharedCheck_5582_ == 0)
{
v___x_5539_ = v___x_5536_;
v_isShared_5540_ = v_isSharedCheck_5582_;
goto v_resetjp_5538_;
}
else
{
lean_inc(v_a_5537_);
lean_dec(v___x_5536_);
v___x_5539_ = lean_box(0);
v_isShared_5540_ = v_isSharedCheck_5582_;
goto v_resetjp_5538_;
}
v_resetjp_5538_:
{
lean_object* v___x_5541_; lean_object* v_traceState_5542_; lean_object* v_env_5543_; lean_object* v_nextMacroScope_5544_; lean_object* v_ngen_5545_; lean_object* v_auxDeclNGen_5546_; lean_object* v_cache_5547_; lean_object* v_recordedDeps_5548_; lean_object* v_messages_5549_; lean_object* v_infoState_5550_; lean_object* v_snapshotTasks_5551_; lean_object* v___x_5553_; uint8_t v_isShared_5554_; uint8_t v_isSharedCheck_5581_; 
v___x_5541_ = lean_st_ref_take(v___y_5533_);
v_traceState_5542_ = lean_ctor_get(v___x_5541_, 4);
v_env_5543_ = lean_ctor_get(v___x_5541_, 0);
v_nextMacroScope_5544_ = lean_ctor_get(v___x_5541_, 1);
v_ngen_5545_ = lean_ctor_get(v___x_5541_, 2);
v_auxDeclNGen_5546_ = lean_ctor_get(v___x_5541_, 3);
v_cache_5547_ = lean_ctor_get(v___x_5541_, 5);
v_recordedDeps_5548_ = lean_ctor_get(v___x_5541_, 6);
v_messages_5549_ = lean_ctor_get(v___x_5541_, 7);
v_infoState_5550_ = lean_ctor_get(v___x_5541_, 8);
v_snapshotTasks_5551_ = lean_ctor_get(v___x_5541_, 9);
v_isSharedCheck_5581_ = !lean_is_exclusive(v___x_5541_);
if (v_isSharedCheck_5581_ == 0)
{
v___x_5553_ = v___x_5541_;
v_isShared_5554_ = v_isSharedCheck_5581_;
goto v_resetjp_5552_;
}
else
{
lean_inc(v_snapshotTasks_5551_);
lean_inc(v_infoState_5550_);
lean_inc(v_messages_5549_);
lean_inc(v_recordedDeps_5548_);
lean_inc(v_cache_5547_);
lean_inc(v_traceState_5542_);
lean_inc(v_auxDeclNGen_5546_);
lean_inc(v_ngen_5545_);
lean_inc(v_nextMacroScope_5544_);
lean_inc(v_env_5543_);
lean_dec(v___x_5541_);
v___x_5553_ = lean_box(0);
v_isShared_5554_ = v_isSharedCheck_5581_;
goto v_resetjp_5552_;
}
v_resetjp_5552_:
{
uint64_t v_tid_5555_; lean_object* v_traces_5556_; lean_object* v___x_5558_; uint8_t v_isShared_5559_; uint8_t v_isSharedCheck_5580_; 
v_tid_5555_ = lean_ctor_get_uint64(v_traceState_5542_, sizeof(void*)*1);
v_traces_5556_ = lean_ctor_get(v_traceState_5542_, 0);
v_isSharedCheck_5580_ = !lean_is_exclusive(v_traceState_5542_);
if (v_isSharedCheck_5580_ == 0)
{
v___x_5558_ = v_traceState_5542_;
v_isShared_5559_ = v_isSharedCheck_5580_;
goto v_resetjp_5557_;
}
else
{
lean_inc(v_traces_5556_);
lean_dec(v_traceState_5542_);
v___x_5558_ = lean_box(0);
v_isShared_5559_ = v_isSharedCheck_5580_;
goto v_resetjp_5557_;
}
v_resetjp_5557_:
{
lean_object* v___x_5560_; lean_object* v___x_5561_; double v___x_5562_; uint8_t v___x_5563_; lean_object* v___x_5564_; lean_object* v___x_5565_; lean_object* v___x_5566_; lean_object* v___x_5567_; lean_object* v___x_5568_; lean_object* v___x_5569_; lean_object* v___x_5571_; 
v___x_5560_ = lean_box(0);
v___x_5561_ = lean_box(0);
v___x_5562_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg___closed__0);
v___x_5563_ = 0;
v___x_5564_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg___closed__1));
v___x_5565_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_5565_, 0, v_cls_5528_);
lean_ctor_set(v___x_5565_, 1, v___x_5561_);
lean_ctor_set(v___x_5565_, 2, v___x_5564_);
lean_ctor_set_float(v___x_5565_, sizeof(void*)*3, v___x_5562_);
lean_ctor_set_float(v___x_5565_, sizeof(void*)*3 + 8, v___x_5562_);
lean_ctor_set_uint8(v___x_5565_, sizeof(void*)*3 + 16, v___x_5563_);
v___x_5566_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg___closed__2));
v___x_5567_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_5567_, 0, v___x_5565_);
lean_ctor_set(v___x_5567_, 1, v_a_5537_);
lean_ctor_set(v___x_5567_, 2, v___x_5566_);
lean_inc(v_ref_5535_);
v___x_5568_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5568_, 0, v_ref_5535_);
lean_ctor_set(v___x_5568_, 1, v___x_5567_);
v___x_5569_ = l_Lean_PersistentArray_push___redArg(v_traces_5556_, v___x_5568_);
if (v_isShared_5559_ == 0)
{
lean_ctor_set(v___x_5558_, 0, v___x_5569_);
v___x_5571_ = v___x_5558_;
goto v_reusejp_5570_;
}
else
{
lean_object* v_reuseFailAlloc_5579_; 
v_reuseFailAlloc_5579_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_5579_, 0, v___x_5569_);
lean_ctor_set_uint64(v_reuseFailAlloc_5579_, sizeof(void*)*1, v_tid_5555_);
v___x_5571_ = v_reuseFailAlloc_5579_;
goto v_reusejp_5570_;
}
v_reusejp_5570_:
{
lean_object* v___x_5573_; 
if (v_isShared_5554_ == 0)
{
lean_ctor_set(v___x_5553_, 4, v___x_5571_);
v___x_5573_ = v___x_5553_;
goto v_reusejp_5572_;
}
else
{
lean_object* v_reuseFailAlloc_5578_; 
v_reuseFailAlloc_5578_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_5578_, 0, v_env_5543_);
lean_ctor_set(v_reuseFailAlloc_5578_, 1, v_nextMacroScope_5544_);
lean_ctor_set(v_reuseFailAlloc_5578_, 2, v_ngen_5545_);
lean_ctor_set(v_reuseFailAlloc_5578_, 3, v_auxDeclNGen_5546_);
lean_ctor_set(v_reuseFailAlloc_5578_, 4, v___x_5571_);
lean_ctor_set(v_reuseFailAlloc_5578_, 5, v_cache_5547_);
lean_ctor_set(v_reuseFailAlloc_5578_, 6, v_recordedDeps_5548_);
lean_ctor_set(v_reuseFailAlloc_5578_, 7, v_messages_5549_);
lean_ctor_set(v_reuseFailAlloc_5578_, 8, v_infoState_5550_);
lean_ctor_set(v_reuseFailAlloc_5578_, 9, v_snapshotTasks_5551_);
v___x_5573_ = v_reuseFailAlloc_5578_;
goto v_reusejp_5572_;
}
v_reusejp_5572_:
{
lean_object* v___x_5574_; lean_object* v___x_5576_; 
v___x_5574_ = lean_st_ref_put(v___y_5533_, v___x_5573_);
if (v_isShared_5540_ == 0)
{
lean_ctor_set(v___x_5539_, 0, v___x_5560_);
v___x_5576_ = v___x_5539_;
goto v_reusejp_5575_;
}
else
{
lean_object* v_reuseFailAlloc_5577_; 
v_reuseFailAlloc_5577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5577_, 0, v___x_5560_);
v___x_5576_ = v_reuseFailAlloc_5577_;
goto v_reusejp_5575_;
}
v_reusejp_5575_:
{
return v___x_5576_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__2___redArg___boxed(lean_object* v_cls_5583_, lean_object* v_msg_5584_, lean_object* v___y_5585_, lean_object* v___y_5586_, lean_object* v___y_5587_, lean_object* v___y_5588_, lean_object* v___y_5589_){
_start:
{
lean_object* v_res_5590_; 
v_res_5590_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__2___redArg(v_cls_5583_, v_msg_5584_, v___y_5585_, v___y_5586_, v___y_5587_, v___y_5588_);
lean_dec(v___y_5588_);
lean_dec_ref(v___y_5587_);
lean_dec(v___y_5586_);
lean_dec_ref(v___y_5585_);
return v_res_5590_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__2(void){
_start:
{
lean_object* v___x_5596_; lean_object* v___x_5597_; lean_object* v___x_5598_; 
v___x_5596_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__1));
v___x_5597_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__1___redArg___closed__7));
v___x_5598_ = l_Lean_Name_append(v___x_5597_, v___x_5596_);
return v___x_5598_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__4(void){
_start:
{
lean_object* v___x_5600_; lean_object* v___x_5601_; 
v___x_5600_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__3));
v___x_5601_ = l_Lean_stringToMessageData(v___x_5600_);
return v___x_5601_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__6(void){
_start:
{
lean_object* v___x_5603_; lean_object* v___x_5604_; 
v___x_5603_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__5));
v___x_5604_ = l_Lean_stringToMessageData(v___x_5603_);
return v___x_5604_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__8(void){
_start:
{
lean_object* v___x_5606_; lean_object* v___x_5607_; 
v___x_5606_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__7));
v___x_5607_ = l_Lean_stringToMessageData(v___x_5606_);
return v___x_5607_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__10(void){
_start:
{
lean_object* v___x_5609_; lean_object* v___x_5610_; 
v___x_5609_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__9));
v___x_5610_ = l_Lean_stringToMessageData(v___x_5609_);
return v___x_5610_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__12(void){
_start:
{
lean_object* v___x_5612_; lean_object* v___x_5613_; 
v___x_5612_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__11));
v___x_5613_ = l_Lean_stringToMessageData(v___x_5612_);
return v___x_5613_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_internalize(lean_object* v_e_5614_, lean_object* v_parent_x3f_5615_, lean_object* v_a_5616_, lean_object* v_a_5617_, lean_object* v_a_5618_, lean_object* v_a_5619_, lean_object* v_a_5620_, lean_object* v_a_5621_, lean_object* v_a_5622_, lean_object* v_a_5623_, lean_object* v_a_5624_, lean_object* v_a_5625_){
_start:
{
lean_object* v___y_5628_; lean_object* v___y_5629_; lean_object* v___y_5630_; lean_object* v___y_5631_; lean_object* v___y_5632_; lean_object* v___y_5633_; lean_object* v___y_5634_; lean_object* v___y_5635_; lean_object* v___y_5636_; lean_object* v___y_5637_; lean_object* v___y_5638_; lean_object* v___y_5639_; lean_object* v___y_5645_; lean_object* v___y_5646_; lean_object* v___y_5647_; lean_object* v___y_5648_; lean_object* v___y_5649_; lean_object* v___y_5650_; lean_object* v___y_5651_; lean_object* v___y_5652_; lean_object* v___y_5653_; lean_object* v___y_5654_; lean_object* v___y_5655_; lean_object* v___y_5656_; lean_object* v___y_5662_; lean_object* v___y_5663_; lean_object* v___y_5664_; lean_object* v___y_5665_; lean_object* v___y_5666_; lean_object* v___y_5667_; lean_object* v___y_5668_; lean_object* v___y_5669_; lean_object* v___y_5670_; lean_object* v___y_5671_; lean_object* v___y_5672_; lean_object* v___y_5673_; lean_object* v___y_5680_; lean_object* v___y_5681_; lean_object* v___y_5682_; lean_object* v___y_5683_; lean_object* v___y_5684_; lean_object* v___y_5685_; lean_object* v___y_5686_; lean_object* v___y_5687_; lean_object* v___y_5688_; lean_object* v___y_5689_; lean_object* v___y_5690_; lean_object* v___y_5691_; lean_object* v___x_5696_; 
v___x_5696_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_5618_);
if (lean_obj_tag(v___x_5696_) == 0)
{
lean_object* v_a_5697_; lean_object* v___x_5699_; uint8_t v_isShared_5700_; uint8_t v_isSharedCheck_6003_; 
v_a_5697_ = lean_ctor_get(v___x_5696_, 0);
v_isSharedCheck_6003_ = !lean_is_exclusive(v___x_5696_);
if (v_isSharedCheck_6003_ == 0)
{
v___x_5699_ = v___x_5696_;
v_isShared_5700_ = v_isSharedCheck_6003_;
goto v_resetjp_5698_;
}
else
{
lean_inc(v_a_5697_);
lean_dec(v___x_5696_);
v___x_5699_ = lean_box(0);
v_isShared_5700_ = v_isSharedCheck_6003_;
goto v_resetjp_5698_;
}
v_resetjp_5698_:
{
uint8_t v_ring_5701_; 
v_ring_5701_ = lean_ctor_get_uint8(v_a_5697_, sizeof(void*)*18 + 22);
lean_dec(v_a_5697_);
if (v_ring_5701_ == 0)
{
lean_object* v___x_5702_; lean_object* v___x_5704_; 
lean_dec_ref(v_e_5614_);
v___x_5702_ = lean_box(0);
if (v_isShared_5700_ == 0)
{
lean_ctor_set(v___x_5699_, 0, v___x_5702_);
v___x_5704_ = v___x_5699_;
goto v_reusejp_5703_;
}
else
{
lean_object* v_reuseFailAlloc_5705_; 
v_reuseFailAlloc_5705_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5705_, 0, v___x_5702_);
v___x_5704_ = v_reuseFailAlloc_5705_;
goto v_reusejp_5703_;
}
v_reusejp_5703_:
{
return v___x_5704_;
}
}
else
{
uint8_t v___x_5706_; 
v___x_5706_ = l_Lean_Meta_Grind_Arith_isIntModuleVirtualParent(v_parent_x3f_5615_);
if (v___x_5706_ == 0)
{
lean_object* v___x_5707_; 
lean_del_object(v___x_5699_);
lean_inc_ref(v_e_5614_);
v___x_5707_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeInv(v_e_5614_, v_a_5616_, v_a_5617_, v_a_5618_, v_a_5619_, v_a_5620_, v_a_5621_, v_a_5622_, v_a_5623_, v_a_5624_, v_a_5625_);
if (lean_obj_tag(v___x_5707_) == 0)
{
lean_object* v_a_5708_; lean_object* v___x_5710_; uint8_t v_isShared_5711_; uint8_t v_isSharedCheck_5990_; 
v_a_5708_ = lean_ctor_get(v___x_5707_, 0);
v_isSharedCheck_5990_ = !lean_is_exclusive(v___x_5707_);
if (v_isSharedCheck_5990_ == 0)
{
v___x_5710_ = v___x_5707_;
v_isShared_5711_ = v_isSharedCheck_5990_;
goto v_resetjp_5709_;
}
else
{
lean_inc(v_a_5708_);
lean_dec(v___x_5707_);
v___x_5710_ = lean_box(0);
v_isShared_5711_ = v_isSharedCheck_5990_;
goto v_resetjp_5709_;
}
v_resetjp_5709_:
{
uint8_t v___x_5712_; 
v___x_5712_ = lean_unbox(v_a_5708_);
lean_dec(v_a_5708_);
if (v___x_5712_ == 0)
{
lean_object* v___x_5713_; 
lean_del_object(v___x_5710_);
lean_inc_ref(v_e_5614_);
v___x_5713_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_internalizeCast(v_e_5614_, v_a_5616_, v_a_5617_, v_a_5618_, v_a_5619_, v_a_5620_, v_a_5621_, v_a_5622_, v_a_5623_, v_a_5624_, v_a_5625_);
if (lean_obj_tag(v___x_5713_) == 0)
{
lean_object* v___x_5715_; uint8_t v_isShared_5716_; uint8_t v_isSharedCheck_5984_; 
v_isSharedCheck_5984_ = !lean_is_exclusive(v___x_5713_);
if (v_isSharedCheck_5984_ == 0)
{
lean_object* v_unused_5985_; 
v_unused_5985_ = lean_ctor_get(v___x_5713_, 0);
lean_dec(v_unused_5985_);
v___x_5715_ = v___x_5713_;
v_isShared_5716_ = v_isSharedCheck_5984_;
goto v_resetjp_5714_;
}
else
{
lean_dec(v___x_5713_);
v___x_5715_ = lean_box(0);
v_isShared_5716_ = v_isSharedCheck_5984_;
goto v_resetjp_5714_;
}
v_resetjp_5714_:
{
lean_object* v___x_5717_; 
v___x_5717_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_getType_x3f(v_e_5614_);
if (lean_obj_tag(v___x_5717_) == 1)
{
lean_object* v_val_5718_; uint8_t v_a_5720_; uint8_t v___x_5954_; 
v_val_5718_ = lean_ctor_get(v___x_5717_, 0);
lean_inc(v_val_5718_);
lean_dec_ref_known(v___x_5717_, 1);
v___x_5954_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isForbiddenParent(v_parent_x3f_5615_);
if (v___x_5954_ == 0)
{
uint8_t v___x_5955_; 
lean_del_object(v___x_5715_);
v___x_5955_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_isIneqParent(v_parent_x3f_5615_);
if (v___x_5955_ == 0)
{
v_a_5720_ = v___x_5955_;
goto v___jp_5719_;
}
else
{
lean_object* v___x_5956_; 
lean_inc(v_val_5718_);
v___x_5956_ = l_Lean_Meta_Grind_Arith_Cutsat_isCutsatType___redArg(v_val_5718_, v_a_5618_, v_a_5623_);
if (lean_obj_tag(v___x_5956_) == 0)
{
lean_object* v_a_5957_; lean_object* v___x_5959_; uint8_t v_isShared_5960_; uint8_t v_isSharedCheck_5967_; 
v_a_5957_ = lean_ctor_get(v___x_5956_, 0);
v_isSharedCheck_5967_ = !lean_is_exclusive(v___x_5956_);
if (v_isSharedCheck_5967_ == 0)
{
v___x_5959_ = v___x_5956_;
v_isShared_5960_ = v_isSharedCheck_5967_;
goto v_resetjp_5958_;
}
else
{
lean_inc(v_a_5957_);
lean_dec(v___x_5956_);
v___x_5959_ = lean_box(0);
v_isShared_5960_ = v_isSharedCheck_5967_;
goto v_resetjp_5958_;
}
v_resetjp_5958_:
{
uint8_t v___x_5961_; 
v___x_5961_ = lean_unbox(v_a_5957_);
if (v___x_5961_ == 0)
{
uint8_t v___x_5962_; 
lean_del_object(v___x_5959_);
v___x_5962_ = lean_unbox(v_a_5957_);
lean_dec(v_a_5957_);
v_a_5720_ = v___x_5962_;
goto v___jp_5719_;
}
else
{
lean_object* v___x_5963_; lean_object* v___x_5965_; 
lean_dec(v_a_5957_);
lean_dec(v_val_5718_);
lean_dec_ref(v_e_5614_);
v___x_5963_ = lean_box(0);
if (v_isShared_5960_ == 0)
{
lean_ctor_set(v___x_5959_, 0, v___x_5963_);
v___x_5965_ = v___x_5959_;
goto v_reusejp_5964_;
}
else
{
lean_object* v_reuseFailAlloc_5966_; 
v_reuseFailAlloc_5966_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5966_, 0, v___x_5963_);
v___x_5965_ = v_reuseFailAlloc_5966_;
goto v_reusejp_5964_;
}
v_reusejp_5964_:
{
return v___x_5965_;
}
}
}
}
else
{
lean_object* v_a_5968_; lean_object* v___x_5970_; uint8_t v_isShared_5971_; uint8_t v_isSharedCheck_5975_; 
lean_dec(v_val_5718_);
lean_dec_ref(v_e_5614_);
v_a_5968_ = lean_ctor_get(v___x_5956_, 0);
v_isSharedCheck_5975_ = !lean_is_exclusive(v___x_5956_);
if (v_isSharedCheck_5975_ == 0)
{
v___x_5970_ = v___x_5956_;
v_isShared_5971_ = v_isSharedCheck_5975_;
goto v_resetjp_5969_;
}
else
{
lean_inc(v_a_5968_);
lean_dec(v___x_5956_);
v___x_5970_ = lean_box(0);
v_isShared_5971_ = v_isSharedCheck_5975_;
goto v_resetjp_5969_;
}
v_resetjp_5969_:
{
lean_object* v___x_5973_; 
if (v_isShared_5971_ == 0)
{
v___x_5973_ = v___x_5970_;
goto v_reusejp_5972_;
}
else
{
lean_object* v_reuseFailAlloc_5974_; 
v_reuseFailAlloc_5974_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5974_, 0, v_a_5968_);
v___x_5973_ = v_reuseFailAlloc_5974_;
goto v_reusejp_5972_;
}
v_reusejp_5972_:
{
return v___x_5973_;
}
}
}
}
}
else
{
lean_object* v___x_5976_; lean_object* v___x_5978_; 
lean_dec(v_val_5718_);
lean_dec_ref(v_e_5614_);
v___x_5976_ = lean_box(0);
if (v_isShared_5716_ == 0)
{
lean_ctor_set(v___x_5715_, 0, v___x_5976_);
v___x_5978_ = v___x_5715_;
goto v_reusejp_5977_;
}
else
{
lean_object* v_reuseFailAlloc_5979_; 
v_reuseFailAlloc_5979_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5979_, 0, v___x_5976_);
v___x_5978_ = v_reuseFailAlloc_5979_;
goto v_reusejp_5977_;
}
v_reusejp_5977_:
{
return v___x_5978_;
}
}
v___jp_5719_:
{
lean_object* v___x_5721_; 
lean_inc(v_val_5718_);
v___x_5721_ = l_Lean_Meta_Grind_Arith_CommRing_getCommRingId_x3f___redArg(v_val_5718_, v_a_5620_, v_a_5621_, v_a_5622_, v_a_5623_, v_a_5624_, v_a_5625_);
if (lean_obj_tag(v___x_5721_) == 0)
{
lean_object* v_a_5722_; 
v_a_5722_ = lean_ctor_get(v___x_5721_, 0);
lean_inc(v_a_5722_);
lean_dec_ref_known(v___x_5721_, 1);
if (lean_obj_tag(v_a_5722_) == 1)
{
lean_object* v_val_5723_; lean_object* v___x_5724_; lean_object* v___x_5725_; 
lean_dec(v_val_5718_);
v_val_5723_ = lean_ctor_get(v_a_5722_, 0);
lean_inc_n(v_val_5723_, 2);
lean_dec_ref_known(v_a_5722_, 1);
v___x_5724_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5724_, 0, v_val_5723_);
lean_ctor_set_uint8(v___x_5724_, sizeof(void*)*1, v_a_5720_);
lean_inc_ref(v_e_5614_);
v___x_5725_ = l_Lean_Meta_Grind_Arith_CommRing_reify_x3f(v_e_5614_, v_ring_5701_, v___x_5724_, v_a_5616_, v_a_5617_, v_a_5618_, v_a_5619_, v_a_5620_, v_a_5621_, v_a_5622_, v_a_5623_, v_a_5624_, v_a_5625_);
if (lean_obj_tag(v___x_5725_) == 0)
{
lean_object* v_a_5726_; lean_object* v___x_5728_; uint8_t v_isShared_5729_; uint8_t v_isSharedCheck_5761_; 
v_a_5726_ = lean_ctor_get(v___x_5725_, 0);
v_isSharedCheck_5761_ = !lean_is_exclusive(v___x_5725_);
if (v_isSharedCheck_5761_ == 0)
{
v___x_5728_ = v___x_5725_;
v_isShared_5729_ = v_isSharedCheck_5761_;
goto v_resetjp_5727_;
}
else
{
lean_inc(v_a_5726_);
lean_dec(v___x_5725_);
v___x_5728_ = lean_box(0);
v_isShared_5729_ = v_isSharedCheck_5761_;
goto v_resetjp_5727_;
}
v_resetjp_5727_:
{
if (lean_obj_tag(v_a_5726_) == 1)
{
lean_object* v_toCold_5730_; lean_object* v_options_5731_; lean_object* v_val_5732_; lean_object* v_inheritedTraceOptions_5733_; uint8_t v_hasTrace_5734_; lean_object* v___f_5735_; 
lean_del_object(v___x_5728_);
v_toCold_5730_ = lean_ctor_get(v_a_5624_, 0);
v_options_5731_ = lean_ctor_get(v_toCold_5730_, 2);
v_val_5732_ = lean_ctor_get(v_a_5726_, 0);
lean_inc(v_val_5732_);
lean_dec_ref_known(v_a_5726_, 1);
v_inheritedTraceOptions_5733_ = lean_ctor_get(v_toCold_5730_, 11);
v_hasTrace_5734_ = lean_ctor_get_uint8(v_options_5731_, sizeof(void*)*1);
lean_inc_ref(v_e_5614_);
v___f_5735_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_internalize___lam__0), 3, 2);
lean_closure_set(v___f_5735_, 0, v_e_5614_);
lean_closure_set(v___f_5735_, 1, v_val_5732_);
if (v_hasTrace_5734_ == 0)
{
lean_dec(v_val_5723_);
v___y_5662_ = v___f_5735_;
v___y_5663_ = v___x_5724_;
v___y_5664_ = v_a_5616_;
v___y_5665_ = v_a_5617_;
v___y_5666_ = v_a_5618_;
v___y_5667_ = v_a_5619_;
v___y_5668_ = v_a_5620_;
v___y_5669_ = v_a_5621_;
v___y_5670_ = v_a_5622_;
v___y_5671_ = v_a_5623_;
v___y_5672_ = v_a_5624_;
v___y_5673_ = v_a_5625_;
goto v___jp_5661_;
}
else
{
lean_object* v___x_5736_; lean_object* v___x_5737_; uint8_t v___x_5738_; 
v___x_5736_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__1));
v___x_5737_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__2, &l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__2_once, _init_l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__2);
v___x_5738_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5733_, v_options_5731_, v___x_5737_);
if (v___x_5738_ == 0)
{
lean_dec(v_val_5723_);
v___y_5662_ = v___f_5735_;
v___y_5663_ = v___x_5724_;
v___y_5664_ = v_a_5616_;
v___y_5665_ = v_a_5617_;
v___y_5666_ = v_a_5618_;
v___y_5667_ = v_a_5619_;
v___y_5668_ = v_a_5620_;
v___y_5669_ = v_a_5621_;
v___y_5670_ = v_a_5622_;
v___y_5671_ = v_a_5623_;
v___y_5672_ = v_a_5624_;
v___y_5673_ = v_a_5625_;
goto v___jp_5661_;
}
else
{
lean_object* v___x_5739_; 
v___x_5739_ = l_Lean_Meta_Grind_updateLastTag(v_a_5616_, v_a_5617_, v_a_5618_, v_a_5619_, v_a_5620_, v_a_5621_, v_a_5622_, v_a_5623_, v_a_5624_, v_a_5625_);
if (lean_obj_tag(v___x_5739_) == 0)
{
lean_object* v___x_5741_; uint8_t v_isShared_5742_; uint8_t v_isSharedCheck_5755_; 
v_isSharedCheck_5755_ = !lean_is_exclusive(v___x_5739_);
if (v_isSharedCheck_5755_ == 0)
{
lean_object* v_unused_5756_; 
v_unused_5756_ = lean_ctor_get(v___x_5739_, 0);
lean_dec(v_unused_5756_);
v___x_5741_ = v___x_5739_;
v_isShared_5742_ = v_isSharedCheck_5755_;
goto v_resetjp_5740_;
}
else
{
lean_dec(v___x_5739_);
v___x_5741_ = lean_box(0);
v_isShared_5742_ = v_isSharedCheck_5755_;
goto v_resetjp_5740_;
}
v_resetjp_5740_:
{
lean_object* v___x_5743_; lean_object* v___x_5744_; lean_object* v___x_5746_; 
v___x_5743_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__4, &l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__4_once, _init_l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__4);
v___x_5744_ = l_Nat_reprFast(v_val_5723_);
if (v_isShared_5742_ == 0)
{
lean_ctor_set_tag(v___x_5741_, 3);
lean_ctor_set(v___x_5741_, 0, v___x_5744_);
v___x_5746_ = v___x_5741_;
goto v_reusejp_5745_;
}
else
{
lean_object* v_reuseFailAlloc_5754_; 
v_reuseFailAlloc_5754_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5754_, 0, v___x_5744_);
v___x_5746_ = v_reuseFailAlloc_5754_;
goto v_reusejp_5745_;
}
v_reusejp_5745_:
{
lean_object* v___x_5747_; lean_object* v___x_5748_; lean_object* v___x_5749_; lean_object* v___x_5750_; lean_object* v___x_5751_; lean_object* v___x_5752_; lean_object* v___x_5753_; 
v___x_5747_ = l_Lean_MessageData_ofFormat(v___x_5746_);
v___x_5748_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5748_, 0, v___x_5743_);
lean_ctor_set(v___x_5748_, 1, v___x_5747_);
v___x_5749_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__6, &l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__6_once, _init_l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__6);
v___x_5750_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5750_, 0, v___x_5748_);
lean_ctor_set(v___x_5750_, 1, v___x_5749_);
lean_inc_ref(v_e_5614_);
v___x_5751_ = l_Lean_MessageData_ofExpr(v_e_5614_);
v___x_5752_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5752_, 0, v___x_5750_);
lean_ctor_set(v___x_5752_, 1, v___x_5751_);
v___x_5753_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars_spec__0___redArg(v___x_5736_, v___x_5752_, v_a_5622_, v_a_5623_, v_a_5624_, v_a_5625_);
if (lean_obj_tag(v___x_5753_) == 0)
{
lean_dec_ref_known(v___x_5753_, 1);
v___y_5662_ = v___f_5735_;
v___y_5663_ = v___x_5724_;
v___y_5664_ = v_a_5616_;
v___y_5665_ = v_a_5617_;
v___y_5666_ = v_a_5618_;
v___y_5667_ = v_a_5619_;
v___y_5668_ = v_a_5620_;
v___y_5669_ = v_a_5621_;
v___y_5670_ = v_a_5622_;
v___y_5671_ = v_a_5623_;
v___y_5672_ = v_a_5624_;
v___y_5673_ = v_a_5625_;
goto v___jp_5661_;
}
else
{
lean_dec_ref(v___f_5735_);
lean_dec_ref_known(v___x_5724_, 1);
lean_dec_ref(v_e_5614_);
return v___x_5753_;
}
}
}
}
else
{
lean_dec_ref(v___f_5735_);
lean_dec_ref_known(v___x_5724_, 1);
lean_dec(v_val_5723_);
lean_dec_ref(v_e_5614_);
return v___x_5739_;
}
}
}
}
else
{
lean_object* v___x_5757_; lean_object* v___x_5759_; 
lean_dec(v_a_5726_);
lean_dec_ref_known(v___x_5724_, 1);
lean_dec(v_val_5723_);
lean_dec_ref(v_e_5614_);
v___x_5757_ = lean_box(0);
if (v_isShared_5729_ == 0)
{
lean_ctor_set(v___x_5728_, 0, v___x_5757_);
v___x_5759_ = v___x_5728_;
goto v_reusejp_5758_;
}
else
{
lean_object* v_reuseFailAlloc_5760_; 
v_reuseFailAlloc_5760_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5760_, 0, v___x_5757_);
v___x_5759_ = v_reuseFailAlloc_5760_;
goto v_reusejp_5758_;
}
v_reusejp_5758_:
{
return v___x_5759_;
}
}
}
}
else
{
lean_object* v_a_5762_; lean_object* v___x_5764_; uint8_t v_isShared_5765_; uint8_t v_isSharedCheck_5769_; 
lean_dec_ref_known(v___x_5724_, 1);
lean_dec(v_val_5723_);
lean_dec_ref(v_e_5614_);
v_a_5762_ = lean_ctor_get(v___x_5725_, 0);
v_isSharedCheck_5769_ = !lean_is_exclusive(v___x_5725_);
if (v_isSharedCheck_5769_ == 0)
{
v___x_5764_ = v___x_5725_;
v_isShared_5765_ = v_isSharedCheck_5769_;
goto v_resetjp_5763_;
}
else
{
lean_inc(v_a_5762_);
lean_dec(v___x_5725_);
v___x_5764_ = lean_box(0);
v_isShared_5765_ = v_isSharedCheck_5769_;
goto v_resetjp_5763_;
}
v_resetjp_5763_:
{
lean_object* v___x_5767_; 
if (v_isShared_5765_ == 0)
{
v___x_5767_ = v___x_5764_;
goto v_reusejp_5766_;
}
else
{
lean_object* v_reuseFailAlloc_5768_; 
v_reuseFailAlloc_5768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5768_, 0, v_a_5762_);
v___x_5767_ = v_reuseFailAlloc_5768_;
goto v_reusejp_5766_;
}
v_reusejp_5766_:
{
return v___x_5767_;
}
}
}
}
else
{
lean_object* v___x_5770_; 
lean_dec(v_a_5722_);
lean_inc(v_val_5718_);
v___x_5770_ = l_Lean_Meta_Grind_Arith_CommRing_getCommSemiringId_x3f___redArg(v_val_5718_, v_a_5620_, v_a_5621_, v_a_5622_, v_a_5623_, v_a_5624_, v_a_5625_);
if (lean_obj_tag(v___x_5770_) == 0)
{
lean_object* v_a_5771_; 
v_a_5771_ = lean_ctor_get(v___x_5770_, 0);
lean_inc(v_a_5771_);
lean_dec_ref_known(v___x_5770_, 1);
if (lean_obj_tag(v_a_5771_) == 1)
{
lean_object* v_val_5772_; lean_object* v___x_5773_; 
lean_dec(v_val_5718_);
v_val_5772_ = lean_ctor_get(v_a_5771_, 0);
lean_inc(v_val_5772_);
lean_dec_ref_known(v_a_5771_, 1);
lean_inc_ref(v_e_5614_);
v___x_5773_ = l_Lean_Meta_Grind_Arith_CommRing_sreify_x3f(v_e_5614_, v_val_5772_, v_a_5616_, v_a_5617_, v_a_5618_, v_a_5619_, v_a_5620_, v_a_5621_, v_a_5622_, v_a_5623_, v_a_5624_, v_a_5625_);
if (lean_obj_tag(v___x_5773_) == 0)
{
lean_object* v_a_5774_; lean_object* v___x_5776_; uint8_t v_isShared_5777_; uint8_t v_isSharedCheck_5809_; 
v_a_5774_ = lean_ctor_get(v___x_5773_, 0);
v_isSharedCheck_5809_ = !lean_is_exclusive(v___x_5773_);
if (v_isSharedCheck_5809_ == 0)
{
v___x_5776_ = v___x_5773_;
v_isShared_5777_ = v_isSharedCheck_5809_;
goto v_resetjp_5775_;
}
else
{
lean_inc(v_a_5774_);
lean_dec(v___x_5773_);
v___x_5776_ = lean_box(0);
v_isShared_5777_ = v_isSharedCheck_5809_;
goto v_resetjp_5775_;
}
v_resetjp_5775_:
{
if (lean_obj_tag(v_a_5774_) == 1)
{
lean_object* v_toCold_5778_; lean_object* v_options_5779_; lean_object* v_val_5780_; lean_object* v_inheritedTraceOptions_5781_; uint8_t v_hasTrace_5782_; lean_object* v___f_5783_; 
lean_del_object(v___x_5776_);
v_toCold_5778_ = lean_ctor_get(v_a_5624_, 0);
v_options_5779_ = lean_ctor_get(v_toCold_5778_, 2);
v_val_5780_ = lean_ctor_get(v_a_5774_, 0);
lean_inc(v_val_5780_);
lean_dec_ref_known(v_a_5774_, 1);
v_inheritedTraceOptions_5781_ = lean_ctor_get(v_toCold_5778_, 11);
v_hasTrace_5782_ = lean_ctor_get_uint8(v_options_5779_, sizeof(void*)*1);
lean_inc_ref(v_e_5614_);
v___f_5783_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_internalize___lam__1), 3, 2);
lean_closure_set(v___f_5783_, 0, v_e_5614_);
lean_closure_set(v___f_5783_, 1, v_val_5780_);
if (v_hasTrace_5782_ == 0)
{
v___y_5645_ = v___f_5783_;
v___y_5646_ = v_val_5772_;
v___y_5647_ = v_a_5616_;
v___y_5648_ = v_a_5617_;
v___y_5649_ = v_a_5618_;
v___y_5650_ = v_a_5619_;
v___y_5651_ = v_a_5620_;
v___y_5652_ = v_a_5621_;
v___y_5653_ = v_a_5622_;
v___y_5654_ = v_a_5623_;
v___y_5655_ = v_a_5624_;
v___y_5656_ = v_a_5625_;
goto v___jp_5644_;
}
else
{
lean_object* v___x_5784_; lean_object* v___x_5785_; uint8_t v___x_5786_; 
v___x_5784_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__1));
v___x_5785_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__2, &l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__2_once, _init_l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__2);
v___x_5786_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5781_, v_options_5779_, v___x_5785_);
if (v___x_5786_ == 0)
{
v___y_5645_ = v___f_5783_;
v___y_5646_ = v_val_5772_;
v___y_5647_ = v_a_5616_;
v___y_5648_ = v_a_5617_;
v___y_5649_ = v_a_5618_;
v___y_5650_ = v_a_5619_;
v___y_5651_ = v_a_5620_;
v___y_5652_ = v_a_5621_;
v___y_5653_ = v_a_5622_;
v___y_5654_ = v_a_5623_;
v___y_5655_ = v_a_5624_;
v___y_5656_ = v_a_5625_;
goto v___jp_5644_;
}
else
{
lean_object* v___x_5787_; 
v___x_5787_ = l_Lean_Meta_Grind_updateLastTag(v_a_5616_, v_a_5617_, v_a_5618_, v_a_5619_, v_a_5620_, v_a_5621_, v_a_5622_, v_a_5623_, v_a_5624_, v_a_5625_);
if (lean_obj_tag(v___x_5787_) == 0)
{
lean_object* v___x_5789_; uint8_t v_isShared_5790_; uint8_t v_isSharedCheck_5803_; 
v_isSharedCheck_5803_ = !lean_is_exclusive(v___x_5787_);
if (v_isSharedCheck_5803_ == 0)
{
lean_object* v_unused_5804_; 
v_unused_5804_ = lean_ctor_get(v___x_5787_, 0);
lean_dec(v_unused_5804_);
v___x_5789_ = v___x_5787_;
v_isShared_5790_ = v_isSharedCheck_5803_;
goto v_resetjp_5788_;
}
else
{
lean_dec(v___x_5787_);
v___x_5789_ = lean_box(0);
v_isShared_5790_ = v_isSharedCheck_5803_;
goto v_resetjp_5788_;
}
v_resetjp_5788_:
{
lean_object* v___x_5791_; lean_object* v___x_5792_; lean_object* v___x_5794_; 
v___x_5791_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__8, &l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__8_once, _init_l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__8);
lean_inc(v_val_5772_);
v___x_5792_ = l_Nat_reprFast(v_val_5772_);
if (v_isShared_5790_ == 0)
{
lean_ctor_set_tag(v___x_5789_, 3);
lean_ctor_set(v___x_5789_, 0, v___x_5792_);
v___x_5794_ = v___x_5789_;
goto v_reusejp_5793_;
}
else
{
lean_object* v_reuseFailAlloc_5802_; 
v_reuseFailAlloc_5802_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5802_, 0, v___x_5792_);
v___x_5794_ = v_reuseFailAlloc_5802_;
goto v_reusejp_5793_;
}
v_reusejp_5793_:
{
lean_object* v___x_5795_; lean_object* v___x_5796_; lean_object* v___x_5797_; lean_object* v___x_5798_; lean_object* v___x_5799_; lean_object* v___x_5800_; lean_object* v___x_5801_; 
v___x_5795_ = l_Lean_MessageData_ofFormat(v___x_5794_);
v___x_5796_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5796_, 0, v___x_5791_);
lean_ctor_set(v___x_5796_, 1, v___x_5795_);
v___x_5797_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__6, &l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__6_once, _init_l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__6);
v___x_5798_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5798_, 0, v___x_5796_);
lean_ctor_set(v___x_5798_, 1, v___x_5797_);
lean_inc_ref(v_e_5614_);
v___x_5799_ = l_Lean_MessageData_ofExpr(v_e_5614_);
v___x_5800_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5800_, 0, v___x_5798_);
lean_ctor_set(v___x_5800_, 1, v___x_5799_);
v___x_5801_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0___redArg(v___x_5784_, v___x_5800_, v_a_5622_, v_a_5623_, v_a_5624_, v_a_5625_);
if (lean_obj_tag(v___x_5801_) == 0)
{
lean_dec_ref_known(v___x_5801_, 1);
v___y_5645_ = v___f_5783_;
v___y_5646_ = v_val_5772_;
v___y_5647_ = v_a_5616_;
v___y_5648_ = v_a_5617_;
v___y_5649_ = v_a_5618_;
v___y_5650_ = v_a_5619_;
v___y_5651_ = v_a_5620_;
v___y_5652_ = v_a_5621_;
v___y_5653_ = v_a_5622_;
v___y_5654_ = v_a_5623_;
v___y_5655_ = v_a_5624_;
v___y_5656_ = v_a_5625_;
goto v___jp_5644_;
}
else
{
lean_dec_ref(v___f_5783_);
lean_dec(v_val_5772_);
lean_dec_ref(v_e_5614_);
return v___x_5801_;
}
}
}
}
else
{
lean_dec_ref(v___f_5783_);
lean_dec(v_val_5772_);
lean_dec_ref(v_e_5614_);
return v___x_5787_;
}
}
}
}
else
{
lean_object* v___x_5805_; lean_object* v___x_5807_; 
lean_dec(v_a_5774_);
lean_dec(v_val_5772_);
lean_dec_ref(v_e_5614_);
v___x_5805_ = lean_box(0);
if (v_isShared_5777_ == 0)
{
lean_ctor_set(v___x_5776_, 0, v___x_5805_);
v___x_5807_ = v___x_5776_;
goto v_reusejp_5806_;
}
else
{
lean_object* v_reuseFailAlloc_5808_; 
v_reuseFailAlloc_5808_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5808_, 0, v___x_5805_);
v___x_5807_ = v_reuseFailAlloc_5808_;
goto v_reusejp_5806_;
}
v_reusejp_5806_:
{
return v___x_5807_;
}
}
}
}
else
{
lean_object* v_a_5810_; lean_object* v___x_5812_; uint8_t v_isShared_5813_; uint8_t v_isSharedCheck_5817_; 
lean_dec(v_val_5772_);
lean_dec_ref(v_e_5614_);
v_a_5810_ = lean_ctor_get(v___x_5773_, 0);
v_isSharedCheck_5817_ = !lean_is_exclusive(v___x_5773_);
if (v_isSharedCheck_5817_ == 0)
{
v___x_5812_ = v___x_5773_;
v_isShared_5813_ = v_isSharedCheck_5817_;
goto v_resetjp_5811_;
}
else
{
lean_inc(v_a_5810_);
lean_dec(v___x_5773_);
v___x_5812_ = lean_box(0);
v_isShared_5813_ = v_isSharedCheck_5817_;
goto v_resetjp_5811_;
}
v_resetjp_5811_:
{
lean_object* v___x_5815_; 
if (v_isShared_5813_ == 0)
{
v___x_5815_ = v___x_5812_;
goto v_reusejp_5814_;
}
else
{
lean_object* v_reuseFailAlloc_5816_; 
v_reuseFailAlloc_5816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5816_, 0, v_a_5810_);
v___x_5815_ = v_reuseFailAlloc_5816_;
goto v_reusejp_5814_;
}
v_reusejp_5814_:
{
return v___x_5815_;
}
}
}
}
else
{
lean_object* v___x_5818_; 
lean_dec(v_a_5771_);
lean_inc(v_val_5718_);
v___x_5818_ = l_Lean_Meta_Grind_Arith_CommRing_getNonCommRingId_x3f___redArg(v_val_5718_, v_a_5620_, v_a_5621_, v_a_5622_, v_a_5623_, v_a_5624_, v_a_5625_);
if (lean_obj_tag(v___x_5818_) == 0)
{
lean_object* v_a_5819_; 
v_a_5819_ = lean_ctor_get(v___x_5818_, 0);
lean_inc(v_a_5819_);
lean_dec_ref_known(v___x_5818_, 1);
if (lean_obj_tag(v_a_5819_) == 1)
{
lean_object* v_val_5820_; lean_object* v___x_5821_; 
lean_dec(v_val_5718_);
v_val_5820_ = lean_ctor_get(v_a_5819_, 0);
lean_inc(v_val_5820_);
lean_dec_ref_known(v_a_5819_, 1);
lean_inc_ref(v_e_5614_);
v___x_5821_ = l_Lean_Meta_Grind_Arith_CommRing_ncreify_x3f(v_e_5614_, v_ring_5701_, v_val_5820_, v_a_5616_, v_a_5617_, v_a_5618_, v_a_5619_, v_a_5620_, v_a_5621_, v_a_5622_, v_a_5623_, v_a_5624_, v_a_5625_);
if (lean_obj_tag(v___x_5821_) == 0)
{
lean_object* v_a_5822_; lean_object* v___x_5824_; uint8_t v_isShared_5825_; uint8_t v_isSharedCheck_5857_; 
v_a_5822_ = lean_ctor_get(v___x_5821_, 0);
v_isSharedCheck_5857_ = !lean_is_exclusive(v___x_5821_);
if (v_isSharedCheck_5857_ == 0)
{
v___x_5824_ = v___x_5821_;
v_isShared_5825_ = v_isSharedCheck_5857_;
goto v_resetjp_5823_;
}
else
{
lean_inc(v_a_5822_);
lean_dec(v___x_5821_);
v___x_5824_ = lean_box(0);
v_isShared_5825_ = v_isSharedCheck_5857_;
goto v_resetjp_5823_;
}
v_resetjp_5823_:
{
if (lean_obj_tag(v_a_5822_) == 1)
{
lean_object* v_toCold_5826_; lean_object* v_options_5827_; lean_object* v_val_5828_; lean_object* v_inheritedTraceOptions_5829_; uint8_t v_hasTrace_5830_; lean_object* v___f_5831_; 
lean_del_object(v___x_5824_);
v_toCold_5826_ = lean_ctor_get(v_a_5624_, 0);
v_options_5827_ = lean_ctor_get(v_toCold_5826_, 2);
v_val_5828_ = lean_ctor_get(v_a_5822_, 0);
lean_inc(v_val_5828_);
lean_dec_ref_known(v_a_5822_, 1);
v_inheritedTraceOptions_5829_ = lean_ctor_get(v_toCold_5826_, 11);
v_hasTrace_5830_ = lean_ctor_get_uint8(v_options_5827_, sizeof(void*)*1);
lean_inc_ref(v_e_5614_);
v___f_5831_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_internalize___lam__2), 3, 2);
lean_closure_set(v___f_5831_, 0, v_e_5614_);
lean_closure_set(v___f_5831_, 1, v_val_5828_);
if (v_hasTrace_5830_ == 0)
{
v___y_5680_ = v___f_5831_;
v___y_5681_ = v_val_5820_;
v___y_5682_ = v_a_5616_;
v___y_5683_ = v_a_5617_;
v___y_5684_ = v_a_5618_;
v___y_5685_ = v_a_5619_;
v___y_5686_ = v_a_5620_;
v___y_5687_ = v_a_5621_;
v___y_5688_ = v_a_5622_;
v___y_5689_ = v_a_5623_;
v___y_5690_ = v_a_5624_;
v___y_5691_ = v_a_5625_;
goto v___jp_5679_;
}
else
{
lean_object* v___x_5832_; lean_object* v___x_5833_; uint8_t v___x_5834_; 
v___x_5832_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__1));
v___x_5833_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__2, &l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__2_once, _init_l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__2);
v___x_5834_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5829_, v_options_5827_, v___x_5833_);
if (v___x_5834_ == 0)
{
v___y_5680_ = v___f_5831_;
v___y_5681_ = v_val_5820_;
v___y_5682_ = v_a_5616_;
v___y_5683_ = v_a_5617_;
v___y_5684_ = v_a_5618_;
v___y_5685_ = v_a_5619_;
v___y_5686_ = v_a_5620_;
v___y_5687_ = v_a_5621_;
v___y_5688_ = v_a_5622_;
v___y_5689_ = v_a_5623_;
v___y_5690_ = v_a_5624_;
v___y_5691_ = v_a_5625_;
goto v___jp_5679_;
}
else
{
lean_object* v___x_5835_; 
v___x_5835_ = l_Lean_Meta_Grind_updateLastTag(v_a_5616_, v_a_5617_, v_a_5618_, v_a_5619_, v_a_5620_, v_a_5621_, v_a_5622_, v_a_5623_, v_a_5624_, v_a_5625_);
if (lean_obj_tag(v___x_5835_) == 0)
{
lean_object* v___x_5837_; uint8_t v_isShared_5838_; uint8_t v_isSharedCheck_5851_; 
v_isSharedCheck_5851_ = !lean_is_exclusive(v___x_5835_);
if (v_isSharedCheck_5851_ == 0)
{
lean_object* v_unused_5852_; 
v_unused_5852_ = lean_ctor_get(v___x_5835_, 0);
lean_dec(v_unused_5852_);
v___x_5837_ = v___x_5835_;
v_isShared_5838_ = v_isSharedCheck_5851_;
goto v_resetjp_5836_;
}
else
{
lean_dec(v___x_5835_);
v___x_5837_ = lean_box(0);
v_isShared_5838_ = v_isSharedCheck_5851_;
goto v_resetjp_5836_;
}
v_resetjp_5836_:
{
lean_object* v___x_5839_; lean_object* v___x_5840_; lean_object* v___x_5842_; 
v___x_5839_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__10, &l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__10_once, _init_l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__10);
lean_inc(v_val_5820_);
v___x_5840_ = l_Nat_reprFast(v_val_5820_);
if (v_isShared_5838_ == 0)
{
lean_ctor_set_tag(v___x_5837_, 3);
lean_ctor_set(v___x_5837_, 0, v___x_5840_);
v___x_5842_ = v___x_5837_;
goto v_reusejp_5841_;
}
else
{
lean_object* v_reuseFailAlloc_5850_; 
v_reuseFailAlloc_5850_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5850_, 0, v___x_5840_);
v___x_5842_ = v_reuseFailAlloc_5850_;
goto v_reusejp_5841_;
}
v_reusejp_5841_:
{
lean_object* v___x_5843_; lean_object* v___x_5844_; lean_object* v___x_5845_; lean_object* v___x_5846_; lean_object* v___x_5847_; lean_object* v___x_5848_; lean_object* v___x_5849_; 
v___x_5843_ = l_Lean_MessageData_ofFormat(v___x_5842_);
v___x_5844_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5844_, 0, v___x_5839_);
lean_ctor_set(v___x_5844_, 1, v___x_5843_);
v___x_5845_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__6, &l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__6_once, _init_l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__6);
v___x_5846_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5846_, 0, v___x_5844_);
lean_ctor_set(v___x_5846_, 1, v___x_5845_);
lean_inc_ref(v_e_5614_);
v___x_5847_ = l_Lean_MessageData_ofExpr(v_e_5614_);
v___x_5848_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5848_, 0, v___x_5846_);
lean_ctor_set(v___x_5848_, 1, v___x_5847_);
v___x_5849_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__1___redArg(v___x_5832_, v___x_5848_, v_a_5622_, v_a_5623_, v_a_5624_, v_a_5625_);
if (lean_obj_tag(v___x_5849_) == 0)
{
lean_dec_ref_known(v___x_5849_, 1);
v___y_5680_ = v___f_5831_;
v___y_5681_ = v_val_5820_;
v___y_5682_ = v_a_5616_;
v___y_5683_ = v_a_5617_;
v___y_5684_ = v_a_5618_;
v___y_5685_ = v_a_5619_;
v___y_5686_ = v_a_5620_;
v___y_5687_ = v_a_5621_;
v___y_5688_ = v_a_5622_;
v___y_5689_ = v_a_5623_;
v___y_5690_ = v_a_5624_;
v___y_5691_ = v_a_5625_;
goto v___jp_5679_;
}
else
{
lean_dec_ref(v___f_5831_);
lean_dec(v_val_5820_);
lean_dec_ref(v_e_5614_);
return v___x_5849_;
}
}
}
}
else
{
lean_dec_ref(v___f_5831_);
lean_dec(v_val_5820_);
lean_dec_ref(v_e_5614_);
return v___x_5835_;
}
}
}
}
else
{
lean_object* v___x_5853_; lean_object* v___x_5855_; 
lean_dec(v_a_5822_);
lean_dec(v_val_5820_);
lean_dec_ref(v_e_5614_);
v___x_5853_ = lean_box(0);
if (v_isShared_5825_ == 0)
{
lean_ctor_set(v___x_5824_, 0, v___x_5853_);
v___x_5855_ = v___x_5824_;
goto v_reusejp_5854_;
}
else
{
lean_object* v_reuseFailAlloc_5856_; 
v_reuseFailAlloc_5856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5856_, 0, v___x_5853_);
v___x_5855_ = v_reuseFailAlloc_5856_;
goto v_reusejp_5854_;
}
v_reusejp_5854_:
{
return v___x_5855_;
}
}
}
}
else
{
lean_object* v_a_5858_; lean_object* v___x_5860_; uint8_t v_isShared_5861_; uint8_t v_isSharedCheck_5865_; 
lean_dec(v_val_5820_);
lean_dec_ref(v_e_5614_);
v_a_5858_ = lean_ctor_get(v___x_5821_, 0);
v_isSharedCheck_5865_ = !lean_is_exclusive(v___x_5821_);
if (v_isSharedCheck_5865_ == 0)
{
v___x_5860_ = v___x_5821_;
v_isShared_5861_ = v_isSharedCheck_5865_;
goto v_resetjp_5859_;
}
else
{
lean_inc(v_a_5858_);
lean_dec(v___x_5821_);
v___x_5860_ = lean_box(0);
v_isShared_5861_ = v_isSharedCheck_5865_;
goto v_resetjp_5859_;
}
v_resetjp_5859_:
{
lean_object* v___x_5863_; 
if (v_isShared_5861_ == 0)
{
v___x_5863_ = v___x_5860_;
goto v_reusejp_5862_;
}
else
{
lean_object* v_reuseFailAlloc_5864_; 
v_reuseFailAlloc_5864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5864_, 0, v_a_5858_);
v___x_5863_ = v_reuseFailAlloc_5864_;
goto v_reusejp_5862_;
}
v_reusejp_5862_:
{
return v___x_5863_;
}
}
}
}
else
{
lean_object* v___x_5866_; 
lean_dec(v_a_5819_);
v___x_5866_ = l_Lean_Meta_Grind_Arith_CommRing_getNonCommSemiringId_x3f___redArg(v_val_5718_, v_a_5620_, v_a_5621_, v_a_5622_, v_a_5623_, v_a_5624_, v_a_5625_);
if (lean_obj_tag(v___x_5866_) == 0)
{
lean_object* v_a_5867_; lean_object* v___x_5869_; uint8_t v_isShared_5870_; uint8_t v_isSharedCheck_5921_; 
v_a_5867_ = lean_ctor_get(v___x_5866_, 0);
v_isSharedCheck_5921_ = !lean_is_exclusive(v___x_5866_);
if (v_isSharedCheck_5921_ == 0)
{
v___x_5869_ = v___x_5866_;
v_isShared_5870_ = v_isSharedCheck_5921_;
goto v_resetjp_5868_;
}
else
{
lean_inc(v_a_5867_);
lean_dec(v___x_5866_);
v___x_5869_ = lean_box(0);
v_isShared_5870_ = v_isSharedCheck_5921_;
goto v_resetjp_5868_;
}
v_resetjp_5868_:
{
if (lean_obj_tag(v_a_5867_) == 1)
{
lean_object* v_val_5871_; lean_object* v___x_5872_; 
lean_del_object(v___x_5869_);
v_val_5871_ = lean_ctor_get(v_a_5867_, 0);
lean_inc(v_val_5871_);
lean_dec_ref_known(v_a_5867_, 1);
lean_inc_ref(v_e_5614_);
v___x_5872_ = l_Lean_Meta_Grind_Arith_CommRing_ncsreify_x3f(v_e_5614_, v_val_5871_, v_a_5616_, v_a_5617_, v_a_5618_, v_a_5619_, v_a_5620_, v_a_5621_, v_a_5622_, v_a_5623_, v_a_5624_, v_a_5625_);
if (lean_obj_tag(v___x_5872_) == 0)
{
lean_object* v_a_5873_; lean_object* v___x_5875_; uint8_t v_isShared_5876_; uint8_t v_isSharedCheck_5908_; 
v_a_5873_ = lean_ctor_get(v___x_5872_, 0);
v_isSharedCheck_5908_ = !lean_is_exclusive(v___x_5872_);
if (v_isSharedCheck_5908_ == 0)
{
v___x_5875_ = v___x_5872_;
v_isShared_5876_ = v_isSharedCheck_5908_;
goto v_resetjp_5874_;
}
else
{
lean_inc(v_a_5873_);
lean_dec(v___x_5872_);
v___x_5875_ = lean_box(0);
v_isShared_5876_ = v_isSharedCheck_5908_;
goto v_resetjp_5874_;
}
v_resetjp_5874_:
{
if (lean_obj_tag(v_a_5873_) == 1)
{
lean_object* v_toCold_5877_; lean_object* v_options_5878_; lean_object* v_val_5879_; lean_object* v_inheritedTraceOptions_5880_; uint8_t v_hasTrace_5881_; lean_object* v___f_5882_; 
lean_del_object(v___x_5875_);
v_toCold_5877_ = lean_ctor_get(v_a_5624_, 0);
v_options_5878_ = lean_ctor_get(v_toCold_5877_, 2);
v_val_5879_ = lean_ctor_get(v_a_5873_, 0);
lean_inc(v_val_5879_);
lean_dec_ref_known(v_a_5873_, 1);
v_inheritedTraceOptions_5880_ = lean_ctor_get(v_toCold_5877_, 11);
v_hasTrace_5881_ = lean_ctor_get_uint8(v_options_5878_, sizeof(void*)*1);
lean_inc_ref(v_e_5614_);
v___f_5882_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_internalize___lam__1), 3, 2);
lean_closure_set(v___f_5882_, 0, v_e_5614_);
lean_closure_set(v___f_5882_, 1, v_val_5879_);
if (v_hasTrace_5881_ == 0)
{
v___y_5628_ = v___f_5882_;
v___y_5629_ = v_val_5871_;
v___y_5630_ = v_a_5616_;
v___y_5631_ = v_a_5617_;
v___y_5632_ = v_a_5618_;
v___y_5633_ = v_a_5619_;
v___y_5634_ = v_a_5620_;
v___y_5635_ = v_a_5621_;
v___y_5636_ = v_a_5622_;
v___y_5637_ = v_a_5623_;
v___y_5638_ = v_a_5624_;
v___y_5639_ = v_a_5625_;
goto v___jp_5627_;
}
else
{
lean_object* v___x_5883_; lean_object* v___x_5884_; uint8_t v___x_5885_; 
v___x_5883_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__1));
v___x_5884_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__2, &l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__2_once, _init_l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__2);
v___x_5885_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5880_, v_options_5878_, v___x_5884_);
if (v___x_5885_ == 0)
{
v___y_5628_ = v___f_5882_;
v___y_5629_ = v_val_5871_;
v___y_5630_ = v_a_5616_;
v___y_5631_ = v_a_5617_;
v___y_5632_ = v_a_5618_;
v___y_5633_ = v_a_5619_;
v___y_5634_ = v_a_5620_;
v___y_5635_ = v_a_5621_;
v___y_5636_ = v_a_5622_;
v___y_5637_ = v_a_5623_;
v___y_5638_ = v_a_5624_;
v___y_5639_ = v_a_5625_;
goto v___jp_5627_;
}
else
{
lean_object* v___x_5886_; 
v___x_5886_ = l_Lean_Meta_Grind_updateLastTag(v_a_5616_, v_a_5617_, v_a_5618_, v_a_5619_, v_a_5620_, v_a_5621_, v_a_5622_, v_a_5623_, v_a_5624_, v_a_5625_);
if (lean_obj_tag(v___x_5886_) == 0)
{
lean_object* v___x_5888_; uint8_t v_isShared_5889_; uint8_t v_isSharedCheck_5902_; 
v_isSharedCheck_5902_ = !lean_is_exclusive(v___x_5886_);
if (v_isSharedCheck_5902_ == 0)
{
lean_object* v_unused_5903_; 
v_unused_5903_ = lean_ctor_get(v___x_5886_, 0);
lean_dec(v_unused_5903_);
v___x_5888_ = v___x_5886_;
v_isShared_5889_ = v_isSharedCheck_5902_;
goto v_resetjp_5887_;
}
else
{
lean_dec(v___x_5886_);
v___x_5888_ = lean_box(0);
v_isShared_5889_ = v_isSharedCheck_5902_;
goto v_resetjp_5887_;
}
v_resetjp_5887_:
{
lean_object* v___x_5890_; lean_object* v___x_5891_; lean_object* v___x_5893_; 
v___x_5890_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__12, &l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__12_once, _init_l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__12);
lean_inc(v_val_5871_);
v___x_5891_ = l_Nat_reprFast(v_val_5871_);
if (v_isShared_5889_ == 0)
{
lean_ctor_set_tag(v___x_5888_, 3);
lean_ctor_set(v___x_5888_, 0, v___x_5891_);
v___x_5893_ = v___x_5888_;
goto v_reusejp_5892_;
}
else
{
lean_object* v_reuseFailAlloc_5901_; 
v_reuseFailAlloc_5901_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5901_, 0, v___x_5891_);
v___x_5893_ = v_reuseFailAlloc_5901_;
goto v_reusejp_5892_;
}
v_reusejp_5892_:
{
lean_object* v___x_5894_; lean_object* v___x_5895_; lean_object* v___x_5896_; lean_object* v___x_5897_; lean_object* v___x_5898_; lean_object* v___x_5899_; lean_object* v___x_5900_; 
v___x_5894_ = l_Lean_MessageData_ofFormat(v___x_5893_);
v___x_5895_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5895_, 0, v___x_5890_);
lean_ctor_set(v___x_5895_, 1, v___x_5894_);
v___x_5896_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__6, &l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__6_once, _init_l_Lean_Meta_Grind_Arith_CommRing_internalize___closed__6);
v___x_5897_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5897_, 0, v___x_5895_);
lean_ctor_set(v___x_5897_, 1, v___x_5896_);
lean_inc_ref(v_e_5614_);
v___x_5898_ = l_Lean_MessageData_ofExpr(v_e_5614_);
v___x_5899_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5899_, 0, v___x_5897_);
lean_ctor_set(v___x_5899_, 1, v___x_5898_);
v___x_5900_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__2___redArg(v___x_5883_, v___x_5899_, v_a_5622_, v_a_5623_, v_a_5624_, v_a_5625_);
if (lean_obj_tag(v___x_5900_) == 0)
{
lean_dec_ref_known(v___x_5900_, 1);
v___y_5628_ = v___f_5882_;
v___y_5629_ = v_val_5871_;
v___y_5630_ = v_a_5616_;
v___y_5631_ = v_a_5617_;
v___y_5632_ = v_a_5618_;
v___y_5633_ = v_a_5619_;
v___y_5634_ = v_a_5620_;
v___y_5635_ = v_a_5621_;
v___y_5636_ = v_a_5622_;
v___y_5637_ = v_a_5623_;
v___y_5638_ = v_a_5624_;
v___y_5639_ = v_a_5625_;
goto v___jp_5627_;
}
else
{
lean_dec_ref(v___f_5882_);
lean_dec(v_val_5871_);
lean_dec_ref(v_e_5614_);
return v___x_5900_;
}
}
}
}
else
{
lean_dec_ref(v___f_5882_);
lean_dec(v_val_5871_);
lean_dec_ref(v_e_5614_);
return v___x_5886_;
}
}
}
}
else
{
lean_object* v___x_5904_; lean_object* v___x_5906_; 
lean_dec(v_a_5873_);
lean_dec(v_val_5871_);
lean_dec_ref(v_e_5614_);
v___x_5904_ = lean_box(0);
if (v_isShared_5876_ == 0)
{
lean_ctor_set(v___x_5875_, 0, v___x_5904_);
v___x_5906_ = v___x_5875_;
goto v_reusejp_5905_;
}
else
{
lean_object* v_reuseFailAlloc_5907_; 
v_reuseFailAlloc_5907_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5907_, 0, v___x_5904_);
v___x_5906_ = v_reuseFailAlloc_5907_;
goto v_reusejp_5905_;
}
v_reusejp_5905_:
{
return v___x_5906_;
}
}
}
}
else
{
lean_object* v_a_5909_; lean_object* v___x_5911_; uint8_t v_isShared_5912_; uint8_t v_isSharedCheck_5916_; 
lean_dec(v_val_5871_);
lean_dec_ref(v_e_5614_);
v_a_5909_ = lean_ctor_get(v___x_5872_, 0);
v_isSharedCheck_5916_ = !lean_is_exclusive(v___x_5872_);
if (v_isSharedCheck_5916_ == 0)
{
v___x_5911_ = v___x_5872_;
v_isShared_5912_ = v_isSharedCheck_5916_;
goto v_resetjp_5910_;
}
else
{
lean_inc(v_a_5909_);
lean_dec(v___x_5872_);
v___x_5911_ = lean_box(0);
v_isShared_5912_ = v_isSharedCheck_5916_;
goto v_resetjp_5910_;
}
v_resetjp_5910_:
{
lean_object* v___x_5914_; 
if (v_isShared_5912_ == 0)
{
v___x_5914_ = v___x_5911_;
goto v_reusejp_5913_;
}
else
{
lean_object* v_reuseFailAlloc_5915_; 
v_reuseFailAlloc_5915_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5915_, 0, v_a_5909_);
v___x_5914_ = v_reuseFailAlloc_5915_;
goto v_reusejp_5913_;
}
v_reusejp_5913_:
{
return v___x_5914_;
}
}
}
}
else
{
lean_object* v___x_5917_; lean_object* v___x_5919_; 
lean_dec(v_a_5867_);
lean_dec_ref(v_e_5614_);
v___x_5917_ = lean_box(0);
if (v_isShared_5870_ == 0)
{
lean_ctor_set(v___x_5869_, 0, v___x_5917_);
v___x_5919_ = v___x_5869_;
goto v_reusejp_5918_;
}
else
{
lean_object* v_reuseFailAlloc_5920_; 
v_reuseFailAlloc_5920_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5920_, 0, v___x_5917_);
v___x_5919_ = v_reuseFailAlloc_5920_;
goto v_reusejp_5918_;
}
v_reusejp_5918_:
{
return v___x_5919_;
}
}
}
}
else
{
lean_object* v_a_5922_; lean_object* v___x_5924_; uint8_t v_isShared_5925_; uint8_t v_isSharedCheck_5929_; 
lean_dec_ref(v_e_5614_);
v_a_5922_ = lean_ctor_get(v___x_5866_, 0);
v_isSharedCheck_5929_ = !lean_is_exclusive(v___x_5866_);
if (v_isSharedCheck_5929_ == 0)
{
v___x_5924_ = v___x_5866_;
v_isShared_5925_ = v_isSharedCheck_5929_;
goto v_resetjp_5923_;
}
else
{
lean_inc(v_a_5922_);
lean_dec(v___x_5866_);
v___x_5924_ = lean_box(0);
v_isShared_5925_ = v_isSharedCheck_5929_;
goto v_resetjp_5923_;
}
v_resetjp_5923_:
{
lean_object* v___x_5927_; 
if (v_isShared_5925_ == 0)
{
v___x_5927_ = v___x_5924_;
goto v_reusejp_5926_;
}
else
{
lean_object* v_reuseFailAlloc_5928_; 
v_reuseFailAlloc_5928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5928_, 0, v_a_5922_);
v___x_5927_ = v_reuseFailAlloc_5928_;
goto v_reusejp_5926_;
}
v_reusejp_5926_:
{
return v___x_5927_;
}
}
}
}
}
else
{
lean_object* v_a_5930_; lean_object* v___x_5932_; uint8_t v_isShared_5933_; uint8_t v_isSharedCheck_5937_; 
lean_dec(v_val_5718_);
lean_dec_ref(v_e_5614_);
v_a_5930_ = lean_ctor_get(v___x_5818_, 0);
v_isSharedCheck_5937_ = !lean_is_exclusive(v___x_5818_);
if (v_isSharedCheck_5937_ == 0)
{
v___x_5932_ = v___x_5818_;
v_isShared_5933_ = v_isSharedCheck_5937_;
goto v_resetjp_5931_;
}
else
{
lean_inc(v_a_5930_);
lean_dec(v___x_5818_);
v___x_5932_ = lean_box(0);
v_isShared_5933_ = v_isSharedCheck_5937_;
goto v_resetjp_5931_;
}
v_resetjp_5931_:
{
lean_object* v___x_5935_; 
if (v_isShared_5933_ == 0)
{
v___x_5935_ = v___x_5932_;
goto v_reusejp_5934_;
}
else
{
lean_object* v_reuseFailAlloc_5936_; 
v_reuseFailAlloc_5936_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5936_, 0, v_a_5930_);
v___x_5935_ = v_reuseFailAlloc_5936_;
goto v_reusejp_5934_;
}
v_reusejp_5934_:
{
return v___x_5935_;
}
}
}
}
}
else
{
lean_object* v_a_5938_; lean_object* v___x_5940_; uint8_t v_isShared_5941_; uint8_t v_isSharedCheck_5945_; 
lean_dec(v_val_5718_);
lean_dec_ref(v_e_5614_);
v_a_5938_ = lean_ctor_get(v___x_5770_, 0);
v_isSharedCheck_5945_ = !lean_is_exclusive(v___x_5770_);
if (v_isSharedCheck_5945_ == 0)
{
v___x_5940_ = v___x_5770_;
v_isShared_5941_ = v_isSharedCheck_5945_;
goto v_resetjp_5939_;
}
else
{
lean_inc(v_a_5938_);
lean_dec(v___x_5770_);
v___x_5940_ = lean_box(0);
v_isShared_5941_ = v_isSharedCheck_5945_;
goto v_resetjp_5939_;
}
v_resetjp_5939_:
{
lean_object* v___x_5943_; 
if (v_isShared_5941_ == 0)
{
v___x_5943_ = v___x_5940_;
goto v_reusejp_5942_;
}
else
{
lean_object* v_reuseFailAlloc_5944_; 
v_reuseFailAlloc_5944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5944_, 0, v_a_5938_);
v___x_5943_ = v_reuseFailAlloc_5944_;
goto v_reusejp_5942_;
}
v_reusejp_5942_:
{
return v___x_5943_;
}
}
}
}
}
else
{
lean_object* v_a_5946_; lean_object* v___x_5948_; uint8_t v_isShared_5949_; uint8_t v_isSharedCheck_5953_; 
lean_dec(v_val_5718_);
lean_dec_ref(v_e_5614_);
v_a_5946_ = lean_ctor_get(v___x_5721_, 0);
v_isSharedCheck_5953_ = !lean_is_exclusive(v___x_5721_);
if (v_isSharedCheck_5953_ == 0)
{
v___x_5948_ = v___x_5721_;
v_isShared_5949_ = v_isSharedCheck_5953_;
goto v_resetjp_5947_;
}
else
{
lean_inc(v_a_5946_);
lean_dec(v___x_5721_);
v___x_5948_ = lean_box(0);
v_isShared_5949_ = v_isSharedCheck_5953_;
goto v_resetjp_5947_;
}
v_resetjp_5947_:
{
lean_object* v___x_5951_; 
if (v_isShared_5949_ == 0)
{
v___x_5951_ = v___x_5948_;
goto v_reusejp_5950_;
}
else
{
lean_object* v_reuseFailAlloc_5952_; 
v_reuseFailAlloc_5952_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5952_, 0, v_a_5946_);
v___x_5951_ = v_reuseFailAlloc_5952_;
goto v_reusejp_5950_;
}
v_reusejp_5950_:
{
return v___x_5951_;
}
}
}
}
}
else
{
lean_object* v___x_5980_; lean_object* v___x_5982_; 
lean_dec(v___x_5717_);
lean_dec_ref(v_e_5614_);
v___x_5980_ = lean_box(0);
if (v_isShared_5716_ == 0)
{
lean_ctor_set(v___x_5715_, 0, v___x_5980_);
v___x_5982_ = v___x_5715_;
goto v_reusejp_5981_;
}
else
{
lean_object* v_reuseFailAlloc_5983_; 
v_reuseFailAlloc_5983_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5983_, 0, v___x_5980_);
v___x_5982_ = v_reuseFailAlloc_5983_;
goto v_reusejp_5981_;
}
v_reusejp_5981_:
{
return v___x_5982_;
}
}
}
}
else
{
lean_dec_ref(v_e_5614_);
return v___x_5713_;
}
}
else
{
lean_object* v___x_5986_; lean_object* v___x_5988_; 
lean_dec_ref(v_e_5614_);
v___x_5986_ = lean_box(0);
if (v_isShared_5711_ == 0)
{
lean_ctor_set(v___x_5710_, 0, v___x_5986_);
v___x_5988_ = v___x_5710_;
goto v_reusejp_5987_;
}
else
{
lean_object* v_reuseFailAlloc_5989_; 
v_reuseFailAlloc_5989_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5989_, 0, v___x_5986_);
v___x_5988_ = v_reuseFailAlloc_5989_;
goto v_reusejp_5987_;
}
v_reusejp_5987_:
{
return v___x_5988_;
}
}
}
}
else
{
lean_object* v_a_5991_; lean_object* v___x_5993_; uint8_t v_isShared_5994_; uint8_t v_isSharedCheck_5998_; 
lean_dec_ref(v_e_5614_);
v_a_5991_ = lean_ctor_get(v___x_5707_, 0);
v_isSharedCheck_5998_ = !lean_is_exclusive(v___x_5707_);
if (v_isSharedCheck_5998_ == 0)
{
v___x_5993_ = v___x_5707_;
v_isShared_5994_ = v_isSharedCheck_5998_;
goto v_resetjp_5992_;
}
else
{
lean_inc(v_a_5991_);
lean_dec(v___x_5707_);
v___x_5993_ = lean_box(0);
v_isShared_5994_ = v_isSharedCheck_5998_;
goto v_resetjp_5992_;
}
v_resetjp_5992_:
{
lean_object* v___x_5996_; 
if (v_isShared_5994_ == 0)
{
v___x_5996_ = v___x_5993_;
goto v_reusejp_5995_;
}
else
{
lean_object* v_reuseFailAlloc_5997_; 
v_reuseFailAlloc_5997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5997_, 0, v_a_5991_);
v___x_5996_ = v_reuseFailAlloc_5997_;
goto v_reusejp_5995_;
}
v_reusejp_5995_:
{
return v___x_5996_;
}
}
}
}
else
{
lean_object* v___x_5999_; lean_object* v___x_6001_; 
lean_dec_ref(v_e_5614_);
v___x_5999_ = lean_box(0);
if (v_isShared_5700_ == 0)
{
lean_ctor_set(v___x_5699_, 0, v___x_5999_);
v___x_6001_ = v___x_5699_;
goto v_reusejp_6000_;
}
else
{
lean_object* v_reuseFailAlloc_6002_; 
v_reuseFailAlloc_6002_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6002_, 0, v___x_5999_);
v___x_6001_ = v_reuseFailAlloc_6002_;
goto v_reusejp_6000_;
}
v_reusejp_6000_:
{
return v___x_6001_;
}
}
}
}
}
else
{
lean_object* v_a_6004_; lean_object* v___x_6006_; uint8_t v_isShared_6007_; uint8_t v_isSharedCheck_6011_; 
lean_dec_ref(v_e_5614_);
v_a_6004_ = lean_ctor_get(v___x_5696_, 0);
v_isSharedCheck_6011_ = !lean_is_exclusive(v___x_5696_);
if (v_isSharedCheck_6011_ == 0)
{
v___x_6006_ = v___x_5696_;
v_isShared_6007_ = v_isSharedCheck_6011_;
goto v_resetjp_6005_;
}
else
{
lean_inc(v_a_6004_);
lean_dec(v___x_5696_);
v___x_6006_ = lean_box(0);
v_isShared_6007_ = v_isSharedCheck_6011_;
goto v_resetjp_6005_;
}
v_resetjp_6005_:
{
lean_object* v___x_6009_; 
if (v_isShared_6007_ == 0)
{
v___x_6009_ = v___x_6006_;
goto v_reusejp_6008_;
}
else
{
lean_object* v_reuseFailAlloc_6010_; 
v_reuseFailAlloc_6010_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6010_, 0, v_a_6004_);
v___x_6009_ = v_reuseFailAlloc_6010_;
goto v_reusejp_6008_;
}
v_reusejp_6008_:
{
return v___x_6009_;
}
}
}
v___jp_5627_:
{
lean_object* v___x_5640_; 
lean_inc_ref(v_e_5614_);
v___x_5640_ = l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommSemiringId___redArg(v_e_5614_, v___y_5629_, v___y_5630_, v___y_5634_, v___y_5635_, v___y_5636_, v___y_5637_, v___y_5638_, v___y_5639_);
if (lean_obj_tag(v___x_5640_) == 0)
{
lean_object* v___x_5641_; lean_object* v___x_5642_; 
lean_dec_ref_known(v___x_5640_, 1);
v___x_5641_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_5642_ = l_Lean_Meta_Grind_SolverExtension_markTerm___redArg(v___x_5641_, v_e_5614_, v___y_5630_, v___y_5631_, v___y_5632_, v___y_5633_, v___y_5634_, v___y_5635_, v___y_5636_, v___y_5637_, v___y_5638_, v___y_5639_);
if (lean_obj_tag(v___x_5642_) == 0)
{
lean_object* v___x_5643_; 
lean_dec_ref_known(v___x_5642_, 1);
v___x_5643_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommSemiringM_modifySemiringState___redArg(v___y_5628_, v___y_5629_, v___y_5630_);
lean_dec(v___y_5629_);
return v___x_5643_;
}
else
{
lean_dec(v___y_5629_);
lean_dec_ref(v___y_5628_);
return v___x_5642_;
}
}
else
{
lean_dec(v___y_5629_);
lean_dec_ref(v___y_5628_);
lean_dec_ref(v_e_5614_);
return v___x_5640_;
}
}
v___jp_5644_:
{
lean_object* v___x_5657_; 
lean_inc_ref(v_e_5614_);
v___x_5657_ = l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId___redArg(v_e_5614_, v___y_5646_, v___y_5647_, v___y_5651_, v___y_5652_, v___y_5653_, v___y_5654_, v___y_5655_, v___y_5656_);
if (lean_obj_tag(v___x_5657_) == 0)
{
lean_object* v___x_5658_; lean_object* v___x_5659_; 
lean_dec_ref_known(v___x_5657_, 1);
v___x_5658_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_5659_ = l_Lean_Meta_Grind_SolverExtension_markTerm___redArg(v___x_5658_, v_e_5614_, v___y_5647_, v___y_5648_, v___y_5649_, v___y_5650_, v___y_5651_, v___y_5652_, v___y_5653_, v___y_5654_, v___y_5655_, v___y_5656_);
if (lean_obj_tag(v___x_5659_) == 0)
{
lean_object* v___x_5660_; 
lean_dec_ref_known(v___x_5659_, 1);
v___x_5660_ = l_Lean_Meta_Grind_Arith_CommRing_SemiringM_modifySemiringState___redArg(v___y_5645_, v___y_5646_, v___y_5647_);
lean_dec(v___y_5646_);
return v___x_5660_;
}
else
{
lean_dec(v___y_5646_);
lean_dec_ref(v___y_5645_);
return v___x_5659_;
}
}
else
{
lean_dec(v___y_5646_);
lean_dec_ref(v___y_5645_);
lean_dec_ref(v_e_5614_);
return v___x_5657_;
}
}
v___jp_5661_:
{
lean_object* v___x_5674_; 
lean_inc_ref(v_e_5614_);
v___x_5674_ = l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg(v_e_5614_, v___y_5663_, v___y_5664_, v___y_5668_, v___y_5669_, v___y_5670_, v___y_5671_, v___y_5672_, v___y_5673_);
if (lean_obj_tag(v___x_5674_) == 0)
{
lean_object* v___x_5675_; lean_object* v___x_5676_; 
lean_dec_ref_known(v___x_5674_, 1);
v___x_5675_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_5676_ = l_Lean_Meta_Grind_SolverExtension_markTerm___redArg(v___x_5675_, v_e_5614_, v___y_5664_, v___y_5665_, v___y_5666_, v___y_5667_, v___y_5668_, v___y_5669_, v___y_5670_, v___y_5671_, v___y_5672_, v___y_5673_);
if (lean_obj_tag(v___x_5676_) == 0)
{
lean_object* v___x_5677_; 
lean_dec_ref_known(v___x_5676_, 1);
v___x_5677_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRingState___redArg(v___y_5662_, v___y_5663_, v___y_5664_);
if (lean_obj_tag(v___x_5677_) == 0)
{
lean_object* v___x_5678_; 
lean_dec_ref_known(v___x_5677_, 1);
v___x_5678_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize_0__Lean_Meta_Grind_Arith_CommRing_processPowIdentityVars(v___y_5663_, v___y_5664_, v___y_5665_, v___y_5666_, v___y_5667_, v___y_5668_, v___y_5669_, v___y_5670_, v___y_5671_, v___y_5672_, v___y_5673_);
lean_dec_ref(v___y_5663_);
return v___x_5678_;
}
else
{
lean_dec_ref(v___y_5663_);
return v___x_5677_;
}
}
else
{
lean_dec_ref(v___y_5663_);
lean_dec_ref(v___y_5662_);
return v___x_5676_;
}
}
else
{
lean_dec_ref(v___y_5663_);
lean_dec_ref(v___y_5662_);
lean_dec_ref(v_e_5614_);
return v___x_5674_;
}
}
v___jp_5679_:
{
lean_object* v___x_5692_; 
lean_inc_ref(v_e_5614_);
v___x_5692_ = l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId___redArg(v_e_5614_, v___y_5681_, v___y_5682_, v___y_5686_, v___y_5687_, v___y_5688_, v___y_5689_, v___y_5690_, v___y_5691_);
if (lean_obj_tag(v___x_5692_) == 0)
{
lean_object* v___x_5693_; lean_object* v___x_5694_; 
lean_dec_ref_known(v___x_5692_, 1);
v___x_5693_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_5694_ = l_Lean_Meta_Grind_SolverExtension_markTerm___redArg(v___x_5693_, v_e_5614_, v___y_5682_, v___y_5683_, v___y_5684_, v___y_5685_, v___y_5686_, v___y_5687_, v___y_5688_, v___y_5689_, v___y_5690_, v___y_5691_);
if (lean_obj_tag(v___x_5694_) == 0)
{
lean_object* v___x_5695_; 
lean_dec_ref_known(v___x_5694_, 1);
v___x_5695_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_modifyRingState___redArg(v___y_5680_, v___y_5681_, v___y_5682_);
lean_dec(v___y_5681_);
return v___x_5695_;
}
else
{
lean_dec(v___y_5681_);
lean_dec_ref(v___y_5680_);
return v___x_5694_;
}
}
else
{
lean_dec(v___y_5681_);
lean_dec_ref(v___y_5680_);
lean_dec_ref(v_e_5614_);
return v___x_5692_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_internalize___boxed(lean_object* v_e_6012_, lean_object* v_parent_x3f_6013_, lean_object* v_a_6014_, lean_object* v_a_6015_, lean_object* v_a_6016_, lean_object* v_a_6017_, lean_object* v_a_6018_, lean_object* v_a_6019_, lean_object* v_a_6020_, lean_object* v_a_6021_, lean_object* v_a_6022_, lean_object* v_a_6023_, lean_object* v_a_6024_){
_start:
{
lean_object* v_res_6025_; 
v_res_6025_ = l_Lean_Meta_Grind_Arith_CommRing_internalize(v_e_6012_, v_parent_x3f_6013_, v_a_6014_, v_a_6015_, v_a_6016_, v_a_6017_, v_a_6018_, v_a_6019_, v_a_6020_, v_a_6021_, v_a_6022_, v_a_6023_);
lean_dec(v_a_6023_);
lean_dec_ref(v_a_6022_);
lean_dec(v_a_6021_);
lean_dec_ref(v_a_6020_);
lean_dec(v_a_6019_);
lean_dec_ref(v_a_6018_);
lean_dec(v_a_6017_);
lean_dec_ref(v_a_6016_);
lean_dec(v_a_6015_);
lean_dec(v_a_6014_);
lean_dec(v_parent_x3f_6013_);
return v_res_6025_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0(lean_object* v_cls_6026_, lean_object* v_msg_6027_, lean_object* v___y_6028_, lean_object* v___y_6029_, lean_object* v___y_6030_, lean_object* v___y_6031_, lean_object* v___y_6032_, lean_object* v___y_6033_, lean_object* v___y_6034_, lean_object* v___y_6035_, lean_object* v___y_6036_, lean_object* v___y_6037_, lean_object* v___y_6038_){
_start:
{
lean_object* v___x_6040_; 
v___x_6040_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0___redArg(v_cls_6026_, v_msg_6027_, v___y_6035_, v___y_6036_, v___y_6037_, v___y_6038_);
return v___x_6040_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0___boxed(lean_object* v_cls_6041_, lean_object* v_msg_6042_, lean_object* v___y_6043_, lean_object* v___y_6044_, lean_object* v___y_6045_, lean_object* v___y_6046_, lean_object* v___y_6047_, lean_object* v___y_6048_, lean_object* v___y_6049_, lean_object* v___y_6050_, lean_object* v___y_6051_, lean_object* v___y_6052_, lean_object* v___y_6053_, lean_object* v___y_6054_){
_start:
{
lean_object* v_res_6055_; 
v_res_6055_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__0(v_cls_6041_, v_msg_6042_, v___y_6043_, v___y_6044_, v___y_6045_, v___y_6046_, v___y_6047_, v___y_6048_, v___y_6049_, v___y_6050_, v___y_6051_, v___y_6052_, v___y_6053_);
lean_dec(v___y_6053_);
lean_dec_ref(v___y_6052_);
lean_dec(v___y_6051_);
lean_dec_ref(v___y_6050_);
lean_dec(v___y_6049_);
lean_dec_ref(v___y_6048_);
lean_dec(v___y_6047_);
lean_dec_ref(v___y_6046_);
lean_dec(v___y_6045_);
lean_dec(v___y_6044_);
lean_dec(v___y_6043_);
return v_res_6055_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__1(lean_object* v_cls_6056_, lean_object* v_msg_6057_, lean_object* v___y_6058_, lean_object* v___y_6059_, lean_object* v___y_6060_, lean_object* v___y_6061_, lean_object* v___y_6062_, lean_object* v___y_6063_, lean_object* v___y_6064_, lean_object* v___y_6065_, lean_object* v___y_6066_, lean_object* v___y_6067_, lean_object* v___y_6068_){
_start:
{
lean_object* v___x_6070_; 
v___x_6070_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__1___redArg(v_cls_6056_, v_msg_6057_, v___y_6065_, v___y_6066_, v___y_6067_, v___y_6068_);
return v___x_6070_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__1___boxed(lean_object* v_cls_6071_, lean_object* v_msg_6072_, lean_object* v___y_6073_, lean_object* v___y_6074_, lean_object* v___y_6075_, lean_object* v___y_6076_, lean_object* v___y_6077_, lean_object* v___y_6078_, lean_object* v___y_6079_, lean_object* v___y_6080_, lean_object* v___y_6081_, lean_object* v___y_6082_, lean_object* v___y_6083_, lean_object* v___y_6084_){
_start:
{
lean_object* v_res_6085_; 
v_res_6085_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__1(v_cls_6071_, v_msg_6072_, v___y_6073_, v___y_6074_, v___y_6075_, v___y_6076_, v___y_6077_, v___y_6078_, v___y_6079_, v___y_6080_, v___y_6081_, v___y_6082_, v___y_6083_);
lean_dec(v___y_6083_);
lean_dec_ref(v___y_6082_);
lean_dec(v___y_6081_);
lean_dec_ref(v___y_6080_);
lean_dec(v___y_6079_);
lean_dec_ref(v___y_6078_);
lean_dec(v___y_6077_);
lean_dec_ref(v___y_6076_);
lean_dec(v___y_6075_);
lean_dec(v___y_6074_);
lean_dec(v___y_6073_);
return v_res_6085_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__2(lean_object* v_cls_6086_, lean_object* v_msg_6087_, lean_object* v___y_6088_, lean_object* v___y_6089_, lean_object* v___y_6090_, lean_object* v___y_6091_, lean_object* v___y_6092_, lean_object* v___y_6093_, lean_object* v___y_6094_, lean_object* v___y_6095_, lean_object* v___y_6096_, lean_object* v___y_6097_, lean_object* v___y_6098_){
_start:
{
lean_object* v___x_6100_; 
v___x_6100_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__2___redArg(v_cls_6086_, v_msg_6087_, v___y_6095_, v___y_6096_, v___y_6097_, v___y_6098_);
return v___x_6100_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__2___boxed(lean_object* v_cls_6101_, lean_object* v_msg_6102_, lean_object* v___y_6103_, lean_object* v___y_6104_, lean_object* v___y_6105_, lean_object* v___y_6106_, lean_object* v___y_6107_, lean_object* v___y_6108_, lean_object* v___y_6109_, lean_object* v___y_6110_, lean_object* v___y_6111_, lean_object* v___y_6112_, lean_object* v___y_6113_, lean_object* v___y_6114_){
_start:
{
lean_object* v_res_6115_; 
v_res_6115_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_CommRing_internalize_spec__2(v_cls_6101_, v_msg_6102_, v___y_6103_, v___y_6104_, v___y_6105_, v___y_6106_, v___y_6107_, v___y_6108_, v___y_6109_, v___y_6110_, v___y_6111_, v___y_6112_, v___y_6113_);
lean_dec(v___y_6113_);
lean_dec_ref(v___y_6112_);
lean_dec(v___y_6111_);
lean_dec_ref(v___y_6110_);
lean_dec(v___y_6109_);
lean_dec_ref(v___y_6108_);
lean_dec(v___y_6107_);
lean_dec_ref(v___y_6106_);
lean_dec(v___y_6105_);
lean_dec(v___y_6104_);
lean_dec(v___y_6103_);
return v_res_6115_;
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
