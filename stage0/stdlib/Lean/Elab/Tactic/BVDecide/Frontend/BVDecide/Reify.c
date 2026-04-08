// Lean compiler output
// Module: Lean.Elab.Tactic.BVDecide.Frontend.BVDecide.Reify
// Imports: public import Lean.Elab.Tactic.BVDecide.Frontend.BVDecide.ReifiedLemmas import Lean.Meta.LitValues
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
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getBitVecValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkBVConst___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_bitVecAtom(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Core_checkSystem(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_BVExpr_bin___override(lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkNatLit(lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkEvalExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_evalsAtAtoms(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkBVRefl(lean_object*, lean_object*);
lean_object* l_Lean_mkApp6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_getNatOrBvValue_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getNatValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_BVExpr_shiftLeft___override(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Std_Tactic_BVDecide_BVExpr_shiftRight___override(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_BVExpr_append___override___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqRefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_BVExpr_arithShiftRight___override(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_BVExpr_extract___override(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_mkBinPred___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_mkGetLsbD___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_boolAtom(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_ofPred___redArg(lean_object*);
lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_mkGate___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_mkIte___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_mkNot___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_mkBoolConst___redArg(uint8_t);
lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_boolAtom(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_BVExpr_un___override(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_BVExpr_replicate___override___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_goBvLit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_goBvLit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_M_simplifyBinaryProof_x27___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryCongrProof_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryCongrProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryCongrProof___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryCongrProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryCongrProof___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom_spec__2_spec__12_spec__17___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom_spec__2_spec__12_spec__17___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom_spec__2_spec__12___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom_spec__2_spec__12___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13_spec__19___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13_spec__19___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13_spec__20_spec__25_spec__26___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13_spec__20_spec__25___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13_spec__20___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13_spec__21___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go_spec__12_spec__20(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go_spec__12_spec__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go_spec__12___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_M_simplifyBinaryProof_x27___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Reflect"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___lam__0___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "append_congr"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___lam__0___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___lam__0___boxed(lean_object**);
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "extract_congr"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___lam__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___lam__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___lam__1___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___lam__2(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___lam__5(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___lam__4(lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "replicate_congr"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___lam__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___lam__3___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___lam__3___boxed(lean_object**);
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "bv_decide"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_go___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_go___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_of_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "BitVec"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_of_go___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_of_go___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "cpop"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__19 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__19_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_of_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(108, 178, 58, 132, 143, 189, 222, 74)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__0_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__19_value),LEAN_SCALAR_PTR_LITERAL(54, 25, 40, 162, 224, 189, 205, 182)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "clz"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__16 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__16_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_of_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(108, 178, 58, 132, 143, 189, 222, 74)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__16_value),LEAN_SCALAR_PTR_LITERAL(61, 156, 207, 111, 211, 81, 174, 218)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "reverse"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__13 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__13_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_of_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(108, 178, 58, 132, 143, 189, 222, 74)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__13_value),LEAN_SCALAR_PTR_LITERAL(244, 136, 165, 42, 211, 46, 208, 62)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__2_value;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ofNat"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_of_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(108, 178, 58, 132, 143, 189, 222, 74)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__3_value),LEAN_SCALAR_PTR_LITERAL(101, 105, 192, 171, 214, 131, 43, 105)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__4_value;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "rotateRight"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__7 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__7_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_of_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(108, 178, 58, 132, 143, 189, 222, 74)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__7_value),LEAN_SCALAR_PTR_LITERAL(208, 30, 240, 114, 51, 110, 152, 157)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__5_value;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "rotateLeft"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_of_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(108, 178, 58, 132, 143, 189, 222, 74)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__6_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__4_value),LEAN_SCALAR_PTR_LITERAL(125, 181, 93, 155, 164, 43, 234, 184)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__6_value;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "replicate"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__7 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__7_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_of_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(108, 178, 58, 132, 143, 189, 222, 74)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__8_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__7_value),LEAN_SCALAR_PTR_LITERAL(234, 123, 74, 120, 175, 214, 39, 20)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__8 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__8_value;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "sshiftRight"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__9 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__9_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_of_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(108, 178, 58, 132, 143, 189, 222, 74)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__10_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__9_value),LEAN_SCALAR_PTR_LITERAL(206, 65, 29, 246, 207, 155, 165, 148)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__10 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__10_value;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "complement"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__12 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__12_value;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "Complement"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__11 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__11_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__11_value),LEAN_SCALAR_PTR_LITERAL(6, 52, 244, 64, 3, 58, 115, 79)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__13_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__12_value),LEAN_SCALAR_PTR_LITERAL(168, 254, 142, 44, 189, 175, 152, 168)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__13 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__13_value;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_go___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "cond"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_go___closed__9 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_go___closed__9_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_go___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_go___closed__9_value),LEAN_SCALAR_PTR_LITERAL(130, 140, 200, 235, 144, 197, 118, 1)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_go___closed__10 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_go___closed__10_value;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "extractLsb'"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__14 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__14_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_of_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(108, 178, 58, 132, 143, 189, 222, 74)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__15_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__14_value),LEAN_SCALAR_PTR_LITERAL(47, 201, 218, 12, 248, 124, 75, 23)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__15 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__15_value;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "sshiftRight'"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__16 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__16_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_of_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(108, 178, 58, 132, 143, 189, 222, 74)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__17_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__16_value),LEAN_SCALAR_PTR_LITERAL(69, 78, 17, 52, 147, 31, 186, 103)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__17 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__17_value;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "hAppend"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__19 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__19_value;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "HAppend"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__18 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__18_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__20_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__18_value),LEAN_SCALAR_PTR_LITERAL(137, 35, 233, 160, 196, 216, 250, 31)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__20_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__19_value),LEAN_SCALAR_PTR_LITERAL(181, 97, 51, 176, 35, 131, 5, 233)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__20 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__20_value;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "hShiftRight"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__22 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__22_value;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "HShiftRight"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__21 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__21_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__23_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__21_value),LEAN_SCALAR_PTR_LITERAL(123, 35, 163, 146, 1, 76, 65, 75)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__23_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__22_value),LEAN_SCALAR_PTR_LITERAL(52, 65, 204, 240, 51, 126, 9, 157)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__23 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__23_value;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "hShiftLeft"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__25 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__25_value;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "HShiftLeft"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__24 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__24_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__26_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__24_value),LEAN_SCALAR_PTR_LITERAL(215, 217, 51, 89, 252, 54, 156, 169)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__26_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__25_value),LEAN_SCALAR_PTR_LITERAL(181, 245, 218, 3, 224, 235, 179, 59)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__26 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__26_value;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hMod"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__28 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__28_value;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HMod"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__27 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__27_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__29_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__27_value),LEAN_SCALAR_PTR_LITERAL(93, 4, 3, 35, 188, 254, 191, 190)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__29_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__28_value),LEAN_SCALAR_PTR_LITERAL(120, 199, 142, 238, 9, 44, 94, 134)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__29 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__29_value;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hDiv"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__31 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__31_value;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HDiv"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__30 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__30_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__32_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__30_value),LEAN_SCALAR_PTR_LITERAL(74, 223, 78, 88, 255, 236, 144, 164)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__32_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__31_value),LEAN_SCALAR_PTR_LITERAL(26, 183, 188, 240, 156, 118, 170, 84)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__32 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__32_value;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hMul"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__34 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__34_value;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HMul"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__33 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__33_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__35_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__33_value),LEAN_SCALAR_PTR_LITERAL(254, 113, 255, 140, 142, 9, 169, 40)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__35_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__34_value),LEAN_SCALAR_PTR_LITERAL(248, 227, 200, 215, 229, 255, 92, 22)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__35 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__35_value;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hAdd"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__37 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__37_value;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HAdd"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__36 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__36_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__38_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__36_value),LEAN_SCALAR_PTR_LITERAL(221, 239, 47, 196, 170, 166, 59, 144)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__38_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__37_value),LEAN_SCALAR_PTR_LITERAL(134, 172, 115, 219, 189, 252, 56, 148)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__38 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__38_value;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hXor"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__40 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__40_value;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HXor"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__39 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__39_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__41_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__39_value),LEAN_SCALAR_PTR_LITERAL(92, 198, 212, 133, 26, 7, 147, 78)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__41_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__40_value),LEAN_SCALAR_PTR_LITERAL(109, 159, 33, 254, 118, 42, 120, 166)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__41 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__41_value;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hAnd"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__43 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__43_value;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HAnd"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__42 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__42_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__44_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__42_value),LEAN_SCALAR_PTR_LITERAL(222, 205, 8, 181, 48, 134, 168, 175)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__44_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__43_value),LEAN_SCALAR_PTR_LITERAL(54, 171, 107, 112, 94, 43, 106, 200)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__44 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__44_value;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "and_congr"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__45 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__45_value;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "BVDecide"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2_value;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Std"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__46_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__46_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__46_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__46_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__46_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__46_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__46_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(32, 92, 17, 213, 68, 211, 219, 250)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__46_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__46_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_of_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(179, 160, 70, 158, 0, 14, 153, 5)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__46_value_aux_4),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__45_value),LEAN_SCALAR_PTR_LITERAL(20, 152, 116, 121, 198, 45, 139, 17)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__46 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__46_value;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "bin"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "BVExpr"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__3_value),LEAN_SCALAR_PTR_LITERAL(43, 53, 240, 176, 234, 207, 251, 199)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__0_value),LEAN_SCALAR_PTR_LITERAL(47, 182, 211, 92, 78, 225, 70, 26)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__1_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__2;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "and"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__4_value;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "BVBinOp"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__5_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__5_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__5_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__3_value),LEAN_SCALAR_PTR_LITERAL(173, 0, 131, 50, 199, 91, 123, 28)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__5_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__4_value),LEAN_SCALAR_PTR_LITERAL(67, 200, 193, 54, 191, 172, 208, 119)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__5_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__6;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "or"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__7 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__7_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__8_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__8_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__8_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__8_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__3_value),LEAN_SCALAR_PTR_LITERAL(173, 0, 131, 50, 199, 91, 123, 28)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__8_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__7_value),LEAN_SCALAR_PTR_LITERAL(137, 33, 141, 132, 156, 154, 79, 232)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__8 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__8_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__9;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "xor"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__10 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__10_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__11_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__11_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__11_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__11_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__3_value),LEAN_SCALAR_PTR_LITERAL(173, 0, 131, 50, 199, 91, 123, 28)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__11_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__10_value),LEAN_SCALAR_PTR_LITERAL(68, 221, 44, 95, 169, 9, 73, 176)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__11 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__11_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__12;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "add"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__13 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__13_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__14_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__14_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__14_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__14_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__14_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__14_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__3_value),LEAN_SCALAR_PTR_LITERAL(173, 0, 131, 50, 199, 91, 123, 28)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__14_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__13_value),LEAN_SCALAR_PTR_LITERAL(236, 85, 182, 141, 252, 28, 21, 198)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__14 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__14_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__15;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "mul"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__16 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__16_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__17_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__17_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__17_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__17_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__17_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__17_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__3_value),LEAN_SCALAR_PTR_LITERAL(173, 0, 131, 50, 199, 91, 123, 28)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__17_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__16_value),LEAN_SCALAR_PTR_LITERAL(66, 46, 226, 27, 15, 162, 209, 81)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__17 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__17_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__18;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "udiv"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__19 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__19_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__20_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__20_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__20_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__20_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__20_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__20_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__20_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__3_value),LEAN_SCALAR_PTR_LITERAL(173, 0, 131, 50, 199, 91, 123, 28)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__20_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__19_value),LEAN_SCALAR_PTR_LITERAL(97, 106, 189, 172, 252, 249, 116, 143)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__20 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__20_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__21;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "umod"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__22 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__22_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__23_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__23_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__23_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__23_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__23_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__23_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__23_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__3_value),LEAN_SCALAR_PTR_LITERAL(173, 0, 131, 50, 199, 91, 123, 28)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__23_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__22_value),LEAN_SCALAR_PTR_LITERAL(185, 164, 216, 8, 44, 82, 23, 11)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__23 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__23_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__24;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "xor_congr"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__47 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__47_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__48_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__48_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__48_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__48_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__48_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__48_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__48_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(32, 92, 17, 213, 68, 211, 219, 250)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__48_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__48_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_of_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(179, 160, 70, 158, 0, 14, 153, 5)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__48_value_aux_4),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__47_value),LEAN_SCALAR_PTR_LITERAL(225, 129, 197, 38, 228, 52, 44, 57)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__48 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__48_value;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "add_congr"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__49 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__49_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__50_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__50_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__50_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__50_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__50_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__50_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__50_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(32, 92, 17, 213, 68, 211, 219, 250)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__50_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__50_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_of_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(179, 160, 70, 158, 0, 14, 153, 5)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__50_value_aux_4),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__49_value),LEAN_SCALAR_PTR_LITERAL(177, 5, 60, 46, 78, 68, 243, 177)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__50 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__50_value;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "mul_congr"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__51 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__51_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__52_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__52_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__52_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__52_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__52_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__52_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__52_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(32, 92, 17, 213, 68, 211, 219, 250)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__52_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__52_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_of_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(179, 160, 70, 158, 0, 14, 153, 5)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__52_value_aux_4),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__51_value),LEAN_SCALAR_PTR_LITERAL(221, 159, 178, 23, 57, 108, 69, 225)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__52 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__52_value;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "udiv_congr"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__53 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__53_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__54_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__54_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__54_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__54_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__54_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__54_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__54_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(32, 92, 17, 213, 68, 211, 219, 250)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__54_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__54_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_of_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(179, 160, 70, 158, 0, 14, 153, 5)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__54_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__54_value_aux_4),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__53_value),LEAN_SCALAR_PTR_LITERAL(118, 153, 195, 105, 228, 227, 83, 28)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__54 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__54_value;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__55_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "umod_congr"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__55 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__55_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__56_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__56_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__56_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__56_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__56_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__56_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__56_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(32, 92, 17, 213, 68, 211, 219, 250)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__56_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__56_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_of_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(179, 160, 70, 158, 0, 14, 153, 5)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__56_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__56_value_aux_4),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__55_value),LEAN_SCALAR_PTR_LITERAL(102, 27, 81, 101, 187, 174, 242, 104)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__56 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__56_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_of_go___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_of_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(108, 178, 58, 132, 143, 189, 222, 74)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_of_go___closed__8 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_of_go___closed__8_value;
static const lean_closure_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__57_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Tactic_BVDecide_BVExpr_shiftLeft___override, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__57 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__57_value;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__58_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "shiftLeft"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__58 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__58_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__59_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__59_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__59_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__59_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__59_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__59_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__59_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__3_value),LEAN_SCALAR_PTR_LITERAL(43, 53, 240, 176, 234, 207, 251, 199)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__59_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__59_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__58_value),LEAN_SCALAR_PTR_LITERAL(197, 209, 242, 75, 214, 61, 180, 95)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__59 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__59_value;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__60_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "shiftLeft_congr"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__60 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__60_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__61_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__61_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__61_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__61_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__61_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__61_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__61_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(32, 92, 17, 213, 68, 211, 219, 250)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__61_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__61_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_of_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(179, 160, 70, 158, 0, 14, 153, 5)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__61_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__61_value_aux_4),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__60_value),LEAN_SCALAR_PTR_LITERAL(121, 119, 67, 4, 228, 88, 122, 113)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__61 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__61_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftReflection(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__62_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 60, .m_capacity = 60, .m_length = 59, .m_data = "internal error: constant shift should have been eliminated."};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__62 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__62_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__63_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__63;
static const lean_closure_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__64_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Tactic_BVDecide_BVExpr_shiftRight___override, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__64 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__64_value;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__65_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "shiftRight"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__65 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__65_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__66_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__66_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__66_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__66_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__66_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__66_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__66_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__3_value),LEAN_SCALAR_PTR_LITERAL(43, 53, 240, 176, 234, 207, 251, 199)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__66_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__66_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__65_value),LEAN_SCALAR_PTR_LITERAL(71, 199, 243, 56, 253, 18, 242, 226)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__66 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__66_value;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__67_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "shiftRight_congr"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__67 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__67_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__68_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__68_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__68_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__68_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__68_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__68_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__68_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(32, 92, 17, 213, 68, 211, 219, 250)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__68_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__68_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_of_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(179, 160, 70, 158, 0, 14, 153, 5)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__68_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__68_value_aux_4),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__67_value),LEAN_SCALAR_PTR_LITERAL(216, 161, 38, 33, 237, 165, 100, 97)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__68 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__68_value;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__69_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "append"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__69 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__69_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__70_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__70_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__70_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__70_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__70_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__70_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__70_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__3_value),LEAN_SCALAR_PTR_LITERAL(43, 53, 240, 176, 234, 207, 251, 199)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__70_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__70_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__69_value),LEAN_SCALAR_PTR_LITERAL(148, 222, 207, 10, 98, 174, 247, 204)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__70 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__70_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__71_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__71;
static const lean_closure_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__72_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Tactic_BVDecide_BVExpr_arithShiftRight___override, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__72 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__72_value;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__73_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "arithShiftRight"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__73 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__73_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__74_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__74_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__74_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__74_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__74_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__74_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__74_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__3_value),LEAN_SCALAR_PTR_LITERAL(43, 53, 240, 176, 234, 207, 251, 199)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__74_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__74_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__73_value),LEAN_SCALAR_PTR_LITERAL(103, 53, 88, 127, 221, 158, 175, 136)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__74 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__74_value;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__75_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "arithShiftRight_congr"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__75 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__75_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__76_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__76_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__76_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__76_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__76_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__76_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__76_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(32, 92, 17, 213, 68, 211, 219, 250)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__76_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__76_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_of_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(179, 160, 70, 158, 0, 14, 153, 5)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__76_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__76_value_aux_4),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__75_value),LEAN_SCALAR_PTR_LITERAL(52, 31, 162, 102, 135, 66, 0, 161)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__76 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__76_value;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__77_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "extract"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__77 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__77_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__78_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__78_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__78_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__78_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__78_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__78_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__78_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__3_value),LEAN_SCALAR_PTR_LITERAL(43, 53, 240, 176, 234, 207, 251, 199)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__78_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__78_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__77_value),LEAN_SCALAR_PTR_LITERAL(13, 22, 63, 119, 146, 191, 248, 8)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__78 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__78_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__79_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__79;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_go___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_go___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_go___closed__2_value;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_go___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Bool"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_go___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_go___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_go___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_go___closed__1_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_go___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_go___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_go___closed__2_value),LEAN_SCALAR_PTR_LITERAL(117, 151, 161, 190, 111, 237, 188, 218)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_go___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_go___closed__3_value;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_go___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_go___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_go___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_go___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_go___closed__1_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_go___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_go___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_go___closed__4_value),LEAN_SCALAR_PTR_LITERAL(22, 245, 194, 28, 184, 9, 113, 128)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_go___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_go___closed__5_value;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_of_go___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "getLsbD"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_of_go___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_of_go___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_of_go___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_of_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(108, 178, 58, 132, 143, 189, 222, 74)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_of_go___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_of_go___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_of_go___closed__1_value),LEAN_SCALAR_PTR_LITERAL(201, 206, 226, 96, 197, 228, 245, 77)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_of_go___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_of_go___closed__2_value;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_of_go___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "ult"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_of_go___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_of_go___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_of_go___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_of_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(108, 178, 58, 132, 143, 189, 222, 74)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_of_go___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_of_go___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_of_go___closed__3_value),LEAN_SCALAR_PTR_LITERAL(111, 62, 117, 244, 108, 14, 8, 240)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_of_go___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_of_go___closed__4_value;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_of_go___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "beq"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_of_go___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_of_go___closed__6_value;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_of_go___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "BEq"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_of_go___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_of_go___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_of_go___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_of_go___closed__5_value),LEAN_SCALAR_PTR_LITERAL(195, 188, 39, 55, 57, 152, 88, 223)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_of_go___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_of_go___closed__7_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_of_go___closed__6_value),LEAN_SCALAR_PTR_LITERAL(82, 52, 243, 194, 7, 226, 90, 135)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_of_go___closed__7 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_of_go___closed__7_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_of_binaryReflection(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_of_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVPredCache___at___00Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_of_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_of(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goPred(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "not"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_go___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_go___closed__1_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_go___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_go___closed__6_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__1_value),LEAN_SCALAR_PTR_LITERAL(208, 215, 171, 150, 192, 180, 249, 22)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_go___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_go___closed__6_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_go___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_go___closed__1_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_go___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_go___closed__7_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__10_value),LEAN_SCALAR_PTR_LITERAL(159, 35, 146, 118, 24, 65, 174, 144)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_go___closed__7 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_go___closed__7_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_go___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_go___closed__1_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_go___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_go___closed__8_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__4_value),LEAN_SCALAR_PTR_LITERAL(160, 26, 8, 228, 104, 32, 82, 85)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_go___closed__8 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_go___closed__8_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_go___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_go___closed__1_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_go___closed__11 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_go___closed__11_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_gateReflection(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__80_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "not_congr"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__80 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__80_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__81_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__81_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__81_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__81_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__81_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__81_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__81_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(32, 92, 17, 213, 68, 211, 219, 250)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__81_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__81_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_of_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(179, 160, 70, 158, 0, 14, 153, 5)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__81_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__81_value_aux_4),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__80_value),LEAN_SCALAR_PTR_LITERAL(189, 30, 154, 245, 30, 224, 55, 44)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__81 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__81_value;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "un"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__5_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__5_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__5_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__3_value),LEAN_SCALAR_PTR_LITERAL(43, 53, 240, 176, 234, 207, 251, 199)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__5_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__4_value),LEAN_SCALAR_PTR_LITERAL(42, 186, 200, 92, 180, 128, 216, 181)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__5_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__6;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "BVUnOp"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__2_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__2_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 14, 123, 74, 130, 241, 190, 47)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__2_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__1_value),LEAN_SCALAR_PTR_LITERAL(30, 170, 248, 163, 146, 14, 228, 74)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__3;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__5_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__5_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__5_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 14, 123, 74, 130, 241, 190, 47)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__5_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__4_value),LEAN_SCALAR_PTR_LITERAL(29, 116, 55, 155, 243, 43, 27, 136)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__5_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__6;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__8_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__8_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__8_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__8_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 14, 123, 74, 130, 241, 190, 47)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__8_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__7_value),LEAN_SCALAR_PTR_LITERAL(112, 197, 123, 204, 93, 250, 252, 249)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__8 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__8_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__9;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "arithShiftRightConst"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__10 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__10_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__11_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__11_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__11_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__11_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 14, 123, 74, 130, 241, 190, 47)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__11_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__10_value),LEAN_SCALAR_PTR_LITERAL(88, 95, 189, 240, 90, 71, 117, 208)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__11 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__11_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__12;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__14_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__14_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__14_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__14_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__14_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__14_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 14, 123, 74, 130, 241, 190, 47)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__14_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__13_value),LEAN_SCALAR_PTR_LITERAL(84, 226, 239, 81, 45, 17, 252, 180)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__14 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__14_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__15;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__17_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__17_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__17_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__17_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__17_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__17_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 14, 123, 74, 130, 241, 190, 47)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__17_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__16_value),LEAN_SCALAR_PTR_LITERAL(221, 66, 219, 130, 52, 97, 84, 10)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__17 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__17_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__18;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__20_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__20_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__20_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__20_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__20_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__20_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__20_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 14, 123, 74, 130, 241, 190, 47)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__20_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__19_value),LEAN_SCALAR_PTR_LITERAL(214, 119, 73, 246, 51, 241, 221, 59)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__20 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__20_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__21;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__82_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___lam__2, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__82 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__82_value;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__83_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "arithShiftRightNat_congr"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__83 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__83_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__84_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__84_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__84_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__84_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__84_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__84_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__84_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(32, 92, 17, 213, 68, 211, 219, 250)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__84_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__84_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_of_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(179, 160, 70, 158, 0, 14, 153, 5)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__84_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__84_value_aux_4),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__83_value),LEAN_SCALAR_PTR_LITERAL(59, 32, 240, 3, 69, 217, 10, 161)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__84 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__84_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__85_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__85_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__85_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__85_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__85_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__85_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__85_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__3_value),LEAN_SCALAR_PTR_LITERAL(43, 53, 240, 176, 234, 207, 251, 199)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__85_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__85_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__7_value),LEAN_SCALAR_PTR_LITERAL(105, 148, 101, 98, 245, 160, 38, 159)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__85 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__85_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__86_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__86;
static const lean_closure_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__87_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___lam__4, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__87 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__87_value;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__88_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "rotateLeft_congr"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__88 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__88_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__89_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__89_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__89_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__89_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__89_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__89_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__89_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(32, 92, 17, 213, 68, 211, 219, 250)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__89_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__89_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_of_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(179, 160, 70, 158, 0, 14, 153, 5)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__89_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__89_value_aux_4),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__88_value),LEAN_SCALAR_PTR_LITERAL(32, 228, 194, 198, 195, 74, 36, 62)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__89 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__89_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_rotateReflection(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__90_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___lam__5, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__90 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__90_value;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__91_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "rotateRight_congr"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__91 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__91_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__92_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__92_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__92_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__92_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__92_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__92_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__92_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(32, 92, 17, 213, 68, 211, 219, 250)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__92_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__92_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_of_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(179, 160, 70, 158, 0, 14, 153, 5)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__92_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__92_value_aux_4),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__91_value),LEAN_SCALAR_PTR_LITERAL(61, 145, 127, 186, 176, 174, 37, 55)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__92 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__92_value;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__93_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "reverse_congr"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__93 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__93_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__94_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__94_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__94_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__94_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__94_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__94_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__94_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(32, 92, 17, 213, 68, 211, 219, 250)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__94_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__94_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_of_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(179, 160, 70, 158, 0, 14, 153, 5)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__94_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__94_value_aux_4),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__93_value),LEAN_SCALAR_PTR_LITERAL(182, 175, 240, 129, 220, 112, 73, 89)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__94 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__94_value;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__95_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "clz_congr"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__95 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__95_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__96_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__96_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__96_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__96_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__96_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__96_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__96_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(32, 92, 17, 213, 68, 211, 219, 250)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__96_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__96_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_of_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(179, 160, 70, 158, 0, 14, 153, 5)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__96_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__96_value_aux_4),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__95_value),LEAN_SCALAR_PTR_LITERAL(108, 254, 78, 195, 105, 118, 43, 132)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__96 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__96_value;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__97_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "cpop_congr"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__97 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__97_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__98_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__98_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__98_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__98_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__98_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__98_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__98_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(32, 92, 17, 213, 68, 211, 219, 250)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__98_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__98_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_of_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(179, 160, 70, 158, 0, 14, 153, 5)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__98_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__98_value_aux_4),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__97_value),LEAN_SCALAR_PTR_LITERAL(181, 75, 188, 170, 67, 231, 89, 223)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__98 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__98_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVExprCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_goOrAtom_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_goOrAtom(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_of___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_goOrAtom___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_rotateReflection___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goPred___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_of_binaryReflection___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_gateReflection___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftReflection___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVPredCache___at___00Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_of_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVExprCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_goOrAtom_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_of_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go_spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom_spec__2_spec__12(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom_spec__2_spec__12___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom_spec__2_spec__12_spec__17(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom_spec__2_spec__12_spec__17___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13_spec__19(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13_spec__19___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13_spec__20(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13_spec__21(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13_spec__20_spec__25(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13_spec__20_spec__25_spec__26(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_goBvLit(lean_object* v_x_1_, lean_object* v_a_2_, lean_object* v_a_3_, lean_object* v_a_4_, lean_object* v_a_5_, lean_object* v_a_6_){
_start:
{
lean_object* v___x_8_; 
lean_inc_ref(v_x_1_);
v___x_8_ = l_Lean_Meta_getBitVecValue_x3f(v_x_1_, v_a_3_, v_a_4_, v_a_5_, v_a_6_);
if (lean_obj_tag(v___x_8_) == 0)
{
lean_object* v_a_9_; 
v_a_9_ = lean_ctor_get(v___x_8_, 0);
lean_inc(v_a_9_);
lean_dec_ref(v___x_8_);
if (lean_obj_tag(v_a_9_) == 1)
{
lean_object* v_val_10_; lean_object* v___x_12_; uint8_t v_isShared_13_; uint8_t v_isSharedCheck_36_; 
lean_dec_ref(v_x_1_);
v_val_10_ = lean_ctor_get(v_a_9_, 0);
v_isSharedCheck_36_ = !lean_is_exclusive(v_a_9_);
if (v_isSharedCheck_36_ == 0)
{
v___x_12_ = v_a_9_;
v_isShared_13_ = v_isSharedCheck_36_;
goto v_resetjp_11_;
}
else
{
lean_inc(v_val_10_);
lean_dec(v_a_9_);
v___x_12_ = lean_box(0);
v_isShared_13_ = v_isSharedCheck_36_;
goto v_resetjp_11_;
}
v_resetjp_11_:
{
lean_object* v_fst_14_; lean_object* v_snd_15_; lean_object* v___x_16_; 
v_fst_14_ = lean_ctor_get(v_val_10_, 0);
lean_inc(v_fst_14_);
v_snd_15_ = lean_ctor_get(v_val_10_, 1);
lean_inc(v_snd_15_);
lean_dec(v_val_10_);
v___x_16_ = l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkBVConst___redArg(v_fst_14_, v_snd_15_);
if (lean_obj_tag(v___x_16_) == 0)
{
lean_object* v_a_17_; lean_object* v___x_19_; uint8_t v_isShared_20_; uint8_t v_isSharedCheck_27_; 
v_a_17_ = lean_ctor_get(v___x_16_, 0);
v_isSharedCheck_27_ = !lean_is_exclusive(v___x_16_);
if (v_isSharedCheck_27_ == 0)
{
v___x_19_ = v___x_16_;
v_isShared_20_ = v_isSharedCheck_27_;
goto v_resetjp_18_;
}
else
{
lean_inc(v_a_17_);
lean_dec(v___x_16_);
v___x_19_ = lean_box(0);
v_isShared_20_ = v_isSharedCheck_27_;
goto v_resetjp_18_;
}
v_resetjp_18_:
{
lean_object* v___x_22_; 
if (v_isShared_13_ == 0)
{
lean_ctor_set(v___x_12_, 0, v_a_17_);
v___x_22_ = v___x_12_;
goto v_reusejp_21_;
}
else
{
lean_object* v_reuseFailAlloc_26_; 
v_reuseFailAlloc_26_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_26_, 0, v_a_17_);
v___x_22_ = v_reuseFailAlloc_26_;
goto v_reusejp_21_;
}
v_reusejp_21_:
{
lean_object* v___x_24_; 
if (v_isShared_20_ == 0)
{
lean_ctor_set(v___x_19_, 0, v___x_22_);
v___x_24_ = v___x_19_;
goto v_reusejp_23_;
}
else
{
lean_object* v_reuseFailAlloc_25_; 
v_reuseFailAlloc_25_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_25_, 0, v___x_22_);
v___x_24_ = v_reuseFailAlloc_25_;
goto v_reusejp_23_;
}
v_reusejp_23_:
{
return v___x_24_;
}
}
}
}
else
{
lean_object* v_a_28_; lean_object* v___x_30_; uint8_t v_isShared_31_; uint8_t v_isSharedCheck_35_; 
lean_del_object(v___x_12_);
v_a_28_ = lean_ctor_get(v___x_16_, 0);
v_isSharedCheck_35_ = !lean_is_exclusive(v___x_16_);
if (v_isSharedCheck_35_ == 0)
{
v___x_30_ = v___x_16_;
v_isShared_31_ = v_isSharedCheck_35_;
goto v_resetjp_29_;
}
else
{
lean_inc(v_a_28_);
lean_dec(v___x_16_);
v___x_30_ = lean_box(0);
v_isShared_31_ = v_isSharedCheck_35_;
goto v_resetjp_29_;
}
v_resetjp_29_:
{
lean_object* v___x_33_; 
if (v_isShared_31_ == 0)
{
v___x_33_ = v___x_30_;
goto v_reusejp_32_;
}
else
{
lean_object* v_reuseFailAlloc_34_; 
v_reuseFailAlloc_34_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_34_, 0, v_a_28_);
v___x_33_ = v_reuseFailAlloc_34_;
goto v_reusejp_32_;
}
v_reusejp_32_:
{
return v___x_33_;
}
}
}
}
}
else
{
uint8_t v___x_37_; lean_object* v___x_38_; 
lean_dec(v_a_9_);
v___x_37_ = 0;
v___x_38_ = l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_bitVecAtom(v_x_1_, v___x_37_, v_a_2_, v_a_3_, v_a_4_, v_a_5_, v_a_6_);
return v___x_38_;
}
}
else
{
lean_object* v_a_39_; lean_object* v___x_41_; uint8_t v_isShared_42_; uint8_t v_isSharedCheck_46_; 
lean_dec_ref(v_x_1_);
v_a_39_ = lean_ctor_get(v___x_8_, 0);
v_isSharedCheck_46_ = !lean_is_exclusive(v___x_8_);
if (v_isSharedCheck_46_ == 0)
{
v___x_41_ = v___x_8_;
v_isShared_42_ = v_isSharedCheck_46_;
goto v_resetjp_40_;
}
else
{
lean_inc(v_a_39_);
lean_dec(v___x_8_);
v___x_41_ = lean_box(0);
v_isShared_42_ = v_isSharedCheck_46_;
goto v_resetjp_40_;
}
v_resetjp_40_:
{
lean_object* v___x_44_; 
if (v_isShared_42_ == 0)
{
v___x_44_ = v___x_41_;
goto v_reusejp_43_;
}
else
{
lean_object* v_reuseFailAlloc_45_; 
v_reuseFailAlloc_45_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_45_, 0, v_a_39_);
v___x_44_ = v_reuseFailAlloc_45_;
goto v_reusejp_43_;
}
v_reusejp_43_:
{
return v___x_44_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_goBvLit___boxed(lean_object* v_x_47_, lean_object* v_a_48_, lean_object* v_a_49_, lean_object* v_a_50_, lean_object* v_a_51_, lean_object* v_a_52_, lean_object* v_a_53_){
_start:
{
lean_object* v_res_54_; 
v_res_54_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_goBvLit(v_x_47_, v_a_48_, v_a_49_, v_a_50_, v_a_51_, v_a_52_);
lean_dec(v_a_52_);
lean_dec_ref(v_a_51_);
lean_dec(v_a_50_);
lean_dec_ref(v_a_49_);
lean_dec(v_a_48_);
return v_res_54_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_M_simplifyBinaryProof_x27___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryCongrProof_spec__0(lean_object* v___x_55_, lean_object* v_fst_56_, lean_object* v_fproof_57_, lean_object* v_snd_58_, lean_object* v_sproof_59_){
_start:
{
if (lean_obj_tag(v_fproof_57_) == 0)
{
lean_dec_ref(v_snd_58_);
if (lean_obj_tag(v_sproof_59_) == 0)
{
lean_object* v___x_60_; 
lean_dec_ref(v_fst_56_);
lean_dec(v___x_55_);
v___x_60_ = lean_box(0);
return v___x_60_;
}
else
{
lean_object* v_val_61_; lean_object* v___x_63_; uint8_t v_isShared_64_; uint8_t v_isSharedCheck_70_; 
v_val_61_ = lean_ctor_get(v_sproof_59_, 0);
v_isSharedCheck_70_ = !lean_is_exclusive(v_sproof_59_);
if (v_isSharedCheck_70_ == 0)
{
v___x_63_ = v_sproof_59_;
v_isShared_64_ = v_isSharedCheck_70_;
goto v_resetjp_62_;
}
else
{
lean_inc(v_val_61_);
lean_dec(v_sproof_59_);
v___x_63_ = lean_box(0);
v_isShared_64_ = v_isSharedCheck_70_;
goto v_resetjp_62_;
}
v_resetjp_62_:
{
lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_68_; 
v___x_65_ = l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkBVRefl(v___x_55_, v_fst_56_);
v___x_66_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_66_, 0, v___x_65_);
lean_ctor_set(v___x_66_, 1, v_val_61_);
if (v_isShared_64_ == 0)
{
lean_ctor_set(v___x_63_, 0, v___x_66_);
v___x_68_ = v___x_63_;
goto v_reusejp_67_;
}
else
{
lean_object* v_reuseFailAlloc_69_; 
v_reuseFailAlloc_69_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_69_, 0, v___x_66_);
v___x_68_ = v_reuseFailAlloc_69_;
goto v_reusejp_67_;
}
v_reusejp_67_:
{
return v___x_68_;
}
}
}
}
else
{
lean_dec_ref(v_fst_56_);
if (lean_obj_tag(v_sproof_59_) == 0)
{
lean_object* v_val_71_; lean_object* v___x_73_; uint8_t v_isShared_74_; uint8_t v_isSharedCheck_80_; 
v_val_71_ = lean_ctor_get(v_fproof_57_, 0);
v_isSharedCheck_80_ = !lean_is_exclusive(v_fproof_57_);
if (v_isSharedCheck_80_ == 0)
{
v___x_73_ = v_fproof_57_;
v_isShared_74_ = v_isSharedCheck_80_;
goto v_resetjp_72_;
}
else
{
lean_inc(v_val_71_);
lean_dec(v_fproof_57_);
v___x_73_ = lean_box(0);
v_isShared_74_ = v_isSharedCheck_80_;
goto v_resetjp_72_;
}
v_resetjp_72_:
{
lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_78_; 
v___x_75_ = l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkBVRefl(v___x_55_, v_snd_58_);
v___x_76_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_76_, 0, v_val_71_);
lean_ctor_set(v___x_76_, 1, v___x_75_);
if (v_isShared_74_ == 0)
{
lean_ctor_set(v___x_73_, 0, v___x_76_);
v___x_78_ = v___x_73_;
goto v_reusejp_77_;
}
else
{
lean_object* v_reuseFailAlloc_79_; 
v_reuseFailAlloc_79_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_79_, 0, v___x_76_);
v___x_78_ = v_reuseFailAlloc_79_;
goto v_reusejp_77_;
}
v_reusejp_77_:
{
return v___x_78_;
}
}
}
else
{
lean_object* v_val_81_; lean_object* v_val_82_; lean_object* v___x_84_; uint8_t v_isShared_85_; uint8_t v_isSharedCheck_90_; 
lean_dec_ref(v_snd_58_);
lean_dec(v___x_55_);
v_val_81_ = lean_ctor_get(v_fproof_57_, 0);
lean_inc(v_val_81_);
lean_dec_ref(v_fproof_57_);
v_val_82_ = lean_ctor_get(v_sproof_59_, 0);
v_isSharedCheck_90_ = !lean_is_exclusive(v_sproof_59_);
if (v_isSharedCheck_90_ == 0)
{
v___x_84_ = v_sproof_59_;
v_isShared_85_ = v_isSharedCheck_90_;
goto v_resetjp_83_;
}
else
{
lean_inc(v_val_82_);
lean_dec(v_sproof_59_);
v___x_84_ = lean_box(0);
v_isShared_85_ = v_isSharedCheck_90_;
goto v_resetjp_83_;
}
v_resetjp_83_:
{
lean_object* v___x_86_; lean_object* v___x_88_; 
v___x_86_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_86_, 0, v_val_81_);
lean_ctor_set(v___x_86_, 1, v_val_82_);
if (v_isShared_85_ == 0)
{
lean_ctor_set(v___x_84_, 0, v___x_86_);
v___x_88_ = v___x_84_;
goto v_reusejp_87_;
}
else
{
lean_object* v_reuseFailAlloc_89_; 
v_reuseFailAlloc_89_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_89_, 0, v___x_86_);
v___x_88_ = v_reuseFailAlloc_89_;
goto v_reusejp_87_;
}
v_reusejp_87_:
{
return v___x_88_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryCongrProof(lean_object* v_lhs_91_, lean_object* v_rhs_92_, lean_object* v_lhsExpr_93_, lean_object* v_rhsExpr_94_, lean_object* v_congrThm_95_, lean_object* v_a_96_, lean_object* v_a_97_, lean_object* v_a_98_, lean_object* v_a_99_, lean_object* v_a_100_){
_start:
{
lean_object* v_width_102_; lean_object* v_expr_103_; lean_object* v___x_104_; 
v_width_102_ = lean_ctor_get(v_lhs_91_, 0);
lean_inc_n(v_width_102_, 2);
v_expr_103_ = lean_ctor_get(v_lhs_91_, 4);
lean_inc_ref(v_expr_103_);
v___x_104_ = l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkEvalExpr(v_width_102_, v_expr_103_, v_a_96_, v_a_97_, v_a_98_, v_a_99_, v_a_100_);
if (lean_obj_tag(v___x_104_) == 0)
{
lean_object* v_a_105_; lean_object* v_width_106_; lean_object* v_expr_107_; lean_object* v___x_108_; 
v_a_105_ = lean_ctor_get(v___x_104_, 0);
lean_inc(v_a_105_);
lean_dec_ref(v___x_104_);
v_width_106_ = lean_ctor_get(v_rhs_92_, 0);
v_expr_107_ = lean_ctor_get(v_rhs_92_, 4);
lean_inc_ref(v_expr_107_);
lean_inc(v_width_106_);
v___x_108_ = l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkEvalExpr(v_width_106_, v_expr_107_, v_a_96_, v_a_97_, v_a_98_, v_a_99_, v_a_100_);
if (lean_obj_tag(v___x_108_) == 0)
{
lean_object* v_a_109_; lean_object* v___x_110_; 
v_a_109_ = lean_ctor_get(v___x_108_, 0);
lean_inc(v_a_109_);
lean_dec_ref(v___x_108_);
v___x_110_ = l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_evalsAtAtoms(v_lhs_91_, v_a_96_, v_a_97_, v_a_98_, v_a_99_, v_a_100_);
if (lean_obj_tag(v___x_110_) == 0)
{
lean_object* v_a_111_; lean_object* v___x_112_; 
v_a_111_ = lean_ctor_get(v___x_110_, 0);
lean_inc(v_a_111_);
lean_dec_ref(v___x_110_);
v___x_112_ = l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_evalsAtAtoms(v_rhs_92_, v_a_96_, v_a_97_, v_a_98_, v_a_99_, v_a_100_);
if (lean_obj_tag(v___x_112_) == 0)
{
lean_object* v_a_113_; lean_object* v___x_115_; uint8_t v_isShared_116_; uint8_t v_isSharedCheck_136_; 
v_a_113_ = lean_ctor_get(v___x_112_, 0);
v_isSharedCheck_136_ = !lean_is_exclusive(v___x_112_);
if (v_isSharedCheck_136_ == 0)
{
v___x_115_ = v___x_112_;
v_isShared_116_ = v_isSharedCheck_136_;
goto v_resetjp_114_;
}
else
{
lean_inc(v_a_113_);
lean_dec(v___x_112_);
v___x_115_ = lean_box(0);
v_isShared_116_ = v_isSharedCheck_136_;
goto v_resetjp_114_;
}
v_resetjp_114_:
{
lean_object* v___x_117_; 
lean_inc(v_a_109_);
lean_inc(v_a_105_);
v___x_117_ = l_Lean_Elab_Tactic_BVDecide_Frontend_M_simplifyBinaryProof_x27___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryCongrProof_spec__0(v_width_102_, v_a_105_, v_a_111_, v_a_109_, v_a_113_);
if (lean_obj_tag(v___x_117_) == 1)
{
lean_object* v_val_118_; lean_object* v___x_120_; uint8_t v_isShared_121_; uint8_t v_isSharedCheck_131_; 
v_val_118_ = lean_ctor_get(v___x_117_, 0);
v_isSharedCheck_131_ = !lean_is_exclusive(v___x_117_);
if (v_isSharedCheck_131_ == 0)
{
v___x_120_ = v___x_117_;
v_isShared_121_ = v_isSharedCheck_131_;
goto v_resetjp_119_;
}
else
{
lean_inc(v_val_118_);
lean_dec(v___x_117_);
v___x_120_ = lean_box(0);
v_isShared_121_ = v_isSharedCheck_131_;
goto v_resetjp_119_;
}
v_resetjp_119_:
{
lean_object* v_fst_122_; lean_object* v_snd_123_; lean_object* v___x_124_; lean_object* v___x_126_; 
v_fst_122_ = lean_ctor_get(v_val_118_, 0);
lean_inc(v_fst_122_);
v_snd_123_ = lean_ctor_get(v_val_118_, 1);
lean_inc(v_snd_123_);
lean_dec(v_val_118_);
v___x_124_ = l_Lean_mkApp6(v_congrThm_95_, v_lhsExpr_93_, v_rhsExpr_94_, v_a_105_, v_a_109_, v_fst_122_, v_snd_123_);
if (v_isShared_121_ == 0)
{
lean_ctor_set(v___x_120_, 0, v___x_124_);
v___x_126_ = v___x_120_;
goto v_reusejp_125_;
}
else
{
lean_object* v_reuseFailAlloc_130_; 
v_reuseFailAlloc_130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_130_, 0, v___x_124_);
v___x_126_ = v_reuseFailAlloc_130_;
goto v_reusejp_125_;
}
v_reusejp_125_:
{
lean_object* v___x_128_; 
if (v_isShared_116_ == 0)
{
lean_ctor_set(v___x_115_, 0, v___x_126_);
v___x_128_ = v___x_115_;
goto v_reusejp_127_;
}
else
{
lean_object* v_reuseFailAlloc_129_; 
v_reuseFailAlloc_129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_129_, 0, v___x_126_);
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
lean_object* v___x_132_; lean_object* v___x_134_; 
lean_dec(v___x_117_);
lean_dec(v_a_109_);
lean_dec(v_a_105_);
lean_dec_ref(v_congrThm_95_);
lean_dec_ref(v_rhsExpr_94_);
lean_dec_ref(v_lhsExpr_93_);
v___x_132_ = lean_box(0);
if (v_isShared_116_ == 0)
{
lean_ctor_set(v___x_115_, 0, v___x_132_);
v___x_134_ = v___x_115_;
goto v_reusejp_133_;
}
else
{
lean_object* v_reuseFailAlloc_135_; 
v_reuseFailAlloc_135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_135_, 0, v___x_132_);
v___x_134_ = v_reuseFailAlloc_135_;
goto v_reusejp_133_;
}
v_reusejp_133_:
{
return v___x_134_;
}
}
}
}
else
{
lean_dec(v_a_111_);
lean_dec(v_a_109_);
lean_dec(v_a_105_);
lean_dec(v_width_102_);
lean_dec_ref(v_congrThm_95_);
lean_dec_ref(v_rhsExpr_94_);
lean_dec_ref(v_lhsExpr_93_);
return v___x_112_;
}
}
else
{
lean_dec(v_a_109_);
lean_dec(v_a_105_);
lean_dec(v_width_102_);
lean_dec_ref(v_congrThm_95_);
lean_dec_ref(v_rhsExpr_94_);
lean_dec_ref(v_lhsExpr_93_);
lean_dec_ref(v_rhs_92_);
return v___x_110_;
}
}
else
{
lean_object* v_a_137_; lean_object* v___x_139_; uint8_t v_isShared_140_; uint8_t v_isSharedCheck_144_; 
lean_dec(v_a_105_);
lean_dec(v_width_102_);
lean_dec_ref(v_congrThm_95_);
lean_dec_ref(v_rhsExpr_94_);
lean_dec_ref(v_lhsExpr_93_);
lean_dec_ref(v_rhs_92_);
lean_dec_ref(v_lhs_91_);
v_a_137_ = lean_ctor_get(v___x_108_, 0);
v_isSharedCheck_144_ = !lean_is_exclusive(v___x_108_);
if (v_isSharedCheck_144_ == 0)
{
v___x_139_ = v___x_108_;
v_isShared_140_ = v_isSharedCheck_144_;
goto v_resetjp_138_;
}
else
{
lean_inc(v_a_137_);
lean_dec(v___x_108_);
v___x_139_ = lean_box(0);
v_isShared_140_ = v_isSharedCheck_144_;
goto v_resetjp_138_;
}
v_resetjp_138_:
{
lean_object* v___x_142_; 
if (v_isShared_140_ == 0)
{
v___x_142_ = v___x_139_;
goto v_reusejp_141_;
}
else
{
lean_object* v_reuseFailAlloc_143_; 
v_reuseFailAlloc_143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_143_, 0, v_a_137_);
v___x_142_ = v_reuseFailAlloc_143_;
goto v_reusejp_141_;
}
v_reusejp_141_:
{
return v___x_142_;
}
}
}
}
else
{
lean_object* v_a_145_; lean_object* v___x_147_; uint8_t v_isShared_148_; uint8_t v_isSharedCheck_152_; 
lean_dec(v_width_102_);
lean_dec_ref(v_congrThm_95_);
lean_dec_ref(v_rhsExpr_94_);
lean_dec_ref(v_lhsExpr_93_);
lean_dec_ref(v_rhs_92_);
lean_dec_ref(v_lhs_91_);
v_a_145_ = lean_ctor_get(v___x_104_, 0);
v_isSharedCheck_152_ = !lean_is_exclusive(v___x_104_);
if (v_isSharedCheck_152_ == 0)
{
v___x_147_ = v___x_104_;
v_isShared_148_ = v_isSharedCheck_152_;
goto v_resetjp_146_;
}
else
{
lean_inc(v_a_145_);
lean_dec(v___x_104_);
v___x_147_ = lean_box(0);
v_isShared_148_ = v_isSharedCheck_152_;
goto v_resetjp_146_;
}
v_resetjp_146_:
{
lean_object* v___x_150_; 
if (v_isShared_148_ == 0)
{
v___x_150_ = v___x_147_;
goto v_reusejp_149_;
}
else
{
lean_object* v_reuseFailAlloc_151_; 
v_reuseFailAlloc_151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_151_, 0, v_a_145_);
v___x_150_ = v_reuseFailAlloc_151_;
goto v_reusejp_149_;
}
v_reusejp_149_:
{
return v___x_150_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryCongrProof___boxed(lean_object* v_lhs_153_, lean_object* v_rhs_154_, lean_object* v_lhsExpr_155_, lean_object* v_rhsExpr_156_, lean_object* v_congrThm_157_, lean_object* v_a_158_, lean_object* v_a_159_, lean_object* v_a_160_, lean_object* v_a_161_, lean_object* v_a_162_, lean_object* v_a_163_){
_start:
{
lean_object* v_res_164_; 
v_res_164_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryCongrProof(v_lhs_153_, v_rhs_154_, v_lhsExpr_155_, v_rhsExpr_156_, v_congrThm_157_, v_a_158_, v_a_159_, v_a_160_, v_a_161_, v_a_162_);
lean_dec(v_a_162_);
lean_dec_ref(v_a_161_);
lean_dec(v_a_160_);
lean_dec_ref(v_a_159_);
lean_dec(v_a_158_);
return v_res_164_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryCongrProof(lean_object* v_inner_165_, lean_object* v_innerExpr_166_, lean_object* v_congrProof_167_, lean_object* v_a_168_, lean_object* v_a_169_, lean_object* v_a_170_, lean_object* v_a_171_, lean_object* v_a_172_){
_start:
{
lean_object* v_width_174_; lean_object* v_expr_175_; lean_object* v___x_176_; 
v_width_174_ = lean_ctor_get(v_inner_165_, 0);
lean_inc_n(v_width_174_, 2);
v_expr_175_ = lean_ctor_get(v_inner_165_, 4);
lean_inc_ref(v_expr_175_);
v___x_176_ = l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkEvalExpr(v_width_174_, v_expr_175_, v_a_168_, v_a_169_, v_a_170_, v_a_171_, v_a_172_);
if (lean_obj_tag(v___x_176_) == 0)
{
lean_object* v_a_177_; lean_object* v___x_178_; 
v_a_177_ = lean_ctor_get(v___x_176_, 0);
lean_inc(v_a_177_);
lean_dec_ref(v___x_176_);
v___x_178_ = l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_evalsAtAtoms(v_inner_165_, v_a_168_, v_a_169_, v_a_170_, v_a_171_, v_a_172_);
if (lean_obj_tag(v___x_178_) == 0)
{
lean_object* v_a_179_; lean_object* v___x_181_; uint8_t v_isShared_182_; uint8_t v_isSharedCheck_200_; 
v_a_179_ = lean_ctor_get(v___x_178_, 0);
v_isSharedCheck_200_ = !lean_is_exclusive(v___x_178_);
if (v_isSharedCheck_200_ == 0)
{
v___x_181_ = v___x_178_;
v_isShared_182_ = v_isSharedCheck_200_;
goto v_resetjp_180_;
}
else
{
lean_inc(v_a_179_);
lean_dec(v___x_178_);
v___x_181_ = lean_box(0);
v_isShared_182_ = v_isSharedCheck_200_;
goto v_resetjp_180_;
}
v_resetjp_180_:
{
if (lean_obj_tag(v_a_179_) == 1)
{
lean_object* v_val_183_; lean_object* v___x_185_; uint8_t v_isShared_186_; uint8_t v_isSharedCheck_195_; 
v_val_183_ = lean_ctor_get(v_a_179_, 0);
v_isSharedCheck_195_ = !lean_is_exclusive(v_a_179_);
if (v_isSharedCheck_195_ == 0)
{
v___x_185_ = v_a_179_;
v_isShared_186_ = v_isSharedCheck_195_;
goto v_resetjp_184_;
}
else
{
lean_inc(v_val_183_);
lean_dec(v_a_179_);
v___x_185_ = lean_box(0);
v_isShared_186_ = v_isSharedCheck_195_;
goto v_resetjp_184_;
}
v_resetjp_184_:
{
lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_190_; 
v___x_187_ = l_Lean_mkNatLit(v_width_174_);
v___x_188_ = l_Lean_mkApp4(v_congrProof_167_, v___x_187_, v_innerExpr_166_, v_a_177_, v_val_183_);
if (v_isShared_186_ == 0)
{
lean_ctor_set(v___x_185_, 0, v___x_188_);
v___x_190_ = v___x_185_;
goto v_reusejp_189_;
}
else
{
lean_object* v_reuseFailAlloc_194_; 
v_reuseFailAlloc_194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_194_, 0, v___x_188_);
v___x_190_ = v_reuseFailAlloc_194_;
goto v_reusejp_189_;
}
v_reusejp_189_:
{
lean_object* v___x_192_; 
if (v_isShared_182_ == 0)
{
lean_ctor_set(v___x_181_, 0, v___x_190_);
v___x_192_ = v___x_181_;
goto v_reusejp_191_;
}
else
{
lean_object* v_reuseFailAlloc_193_; 
v_reuseFailAlloc_193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_193_, 0, v___x_190_);
v___x_192_ = v_reuseFailAlloc_193_;
goto v_reusejp_191_;
}
v_reusejp_191_:
{
return v___x_192_;
}
}
}
}
else
{
lean_object* v___x_196_; lean_object* v___x_198_; 
lean_dec(v_a_179_);
lean_dec(v_a_177_);
lean_dec(v_width_174_);
lean_dec_ref(v_congrProof_167_);
lean_dec_ref(v_innerExpr_166_);
v___x_196_ = lean_box(0);
if (v_isShared_182_ == 0)
{
lean_ctor_set(v___x_181_, 0, v___x_196_);
v___x_198_ = v___x_181_;
goto v_reusejp_197_;
}
else
{
lean_object* v_reuseFailAlloc_199_; 
v_reuseFailAlloc_199_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_199_, 0, v___x_196_);
v___x_198_ = v_reuseFailAlloc_199_;
goto v_reusejp_197_;
}
v_reusejp_197_:
{
return v___x_198_;
}
}
}
}
else
{
lean_dec(v_a_177_);
lean_dec(v_width_174_);
lean_dec_ref(v_congrProof_167_);
lean_dec_ref(v_innerExpr_166_);
return v___x_178_;
}
}
else
{
lean_object* v_a_201_; lean_object* v___x_203_; uint8_t v_isShared_204_; uint8_t v_isSharedCheck_208_; 
lean_dec(v_width_174_);
lean_dec_ref(v_congrProof_167_);
lean_dec_ref(v_innerExpr_166_);
lean_dec_ref(v_inner_165_);
v_a_201_ = lean_ctor_get(v___x_176_, 0);
v_isSharedCheck_208_ = !lean_is_exclusive(v___x_176_);
if (v_isSharedCheck_208_ == 0)
{
v___x_203_ = v___x_176_;
v_isShared_204_ = v_isSharedCheck_208_;
goto v_resetjp_202_;
}
else
{
lean_inc(v_a_201_);
lean_dec(v___x_176_);
v___x_203_ = lean_box(0);
v_isShared_204_ = v_isSharedCheck_208_;
goto v_resetjp_202_;
}
v_resetjp_202_:
{
lean_object* v___x_206_; 
if (v_isShared_204_ == 0)
{
v___x_206_ = v___x_203_;
goto v_reusejp_205_;
}
else
{
lean_object* v_reuseFailAlloc_207_; 
v_reuseFailAlloc_207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_207_, 0, v_a_201_);
v___x_206_ = v_reuseFailAlloc_207_;
goto v_reusejp_205_;
}
v_reusejp_205_:
{
return v___x_206_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryCongrProof___boxed(lean_object* v_inner_209_, lean_object* v_innerExpr_210_, lean_object* v_congrProof_211_, lean_object* v_a_212_, lean_object* v_a_213_, lean_object* v_a_214_, lean_object* v_a_215_, lean_object* v_a_216_, lean_object* v_a_217_){
_start:
{
lean_object* v_res_218_; 
v_res_218_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryCongrProof(v_inner_209_, v_innerExpr_210_, v_congrProof_211_, v_a_212_, v_a_213_, v_a_214_, v_a_215_, v_a_216_);
lean_dec(v_a_216_);
lean_dec_ref(v_a_215_);
lean_dec(v_a_214_);
lean_dec_ref(v_a_213_);
lean_dec(v_a_212_);
return v_res_218_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom_spec__2_spec__12_spec__17___redArg(lean_object* v_a_219_, lean_object* v_x_220_){
_start:
{
if (lean_obj_tag(v_x_220_) == 0)
{
lean_object* v___x_221_; 
v___x_221_ = lean_box(0);
return v___x_221_;
}
else
{
lean_object* v_key_222_; lean_object* v_value_223_; lean_object* v_tail_224_; uint8_t v___x_225_; 
v_key_222_ = lean_ctor_get(v_x_220_, 0);
v_value_223_ = lean_ctor_get(v_x_220_, 1);
v_tail_224_ = lean_ctor_get(v_x_220_, 2);
v___x_225_ = lean_expr_eqv(v_key_222_, v_a_219_);
if (v___x_225_ == 0)
{
v_x_220_ = v_tail_224_;
goto _start;
}
else
{
lean_object* v___x_227_; 
lean_inc(v_value_223_);
v___x_227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_227_, 0, v_value_223_);
return v___x_227_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom_spec__2_spec__12_spec__17___redArg___boxed(lean_object* v_a_228_, lean_object* v_x_229_){
_start:
{
lean_object* v_res_230_; 
v_res_230_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom_spec__2_spec__12_spec__17___redArg(v_a_228_, v_x_229_);
lean_dec(v_x_229_);
lean_dec_ref(v_a_228_);
return v_res_230_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom_spec__2_spec__12___redArg(lean_object* v_m_231_, lean_object* v_a_232_){
_start:
{
lean_object* v_buckets_233_; lean_object* v___x_234_; uint64_t v___x_235_; uint64_t v___x_236_; uint64_t v___x_237_; uint64_t v_fold_238_; uint64_t v___x_239_; uint64_t v___x_240_; uint64_t v___x_241_; size_t v___x_242_; size_t v___x_243_; size_t v___x_244_; size_t v___x_245_; size_t v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; 
v_buckets_233_ = lean_ctor_get(v_m_231_, 1);
v___x_234_ = lean_array_get_size(v_buckets_233_);
v___x_235_ = l_Lean_Expr_hash(v_a_232_);
v___x_236_ = 32ULL;
v___x_237_ = lean_uint64_shift_right(v___x_235_, v___x_236_);
v_fold_238_ = lean_uint64_xor(v___x_235_, v___x_237_);
v___x_239_ = 16ULL;
v___x_240_ = lean_uint64_shift_right(v_fold_238_, v___x_239_);
v___x_241_ = lean_uint64_xor(v_fold_238_, v___x_240_);
v___x_242_ = lean_uint64_to_usize(v___x_241_);
v___x_243_ = lean_usize_of_nat(v___x_234_);
v___x_244_ = ((size_t)1ULL);
v___x_245_ = lean_usize_sub(v___x_243_, v___x_244_);
v___x_246_ = lean_usize_land(v___x_242_, v___x_245_);
v___x_247_ = lean_array_uget_borrowed(v_buckets_233_, v___x_246_);
v___x_248_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom_spec__2_spec__12_spec__17___redArg(v_a_232_, v___x_247_);
return v___x_248_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom_spec__2_spec__12___redArg___boxed(lean_object* v_m_249_, lean_object* v_a_250_){
_start:
{
lean_object* v_res_251_; 
v_res_251_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom_spec__2_spec__12___redArg(v_m_249_, v_a_250_);
lean_dec_ref(v_a_250_);
lean_dec_ref(v_m_249_);
return v_res_251_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13_spec__19___redArg(lean_object* v_a_252_, lean_object* v_x_253_){
_start:
{
if (lean_obj_tag(v_x_253_) == 0)
{
uint8_t v___x_254_; 
v___x_254_ = 0;
return v___x_254_;
}
else
{
lean_object* v_key_255_; lean_object* v_tail_256_; uint8_t v___x_257_; 
v_key_255_ = lean_ctor_get(v_x_253_, 0);
v_tail_256_ = lean_ctor_get(v_x_253_, 2);
v___x_257_ = lean_expr_eqv(v_key_255_, v_a_252_);
if (v___x_257_ == 0)
{
v_x_253_ = v_tail_256_;
goto _start;
}
else
{
return v___x_257_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13_spec__19___redArg___boxed(lean_object* v_a_259_, lean_object* v_x_260_){
_start:
{
uint8_t v_res_261_; lean_object* v_r_262_; 
v_res_261_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13_spec__19___redArg(v_a_259_, v_x_260_);
lean_dec(v_x_260_);
lean_dec_ref(v_a_259_);
v_r_262_ = lean_box(v_res_261_);
return v_r_262_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13_spec__20_spec__25_spec__26___redArg(lean_object* v_x_263_, lean_object* v_x_264_){
_start:
{
if (lean_obj_tag(v_x_264_) == 0)
{
return v_x_263_;
}
else
{
lean_object* v_key_265_; lean_object* v_value_266_; lean_object* v_tail_267_; lean_object* v___x_269_; uint8_t v_isShared_270_; uint8_t v_isSharedCheck_290_; 
v_key_265_ = lean_ctor_get(v_x_264_, 0);
v_value_266_ = lean_ctor_get(v_x_264_, 1);
v_tail_267_ = lean_ctor_get(v_x_264_, 2);
v_isSharedCheck_290_ = !lean_is_exclusive(v_x_264_);
if (v_isSharedCheck_290_ == 0)
{
v___x_269_ = v_x_264_;
v_isShared_270_ = v_isSharedCheck_290_;
goto v_resetjp_268_;
}
else
{
lean_inc(v_tail_267_);
lean_inc(v_value_266_);
lean_inc(v_key_265_);
lean_dec(v_x_264_);
v___x_269_ = lean_box(0);
v_isShared_270_ = v_isSharedCheck_290_;
goto v_resetjp_268_;
}
v_resetjp_268_:
{
lean_object* v___x_271_; uint64_t v___x_272_; uint64_t v___x_273_; uint64_t v___x_274_; uint64_t v_fold_275_; uint64_t v___x_276_; uint64_t v___x_277_; uint64_t v___x_278_; size_t v___x_279_; size_t v___x_280_; size_t v___x_281_; size_t v___x_282_; size_t v___x_283_; lean_object* v___x_284_; lean_object* v___x_286_; 
v___x_271_ = lean_array_get_size(v_x_263_);
v___x_272_ = l_Lean_Expr_hash(v_key_265_);
v___x_273_ = 32ULL;
v___x_274_ = lean_uint64_shift_right(v___x_272_, v___x_273_);
v_fold_275_ = lean_uint64_xor(v___x_272_, v___x_274_);
v___x_276_ = 16ULL;
v___x_277_ = lean_uint64_shift_right(v_fold_275_, v___x_276_);
v___x_278_ = lean_uint64_xor(v_fold_275_, v___x_277_);
v___x_279_ = lean_uint64_to_usize(v___x_278_);
v___x_280_ = lean_usize_of_nat(v___x_271_);
v___x_281_ = ((size_t)1ULL);
v___x_282_ = lean_usize_sub(v___x_280_, v___x_281_);
v___x_283_ = lean_usize_land(v___x_279_, v___x_282_);
v___x_284_ = lean_array_uget_borrowed(v_x_263_, v___x_283_);
lean_inc(v___x_284_);
if (v_isShared_270_ == 0)
{
lean_ctor_set(v___x_269_, 2, v___x_284_);
v___x_286_ = v___x_269_;
goto v_reusejp_285_;
}
else
{
lean_object* v_reuseFailAlloc_289_; 
v_reuseFailAlloc_289_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_289_, 0, v_key_265_);
lean_ctor_set(v_reuseFailAlloc_289_, 1, v_value_266_);
lean_ctor_set(v_reuseFailAlloc_289_, 2, v___x_284_);
v___x_286_ = v_reuseFailAlloc_289_;
goto v_reusejp_285_;
}
v_reusejp_285_:
{
lean_object* v___x_287_; 
v___x_287_ = lean_array_uset(v_x_263_, v___x_283_, v___x_286_);
v_x_263_ = v___x_287_;
v_x_264_ = v_tail_267_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13_spec__20_spec__25___redArg(lean_object* v_i_291_, lean_object* v_source_292_, lean_object* v_target_293_){
_start:
{
lean_object* v___x_294_; uint8_t v___x_295_; 
v___x_294_ = lean_array_get_size(v_source_292_);
v___x_295_ = lean_nat_dec_lt(v_i_291_, v___x_294_);
if (v___x_295_ == 0)
{
lean_dec_ref(v_source_292_);
lean_dec(v_i_291_);
return v_target_293_;
}
else
{
lean_object* v_es_296_; lean_object* v___x_297_; lean_object* v_source_298_; lean_object* v_target_299_; lean_object* v___x_300_; lean_object* v___x_301_; 
v_es_296_ = lean_array_fget(v_source_292_, v_i_291_);
v___x_297_ = lean_box(0);
v_source_298_ = lean_array_fset(v_source_292_, v_i_291_, v___x_297_);
v_target_299_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13_spec__20_spec__25_spec__26___redArg(v_target_293_, v_es_296_);
v___x_300_ = lean_unsigned_to_nat(1u);
v___x_301_ = lean_nat_add(v_i_291_, v___x_300_);
lean_dec(v_i_291_);
v_i_291_ = v___x_301_;
v_source_292_ = v_source_298_;
v_target_293_ = v_target_299_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13_spec__20___redArg(lean_object* v_data_303_){
_start:
{
lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v_nbuckets_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; 
v___x_304_ = lean_array_get_size(v_data_303_);
v___x_305_ = lean_unsigned_to_nat(2u);
v_nbuckets_306_ = lean_nat_mul(v___x_304_, v___x_305_);
v___x_307_ = lean_unsigned_to_nat(0u);
v___x_308_ = lean_box(0);
v___x_309_ = lean_mk_array(v_nbuckets_306_, v___x_308_);
v___x_310_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13_spec__20_spec__25___redArg(v___x_307_, v_data_303_, v___x_309_);
return v___x_310_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13_spec__21___redArg(lean_object* v_a_311_, lean_object* v_b_312_, lean_object* v_x_313_){
_start:
{
if (lean_obj_tag(v_x_313_) == 0)
{
lean_dec(v_b_312_);
lean_dec_ref(v_a_311_);
return v_x_313_;
}
else
{
lean_object* v_key_314_; lean_object* v_value_315_; lean_object* v_tail_316_; lean_object* v___x_318_; uint8_t v_isShared_319_; uint8_t v_isSharedCheck_328_; 
v_key_314_ = lean_ctor_get(v_x_313_, 0);
v_value_315_ = lean_ctor_get(v_x_313_, 1);
v_tail_316_ = lean_ctor_get(v_x_313_, 2);
v_isSharedCheck_328_ = !lean_is_exclusive(v_x_313_);
if (v_isSharedCheck_328_ == 0)
{
v___x_318_ = v_x_313_;
v_isShared_319_ = v_isSharedCheck_328_;
goto v_resetjp_317_;
}
else
{
lean_inc(v_tail_316_);
lean_inc(v_value_315_);
lean_inc(v_key_314_);
lean_dec(v_x_313_);
v___x_318_ = lean_box(0);
v_isShared_319_ = v_isSharedCheck_328_;
goto v_resetjp_317_;
}
v_resetjp_317_:
{
uint8_t v___x_320_; 
v___x_320_ = lean_expr_eqv(v_key_314_, v_a_311_);
if (v___x_320_ == 0)
{
lean_object* v___x_321_; lean_object* v___x_323_; 
v___x_321_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13_spec__21___redArg(v_a_311_, v_b_312_, v_tail_316_);
if (v_isShared_319_ == 0)
{
lean_ctor_set(v___x_318_, 2, v___x_321_);
v___x_323_ = v___x_318_;
goto v_reusejp_322_;
}
else
{
lean_object* v_reuseFailAlloc_324_; 
v_reuseFailAlloc_324_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_324_, 0, v_key_314_);
lean_ctor_set(v_reuseFailAlloc_324_, 1, v_value_315_);
lean_ctor_set(v_reuseFailAlloc_324_, 2, v___x_321_);
v___x_323_ = v_reuseFailAlloc_324_;
goto v_reusejp_322_;
}
v_reusejp_322_:
{
return v___x_323_;
}
}
else
{
lean_object* v___x_326_; 
lean_dec(v_value_315_);
lean_dec(v_key_314_);
if (v_isShared_319_ == 0)
{
lean_ctor_set(v___x_318_, 1, v_b_312_);
lean_ctor_set(v___x_318_, 0, v_a_311_);
v___x_326_ = v___x_318_;
goto v_reusejp_325_;
}
else
{
lean_object* v_reuseFailAlloc_327_; 
v_reuseFailAlloc_327_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_327_, 0, v_a_311_);
lean_ctor_set(v_reuseFailAlloc_327_, 1, v_b_312_);
lean_ctor_set(v_reuseFailAlloc_327_, 2, v_tail_316_);
v___x_326_ = v_reuseFailAlloc_327_;
goto v_reusejp_325_;
}
v_reusejp_325_:
{
return v___x_326_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13___redArg(lean_object* v_m_329_, lean_object* v_a_330_, lean_object* v_b_331_){
_start:
{
lean_object* v_size_332_; lean_object* v_buckets_333_; lean_object* v___x_335_; uint8_t v_isShared_336_; uint8_t v_isSharedCheck_376_; 
v_size_332_ = lean_ctor_get(v_m_329_, 0);
v_buckets_333_ = lean_ctor_get(v_m_329_, 1);
v_isSharedCheck_376_ = !lean_is_exclusive(v_m_329_);
if (v_isSharedCheck_376_ == 0)
{
v___x_335_ = v_m_329_;
v_isShared_336_ = v_isSharedCheck_376_;
goto v_resetjp_334_;
}
else
{
lean_inc(v_buckets_333_);
lean_inc(v_size_332_);
lean_dec(v_m_329_);
v___x_335_ = lean_box(0);
v_isShared_336_ = v_isSharedCheck_376_;
goto v_resetjp_334_;
}
v_resetjp_334_:
{
lean_object* v___x_337_; uint64_t v___x_338_; uint64_t v___x_339_; uint64_t v___x_340_; uint64_t v_fold_341_; uint64_t v___x_342_; uint64_t v___x_343_; uint64_t v___x_344_; size_t v___x_345_; size_t v___x_346_; size_t v___x_347_; size_t v___x_348_; size_t v___x_349_; lean_object* v_bkt_350_; uint8_t v___x_351_; 
v___x_337_ = lean_array_get_size(v_buckets_333_);
v___x_338_ = l_Lean_Expr_hash(v_a_330_);
v___x_339_ = 32ULL;
v___x_340_ = lean_uint64_shift_right(v___x_338_, v___x_339_);
v_fold_341_ = lean_uint64_xor(v___x_338_, v___x_340_);
v___x_342_ = 16ULL;
v___x_343_ = lean_uint64_shift_right(v_fold_341_, v___x_342_);
v___x_344_ = lean_uint64_xor(v_fold_341_, v___x_343_);
v___x_345_ = lean_uint64_to_usize(v___x_344_);
v___x_346_ = lean_usize_of_nat(v___x_337_);
v___x_347_ = ((size_t)1ULL);
v___x_348_ = lean_usize_sub(v___x_346_, v___x_347_);
v___x_349_ = lean_usize_land(v___x_345_, v___x_348_);
v_bkt_350_ = lean_array_uget_borrowed(v_buckets_333_, v___x_349_);
v___x_351_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13_spec__19___redArg(v_a_330_, v_bkt_350_);
if (v___x_351_ == 0)
{
lean_object* v___x_352_; lean_object* v_size_x27_353_; lean_object* v___x_354_; lean_object* v_buckets_x27_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; uint8_t v___x_361_; 
v___x_352_ = lean_unsigned_to_nat(1u);
v_size_x27_353_ = lean_nat_add(v_size_332_, v___x_352_);
lean_dec(v_size_332_);
lean_inc(v_bkt_350_);
v___x_354_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_354_, 0, v_a_330_);
lean_ctor_set(v___x_354_, 1, v_b_331_);
lean_ctor_set(v___x_354_, 2, v_bkt_350_);
v_buckets_x27_355_ = lean_array_uset(v_buckets_333_, v___x_349_, v___x_354_);
v___x_356_ = lean_unsigned_to_nat(4u);
v___x_357_ = lean_nat_mul(v_size_x27_353_, v___x_356_);
v___x_358_ = lean_unsigned_to_nat(3u);
v___x_359_ = lean_nat_div(v___x_357_, v___x_358_);
lean_dec(v___x_357_);
v___x_360_ = lean_array_get_size(v_buckets_x27_355_);
v___x_361_ = lean_nat_dec_le(v___x_359_, v___x_360_);
lean_dec(v___x_359_);
if (v___x_361_ == 0)
{
lean_object* v_val_362_; lean_object* v___x_364_; 
v_val_362_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13_spec__20___redArg(v_buckets_x27_355_);
if (v_isShared_336_ == 0)
{
lean_ctor_set(v___x_335_, 1, v_val_362_);
lean_ctor_set(v___x_335_, 0, v_size_x27_353_);
v___x_364_ = v___x_335_;
goto v_reusejp_363_;
}
else
{
lean_object* v_reuseFailAlloc_365_; 
v_reuseFailAlloc_365_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_365_, 0, v_size_x27_353_);
lean_ctor_set(v_reuseFailAlloc_365_, 1, v_val_362_);
v___x_364_ = v_reuseFailAlloc_365_;
goto v_reusejp_363_;
}
v_reusejp_363_:
{
return v___x_364_;
}
}
else
{
lean_object* v___x_367_; 
if (v_isShared_336_ == 0)
{
lean_ctor_set(v___x_335_, 1, v_buckets_x27_355_);
lean_ctor_set(v___x_335_, 0, v_size_x27_353_);
v___x_367_ = v___x_335_;
goto v_reusejp_366_;
}
else
{
lean_object* v_reuseFailAlloc_368_; 
v_reuseFailAlloc_368_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_368_, 0, v_size_x27_353_);
lean_ctor_set(v_reuseFailAlloc_368_, 1, v_buckets_x27_355_);
v___x_367_ = v_reuseFailAlloc_368_;
goto v_reusejp_366_;
}
v_reusejp_366_:
{
return v___x_367_;
}
}
}
else
{
lean_object* v___x_369_; lean_object* v_buckets_x27_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_374_; 
lean_inc(v_bkt_350_);
v___x_369_ = lean_box(0);
v_buckets_x27_370_ = lean_array_uset(v_buckets_333_, v___x_349_, v___x_369_);
v___x_371_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13_spec__21___redArg(v_a_330_, v_b_331_, v_bkt_350_);
v___x_372_ = lean_array_uset(v_buckets_x27_370_, v___x_349_, v___x_371_);
if (v_isShared_336_ == 0)
{
lean_ctor_set(v___x_335_, 1, v___x_372_);
v___x_374_ = v___x_335_;
goto v_reusejp_373_;
}
else
{
lean_object* v_reuseFailAlloc_375_; 
v_reuseFailAlloc_375_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_375_, 0, v_size_332_);
lean_ctor_set(v_reuseFailAlloc_375_, 1, v___x_372_);
v___x_374_ = v_reuseFailAlloc_375_;
goto v_reusejp_373_;
}
v_reusejp_373_:
{
return v___x_374_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go_spec__12_spec__20(lean_object* v_msgData_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_){
_start:
{
lean_object* v___x_383_; lean_object* v_env_384_; lean_object* v___x_385_; lean_object* v_mctx_386_; lean_object* v_lctx_387_; lean_object* v_options_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; 
v___x_383_ = lean_st_ref_get(v___y_381_);
v_env_384_ = lean_ctor_get(v___x_383_, 0);
lean_inc_ref(v_env_384_);
lean_dec(v___x_383_);
v___x_385_ = lean_st_ref_get(v___y_379_);
v_mctx_386_ = lean_ctor_get(v___x_385_, 0);
lean_inc_ref(v_mctx_386_);
lean_dec(v___x_385_);
v_lctx_387_ = lean_ctor_get(v___y_378_, 2);
v_options_388_ = lean_ctor_get(v___y_380_, 2);
lean_inc_ref(v_options_388_);
lean_inc_ref(v_lctx_387_);
v___x_389_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_389_, 0, v_env_384_);
lean_ctor_set(v___x_389_, 1, v_mctx_386_);
lean_ctor_set(v___x_389_, 2, v_lctx_387_);
lean_ctor_set(v___x_389_, 3, v_options_388_);
v___x_390_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_390_, 0, v___x_389_);
lean_ctor_set(v___x_390_, 1, v_msgData_377_);
v___x_391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_391_, 0, v___x_390_);
return v___x_391_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go_spec__12_spec__20___boxed(lean_object* v_msgData_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_, lean_object* v___y_397_){
_start:
{
lean_object* v_res_398_; 
v_res_398_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go_spec__12_spec__20(v_msgData_392_, v___y_393_, v___y_394_, v___y_395_, v___y_396_);
lean_dec(v___y_396_);
lean_dec_ref(v___y_395_);
lean_dec(v___y_394_);
lean_dec_ref(v___y_393_);
return v_res_398_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go_spec__12___redArg(lean_object* v_msg_399_, lean_object* v___y_400_, lean_object* v___y_401_, lean_object* v___y_402_, lean_object* v___y_403_){
_start:
{
lean_object* v_ref_405_; lean_object* v___x_406_; lean_object* v_a_407_; lean_object* v___x_409_; uint8_t v_isShared_410_; uint8_t v_isSharedCheck_415_; 
v_ref_405_ = lean_ctor_get(v___y_402_, 5);
v___x_406_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go_spec__12_spec__20(v_msg_399_, v___y_400_, v___y_401_, v___y_402_, v___y_403_);
v_a_407_ = lean_ctor_get(v___x_406_, 0);
v_isSharedCheck_415_ = !lean_is_exclusive(v___x_406_);
if (v_isSharedCheck_415_ == 0)
{
v___x_409_ = v___x_406_;
v_isShared_410_ = v_isSharedCheck_415_;
goto v_resetjp_408_;
}
else
{
lean_inc(v_a_407_);
lean_dec(v___x_406_);
v___x_409_ = lean_box(0);
v_isShared_410_ = v_isSharedCheck_415_;
goto v_resetjp_408_;
}
v_resetjp_408_:
{
lean_object* v___x_411_; lean_object* v___x_413_; 
lean_inc(v_ref_405_);
v___x_411_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_411_, 0, v_ref_405_);
lean_ctor_set(v___x_411_, 1, v_a_407_);
if (v_isShared_410_ == 0)
{
lean_ctor_set_tag(v___x_409_, 1);
lean_ctor_set(v___x_409_, 0, v___x_411_);
v___x_413_ = v___x_409_;
goto v_reusejp_412_;
}
else
{
lean_object* v_reuseFailAlloc_414_; 
v_reuseFailAlloc_414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_414_, 0, v___x_411_);
v___x_413_ = v_reuseFailAlloc_414_;
goto v_reusejp_412_;
}
v_reusejp_412_:
{
return v___x_413_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go_spec__12___redArg___boxed(lean_object* v_msg_416_, lean_object* v___y_417_, lean_object* v___y_418_, lean_object* v___y_419_, lean_object* v___y_420_, lean_object* v___y_421_){
_start:
{
lean_object* v_res_422_; 
v_res_422_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go_spec__12___redArg(v_msg_416_, v___y_417_, v___y_418_, v___y_419_, v___y_420_);
lean_dec(v___y_420_);
lean_dec_ref(v___y_419_);
lean_dec(v___y_418_);
lean_dec_ref(v___y_417_);
return v_res_422_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_M_simplifyBinaryProof_x27___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go_spec__13(lean_object* v___x_423_, lean_object* v___x_424_, lean_object* v_fst_425_, lean_object* v_fproof_426_, lean_object* v_snd_427_, lean_object* v_sproof_428_){
_start:
{
if (lean_obj_tag(v_fproof_426_) == 0)
{
lean_dec_ref(v_snd_427_);
lean_dec(v___x_424_);
if (lean_obj_tag(v_sproof_428_) == 0)
{
lean_object* v___x_429_; 
lean_dec_ref(v_fst_425_);
lean_dec(v___x_423_);
v___x_429_ = lean_box(0);
return v___x_429_;
}
else
{
lean_object* v_val_430_; lean_object* v___x_432_; uint8_t v_isShared_433_; uint8_t v_isSharedCheck_439_; 
v_val_430_ = lean_ctor_get(v_sproof_428_, 0);
v_isSharedCheck_439_ = !lean_is_exclusive(v_sproof_428_);
if (v_isSharedCheck_439_ == 0)
{
v___x_432_ = v_sproof_428_;
v_isShared_433_ = v_isSharedCheck_439_;
goto v_resetjp_431_;
}
else
{
lean_inc(v_val_430_);
lean_dec(v_sproof_428_);
v___x_432_ = lean_box(0);
v_isShared_433_ = v_isSharedCheck_439_;
goto v_resetjp_431_;
}
v_resetjp_431_:
{
lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_437_; 
v___x_434_ = l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkBVRefl(v___x_423_, v_fst_425_);
v___x_435_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_435_, 0, v___x_434_);
lean_ctor_set(v___x_435_, 1, v_val_430_);
if (v_isShared_433_ == 0)
{
lean_ctor_set(v___x_432_, 0, v___x_435_);
v___x_437_ = v___x_432_;
goto v_reusejp_436_;
}
else
{
lean_object* v_reuseFailAlloc_438_; 
v_reuseFailAlloc_438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_438_, 0, v___x_435_);
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
else
{
lean_dec_ref(v_fst_425_);
lean_dec(v___x_423_);
if (lean_obj_tag(v_sproof_428_) == 0)
{
lean_object* v_val_440_; lean_object* v___x_442_; uint8_t v_isShared_443_; uint8_t v_isSharedCheck_449_; 
v_val_440_ = lean_ctor_get(v_fproof_426_, 0);
v_isSharedCheck_449_ = !lean_is_exclusive(v_fproof_426_);
if (v_isSharedCheck_449_ == 0)
{
v___x_442_ = v_fproof_426_;
v_isShared_443_ = v_isSharedCheck_449_;
goto v_resetjp_441_;
}
else
{
lean_inc(v_val_440_);
lean_dec(v_fproof_426_);
v___x_442_ = lean_box(0);
v_isShared_443_ = v_isSharedCheck_449_;
goto v_resetjp_441_;
}
v_resetjp_441_:
{
lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_447_; 
v___x_444_ = l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkBVRefl(v___x_424_, v_snd_427_);
v___x_445_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_445_, 0, v_val_440_);
lean_ctor_set(v___x_445_, 1, v___x_444_);
if (v_isShared_443_ == 0)
{
lean_ctor_set(v___x_442_, 0, v___x_445_);
v___x_447_ = v___x_442_;
goto v_reusejp_446_;
}
else
{
lean_object* v_reuseFailAlloc_448_; 
v_reuseFailAlloc_448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_448_, 0, v___x_445_);
v___x_447_ = v_reuseFailAlloc_448_;
goto v_reusejp_446_;
}
v_reusejp_446_:
{
return v___x_447_;
}
}
}
else
{
lean_object* v_val_450_; lean_object* v_val_451_; lean_object* v___x_453_; uint8_t v_isShared_454_; uint8_t v_isSharedCheck_459_; 
lean_dec_ref(v_snd_427_);
lean_dec(v___x_424_);
v_val_450_ = lean_ctor_get(v_fproof_426_, 0);
lean_inc(v_val_450_);
lean_dec_ref(v_fproof_426_);
v_val_451_ = lean_ctor_get(v_sproof_428_, 0);
v_isSharedCheck_459_ = !lean_is_exclusive(v_sproof_428_);
if (v_isSharedCheck_459_ == 0)
{
v___x_453_ = v_sproof_428_;
v_isShared_454_ = v_isSharedCheck_459_;
goto v_resetjp_452_;
}
else
{
lean_inc(v_val_451_);
lean_dec(v_sproof_428_);
v___x_453_ = lean_box(0);
v_isShared_454_ = v_isSharedCheck_459_;
goto v_resetjp_452_;
}
v_resetjp_452_:
{
lean_object* v___x_455_; lean_object* v___x_457_; 
v___x_455_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_455_, 0, v_val_450_);
lean_ctor_set(v___x_455_, 1, v_val_451_);
if (v_isShared_454_ == 0)
{
lean_ctor_set(v___x_453_, 0, v___x_455_);
v___x_457_ = v___x_453_;
goto v_reusejp_456_;
}
else
{
lean_object* v_reuseFailAlloc_458_; 
v_reuseFailAlloc_458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_458_, 0, v___x_455_);
v___x_457_ = v_reuseFailAlloc_458_;
goto v_reusejp_456_;
}
v_reusejp_456_:
{
return v___x_457_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___lam__0(lean_object* v_width_462_, lean_object* v_expr_463_, lean_object* v_width_464_, lean_object* v_expr_465_, lean_object* v_val_466_, lean_object* v_val_467_, lean_object* v___x_468_, lean_object* v___x_469_, lean_object* v___x_470_, lean_object* v___x_471_, lean_object* v___x_472_, lean_object* v___x_473_, lean_object* v___x_474_, lean_object* v_arg_475_, lean_object* v_arg_476_, lean_object* v___y_477_, lean_object* v___y_478_, lean_object* v___y_479_, lean_object* v___y_480_, lean_object* v___y_481_){
_start:
{
lean_object* v___x_483_; 
lean_inc(v_width_462_);
v___x_483_ = l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkEvalExpr(v_width_462_, v_expr_463_, v___y_477_, v___y_478_, v___y_479_, v___y_480_, v___y_481_);
if (lean_obj_tag(v___x_483_) == 0)
{
lean_object* v_a_484_; lean_object* v___x_485_; 
v_a_484_ = lean_ctor_get(v___x_483_, 0);
lean_inc(v_a_484_);
lean_dec_ref(v___x_483_);
lean_inc(v_width_464_);
v___x_485_ = l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkEvalExpr(v_width_464_, v_expr_465_, v___y_477_, v___y_478_, v___y_479_, v___y_480_, v___y_481_);
if (lean_obj_tag(v___x_485_) == 0)
{
lean_object* v_a_486_; lean_object* v___x_487_; 
v_a_486_ = lean_ctor_get(v___x_485_, 0);
lean_inc(v_a_486_);
lean_dec_ref(v___x_485_);
v___x_487_ = l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_evalsAtAtoms(v_val_466_, v___y_477_, v___y_478_, v___y_479_, v___y_480_, v___y_481_);
if (lean_obj_tag(v___x_487_) == 0)
{
lean_object* v_a_488_; lean_object* v___x_489_; 
v_a_488_ = lean_ctor_get(v___x_487_, 0);
lean_inc(v_a_488_);
lean_dec_ref(v___x_487_);
v___x_489_ = l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_evalsAtAtoms(v_val_467_, v___y_477_, v___y_478_, v___y_479_, v___y_480_, v___y_481_);
if (lean_obj_tag(v___x_489_) == 0)
{
lean_object* v_a_490_; lean_object* v___x_492_; uint8_t v_isShared_493_; uint8_t v_isSharedCheck_517_; 
v_a_490_ = lean_ctor_get(v___x_489_, 0);
v_isSharedCheck_517_ = !lean_is_exclusive(v___x_489_);
if (v_isSharedCheck_517_ == 0)
{
v___x_492_ = v___x_489_;
v_isShared_493_ = v_isSharedCheck_517_;
goto v_resetjp_491_;
}
else
{
lean_inc(v_a_490_);
lean_dec(v___x_489_);
v___x_492_ = lean_box(0);
v_isShared_493_ = v_isSharedCheck_517_;
goto v_resetjp_491_;
}
v_resetjp_491_:
{
lean_object* v___x_494_; 
lean_inc(v_a_486_);
lean_inc(v_a_484_);
v___x_494_ = l_Lean_Elab_Tactic_BVDecide_Frontend_M_simplifyBinaryProof_x27___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go_spec__13(v_width_462_, v_width_464_, v_a_484_, v_a_488_, v_a_486_, v_a_490_);
if (lean_obj_tag(v___x_494_) == 1)
{
lean_object* v_val_495_; lean_object* v___x_497_; uint8_t v_isShared_498_; uint8_t v_isSharedCheck_512_; 
v_val_495_ = lean_ctor_get(v___x_494_, 0);
v_isSharedCheck_512_ = !lean_is_exclusive(v___x_494_);
if (v_isSharedCheck_512_ == 0)
{
v___x_497_ = v___x_494_;
v_isShared_498_ = v_isSharedCheck_512_;
goto v_resetjp_496_;
}
else
{
lean_inc(v_val_495_);
lean_dec(v___x_494_);
v___x_497_ = lean_box(0);
v_isShared_498_ = v_isSharedCheck_512_;
goto v_resetjp_496_;
}
v_resetjp_496_:
{
lean_object* v_fst_499_; lean_object* v_snd_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_507_; 
v_fst_499_ = lean_ctor_get(v_val_495_, 0);
lean_inc(v_fst_499_);
v_snd_500_ = lean_ctor_get(v_val_495_, 1);
lean_inc(v_snd_500_);
lean_dec(v_val_495_);
v___x_501_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___lam__0___closed__0));
v___x_502_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___lam__0___closed__1));
v___x_503_ = l_Lean_Name_mkStr6(v___x_468_, v___x_469_, v___x_470_, v___x_501_, v___x_471_, v___x_502_);
v___x_504_ = l_Lean_mkConst(v___x_503_, v___x_472_);
v___x_505_ = l_Lean_mkApp8(v___x_504_, v___x_473_, v___x_474_, v_arg_475_, v_a_484_, v_arg_476_, v_a_486_, v_fst_499_, v_snd_500_);
if (v_isShared_498_ == 0)
{
lean_ctor_set(v___x_497_, 0, v___x_505_);
v___x_507_ = v___x_497_;
goto v_reusejp_506_;
}
else
{
lean_object* v_reuseFailAlloc_511_; 
v_reuseFailAlloc_511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_511_, 0, v___x_505_);
v___x_507_ = v_reuseFailAlloc_511_;
goto v_reusejp_506_;
}
v_reusejp_506_:
{
lean_object* v___x_509_; 
if (v_isShared_493_ == 0)
{
lean_ctor_set(v___x_492_, 0, v___x_507_);
v___x_509_ = v___x_492_;
goto v_reusejp_508_;
}
else
{
lean_object* v_reuseFailAlloc_510_; 
v_reuseFailAlloc_510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_510_, 0, v___x_507_);
v___x_509_ = v_reuseFailAlloc_510_;
goto v_reusejp_508_;
}
v_reusejp_508_:
{
return v___x_509_;
}
}
}
}
else
{
lean_object* v___x_513_; lean_object* v___x_515_; 
lean_dec(v___x_494_);
lean_dec(v_a_486_);
lean_dec(v_a_484_);
lean_dec_ref(v_arg_476_);
lean_dec_ref(v_arg_475_);
lean_dec_ref(v___x_474_);
lean_dec_ref(v___x_473_);
lean_dec(v___x_472_);
lean_dec_ref(v___x_471_);
lean_dec_ref(v___x_470_);
lean_dec_ref(v___x_469_);
lean_dec_ref(v___x_468_);
v___x_513_ = lean_box(0);
if (v_isShared_493_ == 0)
{
lean_ctor_set(v___x_492_, 0, v___x_513_);
v___x_515_ = v___x_492_;
goto v_reusejp_514_;
}
else
{
lean_object* v_reuseFailAlloc_516_; 
v_reuseFailAlloc_516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_516_, 0, v___x_513_);
v___x_515_ = v_reuseFailAlloc_516_;
goto v_reusejp_514_;
}
v_reusejp_514_:
{
return v___x_515_;
}
}
}
}
else
{
lean_dec(v_a_488_);
lean_dec(v_a_486_);
lean_dec(v_a_484_);
lean_dec_ref(v_arg_476_);
lean_dec_ref(v_arg_475_);
lean_dec_ref(v___x_474_);
lean_dec_ref(v___x_473_);
lean_dec(v___x_472_);
lean_dec_ref(v___x_471_);
lean_dec_ref(v___x_470_);
lean_dec_ref(v___x_469_);
lean_dec_ref(v___x_468_);
lean_dec(v_width_464_);
lean_dec(v_width_462_);
return v___x_489_;
}
}
else
{
lean_dec(v_a_486_);
lean_dec(v_a_484_);
lean_dec_ref(v_arg_476_);
lean_dec_ref(v_arg_475_);
lean_dec_ref(v___x_474_);
lean_dec_ref(v___x_473_);
lean_dec(v___x_472_);
lean_dec_ref(v___x_471_);
lean_dec_ref(v___x_470_);
lean_dec_ref(v___x_469_);
lean_dec_ref(v___x_468_);
lean_dec_ref(v_val_467_);
lean_dec(v_width_464_);
lean_dec(v_width_462_);
return v___x_487_;
}
}
else
{
lean_object* v_a_518_; lean_object* v___x_520_; uint8_t v_isShared_521_; uint8_t v_isSharedCheck_525_; 
lean_dec(v_a_484_);
lean_dec_ref(v_arg_476_);
lean_dec_ref(v_arg_475_);
lean_dec_ref(v___x_474_);
lean_dec_ref(v___x_473_);
lean_dec(v___x_472_);
lean_dec_ref(v___x_471_);
lean_dec_ref(v___x_470_);
lean_dec_ref(v___x_469_);
lean_dec_ref(v___x_468_);
lean_dec_ref(v_val_467_);
lean_dec_ref(v_val_466_);
lean_dec(v_width_464_);
lean_dec(v_width_462_);
v_a_518_ = lean_ctor_get(v___x_485_, 0);
v_isSharedCheck_525_ = !lean_is_exclusive(v___x_485_);
if (v_isSharedCheck_525_ == 0)
{
v___x_520_ = v___x_485_;
v_isShared_521_ = v_isSharedCheck_525_;
goto v_resetjp_519_;
}
else
{
lean_inc(v_a_518_);
lean_dec(v___x_485_);
v___x_520_ = lean_box(0);
v_isShared_521_ = v_isSharedCheck_525_;
goto v_resetjp_519_;
}
v_resetjp_519_:
{
lean_object* v___x_523_; 
if (v_isShared_521_ == 0)
{
v___x_523_ = v___x_520_;
goto v_reusejp_522_;
}
else
{
lean_object* v_reuseFailAlloc_524_; 
v_reuseFailAlloc_524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_524_, 0, v_a_518_);
v___x_523_ = v_reuseFailAlloc_524_;
goto v_reusejp_522_;
}
v_reusejp_522_:
{
return v___x_523_;
}
}
}
}
else
{
lean_object* v_a_526_; lean_object* v___x_528_; uint8_t v_isShared_529_; uint8_t v_isSharedCheck_533_; 
lean_dec_ref(v_arg_476_);
lean_dec_ref(v_arg_475_);
lean_dec_ref(v___x_474_);
lean_dec_ref(v___x_473_);
lean_dec(v___x_472_);
lean_dec_ref(v___x_471_);
lean_dec_ref(v___x_470_);
lean_dec_ref(v___x_469_);
lean_dec_ref(v___x_468_);
lean_dec_ref(v_val_467_);
lean_dec_ref(v_val_466_);
lean_dec_ref(v_expr_465_);
lean_dec(v_width_464_);
lean_dec(v_width_462_);
v_a_526_ = lean_ctor_get(v___x_483_, 0);
v_isSharedCheck_533_ = !lean_is_exclusive(v___x_483_);
if (v_isSharedCheck_533_ == 0)
{
v___x_528_ = v___x_483_;
v_isShared_529_ = v_isSharedCheck_533_;
goto v_resetjp_527_;
}
else
{
lean_inc(v_a_526_);
lean_dec(v___x_483_);
v___x_528_ = lean_box(0);
v_isShared_529_ = v_isSharedCheck_533_;
goto v_resetjp_527_;
}
v_resetjp_527_:
{
lean_object* v___x_531_; 
if (v_isShared_529_ == 0)
{
v___x_531_ = v___x_528_;
goto v_reusejp_530_;
}
else
{
lean_object* v_reuseFailAlloc_532_; 
v_reuseFailAlloc_532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_532_, 0, v_a_526_);
v___x_531_ = v_reuseFailAlloc_532_;
goto v_reusejp_530_;
}
v_reusejp_530_:
{
return v___x_531_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___lam__0___boxed(lean_object** _args){
lean_object* v_width_534_ = _args[0];
lean_object* v_expr_535_ = _args[1];
lean_object* v_width_536_ = _args[2];
lean_object* v_expr_537_ = _args[3];
lean_object* v_val_538_ = _args[4];
lean_object* v_val_539_ = _args[5];
lean_object* v___x_540_ = _args[6];
lean_object* v___x_541_ = _args[7];
lean_object* v___x_542_ = _args[8];
lean_object* v___x_543_ = _args[9];
lean_object* v___x_544_ = _args[10];
lean_object* v___x_545_ = _args[11];
lean_object* v___x_546_ = _args[12];
lean_object* v_arg_547_ = _args[13];
lean_object* v_arg_548_ = _args[14];
lean_object* v___y_549_ = _args[15];
lean_object* v___y_550_ = _args[16];
lean_object* v___y_551_ = _args[17];
lean_object* v___y_552_ = _args[18];
lean_object* v___y_553_ = _args[19];
lean_object* v___y_554_ = _args[20];
_start:
{
lean_object* v_res_555_; 
v_res_555_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___lam__0(v_width_534_, v_expr_535_, v_width_536_, v_expr_537_, v_val_538_, v_val_539_, v___x_540_, v___x_541_, v___x_542_, v___x_543_, v___x_544_, v___x_545_, v___x_546_, v_arg_547_, v_arg_548_, v___y_549_, v___y_550_, v___y_551_, v___y_552_, v___y_553_);
lean_dec(v___y_553_);
lean_dec_ref(v___y_552_);
lean_dec(v___y_551_);
lean_dec_ref(v___y_550_);
lean_dec(v___y_549_);
return v_res_555_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___lam__1(lean_object* v_width_557_, lean_object* v_expr_558_, lean_object* v_val_559_, lean_object* v___x_560_, lean_object* v___x_561_, lean_object* v___x_562_, lean_object* v___x_563_, lean_object* v___x_564_, lean_object* v_arg_565_, lean_object* v_arg_566_, lean_object* v___x_567_, lean_object* v_arg_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_){
_start:
{
lean_object* v___x_575_; 
v___x_575_ = l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkEvalExpr(v_width_557_, v_expr_558_, v___y_569_, v___y_570_, v___y_571_, v___y_572_, v___y_573_);
if (lean_obj_tag(v___x_575_) == 0)
{
lean_object* v_a_576_; lean_object* v___x_577_; 
v_a_576_ = lean_ctor_get(v___x_575_, 0);
lean_inc(v_a_576_);
lean_dec_ref(v___x_575_);
v___x_577_ = l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_evalsAtAtoms(v_val_559_, v___y_569_, v___y_570_, v___y_571_, v___y_572_, v___y_573_);
if (lean_obj_tag(v___x_577_) == 0)
{
lean_object* v_a_578_; lean_object* v___x_580_; uint8_t v_isShared_581_; uint8_t v_isSharedCheck_602_; 
v_a_578_ = lean_ctor_get(v___x_577_, 0);
v_isSharedCheck_602_ = !lean_is_exclusive(v___x_577_);
if (v_isSharedCheck_602_ == 0)
{
v___x_580_ = v___x_577_;
v_isShared_581_ = v_isSharedCheck_602_;
goto v_resetjp_579_;
}
else
{
lean_inc(v_a_578_);
lean_dec(v___x_577_);
v___x_580_ = lean_box(0);
v_isShared_581_ = v_isSharedCheck_602_;
goto v_resetjp_579_;
}
v_resetjp_579_:
{
if (lean_obj_tag(v_a_578_) == 1)
{
lean_object* v_val_582_; lean_object* v___x_584_; uint8_t v_isShared_585_; uint8_t v_isSharedCheck_597_; 
v_val_582_ = lean_ctor_get(v_a_578_, 0);
v_isSharedCheck_597_ = !lean_is_exclusive(v_a_578_);
if (v_isSharedCheck_597_ == 0)
{
v___x_584_ = v_a_578_;
v_isShared_585_ = v_isSharedCheck_597_;
goto v_resetjp_583_;
}
else
{
lean_inc(v_val_582_);
lean_dec(v_a_578_);
v___x_584_ = lean_box(0);
v_isShared_585_ = v_isSharedCheck_597_;
goto v_resetjp_583_;
}
v_resetjp_583_:
{
lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_592_; 
v___x_586_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___lam__0___closed__0));
v___x_587_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___lam__1___closed__0));
v___x_588_ = l_Lean_Name_mkStr6(v___x_560_, v___x_561_, v___x_562_, v___x_586_, v___x_563_, v___x_587_);
v___x_589_ = l_Lean_mkConst(v___x_588_, v___x_564_);
v___x_590_ = l_Lean_mkApp6(v___x_589_, v_arg_565_, v_arg_566_, v___x_567_, v_arg_568_, v_a_576_, v_val_582_);
if (v_isShared_585_ == 0)
{
lean_ctor_set(v___x_584_, 0, v___x_590_);
v___x_592_ = v___x_584_;
goto v_reusejp_591_;
}
else
{
lean_object* v_reuseFailAlloc_596_; 
v_reuseFailAlloc_596_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_596_, 0, v___x_590_);
v___x_592_ = v_reuseFailAlloc_596_;
goto v_reusejp_591_;
}
v_reusejp_591_:
{
lean_object* v___x_594_; 
if (v_isShared_581_ == 0)
{
lean_ctor_set(v___x_580_, 0, v___x_592_);
v___x_594_ = v___x_580_;
goto v_reusejp_593_;
}
else
{
lean_object* v_reuseFailAlloc_595_; 
v_reuseFailAlloc_595_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_595_, 0, v___x_592_);
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
lean_object* v___x_598_; lean_object* v___x_600_; 
lean_dec(v_a_578_);
lean_dec(v_a_576_);
lean_dec_ref(v_arg_568_);
lean_dec_ref(v___x_567_);
lean_dec_ref(v_arg_566_);
lean_dec_ref(v_arg_565_);
lean_dec(v___x_564_);
lean_dec_ref(v___x_563_);
lean_dec_ref(v___x_562_);
lean_dec_ref(v___x_561_);
lean_dec_ref(v___x_560_);
v___x_598_ = lean_box(0);
if (v_isShared_581_ == 0)
{
lean_ctor_set(v___x_580_, 0, v___x_598_);
v___x_600_ = v___x_580_;
goto v_reusejp_599_;
}
else
{
lean_object* v_reuseFailAlloc_601_; 
v_reuseFailAlloc_601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_601_, 0, v___x_598_);
v___x_600_ = v_reuseFailAlloc_601_;
goto v_reusejp_599_;
}
v_reusejp_599_:
{
return v___x_600_;
}
}
}
}
else
{
lean_dec(v_a_576_);
lean_dec_ref(v_arg_568_);
lean_dec_ref(v___x_567_);
lean_dec_ref(v_arg_566_);
lean_dec_ref(v_arg_565_);
lean_dec(v___x_564_);
lean_dec_ref(v___x_563_);
lean_dec_ref(v___x_562_);
lean_dec_ref(v___x_561_);
lean_dec_ref(v___x_560_);
return v___x_577_;
}
}
else
{
lean_object* v_a_603_; lean_object* v___x_605_; uint8_t v_isShared_606_; uint8_t v_isSharedCheck_610_; 
lean_dec_ref(v_arg_568_);
lean_dec_ref(v___x_567_);
lean_dec_ref(v_arg_566_);
lean_dec_ref(v_arg_565_);
lean_dec(v___x_564_);
lean_dec_ref(v___x_563_);
lean_dec_ref(v___x_562_);
lean_dec_ref(v___x_561_);
lean_dec_ref(v___x_560_);
lean_dec_ref(v_val_559_);
v_a_603_ = lean_ctor_get(v___x_575_, 0);
v_isSharedCheck_610_ = !lean_is_exclusive(v___x_575_);
if (v_isSharedCheck_610_ == 0)
{
v___x_605_ = v___x_575_;
v_isShared_606_ = v_isSharedCheck_610_;
goto v_resetjp_604_;
}
else
{
lean_inc(v_a_603_);
lean_dec(v___x_575_);
v___x_605_ = lean_box(0);
v_isShared_606_ = v_isSharedCheck_610_;
goto v_resetjp_604_;
}
v_resetjp_604_:
{
lean_object* v___x_608_; 
if (v_isShared_606_ == 0)
{
v___x_608_ = v___x_605_;
goto v_reusejp_607_;
}
else
{
lean_object* v_reuseFailAlloc_609_; 
v_reuseFailAlloc_609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_609_, 0, v_a_603_);
v___x_608_ = v_reuseFailAlloc_609_;
goto v_reusejp_607_;
}
v_reusejp_607_:
{
return v___x_608_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___lam__1___boxed(lean_object** _args){
lean_object* v_width_611_ = _args[0];
lean_object* v_expr_612_ = _args[1];
lean_object* v_val_613_ = _args[2];
lean_object* v___x_614_ = _args[3];
lean_object* v___x_615_ = _args[4];
lean_object* v___x_616_ = _args[5];
lean_object* v___x_617_ = _args[6];
lean_object* v___x_618_ = _args[7];
lean_object* v_arg_619_ = _args[8];
lean_object* v_arg_620_ = _args[9];
lean_object* v___x_621_ = _args[10];
lean_object* v_arg_622_ = _args[11];
lean_object* v___y_623_ = _args[12];
lean_object* v___y_624_ = _args[13];
lean_object* v___y_625_ = _args[14];
lean_object* v___y_626_ = _args[15];
lean_object* v___y_627_ = _args[16];
lean_object* v___y_628_ = _args[17];
_start:
{
lean_object* v_res_629_; 
v_res_629_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___lam__1(v_width_611_, v_expr_612_, v_val_613_, v___x_614_, v___x_615_, v___x_616_, v___x_617_, v___x_618_, v_arg_619_, v_arg_620_, v___x_621_, v_arg_622_, v___y_623_, v___y_624_, v___y_625_, v___y_626_, v___y_627_);
lean_dec(v___y_627_);
lean_dec_ref(v___y_626_);
lean_dec(v___y_625_);
lean_dec_ref(v___y_624_);
lean_dec(v___y_623_);
return v_res_629_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___lam__2(lean_object* v_n_630_){
_start:
{
lean_object* v___x_631_; 
v___x_631_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_631_, 0, v_n_630_);
return v___x_631_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___lam__5(lean_object* v_n_632_){
_start:
{
lean_object* v___x_633_; 
v___x_633_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_633_, 0, v_n_632_);
return v___x_633_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___lam__4(lean_object* v_n_634_){
_start:
{
lean_object* v___x_635_; 
v___x_635_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_635_, 0, v_n_634_);
return v___x_635_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___lam__3(lean_object* v_width_637_, lean_object* v_expr_638_, lean_object* v_val_639_, lean_object* v___x_640_, lean_object* v___x_641_, lean_object* v___x_642_, lean_object* v___x_643_, lean_object* v___x_644_, lean_object* v___x_645_, lean_object* v___x_646_, lean_object* v_arg_647_, lean_object* v___y_648_, lean_object* v___y_649_, lean_object* v___y_650_, lean_object* v___y_651_, lean_object* v___y_652_){
_start:
{
lean_object* v___x_654_; 
v___x_654_ = l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkEvalExpr(v_width_637_, v_expr_638_, v___y_648_, v___y_649_, v___y_650_, v___y_651_, v___y_652_);
if (lean_obj_tag(v___x_654_) == 0)
{
lean_object* v_a_655_; lean_object* v___x_656_; 
v_a_655_ = lean_ctor_get(v___x_654_, 0);
lean_inc(v_a_655_);
lean_dec_ref(v___x_654_);
v___x_656_ = l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_evalsAtAtoms(v_val_639_, v___y_648_, v___y_649_, v___y_650_, v___y_651_, v___y_652_);
if (lean_obj_tag(v___x_656_) == 0)
{
lean_object* v_a_657_; lean_object* v___x_659_; uint8_t v_isShared_660_; uint8_t v_isSharedCheck_681_; 
v_a_657_ = lean_ctor_get(v___x_656_, 0);
v_isSharedCheck_681_ = !lean_is_exclusive(v___x_656_);
if (v_isSharedCheck_681_ == 0)
{
v___x_659_ = v___x_656_;
v_isShared_660_ = v_isSharedCheck_681_;
goto v_resetjp_658_;
}
else
{
lean_inc(v_a_657_);
lean_dec(v___x_656_);
v___x_659_ = lean_box(0);
v_isShared_660_ = v_isSharedCheck_681_;
goto v_resetjp_658_;
}
v_resetjp_658_:
{
if (lean_obj_tag(v_a_657_) == 1)
{
lean_object* v_val_661_; lean_object* v___x_663_; uint8_t v_isShared_664_; uint8_t v_isSharedCheck_676_; 
v_val_661_ = lean_ctor_get(v_a_657_, 0);
v_isSharedCheck_676_ = !lean_is_exclusive(v_a_657_);
if (v_isSharedCheck_676_ == 0)
{
v___x_663_ = v_a_657_;
v_isShared_664_ = v_isSharedCheck_676_;
goto v_resetjp_662_;
}
else
{
lean_inc(v_val_661_);
lean_dec(v_a_657_);
v___x_663_ = lean_box(0);
v_isShared_664_ = v_isSharedCheck_676_;
goto v_resetjp_662_;
}
v_resetjp_662_:
{
lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_671_; 
v___x_665_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___lam__0___closed__0));
v___x_666_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___lam__3___closed__0));
v___x_667_ = l_Lean_Name_mkStr6(v___x_640_, v___x_641_, v___x_642_, v___x_665_, v___x_643_, v___x_666_);
v___x_668_ = l_Lean_mkConst(v___x_667_, v___x_644_);
v___x_669_ = l_Lean_mkApp5(v___x_668_, v___x_645_, v___x_646_, v_arg_647_, v_a_655_, v_val_661_);
if (v_isShared_664_ == 0)
{
lean_ctor_set(v___x_663_, 0, v___x_669_);
v___x_671_ = v___x_663_;
goto v_reusejp_670_;
}
else
{
lean_object* v_reuseFailAlloc_675_; 
v_reuseFailAlloc_675_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_675_, 0, v___x_669_);
v___x_671_ = v_reuseFailAlloc_675_;
goto v_reusejp_670_;
}
v_reusejp_670_:
{
lean_object* v___x_673_; 
if (v_isShared_660_ == 0)
{
lean_ctor_set(v___x_659_, 0, v___x_671_);
v___x_673_ = v___x_659_;
goto v_reusejp_672_;
}
else
{
lean_object* v_reuseFailAlloc_674_; 
v_reuseFailAlloc_674_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_674_, 0, v___x_671_);
v___x_673_ = v_reuseFailAlloc_674_;
goto v_reusejp_672_;
}
v_reusejp_672_:
{
return v___x_673_;
}
}
}
}
else
{
lean_object* v___x_677_; lean_object* v___x_679_; 
lean_dec(v_a_657_);
lean_dec(v_a_655_);
lean_dec_ref(v_arg_647_);
lean_dec_ref(v___x_646_);
lean_dec_ref(v___x_645_);
lean_dec(v___x_644_);
lean_dec_ref(v___x_643_);
lean_dec_ref(v___x_642_);
lean_dec_ref(v___x_641_);
lean_dec_ref(v___x_640_);
v___x_677_ = lean_box(0);
if (v_isShared_660_ == 0)
{
lean_ctor_set(v___x_659_, 0, v___x_677_);
v___x_679_ = v___x_659_;
goto v_reusejp_678_;
}
else
{
lean_object* v_reuseFailAlloc_680_; 
v_reuseFailAlloc_680_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_680_, 0, v___x_677_);
v___x_679_ = v_reuseFailAlloc_680_;
goto v_reusejp_678_;
}
v_reusejp_678_:
{
return v___x_679_;
}
}
}
}
else
{
lean_dec(v_a_655_);
lean_dec_ref(v_arg_647_);
lean_dec_ref(v___x_646_);
lean_dec_ref(v___x_645_);
lean_dec(v___x_644_);
lean_dec_ref(v___x_643_);
lean_dec_ref(v___x_642_);
lean_dec_ref(v___x_641_);
lean_dec_ref(v___x_640_);
return v___x_656_;
}
}
else
{
lean_object* v_a_682_; lean_object* v___x_684_; uint8_t v_isShared_685_; uint8_t v_isSharedCheck_689_; 
lean_dec_ref(v_arg_647_);
lean_dec_ref(v___x_646_);
lean_dec_ref(v___x_645_);
lean_dec(v___x_644_);
lean_dec_ref(v___x_643_);
lean_dec_ref(v___x_642_);
lean_dec_ref(v___x_641_);
lean_dec_ref(v___x_640_);
lean_dec_ref(v_val_639_);
v_a_682_ = lean_ctor_get(v___x_654_, 0);
v_isSharedCheck_689_ = !lean_is_exclusive(v___x_654_);
if (v_isSharedCheck_689_ == 0)
{
v___x_684_ = v___x_654_;
v_isShared_685_ = v_isSharedCheck_689_;
goto v_resetjp_683_;
}
else
{
lean_inc(v_a_682_);
lean_dec(v___x_654_);
v___x_684_ = lean_box(0);
v_isShared_685_ = v_isSharedCheck_689_;
goto v_resetjp_683_;
}
v_resetjp_683_:
{
lean_object* v___x_687_; 
if (v_isShared_685_ == 0)
{
v___x_687_ = v___x_684_;
goto v_reusejp_686_;
}
else
{
lean_object* v_reuseFailAlloc_688_; 
v_reuseFailAlloc_688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_688_, 0, v_a_682_);
v___x_687_ = v_reuseFailAlloc_688_;
goto v_reusejp_686_;
}
v_reusejp_686_:
{
return v___x_687_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___lam__3___boxed(lean_object** _args){
lean_object* v_width_690_ = _args[0];
lean_object* v_expr_691_ = _args[1];
lean_object* v_val_692_ = _args[2];
lean_object* v___x_693_ = _args[3];
lean_object* v___x_694_ = _args[4];
lean_object* v___x_695_ = _args[5];
lean_object* v___x_696_ = _args[6];
lean_object* v___x_697_ = _args[7];
lean_object* v___x_698_ = _args[8];
lean_object* v___x_699_ = _args[9];
lean_object* v_arg_700_ = _args[10];
lean_object* v___y_701_ = _args[11];
lean_object* v___y_702_ = _args[12];
lean_object* v___y_703_ = _args[13];
lean_object* v___y_704_ = _args[14];
lean_object* v___y_705_ = _args[15];
lean_object* v___y_706_ = _args[16];
_start:
{
lean_object* v_res_707_; 
v_res_707_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___lam__3(v_width_690_, v_expr_691_, v_val_692_, v___x_693_, v___x_694_, v___x_695_, v___x_696_, v___x_697_, v___x_698_, v___x_699_, v_arg_700_, v___y_701_, v___y_702_, v___y_703_, v___y_704_, v___y_705_);
lean_dec(v___y_705_);
lean_dec_ref(v___y_704_);
lean_dec(v___y_703_);
lean_dec_ref(v___y_702_);
lean_dec(v___y_701_);
return v_res_707_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__2(void){
_start:
{
lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; 
v___x_822_ = lean_box(0);
v___x_823_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__1));
v___x_824_ = l_Lean_mkConst(v___x_823_, v___x_822_);
return v___x_824_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__6(void){
_start:
{
lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; 
v___x_833_ = lean_box(0);
v___x_834_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__5));
v___x_835_ = l_Lean_mkConst(v___x_834_, v___x_833_);
return v___x_835_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__9(void){
_start:
{
lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; 
v___x_843_ = lean_box(0);
v___x_844_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__8));
v___x_845_ = l_Lean_mkConst(v___x_844_, v___x_843_);
return v___x_845_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__12(void){
_start:
{
lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; 
v___x_853_ = lean_box(0);
v___x_854_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__11));
v___x_855_ = l_Lean_mkConst(v___x_854_, v___x_853_);
return v___x_855_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__15(void){
_start:
{
lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; 
v___x_863_ = lean_box(0);
v___x_864_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__14));
v___x_865_ = l_Lean_mkConst(v___x_864_, v___x_863_);
return v___x_865_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__18(void){
_start:
{
lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; 
v___x_873_ = lean_box(0);
v___x_874_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__17));
v___x_875_ = l_Lean_mkConst(v___x_874_, v___x_873_);
return v___x_875_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__21(void){
_start:
{
lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; 
v___x_883_ = lean_box(0);
v___x_884_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__20));
v___x_885_ = l_Lean_mkConst(v___x_884_, v___x_883_);
return v___x_885_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__24(void){
_start:
{
lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; 
v___x_893_ = lean_box(0);
v___x_894_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__23));
v___x_895_ = l_Lean_mkConst(v___x_894_, v___x_893_);
return v___x_895_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection(lean_object* v_lhsExpr_896_, lean_object* v_rhsExpr_897_, uint8_t v_op_898_, lean_object* v_congrThm_899_, lean_object* v_origExpr_900_, lean_object* v_a_901_, lean_object* v_a_902_, lean_object* v_a_903_, lean_object* v_a_904_, lean_object* v_a_905_, lean_object* v_a_906_){
_start:
{
lean_object* v___x_908_; 
lean_inc_ref(v_lhsExpr_896_);
v___x_908_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_goOrAtom(v_lhsExpr_896_, v_a_901_, v_a_902_, v_a_903_, v_a_904_, v_a_905_, v_a_906_);
if (lean_obj_tag(v___x_908_) == 0)
{
lean_object* v_a_909_; lean_object* v___x_911_; uint8_t v_isShared_912_; uint8_t v_isSharedCheck_968_; 
v_a_909_ = lean_ctor_get(v___x_908_, 0);
v_isSharedCheck_968_ = !lean_is_exclusive(v___x_908_);
if (v_isSharedCheck_968_ == 0)
{
v___x_911_ = v___x_908_;
v_isShared_912_ = v_isSharedCheck_968_;
goto v_resetjp_910_;
}
else
{
lean_inc(v_a_909_);
lean_dec(v___x_908_);
v___x_911_ = lean_box(0);
v_isShared_912_ = v_isSharedCheck_968_;
goto v_resetjp_910_;
}
v_resetjp_910_:
{
if (lean_obj_tag(v_a_909_) == 1)
{
lean_object* v_val_913_; lean_object* v___x_914_; 
lean_del_object(v___x_911_);
v_val_913_ = lean_ctor_get(v_a_909_, 0);
lean_inc(v_val_913_);
lean_dec_ref(v_a_909_);
lean_inc_ref(v_rhsExpr_897_);
v___x_914_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_goOrAtom(v_rhsExpr_897_, v_a_901_, v_a_902_, v_a_903_, v_a_904_, v_a_905_, v_a_906_);
if (lean_obj_tag(v___x_914_) == 0)
{
lean_object* v_a_915_; lean_object* v___x_917_; uint8_t v_isShared_918_; uint8_t v_isSharedCheck_963_; 
v_a_915_ = lean_ctor_get(v___x_914_, 0);
v_isSharedCheck_963_ = !lean_is_exclusive(v___x_914_);
if (v_isSharedCheck_963_ == 0)
{
v___x_917_ = v___x_914_;
v_isShared_918_ = v_isSharedCheck_963_;
goto v_resetjp_916_;
}
else
{
lean_inc(v_a_915_);
lean_dec(v___x_914_);
v___x_917_ = lean_box(0);
v_isShared_918_ = v_isSharedCheck_963_;
goto v_resetjp_916_;
}
v_resetjp_916_:
{
if (lean_obj_tag(v_a_915_) == 1)
{
lean_object* v_val_919_; lean_object* v___x_921_; uint8_t v_isShared_922_; uint8_t v_isSharedCheck_958_; 
v_val_919_ = lean_ctor_get(v_a_915_, 0);
v_isSharedCheck_958_ = !lean_is_exclusive(v_a_915_);
if (v_isSharedCheck_958_ == 0)
{
v___x_921_ = v_a_915_;
v_isShared_922_ = v_isSharedCheck_958_;
goto v_resetjp_920_;
}
else
{
lean_inc(v_val_919_);
lean_dec(v_a_915_);
v___x_921_ = lean_box(0);
v_isShared_922_ = v_isSharedCheck_958_;
goto v_resetjp_920_;
}
v_resetjp_920_:
{
lean_object* v_width_923_; lean_object* v_bvExpr_924_; lean_object* v_expr_925_; lean_object* v_width_926_; lean_object* v_bvExpr_927_; lean_object* v_expr_928_; uint8_t v___x_929_; 
v_width_923_ = lean_ctor_get(v_val_919_, 0);
v_bvExpr_924_ = lean_ctor_get(v_val_919_, 1);
v_expr_925_ = lean_ctor_get(v_val_919_, 4);
v_width_926_ = lean_ctor_get(v_val_913_, 0);
lean_inc(v_width_926_);
v_bvExpr_927_ = lean_ctor_get(v_val_913_, 1);
v_expr_928_ = lean_ctor_get(v_val_913_, 4);
v___x_929_ = lean_nat_dec_eq(v_width_923_, v_width_926_);
if (v___x_929_ == 0)
{
lean_object* v___x_930_; lean_object* v___x_932_; 
lean_dec(v_width_926_);
lean_del_object(v___x_921_);
lean_dec(v_val_919_);
lean_dec(v_val_913_);
lean_dec_ref(v_origExpr_900_);
lean_dec(v_congrThm_899_);
lean_dec_ref(v_rhsExpr_897_);
lean_dec_ref(v_lhsExpr_896_);
v___x_930_ = lean_box(0);
if (v_isShared_918_ == 0)
{
lean_ctor_set(v___x_917_, 0, v___x_930_);
v___x_932_ = v___x_917_;
goto v_reusejp_931_;
}
else
{
lean_object* v_reuseFailAlloc_933_; 
v_reuseFailAlloc_933_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_933_, 0, v___x_930_);
v___x_932_ = v_reuseFailAlloc_933_;
goto v_reusejp_931_;
}
v_reusejp_931_:
{
return v___x_932_;
}
}
else
{
lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___y_939_; 
lean_inc_ref(v_bvExpr_924_);
lean_inc_ref(v_bvExpr_927_);
lean_inc_n(v_width_926_, 2);
v___x_934_ = l_Std_Tactic_BVDecide_BVExpr_bin___override(v_width_926_, v_bvExpr_927_, v_op_898_, v_bvExpr_924_);
v___x_935_ = lean_box(0);
v___x_936_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__2, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__2_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__2);
v___x_937_ = l_Lean_mkNatLit(v_width_926_);
switch(v_op_898_)
{
case 0:
{
lean_object* v___x_951_; 
v___x_951_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__6, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__6_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__6);
v___y_939_ = v___x_951_;
goto v___jp_938_;
}
case 1:
{
lean_object* v___x_952_; 
v___x_952_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__9, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__9_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__9);
v___y_939_ = v___x_952_;
goto v___jp_938_;
}
case 2:
{
lean_object* v___x_953_; 
v___x_953_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__12, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__12_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__12);
v___y_939_ = v___x_953_;
goto v___jp_938_;
}
case 3:
{
lean_object* v___x_954_; 
v___x_954_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__15, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__15_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__15);
v___y_939_ = v___x_954_;
goto v___jp_938_;
}
case 4:
{
lean_object* v___x_955_; 
v___x_955_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__18, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__18_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__18);
v___y_939_ = v___x_955_;
goto v___jp_938_;
}
case 5:
{
lean_object* v___x_956_; 
v___x_956_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__21, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__21_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__21);
v___y_939_ = v___x_956_;
goto v___jp_938_;
}
default: 
{
lean_object* v___x_957_; 
v___x_957_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__24, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__24_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__24);
v___y_939_ = v___x_957_;
goto v___jp_938_;
}
}
v___jp_938_:
{
lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_946_; 
lean_inc_ref(v_expr_925_);
lean_inc_ref(v___y_939_);
lean_inc_ref(v_expr_928_);
lean_inc_ref(v___x_937_);
v___x_940_ = l_Lean_mkApp4(v___x_936_, v___x_937_, v_expr_928_, v___y_939_, v_expr_925_);
v___x_941_ = l_Lean_mkConst(v_congrThm_899_, v___x_935_);
v___x_942_ = l_Lean_Expr_app___override(v___x_941_, v___x_937_);
v___x_943_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryCongrProof___boxed), 11, 5);
lean_closure_set(v___x_943_, 0, v_val_913_);
lean_closure_set(v___x_943_, 1, v_val_919_);
lean_closure_set(v___x_943_, 2, v_lhsExpr_896_);
lean_closure_set(v___x_943_, 3, v_rhsExpr_897_);
lean_closure_set(v___x_943_, 4, v___x_942_);
v___x_944_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_944_, 0, v_width_926_);
lean_ctor_set(v___x_944_, 1, v___x_934_);
lean_ctor_set(v___x_944_, 2, v_origExpr_900_);
lean_ctor_set(v___x_944_, 3, v___x_943_);
lean_ctor_set(v___x_944_, 4, v___x_940_);
if (v_isShared_922_ == 0)
{
lean_ctor_set(v___x_921_, 0, v___x_944_);
v___x_946_ = v___x_921_;
goto v_reusejp_945_;
}
else
{
lean_object* v_reuseFailAlloc_950_; 
v_reuseFailAlloc_950_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_950_, 0, v___x_944_);
v___x_946_ = v_reuseFailAlloc_950_;
goto v_reusejp_945_;
}
v_reusejp_945_:
{
lean_object* v___x_948_; 
if (v_isShared_918_ == 0)
{
lean_ctor_set(v___x_917_, 0, v___x_946_);
v___x_948_ = v___x_917_;
goto v_reusejp_947_;
}
else
{
lean_object* v_reuseFailAlloc_949_; 
v_reuseFailAlloc_949_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_949_, 0, v___x_946_);
v___x_948_ = v_reuseFailAlloc_949_;
goto v_reusejp_947_;
}
v_reusejp_947_:
{
return v___x_948_;
}
}
}
}
}
}
else
{
lean_object* v___x_959_; lean_object* v___x_961_; 
lean_dec(v_a_915_);
lean_dec(v_val_913_);
lean_dec_ref(v_origExpr_900_);
lean_dec(v_congrThm_899_);
lean_dec_ref(v_rhsExpr_897_);
lean_dec_ref(v_lhsExpr_896_);
v___x_959_ = lean_box(0);
if (v_isShared_918_ == 0)
{
lean_ctor_set(v___x_917_, 0, v___x_959_);
v___x_961_ = v___x_917_;
goto v_reusejp_960_;
}
else
{
lean_object* v_reuseFailAlloc_962_; 
v_reuseFailAlloc_962_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_962_, 0, v___x_959_);
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
else
{
lean_dec(v_val_913_);
lean_dec_ref(v_origExpr_900_);
lean_dec(v_congrThm_899_);
lean_dec_ref(v_rhsExpr_897_);
lean_dec_ref(v_lhsExpr_896_);
return v___x_914_;
}
}
else
{
lean_object* v___x_964_; lean_object* v___x_966_; 
lean_dec(v_a_909_);
lean_dec_ref(v_origExpr_900_);
lean_dec(v_congrThm_899_);
lean_dec_ref(v_rhsExpr_897_);
lean_dec_ref(v_lhsExpr_896_);
v___x_964_ = lean_box(0);
if (v_isShared_912_ == 0)
{
lean_ctor_set(v___x_911_, 0, v___x_964_);
v___x_966_ = v___x_911_;
goto v_reusejp_965_;
}
else
{
lean_object* v_reuseFailAlloc_967_; 
v_reuseFailAlloc_967_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_967_, 0, v___x_964_);
v___x_966_ = v_reuseFailAlloc_967_;
goto v_reusejp_965_;
}
v_reusejp_965_:
{
return v___x_966_;
}
}
}
}
else
{
lean_dec_ref(v_origExpr_900_);
lean_dec(v_congrThm_899_);
lean_dec_ref(v_rhsExpr_897_);
lean_dec_ref(v_lhsExpr_896_);
return v___x_908_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftReflection(lean_object* v_distanceExpr_1027_, lean_object* v_innerExpr_1028_, lean_object* v_shiftOp_1029_, lean_object* v_shiftOpName_1030_, lean_object* v_congrThm_1031_, lean_object* v_origExpr_1032_, lean_object* v_a_1033_, lean_object* v_a_1034_, lean_object* v_a_1035_, lean_object* v_a_1036_, lean_object* v_a_1037_, lean_object* v_a_1038_){
_start:
{
lean_object* v___x_1040_; 
lean_inc_ref(v_innerExpr_1028_);
v___x_1040_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_goOrAtom(v_innerExpr_1028_, v_a_1033_, v_a_1034_, v_a_1035_, v_a_1036_, v_a_1037_, v_a_1038_);
if (lean_obj_tag(v___x_1040_) == 0)
{
lean_object* v_a_1041_; lean_object* v___x_1043_; uint8_t v_isShared_1044_; uint8_t v_isSharedCheck_1087_; 
v_a_1041_ = lean_ctor_get(v___x_1040_, 0);
v_isSharedCheck_1087_ = !lean_is_exclusive(v___x_1040_);
if (v_isSharedCheck_1087_ == 0)
{
v___x_1043_ = v___x_1040_;
v_isShared_1044_ = v_isSharedCheck_1087_;
goto v_resetjp_1042_;
}
else
{
lean_inc(v_a_1041_);
lean_dec(v___x_1040_);
v___x_1043_ = lean_box(0);
v_isShared_1044_ = v_isSharedCheck_1087_;
goto v_resetjp_1042_;
}
v_resetjp_1042_:
{
if (lean_obj_tag(v_a_1041_) == 1)
{
lean_object* v_val_1045_; lean_object* v___x_1046_; 
lean_del_object(v___x_1043_);
v_val_1045_ = lean_ctor_get(v_a_1041_, 0);
lean_inc(v_val_1045_);
lean_dec_ref(v_a_1041_);
lean_inc_ref(v_distanceExpr_1027_);
v___x_1046_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_goOrAtom(v_distanceExpr_1027_, v_a_1033_, v_a_1034_, v_a_1035_, v_a_1036_, v_a_1037_, v_a_1038_);
if (lean_obj_tag(v___x_1046_) == 0)
{
lean_object* v_a_1047_; lean_object* v___x_1049_; uint8_t v_isShared_1050_; uint8_t v_isSharedCheck_1082_; 
v_a_1047_ = lean_ctor_get(v___x_1046_, 0);
v_isSharedCheck_1082_ = !lean_is_exclusive(v___x_1046_);
if (v_isSharedCheck_1082_ == 0)
{
v___x_1049_ = v___x_1046_;
v_isShared_1050_ = v_isSharedCheck_1082_;
goto v_resetjp_1048_;
}
else
{
lean_inc(v_a_1047_);
lean_dec(v___x_1046_);
v___x_1049_ = lean_box(0);
v_isShared_1050_ = v_isSharedCheck_1082_;
goto v_resetjp_1048_;
}
v_resetjp_1048_:
{
if (lean_obj_tag(v_a_1047_) == 1)
{
lean_object* v_val_1051_; lean_object* v___x_1053_; uint8_t v_isShared_1054_; uint8_t v_isSharedCheck_1077_; 
v_val_1051_ = lean_ctor_get(v_a_1047_, 0);
v_isSharedCheck_1077_ = !lean_is_exclusive(v_a_1047_);
if (v_isSharedCheck_1077_ == 0)
{
v___x_1053_ = v_a_1047_;
v_isShared_1054_ = v_isSharedCheck_1077_;
goto v_resetjp_1052_;
}
else
{
lean_inc(v_val_1051_);
lean_dec(v_a_1047_);
v___x_1053_ = lean_box(0);
v_isShared_1054_ = v_isSharedCheck_1077_;
goto v_resetjp_1052_;
}
v_resetjp_1052_:
{
lean_object* v_width_1055_; lean_object* v_bvExpr_1056_; lean_object* v_expr_1057_; lean_object* v_width_1058_; lean_object* v_bvExpr_1059_; lean_object* v_expr_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1072_; 
v_width_1055_ = lean_ctor_get(v_val_1045_, 0);
lean_inc_n(v_width_1055_, 3);
v_bvExpr_1056_ = lean_ctor_get(v_val_1045_, 1);
v_expr_1057_ = lean_ctor_get(v_val_1045_, 4);
v_width_1058_ = lean_ctor_get(v_val_1051_, 0);
v_bvExpr_1059_ = lean_ctor_get(v_val_1051_, 1);
v_expr_1060_ = lean_ctor_get(v_val_1051_, 4);
lean_inc_ref(v_bvExpr_1059_);
lean_inc_ref(v_bvExpr_1056_);
lean_inc_n(v_width_1058_, 2);
v___x_1061_ = lean_apply_4(v_shiftOp_1029_, v_width_1055_, v_width_1058_, v_bvExpr_1056_, v_bvExpr_1059_);
v___x_1062_ = lean_box(0);
v___x_1063_ = l_Lean_mkConst(v_shiftOpName_1030_, v___x_1062_);
v___x_1064_ = l_Lean_mkNatLit(v_width_1055_);
v___x_1065_ = l_Lean_mkNatLit(v_width_1058_);
lean_inc_ref(v_expr_1060_);
lean_inc_ref(v_expr_1057_);
lean_inc_ref(v___x_1065_);
lean_inc_ref(v___x_1064_);
v___x_1066_ = l_Lean_mkApp4(v___x_1063_, v___x_1064_, v___x_1065_, v_expr_1057_, v_expr_1060_);
v___x_1067_ = l_Lean_mkConst(v_congrThm_1031_, v___x_1062_);
v___x_1068_ = l_Lean_mkAppB(v___x_1067_, v___x_1064_, v___x_1065_);
v___x_1069_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryCongrProof___boxed), 11, 5);
lean_closure_set(v___x_1069_, 0, v_val_1045_);
lean_closure_set(v___x_1069_, 1, v_val_1051_);
lean_closure_set(v___x_1069_, 2, v_innerExpr_1028_);
lean_closure_set(v___x_1069_, 3, v_distanceExpr_1027_);
lean_closure_set(v___x_1069_, 4, v___x_1068_);
v___x_1070_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1070_, 0, v_width_1055_);
lean_ctor_set(v___x_1070_, 1, v___x_1061_);
lean_ctor_set(v___x_1070_, 2, v_origExpr_1032_);
lean_ctor_set(v___x_1070_, 3, v___x_1069_);
lean_ctor_set(v___x_1070_, 4, v___x_1066_);
if (v_isShared_1054_ == 0)
{
lean_ctor_set(v___x_1053_, 0, v___x_1070_);
v___x_1072_ = v___x_1053_;
goto v_reusejp_1071_;
}
else
{
lean_object* v_reuseFailAlloc_1076_; 
v_reuseFailAlloc_1076_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1076_, 0, v___x_1070_);
v___x_1072_ = v_reuseFailAlloc_1076_;
goto v_reusejp_1071_;
}
v_reusejp_1071_:
{
lean_object* v___x_1074_; 
if (v_isShared_1050_ == 0)
{
lean_ctor_set(v___x_1049_, 0, v___x_1072_);
v___x_1074_ = v___x_1049_;
goto v_reusejp_1073_;
}
else
{
lean_object* v_reuseFailAlloc_1075_; 
v_reuseFailAlloc_1075_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1075_, 0, v___x_1072_);
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
else
{
lean_object* v___x_1078_; lean_object* v___x_1080_; 
lean_dec(v_a_1047_);
lean_dec(v_val_1045_);
lean_dec_ref(v_origExpr_1032_);
lean_dec(v_congrThm_1031_);
lean_dec(v_shiftOpName_1030_);
lean_dec_ref(v_shiftOp_1029_);
lean_dec_ref(v_innerExpr_1028_);
lean_dec_ref(v_distanceExpr_1027_);
v___x_1078_ = lean_box(0);
if (v_isShared_1050_ == 0)
{
lean_ctor_set(v___x_1049_, 0, v___x_1078_);
v___x_1080_ = v___x_1049_;
goto v_reusejp_1079_;
}
else
{
lean_object* v_reuseFailAlloc_1081_; 
v_reuseFailAlloc_1081_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1081_, 0, v___x_1078_);
v___x_1080_ = v_reuseFailAlloc_1081_;
goto v_reusejp_1079_;
}
v_reusejp_1079_:
{
return v___x_1080_;
}
}
}
}
else
{
lean_dec(v_val_1045_);
lean_dec_ref(v_origExpr_1032_);
lean_dec(v_congrThm_1031_);
lean_dec(v_shiftOpName_1030_);
lean_dec_ref(v_shiftOp_1029_);
lean_dec_ref(v_innerExpr_1028_);
lean_dec_ref(v_distanceExpr_1027_);
return v___x_1046_;
}
}
else
{
lean_object* v___x_1083_; lean_object* v___x_1085_; 
lean_dec(v_a_1041_);
lean_dec_ref(v_origExpr_1032_);
lean_dec(v_congrThm_1031_);
lean_dec(v_shiftOpName_1030_);
lean_dec_ref(v_shiftOp_1029_);
lean_dec_ref(v_innerExpr_1028_);
lean_dec_ref(v_distanceExpr_1027_);
v___x_1083_ = lean_box(0);
if (v_isShared_1044_ == 0)
{
lean_ctor_set(v___x_1043_, 0, v___x_1083_);
v___x_1085_ = v___x_1043_;
goto v_reusejp_1084_;
}
else
{
lean_object* v_reuseFailAlloc_1086_; 
v_reuseFailAlloc_1086_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1086_, 0, v___x_1083_);
v___x_1085_ = v_reuseFailAlloc_1086_;
goto v_reusejp_1084_;
}
v_reusejp_1084_:
{
return v___x_1085_;
}
}
}
}
else
{
lean_dec_ref(v_origExpr_1032_);
lean_dec(v_congrThm_1031_);
lean_dec(v_shiftOpName_1030_);
lean_dec_ref(v_shiftOp_1029_);
lean_dec_ref(v_innerExpr_1028_);
lean_dec_ref(v_distanceExpr_1027_);
return v___x_1040_;
}
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__63(void){
_start:
{
lean_object* v___x_1089_; lean_object* v___x_1090_; 
v___x_1089_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__62));
v___x_1090_ = l_Lean_stringToMessageData(v___x_1089_);
return v___x_1090_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__71(void){
_start:
{
lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; 
v___x_1114_ = lean_box(0);
v___x_1115_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__70));
v___x_1116_ = l_Lean_mkConst(v___x_1115_, v___x_1114_);
return v___x_1116_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__79(void){
_start:
{
lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; 
v___x_1140_ = lean_box(0);
v___x_1141_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__78));
v___x_1142_ = l_Lean_mkConst(v___x_1141_, v___x_1140_);
return v___x_1142_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_of_binaryReflection(lean_object* v_lhsExpr_1165_, lean_object* v_rhsExpr_1166_, uint8_t v_pred_1167_, lean_object* v_origExpr_1168_, lean_object* v_a_1169_, lean_object* v_a_1170_, lean_object* v_a_1171_, lean_object* v_a_1172_, lean_object* v_a_1173_, lean_object* v_a_1174_){
_start:
{
lean_object* v___x_1176_; 
lean_inc_ref(v_lhsExpr_1165_);
v___x_1176_ = l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of(v_lhsExpr_1165_, v_a_1169_, v_a_1170_, v_a_1171_, v_a_1172_, v_a_1173_, v_a_1174_);
if (lean_obj_tag(v___x_1176_) == 0)
{
lean_object* v_a_1177_; lean_object* v___x_1179_; uint8_t v_isShared_1180_; uint8_t v_isSharedCheck_1206_; 
v_a_1177_ = lean_ctor_get(v___x_1176_, 0);
v_isSharedCheck_1206_ = !lean_is_exclusive(v___x_1176_);
if (v_isSharedCheck_1206_ == 0)
{
v___x_1179_ = v___x_1176_;
v_isShared_1180_ = v_isSharedCheck_1206_;
goto v_resetjp_1178_;
}
else
{
lean_inc(v_a_1177_);
lean_dec(v___x_1176_);
v___x_1179_ = lean_box(0);
v_isShared_1180_ = v_isSharedCheck_1206_;
goto v_resetjp_1178_;
}
v_resetjp_1178_:
{
if (lean_obj_tag(v_a_1177_) == 1)
{
lean_object* v_val_1181_; lean_object* v___x_1182_; 
lean_del_object(v___x_1179_);
v_val_1181_ = lean_ctor_get(v_a_1177_, 0);
lean_inc(v_val_1181_);
lean_dec_ref(v_a_1177_);
lean_inc_ref(v_rhsExpr_1166_);
v___x_1182_ = l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of(v_rhsExpr_1166_, v_a_1169_, v_a_1170_, v_a_1171_, v_a_1172_, v_a_1173_, v_a_1174_);
if (lean_obj_tag(v___x_1182_) == 0)
{
lean_object* v_a_1183_; lean_object* v___x_1185_; uint8_t v_isShared_1186_; uint8_t v_isSharedCheck_1193_; 
v_a_1183_ = lean_ctor_get(v___x_1182_, 0);
v_isSharedCheck_1193_ = !lean_is_exclusive(v___x_1182_);
if (v_isSharedCheck_1193_ == 0)
{
v___x_1185_ = v___x_1182_;
v_isShared_1186_ = v_isSharedCheck_1193_;
goto v_resetjp_1184_;
}
else
{
lean_inc(v_a_1183_);
lean_dec(v___x_1182_);
v___x_1185_ = lean_box(0);
v_isShared_1186_ = v_isSharedCheck_1193_;
goto v_resetjp_1184_;
}
v_resetjp_1184_:
{
if (lean_obj_tag(v_a_1183_) == 1)
{
lean_object* v_val_1187_; lean_object* v___x_1188_; 
lean_del_object(v___x_1185_);
v_val_1187_ = lean_ctor_get(v_a_1183_, 0);
lean_inc(v_val_1187_);
lean_dec_ref(v_a_1183_);
v___x_1188_ = l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_mkBinPred___redArg(v_val_1181_, v_val_1187_, v_lhsExpr_1165_, v_rhsExpr_1166_, v_pred_1167_, v_origExpr_1168_);
return v___x_1188_;
}
else
{
lean_object* v___x_1189_; lean_object* v___x_1191_; 
lean_dec(v_a_1183_);
lean_dec(v_val_1181_);
lean_dec_ref(v_origExpr_1168_);
lean_dec_ref(v_rhsExpr_1166_);
lean_dec_ref(v_lhsExpr_1165_);
v___x_1189_ = lean_box(0);
if (v_isShared_1186_ == 0)
{
lean_ctor_set(v___x_1185_, 0, v___x_1189_);
v___x_1191_ = v___x_1185_;
goto v_reusejp_1190_;
}
else
{
lean_object* v_reuseFailAlloc_1192_; 
v_reuseFailAlloc_1192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1192_, 0, v___x_1189_);
v___x_1191_ = v_reuseFailAlloc_1192_;
goto v_reusejp_1190_;
}
v_reusejp_1190_:
{
return v___x_1191_;
}
}
}
}
else
{
lean_object* v_a_1194_; lean_object* v___x_1196_; uint8_t v_isShared_1197_; uint8_t v_isSharedCheck_1201_; 
lean_dec(v_val_1181_);
lean_dec_ref(v_origExpr_1168_);
lean_dec_ref(v_rhsExpr_1166_);
lean_dec_ref(v_lhsExpr_1165_);
v_a_1194_ = lean_ctor_get(v___x_1182_, 0);
v_isSharedCheck_1201_ = !lean_is_exclusive(v___x_1182_);
if (v_isSharedCheck_1201_ == 0)
{
v___x_1196_ = v___x_1182_;
v_isShared_1197_ = v_isSharedCheck_1201_;
goto v_resetjp_1195_;
}
else
{
lean_inc(v_a_1194_);
lean_dec(v___x_1182_);
v___x_1196_ = lean_box(0);
v_isShared_1197_ = v_isSharedCheck_1201_;
goto v_resetjp_1195_;
}
v_resetjp_1195_:
{
lean_object* v___x_1199_; 
if (v_isShared_1197_ == 0)
{
v___x_1199_ = v___x_1196_;
goto v_reusejp_1198_;
}
else
{
lean_object* v_reuseFailAlloc_1200_; 
v_reuseFailAlloc_1200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1200_, 0, v_a_1194_);
v___x_1199_ = v_reuseFailAlloc_1200_;
goto v_reusejp_1198_;
}
v_reusejp_1198_:
{
return v___x_1199_;
}
}
}
}
else
{
lean_object* v___x_1202_; lean_object* v___x_1204_; 
lean_dec(v_a_1177_);
lean_dec_ref(v_origExpr_1168_);
lean_dec_ref(v_rhsExpr_1166_);
lean_dec_ref(v_lhsExpr_1165_);
v___x_1202_ = lean_box(0);
if (v_isShared_1180_ == 0)
{
lean_ctor_set(v___x_1179_, 0, v___x_1202_);
v___x_1204_ = v___x_1179_;
goto v_reusejp_1203_;
}
else
{
lean_object* v_reuseFailAlloc_1205_; 
v_reuseFailAlloc_1205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1205_, 0, v___x_1202_);
v___x_1204_ = v_reuseFailAlloc_1205_;
goto v_reusejp_1203_;
}
v_reusejp_1203_:
{
return v___x_1204_;
}
}
}
}
else
{
lean_object* v_a_1207_; lean_object* v___x_1209_; uint8_t v_isShared_1210_; uint8_t v_isSharedCheck_1214_; 
lean_dec_ref(v_origExpr_1168_);
lean_dec_ref(v_rhsExpr_1166_);
lean_dec_ref(v_lhsExpr_1165_);
v_a_1207_ = lean_ctor_get(v___x_1176_, 0);
v_isSharedCheck_1214_ = !lean_is_exclusive(v___x_1176_);
if (v_isSharedCheck_1214_ == 0)
{
v___x_1209_ = v___x_1176_;
v_isShared_1210_ = v_isSharedCheck_1214_;
goto v_resetjp_1208_;
}
else
{
lean_inc(v_a_1207_);
lean_dec(v___x_1176_);
v___x_1209_ = lean_box(0);
v_isShared_1210_ = v_isSharedCheck_1214_;
goto v_resetjp_1208_;
}
v_resetjp_1208_:
{
lean_object* v___x_1212_; 
if (v_isShared_1210_ == 0)
{
v___x_1212_ = v___x_1209_;
goto v_reusejp_1211_;
}
else
{
lean_object* v_reuseFailAlloc_1213_; 
v_reuseFailAlloc_1213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1213_, 0, v_a_1207_);
v___x_1212_ = v_reuseFailAlloc_1213_;
goto v_reusejp_1211_;
}
v_reusejp_1211_:
{
return v___x_1212_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_of_go(lean_object* v_origExpr_1215_, lean_object* v_a_1216_, lean_object* v_a_1217_, lean_object* v_a_1218_, lean_object* v_a_1219_, lean_object* v_a_1220_, lean_object* v_a_1221_){
_start:
{
lean_object* v___x_1226_; 
lean_inc_ref(v_origExpr_1215_);
v___x_1226_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_origExpr_1215_, v_a_1219_);
if (lean_obj_tag(v___x_1226_) == 0)
{
lean_object* v_a_1227_; lean_object* v___x_1229_; uint8_t v_isShared_1230_; uint8_t v_isSharedCheck_1325_; 
v_a_1227_ = lean_ctor_get(v___x_1226_, 0);
v_isSharedCheck_1325_ = !lean_is_exclusive(v___x_1226_);
if (v_isSharedCheck_1325_ == 0)
{
v___x_1229_ = v___x_1226_;
v_isShared_1230_ = v_isSharedCheck_1325_;
goto v_resetjp_1228_;
}
else
{
lean_inc(v_a_1227_);
lean_dec(v___x_1226_);
v___x_1229_ = lean_box(0);
v_isShared_1230_ = v_isSharedCheck_1325_;
goto v_resetjp_1228_;
}
v_resetjp_1228_:
{
lean_object* v___x_1236_; uint8_t v___x_1237_; 
v___x_1236_ = l_Lean_Expr_cleanupAnnotations(v_a_1227_);
v___x_1237_ = l_Lean_Expr_isApp(v___x_1236_);
if (v___x_1237_ == 0)
{
lean_dec_ref(v___x_1236_);
lean_dec_ref(v_origExpr_1215_);
goto v___jp_1231_;
}
else
{
lean_object* v_arg_1238_; lean_object* v___x_1239_; uint8_t v___x_1240_; 
v_arg_1238_ = lean_ctor_get(v___x_1236_, 1);
lean_inc_ref(v_arg_1238_);
v___x_1239_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1236_);
v___x_1240_ = l_Lean_Expr_isApp(v___x_1239_);
if (v___x_1240_ == 0)
{
lean_dec_ref(v___x_1239_);
lean_dec_ref(v_arg_1238_);
lean_dec_ref(v_origExpr_1215_);
goto v___jp_1231_;
}
else
{
lean_object* v_arg_1241_; lean_object* v___x_1242_; uint8_t v___x_1243_; 
v_arg_1241_ = lean_ctor_get(v___x_1239_, 1);
lean_inc_ref(v_arg_1241_);
v___x_1242_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1239_);
v___x_1243_ = l_Lean_Expr_isApp(v___x_1242_);
if (v___x_1243_ == 0)
{
lean_dec_ref(v___x_1242_);
lean_dec_ref(v_arg_1241_);
lean_dec_ref(v_arg_1238_);
lean_dec_ref(v_origExpr_1215_);
goto v___jp_1231_;
}
else
{
lean_object* v___x_1244_; lean_object* v___x_1245_; uint8_t v___x_1246_; 
v___x_1244_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1242_);
v___x_1245_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_of_go___closed__2));
v___x_1246_ = l_Lean_Expr_isConstOf(v___x_1244_, v___x_1245_);
if (v___x_1246_ == 0)
{
lean_object* v___x_1247_; uint8_t v___x_1248_; 
v___x_1247_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_of_go___closed__4));
v___x_1248_ = l_Lean_Expr_isConstOf(v___x_1244_, v___x_1247_);
if (v___x_1248_ == 0)
{
uint8_t v___x_1249_; 
v___x_1249_ = l_Lean_Expr_isApp(v___x_1244_);
if (v___x_1249_ == 0)
{
lean_dec_ref(v___x_1244_);
lean_dec_ref(v_arg_1241_);
lean_dec_ref(v_arg_1238_);
lean_dec_ref(v_origExpr_1215_);
goto v___jp_1231_;
}
else
{
lean_object* v_arg_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; uint8_t v___x_1253_; 
v_arg_1250_ = lean_ctor_get(v___x_1244_, 1);
lean_inc_ref(v_arg_1250_);
v___x_1251_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1244_);
v___x_1252_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_of_go___closed__7));
v___x_1253_ = l_Lean_Expr_isConstOf(v___x_1251_, v___x_1252_);
lean_dec_ref(v___x_1251_);
if (v___x_1253_ == 0)
{
lean_dec_ref(v_arg_1250_);
lean_dec_ref(v_arg_1241_);
lean_dec_ref(v_arg_1238_);
lean_dec_ref(v_origExpr_1215_);
goto v___jp_1231_;
}
else
{
lean_object* v___x_1254_; uint8_t v___x_1255_; 
lean_del_object(v___x_1229_);
v___x_1254_ = l_Lean_Expr_cleanupAnnotations(v_arg_1250_);
v___x_1255_ = l_Lean_Expr_isApp(v___x_1254_);
if (v___x_1255_ == 0)
{
lean_dec_ref(v___x_1254_);
lean_dec_ref(v_arg_1241_);
lean_dec_ref(v_arg_1238_);
lean_dec_ref(v_origExpr_1215_);
goto v___jp_1223_;
}
else
{
lean_object* v___x_1256_; lean_object* v___x_1257_; uint8_t v___x_1258_; 
v___x_1256_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1254_);
v___x_1257_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_of_go___closed__8));
v___x_1258_ = l_Lean_Expr_isConstOf(v___x_1256_, v___x_1257_);
lean_dec_ref(v___x_1256_);
if (v___x_1258_ == 0)
{
lean_dec_ref(v_arg_1241_);
lean_dec_ref(v_arg_1238_);
lean_dec_ref(v_origExpr_1215_);
goto v___jp_1223_;
}
else
{
uint8_t v___x_1259_; lean_object* v___x_1260_; 
v___x_1259_ = 0;
v___x_1260_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_of_binaryReflection(v_arg_1241_, v_arg_1238_, v___x_1259_, v_origExpr_1215_, v_a_1216_, v_a_1217_, v_a_1218_, v_a_1219_, v_a_1220_, v_a_1221_);
return v___x_1260_;
}
}
}
}
}
else
{
uint8_t v___x_1261_; lean_object* v___x_1262_; 
lean_dec_ref(v___x_1244_);
lean_del_object(v___x_1229_);
v___x_1261_ = 1;
v___x_1262_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_of_binaryReflection(v_arg_1241_, v_arg_1238_, v___x_1261_, v_origExpr_1215_, v_a_1216_, v_a_1217_, v_a_1218_, v_a_1219_, v_a_1220_, v_a_1221_);
return v___x_1262_;
}
}
else
{
lean_object* v___x_1263_; 
lean_dec_ref(v___x_1244_);
lean_del_object(v___x_1229_);
lean_inc_ref(v_arg_1241_);
v___x_1263_ = l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of(v_arg_1241_, v_a_1216_, v_a_1217_, v_a_1218_, v_a_1219_, v_a_1220_, v_a_1221_);
if (lean_obj_tag(v___x_1263_) == 0)
{
lean_object* v_a_1264_; lean_object* v___x_1266_; uint8_t v_isShared_1267_; uint8_t v_isSharedCheck_1316_; 
v_a_1264_ = lean_ctor_get(v___x_1263_, 0);
v_isSharedCheck_1316_ = !lean_is_exclusive(v___x_1263_);
if (v_isSharedCheck_1316_ == 0)
{
v___x_1266_ = v___x_1263_;
v_isShared_1267_ = v_isSharedCheck_1316_;
goto v_resetjp_1265_;
}
else
{
lean_inc(v_a_1264_);
lean_dec(v___x_1263_);
v___x_1266_ = lean_box(0);
v_isShared_1267_ = v_isSharedCheck_1316_;
goto v_resetjp_1265_;
}
v_resetjp_1265_:
{
if (lean_obj_tag(v_a_1264_) == 1)
{
lean_object* v_val_1268_; lean_object* v___x_1269_; 
lean_del_object(v___x_1266_);
v_val_1268_ = lean_ctor_get(v_a_1264_, 0);
lean_inc(v_val_1268_);
lean_dec_ref(v_a_1264_);
v___x_1269_ = l_Lean_Meta_getNatValue_x3f(v_arg_1238_, v_a_1218_, v_a_1219_, v_a_1220_, v_a_1221_);
lean_dec_ref(v_arg_1238_);
if (lean_obj_tag(v___x_1269_) == 0)
{
lean_object* v_a_1270_; lean_object* v___x_1272_; uint8_t v_isShared_1273_; uint8_t v_isSharedCheck_1303_; 
v_a_1270_ = lean_ctor_get(v___x_1269_, 0);
v_isSharedCheck_1303_ = !lean_is_exclusive(v___x_1269_);
if (v_isSharedCheck_1303_ == 0)
{
v___x_1272_ = v___x_1269_;
v_isShared_1273_ = v_isSharedCheck_1303_;
goto v_resetjp_1271_;
}
else
{
lean_inc(v_a_1270_);
lean_dec(v___x_1269_);
v___x_1272_ = lean_box(0);
v_isShared_1273_ = v_isSharedCheck_1303_;
goto v_resetjp_1271_;
}
v_resetjp_1271_:
{
if (lean_obj_tag(v_a_1270_) == 1)
{
lean_object* v_val_1274_; lean_object* v___x_1276_; uint8_t v_isShared_1277_; uint8_t v_isSharedCheck_1298_; 
lean_del_object(v___x_1272_);
v_val_1274_ = lean_ctor_get(v_a_1270_, 0);
v_isSharedCheck_1298_ = !lean_is_exclusive(v_a_1270_);
if (v_isSharedCheck_1298_ == 0)
{
v___x_1276_ = v_a_1270_;
v_isShared_1277_ = v_isSharedCheck_1298_;
goto v_resetjp_1275_;
}
else
{
lean_inc(v_val_1274_);
lean_dec(v_a_1270_);
v___x_1276_ = lean_box(0);
v_isShared_1277_ = v_isSharedCheck_1298_;
goto v_resetjp_1275_;
}
v_resetjp_1275_:
{
lean_object* v___x_1278_; 
v___x_1278_ = l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_mkGetLsbD___redArg(v_val_1268_, v_arg_1241_, v_val_1274_, v_origExpr_1215_);
if (lean_obj_tag(v___x_1278_) == 0)
{
lean_object* v_a_1279_; lean_object* v___x_1281_; uint8_t v_isShared_1282_; uint8_t v_isSharedCheck_1289_; 
v_a_1279_ = lean_ctor_get(v___x_1278_, 0);
v_isSharedCheck_1289_ = !lean_is_exclusive(v___x_1278_);
if (v_isSharedCheck_1289_ == 0)
{
v___x_1281_ = v___x_1278_;
v_isShared_1282_ = v_isSharedCheck_1289_;
goto v_resetjp_1280_;
}
else
{
lean_inc(v_a_1279_);
lean_dec(v___x_1278_);
v___x_1281_ = lean_box(0);
v_isShared_1282_ = v_isSharedCheck_1289_;
goto v_resetjp_1280_;
}
v_resetjp_1280_:
{
lean_object* v___x_1284_; 
if (v_isShared_1277_ == 0)
{
lean_ctor_set(v___x_1276_, 0, v_a_1279_);
v___x_1284_ = v___x_1276_;
goto v_reusejp_1283_;
}
else
{
lean_object* v_reuseFailAlloc_1288_; 
v_reuseFailAlloc_1288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1288_, 0, v_a_1279_);
v___x_1284_ = v_reuseFailAlloc_1288_;
goto v_reusejp_1283_;
}
v_reusejp_1283_:
{
lean_object* v___x_1286_; 
if (v_isShared_1282_ == 0)
{
lean_ctor_set(v___x_1281_, 0, v___x_1284_);
v___x_1286_ = v___x_1281_;
goto v_reusejp_1285_;
}
else
{
lean_object* v_reuseFailAlloc_1287_; 
v_reuseFailAlloc_1287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1287_, 0, v___x_1284_);
v___x_1286_ = v_reuseFailAlloc_1287_;
goto v_reusejp_1285_;
}
v_reusejp_1285_:
{
return v___x_1286_;
}
}
}
}
else
{
lean_object* v_a_1290_; lean_object* v___x_1292_; uint8_t v_isShared_1293_; uint8_t v_isSharedCheck_1297_; 
lean_del_object(v___x_1276_);
v_a_1290_ = lean_ctor_get(v___x_1278_, 0);
v_isSharedCheck_1297_ = !lean_is_exclusive(v___x_1278_);
if (v_isSharedCheck_1297_ == 0)
{
v___x_1292_ = v___x_1278_;
v_isShared_1293_ = v_isSharedCheck_1297_;
goto v_resetjp_1291_;
}
else
{
lean_inc(v_a_1290_);
lean_dec(v___x_1278_);
v___x_1292_ = lean_box(0);
v_isShared_1293_ = v_isSharedCheck_1297_;
goto v_resetjp_1291_;
}
v_resetjp_1291_:
{
lean_object* v___x_1295_; 
if (v_isShared_1293_ == 0)
{
v___x_1295_ = v___x_1292_;
goto v_reusejp_1294_;
}
else
{
lean_object* v_reuseFailAlloc_1296_; 
v_reuseFailAlloc_1296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1296_, 0, v_a_1290_);
v___x_1295_ = v_reuseFailAlloc_1296_;
goto v_reusejp_1294_;
}
v_reusejp_1294_:
{
return v___x_1295_;
}
}
}
}
}
else
{
lean_object* v___x_1299_; lean_object* v___x_1301_; 
lean_dec(v_a_1270_);
lean_dec(v_val_1268_);
lean_dec_ref(v_arg_1241_);
lean_dec_ref(v_origExpr_1215_);
v___x_1299_ = lean_box(0);
if (v_isShared_1273_ == 0)
{
lean_ctor_set(v___x_1272_, 0, v___x_1299_);
v___x_1301_ = v___x_1272_;
goto v_reusejp_1300_;
}
else
{
lean_object* v_reuseFailAlloc_1302_; 
v_reuseFailAlloc_1302_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1302_, 0, v___x_1299_);
v___x_1301_ = v_reuseFailAlloc_1302_;
goto v_reusejp_1300_;
}
v_reusejp_1300_:
{
return v___x_1301_;
}
}
}
}
else
{
lean_object* v_a_1304_; lean_object* v___x_1306_; uint8_t v_isShared_1307_; uint8_t v_isSharedCheck_1311_; 
lean_dec(v_val_1268_);
lean_dec_ref(v_arg_1241_);
lean_dec_ref(v_origExpr_1215_);
v_a_1304_ = lean_ctor_get(v___x_1269_, 0);
v_isSharedCheck_1311_ = !lean_is_exclusive(v___x_1269_);
if (v_isSharedCheck_1311_ == 0)
{
v___x_1306_ = v___x_1269_;
v_isShared_1307_ = v_isSharedCheck_1311_;
goto v_resetjp_1305_;
}
else
{
lean_inc(v_a_1304_);
lean_dec(v___x_1269_);
v___x_1306_ = lean_box(0);
v_isShared_1307_ = v_isSharedCheck_1311_;
goto v_resetjp_1305_;
}
v_resetjp_1305_:
{
lean_object* v___x_1309_; 
if (v_isShared_1307_ == 0)
{
v___x_1309_ = v___x_1306_;
goto v_reusejp_1308_;
}
else
{
lean_object* v_reuseFailAlloc_1310_; 
v_reuseFailAlloc_1310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1310_, 0, v_a_1304_);
v___x_1309_ = v_reuseFailAlloc_1310_;
goto v_reusejp_1308_;
}
v_reusejp_1308_:
{
return v___x_1309_;
}
}
}
}
else
{
lean_object* v___x_1312_; lean_object* v___x_1314_; 
lean_dec(v_a_1264_);
lean_dec_ref(v_arg_1241_);
lean_dec_ref(v_arg_1238_);
lean_dec_ref(v_origExpr_1215_);
v___x_1312_ = lean_box(0);
if (v_isShared_1267_ == 0)
{
lean_ctor_set(v___x_1266_, 0, v___x_1312_);
v___x_1314_ = v___x_1266_;
goto v_reusejp_1313_;
}
else
{
lean_object* v_reuseFailAlloc_1315_; 
v_reuseFailAlloc_1315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1315_, 0, v___x_1312_);
v___x_1314_ = v_reuseFailAlloc_1315_;
goto v_reusejp_1313_;
}
v_reusejp_1313_:
{
return v___x_1314_;
}
}
}
}
else
{
lean_object* v_a_1317_; lean_object* v___x_1319_; uint8_t v_isShared_1320_; uint8_t v_isSharedCheck_1324_; 
lean_dec_ref(v_arg_1241_);
lean_dec_ref(v_arg_1238_);
lean_dec_ref(v_origExpr_1215_);
v_a_1317_ = lean_ctor_get(v___x_1263_, 0);
v_isSharedCheck_1324_ = !lean_is_exclusive(v___x_1263_);
if (v_isSharedCheck_1324_ == 0)
{
v___x_1319_ = v___x_1263_;
v_isShared_1320_ = v_isSharedCheck_1324_;
goto v_resetjp_1318_;
}
else
{
lean_inc(v_a_1317_);
lean_dec(v___x_1263_);
v___x_1319_ = lean_box(0);
v_isShared_1320_ = v_isSharedCheck_1324_;
goto v_resetjp_1318_;
}
v_resetjp_1318_:
{
lean_object* v___x_1322_; 
if (v_isShared_1320_ == 0)
{
v___x_1322_ = v___x_1319_;
goto v_reusejp_1321_;
}
else
{
lean_object* v_reuseFailAlloc_1323_; 
v_reuseFailAlloc_1323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1323_, 0, v_a_1317_);
v___x_1322_ = v_reuseFailAlloc_1323_;
goto v_reusejp_1321_;
}
v_reusejp_1321_:
{
return v___x_1322_;
}
}
}
}
}
}
}
v___jp_1231_:
{
lean_object* v___x_1232_; lean_object* v___x_1234_; 
v___x_1232_ = lean_box(0);
if (v_isShared_1230_ == 0)
{
lean_ctor_set(v___x_1229_, 0, v___x_1232_);
v___x_1234_ = v___x_1229_;
goto v_reusejp_1233_;
}
else
{
lean_object* v_reuseFailAlloc_1235_; 
v_reuseFailAlloc_1235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1235_, 0, v___x_1232_);
v___x_1234_ = v_reuseFailAlloc_1235_;
goto v_reusejp_1233_;
}
v_reusejp_1233_:
{
return v___x_1234_;
}
}
}
}
else
{
lean_object* v_a_1326_; lean_object* v___x_1328_; uint8_t v_isShared_1329_; uint8_t v_isSharedCheck_1333_; 
lean_dec_ref(v_origExpr_1215_);
v_a_1326_ = lean_ctor_get(v___x_1226_, 0);
v_isSharedCheck_1333_ = !lean_is_exclusive(v___x_1226_);
if (v_isSharedCheck_1333_ == 0)
{
v___x_1328_ = v___x_1226_;
v_isShared_1329_ = v_isSharedCheck_1333_;
goto v_resetjp_1327_;
}
else
{
lean_inc(v_a_1326_);
lean_dec(v___x_1226_);
v___x_1328_ = lean_box(0);
v_isShared_1329_ = v_isSharedCheck_1333_;
goto v_resetjp_1327_;
}
v_resetjp_1327_:
{
lean_object* v___x_1331_; 
if (v_isShared_1329_ == 0)
{
v___x_1331_ = v___x_1328_;
goto v_reusejp_1330_;
}
else
{
lean_object* v_reuseFailAlloc_1332_; 
v_reuseFailAlloc_1332_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1332_, 0, v_a_1326_);
v___x_1331_ = v_reuseFailAlloc_1332_;
goto v_reusejp_1330_;
}
v_reusejp_1330_:
{
return v___x_1331_;
}
}
}
v___jp_1223_:
{
lean_object* v___x_1224_; lean_object* v___x_1225_; 
v___x_1224_ = lean_box(0);
v___x_1225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1225_, 0, v___x_1224_);
return v___x_1225_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVPredCache___at___00Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_of_spec__5(lean_object* v_e_1334_, lean_object* v_a_1335_, lean_object* v_a_1336_, lean_object* v_a_1337_, lean_object* v_a_1338_, lean_object* v_a_1339_, lean_object* v_a_1340_){
_start:
{
lean_object* v___y_1343_; lean_object* v___x_1366_; lean_object* v_bvPredCache_1367_; lean_object* v___x_1368_; 
v___x_1366_ = lean_st_ref_get(v_a_1335_);
v_bvPredCache_1367_ = lean_ctor_get(v___x_1366_, 2);
lean_inc_ref(v_bvPredCache_1367_);
lean_dec(v___x_1366_);
v___x_1368_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom_spec__2_spec__12___redArg(v_bvPredCache_1367_, v_e_1334_);
lean_dec_ref(v_bvPredCache_1367_);
if (lean_obj_tag(v___x_1368_) == 0)
{
lean_object* v___x_1369_; 
lean_inc_ref(v_e_1334_);
v___x_1369_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_of_go(v_e_1334_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_, v_a_1339_, v_a_1340_);
if (lean_obj_tag(v___x_1369_) == 0)
{
lean_object* v_a_1370_; 
v_a_1370_ = lean_ctor_get(v___x_1369_, 0);
lean_inc(v_a_1370_);
if (lean_obj_tag(v_a_1370_) == 0)
{
lean_object* v___x_1371_; 
lean_dec_ref(v___x_1369_);
lean_inc_ref(v_e_1334_);
v___x_1371_ = l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_boolAtom(v_e_1334_, v_a_1336_, v_a_1337_, v_a_1338_, v_a_1339_, v_a_1340_);
v___y_1343_ = v___x_1371_;
goto v___jp_1342_;
}
else
{
lean_dec_ref(v_a_1370_);
v___y_1343_ = v___x_1369_;
goto v___jp_1342_;
}
}
else
{
v___y_1343_ = v___x_1369_;
goto v___jp_1342_;
}
}
else
{
lean_object* v_val_1372_; lean_object* v___x_1374_; uint8_t v_isShared_1375_; uint8_t v_isSharedCheck_1379_; 
lean_dec_ref(v_e_1334_);
v_val_1372_ = lean_ctor_get(v___x_1368_, 0);
v_isSharedCheck_1379_ = !lean_is_exclusive(v___x_1368_);
if (v_isSharedCheck_1379_ == 0)
{
v___x_1374_ = v___x_1368_;
v_isShared_1375_ = v_isSharedCheck_1379_;
goto v_resetjp_1373_;
}
else
{
lean_inc(v_val_1372_);
lean_dec(v___x_1368_);
v___x_1374_ = lean_box(0);
v_isShared_1375_ = v_isSharedCheck_1379_;
goto v_resetjp_1373_;
}
v_resetjp_1373_:
{
lean_object* v___x_1377_; 
if (v_isShared_1375_ == 0)
{
lean_ctor_set_tag(v___x_1374_, 0);
v___x_1377_ = v___x_1374_;
goto v_reusejp_1376_;
}
else
{
lean_object* v_reuseFailAlloc_1378_; 
v_reuseFailAlloc_1378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1378_, 0, v_val_1372_);
v___x_1377_ = v_reuseFailAlloc_1378_;
goto v_reusejp_1376_;
}
v_reusejp_1376_:
{
return v___x_1377_;
}
}
}
v___jp_1342_:
{
if (lean_obj_tag(v___y_1343_) == 0)
{
lean_object* v_a_1344_; lean_object* v___x_1346_; uint8_t v_isShared_1347_; uint8_t v_isSharedCheck_1365_; 
v_a_1344_ = lean_ctor_get(v___y_1343_, 0);
v_isSharedCheck_1365_ = !lean_is_exclusive(v___y_1343_);
if (v_isSharedCheck_1365_ == 0)
{
v___x_1346_ = v___y_1343_;
v_isShared_1347_ = v_isSharedCheck_1365_;
goto v_resetjp_1345_;
}
else
{
lean_inc(v_a_1344_);
lean_dec(v___y_1343_);
v___x_1346_ = lean_box(0);
v_isShared_1347_ = v_isSharedCheck_1365_;
goto v_resetjp_1345_;
}
v_resetjp_1345_:
{
lean_object* v___x_1348_; lean_object* v_lemmas_1349_; lean_object* v_bvExprCache_1350_; lean_object* v_bvPredCache_1351_; lean_object* v_bvLogicalCache_1352_; lean_object* v___x_1354_; uint8_t v_isShared_1355_; uint8_t v_isSharedCheck_1364_; 
v___x_1348_ = lean_st_ref_take(v_a_1335_);
v_lemmas_1349_ = lean_ctor_get(v___x_1348_, 0);
v_bvExprCache_1350_ = lean_ctor_get(v___x_1348_, 1);
v_bvPredCache_1351_ = lean_ctor_get(v___x_1348_, 2);
v_bvLogicalCache_1352_ = lean_ctor_get(v___x_1348_, 3);
v_isSharedCheck_1364_ = !lean_is_exclusive(v___x_1348_);
if (v_isSharedCheck_1364_ == 0)
{
v___x_1354_ = v___x_1348_;
v_isShared_1355_ = v_isSharedCheck_1364_;
goto v_resetjp_1353_;
}
else
{
lean_inc(v_bvLogicalCache_1352_);
lean_inc(v_bvPredCache_1351_);
lean_inc(v_bvExprCache_1350_);
lean_inc(v_lemmas_1349_);
lean_dec(v___x_1348_);
v___x_1354_ = lean_box(0);
v_isShared_1355_ = v_isSharedCheck_1364_;
goto v_resetjp_1353_;
}
v_resetjp_1353_:
{
lean_object* v___x_1356_; lean_object* v___x_1358_; 
lean_inc(v_a_1344_);
v___x_1356_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13___redArg(v_bvPredCache_1351_, v_e_1334_, v_a_1344_);
if (v_isShared_1355_ == 0)
{
lean_ctor_set(v___x_1354_, 2, v___x_1356_);
v___x_1358_ = v___x_1354_;
goto v_reusejp_1357_;
}
else
{
lean_object* v_reuseFailAlloc_1363_; 
v_reuseFailAlloc_1363_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1363_, 0, v_lemmas_1349_);
lean_ctor_set(v_reuseFailAlloc_1363_, 1, v_bvExprCache_1350_);
lean_ctor_set(v_reuseFailAlloc_1363_, 2, v___x_1356_);
lean_ctor_set(v_reuseFailAlloc_1363_, 3, v_bvLogicalCache_1352_);
v___x_1358_ = v_reuseFailAlloc_1363_;
goto v_reusejp_1357_;
}
v_reusejp_1357_:
{
lean_object* v___x_1359_; lean_object* v___x_1361_; 
v___x_1359_ = lean_st_ref_set(v_a_1335_, v___x_1358_);
if (v_isShared_1347_ == 0)
{
v___x_1361_ = v___x_1346_;
goto v_reusejp_1360_;
}
else
{
lean_object* v_reuseFailAlloc_1362_; 
v_reuseFailAlloc_1362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1362_, 0, v_a_1344_);
v___x_1361_ = v_reuseFailAlloc_1362_;
goto v_reusejp_1360_;
}
v_reusejp_1360_:
{
return v___x_1361_;
}
}
}
}
}
else
{
lean_dec_ref(v_e_1334_);
return v___y_1343_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_of(lean_object* v_origExpr_1380_, lean_object* v_a_1381_, lean_object* v_a_1382_, lean_object* v_a_1383_, lean_object* v_a_1384_, lean_object* v_a_1385_, lean_object* v_a_1386_){
_start:
{
lean_object* v___x_1388_; 
v___x_1388_ = l_Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVPredCache___at___00Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_of_spec__5(v_origExpr_1380_, v_a_1381_, v_a_1382_, v_a_1383_, v_a_1384_, v_a_1385_, v_a_1386_);
return v___x_1388_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goPred(lean_object* v_origExpr_1389_, lean_object* v_a_1390_, lean_object* v_a_1391_, lean_object* v_a_1392_, lean_object* v_a_1393_, lean_object* v_a_1394_, lean_object* v_a_1395_){
_start:
{
lean_object* v___x_1397_; 
v___x_1397_ = l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_of(v_origExpr_1389_, v_a_1390_, v_a_1391_, v_a_1392_, v_a_1393_, v_a_1394_, v_a_1395_);
if (lean_obj_tag(v___x_1397_) == 0)
{
lean_object* v_a_1398_; lean_object* v___x_1400_; uint8_t v_isShared_1401_; uint8_t v_isSharedCheck_1431_; 
v_a_1398_ = lean_ctor_get(v___x_1397_, 0);
v_isSharedCheck_1431_ = !lean_is_exclusive(v___x_1397_);
if (v_isSharedCheck_1431_ == 0)
{
v___x_1400_ = v___x_1397_;
v_isShared_1401_ = v_isSharedCheck_1431_;
goto v_resetjp_1399_;
}
else
{
lean_inc(v_a_1398_);
lean_dec(v___x_1397_);
v___x_1400_ = lean_box(0);
v_isShared_1401_ = v_isSharedCheck_1431_;
goto v_resetjp_1399_;
}
v_resetjp_1399_:
{
if (lean_obj_tag(v_a_1398_) == 1)
{
lean_object* v_val_1402_; lean_object* v___x_1404_; uint8_t v_isShared_1405_; uint8_t v_isSharedCheck_1426_; 
lean_del_object(v___x_1400_);
v_val_1402_ = lean_ctor_get(v_a_1398_, 0);
v_isSharedCheck_1426_ = !lean_is_exclusive(v_a_1398_);
if (v_isSharedCheck_1426_ == 0)
{
v___x_1404_ = v_a_1398_;
v_isShared_1405_ = v_isSharedCheck_1426_;
goto v_resetjp_1403_;
}
else
{
lean_inc(v_val_1402_);
lean_dec(v_a_1398_);
v___x_1404_ = lean_box(0);
v_isShared_1405_ = v_isSharedCheck_1426_;
goto v_resetjp_1403_;
}
v_resetjp_1403_:
{
lean_object* v___x_1406_; 
v___x_1406_ = l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_ofPred___redArg(v_val_1402_);
if (lean_obj_tag(v___x_1406_) == 0)
{
lean_object* v_a_1407_; lean_object* v___x_1409_; uint8_t v_isShared_1410_; uint8_t v_isSharedCheck_1417_; 
v_a_1407_ = lean_ctor_get(v___x_1406_, 0);
v_isSharedCheck_1417_ = !lean_is_exclusive(v___x_1406_);
if (v_isSharedCheck_1417_ == 0)
{
v___x_1409_ = v___x_1406_;
v_isShared_1410_ = v_isSharedCheck_1417_;
goto v_resetjp_1408_;
}
else
{
lean_inc(v_a_1407_);
lean_dec(v___x_1406_);
v___x_1409_ = lean_box(0);
v_isShared_1410_ = v_isSharedCheck_1417_;
goto v_resetjp_1408_;
}
v_resetjp_1408_:
{
lean_object* v___x_1412_; 
if (v_isShared_1405_ == 0)
{
lean_ctor_set(v___x_1404_, 0, v_a_1407_);
v___x_1412_ = v___x_1404_;
goto v_reusejp_1411_;
}
else
{
lean_object* v_reuseFailAlloc_1416_; 
v_reuseFailAlloc_1416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1416_, 0, v_a_1407_);
v___x_1412_ = v_reuseFailAlloc_1416_;
goto v_reusejp_1411_;
}
v_reusejp_1411_:
{
lean_object* v___x_1414_; 
if (v_isShared_1410_ == 0)
{
lean_ctor_set(v___x_1409_, 0, v___x_1412_);
v___x_1414_ = v___x_1409_;
goto v_reusejp_1413_;
}
else
{
lean_object* v_reuseFailAlloc_1415_; 
v_reuseFailAlloc_1415_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1415_, 0, v___x_1412_);
v___x_1414_ = v_reuseFailAlloc_1415_;
goto v_reusejp_1413_;
}
v_reusejp_1413_:
{
return v___x_1414_;
}
}
}
}
else
{
lean_object* v_a_1418_; lean_object* v___x_1420_; uint8_t v_isShared_1421_; uint8_t v_isSharedCheck_1425_; 
lean_del_object(v___x_1404_);
v_a_1418_ = lean_ctor_get(v___x_1406_, 0);
v_isSharedCheck_1425_ = !lean_is_exclusive(v___x_1406_);
if (v_isSharedCheck_1425_ == 0)
{
v___x_1420_ = v___x_1406_;
v_isShared_1421_ = v_isSharedCheck_1425_;
goto v_resetjp_1419_;
}
else
{
lean_inc(v_a_1418_);
lean_dec(v___x_1406_);
v___x_1420_ = lean_box(0);
v_isShared_1421_ = v_isSharedCheck_1425_;
goto v_resetjp_1419_;
}
v_resetjp_1419_:
{
lean_object* v___x_1423_; 
if (v_isShared_1421_ == 0)
{
v___x_1423_ = v___x_1420_;
goto v_reusejp_1422_;
}
else
{
lean_object* v_reuseFailAlloc_1424_; 
v_reuseFailAlloc_1424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1424_, 0, v_a_1418_);
v___x_1423_ = v_reuseFailAlloc_1424_;
goto v_reusejp_1422_;
}
v_reusejp_1422_:
{
return v___x_1423_;
}
}
}
}
}
else
{
lean_object* v___x_1427_; lean_object* v___x_1429_; 
lean_dec(v_a_1398_);
v___x_1427_ = lean_box(0);
if (v_isShared_1401_ == 0)
{
lean_ctor_set(v___x_1400_, 0, v___x_1427_);
v___x_1429_ = v___x_1400_;
goto v_reusejp_1428_;
}
else
{
lean_object* v_reuseFailAlloc_1430_; 
v_reuseFailAlloc_1430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1430_, 0, v___x_1427_);
v___x_1429_ = v_reuseFailAlloc_1430_;
goto v_reusejp_1428_;
}
v_reusejp_1428_:
{
return v___x_1429_;
}
}
}
}
else
{
lean_object* v_a_1432_; lean_object* v___x_1434_; uint8_t v_isShared_1435_; uint8_t v_isSharedCheck_1439_; 
v_a_1432_ = lean_ctor_get(v___x_1397_, 0);
v_isSharedCheck_1439_ = !lean_is_exclusive(v___x_1397_);
if (v_isSharedCheck_1439_ == 0)
{
v___x_1434_ = v___x_1397_;
v_isShared_1435_ = v_isSharedCheck_1439_;
goto v_resetjp_1433_;
}
else
{
lean_inc(v_a_1432_);
lean_dec(v___x_1397_);
v___x_1434_ = lean_box(0);
v_isShared_1435_ = v_isSharedCheck_1439_;
goto v_resetjp_1433_;
}
v_resetjp_1433_:
{
lean_object* v___x_1437_; 
if (v_isShared_1435_ == 0)
{
v___x_1437_ = v___x_1434_;
goto v_reusejp_1436_;
}
else
{
lean_object* v_reuseFailAlloc_1438_; 
v_reuseFailAlloc_1438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1438_, 0, v_a_1432_);
v___x_1437_ = v_reuseFailAlloc_1438_;
goto v_reusejp_1436_;
}
v_reusejp_1436_:
{
return v___x_1437_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_gateReflection(lean_object* v_lhsExpr_1452_, lean_object* v_rhsExpr_1453_, uint8_t v_gate_1454_, lean_object* v_origExpr_1455_, lean_object* v_a_1456_, lean_object* v_a_1457_, lean_object* v_a_1458_, lean_object* v_a_1459_, lean_object* v_a_1460_, lean_object* v_a_1461_){
_start:
{
lean_object* v___x_1463_; 
lean_inc_ref(v_lhsExpr_1452_);
v___x_1463_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom(v_lhsExpr_1452_, v_a_1456_, v_a_1457_, v_a_1458_, v_a_1459_, v_a_1460_, v_a_1461_);
if (lean_obj_tag(v___x_1463_) == 0)
{
lean_object* v_a_1464_; lean_object* v___x_1466_; uint8_t v_isShared_1467_; uint8_t v_isSharedCheck_1508_; 
v_a_1464_ = lean_ctor_get(v___x_1463_, 0);
v_isSharedCheck_1508_ = !lean_is_exclusive(v___x_1463_);
if (v_isSharedCheck_1508_ == 0)
{
v___x_1466_ = v___x_1463_;
v_isShared_1467_ = v_isSharedCheck_1508_;
goto v_resetjp_1465_;
}
else
{
lean_inc(v_a_1464_);
lean_dec(v___x_1463_);
v___x_1466_ = lean_box(0);
v_isShared_1467_ = v_isSharedCheck_1508_;
goto v_resetjp_1465_;
}
v_resetjp_1465_:
{
if (lean_obj_tag(v_a_1464_) == 1)
{
lean_object* v_val_1468_; lean_object* v___x_1469_; 
lean_del_object(v___x_1466_);
v_val_1468_ = lean_ctor_get(v_a_1464_, 0);
lean_inc(v_val_1468_);
lean_dec_ref(v_a_1464_);
lean_inc_ref(v_rhsExpr_1453_);
v___x_1469_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom(v_rhsExpr_1453_, v_a_1456_, v_a_1457_, v_a_1458_, v_a_1459_, v_a_1460_, v_a_1461_);
if (lean_obj_tag(v___x_1469_) == 0)
{
lean_object* v_a_1470_; lean_object* v___x_1472_; uint8_t v_isShared_1473_; uint8_t v_isSharedCheck_1503_; 
v_a_1470_ = lean_ctor_get(v___x_1469_, 0);
v_isSharedCheck_1503_ = !lean_is_exclusive(v___x_1469_);
if (v_isSharedCheck_1503_ == 0)
{
v___x_1472_ = v___x_1469_;
v_isShared_1473_ = v_isSharedCheck_1503_;
goto v_resetjp_1471_;
}
else
{
lean_inc(v_a_1470_);
lean_dec(v___x_1469_);
v___x_1472_ = lean_box(0);
v_isShared_1473_ = v_isSharedCheck_1503_;
goto v_resetjp_1471_;
}
v_resetjp_1471_:
{
if (lean_obj_tag(v_a_1470_) == 1)
{
lean_object* v_val_1474_; lean_object* v___x_1476_; uint8_t v_isShared_1477_; uint8_t v_isSharedCheck_1498_; 
lean_del_object(v___x_1472_);
v_val_1474_ = lean_ctor_get(v_a_1470_, 0);
v_isSharedCheck_1498_ = !lean_is_exclusive(v_a_1470_);
if (v_isSharedCheck_1498_ == 0)
{
v___x_1476_ = v_a_1470_;
v_isShared_1477_ = v_isSharedCheck_1498_;
goto v_resetjp_1475_;
}
else
{
lean_inc(v_val_1474_);
lean_dec(v_a_1470_);
v___x_1476_ = lean_box(0);
v_isShared_1477_ = v_isSharedCheck_1498_;
goto v_resetjp_1475_;
}
v_resetjp_1475_:
{
lean_object* v___x_1478_; 
v___x_1478_ = l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_mkGate___redArg(v_val_1468_, v_val_1474_, v_lhsExpr_1452_, v_rhsExpr_1453_, v_gate_1454_, v_origExpr_1455_);
if (lean_obj_tag(v___x_1478_) == 0)
{
lean_object* v_a_1479_; lean_object* v___x_1481_; uint8_t v_isShared_1482_; uint8_t v_isSharedCheck_1489_; 
v_a_1479_ = lean_ctor_get(v___x_1478_, 0);
v_isSharedCheck_1489_ = !lean_is_exclusive(v___x_1478_);
if (v_isSharedCheck_1489_ == 0)
{
v___x_1481_ = v___x_1478_;
v_isShared_1482_ = v_isSharedCheck_1489_;
goto v_resetjp_1480_;
}
else
{
lean_inc(v_a_1479_);
lean_dec(v___x_1478_);
v___x_1481_ = lean_box(0);
v_isShared_1482_ = v_isSharedCheck_1489_;
goto v_resetjp_1480_;
}
v_resetjp_1480_:
{
lean_object* v___x_1484_; 
if (v_isShared_1477_ == 0)
{
lean_ctor_set(v___x_1476_, 0, v_a_1479_);
v___x_1484_ = v___x_1476_;
goto v_reusejp_1483_;
}
else
{
lean_object* v_reuseFailAlloc_1488_; 
v_reuseFailAlloc_1488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1488_, 0, v_a_1479_);
v___x_1484_ = v_reuseFailAlloc_1488_;
goto v_reusejp_1483_;
}
v_reusejp_1483_:
{
lean_object* v___x_1486_; 
if (v_isShared_1482_ == 0)
{
lean_ctor_set(v___x_1481_, 0, v___x_1484_);
v___x_1486_ = v___x_1481_;
goto v_reusejp_1485_;
}
else
{
lean_object* v_reuseFailAlloc_1487_; 
v_reuseFailAlloc_1487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1487_, 0, v___x_1484_);
v___x_1486_ = v_reuseFailAlloc_1487_;
goto v_reusejp_1485_;
}
v_reusejp_1485_:
{
return v___x_1486_;
}
}
}
}
else
{
lean_object* v_a_1490_; lean_object* v___x_1492_; uint8_t v_isShared_1493_; uint8_t v_isSharedCheck_1497_; 
lean_del_object(v___x_1476_);
v_a_1490_ = lean_ctor_get(v___x_1478_, 0);
v_isSharedCheck_1497_ = !lean_is_exclusive(v___x_1478_);
if (v_isSharedCheck_1497_ == 0)
{
v___x_1492_ = v___x_1478_;
v_isShared_1493_ = v_isSharedCheck_1497_;
goto v_resetjp_1491_;
}
else
{
lean_inc(v_a_1490_);
lean_dec(v___x_1478_);
v___x_1492_ = lean_box(0);
v_isShared_1493_ = v_isSharedCheck_1497_;
goto v_resetjp_1491_;
}
v_resetjp_1491_:
{
lean_object* v___x_1495_; 
if (v_isShared_1493_ == 0)
{
v___x_1495_ = v___x_1492_;
goto v_reusejp_1494_;
}
else
{
lean_object* v_reuseFailAlloc_1496_; 
v_reuseFailAlloc_1496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1496_, 0, v_a_1490_);
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
lean_object* v___x_1499_; lean_object* v___x_1501_; 
lean_dec(v_a_1470_);
lean_dec(v_val_1468_);
lean_dec_ref(v_origExpr_1455_);
lean_dec_ref(v_rhsExpr_1453_);
lean_dec_ref(v_lhsExpr_1452_);
v___x_1499_ = lean_box(0);
if (v_isShared_1473_ == 0)
{
lean_ctor_set(v___x_1472_, 0, v___x_1499_);
v___x_1501_ = v___x_1472_;
goto v_reusejp_1500_;
}
else
{
lean_object* v_reuseFailAlloc_1502_; 
v_reuseFailAlloc_1502_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1502_, 0, v___x_1499_);
v___x_1501_ = v_reuseFailAlloc_1502_;
goto v_reusejp_1500_;
}
v_reusejp_1500_:
{
return v___x_1501_;
}
}
}
}
else
{
lean_dec(v_val_1468_);
lean_dec_ref(v_origExpr_1455_);
lean_dec_ref(v_rhsExpr_1453_);
lean_dec_ref(v_lhsExpr_1452_);
return v___x_1469_;
}
}
else
{
lean_object* v___x_1504_; lean_object* v___x_1506_; 
lean_dec(v_a_1464_);
lean_dec_ref(v_origExpr_1455_);
lean_dec_ref(v_rhsExpr_1453_);
lean_dec_ref(v_lhsExpr_1452_);
v___x_1504_ = lean_box(0);
if (v_isShared_1467_ == 0)
{
lean_ctor_set(v___x_1466_, 0, v___x_1504_);
v___x_1506_ = v___x_1466_;
goto v_reusejp_1505_;
}
else
{
lean_object* v_reuseFailAlloc_1507_; 
v_reuseFailAlloc_1507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1507_, 0, v___x_1504_);
v___x_1506_ = v_reuseFailAlloc_1507_;
goto v_reusejp_1505_;
}
v_reusejp_1505_:
{
return v___x_1506_;
}
}
}
}
else
{
lean_dec_ref(v_origExpr_1455_);
lean_dec_ref(v_rhsExpr_1453_);
lean_dec_ref(v_lhsExpr_1452_);
return v___x_1463_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_go(lean_object* v_origExpr_1509_, lean_object* v_a_1510_, lean_object* v_a_1511_, lean_object* v_a_1512_, lean_object* v_a_1513_, lean_object* v_a_1514_, lean_object* v_a_1515_){
_start:
{
lean_object* v___x_1520_; lean_object* v___x_1521_; 
v___x_1520_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_go___closed__0));
v___x_1521_ = l_Lean_Core_checkSystem(v___x_1520_, v_a_1514_, v_a_1515_);
if (lean_obj_tag(v___x_1521_) == 0)
{
lean_object* v___x_1522_; 
lean_dec_ref(v___x_1521_);
lean_inc_ref(v_origExpr_1509_);
v___x_1522_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_origExpr_1509_, v_a_1513_);
if (lean_obj_tag(v___x_1522_) == 0)
{
lean_object* v_a_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; uint8_t v___x_1526_; 
v_a_1523_ = lean_ctor_get(v___x_1522_, 0);
lean_inc(v_a_1523_);
lean_dec_ref(v___x_1522_);
v___x_1524_ = l_Lean_Expr_cleanupAnnotations(v_a_1523_);
v___x_1525_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_go___closed__3));
v___x_1526_ = l_Lean_Expr_isConstOf(v___x_1524_, v___x_1525_);
if (v___x_1526_ == 0)
{
lean_object* v___x_1527_; uint8_t v___x_1528_; 
v___x_1527_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_go___closed__5));
v___x_1528_ = l_Lean_Expr_isConstOf(v___x_1524_, v___x_1527_);
if (v___x_1528_ == 0)
{
uint8_t v___x_1529_; 
v___x_1529_ = l_Lean_Expr_isApp(v___x_1524_);
if (v___x_1529_ == 0)
{
lean_object* v___x_1530_; 
lean_dec_ref(v___x_1524_);
v___x_1530_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goPred(v_origExpr_1509_, v_a_1510_, v_a_1511_, v_a_1512_, v_a_1513_, v_a_1514_, v_a_1515_);
return v___x_1530_;
}
else
{
lean_object* v_arg_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; uint8_t v___x_1534_; 
v_arg_1531_ = lean_ctor_get(v___x_1524_, 1);
lean_inc_ref(v_arg_1531_);
v___x_1532_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1524_);
v___x_1533_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_go___closed__6));
v___x_1534_ = l_Lean_Expr_isConstOf(v___x_1532_, v___x_1533_);
if (v___x_1534_ == 0)
{
uint8_t v___x_1535_; 
v___x_1535_ = l_Lean_Expr_isApp(v___x_1532_);
if (v___x_1535_ == 0)
{
lean_object* v___x_1536_; 
lean_dec_ref(v___x_1532_);
lean_dec_ref(v_arg_1531_);
v___x_1536_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goPred(v_origExpr_1509_, v_a_1510_, v_a_1511_, v_a_1512_, v_a_1513_, v_a_1514_, v_a_1515_);
return v___x_1536_;
}
else
{
lean_object* v_arg_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; uint8_t v___x_1540_; 
v_arg_1537_ = lean_ctor_get(v___x_1532_, 1);
lean_inc_ref(v_arg_1537_);
v___x_1538_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1532_);
v___x_1539_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_go___closed__7));
v___x_1540_ = l_Lean_Expr_isConstOf(v___x_1538_, v___x_1539_);
if (v___x_1540_ == 0)
{
lean_object* v___x_1541_; uint8_t v___x_1542_; 
v___x_1541_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_go___closed__8));
v___x_1542_ = l_Lean_Expr_isConstOf(v___x_1538_, v___x_1541_);
if (v___x_1542_ == 0)
{
uint8_t v___x_1543_; 
v___x_1543_ = l_Lean_Expr_isApp(v___x_1538_);
if (v___x_1543_ == 0)
{
lean_object* v___x_1544_; 
lean_dec_ref(v___x_1538_);
lean_dec_ref(v_arg_1537_);
lean_dec_ref(v_arg_1531_);
v___x_1544_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goPred(v_origExpr_1509_, v_a_1510_, v_a_1511_, v_a_1512_, v_a_1513_, v_a_1514_, v_a_1515_);
return v___x_1544_;
}
else
{
lean_object* v_arg_1545_; lean_object* v___x_1546_; uint8_t v___x_1547_; 
v_arg_1545_ = lean_ctor_get(v___x_1538_, 1);
lean_inc_ref(v_arg_1545_);
v___x_1546_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1538_);
v___x_1547_ = l_Lean_Expr_isApp(v___x_1546_);
if (v___x_1547_ == 0)
{
lean_object* v___x_1548_; 
lean_dec_ref(v___x_1546_);
lean_dec_ref(v_arg_1545_);
lean_dec_ref(v_arg_1537_);
lean_dec_ref(v_arg_1531_);
v___x_1548_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goPred(v_origExpr_1509_, v_a_1510_, v_a_1511_, v_a_1512_, v_a_1513_, v_a_1514_, v_a_1515_);
return v___x_1548_;
}
else
{
lean_object* v_arg_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; uint8_t v___x_1552_; 
v_arg_1549_ = lean_ctor_get(v___x_1546_, 1);
lean_inc_ref(v_arg_1549_);
v___x_1550_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1546_);
v___x_1551_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_go___closed__10));
v___x_1552_ = l_Lean_Expr_isConstOf(v___x_1550_, v___x_1551_);
if (v___x_1552_ == 0)
{
lean_object* v___x_1553_; uint8_t v___x_1554_; 
lean_dec_ref(v_arg_1545_);
v___x_1553_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_of_go___closed__7));
v___x_1554_ = l_Lean_Expr_isConstOf(v___x_1550_, v___x_1553_);
lean_dec_ref(v___x_1550_);
if (v___x_1554_ == 0)
{
lean_object* v___x_1555_; 
lean_dec_ref(v_arg_1549_);
lean_dec_ref(v_arg_1537_);
lean_dec_ref(v_arg_1531_);
v___x_1555_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goPred(v_origExpr_1509_, v_a_1510_, v_a_1511_, v_a_1512_, v_a_1513_, v_a_1514_, v_a_1515_);
return v___x_1555_;
}
else
{
lean_object* v___x_1556_; 
v___x_1556_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_arg_1549_, v_a_1513_);
if (lean_obj_tag(v___x_1556_) == 0)
{
lean_object* v_a_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; uint8_t v___x_1560_; 
v_a_1557_ = lean_ctor_get(v___x_1556_, 0);
lean_inc(v_a_1557_);
lean_dec_ref(v___x_1556_);
v___x_1558_ = l_Lean_Expr_cleanupAnnotations(v_a_1557_);
v___x_1559_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_go___closed__11));
v___x_1560_ = l_Lean_Expr_isConstOf(v___x_1558_, v___x_1559_);
if (v___x_1560_ == 0)
{
uint8_t v___x_1561_; 
lean_dec_ref(v_arg_1537_);
lean_dec_ref(v_arg_1531_);
v___x_1561_ = l_Lean_Expr_isApp(v___x_1558_);
if (v___x_1561_ == 0)
{
lean_dec_ref(v___x_1558_);
lean_dec_ref(v_origExpr_1509_);
goto v___jp_1517_;
}
else
{
lean_object* v___x_1562_; lean_object* v___x_1563_; uint8_t v___x_1564_; 
v___x_1562_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1558_);
v___x_1563_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_of_go___closed__8));
v___x_1564_ = l_Lean_Expr_isConstOf(v___x_1562_, v___x_1563_);
lean_dec_ref(v___x_1562_);
if (v___x_1564_ == 0)
{
lean_dec_ref(v_origExpr_1509_);
goto v___jp_1517_;
}
else
{
lean_object* v___x_1565_; 
v___x_1565_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goPred(v_origExpr_1509_, v_a_1510_, v_a_1511_, v_a_1512_, v_a_1513_, v_a_1514_, v_a_1515_);
return v___x_1565_;
}
}
}
else
{
uint8_t v___x_1566_; lean_object* v___x_1567_; 
lean_dec_ref(v___x_1558_);
v___x_1566_ = 2;
v___x_1567_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_gateReflection(v_arg_1537_, v_arg_1531_, v___x_1566_, v_origExpr_1509_, v_a_1510_, v_a_1511_, v_a_1512_, v_a_1513_, v_a_1514_, v_a_1515_);
return v___x_1567_;
}
}
else
{
lean_object* v_a_1568_; lean_object* v___x_1570_; uint8_t v_isShared_1571_; uint8_t v_isSharedCheck_1575_; 
lean_dec_ref(v_arg_1537_);
lean_dec_ref(v_arg_1531_);
lean_dec_ref(v_origExpr_1509_);
v_a_1568_ = lean_ctor_get(v___x_1556_, 0);
v_isSharedCheck_1575_ = !lean_is_exclusive(v___x_1556_);
if (v_isSharedCheck_1575_ == 0)
{
v___x_1570_ = v___x_1556_;
v_isShared_1571_ = v_isSharedCheck_1575_;
goto v_resetjp_1569_;
}
else
{
lean_inc(v_a_1568_);
lean_dec(v___x_1556_);
v___x_1570_ = lean_box(0);
v_isShared_1571_ = v_isSharedCheck_1575_;
goto v_resetjp_1569_;
}
v_resetjp_1569_:
{
lean_object* v___x_1573_; 
if (v_isShared_1571_ == 0)
{
v___x_1573_ = v___x_1570_;
goto v_reusejp_1572_;
}
else
{
lean_object* v_reuseFailAlloc_1574_; 
v_reuseFailAlloc_1574_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1574_, 0, v_a_1568_);
v___x_1573_ = v_reuseFailAlloc_1574_;
goto v_reusejp_1572_;
}
v_reusejp_1572_:
{
return v___x_1573_;
}
}
}
}
}
else
{
lean_object* v___x_1576_; 
lean_dec_ref(v___x_1550_);
lean_dec_ref(v_arg_1549_);
lean_inc_ref(v_arg_1545_);
v___x_1576_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom(v_arg_1545_, v_a_1510_, v_a_1511_, v_a_1512_, v_a_1513_, v_a_1514_, v_a_1515_);
if (lean_obj_tag(v___x_1576_) == 0)
{
lean_object* v_a_1577_; lean_object* v___x_1579_; uint8_t v_isShared_1580_; uint8_t v_isSharedCheck_1632_; 
v_a_1577_ = lean_ctor_get(v___x_1576_, 0);
v_isSharedCheck_1632_ = !lean_is_exclusive(v___x_1576_);
if (v_isSharedCheck_1632_ == 0)
{
v___x_1579_ = v___x_1576_;
v_isShared_1580_ = v_isSharedCheck_1632_;
goto v_resetjp_1578_;
}
else
{
lean_inc(v_a_1577_);
lean_dec(v___x_1576_);
v___x_1579_ = lean_box(0);
v_isShared_1580_ = v_isSharedCheck_1632_;
goto v_resetjp_1578_;
}
v_resetjp_1578_:
{
if (lean_obj_tag(v_a_1577_) == 1)
{
lean_object* v_val_1581_; lean_object* v___x_1582_; 
lean_del_object(v___x_1579_);
v_val_1581_ = lean_ctor_get(v_a_1577_, 0);
lean_inc(v_val_1581_);
lean_dec_ref(v_a_1577_);
lean_inc_ref(v_arg_1537_);
v___x_1582_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom(v_arg_1537_, v_a_1510_, v_a_1511_, v_a_1512_, v_a_1513_, v_a_1514_, v_a_1515_);
if (lean_obj_tag(v___x_1582_) == 0)
{
lean_object* v_a_1583_; lean_object* v___x_1585_; uint8_t v_isShared_1586_; uint8_t v_isSharedCheck_1627_; 
v_a_1583_ = lean_ctor_get(v___x_1582_, 0);
v_isSharedCheck_1627_ = !lean_is_exclusive(v___x_1582_);
if (v_isSharedCheck_1627_ == 0)
{
v___x_1585_ = v___x_1582_;
v_isShared_1586_ = v_isSharedCheck_1627_;
goto v_resetjp_1584_;
}
else
{
lean_inc(v_a_1583_);
lean_dec(v___x_1582_);
v___x_1585_ = lean_box(0);
v_isShared_1586_ = v_isSharedCheck_1627_;
goto v_resetjp_1584_;
}
v_resetjp_1584_:
{
if (lean_obj_tag(v_a_1583_) == 1)
{
lean_object* v_val_1587_; lean_object* v___x_1588_; 
lean_del_object(v___x_1585_);
v_val_1587_ = lean_ctor_get(v_a_1583_, 0);
lean_inc(v_val_1587_);
lean_dec_ref(v_a_1583_);
lean_inc_ref(v_arg_1531_);
v___x_1588_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom(v_arg_1531_, v_a_1510_, v_a_1511_, v_a_1512_, v_a_1513_, v_a_1514_, v_a_1515_);
if (lean_obj_tag(v___x_1588_) == 0)
{
lean_object* v_a_1589_; lean_object* v___x_1591_; uint8_t v_isShared_1592_; uint8_t v_isSharedCheck_1622_; 
v_a_1589_ = lean_ctor_get(v___x_1588_, 0);
v_isSharedCheck_1622_ = !lean_is_exclusive(v___x_1588_);
if (v_isSharedCheck_1622_ == 0)
{
v___x_1591_ = v___x_1588_;
v_isShared_1592_ = v_isSharedCheck_1622_;
goto v_resetjp_1590_;
}
else
{
lean_inc(v_a_1589_);
lean_dec(v___x_1588_);
v___x_1591_ = lean_box(0);
v_isShared_1592_ = v_isSharedCheck_1622_;
goto v_resetjp_1590_;
}
v_resetjp_1590_:
{
if (lean_obj_tag(v_a_1589_) == 1)
{
lean_object* v_val_1593_; lean_object* v___x_1595_; uint8_t v_isShared_1596_; uint8_t v_isSharedCheck_1617_; 
lean_del_object(v___x_1591_);
v_val_1593_ = lean_ctor_get(v_a_1589_, 0);
v_isSharedCheck_1617_ = !lean_is_exclusive(v_a_1589_);
if (v_isSharedCheck_1617_ == 0)
{
v___x_1595_ = v_a_1589_;
v_isShared_1596_ = v_isSharedCheck_1617_;
goto v_resetjp_1594_;
}
else
{
lean_inc(v_val_1593_);
lean_dec(v_a_1589_);
v___x_1595_ = lean_box(0);
v_isShared_1596_ = v_isSharedCheck_1617_;
goto v_resetjp_1594_;
}
v_resetjp_1594_:
{
lean_object* v___x_1597_; 
v___x_1597_ = l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_mkIte___redArg(v_val_1581_, v_val_1587_, v_val_1593_, v_arg_1545_, v_arg_1537_, v_arg_1531_, v_origExpr_1509_);
if (lean_obj_tag(v___x_1597_) == 0)
{
lean_object* v_a_1598_; lean_object* v___x_1600_; uint8_t v_isShared_1601_; uint8_t v_isSharedCheck_1608_; 
v_a_1598_ = lean_ctor_get(v___x_1597_, 0);
v_isSharedCheck_1608_ = !lean_is_exclusive(v___x_1597_);
if (v_isSharedCheck_1608_ == 0)
{
v___x_1600_ = v___x_1597_;
v_isShared_1601_ = v_isSharedCheck_1608_;
goto v_resetjp_1599_;
}
else
{
lean_inc(v_a_1598_);
lean_dec(v___x_1597_);
v___x_1600_ = lean_box(0);
v_isShared_1601_ = v_isSharedCheck_1608_;
goto v_resetjp_1599_;
}
v_resetjp_1599_:
{
lean_object* v___x_1603_; 
if (v_isShared_1596_ == 0)
{
lean_ctor_set(v___x_1595_, 0, v_a_1598_);
v___x_1603_ = v___x_1595_;
goto v_reusejp_1602_;
}
else
{
lean_object* v_reuseFailAlloc_1607_; 
v_reuseFailAlloc_1607_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1607_, 0, v_a_1598_);
v___x_1603_ = v_reuseFailAlloc_1607_;
goto v_reusejp_1602_;
}
v_reusejp_1602_:
{
lean_object* v___x_1605_; 
if (v_isShared_1601_ == 0)
{
lean_ctor_set(v___x_1600_, 0, v___x_1603_);
v___x_1605_ = v___x_1600_;
goto v_reusejp_1604_;
}
else
{
lean_object* v_reuseFailAlloc_1606_; 
v_reuseFailAlloc_1606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1606_, 0, v___x_1603_);
v___x_1605_ = v_reuseFailAlloc_1606_;
goto v_reusejp_1604_;
}
v_reusejp_1604_:
{
return v___x_1605_;
}
}
}
}
else
{
lean_object* v_a_1609_; lean_object* v___x_1611_; uint8_t v_isShared_1612_; uint8_t v_isSharedCheck_1616_; 
lean_del_object(v___x_1595_);
v_a_1609_ = lean_ctor_get(v___x_1597_, 0);
v_isSharedCheck_1616_ = !lean_is_exclusive(v___x_1597_);
if (v_isSharedCheck_1616_ == 0)
{
v___x_1611_ = v___x_1597_;
v_isShared_1612_ = v_isSharedCheck_1616_;
goto v_resetjp_1610_;
}
else
{
lean_inc(v_a_1609_);
lean_dec(v___x_1597_);
v___x_1611_ = lean_box(0);
v_isShared_1612_ = v_isSharedCheck_1616_;
goto v_resetjp_1610_;
}
v_resetjp_1610_:
{
lean_object* v___x_1614_; 
if (v_isShared_1612_ == 0)
{
v___x_1614_ = v___x_1611_;
goto v_reusejp_1613_;
}
else
{
lean_object* v_reuseFailAlloc_1615_; 
v_reuseFailAlloc_1615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1615_, 0, v_a_1609_);
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
}
else
{
lean_object* v___x_1618_; lean_object* v___x_1620_; 
lean_dec(v_a_1589_);
lean_dec(v_val_1587_);
lean_dec(v_val_1581_);
lean_dec_ref(v_arg_1545_);
lean_dec_ref(v_arg_1537_);
lean_dec_ref(v_arg_1531_);
lean_dec_ref(v_origExpr_1509_);
v___x_1618_ = lean_box(0);
if (v_isShared_1592_ == 0)
{
lean_ctor_set(v___x_1591_, 0, v___x_1618_);
v___x_1620_ = v___x_1591_;
goto v_reusejp_1619_;
}
else
{
lean_object* v_reuseFailAlloc_1621_; 
v_reuseFailAlloc_1621_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1621_, 0, v___x_1618_);
v___x_1620_ = v_reuseFailAlloc_1621_;
goto v_reusejp_1619_;
}
v_reusejp_1619_:
{
return v___x_1620_;
}
}
}
}
else
{
lean_dec(v_val_1587_);
lean_dec(v_val_1581_);
lean_dec_ref(v_arg_1545_);
lean_dec_ref(v_arg_1537_);
lean_dec_ref(v_arg_1531_);
lean_dec_ref(v_origExpr_1509_);
return v___x_1588_;
}
}
else
{
lean_object* v___x_1623_; lean_object* v___x_1625_; 
lean_dec(v_a_1583_);
lean_dec(v_val_1581_);
lean_dec_ref(v_arg_1545_);
lean_dec_ref(v_arg_1537_);
lean_dec_ref(v_arg_1531_);
lean_dec_ref(v_origExpr_1509_);
v___x_1623_ = lean_box(0);
if (v_isShared_1586_ == 0)
{
lean_ctor_set(v___x_1585_, 0, v___x_1623_);
v___x_1625_ = v___x_1585_;
goto v_reusejp_1624_;
}
else
{
lean_object* v_reuseFailAlloc_1626_; 
v_reuseFailAlloc_1626_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1626_, 0, v___x_1623_);
v___x_1625_ = v_reuseFailAlloc_1626_;
goto v_reusejp_1624_;
}
v_reusejp_1624_:
{
return v___x_1625_;
}
}
}
}
else
{
lean_dec(v_val_1581_);
lean_dec_ref(v_arg_1545_);
lean_dec_ref(v_arg_1537_);
lean_dec_ref(v_arg_1531_);
lean_dec_ref(v_origExpr_1509_);
return v___x_1582_;
}
}
else
{
lean_object* v___x_1628_; lean_object* v___x_1630_; 
lean_dec(v_a_1577_);
lean_dec_ref(v_arg_1545_);
lean_dec_ref(v_arg_1537_);
lean_dec_ref(v_arg_1531_);
lean_dec_ref(v_origExpr_1509_);
v___x_1628_ = lean_box(0);
if (v_isShared_1580_ == 0)
{
lean_ctor_set(v___x_1579_, 0, v___x_1628_);
v___x_1630_ = v___x_1579_;
goto v_reusejp_1629_;
}
else
{
lean_object* v_reuseFailAlloc_1631_; 
v_reuseFailAlloc_1631_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1631_, 0, v___x_1628_);
v___x_1630_ = v_reuseFailAlloc_1631_;
goto v_reusejp_1629_;
}
v_reusejp_1629_:
{
return v___x_1630_;
}
}
}
}
else
{
lean_dec_ref(v_arg_1545_);
lean_dec_ref(v_arg_1537_);
lean_dec_ref(v_arg_1531_);
lean_dec_ref(v_origExpr_1509_);
return v___x_1576_;
}
}
}
}
}
else
{
uint8_t v___x_1633_; lean_object* v___x_1634_; 
lean_dec_ref(v___x_1538_);
v___x_1633_ = 0;
v___x_1634_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_gateReflection(v_arg_1537_, v_arg_1531_, v___x_1633_, v_origExpr_1509_, v_a_1510_, v_a_1511_, v_a_1512_, v_a_1513_, v_a_1514_, v_a_1515_);
return v___x_1634_;
}
}
else
{
uint8_t v___x_1635_; lean_object* v___x_1636_; 
lean_dec_ref(v___x_1538_);
v___x_1635_ = 1;
v___x_1636_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_gateReflection(v_arg_1537_, v_arg_1531_, v___x_1635_, v_origExpr_1509_, v_a_1510_, v_a_1511_, v_a_1512_, v_a_1513_, v_a_1514_, v_a_1515_);
return v___x_1636_;
}
}
}
else
{
lean_object* v___x_1637_; 
lean_dec_ref(v___x_1532_);
lean_inc_ref(v_arg_1531_);
v___x_1637_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom(v_arg_1531_, v_a_1510_, v_a_1511_, v_a_1512_, v_a_1513_, v_a_1514_, v_a_1515_);
if (lean_obj_tag(v___x_1637_) == 0)
{
lean_object* v_a_1638_; lean_object* v___x_1640_; uint8_t v_isShared_1641_; uint8_t v_isSharedCheck_1671_; 
v_a_1638_ = lean_ctor_get(v___x_1637_, 0);
v_isSharedCheck_1671_ = !lean_is_exclusive(v___x_1637_);
if (v_isSharedCheck_1671_ == 0)
{
v___x_1640_ = v___x_1637_;
v_isShared_1641_ = v_isSharedCheck_1671_;
goto v_resetjp_1639_;
}
else
{
lean_inc(v_a_1638_);
lean_dec(v___x_1637_);
v___x_1640_ = lean_box(0);
v_isShared_1641_ = v_isSharedCheck_1671_;
goto v_resetjp_1639_;
}
v_resetjp_1639_:
{
if (lean_obj_tag(v_a_1638_) == 1)
{
lean_object* v_val_1642_; lean_object* v___x_1644_; uint8_t v_isShared_1645_; uint8_t v_isSharedCheck_1666_; 
lean_del_object(v___x_1640_);
v_val_1642_ = lean_ctor_get(v_a_1638_, 0);
v_isSharedCheck_1666_ = !lean_is_exclusive(v_a_1638_);
if (v_isSharedCheck_1666_ == 0)
{
v___x_1644_ = v_a_1638_;
v_isShared_1645_ = v_isSharedCheck_1666_;
goto v_resetjp_1643_;
}
else
{
lean_inc(v_val_1642_);
lean_dec(v_a_1638_);
v___x_1644_ = lean_box(0);
v_isShared_1645_ = v_isSharedCheck_1666_;
goto v_resetjp_1643_;
}
v_resetjp_1643_:
{
lean_object* v___x_1646_; 
v___x_1646_ = l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_mkNot___redArg(v_val_1642_, v_arg_1531_, v_origExpr_1509_);
if (lean_obj_tag(v___x_1646_) == 0)
{
lean_object* v_a_1647_; lean_object* v___x_1649_; uint8_t v_isShared_1650_; uint8_t v_isSharedCheck_1657_; 
v_a_1647_ = lean_ctor_get(v___x_1646_, 0);
v_isSharedCheck_1657_ = !lean_is_exclusive(v___x_1646_);
if (v_isSharedCheck_1657_ == 0)
{
v___x_1649_ = v___x_1646_;
v_isShared_1650_ = v_isSharedCheck_1657_;
goto v_resetjp_1648_;
}
else
{
lean_inc(v_a_1647_);
lean_dec(v___x_1646_);
v___x_1649_ = lean_box(0);
v_isShared_1650_ = v_isSharedCheck_1657_;
goto v_resetjp_1648_;
}
v_resetjp_1648_:
{
lean_object* v___x_1652_; 
if (v_isShared_1645_ == 0)
{
lean_ctor_set(v___x_1644_, 0, v_a_1647_);
v___x_1652_ = v___x_1644_;
goto v_reusejp_1651_;
}
else
{
lean_object* v_reuseFailAlloc_1656_; 
v_reuseFailAlloc_1656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1656_, 0, v_a_1647_);
v___x_1652_ = v_reuseFailAlloc_1656_;
goto v_reusejp_1651_;
}
v_reusejp_1651_:
{
lean_object* v___x_1654_; 
if (v_isShared_1650_ == 0)
{
lean_ctor_set(v___x_1649_, 0, v___x_1652_);
v___x_1654_ = v___x_1649_;
goto v_reusejp_1653_;
}
else
{
lean_object* v_reuseFailAlloc_1655_; 
v_reuseFailAlloc_1655_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1655_, 0, v___x_1652_);
v___x_1654_ = v_reuseFailAlloc_1655_;
goto v_reusejp_1653_;
}
v_reusejp_1653_:
{
return v___x_1654_;
}
}
}
}
else
{
lean_object* v_a_1658_; lean_object* v___x_1660_; uint8_t v_isShared_1661_; uint8_t v_isSharedCheck_1665_; 
lean_del_object(v___x_1644_);
v_a_1658_ = lean_ctor_get(v___x_1646_, 0);
v_isSharedCheck_1665_ = !lean_is_exclusive(v___x_1646_);
if (v_isSharedCheck_1665_ == 0)
{
v___x_1660_ = v___x_1646_;
v_isShared_1661_ = v_isSharedCheck_1665_;
goto v_resetjp_1659_;
}
else
{
lean_inc(v_a_1658_);
lean_dec(v___x_1646_);
v___x_1660_ = lean_box(0);
v_isShared_1661_ = v_isSharedCheck_1665_;
goto v_resetjp_1659_;
}
v_resetjp_1659_:
{
lean_object* v___x_1663_; 
if (v_isShared_1661_ == 0)
{
v___x_1663_ = v___x_1660_;
goto v_reusejp_1662_;
}
else
{
lean_object* v_reuseFailAlloc_1664_; 
v_reuseFailAlloc_1664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1664_, 0, v_a_1658_);
v___x_1663_ = v_reuseFailAlloc_1664_;
goto v_reusejp_1662_;
}
v_reusejp_1662_:
{
return v___x_1663_;
}
}
}
}
}
else
{
lean_object* v___x_1667_; lean_object* v___x_1669_; 
lean_dec(v_a_1638_);
lean_dec_ref(v_arg_1531_);
lean_dec_ref(v_origExpr_1509_);
v___x_1667_ = lean_box(0);
if (v_isShared_1641_ == 0)
{
lean_ctor_set(v___x_1640_, 0, v___x_1667_);
v___x_1669_ = v___x_1640_;
goto v_reusejp_1668_;
}
else
{
lean_object* v_reuseFailAlloc_1670_; 
v_reuseFailAlloc_1670_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1670_, 0, v___x_1667_);
v___x_1669_ = v_reuseFailAlloc_1670_;
goto v_reusejp_1668_;
}
v_reusejp_1668_:
{
return v___x_1669_;
}
}
}
}
else
{
lean_dec_ref(v_arg_1531_);
lean_dec_ref(v_origExpr_1509_);
return v___x_1637_;
}
}
}
}
else
{
lean_object* v___x_1672_; 
lean_dec_ref(v___x_1524_);
lean_dec_ref(v_origExpr_1509_);
v___x_1672_ = l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_mkBoolConst___redArg(v___x_1528_);
if (lean_obj_tag(v___x_1672_) == 0)
{
lean_object* v_a_1673_; lean_object* v___x_1675_; uint8_t v_isShared_1676_; uint8_t v_isSharedCheck_1681_; 
v_a_1673_ = lean_ctor_get(v___x_1672_, 0);
v_isSharedCheck_1681_ = !lean_is_exclusive(v___x_1672_);
if (v_isSharedCheck_1681_ == 0)
{
v___x_1675_ = v___x_1672_;
v_isShared_1676_ = v_isSharedCheck_1681_;
goto v_resetjp_1674_;
}
else
{
lean_inc(v_a_1673_);
lean_dec(v___x_1672_);
v___x_1675_ = lean_box(0);
v_isShared_1676_ = v_isSharedCheck_1681_;
goto v_resetjp_1674_;
}
v_resetjp_1674_:
{
lean_object* v___x_1677_; lean_object* v___x_1679_; 
v___x_1677_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1677_, 0, v_a_1673_);
if (v_isShared_1676_ == 0)
{
lean_ctor_set(v___x_1675_, 0, v___x_1677_);
v___x_1679_ = v___x_1675_;
goto v_reusejp_1678_;
}
else
{
lean_object* v_reuseFailAlloc_1680_; 
v_reuseFailAlloc_1680_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1680_, 0, v___x_1677_);
v___x_1679_ = v_reuseFailAlloc_1680_;
goto v_reusejp_1678_;
}
v_reusejp_1678_:
{
return v___x_1679_;
}
}
}
else
{
lean_object* v_a_1682_; lean_object* v___x_1684_; uint8_t v_isShared_1685_; uint8_t v_isSharedCheck_1689_; 
v_a_1682_ = lean_ctor_get(v___x_1672_, 0);
v_isSharedCheck_1689_ = !lean_is_exclusive(v___x_1672_);
if (v_isSharedCheck_1689_ == 0)
{
v___x_1684_ = v___x_1672_;
v_isShared_1685_ = v_isSharedCheck_1689_;
goto v_resetjp_1683_;
}
else
{
lean_inc(v_a_1682_);
lean_dec(v___x_1672_);
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
}
else
{
uint8_t v___x_1690_; lean_object* v___x_1691_; 
lean_dec_ref(v___x_1524_);
lean_dec_ref(v_origExpr_1509_);
v___x_1690_ = 0;
v___x_1691_ = l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_mkBoolConst___redArg(v___x_1690_);
if (lean_obj_tag(v___x_1691_) == 0)
{
lean_object* v_a_1692_; lean_object* v___x_1694_; uint8_t v_isShared_1695_; uint8_t v_isSharedCheck_1700_; 
v_a_1692_ = lean_ctor_get(v___x_1691_, 0);
v_isSharedCheck_1700_ = !lean_is_exclusive(v___x_1691_);
if (v_isSharedCheck_1700_ == 0)
{
v___x_1694_ = v___x_1691_;
v_isShared_1695_ = v_isSharedCheck_1700_;
goto v_resetjp_1693_;
}
else
{
lean_inc(v_a_1692_);
lean_dec(v___x_1691_);
v___x_1694_ = lean_box(0);
v_isShared_1695_ = v_isSharedCheck_1700_;
goto v_resetjp_1693_;
}
v_resetjp_1693_:
{
lean_object* v___x_1696_; lean_object* v___x_1698_; 
v___x_1696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1696_, 0, v_a_1692_);
if (v_isShared_1695_ == 0)
{
lean_ctor_set(v___x_1694_, 0, v___x_1696_);
v___x_1698_ = v___x_1694_;
goto v_reusejp_1697_;
}
else
{
lean_object* v_reuseFailAlloc_1699_; 
v_reuseFailAlloc_1699_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1699_, 0, v___x_1696_);
v___x_1698_ = v_reuseFailAlloc_1699_;
goto v_reusejp_1697_;
}
v_reusejp_1697_:
{
return v___x_1698_;
}
}
}
else
{
lean_object* v_a_1701_; lean_object* v___x_1703_; uint8_t v_isShared_1704_; uint8_t v_isSharedCheck_1708_; 
v_a_1701_ = lean_ctor_get(v___x_1691_, 0);
v_isSharedCheck_1708_ = !lean_is_exclusive(v___x_1691_);
if (v_isSharedCheck_1708_ == 0)
{
v___x_1703_ = v___x_1691_;
v_isShared_1704_ = v_isSharedCheck_1708_;
goto v_resetjp_1702_;
}
else
{
lean_inc(v_a_1701_);
lean_dec(v___x_1691_);
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
else
{
lean_object* v_a_1709_; lean_object* v___x_1711_; uint8_t v_isShared_1712_; uint8_t v_isSharedCheck_1716_; 
lean_dec_ref(v_origExpr_1509_);
v_a_1709_ = lean_ctor_get(v___x_1522_, 0);
v_isSharedCheck_1716_ = !lean_is_exclusive(v___x_1522_);
if (v_isSharedCheck_1716_ == 0)
{
v___x_1711_ = v___x_1522_;
v_isShared_1712_ = v_isSharedCheck_1716_;
goto v_resetjp_1710_;
}
else
{
lean_inc(v_a_1709_);
lean_dec(v___x_1522_);
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
else
{
lean_object* v_a_1717_; lean_object* v___x_1719_; uint8_t v_isShared_1720_; uint8_t v_isSharedCheck_1724_; 
lean_dec_ref(v_origExpr_1509_);
v_a_1717_ = lean_ctor_get(v___x_1521_, 0);
v_isSharedCheck_1724_ = !lean_is_exclusive(v___x_1521_);
if (v_isSharedCheck_1724_ == 0)
{
v___x_1719_ = v___x_1521_;
v_isShared_1720_ = v_isSharedCheck_1724_;
goto v_resetjp_1718_;
}
else
{
lean_inc(v_a_1717_);
lean_dec(v___x_1521_);
v___x_1719_ = lean_box(0);
v_isShared_1720_ = v_isSharedCheck_1724_;
goto v_resetjp_1718_;
}
v_resetjp_1718_:
{
lean_object* v___x_1722_; 
if (v_isShared_1720_ == 0)
{
v___x_1722_ = v___x_1719_;
goto v_reusejp_1721_;
}
else
{
lean_object* v_reuseFailAlloc_1723_; 
v_reuseFailAlloc_1723_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1723_, 0, v_a_1717_);
v___x_1722_ = v_reuseFailAlloc_1723_;
goto v_reusejp_1721_;
}
v_reusejp_1721_:
{
return v___x_1722_;
}
}
}
v___jp_1517_:
{
lean_object* v___x_1518_; lean_object* v___x_1519_; 
v___x_1518_ = lean_box(0);
v___x_1519_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1519_, 0, v___x_1518_);
return v___x_1519_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom_spec__2(lean_object* v_e_1725_, lean_object* v_a_1726_, lean_object* v_a_1727_, lean_object* v_a_1728_, lean_object* v_a_1729_, lean_object* v_a_1730_, lean_object* v_a_1731_){
_start:
{
lean_object* v___y_1734_; lean_object* v___x_1757_; lean_object* v_bvLogicalCache_1758_; lean_object* v___x_1759_; 
v___x_1757_ = lean_st_ref_get(v_a_1726_);
v_bvLogicalCache_1758_ = lean_ctor_get(v___x_1757_, 3);
lean_inc_ref(v_bvLogicalCache_1758_);
lean_dec(v___x_1757_);
v___x_1759_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom_spec__2_spec__12___redArg(v_bvLogicalCache_1758_, v_e_1725_);
lean_dec_ref(v_bvLogicalCache_1758_);
if (lean_obj_tag(v___x_1759_) == 0)
{
lean_object* v___x_1760_; 
lean_inc_ref(v_e_1725_);
v___x_1760_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_go(v_e_1725_, v_a_1726_, v_a_1727_, v_a_1728_, v_a_1729_, v_a_1730_, v_a_1731_);
if (lean_obj_tag(v___x_1760_) == 0)
{
lean_object* v_a_1761_; 
v_a_1761_ = lean_ctor_get(v___x_1760_, 0);
lean_inc(v_a_1761_);
if (lean_obj_tag(v_a_1761_) == 0)
{
lean_object* v___x_1762_; 
lean_dec_ref(v___x_1760_);
lean_inc_ref(v_e_1725_);
v___x_1762_ = l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_boolAtom(v_e_1725_, v_a_1727_, v_a_1728_, v_a_1729_, v_a_1730_, v_a_1731_);
v___y_1734_ = v___x_1762_;
goto v___jp_1733_;
}
else
{
lean_dec_ref(v_a_1761_);
v___y_1734_ = v___x_1760_;
goto v___jp_1733_;
}
}
else
{
v___y_1734_ = v___x_1760_;
goto v___jp_1733_;
}
}
else
{
lean_object* v_val_1763_; lean_object* v___x_1765_; uint8_t v_isShared_1766_; uint8_t v_isSharedCheck_1770_; 
lean_dec_ref(v_e_1725_);
v_val_1763_ = lean_ctor_get(v___x_1759_, 0);
v_isSharedCheck_1770_ = !lean_is_exclusive(v___x_1759_);
if (v_isSharedCheck_1770_ == 0)
{
v___x_1765_ = v___x_1759_;
v_isShared_1766_ = v_isSharedCheck_1770_;
goto v_resetjp_1764_;
}
else
{
lean_inc(v_val_1763_);
lean_dec(v___x_1759_);
v___x_1765_ = lean_box(0);
v_isShared_1766_ = v_isSharedCheck_1770_;
goto v_resetjp_1764_;
}
v_resetjp_1764_:
{
lean_object* v___x_1768_; 
if (v_isShared_1766_ == 0)
{
lean_ctor_set_tag(v___x_1765_, 0);
v___x_1768_ = v___x_1765_;
goto v_reusejp_1767_;
}
else
{
lean_object* v_reuseFailAlloc_1769_; 
v_reuseFailAlloc_1769_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1769_, 0, v_val_1763_);
v___x_1768_ = v_reuseFailAlloc_1769_;
goto v_reusejp_1767_;
}
v_reusejp_1767_:
{
return v___x_1768_;
}
}
}
v___jp_1733_:
{
if (lean_obj_tag(v___y_1734_) == 0)
{
lean_object* v_a_1735_; lean_object* v___x_1737_; uint8_t v_isShared_1738_; uint8_t v_isSharedCheck_1756_; 
v_a_1735_ = lean_ctor_get(v___y_1734_, 0);
v_isSharedCheck_1756_ = !lean_is_exclusive(v___y_1734_);
if (v_isSharedCheck_1756_ == 0)
{
v___x_1737_ = v___y_1734_;
v_isShared_1738_ = v_isSharedCheck_1756_;
goto v_resetjp_1736_;
}
else
{
lean_inc(v_a_1735_);
lean_dec(v___y_1734_);
v___x_1737_ = lean_box(0);
v_isShared_1738_ = v_isSharedCheck_1756_;
goto v_resetjp_1736_;
}
v_resetjp_1736_:
{
lean_object* v___x_1739_; lean_object* v_lemmas_1740_; lean_object* v_bvExprCache_1741_; lean_object* v_bvPredCache_1742_; lean_object* v_bvLogicalCache_1743_; lean_object* v___x_1745_; uint8_t v_isShared_1746_; uint8_t v_isSharedCheck_1755_; 
v___x_1739_ = lean_st_ref_take(v_a_1726_);
v_lemmas_1740_ = lean_ctor_get(v___x_1739_, 0);
v_bvExprCache_1741_ = lean_ctor_get(v___x_1739_, 1);
v_bvPredCache_1742_ = lean_ctor_get(v___x_1739_, 2);
v_bvLogicalCache_1743_ = lean_ctor_get(v___x_1739_, 3);
v_isSharedCheck_1755_ = !lean_is_exclusive(v___x_1739_);
if (v_isSharedCheck_1755_ == 0)
{
v___x_1745_ = v___x_1739_;
v_isShared_1746_ = v_isSharedCheck_1755_;
goto v_resetjp_1744_;
}
else
{
lean_inc(v_bvLogicalCache_1743_);
lean_inc(v_bvPredCache_1742_);
lean_inc(v_bvExprCache_1741_);
lean_inc(v_lemmas_1740_);
lean_dec(v___x_1739_);
v___x_1745_ = lean_box(0);
v_isShared_1746_ = v_isSharedCheck_1755_;
goto v_resetjp_1744_;
}
v_resetjp_1744_:
{
lean_object* v___x_1747_; lean_object* v___x_1749_; 
lean_inc(v_a_1735_);
v___x_1747_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13___redArg(v_bvLogicalCache_1743_, v_e_1725_, v_a_1735_);
if (v_isShared_1746_ == 0)
{
lean_ctor_set(v___x_1745_, 3, v___x_1747_);
v___x_1749_ = v___x_1745_;
goto v_reusejp_1748_;
}
else
{
lean_object* v_reuseFailAlloc_1754_; 
v_reuseFailAlloc_1754_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1754_, 0, v_lemmas_1740_);
lean_ctor_set(v_reuseFailAlloc_1754_, 1, v_bvExprCache_1741_);
lean_ctor_set(v_reuseFailAlloc_1754_, 2, v_bvPredCache_1742_);
lean_ctor_set(v_reuseFailAlloc_1754_, 3, v___x_1747_);
v___x_1749_ = v_reuseFailAlloc_1754_;
goto v_reusejp_1748_;
}
v_reusejp_1748_:
{
lean_object* v___x_1750_; lean_object* v___x_1752_; 
v___x_1750_ = lean_st_ref_set(v_a_1726_, v___x_1749_);
if (v_isShared_1738_ == 0)
{
v___x_1752_ = v___x_1737_;
goto v_reusejp_1751_;
}
else
{
lean_object* v_reuseFailAlloc_1753_; 
v_reuseFailAlloc_1753_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1753_, 0, v_a_1735_);
v___x_1752_ = v_reuseFailAlloc_1753_;
goto v_reusejp_1751_;
}
v_reusejp_1751_:
{
return v___x_1752_;
}
}
}
}
}
else
{
lean_dec_ref(v_e_1725_);
return v___y_1734_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom(lean_object* v_origExpr_1771_, lean_object* v_a_1772_, lean_object* v_a_1773_, lean_object* v_a_1774_, lean_object* v_a_1775_, lean_object* v_a_1776_, lean_object* v_a_1777_){
_start:
{
lean_object* v___x_1779_; 
v___x_1779_ = l_Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom_spec__2(v_origExpr_1771_, v_a_1772_, v_a_1773_, v_a_1774_, v_a_1775_, v_a_1776_, v_a_1777_);
return v___x_1779_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of(lean_object* v_origExpr_1780_, lean_object* v_a_1781_, lean_object* v_a_1782_, lean_object* v_a_1783_, lean_object* v_a_1784_, lean_object* v_a_1785_, lean_object* v_a_1786_){
_start:
{
lean_object* v___x_1788_; 
v___x_1788_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom(v_origExpr_1780_, v_a_1781_, v_a_1782_, v_a_1783_, v_a_1784_, v_a_1785_, v_a_1786_);
return v___x_1788_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__6(void){
_start:
{
lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; 
v___x_1804_ = lean_box(0);
v___x_1805_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__5));
v___x_1806_ = l_Lean_mkConst(v___x_1805_, v___x_1804_);
return v___x_1806_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__3(void){
_start:
{
lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; 
v___x_1814_ = lean_box(0);
v___x_1815_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__2));
v___x_1816_ = l_Lean_mkConst(v___x_1815_, v___x_1814_);
return v___x_1816_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__6(void){
_start:
{
lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; 
v___x_1823_ = lean_box(0);
v___x_1824_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__5));
v___x_1825_ = l_Lean_mkConst(v___x_1824_, v___x_1823_);
return v___x_1825_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__9(void){
_start:
{
lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; 
v___x_1832_ = lean_box(0);
v___x_1833_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__8));
v___x_1834_ = l_Lean_mkConst(v___x_1833_, v___x_1832_);
return v___x_1834_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__12(void){
_start:
{
lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; 
v___x_1842_ = lean_box(0);
v___x_1843_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__11));
v___x_1844_ = l_Lean_mkConst(v___x_1843_, v___x_1842_);
return v___x_1844_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__15(void){
_start:
{
lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; 
v___x_1851_ = lean_box(0);
v___x_1852_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__14));
v___x_1853_ = l_Lean_mkConst(v___x_1852_, v___x_1851_);
return v___x_1853_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__18(void){
_start:
{
lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; 
v___x_1860_ = lean_box(0);
v___x_1861_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__17));
v___x_1862_ = l_Lean_mkConst(v___x_1861_, v___x_1860_);
return v___x_1862_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__21(void){
_start:
{
lean_object* v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; 
v___x_1869_ = lean_box(0);
v___x_1870_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__20));
v___x_1871_ = l_Lean_mkConst(v___x_1870_, v___x_1869_);
return v___x_1871_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection(lean_object* v_innerExpr_1872_, lean_object* v_op_1873_, lean_object* v_congrThm_1874_, lean_object* v_origExpr_1875_, lean_object* v_a_1876_, lean_object* v_a_1877_, lean_object* v_a_1878_, lean_object* v_a_1879_, lean_object* v_a_1880_, lean_object* v_a_1881_){
_start:
{
lean_object* v___x_1883_; 
lean_inc_ref(v_innerExpr_1872_);
v___x_1883_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_goOrAtom(v_innerExpr_1872_, v_a_1876_, v_a_1877_, v_a_1878_, v_a_1879_, v_a_1880_, v_a_1881_);
if (lean_obj_tag(v___x_1883_) == 0)
{
lean_object* v_a_1884_; lean_object* v___x_1886_; uint8_t v_isShared_1887_; uint8_t v_isSharedCheck_1932_; 
v_a_1884_ = lean_ctor_get(v___x_1883_, 0);
v_isSharedCheck_1932_ = !lean_is_exclusive(v___x_1883_);
if (v_isSharedCheck_1932_ == 0)
{
v___x_1886_ = v___x_1883_;
v_isShared_1887_ = v_isSharedCheck_1932_;
goto v_resetjp_1885_;
}
else
{
lean_inc(v_a_1884_);
lean_dec(v___x_1883_);
v___x_1886_ = lean_box(0);
v_isShared_1887_ = v_isSharedCheck_1932_;
goto v_resetjp_1885_;
}
v_resetjp_1885_:
{
if (lean_obj_tag(v_a_1884_) == 1)
{
lean_object* v_val_1888_; lean_object* v___x_1890_; uint8_t v_isShared_1891_; uint8_t v_isSharedCheck_1927_; 
v_val_1888_ = lean_ctor_get(v_a_1884_, 0);
v_isSharedCheck_1927_ = !lean_is_exclusive(v_a_1884_);
if (v_isSharedCheck_1927_ == 0)
{
v___x_1890_ = v_a_1884_;
v_isShared_1891_ = v_isSharedCheck_1927_;
goto v_resetjp_1889_;
}
else
{
lean_inc(v_val_1888_);
lean_dec(v_a_1884_);
v___x_1890_ = lean_box(0);
v_isShared_1891_ = v_isSharedCheck_1927_;
goto v_resetjp_1889_;
}
v_resetjp_1889_:
{
lean_object* v_width_1892_; lean_object* v_bvExpr_1893_; lean_object* v_expr_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; lean_object* v___y_1900_; 
v_width_1892_ = lean_ctor_get(v_val_1888_, 0);
lean_inc_n(v_width_1892_, 3);
v_bvExpr_1893_ = lean_ctor_get(v_val_1888_, 1);
v_expr_1894_ = lean_ctor_get(v_val_1888_, 4);
lean_inc_ref(v_bvExpr_1893_);
lean_inc(v_op_1873_);
v___x_1895_ = l_Std_Tactic_BVDecide_BVExpr_un___override(v_width_1892_, v_op_1873_, v_bvExpr_1893_);
v___x_1896_ = lean_box(0);
v___x_1897_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__6, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__6_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__6);
v___x_1898_ = l_Lean_mkNatLit(v_width_1892_);
switch(lean_obj_tag(v_op_1873_))
{
case 0:
{
lean_object* v___x_1911_; 
v___x_1911_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__3, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__3_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__3);
v___y_1900_ = v___x_1911_;
goto v___jp_1899_;
}
case 1:
{
lean_object* v_n_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; 
v_n_1912_ = lean_ctor_get(v_op_1873_, 0);
lean_inc(v_n_1912_);
lean_dec_ref(v_op_1873_);
v___x_1913_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__6, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__6_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__6);
v___x_1914_ = l_Lean_mkNatLit(v_n_1912_);
v___x_1915_ = l_Lean_Expr_app___override(v___x_1913_, v___x_1914_);
v___y_1900_ = v___x_1915_;
goto v___jp_1899_;
}
case 2:
{
lean_object* v_n_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; 
v_n_1916_ = lean_ctor_get(v_op_1873_, 0);
lean_inc(v_n_1916_);
lean_dec_ref(v_op_1873_);
v___x_1917_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__9, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__9_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__9);
v___x_1918_ = l_Lean_mkNatLit(v_n_1916_);
v___x_1919_ = l_Lean_Expr_app___override(v___x_1917_, v___x_1918_);
v___y_1900_ = v___x_1919_;
goto v___jp_1899_;
}
case 3:
{
lean_object* v_n_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; 
v_n_1920_ = lean_ctor_get(v_op_1873_, 0);
lean_inc(v_n_1920_);
lean_dec_ref(v_op_1873_);
v___x_1921_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__12, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__12_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__12);
v___x_1922_ = l_Lean_mkNatLit(v_n_1920_);
v___x_1923_ = l_Lean_Expr_app___override(v___x_1921_, v___x_1922_);
v___y_1900_ = v___x_1923_;
goto v___jp_1899_;
}
case 4:
{
lean_object* v___x_1924_; 
v___x_1924_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__15, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__15_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__15);
v___y_1900_ = v___x_1924_;
goto v___jp_1899_;
}
case 5:
{
lean_object* v___x_1925_; 
v___x_1925_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__18, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__18_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__18);
v___y_1900_ = v___x_1925_;
goto v___jp_1899_;
}
default: 
{
lean_object* v___x_1926_; 
v___x_1926_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__21, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__21_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__21);
v___y_1900_ = v___x_1926_;
goto v___jp_1899_;
}
}
v___jp_1899_:
{
lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1906_; 
lean_inc_ref(v_expr_1894_);
v___x_1901_ = l_Lean_mkApp3(v___x_1897_, v___x_1898_, v___y_1900_, v_expr_1894_);
v___x_1902_ = l_Lean_mkConst(v_congrThm_1874_, v___x_1896_);
v___x_1903_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryCongrProof___boxed), 9, 3);
lean_closure_set(v___x_1903_, 0, v_val_1888_);
lean_closure_set(v___x_1903_, 1, v_innerExpr_1872_);
lean_closure_set(v___x_1903_, 2, v___x_1902_);
v___x_1904_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1904_, 0, v_width_1892_);
lean_ctor_set(v___x_1904_, 1, v___x_1895_);
lean_ctor_set(v___x_1904_, 2, v_origExpr_1875_);
lean_ctor_set(v___x_1904_, 3, v___x_1903_);
lean_ctor_set(v___x_1904_, 4, v___x_1901_);
if (v_isShared_1891_ == 0)
{
lean_ctor_set(v___x_1890_, 0, v___x_1904_);
v___x_1906_ = v___x_1890_;
goto v_reusejp_1905_;
}
else
{
lean_object* v_reuseFailAlloc_1910_; 
v_reuseFailAlloc_1910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1910_, 0, v___x_1904_);
v___x_1906_ = v_reuseFailAlloc_1910_;
goto v_reusejp_1905_;
}
v_reusejp_1905_:
{
lean_object* v___x_1908_; 
if (v_isShared_1887_ == 0)
{
lean_ctor_set(v___x_1886_, 0, v___x_1906_);
v___x_1908_ = v___x_1886_;
goto v_reusejp_1907_;
}
else
{
lean_object* v_reuseFailAlloc_1909_; 
v_reuseFailAlloc_1909_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1909_, 0, v___x_1906_);
v___x_1908_ = v_reuseFailAlloc_1909_;
goto v_reusejp_1907_;
}
v_reusejp_1907_:
{
return v___x_1908_;
}
}
}
}
}
else
{
lean_object* v___x_1928_; lean_object* v___x_1930_; 
lean_dec(v_a_1884_);
lean_dec_ref(v_origExpr_1875_);
lean_dec(v_congrThm_1874_);
lean_dec(v_op_1873_);
lean_dec_ref(v_innerExpr_1872_);
v___x_1928_ = lean_box(0);
if (v_isShared_1887_ == 0)
{
lean_ctor_set(v___x_1886_, 0, v___x_1928_);
v___x_1930_ = v___x_1886_;
goto v_reusejp_1929_;
}
else
{
lean_object* v_reuseFailAlloc_1931_; 
v_reuseFailAlloc_1931_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1931_, 0, v___x_1928_);
v___x_1930_ = v_reuseFailAlloc_1931_;
goto v_reusejp_1929_;
}
v_reusejp_1929_:
{
return v___x_1930_;
}
}
}
}
else
{
lean_dec_ref(v_origExpr_1875_);
lean_dec(v_congrThm_1874_);
lean_dec(v_op_1873_);
lean_dec_ref(v_innerExpr_1872_);
return v___x_1883_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection(lean_object* v_distance_1942_, lean_object* v_innerExpr_1943_, lean_object* v_shiftOp_1944_, lean_object* v_shiftOpName_1945_, lean_object* v_congrThm_1946_, lean_object* v_origExpr_1947_, lean_object* v_a_1948_, lean_object* v_a_1949_, lean_object* v_a_1950_, lean_object* v_a_1951_, lean_object* v_a_1952_, lean_object* v_a_1953_){
_start:
{
lean_object* v___x_1955_; 
lean_inc_ref(v_innerExpr_1943_);
v___x_1955_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_goOrAtom(v_innerExpr_1943_, v_a_1948_, v_a_1949_, v_a_1950_, v_a_1951_, v_a_1952_, v_a_1953_);
if (lean_obj_tag(v___x_1955_) == 0)
{
lean_object* v_a_1956_; lean_object* v___x_1958_; uint8_t v_isShared_1959_; uint8_t v_isSharedCheck_1991_; 
v_a_1956_ = lean_ctor_get(v___x_1955_, 0);
v_isSharedCheck_1991_ = !lean_is_exclusive(v___x_1955_);
if (v_isSharedCheck_1991_ == 0)
{
v___x_1958_ = v___x_1955_;
v_isShared_1959_ = v_isSharedCheck_1991_;
goto v_resetjp_1957_;
}
else
{
lean_inc(v_a_1956_);
lean_dec(v___x_1955_);
v___x_1958_ = lean_box(0);
v_isShared_1959_ = v_isSharedCheck_1991_;
goto v_resetjp_1957_;
}
v_resetjp_1957_:
{
if (lean_obj_tag(v_a_1956_) == 1)
{
lean_object* v_val_1960_; lean_object* v___x_1962_; uint8_t v_isShared_1963_; uint8_t v_isSharedCheck_1986_; 
v_val_1960_ = lean_ctor_get(v_a_1956_, 0);
v_isSharedCheck_1986_ = !lean_is_exclusive(v_a_1956_);
if (v_isSharedCheck_1986_ == 0)
{
v___x_1962_ = v_a_1956_;
v_isShared_1963_ = v_isSharedCheck_1986_;
goto v_resetjp_1961_;
}
else
{
lean_inc(v_val_1960_);
lean_dec(v_a_1956_);
v___x_1962_ = lean_box(0);
v_isShared_1963_ = v_isSharedCheck_1986_;
goto v_resetjp_1961_;
}
v_resetjp_1961_:
{
lean_object* v_width_1964_; lean_object* v_bvExpr_1965_; lean_object* v_expr_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; lean_object* v___x_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; lean_object* v___x_1979_; lean_object* v___x_1981_; 
v_width_1964_ = lean_ctor_get(v_val_1960_, 0);
lean_inc_n(v_width_1964_, 3);
v_bvExpr_1965_ = lean_ctor_get(v_val_1960_, 1);
v_expr_1966_ = lean_ctor_get(v_val_1960_, 4);
lean_inc(v_distance_1942_);
v___x_1967_ = lean_apply_1(v_shiftOp_1944_, v_distance_1942_);
lean_inc_ref(v_bvExpr_1965_);
v___x_1968_ = l_Std_Tactic_BVDecide_BVExpr_un___override(v_width_1964_, v___x_1967_, v_bvExpr_1965_);
v___x_1969_ = lean_box(0);
v___x_1970_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__6, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__6_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__6);
v___x_1971_ = l_Lean_mkNatLit(v_width_1964_);
v___x_1972_ = l_Lean_mkConst(v_shiftOpName_1945_, v___x_1969_);
v___x_1973_ = l_Lean_mkNatLit(v_distance_1942_);
lean_inc_ref(v___x_1973_);
v___x_1974_ = l_Lean_Expr_app___override(v___x_1972_, v___x_1973_);
lean_inc_ref(v_expr_1966_);
v___x_1975_ = l_Lean_mkApp3(v___x_1970_, v___x_1971_, v___x_1974_, v_expr_1966_);
v___x_1976_ = l_Lean_mkConst(v_congrThm_1946_, v___x_1969_);
v___x_1977_ = l_Lean_Expr_app___override(v___x_1976_, v___x_1973_);
v___x_1978_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryCongrProof___boxed), 9, 3);
lean_closure_set(v___x_1978_, 0, v_val_1960_);
lean_closure_set(v___x_1978_, 1, v_innerExpr_1943_);
lean_closure_set(v___x_1978_, 2, v___x_1977_);
v___x_1979_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1979_, 0, v_width_1964_);
lean_ctor_set(v___x_1979_, 1, v___x_1968_);
lean_ctor_set(v___x_1979_, 2, v_origExpr_1947_);
lean_ctor_set(v___x_1979_, 3, v___x_1978_);
lean_ctor_set(v___x_1979_, 4, v___x_1975_);
if (v_isShared_1963_ == 0)
{
lean_ctor_set(v___x_1962_, 0, v___x_1979_);
v___x_1981_ = v___x_1962_;
goto v_reusejp_1980_;
}
else
{
lean_object* v_reuseFailAlloc_1985_; 
v_reuseFailAlloc_1985_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1985_, 0, v___x_1979_);
v___x_1981_ = v_reuseFailAlloc_1985_;
goto v_reusejp_1980_;
}
v_reusejp_1980_:
{
lean_object* v___x_1983_; 
if (v_isShared_1959_ == 0)
{
lean_ctor_set(v___x_1958_, 0, v___x_1981_);
v___x_1983_ = v___x_1958_;
goto v_reusejp_1982_;
}
else
{
lean_object* v_reuseFailAlloc_1984_; 
v_reuseFailAlloc_1984_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1984_, 0, v___x_1981_);
v___x_1983_ = v_reuseFailAlloc_1984_;
goto v_reusejp_1982_;
}
v_reusejp_1982_:
{
return v___x_1983_;
}
}
}
}
else
{
lean_object* v___x_1987_; lean_object* v___x_1989_; 
lean_dec(v_a_1956_);
lean_dec_ref(v_origExpr_1947_);
lean_dec(v_congrThm_1946_);
lean_dec(v_shiftOpName_1945_);
lean_dec_ref(v_shiftOp_1944_);
lean_dec_ref(v_innerExpr_1943_);
lean_dec(v_distance_1942_);
v___x_1987_ = lean_box(0);
if (v_isShared_1959_ == 0)
{
lean_ctor_set(v___x_1958_, 0, v___x_1987_);
v___x_1989_ = v___x_1958_;
goto v_reusejp_1988_;
}
else
{
lean_object* v_reuseFailAlloc_1990_; 
v_reuseFailAlloc_1990_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1990_, 0, v___x_1987_);
v___x_1989_ = v_reuseFailAlloc_1990_;
goto v_reusejp_1988_;
}
v_reusejp_1988_:
{
return v___x_1989_;
}
}
}
}
else
{
lean_dec_ref(v_origExpr_1947_);
lean_dec(v_congrThm_1946_);
lean_dec(v_shiftOpName_1945_);
lean_dec_ref(v_shiftOp_1944_);
lean_dec_ref(v_innerExpr_1943_);
lean_dec(v_distance_1942_);
return v___x_1955_;
}
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__86(void){
_start:
{
lean_object* v___x_1998_; lean_object* v___x_1999_; lean_object* v___x_2000_; 
v___x_1998_ = lean_box(0);
v___x_1999_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__85));
v___x_2000_ = l_Lean_mkConst(v___x_1999_, v___x_1998_);
return v___x_2000_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_rotateReflection(lean_object* v_distanceExpr_2010_, lean_object* v_innerExpr_2011_, lean_object* v_rotateOp_2012_, lean_object* v_rotateOpName_2013_, lean_object* v_congrThm_2014_, lean_object* v_origExpr_2015_, lean_object* v_a_2016_, lean_object* v_a_2017_, lean_object* v_a_2018_, lean_object* v_a_2019_, lean_object* v_a_2020_, lean_object* v_a_2021_){
_start:
{
lean_object* v___x_2023_; 
v___x_2023_ = l_Lean_Meta_getNatValue_x3f(v_distanceExpr_2010_, v_a_2018_, v_a_2019_, v_a_2020_, v_a_2021_);
if (lean_obj_tag(v___x_2023_) == 0)
{
lean_object* v_a_2024_; lean_object* v___x_2026_; uint8_t v_isShared_2027_; uint8_t v_isSharedCheck_2034_; 
v_a_2024_ = lean_ctor_get(v___x_2023_, 0);
v_isSharedCheck_2034_ = !lean_is_exclusive(v___x_2023_);
if (v_isSharedCheck_2034_ == 0)
{
v___x_2026_ = v___x_2023_;
v_isShared_2027_ = v_isSharedCheck_2034_;
goto v_resetjp_2025_;
}
else
{
lean_inc(v_a_2024_);
lean_dec(v___x_2023_);
v___x_2026_ = lean_box(0);
v_isShared_2027_ = v_isSharedCheck_2034_;
goto v_resetjp_2025_;
}
v_resetjp_2025_:
{
if (lean_obj_tag(v_a_2024_) == 1)
{
lean_object* v_val_2028_; lean_object* v___x_2029_; 
lean_del_object(v___x_2026_);
v_val_2028_ = lean_ctor_get(v_a_2024_, 0);
lean_inc(v_val_2028_);
lean_dec_ref(v_a_2024_);
v___x_2029_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection(v_val_2028_, v_innerExpr_2011_, v_rotateOp_2012_, v_rotateOpName_2013_, v_congrThm_2014_, v_origExpr_2015_, v_a_2016_, v_a_2017_, v_a_2018_, v_a_2019_, v_a_2020_, v_a_2021_);
return v___x_2029_;
}
else
{
lean_object* v___x_2030_; lean_object* v___x_2032_; 
lean_dec(v_a_2024_);
lean_dec_ref(v_origExpr_2015_);
lean_dec(v_congrThm_2014_);
lean_dec(v_rotateOpName_2013_);
lean_dec_ref(v_rotateOp_2012_);
lean_dec_ref(v_innerExpr_2011_);
v___x_2030_ = lean_box(0);
if (v_isShared_2027_ == 0)
{
lean_ctor_set(v___x_2026_, 0, v___x_2030_);
v___x_2032_ = v___x_2026_;
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
}
}
else
{
lean_object* v_a_2035_; lean_object* v___x_2037_; uint8_t v_isShared_2038_; uint8_t v_isSharedCheck_2042_; 
lean_dec_ref(v_origExpr_2015_);
lean_dec(v_congrThm_2014_);
lean_dec(v_rotateOpName_2013_);
lean_dec_ref(v_rotateOp_2012_);
lean_dec_ref(v_innerExpr_2011_);
v_a_2035_ = lean_ctor_get(v___x_2023_, 0);
v_isSharedCheck_2042_ = !lean_is_exclusive(v___x_2023_);
if (v_isSharedCheck_2042_ == 0)
{
v___x_2037_ = v___x_2023_;
v_isShared_2038_ = v_isSharedCheck_2042_;
goto v_resetjp_2036_;
}
else
{
lean_inc(v_a_2035_);
lean_dec(v___x_2023_);
v___x_2037_ = lean_box(0);
v_isShared_2038_ = v_isSharedCheck_2042_;
goto v_resetjp_2036_;
}
v_resetjp_2036_:
{
lean_object* v___x_2040_; 
if (v_isShared_2038_ == 0)
{
v___x_2040_ = v___x_2037_;
goto v_reusejp_2039_;
}
else
{
lean_object* v_reuseFailAlloc_2041_; 
v_reuseFailAlloc_2041_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2041_, 0, v_a_2035_);
v___x_2040_ = v_reuseFailAlloc_2041_;
goto v_reusejp_2039_;
}
v_reusejp_2039_:
{
return v___x_2040_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go(lean_object* v_origExpr_2076_, lean_object* v_a_2077_, lean_object* v_a_2078_, lean_object* v_a_2079_, lean_object* v_a_2080_, lean_object* v_a_2081_, lean_object* v_a_2082_){
_start:
{
lean_object* v___x_2090_; lean_object* v___x_2091_; 
v___x_2090_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_go___closed__0));
v___x_2091_ = l_Lean_Core_checkSystem(v___x_2090_, v_a_2081_, v_a_2082_);
if (lean_obj_tag(v___x_2091_) == 0)
{
lean_object* v___x_2092_; 
lean_dec_ref(v___x_2091_);
lean_inc_ref(v_origExpr_2076_);
v___x_2092_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_origExpr_2076_, v_a_2080_);
if (lean_obj_tag(v___x_2092_) == 0)
{
lean_object* v_a_2093_; lean_object* v___x_2095_; uint8_t v_isShared_2096_; uint8_t v_isSharedCheck_2631_; 
v_a_2093_ = lean_ctor_get(v___x_2092_, 0);
v_isSharedCheck_2631_ = !lean_is_exclusive(v___x_2092_);
if (v_isSharedCheck_2631_ == 0)
{
v___x_2095_ = v___x_2092_;
v_isShared_2096_ = v_isSharedCheck_2631_;
goto v_resetjp_2094_;
}
else
{
lean_inc(v_a_2093_);
lean_dec(v___x_2092_);
v___x_2095_ = lean_box(0);
v_isShared_2096_ = v_isSharedCheck_2631_;
goto v_resetjp_2094_;
}
v_resetjp_2094_:
{
lean_object* v___x_2102_; uint8_t v___x_2103_; 
v___x_2102_ = l_Lean_Expr_cleanupAnnotations(v_a_2093_);
v___x_2103_ = l_Lean_Expr_isApp(v___x_2102_);
if (v___x_2103_ == 0)
{
lean_dec_ref(v___x_2102_);
lean_dec_ref(v_origExpr_2076_);
goto v___jp_2097_;
}
else
{
lean_object* v_arg_2104_; lean_object* v___x_2105_; uint8_t v___x_2106_; 
v_arg_2104_ = lean_ctor_get(v___x_2102_, 1);
lean_inc_ref(v_arg_2104_);
v___x_2105_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2102_);
v___x_2106_ = l_Lean_Expr_isApp(v___x_2105_);
if (v___x_2106_ == 0)
{
lean_dec_ref(v___x_2105_);
lean_dec_ref(v_arg_2104_);
lean_dec_ref(v_origExpr_2076_);
goto v___jp_2097_;
}
else
{
lean_object* v_arg_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; uint8_t v___x_2111_; 
v_arg_2107_ = lean_ctor_get(v___x_2105_, 1);
lean_inc_ref(v_arg_2107_);
v___x_2108_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2105_);
v___x_2109_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_of_go___closed__0));
v___x_2110_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__0));
v___x_2111_ = l_Lean_Expr_isConstOf(v___x_2108_, v___x_2110_);
if (v___x_2111_ == 0)
{
lean_object* v___x_2112_; uint8_t v___x_2113_; 
v___x_2112_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__1));
v___x_2113_ = l_Lean_Expr_isConstOf(v___x_2108_, v___x_2112_);
if (v___x_2113_ == 0)
{
lean_object* v___x_2114_; uint8_t v___x_2115_; 
v___x_2114_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__2));
v___x_2115_ = l_Lean_Expr_isConstOf(v___x_2108_, v___x_2114_);
if (v___x_2115_ == 0)
{
lean_object* v___x_2116_; uint8_t v___x_2117_; 
v___x_2116_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__4));
v___x_2117_ = l_Lean_Expr_isConstOf(v___x_2108_, v___x_2116_);
if (v___x_2117_ == 0)
{
uint8_t v___x_2118_; 
v___x_2118_ = l_Lean_Expr_isApp(v___x_2108_);
if (v___x_2118_ == 0)
{
lean_dec_ref(v___x_2108_);
lean_dec_ref(v_arg_2107_);
lean_dec_ref(v_arg_2104_);
lean_dec_ref(v_origExpr_2076_);
goto v___jp_2097_;
}
else
{
lean_object* v_arg_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; uint8_t v___x_2122_; 
v_arg_2119_ = lean_ctor_get(v___x_2108_, 1);
lean_inc_ref(v_arg_2119_);
v___x_2120_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2108_);
v___x_2121_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__5));
v___x_2122_ = l_Lean_Expr_isConstOf(v___x_2120_, v___x_2121_);
if (v___x_2122_ == 0)
{
lean_object* v___x_2123_; uint8_t v___x_2124_; 
v___x_2123_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__6));
v___x_2124_ = l_Lean_Expr_isConstOf(v___x_2120_, v___x_2123_);
if (v___x_2124_ == 0)
{
lean_object* v___x_2125_; uint8_t v___x_2126_; 
v___x_2125_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__8));
v___x_2126_ = l_Lean_Expr_isConstOf(v___x_2120_, v___x_2125_);
if (v___x_2126_ == 0)
{
lean_object* v___x_2127_; uint8_t v___x_2128_; 
v___x_2127_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__10));
v___x_2128_ = l_Lean_Expr_isConstOf(v___x_2120_, v___x_2127_);
if (v___x_2128_ == 0)
{
lean_object* v___x_2129_; uint8_t v___x_2130_; 
v___x_2129_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__13));
v___x_2130_ = l_Lean_Expr_isConstOf(v___x_2120_, v___x_2129_);
if (v___x_2130_ == 0)
{
uint8_t v___x_2131_; 
v___x_2131_ = l_Lean_Expr_isApp(v___x_2120_);
if (v___x_2131_ == 0)
{
lean_dec_ref(v___x_2120_);
lean_dec_ref(v_arg_2119_);
lean_dec_ref(v_arg_2107_);
lean_dec_ref(v_arg_2104_);
lean_dec_ref(v_origExpr_2076_);
goto v___jp_2097_;
}
else
{
lean_object* v___x_2132_; lean_object* v___x_2133_; uint8_t v___x_2134_; 
v___x_2132_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2120_);
v___x_2133_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_go___closed__10));
v___x_2134_ = l_Lean_Expr_isConstOf(v___x_2132_, v___x_2133_);
if (v___x_2134_ == 0)
{
lean_object* v___x_2135_; uint8_t v___x_2136_; 
v___x_2135_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__15));
v___x_2136_ = l_Lean_Expr_isConstOf(v___x_2132_, v___x_2135_);
if (v___x_2136_ == 0)
{
lean_object* v___x_2137_; uint8_t v___x_2138_; 
lean_dec_ref(v_arg_2119_);
v___x_2137_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__17));
v___x_2138_ = l_Lean_Expr_isConstOf(v___x_2132_, v___x_2137_);
if (v___x_2138_ == 0)
{
uint8_t v___x_2139_; 
v___x_2139_ = l_Lean_Expr_isApp(v___x_2132_);
if (v___x_2139_ == 0)
{
lean_dec_ref(v___x_2132_);
lean_dec_ref(v_arg_2107_);
lean_dec_ref(v_arg_2104_);
lean_dec_ref(v_origExpr_2076_);
goto v___jp_2097_;
}
else
{
lean_object* v_arg_2140_; lean_object* v___x_2141_; uint8_t v___x_2142_; 
v_arg_2140_ = lean_ctor_get(v___x_2132_, 1);
lean_inc_ref(v_arg_2140_);
v___x_2141_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2132_);
v___x_2142_ = l_Lean_Expr_isApp(v___x_2141_);
if (v___x_2142_ == 0)
{
lean_dec_ref(v___x_2141_);
lean_dec_ref(v_arg_2140_);
lean_dec_ref(v_arg_2107_);
lean_dec_ref(v_arg_2104_);
lean_dec_ref(v_origExpr_2076_);
goto v___jp_2097_;
}
else
{
lean_object* v_arg_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; uint8_t v___x_2146_; 
v_arg_2143_ = lean_ctor_get(v___x_2141_, 1);
lean_inc_ref(v_arg_2143_);
v___x_2144_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2141_);
v___x_2145_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__20));
v___x_2146_ = l_Lean_Expr_isConstOf(v___x_2144_, v___x_2145_);
if (v___x_2146_ == 0)
{
lean_object* v___x_2147_; uint8_t v___x_2148_; 
v___x_2147_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__23));
v___x_2148_ = l_Lean_Expr_isConstOf(v___x_2144_, v___x_2147_);
if (v___x_2148_ == 0)
{
lean_object* v___x_2149_; uint8_t v___x_2150_; 
v___x_2149_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__26));
v___x_2150_ = l_Lean_Expr_isConstOf(v___x_2144_, v___x_2149_);
if (v___x_2150_ == 0)
{
lean_object* v___x_2151_; uint8_t v___x_2152_; 
lean_dec_ref(v_arg_2143_);
lean_dec_ref(v_arg_2140_);
v___x_2151_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__29));
v___x_2152_ = l_Lean_Expr_isConstOf(v___x_2144_, v___x_2151_);
if (v___x_2152_ == 0)
{
lean_object* v___x_2153_; uint8_t v___x_2154_; 
v___x_2153_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__32));
v___x_2154_ = l_Lean_Expr_isConstOf(v___x_2144_, v___x_2153_);
if (v___x_2154_ == 0)
{
lean_object* v___x_2155_; uint8_t v___x_2156_; 
v___x_2155_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__35));
v___x_2156_ = l_Lean_Expr_isConstOf(v___x_2144_, v___x_2155_);
if (v___x_2156_ == 0)
{
lean_object* v___x_2157_; uint8_t v___x_2158_; 
v___x_2157_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__38));
v___x_2158_ = l_Lean_Expr_isConstOf(v___x_2144_, v___x_2157_);
if (v___x_2158_ == 0)
{
lean_object* v___x_2159_; uint8_t v___x_2160_; 
v___x_2159_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__41));
v___x_2160_ = l_Lean_Expr_isConstOf(v___x_2144_, v___x_2159_);
if (v___x_2160_ == 0)
{
lean_object* v___x_2161_; uint8_t v___x_2162_; 
v___x_2161_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__44));
v___x_2162_ = l_Lean_Expr_isConstOf(v___x_2144_, v___x_2161_);
lean_dec_ref(v___x_2144_);
if (v___x_2162_ == 0)
{
lean_dec_ref(v_arg_2107_);
lean_dec_ref(v_arg_2104_);
lean_dec_ref(v_origExpr_2076_);
goto v___jp_2097_;
}
else
{
uint8_t v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; 
lean_del_object(v___x_2095_);
v___x_2163_ = 0;
v___x_2164_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__46));
v___x_2165_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection(v_arg_2107_, v_arg_2104_, v___x_2163_, v___x_2164_, v_origExpr_2076_, v_a_2077_, v_a_2078_, v_a_2079_, v_a_2080_, v_a_2081_, v_a_2082_);
return v___x_2165_;
}
}
else
{
uint8_t v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; 
lean_dec_ref(v___x_2144_);
lean_del_object(v___x_2095_);
v___x_2166_ = 2;
v___x_2167_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__48));
v___x_2168_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection(v_arg_2107_, v_arg_2104_, v___x_2166_, v___x_2167_, v_origExpr_2076_, v_a_2077_, v_a_2078_, v_a_2079_, v_a_2080_, v_a_2081_, v_a_2082_);
return v___x_2168_;
}
}
else
{
uint8_t v___x_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; 
lean_dec_ref(v___x_2144_);
lean_del_object(v___x_2095_);
v___x_2169_ = 3;
v___x_2170_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__50));
v___x_2171_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection(v_arg_2107_, v_arg_2104_, v___x_2169_, v___x_2170_, v_origExpr_2076_, v_a_2077_, v_a_2078_, v_a_2079_, v_a_2080_, v_a_2081_, v_a_2082_);
return v___x_2171_;
}
}
else
{
uint8_t v___x_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; 
lean_dec_ref(v___x_2144_);
lean_del_object(v___x_2095_);
v___x_2172_ = 4;
v___x_2173_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__52));
v___x_2174_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection(v_arg_2107_, v_arg_2104_, v___x_2172_, v___x_2173_, v_origExpr_2076_, v_a_2077_, v_a_2078_, v_a_2079_, v_a_2080_, v_a_2081_, v_a_2082_);
return v___x_2174_;
}
}
else
{
uint8_t v___x_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; 
lean_dec_ref(v___x_2144_);
lean_del_object(v___x_2095_);
v___x_2175_ = 5;
v___x_2176_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__54));
v___x_2177_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection(v_arg_2107_, v_arg_2104_, v___x_2175_, v___x_2176_, v_origExpr_2076_, v_a_2077_, v_a_2078_, v_a_2079_, v_a_2080_, v_a_2081_, v_a_2082_);
return v___x_2177_;
}
}
else
{
uint8_t v___x_2178_; lean_object* v___x_2179_; lean_object* v___x_2180_; 
lean_dec_ref(v___x_2144_);
lean_del_object(v___x_2095_);
v___x_2178_ = 6;
v___x_2179_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__56));
v___x_2180_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection(v_arg_2107_, v_arg_2104_, v___x_2178_, v___x_2179_, v_origExpr_2076_, v_a_2077_, v_a_2078_, v_a_2079_, v_a_2080_, v_a_2081_, v_a_2082_);
return v___x_2180_;
}
}
else
{
lean_object* v___x_2181_; 
lean_dec_ref(v___x_2144_);
lean_del_object(v___x_2095_);
lean_inc_ref(v_arg_2104_);
lean_inc_ref(v_arg_2140_);
v___x_2181_ = l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_getNatOrBvValue_x3f___redArg(v_arg_2140_, v_arg_2104_, v_a_2079_, v_a_2080_, v_a_2081_, v_a_2082_);
if (lean_obj_tag(v___x_2181_) == 0)
{
lean_object* v_a_2182_; lean_object* v___x_2184_; uint8_t v_isShared_2185_; uint8_t v_isSharedCheck_2235_; 
v_a_2182_ = lean_ctor_get(v___x_2181_, 0);
v_isSharedCheck_2235_ = !lean_is_exclusive(v___x_2181_);
if (v_isSharedCheck_2235_ == 0)
{
v___x_2184_ = v___x_2181_;
v_isShared_2185_ = v_isSharedCheck_2235_;
goto v_resetjp_2183_;
}
else
{
lean_inc(v_a_2182_);
lean_dec(v___x_2181_);
v___x_2184_ = lean_box(0);
v_isShared_2185_ = v_isSharedCheck_2235_;
goto v_resetjp_2183_;
}
v_resetjp_2183_:
{
lean_object* v___x_2191_; uint8_t v___x_2192_; 
v___x_2191_ = l_Lean_Expr_cleanupAnnotations(v_arg_2143_);
v___x_2192_ = l_Lean_Expr_isApp(v___x_2191_);
if (v___x_2192_ == 0)
{
lean_dec_ref(v___x_2191_);
lean_dec(v_a_2182_);
lean_dec_ref(v_arg_2140_);
lean_dec_ref(v_arg_2107_);
lean_dec_ref(v_arg_2104_);
lean_dec_ref(v_origExpr_2076_);
goto v___jp_2186_;
}
else
{
lean_object* v_arg_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; uint8_t v___x_2196_; 
v_arg_2193_ = lean_ctor_get(v___x_2191_, 1);
lean_inc_ref(v_arg_2193_);
v___x_2194_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2191_);
v___x_2195_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_of_go___closed__8));
v___x_2196_ = l_Lean_Expr_isConstOf(v___x_2194_, v___x_2195_);
lean_dec_ref(v___x_2194_);
if (v___x_2196_ == 0)
{
lean_dec_ref(v_arg_2193_);
lean_dec(v_a_2182_);
lean_dec_ref(v_arg_2140_);
lean_dec_ref(v_arg_2107_);
lean_dec_ref(v_arg_2104_);
lean_dec_ref(v_origExpr_2076_);
goto v___jp_2186_;
}
else
{
lean_object* v___x_2197_; 
lean_del_object(v___x_2184_);
v___x_2197_ = l_Lean_Meta_getNatValue_x3f(v_arg_2193_, v_a_2079_, v_a_2080_, v_a_2081_, v_a_2082_);
lean_dec_ref(v_arg_2193_);
if (lean_obj_tag(v___x_2197_) == 0)
{
lean_object* v_a_2198_; lean_object* v___f_2199_; lean_object* v___y_2201_; lean_object* v___y_2202_; lean_object* v___y_2203_; lean_object* v___y_2204_; lean_object* v___y_2205_; lean_object* v___y_2206_; uint8_t v___y_2226_; 
v_a_2198_ = lean_ctor_get(v___x_2197_, 0);
lean_inc(v_a_2198_);
lean_dec_ref(v___x_2197_);
v___f_2199_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__57));
if (lean_obj_tag(v_a_2198_) == 0)
{
v___y_2226_ = v___x_2148_;
goto v___jp_2225_;
}
else
{
lean_dec_ref(v_a_2198_);
v___y_2226_ = v___x_2196_;
goto v___jp_2225_;
}
v___jp_2200_:
{
lean_object* v___x_2207_; uint8_t v___x_2208_; 
v___x_2207_ = l_Lean_Expr_cleanupAnnotations(v_arg_2140_);
v___x_2208_ = l_Lean_Expr_isApp(v___x_2207_);
if (v___x_2208_ == 0)
{
lean_dec_ref(v___x_2207_);
lean_dec_ref(v_arg_2107_);
lean_dec_ref(v_arg_2104_);
lean_dec_ref(v_origExpr_2076_);
goto v___jp_2084_;
}
else
{
lean_object* v___x_2209_; uint8_t v___x_2210_; 
v___x_2209_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2207_);
v___x_2210_ = l_Lean_Expr_isConstOf(v___x_2209_, v___x_2195_);
lean_dec_ref(v___x_2209_);
if (v___x_2210_ == 0)
{
lean_dec_ref(v_arg_2107_);
lean_dec_ref(v_arg_2104_);
lean_dec_ref(v_origExpr_2076_);
goto v___jp_2084_;
}
else
{
lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; 
v___x_2211_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__59));
v___x_2212_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__61));
v___x_2213_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftReflection(v_arg_2104_, v_arg_2107_, v___f_2199_, v___x_2211_, v___x_2212_, v_origExpr_2076_, v___y_2201_, v___y_2202_, v___y_2203_, v___y_2204_, v___y_2205_, v___y_2206_);
return v___x_2213_;
}
}
}
v___jp_2214_:
{
lean_object* v___x_2215_; lean_object* v___x_2216_; 
v___x_2215_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__63, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__63_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__63);
v___x_2216_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go_spec__12___redArg(v___x_2215_, v_a_2079_, v_a_2080_, v_a_2081_, v_a_2082_);
if (lean_obj_tag(v___x_2216_) == 0)
{
lean_dec_ref(v___x_2216_);
v___y_2201_ = v_a_2077_;
v___y_2202_ = v_a_2078_;
v___y_2203_ = v_a_2079_;
v___y_2204_ = v_a_2080_;
v___y_2205_ = v_a_2081_;
v___y_2206_ = v_a_2082_;
goto v___jp_2200_;
}
else
{
lean_object* v_a_2217_; lean_object* v___x_2219_; uint8_t v_isShared_2220_; uint8_t v_isSharedCheck_2224_; 
lean_dec_ref(v_arg_2140_);
lean_dec_ref(v_arg_2107_);
lean_dec_ref(v_arg_2104_);
lean_dec_ref(v_origExpr_2076_);
v_a_2217_ = lean_ctor_get(v___x_2216_, 0);
v_isSharedCheck_2224_ = !lean_is_exclusive(v___x_2216_);
if (v_isSharedCheck_2224_ == 0)
{
v___x_2219_ = v___x_2216_;
v_isShared_2220_ = v_isSharedCheck_2224_;
goto v_resetjp_2218_;
}
else
{
lean_inc(v_a_2217_);
lean_dec(v___x_2216_);
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
v___jp_2225_:
{
if (v___y_2226_ == 0)
{
lean_dec(v_a_2182_);
v___y_2201_ = v_a_2077_;
v___y_2202_ = v_a_2078_;
v___y_2203_ = v_a_2079_;
v___y_2204_ = v_a_2080_;
v___y_2205_ = v_a_2081_;
v___y_2206_ = v_a_2082_;
goto v___jp_2200_;
}
else
{
if (lean_obj_tag(v_a_2182_) == 0)
{
if (v___x_2148_ == 0)
{
v___y_2201_ = v_a_2077_;
v___y_2202_ = v_a_2078_;
v___y_2203_ = v_a_2079_;
v___y_2204_ = v_a_2080_;
v___y_2205_ = v_a_2081_;
v___y_2206_ = v_a_2082_;
goto v___jp_2200_;
}
else
{
goto v___jp_2214_;
}
}
else
{
lean_dec_ref(v_a_2182_);
goto v___jp_2214_;
}
}
}
}
else
{
lean_object* v_a_2227_; lean_object* v___x_2229_; uint8_t v_isShared_2230_; uint8_t v_isSharedCheck_2234_; 
lean_dec(v_a_2182_);
lean_dec_ref(v_arg_2140_);
lean_dec_ref(v_arg_2107_);
lean_dec_ref(v_arg_2104_);
lean_dec_ref(v_origExpr_2076_);
v_a_2227_ = lean_ctor_get(v___x_2197_, 0);
v_isSharedCheck_2234_ = !lean_is_exclusive(v___x_2197_);
if (v_isSharedCheck_2234_ == 0)
{
v___x_2229_ = v___x_2197_;
v_isShared_2230_ = v_isSharedCheck_2234_;
goto v_resetjp_2228_;
}
else
{
lean_inc(v_a_2227_);
lean_dec(v___x_2197_);
v___x_2229_ = lean_box(0);
v_isShared_2230_ = v_isSharedCheck_2234_;
goto v_resetjp_2228_;
}
v_resetjp_2228_:
{
lean_object* v___x_2232_; 
if (v_isShared_2230_ == 0)
{
v___x_2232_ = v___x_2229_;
goto v_reusejp_2231_;
}
else
{
lean_object* v_reuseFailAlloc_2233_; 
v_reuseFailAlloc_2233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2233_, 0, v_a_2227_);
v___x_2232_ = v_reuseFailAlloc_2233_;
goto v_reusejp_2231_;
}
v_reusejp_2231_:
{
return v___x_2232_;
}
}
}
}
}
v___jp_2186_:
{
lean_object* v___x_2187_; lean_object* v___x_2189_; 
v___x_2187_ = lean_box(0);
if (v_isShared_2185_ == 0)
{
lean_ctor_set(v___x_2184_, 0, v___x_2187_);
v___x_2189_ = v___x_2184_;
goto v_reusejp_2188_;
}
else
{
lean_object* v_reuseFailAlloc_2190_; 
v_reuseFailAlloc_2190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2190_, 0, v___x_2187_);
v___x_2189_ = v_reuseFailAlloc_2190_;
goto v_reusejp_2188_;
}
v_reusejp_2188_:
{
return v___x_2189_;
}
}
}
}
else
{
lean_object* v_a_2236_; lean_object* v___x_2238_; uint8_t v_isShared_2239_; uint8_t v_isSharedCheck_2243_; 
lean_dec_ref(v_arg_2143_);
lean_dec_ref(v_arg_2140_);
lean_dec_ref(v_arg_2107_);
lean_dec_ref(v_arg_2104_);
lean_dec_ref(v_origExpr_2076_);
v_a_2236_ = lean_ctor_get(v___x_2181_, 0);
v_isSharedCheck_2243_ = !lean_is_exclusive(v___x_2181_);
if (v_isSharedCheck_2243_ == 0)
{
v___x_2238_ = v___x_2181_;
v_isShared_2239_ = v_isSharedCheck_2243_;
goto v_resetjp_2237_;
}
else
{
lean_inc(v_a_2236_);
lean_dec(v___x_2181_);
v___x_2238_ = lean_box(0);
v_isShared_2239_ = v_isSharedCheck_2243_;
goto v_resetjp_2237_;
}
v_resetjp_2237_:
{
lean_object* v___x_2241_; 
if (v_isShared_2239_ == 0)
{
v___x_2241_ = v___x_2238_;
goto v_reusejp_2240_;
}
else
{
lean_object* v_reuseFailAlloc_2242_; 
v_reuseFailAlloc_2242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2242_, 0, v_a_2236_);
v___x_2241_ = v_reuseFailAlloc_2242_;
goto v_reusejp_2240_;
}
v_reusejp_2240_:
{
return v___x_2241_;
}
}
}
}
}
else
{
lean_object* v___x_2244_; 
lean_dec_ref(v___x_2144_);
lean_del_object(v___x_2095_);
lean_inc_ref(v_arg_2104_);
lean_inc_ref(v_arg_2140_);
v___x_2244_ = l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_getNatOrBvValue_x3f___redArg(v_arg_2140_, v_arg_2104_, v_a_2079_, v_a_2080_, v_a_2081_, v_a_2082_);
if (lean_obj_tag(v___x_2244_) == 0)
{
lean_object* v_a_2245_; lean_object* v___x_2247_; uint8_t v_isShared_2248_; uint8_t v_isSharedCheck_2298_; 
v_a_2245_ = lean_ctor_get(v___x_2244_, 0);
v_isSharedCheck_2298_ = !lean_is_exclusive(v___x_2244_);
if (v_isSharedCheck_2298_ == 0)
{
v___x_2247_ = v___x_2244_;
v_isShared_2248_ = v_isSharedCheck_2298_;
goto v_resetjp_2246_;
}
else
{
lean_inc(v_a_2245_);
lean_dec(v___x_2244_);
v___x_2247_ = lean_box(0);
v_isShared_2248_ = v_isSharedCheck_2298_;
goto v_resetjp_2246_;
}
v_resetjp_2246_:
{
lean_object* v___x_2254_; uint8_t v___x_2255_; 
v___x_2254_ = l_Lean_Expr_cleanupAnnotations(v_arg_2143_);
v___x_2255_ = l_Lean_Expr_isApp(v___x_2254_);
if (v___x_2255_ == 0)
{
lean_dec_ref(v___x_2254_);
lean_dec(v_a_2245_);
lean_dec_ref(v_arg_2140_);
lean_dec_ref(v_arg_2107_);
lean_dec_ref(v_arg_2104_);
lean_dec_ref(v_origExpr_2076_);
goto v___jp_2249_;
}
else
{
lean_object* v_arg_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; uint8_t v___x_2259_; 
v_arg_2256_ = lean_ctor_get(v___x_2254_, 1);
lean_inc_ref(v_arg_2256_);
v___x_2257_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2254_);
v___x_2258_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_of_go___closed__8));
v___x_2259_ = l_Lean_Expr_isConstOf(v___x_2257_, v___x_2258_);
lean_dec_ref(v___x_2257_);
if (v___x_2259_ == 0)
{
lean_dec_ref(v_arg_2256_);
lean_dec(v_a_2245_);
lean_dec_ref(v_arg_2140_);
lean_dec_ref(v_arg_2107_);
lean_dec_ref(v_arg_2104_);
lean_dec_ref(v_origExpr_2076_);
goto v___jp_2249_;
}
else
{
lean_object* v___x_2260_; 
lean_del_object(v___x_2247_);
v___x_2260_ = l_Lean_Meta_getNatValue_x3f(v_arg_2256_, v_a_2079_, v_a_2080_, v_a_2081_, v_a_2082_);
lean_dec_ref(v_arg_2256_);
if (lean_obj_tag(v___x_2260_) == 0)
{
lean_object* v_a_2261_; lean_object* v___f_2262_; lean_object* v___y_2264_; lean_object* v___y_2265_; lean_object* v___y_2266_; lean_object* v___y_2267_; lean_object* v___y_2268_; lean_object* v___y_2269_; uint8_t v___y_2289_; 
v_a_2261_ = lean_ctor_get(v___x_2260_, 0);
lean_inc(v_a_2261_);
lean_dec_ref(v___x_2260_);
v___f_2262_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__64));
if (lean_obj_tag(v_a_2261_) == 0)
{
v___y_2289_ = v___x_2146_;
goto v___jp_2288_;
}
else
{
lean_dec_ref(v_a_2261_);
v___y_2289_ = v___x_2259_;
goto v___jp_2288_;
}
v___jp_2263_:
{
lean_object* v___x_2270_; uint8_t v___x_2271_; 
v___x_2270_ = l_Lean_Expr_cleanupAnnotations(v_arg_2140_);
v___x_2271_ = l_Lean_Expr_isApp(v___x_2270_);
if (v___x_2271_ == 0)
{
lean_dec_ref(v___x_2270_);
lean_dec_ref(v_arg_2107_);
lean_dec_ref(v_arg_2104_);
lean_dec_ref(v_origExpr_2076_);
goto v___jp_2087_;
}
else
{
lean_object* v___x_2272_; uint8_t v___x_2273_; 
v___x_2272_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2270_);
v___x_2273_ = l_Lean_Expr_isConstOf(v___x_2272_, v___x_2258_);
lean_dec_ref(v___x_2272_);
if (v___x_2273_ == 0)
{
lean_dec_ref(v_arg_2107_);
lean_dec_ref(v_arg_2104_);
lean_dec_ref(v_origExpr_2076_);
goto v___jp_2087_;
}
else
{
lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; 
v___x_2274_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__66));
v___x_2275_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__68));
v___x_2276_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftReflection(v_arg_2104_, v_arg_2107_, v___f_2262_, v___x_2274_, v___x_2275_, v_origExpr_2076_, v___y_2264_, v___y_2265_, v___y_2266_, v___y_2267_, v___y_2268_, v___y_2269_);
return v___x_2276_;
}
}
}
v___jp_2277_:
{
lean_object* v___x_2278_; lean_object* v___x_2279_; 
v___x_2278_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__63, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__63_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__63);
v___x_2279_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go_spec__12___redArg(v___x_2278_, v_a_2079_, v_a_2080_, v_a_2081_, v_a_2082_);
if (lean_obj_tag(v___x_2279_) == 0)
{
lean_dec_ref(v___x_2279_);
v___y_2264_ = v_a_2077_;
v___y_2265_ = v_a_2078_;
v___y_2266_ = v_a_2079_;
v___y_2267_ = v_a_2080_;
v___y_2268_ = v_a_2081_;
v___y_2269_ = v_a_2082_;
goto v___jp_2263_;
}
else
{
lean_object* v_a_2280_; lean_object* v___x_2282_; uint8_t v_isShared_2283_; uint8_t v_isSharedCheck_2287_; 
lean_dec_ref(v_arg_2140_);
lean_dec_ref(v_arg_2107_);
lean_dec_ref(v_arg_2104_);
lean_dec_ref(v_origExpr_2076_);
v_a_2280_ = lean_ctor_get(v___x_2279_, 0);
v_isSharedCheck_2287_ = !lean_is_exclusive(v___x_2279_);
if (v_isSharedCheck_2287_ == 0)
{
v___x_2282_ = v___x_2279_;
v_isShared_2283_ = v_isSharedCheck_2287_;
goto v_resetjp_2281_;
}
else
{
lean_inc(v_a_2280_);
lean_dec(v___x_2279_);
v___x_2282_ = lean_box(0);
v_isShared_2283_ = v_isSharedCheck_2287_;
goto v_resetjp_2281_;
}
v_resetjp_2281_:
{
lean_object* v___x_2285_; 
if (v_isShared_2283_ == 0)
{
v___x_2285_ = v___x_2282_;
goto v_reusejp_2284_;
}
else
{
lean_object* v_reuseFailAlloc_2286_; 
v_reuseFailAlloc_2286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2286_, 0, v_a_2280_);
v___x_2285_ = v_reuseFailAlloc_2286_;
goto v_reusejp_2284_;
}
v_reusejp_2284_:
{
return v___x_2285_;
}
}
}
}
v___jp_2288_:
{
if (v___y_2289_ == 0)
{
lean_dec(v_a_2245_);
v___y_2264_ = v_a_2077_;
v___y_2265_ = v_a_2078_;
v___y_2266_ = v_a_2079_;
v___y_2267_ = v_a_2080_;
v___y_2268_ = v_a_2081_;
v___y_2269_ = v_a_2082_;
goto v___jp_2263_;
}
else
{
if (lean_obj_tag(v_a_2245_) == 0)
{
if (v___x_2146_ == 0)
{
v___y_2264_ = v_a_2077_;
v___y_2265_ = v_a_2078_;
v___y_2266_ = v_a_2079_;
v___y_2267_ = v_a_2080_;
v___y_2268_ = v_a_2081_;
v___y_2269_ = v_a_2082_;
goto v___jp_2263_;
}
else
{
goto v___jp_2277_;
}
}
else
{
lean_dec_ref(v_a_2245_);
goto v___jp_2277_;
}
}
}
}
else
{
lean_object* v_a_2290_; lean_object* v___x_2292_; uint8_t v_isShared_2293_; uint8_t v_isSharedCheck_2297_; 
lean_dec(v_a_2245_);
lean_dec_ref(v_arg_2140_);
lean_dec_ref(v_arg_2107_);
lean_dec_ref(v_arg_2104_);
lean_dec_ref(v_origExpr_2076_);
v_a_2290_ = lean_ctor_get(v___x_2260_, 0);
v_isSharedCheck_2297_ = !lean_is_exclusive(v___x_2260_);
if (v_isSharedCheck_2297_ == 0)
{
v___x_2292_ = v___x_2260_;
v_isShared_2293_ = v_isSharedCheck_2297_;
goto v_resetjp_2291_;
}
else
{
lean_inc(v_a_2290_);
lean_dec(v___x_2260_);
v___x_2292_ = lean_box(0);
v_isShared_2293_ = v_isSharedCheck_2297_;
goto v_resetjp_2291_;
}
v_resetjp_2291_:
{
lean_object* v___x_2295_; 
if (v_isShared_2293_ == 0)
{
v___x_2295_ = v___x_2292_;
goto v_reusejp_2294_;
}
else
{
lean_object* v_reuseFailAlloc_2296_; 
v_reuseFailAlloc_2296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2296_, 0, v_a_2290_);
v___x_2295_ = v_reuseFailAlloc_2296_;
goto v_reusejp_2294_;
}
v_reusejp_2294_:
{
return v___x_2295_;
}
}
}
}
}
v___jp_2249_:
{
lean_object* v___x_2250_; lean_object* v___x_2252_; 
v___x_2250_ = lean_box(0);
if (v_isShared_2248_ == 0)
{
lean_ctor_set(v___x_2247_, 0, v___x_2250_);
v___x_2252_ = v___x_2247_;
goto v_reusejp_2251_;
}
else
{
lean_object* v_reuseFailAlloc_2253_; 
v_reuseFailAlloc_2253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2253_, 0, v___x_2250_);
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
lean_object* v_a_2299_; lean_object* v___x_2301_; uint8_t v_isShared_2302_; uint8_t v_isSharedCheck_2306_; 
lean_dec_ref(v_arg_2143_);
lean_dec_ref(v_arg_2140_);
lean_dec_ref(v_arg_2107_);
lean_dec_ref(v_arg_2104_);
lean_dec_ref(v_origExpr_2076_);
v_a_2299_ = lean_ctor_get(v___x_2244_, 0);
v_isSharedCheck_2306_ = !lean_is_exclusive(v___x_2244_);
if (v_isSharedCheck_2306_ == 0)
{
v___x_2301_ = v___x_2244_;
v_isShared_2302_ = v_isSharedCheck_2306_;
goto v_resetjp_2300_;
}
else
{
lean_inc(v_a_2299_);
lean_dec(v___x_2244_);
v___x_2301_ = lean_box(0);
v_isShared_2302_ = v_isSharedCheck_2306_;
goto v_resetjp_2300_;
}
v_resetjp_2300_:
{
lean_object* v___x_2304_; 
if (v_isShared_2302_ == 0)
{
v___x_2304_ = v___x_2301_;
goto v_reusejp_2303_;
}
else
{
lean_object* v_reuseFailAlloc_2305_; 
v_reuseFailAlloc_2305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2305_, 0, v_a_2299_);
v___x_2304_ = v_reuseFailAlloc_2305_;
goto v_reusejp_2303_;
}
v_reusejp_2303_:
{
return v___x_2304_;
}
}
}
}
}
else
{
lean_object* v___x_2307_; 
lean_dec_ref(v___x_2144_);
lean_dec_ref(v_arg_2143_);
lean_dec_ref(v_arg_2140_);
lean_del_object(v___x_2095_);
lean_inc_ref(v_arg_2107_);
v___x_2307_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_goOrAtom(v_arg_2107_, v_a_2077_, v_a_2078_, v_a_2079_, v_a_2080_, v_a_2081_, v_a_2082_);
if (lean_obj_tag(v___x_2307_) == 0)
{
lean_object* v_a_2308_; lean_object* v___x_2310_; uint8_t v_isShared_2311_; uint8_t v_isSharedCheck_2371_; 
v_a_2308_ = lean_ctor_get(v___x_2307_, 0);
v_isSharedCheck_2371_ = !lean_is_exclusive(v___x_2307_);
if (v_isSharedCheck_2371_ == 0)
{
v___x_2310_ = v___x_2307_;
v_isShared_2311_ = v_isSharedCheck_2371_;
goto v_resetjp_2309_;
}
else
{
lean_inc(v_a_2308_);
lean_dec(v___x_2307_);
v___x_2310_ = lean_box(0);
v_isShared_2311_ = v_isSharedCheck_2371_;
goto v_resetjp_2309_;
}
v_resetjp_2309_:
{
if (lean_obj_tag(v_a_2308_) == 1)
{
lean_object* v_val_2312_; lean_object* v___x_2313_; 
lean_del_object(v___x_2310_);
v_val_2312_ = lean_ctor_get(v_a_2308_, 0);
lean_inc(v_val_2312_);
lean_dec_ref(v_a_2308_);
lean_inc_ref(v_arg_2104_);
v___x_2313_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_goOrAtom(v_arg_2104_, v_a_2077_, v_a_2078_, v_a_2079_, v_a_2080_, v_a_2081_, v_a_2082_);
if (lean_obj_tag(v___x_2313_) == 0)
{
lean_object* v_a_2314_; lean_object* v___x_2316_; uint8_t v_isShared_2317_; uint8_t v_isSharedCheck_2366_; 
v_a_2314_ = lean_ctor_get(v___x_2313_, 0);
v_isSharedCheck_2366_ = !lean_is_exclusive(v___x_2313_);
if (v_isSharedCheck_2366_ == 0)
{
v___x_2316_ = v___x_2313_;
v_isShared_2317_ = v_isSharedCheck_2366_;
goto v_resetjp_2315_;
}
else
{
lean_inc(v_a_2314_);
lean_dec(v___x_2313_);
v___x_2316_ = lean_box(0);
v_isShared_2317_ = v_isSharedCheck_2366_;
goto v_resetjp_2315_;
}
v_resetjp_2315_:
{
if (lean_obj_tag(v_a_2314_) == 1)
{
lean_object* v_val_2318_; lean_object* v___x_2320_; uint8_t v_isShared_2321_; uint8_t v_isSharedCheck_2361_; 
lean_del_object(v___x_2316_);
v_val_2318_ = lean_ctor_get(v_a_2314_, 0);
v_isSharedCheck_2361_ = !lean_is_exclusive(v_a_2314_);
if (v_isSharedCheck_2361_ == 0)
{
v___x_2320_ = v_a_2314_;
v_isShared_2321_ = v_isSharedCheck_2361_;
goto v_resetjp_2319_;
}
else
{
lean_inc(v_val_2318_);
lean_dec(v_a_2314_);
v___x_2320_ = lean_box(0);
v_isShared_2321_ = v_isSharedCheck_2361_;
goto v_resetjp_2319_;
}
v_resetjp_2319_:
{
lean_object* v_width_2322_; lean_object* v_bvExpr_2323_; lean_object* v_expr_2324_; lean_object* v_width_2325_; lean_object* v_bvExpr_2326_; lean_object* v_expr_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; 
v_width_2322_ = lean_ctor_get(v_val_2312_, 0);
lean_inc_n(v_width_2322_, 2);
v_bvExpr_2323_ = lean_ctor_get(v_val_2312_, 1);
v_expr_2324_ = lean_ctor_get(v_val_2312_, 4);
lean_inc_ref(v_expr_2324_);
v_width_2325_ = lean_ctor_get(v_val_2318_, 0);
lean_inc_n(v_width_2325_, 2);
v_bvExpr_2326_ = lean_ctor_get(v_val_2318_, 1);
v_expr_2327_ = lean_ctor_get(v_val_2318_, 4);
lean_inc_ref(v_expr_2327_);
v___x_2328_ = lean_nat_add(v_width_2322_, v_width_2325_);
lean_inc_ref(v_bvExpr_2326_);
lean_inc_ref(v_bvExpr_2323_);
lean_inc_n(v___x_2328_, 2);
v___x_2329_ = l_Std_Tactic_BVDecide_BVExpr_append___override___redArg(v_width_2322_, v_width_2325_, v___x_2328_, v_bvExpr_2323_, v_bvExpr_2326_);
v___x_2330_ = l_Lean_mkNatLit(v___x_2328_);
lean_inc_ref(v___x_2330_);
v___x_2331_ = l_Lean_Meta_mkEqRefl(v___x_2330_, v_a_2079_, v_a_2080_, v_a_2081_, v_a_2082_);
if (lean_obj_tag(v___x_2331_) == 0)
{
lean_object* v_a_2332_; lean_object* v___x_2334_; uint8_t v_isShared_2335_; uint8_t v_isSharedCheck_2352_; 
v_a_2332_ = lean_ctor_get(v___x_2331_, 0);
v_isSharedCheck_2352_ = !lean_is_exclusive(v___x_2331_);
if (v_isSharedCheck_2352_ == 0)
{
v___x_2334_ = v___x_2331_;
v_isShared_2335_ = v_isSharedCheck_2352_;
goto v_resetjp_2333_;
}
else
{
lean_inc(v_a_2332_);
lean_dec(v___x_2331_);
v___x_2334_ = lean_box(0);
v_isShared_2335_ = v_isSharedCheck_2352_;
goto v_resetjp_2333_;
}
v_resetjp_2333_:
{
lean_object* v___x_2336_; lean_object* v___x_2337_; lean_object* v___x_2338_; lean_object* v___x_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; lean_object* v___f_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2347_; 
v___x_2336_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0));
v___x_2337_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1));
v___x_2338_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2));
v___x_2339_ = lean_box(0);
v___x_2340_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__71, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__71_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__71);
lean_inc(v_width_2322_);
v___x_2341_ = l_Lean_mkNatLit(v_width_2322_);
lean_inc(v_width_2325_);
v___x_2342_ = l_Lean_mkNatLit(v_width_2325_);
lean_inc_ref(v___x_2342_);
lean_inc_ref(v___x_2341_);
lean_inc_ref(v_expr_2327_);
lean_inc_ref(v_expr_2324_);
v___f_2343_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___lam__0___boxed), 21, 15);
lean_closure_set(v___f_2343_, 0, v_width_2322_);
lean_closure_set(v___f_2343_, 1, v_expr_2324_);
lean_closure_set(v___f_2343_, 2, v_width_2325_);
lean_closure_set(v___f_2343_, 3, v_expr_2327_);
lean_closure_set(v___f_2343_, 4, v_val_2312_);
lean_closure_set(v___f_2343_, 5, v_val_2318_);
lean_closure_set(v___f_2343_, 6, v___x_2336_);
lean_closure_set(v___f_2343_, 7, v___x_2337_);
lean_closure_set(v___f_2343_, 8, v___x_2338_);
lean_closure_set(v___f_2343_, 9, v___x_2109_);
lean_closure_set(v___f_2343_, 10, v___x_2339_);
lean_closure_set(v___f_2343_, 11, v___x_2341_);
lean_closure_set(v___f_2343_, 12, v___x_2342_);
lean_closure_set(v___f_2343_, 13, v_arg_2107_);
lean_closure_set(v___f_2343_, 14, v_arg_2104_);
v___x_2344_ = l_Lean_mkApp6(v___x_2340_, v___x_2341_, v___x_2342_, v___x_2330_, v_expr_2324_, v_expr_2327_, v_a_2332_);
v___x_2345_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2345_, 0, v___x_2328_);
lean_ctor_set(v___x_2345_, 1, v___x_2329_);
lean_ctor_set(v___x_2345_, 2, v_origExpr_2076_);
lean_ctor_set(v___x_2345_, 3, v___f_2343_);
lean_ctor_set(v___x_2345_, 4, v___x_2344_);
if (v_isShared_2321_ == 0)
{
lean_ctor_set(v___x_2320_, 0, v___x_2345_);
v___x_2347_ = v___x_2320_;
goto v_reusejp_2346_;
}
else
{
lean_object* v_reuseFailAlloc_2351_; 
v_reuseFailAlloc_2351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2351_, 0, v___x_2345_);
v___x_2347_ = v_reuseFailAlloc_2351_;
goto v_reusejp_2346_;
}
v_reusejp_2346_:
{
lean_object* v___x_2349_; 
if (v_isShared_2335_ == 0)
{
lean_ctor_set(v___x_2334_, 0, v___x_2347_);
v___x_2349_ = v___x_2334_;
goto v_reusejp_2348_;
}
else
{
lean_object* v_reuseFailAlloc_2350_; 
v_reuseFailAlloc_2350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2350_, 0, v___x_2347_);
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
else
{
lean_object* v_a_2353_; lean_object* v___x_2355_; uint8_t v_isShared_2356_; uint8_t v_isSharedCheck_2360_; 
lean_dec_ref(v___x_2330_);
lean_dec_ref(v___x_2329_);
lean_dec(v___x_2328_);
lean_dec_ref(v_expr_2327_);
lean_dec(v_width_2325_);
lean_dec_ref(v_expr_2324_);
lean_dec(v_width_2322_);
lean_del_object(v___x_2320_);
lean_dec(v_val_2318_);
lean_dec(v_val_2312_);
lean_dec_ref(v_arg_2107_);
lean_dec_ref(v_arg_2104_);
lean_dec_ref(v_origExpr_2076_);
v_a_2353_ = lean_ctor_get(v___x_2331_, 0);
v_isSharedCheck_2360_ = !lean_is_exclusive(v___x_2331_);
if (v_isSharedCheck_2360_ == 0)
{
v___x_2355_ = v___x_2331_;
v_isShared_2356_ = v_isSharedCheck_2360_;
goto v_resetjp_2354_;
}
else
{
lean_inc(v_a_2353_);
lean_dec(v___x_2331_);
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
}
else
{
lean_object* v___x_2362_; lean_object* v___x_2364_; 
lean_dec(v_a_2314_);
lean_dec(v_val_2312_);
lean_dec_ref(v_arg_2107_);
lean_dec_ref(v_arg_2104_);
lean_dec_ref(v_origExpr_2076_);
v___x_2362_ = lean_box(0);
if (v_isShared_2317_ == 0)
{
lean_ctor_set(v___x_2316_, 0, v___x_2362_);
v___x_2364_ = v___x_2316_;
goto v_reusejp_2363_;
}
else
{
lean_object* v_reuseFailAlloc_2365_; 
v_reuseFailAlloc_2365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2365_, 0, v___x_2362_);
v___x_2364_ = v_reuseFailAlloc_2365_;
goto v_reusejp_2363_;
}
v_reusejp_2363_:
{
return v___x_2364_;
}
}
}
}
else
{
lean_dec(v_val_2312_);
lean_dec_ref(v_arg_2107_);
lean_dec_ref(v_arg_2104_);
lean_dec_ref(v_origExpr_2076_);
return v___x_2313_;
}
}
else
{
lean_object* v___x_2367_; lean_object* v___x_2369_; 
lean_dec(v_a_2308_);
lean_dec_ref(v_arg_2107_);
lean_dec_ref(v_arg_2104_);
lean_dec_ref(v_origExpr_2076_);
v___x_2367_ = lean_box(0);
if (v_isShared_2311_ == 0)
{
lean_ctor_set(v___x_2310_, 0, v___x_2367_);
v___x_2369_ = v___x_2310_;
goto v_reusejp_2368_;
}
else
{
lean_object* v_reuseFailAlloc_2370_; 
v_reuseFailAlloc_2370_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2370_, 0, v___x_2367_);
v___x_2369_ = v_reuseFailAlloc_2370_;
goto v_reusejp_2368_;
}
v_reusejp_2368_:
{
return v___x_2369_;
}
}
}
}
else
{
lean_dec_ref(v_arg_2107_);
lean_dec_ref(v_arg_2104_);
lean_dec_ref(v_origExpr_2076_);
return v___x_2307_;
}
}
}
}
}
else
{
lean_object* v___f_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; 
lean_dec_ref(v___x_2132_);
lean_del_object(v___x_2095_);
v___f_2372_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__72));
v___x_2373_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__74));
v___x_2374_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__76));
v___x_2375_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftReflection(v_arg_2104_, v_arg_2107_, v___f_2372_, v___x_2373_, v___x_2374_, v_origExpr_2076_, v_a_2077_, v_a_2078_, v_a_2079_, v_a_2080_, v_a_2081_, v_a_2082_);
return v___x_2375_;
}
}
else
{
lean_object* v___x_2376_; 
lean_dec_ref(v___x_2132_);
lean_del_object(v___x_2095_);
v___x_2376_ = l_Lean_Meta_getNatValue_x3f(v_arg_2119_, v_a_2079_, v_a_2080_, v_a_2081_, v_a_2082_);
if (lean_obj_tag(v___x_2376_) == 0)
{
lean_object* v_a_2377_; lean_object* v___x_2379_; uint8_t v_isShared_2380_; uint8_t v_isSharedCheck_2439_; 
v_a_2377_ = lean_ctor_get(v___x_2376_, 0);
v_isSharedCheck_2439_ = !lean_is_exclusive(v___x_2376_);
if (v_isSharedCheck_2439_ == 0)
{
v___x_2379_ = v___x_2376_;
v_isShared_2380_ = v_isSharedCheck_2439_;
goto v_resetjp_2378_;
}
else
{
lean_inc(v_a_2377_);
lean_dec(v___x_2376_);
v___x_2379_ = lean_box(0);
v_isShared_2380_ = v_isSharedCheck_2439_;
goto v_resetjp_2378_;
}
v_resetjp_2378_:
{
if (lean_obj_tag(v_a_2377_) == 1)
{
lean_object* v_val_2381_; lean_object* v___x_2382_; 
lean_del_object(v___x_2379_);
v_val_2381_ = lean_ctor_get(v_a_2377_, 0);
lean_inc(v_val_2381_);
lean_dec_ref(v_a_2377_);
v___x_2382_ = l_Lean_Meta_getNatValue_x3f(v_arg_2107_, v_a_2079_, v_a_2080_, v_a_2081_, v_a_2082_);
if (lean_obj_tag(v___x_2382_) == 0)
{
lean_object* v_a_2383_; lean_object* v___x_2385_; uint8_t v_isShared_2386_; uint8_t v_isSharedCheck_2426_; 
v_a_2383_ = lean_ctor_get(v___x_2382_, 0);
v_isSharedCheck_2426_ = !lean_is_exclusive(v___x_2382_);
if (v_isSharedCheck_2426_ == 0)
{
v___x_2385_ = v___x_2382_;
v_isShared_2386_ = v_isSharedCheck_2426_;
goto v_resetjp_2384_;
}
else
{
lean_inc(v_a_2383_);
lean_dec(v___x_2382_);
v___x_2385_ = lean_box(0);
v_isShared_2386_ = v_isSharedCheck_2426_;
goto v_resetjp_2384_;
}
v_resetjp_2384_:
{
if (lean_obj_tag(v_a_2383_) == 1)
{
lean_object* v_val_2387_; lean_object* v___x_2388_; 
lean_del_object(v___x_2385_);
v_val_2387_ = lean_ctor_get(v_a_2383_, 0);
lean_inc(v_val_2387_);
lean_dec_ref(v_a_2383_);
lean_inc_ref(v_arg_2104_);
v___x_2388_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_goOrAtom(v_arg_2104_, v_a_2077_, v_a_2078_, v_a_2079_, v_a_2080_, v_a_2081_, v_a_2082_);
if (lean_obj_tag(v___x_2388_) == 0)
{
lean_object* v_a_2389_; lean_object* v___x_2391_; uint8_t v_isShared_2392_; uint8_t v_isSharedCheck_2421_; 
v_a_2389_ = lean_ctor_get(v___x_2388_, 0);
v_isSharedCheck_2421_ = !lean_is_exclusive(v___x_2388_);
if (v_isSharedCheck_2421_ == 0)
{
v___x_2391_ = v___x_2388_;
v_isShared_2392_ = v_isSharedCheck_2421_;
goto v_resetjp_2390_;
}
else
{
lean_inc(v_a_2389_);
lean_dec(v___x_2388_);
v___x_2391_ = lean_box(0);
v_isShared_2392_ = v_isSharedCheck_2421_;
goto v_resetjp_2390_;
}
v_resetjp_2390_:
{
if (lean_obj_tag(v_a_2389_) == 1)
{
lean_object* v_val_2393_; lean_object* v___x_2395_; uint8_t v_isShared_2396_; uint8_t v_isSharedCheck_2416_; 
v_val_2393_ = lean_ctor_get(v_a_2389_, 0);
v_isSharedCheck_2416_ = !lean_is_exclusive(v_a_2389_);
if (v_isSharedCheck_2416_ == 0)
{
v___x_2395_ = v_a_2389_;
v_isShared_2396_ = v_isSharedCheck_2416_;
goto v_resetjp_2394_;
}
else
{
lean_inc(v_val_2393_);
lean_dec(v_a_2389_);
v___x_2395_ = lean_box(0);
v_isShared_2396_ = v_isSharedCheck_2416_;
goto v_resetjp_2394_;
}
v_resetjp_2394_:
{
lean_object* v_width_2397_; lean_object* v_bvExpr_2398_; lean_object* v_expr_2399_; lean_object* v___x_2400_; lean_object* v___x_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v___f_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2411_; 
v_width_2397_ = lean_ctor_get(v_val_2393_, 0);
lean_inc_n(v_width_2397_, 3);
v_bvExpr_2398_ = lean_ctor_get(v_val_2393_, 1);
v_expr_2399_ = lean_ctor_get(v_val_2393_, 4);
lean_inc_ref_n(v_expr_2399_, 2);
lean_inc_ref(v_bvExpr_2398_);
lean_inc(v_val_2387_);
v___x_2400_ = l_Std_Tactic_BVDecide_BVExpr_extract___override(v_width_2397_, v_val_2381_, v_val_2387_, v_bvExpr_2398_);
v___x_2401_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0));
v___x_2402_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1));
v___x_2403_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2));
v___x_2404_ = lean_box(0);
v___x_2405_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__79, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__79_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__79);
v___x_2406_ = l_Lean_mkNatLit(v_width_2397_);
lean_inc_ref(v___x_2406_);
lean_inc_ref(v_arg_2107_);
lean_inc_ref(v_arg_2119_);
v___f_2407_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___lam__1___boxed), 18, 12);
lean_closure_set(v___f_2407_, 0, v_width_2397_);
lean_closure_set(v___f_2407_, 1, v_expr_2399_);
lean_closure_set(v___f_2407_, 2, v_val_2393_);
lean_closure_set(v___f_2407_, 3, v___x_2401_);
lean_closure_set(v___f_2407_, 4, v___x_2402_);
lean_closure_set(v___f_2407_, 5, v___x_2403_);
lean_closure_set(v___f_2407_, 6, v___x_2109_);
lean_closure_set(v___f_2407_, 7, v___x_2404_);
lean_closure_set(v___f_2407_, 8, v_arg_2119_);
lean_closure_set(v___f_2407_, 9, v_arg_2107_);
lean_closure_set(v___f_2407_, 10, v___x_2406_);
lean_closure_set(v___f_2407_, 11, v_arg_2104_);
v___x_2408_ = l_Lean_mkApp4(v___x_2405_, v___x_2406_, v_arg_2119_, v_arg_2107_, v_expr_2399_);
v___x_2409_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2409_, 0, v_val_2387_);
lean_ctor_set(v___x_2409_, 1, v___x_2400_);
lean_ctor_set(v___x_2409_, 2, v_origExpr_2076_);
lean_ctor_set(v___x_2409_, 3, v___f_2407_);
lean_ctor_set(v___x_2409_, 4, v___x_2408_);
if (v_isShared_2396_ == 0)
{
lean_ctor_set(v___x_2395_, 0, v___x_2409_);
v___x_2411_ = v___x_2395_;
goto v_reusejp_2410_;
}
else
{
lean_object* v_reuseFailAlloc_2415_; 
v_reuseFailAlloc_2415_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2415_, 0, v___x_2409_);
v___x_2411_ = v_reuseFailAlloc_2415_;
goto v_reusejp_2410_;
}
v_reusejp_2410_:
{
lean_object* v___x_2413_; 
if (v_isShared_2392_ == 0)
{
lean_ctor_set(v___x_2391_, 0, v___x_2411_);
v___x_2413_ = v___x_2391_;
goto v_reusejp_2412_;
}
else
{
lean_object* v_reuseFailAlloc_2414_; 
v_reuseFailAlloc_2414_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2414_, 0, v___x_2411_);
v___x_2413_ = v_reuseFailAlloc_2414_;
goto v_reusejp_2412_;
}
v_reusejp_2412_:
{
return v___x_2413_;
}
}
}
}
else
{
lean_object* v___x_2417_; lean_object* v___x_2419_; 
lean_dec(v_a_2389_);
lean_dec(v_val_2387_);
lean_dec(v_val_2381_);
lean_dec_ref(v_arg_2119_);
lean_dec_ref(v_arg_2107_);
lean_dec_ref(v_arg_2104_);
lean_dec_ref(v_origExpr_2076_);
v___x_2417_ = lean_box(0);
if (v_isShared_2392_ == 0)
{
lean_ctor_set(v___x_2391_, 0, v___x_2417_);
v___x_2419_ = v___x_2391_;
goto v_reusejp_2418_;
}
else
{
lean_object* v_reuseFailAlloc_2420_; 
v_reuseFailAlloc_2420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2420_, 0, v___x_2417_);
v___x_2419_ = v_reuseFailAlloc_2420_;
goto v_reusejp_2418_;
}
v_reusejp_2418_:
{
return v___x_2419_;
}
}
}
}
else
{
lean_dec(v_val_2387_);
lean_dec(v_val_2381_);
lean_dec_ref(v_arg_2119_);
lean_dec_ref(v_arg_2107_);
lean_dec_ref(v_arg_2104_);
lean_dec_ref(v_origExpr_2076_);
return v___x_2388_;
}
}
else
{
lean_object* v___x_2422_; lean_object* v___x_2424_; 
lean_dec(v_a_2383_);
lean_dec(v_val_2381_);
lean_dec_ref(v_arg_2119_);
lean_dec_ref(v_arg_2107_);
lean_dec_ref(v_arg_2104_);
lean_dec_ref(v_origExpr_2076_);
v___x_2422_ = lean_box(0);
if (v_isShared_2386_ == 0)
{
lean_ctor_set(v___x_2385_, 0, v___x_2422_);
v___x_2424_ = v___x_2385_;
goto v_reusejp_2423_;
}
else
{
lean_object* v_reuseFailAlloc_2425_; 
v_reuseFailAlloc_2425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2425_, 0, v___x_2422_);
v___x_2424_ = v_reuseFailAlloc_2425_;
goto v_reusejp_2423_;
}
v_reusejp_2423_:
{
return v___x_2424_;
}
}
}
}
else
{
lean_object* v_a_2427_; lean_object* v___x_2429_; uint8_t v_isShared_2430_; uint8_t v_isSharedCheck_2434_; 
lean_dec(v_val_2381_);
lean_dec_ref(v_arg_2119_);
lean_dec_ref(v_arg_2107_);
lean_dec_ref(v_arg_2104_);
lean_dec_ref(v_origExpr_2076_);
v_a_2427_ = lean_ctor_get(v___x_2382_, 0);
v_isSharedCheck_2434_ = !lean_is_exclusive(v___x_2382_);
if (v_isSharedCheck_2434_ == 0)
{
v___x_2429_ = v___x_2382_;
v_isShared_2430_ = v_isSharedCheck_2434_;
goto v_resetjp_2428_;
}
else
{
lean_inc(v_a_2427_);
lean_dec(v___x_2382_);
v___x_2429_ = lean_box(0);
v_isShared_2430_ = v_isSharedCheck_2434_;
goto v_resetjp_2428_;
}
v_resetjp_2428_:
{
lean_object* v___x_2432_; 
if (v_isShared_2430_ == 0)
{
v___x_2432_ = v___x_2429_;
goto v_reusejp_2431_;
}
else
{
lean_object* v_reuseFailAlloc_2433_; 
v_reuseFailAlloc_2433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2433_, 0, v_a_2427_);
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
else
{
lean_object* v___x_2435_; lean_object* v___x_2437_; 
lean_dec(v_a_2377_);
lean_dec_ref(v_arg_2119_);
lean_dec_ref(v_arg_2107_);
lean_dec_ref(v_arg_2104_);
lean_dec_ref(v_origExpr_2076_);
v___x_2435_ = lean_box(0);
if (v_isShared_2380_ == 0)
{
lean_ctor_set(v___x_2379_, 0, v___x_2435_);
v___x_2437_ = v___x_2379_;
goto v_reusejp_2436_;
}
else
{
lean_object* v_reuseFailAlloc_2438_; 
v_reuseFailAlloc_2438_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2438_, 0, v___x_2435_);
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
lean_object* v_a_2440_; lean_object* v___x_2442_; uint8_t v_isShared_2443_; uint8_t v_isSharedCheck_2447_; 
lean_dec_ref(v_arg_2119_);
lean_dec_ref(v_arg_2107_);
lean_dec_ref(v_arg_2104_);
lean_dec_ref(v_origExpr_2076_);
v_a_2440_ = lean_ctor_get(v___x_2376_, 0);
v_isSharedCheck_2447_ = !lean_is_exclusive(v___x_2376_);
if (v_isSharedCheck_2447_ == 0)
{
v___x_2442_ = v___x_2376_;
v_isShared_2443_ = v_isSharedCheck_2447_;
goto v_resetjp_2441_;
}
else
{
lean_inc(v_a_2440_);
lean_dec(v___x_2376_);
v___x_2442_ = lean_box(0);
v_isShared_2443_ = v_isSharedCheck_2447_;
goto v_resetjp_2441_;
}
v_resetjp_2441_:
{
lean_object* v___x_2445_; 
if (v_isShared_2443_ == 0)
{
v___x_2445_ = v___x_2442_;
goto v_reusejp_2444_;
}
else
{
lean_object* v_reuseFailAlloc_2446_; 
v_reuseFailAlloc_2446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2446_, 0, v_a_2440_);
v___x_2445_ = v_reuseFailAlloc_2446_;
goto v_reusejp_2444_;
}
v_reusejp_2444_:
{
return v___x_2445_;
}
}
}
}
}
else
{
lean_object* v___x_2448_; 
lean_dec_ref(v___x_2132_);
lean_del_object(v___x_2095_);
lean_inc_ref(v_origExpr_2076_);
v___x_2448_ = l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_bitVecAtom(v_origExpr_2076_, v___x_2134_, v_a_2078_, v_a_2079_, v_a_2080_, v_a_2081_, v_a_2082_);
if (lean_obj_tag(v___x_2448_) == 0)
{
lean_object* v_a_2449_; lean_object* v___x_2451_; uint8_t v_isShared_2452_; uint8_t v_isSharedCheck_2516_; 
v_a_2449_ = lean_ctor_get(v___x_2448_, 0);
v_isSharedCheck_2516_ = !lean_is_exclusive(v___x_2448_);
if (v_isSharedCheck_2516_ == 0)
{
v___x_2451_ = v___x_2448_;
v_isShared_2452_ = v_isSharedCheck_2516_;
goto v_resetjp_2450_;
}
else
{
lean_inc(v_a_2449_);
lean_dec(v___x_2448_);
v___x_2451_ = lean_box(0);
v_isShared_2452_ = v_isSharedCheck_2516_;
goto v_resetjp_2450_;
}
v_resetjp_2450_:
{
if (lean_obj_tag(v_a_2449_) == 1)
{
lean_object* v_val_2453_; lean_object* v___x_2454_; 
lean_del_object(v___x_2451_);
v_val_2453_ = lean_ctor_get(v_a_2449_, 0);
lean_inc_ref(v_arg_2119_);
v___x_2454_ = l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of(v_arg_2119_, v_a_2077_, v_a_2078_, v_a_2079_, v_a_2080_, v_a_2081_, v_a_2082_);
if (lean_obj_tag(v___x_2454_) == 0)
{
lean_object* v_a_2455_; lean_object* v___x_2457_; uint8_t v_isShared_2458_; uint8_t v_isSharedCheck_2503_; 
v_a_2455_ = lean_ctor_get(v___x_2454_, 0);
v_isSharedCheck_2503_ = !lean_is_exclusive(v___x_2454_);
if (v_isSharedCheck_2503_ == 0)
{
v___x_2457_ = v___x_2454_;
v_isShared_2458_ = v_isSharedCheck_2503_;
goto v_resetjp_2456_;
}
else
{
lean_inc(v_a_2455_);
lean_dec(v___x_2454_);
v___x_2457_ = lean_box(0);
v_isShared_2458_ = v_isSharedCheck_2503_;
goto v_resetjp_2456_;
}
v_resetjp_2456_:
{
if (lean_obj_tag(v_a_2455_) == 1)
{
lean_object* v_val_2459_; lean_object* v___x_2460_; 
lean_del_object(v___x_2457_);
v_val_2459_ = lean_ctor_get(v_a_2455_, 0);
lean_inc(v_val_2459_);
lean_dec_ref(v_a_2455_);
lean_inc_ref(v_arg_2107_);
v___x_2460_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_goOrAtom(v_arg_2107_, v_a_2077_, v_a_2078_, v_a_2079_, v_a_2080_, v_a_2081_, v_a_2082_);
if (lean_obj_tag(v___x_2460_) == 0)
{
lean_object* v_a_2461_; lean_object* v___x_2463_; uint8_t v_isShared_2464_; uint8_t v_isSharedCheck_2498_; 
v_a_2461_ = lean_ctor_get(v___x_2460_, 0);
v_isSharedCheck_2498_ = !lean_is_exclusive(v___x_2460_);
if (v_isSharedCheck_2498_ == 0)
{
v___x_2463_ = v___x_2460_;
v_isShared_2464_ = v_isSharedCheck_2498_;
goto v_resetjp_2462_;
}
else
{
lean_inc(v_a_2461_);
lean_dec(v___x_2460_);
v___x_2463_ = lean_box(0);
v_isShared_2464_ = v_isSharedCheck_2498_;
goto v_resetjp_2462_;
}
v_resetjp_2462_:
{
if (lean_obj_tag(v_a_2461_) == 1)
{
lean_object* v_val_2465_; lean_object* v___x_2466_; 
lean_del_object(v___x_2463_);
v_val_2465_ = lean_ctor_get(v_a_2461_, 0);
lean_inc(v_val_2465_);
lean_dec_ref(v_a_2461_);
lean_inc_ref(v_arg_2104_);
v___x_2466_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_goOrAtom(v_arg_2104_, v_a_2077_, v_a_2078_, v_a_2079_, v_a_2080_, v_a_2081_, v_a_2082_);
if (lean_obj_tag(v___x_2466_) == 0)
{
lean_object* v_a_2467_; lean_object* v___x_2469_; uint8_t v_isShared_2470_; uint8_t v_isSharedCheck_2493_; 
v_a_2467_ = lean_ctor_get(v___x_2466_, 0);
v_isSharedCheck_2493_ = !lean_is_exclusive(v___x_2466_);
if (v_isSharedCheck_2493_ == 0)
{
v___x_2469_ = v___x_2466_;
v_isShared_2470_ = v_isSharedCheck_2493_;
goto v_resetjp_2468_;
}
else
{
lean_inc(v_a_2467_);
lean_dec(v___x_2466_);
v___x_2469_ = lean_box(0);
v_isShared_2470_ = v_isSharedCheck_2493_;
goto v_resetjp_2468_;
}
v_resetjp_2468_:
{
if (lean_obj_tag(v_a_2467_) == 1)
{
lean_object* v_val_2471_; lean_object* v___x_2472_; 
lean_del_object(v___x_2469_);
v_val_2471_ = lean_ctor_get(v_a_2467_, 0);
lean_inc(v_val_2471_);
lean_dec_ref(v_a_2467_);
lean_inc(v_val_2453_);
v___x_2472_ = l_Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas___redArg(v_val_2459_, v_val_2453_, v_val_2465_, v_val_2471_, v_arg_2119_, v_origExpr_2076_, v_arg_2107_, v_arg_2104_, v_a_2077_, v_a_2079_, v_a_2080_, v_a_2081_, v_a_2082_);
if (lean_obj_tag(v___x_2472_) == 0)
{
lean_object* v___x_2474_; uint8_t v_isShared_2475_; uint8_t v_isSharedCheck_2479_; 
v_isSharedCheck_2479_ = !lean_is_exclusive(v___x_2472_);
if (v_isSharedCheck_2479_ == 0)
{
lean_object* v_unused_2480_; 
v_unused_2480_ = lean_ctor_get(v___x_2472_, 0);
lean_dec(v_unused_2480_);
v___x_2474_ = v___x_2472_;
v_isShared_2475_ = v_isSharedCheck_2479_;
goto v_resetjp_2473_;
}
else
{
lean_dec(v___x_2472_);
v___x_2474_ = lean_box(0);
v_isShared_2475_ = v_isSharedCheck_2479_;
goto v_resetjp_2473_;
}
v_resetjp_2473_:
{
lean_object* v___x_2477_; 
if (v_isShared_2475_ == 0)
{
lean_ctor_set(v___x_2474_, 0, v_a_2449_);
v___x_2477_ = v___x_2474_;
goto v_reusejp_2476_;
}
else
{
lean_object* v_reuseFailAlloc_2478_; 
v_reuseFailAlloc_2478_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2478_, 0, v_a_2449_);
v___x_2477_ = v_reuseFailAlloc_2478_;
goto v_reusejp_2476_;
}
v_reusejp_2476_:
{
return v___x_2477_;
}
}
}
else
{
lean_object* v_a_2481_; lean_object* v___x_2483_; uint8_t v_isShared_2484_; uint8_t v_isSharedCheck_2488_; 
lean_dec_ref(v_a_2449_);
v_a_2481_ = lean_ctor_get(v___x_2472_, 0);
v_isSharedCheck_2488_ = !lean_is_exclusive(v___x_2472_);
if (v_isSharedCheck_2488_ == 0)
{
v___x_2483_ = v___x_2472_;
v_isShared_2484_ = v_isSharedCheck_2488_;
goto v_resetjp_2482_;
}
else
{
lean_inc(v_a_2481_);
lean_dec(v___x_2472_);
v___x_2483_ = lean_box(0);
v_isShared_2484_ = v_isSharedCheck_2488_;
goto v_resetjp_2482_;
}
v_resetjp_2482_:
{
lean_object* v___x_2486_; 
if (v_isShared_2484_ == 0)
{
v___x_2486_ = v___x_2483_;
goto v_reusejp_2485_;
}
else
{
lean_object* v_reuseFailAlloc_2487_; 
v_reuseFailAlloc_2487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2487_, 0, v_a_2481_);
v___x_2486_ = v_reuseFailAlloc_2487_;
goto v_reusejp_2485_;
}
v_reusejp_2485_:
{
return v___x_2486_;
}
}
}
}
else
{
lean_object* v___x_2489_; lean_object* v___x_2491_; 
lean_dec(v_a_2467_);
lean_dec(v_val_2465_);
lean_dec(v_val_2459_);
lean_dec_ref(v_a_2449_);
lean_dec_ref(v_arg_2119_);
lean_dec_ref(v_arg_2107_);
lean_dec_ref(v_arg_2104_);
lean_dec_ref(v_origExpr_2076_);
v___x_2489_ = lean_box(0);
if (v_isShared_2470_ == 0)
{
lean_ctor_set(v___x_2469_, 0, v___x_2489_);
v___x_2491_ = v___x_2469_;
goto v_reusejp_2490_;
}
else
{
lean_object* v_reuseFailAlloc_2492_; 
v_reuseFailAlloc_2492_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2492_, 0, v___x_2489_);
v___x_2491_ = v_reuseFailAlloc_2492_;
goto v_reusejp_2490_;
}
v_reusejp_2490_:
{
return v___x_2491_;
}
}
}
}
else
{
lean_dec(v_val_2465_);
lean_dec(v_val_2459_);
lean_dec_ref(v_a_2449_);
lean_dec_ref(v_arg_2119_);
lean_dec_ref(v_arg_2107_);
lean_dec_ref(v_arg_2104_);
lean_dec_ref(v_origExpr_2076_);
return v___x_2466_;
}
}
else
{
lean_object* v___x_2494_; lean_object* v___x_2496_; 
lean_dec(v_a_2461_);
lean_dec(v_val_2459_);
lean_dec_ref(v_a_2449_);
lean_dec_ref(v_arg_2119_);
lean_dec_ref(v_arg_2107_);
lean_dec_ref(v_arg_2104_);
lean_dec_ref(v_origExpr_2076_);
v___x_2494_ = lean_box(0);
if (v_isShared_2464_ == 0)
{
lean_ctor_set(v___x_2463_, 0, v___x_2494_);
v___x_2496_ = v___x_2463_;
goto v_reusejp_2495_;
}
else
{
lean_object* v_reuseFailAlloc_2497_; 
v_reuseFailAlloc_2497_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2497_, 0, v___x_2494_);
v___x_2496_ = v_reuseFailAlloc_2497_;
goto v_reusejp_2495_;
}
v_reusejp_2495_:
{
return v___x_2496_;
}
}
}
}
else
{
lean_dec(v_val_2459_);
lean_dec_ref(v_a_2449_);
lean_dec_ref(v_arg_2119_);
lean_dec_ref(v_arg_2107_);
lean_dec_ref(v_arg_2104_);
lean_dec_ref(v_origExpr_2076_);
return v___x_2460_;
}
}
else
{
lean_object* v___x_2499_; lean_object* v___x_2501_; 
lean_dec(v_a_2455_);
lean_dec_ref(v_a_2449_);
lean_dec_ref(v_arg_2119_);
lean_dec_ref(v_arg_2107_);
lean_dec_ref(v_arg_2104_);
lean_dec_ref(v_origExpr_2076_);
v___x_2499_ = lean_box(0);
if (v_isShared_2458_ == 0)
{
lean_ctor_set(v___x_2457_, 0, v___x_2499_);
v___x_2501_ = v___x_2457_;
goto v_reusejp_2500_;
}
else
{
lean_object* v_reuseFailAlloc_2502_; 
v_reuseFailAlloc_2502_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2502_, 0, v___x_2499_);
v___x_2501_ = v_reuseFailAlloc_2502_;
goto v_reusejp_2500_;
}
v_reusejp_2500_:
{
return v___x_2501_;
}
}
}
}
else
{
lean_object* v_a_2504_; lean_object* v___x_2506_; uint8_t v_isShared_2507_; uint8_t v_isSharedCheck_2511_; 
lean_dec_ref(v_a_2449_);
lean_dec_ref(v_arg_2119_);
lean_dec_ref(v_arg_2107_);
lean_dec_ref(v_arg_2104_);
lean_dec_ref(v_origExpr_2076_);
v_a_2504_ = lean_ctor_get(v___x_2454_, 0);
v_isSharedCheck_2511_ = !lean_is_exclusive(v___x_2454_);
if (v_isSharedCheck_2511_ == 0)
{
v___x_2506_ = v___x_2454_;
v_isShared_2507_ = v_isSharedCheck_2511_;
goto v_resetjp_2505_;
}
else
{
lean_inc(v_a_2504_);
lean_dec(v___x_2454_);
v___x_2506_ = lean_box(0);
v_isShared_2507_ = v_isSharedCheck_2511_;
goto v_resetjp_2505_;
}
v_resetjp_2505_:
{
lean_object* v___x_2509_; 
if (v_isShared_2507_ == 0)
{
v___x_2509_ = v___x_2506_;
goto v_reusejp_2508_;
}
else
{
lean_object* v_reuseFailAlloc_2510_; 
v_reuseFailAlloc_2510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2510_, 0, v_a_2504_);
v___x_2509_ = v_reuseFailAlloc_2510_;
goto v_reusejp_2508_;
}
v_reusejp_2508_:
{
return v___x_2509_;
}
}
}
}
else
{
lean_object* v___x_2512_; lean_object* v___x_2514_; 
lean_dec(v_a_2449_);
lean_dec_ref(v_arg_2119_);
lean_dec_ref(v_arg_2107_);
lean_dec_ref(v_arg_2104_);
lean_dec_ref(v_origExpr_2076_);
v___x_2512_ = lean_box(0);
if (v_isShared_2452_ == 0)
{
lean_ctor_set(v___x_2451_, 0, v___x_2512_);
v___x_2514_ = v___x_2451_;
goto v_reusejp_2513_;
}
else
{
lean_object* v_reuseFailAlloc_2515_; 
v_reuseFailAlloc_2515_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2515_, 0, v___x_2512_);
v___x_2514_ = v_reuseFailAlloc_2515_;
goto v_reusejp_2513_;
}
v_reusejp_2513_:
{
return v___x_2514_;
}
}
}
}
else
{
lean_dec_ref(v_arg_2119_);
lean_dec_ref(v_arg_2107_);
lean_dec_ref(v_arg_2104_);
lean_dec_ref(v_origExpr_2076_);
return v___x_2448_;
}
}
}
}
else
{
lean_object* v___x_2517_; lean_object* v___x_2518_; lean_object* v___x_2519_; 
lean_dec_ref(v___x_2120_);
lean_dec_ref(v_arg_2119_);
lean_dec_ref(v_arg_2107_);
lean_del_object(v___x_2095_);
v___x_2517_ = lean_box(0);
v___x_2518_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__81));
v___x_2519_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection(v_arg_2104_, v___x_2517_, v___x_2518_, v_origExpr_2076_, v_a_2077_, v_a_2078_, v_a_2079_, v_a_2080_, v_a_2081_, v_a_2082_);
return v___x_2519_;
}
}
else
{
lean_object* v___x_2520_; 
lean_dec_ref(v___x_2120_);
lean_dec_ref(v_arg_2119_);
lean_del_object(v___x_2095_);
v___x_2520_ = l_Lean_Meta_getNatValue_x3f(v_arg_2104_, v_a_2079_, v_a_2080_, v_a_2081_, v_a_2082_);
lean_dec_ref(v_arg_2104_);
if (lean_obj_tag(v___x_2520_) == 0)
{
lean_object* v_a_2521_; lean_object* v___x_2523_; uint8_t v_isShared_2524_; uint8_t v_isSharedCheck_2534_; 
v_a_2521_ = lean_ctor_get(v___x_2520_, 0);
v_isSharedCheck_2534_ = !lean_is_exclusive(v___x_2520_);
if (v_isSharedCheck_2534_ == 0)
{
v___x_2523_ = v___x_2520_;
v_isShared_2524_ = v_isSharedCheck_2534_;
goto v_resetjp_2522_;
}
else
{
lean_inc(v_a_2521_);
lean_dec(v___x_2520_);
v___x_2523_ = lean_box(0);
v_isShared_2524_ = v_isSharedCheck_2534_;
goto v_resetjp_2522_;
}
v_resetjp_2522_:
{
if (lean_obj_tag(v_a_2521_) == 1)
{
lean_object* v_val_2525_; lean_object* v___f_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; lean_object* v___x_2529_; 
lean_del_object(v___x_2523_);
v_val_2525_ = lean_ctor_get(v_a_2521_, 0);
lean_inc(v_val_2525_);
lean_dec_ref(v_a_2521_);
v___f_2526_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__82));
v___x_2527_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__11));
v___x_2528_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__84));
v___x_2529_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection(v_val_2525_, v_arg_2107_, v___f_2526_, v___x_2527_, v___x_2528_, v_origExpr_2076_, v_a_2077_, v_a_2078_, v_a_2079_, v_a_2080_, v_a_2081_, v_a_2082_);
return v___x_2529_;
}
else
{
lean_object* v___x_2530_; lean_object* v___x_2532_; 
lean_dec(v_a_2521_);
lean_dec_ref(v_arg_2107_);
lean_dec_ref(v_origExpr_2076_);
v___x_2530_ = lean_box(0);
if (v_isShared_2524_ == 0)
{
lean_ctor_set(v___x_2523_, 0, v___x_2530_);
v___x_2532_ = v___x_2523_;
goto v_reusejp_2531_;
}
else
{
lean_object* v_reuseFailAlloc_2533_; 
v_reuseFailAlloc_2533_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2533_, 0, v___x_2530_);
v___x_2532_ = v_reuseFailAlloc_2533_;
goto v_reusejp_2531_;
}
v_reusejp_2531_:
{
return v___x_2532_;
}
}
}
}
else
{
lean_object* v_a_2535_; lean_object* v___x_2537_; uint8_t v_isShared_2538_; uint8_t v_isSharedCheck_2542_; 
lean_dec_ref(v_arg_2107_);
lean_dec_ref(v_origExpr_2076_);
v_a_2535_ = lean_ctor_get(v___x_2520_, 0);
v_isSharedCheck_2542_ = !lean_is_exclusive(v___x_2520_);
if (v_isSharedCheck_2542_ == 0)
{
v___x_2537_ = v___x_2520_;
v_isShared_2538_ = v_isSharedCheck_2542_;
goto v_resetjp_2536_;
}
else
{
lean_inc(v_a_2535_);
lean_dec(v___x_2520_);
v___x_2537_ = lean_box(0);
v_isShared_2538_ = v_isSharedCheck_2542_;
goto v_resetjp_2536_;
}
v_resetjp_2536_:
{
lean_object* v___x_2540_; 
if (v_isShared_2538_ == 0)
{
v___x_2540_ = v___x_2537_;
goto v_reusejp_2539_;
}
else
{
lean_object* v_reuseFailAlloc_2541_; 
v_reuseFailAlloc_2541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2541_, 0, v_a_2535_);
v___x_2540_ = v_reuseFailAlloc_2541_;
goto v_reusejp_2539_;
}
v_reusejp_2539_:
{
return v___x_2540_;
}
}
}
}
}
else
{
lean_object* v___x_2543_; 
lean_dec_ref(v___x_2120_);
lean_dec_ref(v_arg_2119_);
lean_del_object(v___x_2095_);
lean_inc_ref(v_arg_2104_);
v___x_2543_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_goOrAtom(v_arg_2104_, v_a_2077_, v_a_2078_, v_a_2079_, v_a_2080_, v_a_2081_, v_a_2082_);
if (lean_obj_tag(v___x_2543_) == 0)
{
lean_object* v_a_2544_; lean_object* v___x_2546_; uint8_t v_isShared_2547_; uint8_t v_isSharedCheck_2612_; 
v_a_2544_ = lean_ctor_get(v___x_2543_, 0);
v_isSharedCheck_2612_ = !lean_is_exclusive(v___x_2543_);
if (v_isSharedCheck_2612_ == 0)
{
v___x_2546_ = v___x_2543_;
v_isShared_2547_ = v_isSharedCheck_2612_;
goto v_resetjp_2545_;
}
else
{
lean_inc(v_a_2544_);
lean_dec(v___x_2543_);
v___x_2546_ = lean_box(0);
v_isShared_2547_ = v_isSharedCheck_2612_;
goto v_resetjp_2545_;
}
v_resetjp_2545_:
{
if (lean_obj_tag(v_a_2544_) == 1)
{
lean_object* v_val_2548_; lean_object* v___x_2549_; 
lean_del_object(v___x_2546_);
v_val_2548_ = lean_ctor_get(v_a_2544_, 0);
lean_inc(v_val_2548_);
lean_dec_ref(v_a_2544_);
v___x_2549_ = l_Lean_Meta_getNatValue_x3f(v_arg_2107_, v_a_2079_, v_a_2080_, v_a_2081_, v_a_2082_);
lean_dec_ref(v_arg_2107_);
if (lean_obj_tag(v___x_2549_) == 0)
{
lean_object* v_a_2550_; lean_object* v___x_2552_; uint8_t v_isShared_2553_; uint8_t v_isSharedCheck_2599_; 
v_a_2550_ = lean_ctor_get(v___x_2549_, 0);
v_isSharedCheck_2599_ = !lean_is_exclusive(v___x_2549_);
if (v_isSharedCheck_2599_ == 0)
{
v___x_2552_ = v___x_2549_;
v_isShared_2553_ = v_isSharedCheck_2599_;
goto v_resetjp_2551_;
}
else
{
lean_inc(v_a_2550_);
lean_dec(v___x_2549_);
v___x_2552_ = lean_box(0);
v_isShared_2553_ = v_isSharedCheck_2599_;
goto v_resetjp_2551_;
}
v_resetjp_2551_:
{
if (lean_obj_tag(v_a_2550_) == 1)
{
lean_object* v_val_2554_; lean_object* v___x_2556_; uint8_t v_isShared_2557_; uint8_t v_isSharedCheck_2594_; 
lean_del_object(v___x_2552_);
v_val_2554_ = lean_ctor_get(v_a_2550_, 0);
v_isSharedCheck_2594_ = !lean_is_exclusive(v_a_2550_);
if (v_isSharedCheck_2594_ == 0)
{
v___x_2556_ = v_a_2550_;
v_isShared_2557_ = v_isSharedCheck_2594_;
goto v_resetjp_2555_;
}
else
{
lean_inc(v_val_2554_);
lean_dec(v_a_2550_);
v___x_2556_ = lean_box(0);
v_isShared_2557_ = v_isSharedCheck_2594_;
goto v_resetjp_2555_;
}
v_resetjp_2555_:
{
lean_object* v_width_2558_; lean_object* v_bvExpr_2559_; lean_object* v_expr_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; 
v_width_2558_ = lean_ctor_get(v_val_2548_, 0);
lean_inc_n(v_width_2558_, 2);
v_bvExpr_2559_ = lean_ctor_get(v_val_2548_, 1);
v_expr_2560_ = lean_ctor_get(v_val_2548_, 4);
lean_inc_ref(v_expr_2560_);
v___x_2561_ = lean_nat_mul(v_width_2558_, v_val_2554_);
lean_inc_ref(v_bvExpr_2559_);
lean_inc(v_val_2554_);
lean_inc_n(v___x_2561_, 2);
v___x_2562_ = l_Std_Tactic_BVDecide_BVExpr_replicate___override___redArg(v_width_2558_, v___x_2561_, v_val_2554_, v_bvExpr_2559_);
v___x_2563_ = l_Lean_mkNatLit(v___x_2561_);
lean_inc_ref(v___x_2563_);
v___x_2564_ = l_Lean_Meta_mkEqRefl(v___x_2563_, v_a_2079_, v_a_2080_, v_a_2081_, v_a_2082_);
if (lean_obj_tag(v___x_2564_) == 0)
{
lean_object* v_a_2565_; lean_object* v___x_2567_; uint8_t v_isShared_2568_; uint8_t v_isSharedCheck_2585_; 
v_a_2565_ = lean_ctor_get(v___x_2564_, 0);
v_isSharedCheck_2585_ = !lean_is_exclusive(v___x_2564_);
if (v_isSharedCheck_2585_ == 0)
{
v___x_2567_ = v___x_2564_;
v_isShared_2568_ = v_isSharedCheck_2585_;
goto v_resetjp_2566_;
}
else
{
lean_inc(v_a_2565_);
lean_dec(v___x_2564_);
v___x_2567_ = lean_box(0);
v_isShared_2568_ = v_isSharedCheck_2585_;
goto v_resetjp_2566_;
}
v_resetjp_2566_:
{
lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___f_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2580_; 
v___x_2569_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0));
v___x_2570_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1));
v___x_2571_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2));
v___x_2572_ = lean_box(0);
v___x_2573_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__86, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__86_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__86);
lean_inc(v_width_2558_);
v___x_2574_ = l_Lean_mkNatLit(v_width_2558_);
v___x_2575_ = l_Lean_mkNatLit(v_val_2554_);
lean_inc_ref(v___x_2574_);
lean_inc_ref(v___x_2575_);
lean_inc_ref(v_expr_2560_);
v___f_2576_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___lam__3___boxed), 17, 11);
lean_closure_set(v___f_2576_, 0, v_width_2558_);
lean_closure_set(v___f_2576_, 1, v_expr_2560_);
lean_closure_set(v___f_2576_, 2, v_val_2548_);
lean_closure_set(v___f_2576_, 3, v___x_2569_);
lean_closure_set(v___f_2576_, 4, v___x_2570_);
lean_closure_set(v___f_2576_, 5, v___x_2571_);
lean_closure_set(v___f_2576_, 6, v___x_2109_);
lean_closure_set(v___f_2576_, 7, v___x_2572_);
lean_closure_set(v___f_2576_, 8, v___x_2575_);
lean_closure_set(v___f_2576_, 9, v___x_2574_);
lean_closure_set(v___f_2576_, 10, v_arg_2104_);
v___x_2577_ = l_Lean_mkApp5(v___x_2573_, v___x_2574_, v___x_2563_, v___x_2575_, v_expr_2560_, v_a_2565_);
v___x_2578_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2578_, 0, v___x_2561_);
lean_ctor_set(v___x_2578_, 1, v___x_2562_);
lean_ctor_set(v___x_2578_, 2, v_origExpr_2076_);
lean_ctor_set(v___x_2578_, 3, v___f_2576_);
lean_ctor_set(v___x_2578_, 4, v___x_2577_);
if (v_isShared_2557_ == 0)
{
lean_ctor_set(v___x_2556_, 0, v___x_2578_);
v___x_2580_ = v___x_2556_;
goto v_reusejp_2579_;
}
else
{
lean_object* v_reuseFailAlloc_2584_; 
v_reuseFailAlloc_2584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2584_, 0, v___x_2578_);
v___x_2580_ = v_reuseFailAlloc_2584_;
goto v_reusejp_2579_;
}
v_reusejp_2579_:
{
lean_object* v___x_2582_; 
if (v_isShared_2568_ == 0)
{
lean_ctor_set(v___x_2567_, 0, v___x_2580_);
v___x_2582_ = v___x_2567_;
goto v_reusejp_2581_;
}
else
{
lean_object* v_reuseFailAlloc_2583_; 
v_reuseFailAlloc_2583_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2583_, 0, v___x_2580_);
v___x_2582_ = v_reuseFailAlloc_2583_;
goto v_reusejp_2581_;
}
v_reusejp_2581_:
{
return v___x_2582_;
}
}
}
}
else
{
lean_object* v_a_2586_; lean_object* v___x_2588_; uint8_t v_isShared_2589_; uint8_t v_isSharedCheck_2593_; 
lean_dec_ref(v___x_2563_);
lean_dec_ref(v___x_2562_);
lean_dec(v___x_2561_);
lean_dec_ref(v_expr_2560_);
lean_dec(v_width_2558_);
lean_del_object(v___x_2556_);
lean_dec(v_val_2554_);
lean_dec(v_val_2548_);
lean_dec_ref(v_arg_2104_);
lean_dec_ref(v_origExpr_2076_);
v_a_2586_ = lean_ctor_get(v___x_2564_, 0);
v_isSharedCheck_2593_ = !lean_is_exclusive(v___x_2564_);
if (v_isSharedCheck_2593_ == 0)
{
v___x_2588_ = v___x_2564_;
v_isShared_2589_ = v_isSharedCheck_2593_;
goto v_resetjp_2587_;
}
else
{
lean_inc(v_a_2586_);
lean_dec(v___x_2564_);
v___x_2588_ = lean_box(0);
v_isShared_2589_ = v_isSharedCheck_2593_;
goto v_resetjp_2587_;
}
v_resetjp_2587_:
{
lean_object* v___x_2591_; 
if (v_isShared_2589_ == 0)
{
v___x_2591_ = v___x_2588_;
goto v_reusejp_2590_;
}
else
{
lean_object* v_reuseFailAlloc_2592_; 
v_reuseFailAlloc_2592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2592_, 0, v_a_2586_);
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
}
else
{
lean_object* v___x_2595_; lean_object* v___x_2597_; 
lean_dec(v_a_2550_);
lean_dec(v_val_2548_);
lean_dec_ref(v_arg_2104_);
lean_dec_ref(v_origExpr_2076_);
v___x_2595_ = lean_box(0);
if (v_isShared_2553_ == 0)
{
lean_ctor_set(v___x_2552_, 0, v___x_2595_);
v___x_2597_ = v___x_2552_;
goto v_reusejp_2596_;
}
else
{
lean_object* v_reuseFailAlloc_2598_; 
v_reuseFailAlloc_2598_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2598_, 0, v___x_2595_);
v___x_2597_ = v_reuseFailAlloc_2598_;
goto v_reusejp_2596_;
}
v_reusejp_2596_:
{
return v___x_2597_;
}
}
}
}
else
{
lean_object* v_a_2600_; lean_object* v___x_2602_; uint8_t v_isShared_2603_; uint8_t v_isSharedCheck_2607_; 
lean_dec(v_val_2548_);
lean_dec_ref(v_arg_2104_);
lean_dec_ref(v_origExpr_2076_);
v_a_2600_ = lean_ctor_get(v___x_2549_, 0);
v_isSharedCheck_2607_ = !lean_is_exclusive(v___x_2549_);
if (v_isSharedCheck_2607_ == 0)
{
v___x_2602_ = v___x_2549_;
v_isShared_2603_ = v_isSharedCheck_2607_;
goto v_resetjp_2601_;
}
else
{
lean_inc(v_a_2600_);
lean_dec(v___x_2549_);
v___x_2602_ = lean_box(0);
v_isShared_2603_ = v_isSharedCheck_2607_;
goto v_resetjp_2601_;
}
v_resetjp_2601_:
{
lean_object* v___x_2605_; 
if (v_isShared_2603_ == 0)
{
v___x_2605_ = v___x_2602_;
goto v_reusejp_2604_;
}
else
{
lean_object* v_reuseFailAlloc_2606_; 
v_reuseFailAlloc_2606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2606_, 0, v_a_2600_);
v___x_2605_ = v_reuseFailAlloc_2606_;
goto v_reusejp_2604_;
}
v_reusejp_2604_:
{
return v___x_2605_;
}
}
}
}
else
{
lean_object* v___x_2608_; lean_object* v___x_2610_; 
lean_dec(v_a_2544_);
lean_dec_ref(v_arg_2107_);
lean_dec_ref(v_arg_2104_);
lean_dec_ref(v_origExpr_2076_);
v___x_2608_ = lean_box(0);
if (v_isShared_2547_ == 0)
{
lean_ctor_set(v___x_2546_, 0, v___x_2608_);
v___x_2610_ = v___x_2546_;
goto v_reusejp_2609_;
}
else
{
lean_object* v_reuseFailAlloc_2611_; 
v_reuseFailAlloc_2611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2611_, 0, v___x_2608_);
v___x_2610_ = v_reuseFailAlloc_2611_;
goto v_reusejp_2609_;
}
v_reusejp_2609_:
{
return v___x_2610_;
}
}
}
}
else
{
lean_dec_ref(v_arg_2107_);
lean_dec_ref(v_arg_2104_);
lean_dec_ref(v_origExpr_2076_);
return v___x_2543_;
}
}
}
else
{
lean_object* v___f_2613_; lean_object* v___x_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; 
lean_dec_ref(v___x_2120_);
lean_dec_ref(v_arg_2119_);
lean_del_object(v___x_2095_);
v___f_2613_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__87));
v___x_2614_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__5));
v___x_2615_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__89));
v___x_2616_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_rotateReflection(v_arg_2104_, v_arg_2107_, v___f_2613_, v___x_2614_, v___x_2615_, v_origExpr_2076_, v_a_2077_, v_a_2078_, v_a_2079_, v_a_2080_, v_a_2081_, v_a_2082_);
lean_dec_ref(v_arg_2104_);
return v___x_2616_;
}
}
else
{
lean_object* v___f_2617_; lean_object* v___x_2618_; lean_object* v___x_2619_; lean_object* v___x_2620_; 
lean_dec_ref(v___x_2120_);
lean_dec_ref(v_arg_2119_);
lean_del_object(v___x_2095_);
v___f_2617_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__90));
v___x_2618_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__8));
v___x_2619_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__92));
v___x_2620_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_rotateReflection(v_arg_2104_, v_arg_2107_, v___f_2617_, v___x_2618_, v___x_2619_, v_origExpr_2076_, v_a_2077_, v_a_2078_, v_a_2079_, v_a_2080_, v_a_2081_, v_a_2082_);
lean_dec_ref(v_arg_2104_);
return v___x_2620_;
}
}
}
else
{
lean_object* v___x_2621_; 
lean_dec_ref(v___x_2108_);
lean_dec_ref(v_arg_2107_);
lean_dec_ref(v_arg_2104_);
lean_del_object(v___x_2095_);
v___x_2621_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_goBvLit(v_origExpr_2076_, v_a_2078_, v_a_2079_, v_a_2080_, v_a_2081_, v_a_2082_);
return v___x_2621_;
}
}
else
{
lean_object* v___x_2622_; lean_object* v___x_2623_; lean_object* v___x_2624_; 
lean_dec_ref(v___x_2108_);
lean_dec_ref(v_arg_2107_);
lean_del_object(v___x_2095_);
v___x_2622_ = lean_box(4);
v___x_2623_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__94));
v___x_2624_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection(v_arg_2104_, v___x_2622_, v___x_2623_, v_origExpr_2076_, v_a_2077_, v_a_2078_, v_a_2079_, v_a_2080_, v_a_2081_, v_a_2082_);
return v___x_2624_;
}
}
else
{
lean_object* v___x_2625_; lean_object* v___x_2626_; lean_object* v___x_2627_; 
lean_dec_ref(v___x_2108_);
lean_dec_ref(v_arg_2107_);
lean_del_object(v___x_2095_);
v___x_2625_ = lean_box(5);
v___x_2626_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__96));
v___x_2627_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection(v_arg_2104_, v___x_2625_, v___x_2626_, v_origExpr_2076_, v_a_2077_, v_a_2078_, v_a_2079_, v_a_2080_, v_a_2081_, v_a_2082_);
return v___x_2627_;
}
}
else
{
lean_object* v___x_2628_; lean_object* v___x_2629_; lean_object* v___x_2630_; 
lean_dec_ref(v___x_2108_);
lean_dec_ref(v_arg_2107_);
lean_del_object(v___x_2095_);
v___x_2628_ = lean_box(6);
v___x_2629_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__98));
v___x_2630_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection(v_arg_2104_, v___x_2628_, v___x_2629_, v_origExpr_2076_, v_a_2077_, v_a_2078_, v_a_2079_, v_a_2080_, v_a_2081_, v_a_2082_);
return v___x_2630_;
}
}
}
v___jp_2097_:
{
lean_object* v___x_2098_; lean_object* v___x_2100_; 
v___x_2098_ = lean_box(0);
if (v_isShared_2096_ == 0)
{
lean_ctor_set(v___x_2095_, 0, v___x_2098_);
v___x_2100_ = v___x_2095_;
goto v_reusejp_2099_;
}
else
{
lean_object* v_reuseFailAlloc_2101_; 
v_reuseFailAlloc_2101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2101_, 0, v___x_2098_);
v___x_2100_ = v_reuseFailAlloc_2101_;
goto v_reusejp_2099_;
}
v_reusejp_2099_:
{
return v___x_2100_;
}
}
}
}
else
{
lean_object* v_a_2632_; lean_object* v___x_2634_; uint8_t v_isShared_2635_; uint8_t v_isSharedCheck_2639_; 
lean_dec_ref(v_origExpr_2076_);
v_a_2632_ = lean_ctor_get(v___x_2092_, 0);
v_isSharedCheck_2639_ = !lean_is_exclusive(v___x_2092_);
if (v_isSharedCheck_2639_ == 0)
{
v___x_2634_ = v___x_2092_;
v_isShared_2635_ = v_isSharedCheck_2639_;
goto v_resetjp_2633_;
}
else
{
lean_inc(v_a_2632_);
lean_dec(v___x_2092_);
v___x_2634_ = lean_box(0);
v_isShared_2635_ = v_isSharedCheck_2639_;
goto v_resetjp_2633_;
}
v_resetjp_2633_:
{
lean_object* v___x_2637_; 
if (v_isShared_2635_ == 0)
{
v___x_2637_ = v___x_2634_;
goto v_reusejp_2636_;
}
else
{
lean_object* v_reuseFailAlloc_2638_; 
v_reuseFailAlloc_2638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2638_, 0, v_a_2632_);
v___x_2637_ = v_reuseFailAlloc_2638_;
goto v_reusejp_2636_;
}
v_reusejp_2636_:
{
return v___x_2637_;
}
}
}
}
else
{
lean_object* v_a_2640_; lean_object* v___x_2642_; uint8_t v_isShared_2643_; uint8_t v_isSharedCheck_2647_; 
lean_dec_ref(v_origExpr_2076_);
v_a_2640_ = lean_ctor_get(v___x_2091_, 0);
v_isSharedCheck_2647_ = !lean_is_exclusive(v___x_2091_);
if (v_isSharedCheck_2647_ == 0)
{
v___x_2642_ = v___x_2091_;
v_isShared_2643_ = v_isSharedCheck_2647_;
goto v_resetjp_2641_;
}
else
{
lean_inc(v_a_2640_);
lean_dec(v___x_2091_);
v___x_2642_ = lean_box(0);
v_isShared_2643_ = v_isSharedCheck_2647_;
goto v_resetjp_2641_;
}
v_resetjp_2641_:
{
lean_object* v___x_2645_; 
if (v_isShared_2643_ == 0)
{
v___x_2645_ = v___x_2642_;
goto v_reusejp_2644_;
}
else
{
lean_object* v_reuseFailAlloc_2646_; 
v_reuseFailAlloc_2646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2646_, 0, v_a_2640_);
v___x_2645_ = v_reuseFailAlloc_2646_;
goto v_reusejp_2644_;
}
v_reusejp_2644_:
{
return v___x_2645_;
}
}
}
v___jp_2084_:
{
lean_object* v___x_2085_; lean_object* v___x_2086_; 
v___x_2085_ = lean_box(0);
v___x_2086_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2086_, 0, v___x_2085_);
return v___x_2086_;
}
v___jp_2087_:
{
lean_object* v___x_2088_; lean_object* v___x_2089_; 
v___x_2088_ = lean_box(0);
v___x_2089_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2089_, 0, v___x_2088_);
return v___x_2089_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVExprCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_goOrAtom_spec__10(lean_object* v_e_2648_, lean_object* v_a_2649_, lean_object* v_a_2650_, lean_object* v_a_2651_, lean_object* v_a_2652_, lean_object* v_a_2653_, lean_object* v_a_2654_){
_start:
{
lean_object* v___y_2657_; lean_object* v___x_2680_; lean_object* v_bvExprCache_2681_; lean_object* v___x_2682_; 
v___x_2680_ = lean_st_ref_get(v_a_2649_);
v_bvExprCache_2681_ = lean_ctor_get(v___x_2680_, 1);
lean_inc_ref(v_bvExprCache_2681_);
lean_dec(v___x_2680_);
v___x_2682_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom_spec__2_spec__12___redArg(v_bvExprCache_2681_, v_e_2648_);
lean_dec_ref(v_bvExprCache_2681_);
if (lean_obj_tag(v___x_2682_) == 0)
{
lean_object* v___x_2683_; 
lean_inc_ref(v_e_2648_);
v___x_2683_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go(v_e_2648_, v_a_2649_, v_a_2650_, v_a_2651_, v_a_2652_, v_a_2653_, v_a_2654_);
if (lean_obj_tag(v___x_2683_) == 0)
{
lean_object* v_a_2684_; 
v_a_2684_ = lean_ctor_get(v___x_2683_, 0);
lean_inc(v_a_2684_);
if (lean_obj_tag(v_a_2684_) == 0)
{
uint8_t v___x_2685_; lean_object* v___x_2686_; 
lean_dec_ref(v___x_2683_);
v___x_2685_ = 0;
lean_inc_ref(v_e_2648_);
v___x_2686_ = l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_bitVecAtom(v_e_2648_, v___x_2685_, v_a_2650_, v_a_2651_, v_a_2652_, v_a_2653_, v_a_2654_);
v___y_2657_ = v___x_2686_;
goto v___jp_2656_;
}
else
{
lean_dec_ref(v_a_2684_);
v___y_2657_ = v___x_2683_;
goto v___jp_2656_;
}
}
else
{
v___y_2657_ = v___x_2683_;
goto v___jp_2656_;
}
}
else
{
lean_object* v_val_2687_; lean_object* v___x_2689_; uint8_t v_isShared_2690_; uint8_t v_isSharedCheck_2694_; 
lean_dec_ref(v_e_2648_);
v_val_2687_ = lean_ctor_get(v___x_2682_, 0);
v_isSharedCheck_2694_ = !lean_is_exclusive(v___x_2682_);
if (v_isSharedCheck_2694_ == 0)
{
v___x_2689_ = v___x_2682_;
v_isShared_2690_ = v_isSharedCheck_2694_;
goto v_resetjp_2688_;
}
else
{
lean_inc(v_val_2687_);
lean_dec(v___x_2682_);
v___x_2689_ = lean_box(0);
v_isShared_2690_ = v_isSharedCheck_2694_;
goto v_resetjp_2688_;
}
v_resetjp_2688_:
{
lean_object* v___x_2692_; 
if (v_isShared_2690_ == 0)
{
lean_ctor_set_tag(v___x_2689_, 0);
v___x_2692_ = v___x_2689_;
goto v_reusejp_2691_;
}
else
{
lean_object* v_reuseFailAlloc_2693_; 
v_reuseFailAlloc_2693_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2693_, 0, v_val_2687_);
v___x_2692_ = v_reuseFailAlloc_2693_;
goto v_reusejp_2691_;
}
v_reusejp_2691_:
{
return v___x_2692_;
}
}
}
v___jp_2656_:
{
if (lean_obj_tag(v___y_2657_) == 0)
{
lean_object* v_a_2658_; lean_object* v___x_2660_; uint8_t v_isShared_2661_; uint8_t v_isSharedCheck_2679_; 
v_a_2658_ = lean_ctor_get(v___y_2657_, 0);
v_isSharedCheck_2679_ = !lean_is_exclusive(v___y_2657_);
if (v_isSharedCheck_2679_ == 0)
{
v___x_2660_ = v___y_2657_;
v_isShared_2661_ = v_isSharedCheck_2679_;
goto v_resetjp_2659_;
}
else
{
lean_inc(v_a_2658_);
lean_dec(v___y_2657_);
v___x_2660_ = lean_box(0);
v_isShared_2661_ = v_isSharedCheck_2679_;
goto v_resetjp_2659_;
}
v_resetjp_2659_:
{
lean_object* v___x_2662_; lean_object* v_lemmas_2663_; lean_object* v_bvExprCache_2664_; lean_object* v_bvPredCache_2665_; lean_object* v_bvLogicalCache_2666_; lean_object* v___x_2668_; uint8_t v_isShared_2669_; uint8_t v_isSharedCheck_2678_; 
v___x_2662_ = lean_st_ref_take(v_a_2649_);
v_lemmas_2663_ = lean_ctor_get(v___x_2662_, 0);
v_bvExprCache_2664_ = lean_ctor_get(v___x_2662_, 1);
v_bvPredCache_2665_ = lean_ctor_get(v___x_2662_, 2);
v_bvLogicalCache_2666_ = lean_ctor_get(v___x_2662_, 3);
v_isSharedCheck_2678_ = !lean_is_exclusive(v___x_2662_);
if (v_isSharedCheck_2678_ == 0)
{
v___x_2668_ = v___x_2662_;
v_isShared_2669_ = v_isSharedCheck_2678_;
goto v_resetjp_2667_;
}
else
{
lean_inc(v_bvLogicalCache_2666_);
lean_inc(v_bvPredCache_2665_);
lean_inc(v_bvExprCache_2664_);
lean_inc(v_lemmas_2663_);
lean_dec(v___x_2662_);
v___x_2668_ = lean_box(0);
v_isShared_2669_ = v_isSharedCheck_2678_;
goto v_resetjp_2667_;
}
v_resetjp_2667_:
{
lean_object* v___x_2670_; lean_object* v___x_2672_; 
lean_inc(v_a_2658_);
v___x_2670_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13___redArg(v_bvExprCache_2664_, v_e_2648_, v_a_2658_);
if (v_isShared_2669_ == 0)
{
lean_ctor_set(v___x_2668_, 1, v___x_2670_);
v___x_2672_ = v___x_2668_;
goto v_reusejp_2671_;
}
else
{
lean_object* v_reuseFailAlloc_2677_; 
v_reuseFailAlloc_2677_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2677_, 0, v_lemmas_2663_);
lean_ctor_set(v_reuseFailAlloc_2677_, 1, v___x_2670_);
lean_ctor_set(v_reuseFailAlloc_2677_, 2, v_bvPredCache_2665_);
lean_ctor_set(v_reuseFailAlloc_2677_, 3, v_bvLogicalCache_2666_);
v___x_2672_ = v_reuseFailAlloc_2677_;
goto v_reusejp_2671_;
}
v_reusejp_2671_:
{
lean_object* v___x_2673_; lean_object* v___x_2675_; 
v___x_2673_ = lean_st_ref_set(v_a_2649_, v___x_2672_);
if (v_isShared_2661_ == 0)
{
v___x_2675_ = v___x_2660_;
goto v_reusejp_2674_;
}
else
{
lean_object* v_reuseFailAlloc_2676_; 
v_reuseFailAlloc_2676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2676_, 0, v_a_2658_);
v___x_2675_ = v_reuseFailAlloc_2676_;
goto v_reusejp_2674_;
}
v_reusejp_2674_:
{
return v___x_2675_;
}
}
}
}
}
else
{
lean_dec_ref(v_e_2648_);
return v___y_2657_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_goOrAtom(lean_object* v_origExpr_2695_, lean_object* v_a_2696_, lean_object* v_a_2697_, lean_object* v_a_2698_, lean_object* v_a_2699_, lean_object* v_a_2700_, lean_object* v_a_2701_){
_start:
{
lean_object* v___x_2703_; 
v___x_2703_ = l_Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVExprCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_goOrAtom_spec__10(v_origExpr_2695_, v_a_2696_, v_a_2697_, v_a_2698_, v_a_2699_, v_a_2700_, v_a_2701_);
return v___x_2703_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of(lean_object* v_origExpr_2704_, lean_object* v_a_2705_, lean_object* v_a_2706_, lean_object* v_a_2707_, lean_object* v_a_2708_, lean_object* v_a_2709_, lean_object* v_a_2710_){
_start:
{
lean_object* v___x_2712_; 
v___x_2712_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_goOrAtom(v_origExpr_2704_, v_a_2705_, v_a_2706_, v_a_2707_, v_a_2708_, v_a_2709_, v_a_2710_);
return v___x_2712_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of___boxed(lean_object* v_origExpr_2713_, lean_object* v_a_2714_, lean_object* v_a_2715_, lean_object* v_a_2716_, lean_object* v_a_2717_, lean_object* v_a_2718_, lean_object* v_a_2719_, lean_object* v_a_2720_){
_start:
{
lean_object* v_res_2721_; 
v_res_2721_ = l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of(v_origExpr_2713_, v_a_2714_, v_a_2715_, v_a_2716_, v_a_2717_, v_a_2718_, v_a_2719_);
lean_dec(v_a_2719_);
lean_dec_ref(v_a_2718_);
lean_dec(v_a_2717_);
lean_dec_ref(v_a_2716_);
lean_dec(v_a_2715_);
lean_dec(v_a_2714_);
return v_res_2721_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of___boxed(lean_object* v_origExpr_2722_, lean_object* v_a_2723_, lean_object* v_a_2724_, lean_object* v_a_2725_, lean_object* v_a_2726_, lean_object* v_a_2727_, lean_object* v_a_2728_, lean_object* v_a_2729_){
_start:
{
lean_object* v_res_2730_; 
v_res_2730_ = l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of(v_origExpr_2722_, v_a_2723_, v_a_2724_, v_a_2725_, v_a_2726_, v_a_2727_, v_a_2728_);
lean_dec(v_a_2728_);
lean_dec_ref(v_a_2727_);
lean_dec(v_a_2726_);
lean_dec_ref(v_a_2725_);
lean_dec(v_a_2724_);
lean_dec(v_a_2723_);
return v_res_2730_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_of___boxed(lean_object* v_origExpr_2731_, lean_object* v_a_2732_, lean_object* v_a_2733_, lean_object* v_a_2734_, lean_object* v_a_2735_, lean_object* v_a_2736_, lean_object* v_a_2737_, lean_object* v_a_2738_){
_start:
{
lean_object* v_res_2739_; 
v_res_2739_ = l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_of(v_origExpr_2731_, v_a_2732_, v_a_2733_, v_a_2734_, v_a_2735_, v_a_2736_, v_a_2737_);
lean_dec(v_a_2737_);
lean_dec_ref(v_a_2736_);
lean_dec(v_a_2735_);
lean_dec_ref(v_a_2734_);
lean_dec(v_a_2733_);
lean_dec(v_a_2732_);
return v_res_2739_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_goOrAtom___boxed(lean_object* v_origExpr_2740_, lean_object* v_a_2741_, lean_object* v_a_2742_, lean_object* v_a_2743_, lean_object* v_a_2744_, lean_object* v_a_2745_, lean_object* v_a_2746_, lean_object* v_a_2747_){
_start:
{
lean_object* v_res_2748_; 
v_res_2748_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_goOrAtom(v_origExpr_2740_, v_a_2741_, v_a_2742_, v_a_2743_, v_a_2744_, v_a_2745_, v_a_2746_);
lean_dec(v_a_2746_);
lean_dec_ref(v_a_2745_);
lean_dec(v_a_2744_);
lean_dec_ref(v_a_2743_);
lean_dec(v_a_2742_);
lean_dec(v_a_2741_);
return v_res_2748_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom___boxed(lean_object* v_origExpr_2749_, lean_object* v_a_2750_, lean_object* v_a_2751_, lean_object* v_a_2752_, lean_object* v_a_2753_, lean_object* v_a_2754_, lean_object* v_a_2755_, lean_object* v_a_2756_){
_start:
{
lean_object* v_res_2757_; 
v_res_2757_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom(v_origExpr_2749_, v_a_2750_, v_a_2751_, v_a_2752_, v_a_2753_, v_a_2754_, v_a_2755_);
lean_dec(v_a_2755_);
lean_dec_ref(v_a_2754_);
lean_dec(v_a_2753_);
lean_dec_ref(v_a_2752_);
lean_dec(v_a_2751_);
lean_dec(v_a_2750_);
return v_res_2757_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_rotateReflection___boxed(lean_object* v_distanceExpr_2758_, lean_object* v_innerExpr_2759_, lean_object* v_rotateOp_2760_, lean_object* v_rotateOpName_2761_, lean_object* v_congrThm_2762_, lean_object* v_origExpr_2763_, lean_object* v_a_2764_, lean_object* v_a_2765_, lean_object* v_a_2766_, lean_object* v_a_2767_, lean_object* v_a_2768_, lean_object* v_a_2769_, lean_object* v_a_2770_){
_start:
{
lean_object* v_res_2771_; 
v_res_2771_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_rotateReflection(v_distanceExpr_2758_, v_innerExpr_2759_, v_rotateOp_2760_, v_rotateOpName_2761_, v_congrThm_2762_, v_origExpr_2763_, v_a_2764_, v_a_2765_, v_a_2766_, v_a_2767_, v_a_2768_, v_a_2769_);
lean_dec(v_a_2769_);
lean_dec_ref(v_a_2768_);
lean_dec(v_a_2767_);
lean_dec_ref(v_a_2766_);
lean_dec(v_a_2765_);
lean_dec(v_a_2764_);
lean_dec_ref(v_distanceExpr_2758_);
return v_res_2771_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goPred___boxed(lean_object* v_origExpr_2772_, lean_object* v_a_2773_, lean_object* v_a_2774_, lean_object* v_a_2775_, lean_object* v_a_2776_, lean_object* v_a_2777_, lean_object* v_a_2778_, lean_object* v_a_2779_){
_start:
{
lean_object* v_res_2780_; 
v_res_2780_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goPred(v_origExpr_2772_, v_a_2773_, v_a_2774_, v_a_2775_, v_a_2776_, v_a_2777_, v_a_2778_);
lean_dec(v_a_2778_);
lean_dec_ref(v_a_2777_);
lean_dec(v_a_2776_);
lean_dec_ref(v_a_2775_);
lean_dec(v_a_2774_);
lean_dec(v_a_2773_);
return v_res_2780_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_of_binaryReflection___boxed(lean_object* v_lhsExpr_2781_, lean_object* v_rhsExpr_2782_, lean_object* v_pred_2783_, lean_object* v_origExpr_2784_, lean_object* v_a_2785_, lean_object* v_a_2786_, lean_object* v_a_2787_, lean_object* v_a_2788_, lean_object* v_a_2789_, lean_object* v_a_2790_, lean_object* v_a_2791_){
_start:
{
uint8_t v_pred_boxed_2792_; lean_object* v_res_2793_; 
v_pred_boxed_2792_ = lean_unbox(v_pred_2783_);
v_res_2793_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_of_binaryReflection(v_lhsExpr_2781_, v_rhsExpr_2782_, v_pred_boxed_2792_, v_origExpr_2784_, v_a_2785_, v_a_2786_, v_a_2787_, v_a_2788_, v_a_2789_, v_a_2790_);
lean_dec(v_a_2790_);
lean_dec_ref(v_a_2789_);
lean_dec(v_a_2788_);
lean_dec_ref(v_a_2787_);
lean_dec(v_a_2786_);
lean_dec(v_a_2785_);
return v_res_2793_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_gateReflection___boxed(lean_object* v_lhsExpr_2794_, lean_object* v_rhsExpr_2795_, lean_object* v_gate_2796_, lean_object* v_origExpr_2797_, lean_object* v_a_2798_, lean_object* v_a_2799_, lean_object* v_a_2800_, lean_object* v_a_2801_, lean_object* v_a_2802_, lean_object* v_a_2803_, lean_object* v_a_2804_){
_start:
{
uint8_t v_gate_boxed_2805_; lean_object* v_res_2806_; 
v_gate_boxed_2805_ = lean_unbox(v_gate_2796_);
v_res_2806_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_gateReflection(v_lhsExpr_2794_, v_rhsExpr_2795_, v_gate_boxed_2805_, v_origExpr_2797_, v_a_2798_, v_a_2799_, v_a_2800_, v_a_2801_, v_a_2802_, v_a_2803_);
lean_dec(v_a_2803_);
lean_dec_ref(v_a_2802_);
lean_dec(v_a_2801_);
lean_dec_ref(v_a_2800_);
lean_dec(v_a_2799_);
lean_dec(v_a_2798_);
return v_res_2806_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___boxed(lean_object* v_distance_2807_, lean_object* v_innerExpr_2808_, lean_object* v_shiftOp_2809_, lean_object* v_shiftOpName_2810_, lean_object* v_congrThm_2811_, lean_object* v_origExpr_2812_, lean_object* v_a_2813_, lean_object* v_a_2814_, lean_object* v_a_2815_, lean_object* v_a_2816_, lean_object* v_a_2817_, lean_object* v_a_2818_, lean_object* v_a_2819_){
_start:
{
lean_object* v_res_2820_; 
v_res_2820_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection(v_distance_2807_, v_innerExpr_2808_, v_shiftOp_2809_, v_shiftOpName_2810_, v_congrThm_2811_, v_origExpr_2812_, v_a_2813_, v_a_2814_, v_a_2815_, v_a_2816_, v_a_2817_, v_a_2818_);
lean_dec(v_a_2818_);
lean_dec_ref(v_a_2817_);
lean_dec(v_a_2816_);
lean_dec_ref(v_a_2815_);
lean_dec(v_a_2814_);
lean_dec(v_a_2813_);
return v_res_2820_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftReflection___boxed(lean_object* v_distanceExpr_2821_, lean_object* v_innerExpr_2822_, lean_object* v_shiftOp_2823_, lean_object* v_shiftOpName_2824_, lean_object* v_congrThm_2825_, lean_object* v_origExpr_2826_, lean_object* v_a_2827_, lean_object* v_a_2828_, lean_object* v_a_2829_, lean_object* v_a_2830_, lean_object* v_a_2831_, lean_object* v_a_2832_, lean_object* v_a_2833_){
_start:
{
lean_object* v_res_2834_; 
v_res_2834_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftReflection(v_distanceExpr_2821_, v_innerExpr_2822_, v_shiftOp_2823_, v_shiftOpName_2824_, v_congrThm_2825_, v_origExpr_2826_, v_a_2827_, v_a_2828_, v_a_2829_, v_a_2830_, v_a_2831_, v_a_2832_);
lean_dec(v_a_2832_);
lean_dec_ref(v_a_2831_);
lean_dec(v_a_2830_);
lean_dec_ref(v_a_2829_);
lean_dec(v_a_2828_);
lean_dec(v_a_2827_);
return v_res_2834_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom_spec__2___boxed(lean_object* v_e_2835_, lean_object* v_a_2836_, lean_object* v_a_2837_, lean_object* v_a_2838_, lean_object* v_a_2839_, lean_object* v_a_2840_, lean_object* v_a_2841_, lean_object* v_a_2842_){
_start:
{
lean_object* v_res_2843_; 
v_res_2843_ = l_Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom_spec__2(v_e_2835_, v_a_2836_, v_a_2837_, v_a_2838_, v_a_2839_, v_a_2840_, v_a_2841_);
lean_dec(v_a_2841_);
lean_dec_ref(v_a_2840_);
lean_dec(v_a_2839_);
lean_dec_ref(v_a_2838_);
lean_dec(v_a_2837_);
lean_dec(v_a_2836_);
return v_res_2843_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVPredCache___at___00Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_of_spec__5___boxed(lean_object* v_e_2844_, lean_object* v_a_2845_, lean_object* v_a_2846_, lean_object* v_a_2847_, lean_object* v_a_2848_, lean_object* v_a_2849_, lean_object* v_a_2850_, lean_object* v_a_2851_){
_start:
{
lean_object* v_res_2852_; 
v_res_2852_ = l_Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVPredCache___at___00Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_of_spec__5(v_e_2844_, v_a_2845_, v_a_2846_, v_a_2847_, v_a_2848_, v_a_2849_, v_a_2850_);
lean_dec(v_a_2850_);
lean_dec_ref(v_a_2849_);
lean_dec(v_a_2848_);
lean_dec_ref(v_a_2847_);
lean_dec(v_a_2846_);
lean_dec(v_a_2845_);
return v_res_2852_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVExprCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_goOrAtom_spec__10___boxed(lean_object* v_e_2853_, lean_object* v_a_2854_, lean_object* v_a_2855_, lean_object* v_a_2856_, lean_object* v_a_2857_, lean_object* v_a_2858_, lean_object* v_a_2859_, lean_object* v_a_2860_){
_start:
{
lean_object* v_res_2861_; 
v_res_2861_ = l_Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVExprCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_goOrAtom_spec__10(v_e_2853_, v_a_2854_, v_a_2855_, v_a_2856_, v_a_2857_, v_a_2858_, v_a_2859_);
lean_dec(v_a_2859_);
lean_dec_ref(v_a_2858_);
lean_dec(v_a_2857_);
lean_dec_ref(v_a_2856_);
lean_dec(v_a_2855_);
lean_dec(v_a_2854_);
return v_res_2861_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___boxed(lean_object* v_innerExpr_2862_, lean_object* v_op_2863_, lean_object* v_congrThm_2864_, lean_object* v_origExpr_2865_, lean_object* v_a_2866_, lean_object* v_a_2867_, lean_object* v_a_2868_, lean_object* v_a_2869_, lean_object* v_a_2870_, lean_object* v_a_2871_, lean_object* v_a_2872_){
_start:
{
lean_object* v_res_2873_; 
v_res_2873_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection(v_innerExpr_2862_, v_op_2863_, v_congrThm_2864_, v_origExpr_2865_, v_a_2866_, v_a_2867_, v_a_2868_, v_a_2869_, v_a_2870_, v_a_2871_);
lean_dec(v_a_2871_);
lean_dec_ref(v_a_2870_);
lean_dec(v_a_2869_);
lean_dec_ref(v_a_2868_);
lean_dec(v_a_2867_);
lean_dec(v_a_2866_);
return v_res_2873_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___boxed(lean_object* v_lhsExpr_2874_, lean_object* v_rhsExpr_2875_, lean_object* v_op_2876_, lean_object* v_congrThm_2877_, lean_object* v_origExpr_2878_, lean_object* v_a_2879_, lean_object* v_a_2880_, lean_object* v_a_2881_, lean_object* v_a_2882_, lean_object* v_a_2883_, lean_object* v_a_2884_, lean_object* v_a_2885_){
_start:
{
uint8_t v_op_boxed_2886_; lean_object* v_res_2887_; 
v_op_boxed_2886_ = lean_unbox(v_op_2876_);
v_res_2887_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection(v_lhsExpr_2874_, v_rhsExpr_2875_, v_op_boxed_2886_, v_congrThm_2877_, v_origExpr_2878_, v_a_2879_, v_a_2880_, v_a_2881_, v_a_2882_, v_a_2883_, v_a_2884_);
lean_dec(v_a_2884_);
lean_dec_ref(v_a_2883_);
lean_dec(v_a_2882_);
lean_dec_ref(v_a_2881_);
lean_dec(v_a_2880_);
lean_dec(v_a_2879_);
return v_res_2887_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_of_go___boxed(lean_object* v_origExpr_2888_, lean_object* v_a_2889_, lean_object* v_a_2890_, lean_object* v_a_2891_, lean_object* v_a_2892_, lean_object* v_a_2893_, lean_object* v_a_2894_, lean_object* v_a_2895_){
_start:
{
lean_object* v_res_2896_; 
v_res_2896_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_of_go(v_origExpr_2888_, v_a_2889_, v_a_2890_, v_a_2891_, v_a_2892_, v_a_2893_, v_a_2894_);
lean_dec(v_a_2894_);
lean_dec_ref(v_a_2893_);
lean_dec(v_a_2892_);
lean_dec_ref(v_a_2891_);
lean_dec(v_a_2890_);
lean_dec(v_a_2889_);
return v_res_2896_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_go___boxed(lean_object* v_origExpr_2897_, lean_object* v_a_2898_, lean_object* v_a_2899_, lean_object* v_a_2900_, lean_object* v_a_2901_, lean_object* v_a_2902_, lean_object* v_a_2903_, lean_object* v_a_2904_){
_start:
{
lean_object* v_res_2905_; 
v_res_2905_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_go(v_origExpr_2897_, v_a_2898_, v_a_2899_, v_a_2900_, v_a_2901_, v_a_2902_, v_a_2903_);
lean_dec(v_a_2903_);
lean_dec_ref(v_a_2902_);
lean_dec(v_a_2901_);
lean_dec_ref(v_a_2900_);
lean_dec(v_a_2899_);
lean_dec(v_a_2898_);
return v_res_2905_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___boxed(lean_object* v_origExpr_2906_, lean_object* v_a_2907_, lean_object* v_a_2908_, lean_object* v_a_2909_, lean_object* v_a_2910_, lean_object* v_a_2911_, lean_object* v_a_2912_, lean_object* v_a_2913_){
_start:
{
lean_object* v_res_2914_; 
v_res_2914_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go(v_origExpr_2906_, v_a_2907_, v_a_2908_, v_a_2909_, v_a_2910_, v_a_2911_, v_a_2912_);
lean_dec(v_a_2912_);
lean_dec_ref(v_a_2911_);
lean_dec(v_a_2910_);
lean_dec_ref(v_a_2909_);
lean_dec(v_a_2908_);
lean_dec(v_a_2907_);
return v_res_2914_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go_spec__12(lean_object* v_00_u03b1_2915_, lean_object* v_msg_2916_, lean_object* v___y_2917_, lean_object* v___y_2918_, lean_object* v___y_2919_, lean_object* v___y_2920_, lean_object* v___y_2921_, lean_object* v___y_2922_){
_start:
{
lean_object* v___x_2924_; 
v___x_2924_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go_spec__12___redArg(v_msg_2916_, v___y_2919_, v___y_2920_, v___y_2921_, v___y_2922_);
return v___x_2924_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go_spec__12___boxed(lean_object* v_00_u03b1_2925_, lean_object* v_msg_2926_, lean_object* v___y_2927_, lean_object* v___y_2928_, lean_object* v___y_2929_, lean_object* v___y_2930_, lean_object* v___y_2931_, lean_object* v___y_2932_, lean_object* v___y_2933_){
_start:
{
lean_object* v_res_2934_; 
v_res_2934_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go_spec__12(v_00_u03b1_2925_, v_msg_2926_, v___y_2927_, v___y_2928_, v___y_2929_, v___y_2930_, v___y_2931_, v___y_2932_);
lean_dec(v___y_2932_);
lean_dec_ref(v___y_2931_);
lean_dec(v___y_2930_);
lean_dec_ref(v___y_2929_);
lean_dec(v___y_2928_);
lean_dec(v___y_2927_);
return v_res_2934_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom_spec__2_spec__12(lean_object* v_00_u03b2_2935_, lean_object* v_m_2936_, lean_object* v_a_2937_){
_start:
{
lean_object* v___x_2938_; 
v___x_2938_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom_spec__2_spec__12___redArg(v_m_2936_, v_a_2937_);
return v___x_2938_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom_spec__2_spec__12___boxed(lean_object* v_00_u03b2_2939_, lean_object* v_m_2940_, lean_object* v_a_2941_){
_start:
{
lean_object* v_res_2942_; 
v_res_2942_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom_spec__2_spec__12(v_00_u03b2_2939_, v_m_2940_, v_a_2941_);
lean_dec_ref(v_a_2941_);
lean_dec_ref(v_m_2940_);
return v_res_2942_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13(lean_object* v_00_u03b2_2943_, lean_object* v_m_2944_, lean_object* v_a_2945_, lean_object* v_b_2946_){
_start:
{
lean_object* v___x_2947_; 
v___x_2947_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13___redArg(v_m_2944_, v_a_2945_, v_b_2946_);
return v___x_2947_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom_spec__2_spec__12_spec__17(lean_object* v_00_u03b2_2948_, lean_object* v_a_2949_, lean_object* v_x_2950_){
_start:
{
lean_object* v___x_2951_; 
v___x_2951_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom_spec__2_spec__12_spec__17___redArg(v_a_2949_, v_x_2950_);
return v___x_2951_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom_spec__2_spec__12_spec__17___boxed(lean_object* v_00_u03b2_2952_, lean_object* v_a_2953_, lean_object* v_x_2954_){
_start:
{
lean_object* v_res_2955_; 
v_res_2955_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom_spec__2_spec__12_spec__17(v_00_u03b2_2952_, v_a_2953_, v_x_2954_);
lean_dec(v_x_2954_);
lean_dec_ref(v_a_2953_);
return v_res_2955_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13_spec__19(lean_object* v_00_u03b2_2956_, lean_object* v_a_2957_, lean_object* v_x_2958_){
_start:
{
uint8_t v___x_2959_; 
v___x_2959_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13_spec__19___redArg(v_a_2957_, v_x_2958_);
return v___x_2959_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13_spec__19___boxed(lean_object* v_00_u03b2_2960_, lean_object* v_a_2961_, lean_object* v_x_2962_){
_start:
{
uint8_t v_res_2963_; lean_object* v_r_2964_; 
v_res_2963_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13_spec__19(v_00_u03b2_2960_, v_a_2961_, v_x_2962_);
lean_dec(v_x_2962_);
lean_dec_ref(v_a_2961_);
v_r_2964_ = lean_box(v_res_2963_);
return v_r_2964_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13_spec__20(lean_object* v_00_u03b2_2965_, lean_object* v_data_2966_){
_start:
{
lean_object* v___x_2967_; 
v___x_2967_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13_spec__20___redArg(v_data_2966_);
return v___x_2967_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13_spec__21(lean_object* v_00_u03b2_2968_, lean_object* v_a_2969_, lean_object* v_b_2970_, lean_object* v_x_2971_){
_start:
{
lean_object* v___x_2972_; 
v___x_2972_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13_spec__21___redArg(v_a_2969_, v_b_2970_, v_x_2971_);
return v___x_2972_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13_spec__20_spec__25(lean_object* v_00_u03b2_2973_, lean_object* v_i_2974_, lean_object* v_source_2975_, lean_object* v_target_2976_){
_start:
{
lean_object* v___x_2977_; 
v___x_2977_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13_spec__20_spec__25___redArg(v_i_2974_, v_source_2975_, v_target_2976_);
return v___x_2977_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13_spec__20_spec__25_spec__26(lean_object* v_00_u03b2_2978_, lean_object* v_x_2979_, lean_object* v_x_2980_){
_start:
{
lean_object* v___x_2981_; 
v___x_2981_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13_spec__20_spec__25_spec__26___redArg(v_x_2979_, v_x_2980_);
return v___x_2981_;
}
}
lean_object* runtime_initialize_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_LitValues(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_LitValues(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas(uint8_t builtin);
lean_object* initialize_Lean_Meta_LitValues(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_LitValues(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify(builtin);
}
#ifdef __cplusplus
}
#endif
