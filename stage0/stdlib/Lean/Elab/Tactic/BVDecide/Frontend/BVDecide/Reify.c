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
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_go___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "cond"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_go___closed__8 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_go___closed__8_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_go___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_go___closed__8_value),LEAN_SCALAR_PTR_LITERAL(130, 140, 200, 235, 144, 197, 118, 1)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_go___closed__9 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_go___closed__9_value;
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
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_go___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_go___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_go___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Bool"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_go___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_go___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_go___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_go___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_go___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_go___closed__1_value),LEAN_SCALAR_PTR_LITERAL(117, 151, 161, 190, 111, 237, 188, 218)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_go___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_go___closed__2_value;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_go___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_go___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_go___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_go___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_go___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_go___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_go___closed__3_value),LEAN_SCALAR_PTR_LITERAL(22, 245, 194, 28, 184, 9, 113, 128)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_go___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_go___closed__4_value;
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
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_go___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_go___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_go___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__1_value),LEAN_SCALAR_PTR_LITERAL(208, 215, 171, 150, 192, 180, 249, 22)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_go___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_go___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_go___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_go___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_go___closed__6_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__10_value),LEAN_SCALAR_PTR_LITERAL(159, 35, 146, 118, 24, 65, 174, 144)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_go___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_go___closed__6_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_go___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_go___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_go___closed__7_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__4_value),LEAN_SCALAR_PTR_LITERAL(160, 26, 8, 228, 104, 32, 82, 85)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_go___closed__7 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_go___closed__7_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_go___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_go___closed__10 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_go___closed__10_value;
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
lean_inc(v_width_102_);
v_expr_103_ = lean_ctor_get(v_lhs_91_, 4);
lean_inc_ref(v_expr_103_);
lean_inc(v_width_102_);
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
lean_inc(v_width_174_);
v_expr_175_ = lean_ctor_get(v_inner_165_, 4);
lean_inc_ref(v_expr_175_);
lean_inc(v_width_174_);
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
lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; 
v___x_821_ = lean_box(0);
v___x_822_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__1));
v___x_823_ = l_Lean_mkConst(v___x_822_, v___x_821_);
return v___x_823_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__6(void){
_start:
{
lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; 
v___x_832_ = lean_box(0);
v___x_833_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__5));
v___x_834_ = l_Lean_mkConst(v___x_833_, v___x_832_);
return v___x_834_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__9(void){
_start:
{
lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; 
v___x_842_ = lean_box(0);
v___x_843_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__8));
v___x_844_ = l_Lean_mkConst(v___x_843_, v___x_842_);
return v___x_844_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__12(void){
_start:
{
lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; 
v___x_852_ = lean_box(0);
v___x_853_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__11));
v___x_854_ = l_Lean_mkConst(v___x_853_, v___x_852_);
return v___x_854_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__15(void){
_start:
{
lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; 
v___x_862_ = lean_box(0);
v___x_863_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__14));
v___x_864_ = l_Lean_mkConst(v___x_863_, v___x_862_);
return v___x_864_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__18(void){
_start:
{
lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; 
v___x_872_ = lean_box(0);
v___x_873_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__17));
v___x_874_ = l_Lean_mkConst(v___x_873_, v___x_872_);
return v___x_874_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__21(void){
_start:
{
lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; 
v___x_882_ = lean_box(0);
v___x_883_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__20));
v___x_884_ = l_Lean_mkConst(v___x_883_, v___x_882_);
return v___x_884_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__24(void){
_start:
{
lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; 
v___x_892_ = lean_box(0);
v___x_893_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__23));
v___x_894_ = l_Lean_mkConst(v___x_893_, v___x_892_);
return v___x_894_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection(lean_object* v_lhsExpr_895_, lean_object* v_rhsExpr_896_, uint8_t v_op_897_, lean_object* v_congrThm_898_, lean_object* v_origExpr_899_, lean_object* v_a_900_, lean_object* v_a_901_, lean_object* v_a_902_, lean_object* v_a_903_, lean_object* v_a_904_, lean_object* v_a_905_){
_start:
{
lean_object* v___x_907_; 
lean_inc_ref(v_lhsExpr_895_);
v___x_907_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_goOrAtom(v_lhsExpr_895_, v_a_900_, v_a_901_, v_a_902_, v_a_903_, v_a_904_, v_a_905_);
if (lean_obj_tag(v___x_907_) == 0)
{
lean_object* v_a_908_; lean_object* v___x_910_; uint8_t v_isShared_911_; uint8_t v_isSharedCheck_967_; 
v_a_908_ = lean_ctor_get(v___x_907_, 0);
v_isSharedCheck_967_ = !lean_is_exclusive(v___x_907_);
if (v_isSharedCheck_967_ == 0)
{
v___x_910_ = v___x_907_;
v_isShared_911_ = v_isSharedCheck_967_;
goto v_resetjp_909_;
}
else
{
lean_inc(v_a_908_);
lean_dec(v___x_907_);
v___x_910_ = lean_box(0);
v_isShared_911_ = v_isSharedCheck_967_;
goto v_resetjp_909_;
}
v_resetjp_909_:
{
if (lean_obj_tag(v_a_908_) == 1)
{
lean_object* v_val_912_; lean_object* v___x_913_; 
lean_del_object(v___x_910_);
v_val_912_ = lean_ctor_get(v_a_908_, 0);
lean_inc(v_val_912_);
lean_dec_ref(v_a_908_);
lean_inc_ref(v_rhsExpr_896_);
v___x_913_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_goOrAtom(v_rhsExpr_896_, v_a_900_, v_a_901_, v_a_902_, v_a_903_, v_a_904_, v_a_905_);
if (lean_obj_tag(v___x_913_) == 0)
{
lean_object* v_a_914_; lean_object* v___x_916_; uint8_t v_isShared_917_; uint8_t v_isSharedCheck_962_; 
v_a_914_ = lean_ctor_get(v___x_913_, 0);
v_isSharedCheck_962_ = !lean_is_exclusive(v___x_913_);
if (v_isSharedCheck_962_ == 0)
{
v___x_916_ = v___x_913_;
v_isShared_917_ = v_isSharedCheck_962_;
goto v_resetjp_915_;
}
else
{
lean_inc(v_a_914_);
lean_dec(v___x_913_);
v___x_916_ = lean_box(0);
v_isShared_917_ = v_isSharedCheck_962_;
goto v_resetjp_915_;
}
v_resetjp_915_:
{
if (lean_obj_tag(v_a_914_) == 1)
{
lean_object* v_val_918_; lean_object* v___x_920_; uint8_t v_isShared_921_; uint8_t v_isSharedCheck_957_; 
v_val_918_ = lean_ctor_get(v_a_914_, 0);
v_isSharedCheck_957_ = !lean_is_exclusive(v_a_914_);
if (v_isSharedCheck_957_ == 0)
{
v___x_920_ = v_a_914_;
v_isShared_921_ = v_isSharedCheck_957_;
goto v_resetjp_919_;
}
else
{
lean_inc(v_val_918_);
lean_dec(v_a_914_);
v___x_920_ = lean_box(0);
v_isShared_921_ = v_isSharedCheck_957_;
goto v_resetjp_919_;
}
v_resetjp_919_:
{
lean_object* v_width_922_; lean_object* v_bvExpr_923_; lean_object* v_expr_924_; lean_object* v_width_925_; lean_object* v_bvExpr_926_; lean_object* v_expr_927_; uint8_t v___x_928_; 
v_width_922_ = lean_ctor_get(v_val_918_, 0);
v_bvExpr_923_ = lean_ctor_get(v_val_918_, 1);
v_expr_924_ = lean_ctor_get(v_val_918_, 4);
v_width_925_ = lean_ctor_get(v_val_912_, 0);
lean_inc(v_width_925_);
v_bvExpr_926_ = lean_ctor_get(v_val_912_, 1);
v_expr_927_ = lean_ctor_get(v_val_912_, 4);
v___x_928_ = lean_nat_dec_eq(v_width_922_, v_width_925_);
if (v___x_928_ == 0)
{
lean_object* v___x_929_; lean_object* v___x_931_; 
lean_dec(v_width_925_);
lean_del_object(v___x_920_);
lean_dec(v_val_918_);
lean_dec(v_val_912_);
lean_dec_ref(v_origExpr_899_);
lean_dec(v_congrThm_898_);
lean_dec_ref(v_rhsExpr_896_);
lean_dec_ref(v_lhsExpr_895_);
v___x_929_ = lean_box(0);
if (v_isShared_917_ == 0)
{
lean_ctor_set(v___x_916_, 0, v___x_929_);
v___x_931_ = v___x_916_;
goto v_reusejp_930_;
}
else
{
lean_object* v_reuseFailAlloc_932_; 
v_reuseFailAlloc_932_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_932_, 0, v___x_929_);
v___x_931_ = v_reuseFailAlloc_932_;
goto v_reusejp_930_;
}
v_reusejp_930_:
{
return v___x_931_;
}
}
else
{
lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___y_938_; 
lean_inc_ref(v_bvExpr_923_);
lean_inc_ref(v_bvExpr_926_);
lean_inc(v_width_925_);
v___x_933_ = l_Std_Tactic_BVDecide_BVExpr_bin___override(v_width_925_, v_bvExpr_926_, v_op_897_, v_bvExpr_923_);
v___x_934_ = lean_box(0);
v___x_935_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__2, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__2_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__2);
lean_inc(v_width_925_);
v___x_936_ = l_Lean_mkNatLit(v_width_925_);
switch(v_op_897_)
{
case 0:
{
lean_object* v___x_950_; 
v___x_950_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__6, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__6_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__6);
v___y_938_ = v___x_950_;
goto v___jp_937_;
}
case 1:
{
lean_object* v___x_951_; 
v___x_951_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__9, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__9_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__9);
v___y_938_ = v___x_951_;
goto v___jp_937_;
}
case 2:
{
lean_object* v___x_952_; 
v___x_952_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__12, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__12_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__12);
v___y_938_ = v___x_952_;
goto v___jp_937_;
}
case 3:
{
lean_object* v___x_953_; 
v___x_953_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__15, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__15_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__15);
v___y_938_ = v___x_953_;
goto v___jp_937_;
}
case 4:
{
lean_object* v___x_954_; 
v___x_954_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__18, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__18_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__18);
v___y_938_ = v___x_954_;
goto v___jp_937_;
}
case 5:
{
lean_object* v___x_955_; 
v___x_955_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__21, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__21_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__21);
v___y_938_ = v___x_955_;
goto v___jp_937_;
}
default: 
{
lean_object* v___x_956_; 
v___x_956_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__24, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__24_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__24);
v___y_938_ = v___x_956_;
goto v___jp_937_;
}
}
v___jp_937_:
{
lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_945_; 
lean_inc_ref(v_expr_924_);
lean_inc_ref(v_expr_927_);
lean_inc_ref(v___x_936_);
v___x_939_ = l_Lean_mkApp4(v___x_935_, v___x_936_, v_expr_927_, v___y_938_, v_expr_924_);
v___x_940_ = l_Lean_mkConst(v_congrThm_898_, v___x_934_);
v___x_941_ = l_Lean_Expr_app___override(v___x_940_, v___x_936_);
v___x_942_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryCongrProof___boxed), 11, 5);
lean_closure_set(v___x_942_, 0, v_val_912_);
lean_closure_set(v___x_942_, 1, v_val_918_);
lean_closure_set(v___x_942_, 2, v_lhsExpr_895_);
lean_closure_set(v___x_942_, 3, v_rhsExpr_896_);
lean_closure_set(v___x_942_, 4, v___x_941_);
v___x_943_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_943_, 0, v_width_925_);
lean_ctor_set(v___x_943_, 1, v___x_933_);
lean_ctor_set(v___x_943_, 2, v_origExpr_899_);
lean_ctor_set(v___x_943_, 3, v___x_942_);
lean_ctor_set(v___x_943_, 4, v___x_939_);
if (v_isShared_921_ == 0)
{
lean_ctor_set(v___x_920_, 0, v___x_943_);
v___x_945_ = v___x_920_;
goto v_reusejp_944_;
}
else
{
lean_object* v_reuseFailAlloc_949_; 
v_reuseFailAlloc_949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_949_, 0, v___x_943_);
v___x_945_ = v_reuseFailAlloc_949_;
goto v_reusejp_944_;
}
v_reusejp_944_:
{
lean_object* v___x_947_; 
if (v_isShared_917_ == 0)
{
lean_ctor_set(v___x_916_, 0, v___x_945_);
v___x_947_ = v___x_916_;
goto v_reusejp_946_;
}
else
{
lean_object* v_reuseFailAlloc_948_; 
v_reuseFailAlloc_948_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_948_, 0, v___x_945_);
v___x_947_ = v_reuseFailAlloc_948_;
goto v_reusejp_946_;
}
v_reusejp_946_:
{
return v___x_947_;
}
}
}
}
}
}
else
{
lean_object* v___x_958_; lean_object* v___x_960_; 
lean_dec(v_a_914_);
lean_dec(v_val_912_);
lean_dec_ref(v_origExpr_899_);
lean_dec(v_congrThm_898_);
lean_dec_ref(v_rhsExpr_896_);
lean_dec_ref(v_lhsExpr_895_);
v___x_958_ = lean_box(0);
if (v_isShared_917_ == 0)
{
lean_ctor_set(v___x_916_, 0, v___x_958_);
v___x_960_ = v___x_916_;
goto v_reusejp_959_;
}
else
{
lean_object* v_reuseFailAlloc_961_; 
v_reuseFailAlloc_961_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_961_, 0, v___x_958_);
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
else
{
lean_dec(v_val_912_);
lean_dec_ref(v_origExpr_899_);
lean_dec(v_congrThm_898_);
lean_dec_ref(v_rhsExpr_896_);
lean_dec_ref(v_lhsExpr_895_);
return v___x_913_;
}
}
else
{
lean_object* v___x_963_; lean_object* v___x_965_; 
lean_dec(v_a_908_);
lean_dec_ref(v_origExpr_899_);
lean_dec(v_congrThm_898_);
lean_dec_ref(v_rhsExpr_896_);
lean_dec_ref(v_lhsExpr_895_);
v___x_963_ = lean_box(0);
if (v_isShared_911_ == 0)
{
lean_ctor_set(v___x_910_, 0, v___x_963_);
v___x_965_ = v___x_910_;
goto v_reusejp_964_;
}
else
{
lean_object* v_reuseFailAlloc_966_; 
v_reuseFailAlloc_966_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_966_, 0, v___x_963_);
v___x_965_ = v_reuseFailAlloc_966_;
goto v_reusejp_964_;
}
v_reusejp_964_:
{
return v___x_965_;
}
}
}
}
else
{
lean_dec_ref(v_origExpr_899_);
lean_dec(v_congrThm_898_);
lean_dec_ref(v_rhsExpr_896_);
lean_dec_ref(v_lhsExpr_895_);
return v___x_907_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftReflection(lean_object* v_distanceExpr_1026_, lean_object* v_innerExpr_1027_, lean_object* v_shiftOp_1028_, lean_object* v_shiftOpName_1029_, lean_object* v_congrThm_1030_, lean_object* v_origExpr_1031_, lean_object* v_a_1032_, lean_object* v_a_1033_, lean_object* v_a_1034_, lean_object* v_a_1035_, lean_object* v_a_1036_, lean_object* v_a_1037_){
_start:
{
lean_object* v___x_1039_; 
lean_inc_ref(v_innerExpr_1027_);
v___x_1039_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_goOrAtom(v_innerExpr_1027_, v_a_1032_, v_a_1033_, v_a_1034_, v_a_1035_, v_a_1036_, v_a_1037_);
if (lean_obj_tag(v___x_1039_) == 0)
{
lean_object* v_a_1040_; lean_object* v___x_1042_; uint8_t v_isShared_1043_; uint8_t v_isSharedCheck_1086_; 
v_a_1040_ = lean_ctor_get(v___x_1039_, 0);
v_isSharedCheck_1086_ = !lean_is_exclusive(v___x_1039_);
if (v_isSharedCheck_1086_ == 0)
{
v___x_1042_ = v___x_1039_;
v_isShared_1043_ = v_isSharedCheck_1086_;
goto v_resetjp_1041_;
}
else
{
lean_inc(v_a_1040_);
lean_dec(v___x_1039_);
v___x_1042_ = lean_box(0);
v_isShared_1043_ = v_isSharedCheck_1086_;
goto v_resetjp_1041_;
}
v_resetjp_1041_:
{
if (lean_obj_tag(v_a_1040_) == 1)
{
lean_object* v_val_1044_; lean_object* v___x_1045_; 
lean_del_object(v___x_1042_);
v_val_1044_ = lean_ctor_get(v_a_1040_, 0);
lean_inc(v_val_1044_);
lean_dec_ref(v_a_1040_);
lean_inc_ref(v_distanceExpr_1026_);
v___x_1045_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_goOrAtom(v_distanceExpr_1026_, v_a_1032_, v_a_1033_, v_a_1034_, v_a_1035_, v_a_1036_, v_a_1037_);
if (lean_obj_tag(v___x_1045_) == 0)
{
lean_object* v_a_1046_; lean_object* v___x_1048_; uint8_t v_isShared_1049_; uint8_t v_isSharedCheck_1081_; 
v_a_1046_ = lean_ctor_get(v___x_1045_, 0);
v_isSharedCheck_1081_ = !lean_is_exclusive(v___x_1045_);
if (v_isSharedCheck_1081_ == 0)
{
v___x_1048_ = v___x_1045_;
v_isShared_1049_ = v_isSharedCheck_1081_;
goto v_resetjp_1047_;
}
else
{
lean_inc(v_a_1046_);
lean_dec(v___x_1045_);
v___x_1048_ = lean_box(0);
v_isShared_1049_ = v_isSharedCheck_1081_;
goto v_resetjp_1047_;
}
v_resetjp_1047_:
{
if (lean_obj_tag(v_a_1046_) == 1)
{
lean_object* v_val_1050_; lean_object* v___x_1052_; uint8_t v_isShared_1053_; uint8_t v_isSharedCheck_1076_; 
v_val_1050_ = lean_ctor_get(v_a_1046_, 0);
v_isSharedCheck_1076_ = !lean_is_exclusive(v_a_1046_);
if (v_isSharedCheck_1076_ == 0)
{
v___x_1052_ = v_a_1046_;
v_isShared_1053_ = v_isSharedCheck_1076_;
goto v_resetjp_1051_;
}
else
{
lean_inc(v_val_1050_);
lean_dec(v_a_1046_);
v___x_1052_ = lean_box(0);
v_isShared_1053_ = v_isSharedCheck_1076_;
goto v_resetjp_1051_;
}
v_resetjp_1051_:
{
lean_object* v_width_1054_; lean_object* v_bvExpr_1055_; lean_object* v_expr_1056_; lean_object* v_width_1057_; lean_object* v_bvExpr_1058_; lean_object* v_expr_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1071_; 
v_width_1054_ = lean_ctor_get(v_val_1044_, 0);
lean_inc(v_width_1054_);
v_bvExpr_1055_ = lean_ctor_get(v_val_1044_, 1);
v_expr_1056_ = lean_ctor_get(v_val_1044_, 4);
v_width_1057_ = lean_ctor_get(v_val_1050_, 0);
v_bvExpr_1058_ = lean_ctor_get(v_val_1050_, 1);
v_expr_1059_ = lean_ctor_get(v_val_1050_, 4);
lean_inc_ref(v_bvExpr_1058_);
lean_inc_ref(v_bvExpr_1055_);
lean_inc(v_width_1057_);
lean_inc(v_width_1054_);
v___x_1060_ = lean_apply_4(v_shiftOp_1028_, v_width_1054_, v_width_1057_, v_bvExpr_1055_, v_bvExpr_1058_);
v___x_1061_ = lean_box(0);
v___x_1062_ = l_Lean_mkConst(v_shiftOpName_1029_, v___x_1061_);
lean_inc(v_width_1054_);
v___x_1063_ = l_Lean_mkNatLit(v_width_1054_);
lean_inc(v_width_1057_);
v___x_1064_ = l_Lean_mkNatLit(v_width_1057_);
lean_inc_ref(v_expr_1059_);
lean_inc_ref(v_expr_1056_);
lean_inc_ref(v___x_1064_);
lean_inc_ref(v___x_1063_);
v___x_1065_ = l_Lean_mkApp4(v___x_1062_, v___x_1063_, v___x_1064_, v_expr_1056_, v_expr_1059_);
v___x_1066_ = l_Lean_mkConst(v_congrThm_1030_, v___x_1061_);
v___x_1067_ = l_Lean_mkAppB(v___x_1066_, v___x_1063_, v___x_1064_);
v___x_1068_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryCongrProof___boxed), 11, 5);
lean_closure_set(v___x_1068_, 0, v_val_1044_);
lean_closure_set(v___x_1068_, 1, v_val_1050_);
lean_closure_set(v___x_1068_, 2, v_innerExpr_1027_);
lean_closure_set(v___x_1068_, 3, v_distanceExpr_1026_);
lean_closure_set(v___x_1068_, 4, v___x_1067_);
v___x_1069_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1069_, 0, v_width_1054_);
lean_ctor_set(v___x_1069_, 1, v___x_1060_);
lean_ctor_set(v___x_1069_, 2, v_origExpr_1031_);
lean_ctor_set(v___x_1069_, 3, v___x_1068_);
lean_ctor_set(v___x_1069_, 4, v___x_1065_);
if (v_isShared_1053_ == 0)
{
lean_ctor_set(v___x_1052_, 0, v___x_1069_);
v___x_1071_ = v___x_1052_;
goto v_reusejp_1070_;
}
else
{
lean_object* v_reuseFailAlloc_1075_; 
v_reuseFailAlloc_1075_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1075_, 0, v___x_1069_);
v___x_1071_ = v_reuseFailAlloc_1075_;
goto v_reusejp_1070_;
}
v_reusejp_1070_:
{
lean_object* v___x_1073_; 
if (v_isShared_1049_ == 0)
{
lean_ctor_set(v___x_1048_, 0, v___x_1071_);
v___x_1073_ = v___x_1048_;
goto v_reusejp_1072_;
}
else
{
lean_object* v_reuseFailAlloc_1074_; 
v_reuseFailAlloc_1074_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1074_, 0, v___x_1071_);
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
else
{
lean_object* v___x_1077_; lean_object* v___x_1079_; 
lean_dec(v_a_1046_);
lean_dec(v_val_1044_);
lean_dec_ref(v_origExpr_1031_);
lean_dec(v_congrThm_1030_);
lean_dec(v_shiftOpName_1029_);
lean_dec_ref(v_shiftOp_1028_);
lean_dec_ref(v_innerExpr_1027_);
lean_dec_ref(v_distanceExpr_1026_);
v___x_1077_ = lean_box(0);
if (v_isShared_1049_ == 0)
{
lean_ctor_set(v___x_1048_, 0, v___x_1077_);
v___x_1079_ = v___x_1048_;
goto v_reusejp_1078_;
}
else
{
lean_object* v_reuseFailAlloc_1080_; 
v_reuseFailAlloc_1080_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1080_, 0, v___x_1077_);
v___x_1079_ = v_reuseFailAlloc_1080_;
goto v_reusejp_1078_;
}
v_reusejp_1078_:
{
return v___x_1079_;
}
}
}
}
else
{
lean_dec(v_val_1044_);
lean_dec_ref(v_origExpr_1031_);
lean_dec(v_congrThm_1030_);
lean_dec(v_shiftOpName_1029_);
lean_dec_ref(v_shiftOp_1028_);
lean_dec_ref(v_innerExpr_1027_);
lean_dec_ref(v_distanceExpr_1026_);
return v___x_1045_;
}
}
else
{
lean_object* v___x_1082_; lean_object* v___x_1084_; 
lean_dec(v_a_1040_);
lean_dec_ref(v_origExpr_1031_);
lean_dec(v_congrThm_1030_);
lean_dec(v_shiftOpName_1029_);
lean_dec_ref(v_shiftOp_1028_);
lean_dec_ref(v_innerExpr_1027_);
lean_dec_ref(v_distanceExpr_1026_);
v___x_1082_ = lean_box(0);
if (v_isShared_1043_ == 0)
{
lean_ctor_set(v___x_1042_, 0, v___x_1082_);
v___x_1084_ = v___x_1042_;
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
lean_dec_ref(v_origExpr_1031_);
lean_dec(v_congrThm_1030_);
lean_dec(v_shiftOpName_1029_);
lean_dec_ref(v_shiftOp_1028_);
lean_dec_ref(v_innerExpr_1027_);
lean_dec_ref(v_distanceExpr_1026_);
return v___x_1039_;
}
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__63(void){
_start:
{
lean_object* v___x_1088_; lean_object* v___x_1089_; 
v___x_1088_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__62));
v___x_1089_ = l_Lean_stringToMessageData(v___x_1088_);
return v___x_1089_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__71(void){
_start:
{
lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; 
v___x_1113_ = lean_box(0);
v___x_1114_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__70));
v___x_1115_ = l_Lean_mkConst(v___x_1114_, v___x_1113_);
return v___x_1115_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__79(void){
_start:
{
lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; 
v___x_1139_ = lean_box(0);
v___x_1140_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__78));
v___x_1141_ = l_Lean_mkConst(v___x_1140_, v___x_1139_);
return v___x_1141_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_of_binaryReflection(lean_object* v_lhsExpr_1164_, lean_object* v_rhsExpr_1165_, uint8_t v_pred_1166_, lean_object* v_origExpr_1167_, lean_object* v_a_1168_, lean_object* v_a_1169_, lean_object* v_a_1170_, lean_object* v_a_1171_, lean_object* v_a_1172_, lean_object* v_a_1173_){
_start:
{
lean_object* v___x_1175_; 
lean_inc_ref(v_lhsExpr_1164_);
v___x_1175_ = l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of(v_lhsExpr_1164_, v_a_1168_, v_a_1169_, v_a_1170_, v_a_1171_, v_a_1172_, v_a_1173_);
if (lean_obj_tag(v___x_1175_) == 0)
{
lean_object* v_a_1176_; lean_object* v___x_1178_; uint8_t v_isShared_1179_; uint8_t v_isSharedCheck_1205_; 
v_a_1176_ = lean_ctor_get(v___x_1175_, 0);
v_isSharedCheck_1205_ = !lean_is_exclusive(v___x_1175_);
if (v_isSharedCheck_1205_ == 0)
{
v___x_1178_ = v___x_1175_;
v_isShared_1179_ = v_isSharedCheck_1205_;
goto v_resetjp_1177_;
}
else
{
lean_inc(v_a_1176_);
lean_dec(v___x_1175_);
v___x_1178_ = lean_box(0);
v_isShared_1179_ = v_isSharedCheck_1205_;
goto v_resetjp_1177_;
}
v_resetjp_1177_:
{
if (lean_obj_tag(v_a_1176_) == 1)
{
lean_object* v_val_1180_; lean_object* v___x_1181_; 
lean_del_object(v___x_1178_);
v_val_1180_ = lean_ctor_get(v_a_1176_, 0);
lean_inc(v_val_1180_);
lean_dec_ref(v_a_1176_);
lean_inc_ref(v_rhsExpr_1165_);
v___x_1181_ = l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of(v_rhsExpr_1165_, v_a_1168_, v_a_1169_, v_a_1170_, v_a_1171_, v_a_1172_, v_a_1173_);
if (lean_obj_tag(v___x_1181_) == 0)
{
lean_object* v_a_1182_; lean_object* v___x_1184_; uint8_t v_isShared_1185_; uint8_t v_isSharedCheck_1192_; 
v_a_1182_ = lean_ctor_get(v___x_1181_, 0);
v_isSharedCheck_1192_ = !lean_is_exclusive(v___x_1181_);
if (v_isSharedCheck_1192_ == 0)
{
v___x_1184_ = v___x_1181_;
v_isShared_1185_ = v_isSharedCheck_1192_;
goto v_resetjp_1183_;
}
else
{
lean_inc(v_a_1182_);
lean_dec(v___x_1181_);
v___x_1184_ = lean_box(0);
v_isShared_1185_ = v_isSharedCheck_1192_;
goto v_resetjp_1183_;
}
v_resetjp_1183_:
{
if (lean_obj_tag(v_a_1182_) == 1)
{
lean_object* v_val_1186_; lean_object* v___x_1187_; 
lean_del_object(v___x_1184_);
v_val_1186_ = lean_ctor_get(v_a_1182_, 0);
lean_inc(v_val_1186_);
lean_dec_ref(v_a_1182_);
v___x_1187_ = l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_mkBinPred___redArg(v_val_1180_, v_val_1186_, v_lhsExpr_1164_, v_rhsExpr_1165_, v_pred_1166_, v_origExpr_1167_);
return v___x_1187_;
}
else
{
lean_object* v___x_1188_; lean_object* v___x_1190_; 
lean_dec(v_a_1182_);
lean_dec(v_val_1180_);
lean_dec_ref(v_origExpr_1167_);
lean_dec_ref(v_rhsExpr_1165_);
lean_dec_ref(v_lhsExpr_1164_);
v___x_1188_ = lean_box(0);
if (v_isShared_1185_ == 0)
{
lean_ctor_set(v___x_1184_, 0, v___x_1188_);
v___x_1190_ = v___x_1184_;
goto v_reusejp_1189_;
}
else
{
lean_object* v_reuseFailAlloc_1191_; 
v_reuseFailAlloc_1191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1191_, 0, v___x_1188_);
v___x_1190_ = v_reuseFailAlloc_1191_;
goto v_reusejp_1189_;
}
v_reusejp_1189_:
{
return v___x_1190_;
}
}
}
}
else
{
lean_object* v_a_1193_; lean_object* v___x_1195_; uint8_t v_isShared_1196_; uint8_t v_isSharedCheck_1200_; 
lean_dec(v_val_1180_);
lean_dec_ref(v_origExpr_1167_);
lean_dec_ref(v_rhsExpr_1165_);
lean_dec_ref(v_lhsExpr_1164_);
v_a_1193_ = lean_ctor_get(v___x_1181_, 0);
v_isSharedCheck_1200_ = !lean_is_exclusive(v___x_1181_);
if (v_isSharedCheck_1200_ == 0)
{
v___x_1195_ = v___x_1181_;
v_isShared_1196_ = v_isSharedCheck_1200_;
goto v_resetjp_1194_;
}
else
{
lean_inc(v_a_1193_);
lean_dec(v___x_1181_);
v___x_1195_ = lean_box(0);
v_isShared_1196_ = v_isSharedCheck_1200_;
goto v_resetjp_1194_;
}
v_resetjp_1194_:
{
lean_object* v___x_1198_; 
if (v_isShared_1196_ == 0)
{
v___x_1198_ = v___x_1195_;
goto v_reusejp_1197_;
}
else
{
lean_object* v_reuseFailAlloc_1199_; 
v_reuseFailAlloc_1199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1199_, 0, v_a_1193_);
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
else
{
lean_object* v___x_1201_; lean_object* v___x_1203_; 
lean_dec(v_a_1176_);
lean_dec_ref(v_origExpr_1167_);
lean_dec_ref(v_rhsExpr_1165_);
lean_dec_ref(v_lhsExpr_1164_);
v___x_1201_ = lean_box(0);
if (v_isShared_1179_ == 0)
{
lean_ctor_set(v___x_1178_, 0, v___x_1201_);
v___x_1203_ = v___x_1178_;
goto v_reusejp_1202_;
}
else
{
lean_object* v_reuseFailAlloc_1204_; 
v_reuseFailAlloc_1204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1204_, 0, v___x_1201_);
v___x_1203_ = v_reuseFailAlloc_1204_;
goto v_reusejp_1202_;
}
v_reusejp_1202_:
{
return v___x_1203_;
}
}
}
}
else
{
lean_object* v_a_1206_; lean_object* v___x_1208_; uint8_t v_isShared_1209_; uint8_t v_isSharedCheck_1213_; 
lean_dec_ref(v_origExpr_1167_);
lean_dec_ref(v_rhsExpr_1165_);
lean_dec_ref(v_lhsExpr_1164_);
v_a_1206_ = lean_ctor_get(v___x_1175_, 0);
v_isSharedCheck_1213_ = !lean_is_exclusive(v___x_1175_);
if (v_isSharedCheck_1213_ == 0)
{
v___x_1208_ = v___x_1175_;
v_isShared_1209_ = v_isSharedCheck_1213_;
goto v_resetjp_1207_;
}
else
{
lean_inc(v_a_1206_);
lean_dec(v___x_1175_);
v___x_1208_ = lean_box(0);
v_isShared_1209_ = v_isSharedCheck_1213_;
goto v_resetjp_1207_;
}
v_resetjp_1207_:
{
lean_object* v___x_1211_; 
if (v_isShared_1209_ == 0)
{
v___x_1211_ = v___x_1208_;
goto v_reusejp_1210_;
}
else
{
lean_object* v_reuseFailAlloc_1212_; 
v_reuseFailAlloc_1212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1212_, 0, v_a_1206_);
v___x_1211_ = v_reuseFailAlloc_1212_;
goto v_reusejp_1210_;
}
v_reusejp_1210_:
{
return v___x_1211_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_of_go(lean_object* v_origExpr_1214_, lean_object* v_a_1215_, lean_object* v_a_1216_, lean_object* v_a_1217_, lean_object* v_a_1218_, lean_object* v_a_1219_, lean_object* v_a_1220_){
_start:
{
lean_object* v___x_1225_; 
lean_inc_ref(v_origExpr_1214_);
v___x_1225_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_origExpr_1214_, v_a_1218_);
if (lean_obj_tag(v___x_1225_) == 0)
{
lean_object* v_a_1226_; lean_object* v___x_1228_; uint8_t v_isShared_1229_; uint8_t v_isSharedCheck_1324_; 
v_a_1226_ = lean_ctor_get(v___x_1225_, 0);
v_isSharedCheck_1324_ = !lean_is_exclusive(v___x_1225_);
if (v_isSharedCheck_1324_ == 0)
{
v___x_1228_ = v___x_1225_;
v_isShared_1229_ = v_isSharedCheck_1324_;
goto v_resetjp_1227_;
}
else
{
lean_inc(v_a_1226_);
lean_dec(v___x_1225_);
v___x_1228_ = lean_box(0);
v_isShared_1229_ = v_isSharedCheck_1324_;
goto v_resetjp_1227_;
}
v_resetjp_1227_:
{
lean_object* v___x_1235_; uint8_t v___x_1236_; 
v___x_1235_ = l_Lean_Expr_cleanupAnnotations(v_a_1226_);
v___x_1236_ = l_Lean_Expr_isApp(v___x_1235_);
if (v___x_1236_ == 0)
{
lean_dec_ref(v___x_1235_);
lean_dec_ref(v_origExpr_1214_);
goto v___jp_1230_;
}
else
{
lean_object* v_arg_1237_; lean_object* v___x_1238_; uint8_t v___x_1239_; 
v_arg_1237_ = lean_ctor_get(v___x_1235_, 1);
lean_inc_ref(v_arg_1237_);
v___x_1238_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1235_);
v___x_1239_ = l_Lean_Expr_isApp(v___x_1238_);
if (v___x_1239_ == 0)
{
lean_dec_ref(v___x_1238_);
lean_dec_ref(v_arg_1237_);
lean_dec_ref(v_origExpr_1214_);
goto v___jp_1230_;
}
else
{
lean_object* v_arg_1240_; lean_object* v___x_1241_; uint8_t v___x_1242_; 
v_arg_1240_ = lean_ctor_get(v___x_1238_, 1);
lean_inc_ref(v_arg_1240_);
v___x_1241_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1238_);
v___x_1242_ = l_Lean_Expr_isApp(v___x_1241_);
if (v___x_1242_ == 0)
{
lean_dec_ref(v___x_1241_);
lean_dec_ref(v_arg_1240_);
lean_dec_ref(v_arg_1237_);
lean_dec_ref(v_origExpr_1214_);
goto v___jp_1230_;
}
else
{
lean_object* v___x_1243_; lean_object* v___x_1244_; uint8_t v___x_1245_; 
v___x_1243_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1241_);
v___x_1244_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_of_go___closed__2));
v___x_1245_ = l_Lean_Expr_isConstOf(v___x_1243_, v___x_1244_);
if (v___x_1245_ == 0)
{
lean_object* v___x_1246_; uint8_t v___x_1247_; 
v___x_1246_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_of_go___closed__4));
v___x_1247_ = l_Lean_Expr_isConstOf(v___x_1243_, v___x_1246_);
if (v___x_1247_ == 0)
{
uint8_t v___x_1248_; 
v___x_1248_ = l_Lean_Expr_isApp(v___x_1243_);
if (v___x_1248_ == 0)
{
lean_dec_ref(v___x_1243_);
lean_dec_ref(v_arg_1240_);
lean_dec_ref(v_arg_1237_);
lean_dec_ref(v_origExpr_1214_);
goto v___jp_1230_;
}
else
{
lean_object* v_arg_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; uint8_t v___x_1252_; 
v_arg_1249_ = lean_ctor_get(v___x_1243_, 1);
lean_inc_ref(v_arg_1249_);
v___x_1250_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1243_);
v___x_1251_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_of_go___closed__7));
v___x_1252_ = l_Lean_Expr_isConstOf(v___x_1250_, v___x_1251_);
lean_dec_ref(v___x_1250_);
if (v___x_1252_ == 0)
{
lean_dec_ref(v_arg_1249_);
lean_dec_ref(v_arg_1240_);
lean_dec_ref(v_arg_1237_);
lean_dec_ref(v_origExpr_1214_);
goto v___jp_1230_;
}
else
{
lean_object* v___x_1253_; uint8_t v___x_1254_; 
lean_del_object(v___x_1228_);
v___x_1253_ = l_Lean_Expr_cleanupAnnotations(v_arg_1249_);
v___x_1254_ = l_Lean_Expr_isApp(v___x_1253_);
if (v___x_1254_ == 0)
{
lean_dec_ref(v___x_1253_);
lean_dec_ref(v_arg_1240_);
lean_dec_ref(v_arg_1237_);
lean_dec_ref(v_origExpr_1214_);
goto v___jp_1222_;
}
else
{
lean_object* v___x_1255_; lean_object* v___x_1256_; uint8_t v___x_1257_; 
v___x_1255_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1253_);
v___x_1256_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_of_go___closed__8));
v___x_1257_ = l_Lean_Expr_isConstOf(v___x_1255_, v___x_1256_);
lean_dec_ref(v___x_1255_);
if (v___x_1257_ == 0)
{
lean_dec_ref(v_arg_1240_);
lean_dec_ref(v_arg_1237_);
lean_dec_ref(v_origExpr_1214_);
goto v___jp_1222_;
}
else
{
uint8_t v___x_1258_; lean_object* v___x_1259_; 
v___x_1258_ = 0;
v___x_1259_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_of_binaryReflection(v_arg_1240_, v_arg_1237_, v___x_1258_, v_origExpr_1214_, v_a_1215_, v_a_1216_, v_a_1217_, v_a_1218_, v_a_1219_, v_a_1220_);
return v___x_1259_;
}
}
}
}
}
else
{
uint8_t v___x_1260_; lean_object* v___x_1261_; 
lean_dec_ref(v___x_1243_);
lean_del_object(v___x_1228_);
v___x_1260_ = 1;
v___x_1261_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_of_binaryReflection(v_arg_1240_, v_arg_1237_, v___x_1260_, v_origExpr_1214_, v_a_1215_, v_a_1216_, v_a_1217_, v_a_1218_, v_a_1219_, v_a_1220_);
return v___x_1261_;
}
}
else
{
lean_object* v___x_1262_; 
lean_dec_ref(v___x_1243_);
lean_del_object(v___x_1228_);
lean_inc_ref(v_arg_1240_);
v___x_1262_ = l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of(v_arg_1240_, v_a_1215_, v_a_1216_, v_a_1217_, v_a_1218_, v_a_1219_, v_a_1220_);
if (lean_obj_tag(v___x_1262_) == 0)
{
lean_object* v_a_1263_; lean_object* v___x_1265_; uint8_t v_isShared_1266_; uint8_t v_isSharedCheck_1315_; 
v_a_1263_ = lean_ctor_get(v___x_1262_, 0);
v_isSharedCheck_1315_ = !lean_is_exclusive(v___x_1262_);
if (v_isSharedCheck_1315_ == 0)
{
v___x_1265_ = v___x_1262_;
v_isShared_1266_ = v_isSharedCheck_1315_;
goto v_resetjp_1264_;
}
else
{
lean_inc(v_a_1263_);
lean_dec(v___x_1262_);
v___x_1265_ = lean_box(0);
v_isShared_1266_ = v_isSharedCheck_1315_;
goto v_resetjp_1264_;
}
v_resetjp_1264_:
{
if (lean_obj_tag(v_a_1263_) == 1)
{
lean_object* v_val_1267_; lean_object* v___x_1268_; 
lean_del_object(v___x_1265_);
v_val_1267_ = lean_ctor_get(v_a_1263_, 0);
lean_inc(v_val_1267_);
lean_dec_ref(v_a_1263_);
v___x_1268_ = l_Lean_Meta_getNatValue_x3f(v_arg_1237_, v_a_1217_, v_a_1218_, v_a_1219_, v_a_1220_);
lean_dec_ref(v_arg_1237_);
if (lean_obj_tag(v___x_1268_) == 0)
{
lean_object* v_a_1269_; lean_object* v___x_1271_; uint8_t v_isShared_1272_; uint8_t v_isSharedCheck_1302_; 
v_a_1269_ = lean_ctor_get(v___x_1268_, 0);
v_isSharedCheck_1302_ = !lean_is_exclusive(v___x_1268_);
if (v_isSharedCheck_1302_ == 0)
{
v___x_1271_ = v___x_1268_;
v_isShared_1272_ = v_isSharedCheck_1302_;
goto v_resetjp_1270_;
}
else
{
lean_inc(v_a_1269_);
lean_dec(v___x_1268_);
v___x_1271_ = lean_box(0);
v_isShared_1272_ = v_isSharedCheck_1302_;
goto v_resetjp_1270_;
}
v_resetjp_1270_:
{
if (lean_obj_tag(v_a_1269_) == 1)
{
lean_object* v_val_1273_; lean_object* v___x_1275_; uint8_t v_isShared_1276_; uint8_t v_isSharedCheck_1297_; 
lean_del_object(v___x_1271_);
v_val_1273_ = lean_ctor_get(v_a_1269_, 0);
v_isSharedCheck_1297_ = !lean_is_exclusive(v_a_1269_);
if (v_isSharedCheck_1297_ == 0)
{
v___x_1275_ = v_a_1269_;
v_isShared_1276_ = v_isSharedCheck_1297_;
goto v_resetjp_1274_;
}
else
{
lean_inc(v_val_1273_);
lean_dec(v_a_1269_);
v___x_1275_ = lean_box(0);
v_isShared_1276_ = v_isSharedCheck_1297_;
goto v_resetjp_1274_;
}
v_resetjp_1274_:
{
lean_object* v___x_1277_; 
v___x_1277_ = l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_mkGetLsbD___redArg(v_val_1267_, v_arg_1240_, v_val_1273_, v_origExpr_1214_);
if (lean_obj_tag(v___x_1277_) == 0)
{
lean_object* v_a_1278_; lean_object* v___x_1280_; uint8_t v_isShared_1281_; uint8_t v_isSharedCheck_1288_; 
v_a_1278_ = lean_ctor_get(v___x_1277_, 0);
v_isSharedCheck_1288_ = !lean_is_exclusive(v___x_1277_);
if (v_isSharedCheck_1288_ == 0)
{
v___x_1280_ = v___x_1277_;
v_isShared_1281_ = v_isSharedCheck_1288_;
goto v_resetjp_1279_;
}
else
{
lean_inc(v_a_1278_);
lean_dec(v___x_1277_);
v___x_1280_ = lean_box(0);
v_isShared_1281_ = v_isSharedCheck_1288_;
goto v_resetjp_1279_;
}
v_resetjp_1279_:
{
lean_object* v___x_1283_; 
if (v_isShared_1276_ == 0)
{
lean_ctor_set(v___x_1275_, 0, v_a_1278_);
v___x_1283_ = v___x_1275_;
goto v_reusejp_1282_;
}
else
{
lean_object* v_reuseFailAlloc_1287_; 
v_reuseFailAlloc_1287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1287_, 0, v_a_1278_);
v___x_1283_ = v_reuseFailAlloc_1287_;
goto v_reusejp_1282_;
}
v_reusejp_1282_:
{
lean_object* v___x_1285_; 
if (v_isShared_1281_ == 0)
{
lean_ctor_set(v___x_1280_, 0, v___x_1283_);
v___x_1285_ = v___x_1280_;
goto v_reusejp_1284_;
}
else
{
lean_object* v_reuseFailAlloc_1286_; 
v_reuseFailAlloc_1286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1286_, 0, v___x_1283_);
v___x_1285_ = v_reuseFailAlloc_1286_;
goto v_reusejp_1284_;
}
v_reusejp_1284_:
{
return v___x_1285_;
}
}
}
}
else
{
lean_object* v_a_1289_; lean_object* v___x_1291_; uint8_t v_isShared_1292_; uint8_t v_isSharedCheck_1296_; 
lean_del_object(v___x_1275_);
v_a_1289_ = lean_ctor_get(v___x_1277_, 0);
v_isSharedCheck_1296_ = !lean_is_exclusive(v___x_1277_);
if (v_isSharedCheck_1296_ == 0)
{
v___x_1291_ = v___x_1277_;
v_isShared_1292_ = v_isSharedCheck_1296_;
goto v_resetjp_1290_;
}
else
{
lean_inc(v_a_1289_);
lean_dec(v___x_1277_);
v___x_1291_ = lean_box(0);
v_isShared_1292_ = v_isSharedCheck_1296_;
goto v_resetjp_1290_;
}
v_resetjp_1290_:
{
lean_object* v___x_1294_; 
if (v_isShared_1292_ == 0)
{
v___x_1294_ = v___x_1291_;
goto v_reusejp_1293_;
}
else
{
lean_object* v_reuseFailAlloc_1295_; 
v_reuseFailAlloc_1295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1295_, 0, v_a_1289_);
v___x_1294_ = v_reuseFailAlloc_1295_;
goto v_reusejp_1293_;
}
v_reusejp_1293_:
{
return v___x_1294_;
}
}
}
}
}
else
{
lean_object* v___x_1298_; lean_object* v___x_1300_; 
lean_dec(v_a_1269_);
lean_dec(v_val_1267_);
lean_dec_ref(v_arg_1240_);
lean_dec_ref(v_origExpr_1214_);
v___x_1298_ = lean_box(0);
if (v_isShared_1272_ == 0)
{
lean_ctor_set(v___x_1271_, 0, v___x_1298_);
v___x_1300_ = v___x_1271_;
goto v_reusejp_1299_;
}
else
{
lean_object* v_reuseFailAlloc_1301_; 
v_reuseFailAlloc_1301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1301_, 0, v___x_1298_);
v___x_1300_ = v_reuseFailAlloc_1301_;
goto v_reusejp_1299_;
}
v_reusejp_1299_:
{
return v___x_1300_;
}
}
}
}
else
{
lean_object* v_a_1303_; lean_object* v___x_1305_; uint8_t v_isShared_1306_; uint8_t v_isSharedCheck_1310_; 
lean_dec(v_val_1267_);
lean_dec_ref(v_arg_1240_);
lean_dec_ref(v_origExpr_1214_);
v_a_1303_ = lean_ctor_get(v___x_1268_, 0);
v_isSharedCheck_1310_ = !lean_is_exclusive(v___x_1268_);
if (v_isSharedCheck_1310_ == 0)
{
v___x_1305_ = v___x_1268_;
v_isShared_1306_ = v_isSharedCheck_1310_;
goto v_resetjp_1304_;
}
else
{
lean_inc(v_a_1303_);
lean_dec(v___x_1268_);
v___x_1305_ = lean_box(0);
v_isShared_1306_ = v_isSharedCheck_1310_;
goto v_resetjp_1304_;
}
v_resetjp_1304_:
{
lean_object* v___x_1308_; 
if (v_isShared_1306_ == 0)
{
v___x_1308_ = v___x_1305_;
goto v_reusejp_1307_;
}
else
{
lean_object* v_reuseFailAlloc_1309_; 
v_reuseFailAlloc_1309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1309_, 0, v_a_1303_);
v___x_1308_ = v_reuseFailAlloc_1309_;
goto v_reusejp_1307_;
}
v_reusejp_1307_:
{
return v___x_1308_;
}
}
}
}
else
{
lean_object* v___x_1311_; lean_object* v___x_1313_; 
lean_dec(v_a_1263_);
lean_dec_ref(v_arg_1240_);
lean_dec_ref(v_arg_1237_);
lean_dec_ref(v_origExpr_1214_);
v___x_1311_ = lean_box(0);
if (v_isShared_1266_ == 0)
{
lean_ctor_set(v___x_1265_, 0, v___x_1311_);
v___x_1313_ = v___x_1265_;
goto v_reusejp_1312_;
}
else
{
lean_object* v_reuseFailAlloc_1314_; 
v_reuseFailAlloc_1314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1314_, 0, v___x_1311_);
v___x_1313_ = v_reuseFailAlloc_1314_;
goto v_reusejp_1312_;
}
v_reusejp_1312_:
{
return v___x_1313_;
}
}
}
}
else
{
lean_object* v_a_1316_; lean_object* v___x_1318_; uint8_t v_isShared_1319_; uint8_t v_isSharedCheck_1323_; 
lean_dec_ref(v_arg_1240_);
lean_dec_ref(v_arg_1237_);
lean_dec_ref(v_origExpr_1214_);
v_a_1316_ = lean_ctor_get(v___x_1262_, 0);
v_isSharedCheck_1323_ = !lean_is_exclusive(v___x_1262_);
if (v_isSharedCheck_1323_ == 0)
{
v___x_1318_ = v___x_1262_;
v_isShared_1319_ = v_isSharedCheck_1323_;
goto v_resetjp_1317_;
}
else
{
lean_inc(v_a_1316_);
lean_dec(v___x_1262_);
v___x_1318_ = lean_box(0);
v_isShared_1319_ = v_isSharedCheck_1323_;
goto v_resetjp_1317_;
}
v_resetjp_1317_:
{
lean_object* v___x_1321_; 
if (v_isShared_1319_ == 0)
{
v___x_1321_ = v___x_1318_;
goto v_reusejp_1320_;
}
else
{
lean_object* v_reuseFailAlloc_1322_; 
v_reuseFailAlloc_1322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1322_, 0, v_a_1316_);
v___x_1321_ = v_reuseFailAlloc_1322_;
goto v_reusejp_1320_;
}
v_reusejp_1320_:
{
return v___x_1321_;
}
}
}
}
}
}
}
v___jp_1230_:
{
lean_object* v___x_1231_; lean_object* v___x_1233_; 
v___x_1231_ = lean_box(0);
if (v_isShared_1229_ == 0)
{
lean_ctor_set(v___x_1228_, 0, v___x_1231_);
v___x_1233_ = v___x_1228_;
goto v_reusejp_1232_;
}
else
{
lean_object* v_reuseFailAlloc_1234_; 
v_reuseFailAlloc_1234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1234_, 0, v___x_1231_);
v___x_1233_ = v_reuseFailAlloc_1234_;
goto v_reusejp_1232_;
}
v_reusejp_1232_:
{
return v___x_1233_;
}
}
}
}
else
{
lean_object* v_a_1325_; lean_object* v___x_1327_; uint8_t v_isShared_1328_; uint8_t v_isSharedCheck_1332_; 
lean_dec_ref(v_origExpr_1214_);
v_a_1325_ = lean_ctor_get(v___x_1225_, 0);
v_isSharedCheck_1332_ = !lean_is_exclusive(v___x_1225_);
if (v_isSharedCheck_1332_ == 0)
{
v___x_1327_ = v___x_1225_;
v_isShared_1328_ = v_isSharedCheck_1332_;
goto v_resetjp_1326_;
}
else
{
lean_inc(v_a_1325_);
lean_dec(v___x_1225_);
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
v___jp_1222_:
{
lean_object* v___x_1223_; lean_object* v___x_1224_; 
v___x_1223_ = lean_box(0);
v___x_1224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1224_, 0, v___x_1223_);
return v___x_1224_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVPredCache___at___00Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_of_spec__5(lean_object* v_e_1333_, lean_object* v_a_1334_, lean_object* v_a_1335_, lean_object* v_a_1336_, lean_object* v_a_1337_, lean_object* v_a_1338_, lean_object* v_a_1339_){
_start:
{
lean_object* v___y_1342_; lean_object* v___x_1365_; lean_object* v_bvPredCache_1366_; lean_object* v___x_1367_; 
v___x_1365_ = lean_st_ref_get(v_a_1334_);
v_bvPredCache_1366_ = lean_ctor_get(v___x_1365_, 2);
lean_inc_ref(v_bvPredCache_1366_);
lean_dec(v___x_1365_);
v___x_1367_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom_spec__2_spec__12___redArg(v_bvPredCache_1366_, v_e_1333_);
lean_dec_ref(v_bvPredCache_1366_);
if (lean_obj_tag(v___x_1367_) == 0)
{
lean_object* v___x_1368_; 
lean_inc_ref(v_e_1333_);
v___x_1368_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_of_go(v_e_1333_, v_a_1334_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_, v_a_1339_);
if (lean_obj_tag(v___x_1368_) == 0)
{
lean_object* v_a_1369_; 
v_a_1369_ = lean_ctor_get(v___x_1368_, 0);
lean_inc(v_a_1369_);
if (lean_obj_tag(v_a_1369_) == 0)
{
lean_object* v___x_1370_; 
lean_dec_ref(v___x_1368_);
lean_inc_ref(v_e_1333_);
v___x_1370_ = l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_boolAtom(v_e_1333_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_, v_a_1339_);
v___y_1342_ = v___x_1370_;
goto v___jp_1341_;
}
else
{
lean_dec_ref(v_a_1369_);
v___y_1342_ = v___x_1368_;
goto v___jp_1341_;
}
}
else
{
v___y_1342_ = v___x_1368_;
goto v___jp_1341_;
}
}
else
{
lean_object* v_val_1371_; lean_object* v___x_1373_; uint8_t v_isShared_1374_; uint8_t v_isSharedCheck_1378_; 
lean_dec_ref(v_e_1333_);
v_val_1371_ = lean_ctor_get(v___x_1367_, 0);
v_isSharedCheck_1378_ = !lean_is_exclusive(v___x_1367_);
if (v_isSharedCheck_1378_ == 0)
{
v___x_1373_ = v___x_1367_;
v_isShared_1374_ = v_isSharedCheck_1378_;
goto v_resetjp_1372_;
}
else
{
lean_inc(v_val_1371_);
lean_dec(v___x_1367_);
v___x_1373_ = lean_box(0);
v_isShared_1374_ = v_isSharedCheck_1378_;
goto v_resetjp_1372_;
}
v_resetjp_1372_:
{
lean_object* v___x_1376_; 
if (v_isShared_1374_ == 0)
{
lean_ctor_set_tag(v___x_1373_, 0);
v___x_1376_ = v___x_1373_;
goto v_reusejp_1375_;
}
else
{
lean_object* v_reuseFailAlloc_1377_; 
v_reuseFailAlloc_1377_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1377_, 0, v_val_1371_);
v___x_1376_ = v_reuseFailAlloc_1377_;
goto v_reusejp_1375_;
}
v_reusejp_1375_:
{
return v___x_1376_;
}
}
}
v___jp_1341_:
{
if (lean_obj_tag(v___y_1342_) == 0)
{
lean_object* v_a_1343_; lean_object* v___x_1345_; uint8_t v_isShared_1346_; uint8_t v_isSharedCheck_1364_; 
v_a_1343_ = lean_ctor_get(v___y_1342_, 0);
v_isSharedCheck_1364_ = !lean_is_exclusive(v___y_1342_);
if (v_isSharedCheck_1364_ == 0)
{
v___x_1345_ = v___y_1342_;
v_isShared_1346_ = v_isSharedCheck_1364_;
goto v_resetjp_1344_;
}
else
{
lean_inc(v_a_1343_);
lean_dec(v___y_1342_);
v___x_1345_ = lean_box(0);
v_isShared_1346_ = v_isSharedCheck_1364_;
goto v_resetjp_1344_;
}
v_resetjp_1344_:
{
lean_object* v___x_1347_; lean_object* v_lemmas_1348_; lean_object* v_bvExprCache_1349_; lean_object* v_bvPredCache_1350_; lean_object* v_bvLogicalCache_1351_; lean_object* v___x_1353_; uint8_t v_isShared_1354_; uint8_t v_isSharedCheck_1363_; 
v___x_1347_ = lean_st_ref_take(v_a_1334_);
v_lemmas_1348_ = lean_ctor_get(v___x_1347_, 0);
v_bvExprCache_1349_ = lean_ctor_get(v___x_1347_, 1);
v_bvPredCache_1350_ = lean_ctor_get(v___x_1347_, 2);
v_bvLogicalCache_1351_ = lean_ctor_get(v___x_1347_, 3);
v_isSharedCheck_1363_ = !lean_is_exclusive(v___x_1347_);
if (v_isSharedCheck_1363_ == 0)
{
v___x_1353_ = v___x_1347_;
v_isShared_1354_ = v_isSharedCheck_1363_;
goto v_resetjp_1352_;
}
else
{
lean_inc(v_bvLogicalCache_1351_);
lean_inc(v_bvPredCache_1350_);
lean_inc(v_bvExprCache_1349_);
lean_inc(v_lemmas_1348_);
lean_dec(v___x_1347_);
v___x_1353_ = lean_box(0);
v_isShared_1354_ = v_isSharedCheck_1363_;
goto v_resetjp_1352_;
}
v_resetjp_1352_:
{
lean_object* v___x_1355_; lean_object* v___x_1357_; 
lean_inc(v_a_1343_);
v___x_1355_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13___redArg(v_bvPredCache_1350_, v_e_1333_, v_a_1343_);
if (v_isShared_1354_ == 0)
{
lean_ctor_set(v___x_1353_, 2, v___x_1355_);
v___x_1357_ = v___x_1353_;
goto v_reusejp_1356_;
}
else
{
lean_object* v_reuseFailAlloc_1362_; 
v_reuseFailAlloc_1362_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1362_, 0, v_lemmas_1348_);
lean_ctor_set(v_reuseFailAlloc_1362_, 1, v_bvExprCache_1349_);
lean_ctor_set(v_reuseFailAlloc_1362_, 2, v___x_1355_);
lean_ctor_set(v_reuseFailAlloc_1362_, 3, v_bvLogicalCache_1351_);
v___x_1357_ = v_reuseFailAlloc_1362_;
goto v_reusejp_1356_;
}
v_reusejp_1356_:
{
lean_object* v___x_1358_; lean_object* v___x_1360_; 
v___x_1358_ = lean_st_ref_set(v_a_1334_, v___x_1357_);
if (v_isShared_1346_ == 0)
{
v___x_1360_ = v___x_1345_;
goto v_reusejp_1359_;
}
else
{
lean_object* v_reuseFailAlloc_1361_; 
v_reuseFailAlloc_1361_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1361_, 0, v_a_1343_);
v___x_1360_ = v_reuseFailAlloc_1361_;
goto v_reusejp_1359_;
}
v_reusejp_1359_:
{
return v___x_1360_;
}
}
}
}
}
else
{
lean_dec_ref(v_e_1333_);
return v___y_1342_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_of(lean_object* v_origExpr_1379_, lean_object* v_a_1380_, lean_object* v_a_1381_, lean_object* v_a_1382_, lean_object* v_a_1383_, lean_object* v_a_1384_, lean_object* v_a_1385_){
_start:
{
lean_object* v___x_1387_; 
v___x_1387_ = l_Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVPredCache___at___00Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_of_spec__5(v_origExpr_1379_, v_a_1380_, v_a_1381_, v_a_1382_, v_a_1383_, v_a_1384_, v_a_1385_);
return v___x_1387_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goPred(lean_object* v_origExpr_1388_, lean_object* v_a_1389_, lean_object* v_a_1390_, lean_object* v_a_1391_, lean_object* v_a_1392_, lean_object* v_a_1393_, lean_object* v_a_1394_){
_start:
{
lean_object* v___x_1396_; 
v___x_1396_ = l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_of(v_origExpr_1388_, v_a_1389_, v_a_1390_, v_a_1391_, v_a_1392_, v_a_1393_, v_a_1394_);
if (lean_obj_tag(v___x_1396_) == 0)
{
lean_object* v_a_1397_; lean_object* v___x_1399_; uint8_t v_isShared_1400_; uint8_t v_isSharedCheck_1430_; 
v_a_1397_ = lean_ctor_get(v___x_1396_, 0);
v_isSharedCheck_1430_ = !lean_is_exclusive(v___x_1396_);
if (v_isSharedCheck_1430_ == 0)
{
v___x_1399_ = v___x_1396_;
v_isShared_1400_ = v_isSharedCheck_1430_;
goto v_resetjp_1398_;
}
else
{
lean_inc(v_a_1397_);
lean_dec(v___x_1396_);
v___x_1399_ = lean_box(0);
v_isShared_1400_ = v_isSharedCheck_1430_;
goto v_resetjp_1398_;
}
v_resetjp_1398_:
{
if (lean_obj_tag(v_a_1397_) == 1)
{
lean_object* v_val_1401_; lean_object* v___x_1403_; uint8_t v_isShared_1404_; uint8_t v_isSharedCheck_1425_; 
lean_del_object(v___x_1399_);
v_val_1401_ = lean_ctor_get(v_a_1397_, 0);
v_isSharedCheck_1425_ = !lean_is_exclusive(v_a_1397_);
if (v_isSharedCheck_1425_ == 0)
{
v___x_1403_ = v_a_1397_;
v_isShared_1404_ = v_isSharedCheck_1425_;
goto v_resetjp_1402_;
}
else
{
lean_inc(v_val_1401_);
lean_dec(v_a_1397_);
v___x_1403_ = lean_box(0);
v_isShared_1404_ = v_isSharedCheck_1425_;
goto v_resetjp_1402_;
}
v_resetjp_1402_:
{
lean_object* v___x_1405_; 
v___x_1405_ = l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_ofPred___redArg(v_val_1401_);
if (lean_obj_tag(v___x_1405_) == 0)
{
lean_object* v_a_1406_; lean_object* v___x_1408_; uint8_t v_isShared_1409_; uint8_t v_isSharedCheck_1416_; 
v_a_1406_ = lean_ctor_get(v___x_1405_, 0);
v_isSharedCheck_1416_ = !lean_is_exclusive(v___x_1405_);
if (v_isSharedCheck_1416_ == 0)
{
v___x_1408_ = v___x_1405_;
v_isShared_1409_ = v_isSharedCheck_1416_;
goto v_resetjp_1407_;
}
else
{
lean_inc(v_a_1406_);
lean_dec(v___x_1405_);
v___x_1408_ = lean_box(0);
v_isShared_1409_ = v_isSharedCheck_1416_;
goto v_resetjp_1407_;
}
v_resetjp_1407_:
{
lean_object* v___x_1411_; 
if (v_isShared_1404_ == 0)
{
lean_ctor_set(v___x_1403_, 0, v_a_1406_);
v___x_1411_ = v___x_1403_;
goto v_reusejp_1410_;
}
else
{
lean_object* v_reuseFailAlloc_1415_; 
v_reuseFailAlloc_1415_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1415_, 0, v_a_1406_);
v___x_1411_ = v_reuseFailAlloc_1415_;
goto v_reusejp_1410_;
}
v_reusejp_1410_:
{
lean_object* v___x_1413_; 
if (v_isShared_1409_ == 0)
{
lean_ctor_set(v___x_1408_, 0, v___x_1411_);
v___x_1413_ = v___x_1408_;
goto v_reusejp_1412_;
}
else
{
lean_object* v_reuseFailAlloc_1414_; 
v_reuseFailAlloc_1414_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1414_, 0, v___x_1411_);
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
else
{
lean_object* v_a_1417_; lean_object* v___x_1419_; uint8_t v_isShared_1420_; uint8_t v_isSharedCheck_1424_; 
lean_del_object(v___x_1403_);
v_a_1417_ = lean_ctor_get(v___x_1405_, 0);
v_isSharedCheck_1424_ = !lean_is_exclusive(v___x_1405_);
if (v_isSharedCheck_1424_ == 0)
{
v___x_1419_ = v___x_1405_;
v_isShared_1420_ = v_isSharedCheck_1424_;
goto v_resetjp_1418_;
}
else
{
lean_inc(v_a_1417_);
lean_dec(v___x_1405_);
v___x_1419_ = lean_box(0);
v_isShared_1420_ = v_isSharedCheck_1424_;
goto v_resetjp_1418_;
}
v_resetjp_1418_:
{
lean_object* v___x_1422_; 
if (v_isShared_1420_ == 0)
{
v___x_1422_ = v___x_1419_;
goto v_reusejp_1421_;
}
else
{
lean_object* v_reuseFailAlloc_1423_; 
v_reuseFailAlloc_1423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1423_, 0, v_a_1417_);
v___x_1422_ = v_reuseFailAlloc_1423_;
goto v_reusejp_1421_;
}
v_reusejp_1421_:
{
return v___x_1422_;
}
}
}
}
}
else
{
lean_object* v___x_1426_; lean_object* v___x_1428_; 
lean_dec(v_a_1397_);
v___x_1426_ = lean_box(0);
if (v_isShared_1400_ == 0)
{
lean_ctor_set(v___x_1399_, 0, v___x_1426_);
v___x_1428_ = v___x_1399_;
goto v_reusejp_1427_;
}
else
{
lean_object* v_reuseFailAlloc_1429_; 
v_reuseFailAlloc_1429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1429_, 0, v___x_1426_);
v___x_1428_ = v_reuseFailAlloc_1429_;
goto v_reusejp_1427_;
}
v_reusejp_1427_:
{
return v___x_1428_;
}
}
}
}
else
{
lean_object* v_a_1431_; lean_object* v___x_1433_; uint8_t v_isShared_1434_; uint8_t v_isSharedCheck_1438_; 
v_a_1431_ = lean_ctor_get(v___x_1396_, 0);
v_isSharedCheck_1438_ = !lean_is_exclusive(v___x_1396_);
if (v_isSharedCheck_1438_ == 0)
{
v___x_1433_ = v___x_1396_;
v_isShared_1434_ = v_isSharedCheck_1438_;
goto v_resetjp_1432_;
}
else
{
lean_inc(v_a_1431_);
lean_dec(v___x_1396_);
v___x_1433_ = lean_box(0);
v_isShared_1434_ = v_isSharedCheck_1438_;
goto v_resetjp_1432_;
}
v_resetjp_1432_:
{
lean_object* v___x_1436_; 
if (v_isShared_1434_ == 0)
{
v___x_1436_ = v___x_1433_;
goto v_reusejp_1435_;
}
else
{
lean_object* v_reuseFailAlloc_1437_; 
v_reuseFailAlloc_1437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1437_, 0, v_a_1431_);
v___x_1436_ = v_reuseFailAlloc_1437_;
goto v_reusejp_1435_;
}
v_reusejp_1435_:
{
return v___x_1436_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_gateReflection(lean_object* v_lhsExpr_1451_, lean_object* v_rhsExpr_1452_, uint8_t v_gate_1453_, lean_object* v_origExpr_1454_, lean_object* v_a_1455_, lean_object* v_a_1456_, lean_object* v_a_1457_, lean_object* v_a_1458_, lean_object* v_a_1459_, lean_object* v_a_1460_){
_start:
{
lean_object* v___x_1462_; 
lean_inc_ref(v_lhsExpr_1451_);
v___x_1462_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom(v_lhsExpr_1451_, v_a_1455_, v_a_1456_, v_a_1457_, v_a_1458_, v_a_1459_, v_a_1460_);
if (lean_obj_tag(v___x_1462_) == 0)
{
lean_object* v_a_1463_; lean_object* v___x_1465_; uint8_t v_isShared_1466_; uint8_t v_isSharedCheck_1507_; 
v_a_1463_ = lean_ctor_get(v___x_1462_, 0);
v_isSharedCheck_1507_ = !lean_is_exclusive(v___x_1462_);
if (v_isSharedCheck_1507_ == 0)
{
v___x_1465_ = v___x_1462_;
v_isShared_1466_ = v_isSharedCheck_1507_;
goto v_resetjp_1464_;
}
else
{
lean_inc(v_a_1463_);
lean_dec(v___x_1462_);
v___x_1465_ = lean_box(0);
v_isShared_1466_ = v_isSharedCheck_1507_;
goto v_resetjp_1464_;
}
v_resetjp_1464_:
{
if (lean_obj_tag(v_a_1463_) == 1)
{
lean_object* v_val_1467_; lean_object* v___x_1468_; 
lean_del_object(v___x_1465_);
v_val_1467_ = lean_ctor_get(v_a_1463_, 0);
lean_inc(v_val_1467_);
lean_dec_ref(v_a_1463_);
lean_inc_ref(v_rhsExpr_1452_);
v___x_1468_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom(v_rhsExpr_1452_, v_a_1455_, v_a_1456_, v_a_1457_, v_a_1458_, v_a_1459_, v_a_1460_);
if (lean_obj_tag(v___x_1468_) == 0)
{
lean_object* v_a_1469_; lean_object* v___x_1471_; uint8_t v_isShared_1472_; uint8_t v_isSharedCheck_1502_; 
v_a_1469_ = lean_ctor_get(v___x_1468_, 0);
v_isSharedCheck_1502_ = !lean_is_exclusive(v___x_1468_);
if (v_isSharedCheck_1502_ == 0)
{
v___x_1471_ = v___x_1468_;
v_isShared_1472_ = v_isSharedCheck_1502_;
goto v_resetjp_1470_;
}
else
{
lean_inc(v_a_1469_);
lean_dec(v___x_1468_);
v___x_1471_ = lean_box(0);
v_isShared_1472_ = v_isSharedCheck_1502_;
goto v_resetjp_1470_;
}
v_resetjp_1470_:
{
if (lean_obj_tag(v_a_1469_) == 1)
{
lean_object* v_val_1473_; lean_object* v___x_1475_; uint8_t v_isShared_1476_; uint8_t v_isSharedCheck_1497_; 
lean_del_object(v___x_1471_);
v_val_1473_ = lean_ctor_get(v_a_1469_, 0);
v_isSharedCheck_1497_ = !lean_is_exclusive(v_a_1469_);
if (v_isSharedCheck_1497_ == 0)
{
v___x_1475_ = v_a_1469_;
v_isShared_1476_ = v_isSharedCheck_1497_;
goto v_resetjp_1474_;
}
else
{
lean_inc(v_val_1473_);
lean_dec(v_a_1469_);
v___x_1475_ = lean_box(0);
v_isShared_1476_ = v_isSharedCheck_1497_;
goto v_resetjp_1474_;
}
v_resetjp_1474_:
{
lean_object* v___x_1477_; 
v___x_1477_ = l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_mkGate___redArg(v_val_1467_, v_val_1473_, v_lhsExpr_1451_, v_rhsExpr_1452_, v_gate_1453_, v_origExpr_1454_);
if (lean_obj_tag(v___x_1477_) == 0)
{
lean_object* v_a_1478_; lean_object* v___x_1480_; uint8_t v_isShared_1481_; uint8_t v_isSharedCheck_1488_; 
v_a_1478_ = lean_ctor_get(v___x_1477_, 0);
v_isSharedCheck_1488_ = !lean_is_exclusive(v___x_1477_);
if (v_isSharedCheck_1488_ == 0)
{
v___x_1480_ = v___x_1477_;
v_isShared_1481_ = v_isSharedCheck_1488_;
goto v_resetjp_1479_;
}
else
{
lean_inc(v_a_1478_);
lean_dec(v___x_1477_);
v___x_1480_ = lean_box(0);
v_isShared_1481_ = v_isSharedCheck_1488_;
goto v_resetjp_1479_;
}
v_resetjp_1479_:
{
lean_object* v___x_1483_; 
if (v_isShared_1476_ == 0)
{
lean_ctor_set(v___x_1475_, 0, v_a_1478_);
v___x_1483_ = v___x_1475_;
goto v_reusejp_1482_;
}
else
{
lean_object* v_reuseFailAlloc_1487_; 
v_reuseFailAlloc_1487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1487_, 0, v_a_1478_);
v___x_1483_ = v_reuseFailAlloc_1487_;
goto v_reusejp_1482_;
}
v_reusejp_1482_:
{
lean_object* v___x_1485_; 
if (v_isShared_1481_ == 0)
{
lean_ctor_set(v___x_1480_, 0, v___x_1483_);
v___x_1485_ = v___x_1480_;
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
else
{
lean_object* v_a_1489_; lean_object* v___x_1491_; uint8_t v_isShared_1492_; uint8_t v_isSharedCheck_1496_; 
lean_del_object(v___x_1475_);
v_a_1489_ = lean_ctor_get(v___x_1477_, 0);
v_isSharedCheck_1496_ = !lean_is_exclusive(v___x_1477_);
if (v_isSharedCheck_1496_ == 0)
{
v___x_1491_ = v___x_1477_;
v_isShared_1492_ = v_isSharedCheck_1496_;
goto v_resetjp_1490_;
}
else
{
lean_inc(v_a_1489_);
lean_dec(v___x_1477_);
v___x_1491_ = lean_box(0);
v_isShared_1492_ = v_isSharedCheck_1496_;
goto v_resetjp_1490_;
}
v_resetjp_1490_:
{
lean_object* v___x_1494_; 
if (v_isShared_1492_ == 0)
{
v___x_1494_ = v___x_1491_;
goto v_reusejp_1493_;
}
else
{
lean_object* v_reuseFailAlloc_1495_; 
v_reuseFailAlloc_1495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1495_, 0, v_a_1489_);
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
lean_object* v___x_1498_; lean_object* v___x_1500_; 
lean_dec(v_a_1469_);
lean_dec(v_val_1467_);
lean_dec_ref(v_origExpr_1454_);
lean_dec_ref(v_rhsExpr_1452_);
lean_dec_ref(v_lhsExpr_1451_);
v___x_1498_ = lean_box(0);
if (v_isShared_1472_ == 0)
{
lean_ctor_set(v___x_1471_, 0, v___x_1498_);
v___x_1500_ = v___x_1471_;
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
else
{
lean_dec(v_val_1467_);
lean_dec_ref(v_origExpr_1454_);
lean_dec_ref(v_rhsExpr_1452_);
lean_dec_ref(v_lhsExpr_1451_);
return v___x_1468_;
}
}
else
{
lean_object* v___x_1503_; lean_object* v___x_1505_; 
lean_dec(v_a_1463_);
lean_dec_ref(v_origExpr_1454_);
lean_dec_ref(v_rhsExpr_1452_);
lean_dec_ref(v_lhsExpr_1451_);
v___x_1503_ = lean_box(0);
if (v_isShared_1466_ == 0)
{
lean_ctor_set(v___x_1465_, 0, v___x_1503_);
v___x_1505_ = v___x_1465_;
goto v_reusejp_1504_;
}
else
{
lean_object* v_reuseFailAlloc_1506_; 
v_reuseFailAlloc_1506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1506_, 0, v___x_1503_);
v___x_1505_ = v_reuseFailAlloc_1506_;
goto v_reusejp_1504_;
}
v_reusejp_1504_:
{
return v___x_1505_;
}
}
}
}
else
{
lean_dec_ref(v_origExpr_1454_);
lean_dec_ref(v_rhsExpr_1452_);
lean_dec_ref(v_lhsExpr_1451_);
return v___x_1462_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_go(lean_object* v_origExpr_1508_, lean_object* v_a_1509_, lean_object* v_a_1510_, lean_object* v_a_1511_, lean_object* v_a_1512_, lean_object* v_a_1513_, lean_object* v_a_1514_){
_start:
{
lean_object* v___x_1519_; 
lean_inc_ref(v_origExpr_1508_);
v___x_1519_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_origExpr_1508_, v_a_1512_);
if (lean_obj_tag(v___x_1519_) == 0)
{
lean_object* v_a_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; uint8_t v___x_1523_; 
v_a_1520_ = lean_ctor_get(v___x_1519_, 0);
lean_inc(v_a_1520_);
lean_dec_ref(v___x_1519_);
v___x_1521_ = l_Lean_Expr_cleanupAnnotations(v_a_1520_);
v___x_1522_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_go___closed__2));
v___x_1523_ = l_Lean_Expr_isConstOf(v___x_1521_, v___x_1522_);
if (v___x_1523_ == 0)
{
lean_object* v___x_1524_; uint8_t v___x_1525_; 
v___x_1524_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_go___closed__4));
v___x_1525_ = l_Lean_Expr_isConstOf(v___x_1521_, v___x_1524_);
if (v___x_1525_ == 0)
{
uint8_t v___x_1526_; 
v___x_1526_ = l_Lean_Expr_isApp(v___x_1521_);
if (v___x_1526_ == 0)
{
lean_object* v___x_1527_; 
lean_dec_ref(v___x_1521_);
v___x_1527_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goPred(v_origExpr_1508_, v_a_1509_, v_a_1510_, v_a_1511_, v_a_1512_, v_a_1513_, v_a_1514_);
return v___x_1527_;
}
else
{
lean_object* v_arg_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; uint8_t v___x_1531_; 
v_arg_1528_ = lean_ctor_get(v___x_1521_, 1);
lean_inc_ref(v_arg_1528_);
v___x_1529_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1521_);
v___x_1530_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_go___closed__5));
v___x_1531_ = l_Lean_Expr_isConstOf(v___x_1529_, v___x_1530_);
if (v___x_1531_ == 0)
{
uint8_t v___x_1532_; 
v___x_1532_ = l_Lean_Expr_isApp(v___x_1529_);
if (v___x_1532_ == 0)
{
lean_object* v___x_1533_; 
lean_dec_ref(v___x_1529_);
lean_dec_ref(v_arg_1528_);
v___x_1533_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goPred(v_origExpr_1508_, v_a_1509_, v_a_1510_, v_a_1511_, v_a_1512_, v_a_1513_, v_a_1514_);
return v___x_1533_;
}
else
{
lean_object* v_arg_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; uint8_t v___x_1537_; 
v_arg_1534_ = lean_ctor_get(v___x_1529_, 1);
lean_inc_ref(v_arg_1534_);
v___x_1535_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1529_);
v___x_1536_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_go___closed__6));
v___x_1537_ = l_Lean_Expr_isConstOf(v___x_1535_, v___x_1536_);
if (v___x_1537_ == 0)
{
lean_object* v___x_1538_; uint8_t v___x_1539_; 
v___x_1538_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_go___closed__7));
v___x_1539_ = l_Lean_Expr_isConstOf(v___x_1535_, v___x_1538_);
if (v___x_1539_ == 0)
{
uint8_t v___x_1540_; 
v___x_1540_ = l_Lean_Expr_isApp(v___x_1535_);
if (v___x_1540_ == 0)
{
lean_object* v___x_1541_; 
lean_dec_ref(v___x_1535_);
lean_dec_ref(v_arg_1534_);
lean_dec_ref(v_arg_1528_);
v___x_1541_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goPred(v_origExpr_1508_, v_a_1509_, v_a_1510_, v_a_1511_, v_a_1512_, v_a_1513_, v_a_1514_);
return v___x_1541_;
}
else
{
lean_object* v_arg_1542_; lean_object* v___x_1543_; uint8_t v___x_1544_; 
v_arg_1542_ = lean_ctor_get(v___x_1535_, 1);
lean_inc_ref(v_arg_1542_);
v___x_1543_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1535_);
v___x_1544_ = l_Lean_Expr_isApp(v___x_1543_);
if (v___x_1544_ == 0)
{
lean_object* v___x_1545_; 
lean_dec_ref(v___x_1543_);
lean_dec_ref(v_arg_1542_);
lean_dec_ref(v_arg_1534_);
lean_dec_ref(v_arg_1528_);
v___x_1545_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goPred(v_origExpr_1508_, v_a_1509_, v_a_1510_, v_a_1511_, v_a_1512_, v_a_1513_, v_a_1514_);
return v___x_1545_;
}
else
{
lean_object* v_arg_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; uint8_t v___x_1549_; 
v_arg_1546_ = lean_ctor_get(v___x_1543_, 1);
lean_inc_ref(v_arg_1546_);
v___x_1547_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1543_);
v___x_1548_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_go___closed__9));
v___x_1549_ = l_Lean_Expr_isConstOf(v___x_1547_, v___x_1548_);
if (v___x_1549_ == 0)
{
lean_object* v___x_1550_; uint8_t v___x_1551_; 
lean_dec_ref(v_arg_1542_);
v___x_1550_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_of_go___closed__7));
v___x_1551_ = l_Lean_Expr_isConstOf(v___x_1547_, v___x_1550_);
lean_dec_ref(v___x_1547_);
if (v___x_1551_ == 0)
{
lean_object* v___x_1552_; 
lean_dec_ref(v_arg_1546_);
lean_dec_ref(v_arg_1534_);
lean_dec_ref(v_arg_1528_);
v___x_1552_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goPred(v_origExpr_1508_, v_a_1509_, v_a_1510_, v_a_1511_, v_a_1512_, v_a_1513_, v_a_1514_);
return v___x_1552_;
}
else
{
lean_object* v___x_1553_; 
v___x_1553_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_arg_1546_, v_a_1512_);
if (lean_obj_tag(v___x_1553_) == 0)
{
lean_object* v_a_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; uint8_t v___x_1557_; 
v_a_1554_ = lean_ctor_get(v___x_1553_, 0);
lean_inc(v_a_1554_);
lean_dec_ref(v___x_1553_);
v___x_1555_ = l_Lean_Expr_cleanupAnnotations(v_a_1554_);
v___x_1556_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_go___closed__10));
v___x_1557_ = l_Lean_Expr_isConstOf(v___x_1555_, v___x_1556_);
if (v___x_1557_ == 0)
{
uint8_t v___x_1558_; 
lean_dec_ref(v_arg_1534_);
lean_dec_ref(v_arg_1528_);
v___x_1558_ = l_Lean_Expr_isApp(v___x_1555_);
if (v___x_1558_ == 0)
{
lean_dec_ref(v___x_1555_);
lean_dec_ref(v_origExpr_1508_);
goto v___jp_1516_;
}
else
{
lean_object* v___x_1559_; lean_object* v___x_1560_; uint8_t v___x_1561_; 
v___x_1559_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1555_);
v___x_1560_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_of_go___closed__8));
v___x_1561_ = l_Lean_Expr_isConstOf(v___x_1559_, v___x_1560_);
lean_dec_ref(v___x_1559_);
if (v___x_1561_ == 0)
{
lean_dec_ref(v_origExpr_1508_);
goto v___jp_1516_;
}
else
{
lean_object* v___x_1562_; 
v___x_1562_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goPred(v_origExpr_1508_, v_a_1509_, v_a_1510_, v_a_1511_, v_a_1512_, v_a_1513_, v_a_1514_);
return v___x_1562_;
}
}
}
else
{
uint8_t v___x_1563_; lean_object* v___x_1564_; 
lean_dec_ref(v___x_1555_);
v___x_1563_ = 2;
v___x_1564_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_gateReflection(v_arg_1534_, v_arg_1528_, v___x_1563_, v_origExpr_1508_, v_a_1509_, v_a_1510_, v_a_1511_, v_a_1512_, v_a_1513_, v_a_1514_);
return v___x_1564_;
}
}
else
{
lean_object* v_a_1565_; lean_object* v___x_1567_; uint8_t v_isShared_1568_; uint8_t v_isSharedCheck_1572_; 
lean_dec_ref(v_arg_1534_);
lean_dec_ref(v_arg_1528_);
lean_dec_ref(v_origExpr_1508_);
v_a_1565_ = lean_ctor_get(v___x_1553_, 0);
v_isSharedCheck_1572_ = !lean_is_exclusive(v___x_1553_);
if (v_isSharedCheck_1572_ == 0)
{
v___x_1567_ = v___x_1553_;
v_isShared_1568_ = v_isSharedCheck_1572_;
goto v_resetjp_1566_;
}
else
{
lean_inc(v_a_1565_);
lean_dec(v___x_1553_);
v___x_1567_ = lean_box(0);
v_isShared_1568_ = v_isSharedCheck_1572_;
goto v_resetjp_1566_;
}
v_resetjp_1566_:
{
lean_object* v___x_1570_; 
if (v_isShared_1568_ == 0)
{
v___x_1570_ = v___x_1567_;
goto v_reusejp_1569_;
}
else
{
lean_object* v_reuseFailAlloc_1571_; 
v_reuseFailAlloc_1571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1571_, 0, v_a_1565_);
v___x_1570_ = v_reuseFailAlloc_1571_;
goto v_reusejp_1569_;
}
v_reusejp_1569_:
{
return v___x_1570_;
}
}
}
}
}
else
{
lean_object* v___x_1573_; 
lean_dec_ref(v___x_1547_);
lean_dec_ref(v_arg_1546_);
lean_inc_ref(v_arg_1542_);
v___x_1573_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom(v_arg_1542_, v_a_1509_, v_a_1510_, v_a_1511_, v_a_1512_, v_a_1513_, v_a_1514_);
if (lean_obj_tag(v___x_1573_) == 0)
{
lean_object* v_a_1574_; lean_object* v___x_1576_; uint8_t v_isShared_1577_; uint8_t v_isSharedCheck_1629_; 
v_a_1574_ = lean_ctor_get(v___x_1573_, 0);
v_isSharedCheck_1629_ = !lean_is_exclusive(v___x_1573_);
if (v_isSharedCheck_1629_ == 0)
{
v___x_1576_ = v___x_1573_;
v_isShared_1577_ = v_isSharedCheck_1629_;
goto v_resetjp_1575_;
}
else
{
lean_inc(v_a_1574_);
lean_dec(v___x_1573_);
v___x_1576_ = lean_box(0);
v_isShared_1577_ = v_isSharedCheck_1629_;
goto v_resetjp_1575_;
}
v_resetjp_1575_:
{
if (lean_obj_tag(v_a_1574_) == 1)
{
lean_object* v_val_1578_; lean_object* v___x_1579_; 
lean_del_object(v___x_1576_);
v_val_1578_ = lean_ctor_get(v_a_1574_, 0);
lean_inc(v_val_1578_);
lean_dec_ref(v_a_1574_);
lean_inc_ref(v_arg_1534_);
v___x_1579_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom(v_arg_1534_, v_a_1509_, v_a_1510_, v_a_1511_, v_a_1512_, v_a_1513_, v_a_1514_);
if (lean_obj_tag(v___x_1579_) == 0)
{
lean_object* v_a_1580_; lean_object* v___x_1582_; uint8_t v_isShared_1583_; uint8_t v_isSharedCheck_1624_; 
v_a_1580_ = lean_ctor_get(v___x_1579_, 0);
v_isSharedCheck_1624_ = !lean_is_exclusive(v___x_1579_);
if (v_isSharedCheck_1624_ == 0)
{
v___x_1582_ = v___x_1579_;
v_isShared_1583_ = v_isSharedCheck_1624_;
goto v_resetjp_1581_;
}
else
{
lean_inc(v_a_1580_);
lean_dec(v___x_1579_);
v___x_1582_ = lean_box(0);
v_isShared_1583_ = v_isSharedCheck_1624_;
goto v_resetjp_1581_;
}
v_resetjp_1581_:
{
if (lean_obj_tag(v_a_1580_) == 1)
{
lean_object* v_val_1584_; lean_object* v___x_1585_; 
lean_del_object(v___x_1582_);
v_val_1584_ = lean_ctor_get(v_a_1580_, 0);
lean_inc(v_val_1584_);
lean_dec_ref(v_a_1580_);
lean_inc_ref(v_arg_1528_);
v___x_1585_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom(v_arg_1528_, v_a_1509_, v_a_1510_, v_a_1511_, v_a_1512_, v_a_1513_, v_a_1514_);
if (lean_obj_tag(v___x_1585_) == 0)
{
lean_object* v_a_1586_; lean_object* v___x_1588_; uint8_t v_isShared_1589_; uint8_t v_isSharedCheck_1619_; 
v_a_1586_ = lean_ctor_get(v___x_1585_, 0);
v_isSharedCheck_1619_ = !lean_is_exclusive(v___x_1585_);
if (v_isSharedCheck_1619_ == 0)
{
v___x_1588_ = v___x_1585_;
v_isShared_1589_ = v_isSharedCheck_1619_;
goto v_resetjp_1587_;
}
else
{
lean_inc(v_a_1586_);
lean_dec(v___x_1585_);
v___x_1588_ = lean_box(0);
v_isShared_1589_ = v_isSharedCheck_1619_;
goto v_resetjp_1587_;
}
v_resetjp_1587_:
{
if (lean_obj_tag(v_a_1586_) == 1)
{
lean_object* v_val_1590_; lean_object* v___x_1592_; uint8_t v_isShared_1593_; uint8_t v_isSharedCheck_1614_; 
lean_del_object(v___x_1588_);
v_val_1590_ = lean_ctor_get(v_a_1586_, 0);
v_isSharedCheck_1614_ = !lean_is_exclusive(v_a_1586_);
if (v_isSharedCheck_1614_ == 0)
{
v___x_1592_ = v_a_1586_;
v_isShared_1593_ = v_isSharedCheck_1614_;
goto v_resetjp_1591_;
}
else
{
lean_inc(v_val_1590_);
lean_dec(v_a_1586_);
v___x_1592_ = lean_box(0);
v_isShared_1593_ = v_isSharedCheck_1614_;
goto v_resetjp_1591_;
}
v_resetjp_1591_:
{
lean_object* v___x_1594_; 
v___x_1594_ = l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_mkIte___redArg(v_val_1578_, v_val_1584_, v_val_1590_, v_arg_1542_, v_arg_1534_, v_arg_1528_, v_origExpr_1508_);
if (lean_obj_tag(v___x_1594_) == 0)
{
lean_object* v_a_1595_; lean_object* v___x_1597_; uint8_t v_isShared_1598_; uint8_t v_isSharedCheck_1605_; 
v_a_1595_ = lean_ctor_get(v___x_1594_, 0);
v_isSharedCheck_1605_ = !lean_is_exclusive(v___x_1594_);
if (v_isSharedCheck_1605_ == 0)
{
v___x_1597_ = v___x_1594_;
v_isShared_1598_ = v_isSharedCheck_1605_;
goto v_resetjp_1596_;
}
else
{
lean_inc(v_a_1595_);
lean_dec(v___x_1594_);
v___x_1597_ = lean_box(0);
v_isShared_1598_ = v_isSharedCheck_1605_;
goto v_resetjp_1596_;
}
v_resetjp_1596_:
{
lean_object* v___x_1600_; 
if (v_isShared_1593_ == 0)
{
lean_ctor_set(v___x_1592_, 0, v_a_1595_);
v___x_1600_ = v___x_1592_;
goto v_reusejp_1599_;
}
else
{
lean_object* v_reuseFailAlloc_1604_; 
v_reuseFailAlloc_1604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1604_, 0, v_a_1595_);
v___x_1600_ = v_reuseFailAlloc_1604_;
goto v_reusejp_1599_;
}
v_reusejp_1599_:
{
lean_object* v___x_1602_; 
if (v_isShared_1598_ == 0)
{
lean_ctor_set(v___x_1597_, 0, v___x_1600_);
v___x_1602_ = v___x_1597_;
goto v_reusejp_1601_;
}
else
{
lean_object* v_reuseFailAlloc_1603_; 
v_reuseFailAlloc_1603_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1603_, 0, v___x_1600_);
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
else
{
lean_object* v_a_1606_; lean_object* v___x_1608_; uint8_t v_isShared_1609_; uint8_t v_isSharedCheck_1613_; 
lean_del_object(v___x_1592_);
v_a_1606_ = lean_ctor_get(v___x_1594_, 0);
v_isSharedCheck_1613_ = !lean_is_exclusive(v___x_1594_);
if (v_isSharedCheck_1613_ == 0)
{
v___x_1608_ = v___x_1594_;
v_isShared_1609_ = v_isSharedCheck_1613_;
goto v_resetjp_1607_;
}
else
{
lean_inc(v_a_1606_);
lean_dec(v___x_1594_);
v___x_1608_ = lean_box(0);
v_isShared_1609_ = v_isSharedCheck_1613_;
goto v_resetjp_1607_;
}
v_resetjp_1607_:
{
lean_object* v___x_1611_; 
if (v_isShared_1609_ == 0)
{
v___x_1611_ = v___x_1608_;
goto v_reusejp_1610_;
}
else
{
lean_object* v_reuseFailAlloc_1612_; 
v_reuseFailAlloc_1612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1612_, 0, v_a_1606_);
v___x_1611_ = v_reuseFailAlloc_1612_;
goto v_reusejp_1610_;
}
v_reusejp_1610_:
{
return v___x_1611_;
}
}
}
}
}
else
{
lean_object* v___x_1615_; lean_object* v___x_1617_; 
lean_dec(v_a_1586_);
lean_dec(v_val_1584_);
lean_dec(v_val_1578_);
lean_dec_ref(v_arg_1542_);
lean_dec_ref(v_arg_1534_);
lean_dec_ref(v_arg_1528_);
lean_dec_ref(v_origExpr_1508_);
v___x_1615_ = lean_box(0);
if (v_isShared_1589_ == 0)
{
lean_ctor_set(v___x_1588_, 0, v___x_1615_);
v___x_1617_ = v___x_1588_;
goto v_reusejp_1616_;
}
else
{
lean_object* v_reuseFailAlloc_1618_; 
v_reuseFailAlloc_1618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1618_, 0, v___x_1615_);
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
else
{
lean_dec(v_val_1584_);
lean_dec(v_val_1578_);
lean_dec_ref(v_arg_1542_);
lean_dec_ref(v_arg_1534_);
lean_dec_ref(v_arg_1528_);
lean_dec_ref(v_origExpr_1508_);
return v___x_1585_;
}
}
else
{
lean_object* v___x_1620_; lean_object* v___x_1622_; 
lean_dec(v_a_1580_);
lean_dec(v_val_1578_);
lean_dec_ref(v_arg_1542_);
lean_dec_ref(v_arg_1534_);
lean_dec_ref(v_arg_1528_);
lean_dec_ref(v_origExpr_1508_);
v___x_1620_ = lean_box(0);
if (v_isShared_1583_ == 0)
{
lean_ctor_set(v___x_1582_, 0, v___x_1620_);
v___x_1622_ = v___x_1582_;
goto v_reusejp_1621_;
}
else
{
lean_object* v_reuseFailAlloc_1623_; 
v_reuseFailAlloc_1623_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1623_, 0, v___x_1620_);
v___x_1622_ = v_reuseFailAlloc_1623_;
goto v_reusejp_1621_;
}
v_reusejp_1621_:
{
return v___x_1622_;
}
}
}
}
else
{
lean_dec(v_val_1578_);
lean_dec_ref(v_arg_1542_);
lean_dec_ref(v_arg_1534_);
lean_dec_ref(v_arg_1528_);
lean_dec_ref(v_origExpr_1508_);
return v___x_1579_;
}
}
else
{
lean_object* v___x_1625_; lean_object* v___x_1627_; 
lean_dec(v_a_1574_);
lean_dec_ref(v_arg_1542_);
lean_dec_ref(v_arg_1534_);
lean_dec_ref(v_arg_1528_);
lean_dec_ref(v_origExpr_1508_);
v___x_1625_ = lean_box(0);
if (v_isShared_1577_ == 0)
{
lean_ctor_set(v___x_1576_, 0, v___x_1625_);
v___x_1627_ = v___x_1576_;
goto v_reusejp_1626_;
}
else
{
lean_object* v_reuseFailAlloc_1628_; 
v_reuseFailAlloc_1628_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1628_, 0, v___x_1625_);
v___x_1627_ = v_reuseFailAlloc_1628_;
goto v_reusejp_1626_;
}
v_reusejp_1626_:
{
return v___x_1627_;
}
}
}
}
else
{
lean_dec_ref(v_arg_1542_);
lean_dec_ref(v_arg_1534_);
lean_dec_ref(v_arg_1528_);
lean_dec_ref(v_origExpr_1508_);
return v___x_1573_;
}
}
}
}
}
else
{
uint8_t v___x_1630_; lean_object* v___x_1631_; 
lean_dec_ref(v___x_1535_);
v___x_1630_ = 0;
v___x_1631_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_gateReflection(v_arg_1534_, v_arg_1528_, v___x_1630_, v_origExpr_1508_, v_a_1509_, v_a_1510_, v_a_1511_, v_a_1512_, v_a_1513_, v_a_1514_);
return v___x_1631_;
}
}
else
{
uint8_t v___x_1632_; lean_object* v___x_1633_; 
lean_dec_ref(v___x_1535_);
v___x_1632_ = 1;
v___x_1633_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_gateReflection(v_arg_1534_, v_arg_1528_, v___x_1632_, v_origExpr_1508_, v_a_1509_, v_a_1510_, v_a_1511_, v_a_1512_, v_a_1513_, v_a_1514_);
return v___x_1633_;
}
}
}
else
{
lean_object* v___x_1634_; 
lean_dec_ref(v___x_1529_);
lean_inc_ref(v_arg_1528_);
v___x_1634_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom(v_arg_1528_, v_a_1509_, v_a_1510_, v_a_1511_, v_a_1512_, v_a_1513_, v_a_1514_);
if (lean_obj_tag(v___x_1634_) == 0)
{
lean_object* v_a_1635_; lean_object* v___x_1637_; uint8_t v_isShared_1638_; uint8_t v_isSharedCheck_1668_; 
v_a_1635_ = lean_ctor_get(v___x_1634_, 0);
v_isSharedCheck_1668_ = !lean_is_exclusive(v___x_1634_);
if (v_isSharedCheck_1668_ == 0)
{
v___x_1637_ = v___x_1634_;
v_isShared_1638_ = v_isSharedCheck_1668_;
goto v_resetjp_1636_;
}
else
{
lean_inc(v_a_1635_);
lean_dec(v___x_1634_);
v___x_1637_ = lean_box(0);
v_isShared_1638_ = v_isSharedCheck_1668_;
goto v_resetjp_1636_;
}
v_resetjp_1636_:
{
if (lean_obj_tag(v_a_1635_) == 1)
{
lean_object* v_val_1639_; lean_object* v___x_1641_; uint8_t v_isShared_1642_; uint8_t v_isSharedCheck_1663_; 
lean_del_object(v___x_1637_);
v_val_1639_ = lean_ctor_get(v_a_1635_, 0);
v_isSharedCheck_1663_ = !lean_is_exclusive(v_a_1635_);
if (v_isSharedCheck_1663_ == 0)
{
v___x_1641_ = v_a_1635_;
v_isShared_1642_ = v_isSharedCheck_1663_;
goto v_resetjp_1640_;
}
else
{
lean_inc(v_val_1639_);
lean_dec(v_a_1635_);
v___x_1641_ = lean_box(0);
v_isShared_1642_ = v_isSharedCheck_1663_;
goto v_resetjp_1640_;
}
v_resetjp_1640_:
{
lean_object* v___x_1643_; 
v___x_1643_ = l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_mkNot___redArg(v_val_1639_, v_arg_1528_, v_origExpr_1508_);
if (lean_obj_tag(v___x_1643_) == 0)
{
lean_object* v_a_1644_; lean_object* v___x_1646_; uint8_t v_isShared_1647_; uint8_t v_isSharedCheck_1654_; 
v_a_1644_ = lean_ctor_get(v___x_1643_, 0);
v_isSharedCheck_1654_ = !lean_is_exclusive(v___x_1643_);
if (v_isSharedCheck_1654_ == 0)
{
v___x_1646_ = v___x_1643_;
v_isShared_1647_ = v_isSharedCheck_1654_;
goto v_resetjp_1645_;
}
else
{
lean_inc(v_a_1644_);
lean_dec(v___x_1643_);
v___x_1646_ = lean_box(0);
v_isShared_1647_ = v_isSharedCheck_1654_;
goto v_resetjp_1645_;
}
v_resetjp_1645_:
{
lean_object* v___x_1649_; 
if (v_isShared_1642_ == 0)
{
lean_ctor_set(v___x_1641_, 0, v_a_1644_);
v___x_1649_ = v___x_1641_;
goto v_reusejp_1648_;
}
else
{
lean_object* v_reuseFailAlloc_1653_; 
v_reuseFailAlloc_1653_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1653_, 0, v_a_1644_);
v___x_1649_ = v_reuseFailAlloc_1653_;
goto v_reusejp_1648_;
}
v_reusejp_1648_:
{
lean_object* v___x_1651_; 
if (v_isShared_1647_ == 0)
{
lean_ctor_set(v___x_1646_, 0, v___x_1649_);
v___x_1651_ = v___x_1646_;
goto v_reusejp_1650_;
}
else
{
lean_object* v_reuseFailAlloc_1652_; 
v_reuseFailAlloc_1652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1652_, 0, v___x_1649_);
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
else
{
lean_object* v_a_1655_; lean_object* v___x_1657_; uint8_t v_isShared_1658_; uint8_t v_isSharedCheck_1662_; 
lean_del_object(v___x_1641_);
v_a_1655_ = lean_ctor_get(v___x_1643_, 0);
v_isSharedCheck_1662_ = !lean_is_exclusive(v___x_1643_);
if (v_isSharedCheck_1662_ == 0)
{
v___x_1657_ = v___x_1643_;
v_isShared_1658_ = v_isSharedCheck_1662_;
goto v_resetjp_1656_;
}
else
{
lean_inc(v_a_1655_);
lean_dec(v___x_1643_);
v___x_1657_ = lean_box(0);
v_isShared_1658_ = v_isSharedCheck_1662_;
goto v_resetjp_1656_;
}
v_resetjp_1656_:
{
lean_object* v___x_1660_; 
if (v_isShared_1658_ == 0)
{
v___x_1660_ = v___x_1657_;
goto v_reusejp_1659_;
}
else
{
lean_object* v_reuseFailAlloc_1661_; 
v_reuseFailAlloc_1661_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1661_, 0, v_a_1655_);
v___x_1660_ = v_reuseFailAlloc_1661_;
goto v_reusejp_1659_;
}
v_reusejp_1659_:
{
return v___x_1660_;
}
}
}
}
}
else
{
lean_object* v___x_1664_; lean_object* v___x_1666_; 
lean_dec(v_a_1635_);
lean_dec_ref(v_arg_1528_);
lean_dec_ref(v_origExpr_1508_);
v___x_1664_ = lean_box(0);
if (v_isShared_1638_ == 0)
{
lean_ctor_set(v___x_1637_, 0, v___x_1664_);
v___x_1666_ = v___x_1637_;
goto v_reusejp_1665_;
}
else
{
lean_object* v_reuseFailAlloc_1667_; 
v_reuseFailAlloc_1667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1667_, 0, v___x_1664_);
v___x_1666_ = v_reuseFailAlloc_1667_;
goto v_reusejp_1665_;
}
v_reusejp_1665_:
{
return v___x_1666_;
}
}
}
}
else
{
lean_dec_ref(v_arg_1528_);
lean_dec_ref(v_origExpr_1508_);
return v___x_1634_;
}
}
}
}
else
{
lean_object* v___x_1669_; 
lean_dec_ref(v___x_1521_);
lean_dec_ref(v_origExpr_1508_);
v___x_1669_ = l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_mkBoolConst___redArg(v___x_1525_);
if (lean_obj_tag(v___x_1669_) == 0)
{
lean_object* v_a_1670_; lean_object* v___x_1672_; uint8_t v_isShared_1673_; uint8_t v_isSharedCheck_1678_; 
v_a_1670_ = lean_ctor_get(v___x_1669_, 0);
v_isSharedCheck_1678_ = !lean_is_exclusive(v___x_1669_);
if (v_isSharedCheck_1678_ == 0)
{
v___x_1672_ = v___x_1669_;
v_isShared_1673_ = v_isSharedCheck_1678_;
goto v_resetjp_1671_;
}
else
{
lean_inc(v_a_1670_);
lean_dec(v___x_1669_);
v___x_1672_ = lean_box(0);
v_isShared_1673_ = v_isSharedCheck_1678_;
goto v_resetjp_1671_;
}
v_resetjp_1671_:
{
lean_object* v___x_1674_; lean_object* v___x_1676_; 
v___x_1674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1674_, 0, v_a_1670_);
if (v_isShared_1673_ == 0)
{
lean_ctor_set(v___x_1672_, 0, v___x_1674_);
v___x_1676_ = v___x_1672_;
goto v_reusejp_1675_;
}
else
{
lean_object* v_reuseFailAlloc_1677_; 
v_reuseFailAlloc_1677_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1677_, 0, v___x_1674_);
v___x_1676_ = v_reuseFailAlloc_1677_;
goto v_reusejp_1675_;
}
v_reusejp_1675_:
{
return v___x_1676_;
}
}
}
else
{
lean_object* v_a_1679_; lean_object* v___x_1681_; uint8_t v_isShared_1682_; uint8_t v_isSharedCheck_1686_; 
v_a_1679_ = lean_ctor_get(v___x_1669_, 0);
v_isSharedCheck_1686_ = !lean_is_exclusive(v___x_1669_);
if (v_isSharedCheck_1686_ == 0)
{
v___x_1681_ = v___x_1669_;
v_isShared_1682_ = v_isSharedCheck_1686_;
goto v_resetjp_1680_;
}
else
{
lean_inc(v_a_1679_);
lean_dec(v___x_1669_);
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
}
else
{
uint8_t v___x_1687_; lean_object* v___x_1688_; 
lean_dec_ref(v___x_1521_);
lean_dec_ref(v_origExpr_1508_);
v___x_1687_ = 0;
v___x_1688_ = l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_mkBoolConst___redArg(v___x_1687_);
if (lean_obj_tag(v___x_1688_) == 0)
{
lean_object* v_a_1689_; lean_object* v___x_1691_; uint8_t v_isShared_1692_; uint8_t v_isSharedCheck_1697_; 
v_a_1689_ = lean_ctor_get(v___x_1688_, 0);
v_isSharedCheck_1697_ = !lean_is_exclusive(v___x_1688_);
if (v_isSharedCheck_1697_ == 0)
{
v___x_1691_ = v___x_1688_;
v_isShared_1692_ = v_isSharedCheck_1697_;
goto v_resetjp_1690_;
}
else
{
lean_inc(v_a_1689_);
lean_dec(v___x_1688_);
v___x_1691_ = lean_box(0);
v_isShared_1692_ = v_isSharedCheck_1697_;
goto v_resetjp_1690_;
}
v_resetjp_1690_:
{
lean_object* v___x_1693_; lean_object* v___x_1695_; 
v___x_1693_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1693_, 0, v_a_1689_);
if (v_isShared_1692_ == 0)
{
lean_ctor_set(v___x_1691_, 0, v___x_1693_);
v___x_1695_ = v___x_1691_;
goto v_reusejp_1694_;
}
else
{
lean_object* v_reuseFailAlloc_1696_; 
v_reuseFailAlloc_1696_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1696_, 0, v___x_1693_);
v___x_1695_ = v_reuseFailAlloc_1696_;
goto v_reusejp_1694_;
}
v_reusejp_1694_:
{
return v___x_1695_;
}
}
}
else
{
lean_object* v_a_1698_; lean_object* v___x_1700_; uint8_t v_isShared_1701_; uint8_t v_isSharedCheck_1705_; 
v_a_1698_ = lean_ctor_get(v___x_1688_, 0);
v_isSharedCheck_1705_ = !lean_is_exclusive(v___x_1688_);
if (v_isSharedCheck_1705_ == 0)
{
v___x_1700_ = v___x_1688_;
v_isShared_1701_ = v_isSharedCheck_1705_;
goto v_resetjp_1699_;
}
else
{
lean_inc(v_a_1698_);
lean_dec(v___x_1688_);
v___x_1700_ = lean_box(0);
v_isShared_1701_ = v_isSharedCheck_1705_;
goto v_resetjp_1699_;
}
v_resetjp_1699_:
{
lean_object* v___x_1703_; 
if (v_isShared_1701_ == 0)
{
v___x_1703_ = v___x_1700_;
goto v_reusejp_1702_;
}
else
{
lean_object* v_reuseFailAlloc_1704_; 
v_reuseFailAlloc_1704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1704_, 0, v_a_1698_);
v___x_1703_ = v_reuseFailAlloc_1704_;
goto v_reusejp_1702_;
}
v_reusejp_1702_:
{
return v___x_1703_;
}
}
}
}
}
else
{
lean_object* v_a_1706_; lean_object* v___x_1708_; uint8_t v_isShared_1709_; uint8_t v_isSharedCheck_1713_; 
lean_dec_ref(v_origExpr_1508_);
v_a_1706_ = lean_ctor_get(v___x_1519_, 0);
v_isSharedCheck_1713_ = !lean_is_exclusive(v___x_1519_);
if (v_isSharedCheck_1713_ == 0)
{
v___x_1708_ = v___x_1519_;
v_isShared_1709_ = v_isSharedCheck_1713_;
goto v_resetjp_1707_;
}
else
{
lean_inc(v_a_1706_);
lean_dec(v___x_1519_);
v___x_1708_ = lean_box(0);
v_isShared_1709_ = v_isSharedCheck_1713_;
goto v_resetjp_1707_;
}
v_resetjp_1707_:
{
lean_object* v___x_1711_; 
if (v_isShared_1709_ == 0)
{
v___x_1711_ = v___x_1708_;
goto v_reusejp_1710_;
}
else
{
lean_object* v_reuseFailAlloc_1712_; 
v_reuseFailAlloc_1712_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1712_, 0, v_a_1706_);
v___x_1711_ = v_reuseFailAlloc_1712_;
goto v_reusejp_1710_;
}
v_reusejp_1710_:
{
return v___x_1711_;
}
}
}
v___jp_1516_:
{
lean_object* v___x_1517_; lean_object* v___x_1518_; 
v___x_1517_ = lean_box(0);
v___x_1518_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1518_, 0, v___x_1517_);
return v___x_1518_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom_spec__2(lean_object* v_e_1714_, lean_object* v_a_1715_, lean_object* v_a_1716_, lean_object* v_a_1717_, lean_object* v_a_1718_, lean_object* v_a_1719_, lean_object* v_a_1720_){
_start:
{
lean_object* v___y_1723_; lean_object* v___x_1746_; lean_object* v_bvLogicalCache_1747_; lean_object* v___x_1748_; 
v___x_1746_ = lean_st_ref_get(v_a_1715_);
v_bvLogicalCache_1747_ = lean_ctor_get(v___x_1746_, 3);
lean_inc_ref(v_bvLogicalCache_1747_);
lean_dec(v___x_1746_);
v___x_1748_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom_spec__2_spec__12___redArg(v_bvLogicalCache_1747_, v_e_1714_);
lean_dec_ref(v_bvLogicalCache_1747_);
if (lean_obj_tag(v___x_1748_) == 0)
{
lean_object* v___x_1749_; 
lean_inc_ref(v_e_1714_);
v___x_1749_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_go(v_e_1714_, v_a_1715_, v_a_1716_, v_a_1717_, v_a_1718_, v_a_1719_, v_a_1720_);
if (lean_obj_tag(v___x_1749_) == 0)
{
lean_object* v_a_1750_; 
v_a_1750_ = lean_ctor_get(v___x_1749_, 0);
lean_inc(v_a_1750_);
if (lean_obj_tag(v_a_1750_) == 0)
{
lean_object* v___x_1751_; 
lean_dec_ref(v___x_1749_);
lean_inc_ref(v_e_1714_);
v___x_1751_ = l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_boolAtom(v_e_1714_, v_a_1716_, v_a_1717_, v_a_1718_, v_a_1719_, v_a_1720_);
v___y_1723_ = v___x_1751_;
goto v___jp_1722_;
}
else
{
lean_dec_ref(v_a_1750_);
v___y_1723_ = v___x_1749_;
goto v___jp_1722_;
}
}
else
{
v___y_1723_ = v___x_1749_;
goto v___jp_1722_;
}
}
else
{
lean_object* v_val_1752_; lean_object* v___x_1754_; uint8_t v_isShared_1755_; uint8_t v_isSharedCheck_1759_; 
lean_dec_ref(v_e_1714_);
v_val_1752_ = lean_ctor_get(v___x_1748_, 0);
v_isSharedCheck_1759_ = !lean_is_exclusive(v___x_1748_);
if (v_isSharedCheck_1759_ == 0)
{
v___x_1754_ = v___x_1748_;
v_isShared_1755_ = v_isSharedCheck_1759_;
goto v_resetjp_1753_;
}
else
{
lean_inc(v_val_1752_);
lean_dec(v___x_1748_);
v___x_1754_ = lean_box(0);
v_isShared_1755_ = v_isSharedCheck_1759_;
goto v_resetjp_1753_;
}
v_resetjp_1753_:
{
lean_object* v___x_1757_; 
if (v_isShared_1755_ == 0)
{
lean_ctor_set_tag(v___x_1754_, 0);
v___x_1757_ = v___x_1754_;
goto v_reusejp_1756_;
}
else
{
lean_object* v_reuseFailAlloc_1758_; 
v_reuseFailAlloc_1758_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1758_, 0, v_val_1752_);
v___x_1757_ = v_reuseFailAlloc_1758_;
goto v_reusejp_1756_;
}
v_reusejp_1756_:
{
return v___x_1757_;
}
}
}
v___jp_1722_:
{
if (lean_obj_tag(v___y_1723_) == 0)
{
lean_object* v_a_1724_; lean_object* v___x_1726_; uint8_t v_isShared_1727_; uint8_t v_isSharedCheck_1745_; 
v_a_1724_ = lean_ctor_get(v___y_1723_, 0);
v_isSharedCheck_1745_ = !lean_is_exclusive(v___y_1723_);
if (v_isSharedCheck_1745_ == 0)
{
v___x_1726_ = v___y_1723_;
v_isShared_1727_ = v_isSharedCheck_1745_;
goto v_resetjp_1725_;
}
else
{
lean_inc(v_a_1724_);
lean_dec(v___y_1723_);
v___x_1726_ = lean_box(0);
v_isShared_1727_ = v_isSharedCheck_1745_;
goto v_resetjp_1725_;
}
v_resetjp_1725_:
{
lean_object* v___x_1728_; lean_object* v_lemmas_1729_; lean_object* v_bvExprCache_1730_; lean_object* v_bvPredCache_1731_; lean_object* v_bvLogicalCache_1732_; lean_object* v___x_1734_; uint8_t v_isShared_1735_; uint8_t v_isSharedCheck_1744_; 
v___x_1728_ = lean_st_ref_take(v_a_1715_);
v_lemmas_1729_ = lean_ctor_get(v___x_1728_, 0);
v_bvExprCache_1730_ = lean_ctor_get(v___x_1728_, 1);
v_bvPredCache_1731_ = lean_ctor_get(v___x_1728_, 2);
v_bvLogicalCache_1732_ = lean_ctor_get(v___x_1728_, 3);
v_isSharedCheck_1744_ = !lean_is_exclusive(v___x_1728_);
if (v_isSharedCheck_1744_ == 0)
{
v___x_1734_ = v___x_1728_;
v_isShared_1735_ = v_isSharedCheck_1744_;
goto v_resetjp_1733_;
}
else
{
lean_inc(v_bvLogicalCache_1732_);
lean_inc(v_bvPredCache_1731_);
lean_inc(v_bvExprCache_1730_);
lean_inc(v_lemmas_1729_);
lean_dec(v___x_1728_);
v___x_1734_ = lean_box(0);
v_isShared_1735_ = v_isSharedCheck_1744_;
goto v_resetjp_1733_;
}
v_resetjp_1733_:
{
lean_object* v___x_1736_; lean_object* v___x_1738_; 
lean_inc(v_a_1724_);
v___x_1736_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13___redArg(v_bvLogicalCache_1732_, v_e_1714_, v_a_1724_);
if (v_isShared_1735_ == 0)
{
lean_ctor_set(v___x_1734_, 3, v___x_1736_);
v___x_1738_ = v___x_1734_;
goto v_reusejp_1737_;
}
else
{
lean_object* v_reuseFailAlloc_1743_; 
v_reuseFailAlloc_1743_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1743_, 0, v_lemmas_1729_);
lean_ctor_set(v_reuseFailAlloc_1743_, 1, v_bvExprCache_1730_);
lean_ctor_set(v_reuseFailAlloc_1743_, 2, v_bvPredCache_1731_);
lean_ctor_set(v_reuseFailAlloc_1743_, 3, v___x_1736_);
v___x_1738_ = v_reuseFailAlloc_1743_;
goto v_reusejp_1737_;
}
v_reusejp_1737_:
{
lean_object* v___x_1739_; lean_object* v___x_1741_; 
v___x_1739_ = lean_st_ref_set(v_a_1715_, v___x_1738_);
if (v_isShared_1727_ == 0)
{
v___x_1741_ = v___x_1726_;
goto v_reusejp_1740_;
}
else
{
lean_object* v_reuseFailAlloc_1742_; 
v_reuseFailAlloc_1742_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1742_, 0, v_a_1724_);
v___x_1741_ = v_reuseFailAlloc_1742_;
goto v_reusejp_1740_;
}
v_reusejp_1740_:
{
return v___x_1741_;
}
}
}
}
}
else
{
lean_dec_ref(v_e_1714_);
return v___y_1723_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom(lean_object* v_origExpr_1760_, lean_object* v_a_1761_, lean_object* v_a_1762_, lean_object* v_a_1763_, lean_object* v_a_1764_, lean_object* v_a_1765_, lean_object* v_a_1766_){
_start:
{
lean_object* v___x_1768_; 
v___x_1768_ = l_Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom_spec__2(v_origExpr_1760_, v_a_1761_, v_a_1762_, v_a_1763_, v_a_1764_, v_a_1765_, v_a_1766_);
return v___x_1768_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of(lean_object* v_origExpr_1769_, lean_object* v_a_1770_, lean_object* v_a_1771_, lean_object* v_a_1772_, lean_object* v_a_1773_, lean_object* v_a_1774_, lean_object* v_a_1775_){
_start:
{
lean_object* v___x_1777_; 
v___x_1777_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom(v_origExpr_1769_, v_a_1770_, v_a_1771_, v_a_1772_, v_a_1773_, v_a_1774_, v_a_1775_);
return v___x_1777_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__6(void){
_start:
{
lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; 
v___x_1793_ = lean_box(0);
v___x_1794_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__5));
v___x_1795_ = l_Lean_mkConst(v___x_1794_, v___x_1793_);
return v___x_1795_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__3(void){
_start:
{
lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; 
v___x_1803_ = lean_box(0);
v___x_1804_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__2));
v___x_1805_ = l_Lean_mkConst(v___x_1804_, v___x_1803_);
return v___x_1805_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__6(void){
_start:
{
lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; 
v___x_1812_ = lean_box(0);
v___x_1813_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__5));
v___x_1814_ = l_Lean_mkConst(v___x_1813_, v___x_1812_);
return v___x_1814_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__9(void){
_start:
{
lean_object* v___x_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; 
v___x_1821_ = lean_box(0);
v___x_1822_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__8));
v___x_1823_ = l_Lean_mkConst(v___x_1822_, v___x_1821_);
return v___x_1823_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__12(void){
_start:
{
lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; 
v___x_1831_ = lean_box(0);
v___x_1832_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__11));
v___x_1833_ = l_Lean_mkConst(v___x_1832_, v___x_1831_);
return v___x_1833_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__15(void){
_start:
{
lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; 
v___x_1840_ = lean_box(0);
v___x_1841_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__14));
v___x_1842_ = l_Lean_mkConst(v___x_1841_, v___x_1840_);
return v___x_1842_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__18(void){
_start:
{
lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; 
v___x_1849_ = lean_box(0);
v___x_1850_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__17));
v___x_1851_ = l_Lean_mkConst(v___x_1850_, v___x_1849_);
return v___x_1851_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__21(void){
_start:
{
lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; 
v___x_1858_ = lean_box(0);
v___x_1859_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__20));
v___x_1860_ = l_Lean_mkConst(v___x_1859_, v___x_1858_);
return v___x_1860_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection(lean_object* v_innerExpr_1861_, lean_object* v_op_1862_, lean_object* v_congrThm_1863_, lean_object* v_origExpr_1864_, lean_object* v_a_1865_, lean_object* v_a_1866_, lean_object* v_a_1867_, lean_object* v_a_1868_, lean_object* v_a_1869_, lean_object* v_a_1870_){
_start:
{
lean_object* v___x_1872_; 
lean_inc_ref(v_innerExpr_1861_);
v___x_1872_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_goOrAtom(v_innerExpr_1861_, v_a_1865_, v_a_1866_, v_a_1867_, v_a_1868_, v_a_1869_, v_a_1870_);
if (lean_obj_tag(v___x_1872_) == 0)
{
lean_object* v_a_1873_; lean_object* v___x_1875_; uint8_t v_isShared_1876_; uint8_t v_isSharedCheck_1921_; 
v_a_1873_ = lean_ctor_get(v___x_1872_, 0);
v_isSharedCheck_1921_ = !lean_is_exclusive(v___x_1872_);
if (v_isSharedCheck_1921_ == 0)
{
v___x_1875_ = v___x_1872_;
v_isShared_1876_ = v_isSharedCheck_1921_;
goto v_resetjp_1874_;
}
else
{
lean_inc(v_a_1873_);
lean_dec(v___x_1872_);
v___x_1875_ = lean_box(0);
v_isShared_1876_ = v_isSharedCheck_1921_;
goto v_resetjp_1874_;
}
v_resetjp_1874_:
{
if (lean_obj_tag(v_a_1873_) == 1)
{
lean_object* v_val_1877_; lean_object* v___x_1879_; uint8_t v_isShared_1880_; uint8_t v_isSharedCheck_1916_; 
v_val_1877_ = lean_ctor_get(v_a_1873_, 0);
v_isSharedCheck_1916_ = !lean_is_exclusive(v_a_1873_);
if (v_isSharedCheck_1916_ == 0)
{
v___x_1879_ = v_a_1873_;
v_isShared_1880_ = v_isSharedCheck_1916_;
goto v_resetjp_1878_;
}
else
{
lean_inc(v_val_1877_);
lean_dec(v_a_1873_);
v___x_1879_ = lean_box(0);
v_isShared_1880_ = v_isSharedCheck_1916_;
goto v_resetjp_1878_;
}
v_resetjp_1878_:
{
lean_object* v_width_1881_; lean_object* v_bvExpr_1882_; lean_object* v_expr_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; lean_object* v___y_1889_; 
v_width_1881_ = lean_ctor_get(v_val_1877_, 0);
lean_inc(v_width_1881_);
v_bvExpr_1882_ = lean_ctor_get(v_val_1877_, 1);
v_expr_1883_ = lean_ctor_get(v_val_1877_, 4);
lean_inc_ref(v_bvExpr_1882_);
lean_inc(v_op_1862_);
lean_inc(v_width_1881_);
v___x_1884_ = l_Std_Tactic_BVDecide_BVExpr_un___override(v_width_1881_, v_op_1862_, v_bvExpr_1882_);
v___x_1885_ = lean_box(0);
v___x_1886_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__6, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__6_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__6);
lean_inc(v_width_1881_);
v___x_1887_ = l_Lean_mkNatLit(v_width_1881_);
switch(lean_obj_tag(v_op_1862_))
{
case 0:
{
lean_object* v___x_1900_; 
v___x_1900_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__3, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__3_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__3);
v___y_1889_ = v___x_1900_;
goto v___jp_1888_;
}
case 1:
{
lean_object* v_n_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; 
v_n_1901_ = lean_ctor_get(v_op_1862_, 0);
lean_inc(v_n_1901_);
lean_dec_ref(v_op_1862_);
v___x_1902_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__6, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__6_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__6);
v___x_1903_ = l_Lean_mkNatLit(v_n_1901_);
v___x_1904_ = l_Lean_Expr_app___override(v___x_1902_, v___x_1903_);
v___y_1889_ = v___x_1904_;
goto v___jp_1888_;
}
case 2:
{
lean_object* v_n_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; 
v_n_1905_ = lean_ctor_get(v_op_1862_, 0);
lean_inc(v_n_1905_);
lean_dec_ref(v_op_1862_);
v___x_1906_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__9, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__9_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__9);
v___x_1907_ = l_Lean_mkNatLit(v_n_1905_);
v___x_1908_ = l_Lean_Expr_app___override(v___x_1906_, v___x_1907_);
v___y_1889_ = v___x_1908_;
goto v___jp_1888_;
}
case 3:
{
lean_object* v_n_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; 
v_n_1909_ = lean_ctor_get(v_op_1862_, 0);
lean_inc(v_n_1909_);
lean_dec_ref(v_op_1862_);
v___x_1910_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__12, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__12_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__12);
v___x_1911_ = l_Lean_mkNatLit(v_n_1909_);
v___x_1912_ = l_Lean_Expr_app___override(v___x_1910_, v___x_1911_);
v___y_1889_ = v___x_1912_;
goto v___jp_1888_;
}
case 4:
{
lean_object* v___x_1913_; 
v___x_1913_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__15, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__15_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__15);
v___y_1889_ = v___x_1913_;
goto v___jp_1888_;
}
case 5:
{
lean_object* v___x_1914_; 
v___x_1914_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__18, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__18_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__18);
v___y_1889_ = v___x_1914_;
goto v___jp_1888_;
}
default: 
{
lean_object* v___x_1915_; 
v___x_1915_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__21, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__21_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__21);
v___y_1889_ = v___x_1915_;
goto v___jp_1888_;
}
}
v___jp_1888_:
{
lean_object* v___x_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; lean_object* v___x_1895_; 
lean_inc_ref(v_expr_1883_);
v___x_1890_ = l_Lean_mkApp3(v___x_1886_, v___x_1887_, v___y_1889_, v_expr_1883_);
v___x_1891_ = l_Lean_mkConst(v_congrThm_1863_, v___x_1885_);
v___x_1892_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryCongrProof___boxed), 9, 3);
lean_closure_set(v___x_1892_, 0, v_val_1877_);
lean_closure_set(v___x_1892_, 1, v_innerExpr_1861_);
lean_closure_set(v___x_1892_, 2, v___x_1891_);
v___x_1893_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1893_, 0, v_width_1881_);
lean_ctor_set(v___x_1893_, 1, v___x_1884_);
lean_ctor_set(v___x_1893_, 2, v_origExpr_1864_);
lean_ctor_set(v___x_1893_, 3, v___x_1892_);
lean_ctor_set(v___x_1893_, 4, v___x_1890_);
if (v_isShared_1880_ == 0)
{
lean_ctor_set(v___x_1879_, 0, v___x_1893_);
v___x_1895_ = v___x_1879_;
goto v_reusejp_1894_;
}
else
{
lean_object* v_reuseFailAlloc_1899_; 
v_reuseFailAlloc_1899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1899_, 0, v___x_1893_);
v___x_1895_ = v_reuseFailAlloc_1899_;
goto v_reusejp_1894_;
}
v_reusejp_1894_:
{
lean_object* v___x_1897_; 
if (v_isShared_1876_ == 0)
{
lean_ctor_set(v___x_1875_, 0, v___x_1895_);
v___x_1897_ = v___x_1875_;
goto v_reusejp_1896_;
}
else
{
lean_object* v_reuseFailAlloc_1898_; 
v_reuseFailAlloc_1898_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1898_, 0, v___x_1895_);
v___x_1897_ = v_reuseFailAlloc_1898_;
goto v_reusejp_1896_;
}
v_reusejp_1896_:
{
return v___x_1897_;
}
}
}
}
}
else
{
lean_object* v___x_1917_; lean_object* v___x_1919_; 
lean_dec(v_a_1873_);
lean_dec_ref(v_origExpr_1864_);
lean_dec(v_congrThm_1863_);
lean_dec(v_op_1862_);
lean_dec_ref(v_innerExpr_1861_);
v___x_1917_ = lean_box(0);
if (v_isShared_1876_ == 0)
{
lean_ctor_set(v___x_1875_, 0, v___x_1917_);
v___x_1919_ = v___x_1875_;
goto v_reusejp_1918_;
}
else
{
lean_object* v_reuseFailAlloc_1920_; 
v_reuseFailAlloc_1920_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1920_, 0, v___x_1917_);
v___x_1919_ = v_reuseFailAlloc_1920_;
goto v_reusejp_1918_;
}
v_reusejp_1918_:
{
return v___x_1919_;
}
}
}
}
else
{
lean_dec_ref(v_origExpr_1864_);
lean_dec(v_congrThm_1863_);
lean_dec(v_op_1862_);
lean_dec_ref(v_innerExpr_1861_);
return v___x_1872_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection(lean_object* v_distance_1931_, lean_object* v_innerExpr_1932_, lean_object* v_shiftOp_1933_, lean_object* v_shiftOpName_1934_, lean_object* v_congrThm_1935_, lean_object* v_origExpr_1936_, lean_object* v_a_1937_, lean_object* v_a_1938_, lean_object* v_a_1939_, lean_object* v_a_1940_, lean_object* v_a_1941_, lean_object* v_a_1942_){
_start:
{
lean_object* v___x_1944_; 
lean_inc_ref(v_innerExpr_1932_);
v___x_1944_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_goOrAtom(v_innerExpr_1932_, v_a_1937_, v_a_1938_, v_a_1939_, v_a_1940_, v_a_1941_, v_a_1942_);
if (lean_obj_tag(v___x_1944_) == 0)
{
lean_object* v_a_1945_; lean_object* v___x_1947_; uint8_t v_isShared_1948_; uint8_t v_isSharedCheck_1980_; 
v_a_1945_ = lean_ctor_get(v___x_1944_, 0);
v_isSharedCheck_1980_ = !lean_is_exclusive(v___x_1944_);
if (v_isSharedCheck_1980_ == 0)
{
v___x_1947_ = v___x_1944_;
v_isShared_1948_ = v_isSharedCheck_1980_;
goto v_resetjp_1946_;
}
else
{
lean_inc(v_a_1945_);
lean_dec(v___x_1944_);
v___x_1947_ = lean_box(0);
v_isShared_1948_ = v_isSharedCheck_1980_;
goto v_resetjp_1946_;
}
v_resetjp_1946_:
{
if (lean_obj_tag(v_a_1945_) == 1)
{
lean_object* v_val_1949_; lean_object* v___x_1951_; uint8_t v_isShared_1952_; uint8_t v_isSharedCheck_1975_; 
v_val_1949_ = lean_ctor_get(v_a_1945_, 0);
v_isSharedCheck_1975_ = !lean_is_exclusive(v_a_1945_);
if (v_isSharedCheck_1975_ == 0)
{
v___x_1951_ = v_a_1945_;
v_isShared_1952_ = v_isSharedCheck_1975_;
goto v_resetjp_1950_;
}
else
{
lean_inc(v_val_1949_);
lean_dec(v_a_1945_);
v___x_1951_ = lean_box(0);
v_isShared_1952_ = v_isSharedCheck_1975_;
goto v_resetjp_1950_;
}
v_resetjp_1950_:
{
lean_object* v_width_1953_; lean_object* v_bvExpr_1954_; lean_object* v_expr_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; lean_object* v___x_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1970_; 
v_width_1953_ = lean_ctor_get(v_val_1949_, 0);
lean_inc(v_width_1953_);
v_bvExpr_1954_ = lean_ctor_get(v_val_1949_, 1);
v_expr_1955_ = lean_ctor_get(v_val_1949_, 4);
lean_inc(v_distance_1931_);
v___x_1956_ = lean_apply_1(v_shiftOp_1933_, v_distance_1931_);
lean_inc_ref(v_bvExpr_1954_);
lean_inc(v_width_1953_);
v___x_1957_ = l_Std_Tactic_BVDecide_BVExpr_un___override(v_width_1953_, v___x_1956_, v_bvExpr_1954_);
v___x_1958_ = lean_box(0);
v___x_1959_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__6, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__6_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__6);
lean_inc(v_width_1953_);
v___x_1960_ = l_Lean_mkNatLit(v_width_1953_);
v___x_1961_ = l_Lean_mkConst(v_shiftOpName_1934_, v___x_1958_);
v___x_1962_ = l_Lean_mkNatLit(v_distance_1931_);
lean_inc_ref(v___x_1962_);
v___x_1963_ = l_Lean_Expr_app___override(v___x_1961_, v___x_1962_);
lean_inc_ref(v_expr_1955_);
v___x_1964_ = l_Lean_mkApp3(v___x_1959_, v___x_1960_, v___x_1963_, v_expr_1955_);
v___x_1965_ = l_Lean_mkConst(v_congrThm_1935_, v___x_1958_);
v___x_1966_ = l_Lean_Expr_app___override(v___x_1965_, v___x_1962_);
v___x_1967_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryCongrProof___boxed), 9, 3);
lean_closure_set(v___x_1967_, 0, v_val_1949_);
lean_closure_set(v___x_1967_, 1, v_innerExpr_1932_);
lean_closure_set(v___x_1967_, 2, v___x_1966_);
v___x_1968_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1968_, 0, v_width_1953_);
lean_ctor_set(v___x_1968_, 1, v___x_1957_);
lean_ctor_set(v___x_1968_, 2, v_origExpr_1936_);
lean_ctor_set(v___x_1968_, 3, v___x_1967_);
lean_ctor_set(v___x_1968_, 4, v___x_1964_);
if (v_isShared_1952_ == 0)
{
lean_ctor_set(v___x_1951_, 0, v___x_1968_);
v___x_1970_ = v___x_1951_;
goto v_reusejp_1969_;
}
else
{
lean_object* v_reuseFailAlloc_1974_; 
v_reuseFailAlloc_1974_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1974_, 0, v___x_1968_);
v___x_1970_ = v_reuseFailAlloc_1974_;
goto v_reusejp_1969_;
}
v_reusejp_1969_:
{
lean_object* v___x_1972_; 
if (v_isShared_1948_ == 0)
{
lean_ctor_set(v___x_1947_, 0, v___x_1970_);
v___x_1972_ = v___x_1947_;
goto v_reusejp_1971_;
}
else
{
lean_object* v_reuseFailAlloc_1973_; 
v_reuseFailAlloc_1973_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1973_, 0, v___x_1970_);
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
else
{
lean_object* v___x_1976_; lean_object* v___x_1978_; 
lean_dec(v_a_1945_);
lean_dec_ref(v_origExpr_1936_);
lean_dec(v_congrThm_1935_);
lean_dec(v_shiftOpName_1934_);
lean_dec_ref(v_shiftOp_1933_);
lean_dec_ref(v_innerExpr_1932_);
lean_dec(v_distance_1931_);
v___x_1976_ = lean_box(0);
if (v_isShared_1948_ == 0)
{
lean_ctor_set(v___x_1947_, 0, v___x_1976_);
v___x_1978_ = v___x_1947_;
goto v_reusejp_1977_;
}
else
{
lean_object* v_reuseFailAlloc_1979_; 
v_reuseFailAlloc_1979_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1979_, 0, v___x_1976_);
v___x_1978_ = v_reuseFailAlloc_1979_;
goto v_reusejp_1977_;
}
v_reusejp_1977_:
{
return v___x_1978_;
}
}
}
}
else
{
lean_dec_ref(v_origExpr_1936_);
lean_dec(v_congrThm_1935_);
lean_dec(v_shiftOpName_1934_);
lean_dec_ref(v_shiftOp_1933_);
lean_dec_ref(v_innerExpr_1932_);
lean_dec(v_distance_1931_);
return v___x_1944_;
}
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__86(void){
_start:
{
lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; 
v___x_1987_ = lean_box(0);
v___x_1988_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__85));
v___x_1989_ = l_Lean_mkConst(v___x_1988_, v___x_1987_);
return v___x_1989_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_rotateReflection(lean_object* v_distanceExpr_1999_, lean_object* v_innerExpr_2000_, lean_object* v_rotateOp_2001_, lean_object* v_rotateOpName_2002_, lean_object* v_congrThm_2003_, lean_object* v_origExpr_2004_, lean_object* v_a_2005_, lean_object* v_a_2006_, lean_object* v_a_2007_, lean_object* v_a_2008_, lean_object* v_a_2009_, lean_object* v_a_2010_){
_start:
{
lean_object* v___x_2012_; 
v___x_2012_ = l_Lean_Meta_getNatValue_x3f(v_distanceExpr_1999_, v_a_2007_, v_a_2008_, v_a_2009_, v_a_2010_);
if (lean_obj_tag(v___x_2012_) == 0)
{
lean_object* v_a_2013_; lean_object* v___x_2015_; uint8_t v_isShared_2016_; uint8_t v_isSharedCheck_2023_; 
v_a_2013_ = lean_ctor_get(v___x_2012_, 0);
v_isSharedCheck_2023_ = !lean_is_exclusive(v___x_2012_);
if (v_isSharedCheck_2023_ == 0)
{
v___x_2015_ = v___x_2012_;
v_isShared_2016_ = v_isSharedCheck_2023_;
goto v_resetjp_2014_;
}
else
{
lean_inc(v_a_2013_);
lean_dec(v___x_2012_);
v___x_2015_ = lean_box(0);
v_isShared_2016_ = v_isSharedCheck_2023_;
goto v_resetjp_2014_;
}
v_resetjp_2014_:
{
if (lean_obj_tag(v_a_2013_) == 1)
{
lean_object* v_val_2017_; lean_object* v___x_2018_; 
lean_del_object(v___x_2015_);
v_val_2017_ = lean_ctor_get(v_a_2013_, 0);
lean_inc(v_val_2017_);
lean_dec_ref(v_a_2013_);
v___x_2018_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection(v_val_2017_, v_innerExpr_2000_, v_rotateOp_2001_, v_rotateOpName_2002_, v_congrThm_2003_, v_origExpr_2004_, v_a_2005_, v_a_2006_, v_a_2007_, v_a_2008_, v_a_2009_, v_a_2010_);
return v___x_2018_;
}
else
{
lean_object* v___x_2019_; lean_object* v___x_2021_; 
lean_dec(v_a_2013_);
lean_dec_ref(v_origExpr_2004_);
lean_dec(v_congrThm_2003_);
lean_dec(v_rotateOpName_2002_);
lean_dec_ref(v_rotateOp_2001_);
lean_dec_ref(v_innerExpr_2000_);
v___x_2019_ = lean_box(0);
if (v_isShared_2016_ == 0)
{
lean_ctor_set(v___x_2015_, 0, v___x_2019_);
v___x_2021_ = v___x_2015_;
goto v_reusejp_2020_;
}
else
{
lean_object* v_reuseFailAlloc_2022_; 
v_reuseFailAlloc_2022_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2022_, 0, v___x_2019_);
v___x_2021_ = v_reuseFailAlloc_2022_;
goto v_reusejp_2020_;
}
v_reusejp_2020_:
{
return v___x_2021_;
}
}
}
}
else
{
lean_object* v_a_2024_; lean_object* v___x_2026_; uint8_t v_isShared_2027_; uint8_t v_isSharedCheck_2031_; 
lean_dec_ref(v_origExpr_2004_);
lean_dec(v_congrThm_2003_);
lean_dec(v_rotateOpName_2002_);
lean_dec_ref(v_rotateOp_2001_);
lean_dec_ref(v_innerExpr_2000_);
v_a_2024_ = lean_ctor_get(v___x_2012_, 0);
v_isSharedCheck_2031_ = !lean_is_exclusive(v___x_2012_);
if (v_isSharedCheck_2031_ == 0)
{
v___x_2026_ = v___x_2012_;
v_isShared_2027_ = v_isSharedCheck_2031_;
goto v_resetjp_2025_;
}
else
{
lean_inc(v_a_2024_);
lean_dec(v___x_2012_);
v___x_2026_ = lean_box(0);
v_isShared_2027_ = v_isSharedCheck_2031_;
goto v_resetjp_2025_;
}
v_resetjp_2025_:
{
lean_object* v___x_2029_; 
if (v_isShared_2027_ == 0)
{
v___x_2029_ = v___x_2026_;
goto v_reusejp_2028_;
}
else
{
lean_object* v_reuseFailAlloc_2030_; 
v_reuseFailAlloc_2030_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2030_, 0, v_a_2024_);
v___x_2029_ = v_reuseFailAlloc_2030_;
goto v_reusejp_2028_;
}
v_reusejp_2028_:
{
return v___x_2029_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go(lean_object* v_origExpr_2065_, lean_object* v_a_2066_, lean_object* v_a_2067_, lean_object* v_a_2068_, lean_object* v_a_2069_, lean_object* v_a_2070_, lean_object* v_a_2071_){
_start:
{
lean_object* v___x_2079_; 
lean_inc_ref(v_origExpr_2065_);
v___x_2079_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_origExpr_2065_, v_a_2069_);
if (lean_obj_tag(v___x_2079_) == 0)
{
lean_object* v_a_2080_; lean_object* v___x_2082_; uint8_t v_isShared_2083_; uint8_t v_isSharedCheck_2618_; 
v_a_2080_ = lean_ctor_get(v___x_2079_, 0);
v_isSharedCheck_2618_ = !lean_is_exclusive(v___x_2079_);
if (v_isSharedCheck_2618_ == 0)
{
v___x_2082_ = v___x_2079_;
v_isShared_2083_ = v_isSharedCheck_2618_;
goto v_resetjp_2081_;
}
else
{
lean_inc(v_a_2080_);
lean_dec(v___x_2079_);
v___x_2082_ = lean_box(0);
v_isShared_2083_ = v_isSharedCheck_2618_;
goto v_resetjp_2081_;
}
v_resetjp_2081_:
{
lean_object* v___x_2089_; uint8_t v___x_2090_; 
v___x_2089_ = l_Lean_Expr_cleanupAnnotations(v_a_2080_);
v___x_2090_ = l_Lean_Expr_isApp(v___x_2089_);
if (v___x_2090_ == 0)
{
lean_dec_ref(v___x_2089_);
lean_dec_ref(v_origExpr_2065_);
goto v___jp_2084_;
}
else
{
lean_object* v_arg_2091_; lean_object* v___x_2092_; uint8_t v___x_2093_; 
v_arg_2091_ = lean_ctor_get(v___x_2089_, 1);
lean_inc_ref(v_arg_2091_);
v___x_2092_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2089_);
v___x_2093_ = l_Lean_Expr_isApp(v___x_2092_);
if (v___x_2093_ == 0)
{
lean_dec_ref(v___x_2092_);
lean_dec_ref(v_arg_2091_);
lean_dec_ref(v_origExpr_2065_);
goto v___jp_2084_;
}
else
{
lean_object* v_arg_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; uint8_t v___x_2098_; 
v_arg_2094_ = lean_ctor_get(v___x_2092_, 1);
lean_inc_ref(v_arg_2094_);
v___x_2095_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2092_);
v___x_2096_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_of_go___closed__0));
v___x_2097_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__0));
v___x_2098_ = l_Lean_Expr_isConstOf(v___x_2095_, v___x_2097_);
if (v___x_2098_ == 0)
{
lean_object* v___x_2099_; uint8_t v___x_2100_; 
v___x_2099_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__1));
v___x_2100_ = l_Lean_Expr_isConstOf(v___x_2095_, v___x_2099_);
if (v___x_2100_ == 0)
{
lean_object* v___x_2101_; uint8_t v___x_2102_; 
v___x_2101_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__2));
v___x_2102_ = l_Lean_Expr_isConstOf(v___x_2095_, v___x_2101_);
if (v___x_2102_ == 0)
{
lean_object* v___x_2103_; uint8_t v___x_2104_; 
v___x_2103_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__4));
v___x_2104_ = l_Lean_Expr_isConstOf(v___x_2095_, v___x_2103_);
if (v___x_2104_ == 0)
{
uint8_t v___x_2105_; 
v___x_2105_ = l_Lean_Expr_isApp(v___x_2095_);
if (v___x_2105_ == 0)
{
lean_dec_ref(v___x_2095_);
lean_dec_ref(v_arg_2094_);
lean_dec_ref(v_arg_2091_);
lean_dec_ref(v_origExpr_2065_);
goto v___jp_2084_;
}
else
{
lean_object* v_arg_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; uint8_t v___x_2109_; 
v_arg_2106_ = lean_ctor_get(v___x_2095_, 1);
lean_inc_ref(v_arg_2106_);
v___x_2107_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2095_);
v___x_2108_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__5));
v___x_2109_ = l_Lean_Expr_isConstOf(v___x_2107_, v___x_2108_);
if (v___x_2109_ == 0)
{
lean_object* v___x_2110_; uint8_t v___x_2111_; 
v___x_2110_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__6));
v___x_2111_ = l_Lean_Expr_isConstOf(v___x_2107_, v___x_2110_);
if (v___x_2111_ == 0)
{
lean_object* v___x_2112_; uint8_t v___x_2113_; 
v___x_2112_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__8));
v___x_2113_ = l_Lean_Expr_isConstOf(v___x_2107_, v___x_2112_);
if (v___x_2113_ == 0)
{
lean_object* v___x_2114_; uint8_t v___x_2115_; 
v___x_2114_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__10));
v___x_2115_ = l_Lean_Expr_isConstOf(v___x_2107_, v___x_2114_);
if (v___x_2115_ == 0)
{
lean_object* v___x_2116_; uint8_t v___x_2117_; 
v___x_2116_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__13));
v___x_2117_ = l_Lean_Expr_isConstOf(v___x_2107_, v___x_2116_);
if (v___x_2117_ == 0)
{
uint8_t v___x_2118_; 
v___x_2118_ = l_Lean_Expr_isApp(v___x_2107_);
if (v___x_2118_ == 0)
{
lean_dec_ref(v___x_2107_);
lean_dec_ref(v_arg_2106_);
lean_dec_ref(v_arg_2094_);
lean_dec_ref(v_arg_2091_);
lean_dec_ref(v_origExpr_2065_);
goto v___jp_2084_;
}
else
{
lean_object* v___x_2119_; lean_object* v___x_2120_; uint8_t v___x_2121_; 
v___x_2119_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2107_);
v___x_2120_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_go___closed__9));
v___x_2121_ = l_Lean_Expr_isConstOf(v___x_2119_, v___x_2120_);
if (v___x_2121_ == 0)
{
lean_object* v___x_2122_; uint8_t v___x_2123_; 
v___x_2122_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__15));
v___x_2123_ = l_Lean_Expr_isConstOf(v___x_2119_, v___x_2122_);
if (v___x_2123_ == 0)
{
lean_object* v___x_2124_; uint8_t v___x_2125_; 
lean_dec_ref(v_arg_2106_);
v___x_2124_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__17));
v___x_2125_ = l_Lean_Expr_isConstOf(v___x_2119_, v___x_2124_);
if (v___x_2125_ == 0)
{
uint8_t v___x_2126_; 
v___x_2126_ = l_Lean_Expr_isApp(v___x_2119_);
if (v___x_2126_ == 0)
{
lean_dec_ref(v___x_2119_);
lean_dec_ref(v_arg_2094_);
lean_dec_ref(v_arg_2091_);
lean_dec_ref(v_origExpr_2065_);
goto v___jp_2084_;
}
else
{
lean_object* v_arg_2127_; lean_object* v___x_2128_; uint8_t v___x_2129_; 
v_arg_2127_ = lean_ctor_get(v___x_2119_, 1);
lean_inc_ref(v_arg_2127_);
v___x_2128_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2119_);
v___x_2129_ = l_Lean_Expr_isApp(v___x_2128_);
if (v___x_2129_ == 0)
{
lean_dec_ref(v___x_2128_);
lean_dec_ref(v_arg_2127_);
lean_dec_ref(v_arg_2094_);
lean_dec_ref(v_arg_2091_);
lean_dec_ref(v_origExpr_2065_);
goto v___jp_2084_;
}
else
{
lean_object* v_arg_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; uint8_t v___x_2133_; 
v_arg_2130_ = lean_ctor_get(v___x_2128_, 1);
lean_inc_ref(v_arg_2130_);
v___x_2131_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2128_);
v___x_2132_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__20));
v___x_2133_ = l_Lean_Expr_isConstOf(v___x_2131_, v___x_2132_);
if (v___x_2133_ == 0)
{
lean_object* v___x_2134_; uint8_t v___x_2135_; 
v___x_2134_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__23));
v___x_2135_ = l_Lean_Expr_isConstOf(v___x_2131_, v___x_2134_);
if (v___x_2135_ == 0)
{
lean_object* v___x_2136_; uint8_t v___x_2137_; 
v___x_2136_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__26));
v___x_2137_ = l_Lean_Expr_isConstOf(v___x_2131_, v___x_2136_);
if (v___x_2137_ == 0)
{
lean_object* v___x_2138_; uint8_t v___x_2139_; 
lean_dec_ref(v_arg_2130_);
lean_dec_ref(v_arg_2127_);
v___x_2138_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__29));
v___x_2139_ = l_Lean_Expr_isConstOf(v___x_2131_, v___x_2138_);
if (v___x_2139_ == 0)
{
lean_object* v___x_2140_; uint8_t v___x_2141_; 
v___x_2140_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__32));
v___x_2141_ = l_Lean_Expr_isConstOf(v___x_2131_, v___x_2140_);
if (v___x_2141_ == 0)
{
lean_object* v___x_2142_; uint8_t v___x_2143_; 
v___x_2142_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__35));
v___x_2143_ = l_Lean_Expr_isConstOf(v___x_2131_, v___x_2142_);
if (v___x_2143_ == 0)
{
lean_object* v___x_2144_; uint8_t v___x_2145_; 
v___x_2144_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__38));
v___x_2145_ = l_Lean_Expr_isConstOf(v___x_2131_, v___x_2144_);
if (v___x_2145_ == 0)
{
lean_object* v___x_2146_; uint8_t v___x_2147_; 
v___x_2146_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__41));
v___x_2147_ = l_Lean_Expr_isConstOf(v___x_2131_, v___x_2146_);
if (v___x_2147_ == 0)
{
lean_object* v___x_2148_; uint8_t v___x_2149_; 
v___x_2148_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__44));
v___x_2149_ = l_Lean_Expr_isConstOf(v___x_2131_, v___x_2148_);
lean_dec_ref(v___x_2131_);
if (v___x_2149_ == 0)
{
lean_dec_ref(v_arg_2094_);
lean_dec_ref(v_arg_2091_);
lean_dec_ref(v_origExpr_2065_);
goto v___jp_2084_;
}
else
{
uint8_t v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; 
lean_del_object(v___x_2082_);
v___x_2150_ = 0;
v___x_2151_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__46));
v___x_2152_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection(v_arg_2094_, v_arg_2091_, v___x_2150_, v___x_2151_, v_origExpr_2065_, v_a_2066_, v_a_2067_, v_a_2068_, v_a_2069_, v_a_2070_, v_a_2071_);
return v___x_2152_;
}
}
else
{
uint8_t v___x_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; 
lean_dec_ref(v___x_2131_);
lean_del_object(v___x_2082_);
v___x_2153_ = 2;
v___x_2154_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__48));
v___x_2155_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection(v_arg_2094_, v_arg_2091_, v___x_2153_, v___x_2154_, v_origExpr_2065_, v_a_2066_, v_a_2067_, v_a_2068_, v_a_2069_, v_a_2070_, v_a_2071_);
return v___x_2155_;
}
}
else
{
uint8_t v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; 
lean_dec_ref(v___x_2131_);
lean_del_object(v___x_2082_);
v___x_2156_ = 3;
v___x_2157_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__50));
v___x_2158_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection(v_arg_2094_, v_arg_2091_, v___x_2156_, v___x_2157_, v_origExpr_2065_, v_a_2066_, v_a_2067_, v_a_2068_, v_a_2069_, v_a_2070_, v_a_2071_);
return v___x_2158_;
}
}
else
{
uint8_t v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; 
lean_dec_ref(v___x_2131_);
lean_del_object(v___x_2082_);
v___x_2159_ = 4;
v___x_2160_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__52));
v___x_2161_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection(v_arg_2094_, v_arg_2091_, v___x_2159_, v___x_2160_, v_origExpr_2065_, v_a_2066_, v_a_2067_, v_a_2068_, v_a_2069_, v_a_2070_, v_a_2071_);
return v___x_2161_;
}
}
else
{
uint8_t v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; 
lean_dec_ref(v___x_2131_);
lean_del_object(v___x_2082_);
v___x_2162_ = 5;
v___x_2163_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__54));
v___x_2164_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection(v_arg_2094_, v_arg_2091_, v___x_2162_, v___x_2163_, v_origExpr_2065_, v_a_2066_, v_a_2067_, v_a_2068_, v_a_2069_, v_a_2070_, v_a_2071_);
return v___x_2164_;
}
}
else
{
uint8_t v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; 
lean_dec_ref(v___x_2131_);
lean_del_object(v___x_2082_);
v___x_2165_ = 6;
v___x_2166_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__56));
v___x_2167_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection(v_arg_2094_, v_arg_2091_, v___x_2165_, v___x_2166_, v_origExpr_2065_, v_a_2066_, v_a_2067_, v_a_2068_, v_a_2069_, v_a_2070_, v_a_2071_);
return v___x_2167_;
}
}
else
{
lean_object* v___x_2168_; 
lean_dec_ref(v___x_2131_);
lean_del_object(v___x_2082_);
lean_inc_ref(v_arg_2091_);
lean_inc_ref(v_arg_2127_);
v___x_2168_ = l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_getNatOrBvValue_x3f___redArg(v_arg_2127_, v_arg_2091_, v_a_2068_, v_a_2069_, v_a_2070_, v_a_2071_);
if (lean_obj_tag(v___x_2168_) == 0)
{
lean_object* v_a_2169_; lean_object* v___x_2171_; uint8_t v_isShared_2172_; uint8_t v_isSharedCheck_2222_; 
v_a_2169_ = lean_ctor_get(v___x_2168_, 0);
v_isSharedCheck_2222_ = !lean_is_exclusive(v___x_2168_);
if (v_isSharedCheck_2222_ == 0)
{
v___x_2171_ = v___x_2168_;
v_isShared_2172_ = v_isSharedCheck_2222_;
goto v_resetjp_2170_;
}
else
{
lean_inc(v_a_2169_);
lean_dec(v___x_2168_);
v___x_2171_ = lean_box(0);
v_isShared_2172_ = v_isSharedCheck_2222_;
goto v_resetjp_2170_;
}
v_resetjp_2170_:
{
lean_object* v___x_2178_; uint8_t v___x_2179_; 
v___x_2178_ = l_Lean_Expr_cleanupAnnotations(v_arg_2130_);
v___x_2179_ = l_Lean_Expr_isApp(v___x_2178_);
if (v___x_2179_ == 0)
{
lean_dec_ref(v___x_2178_);
lean_dec(v_a_2169_);
lean_dec_ref(v_arg_2127_);
lean_dec_ref(v_arg_2094_);
lean_dec_ref(v_arg_2091_);
lean_dec_ref(v_origExpr_2065_);
goto v___jp_2173_;
}
else
{
lean_object* v_arg_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; uint8_t v___x_2183_; 
v_arg_2180_ = lean_ctor_get(v___x_2178_, 1);
lean_inc_ref(v_arg_2180_);
v___x_2181_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2178_);
v___x_2182_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_of_go___closed__8));
v___x_2183_ = l_Lean_Expr_isConstOf(v___x_2181_, v___x_2182_);
lean_dec_ref(v___x_2181_);
if (v___x_2183_ == 0)
{
lean_dec_ref(v_arg_2180_);
lean_dec(v_a_2169_);
lean_dec_ref(v_arg_2127_);
lean_dec_ref(v_arg_2094_);
lean_dec_ref(v_arg_2091_);
lean_dec_ref(v_origExpr_2065_);
goto v___jp_2173_;
}
else
{
lean_object* v___x_2184_; 
lean_del_object(v___x_2171_);
v___x_2184_ = l_Lean_Meta_getNatValue_x3f(v_arg_2180_, v_a_2068_, v_a_2069_, v_a_2070_, v_a_2071_);
lean_dec_ref(v_arg_2180_);
if (lean_obj_tag(v___x_2184_) == 0)
{
lean_object* v_a_2185_; lean_object* v___f_2186_; lean_object* v___y_2188_; lean_object* v___y_2189_; lean_object* v___y_2190_; lean_object* v___y_2191_; lean_object* v___y_2192_; lean_object* v___y_2193_; uint8_t v___y_2213_; 
v_a_2185_ = lean_ctor_get(v___x_2184_, 0);
lean_inc(v_a_2185_);
lean_dec_ref(v___x_2184_);
v___f_2186_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__57));
if (lean_obj_tag(v_a_2185_) == 0)
{
v___y_2213_ = v___x_2135_;
goto v___jp_2212_;
}
else
{
lean_dec_ref(v_a_2185_);
v___y_2213_ = v___x_2183_;
goto v___jp_2212_;
}
v___jp_2187_:
{
lean_object* v___x_2194_; uint8_t v___x_2195_; 
v___x_2194_ = l_Lean_Expr_cleanupAnnotations(v_arg_2127_);
v___x_2195_ = l_Lean_Expr_isApp(v___x_2194_);
if (v___x_2195_ == 0)
{
lean_dec_ref(v___x_2194_);
lean_dec_ref(v_arg_2094_);
lean_dec_ref(v_arg_2091_);
lean_dec_ref(v_origExpr_2065_);
goto v___jp_2073_;
}
else
{
lean_object* v___x_2196_; uint8_t v___x_2197_; 
v___x_2196_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2194_);
v___x_2197_ = l_Lean_Expr_isConstOf(v___x_2196_, v___x_2182_);
lean_dec_ref(v___x_2196_);
if (v___x_2197_ == 0)
{
lean_dec_ref(v_arg_2094_);
lean_dec_ref(v_arg_2091_);
lean_dec_ref(v_origExpr_2065_);
goto v___jp_2073_;
}
else
{
lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; 
v___x_2198_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__59));
v___x_2199_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__61));
v___x_2200_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftReflection(v_arg_2091_, v_arg_2094_, v___f_2186_, v___x_2198_, v___x_2199_, v_origExpr_2065_, v___y_2188_, v___y_2189_, v___y_2190_, v___y_2191_, v___y_2192_, v___y_2193_);
return v___x_2200_;
}
}
}
v___jp_2201_:
{
lean_object* v___x_2202_; lean_object* v___x_2203_; 
v___x_2202_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__63, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__63_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__63);
v___x_2203_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go_spec__12___redArg(v___x_2202_, v_a_2068_, v_a_2069_, v_a_2070_, v_a_2071_);
if (lean_obj_tag(v___x_2203_) == 0)
{
lean_dec_ref(v___x_2203_);
v___y_2188_ = v_a_2066_;
v___y_2189_ = v_a_2067_;
v___y_2190_ = v_a_2068_;
v___y_2191_ = v_a_2069_;
v___y_2192_ = v_a_2070_;
v___y_2193_ = v_a_2071_;
goto v___jp_2187_;
}
else
{
lean_object* v_a_2204_; lean_object* v___x_2206_; uint8_t v_isShared_2207_; uint8_t v_isSharedCheck_2211_; 
lean_dec_ref(v_arg_2127_);
lean_dec_ref(v_arg_2094_);
lean_dec_ref(v_arg_2091_);
lean_dec_ref(v_origExpr_2065_);
v_a_2204_ = lean_ctor_get(v___x_2203_, 0);
v_isSharedCheck_2211_ = !lean_is_exclusive(v___x_2203_);
if (v_isSharedCheck_2211_ == 0)
{
v___x_2206_ = v___x_2203_;
v_isShared_2207_ = v_isSharedCheck_2211_;
goto v_resetjp_2205_;
}
else
{
lean_inc(v_a_2204_);
lean_dec(v___x_2203_);
v___x_2206_ = lean_box(0);
v_isShared_2207_ = v_isSharedCheck_2211_;
goto v_resetjp_2205_;
}
v_resetjp_2205_:
{
lean_object* v___x_2209_; 
if (v_isShared_2207_ == 0)
{
v___x_2209_ = v___x_2206_;
goto v_reusejp_2208_;
}
else
{
lean_object* v_reuseFailAlloc_2210_; 
v_reuseFailAlloc_2210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2210_, 0, v_a_2204_);
v___x_2209_ = v_reuseFailAlloc_2210_;
goto v_reusejp_2208_;
}
v_reusejp_2208_:
{
return v___x_2209_;
}
}
}
}
v___jp_2212_:
{
if (v___y_2213_ == 0)
{
lean_dec(v_a_2169_);
v___y_2188_ = v_a_2066_;
v___y_2189_ = v_a_2067_;
v___y_2190_ = v_a_2068_;
v___y_2191_ = v_a_2069_;
v___y_2192_ = v_a_2070_;
v___y_2193_ = v_a_2071_;
goto v___jp_2187_;
}
else
{
if (lean_obj_tag(v_a_2169_) == 0)
{
if (v___x_2135_ == 0)
{
v___y_2188_ = v_a_2066_;
v___y_2189_ = v_a_2067_;
v___y_2190_ = v_a_2068_;
v___y_2191_ = v_a_2069_;
v___y_2192_ = v_a_2070_;
v___y_2193_ = v_a_2071_;
goto v___jp_2187_;
}
else
{
goto v___jp_2201_;
}
}
else
{
lean_dec_ref(v_a_2169_);
goto v___jp_2201_;
}
}
}
}
else
{
lean_object* v_a_2214_; lean_object* v___x_2216_; uint8_t v_isShared_2217_; uint8_t v_isSharedCheck_2221_; 
lean_dec(v_a_2169_);
lean_dec_ref(v_arg_2127_);
lean_dec_ref(v_arg_2094_);
lean_dec_ref(v_arg_2091_);
lean_dec_ref(v_origExpr_2065_);
v_a_2214_ = lean_ctor_get(v___x_2184_, 0);
v_isSharedCheck_2221_ = !lean_is_exclusive(v___x_2184_);
if (v_isSharedCheck_2221_ == 0)
{
v___x_2216_ = v___x_2184_;
v_isShared_2217_ = v_isSharedCheck_2221_;
goto v_resetjp_2215_;
}
else
{
lean_inc(v_a_2214_);
lean_dec(v___x_2184_);
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
v___jp_2173_:
{
lean_object* v___x_2174_; lean_object* v___x_2176_; 
v___x_2174_ = lean_box(0);
if (v_isShared_2172_ == 0)
{
lean_ctor_set(v___x_2171_, 0, v___x_2174_);
v___x_2176_ = v___x_2171_;
goto v_reusejp_2175_;
}
else
{
lean_object* v_reuseFailAlloc_2177_; 
v_reuseFailAlloc_2177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2177_, 0, v___x_2174_);
v___x_2176_ = v_reuseFailAlloc_2177_;
goto v_reusejp_2175_;
}
v_reusejp_2175_:
{
return v___x_2176_;
}
}
}
}
else
{
lean_object* v_a_2223_; lean_object* v___x_2225_; uint8_t v_isShared_2226_; uint8_t v_isSharedCheck_2230_; 
lean_dec_ref(v_arg_2130_);
lean_dec_ref(v_arg_2127_);
lean_dec_ref(v_arg_2094_);
lean_dec_ref(v_arg_2091_);
lean_dec_ref(v_origExpr_2065_);
v_a_2223_ = lean_ctor_get(v___x_2168_, 0);
v_isSharedCheck_2230_ = !lean_is_exclusive(v___x_2168_);
if (v_isSharedCheck_2230_ == 0)
{
v___x_2225_ = v___x_2168_;
v_isShared_2226_ = v_isSharedCheck_2230_;
goto v_resetjp_2224_;
}
else
{
lean_inc(v_a_2223_);
lean_dec(v___x_2168_);
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
}
else
{
lean_object* v___x_2231_; 
lean_dec_ref(v___x_2131_);
lean_del_object(v___x_2082_);
lean_inc_ref(v_arg_2091_);
lean_inc_ref(v_arg_2127_);
v___x_2231_ = l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_getNatOrBvValue_x3f___redArg(v_arg_2127_, v_arg_2091_, v_a_2068_, v_a_2069_, v_a_2070_, v_a_2071_);
if (lean_obj_tag(v___x_2231_) == 0)
{
lean_object* v_a_2232_; lean_object* v___x_2234_; uint8_t v_isShared_2235_; uint8_t v_isSharedCheck_2285_; 
v_a_2232_ = lean_ctor_get(v___x_2231_, 0);
v_isSharedCheck_2285_ = !lean_is_exclusive(v___x_2231_);
if (v_isSharedCheck_2285_ == 0)
{
v___x_2234_ = v___x_2231_;
v_isShared_2235_ = v_isSharedCheck_2285_;
goto v_resetjp_2233_;
}
else
{
lean_inc(v_a_2232_);
lean_dec(v___x_2231_);
v___x_2234_ = lean_box(0);
v_isShared_2235_ = v_isSharedCheck_2285_;
goto v_resetjp_2233_;
}
v_resetjp_2233_:
{
lean_object* v___x_2241_; uint8_t v___x_2242_; 
v___x_2241_ = l_Lean_Expr_cleanupAnnotations(v_arg_2130_);
v___x_2242_ = l_Lean_Expr_isApp(v___x_2241_);
if (v___x_2242_ == 0)
{
lean_dec_ref(v___x_2241_);
lean_dec(v_a_2232_);
lean_dec_ref(v_arg_2127_);
lean_dec_ref(v_arg_2094_);
lean_dec_ref(v_arg_2091_);
lean_dec_ref(v_origExpr_2065_);
goto v___jp_2236_;
}
else
{
lean_object* v_arg_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; uint8_t v___x_2246_; 
v_arg_2243_ = lean_ctor_get(v___x_2241_, 1);
lean_inc_ref(v_arg_2243_);
v___x_2244_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2241_);
v___x_2245_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_of_go___closed__8));
v___x_2246_ = l_Lean_Expr_isConstOf(v___x_2244_, v___x_2245_);
lean_dec_ref(v___x_2244_);
if (v___x_2246_ == 0)
{
lean_dec_ref(v_arg_2243_);
lean_dec(v_a_2232_);
lean_dec_ref(v_arg_2127_);
lean_dec_ref(v_arg_2094_);
lean_dec_ref(v_arg_2091_);
lean_dec_ref(v_origExpr_2065_);
goto v___jp_2236_;
}
else
{
lean_object* v___x_2247_; 
lean_del_object(v___x_2234_);
v___x_2247_ = l_Lean_Meta_getNatValue_x3f(v_arg_2243_, v_a_2068_, v_a_2069_, v_a_2070_, v_a_2071_);
lean_dec_ref(v_arg_2243_);
if (lean_obj_tag(v___x_2247_) == 0)
{
lean_object* v_a_2248_; lean_object* v___f_2249_; lean_object* v___y_2251_; lean_object* v___y_2252_; lean_object* v___y_2253_; lean_object* v___y_2254_; lean_object* v___y_2255_; lean_object* v___y_2256_; uint8_t v___y_2276_; 
v_a_2248_ = lean_ctor_get(v___x_2247_, 0);
lean_inc(v_a_2248_);
lean_dec_ref(v___x_2247_);
v___f_2249_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__64));
if (lean_obj_tag(v_a_2248_) == 0)
{
v___y_2276_ = v___x_2133_;
goto v___jp_2275_;
}
else
{
lean_dec_ref(v_a_2248_);
v___y_2276_ = v___x_2246_;
goto v___jp_2275_;
}
v___jp_2250_:
{
lean_object* v___x_2257_; uint8_t v___x_2258_; 
v___x_2257_ = l_Lean_Expr_cleanupAnnotations(v_arg_2127_);
v___x_2258_ = l_Lean_Expr_isApp(v___x_2257_);
if (v___x_2258_ == 0)
{
lean_dec_ref(v___x_2257_);
lean_dec_ref(v_arg_2094_);
lean_dec_ref(v_arg_2091_);
lean_dec_ref(v_origExpr_2065_);
goto v___jp_2076_;
}
else
{
lean_object* v___x_2259_; uint8_t v___x_2260_; 
v___x_2259_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2257_);
v___x_2260_ = l_Lean_Expr_isConstOf(v___x_2259_, v___x_2245_);
lean_dec_ref(v___x_2259_);
if (v___x_2260_ == 0)
{
lean_dec_ref(v_arg_2094_);
lean_dec_ref(v_arg_2091_);
lean_dec_ref(v_origExpr_2065_);
goto v___jp_2076_;
}
else
{
lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; 
v___x_2261_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__66));
v___x_2262_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__68));
v___x_2263_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftReflection(v_arg_2091_, v_arg_2094_, v___f_2249_, v___x_2261_, v___x_2262_, v_origExpr_2065_, v___y_2251_, v___y_2252_, v___y_2253_, v___y_2254_, v___y_2255_, v___y_2256_);
return v___x_2263_;
}
}
}
v___jp_2264_:
{
lean_object* v___x_2265_; lean_object* v___x_2266_; 
v___x_2265_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__63, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__63_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__63);
v___x_2266_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go_spec__12___redArg(v___x_2265_, v_a_2068_, v_a_2069_, v_a_2070_, v_a_2071_);
if (lean_obj_tag(v___x_2266_) == 0)
{
lean_dec_ref(v___x_2266_);
v___y_2251_ = v_a_2066_;
v___y_2252_ = v_a_2067_;
v___y_2253_ = v_a_2068_;
v___y_2254_ = v_a_2069_;
v___y_2255_ = v_a_2070_;
v___y_2256_ = v_a_2071_;
goto v___jp_2250_;
}
else
{
lean_object* v_a_2267_; lean_object* v___x_2269_; uint8_t v_isShared_2270_; uint8_t v_isSharedCheck_2274_; 
lean_dec_ref(v_arg_2127_);
lean_dec_ref(v_arg_2094_);
lean_dec_ref(v_arg_2091_);
lean_dec_ref(v_origExpr_2065_);
v_a_2267_ = lean_ctor_get(v___x_2266_, 0);
v_isSharedCheck_2274_ = !lean_is_exclusive(v___x_2266_);
if (v_isSharedCheck_2274_ == 0)
{
v___x_2269_ = v___x_2266_;
v_isShared_2270_ = v_isSharedCheck_2274_;
goto v_resetjp_2268_;
}
else
{
lean_inc(v_a_2267_);
lean_dec(v___x_2266_);
v___x_2269_ = lean_box(0);
v_isShared_2270_ = v_isSharedCheck_2274_;
goto v_resetjp_2268_;
}
v_resetjp_2268_:
{
lean_object* v___x_2272_; 
if (v_isShared_2270_ == 0)
{
v___x_2272_ = v___x_2269_;
goto v_reusejp_2271_;
}
else
{
lean_object* v_reuseFailAlloc_2273_; 
v_reuseFailAlloc_2273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2273_, 0, v_a_2267_);
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
v___jp_2275_:
{
if (v___y_2276_ == 0)
{
lean_dec(v_a_2232_);
v___y_2251_ = v_a_2066_;
v___y_2252_ = v_a_2067_;
v___y_2253_ = v_a_2068_;
v___y_2254_ = v_a_2069_;
v___y_2255_ = v_a_2070_;
v___y_2256_ = v_a_2071_;
goto v___jp_2250_;
}
else
{
if (lean_obj_tag(v_a_2232_) == 0)
{
if (v___x_2133_ == 0)
{
v___y_2251_ = v_a_2066_;
v___y_2252_ = v_a_2067_;
v___y_2253_ = v_a_2068_;
v___y_2254_ = v_a_2069_;
v___y_2255_ = v_a_2070_;
v___y_2256_ = v_a_2071_;
goto v___jp_2250_;
}
else
{
goto v___jp_2264_;
}
}
else
{
lean_dec_ref(v_a_2232_);
goto v___jp_2264_;
}
}
}
}
else
{
lean_object* v_a_2277_; lean_object* v___x_2279_; uint8_t v_isShared_2280_; uint8_t v_isSharedCheck_2284_; 
lean_dec(v_a_2232_);
lean_dec_ref(v_arg_2127_);
lean_dec_ref(v_arg_2094_);
lean_dec_ref(v_arg_2091_);
lean_dec_ref(v_origExpr_2065_);
v_a_2277_ = lean_ctor_get(v___x_2247_, 0);
v_isSharedCheck_2284_ = !lean_is_exclusive(v___x_2247_);
if (v_isSharedCheck_2284_ == 0)
{
v___x_2279_ = v___x_2247_;
v_isShared_2280_ = v_isSharedCheck_2284_;
goto v_resetjp_2278_;
}
else
{
lean_inc(v_a_2277_);
lean_dec(v___x_2247_);
v___x_2279_ = lean_box(0);
v_isShared_2280_ = v_isSharedCheck_2284_;
goto v_resetjp_2278_;
}
v_resetjp_2278_:
{
lean_object* v___x_2282_; 
if (v_isShared_2280_ == 0)
{
v___x_2282_ = v___x_2279_;
goto v_reusejp_2281_;
}
else
{
lean_object* v_reuseFailAlloc_2283_; 
v_reuseFailAlloc_2283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2283_, 0, v_a_2277_);
v___x_2282_ = v_reuseFailAlloc_2283_;
goto v_reusejp_2281_;
}
v_reusejp_2281_:
{
return v___x_2282_;
}
}
}
}
}
v___jp_2236_:
{
lean_object* v___x_2237_; lean_object* v___x_2239_; 
v___x_2237_ = lean_box(0);
if (v_isShared_2235_ == 0)
{
lean_ctor_set(v___x_2234_, 0, v___x_2237_);
v___x_2239_ = v___x_2234_;
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
}
else
{
lean_object* v_a_2286_; lean_object* v___x_2288_; uint8_t v_isShared_2289_; uint8_t v_isSharedCheck_2293_; 
lean_dec_ref(v_arg_2130_);
lean_dec_ref(v_arg_2127_);
lean_dec_ref(v_arg_2094_);
lean_dec_ref(v_arg_2091_);
lean_dec_ref(v_origExpr_2065_);
v_a_2286_ = lean_ctor_get(v___x_2231_, 0);
v_isSharedCheck_2293_ = !lean_is_exclusive(v___x_2231_);
if (v_isSharedCheck_2293_ == 0)
{
v___x_2288_ = v___x_2231_;
v_isShared_2289_ = v_isSharedCheck_2293_;
goto v_resetjp_2287_;
}
else
{
lean_inc(v_a_2286_);
lean_dec(v___x_2231_);
v___x_2288_ = lean_box(0);
v_isShared_2289_ = v_isSharedCheck_2293_;
goto v_resetjp_2287_;
}
v_resetjp_2287_:
{
lean_object* v___x_2291_; 
if (v_isShared_2289_ == 0)
{
v___x_2291_ = v___x_2288_;
goto v_reusejp_2290_;
}
else
{
lean_object* v_reuseFailAlloc_2292_; 
v_reuseFailAlloc_2292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2292_, 0, v_a_2286_);
v___x_2291_ = v_reuseFailAlloc_2292_;
goto v_reusejp_2290_;
}
v_reusejp_2290_:
{
return v___x_2291_;
}
}
}
}
}
else
{
lean_object* v___x_2294_; 
lean_dec_ref(v___x_2131_);
lean_dec_ref(v_arg_2130_);
lean_dec_ref(v_arg_2127_);
lean_del_object(v___x_2082_);
lean_inc_ref(v_arg_2094_);
v___x_2294_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_goOrAtom(v_arg_2094_, v_a_2066_, v_a_2067_, v_a_2068_, v_a_2069_, v_a_2070_, v_a_2071_);
if (lean_obj_tag(v___x_2294_) == 0)
{
lean_object* v_a_2295_; lean_object* v___x_2297_; uint8_t v_isShared_2298_; uint8_t v_isSharedCheck_2358_; 
v_a_2295_ = lean_ctor_get(v___x_2294_, 0);
v_isSharedCheck_2358_ = !lean_is_exclusive(v___x_2294_);
if (v_isSharedCheck_2358_ == 0)
{
v___x_2297_ = v___x_2294_;
v_isShared_2298_ = v_isSharedCheck_2358_;
goto v_resetjp_2296_;
}
else
{
lean_inc(v_a_2295_);
lean_dec(v___x_2294_);
v___x_2297_ = lean_box(0);
v_isShared_2298_ = v_isSharedCheck_2358_;
goto v_resetjp_2296_;
}
v_resetjp_2296_:
{
if (lean_obj_tag(v_a_2295_) == 1)
{
lean_object* v_val_2299_; lean_object* v___x_2300_; 
lean_del_object(v___x_2297_);
v_val_2299_ = lean_ctor_get(v_a_2295_, 0);
lean_inc(v_val_2299_);
lean_dec_ref(v_a_2295_);
lean_inc_ref(v_arg_2091_);
v___x_2300_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_goOrAtom(v_arg_2091_, v_a_2066_, v_a_2067_, v_a_2068_, v_a_2069_, v_a_2070_, v_a_2071_);
if (lean_obj_tag(v___x_2300_) == 0)
{
lean_object* v_a_2301_; lean_object* v___x_2303_; uint8_t v_isShared_2304_; uint8_t v_isSharedCheck_2353_; 
v_a_2301_ = lean_ctor_get(v___x_2300_, 0);
v_isSharedCheck_2353_ = !lean_is_exclusive(v___x_2300_);
if (v_isSharedCheck_2353_ == 0)
{
v___x_2303_ = v___x_2300_;
v_isShared_2304_ = v_isSharedCheck_2353_;
goto v_resetjp_2302_;
}
else
{
lean_inc(v_a_2301_);
lean_dec(v___x_2300_);
v___x_2303_ = lean_box(0);
v_isShared_2304_ = v_isSharedCheck_2353_;
goto v_resetjp_2302_;
}
v_resetjp_2302_:
{
if (lean_obj_tag(v_a_2301_) == 1)
{
lean_object* v_val_2305_; lean_object* v___x_2307_; uint8_t v_isShared_2308_; uint8_t v_isSharedCheck_2348_; 
lean_del_object(v___x_2303_);
v_val_2305_ = lean_ctor_get(v_a_2301_, 0);
v_isSharedCheck_2348_ = !lean_is_exclusive(v_a_2301_);
if (v_isSharedCheck_2348_ == 0)
{
v___x_2307_ = v_a_2301_;
v_isShared_2308_ = v_isSharedCheck_2348_;
goto v_resetjp_2306_;
}
else
{
lean_inc(v_val_2305_);
lean_dec(v_a_2301_);
v___x_2307_ = lean_box(0);
v_isShared_2308_ = v_isSharedCheck_2348_;
goto v_resetjp_2306_;
}
v_resetjp_2306_:
{
lean_object* v_width_2309_; lean_object* v_bvExpr_2310_; lean_object* v_expr_2311_; lean_object* v_width_2312_; lean_object* v_bvExpr_2313_; lean_object* v_expr_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; 
v_width_2309_ = lean_ctor_get(v_val_2299_, 0);
lean_inc(v_width_2309_);
v_bvExpr_2310_ = lean_ctor_get(v_val_2299_, 1);
v_expr_2311_ = lean_ctor_get(v_val_2299_, 4);
lean_inc_ref(v_expr_2311_);
v_width_2312_ = lean_ctor_get(v_val_2305_, 0);
lean_inc(v_width_2312_);
v_bvExpr_2313_ = lean_ctor_get(v_val_2305_, 1);
v_expr_2314_ = lean_ctor_get(v_val_2305_, 4);
lean_inc_ref(v_expr_2314_);
v___x_2315_ = lean_nat_add(v_width_2309_, v_width_2312_);
lean_inc_ref(v_bvExpr_2313_);
lean_inc_ref(v_bvExpr_2310_);
lean_inc(v___x_2315_);
lean_inc(v_width_2312_);
lean_inc(v_width_2309_);
v___x_2316_ = l_Std_Tactic_BVDecide_BVExpr_append___override___redArg(v_width_2309_, v_width_2312_, v___x_2315_, v_bvExpr_2310_, v_bvExpr_2313_);
lean_inc(v___x_2315_);
v___x_2317_ = l_Lean_mkNatLit(v___x_2315_);
lean_inc_ref(v___x_2317_);
v___x_2318_ = l_Lean_Meta_mkEqRefl(v___x_2317_, v_a_2068_, v_a_2069_, v_a_2070_, v_a_2071_);
if (lean_obj_tag(v___x_2318_) == 0)
{
lean_object* v_a_2319_; lean_object* v___x_2321_; uint8_t v_isShared_2322_; uint8_t v_isSharedCheck_2339_; 
v_a_2319_ = lean_ctor_get(v___x_2318_, 0);
v_isSharedCheck_2339_ = !lean_is_exclusive(v___x_2318_);
if (v_isSharedCheck_2339_ == 0)
{
v___x_2321_ = v___x_2318_;
v_isShared_2322_ = v_isSharedCheck_2339_;
goto v_resetjp_2320_;
}
else
{
lean_inc(v_a_2319_);
lean_dec(v___x_2318_);
v___x_2321_ = lean_box(0);
v_isShared_2322_ = v_isSharedCheck_2339_;
goto v_resetjp_2320_;
}
v_resetjp_2320_:
{
lean_object* v___x_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___f_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2334_; 
v___x_2323_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0));
v___x_2324_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1));
v___x_2325_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2));
v___x_2326_ = lean_box(0);
v___x_2327_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__71, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__71_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__71);
lean_inc(v_width_2309_);
v___x_2328_ = l_Lean_mkNatLit(v_width_2309_);
lean_inc(v_width_2312_);
v___x_2329_ = l_Lean_mkNatLit(v_width_2312_);
lean_inc_ref(v___x_2329_);
lean_inc_ref(v___x_2328_);
lean_inc_ref(v_expr_2314_);
lean_inc_ref(v_expr_2311_);
v___f_2330_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___lam__0___boxed), 21, 15);
lean_closure_set(v___f_2330_, 0, v_width_2309_);
lean_closure_set(v___f_2330_, 1, v_expr_2311_);
lean_closure_set(v___f_2330_, 2, v_width_2312_);
lean_closure_set(v___f_2330_, 3, v_expr_2314_);
lean_closure_set(v___f_2330_, 4, v_val_2299_);
lean_closure_set(v___f_2330_, 5, v_val_2305_);
lean_closure_set(v___f_2330_, 6, v___x_2323_);
lean_closure_set(v___f_2330_, 7, v___x_2324_);
lean_closure_set(v___f_2330_, 8, v___x_2325_);
lean_closure_set(v___f_2330_, 9, v___x_2096_);
lean_closure_set(v___f_2330_, 10, v___x_2326_);
lean_closure_set(v___f_2330_, 11, v___x_2328_);
lean_closure_set(v___f_2330_, 12, v___x_2329_);
lean_closure_set(v___f_2330_, 13, v_arg_2094_);
lean_closure_set(v___f_2330_, 14, v_arg_2091_);
v___x_2331_ = l_Lean_mkApp6(v___x_2327_, v___x_2328_, v___x_2329_, v___x_2317_, v_expr_2311_, v_expr_2314_, v_a_2319_);
v___x_2332_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2332_, 0, v___x_2315_);
lean_ctor_set(v___x_2332_, 1, v___x_2316_);
lean_ctor_set(v___x_2332_, 2, v_origExpr_2065_);
lean_ctor_set(v___x_2332_, 3, v___f_2330_);
lean_ctor_set(v___x_2332_, 4, v___x_2331_);
if (v_isShared_2308_ == 0)
{
lean_ctor_set(v___x_2307_, 0, v___x_2332_);
v___x_2334_ = v___x_2307_;
goto v_reusejp_2333_;
}
else
{
lean_object* v_reuseFailAlloc_2338_; 
v_reuseFailAlloc_2338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2338_, 0, v___x_2332_);
v___x_2334_ = v_reuseFailAlloc_2338_;
goto v_reusejp_2333_;
}
v_reusejp_2333_:
{
lean_object* v___x_2336_; 
if (v_isShared_2322_ == 0)
{
lean_ctor_set(v___x_2321_, 0, v___x_2334_);
v___x_2336_ = v___x_2321_;
goto v_reusejp_2335_;
}
else
{
lean_object* v_reuseFailAlloc_2337_; 
v_reuseFailAlloc_2337_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2337_, 0, v___x_2334_);
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
lean_object* v_a_2340_; lean_object* v___x_2342_; uint8_t v_isShared_2343_; uint8_t v_isSharedCheck_2347_; 
lean_dec_ref(v___x_2317_);
lean_dec_ref(v___x_2316_);
lean_dec(v___x_2315_);
lean_dec_ref(v_expr_2314_);
lean_dec(v_width_2312_);
lean_dec_ref(v_expr_2311_);
lean_dec(v_width_2309_);
lean_del_object(v___x_2307_);
lean_dec(v_val_2305_);
lean_dec(v_val_2299_);
lean_dec_ref(v_arg_2094_);
lean_dec_ref(v_arg_2091_);
lean_dec_ref(v_origExpr_2065_);
v_a_2340_ = lean_ctor_get(v___x_2318_, 0);
v_isSharedCheck_2347_ = !lean_is_exclusive(v___x_2318_);
if (v_isSharedCheck_2347_ == 0)
{
v___x_2342_ = v___x_2318_;
v_isShared_2343_ = v_isSharedCheck_2347_;
goto v_resetjp_2341_;
}
else
{
lean_inc(v_a_2340_);
lean_dec(v___x_2318_);
v___x_2342_ = lean_box(0);
v_isShared_2343_ = v_isSharedCheck_2347_;
goto v_resetjp_2341_;
}
v_resetjp_2341_:
{
lean_object* v___x_2345_; 
if (v_isShared_2343_ == 0)
{
v___x_2345_ = v___x_2342_;
goto v_reusejp_2344_;
}
else
{
lean_object* v_reuseFailAlloc_2346_; 
v_reuseFailAlloc_2346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2346_, 0, v_a_2340_);
v___x_2345_ = v_reuseFailAlloc_2346_;
goto v_reusejp_2344_;
}
v_reusejp_2344_:
{
return v___x_2345_;
}
}
}
}
}
else
{
lean_object* v___x_2349_; lean_object* v___x_2351_; 
lean_dec(v_a_2301_);
lean_dec(v_val_2299_);
lean_dec_ref(v_arg_2094_);
lean_dec_ref(v_arg_2091_);
lean_dec_ref(v_origExpr_2065_);
v___x_2349_ = lean_box(0);
if (v_isShared_2304_ == 0)
{
lean_ctor_set(v___x_2303_, 0, v___x_2349_);
v___x_2351_ = v___x_2303_;
goto v_reusejp_2350_;
}
else
{
lean_object* v_reuseFailAlloc_2352_; 
v_reuseFailAlloc_2352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2352_, 0, v___x_2349_);
v___x_2351_ = v_reuseFailAlloc_2352_;
goto v_reusejp_2350_;
}
v_reusejp_2350_:
{
return v___x_2351_;
}
}
}
}
else
{
lean_dec(v_val_2299_);
lean_dec_ref(v_arg_2094_);
lean_dec_ref(v_arg_2091_);
lean_dec_ref(v_origExpr_2065_);
return v___x_2300_;
}
}
else
{
lean_object* v___x_2354_; lean_object* v___x_2356_; 
lean_dec(v_a_2295_);
lean_dec_ref(v_arg_2094_);
lean_dec_ref(v_arg_2091_);
lean_dec_ref(v_origExpr_2065_);
v___x_2354_ = lean_box(0);
if (v_isShared_2298_ == 0)
{
lean_ctor_set(v___x_2297_, 0, v___x_2354_);
v___x_2356_ = v___x_2297_;
goto v_reusejp_2355_;
}
else
{
lean_object* v_reuseFailAlloc_2357_; 
v_reuseFailAlloc_2357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2357_, 0, v___x_2354_);
v___x_2356_ = v_reuseFailAlloc_2357_;
goto v_reusejp_2355_;
}
v_reusejp_2355_:
{
return v___x_2356_;
}
}
}
}
else
{
lean_dec_ref(v_arg_2094_);
lean_dec_ref(v_arg_2091_);
lean_dec_ref(v_origExpr_2065_);
return v___x_2294_;
}
}
}
}
}
else
{
lean_object* v___f_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; 
lean_dec_ref(v___x_2119_);
lean_del_object(v___x_2082_);
v___f_2359_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__72));
v___x_2360_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__74));
v___x_2361_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__76));
v___x_2362_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftReflection(v_arg_2091_, v_arg_2094_, v___f_2359_, v___x_2360_, v___x_2361_, v_origExpr_2065_, v_a_2066_, v_a_2067_, v_a_2068_, v_a_2069_, v_a_2070_, v_a_2071_);
return v___x_2362_;
}
}
else
{
lean_object* v___x_2363_; 
lean_dec_ref(v___x_2119_);
lean_del_object(v___x_2082_);
v___x_2363_ = l_Lean_Meta_getNatValue_x3f(v_arg_2106_, v_a_2068_, v_a_2069_, v_a_2070_, v_a_2071_);
if (lean_obj_tag(v___x_2363_) == 0)
{
lean_object* v_a_2364_; lean_object* v___x_2366_; uint8_t v_isShared_2367_; uint8_t v_isSharedCheck_2426_; 
v_a_2364_ = lean_ctor_get(v___x_2363_, 0);
v_isSharedCheck_2426_ = !lean_is_exclusive(v___x_2363_);
if (v_isSharedCheck_2426_ == 0)
{
v___x_2366_ = v___x_2363_;
v_isShared_2367_ = v_isSharedCheck_2426_;
goto v_resetjp_2365_;
}
else
{
lean_inc(v_a_2364_);
lean_dec(v___x_2363_);
v___x_2366_ = lean_box(0);
v_isShared_2367_ = v_isSharedCheck_2426_;
goto v_resetjp_2365_;
}
v_resetjp_2365_:
{
if (lean_obj_tag(v_a_2364_) == 1)
{
lean_object* v_val_2368_; lean_object* v___x_2369_; 
lean_del_object(v___x_2366_);
v_val_2368_ = lean_ctor_get(v_a_2364_, 0);
lean_inc(v_val_2368_);
lean_dec_ref(v_a_2364_);
v___x_2369_ = l_Lean_Meta_getNatValue_x3f(v_arg_2094_, v_a_2068_, v_a_2069_, v_a_2070_, v_a_2071_);
if (lean_obj_tag(v___x_2369_) == 0)
{
lean_object* v_a_2370_; lean_object* v___x_2372_; uint8_t v_isShared_2373_; uint8_t v_isSharedCheck_2413_; 
v_a_2370_ = lean_ctor_get(v___x_2369_, 0);
v_isSharedCheck_2413_ = !lean_is_exclusive(v___x_2369_);
if (v_isSharedCheck_2413_ == 0)
{
v___x_2372_ = v___x_2369_;
v_isShared_2373_ = v_isSharedCheck_2413_;
goto v_resetjp_2371_;
}
else
{
lean_inc(v_a_2370_);
lean_dec(v___x_2369_);
v___x_2372_ = lean_box(0);
v_isShared_2373_ = v_isSharedCheck_2413_;
goto v_resetjp_2371_;
}
v_resetjp_2371_:
{
if (lean_obj_tag(v_a_2370_) == 1)
{
lean_object* v_val_2374_; lean_object* v___x_2375_; 
lean_del_object(v___x_2372_);
v_val_2374_ = lean_ctor_get(v_a_2370_, 0);
lean_inc(v_val_2374_);
lean_dec_ref(v_a_2370_);
lean_inc_ref(v_arg_2091_);
v___x_2375_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_goOrAtom(v_arg_2091_, v_a_2066_, v_a_2067_, v_a_2068_, v_a_2069_, v_a_2070_, v_a_2071_);
if (lean_obj_tag(v___x_2375_) == 0)
{
lean_object* v_a_2376_; lean_object* v___x_2378_; uint8_t v_isShared_2379_; uint8_t v_isSharedCheck_2408_; 
v_a_2376_ = lean_ctor_get(v___x_2375_, 0);
v_isSharedCheck_2408_ = !lean_is_exclusive(v___x_2375_);
if (v_isSharedCheck_2408_ == 0)
{
v___x_2378_ = v___x_2375_;
v_isShared_2379_ = v_isSharedCheck_2408_;
goto v_resetjp_2377_;
}
else
{
lean_inc(v_a_2376_);
lean_dec(v___x_2375_);
v___x_2378_ = lean_box(0);
v_isShared_2379_ = v_isSharedCheck_2408_;
goto v_resetjp_2377_;
}
v_resetjp_2377_:
{
if (lean_obj_tag(v_a_2376_) == 1)
{
lean_object* v_val_2380_; lean_object* v___x_2382_; uint8_t v_isShared_2383_; uint8_t v_isSharedCheck_2403_; 
v_val_2380_ = lean_ctor_get(v_a_2376_, 0);
v_isSharedCheck_2403_ = !lean_is_exclusive(v_a_2376_);
if (v_isSharedCheck_2403_ == 0)
{
v___x_2382_ = v_a_2376_;
v_isShared_2383_ = v_isSharedCheck_2403_;
goto v_resetjp_2381_;
}
else
{
lean_inc(v_val_2380_);
lean_dec(v_a_2376_);
v___x_2382_ = lean_box(0);
v_isShared_2383_ = v_isSharedCheck_2403_;
goto v_resetjp_2381_;
}
v_resetjp_2381_:
{
lean_object* v_width_2384_; lean_object* v_bvExpr_2385_; lean_object* v_expr_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___f_2394_; lean_object* v___x_2395_; lean_object* v___x_2396_; lean_object* v___x_2398_; 
v_width_2384_ = lean_ctor_get(v_val_2380_, 0);
lean_inc(v_width_2384_);
v_bvExpr_2385_ = lean_ctor_get(v_val_2380_, 1);
v_expr_2386_ = lean_ctor_get(v_val_2380_, 4);
lean_inc_ref(v_expr_2386_);
lean_inc_ref(v_bvExpr_2385_);
lean_inc(v_val_2374_);
lean_inc(v_width_2384_);
v___x_2387_ = l_Std_Tactic_BVDecide_BVExpr_extract___override(v_width_2384_, v_val_2368_, v_val_2374_, v_bvExpr_2385_);
v___x_2388_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0));
v___x_2389_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1));
v___x_2390_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2));
v___x_2391_ = lean_box(0);
v___x_2392_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__79, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__79_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__79);
lean_inc(v_width_2384_);
v___x_2393_ = l_Lean_mkNatLit(v_width_2384_);
lean_inc_ref(v___x_2393_);
lean_inc_ref(v_arg_2094_);
lean_inc_ref(v_arg_2106_);
lean_inc_ref(v_expr_2386_);
v___f_2394_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___lam__1___boxed), 18, 12);
lean_closure_set(v___f_2394_, 0, v_width_2384_);
lean_closure_set(v___f_2394_, 1, v_expr_2386_);
lean_closure_set(v___f_2394_, 2, v_val_2380_);
lean_closure_set(v___f_2394_, 3, v___x_2388_);
lean_closure_set(v___f_2394_, 4, v___x_2389_);
lean_closure_set(v___f_2394_, 5, v___x_2390_);
lean_closure_set(v___f_2394_, 6, v___x_2096_);
lean_closure_set(v___f_2394_, 7, v___x_2391_);
lean_closure_set(v___f_2394_, 8, v_arg_2106_);
lean_closure_set(v___f_2394_, 9, v_arg_2094_);
lean_closure_set(v___f_2394_, 10, v___x_2393_);
lean_closure_set(v___f_2394_, 11, v_arg_2091_);
v___x_2395_ = l_Lean_mkApp4(v___x_2392_, v___x_2393_, v_arg_2106_, v_arg_2094_, v_expr_2386_);
v___x_2396_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2396_, 0, v_val_2374_);
lean_ctor_set(v___x_2396_, 1, v___x_2387_);
lean_ctor_set(v___x_2396_, 2, v_origExpr_2065_);
lean_ctor_set(v___x_2396_, 3, v___f_2394_);
lean_ctor_set(v___x_2396_, 4, v___x_2395_);
if (v_isShared_2383_ == 0)
{
lean_ctor_set(v___x_2382_, 0, v___x_2396_);
v___x_2398_ = v___x_2382_;
goto v_reusejp_2397_;
}
else
{
lean_object* v_reuseFailAlloc_2402_; 
v_reuseFailAlloc_2402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2402_, 0, v___x_2396_);
v___x_2398_ = v_reuseFailAlloc_2402_;
goto v_reusejp_2397_;
}
v_reusejp_2397_:
{
lean_object* v___x_2400_; 
if (v_isShared_2379_ == 0)
{
lean_ctor_set(v___x_2378_, 0, v___x_2398_);
v___x_2400_ = v___x_2378_;
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
lean_object* v___x_2404_; lean_object* v___x_2406_; 
lean_dec(v_a_2376_);
lean_dec(v_val_2374_);
lean_dec(v_val_2368_);
lean_dec_ref(v_arg_2106_);
lean_dec_ref(v_arg_2094_);
lean_dec_ref(v_arg_2091_);
lean_dec_ref(v_origExpr_2065_);
v___x_2404_ = lean_box(0);
if (v_isShared_2379_ == 0)
{
lean_ctor_set(v___x_2378_, 0, v___x_2404_);
v___x_2406_ = v___x_2378_;
goto v_reusejp_2405_;
}
else
{
lean_object* v_reuseFailAlloc_2407_; 
v_reuseFailAlloc_2407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2407_, 0, v___x_2404_);
v___x_2406_ = v_reuseFailAlloc_2407_;
goto v_reusejp_2405_;
}
v_reusejp_2405_:
{
return v___x_2406_;
}
}
}
}
else
{
lean_dec(v_val_2374_);
lean_dec(v_val_2368_);
lean_dec_ref(v_arg_2106_);
lean_dec_ref(v_arg_2094_);
lean_dec_ref(v_arg_2091_);
lean_dec_ref(v_origExpr_2065_);
return v___x_2375_;
}
}
else
{
lean_object* v___x_2409_; lean_object* v___x_2411_; 
lean_dec(v_a_2370_);
lean_dec(v_val_2368_);
lean_dec_ref(v_arg_2106_);
lean_dec_ref(v_arg_2094_);
lean_dec_ref(v_arg_2091_);
lean_dec_ref(v_origExpr_2065_);
v___x_2409_ = lean_box(0);
if (v_isShared_2373_ == 0)
{
lean_ctor_set(v___x_2372_, 0, v___x_2409_);
v___x_2411_ = v___x_2372_;
goto v_reusejp_2410_;
}
else
{
lean_object* v_reuseFailAlloc_2412_; 
v_reuseFailAlloc_2412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2412_, 0, v___x_2409_);
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
else
{
lean_object* v_a_2414_; lean_object* v___x_2416_; uint8_t v_isShared_2417_; uint8_t v_isSharedCheck_2421_; 
lean_dec(v_val_2368_);
lean_dec_ref(v_arg_2106_);
lean_dec_ref(v_arg_2094_);
lean_dec_ref(v_arg_2091_);
lean_dec_ref(v_origExpr_2065_);
v_a_2414_ = lean_ctor_get(v___x_2369_, 0);
v_isSharedCheck_2421_ = !lean_is_exclusive(v___x_2369_);
if (v_isSharedCheck_2421_ == 0)
{
v___x_2416_ = v___x_2369_;
v_isShared_2417_ = v_isSharedCheck_2421_;
goto v_resetjp_2415_;
}
else
{
lean_inc(v_a_2414_);
lean_dec(v___x_2369_);
v___x_2416_ = lean_box(0);
v_isShared_2417_ = v_isSharedCheck_2421_;
goto v_resetjp_2415_;
}
v_resetjp_2415_:
{
lean_object* v___x_2419_; 
if (v_isShared_2417_ == 0)
{
v___x_2419_ = v___x_2416_;
goto v_reusejp_2418_;
}
else
{
lean_object* v_reuseFailAlloc_2420_; 
v_reuseFailAlloc_2420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2420_, 0, v_a_2414_);
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
lean_object* v___x_2422_; lean_object* v___x_2424_; 
lean_dec(v_a_2364_);
lean_dec_ref(v_arg_2106_);
lean_dec_ref(v_arg_2094_);
lean_dec_ref(v_arg_2091_);
lean_dec_ref(v_origExpr_2065_);
v___x_2422_ = lean_box(0);
if (v_isShared_2367_ == 0)
{
lean_ctor_set(v___x_2366_, 0, v___x_2422_);
v___x_2424_ = v___x_2366_;
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
lean_dec_ref(v_arg_2106_);
lean_dec_ref(v_arg_2094_);
lean_dec_ref(v_arg_2091_);
lean_dec_ref(v_origExpr_2065_);
v_a_2427_ = lean_ctor_get(v___x_2363_, 0);
v_isSharedCheck_2434_ = !lean_is_exclusive(v___x_2363_);
if (v_isSharedCheck_2434_ == 0)
{
v___x_2429_ = v___x_2363_;
v_isShared_2430_ = v_isSharedCheck_2434_;
goto v_resetjp_2428_;
}
else
{
lean_inc(v_a_2427_);
lean_dec(v___x_2363_);
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
}
else
{
lean_object* v___x_2435_; 
lean_dec_ref(v___x_2119_);
lean_del_object(v___x_2082_);
lean_inc_ref(v_origExpr_2065_);
v___x_2435_ = l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_bitVecAtom(v_origExpr_2065_, v___x_2121_, v_a_2067_, v_a_2068_, v_a_2069_, v_a_2070_, v_a_2071_);
if (lean_obj_tag(v___x_2435_) == 0)
{
lean_object* v_a_2436_; lean_object* v___x_2438_; uint8_t v_isShared_2439_; uint8_t v_isSharedCheck_2503_; 
v_a_2436_ = lean_ctor_get(v___x_2435_, 0);
v_isSharedCheck_2503_ = !lean_is_exclusive(v___x_2435_);
if (v_isSharedCheck_2503_ == 0)
{
v___x_2438_ = v___x_2435_;
v_isShared_2439_ = v_isSharedCheck_2503_;
goto v_resetjp_2437_;
}
else
{
lean_inc(v_a_2436_);
lean_dec(v___x_2435_);
v___x_2438_ = lean_box(0);
v_isShared_2439_ = v_isSharedCheck_2503_;
goto v_resetjp_2437_;
}
v_resetjp_2437_:
{
if (lean_obj_tag(v_a_2436_) == 1)
{
lean_object* v_val_2440_; lean_object* v___x_2441_; 
lean_del_object(v___x_2438_);
v_val_2440_ = lean_ctor_get(v_a_2436_, 0);
lean_inc_ref(v_arg_2106_);
v___x_2441_ = l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of(v_arg_2106_, v_a_2066_, v_a_2067_, v_a_2068_, v_a_2069_, v_a_2070_, v_a_2071_);
if (lean_obj_tag(v___x_2441_) == 0)
{
lean_object* v_a_2442_; lean_object* v___x_2444_; uint8_t v_isShared_2445_; uint8_t v_isSharedCheck_2490_; 
v_a_2442_ = lean_ctor_get(v___x_2441_, 0);
v_isSharedCheck_2490_ = !lean_is_exclusive(v___x_2441_);
if (v_isSharedCheck_2490_ == 0)
{
v___x_2444_ = v___x_2441_;
v_isShared_2445_ = v_isSharedCheck_2490_;
goto v_resetjp_2443_;
}
else
{
lean_inc(v_a_2442_);
lean_dec(v___x_2441_);
v___x_2444_ = lean_box(0);
v_isShared_2445_ = v_isSharedCheck_2490_;
goto v_resetjp_2443_;
}
v_resetjp_2443_:
{
if (lean_obj_tag(v_a_2442_) == 1)
{
lean_object* v_val_2446_; lean_object* v___x_2447_; 
lean_del_object(v___x_2444_);
v_val_2446_ = lean_ctor_get(v_a_2442_, 0);
lean_inc(v_val_2446_);
lean_dec_ref(v_a_2442_);
lean_inc_ref(v_arg_2094_);
v___x_2447_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_goOrAtom(v_arg_2094_, v_a_2066_, v_a_2067_, v_a_2068_, v_a_2069_, v_a_2070_, v_a_2071_);
if (lean_obj_tag(v___x_2447_) == 0)
{
lean_object* v_a_2448_; lean_object* v___x_2450_; uint8_t v_isShared_2451_; uint8_t v_isSharedCheck_2485_; 
v_a_2448_ = lean_ctor_get(v___x_2447_, 0);
v_isSharedCheck_2485_ = !lean_is_exclusive(v___x_2447_);
if (v_isSharedCheck_2485_ == 0)
{
v___x_2450_ = v___x_2447_;
v_isShared_2451_ = v_isSharedCheck_2485_;
goto v_resetjp_2449_;
}
else
{
lean_inc(v_a_2448_);
lean_dec(v___x_2447_);
v___x_2450_ = lean_box(0);
v_isShared_2451_ = v_isSharedCheck_2485_;
goto v_resetjp_2449_;
}
v_resetjp_2449_:
{
if (lean_obj_tag(v_a_2448_) == 1)
{
lean_object* v_val_2452_; lean_object* v___x_2453_; 
lean_del_object(v___x_2450_);
v_val_2452_ = lean_ctor_get(v_a_2448_, 0);
lean_inc(v_val_2452_);
lean_dec_ref(v_a_2448_);
lean_inc_ref(v_arg_2091_);
v___x_2453_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_goOrAtom(v_arg_2091_, v_a_2066_, v_a_2067_, v_a_2068_, v_a_2069_, v_a_2070_, v_a_2071_);
if (lean_obj_tag(v___x_2453_) == 0)
{
lean_object* v_a_2454_; lean_object* v___x_2456_; uint8_t v_isShared_2457_; uint8_t v_isSharedCheck_2480_; 
v_a_2454_ = lean_ctor_get(v___x_2453_, 0);
v_isSharedCheck_2480_ = !lean_is_exclusive(v___x_2453_);
if (v_isSharedCheck_2480_ == 0)
{
v___x_2456_ = v___x_2453_;
v_isShared_2457_ = v_isSharedCheck_2480_;
goto v_resetjp_2455_;
}
else
{
lean_inc(v_a_2454_);
lean_dec(v___x_2453_);
v___x_2456_ = lean_box(0);
v_isShared_2457_ = v_isSharedCheck_2480_;
goto v_resetjp_2455_;
}
v_resetjp_2455_:
{
if (lean_obj_tag(v_a_2454_) == 1)
{
lean_object* v_val_2458_; lean_object* v___x_2459_; 
lean_del_object(v___x_2456_);
v_val_2458_ = lean_ctor_get(v_a_2454_, 0);
lean_inc(v_val_2458_);
lean_dec_ref(v_a_2454_);
lean_inc(v_val_2440_);
v___x_2459_ = l_Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas___redArg(v_val_2446_, v_val_2440_, v_val_2452_, v_val_2458_, v_arg_2106_, v_origExpr_2065_, v_arg_2094_, v_arg_2091_, v_a_2066_, v_a_2068_, v_a_2069_, v_a_2070_, v_a_2071_);
if (lean_obj_tag(v___x_2459_) == 0)
{
lean_object* v___x_2461_; uint8_t v_isShared_2462_; uint8_t v_isSharedCheck_2466_; 
v_isSharedCheck_2466_ = !lean_is_exclusive(v___x_2459_);
if (v_isSharedCheck_2466_ == 0)
{
lean_object* v_unused_2467_; 
v_unused_2467_ = lean_ctor_get(v___x_2459_, 0);
lean_dec(v_unused_2467_);
v___x_2461_ = v___x_2459_;
v_isShared_2462_ = v_isSharedCheck_2466_;
goto v_resetjp_2460_;
}
else
{
lean_dec(v___x_2459_);
v___x_2461_ = lean_box(0);
v_isShared_2462_ = v_isSharedCheck_2466_;
goto v_resetjp_2460_;
}
v_resetjp_2460_:
{
lean_object* v___x_2464_; 
if (v_isShared_2462_ == 0)
{
lean_ctor_set(v___x_2461_, 0, v_a_2436_);
v___x_2464_ = v___x_2461_;
goto v_reusejp_2463_;
}
else
{
lean_object* v_reuseFailAlloc_2465_; 
v_reuseFailAlloc_2465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2465_, 0, v_a_2436_);
v___x_2464_ = v_reuseFailAlloc_2465_;
goto v_reusejp_2463_;
}
v_reusejp_2463_:
{
return v___x_2464_;
}
}
}
else
{
lean_object* v_a_2468_; lean_object* v___x_2470_; uint8_t v_isShared_2471_; uint8_t v_isSharedCheck_2475_; 
lean_dec_ref(v_a_2436_);
v_a_2468_ = lean_ctor_get(v___x_2459_, 0);
v_isSharedCheck_2475_ = !lean_is_exclusive(v___x_2459_);
if (v_isSharedCheck_2475_ == 0)
{
v___x_2470_ = v___x_2459_;
v_isShared_2471_ = v_isSharedCheck_2475_;
goto v_resetjp_2469_;
}
else
{
lean_inc(v_a_2468_);
lean_dec(v___x_2459_);
v___x_2470_ = lean_box(0);
v_isShared_2471_ = v_isSharedCheck_2475_;
goto v_resetjp_2469_;
}
v_resetjp_2469_:
{
lean_object* v___x_2473_; 
if (v_isShared_2471_ == 0)
{
v___x_2473_ = v___x_2470_;
goto v_reusejp_2472_;
}
else
{
lean_object* v_reuseFailAlloc_2474_; 
v_reuseFailAlloc_2474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2474_, 0, v_a_2468_);
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
else
{
lean_object* v___x_2476_; lean_object* v___x_2478_; 
lean_dec(v_a_2454_);
lean_dec(v_val_2452_);
lean_dec(v_val_2446_);
lean_dec_ref(v_a_2436_);
lean_dec_ref(v_arg_2106_);
lean_dec_ref(v_arg_2094_);
lean_dec_ref(v_arg_2091_);
lean_dec_ref(v_origExpr_2065_);
v___x_2476_ = lean_box(0);
if (v_isShared_2457_ == 0)
{
lean_ctor_set(v___x_2456_, 0, v___x_2476_);
v___x_2478_ = v___x_2456_;
goto v_reusejp_2477_;
}
else
{
lean_object* v_reuseFailAlloc_2479_; 
v_reuseFailAlloc_2479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2479_, 0, v___x_2476_);
v___x_2478_ = v_reuseFailAlloc_2479_;
goto v_reusejp_2477_;
}
v_reusejp_2477_:
{
return v___x_2478_;
}
}
}
}
else
{
lean_dec(v_val_2452_);
lean_dec(v_val_2446_);
lean_dec_ref(v_a_2436_);
lean_dec_ref(v_arg_2106_);
lean_dec_ref(v_arg_2094_);
lean_dec_ref(v_arg_2091_);
lean_dec_ref(v_origExpr_2065_);
return v___x_2453_;
}
}
else
{
lean_object* v___x_2481_; lean_object* v___x_2483_; 
lean_dec(v_a_2448_);
lean_dec(v_val_2446_);
lean_dec_ref(v_a_2436_);
lean_dec_ref(v_arg_2106_);
lean_dec_ref(v_arg_2094_);
lean_dec_ref(v_arg_2091_);
lean_dec_ref(v_origExpr_2065_);
v___x_2481_ = lean_box(0);
if (v_isShared_2451_ == 0)
{
lean_ctor_set(v___x_2450_, 0, v___x_2481_);
v___x_2483_ = v___x_2450_;
goto v_reusejp_2482_;
}
else
{
lean_object* v_reuseFailAlloc_2484_; 
v_reuseFailAlloc_2484_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2484_, 0, v___x_2481_);
v___x_2483_ = v_reuseFailAlloc_2484_;
goto v_reusejp_2482_;
}
v_reusejp_2482_:
{
return v___x_2483_;
}
}
}
}
else
{
lean_dec(v_val_2446_);
lean_dec_ref(v_a_2436_);
lean_dec_ref(v_arg_2106_);
lean_dec_ref(v_arg_2094_);
lean_dec_ref(v_arg_2091_);
lean_dec_ref(v_origExpr_2065_);
return v___x_2447_;
}
}
else
{
lean_object* v___x_2486_; lean_object* v___x_2488_; 
lean_dec(v_a_2442_);
lean_dec_ref(v_a_2436_);
lean_dec_ref(v_arg_2106_);
lean_dec_ref(v_arg_2094_);
lean_dec_ref(v_arg_2091_);
lean_dec_ref(v_origExpr_2065_);
v___x_2486_ = lean_box(0);
if (v_isShared_2445_ == 0)
{
lean_ctor_set(v___x_2444_, 0, v___x_2486_);
v___x_2488_ = v___x_2444_;
goto v_reusejp_2487_;
}
else
{
lean_object* v_reuseFailAlloc_2489_; 
v_reuseFailAlloc_2489_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2489_, 0, v___x_2486_);
v___x_2488_ = v_reuseFailAlloc_2489_;
goto v_reusejp_2487_;
}
v_reusejp_2487_:
{
return v___x_2488_;
}
}
}
}
else
{
lean_object* v_a_2491_; lean_object* v___x_2493_; uint8_t v_isShared_2494_; uint8_t v_isSharedCheck_2498_; 
lean_dec_ref(v_a_2436_);
lean_dec_ref(v_arg_2106_);
lean_dec_ref(v_arg_2094_);
lean_dec_ref(v_arg_2091_);
lean_dec_ref(v_origExpr_2065_);
v_a_2491_ = lean_ctor_get(v___x_2441_, 0);
v_isSharedCheck_2498_ = !lean_is_exclusive(v___x_2441_);
if (v_isSharedCheck_2498_ == 0)
{
v___x_2493_ = v___x_2441_;
v_isShared_2494_ = v_isSharedCheck_2498_;
goto v_resetjp_2492_;
}
else
{
lean_inc(v_a_2491_);
lean_dec(v___x_2441_);
v___x_2493_ = lean_box(0);
v_isShared_2494_ = v_isSharedCheck_2498_;
goto v_resetjp_2492_;
}
v_resetjp_2492_:
{
lean_object* v___x_2496_; 
if (v_isShared_2494_ == 0)
{
v___x_2496_ = v___x_2493_;
goto v_reusejp_2495_;
}
else
{
lean_object* v_reuseFailAlloc_2497_; 
v_reuseFailAlloc_2497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2497_, 0, v_a_2491_);
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
lean_object* v___x_2499_; lean_object* v___x_2501_; 
lean_dec(v_a_2436_);
lean_dec_ref(v_arg_2106_);
lean_dec_ref(v_arg_2094_);
lean_dec_ref(v_arg_2091_);
lean_dec_ref(v_origExpr_2065_);
v___x_2499_ = lean_box(0);
if (v_isShared_2439_ == 0)
{
lean_ctor_set(v___x_2438_, 0, v___x_2499_);
v___x_2501_ = v___x_2438_;
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
lean_dec_ref(v_arg_2106_);
lean_dec_ref(v_arg_2094_);
lean_dec_ref(v_arg_2091_);
lean_dec_ref(v_origExpr_2065_);
return v___x_2435_;
}
}
}
}
else
{
lean_object* v___x_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; 
lean_dec_ref(v___x_2107_);
lean_dec_ref(v_arg_2106_);
lean_dec_ref(v_arg_2094_);
lean_del_object(v___x_2082_);
v___x_2504_ = lean_box(0);
v___x_2505_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__81));
v___x_2506_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection(v_arg_2091_, v___x_2504_, v___x_2505_, v_origExpr_2065_, v_a_2066_, v_a_2067_, v_a_2068_, v_a_2069_, v_a_2070_, v_a_2071_);
return v___x_2506_;
}
}
else
{
lean_object* v___x_2507_; 
lean_dec_ref(v___x_2107_);
lean_dec_ref(v_arg_2106_);
lean_del_object(v___x_2082_);
v___x_2507_ = l_Lean_Meta_getNatValue_x3f(v_arg_2091_, v_a_2068_, v_a_2069_, v_a_2070_, v_a_2071_);
lean_dec_ref(v_arg_2091_);
if (lean_obj_tag(v___x_2507_) == 0)
{
lean_object* v_a_2508_; lean_object* v___x_2510_; uint8_t v_isShared_2511_; uint8_t v_isSharedCheck_2521_; 
v_a_2508_ = lean_ctor_get(v___x_2507_, 0);
v_isSharedCheck_2521_ = !lean_is_exclusive(v___x_2507_);
if (v_isSharedCheck_2521_ == 0)
{
v___x_2510_ = v___x_2507_;
v_isShared_2511_ = v_isSharedCheck_2521_;
goto v_resetjp_2509_;
}
else
{
lean_inc(v_a_2508_);
lean_dec(v___x_2507_);
v___x_2510_ = lean_box(0);
v_isShared_2511_ = v_isSharedCheck_2521_;
goto v_resetjp_2509_;
}
v_resetjp_2509_:
{
if (lean_obj_tag(v_a_2508_) == 1)
{
lean_object* v_val_2512_; lean_object* v___f_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; 
lean_del_object(v___x_2510_);
v_val_2512_ = lean_ctor_get(v_a_2508_, 0);
lean_inc(v_val_2512_);
lean_dec_ref(v_a_2508_);
v___f_2513_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__82));
v___x_2514_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__11));
v___x_2515_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__84));
v___x_2516_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection(v_val_2512_, v_arg_2094_, v___f_2513_, v___x_2514_, v___x_2515_, v_origExpr_2065_, v_a_2066_, v_a_2067_, v_a_2068_, v_a_2069_, v_a_2070_, v_a_2071_);
return v___x_2516_;
}
else
{
lean_object* v___x_2517_; lean_object* v___x_2519_; 
lean_dec(v_a_2508_);
lean_dec_ref(v_arg_2094_);
lean_dec_ref(v_origExpr_2065_);
v___x_2517_ = lean_box(0);
if (v_isShared_2511_ == 0)
{
lean_ctor_set(v___x_2510_, 0, v___x_2517_);
v___x_2519_ = v___x_2510_;
goto v_reusejp_2518_;
}
else
{
lean_object* v_reuseFailAlloc_2520_; 
v_reuseFailAlloc_2520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2520_, 0, v___x_2517_);
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
else
{
lean_object* v_a_2522_; lean_object* v___x_2524_; uint8_t v_isShared_2525_; uint8_t v_isSharedCheck_2529_; 
lean_dec_ref(v_arg_2094_);
lean_dec_ref(v_origExpr_2065_);
v_a_2522_ = lean_ctor_get(v___x_2507_, 0);
v_isSharedCheck_2529_ = !lean_is_exclusive(v___x_2507_);
if (v_isSharedCheck_2529_ == 0)
{
v___x_2524_ = v___x_2507_;
v_isShared_2525_ = v_isSharedCheck_2529_;
goto v_resetjp_2523_;
}
else
{
lean_inc(v_a_2522_);
lean_dec(v___x_2507_);
v___x_2524_ = lean_box(0);
v_isShared_2525_ = v_isSharedCheck_2529_;
goto v_resetjp_2523_;
}
v_resetjp_2523_:
{
lean_object* v___x_2527_; 
if (v_isShared_2525_ == 0)
{
v___x_2527_ = v___x_2524_;
goto v_reusejp_2526_;
}
else
{
lean_object* v_reuseFailAlloc_2528_; 
v_reuseFailAlloc_2528_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2528_, 0, v_a_2522_);
v___x_2527_ = v_reuseFailAlloc_2528_;
goto v_reusejp_2526_;
}
v_reusejp_2526_:
{
return v___x_2527_;
}
}
}
}
}
else
{
lean_object* v___x_2530_; 
lean_dec_ref(v___x_2107_);
lean_dec_ref(v_arg_2106_);
lean_del_object(v___x_2082_);
lean_inc_ref(v_arg_2091_);
v___x_2530_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_goOrAtom(v_arg_2091_, v_a_2066_, v_a_2067_, v_a_2068_, v_a_2069_, v_a_2070_, v_a_2071_);
if (lean_obj_tag(v___x_2530_) == 0)
{
lean_object* v_a_2531_; lean_object* v___x_2533_; uint8_t v_isShared_2534_; uint8_t v_isSharedCheck_2599_; 
v_a_2531_ = lean_ctor_get(v___x_2530_, 0);
v_isSharedCheck_2599_ = !lean_is_exclusive(v___x_2530_);
if (v_isSharedCheck_2599_ == 0)
{
v___x_2533_ = v___x_2530_;
v_isShared_2534_ = v_isSharedCheck_2599_;
goto v_resetjp_2532_;
}
else
{
lean_inc(v_a_2531_);
lean_dec(v___x_2530_);
v___x_2533_ = lean_box(0);
v_isShared_2534_ = v_isSharedCheck_2599_;
goto v_resetjp_2532_;
}
v_resetjp_2532_:
{
if (lean_obj_tag(v_a_2531_) == 1)
{
lean_object* v_val_2535_; lean_object* v___x_2536_; 
lean_del_object(v___x_2533_);
v_val_2535_ = lean_ctor_get(v_a_2531_, 0);
lean_inc(v_val_2535_);
lean_dec_ref(v_a_2531_);
v___x_2536_ = l_Lean_Meta_getNatValue_x3f(v_arg_2094_, v_a_2068_, v_a_2069_, v_a_2070_, v_a_2071_);
lean_dec_ref(v_arg_2094_);
if (lean_obj_tag(v___x_2536_) == 0)
{
lean_object* v_a_2537_; lean_object* v___x_2539_; uint8_t v_isShared_2540_; uint8_t v_isSharedCheck_2586_; 
v_a_2537_ = lean_ctor_get(v___x_2536_, 0);
v_isSharedCheck_2586_ = !lean_is_exclusive(v___x_2536_);
if (v_isSharedCheck_2586_ == 0)
{
v___x_2539_ = v___x_2536_;
v_isShared_2540_ = v_isSharedCheck_2586_;
goto v_resetjp_2538_;
}
else
{
lean_inc(v_a_2537_);
lean_dec(v___x_2536_);
v___x_2539_ = lean_box(0);
v_isShared_2540_ = v_isSharedCheck_2586_;
goto v_resetjp_2538_;
}
v_resetjp_2538_:
{
if (lean_obj_tag(v_a_2537_) == 1)
{
lean_object* v_val_2541_; lean_object* v___x_2543_; uint8_t v_isShared_2544_; uint8_t v_isSharedCheck_2581_; 
lean_del_object(v___x_2539_);
v_val_2541_ = lean_ctor_get(v_a_2537_, 0);
v_isSharedCheck_2581_ = !lean_is_exclusive(v_a_2537_);
if (v_isSharedCheck_2581_ == 0)
{
v___x_2543_ = v_a_2537_;
v_isShared_2544_ = v_isSharedCheck_2581_;
goto v_resetjp_2542_;
}
else
{
lean_inc(v_val_2541_);
lean_dec(v_a_2537_);
v___x_2543_ = lean_box(0);
v_isShared_2544_ = v_isSharedCheck_2581_;
goto v_resetjp_2542_;
}
v_resetjp_2542_:
{
lean_object* v_width_2545_; lean_object* v_bvExpr_2546_; lean_object* v_expr_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; 
v_width_2545_ = lean_ctor_get(v_val_2535_, 0);
lean_inc(v_width_2545_);
v_bvExpr_2546_ = lean_ctor_get(v_val_2535_, 1);
v_expr_2547_ = lean_ctor_get(v_val_2535_, 4);
lean_inc_ref(v_expr_2547_);
v___x_2548_ = lean_nat_mul(v_width_2545_, v_val_2541_);
lean_inc_ref(v_bvExpr_2546_);
lean_inc(v_val_2541_);
lean_inc(v___x_2548_);
lean_inc(v_width_2545_);
v___x_2549_ = l_Std_Tactic_BVDecide_BVExpr_replicate___override___redArg(v_width_2545_, v___x_2548_, v_val_2541_, v_bvExpr_2546_);
lean_inc(v___x_2548_);
v___x_2550_ = l_Lean_mkNatLit(v___x_2548_);
lean_inc_ref(v___x_2550_);
v___x_2551_ = l_Lean_Meta_mkEqRefl(v___x_2550_, v_a_2068_, v_a_2069_, v_a_2070_, v_a_2071_);
if (lean_obj_tag(v___x_2551_) == 0)
{
lean_object* v_a_2552_; lean_object* v___x_2554_; uint8_t v_isShared_2555_; uint8_t v_isSharedCheck_2572_; 
v_a_2552_ = lean_ctor_get(v___x_2551_, 0);
v_isSharedCheck_2572_ = !lean_is_exclusive(v___x_2551_);
if (v_isSharedCheck_2572_ == 0)
{
v___x_2554_ = v___x_2551_;
v_isShared_2555_ = v_isSharedCheck_2572_;
goto v_resetjp_2553_;
}
else
{
lean_inc(v_a_2552_);
lean_dec(v___x_2551_);
v___x_2554_ = lean_box(0);
v_isShared_2555_ = v_isSharedCheck_2572_;
goto v_resetjp_2553_;
}
v_resetjp_2553_:
{
lean_object* v___x_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; lean_object* v___f_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2567_; 
v___x_2556_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0));
v___x_2557_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1));
v___x_2558_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2));
v___x_2559_ = lean_box(0);
v___x_2560_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__86, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__86_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__86);
lean_inc(v_width_2545_);
v___x_2561_ = l_Lean_mkNatLit(v_width_2545_);
v___x_2562_ = l_Lean_mkNatLit(v_val_2541_);
lean_inc_ref(v___x_2561_);
lean_inc_ref(v___x_2562_);
lean_inc_ref(v_expr_2547_);
v___f_2563_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___lam__3___boxed), 17, 11);
lean_closure_set(v___f_2563_, 0, v_width_2545_);
lean_closure_set(v___f_2563_, 1, v_expr_2547_);
lean_closure_set(v___f_2563_, 2, v_val_2535_);
lean_closure_set(v___f_2563_, 3, v___x_2556_);
lean_closure_set(v___f_2563_, 4, v___x_2557_);
lean_closure_set(v___f_2563_, 5, v___x_2558_);
lean_closure_set(v___f_2563_, 6, v___x_2096_);
lean_closure_set(v___f_2563_, 7, v___x_2559_);
lean_closure_set(v___f_2563_, 8, v___x_2562_);
lean_closure_set(v___f_2563_, 9, v___x_2561_);
lean_closure_set(v___f_2563_, 10, v_arg_2091_);
v___x_2564_ = l_Lean_mkApp5(v___x_2560_, v___x_2561_, v___x_2550_, v___x_2562_, v_expr_2547_, v_a_2552_);
v___x_2565_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2565_, 0, v___x_2548_);
lean_ctor_set(v___x_2565_, 1, v___x_2549_);
lean_ctor_set(v___x_2565_, 2, v_origExpr_2065_);
lean_ctor_set(v___x_2565_, 3, v___f_2563_);
lean_ctor_set(v___x_2565_, 4, v___x_2564_);
if (v_isShared_2544_ == 0)
{
lean_ctor_set(v___x_2543_, 0, v___x_2565_);
v___x_2567_ = v___x_2543_;
goto v_reusejp_2566_;
}
else
{
lean_object* v_reuseFailAlloc_2571_; 
v_reuseFailAlloc_2571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2571_, 0, v___x_2565_);
v___x_2567_ = v_reuseFailAlloc_2571_;
goto v_reusejp_2566_;
}
v_reusejp_2566_:
{
lean_object* v___x_2569_; 
if (v_isShared_2555_ == 0)
{
lean_ctor_set(v___x_2554_, 0, v___x_2567_);
v___x_2569_ = v___x_2554_;
goto v_reusejp_2568_;
}
else
{
lean_object* v_reuseFailAlloc_2570_; 
v_reuseFailAlloc_2570_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2570_, 0, v___x_2567_);
v___x_2569_ = v_reuseFailAlloc_2570_;
goto v_reusejp_2568_;
}
v_reusejp_2568_:
{
return v___x_2569_;
}
}
}
}
else
{
lean_object* v_a_2573_; lean_object* v___x_2575_; uint8_t v_isShared_2576_; uint8_t v_isSharedCheck_2580_; 
lean_dec_ref(v___x_2550_);
lean_dec_ref(v___x_2549_);
lean_dec(v___x_2548_);
lean_dec_ref(v_expr_2547_);
lean_dec(v_width_2545_);
lean_del_object(v___x_2543_);
lean_dec(v_val_2541_);
lean_dec(v_val_2535_);
lean_dec_ref(v_arg_2091_);
lean_dec_ref(v_origExpr_2065_);
v_a_2573_ = lean_ctor_get(v___x_2551_, 0);
v_isSharedCheck_2580_ = !lean_is_exclusive(v___x_2551_);
if (v_isSharedCheck_2580_ == 0)
{
v___x_2575_ = v___x_2551_;
v_isShared_2576_ = v_isSharedCheck_2580_;
goto v_resetjp_2574_;
}
else
{
lean_inc(v_a_2573_);
lean_dec(v___x_2551_);
v___x_2575_ = lean_box(0);
v_isShared_2576_ = v_isSharedCheck_2580_;
goto v_resetjp_2574_;
}
v_resetjp_2574_:
{
lean_object* v___x_2578_; 
if (v_isShared_2576_ == 0)
{
v___x_2578_ = v___x_2575_;
goto v_reusejp_2577_;
}
else
{
lean_object* v_reuseFailAlloc_2579_; 
v_reuseFailAlloc_2579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2579_, 0, v_a_2573_);
v___x_2578_ = v_reuseFailAlloc_2579_;
goto v_reusejp_2577_;
}
v_reusejp_2577_:
{
return v___x_2578_;
}
}
}
}
}
else
{
lean_object* v___x_2582_; lean_object* v___x_2584_; 
lean_dec(v_a_2537_);
lean_dec(v_val_2535_);
lean_dec_ref(v_arg_2091_);
lean_dec_ref(v_origExpr_2065_);
v___x_2582_ = lean_box(0);
if (v_isShared_2540_ == 0)
{
lean_ctor_set(v___x_2539_, 0, v___x_2582_);
v___x_2584_ = v___x_2539_;
goto v_reusejp_2583_;
}
else
{
lean_object* v_reuseFailAlloc_2585_; 
v_reuseFailAlloc_2585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2585_, 0, v___x_2582_);
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
else
{
lean_object* v_a_2587_; lean_object* v___x_2589_; uint8_t v_isShared_2590_; uint8_t v_isSharedCheck_2594_; 
lean_dec(v_val_2535_);
lean_dec_ref(v_arg_2091_);
lean_dec_ref(v_origExpr_2065_);
v_a_2587_ = lean_ctor_get(v___x_2536_, 0);
v_isSharedCheck_2594_ = !lean_is_exclusive(v___x_2536_);
if (v_isSharedCheck_2594_ == 0)
{
v___x_2589_ = v___x_2536_;
v_isShared_2590_ = v_isSharedCheck_2594_;
goto v_resetjp_2588_;
}
else
{
lean_inc(v_a_2587_);
lean_dec(v___x_2536_);
v___x_2589_ = lean_box(0);
v_isShared_2590_ = v_isSharedCheck_2594_;
goto v_resetjp_2588_;
}
v_resetjp_2588_:
{
lean_object* v___x_2592_; 
if (v_isShared_2590_ == 0)
{
v___x_2592_ = v___x_2589_;
goto v_reusejp_2591_;
}
else
{
lean_object* v_reuseFailAlloc_2593_; 
v_reuseFailAlloc_2593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2593_, 0, v_a_2587_);
v___x_2592_ = v_reuseFailAlloc_2593_;
goto v_reusejp_2591_;
}
v_reusejp_2591_:
{
return v___x_2592_;
}
}
}
}
else
{
lean_object* v___x_2595_; lean_object* v___x_2597_; 
lean_dec(v_a_2531_);
lean_dec_ref(v_arg_2094_);
lean_dec_ref(v_arg_2091_);
lean_dec_ref(v_origExpr_2065_);
v___x_2595_ = lean_box(0);
if (v_isShared_2534_ == 0)
{
lean_ctor_set(v___x_2533_, 0, v___x_2595_);
v___x_2597_ = v___x_2533_;
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
lean_dec_ref(v_arg_2094_);
lean_dec_ref(v_arg_2091_);
lean_dec_ref(v_origExpr_2065_);
return v___x_2530_;
}
}
}
else
{
lean_object* v___f_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; 
lean_dec_ref(v___x_2107_);
lean_dec_ref(v_arg_2106_);
lean_del_object(v___x_2082_);
v___f_2600_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__87));
v___x_2601_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__5));
v___x_2602_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__89));
v___x_2603_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_rotateReflection(v_arg_2091_, v_arg_2094_, v___f_2600_, v___x_2601_, v___x_2602_, v_origExpr_2065_, v_a_2066_, v_a_2067_, v_a_2068_, v_a_2069_, v_a_2070_, v_a_2071_);
lean_dec_ref(v_arg_2091_);
return v___x_2603_;
}
}
else
{
lean_object* v___f_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; 
lean_dec_ref(v___x_2107_);
lean_dec_ref(v_arg_2106_);
lean_del_object(v___x_2082_);
v___f_2604_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__90));
v___x_2605_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__8));
v___x_2606_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__92));
v___x_2607_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_rotateReflection(v_arg_2091_, v_arg_2094_, v___f_2604_, v___x_2605_, v___x_2606_, v_origExpr_2065_, v_a_2066_, v_a_2067_, v_a_2068_, v_a_2069_, v_a_2070_, v_a_2071_);
lean_dec_ref(v_arg_2091_);
return v___x_2607_;
}
}
}
else
{
lean_object* v___x_2608_; 
lean_dec_ref(v___x_2095_);
lean_dec_ref(v_arg_2094_);
lean_dec_ref(v_arg_2091_);
lean_del_object(v___x_2082_);
v___x_2608_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_goBvLit(v_origExpr_2065_, v_a_2067_, v_a_2068_, v_a_2069_, v_a_2070_, v_a_2071_);
return v___x_2608_;
}
}
else
{
lean_object* v___x_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; 
lean_dec_ref(v___x_2095_);
lean_dec_ref(v_arg_2094_);
lean_del_object(v___x_2082_);
v___x_2609_ = lean_box(4);
v___x_2610_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__94));
v___x_2611_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection(v_arg_2091_, v___x_2609_, v___x_2610_, v_origExpr_2065_, v_a_2066_, v_a_2067_, v_a_2068_, v_a_2069_, v_a_2070_, v_a_2071_);
return v___x_2611_;
}
}
else
{
lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; 
lean_dec_ref(v___x_2095_);
lean_dec_ref(v_arg_2094_);
lean_del_object(v___x_2082_);
v___x_2612_ = lean_box(5);
v___x_2613_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__96));
v___x_2614_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection(v_arg_2091_, v___x_2612_, v___x_2613_, v_origExpr_2065_, v_a_2066_, v_a_2067_, v_a_2068_, v_a_2069_, v_a_2070_, v_a_2071_);
return v___x_2614_;
}
}
else
{
lean_object* v___x_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; 
lean_dec_ref(v___x_2095_);
lean_dec_ref(v_arg_2094_);
lean_del_object(v___x_2082_);
v___x_2615_ = lean_box(6);
v___x_2616_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__98));
v___x_2617_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection(v_arg_2091_, v___x_2615_, v___x_2616_, v_origExpr_2065_, v_a_2066_, v_a_2067_, v_a_2068_, v_a_2069_, v_a_2070_, v_a_2071_);
return v___x_2617_;
}
}
}
v___jp_2084_:
{
lean_object* v___x_2085_; lean_object* v___x_2087_; 
v___x_2085_ = lean_box(0);
if (v_isShared_2083_ == 0)
{
lean_ctor_set(v___x_2082_, 0, v___x_2085_);
v___x_2087_ = v___x_2082_;
goto v_reusejp_2086_;
}
else
{
lean_object* v_reuseFailAlloc_2088_; 
v_reuseFailAlloc_2088_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2088_, 0, v___x_2085_);
v___x_2087_ = v_reuseFailAlloc_2088_;
goto v_reusejp_2086_;
}
v_reusejp_2086_:
{
return v___x_2087_;
}
}
}
}
else
{
lean_object* v_a_2619_; lean_object* v___x_2621_; uint8_t v_isShared_2622_; uint8_t v_isSharedCheck_2626_; 
lean_dec_ref(v_origExpr_2065_);
v_a_2619_ = lean_ctor_get(v___x_2079_, 0);
v_isSharedCheck_2626_ = !lean_is_exclusive(v___x_2079_);
if (v_isSharedCheck_2626_ == 0)
{
v___x_2621_ = v___x_2079_;
v_isShared_2622_ = v_isSharedCheck_2626_;
goto v_resetjp_2620_;
}
else
{
lean_inc(v_a_2619_);
lean_dec(v___x_2079_);
v___x_2621_ = lean_box(0);
v_isShared_2622_ = v_isSharedCheck_2626_;
goto v_resetjp_2620_;
}
v_resetjp_2620_:
{
lean_object* v___x_2624_; 
if (v_isShared_2622_ == 0)
{
v___x_2624_ = v___x_2621_;
goto v_reusejp_2623_;
}
else
{
lean_object* v_reuseFailAlloc_2625_; 
v_reuseFailAlloc_2625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2625_, 0, v_a_2619_);
v___x_2624_ = v_reuseFailAlloc_2625_;
goto v_reusejp_2623_;
}
v_reusejp_2623_:
{
return v___x_2624_;
}
}
}
v___jp_2073_:
{
lean_object* v___x_2074_; lean_object* v___x_2075_; 
v___x_2074_ = lean_box(0);
v___x_2075_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2075_, 0, v___x_2074_);
return v___x_2075_;
}
v___jp_2076_:
{
lean_object* v___x_2077_; lean_object* v___x_2078_; 
v___x_2077_ = lean_box(0);
v___x_2078_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2078_, 0, v___x_2077_);
return v___x_2078_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVExprCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_goOrAtom_spec__10(lean_object* v_e_2627_, lean_object* v_a_2628_, lean_object* v_a_2629_, lean_object* v_a_2630_, lean_object* v_a_2631_, lean_object* v_a_2632_, lean_object* v_a_2633_){
_start:
{
lean_object* v___y_2636_; lean_object* v___x_2659_; lean_object* v_bvExprCache_2660_; lean_object* v___x_2661_; 
v___x_2659_ = lean_st_ref_get(v_a_2628_);
v_bvExprCache_2660_ = lean_ctor_get(v___x_2659_, 1);
lean_inc_ref(v_bvExprCache_2660_);
lean_dec(v___x_2659_);
v___x_2661_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom_spec__2_spec__12___redArg(v_bvExprCache_2660_, v_e_2627_);
lean_dec_ref(v_bvExprCache_2660_);
if (lean_obj_tag(v___x_2661_) == 0)
{
lean_object* v___x_2662_; 
lean_inc_ref(v_e_2627_);
v___x_2662_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go(v_e_2627_, v_a_2628_, v_a_2629_, v_a_2630_, v_a_2631_, v_a_2632_, v_a_2633_);
if (lean_obj_tag(v___x_2662_) == 0)
{
lean_object* v_a_2663_; 
v_a_2663_ = lean_ctor_get(v___x_2662_, 0);
lean_inc(v_a_2663_);
if (lean_obj_tag(v_a_2663_) == 0)
{
uint8_t v___x_2664_; lean_object* v___x_2665_; 
lean_dec_ref(v___x_2662_);
v___x_2664_ = 0;
lean_inc_ref(v_e_2627_);
v___x_2665_ = l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_bitVecAtom(v_e_2627_, v___x_2664_, v_a_2629_, v_a_2630_, v_a_2631_, v_a_2632_, v_a_2633_);
v___y_2636_ = v___x_2665_;
goto v___jp_2635_;
}
else
{
lean_dec_ref(v_a_2663_);
v___y_2636_ = v___x_2662_;
goto v___jp_2635_;
}
}
else
{
v___y_2636_ = v___x_2662_;
goto v___jp_2635_;
}
}
else
{
lean_object* v_val_2666_; lean_object* v___x_2668_; uint8_t v_isShared_2669_; uint8_t v_isSharedCheck_2673_; 
lean_dec_ref(v_e_2627_);
v_val_2666_ = lean_ctor_get(v___x_2661_, 0);
v_isSharedCheck_2673_ = !lean_is_exclusive(v___x_2661_);
if (v_isSharedCheck_2673_ == 0)
{
v___x_2668_ = v___x_2661_;
v_isShared_2669_ = v_isSharedCheck_2673_;
goto v_resetjp_2667_;
}
else
{
lean_inc(v_val_2666_);
lean_dec(v___x_2661_);
v___x_2668_ = lean_box(0);
v_isShared_2669_ = v_isSharedCheck_2673_;
goto v_resetjp_2667_;
}
v_resetjp_2667_:
{
lean_object* v___x_2671_; 
if (v_isShared_2669_ == 0)
{
lean_ctor_set_tag(v___x_2668_, 0);
v___x_2671_ = v___x_2668_;
goto v_reusejp_2670_;
}
else
{
lean_object* v_reuseFailAlloc_2672_; 
v_reuseFailAlloc_2672_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2672_, 0, v_val_2666_);
v___x_2671_ = v_reuseFailAlloc_2672_;
goto v_reusejp_2670_;
}
v_reusejp_2670_:
{
return v___x_2671_;
}
}
}
v___jp_2635_:
{
if (lean_obj_tag(v___y_2636_) == 0)
{
lean_object* v_a_2637_; lean_object* v___x_2639_; uint8_t v_isShared_2640_; uint8_t v_isSharedCheck_2658_; 
v_a_2637_ = lean_ctor_get(v___y_2636_, 0);
v_isSharedCheck_2658_ = !lean_is_exclusive(v___y_2636_);
if (v_isSharedCheck_2658_ == 0)
{
v___x_2639_ = v___y_2636_;
v_isShared_2640_ = v_isSharedCheck_2658_;
goto v_resetjp_2638_;
}
else
{
lean_inc(v_a_2637_);
lean_dec(v___y_2636_);
v___x_2639_ = lean_box(0);
v_isShared_2640_ = v_isSharedCheck_2658_;
goto v_resetjp_2638_;
}
v_resetjp_2638_:
{
lean_object* v___x_2641_; lean_object* v_lemmas_2642_; lean_object* v_bvExprCache_2643_; lean_object* v_bvPredCache_2644_; lean_object* v_bvLogicalCache_2645_; lean_object* v___x_2647_; uint8_t v_isShared_2648_; uint8_t v_isSharedCheck_2657_; 
v___x_2641_ = lean_st_ref_take(v_a_2628_);
v_lemmas_2642_ = lean_ctor_get(v___x_2641_, 0);
v_bvExprCache_2643_ = lean_ctor_get(v___x_2641_, 1);
v_bvPredCache_2644_ = lean_ctor_get(v___x_2641_, 2);
v_bvLogicalCache_2645_ = lean_ctor_get(v___x_2641_, 3);
v_isSharedCheck_2657_ = !lean_is_exclusive(v___x_2641_);
if (v_isSharedCheck_2657_ == 0)
{
v___x_2647_ = v___x_2641_;
v_isShared_2648_ = v_isSharedCheck_2657_;
goto v_resetjp_2646_;
}
else
{
lean_inc(v_bvLogicalCache_2645_);
lean_inc(v_bvPredCache_2644_);
lean_inc(v_bvExprCache_2643_);
lean_inc(v_lemmas_2642_);
lean_dec(v___x_2641_);
v___x_2647_ = lean_box(0);
v_isShared_2648_ = v_isSharedCheck_2657_;
goto v_resetjp_2646_;
}
v_resetjp_2646_:
{
lean_object* v___x_2649_; lean_object* v___x_2651_; 
lean_inc(v_a_2637_);
v___x_2649_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13___redArg(v_bvExprCache_2643_, v_e_2627_, v_a_2637_);
if (v_isShared_2648_ == 0)
{
lean_ctor_set(v___x_2647_, 1, v___x_2649_);
v___x_2651_ = v___x_2647_;
goto v_reusejp_2650_;
}
else
{
lean_object* v_reuseFailAlloc_2656_; 
v_reuseFailAlloc_2656_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2656_, 0, v_lemmas_2642_);
lean_ctor_set(v_reuseFailAlloc_2656_, 1, v___x_2649_);
lean_ctor_set(v_reuseFailAlloc_2656_, 2, v_bvPredCache_2644_);
lean_ctor_set(v_reuseFailAlloc_2656_, 3, v_bvLogicalCache_2645_);
v___x_2651_ = v_reuseFailAlloc_2656_;
goto v_reusejp_2650_;
}
v_reusejp_2650_:
{
lean_object* v___x_2652_; lean_object* v___x_2654_; 
v___x_2652_ = lean_st_ref_set(v_a_2628_, v___x_2651_);
if (v_isShared_2640_ == 0)
{
v___x_2654_ = v___x_2639_;
goto v_reusejp_2653_;
}
else
{
lean_object* v_reuseFailAlloc_2655_; 
v_reuseFailAlloc_2655_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2655_, 0, v_a_2637_);
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
}
else
{
lean_dec_ref(v_e_2627_);
return v___y_2636_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_goOrAtom(lean_object* v_origExpr_2674_, lean_object* v_a_2675_, lean_object* v_a_2676_, lean_object* v_a_2677_, lean_object* v_a_2678_, lean_object* v_a_2679_, lean_object* v_a_2680_){
_start:
{
lean_object* v___x_2682_; 
v___x_2682_ = l_Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVExprCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_goOrAtom_spec__10(v_origExpr_2674_, v_a_2675_, v_a_2676_, v_a_2677_, v_a_2678_, v_a_2679_, v_a_2680_);
return v___x_2682_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of(lean_object* v_origExpr_2683_, lean_object* v_a_2684_, lean_object* v_a_2685_, lean_object* v_a_2686_, lean_object* v_a_2687_, lean_object* v_a_2688_, lean_object* v_a_2689_){
_start:
{
lean_object* v___x_2691_; 
v___x_2691_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_goOrAtom(v_origExpr_2683_, v_a_2684_, v_a_2685_, v_a_2686_, v_a_2687_, v_a_2688_, v_a_2689_);
return v___x_2691_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of___boxed(lean_object* v_origExpr_2692_, lean_object* v_a_2693_, lean_object* v_a_2694_, lean_object* v_a_2695_, lean_object* v_a_2696_, lean_object* v_a_2697_, lean_object* v_a_2698_, lean_object* v_a_2699_){
_start:
{
lean_object* v_res_2700_; 
v_res_2700_ = l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of(v_origExpr_2692_, v_a_2693_, v_a_2694_, v_a_2695_, v_a_2696_, v_a_2697_, v_a_2698_);
lean_dec(v_a_2698_);
lean_dec_ref(v_a_2697_);
lean_dec(v_a_2696_);
lean_dec_ref(v_a_2695_);
lean_dec(v_a_2694_);
lean_dec(v_a_2693_);
return v_res_2700_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of___boxed(lean_object* v_origExpr_2701_, lean_object* v_a_2702_, lean_object* v_a_2703_, lean_object* v_a_2704_, lean_object* v_a_2705_, lean_object* v_a_2706_, lean_object* v_a_2707_, lean_object* v_a_2708_){
_start:
{
lean_object* v_res_2709_; 
v_res_2709_ = l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of(v_origExpr_2701_, v_a_2702_, v_a_2703_, v_a_2704_, v_a_2705_, v_a_2706_, v_a_2707_);
lean_dec(v_a_2707_);
lean_dec_ref(v_a_2706_);
lean_dec(v_a_2705_);
lean_dec_ref(v_a_2704_);
lean_dec(v_a_2703_);
lean_dec(v_a_2702_);
return v_res_2709_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_of___boxed(lean_object* v_origExpr_2710_, lean_object* v_a_2711_, lean_object* v_a_2712_, lean_object* v_a_2713_, lean_object* v_a_2714_, lean_object* v_a_2715_, lean_object* v_a_2716_, lean_object* v_a_2717_){
_start:
{
lean_object* v_res_2718_; 
v_res_2718_ = l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_of(v_origExpr_2710_, v_a_2711_, v_a_2712_, v_a_2713_, v_a_2714_, v_a_2715_, v_a_2716_);
lean_dec(v_a_2716_);
lean_dec_ref(v_a_2715_);
lean_dec(v_a_2714_);
lean_dec_ref(v_a_2713_);
lean_dec(v_a_2712_);
lean_dec(v_a_2711_);
return v_res_2718_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_goOrAtom___boxed(lean_object* v_origExpr_2719_, lean_object* v_a_2720_, lean_object* v_a_2721_, lean_object* v_a_2722_, lean_object* v_a_2723_, lean_object* v_a_2724_, lean_object* v_a_2725_, lean_object* v_a_2726_){
_start:
{
lean_object* v_res_2727_; 
v_res_2727_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_goOrAtom(v_origExpr_2719_, v_a_2720_, v_a_2721_, v_a_2722_, v_a_2723_, v_a_2724_, v_a_2725_);
lean_dec(v_a_2725_);
lean_dec_ref(v_a_2724_);
lean_dec(v_a_2723_);
lean_dec_ref(v_a_2722_);
lean_dec(v_a_2721_);
lean_dec(v_a_2720_);
return v_res_2727_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom___boxed(lean_object* v_origExpr_2728_, lean_object* v_a_2729_, lean_object* v_a_2730_, lean_object* v_a_2731_, lean_object* v_a_2732_, lean_object* v_a_2733_, lean_object* v_a_2734_, lean_object* v_a_2735_){
_start:
{
lean_object* v_res_2736_; 
v_res_2736_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom(v_origExpr_2728_, v_a_2729_, v_a_2730_, v_a_2731_, v_a_2732_, v_a_2733_, v_a_2734_);
lean_dec(v_a_2734_);
lean_dec_ref(v_a_2733_);
lean_dec(v_a_2732_);
lean_dec_ref(v_a_2731_);
lean_dec(v_a_2730_);
lean_dec(v_a_2729_);
return v_res_2736_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_rotateReflection___boxed(lean_object* v_distanceExpr_2737_, lean_object* v_innerExpr_2738_, lean_object* v_rotateOp_2739_, lean_object* v_rotateOpName_2740_, lean_object* v_congrThm_2741_, lean_object* v_origExpr_2742_, lean_object* v_a_2743_, lean_object* v_a_2744_, lean_object* v_a_2745_, lean_object* v_a_2746_, lean_object* v_a_2747_, lean_object* v_a_2748_, lean_object* v_a_2749_){
_start:
{
lean_object* v_res_2750_; 
v_res_2750_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_rotateReflection(v_distanceExpr_2737_, v_innerExpr_2738_, v_rotateOp_2739_, v_rotateOpName_2740_, v_congrThm_2741_, v_origExpr_2742_, v_a_2743_, v_a_2744_, v_a_2745_, v_a_2746_, v_a_2747_, v_a_2748_);
lean_dec(v_a_2748_);
lean_dec_ref(v_a_2747_);
lean_dec(v_a_2746_);
lean_dec_ref(v_a_2745_);
lean_dec(v_a_2744_);
lean_dec(v_a_2743_);
lean_dec_ref(v_distanceExpr_2737_);
return v_res_2750_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goPred___boxed(lean_object* v_origExpr_2751_, lean_object* v_a_2752_, lean_object* v_a_2753_, lean_object* v_a_2754_, lean_object* v_a_2755_, lean_object* v_a_2756_, lean_object* v_a_2757_, lean_object* v_a_2758_){
_start:
{
lean_object* v_res_2759_; 
v_res_2759_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goPred(v_origExpr_2751_, v_a_2752_, v_a_2753_, v_a_2754_, v_a_2755_, v_a_2756_, v_a_2757_);
lean_dec(v_a_2757_);
lean_dec_ref(v_a_2756_);
lean_dec(v_a_2755_);
lean_dec_ref(v_a_2754_);
lean_dec(v_a_2753_);
lean_dec(v_a_2752_);
return v_res_2759_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_of_binaryReflection___boxed(lean_object* v_lhsExpr_2760_, lean_object* v_rhsExpr_2761_, lean_object* v_pred_2762_, lean_object* v_origExpr_2763_, lean_object* v_a_2764_, lean_object* v_a_2765_, lean_object* v_a_2766_, lean_object* v_a_2767_, lean_object* v_a_2768_, lean_object* v_a_2769_, lean_object* v_a_2770_){
_start:
{
uint8_t v_pred_boxed_2771_; lean_object* v_res_2772_; 
v_pred_boxed_2771_ = lean_unbox(v_pred_2762_);
v_res_2772_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_of_binaryReflection(v_lhsExpr_2760_, v_rhsExpr_2761_, v_pred_boxed_2771_, v_origExpr_2763_, v_a_2764_, v_a_2765_, v_a_2766_, v_a_2767_, v_a_2768_, v_a_2769_);
lean_dec(v_a_2769_);
lean_dec_ref(v_a_2768_);
lean_dec(v_a_2767_);
lean_dec_ref(v_a_2766_);
lean_dec(v_a_2765_);
lean_dec(v_a_2764_);
return v_res_2772_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_gateReflection___boxed(lean_object* v_lhsExpr_2773_, lean_object* v_rhsExpr_2774_, lean_object* v_gate_2775_, lean_object* v_origExpr_2776_, lean_object* v_a_2777_, lean_object* v_a_2778_, lean_object* v_a_2779_, lean_object* v_a_2780_, lean_object* v_a_2781_, lean_object* v_a_2782_, lean_object* v_a_2783_){
_start:
{
uint8_t v_gate_boxed_2784_; lean_object* v_res_2785_; 
v_gate_boxed_2784_ = lean_unbox(v_gate_2775_);
v_res_2785_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_gateReflection(v_lhsExpr_2773_, v_rhsExpr_2774_, v_gate_boxed_2784_, v_origExpr_2776_, v_a_2777_, v_a_2778_, v_a_2779_, v_a_2780_, v_a_2781_, v_a_2782_);
lean_dec(v_a_2782_);
lean_dec_ref(v_a_2781_);
lean_dec(v_a_2780_);
lean_dec_ref(v_a_2779_);
lean_dec(v_a_2778_);
lean_dec(v_a_2777_);
return v_res_2785_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___boxed(lean_object* v_distance_2786_, lean_object* v_innerExpr_2787_, lean_object* v_shiftOp_2788_, lean_object* v_shiftOpName_2789_, lean_object* v_congrThm_2790_, lean_object* v_origExpr_2791_, lean_object* v_a_2792_, lean_object* v_a_2793_, lean_object* v_a_2794_, lean_object* v_a_2795_, lean_object* v_a_2796_, lean_object* v_a_2797_, lean_object* v_a_2798_){
_start:
{
lean_object* v_res_2799_; 
v_res_2799_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection(v_distance_2786_, v_innerExpr_2787_, v_shiftOp_2788_, v_shiftOpName_2789_, v_congrThm_2790_, v_origExpr_2791_, v_a_2792_, v_a_2793_, v_a_2794_, v_a_2795_, v_a_2796_, v_a_2797_);
lean_dec(v_a_2797_);
lean_dec_ref(v_a_2796_);
lean_dec(v_a_2795_);
lean_dec_ref(v_a_2794_);
lean_dec(v_a_2793_);
lean_dec(v_a_2792_);
return v_res_2799_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftReflection___boxed(lean_object* v_distanceExpr_2800_, lean_object* v_innerExpr_2801_, lean_object* v_shiftOp_2802_, lean_object* v_shiftOpName_2803_, lean_object* v_congrThm_2804_, lean_object* v_origExpr_2805_, lean_object* v_a_2806_, lean_object* v_a_2807_, lean_object* v_a_2808_, lean_object* v_a_2809_, lean_object* v_a_2810_, lean_object* v_a_2811_, lean_object* v_a_2812_){
_start:
{
lean_object* v_res_2813_; 
v_res_2813_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftReflection(v_distanceExpr_2800_, v_innerExpr_2801_, v_shiftOp_2802_, v_shiftOpName_2803_, v_congrThm_2804_, v_origExpr_2805_, v_a_2806_, v_a_2807_, v_a_2808_, v_a_2809_, v_a_2810_, v_a_2811_);
lean_dec(v_a_2811_);
lean_dec_ref(v_a_2810_);
lean_dec(v_a_2809_);
lean_dec_ref(v_a_2808_);
lean_dec(v_a_2807_);
lean_dec(v_a_2806_);
return v_res_2813_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom_spec__2___boxed(lean_object* v_e_2814_, lean_object* v_a_2815_, lean_object* v_a_2816_, lean_object* v_a_2817_, lean_object* v_a_2818_, lean_object* v_a_2819_, lean_object* v_a_2820_, lean_object* v_a_2821_){
_start:
{
lean_object* v_res_2822_; 
v_res_2822_ = l_Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom_spec__2(v_e_2814_, v_a_2815_, v_a_2816_, v_a_2817_, v_a_2818_, v_a_2819_, v_a_2820_);
lean_dec(v_a_2820_);
lean_dec_ref(v_a_2819_);
lean_dec(v_a_2818_);
lean_dec_ref(v_a_2817_);
lean_dec(v_a_2816_);
lean_dec(v_a_2815_);
return v_res_2822_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVPredCache___at___00Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_of_spec__5___boxed(lean_object* v_e_2823_, lean_object* v_a_2824_, lean_object* v_a_2825_, lean_object* v_a_2826_, lean_object* v_a_2827_, lean_object* v_a_2828_, lean_object* v_a_2829_, lean_object* v_a_2830_){
_start:
{
lean_object* v_res_2831_; 
v_res_2831_ = l_Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVPredCache___at___00Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_of_spec__5(v_e_2823_, v_a_2824_, v_a_2825_, v_a_2826_, v_a_2827_, v_a_2828_, v_a_2829_);
lean_dec(v_a_2829_);
lean_dec_ref(v_a_2828_);
lean_dec(v_a_2827_);
lean_dec_ref(v_a_2826_);
lean_dec(v_a_2825_);
lean_dec(v_a_2824_);
return v_res_2831_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVExprCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_goOrAtom_spec__10___boxed(lean_object* v_e_2832_, lean_object* v_a_2833_, lean_object* v_a_2834_, lean_object* v_a_2835_, lean_object* v_a_2836_, lean_object* v_a_2837_, lean_object* v_a_2838_, lean_object* v_a_2839_){
_start:
{
lean_object* v_res_2840_; 
v_res_2840_ = l_Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVExprCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_goOrAtom_spec__10(v_e_2832_, v_a_2833_, v_a_2834_, v_a_2835_, v_a_2836_, v_a_2837_, v_a_2838_);
lean_dec(v_a_2838_);
lean_dec_ref(v_a_2837_);
lean_dec(v_a_2836_);
lean_dec_ref(v_a_2835_);
lean_dec(v_a_2834_);
lean_dec(v_a_2833_);
return v_res_2840_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___boxed(lean_object* v_innerExpr_2841_, lean_object* v_op_2842_, lean_object* v_congrThm_2843_, lean_object* v_origExpr_2844_, lean_object* v_a_2845_, lean_object* v_a_2846_, lean_object* v_a_2847_, lean_object* v_a_2848_, lean_object* v_a_2849_, lean_object* v_a_2850_, lean_object* v_a_2851_){
_start:
{
lean_object* v_res_2852_; 
v_res_2852_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection(v_innerExpr_2841_, v_op_2842_, v_congrThm_2843_, v_origExpr_2844_, v_a_2845_, v_a_2846_, v_a_2847_, v_a_2848_, v_a_2849_, v_a_2850_);
lean_dec(v_a_2850_);
lean_dec_ref(v_a_2849_);
lean_dec(v_a_2848_);
lean_dec_ref(v_a_2847_);
lean_dec(v_a_2846_);
lean_dec(v_a_2845_);
return v_res_2852_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___boxed(lean_object* v_lhsExpr_2853_, lean_object* v_rhsExpr_2854_, lean_object* v_op_2855_, lean_object* v_congrThm_2856_, lean_object* v_origExpr_2857_, lean_object* v_a_2858_, lean_object* v_a_2859_, lean_object* v_a_2860_, lean_object* v_a_2861_, lean_object* v_a_2862_, lean_object* v_a_2863_, lean_object* v_a_2864_){
_start:
{
uint8_t v_op_boxed_2865_; lean_object* v_res_2866_; 
v_op_boxed_2865_ = lean_unbox(v_op_2855_);
v_res_2866_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection(v_lhsExpr_2853_, v_rhsExpr_2854_, v_op_boxed_2865_, v_congrThm_2856_, v_origExpr_2857_, v_a_2858_, v_a_2859_, v_a_2860_, v_a_2861_, v_a_2862_, v_a_2863_);
lean_dec(v_a_2863_);
lean_dec_ref(v_a_2862_);
lean_dec(v_a_2861_);
lean_dec_ref(v_a_2860_);
lean_dec(v_a_2859_);
lean_dec(v_a_2858_);
return v_res_2866_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_of_go___boxed(lean_object* v_origExpr_2867_, lean_object* v_a_2868_, lean_object* v_a_2869_, lean_object* v_a_2870_, lean_object* v_a_2871_, lean_object* v_a_2872_, lean_object* v_a_2873_, lean_object* v_a_2874_){
_start:
{
lean_object* v_res_2875_; 
v_res_2875_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_of_go(v_origExpr_2867_, v_a_2868_, v_a_2869_, v_a_2870_, v_a_2871_, v_a_2872_, v_a_2873_);
lean_dec(v_a_2873_);
lean_dec_ref(v_a_2872_);
lean_dec(v_a_2871_);
lean_dec_ref(v_a_2870_);
lean_dec(v_a_2869_);
lean_dec(v_a_2868_);
return v_res_2875_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_go___boxed(lean_object* v_origExpr_2876_, lean_object* v_a_2877_, lean_object* v_a_2878_, lean_object* v_a_2879_, lean_object* v_a_2880_, lean_object* v_a_2881_, lean_object* v_a_2882_, lean_object* v_a_2883_){
_start:
{
lean_object* v_res_2884_; 
v_res_2884_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_go(v_origExpr_2876_, v_a_2877_, v_a_2878_, v_a_2879_, v_a_2880_, v_a_2881_, v_a_2882_);
lean_dec(v_a_2882_);
lean_dec_ref(v_a_2881_);
lean_dec(v_a_2880_);
lean_dec_ref(v_a_2879_);
lean_dec(v_a_2878_);
lean_dec(v_a_2877_);
return v_res_2884_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___boxed(lean_object* v_origExpr_2885_, lean_object* v_a_2886_, lean_object* v_a_2887_, lean_object* v_a_2888_, lean_object* v_a_2889_, lean_object* v_a_2890_, lean_object* v_a_2891_, lean_object* v_a_2892_){
_start:
{
lean_object* v_res_2893_; 
v_res_2893_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go(v_origExpr_2885_, v_a_2886_, v_a_2887_, v_a_2888_, v_a_2889_, v_a_2890_, v_a_2891_);
lean_dec(v_a_2891_);
lean_dec_ref(v_a_2890_);
lean_dec(v_a_2889_);
lean_dec_ref(v_a_2888_);
lean_dec(v_a_2887_);
lean_dec(v_a_2886_);
return v_res_2893_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go_spec__12(lean_object* v_00_u03b1_2894_, lean_object* v_msg_2895_, lean_object* v___y_2896_, lean_object* v___y_2897_, lean_object* v___y_2898_, lean_object* v___y_2899_, lean_object* v___y_2900_, lean_object* v___y_2901_){
_start:
{
lean_object* v___x_2903_; 
v___x_2903_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go_spec__12___redArg(v_msg_2895_, v___y_2898_, v___y_2899_, v___y_2900_, v___y_2901_);
return v___x_2903_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go_spec__12___boxed(lean_object* v_00_u03b1_2904_, lean_object* v_msg_2905_, lean_object* v___y_2906_, lean_object* v___y_2907_, lean_object* v___y_2908_, lean_object* v___y_2909_, lean_object* v___y_2910_, lean_object* v___y_2911_, lean_object* v___y_2912_){
_start:
{
lean_object* v_res_2913_; 
v_res_2913_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go_spec__12(v_00_u03b1_2904_, v_msg_2905_, v___y_2906_, v___y_2907_, v___y_2908_, v___y_2909_, v___y_2910_, v___y_2911_);
lean_dec(v___y_2911_);
lean_dec_ref(v___y_2910_);
lean_dec(v___y_2909_);
lean_dec_ref(v___y_2908_);
lean_dec(v___y_2907_);
lean_dec(v___y_2906_);
return v_res_2913_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom_spec__2_spec__12(lean_object* v_00_u03b2_2914_, lean_object* v_m_2915_, lean_object* v_a_2916_){
_start:
{
lean_object* v___x_2917_; 
v___x_2917_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom_spec__2_spec__12___redArg(v_m_2915_, v_a_2916_);
return v___x_2917_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom_spec__2_spec__12___boxed(lean_object* v_00_u03b2_2918_, lean_object* v_m_2919_, lean_object* v_a_2920_){
_start:
{
lean_object* v_res_2921_; 
v_res_2921_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom_spec__2_spec__12(v_00_u03b2_2918_, v_m_2919_, v_a_2920_);
lean_dec_ref(v_a_2920_);
lean_dec_ref(v_m_2919_);
return v_res_2921_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13(lean_object* v_00_u03b2_2922_, lean_object* v_m_2923_, lean_object* v_a_2924_, lean_object* v_b_2925_){
_start:
{
lean_object* v___x_2926_; 
v___x_2926_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13___redArg(v_m_2923_, v_a_2924_, v_b_2925_);
return v___x_2926_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom_spec__2_spec__12_spec__17(lean_object* v_00_u03b2_2927_, lean_object* v_a_2928_, lean_object* v_x_2929_){
_start:
{
lean_object* v___x_2930_; 
v___x_2930_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom_spec__2_spec__12_spec__17___redArg(v_a_2928_, v_x_2929_);
return v___x_2930_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom_spec__2_spec__12_spec__17___boxed(lean_object* v_00_u03b2_2931_, lean_object* v_a_2932_, lean_object* v_x_2933_){
_start:
{
lean_object* v_res_2934_; 
v_res_2934_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom_spec__2_spec__12_spec__17(v_00_u03b2_2931_, v_a_2932_, v_x_2933_);
lean_dec(v_x_2933_);
lean_dec_ref(v_a_2932_);
return v_res_2934_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13_spec__19(lean_object* v_00_u03b2_2935_, lean_object* v_a_2936_, lean_object* v_x_2937_){
_start:
{
uint8_t v___x_2938_; 
v___x_2938_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13_spec__19___redArg(v_a_2936_, v_x_2937_);
return v___x_2938_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13_spec__19___boxed(lean_object* v_00_u03b2_2939_, lean_object* v_a_2940_, lean_object* v_x_2941_){
_start:
{
uint8_t v_res_2942_; lean_object* v_r_2943_; 
v_res_2942_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13_spec__19(v_00_u03b2_2939_, v_a_2940_, v_x_2941_);
lean_dec(v_x_2941_);
lean_dec_ref(v_a_2940_);
v_r_2943_ = lean_box(v_res_2942_);
return v_r_2943_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13_spec__20(lean_object* v_00_u03b2_2944_, lean_object* v_data_2945_){
_start:
{
lean_object* v___x_2946_; 
v___x_2946_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13_spec__20___redArg(v_data_2945_);
return v___x_2946_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13_spec__21(lean_object* v_00_u03b2_2947_, lean_object* v_a_2948_, lean_object* v_b_2949_, lean_object* v_x_2950_){
_start:
{
lean_object* v___x_2951_; 
v___x_2951_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13_spec__21___redArg(v_a_2948_, v_b_2949_, v_x_2950_);
return v___x_2951_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13_spec__20_spec__25(lean_object* v_00_u03b2_2952_, lean_object* v_i_2953_, lean_object* v_source_2954_, lean_object* v_target_2955_){
_start:
{
lean_object* v___x_2956_; 
v___x_2956_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13_spec__20_spec__25___redArg(v_i_2953_, v_source_2954_, v_target_2955_);
return v___x_2956_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13_spec__20_spec__25_spec__26(lean_object* v_00_u03b2_2957_, lean_object* v_x_2958_, lean_object* v_x_2959_){
_start:
{
lean_object* v___x_2960_; 
v___x_2960_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13_spec__20_spec__25_spec__26___redArg(v_x_2958_, v_x_2959_);
return v___x_2960_;
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
