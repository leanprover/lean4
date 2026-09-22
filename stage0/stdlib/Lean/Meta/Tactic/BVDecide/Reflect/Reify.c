// Lean compiler output
// Module: Lean.Meta.Tactic.BVDecide.Reflect.Reify
// Imports: public import Lean.Meta.Tactic.BVDecide.Reflect.Basic import Lean.Meta.Tactic.BVDecide.Reflect.ReifiedLemmas import Lean.Meta.Tactic.BVDecide.Reflect.ReifiedBVExpr import Lean.Meta.Tactic.BVDecide.Reflect.ReifiedBVPred import Lean.Meta.Tactic.BVDecide.Reflect.ReifiedBVLogical import Lean.Meta.Sym.LitValues import Lean.Meta.AppBuilder import Std.Tactic.BVDecide.Reflect
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
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
uint64_t lean_usize_to_uint64(size_t);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Std_Tactic_BVDecide_BVExpr_shiftLeft___override(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_BVExpr_shiftRight___override(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_BVExpr_arithShiftRight___override(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_checkSystem(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkNatLit(lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommonInc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkEvalExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVRefl(lean_object*, lean_object*);
lean_object* l_Lean_mkApp6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_BVExpr_bin___override(lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_getNatOrBvValue_x3f___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Meta_Sym_getNatValue_x3f(lean_object*);
lean_object* l_Std_Tactic_BVDecide_BVExpr_append___override___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqRefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_BVExpr_extract___override(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_bitVecAtom(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkGetLsbD___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkIte___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkNot___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_boolAtom(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_addCondLemmas___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_BVExpr_un___override(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_BVExpr_replicate___override___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_getBitVecValue_x3f(lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVConst___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_goBvLit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_goBvLit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_M_simplifyBinaryProof_x27___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryCongrProof_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryCongrProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryCongrProof___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryCongrProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryCongrProof___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__12_spec__17___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__12_spec__17___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__12___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__12___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13_spec__20_spec__25_spec__26___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13_spec__20_spec__25___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13_spec__20___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13_spec__21___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13_spec__19___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13_spec__19___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__0(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Reflect"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__4___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__4___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "extract_congr"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__4___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__4___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__4___boxed(lean_object**);
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "replicate_congr"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__5___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__5___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__5___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go_spec__12_spec__20(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go_spec__12_spec__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go_spec__12___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_M_simplifyBinaryProof_x27___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "append_congr"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__3___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__3___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__3___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__1(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__2(lean_object*);
static const lean_closure_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__0_value;
static const lean_closure_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Tactic_BVDecide_BVExpr_shiftLeft___override, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__1_value;
static const lean_closure_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Tactic_BVDecide_BVExpr_shiftRight___override, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__2_value;
static const lean_closure_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Tactic_BVDecide_BVExpr_arithShiftRight___override, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__3_value;
static const lean_closure_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__1, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__4_value;
static const lean_closure_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__2, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__5_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "bv_decide"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "BitVec"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "cpop"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__19 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__19_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(108, 178, 58, 132, 143, 189, 222, 74)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__6_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__19_value),LEAN_SCALAR_PTR_LITERAL(54, 25, 40, 162, 224, 189, 205, 182)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__6_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "clz"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__16 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__16_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(108, 178, 58, 132, 143, 189, 222, 74)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__7_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__16_value),LEAN_SCALAR_PTR_LITERAL(61, 156, 207, 111, 211, 81, 174, 218)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__7_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "reverse"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__13 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__13_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(108, 178, 58, 132, 143, 189, 222, 74)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__8_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__13_value),LEAN_SCALAR_PTR_LITERAL(244, 136, 165, 42, 211, 46, 208, 62)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__8_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ofNat"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__9_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(108, 178, 58, 132, 143, 189, 222, 74)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__10_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__9_value),LEAN_SCALAR_PTR_LITERAL(101, 105, 192, 171, 214, 131, 43, 105)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__10 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__10_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "rotateRight"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__7_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(108, 178, 58, 132, 143, 189, 222, 74)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__11_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__7_value),LEAN_SCALAR_PTR_LITERAL(208, 30, 240, 114, 51, 110, 152, 157)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__11 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__11_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "rotateLeft"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__4_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(108, 178, 58, 132, 143, 189, 222, 74)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__12_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__4_value),LEAN_SCALAR_PTR_LITERAL(125, 181, 93, 155, 164, 43, 234, 184)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__12 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__12_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "replicate"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__13 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__13_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(108, 178, 58, 132, 143, 189, 222, 74)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__14_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__13_value),LEAN_SCALAR_PTR_LITERAL(234, 123, 74, 120, 175, 214, 39, 20)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__14 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__14_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "sshiftRight"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__15 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__15_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(108, 178, 58, 132, 143, 189, 222, 74)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__16_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__15_value),LEAN_SCALAR_PTR_LITERAL(206, 65, 29, 246, 207, 155, 165, 148)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__16 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__16_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "complement"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__18 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__18_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "Complement"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__17 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__17_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__19_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__17_value),LEAN_SCALAR_PTR_LITERAL(6, 52, 244, 64, 3, 58, 115, 79)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__19_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__18_value),LEAN_SCALAR_PTR_LITERAL(168, 254, 142, 44, 189, 175, 152, 168)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__19 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__19_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "cond"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__9_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__9_value),LEAN_SCALAR_PTR_LITERAL(130, 140, 200, 235, 144, 197, 118, 1)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__10 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__10_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "extractLsb'"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__20 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__20_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__21_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(108, 178, 58, 132, 143, 189, 222, 74)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__21_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__20_value),LEAN_SCALAR_PTR_LITERAL(47, 201, 218, 12, 248, 124, 75, 23)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__21 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__21_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "sshiftRight'"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__22 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__22_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__23_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(108, 178, 58, 132, 143, 189, 222, 74)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__23_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__22_value),LEAN_SCALAR_PTR_LITERAL(69, 78, 17, 52, 147, 31, 186, 103)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__23 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__23_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(108, 178, 58, 132, 143, 189, 222, 74)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__8_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "shiftRight"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__24 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__24_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "BVExpr"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__3_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "BVDecide"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Std"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__25_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__25_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__25_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__25_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__25_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__25_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__25_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__3_value),LEAN_SCALAR_PTR_LITERAL(43, 53, 240, 176, 234, 207, 251, 199)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__25_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__24_value),LEAN_SCALAR_PTR_LITERAL(71, 199, 243, 56, 253, 18, 242, 226)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__25 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__25_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "shiftRight_congr"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__26 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__26_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__27_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__27_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__27_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__27_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__27_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__27_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__27_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__4___closed__0_value),LEAN_SCALAR_PTR_LITERAL(32, 92, 17, 213, 68, 211, 219, 250)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__27_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__27_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(179, 160, 70, 158, 0, 14, 153, 5)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__27_value_aux_4),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__26_value),LEAN_SCALAR_PTR_LITERAL(216, 161, 38, 33, 237, 165, 100, 97)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__27 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__27_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftReflection(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "shiftLeft"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__28 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__28_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__29_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__29_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__29_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__29_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__29_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__29_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__29_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__3_value),LEAN_SCALAR_PTR_LITERAL(43, 53, 240, 176, 234, 207, 251, 199)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__29_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__28_value),LEAN_SCALAR_PTR_LITERAL(197, 209, 242, 75, 214, 61, 180, 95)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__29 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__29_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "shiftLeft_congr"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__30 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__30_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__31_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__31_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__31_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__31_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__31_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__31_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__31_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__4___closed__0_value),LEAN_SCALAR_PTR_LITERAL(32, 92, 17, 213, 68, 211, 219, 250)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__31_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__31_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(179, 160, 70, 158, 0, 14, 153, 5)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__31_value_aux_4),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__30_value),LEAN_SCALAR_PTR_LITERAL(121, 119, 67, 4, 228, 88, 122, 113)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__31 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__31_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "hAppend"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__33 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__33_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "HAppend"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__32 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__32_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__34_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__32_value),LEAN_SCALAR_PTR_LITERAL(137, 35, 233, 160, 196, 216, 250, 31)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__34_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__33_value),LEAN_SCALAR_PTR_LITERAL(181, 97, 51, 176, 35, 131, 5, 233)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__34 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__34_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "hShiftRight"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__36 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__36_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "HShiftRight"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__35 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__35_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__37_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__35_value),LEAN_SCALAR_PTR_LITERAL(123, 35, 163, 146, 1, 76, 65, 75)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__37_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__36_value),LEAN_SCALAR_PTR_LITERAL(52, 65, 204, 240, 51, 126, 9, 157)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__37 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__37_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "hShiftLeft"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__39 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__39_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "HShiftLeft"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__38 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__38_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__40_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__38_value),LEAN_SCALAR_PTR_LITERAL(215, 217, 51, 89, 252, 54, 156, 169)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__40_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__39_value),LEAN_SCALAR_PTR_LITERAL(181, 245, 218, 3, 224, 235, 179, 59)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__40 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__40_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hMod"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__42 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__42_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HMod"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__41 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__41_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__43_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__41_value),LEAN_SCALAR_PTR_LITERAL(93, 4, 3, 35, 188, 254, 191, 190)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__43_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__42_value),LEAN_SCALAR_PTR_LITERAL(120, 199, 142, 238, 9, 44, 94, 134)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__43 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__43_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hDiv"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__45 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__45_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HDiv"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__44 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__44_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__46_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__44_value),LEAN_SCALAR_PTR_LITERAL(74, 223, 78, 88, 255, 236, 144, 164)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__46_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__45_value),LEAN_SCALAR_PTR_LITERAL(26, 183, 188, 240, 156, 118, 170, 84)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__46 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__46_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hMul"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__48 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__48_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HMul"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__47 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__47_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__49_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__47_value),LEAN_SCALAR_PTR_LITERAL(254, 113, 255, 140, 142, 9, 169, 40)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__49_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__48_value),LEAN_SCALAR_PTR_LITERAL(248, 227, 200, 215, 229, 255, 92, 22)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__49 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__49_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hAdd"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__51 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__51_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HAdd"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__50 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__50_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__52_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__50_value),LEAN_SCALAR_PTR_LITERAL(221, 239, 47, 196, 170, 166, 59, 144)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__52_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__51_value),LEAN_SCALAR_PTR_LITERAL(134, 172, 115, 219, 189, 252, 56, 148)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__52 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__52_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__54_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hXor"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__54 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__54_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HXor"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__53 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__53_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__55_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__53_value),LEAN_SCALAR_PTR_LITERAL(92, 198, 212, 133, 26, 7, 147, 78)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__55_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__55_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__54_value),LEAN_SCALAR_PTR_LITERAL(109, 159, 33, 254, 118, 42, 120, 166)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__55 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__55_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__57_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hAnd"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__57 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__57_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__56_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HAnd"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__56 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__56_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__58_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__56_value),LEAN_SCALAR_PTR_LITERAL(222, 205, 8, 181, 48, 134, 168, 175)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__58_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__58_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__57_value),LEAN_SCALAR_PTR_LITERAL(54, 171, 107, 112, 94, 43, 106, 200)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__58 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__58_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__59_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "and_congr"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__59 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__59_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__60_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__60_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__60_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__60_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__60_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__60_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__60_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__4___closed__0_value),LEAN_SCALAR_PTR_LITERAL(32, 92, 17, 213, 68, 211, 219, 250)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__60_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__60_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(179, 160, 70, 158, 0, 14, 153, 5)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__60_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__60_value_aux_4),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__59_value),LEAN_SCALAR_PTR_LITERAL(20, 152, 116, 121, 198, 45, 139, 17)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__60 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__60_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "bin"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__3_value),LEAN_SCALAR_PTR_LITERAL(43, 53, 240, 176, 234, 207, 251, 199)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__0_value),LEAN_SCALAR_PTR_LITERAL(47, 182, 211, 92, 78, 225, 70, 26)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__1_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__2;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "and"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__4_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "BVBinOp"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__3_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__5_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__5_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__5_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__3_value),LEAN_SCALAR_PTR_LITERAL(173, 0, 131, 50, 199, 91, 123, 28)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__5_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__4_value),LEAN_SCALAR_PTR_LITERAL(67, 200, 193, 54, 191, 172, 208, 119)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__5_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__6;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "or"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__7_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__8_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__8_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__8_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__8_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__3_value),LEAN_SCALAR_PTR_LITERAL(173, 0, 131, 50, 199, 91, 123, 28)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__8_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__7_value),LEAN_SCALAR_PTR_LITERAL(137, 33, 141, 132, 156, 154, 79, 232)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__8_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__9;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "xor"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__10 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__10_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__11_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__11_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__11_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__11_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__3_value),LEAN_SCALAR_PTR_LITERAL(173, 0, 131, 50, 199, 91, 123, 28)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__11_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__10_value),LEAN_SCALAR_PTR_LITERAL(68, 221, 44, 95, 169, 9, 73, 176)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__11 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__11_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__12;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "add"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__13 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__13_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__14_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__14_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__14_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__14_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__14_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__14_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__3_value),LEAN_SCALAR_PTR_LITERAL(173, 0, 131, 50, 199, 91, 123, 28)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__14_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__13_value),LEAN_SCALAR_PTR_LITERAL(236, 85, 182, 141, 252, 28, 21, 198)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__14 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__14_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__15;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "mul"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__16 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__16_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__17_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__17_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__17_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__17_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__17_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__17_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__3_value),LEAN_SCALAR_PTR_LITERAL(173, 0, 131, 50, 199, 91, 123, 28)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__17_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__16_value),LEAN_SCALAR_PTR_LITERAL(66, 46, 226, 27, 15, 162, 209, 81)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__17 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__17_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__18;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "udiv"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__19 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__19_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__20_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__20_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__20_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__20_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__20_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__20_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__20_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__3_value),LEAN_SCALAR_PTR_LITERAL(173, 0, 131, 50, 199, 91, 123, 28)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__20_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__19_value),LEAN_SCALAR_PTR_LITERAL(97, 106, 189, 172, 252, 249, 116, 143)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__20 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__20_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__21;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "umod"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__22 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__22_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__23_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__23_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__23_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__23_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__23_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__23_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__23_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__3_value),LEAN_SCALAR_PTR_LITERAL(173, 0, 131, 50, 199, 91, 123, 28)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__23_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__22_value),LEAN_SCALAR_PTR_LITERAL(185, 164, 216, 8, 44, 82, 23, 11)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__23 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__23_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__24;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__61_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "xor_congr"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__61 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__61_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__62_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__62_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__62_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__62_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__62_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__62_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__62_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__4___closed__0_value),LEAN_SCALAR_PTR_LITERAL(32, 92, 17, 213, 68, 211, 219, 250)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__62_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__62_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(179, 160, 70, 158, 0, 14, 153, 5)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__62_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__62_value_aux_4),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__61_value),LEAN_SCALAR_PTR_LITERAL(225, 129, 197, 38, 228, 52, 44, 57)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__62 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__62_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__63_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "add_congr"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__63 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__63_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__64_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__64_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__64_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__64_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__64_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__64_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__64_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__4___closed__0_value),LEAN_SCALAR_PTR_LITERAL(32, 92, 17, 213, 68, 211, 219, 250)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__64_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__64_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(179, 160, 70, 158, 0, 14, 153, 5)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__64_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__64_value_aux_4),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__63_value),LEAN_SCALAR_PTR_LITERAL(177, 5, 60, 46, 78, 68, 243, 177)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__64 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__64_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__65_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "mul_congr"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__65 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__65_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__66_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__66_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__66_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__66_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__66_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__66_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__66_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__4___closed__0_value),LEAN_SCALAR_PTR_LITERAL(32, 92, 17, 213, 68, 211, 219, 250)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__66_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__66_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(179, 160, 70, 158, 0, 14, 153, 5)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__66_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__66_value_aux_4),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__65_value),LEAN_SCALAR_PTR_LITERAL(221, 159, 178, 23, 57, 108, 69, 225)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__66 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__66_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__67_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "udiv_congr"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__67 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__67_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__68_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__68_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__68_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__68_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__68_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__68_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__68_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__4___closed__0_value),LEAN_SCALAR_PTR_LITERAL(32, 92, 17, 213, 68, 211, 219, 250)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__68_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__68_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(179, 160, 70, 158, 0, 14, 153, 5)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__68_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__68_value_aux_4),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__67_value),LEAN_SCALAR_PTR_LITERAL(118, 153, 195, 105, 228, 227, 83, 28)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__68 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__68_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__69_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "umod_congr"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__69 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__69_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__70_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__70_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__70_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__70_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__70_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__70_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__70_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__4___closed__0_value),LEAN_SCALAR_PTR_LITERAL(32, 92, 17, 213, 68, 211, 219, 250)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__70_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__70_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(179, 160, 70, 158, 0, 14, 153, 5)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__70_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__70_value_aux_4),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__69_value),LEAN_SCALAR_PTR_LITERAL(102, 27, 81, 101, 187, 174, 242, 104)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__70 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__70_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__71_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 60, .m_capacity = 60, .m_length = 59, .m_data = "internal error: constant shift should have been eliminated."};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__71 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__71_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__72_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__72;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__73_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "append"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__73 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__73_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__74_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__74_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__74_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__74_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__74_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__74_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__74_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__3_value),LEAN_SCALAR_PTR_LITERAL(43, 53, 240, 176, 234, 207, 251, 199)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__74_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__74_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__73_value),LEAN_SCALAR_PTR_LITERAL(148, 222, 207, 10, 98, 174, 247, 204)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__74 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__74_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__75_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__75;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__76_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "arithShiftRight"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__76 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__76_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__77_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__77_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__77_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__77_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__77_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__77_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__77_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__3_value),LEAN_SCALAR_PTR_LITERAL(43, 53, 240, 176, 234, 207, 251, 199)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__77_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__77_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__76_value),LEAN_SCALAR_PTR_LITERAL(103, 53, 88, 127, 221, 158, 175, 136)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__77 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__77_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__78_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "arithShiftRight_congr"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__78 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__78_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__79_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__79_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__79_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__79_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__79_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__79_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__79_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__4___closed__0_value),LEAN_SCALAR_PTR_LITERAL(32, 92, 17, 213, 68, 211, 219, 250)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__79_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__79_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(179, 160, 70, 158, 0, 14, 153, 5)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__79_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__79_value_aux_4),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__78_value),LEAN_SCALAR_PTR_LITERAL(52, 31, 162, 102, 135, 66, 0, 161)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__79 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__79_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__80_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "extract"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__80 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__80_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__81_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__81_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__81_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__81_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__81_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__81_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__81_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__3_value),LEAN_SCALAR_PTR_LITERAL(43, 53, 240, 176, 234, 207, 251, 199)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__81_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__81_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__80_value),LEAN_SCALAR_PTR_LITERAL(13, 22, 63, 119, 146, 191, 248, 8)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__81 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__81_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__82_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__82;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Bool"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__1_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__2_value),LEAN_SCALAR_PTR_LITERAL(117, 151, 161, 190, 111, 237, 188, 218)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__3_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__4_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__1_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__4_value),LEAN_SCALAR_PTR_LITERAL(22, 245, 194, 28, 184, 9, 113, 128)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__5_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "getLsbD"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(108, 178, 58, 132, 143, 189, 222, 74)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__1_value),LEAN_SCALAR_PTR_LITERAL(201, 206, 226, 96, 197, 228, 245, 77)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "ult"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__3_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(108, 178, 58, 132, 143, 189, 222, 74)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__3_value),LEAN_SCALAR_PTR_LITERAL(111, 62, 117, 244, 108, 14, 8, 240)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__4_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "beq"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__6_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "BEq"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__5_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__5_value),LEAN_SCALAR_PTR_LITERAL(195, 188, 39, 55, 57, 152, 88, 223)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__7_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__6_value),LEAN_SCALAR_PTR_LITERAL(82, 52, 243, 194, 7, 226, 90, 135)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__7_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_binaryReflection(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_LemmaM_withBVPredCache___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goPred(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "not"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__1_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__6_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__1_value),LEAN_SCALAR_PTR_LITERAL(208, 215, 171, 150, 192, 180, 249, 22)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__6_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__1_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__7_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__10_value),LEAN_SCALAR_PTR_LITERAL(159, 35, 146, 118, 24, 65, 174, 144)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__7_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__1_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__8_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__4_value),LEAN_SCALAR_PTR_LITERAL(160, 26, 8, 228, 104, 32, 82, 85)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__8_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__1_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__11 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__11_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_gateReflection(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__83_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "not_congr"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__83 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__83_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__84_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__84_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__84_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__84_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__84_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__84_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__84_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__4___closed__0_value),LEAN_SCALAR_PTR_LITERAL(32, 92, 17, 213, 68, 211, 219, 250)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__84_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__84_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(179, 160, 70, 158, 0, 14, 153, 5)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__84_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__84_value_aux_4),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__83_value),LEAN_SCALAR_PTR_LITERAL(189, 30, 154, 245, 30, 224, 55, 44)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__84 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__84_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "un"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__4_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__5_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__5_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__5_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__3_value),LEAN_SCALAR_PTR_LITERAL(43, 53, 240, 176, 234, 207, 251, 199)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__5_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__4_value),LEAN_SCALAR_PTR_LITERAL(42, 186, 200, 92, 180, 128, 216, 181)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__5_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__6;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "BVUnOp"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__2_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__2_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 14, 123, 74, 130, 241, 190, 47)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__2_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__1_value),LEAN_SCALAR_PTR_LITERAL(30, 170, 248, 163, 146, 14, 228, 74)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__3;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__5_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__5_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__5_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 14, 123, 74, 130, 241, 190, 47)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__5_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__4_value),LEAN_SCALAR_PTR_LITERAL(29, 116, 55, 155, 243, 43, 27, 136)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__5_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__6;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__8_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__8_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__8_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__8_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 14, 123, 74, 130, 241, 190, 47)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__8_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__7_value),LEAN_SCALAR_PTR_LITERAL(112, 197, 123, 204, 93, 250, 252, 249)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__8_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__9;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "arithShiftRightConst"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__10 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__10_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__11_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__11_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__11_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__11_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 14, 123, 74, 130, 241, 190, 47)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__11_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__10_value),LEAN_SCALAR_PTR_LITERAL(88, 95, 189, 240, 90, 71, 117, 208)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__11 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__11_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__12;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__14_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__14_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__14_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__14_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__14_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__14_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 14, 123, 74, 130, 241, 190, 47)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__14_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__13_value),LEAN_SCALAR_PTR_LITERAL(84, 226, 239, 81, 45, 17, 252, 180)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__14 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__14_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__15;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__17_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__17_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__17_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__17_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__17_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__17_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 14, 123, 74, 130, 241, 190, 47)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__17_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__16_value),LEAN_SCALAR_PTR_LITERAL(221, 66, 219, 130, 52, 97, 84, 10)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__17 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__17_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__18;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__20_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__20_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__20_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__20_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__20_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__20_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__20_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 14, 123, 74, 130, 241, 190, 47)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__20_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__19_value),LEAN_SCALAR_PTR_LITERAL(214, 119, 73, 246, 51, 241, 221, 59)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__20 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__20_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__21;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__85_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "arithShiftRightNat_congr"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__85 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__85_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__86_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__86_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__86_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__86_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__86_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__86_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__86_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__4___closed__0_value),LEAN_SCALAR_PTR_LITERAL(32, 92, 17, 213, 68, 211, 219, 250)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__86_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__86_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(179, 160, 70, 158, 0, 14, 153, 5)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__86_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__86_value_aux_4),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__85_value),LEAN_SCALAR_PTR_LITERAL(59, 32, 240, 3, 69, 217, 10, 161)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__86 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__86_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__87_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__87_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__87_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__87_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__87_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__87_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__87_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__3_value),LEAN_SCALAR_PTR_LITERAL(43, 53, 240, 176, 234, 207, 251, 199)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__87_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__87_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__13_value),LEAN_SCALAR_PTR_LITERAL(105, 148, 101, 98, 245, 160, 38, 159)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__87 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__87_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__88_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__88;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__89_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "rotateLeft_congr"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__89 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__89_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__90_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__90_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__90_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__90_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__90_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__90_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__90_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__4___closed__0_value),LEAN_SCALAR_PTR_LITERAL(32, 92, 17, 213, 68, 211, 219, 250)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__90_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__90_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(179, 160, 70, 158, 0, 14, 153, 5)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__90_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__90_value_aux_4),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__89_value),LEAN_SCALAR_PTR_LITERAL(32, 228, 194, 198, 195, 74, 36, 62)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__90 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__90_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_rotateReflection(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__91_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "rotateRight_congr"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__91 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__91_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__92_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__92_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__92_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__92_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__92_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__92_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__92_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__4___closed__0_value),LEAN_SCALAR_PTR_LITERAL(32, 92, 17, 213, 68, 211, 219, 250)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__92_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__92_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(179, 160, 70, 158, 0, 14, 153, 5)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__92_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__92_value_aux_4),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__91_value),LEAN_SCALAR_PTR_LITERAL(61, 145, 127, 186, 176, 174, 37, 55)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__92 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__92_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__93_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "reverse_congr"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__93 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__93_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__94_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__94_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__94_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__94_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__94_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__94_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__94_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__4___closed__0_value),LEAN_SCALAR_PTR_LITERAL(32, 92, 17, 213, 68, 211, 219, 250)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__94_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__94_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(179, 160, 70, 158, 0, 14, 153, 5)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__94_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__94_value_aux_4),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__93_value),LEAN_SCALAR_PTR_LITERAL(182, 175, 240, 129, 220, 112, 73, 89)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__94 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__94_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__95_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "clz_congr"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__95 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__95_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__96_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__96_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__96_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__96_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__96_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__96_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__96_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__4___closed__0_value),LEAN_SCALAR_PTR_LITERAL(32, 92, 17, 213, 68, 211, 219, 250)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__96_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__96_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(179, 160, 70, 158, 0, 14, 153, 5)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__96_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__96_value_aux_4),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__95_value),LEAN_SCALAR_PTR_LITERAL(108, 254, 78, 195, 105, 118, 43, 132)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__96 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__96_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__97_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "cpop_congr"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__97 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__97_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__98_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__98_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__98_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__98_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__98_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__98_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__98_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__4___closed__0_value),LEAN_SCALAR_PTR_LITERAL(32, 92, 17, 213, 68, 211, 219, 250)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__98_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__98_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(179, 160, 70, 158, 0, 14, 153, 5)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__98_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__98_value_aux_4),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__97_value),LEAN_SCALAR_PTR_LITERAL(181, 75, 188, 170, 67, 231, 89, 223)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__98 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__98_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_LemmaM_withBVExprCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_goOrAtom_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_goOrAtom(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_goOrAtom___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_rotateReflection___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goPred___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_binaryReflection___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_gateReflection___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_LemmaM_withBVPredCache___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_LemmaM_withBVExprCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_goOrAtom_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftReflection___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go_spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__12(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__12___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__12_spec__17(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__12_spec__17___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13_spec__19(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13_spec__19___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13_spec__20(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13_spec__21(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13_spec__20_spec__25(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13_spec__20_spec__25_spec__26(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_goBvLit(lean_object* v_x_1_, lean_object* v_a_2_, lean_object* v_a_3_, lean_object* v_a_4_, lean_object* v_a_5_, lean_object* v_a_6_, lean_object* v_a_7_, lean_object* v_a_8_, lean_object* v_a_9_){
_start:
{
lean_object* v___x_11_; 
lean_inc_ref(v_x_1_);
v___x_11_ = l_Lean_Meta_Sym_getBitVecValue_x3f(v_x_1_);
if (lean_obj_tag(v___x_11_) == 1)
{
lean_object* v_val_12_; lean_object* v___x_14_; uint8_t v_isShared_15_; uint8_t v_isSharedCheck_38_; 
lean_dec_ref(v_x_1_);
v_val_12_ = lean_ctor_get(v___x_11_, 0);
v_isSharedCheck_38_ = !lean_is_exclusive(v___x_11_);
if (v_isSharedCheck_38_ == 0)
{
v___x_14_ = v___x_11_;
v_isShared_15_ = v_isSharedCheck_38_;
goto v_resetjp_13_;
}
else
{
lean_inc(v_val_12_);
lean_dec(v___x_11_);
v___x_14_ = lean_box(0);
v_isShared_15_ = v_isSharedCheck_38_;
goto v_resetjp_13_;
}
v_resetjp_13_:
{
lean_object* v_n_16_; lean_object* v_val_17_; lean_object* v___x_18_; 
v_n_16_ = lean_ctor_get(v_val_12_, 0);
lean_inc(v_n_16_);
v_val_17_ = lean_ctor_get(v_val_12_, 1);
lean_inc(v_val_17_);
lean_dec(v_val_12_);
v___x_18_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVConst___redArg(v_n_16_, v_val_17_, v_a_4_, v_a_5_, v_a_6_, v_a_7_, v_a_8_, v_a_9_);
if (lean_obj_tag(v___x_18_) == 0)
{
lean_object* v_a_19_; lean_object* v___x_21_; uint8_t v_isShared_22_; uint8_t v_isSharedCheck_29_; 
v_a_19_ = lean_ctor_get(v___x_18_, 0);
v_isSharedCheck_29_ = !lean_is_exclusive(v___x_18_);
if (v_isSharedCheck_29_ == 0)
{
v___x_21_ = v___x_18_;
v_isShared_22_ = v_isSharedCheck_29_;
goto v_resetjp_20_;
}
else
{
lean_inc(v_a_19_);
lean_dec(v___x_18_);
v___x_21_ = lean_box(0);
v_isShared_22_ = v_isSharedCheck_29_;
goto v_resetjp_20_;
}
v_resetjp_20_:
{
lean_object* v___x_24_; 
if (v_isShared_15_ == 0)
{
lean_ctor_set(v___x_14_, 0, v_a_19_);
v___x_24_ = v___x_14_;
goto v_reusejp_23_;
}
else
{
lean_object* v_reuseFailAlloc_28_; 
v_reuseFailAlloc_28_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_28_, 0, v_a_19_);
v___x_24_ = v_reuseFailAlloc_28_;
goto v_reusejp_23_;
}
v_reusejp_23_:
{
lean_object* v___x_26_; 
if (v_isShared_22_ == 0)
{
lean_ctor_set(v___x_21_, 0, v___x_24_);
v___x_26_ = v___x_21_;
goto v_reusejp_25_;
}
else
{
lean_object* v_reuseFailAlloc_27_; 
v_reuseFailAlloc_27_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_27_, 0, v___x_24_);
v___x_26_ = v_reuseFailAlloc_27_;
goto v_reusejp_25_;
}
v_reusejp_25_:
{
return v___x_26_;
}
}
}
}
else
{
lean_object* v_a_30_; lean_object* v___x_32_; uint8_t v_isShared_33_; uint8_t v_isSharedCheck_37_; 
lean_del_object(v___x_14_);
v_a_30_ = lean_ctor_get(v___x_18_, 0);
v_isSharedCheck_37_ = !lean_is_exclusive(v___x_18_);
if (v_isSharedCheck_37_ == 0)
{
v___x_32_ = v___x_18_;
v_isShared_33_ = v_isSharedCheck_37_;
goto v_resetjp_31_;
}
else
{
lean_inc(v_a_30_);
lean_dec(v___x_18_);
v___x_32_ = lean_box(0);
v_isShared_33_ = v_isSharedCheck_37_;
goto v_resetjp_31_;
}
v_resetjp_31_:
{
lean_object* v___x_35_; 
if (v_isShared_33_ == 0)
{
v___x_35_ = v___x_32_;
goto v_reusejp_34_;
}
else
{
lean_object* v_reuseFailAlloc_36_; 
v_reuseFailAlloc_36_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_36_, 0, v_a_30_);
v___x_35_ = v_reuseFailAlloc_36_;
goto v_reusejp_34_;
}
v_reusejp_34_:
{
return v___x_35_;
}
}
}
}
}
else
{
uint8_t v___x_39_; lean_object* v___x_40_; 
lean_dec(v___x_11_);
v___x_39_ = 0;
v___x_40_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_bitVecAtom(v_x_1_, v___x_39_, v_a_2_, v_a_3_, v_a_4_, v_a_5_, v_a_6_, v_a_7_, v_a_8_, v_a_9_);
return v___x_40_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_goBvLit___boxed(lean_object* v_x_41_, lean_object* v_a_42_, lean_object* v_a_43_, lean_object* v_a_44_, lean_object* v_a_45_, lean_object* v_a_46_, lean_object* v_a_47_, lean_object* v_a_48_, lean_object* v_a_49_, lean_object* v_a_50_){
_start:
{
lean_object* v_res_51_; 
v_res_51_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_goBvLit(v_x_41_, v_a_42_, v_a_43_, v_a_44_, v_a_45_, v_a_46_, v_a_47_, v_a_48_, v_a_49_);
lean_dec(v_a_49_);
lean_dec_ref(v_a_48_);
lean_dec(v_a_47_);
lean_dec_ref(v_a_46_);
lean_dec(v_a_45_);
lean_dec_ref(v_a_44_);
lean_dec(v_a_43_);
lean_dec_ref(v_a_42_);
return v_res_51_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_M_simplifyBinaryProof_x27___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryCongrProof_spec__0(lean_object* v___x_52_, lean_object* v_fst_53_, lean_object* v_fproof_54_, lean_object* v_snd_55_, lean_object* v_sproof_56_){
_start:
{
if (lean_obj_tag(v_fproof_54_) == 0)
{
lean_dec_ref(v_snd_55_);
if (lean_obj_tag(v_sproof_56_) == 0)
{
lean_object* v___x_57_; 
lean_dec_ref(v_fst_53_);
lean_dec(v___x_52_);
v___x_57_ = lean_box(0);
return v___x_57_;
}
else
{
lean_object* v_val_58_; lean_object* v___x_60_; uint8_t v_isShared_61_; uint8_t v_isSharedCheck_67_; 
v_val_58_ = lean_ctor_get(v_sproof_56_, 0);
v_isSharedCheck_67_ = !lean_is_exclusive(v_sproof_56_);
if (v_isSharedCheck_67_ == 0)
{
v___x_60_ = v_sproof_56_;
v_isShared_61_ = v_isSharedCheck_67_;
goto v_resetjp_59_;
}
else
{
lean_inc(v_val_58_);
lean_dec(v_sproof_56_);
v___x_60_ = lean_box(0);
v_isShared_61_ = v_isSharedCheck_67_;
goto v_resetjp_59_;
}
v_resetjp_59_:
{
lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_65_; 
v___x_62_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVRefl(v___x_52_, v_fst_53_);
v___x_63_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_63_, 0, v___x_62_);
lean_ctor_set(v___x_63_, 1, v_val_58_);
if (v_isShared_61_ == 0)
{
lean_ctor_set(v___x_60_, 0, v___x_63_);
v___x_65_ = v___x_60_;
goto v_reusejp_64_;
}
else
{
lean_object* v_reuseFailAlloc_66_; 
v_reuseFailAlloc_66_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_66_, 0, v___x_63_);
v___x_65_ = v_reuseFailAlloc_66_;
goto v_reusejp_64_;
}
v_reusejp_64_:
{
return v___x_65_;
}
}
}
}
else
{
lean_dec_ref(v_fst_53_);
if (lean_obj_tag(v_sproof_56_) == 0)
{
lean_object* v_val_68_; lean_object* v___x_70_; uint8_t v_isShared_71_; uint8_t v_isSharedCheck_77_; 
v_val_68_ = lean_ctor_get(v_fproof_54_, 0);
v_isSharedCheck_77_ = !lean_is_exclusive(v_fproof_54_);
if (v_isSharedCheck_77_ == 0)
{
v___x_70_ = v_fproof_54_;
v_isShared_71_ = v_isSharedCheck_77_;
goto v_resetjp_69_;
}
else
{
lean_inc(v_val_68_);
lean_dec(v_fproof_54_);
v___x_70_ = lean_box(0);
v_isShared_71_ = v_isSharedCheck_77_;
goto v_resetjp_69_;
}
v_resetjp_69_:
{
lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_75_; 
v___x_72_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVRefl(v___x_52_, v_snd_55_);
v___x_73_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_73_, 0, v_val_68_);
lean_ctor_set(v___x_73_, 1, v___x_72_);
if (v_isShared_71_ == 0)
{
lean_ctor_set(v___x_70_, 0, v___x_73_);
v___x_75_ = v___x_70_;
goto v_reusejp_74_;
}
else
{
lean_object* v_reuseFailAlloc_76_; 
v_reuseFailAlloc_76_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_76_, 0, v___x_73_);
v___x_75_ = v_reuseFailAlloc_76_;
goto v_reusejp_74_;
}
v_reusejp_74_:
{
return v___x_75_;
}
}
}
else
{
lean_object* v_val_78_; lean_object* v_val_79_; lean_object* v___x_81_; uint8_t v_isShared_82_; uint8_t v_isSharedCheck_87_; 
lean_dec_ref(v_snd_55_);
lean_dec(v___x_52_);
v_val_78_ = lean_ctor_get(v_fproof_54_, 0);
lean_inc(v_val_78_);
lean_dec_ref_known(v_fproof_54_, 1);
v_val_79_ = lean_ctor_get(v_sproof_56_, 0);
v_isSharedCheck_87_ = !lean_is_exclusive(v_sproof_56_);
if (v_isSharedCheck_87_ == 0)
{
v___x_81_ = v_sproof_56_;
v_isShared_82_ = v_isSharedCheck_87_;
goto v_resetjp_80_;
}
else
{
lean_inc(v_val_79_);
lean_dec(v_sproof_56_);
v___x_81_ = lean_box(0);
v_isShared_82_ = v_isSharedCheck_87_;
goto v_resetjp_80_;
}
v_resetjp_80_:
{
lean_object* v___x_83_; lean_object* v___x_85_; 
v___x_83_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_83_, 0, v_val_78_);
lean_ctor_set(v___x_83_, 1, v_val_79_);
if (v_isShared_82_ == 0)
{
lean_ctor_set(v___x_81_, 0, v___x_83_);
v___x_85_ = v___x_81_;
goto v_reusejp_84_;
}
else
{
lean_object* v_reuseFailAlloc_86_; 
v_reuseFailAlloc_86_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_86_, 0, v___x_83_);
v___x_85_ = v_reuseFailAlloc_86_;
goto v_reusejp_84_;
}
v_reusejp_84_:
{
return v___x_85_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryCongrProof(lean_object* v_lhs_88_, lean_object* v_rhs_89_, lean_object* v_lhsExpr_90_, lean_object* v_rhsExpr_91_, lean_object* v_congrThm_92_, lean_object* v_a_93_, lean_object* v_a_94_, lean_object* v_a_95_, lean_object* v_a_96_, lean_object* v_a_97_, lean_object* v_a_98_, lean_object* v_a_99_, lean_object* v_a_100_){
_start:
{
lean_object* v_width_102_; lean_object* v_expr_103_; lean_object* v___x_104_; 
v_width_102_ = lean_ctor_get(v_lhs_88_, 0);
lean_inc_n(v_width_102_, 2);
v_expr_103_ = lean_ctor_get(v_lhs_88_, 4);
lean_inc_ref(v_expr_103_);
v___x_104_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkEvalExpr(v_width_102_, v_expr_103_, v_a_93_, v_a_94_, v_a_95_, v_a_96_, v_a_97_, v_a_98_, v_a_99_, v_a_100_);
if (lean_obj_tag(v___x_104_) == 0)
{
lean_object* v_a_105_; lean_object* v_width_106_; lean_object* v_expr_107_; lean_object* v___x_108_; 
v_a_105_ = lean_ctor_get(v___x_104_, 0);
lean_inc(v_a_105_);
lean_dec_ref_known(v___x_104_, 1);
v_width_106_ = lean_ctor_get(v_rhs_89_, 0);
v_expr_107_ = lean_ctor_get(v_rhs_89_, 4);
lean_inc_ref(v_expr_107_);
lean_inc(v_width_106_);
v___x_108_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkEvalExpr(v_width_106_, v_expr_107_, v_a_93_, v_a_94_, v_a_95_, v_a_96_, v_a_97_, v_a_98_, v_a_99_, v_a_100_);
if (lean_obj_tag(v___x_108_) == 0)
{
lean_object* v_a_109_; lean_object* v___x_110_; 
v_a_109_ = lean_ctor_get(v___x_108_, 0);
lean_inc(v_a_109_);
lean_dec_ref_known(v___x_108_, 1);
v___x_110_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms(v_lhs_88_, v_a_93_, v_a_94_, v_a_95_, v_a_96_, v_a_97_, v_a_98_, v_a_99_, v_a_100_);
if (lean_obj_tag(v___x_110_) == 0)
{
lean_object* v_a_111_; lean_object* v___x_112_; 
v_a_111_ = lean_ctor_get(v___x_110_, 0);
lean_inc(v_a_111_);
lean_dec_ref_known(v___x_110_, 1);
v___x_112_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms(v_rhs_89_, v_a_93_, v_a_94_, v_a_95_, v_a_96_, v_a_97_, v_a_98_, v_a_99_, v_a_100_);
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
v___x_117_ = l_Lean_Meta_Tactic_BVDecide_M_simplifyBinaryProof_x27___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryCongrProof_spec__0(v_width_102_, v_a_105_, v_a_111_, v_a_109_, v_a_113_);
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
v___x_124_ = l_Lean_mkApp6(v_congrThm_92_, v_lhsExpr_90_, v_rhsExpr_91_, v_a_105_, v_a_109_, v_fst_122_, v_snd_123_);
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
lean_dec_ref(v_congrThm_92_);
lean_dec_ref(v_rhsExpr_91_);
lean_dec_ref(v_lhsExpr_90_);
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
lean_dec_ref(v_congrThm_92_);
lean_dec_ref(v_rhsExpr_91_);
lean_dec_ref(v_lhsExpr_90_);
return v___x_112_;
}
}
else
{
lean_dec(v_a_109_);
lean_dec(v_a_105_);
lean_dec(v_width_102_);
lean_dec_ref(v_congrThm_92_);
lean_dec_ref(v_rhsExpr_91_);
lean_dec_ref(v_lhsExpr_90_);
lean_dec_ref(v_rhs_89_);
return v___x_110_;
}
}
else
{
lean_object* v_a_137_; lean_object* v___x_139_; uint8_t v_isShared_140_; uint8_t v_isSharedCheck_144_; 
lean_dec(v_a_105_);
lean_dec(v_width_102_);
lean_dec_ref(v_congrThm_92_);
lean_dec_ref(v_rhsExpr_91_);
lean_dec_ref(v_lhsExpr_90_);
lean_dec_ref(v_rhs_89_);
lean_dec_ref(v_lhs_88_);
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
lean_dec_ref(v_congrThm_92_);
lean_dec_ref(v_rhsExpr_91_);
lean_dec_ref(v_lhsExpr_90_);
lean_dec_ref(v_rhs_89_);
lean_dec_ref(v_lhs_88_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryCongrProof___boxed(lean_object* v_lhs_153_, lean_object* v_rhs_154_, lean_object* v_lhsExpr_155_, lean_object* v_rhsExpr_156_, lean_object* v_congrThm_157_, lean_object* v_a_158_, lean_object* v_a_159_, lean_object* v_a_160_, lean_object* v_a_161_, lean_object* v_a_162_, lean_object* v_a_163_, lean_object* v_a_164_, lean_object* v_a_165_, lean_object* v_a_166_){
_start:
{
lean_object* v_res_167_; 
v_res_167_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryCongrProof(v_lhs_153_, v_rhs_154_, v_lhsExpr_155_, v_rhsExpr_156_, v_congrThm_157_, v_a_158_, v_a_159_, v_a_160_, v_a_161_, v_a_162_, v_a_163_, v_a_164_, v_a_165_);
lean_dec(v_a_165_);
lean_dec_ref(v_a_164_);
lean_dec(v_a_163_);
lean_dec_ref(v_a_162_);
lean_dec(v_a_161_);
lean_dec_ref(v_a_160_);
lean_dec(v_a_159_);
lean_dec_ref(v_a_158_);
return v_res_167_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryCongrProof(lean_object* v_inner_168_, lean_object* v_innerExpr_169_, lean_object* v_congrProof_170_, lean_object* v_a_171_, lean_object* v_a_172_, lean_object* v_a_173_, lean_object* v_a_174_, lean_object* v_a_175_, lean_object* v_a_176_, lean_object* v_a_177_, lean_object* v_a_178_){
_start:
{
lean_object* v_width_180_; lean_object* v_expr_181_; lean_object* v___x_182_; 
v_width_180_ = lean_ctor_get(v_inner_168_, 0);
lean_inc_n(v_width_180_, 2);
v_expr_181_ = lean_ctor_get(v_inner_168_, 4);
lean_inc_ref(v_expr_181_);
v___x_182_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkEvalExpr(v_width_180_, v_expr_181_, v_a_171_, v_a_172_, v_a_173_, v_a_174_, v_a_175_, v_a_176_, v_a_177_, v_a_178_);
if (lean_obj_tag(v___x_182_) == 0)
{
lean_object* v_a_183_; lean_object* v___x_184_; 
v_a_183_ = lean_ctor_get(v___x_182_, 0);
lean_inc(v_a_183_);
lean_dec_ref_known(v___x_182_, 1);
v___x_184_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms(v_inner_168_, v_a_171_, v_a_172_, v_a_173_, v_a_174_, v_a_175_, v_a_176_, v_a_177_, v_a_178_);
if (lean_obj_tag(v___x_184_) == 0)
{
lean_object* v_a_185_; lean_object* v___x_187_; uint8_t v_isShared_188_; uint8_t v_isSharedCheck_206_; 
v_a_185_ = lean_ctor_get(v___x_184_, 0);
v_isSharedCheck_206_ = !lean_is_exclusive(v___x_184_);
if (v_isSharedCheck_206_ == 0)
{
v___x_187_ = v___x_184_;
v_isShared_188_ = v_isSharedCheck_206_;
goto v_resetjp_186_;
}
else
{
lean_inc(v_a_185_);
lean_dec(v___x_184_);
v___x_187_ = lean_box(0);
v_isShared_188_ = v_isSharedCheck_206_;
goto v_resetjp_186_;
}
v_resetjp_186_:
{
if (lean_obj_tag(v_a_185_) == 1)
{
lean_object* v_val_189_; lean_object* v___x_191_; uint8_t v_isShared_192_; uint8_t v_isSharedCheck_201_; 
v_val_189_ = lean_ctor_get(v_a_185_, 0);
v_isSharedCheck_201_ = !lean_is_exclusive(v_a_185_);
if (v_isSharedCheck_201_ == 0)
{
v___x_191_ = v_a_185_;
v_isShared_192_ = v_isSharedCheck_201_;
goto v_resetjp_190_;
}
else
{
lean_inc(v_val_189_);
lean_dec(v_a_185_);
v___x_191_ = lean_box(0);
v_isShared_192_ = v_isSharedCheck_201_;
goto v_resetjp_190_;
}
v_resetjp_190_:
{
lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_196_; 
v___x_193_ = l_Lean_mkNatLit(v_width_180_);
v___x_194_ = l_Lean_mkApp4(v_congrProof_170_, v___x_193_, v_innerExpr_169_, v_a_183_, v_val_189_);
if (v_isShared_192_ == 0)
{
lean_ctor_set(v___x_191_, 0, v___x_194_);
v___x_196_ = v___x_191_;
goto v_reusejp_195_;
}
else
{
lean_object* v_reuseFailAlloc_200_; 
v_reuseFailAlloc_200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_200_, 0, v___x_194_);
v___x_196_ = v_reuseFailAlloc_200_;
goto v_reusejp_195_;
}
v_reusejp_195_:
{
lean_object* v___x_198_; 
if (v_isShared_188_ == 0)
{
lean_ctor_set(v___x_187_, 0, v___x_196_);
v___x_198_ = v___x_187_;
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
lean_object* v___x_202_; lean_object* v___x_204_; 
lean_dec(v_a_185_);
lean_dec(v_a_183_);
lean_dec(v_width_180_);
lean_dec_ref(v_congrProof_170_);
lean_dec_ref(v_innerExpr_169_);
v___x_202_ = lean_box(0);
if (v_isShared_188_ == 0)
{
lean_ctor_set(v___x_187_, 0, v___x_202_);
v___x_204_ = v___x_187_;
goto v_reusejp_203_;
}
else
{
lean_object* v_reuseFailAlloc_205_; 
v_reuseFailAlloc_205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_205_, 0, v___x_202_);
v___x_204_ = v_reuseFailAlloc_205_;
goto v_reusejp_203_;
}
v_reusejp_203_:
{
return v___x_204_;
}
}
}
}
else
{
lean_dec(v_a_183_);
lean_dec(v_width_180_);
lean_dec_ref(v_congrProof_170_);
lean_dec_ref(v_innerExpr_169_);
return v___x_184_;
}
}
else
{
lean_object* v_a_207_; lean_object* v___x_209_; uint8_t v_isShared_210_; uint8_t v_isSharedCheck_214_; 
lean_dec(v_width_180_);
lean_dec_ref(v_congrProof_170_);
lean_dec_ref(v_innerExpr_169_);
lean_dec_ref(v_inner_168_);
v_a_207_ = lean_ctor_get(v___x_182_, 0);
v_isSharedCheck_214_ = !lean_is_exclusive(v___x_182_);
if (v_isSharedCheck_214_ == 0)
{
v___x_209_ = v___x_182_;
v_isShared_210_ = v_isSharedCheck_214_;
goto v_resetjp_208_;
}
else
{
lean_inc(v_a_207_);
lean_dec(v___x_182_);
v___x_209_ = lean_box(0);
v_isShared_210_ = v_isSharedCheck_214_;
goto v_resetjp_208_;
}
v_resetjp_208_:
{
lean_object* v___x_212_; 
if (v_isShared_210_ == 0)
{
v___x_212_ = v___x_209_;
goto v_reusejp_211_;
}
else
{
lean_object* v_reuseFailAlloc_213_; 
v_reuseFailAlloc_213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_213_, 0, v_a_207_);
v___x_212_ = v_reuseFailAlloc_213_;
goto v_reusejp_211_;
}
v_reusejp_211_:
{
return v___x_212_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryCongrProof___boxed(lean_object* v_inner_215_, lean_object* v_innerExpr_216_, lean_object* v_congrProof_217_, lean_object* v_a_218_, lean_object* v_a_219_, lean_object* v_a_220_, lean_object* v_a_221_, lean_object* v_a_222_, lean_object* v_a_223_, lean_object* v_a_224_, lean_object* v_a_225_, lean_object* v_a_226_){
_start:
{
lean_object* v_res_227_; 
v_res_227_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryCongrProof(v_inner_215_, v_innerExpr_216_, v_congrProof_217_, v_a_218_, v_a_219_, v_a_220_, v_a_221_, v_a_222_, v_a_223_, v_a_224_, v_a_225_);
lean_dec(v_a_225_);
lean_dec_ref(v_a_224_);
lean_dec(v_a_223_);
lean_dec_ref(v_a_222_);
lean_dec(v_a_221_);
lean_dec_ref(v_a_220_);
lean_dec(v_a_219_);
lean_dec_ref(v_a_218_);
return v_res_227_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__12_spec__17___redArg(lean_object* v_a_228_, lean_object* v_x_229_){
_start:
{
if (lean_obj_tag(v_x_229_) == 0)
{
lean_object* v___x_230_; 
v___x_230_ = lean_box(0);
return v___x_230_;
}
else
{
lean_object* v_key_231_; lean_object* v_value_232_; lean_object* v_tail_233_; size_t v___x_234_; size_t v___x_235_; uint8_t v___x_236_; 
v_key_231_ = lean_ctor_get(v_x_229_, 0);
v_value_232_ = lean_ctor_get(v_x_229_, 1);
v_tail_233_ = lean_ctor_get(v_x_229_, 2);
v___x_234_ = lean_ptr_addr(v_key_231_);
v___x_235_ = lean_ptr_addr(v_a_228_);
v___x_236_ = lean_usize_dec_eq(v___x_234_, v___x_235_);
if (v___x_236_ == 0)
{
v_x_229_ = v_tail_233_;
goto _start;
}
else
{
lean_object* v___x_238_; 
lean_inc(v_value_232_);
v___x_238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_238_, 0, v_value_232_);
return v___x_238_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__12_spec__17___redArg___boxed(lean_object* v_a_239_, lean_object* v_x_240_){
_start:
{
lean_object* v_res_241_; 
v_res_241_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__12_spec__17___redArg(v_a_239_, v_x_240_);
lean_dec(v_x_240_);
lean_dec_ref(v_a_239_);
return v_res_241_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__12___redArg(lean_object* v_m_242_, lean_object* v_a_243_){
_start:
{
lean_object* v_buckets_244_; lean_object* v___x_245_; size_t v___x_246_; size_t v___x_247_; size_t v___x_248_; uint64_t v___x_249_; uint64_t v___x_250_; uint64_t v___x_251_; uint64_t v_fold_252_; uint64_t v___x_253_; uint64_t v___x_254_; uint64_t v___x_255_; size_t v___x_256_; size_t v___x_257_; size_t v___x_258_; size_t v___x_259_; size_t v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; 
v_buckets_244_ = lean_ctor_get(v_m_242_, 1);
v___x_245_ = lean_array_get_size(v_buckets_244_);
v___x_246_ = lean_ptr_addr(v_a_243_);
v___x_247_ = ((size_t)3ULL);
v___x_248_ = lean_usize_shift_right(v___x_246_, v___x_247_);
v___x_249_ = lean_usize_to_uint64(v___x_248_);
v___x_250_ = 32ULL;
v___x_251_ = lean_uint64_shift_right(v___x_249_, v___x_250_);
v_fold_252_ = lean_uint64_xor(v___x_249_, v___x_251_);
v___x_253_ = 16ULL;
v___x_254_ = lean_uint64_shift_right(v_fold_252_, v___x_253_);
v___x_255_ = lean_uint64_xor(v_fold_252_, v___x_254_);
v___x_256_ = lean_uint64_to_usize(v___x_255_);
v___x_257_ = lean_usize_of_nat(v___x_245_);
v___x_258_ = ((size_t)1ULL);
v___x_259_ = lean_usize_sub(v___x_257_, v___x_258_);
v___x_260_ = lean_usize_land(v___x_256_, v___x_259_);
v___x_261_ = lean_array_uget_borrowed(v_buckets_244_, v___x_260_);
v___x_262_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__12_spec__17___redArg(v_a_243_, v___x_261_);
return v___x_262_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__12___redArg___boxed(lean_object* v_m_263_, lean_object* v_a_264_){
_start:
{
lean_object* v_res_265_; 
v_res_265_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__12___redArg(v_m_263_, v_a_264_);
lean_dec_ref(v_a_264_);
lean_dec_ref(v_m_263_);
return v_res_265_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13_spec__20_spec__25_spec__26___redArg(lean_object* v_x_266_, lean_object* v_x_267_){
_start:
{
if (lean_obj_tag(v_x_267_) == 0)
{
return v_x_266_;
}
else
{
lean_object* v_key_268_; lean_object* v_value_269_; lean_object* v_tail_270_; lean_object* v___x_272_; uint8_t v_isShared_273_; uint8_t v_isSharedCheck_296_; 
v_key_268_ = lean_ctor_get(v_x_267_, 0);
v_value_269_ = lean_ctor_get(v_x_267_, 1);
v_tail_270_ = lean_ctor_get(v_x_267_, 2);
v_isSharedCheck_296_ = !lean_is_exclusive(v_x_267_);
if (v_isSharedCheck_296_ == 0)
{
v___x_272_ = v_x_267_;
v_isShared_273_ = v_isSharedCheck_296_;
goto v_resetjp_271_;
}
else
{
lean_inc(v_tail_270_);
lean_inc(v_value_269_);
lean_inc(v_key_268_);
lean_dec(v_x_267_);
v___x_272_ = lean_box(0);
v_isShared_273_ = v_isSharedCheck_296_;
goto v_resetjp_271_;
}
v_resetjp_271_:
{
lean_object* v___x_274_; size_t v___x_275_; size_t v___x_276_; size_t v___x_277_; uint64_t v___x_278_; uint64_t v___x_279_; uint64_t v___x_280_; uint64_t v_fold_281_; uint64_t v___x_282_; uint64_t v___x_283_; uint64_t v___x_284_; size_t v___x_285_; size_t v___x_286_; size_t v___x_287_; size_t v___x_288_; size_t v___x_289_; lean_object* v___x_290_; lean_object* v___x_292_; 
v___x_274_ = lean_array_get_size(v_x_266_);
v___x_275_ = lean_ptr_addr(v_key_268_);
v___x_276_ = ((size_t)3ULL);
v___x_277_ = lean_usize_shift_right(v___x_275_, v___x_276_);
v___x_278_ = lean_usize_to_uint64(v___x_277_);
v___x_279_ = 32ULL;
v___x_280_ = lean_uint64_shift_right(v___x_278_, v___x_279_);
v_fold_281_ = lean_uint64_xor(v___x_278_, v___x_280_);
v___x_282_ = 16ULL;
v___x_283_ = lean_uint64_shift_right(v_fold_281_, v___x_282_);
v___x_284_ = lean_uint64_xor(v_fold_281_, v___x_283_);
v___x_285_ = lean_uint64_to_usize(v___x_284_);
v___x_286_ = lean_usize_of_nat(v___x_274_);
v___x_287_ = ((size_t)1ULL);
v___x_288_ = lean_usize_sub(v___x_286_, v___x_287_);
v___x_289_ = lean_usize_land(v___x_285_, v___x_288_);
v___x_290_ = lean_array_uget_borrowed(v_x_266_, v___x_289_);
lean_inc(v___x_290_);
if (v_isShared_273_ == 0)
{
lean_ctor_set(v___x_272_, 2, v___x_290_);
v___x_292_ = v___x_272_;
goto v_reusejp_291_;
}
else
{
lean_object* v_reuseFailAlloc_295_; 
v_reuseFailAlloc_295_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_295_, 0, v_key_268_);
lean_ctor_set(v_reuseFailAlloc_295_, 1, v_value_269_);
lean_ctor_set(v_reuseFailAlloc_295_, 2, v___x_290_);
v___x_292_ = v_reuseFailAlloc_295_;
goto v_reusejp_291_;
}
v_reusejp_291_:
{
lean_object* v___x_293_; 
v___x_293_ = lean_array_uset(v_x_266_, v___x_289_, v___x_292_);
v_x_266_ = v___x_293_;
v_x_267_ = v_tail_270_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13_spec__20_spec__25___redArg(lean_object* v_i_297_, lean_object* v_source_298_, lean_object* v_target_299_){
_start:
{
lean_object* v___x_300_; uint8_t v___x_301_; 
v___x_300_ = lean_array_get_size(v_source_298_);
v___x_301_ = lean_nat_dec_lt(v_i_297_, v___x_300_);
if (v___x_301_ == 0)
{
lean_dec_ref(v_source_298_);
lean_dec(v_i_297_);
return v_target_299_;
}
else
{
lean_object* v_es_302_; lean_object* v___x_303_; lean_object* v_source_304_; lean_object* v_target_305_; lean_object* v___x_306_; lean_object* v___x_307_; 
v_es_302_ = lean_array_fget(v_source_298_, v_i_297_);
v___x_303_ = lean_box(0);
v_source_304_ = lean_array_fset(v_source_298_, v_i_297_, v___x_303_);
v_target_305_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13_spec__20_spec__25_spec__26___redArg(v_target_299_, v_es_302_);
v___x_306_ = lean_unsigned_to_nat(1u);
v___x_307_ = lean_nat_add(v_i_297_, v___x_306_);
lean_dec(v_i_297_);
v_i_297_ = v___x_307_;
v_source_298_ = v_source_304_;
v_target_299_ = v_target_305_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13_spec__20___redArg(lean_object* v_data_309_){
_start:
{
lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v_nbuckets_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; 
v___x_310_ = lean_array_get_size(v_data_309_);
v___x_311_ = lean_unsigned_to_nat(2u);
v_nbuckets_312_ = lean_nat_mul(v___x_310_, v___x_311_);
v___x_313_ = lean_unsigned_to_nat(0u);
v___x_314_ = lean_box(0);
v___x_315_ = lean_mk_array(v_nbuckets_312_, v___x_314_);
v___x_316_ = lean_array_propagate_mark(v_data_309_, v___x_315_);
v___x_317_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13_spec__20_spec__25___redArg(v___x_313_, v_data_309_, v___x_316_);
return v___x_317_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13_spec__21___redArg(lean_object* v_a_318_, lean_object* v_b_319_, lean_object* v_x_320_){
_start:
{
if (lean_obj_tag(v_x_320_) == 0)
{
lean_dec(v_b_319_);
lean_dec_ref(v_a_318_);
return v_x_320_;
}
else
{
lean_object* v_key_321_; lean_object* v_value_322_; lean_object* v_tail_323_; lean_object* v___x_325_; uint8_t v_isShared_326_; uint8_t v_isSharedCheck_337_; 
v_key_321_ = lean_ctor_get(v_x_320_, 0);
v_value_322_ = lean_ctor_get(v_x_320_, 1);
v_tail_323_ = lean_ctor_get(v_x_320_, 2);
v_isSharedCheck_337_ = !lean_is_exclusive(v_x_320_);
if (v_isSharedCheck_337_ == 0)
{
v___x_325_ = v_x_320_;
v_isShared_326_ = v_isSharedCheck_337_;
goto v_resetjp_324_;
}
else
{
lean_inc(v_tail_323_);
lean_inc(v_value_322_);
lean_inc(v_key_321_);
lean_dec(v_x_320_);
v___x_325_ = lean_box(0);
v_isShared_326_ = v_isSharedCheck_337_;
goto v_resetjp_324_;
}
v_resetjp_324_:
{
size_t v___x_327_; size_t v___x_328_; uint8_t v___x_329_; 
v___x_327_ = lean_ptr_addr(v_key_321_);
v___x_328_ = lean_ptr_addr(v_a_318_);
v___x_329_ = lean_usize_dec_eq(v___x_327_, v___x_328_);
if (v___x_329_ == 0)
{
lean_object* v___x_330_; lean_object* v___x_332_; 
v___x_330_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13_spec__21___redArg(v_a_318_, v_b_319_, v_tail_323_);
if (v_isShared_326_ == 0)
{
lean_ctor_set(v___x_325_, 2, v___x_330_);
v___x_332_ = v___x_325_;
goto v_reusejp_331_;
}
else
{
lean_object* v_reuseFailAlloc_333_; 
v_reuseFailAlloc_333_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_333_, 0, v_key_321_);
lean_ctor_set(v_reuseFailAlloc_333_, 1, v_value_322_);
lean_ctor_set(v_reuseFailAlloc_333_, 2, v___x_330_);
v___x_332_ = v_reuseFailAlloc_333_;
goto v_reusejp_331_;
}
v_reusejp_331_:
{
return v___x_332_;
}
}
else
{
lean_object* v___x_335_; 
lean_dec(v_value_322_);
lean_dec(v_key_321_);
if (v_isShared_326_ == 0)
{
lean_ctor_set(v___x_325_, 1, v_b_319_);
lean_ctor_set(v___x_325_, 0, v_a_318_);
v___x_335_ = v___x_325_;
goto v_reusejp_334_;
}
else
{
lean_object* v_reuseFailAlloc_336_; 
v_reuseFailAlloc_336_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_336_, 0, v_a_318_);
lean_ctor_set(v_reuseFailAlloc_336_, 1, v_b_319_);
lean_ctor_set(v_reuseFailAlloc_336_, 2, v_tail_323_);
v___x_335_ = v_reuseFailAlloc_336_;
goto v_reusejp_334_;
}
v_reusejp_334_:
{
return v___x_335_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13_spec__19___redArg(lean_object* v_a_338_, lean_object* v_x_339_){
_start:
{
if (lean_obj_tag(v_x_339_) == 0)
{
uint8_t v___x_340_; 
v___x_340_ = 0;
return v___x_340_;
}
else
{
lean_object* v_key_341_; lean_object* v_tail_342_; size_t v___x_343_; size_t v___x_344_; uint8_t v___x_345_; 
v_key_341_ = lean_ctor_get(v_x_339_, 0);
v_tail_342_ = lean_ctor_get(v_x_339_, 2);
v___x_343_ = lean_ptr_addr(v_key_341_);
v___x_344_ = lean_ptr_addr(v_a_338_);
v___x_345_ = lean_usize_dec_eq(v___x_343_, v___x_344_);
if (v___x_345_ == 0)
{
v_x_339_ = v_tail_342_;
goto _start;
}
else
{
return v___x_345_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13_spec__19___redArg___boxed(lean_object* v_a_347_, lean_object* v_x_348_){
_start:
{
uint8_t v_res_349_; lean_object* v_r_350_; 
v_res_349_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13_spec__19___redArg(v_a_347_, v_x_348_);
lean_dec(v_x_348_);
lean_dec_ref(v_a_347_);
v_r_350_ = lean_box(v_res_349_);
return v_r_350_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13___redArg(lean_object* v_m_351_, lean_object* v_a_352_, lean_object* v_b_353_){
_start:
{
lean_object* v_size_354_; lean_object* v_buckets_355_; lean_object* v___x_357_; uint8_t v_isShared_358_; uint8_t v_isSharedCheck_401_; 
v_size_354_ = lean_ctor_get(v_m_351_, 0);
v_buckets_355_ = lean_ctor_get(v_m_351_, 1);
v_isSharedCheck_401_ = !lean_is_exclusive(v_m_351_);
if (v_isSharedCheck_401_ == 0)
{
v___x_357_ = v_m_351_;
v_isShared_358_ = v_isSharedCheck_401_;
goto v_resetjp_356_;
}
else
{
lean_inc(v_buckets_355_);
lean_inc(v_size_354_);
lean_dec(v_m_351_);
v___x_357_ = lean_box(0);
v_isShared_358_ = v_isSharedCheck_401_;
goto v_resetjp_356_;
}
v_resetjp_356_:
{
lean_object* v___x_359_; size_t v___x_360_; size_t v___x_361_; size_t v___x_362_; uint64_t v___x_363_; uint64_t v___x_364_; uint64_t v___x_365_; uint64_t v_fold_366_; uint64_t v___x_367_; uint64_t v___x_368_; uint64_t v___x_369_; size_t v___x_370_; size_t v___x_371_; size_t v___x_372_; size_t v___x_373_; size_t v___x_374_; lean_object* v_bkt_375_; uint8_t v___x_376_; 
v___x_359_ = lean_array_get_size(v_buckets_355_);
v___x_360_ = lean_ptr_addr(v_a_352_);
v___x_361_ = ((size_t)3ULL);
v___x_362_ = lean_usize_shift_right(v___x_360_, v___x_361_);
v___x_363_ = lean_usize_to_uint64(v___x_362_);
v___x_364_ = 32ULL;
v___x_365_ = lean_uint64_shift_right(v___x_363_, v___x_364_);
v_fold_366_ = lean_uint64_xor(v___x_363_, v___x_365_);
v___x_367_ = 16ULL;
v___x_368_ = lean_uint64_shift_right(v_fold_366_, v___x_367_);
v___x_369_ = lean_uint64_xor(v_fold_366_, v___x_368_);
v___x_370_ = lean_uint64_to_usize(v___x_369_);
v___x_371_ = lean_usize_of_nat(v___x_359_);
v___x_372_ = ((size_t)1ULL);
v___x_373_ = lean_usize_sub(v___x_371_, v___x_372_);
v___x_374_ = lean_usize_land(v___x_370_, v___x_373_);
v_bkt_375_ = lean_array_uget_borrowed(v_buckets_355_, v___x_374_);
v___x_376_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13_spec__19___redArg(v_a_352_, v_bkt_375_);
if (v___x_376_ == 0)
{
lean_object* v___x_377_; lean_object* v_size_x27_378_; lean_object* v___x_379_; lean_object* v_buckets_x27_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; uint8_t v___x_386_; 
v___x_377_ = lean_unsigned_to_nat(1u);
v_size_x27_378_ = lean_nat_add(v_size_354_, v___x_377_);
lean_dec(v_size_354_);
lean_inc(v_bkt_375_);
v___x_379_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_379_, 0, v_a_352_);
lean_ctor_set(v___x_379_, 1, v_b_353_);
lean_ctor_set(v___x_379_, 2, v_bkt_375_);
v_buckets_x27_380_ = lean_array_uset(v_buckets_355_, v___x_374_, v___x_379_);
v___x_381_ = lean_unsigned_to_nat(4u);
v___x_382_ = lean_nat_mul(v_size_x27_378_, v___x_381_);
v___x_383_ = lean_unsigned_to_nat(3u);
v___x_384_ = lean_nat_div(v___x_382_, v___x_383_);
lean_dec(v___x_382_);
v___x_385_ = lean_array_get_size(v_buckets_x27_380_);
v___x_386_ = lean_nat_dec_le(v___x_384_, v___x_385_);
lean_dec(v___x_384_);
if (v___x_386_ == 0)
{
lean_object* v_val_387_; lean_object* v___x_389_; 
v_val_387_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13_spec__20___redArg(v_buckets_x27_380_);
if (v_isShared_358_ == 0)
{
lean_ctor_set(v___x_357_, 1, v_val_387_);
lean_ctor_set(v___x_357_, 0, v_size_x27_378_);
v___x_389_ = v___x_357_;
goto v_reusejp_388_;
}
else
{
lean_object* v_reuseFailAlloc_390_; 
v_reuseFailAlloc_390_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_390_, 0, v_size_x27_378_);
lean_ctor_set(v_reuseFailAlloc_390_, 1, v_val_387_);
v___x_389_ = v_reuseFailAlloc_390_;
goto v_reusejp_388_;
}
v_reusejp_388_:
{
return v___x_389_;
}
}
else
{
lean_object* v___x_392_; 
if (v_isShared_358_ == 0)
{
lean_ctor_set(v___x_357_, 1, v_buckets_x27_380_);
lean_ctor_set(v___x_357_, 0, v_size_x27_378_);
v___x_392_ = v___x_357_;
goto v_reusejp_391_;
}
else
{
lean_object* v_reuseFailAlloc_393_; 
v_reuseFailAlloc_393_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_393_, 0, v_size_x27_378_);
lean_ctor_set(v_reuseFailAlloc_393_, 1, v_buckets_x27_380_);
v___x_392_ = v_reuseFailAlloc_393_;
goto v_reusejp_391_;
}
v_reusejp_391_:
{
return v___x_392_;
}
}
}
else
{
lean_object* v___x_394_; lean_object* v_buckets_x27_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_399_; 
lean_inc(v_bkt_375_);
v___x_394_ = lean_box(0);
v_buckets_x27_395_ = lean_array_uset(v_buckets_355_, v___x_374_, v___x_394_);
v___x_396_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13_spec__21___redArg(v_a_352_, v_b_353_, v_bkt_375_);
v___x_397_ = lean_array_uset(v_buckets_x27_395_, v___x_374_, v___x_396_);
if (v_isShared_358_ == 0)
{
lean_ctor_set(v___x_357_, 1, v___x_397_);
v___x_399_ = v___x_357_;
goto v_reusejp_398_;
}
else
{
lean_object* v_reuseFailAlloc_400_; 
v_reuseFailAlloc_400_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_400_, 0, v_size_354_);
lean_ctor_set(v_reuseFailAlloc_400_, 1, v___x_397_);
v___x_399_ = v_reuseFailAlloc_400_;
goto v_reusejp_398_;
}
v_reusejp_398_:
{
return v___x_399_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__0(lean_object* v_n_402_){
_start:
{
lean_object* v___x_403_; 
v___x_403_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_403_, 0, v_n_402_);
return v___x_403_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__4(lean_object* v_width_406_, lean_object* v_expr_407_, lean_object* v_val_408_, lean_object* v___x_409_, lean_object* v___x_410_, lean_object* v___x_411_, lean_object* v___x_412_, lean_object* v___x_413_, lean_object* v_arg_414_, lean_object* v_arg_415_, lean_object* v___x_416_, lean_object* v_arg_417_, lean_object* v___y_418_, lean_object* v___y_419_, lean_object* v___y_420_, lean_object* v___y_421_, lean_object* v___y_422_, lean_object* v___y_423_, lean_object* v___y_424_, lean_object* v___y_425_){
_start:
{
lean_object* v___x_427_; 
v___x_427_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkEvalExpr(v_width_406_, v_expr_407_, v___y_418_, v___y_419_, v___y_420_, v___y_421_, v___y_422_, v___y_423_, v___y_424_, v___y_425_);
if (lean_obj_tag(v___x_427_) == 0)
{
lean_object* v_a_428_; lean_object* v___x_429_; 
v_a_428_ = lean_ctor_get(v___x_427_, 0);
lean_inc(v_a_428_);
lean_dec_ref_known(v___x_427_, 1);
v___x_429_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms(v_val_408_, v___y_418_, v___y_419_, v___y_420_, v___y_421_, v___y_422_, v___y_423_, v___y_424_, v___y_425_);
if (lean_obj_tag(v___x_429_) == 0)
{
lean_object* v_a_430_; lean_object* v___x_432_; uint8_t v_isShared_433_; uint8_t v_isSharedCheck_454_; 
v_a_430_ = lean_ctor_get(v___x_429_, 0);
v_isSharedCheck_454_ = !lean_is_exclusive(v___x_429_);
if (v_isSharedCheck_454_ == 0)
{
v___x_432_ = v___x_429_;
v_isShared_433_ = v_isSharedCheck_454_;
goto v_resetjp_431_;
}
else
{
lean_inc(v_a_430_);
lean_dec(v___x_429_);
v___x_432_ = lean_box(0);
v_isShared_433_ = v_isSharedCheck_454_;
goto v_resetjp_431_;
}
v_resetjp_431_:
{
if (lean_obj_tag(v_a_430_) == 1)
{
lean_object* v_val_434_; lean_object* v___x_436_; uint8_t v_isShared_437_; uint8_t v_isSharedCheck_449_; 
v_val_434_ = lean_ctor_get(v_a_430_, 0);
v_isSharedCheck_449_ = !lean_is_exclusive(v_a_430_);
if (v_isSharedCheck_449_ == 0)
{
v___x_436_ = v_a_430_;
v_isShared_437_ = v_isSharedCheck_449_;
goto v_resetjp_435_;
}
else
{
lean_inc(v_val_434_);
lean_dec(v_a_430_);
v___x_436_ = lean_box(0);
v_isShared_437_ = v_isSharedCheck_449_;
goto v_resetjp_435_;
}
v_resetjp_435_:
{
lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_444_; 
v___x_438_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__4___closed__0));
v___x_439_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__4___closed__1));
v___x_440_ = l_Lean_Name_mkStr6(v___x_409_, v___x_410_, v___x_411_, v___x_438_, v___x_412_, v___x_439_);
v___x_441_ = l_Lean_mkConst(v___x_440_, v___x_413_);
v___x_442_ = l_Lean_mkApp6(v___x_441_, v_arg_414_, v_arg_415_, v___x_416_, v_arg_417_, v_a_428_, v_val_434_);
if (v_isShared_437_ == 0)
{
lean_ctor_set(v___x_436_, 0, v___x_442_);
v___x_444_ = v___x_436_;
goto v_reusejp_443_;
}
else
{
lean_object* v_reuseFailAlloc_448_; 
v_reuseFailAlloc_448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_448_, 0, v___x_442_);
v___x_444_ = v_reuseFailAlloc_448_;
goto v_reusejp_443_;
}
v_reusejp_443_:
{
lean_object* v___x_446_; 
if (v_isShared_433_ == 0)
{
lean_ctor_set(v___x_432_, 0, v___x_444_);
v___x_446_ = v___x_432_;
goto v_reusejp_445_;
}
else
{
lean_object* v_reuseFailAlloc_447_; 
v_reuseFailAlloc_447_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_447_, 0, v___x_444_);
v___x_446_ = v_reuseFailAlloc_447_;
goto v_reusejp_445_;
}
v_reusejp_445_:
{
return v___x_446_;
}
}
}
}
else
{
lean_object* v___x_450_; lean_object* v___x_452_; 
lean_dec(v_a_430_);
lean_dec(v_a_428_);
lean_dec_ref(v_arg_417_);
lean_dec_ref(v___x_416_);
lean_dec_ref(v_arg_415_);
lean_dec_ref(v_arg_414_);
lean_dec(v___x_413_);
lean_dec_ref(v___x_412_);
lean_dec_ref(v___x_411_);
lean_dec_ref(v___x_410_);
lean_dec_ref(v___x_409_);
v___x_450_ = lean_box(0);
if (v_isShared_433_ == 0)
{
lean_ctor_set(v___x_432_, 0, v___x_450_);
v___x_452_ = v___x_432_;
goto v_reusejp_451_;
}
else
{
lean_object* v_reuseFailAlloc_453_; 
v_reuseFailAlloc_453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_453_, 0, v___x_450_);
v___x_452_ = v_reuseFailAlloc_453_;
goto v_reusejp_451_;
}
v_reusejp_451_:
{
return v___x_452_;
}
}
}
}
else
{
lean_dec(v_a_428_);
lean_dec_ref(v_arg_417_);
lean_dec_ref(v___x_416_);
lean_dec_ref(v_arg_415_);
lean_dec_ref(v_arg_414_);
lean_dec(v___x_413_);
lean_dec_ref(v___x_412_);
lean_dec_ref(v___x_411_);
lean_dec_ref(v___x_410_);
lean_dec_ref(v___x_409_);
return v___x_429_;
}
}
else
{
lean_object* v_a_455_; lean_object* v___x_457_; uint8_t v_isShared_458_; uint8_t v_isSharedCheck_462_; 
lean_dec_ref(v_arg_417_);
lean_dec_ref(v___x_416_);
lean_dec_ref(v_arg_415_);
lean_dec_ref(v_arg_414_);
lean_dec(v___x_413_);
lean_dec_ref(v___x_412_);
lean_dec_ref(v___x_411_);
lean_dec_ref(v___x_410_);
lean_dec_ref(v___x_409_);
lean_dec_ref(v_val_408_);
v_a_455_ = lean_ctor_get(v___x_427_, 0);
v_isSharedCheck_462_ = !lean_is_exclusive(v___x_427_);
if (v_isSharedCheck_462_ == 0)
{
v___x_457_ = v___x_427_;
v_isShared_458_ = v_isSharedCheck_462_;
goto v_resetjp_456_;
}
else
{
lean_inc(v_a_455_);
lean_dec(v___x_427_);
v___x_457_ = lean_box(0);
v_isShared_458_ = v_isSharedCheck_462_;
goto v_resetjp_456_;
}
v_resetjp_456_:
{
lean_object* v___x_460_; 
if (v_isShared_458_ == 0)
{
v___x_460_ = v___x_457_;
goto v_reusejp_459_;
}
else
{
lean_object* v_reuseFailAlloc_461_; 
v_reuseFailAlloc_461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_461_, 0, v_a_455_);
v___x_460_ = v_reuseFailAlloc_461_;
goto v_reusejp_459_;
}
v_reusejp_459_:
{
return v___x_460_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__4___boxed(lean_object** _args){
lean_object* v_width_463_ = _args[0];
lean_object* v_expr_464_ = _args[1];
lean_object* v_val_465_ = _args[2];
lean_object* v___x_466_ = _args[3];
lean_object* v___x_467_ = _args[4];
lean_object* v___x_468_ = _args[5];
lean_object* v___x_469_ = _args[6];
lean_object* v___x_470_ = _args[7];
lean_object* v_arg_471_ = _args[8];
lean_object* v_arg_472_ = _args[9];
lean_object* v___x_473_ = _args[10];
lean_object* v_arg_474_ = _args[11];
lean_object* v___y_475_ = _args[12];
lean_object* v___y_476_ = _args[13];
lean_object* v___y_477_ = _args[14];
lean_object* v___y_478_ = _args[15];
lean_object* v___y_479_ = _args[16];
lean_object* v___y_480_ = _args[17];
lean_object* v___y_481_ = _args[18];
lean_object* v___y_482_ = _args[19];
lean_object* v___y_483_ = _args[20];
_start:
{
lean_object* v_res_484_; 
v_res_484_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__4(v_width_463_, v_expr_464_, v_val_465_, v___x_466_, v___x_467_, v___x_468_, v___x_469_, v___x_470_, v_arg_471_, v_arg_472_, v___x_473_, v_arg_474_, v___y_475_, v___y_476_, v___y_477_, v___y_478_, v___y_479_, v___y_480_, v___y_481_, v___y_482_);
lean_dec(v___y_482_);
lean_dec_ref(v___y_481_);
lean_dec(v___y_480_);
lean_dec_ref(v___y_479_);
lean_dec(v___y_478_);
lean_dec_ref(v___y_477_);
lean_dec(v___y_476_);
lean_dec_ref(v___y_475_);
return v_res_484_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__5(lean_object* v_width_486_, lean_object* v_expr_487_, lean_object* v_val_488_, lean_object* v___x_489_, lean_object* v___x_490_, lean_object* v___x_491_, lean_object* v___x_492_, lean_object* v___x_493_, lean_object* v___x_494_, lean_object* v___x_495_, lean_object* v_arg_496_, lean_object* v___y_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_){
_start:
{
lean_object* v___x_506_; 
v___x_506_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkEvalExpr(v_width_486_, v_expr_487_, v___y_497_, v___y_498_, v___y_499_, v___y_500_, v___y_501_, v___y_502_, v___y_503_, v___y_504_);
if (lean_obj_tag(v___x_506_) == 0)
{
lean_object* v_a_507_; lean_object* v___x_508_; 
v_a_507_ = lean_ctor_get(v___x_506_, 0);
lean_inc(v_a_507_);
lean_dec_ref_known(v___x_506_, 1);
v___x_508_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms(v_val_488_, v___y_497_, v___y_498_, v___y_499_, v___y_500_, v___y_501_, v___y_502_, v___y_503_, v___y_504_);
if (lean_obj_tag(v___x_508_) == 0)
{
lean_object* v_a_509_; lean_object* v___x_511_; uint8_t v_isShared_512_; uint8_t v_isSharedCheck_533_; 
v_a_509_ = lean_ctor_get(v___x_508_, 0);
v_isSharedCheck_533_ = !lean_is_exclusive(v___x_508_);
if (v_isSharedCheck_533_ == 0)
{
v___x_511_ = v___x_508_;
v_isShared_512_ = v_isSharedCheck_533_;
goto v_resetjp_510_;
}
else
{
lean_inc(v_a_509_);
lean_dec(v___x_508_);
v___x_511_ = lean_box(0);
v_isShared_512_ = v_isSharedCheck_533_;
goto v_resetjp_510_;
}
v_resetjp_510_:
{
if (lean_obj_tag(v_a_509_) == 1)
{
lean_object* v_val_513_; lean_object* v___x_515_; uint8_t v_isShared_516_; uint8_t v_isSharedCheck_528_; 
v_val_513_ = lean_ctor_get(v_a_509_, 0);
v_isSharedCheck_528_ = !lean_is_exclusive(v_a_509_);
if (v_isSharedCheck_528_ == 0)
{
v___x_515_ = v_a_509_;
v_isShared_516_ = v_isSharedCheck_528_;
goto v_resetjp_514_;
}
else
{
lean_inc(v_val_513_);
lean_dec(v_a_509_);
v___x_515_ = lean_box(0);
v_isShared_516_ = v_isSharedCheck_528_;
goto v_resetjp_514_;
}
v_resetjp_514_:
{
lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_523_; 
v___x_517_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__4___closed__0));
v___x_518_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__5___closed__0));
v___x_519_ = l_Lean_Name_mkStr6(v___x_489_, v___x_490_, v___x_491_, v___x_517_, v___x_492_, v___x_518_);
v___x_520_ = l_Lean_mkConst(v___x_519_, v___x_493_);
v___x_521_ = l_Lean_mkApp5(v___x_520_, v___x_494_, v___x_495_, v_arg_496_, v_a_507_, v_val_513_);
if (v_isShared_516_ == 0)
{
lean_ctor_set(v___x_515_, 0, v___x_521_);
v___x_523_ = v___x_515_;
goto v_reusejp_522_;
}
else
{
lean_object* v_reuseFailAlloc_527_; 
v_reuseFailAlloc_527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_527_, 0, v___x_521_);
v___x_523_ = v_reuseFailAlloc_527_;
goto v_reusejp_522_;
}
v_reusejp_522_:
{
lean_object* v___x_525_; 
if (v_isShared_512_ == 0)
{
lean_ctor_set(v___x_511_, 0, v___x_523_);
v___x_525_ = v___x_511_;
goto v_reusejp_524_;
}
else
{
lean_object* v_reuseFailAlloc_526_; 
v_reuseFailAlloc_526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_526_, 0, v___x_523_);
v___x_525_ = v_reuseFailAlloc_526_;
goto v_reusejp_524_;
}
v_reusejp_524_:
{
return v___x_525_;
}
}
}
}
else
{
lean_object* v___x_529_; lean_object* v___x_531_; 
lean_dec(v_a_509_);
lean_dec(v_a_507_);
lean_dec_ref(v_arg_496_);
lean_dec_ref(v___x_495_);
lean_dec_ref(v___x_494_);
lean_dec(v___x_493_);
lean_dec_ref(v___x_492_);
lean_dec_ref(v___x_491_);
lean_dec_ref(v___x_490_);
lean_dec_ref(v___x_489_);
v___x_529_ = lean_box(0);
if (v_isShared_512_ == 0)
{
lean_ctor_set(v___x_511_, 0, v___x_529_);
v___x_531_ = v___x_511_;
goto v_reusejp_530_;
}
else
{
lean_object* v_reuseFailAlloc_532_; 
v_reuseFailAlloc_532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_532_, 0, v___x_529_);
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
else
{
lean_dec(v_a_507_);
lean_dec_ref(v_arg_496_);
lean_dec_ref(v___x_495_);
lean_dec_ref(v___x_494_);
lean_dec(v___x_493_);
lean_dec_ref(v___x_492_);
lean_dec_ref(v___x_491_);
lean_dec_ref(v___x_490_);
lean_dec_ref(v___x_489_);
return v___x_508_;
}
}
else
{
lean_object* v_a_534_; lean_object* v___x_536_; uint8_t v_isShared_537_; uint8_t v_isSharedCheck_541_; 
lean_dec_ref(v_arg_496_);
lean_dec_ref(v___x_495_);
lean_dec_ref(v___x_494_);
lean_dec(v___x_493_);
lean_dec_ref(v___x_492_);
lean_dec_ref(v___x_491_);
lean_dec_ref(v___x_490_);
lean_dec_ref(v___x_489_);
lean_dec_ref(v_val_488_);
v_a_534_ = lean_ctor_get(v___x_506_, 0);
v_isSharedCheck_541_ = !lean_is_exclusive(v___x_506_);
if (v_isSharedCheck_541_ == 0)
{
v___x_536_ = v___x_506_;
v_isShared_537_ = v_isSharedCheck_541_;
goto v_resetjp_535_;
}
else
{
lean_inc(v_a_534_);
lean_dec(v___x_506_);
v___x_536_ = lean_box(0);
v_isShared_537_ = v_isSharedCheck_541_;
goto v_resetjp_535_;
}
v_resetjp_535_:
{
lean_object* v___x_539_; 
if (v_isShared_537_ == 0)
{
v___x_539_ = v___x_536_;
goto v_reusejp_538_;
}
else
{
lean_object* v_reuseFailAlloc_540_; 
v_reuseFailAlloc_540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_540_, 0, v_a_534_);
v___x_539_ = v_reuseFailAlloc_540_;
goto v_reusejp_538_;
}
v_reusejp_538_:
{
return v___x_539_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__5___boxed(lean_object** _args){
lean_object* v_width_542_ = _args[0];
lean_object* v_expr_543_ = _args[1];
lean_object* v_val_544_ = _args[2];
lean_object* v___x_545_ = _args[3];
lean_object* v___x_546_ = _args[4];
lean_object* v___x_547_ = _args[5];
lean_object* v___x_548_ = _args[6];
lean_object* v___x_549_ = _args[7];
lean_object* v___x_550_ = _args[8];
lean_object* v___x_551_ = _args[9];
lean_object* v_arg_552_ = _args[10];
lean_object* v___y_553_ = _args[11];
lean_object* v___y_554_ = _args[12];
lean_object* v___y_555_ = _args[13];
lean_object* v___y_556_ = _args[14];
lean_object* v___y_557_ = _args[15];
lean_object* v___y_558_ = _args[16];
lean_object* v___y_559_ = _args[17];
lean_object* v___y_560_ = _args[18];
lean_object* v___y_561_ = _args[19];
_start:
{
lean_object* v_res_562_; 
v_res_562_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__5(v_width_542_, v_expr_543_, v_val_544_, v___x_545_, v___x_546_, v___x_547_, v___x_548_, v___x_549_, v___x_550_, v___x_551_, v_arg_552_, v___y_553_, v___y_554_, v___y_555_, v___y_556_, v___y_557_, v___y_558_, v___y_559_, v___y_560_);
lean_dec(v___y_560_);
lean_dec_ref(v___y_559_);
lean_dec(v___y_558_);
lean_dec_ref(v___y_557_);
lean_dec(v___y_556_);
lean_dec_ref(v___y_555_);
lean_dec(v___y_554_);
lean_dec_ref(v___y_553_);
return v_res_562_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go_spec__12_spec__20(lean_object* v_msgData_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_){
_start:
{
lean_object* v___x_569_; lean_object* v_env_570_; lean_object* v___x_571_; lean_object* v_toCold_572_; lean_object* v_mctx_573_; lean_object* v_lctx_574_; lean_object* v_options_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; 
v___x_569_ = lean_st_ref_get(v___y_567_);
v_env_570_ = lean_ctor_get(v___x_569_, 0);
lean_inc_ref(v_env_570_);
lean_dec(v___x_569_);
v___x_571_ = lean_st_ref_get(v___y_565_);
v_toCold_572_ = lean_ctor_get(v___y_566_, 0);
v_mctx_573_ = lean_ctor_get(v___x_571_, 0);
lean_inc_ref(v_mctx_573_);
lean_dec(v___x_571_);
v_lctx_574_ = lean_ctor_get(v___y_564_, 2);
v_options_575_ = lean_ctor_get(v_toCold_572_, 2);
lean_inc_ref(v_options_575_);
lean_inc_ref(v_lctx_574_);
v___x_576_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_576_, 0, v_env_570_);
lean_ctor_set(v___x_576_, 1, v_mctx_573_);
lean_ctor_set(v___x_576_, 2, v_lctx_574_);
lean_ctor_set(v___x_576_, 3, v_options_575_);
v___x_577_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_577_, 0, v___x_576_);
lean_ctor_set(v___x_577_, 1, v_msgData_563_);
v___x_578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_578_, 0, v___x_577_);
return v___x_578_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go_spec__12_spec__20___boxed(lean_object* v_msgData_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_, lean_object* v___y_583_, lean_object* v___y_584_){
_start:
{
lean_object* v_res_585_; 
v_res_585_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go_spec__12_spec__20(v_msgData_579_, v___y_580_, v___y_581_, v___y_582_, v___y_583_);
lean_dec(v___y_583_);
lean_dec_ref(v___y_582_);
lean_dec(v___y_581_);
lean_dec_ref(v___y_580_);
return v_res_585_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go_spec__12___redArg(lean_object* v_msg_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_){
_start:
{
lean_object* v_ref_592_; lean_object* v___x_593_; lean_object* v_a_594_; lean_object* v___x_596_; uint8_t v_isShared_597_; uint8_t v_isSharedCheck_602_; 
v_ref_592_ = lean_ctor_get(v___y_589_, 2);
v___x_593_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go_spec__12_spec__20(v_msg_586_, v___y_587_, v___y_588_, v___y_589_, v___y_590_);
v_a_594_ = lean_ctor_get(v___x_593_, 0);
v_isSharedCheck_602_ = !lean_is_exclusive(v___x_593_);
if (v_isSharedCheck_602_ == 0)
{
v___x_596_ = v___x_593_;
v_isShared_597_ = v_isSharedCheck_602_;
goto v_resetjp_595_;
}
else
{
lean_inc(v_a_594_);
lean_dec(v___x_593_);
v___x_596_ = lean_box(0);
v_isShared_597_ = v_isSharedCheck_602_;
goto v_resetjp_595_;
}
v_resetjp_595_:
{
lean_object* v___x_598_; lean_object* v___x_600_; 
lean_inc(v_ref_592_);
v___x_598_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_598_, 0, v_ref_592_);
lean_ctor_set(v___x_598_, 1, v_a_594_);
if (v_isShared_597_ == 0)
{
lean_ctor_set_tag(v___x_596_, 1);
lean_ctor_set(v___x_596_, 0, v___x_598_);
v___x_600_ = v___x_596_;
goto v_reusejp_599_;
}
else
{
lean_object* v_reuseFailAlloc_601_; 
v_reuseFailAlloc_601_ = lean_alloc_ctor(1, 1, 0);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go_spec__12___redArg___boxed(lean_object* v_msg_603_, lean_object* v___y_604_, lean_object* v___y_605_, lean_object* v___y_606_, lean_object* v___y_607_, lean_object* v___y_608_){
_start:
{
lean_object* v_res_609_; 
v_res_609_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go_spec__12___redArg(v_msg_603_, v___y_604_, v___y_605_, v___y_606_, v___y_607_);
lean_dec(v___y_607_);
lean_dec_ref(v___y_606_);
lean_dec(v___y_605_);
lean_dec_ref(v___y_604_);
return v_res_609_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_M_simplifyBinaryProof_x27___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go_spec__13(lean_object* v___x_610_, lean_object* v___x_611_, lean_object* v_fst_612_, lean_object* v_fproof_613_, lean_object* v_snd_614_, lean_object* v_sproof_615_){
_start:
{
if (lean_obj_tag(v_fproof_613_) == 0)
{
lean_dec_ref(v_snd_614_);
lean_dec(v___x_611_);
if (lean_obj_tag(v_sproof_615_) == 0)
{
lean_object* v___x_616_; 
lean_dec_ref(v_fst_612_);
lean_dec(v___x_610_);
v___x_616_ = lean_box(0);
return v___x_616_;
}
else
{
lean_object* v_val_617_; lean_object* v___x_619_; uint8_t v_isShared_620_; uint8_t v_isSharedCheck_626_; 
v_val_617_ = lean_ctor_get(v_sproof_615_, 0);
v_isSharedCheck_626_ = !lean_is_exclusive(v_sproof_615_);
if (v_isSharedCheck_626_ == 0)
{
v___x_619_ = v_sproof_615_;
v_isShared_620_ = v_isSharedCheck_626_;
goto v_resetjp_618_;
}
else
{
lean_inc(v_val_617_);
lean_dec(v_sproof_615_);
v___x_619_ = lean_box(0);
v_isShared_620_ = v_isSharedCheck_626_;
goto v_resetjp_618_;
}
v_resetjp_618_:
{
lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_624_; 
v___x_621_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVRefl(v___x_610_, v_fst_612_);
v___x_622_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_622_, 0, v___x_621_);
lean_ctor_set(v___x_622_, 1, v_val_617_);
if (v_isShared_620_ == 0)
{
lean_ctor_set(v___x_619_, 0, v___x_622_);
v___x_624_ = v___x_619_;
goto v_reusejp_623_;
}
else
{
lean_object* v_reuseFailAlloc_625_; 
v_reuseFailAlloc_625_ = lean_alloc_ctor(1, 1, 0);
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
lean_dec_ref(v_fst_612_);
lean_dec(v___x_610_);
if (lean_obj_tag(v_sproof_615_) == 0)
{
lean_object* v_val_627_; lean_object* v___x_629_; uint8_t v_isShared_630_; uint8_t v_isSharedCheck_636_; 
v_val_627_ = lean_ctor_get(v_fproof_613_, 0);
v_isSharedCheck_636_ = !lean_is_exclusive(v_fproof_613_);
if (v_isSharedCheck_636_ == 0)
{
v___x_629_ = v_fproof_613_;
v_isShared_630_ = v_isSharedCheck_636_;
goto v_resetjp_628_;
}
else
{
lean_inc(v_val_627_);
lean_dec(v_fproof_613_);
v___x_629_ = lean_box(0);
v_isShared_630_ = v_isSharedCheck_636_;
goto v_resetjp_628_;
}
v_resetjp_628_:
{
lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_634_; 
v___x_631_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVRefl(v___x_611_, v_snd_614_);
v___x_632_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_632_, 0, v_val_627_);
lean_ctor_set(v___x_632_, 1, v___x_631_);
if (v_isShared_630_ == 0)
{
lean_ctor_set(v___x_629_, 0, v___x_632_);
v___x_634_ = v___x_629_;
goto v_reusejp_633_;
}
else
{
lean_object* v_reuseFailAlloc_635_; 
v_reuseFailAlloc_635_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_635_, 0, v___x_632_);
v___x_634_ = v_reuseFailAlloc_635_;
goto v_reusejp_633_;
}
v_reusejp_633_:
{
return v___x_634_;
}
}
}
else
{
lean_object* v_val_637_; lean_object* v_val_638_; lean_object* v___x_640_; uint8_t v_isShared_641_; uint8_t v_isSharedCheck_646_; 
lean_dec_ref(v_snd_614_);
lean_dec(v___x_611_);
v_val_637_ = lean_ctor_get(v_fproof_613_, 0);
lean_inc(v_val_637_);
lean_dec_ref_known(v_fproof_613_, 1);
v_val_638_ = lean_ctor_get(v_sproof_615_, 0);
v_isSharedCheck_646_ = !lean_is_exclusive(v_sproof_615_);
if (v_isSharedCheck_646_ == 0)
{
v___x_640_ = v_sproof_615_;
v_isShared_641_ = v_isSharedCheck_646_;
goto v_resetjp_639_;
}
else
{
lean_inc(v_val_638_);
lean_dec(v_sproof_615_);
v___x_640_ = lean_box(0);
v_isShared_641_ = v_isSharedCheck_646_;
goto v_resetjp_639_;
}
v_resetjp_639_:
{
lean_object* v___x_642_; lean_object* v___x_644_; 
v___x_642_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_642_, 0, v_val_637_);
lean_ctor_set(v___x_642_, 1, v_val_638_);
if (v_isShared_641_ == 0)
{
lean_ctor_set(v___x_640_, 0, v___x_642_);
v___x_644_ = v___x_640_;
goto v_reusejp_643_;
}
else
{
lean_object* v_reuseFailAlloc_645_; 
v_reuseFailAlloc_645_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_645_, 0, v___x_642_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__3(lean_object* v_width_648_, lean_object* v_expr_649_, lean_object* v_width_650_, lean_object* v_expr_651_, lean_object* v_val_652_, lean_object* v_val_653_, lean_object* v___x_654_, lean_object* v___x_655_, lean_object* v___x_656_, lean_object* v___x_657_, lean_object* v___x_658_, lean_object* v___x_659_, lean_object* v___x_660_, lean_object* v_arg_661_, lean_object* v_arg_662_, lean_object* v___y_663_, lean_object* v___y_664_, lean_object* v___y_665_, lean_object* v___y_666_, lean_object* v___y_667_, lean_object* v___y_668_, lean_object* v___y_669_, lean_object* v___y_670_){
_start:
{
lean_object* v___x_672_; 
lean_inc(v_width_648_);
v___x_672_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkEvalExpr(v_width_648_, v_expr_649_, v___y_663_, v___y_664_, v___y_665_, v___y_666_, v___y_667_, v___y_668_, v___y_669_, v___y_670_);
if (lean_obj_tag(v___x_672_) == 0)
{
lean_object* v_a_673_; lean_object* v___x_674_; 
v_a_673_ = lean_ctor_get(v___x_672_, 0);
lean_inc(v_a_673_);
lean_dec_ref_known(v___x_672_, 1);
lean_inc(v_width_650_);
v___x_674_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkEvalExpr(v_width_650_, v_expr_651_, v___y_663_, v___y_664_, v___y_665_, v___y_666_, v___y_667_, v___y_668_, v___y_669_, v___y_670_);
if (lean_obj_tag(v___x_674_) == 0)
{
lean_object* v_a_675_; lean_object* v___x_676_; 
v_a_675_ = lean_ctor_get(v___x_674_, 0);
lean_inc(v_a_675_);
lean_dec_ref_known(v___x_674_, 1);
v___x_676_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms(v_val_652_, v___y_663_, v___y_664_, v___y_665_, v___y_666_, v___y_667_, v___y_668_, v___y_669_, v___y_670_);
if (lean_obj_tag(v___x_676_) == 0)
{
lean_object* v_a_677_; lean_object* v___x_678_; 
v_a_677_ = lean_ctor_get(v___x_676_, 0);
lean_inc(v_a_677_);
lean_dec_ref_known(v___x_676_, 1);
v___x_678_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms(v_val_653_, v___y_663_, v___y_664_, v___y_665_, v___y_666_, v___y_667_, v___y_668_, v___y_669_, v___y_670_);
if (lean_obj_tag(v___x_678_) == 0)
{
lean_object* v_a_679_; lean_object* v___x_681_; uint8_t v_isShared_682_; uint8_t v_isSharedCheck_706_; 
v_a_679_ = lean_ctor_get(v___x_678_, 0);
v_isSharedCheck_706_ = !lean_is_exclusive(v___x_678_);
if (v_isSharedCheck_706_ == 0)
{
v___x_681_ = v___x_678_;
v_isShared_682_ = v_isSharedCheck_706_;
goto v_resetjp_680_;
}
else
{
lean_inc(v_a_679_);
lean_dec(v___x_678_);
v___x_681_ = lean_box(0);
v_isShared_682_ = v_isSharedCheck_706_;
goto v_resetjp_680_;
}
v_resetjp_680_:
{
lean_object* v___x_683_; 
lean_inc(v_a_675_);
lean_inc(v_a_673_);
v___x_683_ = l_Lean_Meta_Tactic_BVDecide_M_simplifyBinaryProof_x27___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go_spec__13(v_width_648_, v_width_650_, v_a_673_, v_a_677_, v_a_675_, v_a_679_);
if (lean_obj_tag(v___x_683_) == 1)
{
lean_object* v_val_684_; lean_object* v___x_686_; uint8_t v_isShared_687_; uint8_t v_isSharedCheck_701_; 
v_val_684_ = lean_ctor_get(v___x_683_, 0);
v_isSharedCheck_701_ = !lean_is_exclusive(v___x_683_);
if (v_isSharedCheck_701_ == 0)
{
v___x_686_ = v___x_683_;
v_isShared_687_ = v_isSharedCheck_701_;
goto v_resetjp_685_;
}
else
{
lean_inc(v_val_684_);
lean_dec(v___x_683_);
v___x_686_ = lean_box(0);
v_isShared_687_ = v_isSharedCheck_701_;
goto v_resetjp_685_;
}
v_resetjp_685_:
{
lean_object* v_fst_688_; lean_object* v_snd_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_696_; 
v_fst_688_ = lean_ctor_get(v_val_684_, 0);
lean_inc(v_fst_688_);
v_snd_689_ = lean_ctor_get(v_val_684_, 1);
lean_inc(v_snd_689_);
lean_dec(v_val_684_);
v___x_690_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__4___closed__0));
v___x_691_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__3___closed__0));
v___x_692_ = l_Lean_Name_mkStr6(v___x_654_, v___x_655_, v___x_656_, v___x_690_, v___x_657_, v___x_691_);
v___x_693_ = l_Lean_mkConst(v___x_692_, v___x_658_);
v___x_694_ = l_Lean_mkApp8(v___x_693_, v___x_659_, v___x_660_, v_arg_661_, v_a_673_, v_arg_662_, v_a_675_, v_fst_688_, v_snd_689_);
if (v_isShared_687_ == 0)
{
lean_ctor_set(v___x_686_, 0, v___x_694_);
v___x_696_ = v___x_686_;
goto v_reusejp_695_;
}
else
{
lean_object* v_reuseFailAlloc_700_; 
v_reuseFailAlloc_700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_700_, 0, v___x_694_);
v___x_696_ = v_reuseFailAlloc_700_;
goto v_reusejp_695_;
}
v_reusejp_695_:
{
lean_object* v___x_698_; 
if (v_isShared_682_ == 0)
{
lean_ctor_set(v___x_681_, 0, v___x_696_);
v___x_698_ = v___x_681_;
goto v_reusejp_697_;
}
else
{
lean_object* v_reuseFailAlloc_699_; 
v_reuseFailAlloc_699_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_699_, 0, v___x_696_);
v___x_698_ = v_reuseFailAlloc_699_;
goto v_reusejp_697_;
}
v_reusejp_697_:
{
return v___x_698_;
}
}
}
}
else
{
lean_object* v___x_702_; lean_object* v___x_704_; 
lean_dec(v___x_683_);
lean_dec(v_a_675_);
lean_dec(v_a_673_);
lean_dec_ref(v_arg_662_);
lean_dec_ref(v_arg_661_);
lean_dec_ref(v___x_660_);
lean_dec_ref(v___x_659_);
lean_dec(v___x_658_);
lean_dec_ref(v___x_657_);
lean_dec_ref(v___x_656_);
lean_dec_ref(v___x_655_);
lean_dec_ref(v___x_654_);
v___x_702_ = lean_box(0);
if (v_isShared_682_ == 0)
{
lean_ctor_set(v___x_681_, 0, v___x_702_);
v___x_704_ = v___x_681_;
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
}
else
{
lean_dec(v_a_677_);
lean_dec(v_a_675_);
lean_dec(v_a_673_);
lean_dec_ref(v_arg_662_);
lean_dec_ref(v_arg_661_);
lean_dec_ref(v___x_660_);
lean_dec_ref(v___x_659_);
lean_dec(v___x_658_);
lean_dec_ref(v___x_657_);
lean_dec_ref(v___x_656_);
lean_dec_ref(v___x_655_);
lean_dec_ref(v___x_654_);
lean_dec(v_width_650_);
lean_dec(v_width_648_);
return v___x_678_;
}
}
else
{
lean_dec(v_a_675_);
lean_dec(v_a_673_);
lean_dec_ref(v_arg_662_);
lean_dec_ref(v_arg_661_);
lean_dec_ref(v___x_660_);
lean_dec_ref(v___x_659_);
lean_dec(v___x_658_);
lean_dec_ref(v___x_657_);
lean_dec_ref(v___x_656_);
lean_dec_ref(v___x_655_);
lean_dec_ref(v___x_654_);
lean_dec_ref(v_val_653_);
lean_dec(v_width_650_);
lean_dec(v_width_648_);
return v___x_676_;
}
}
else
{
lean_object* v_a_707_; lean_object* v___x_709_; uint8_t v_isShared_710_; uint8_t v_isSharedCheck_714_; 
lean_dec(v_a_673_);
lean_dec_ref(v_arg_662_);
lean_dec_ref(v_arg_661_);
lean_dec_ref(v___x_660_);
lean_dec_ref(v___x_659_);
lean_dec(v___x_658_);
lean_dec_ref(v___x_657_);
lean_dec_ref(v___x_656_);
lean_dec_ref(v___x_655_);
lean_dec_ref(v___x_654_);
lean_dec_ref(v_val_653_);
lean_dec_ref(v_val_652_);
lean_dec(v_width_650_);
lean_dec(v_width_648_);
v_a_707_ = lean_ctor_get(v___x_674_, 0);
v_isSharedCheck_714_ = !lean_is_exclusive(v___x_674_);
if (v_isSharedCheck_714_ == 0)
{
v___x_709_ = v___x_674_;
v_isShared_710_ = v_isSharedCheck_714_;
goto v_resetjp_708_;
}
else
{
lean_inc(v_a_707_);
lean_dec(v___x_674_);
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
else
{
lean_object* v_a_715_; lean_object* v___x_717_; uint8_t v_isShared_718_; uint8_t v_isSharedCheck_722_; 
lean_dec_ref(v_arg_662_);
lean_dec_ref(v_arg_661_);
lean_dec_ref(v___x_660_);
lean_dec_ref(v___x_659_);
lean_dec(v___x_658_);
lean_dec_ref(v___x_657_);
lean_dec_ref(v___x_656_);
lean_dec_ref(v___x_655_);
lean_dec_ref(v___x_654_);
lean_dec_ref(v_val_653_);
lean_dec_ref(v_val_652_);
lean_dec_ref(v_expr_651_);
lean_dec(v_width_650_);
lean_dec(v_width_648_);
v_a_715_ = lean_ctor_get(v___x_672_, 0);
v_isSharedCheck_722_ = !lean_is_exclusive(v___x_672_);
if (v_isSharedCheck_722_ == 0)
{
v___x_717_ = v___x_672_;
v_isShared_718_ = v_isSharedCheck_722_;
goto v_resetjp_716_;
}
else
{
lean_inc(v_a_715_);
lean_dec(v___x_672_);
v___x_717_ = lean_box(0);
v_isShared_718_ = v_isSharedCheck_722_;
goto v_resetjp_716_;
}
v_resetjp_716_:
{
lean_object* v___x_720_; 
if (v_isShared_718_ == 0)
{
v___x_720_ = v___x_717_;
goto v_reusejp_719_;
}
else
{
lean_object* v_reuseFailAlloc_721_; 
v_reuseFailAlloc_721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_721_, 0, v_a_715_);
v___x_720_ = v_reuseFailAlloc_721_;
goto v_reusejp_719_;
}
v_reusejp_719_:
{
return v___x_720_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__3___boxed(lean_object** _args){
lean_object* v_width_723_ = _args[0];
lean_object* v_expr_724_ = _args[1];
lean_object* v_width_725_ = _args[2];
lean_object* v_expr_726_ = _args[3];
lean_object* v_val_727_ = _args[4];
lean_object* v_val_728_ = _args[5];
lean_object* v___x_729_ = _args[6];
lean_object* v___x_730_ = _args[7];
lean_object* v___x_731_ = _args[8];
lean_object* v___x_732_ = _args[9];
lean_object* v___x_733_ = _args[10];
lean_object* v___x_734_ = _args[11];
lean_object* v___x_735_ = _args[12];
lean_object* v_arg_736_ = _args[13];
lean_object* v_arg_737_ = _args[14];
lean_object* v___y_738_ = _args[15];
lean_object* v___y_739_ = _args[16];
lean_object* v___y_740_ = _args[17];
lean_object* v___y_741_ = _args[18];
lean_object* v___y_742_ = _args[19];
lean_object* v___y_743_ = _args[20];
lean_object* v___y_744_ = _args[21];
lean_object* v___y_745_ = _args[22];
lean_object* v___y_746_ = _args[23];
_start:
{
lean_object* v_res_747_; 
v_res_747_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__3(v_width_723_, v_expr_724_, v_width_725_, v_expr_726_, v_val_727_, v_val_728_, v___x_729_, v___x_730_, v___x_731_, v___x_732_, v___x_733_, v___x_734_, v___x_735_, v_arg_736_, v_arg_737_, v___y_738_, v___y_739_, v___y_740_, v___y_741_, v___y_742_, v___y_743_, v___y_744_, v___y_745_);
lean_dec(v___y_745_);
lean_dec_ref(v___y_744_);
lean_dec(v___y_743_);
lean_dec_ref(v___y_742_);
lean_dec(v___y_741_);
lean_dec_ref(v___y_740_);
lean_dec(v___y_739_);
lean_dec_ref(v___y_738_);
return v_res_747_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__1(lean_object* v_n_748_){
_start:
{
lean_object* v___x_749_; 
v___x_749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_749_, 0, v_n_748_);
return v___x_749_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__2(lean_object* v_n_750_){
_start:
{
lean_object* v___x_751_; 
v___x_751_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_751_, 0, v_n_750_);
return v___x_751_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftReflection(lean_object* v_distanceExpr_829_, lean_object* v_innerExpr_830_, lean_object* v_shiftOp_831_, lean_object* v_shiftOpName_832_, lean_object* v_congrThm_833_, lean_object* v_origExpr_834_, lean_object* v_a_835_, lean_object* v_a_836_, lean_object* v_a_837_, lean_object* v_a_838_, lean_object* v_a_839_, lean_object* v_a_840_, lean_object* v_a_841_, lean_object* v_a_842_, lean_object* v_a_843_){
_start:
{
lean_object* v___x_845_; 
lean_inc_ref(v_innerExpr_830_);
v___x_845_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_goOrAtom(v_innerExpr_830_, v_a_835_, v_a_836_, v_a_837_, v_a_838_, v_a_839_, v_a_840_, v_a_841_, v_a_842_, v_a_843_);
if (lean_obj_tag(v___x_845_) == 0)
{
lean_object* v_a_846_; lean_object* v___x_848_; uint8_t v_isShared_849_; uint8_t v_isSharedCheck_906_; 
v_a_846_ = lean_ctor_get(v___x_845_, 0);
v_isSharedCheck_906_ = !lean_is_exclusive(v___x_845_);
if (v_isSharedCheck_906_ == 0)
{
v___x_848_ = v___x_845_;
v_isShared_849_ = v_isSharedCheck_906_;
goto v_resetjp_847_;
}
else
{
lean_inc(v_a_846_);
lean_dec(v___x_845_);
v___x_848_ = lean_box(0);
v_isShared_849_ = v_isSharedCheck_906_;
goto v_resetjp_847_;
}
v_resetjp_847_:
{
if (lean_obj_tag(v_a_846_) == 1)
{
lean_object* v_val_850_; lean_object* v___x_851_; 
lean_del_object(v___x_848_);
v_val_850_ = lean_ctor_get(v_a_846_, 0);
lean_inc(v_val_850_);
lean_dec_ref_known(v_a_846_, 1);
lean_inc_ref(v_distanceExpr_829_);
v___x_851_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_goOrAtom(v_distanceExpr_829_, v_a_835_, v_a_836_, v_a_837_, v_a_838_, v_a_839_, v_a_840_, v_a_841_, v_a_842_, v_a_843_);
if (lean_obj_tag(v___x_851_) == 0)
{
lean_object* v_a_852_; lean_object* v___x_854_; uint8_t v_isShared_855_; uint8_t v_isSharedCheck_901_; 
v_a_852_ = lean_ctor_get(v___x_851_, 0);
v_isSharedCheck_901_ = !lean_is_exclusive(v___x_851_);
if (v_isSharedCheck_901_ == 0)
{
v___x_854_ = v___x_851_;
v_isShared_855_ = v_isSharedCheck_901_;
goto v_resetjp_853_;
}
else
{
lean_inc(v_a_852_);
lean_dec(v___x_851_);
v___x_854_ = lean_box(0);
v_isShared_855_ = v_isSharedCheck_901_;
goto v_resetjp_853_;
}
v_resetjp_853_:
{
if (lean_obj_tag(v_a_852_) == 1)
{
lean_object* v_val_856_; lean_object* v___x_858_; uint8_t v_isShared_859_; uint8_t v_isSharedCheck_896_; 
lean_del_object(v___x_854_);
v_val_856_ = lean_ctor_get(v_a_852_, 0);
v_isSharedCheck_896_ = !lean_is_exclusive(v_a_852_);
if (v_isSharedCheck_896_ == 0)
{
v___x_858_ = v_a_852_;
v_isShared_859_ = v_isSharedCheck_896_;
goto v_resetjp_857_;
}
else
{
lean_inc(v_val_856_);
lean_dec(v_a_852_);
v___x_858_ = lean_box(0);
v_isShared_859_ = v_isSharedCheck_896_;
goto v_resetjp_857_;
}
v_resetjp_857_:
{
lean_object* v_width_860_; lean_object* v_bvExpr_861_; lean_object* v_expr_862_; lean_object* v_width_863_; lean_object* v_bvExpr_864_; lean_object* v_expr_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; 
v_width_860_ = lean_ctor_get(v_val_850_, 0);
lean_inc_n(v_width_860_, 3);
v_bvExpr_861_ = lean_ctor_get(v_val_850_, 1);
v_expr_862_ = lean_ctor_get(v_val_850_, 4);
v_width_863_ = lean_ctor_get(v_val_856_, 0);
v_bvExpr_864_ = lean_ctor_get(v_val_856_, 1);
v_expr_865_ = lean_ctor_get(v_val_856_, 4);
lean_inc_ref(v_bvExpr_864_);
lean_inc_ref(v_bvExpr_861_);
lean_inc_n(v_width_863_, 2);
v___x_866_ = lean_apply_4(v_shiftOp_831_, v_width_860_, v_width_863_, v_bvExpr_861_, v_bvExpr_864_);
v___x_867_ = lean_box(0);
v___x_868_ = l_Lean_mkConst(v_shiftOpName_832_, v___x_867_);
v___x_869_ = l_Lean_mkNatLit(v_width_860_);
v___x_870_ = l_Lean_mkNatLit(v_width_863_);
lean_inc_ref(v_expr_865_);
lean_inc_ref(v_expr_862_);
lean_inc_ref(v___x_870_);
lean_inc_ref(v___x_869_);
v___x_871_ = l_Lean_mkApp4(v___x_868_, v___x_869_, v___x_870_, v_expr_862_, v_expr_865_);
v___x_872_ = l_Lean_Meta_Sym_shareCommonInc(v___x_871_, v_a_838_, v_a_839_, v_a_840_, v_a_841_, v_a_842_, v_a_843_);
if (lean_obj_tag(v___x_872_) == 0)
{
lean_object* v_a_873_; lean_object* v___x_875_; uint8_t v_isShared_876_; uint8_t v_isSharedCheck_887_; 
v_a_873_ = lean_ctor_get(v___x_872_, 0);
v_isSharedCheck_887_ = !lean_is_exclusive(v___x_872_);
if (v_isSharedCheck_887_ == 0)
{
v___x_875_ = v___x_872_;
v_isShared_876_ = v_isSharedCheck_887_;
goto v_resetjp_874_;
}
else
{
lean_inc(v_a_873_);
lean_dec(v___x_872_);
v___x_875_ = lean_box(0);
v_isShared_876_ = v_isSharedCheck_887_;
goto v_resetjp_874_;
}
v_resetjp_874_:
{
lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_882_; 
v___x_877_ = l_Lean_mkConst(v_congrThm_833_, v___x_867_);
v___x_878_ = l_Lean_mkAppB(v___x_877_, v___x_869_, v___x_870_);
v___x_879_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryCongrProof___boxed), 14, 5);
lean_closure_set(v___x_879_, 0, v_val_850_);
lean_closure_set(v___x_879_, 1, v_val_856_);
lean_closure_set(v___x_879_, 2, v_innerExpr_830_);
lean_closure_set(v___x_879_, 3, v_distanceExpr_829_);
lean_closure_set(v___x_879_, 4, v___x_878_);
v___x_880_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_880_, 0, v_width_860_);
lean_ctor_set(v___x_880_, 1, v___x_866_);
lean_ctor_set(v___x_880_, 2, v_origExpr_834_);
lean_ctor_set(v___x_880_, 3, v___x_879_);
lean_ctor_set(v___x_880_, 4, v_a_873_);
if (v_isShared_859_ == 0)
{
lean_ctor_set(v___x_858_, 0, v___x_880_);
v___x_882_ = v___x_858_;
goto v_reusejp_881_;
}
else
{
lean_object* v_reuseFailAlloc_886_; 
v_reuseFailAlloc_886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_886_, 0, v___x_880_);
v___x_882_ = v_reuseFailAlloc_886_;
goto v_reusejp_881_;
}
v_reusejp_881_:
{
lean_object* v___x_884_; 
if (v_isShared_876_ == 0)
{
lean_ctor_set(v___x_875_, 0, v___x_882_);
v___x_884_ = v___x_875_;
goto v_reusejp_883_;
}
else
{
lean_object* v_reuseFailAlloc_885_; 
v_reuseFailAlloc_885_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_885_, 0, v___x_882_);
v___x_884_ = v_reuseFailAlloc_885_;
goto v_reusejp_883_;
}
v_reusejp_883_:
{
return v___x_884_;
}
}
}
}
else
{
lean_object* v_a_888_; lean_object* v___x_890_; uint8_t v_isShared_891_; uint8_t v_isSharedCheck_895_; 
lean_dec_ref(v___x_870_);
lean_dec_ref(v___x_869_);
lean_dec_ref(v___x_866_);
lean_dec(v_width_860_);
lean_del_object(v___x_858_);
lean_dec(v_val_856_);
lean_dec(v_val_850_);
lean_dec_ref(v_origExpr_834_);
lean_dec(v_congrThm_833_);
lean_dec_ref(v_innerExpr_830_);
lean_dec_ref(v_distanceExpr_829_);
v_a_888_ = lean_ctor_get(v___x_872_, 0);
v_isSharedCheck_895_ = !lean_is_exclusive(v___x_872_);
if (v_isSharedCheck_895_ == 0)
{
v___x_890_ = v___x_872_;
v_isShared_891_ = v_isSharedCheck_895_;
goto v_resetjp_889_;
}
else
{
lean_inc(v_a_888_);
lean_dec(v___x_872_);
v___x_890_ = lean_box(0);
v_isShared_891_ = v_isSharedCheck_895_;
goto v_resetjp_889_;
}
v_resetjp_889_:
{
lean_object* v___x_893_; 
if (v_isShared_891_ == 0)
{
v___x_893_ = v___x_890_;
goto v_reusejp_892_;
}
else
{
lean_object* v_reuseFailAlloc_894_; 
v_reuseFailAlloc_894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_894_, 0, v_a_888_);
v___x_893_ = v_reuseFailAlloc_894_;
goto v_reusejp_892_;
}
v_reusejp_892_:
{
return v___x_893_;
}
}
}
}
}
else
{
lean_object* v___x_897_; lean_object* v___x_899_; 
lean_dec(v_a_852_);
lean_dec(v_val_850_);
lean_dec_ref(v_origExpr_834_);
lean_dec(v_congrThm_833_);
lean_dec(v_shiftOpName_832_);
lean_dec_ref(v_shiftOp_831_);
lean_dec_ref(v_innerExpr_830_);
lean_dec_ref(v_distanceExpr_829_);
v___x_897_ = lean_box(0);
if (v_isShared_855_ == 0)
{
lean_ctor_set(v___x_854_, 0, v___x_897_);
v___x_899_ = v___x_854_;
goto v_reusejp_898_;
}
else
{
lean_object* v_reuseFailAlloc_900_; 
v_reuseFailAlloc_900_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_900_, 0, v___x_897_);
v___x_899_ = v_reuseFailAlloc_900_;
goto v_reusejp_898_;
}
v_reusejp_898_:
{
return v___x_899_;
}
}
}
}
else
{
lean_dec(v_val_850_);
lean_dec_ref(v_origExpr_834_);
lean_dec(v_congrThm_833_);
lean_dec(v_shiftOpName_832_);
lean_dec_ref(v_shiftOp_831_);
lean_dec_ref(v_innerExpr_830_);
lean_dec_ref(v_distanceExpr_829_);
return v___x_851_;
}
}
else
{
lean_object* v___x_902_; lean_object* v___x_904_; 
lean_dec(v_a_846_);
lean_dec_ref(v_origExpr_834_);
lean_dec(v_congrThm_833_);
lean_dec(v_shiftOpName_832_);
lean_dec_ref(v_shiftOp_831_);
lean_dec_ref(v_innerExpr_830_);
lean_dec_ref(v_distanceExpr_829_);
v___x_902_ = lean_box(0);
if (v_isShared_849_ == 0)
{
lean_ctor_set(v___x_848_, 0, v___x_902_);
v___x_904_ = v___x_848_;
goto v_reusejp_903_;
}
else
{
lean_object* v_reuseFailAlloc_905_; 
v_reuseFailAlloc_905_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_905_, 0, v___x_902_);
v___x_904_ = v_reuseFailAlloc_905_;
goto v_reusejp_903_;
}
v_reusejp_903_:
{
return v___x_904_;
}
}
}
}
else
{
lean_dec_ref(v_origExpr_834_);
lean_dec(v_congrThm_833_);
lean_dec(v_shiftOpName_832_);
lean_dec_ref(v_shiftOp_831_);
lean_dec_ref(v_innerExpr_830_);
lean_dec_ref(v_distanceExpr_829_);
return v___x_845_;
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__2(void){
_start:
{
lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; 
v___x_982_ = lean_box(0);
v___x_983_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__1));
v___x_984_ = l_Lean_mkConst(v___x_983_, v___x_982_);
return v___x_984_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__6(void){
_start:
{
lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; 
v___x_993_ = lean_box(0);
v___x_994_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__5));
v___x_995_ = l_Lean_mkConst(v___x_994_, v___x_993_);
return v___x_995_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__9(void){
_start:
{
lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; 
v___x_1003_ = lean_box(0);
v___x_1004_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__8));
v___x_1005_ = l_Lean_mkConst(v___x_1004_, v___x_1003_);
return v___x_1005_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__12(void){
_start:
{
lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; 
v___x_1013_ = lean_box(0);
v___x_1014_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__11));
v___x_1015_ = l_Lean_mkConst(v___x_1014_, v___x_1013_);
return v___x_1015_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__15(void){
_start:
{
lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; 
v___x_1023_ = lean_box(0);
v___x_1024_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__14));
v___x_1025_ = l_Lean_mkConst(v___x_1024_, v___x_1023_);
return v___x_1025_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__18(void){
_start:
{
lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; 
v___x_1033_ = lean_box(0);
v___x_1034_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__17));
v___x_1035_ = l_Lean_mkConst(v___x_1034_, v___x_1033_);
return v___x_1035_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__21(void){
_start:
{
lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; 
v___x_1043_ = lean_box(0);
v___x_1044_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__20));
v___x_1045_ = l_Lean_mkConst(v___x_1044_, v___x_1043_);
return v___x_1045_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__24(void){
_start:
{
lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; 
v___x_1053_ = lean_box(0);
v___x_1054_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__23));
v___x_1055_ = l_Lean_mkConst(v___x_1054_, v___x_1053_);
return v___x_1055_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection(lean_object* v_lhsExpr_1056_, lean_object* v_rhsExpr_1057_, uint8_t v_op_1058_, lean_object* v_congrThm_1059_, lean_object* v_origExpr_1060_, lean_object* v_a_1061_, lean_object* v_a_1062_, lean_object* v_a_1063_, lean_object* v_a_1064_, lean_object* v_a_1065_, lean_object* v_a_1066_, lean_object* v_a_1067_, lean_object* v_a_1068_, lean_object* v_a_1069_){
_start:
{
lean_object* v___x_1071_; 
lean_inc_ref(v_lhsExpr_1056_);
v___x_1071_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_goOrAtom(v_lhsExpr_1056_, v_a_1061_, v_a_1062_, v_a_1063_, v_a_1064_, v_a_1065_, v_a_1066_, v_a_1067_, v_a_1068_, v_a_1069_);
if (lean_obj_tag(v___x_1071_) == 0)
{
lean_object* v_a_1072_; lean_object* v___x_1074_; uint8_t v_isShared_1075_; uint8_t v_isSharedCheck_1145_; 
v_a_1072_ = lean_ctor_get(v___x_1071_, 0);
v_isSharedCheck_1145_ = !lean_is_exclusive(v___x_1071_);
if (v_isSharedCheck_1145_ == 0)
{
v___x_1074_ = v___x_1071_;
v_isShared_1075_ = v_isSharedCheck_1145_;
goto v_resetjp_1073_;
}
else
{
lean_inc(v_a_1072_);
lean_dec(v___x_1071_);
v___x_1074_ = lean_box(0);
v_isShared_1075_ = v_isSharedCheck_1145_;
goto v_resetjp_1073_;
}
v_resetjp_1073_:
{
if (lean_obj_tag(v_a_1072_) == 1)
{
lean_object* v_val_1076_; lean_object* v___x_1077_; 
lean_del_object(v___x_1074_);
v_val_1076_ = lean_ctor_get(v_a_1072_, 0);
lean_inc(v_val_1076_);
lean_dec_ref_known(v_a_1072_, 1);
lean_inc_ref(v_rhsExpr_1057_);
v___x_1077_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_goOrAtom(v_rhsExpr_1057_, v_a_1061_, v_a_1062_, v_a_1063_, v_a_1064_, v_a_1065_, v_a_1066_, v_a_1067_, v_a_1068_, v_a_1069_);
if (lean_obj_tag(v___x_1077_) == 0)
{
lean_object* v_a_1078_; lean_object* v___x_1080_; uint8_t v_isShared_1081_; uint8_t v_isSharedCheck_1140_; 
v_a_1078_ = lean_ctor_get(v___x_1077_, 0);
v_isSharedCheck_1140_ = !lean_is_exclusive(v___x_1077_);
if (v_isSharedCheck_1140_ == 0)
{
v___x_1080_ = v___x_1077_;
v_isShared_1081_ = v_isSharedCheck_1140_;
goto v_resetjp_1079_;
}
else
{
lean_inc(v_a_1078_);
lean_dec(v___x_1077_);
v___x_1080_ = lean_box(0);
v_isShared_1081_ = v_isSharedCheck_1140_;
goto v_resetjp_1079_;
}
v_resetjp_1079_:
{
if (lean_obj_tag(v_a_1078_) == 1)
{
lean_object* v_val_1082_; lean_object* v___x_1084_; uint8_t v_isShared_1085_; uint8_t v_isSharedCheck_1135_; 
v_val_1082_ = lean_ctor_get(v_a_1078_, 0);
v_isSharedCheck_1135_ = !lean_is_exclusive(v_a_1078_);
if (v_isSharedCheck_1135_ == 0)
{
v___x_1084_ = v_a_1078_;
v_isShared_1085_ = v_isSharedCheck_1135_;
goto v_resetjp_1083_;
}
else
{
lean_inc(v_val_1082_);
lean_dec(v_a_1078_);
v___x_1084_ = lean_box(0);
v_isShared_1085_ = v_isSharedCheck_1135_;
goto v_resetjp_1083_;
}
v_resetjp_1083_:
{
lean_object* v_width_1086_; lean_object* v_bvExpr_1087_; lean_object* v_expr_1088_; lean_object* v_width_1089_; lean_object* v_bvExpr_1090_; lean_object* v_expr_1091_; uint8_t v___x_1092_; 
v_width_1086_ = lean_ctor_get(v_val_1082_, 0);
v_bvExpr_1087_ = lean_ctor_get(v_val_1082_, 1);
v_expr_1088_ = lean_ctor_get(v_val_1082_, 4);
v_width_1089_ = lean_ctor_get(v_val_1076_, 0);
lean_inc(v_width_1089_);
v_bvExpr_1090_ = lean_ctor_get(v_val_1076_, 1);
v_expr_1091_ = lean_ctor_get(v_val_1076_, 4);
v___x_1092_ = lean_nat_dec_eq(v_width_1086_, v_width_1089_);
if (v___x_1092_ == 0)
{
lean_object* v___x_1093_; lean_object* v___x_1095_; 
lean_dec(v_width_1089_);
lean_del_object(v___x_1084_);
lean_dec(v_val_1082_);
lean_dec(v_val_1076_);
lean_dec_ref(v_origExpr_1060_);
lean_dec(v_congrThm_1059_);
lean_dec_ref(v_rhsExpr_1057_);
lean_dec_ref(v_lhsExpr_1056_);
v___x_1093_ = lean_box(0);
if (v_isShared_1081_ == 0)
{
lean_ctor_set(v___x_1080_, 0, v___x_1093_);
v___x_1095_ = v___x_1080_;
goto v_reusejp_1094_;
}
else
{
lean_object* v_reuseFailAlloc_1096_; 
v_reuseFailAlloc_1096_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1096_, 0, v___x_1093_);
v___x_1095_ = v_reuseFailAlloc_1096_;
goto v_reusejp_1094_;
}
v_reusejp_1094_:
{
return v___x_1095_;
}
}
else
{
lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___y_1102_; 
lean_del_object(v___x_1080_);
lean_inc_ref(v_bvExpr_1087_);
lean_inc_ref(v_bvExpr_1090_);
lean_inc_n(v_width_1089_, 2);
v___x_1097_ = l_Std_Tactic_BVDecide_BVExpr_bin___override(v_width_1089_, v_bvExpr_1090_, v_op_1058_, v_bvExpr_1087_);
v___x_1098_ = lean_box(0);
v___x_1099_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__2, &l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__2_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__2);
v___x_1100_ = l_Lean_mkNatLit(v_width_1089_);
switch(v_op_1058_)
{
case 0:
{
lean_object* v___x_1128_; 
v___x_1128_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__6, &l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__6_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__6);
v___y_1102_ = v___x_1128_;
goto v___jp_1101_;
}
case 1:
{
lean_object* v___x_1129_; 
v___x_1129_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__9, &l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__9_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__9);
v___y_1102_ = v___x_1129_;
goto v___jp_1101_;
}
case 2:
{
lean_object* v___x_1130_; 
v___x_1130_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__12);
v___y_1102_ = v___x_1130_;
goto v___jp_1101_;
}
case 3:
{
lean_object* v___x_1131_; 
v___x_1131_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__15, &l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__15_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__15);
v___y_1102_ = v___x_1131_;
goto v___jp_1101_;
}
case 4:
{
lean_object* v___x_1132_; 
v___x_1132_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__18, &l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__18_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__18);
v___y_1102_ = v___x_1132_;
goto v___jp_1101_;
}
case 5:
{
lean_object* v___x_1133_; 
v___x_1133_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__21, &l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__21_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__21);
v___y_1102_ = v___x_1133_;
goto v___jp_1101_;
}
default: 
{
lean_object* v___x_1134_; 
v___x_1134_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__24, &l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__24_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___closed__24);
v___y_1102_ = v___x_1134_;
goto v___jp_1101_;
}
}
v___jp_1101_:
{
lean_object* v___x_1103_; lean_object* v___x_1104_; 
lean_inc_ref(v_expr_1088_);
lean_inc_ref(v___y_1102_);
lean_inc_ref(v_expr_1091_);
lean_inc_ref(v___x_1100_);
v___x_1103_ = l_Lean_mkApp4(v___x_1099_, v___x_1100_, v_expr_1091_, v___y_1102_, v_expr_1088_);
v___x_1104_ = l_Lean_Meta_Sym_shareCommonInc(v___x_1103_, v_a_1064_, v_a_1065_, v_a_1066_, v_a_1067_, v_a_1068_, v_a_1069_);
if (lean_obj_tag(v___x_1104_) == 0)
{
lean_object* v_a_1105_; lean_object* v___x_1107_; uint8_t v_isShared_1108_; uint8_t v_isSharedCheck_1119_; 
v_a_1105_ = lean_ctor_get(v___x_1104_, 0);
v_isSharedCheck_1119_ = !lean_is_exclusive(v___x_1104_);
if (v_isSharedCheck_1119_ == 0)
{
v___x_1107_ = v___x_1104_;
v_isShared_1108_ = v_isSharedCheck_1119_;
goto v_resetjp_1106_;
}
else
{
lean_inc(v_a_1105_);
lean_dec(v___x_1104_);
v___x_1107_ = lean_box(0);
v_isShared_1108_ = v_isSharedCheck_1119_;
goto v_resetjp_1106_;
}
v_resetjp_1106_:
{
lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1114_; 
v___x_1109_ = l_Lean_mkConst(v_congrThm_1059_, v___x_1098_);
v___x_1110_ = l_Lean_Expr_app___override(v___x_1109_, v___x_1100_);
v___x_1111_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryCongrProof___boxed), 14, 5);
lean_closure_set(v___x_1111_, 0, v_val_1076_);
lean_closure_set(v___x_1111_, 1, v_val_1082_);
lean_closure_set(v___x_1111_, 2, v_lhsExpr_1056_);
lean_closure_set(v___x_1111_, 3, v_rhsExpr_1057_);
lean_closure_set(v___x_1111_, 4, v___x_1110_);
v___x_1112_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1112_, 0, v_width_1089_);
lean_ctor_set(v___x_1112_, 1, v___x_1097_);
lean_ctor_set(v___x_1112_, 2, v_origExpr_1060_);
lean_ctor_set(v___x_1112_, 3, v___x_1111_);
lean_ctor_set(v___x_1112_, 4, v_a_1105_);
if (v_isShared_1085_ == 0)
{
lean_ctor_set(v___x_1084_, 0, v___x_1112_);
v___x_1114_ = v___x_1084_;
goto v_reusejp_1113_;
}
else
{
lean_object* v_reuseFailAlloc_1118_; 
v_reuseFailAlloc_1118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1118_, 0, v___x_1112_);
v___x_1114_ = v_reuseFailAlloc_1118_;
goto v_reusejp_1113_;
}
v_reusejp_1113_:
{
lean_object* v___x_1116_; 
if (v_isShared_1108_ == 0)
{
lean_ctor_set(v___x_1107_, 0, v___x_1114_);
v___x_1116_ = v___x_1107_;
goto v_reusejp_1115_;
}
else
{
lean_object* v_reuseFailAlloc_1117_; 
v_reuseFailAlloc_1117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1117_, 0, v___x_1114_);
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
else
{
lean_object* v_a_1120_; lean_object* v___x_1122_; uint8_t v_isShared_1123_; uint8_t v_isSharedCheck_1127_; 
lean_dec_ref(v___x_1100_);
lean_dec_ref(v___x_1097_);
lean_dec(v_width_1089_);
lean_del_object(v___x_1084_);
lean_dec(v_val_1082_);
lean_dec(v_val_1076_);
lean_dec_ref(v_origExpr_1060_);
lean_dec(v_congrThm_1059_);
lean_dec_ref(v_rhsExpr_1057_);
lean_dec_ref(v_lhsExpr_1056_);
v_a_1120_ = lean_ctor_get(v___x_1104_, 0);
v_isSharedCheck_1127_ = !lean_is_exclusive(v___x_1104_);
if (v_isSharedCheck_1127_ == 0)
{
v___x_1122_ = v___x_1104_;
v_isShared_1123_ = v_isSharedCheck_1127_;
goto v_resetjp_1121_;
}
else
{
lean_inc(v_a_1120_);
lean_dec(v___x_1104_);
v___x_1122_ = lean_box(0);
v_isShared_1123_ = v_isSharedCheck_1127_;
goto v_resetjp_1121_;
}
v_resetjp_1121_:
{
lean_object* v___x_1125_; 
if (v_isShared_1123_ == 0)
{
v___x_1125_ = v___x_1122_;
goto v_reusejp_1124_;
}
else
{
lean_object* v_reuseFailAlloc_1126_; 
v_reuseFailAlloc_1126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1126_, 0, v_a_1120_);
v___x_1125_ = v_reuseFailAlloc_1126_;
goto v_reusejp_1124_;
}
v_reusejp_1124_:
{
return v___x_1125_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1136_; lean_object* v___x_1138_; 
lean_dec(v_a_1078_);
lean_dec(v_val_1076_);
lean_dec_ref(v_origExpr_1060_);
lean_dec(v_congrThm_1059_);
lean_dec_ref(v_rhsExpr_1057_);
lean_dec_ref(v_lhsExpr_1056_);
v___x_1136_ = lean_box(0);
if (v_isShared_1081_ == 0)
{
lean_ctor_set(v___x_1080_, 0, v___x_1136_);
v___x_1138_ = v___x_1080_;
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
lean_dec(v_val_1076_);
lean_dec_ref(v_origExpr_1060_);
lean_dec(v_congrThm_1059_);
lean_dec_ref(v_rhsExpr_1057_);
lean_dec_ref(v_lhsExpr_1056_);
return v___x_1077_;
}
}
else
{
lean_object* v___x_1141_; lean_object* v___x_1143_; 
lean_dec(v_a_1072_);
lean_dec_ref(v_origExpr_1060_);
lean_dec(v_congrThm_1059_);
lean_dec_ref(v_rhsExpr_1057_);
lean_dec_ref(v_lhsExpr_1056_);
v___x_1141_ = lean_box(0);
if (v_isShared_1075_ == 0)
{
lean_ctor_set(v___x_1074_, 0, v___x_1141_);
v___x_1143_ = v___x_1074_;
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
lean_dec_ref(v_origExpr_1060_);
lean_dec(v_congrThm_1059_);
lean_dec_ref(v_rhsExpr_1057_);
lean_dec_ref(v_lhsExpr_1056_);
return v___x_1071_;
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__72(void){
_start:
{
lean_object* v___x_1187_; lean_object* v___x_1188_; 
v___x_1187_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__71));
v___x_1188_ = l_Lean_stringToMessageData(v___x_1187_);
return v___x_1188_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__75(void){
_start:
{
lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; 
v___x_1196_ = lean_box(0);
v___x_1197_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__74));
v___x_1198_ = l_Lean_mkConst(v___x_1197_, v___x_1196_);
return v___x_1198_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__82(void){
_start:
{
lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; 
v___x_1221_ = lean_box(0);
v___x_1222_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__81));
v___x_1223_ = l_Lean_mkConst(v___x_1222_, v___x_1221_);
return v___x_1223_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_binaryReflection(lean_object* v_lhsExpr_1246_, lean_object* v_rhsExpr_1247_, uint8_t v_pred_1248_, lean_object* v_origExpr_1249_, lean_object* v_a_1250_, lean_object* v_a_1251_, lean_object* v_a_1252_, lean_object* v_a_1253_, lean_object* v_a_1254_, lean_object* v_a_1255_, lean_object* v_a_1256_, lean_object* v_a_1257_, lean_object* v_a_1258_){
_start:
{
lean_object* v___x_1260_; 
lean_inc_ref(v_lhsExpr_1246_);
v___x_1260_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of(v_lhsExpr_1246_, v_a_1250_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_);
if (lean_obj_tag(v___x_1260_) == 0)
{
lean_object* v_a_1261_; lean_object* v___x_1263_; uint8_t v_isShared_1264_; uint8_t v_isSharedCheck_1290_; 
v_a_1261_ = lean_ctor_get(v___x_1260_, 0);
v_isSharedCheck_1290_ = !lean_is_exclusive(v___x_1260_);
if (v_isSharedCheck_1290_ == 0)
{
v___x_1263_ = v___x_1260_;
v_isShared_1264_ = v_isSharedCheck_1290_;
goto v_resetjp_1262_;
}
else
{
lean_inc(v_a_1261_);
lean_dec(v___x_1260_);
v___x_1263_ = lean_box(0);
v_isShared_1264_ = v_isSharedCheck_1290_;
goto v_resetjp_1262_;
}
v_resetjp_1262_:
{
if (lean_obj_tag(v_a_1261_) == 1)
{
lean_object* v_val_1265_; lean_object* v___x_1266_; 
lean_del_object(v___x_1263_);
v_val_1265_ = lean_ctor_get(v_a_1261_, 0);
lean_inc(v_val_1265_);
lean_dec_ref_known(v_a_1261_, 1);
lean_inc_ref(v_rhsExpr_1247_);
v___x_1266_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of(v_rhsExpr_1247_, v_a_1250_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_);
if (lean_obj_tag(v___x_1266_) == 0)
{
lean_object* v_a_1267_; lean_object* v___x_1269_; uint8_t v_isShared_1270_; uint8_t v_isSharedCheck_1277_; 
v_a_1267_ = lean_ctor_get(v___x_1266_, 0);
v_isSharedCheck_1277_ = !lean_is_exclusive(v___x_1266_);
if (v_isSharedCheck_1277_ == 0)
{
v___x_1269_ = v___x_1266_;
v_isShared_1270_ = v_isSharedCheck_1277_;
goto v_resetjp_1268_;
}
else
{
lean_inc(v_a_1267_);
lean_dec(v___x_1266_);
v___x_1269_ = lean_box(0);
v_isShared_1270_ = v_isSharedCheck_1277_;
goto v_resetjp_1268_;
}
v_resetjp_1268_:
{
if (lean_obj_tag(v_a_1267_) == 1)
{
lean_object* v_val_1271_; lean_object* v___x_1272_; 
lean_del_object(v___x_1269_);
v_val_1271_ = lean_ctor_get(v_a_1267_, 0);
lean_inc(v_val_1271_);
lean_dec_ref_known(v_a_1267_, 1);
v___x_1272_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg(v_val_1265_, v_val_1271_, v_lhsExpr_1246_, v_rhsExpr_1247_, v_pred_1248_, v_origExpr_1249_, v_a_1253_, v_a_1254_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_);
return v___x_1272_;
}
else
{
lean_object* v___x_1273_; lean_object* v___x_1275_; 
lean_dec(v_a_1267_);
lean_dec(v_val_1265_);
lean_dec_ref(v_origExpr_1249_);
lean_dec_ref(v_rhsExpr_1247_);
lean_dec_ref(v_lhsExpr_1246_);
v___x_1273_ = lean_box(0);
if (v_isShared_1270_ == 0)
{
lean_ctor_set(v___x_1269_, 0, v___x_1273_);
v___x_1275_ = v___x_1269_;
goto v_reusejp_1274_;
}
else
{
lean_object* v_reuseFailAlloc_1276_; 
v_reuseFailAlloc_1276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1276_, 0, v___x_1273_);
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
else
{
lean_object* v_a_1278_; lean_object* v___x_1280_; uint8_t v_isShared_1281_; uint8_t v_isSharedCheck_1285_; 
lean_dec(v_val_1265_);
lean_dec_ref(v_origExpr_1249_);
lean_dec_ref(v_rhsExpr_1247_);
lean_dec_ref(v_lhsExpr_1246_);
v_a_1278_ = lean_ctor_get(v___x_1266_, 0);
v_isSharedCheck_1285_ = !lean_is_exclusive(v___x_1266_);
if (v_isSharedCheck_1285_ == 0)
{
v___x_1280_ = v___x_1266_;
v_isShared_1281_ = v_isSharedCheck_1285_;
goto v_resetjp_1279_;
}
else
{
lean_inc(v_a_1278_);
lean_dec(v___x_1266_);
v___x_1280_ = lean_box(0);
v_isShared_1281_ = v_isSharedCheck_1285_;
goto v_resetjp_1279_;
}
v_resetjp_1279_:
{
lean_object* v___x_1283_; 
if (v_isShared_1281_ == 0)
{
v___x_1283_ = v___x_1280_;
goto v_reusejp_1282_;
}
else
{
lean_object* v_reuseFailAlloc_1284_; 
v_reuseFailAlloc_1284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1284_, 0, v_a_1278_);
v___x_1283_ = v_reuseFailAlloc_1284_;
goto v_reusejp_1282_;
}
v_reusejp_1282_:
{
return v___x_1283_;
}
}
}
}
else
{
lean_object* v___x_1286_; lean_object* v___x_1288_; 
lean_dec(v_a_1261_);
lean_dec_ref(v_origExpr_1249_);
lean_dec_ref(v_rhsExpr_1247_);
lean_dec_ref(v_lhsExpr_1246_);
v___x_1286_ = lean_box(0);
if (v_isShared_1264_ == 0)
{
lean_ctor_set(v___x_1263_, 0, v___x_1286_);
v___x_1288_ = v___x_1263_;
goto v_reusejp_1287_;
}
else
{
lean_object* v_reuseFailAlloc_1289_; 
v_reuseFailAlloc_1289_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1289_, 0, v___x_1286_);
v___x_1288_ = v_reuseFailAlloc_1289_;
goto v_reusejp_1287_;
}
v_reusejp_1287_:
{
return v___x_1288_;
}
}
}
}
else
{
lean_object* v_a_1291_; lean_object* v___x_1293_; uint8_t v_isShared_1294_; uint8_t v_isSharedCheck_1298_; 
lean_dec_ref(v_origExpr_1249_);
lean_dec_ref(v_rhsExpr_1247_);
lean_dec_ref(v_lhsExpr_1246_);
v_a_1291_ = lean_ctor_get(v___x_1260_, 0);
v_isSharedCheck_1298_ = !lean_is_exclusive(v___x_1260_);
if (v_isSharedCheck_1298_ == 0)
{
v___x_1293_ = v___x_1260_;
v_isShared_1294_ = v_isSharedCheck_1298_;
goto v_resetjp_1292_;
}
else
{
lean_inc(v_a_1291_);
lean_dec(v___x_1260_);
v___x_1293_ = lean_box(0);
v_isShared_1294_ = v_isSharedCheck_1298_;
goto v_resetjp_1292_;
}
v_resetjp_1292_:
{
lean_object* v___x_1296_; 
if (v_isShared_1294_ == 0)
{
v___x_1296_ = v___x_1293_;
goto v_reusejp_1295_;
}
else
{
lean_object* v_reuseFailAlloc_1297_; 
v_reuseFailAlloc_1297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1297_, 0, v_a_1291_);
v___x_1296_ = v_reuseFailAlloc_1297_;
goto v_reusejp_1295_;
}
v_reusejp_1295_:
{
return v___x_1296_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go(lean_object* v_origExpr_1299_, lean_object* v_a_1300_, lean_object* v_a_1301_, lean_object* v_a_1302_, lean_object* v_a_1303_, lean_object* v_a_1304_, lean_object* v_a_1305_, lean_object* v_a_1306_, lean_object* v_a_1307_, lean_object* v_a_1308_){
_start:
{
lean_object* v___x_1316_; 
lean_inc_ref(v_origExpr_1299_);
v___x_1316_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_origExpr_1299_, v_a_1306_);
if (lean_obj_tag(v___x_1316_) == 0)
{
lean_object* v_a_1317_; lean_object* v___x_1318_; uint8_t v___x_1319_; 
v_a_1317_ = lean_ctor_get(v___x_1316_, 0);
lean_inc(v_a_1317_);
lean_dec_ref_known(v___x_1316_, 1);
v___x_1318_ = l_Lean_Expr_cleanupAnnotations(v_a_1317_);
v___x_1319_ = l_Lean_Expr_isApp(v___x_1318_);
if (v___x_1319_ == 0)
{
lean_dec_ref(v___x_1318_);
lean_dec_ref(v_origExpr_1299_);
goto v___jp_1310_;
}
else
{
lean_object* v_arg_1320_; lean_object* v___x_1321_; uint8_t v___x_1322_; 
v_arg_1320_ = lean_ctor_get(v___x_1318_, 1);
lean_inc_ref(v_arg_1320_);
v___x_1321_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1318_);
v___x_1322_ = l_Lean_Expr_isApp(v___x_1321_);
if (v___x_1322_ == 0)
{
lean_dec_ref(v___x_1321_);
lean_dec_ref(v_arg_1320_);
lean_dec_ref(v_origExpr_1299_);
goto v___jp_1310_;
}
else
{
lean_object* v_arg_1323_; lean_object* v___x_1324_; uint8_t v___x_1325_; 
v_arg_1323_ = lean_ctor_get(v___x_1321_, 1);
lean_inc_ref(v_arg_1323_);
v___x_1324_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1321_);
v___x_1325_ = l_Lean_Expr_isApp(v___x_1324_);
if (v___x_1325_ == 0)
{
lean_dec_ref(v___x_1324_);
lean_dec_ref(v_arg_1323_);
lean_dec_ref(v_arg_1320_);
lean_dec_ref(v_origExpr_1299_);
goto v___jp_1310_;
}
else
{
lean_object* v___x_1326_; lean_object* v___x_1327_; uint8_t v___x_1328_; 
v___x_1326_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1324_);
v___x_1327_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__2));
v___x_1328_ = l_Lean_Expr_isConstOf(v___x_1326_, v___x_1327_);
if (v___x_1328_ == 0)
{
lean_object* v___x_1329_; uint8_t v___x_1330_; 
v___x_1329_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__4));
v___x_1330_ = l_Lean_Expr_isConstOf(v___x_1326_, v___x_1329_);
if (v___x_1330_ == 0)
{
uint8_t v___x_1331_; 
v___x_1331_ = l_Lean_Expr_isApp(v___x_1326_);
if (v___x_1331_ == 0)
{
lean_dec_ref(v___x_1326_);
lean_dec_ref(v_arg_1323_);
lean_dec_ref(v_arg_1320_);
lean_dec_ref(v_origExpr_1299_);
goto v___jp_1310_;
}
else
{
lean_object* v_arg_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; uint8_t v___x_1335_; 
v_arg_1332_ = lean_ctor_get(v___x_1326_, 1);
lean_inc_ref(v_arg_1332_);
v___x_1333_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1326_);
v___x_1334_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__7));
v___x_1335_ = l_Lean_Expr_isConstOf(v___x_1333_, v___x_1334_);
lean_dec_ref(v___x_1333_);
if (v___x_1335_ == 0)
{
lean_dec_ref(v_arg_1332_);
lean_dec_ref(v_arg_1323_);
lean_dec_ref(v_arg_1320_);
lean_dec_ref(v_origExpr_1299_);
goto v___jp_1310_;
}
else
{
lean_object* v___x_1336_; uint8_t v___x_1337_; 
v___x_1336_ = l_Lean_Expr_cleanupAnnotations(v_arg_1332_);
v___x_1337_ = l_Lean_Expr_isApp(v___x_1336_);
if (v___x_1337_ == 0)
{
lean_dec_ref(v___x_1336_);
lean_dec_ref(v_arg_1323_);
lean_dec_ref(v_arg_1320_);
lean_dec_ref(v_origExpr_1299_);
goto v___jp_1313_;
}
else
{
lean_object* v___x_1338_; lean_object* v___x_1339_; uint8_t v___x_1340_; 
v___x_1338_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1336_);
v___x_1339_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__8));
v___x_1340_ = l_Lean_Expr_isConstOf(v___x_1338_, v___x_1339_);
lean_dec_ref(v___x_1338_);
if (v___x_1340_ == 0)
{
lean_dec_ref(v_arg_1323_);
lean_dec_ref(v_arg_1320_);
lean_dec_ref(v_origExpr_1299_);
goto v___jp_1313_;
}
else
{
uint8_t v___x_1341_; lean_object* v___x_1342_; 
v___x_1341_ = 0;
v___x_1342_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_binaryReflection(v_arg_1323_, v_arg_1320_, v___x_1341_, v_origExpr_1299_, v_a_1300_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_, v_a_1307_, v_a_1308_);
return v___x_1342_;
}
}
}
}
}
else
{
uint8_t v___x_1343_; lean_object* v___x_1344_; 
lean_dec_ref(v___x_1326_);
v___x_1343_ = 1;
v___x_1344_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_binaryReflection(v_arg_1323_, v_arg_1320_, v___x_1343_, v_origExpr_1299_, v_a_1300_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_, v_a_1307_, v_a_1308_);
return v___x_1344_;
}
}
else
{
lean_object* v___x_1345_; 
lean_dec_ref(v___x_1326_);
lean_inc_ref(v_arg_1323_);
v___x_1345_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of(v_arg_1323_, v_a_1300_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_, v_a_1307_, v_a_1308_);
if (lean_obj_tag(v___x_1345_) == 0)
{
lean_object* v_a_1346_; lean_object* v___x_1348_; uint8_t v_isShared_1349_; uint8_t v_isSharedCheck_1385_; 
v_a_1346_ = lean_ctor_get(v___x_1345_, 0);
v_isSharedCheck_1385_ = !lean_is_exclusive(v___x_1345_);
if (v_isSharedCheck_1385_ == 0)
{
v___x_1348_ = v___x_1345_;
v_isShared_1349_ = v_isSharedCheck_1385_;
goto v_resetjp_1347_;
}
else
{
lean_inc(v_a_1346_);
lean_dec(v___x_1345_);
v___x_1348_ = lean_box(0);
v_isShared_1349_ = v_isSharedCheck_1385_;
goto v_resetjp_1347_;
}
v_resetjp_1347_:
{
if (lean_obj_tag(v_a_1346_) == 1)
{
lean_object* v_val_1350_; lean_object* v___x_1351_; 
v_val_1350_ = lean_ctor_get(v_a_1346_, 0);
lean_inc(v_val_1350_);
lean_dec_ref_known(v_a_1346_, 1);
v___x_1351_ = l_Lean_Meta_Sym_getNatValue_x3f(v_arg_1320_);
if (lean_obj_tag(v___x_1351_) == 1)
{
lean_object* v_val_1352_; lean_object* v___x_1354_; uint8_t v_isShared_1355_; uint8_t v_isSharedCheck_1376_; 
lean_del_object(v___x_1348_);
v_val_1352_ = lean_ctor_get(v___x_1351_, 0);
v_isSharedCheck_1376_ = !lean_is_exclusive(v___x_1351_);
if (v_isSharedCheck_1376_ == 0)
{
v___x_1354_ = v___x_1351_;
v_isShared_1355_ = v_isSharedCheck_1376_;
goto v_resetjp_1353_;
}
else
{
lean_inc(v_val_1352_);
lean_dec(v___x_1351_);
v___x_1354_ = lean_box(0);
v_isShared_1355_ = v_isSharedCheck_1376_;
goto v_resetjp_1353_;
}
v_resetjp_1353_:
{
lean_object* v___x_1356_; 
v___x_1356_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkGetLsbD___redArg(v_val_1350_, v_arg_1323_, v_val_1352_, v_origExpr_1299_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_, v_a_1307_, v_a_1308_);
if (lean_obj_tag(v___x_1356_) == 0)
{
lean_object* v_a_1357_; lean_object* v___x_1359_; uint8_t v_isShared_1360_; uint8_t v_isSharedCheck_1367_; 
v_a_1357_ = lean_ctor_get(v___x_1356_, 0);
v_isSharedCheck_1367_ = !lean_is_exclusive(v___x_1356_);
if (v_isSharedCheck_1367_ == 0)
{
v___x_1359_ = v___x_1356_;
v_isShared_1360_ = v_isSharedCheck_1367_;
goto v_resetjp_1358_;
}
else
{
lean_inc(v_a_1357_);
lean_dec(v___x_1356_);
v___x_1359_ = lean_box(0);
v_isShared_1360_ = v_isSharedCheck_1367_;
goto v_resetjp_1358_;
}
v_resetjp_1358_:
{
lean_object* v___x_1362_; 
if (v_isShared_1355_ == 0)
{
lean_ctor_set(v___x_1354_, 0, v_a_1357_);
v___x_1362_ = v___x_1354_;
goto v_reusejp_1361_;
}
else
{
lean_object* v_reuseFailAlloc_1366_; 
v_reuseFailAlloc_1366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1366_, 0, v_a_1357_);
v___x_1362_ = v_reuseFailAlloc_1366_;
goto v_reusejp_1361_;
}
v_reusejp_1361_:
{
lean_object* v___x_1364_; 
if (v_isShared_1360_ == 0)
{
lean_ctor_set(v___x_1359_, 0, v___x_1362_);
v___x_1364_ = v___x_1359_;
goto v_reusejp_1363_;
}
else
{
lean_object* v_reuseFailAlloc_1365_; 
v_reuseFailAlloc_1365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1365_, 0, v___x_1362_);
v___x_1364_ = v_reuseFailAlloc_1365_;
goto v_reusejp_1363_;
}
v_reusejp_1363_:
{
return v___x_1364_;
}
}
}
}
else
{
lean_object* v_a_1368_; lean_object* v___x_1370_; uint8_t v_isShared_1371_; uint8_t v_isSharedCheck_1375_; 
lean_del_object(v___x_1354_);
v_a_1368_ = lean_ctor_get(v___x_1356_, 0);
v_isSharedCheck_1375_ = !lean_is_exclusive(v___x_1356_);
if (v_isSharedCheck_1375_ == 0)
{
v___x_1370_ = v___x_1356_;
v_isShared_1371_ = v_isSharedCheck_1375_;
goto v_resetjp_1369_;
}
else
{
lean_inc(v_a_1368_);
lean_dec(v___x_1356_);
v___x_1370_ = lean_box(0);
v_isShared_1371_ = v_isSharedCheck_1375_;
goto v_resetjp_1369_;
}
v_resetjp_1369_:
{
lean_object* v___x_1373_; 
if (v_isShared_1371_ == 0)
{
v___x_1373_ = v___x_1370_;
goto v_reusejp_1372_;
}
else
{
lean_object* v_reuseFailAlloc_1374_; 
v_reuseFailAlloc_1374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1374_, 0, v_a_1368_);
v___x_1373_ = v_reuseFailAlloc_1374_;
goto v_reusejp_1372_;
}
v_reusejp_1372_:
{
return v___x_1373_;
}
}
}
}
}
else
{
lean_object* v___x_1377_; lean_object* v___x_1379_; 
lean_dec(v___x_1351_);
lean_dec(v_val_1350_);
lean_dec_ref(v_arg_1323_);
lean_dec_ref(v_origExpr_1299_);
v___x_1377_ = lean_box(0);
if (v_isShared_1349_ == 0)
{
lean_ctor_set(v___x_1348_, 0, v___x_1377_);
v___x_1379_ = v___x_1348_;
goto v_reusejp_1378_;
}
else
{
lean_object* v_reuseFailAlloc_1380_; 
v_reuseFailAlloc_1380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1380_, 0, v___x_1377_);
v___x_1379_ = v_reuseFailAlloc_1380_;
goto v_reusejp_1378_;
}
v_reusejp_1378_:
{
return v___x_1379_;
}
}
}
else
{
lean_object* v___x_1381_; lean_object* v___x_1383_; 
lean_dec(v_a_1346_);
lean_dec_ref(v_arg_1323_);
lean_dec_ref(v_arg_1320_);
lean_dec_ref(v_origExpr_1299_);
v___x_1381_ = lean_box(0);
if (v_isShared_1349_ == 0)
{
lean_ctor_set(v___x_1348_, 0, v___x_1381_);
v___x_1383_ = v___x_1348_;
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
}
}
else
{
lean_object* v_a_1386_; lean_object* v___x_1388_; uint8_t v_isShared_1389_; uint8_t v_isSharedCheck_1393_; 
lean_dec_ref(v_arg_1323_);
lean_dec_ref(v_arg_1320_);
lean_dec_ref(v_origExpr_1299_);
v_a_1386_ = lean_ctor_get(v___x_1345_, 0);
v_isSharedCheck_1393_ = !lean_is_exclusive(v___x_1345_);
if (v_isSharedCheck_1393_ == 0)
{
v___x_1388_ = v___x_1345_;
v_isShared_1389_ = v_isSharedCheck_1393_;
goto v_resetjp_1387_;
}
else
{
lean_inc(v_a_1386_);
lean_dec(v___x_1345_);
v___x_1388_ = lean_box(0);
v_isShared_1389_ = v_isSharedCheck_1393_;
goto v_resetjp_1387_;
}
v_resetjp_1387_:
{
lean_object* v___x_1391_; 
if (v_isShared_1389_ == 0)
{
v___x_1391_ = v___x_1388_;
goto v_reusejp_1390_;
}
else
{
lean_object* v_reuseFailAlloc_1392_; 
v_reuseFailAlloc_1392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1392_, 0, v_a_1386_);
v___x_1391_ = v_reuseFailAlloc_1392_;
goto v_reusejp_1390_;
}
v_reusejp_1390_:
{
return v___x_1391_;
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
lean_object* v_a_1394_; lean_object* v___x_1396_; uint8_t v_isShared_1397_; uint8_t v_isSharedCheck_1401_; 
lean_dec_ref(v_origExpr_1299_);
v_a_1394_ = lean_ctor_get(v___x_1316_, 0);
v_isSharedCheck_1401_ = !lean_is_exclusive(v___x_1316_);
if (v_isSharedCheck_1401_ == 0)
{
v___x_1396_ = v___x_1316_;
v_isShared_1397_ = v_isSharedCheck_1401_;
goto v_resetjp_1395_;
}
else
{
lean_inc(v_a_1394_);
lean_dec(v___x_1316_);
v___x_1396_ = lean_box(0);
v_isShared_1397_ = v_isSharedCheck_1401_;
goto v_resetjp_1395_;
}
v_resetjp_1395_:
{
lean_object* v___x_1399_; 
if (v_isShared_1397_ == 0)
{
v___x_1399_ = v___x_1396_;
goto v_reusejp_1398_;
}
else
{
lean_object* v_reuseFailAlloc_1400_; 
v_reuseFailAlloc_1400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1400_, 0, v_a_1394_);
v___x_1399_ = v_reuseFailAlloc_1400_;
goto v_reusejp_1398_;
}
v_reusejp_1398_:
{
return v___x_1399_;
}
}
}
v___jp_1310_:
{
lean_object* v___x_1311_; lean_object* v___x_1312_; 
v___x_1311_ = lean_box(0);
v___x_1312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1312_, 0, v___x_1311_);
return v___x_1312_;
}
v___jp_1313_:
{
lean_object* v___x_1314_; lean_object* v___x_1315_; 
v___x_1314_ = lean_box(0);
v___x_1315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1315_, 0, v___x_1314_);
return v___x_1315_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_LemmaM_withBVPredCache___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_spec__5(lean_object* v_e_1402_, lean_object* v_a_1403_, lean_object* v_a_1404_, lean_object* v_a_1405_, lean_object* v_a_1406_, lean_object* v_a_1407_, lean_object* v_a_1408_, lean_object* v_a_1409_, lean_object* v_a_1410_, lean_object* v_a_1411_){
_start:
{
lean_object* v___y_1414_; lean_object* v___x_1437_; lean_object* v_bvPredCache_1438_; lean_object* v___x_1439_; 
v___x_1437_ = lean_st_ref_get(v_a_1403_);
v_bvPredCache_1438_ = lean_ctor_get(v___x_1437_, 2);
lean_inc_ref(v_bvPredCache_1438_);
lean_dec(v___x_1437_);
v___x_1439_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__12___redArg(v_bvPredCache_1438_, v_e_1402_);
lean_dec_ref(v_bvPredCache_1438_);
if (lean_obj_tag(v___x_1439_) == 0)
{
lean_object* v___x_1440_; 
lean_inc_ref(v_e_1402_);
v___x_1440_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go(v_e_1402_, v_a_1403_, v_a_1404_, v_a_1405_, v_a_1406_, v_a_1407_, v_a_1408_, v_a_1409_, v_a_1410_, v_a_1411_);
if (lean_obj_tag(v___x_1440_) == 0)
{
lean_object* v_a_1441_; 
v_a_1441_ = lean_ctor_get(v___x_1440_, 0);
lean_inc(v_a_1441_);
if (lean_obj_tag(v_a_1441_) == 0)
{
lean_object* v___x_1442_; 
lean_dec_ref_known(v___x_1440_, 1);
lean_inc_ref(v_e_1402_);
v___x_1442_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom(v_e_1402_, v_a_1404_, v_a_1405_, v_a_1406_, v_a_1407_, v_a_1408_, v_a_1409_, v_a_1410_, v_a_1411_);
v___y_1414_ = v___x_1442_;
goto v___jp_1413_;
}
else
{
lean_dec_ref_known(v_a_1441_, 1);
v___y_1414_ = v___x_1440_;
goto v___jp_1413_;
}
}
else
{
v___y_1414_ = v___x_1440_;
goto v___jp_1413_;
}
}
else
{
lean_object* v_val_1443_; lean_object* v___x_1445_; uint8_t v_isShared_1446_; uint8_t v_isSharedCheck_1450_; 
lean_dec_ref(v_e_1402_);
v_val_1443_ = lean_ctor_get(v___x_1439_, 0);
v_isSharedCheck_1450_ = !lean_is_exclusive(v___x_1439_);
if (v_isSharedCheck_1450_ == 0)
{
v___x_1445_ = v___x_1439_;
v_isShared_1446_ = v_isSharedCheck_1450_;
goto v_resetjp_1444_;
}
else
{
lean_inc(v_val_1443_);
lean_dec(v___x_1439_);
v___x_1445_ = lean_box(0);
v_isShared_1446_ = v_isSharedCheck_1450_;
goto v_resetjp_1444_;
}
v_resetjp_1444_:
{
lean_object* v___x_1448_; 
if (v_isShared_1446_ == 0)
{
lean_ctor_set_tag(v___x_1445_, 0);
v___x_1448_ = v___x_1445_;
goto v_reusejp_1447_;
}
else
{
lean_object* v_reuseFailAlloc_1449_; 
v_reuseFailAlloc_1449_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1449_, 0, v_val_1443_);
v___x_1448_ = v_reuseFailAlloc_1449_;
goto v_reusejp_1447_;
}
v_reusejp_1447_:
{
return v___x_1448_;
}
}
}
v___jp_1413_:
{
if (lean_obj_tag(v___y_1414_) == 0)
{
lean_object* v_a_1415_; lean_object* v___x_1417_; uint8_t v_isShared_1418_; uint8_t v_isSharedCheck_1436_; 
v_a_1415_ = lean_ctor_get(v___y_1414_, 0);
v_isSharedCheck_1436_ = !lean_is_exclusive(v___y_1414_);
if (v_isSharedCheck_1436_ == 0)
{
v___x_1417_ = v___y_1414_;
v_isShared_1418_ = v_isSharedCheck_1436_;
goto v_resetjp_1416_;
}
else
{
lean_inc(v_a_1415_);
lean_dec(v___y_1414_);
v___x_1417_ = lean_box(0);
v_isShared_1418_ = v_isSharedCheck_1436_;
goto v_resetjp_1416_;
}
v_resetjp_1416_:
{
lean_object* v___x_1419_; lean_object* v_lemmas_1420_; lean_object* v_bvExprCache_1421_; lean_object* v_bvPredCache_1422_; lean_object* v_bvLogicalCache_1423_; lean_object* v___x_1425_; uint8_t v_isShared_1426_; uint8_t v_isSharedCheck_1435_; 
v___x_1419_ = lean_st_ref_take(v_a_1403_);
v_lemmas_1420_ = lean_ctor_get(v___x_1419_, 0);
v_bvExprCache_1421_ = lean_ctor_get(v___x_1419_, 1);
v_bvPredCache_1422_ = lean_ctor_get(v___x_1419_, 2);
v_bvLogicalCache_1423_ = lean_ctor_get(v___x_1419_, 3);
v_isSharedCheck_1435_ = !lean_is_exclusive(v___x_1419_);
if (v_isSharedCheck_1435_ == 0)
{
v___x_1425_ = v___x_1419_;
v_isShared_1426_ = v_isSharedCheck_1435_;
goto v_resetjp_1424_;
}
else
{
lean_inc(v_bvLogicalCache_1423_);
lean_inc(v_bvPredCache_1422_);
lean_inc(v_bvExprCache_1421_);
lean_inc(v_lemmas_1420_);
lean_dec(v___x_1419_);
v___x_1425_ = lean_box(0);
v_isShared_1426_ = v_isSharedCheck_1435_;
goto v_resetjp_1424_;
}
v_resetjp_1424_:
{
lean_object* v___x_1427_; lean_object* v___x_1429_; 
lean_inc(v_a_1415_);
v___x_1427_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13___redArg(v_bvPredCache_1422_, v_e_1402_, v_a_1415_);
if (v_isShared_1426_ == 0)
{
lean_ctor_set(v___x_1425_, 2, v___x_1427_);
v___x_1429_ = v___x_1425_;
goto v_reusejp_1428_;
}
else
{
lean_object* v_reuseFailAlloc_1434_; 
v_reuseFailAlloc_1434_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1434_, 0, v_lemmas_1420_);
lean_ctor_set(v_reuseFailAlloc_1434_, 1, v_bvExprCache_1421_);
lean_ctor_set(v_reuseFailAlloc_1434_, 2, v___x_1427_);
lean_ctor_set(v_reuseFailAlloc_1434_, 3, v_bvLogicalCache_1423_);
v___x_1429_ = v_reuseFailAlloc_1434_;
goto v_reusejp_1428_;
}
v_reusejp_1428_:
{
lean_object* v___x_1430_; lean_object* v___x_1432_; 
v___x_1430_ = lean_st_ref_put(v_a_1403_, v___x_1429_);
if (v_isShared_1418_ == 0)
{
v___x_1432_ = v___x_1417_;
goto v_reusejp_1431_;
}
else
{
lean_object* v_reuseFailAlloc_1433_; 
v_reuseFailAlloc_1433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1433_, 0, v_a_1415_);
v___x_1432_ = v_reuseFailAlloc_1433_;
goto v_reusejp_1431_;
}
v_reusejp_1431_:
{
return v___x_1432_;
}
}
}
}
}
else
{
lean_dec_ref(v_e_1402_);
return v___y_1414_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of(lean_object* v_origExpr_1451_, lean_object* v_a_1452_, lean_object* v_a_1453_, lean_object* v_a_1454_, lean_object* v_a_1455_, lean_object* v_a_1456_, lean_object* v_a_1457_, lean_object* v_a_1458_, lean_object* v_a_1459_, lean_object* v_a_1460_){
_start:
{
lean_object* v___x_1462_; 
v___x_1462_ = l_Lean_Meta_Tactic_BVDecide_LemmaM_withBVPredCache___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_spec__5(v_origExpr_1451_, v_a_1452_, v_a_1453_, v_a_1454_, v_a_1455_, v_a_1456_, v_a_1457_, v_a_1458_, v_a_1459_, v_a_1460_);
return v___x_1462_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goPred(lean_object* v_origExpr_1463_, lean_object* v_a_1464_, lean_object* v_a_1465_, lean_object* v_a_1466_, lean_object* v_a_1467_, lean_object* v_a_1468_, lean_object* v_a_1469_, lean_object* v_a_1470_, lean_object* v_a_1471_, lean_object* v_a_1472_){
_start:
{
lean_object* v___x_1474_; 
v___x_1474_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of(v_origExpr_1463_, v_a_1464_, v_a_1465_, v_a_1466_, v_a_1467_, v_a_1468_, v_a_1469_, v_a_1470_, v_a_1471_, v_a_1472_);
if (lean_obj_tag(v___x_1474_) == 0)
{
lean_object* v_a_1475_; lean_object* v___x_1477_; uint8_t v_isShared_1478_; uint8_t v_isSharedCheck_1508_; 
v_a_1475_ = lean_ctor_get(v___x_1474_, 0);
v_isSharedCheck_1508_ = !lean_is_exclusive(v___x_1474_);
if (v_isSharedCheck_1508_ == 0)
{
v___x_1477_ = v___x_1474_;
v_isShared_1478_ = v_isSharedCheck_1508_;
goto v_resetjp_1476_;
}
else
{
lean_inc(v_a_1475_);
lean_dec(v___x_1474_);
v___x_1477_ = lean_box(0);
v_isShared_1478_ = v_isSharedCheck_1508_;
goto v_resetjp_1476_;
}
v_resetjp_1476_:
{
if (lean_obj_tag(v_a_1475_) == 1)
{
lean_object* v_val_1479_; lean_object* v___x_1481_; uint8_t v_isShared_1482_; uint8_t v_isSharedCheck_1503_; 
lean_del_object(v___x_1477_);
v_val_1479_ = lean_ctor_get(v_a_1475_, 0);
v_isSharedCheck_1503_ = !lean_is_exclusive(v_a_1475_);
if (v_isSharedCheck_1503_ == 0)
{
v___x_1481_ = v_a_1475_;
v_isShared_1482_ = v_isSharedCheck_1503_;
goto v_resetjp_1480_;
}
else
{
lean_inc(v_val_1479_);
lean_dec(v_a_1475_);
v___x_1481_ = lean_box(0);
v_isShared_1482_ = v_isSharedCheck_1503_;
goto v_resetjp_1480_;
}
v_resetjp_1480_:
{
lean_object* v___x_1483_; 
v___x_1483_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg(v_val_1479_, v_a_1467_, v_a_1468_, v_a_1469_, v_a_1470_, v_a_1471_, v_a_1472_);
if (lean_obj_tag(v___x_1483_) == 0)
{
lean_object* v_a_1484_; lean_object* v___x_1486_; uint8_t v_isShared_1487_; uint8_t v_isSharedCheck_1494_; 
v_a_1484_ = lean_ctor_get(v___x_1483_, 0);
v_isSharedCheck_1494_ = !lean_is_exclusive(v___x_1483_);
if (v_isSharedCheck_1494_ == 0)
{
v___x_1486_ = v___x_1483_;
v_isShared_1487_ = v_isSharedCheck_1494_;
goto v_resetjp_1485_;
}
else
{
lean_inc(v_a_1484_);
lean_dec(v___x_1483_);
v___x_1486_ = lean_box(0);
v_isShared_1487_ = v_isSharedCheck_1494_;
goto v_resetjp_1485_;
}
v_resetjp_1485_:
{
lean_object* v___x_1489_; 
if (v_isShared_1482_ == 0)
{
lean_ctor_set(v___x_1481_, 0, v_a_1484_);
v___x_1489_ = v___x_1481_;
goto v_reusejp_1488_;
}
else
{
lean_object* v_reuseFailAlloc_1493_; 
v_reuseFailAlloc_1493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1493_, 0, v_a_1484_);
v___x_1489_ = v_reuseFailAlloc_1493_;
goto v_reusejp_1488_;
}
v_reusejp_1488_:
{
lean_object* v___x_1491_; 
if (v_isShared_1487_ == 0)
{
lean_ctor_set(v___x_1486_, 0, v___x_1489_);
v___x_1491_ = v___x_1486_;
goto v_reusejp_1490_;
}
else
{
lean_object* v_reuseFailAlloc_1492_; 
v_reuseFailAlloc_1492_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1492_, 0, v___x_1489_);
v___x_1491_ = v_reuseFailAlloc_1492_;
goto v_reusejp_1490_;
}
v_reusejp_1490_:
{
return v___x_1491_;
}
}
}
}
else
{
lean_object* v_a_1495_; lean_object* v___x_1497_; uint8_t v_isShared_1498_; uint8_t v_isSharedCheck_1502_; 
lean_del_object(v___x_1481_);
v_a_1495_ = lean_ctor_get(v___x_1483_, 0);
v_isSharedCheck_1502_ = !lean_is_exclusive(v___x_1483_);
if (v_isSharedCheck_1502_ == 0)
{
v___x_1497_ = v___x_1483_;
v_isShared_1498_ = v_isSharedCheck_1502_;
goto v_resetjp_1496_;
}
else
{
lean_inc(v_a_1495_);
lean_dec(v___x_1483_);
v___x_1497_ = lean_box(0);
v_isShared_1498_ = v_isSharedCheck_1502_;
goto v_resetjp_1496_;
}
v_resetjp_1496_:
{
lean_object* v___x_1500_; 
if (v_isShared_1498_ == 0)
{
v___x_1500_ = v___x_1497_;
goto v_reusejp_1499_;
}
else
{
lean_object* v_reuseFailAlloc_1501_; 
v_reuseFailAlloc_1501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1501_, 0, v_a_1495_);
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
lean_object* v___x_1504_; lean_object* v___x_1506_; 
lean_dec(v_a_1475_);
v___x_1504_ = lean_box(0);
if (v_isShared_1478_ == 0)
{
lean_ctor_set(v___x_1477_, 0, v___x_1504_);
v___x_1506_ = v___x_1477_;
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
lean_object* v_a_1509_; lean_object* v___x_1511_; uint8_t v_isShared_1512_; uint8_t v_isSharedCheck_1516_; 
v_a_1509_ = lean_ctor_get(v___x_1474_, 0);
v_isSharedCheck_1516_ = !lean_is_exclusive(v___x_1474_);
if (v_isSharedCheck_1516_ == 0)
{
v___x_1511_ = v___x_1474_;
v_isShared_1512_ = v_isSharedCheck_1516_;
goto v_resetjp_1510_;
}
else
{
lean_inc(v_a_1509_);
lean_dec(v___x_1474_);
v___x_1511_ = lean_box(0);
v_isShared_1512_ = v_isSharedCheck_1516_;
goto v_resetjp_1510_;
}
v_resetjp_1510_:
{
lean_object* v___x_1514_; 
if (v_isShared_1512_ == 0)
{
v___x_1514_ = v___x_1511_;
goto v_reusejp_1513_;
}
else
{
lean_object* v_reuseFailAlloc_1515_; 
v_reuseFailAlloc_1515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1515_, 0, v_a_1509_);
v___x_1514_ = v_reuseFailAlloc_1515_;
goto v_reusejp_1513_;
}
v_reusejp_1513_:
{
return v___x_1514_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_gateReflection(lean_object* v_lhsExpr_1529_, lean_object* v_rhsExpr_1530_, uint8_t v_gate_1531_, lean_object* v_origExpr_1532_, lean_object* v_a_1533_, lean_object* v_a_1534_, lean_object* v_a_1535_, lean_object* v_a_1536_, lean_object* v_a_1537_, lean_object* v_a_1538_, lean_object* v_a_1539_, lean_object* v_a_1540_, lean_object* v_a_1541_){
_start:
{
lean_object* v___x_1543_; 
lean_inc_ref(v_lhsExpr_1529_);
v___x_1543_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom(v_lhsExpr_1529_, v_a_1533_, v_a_1534_, v_a_1535_, v_a_1536_, v_a_1537_, v_a_1538_, v_a_1539_, v_a_1540_, v_a_1541_);
if (lean_obj_tag(v___x_1543_) == 0)
{
lean_object* v_a_1544_; lean_object* v___x_1546_; uint8_t v_isShared_1547_; uint8_t v_isSharedCheck_1588_; 
v_a_1544_ = lean_ctor_get(v___x_1543_, 0);
v_isSharedCheck_1588_ = !lean_is_exclusive(v___x_1543_);
if (v_isSharedCheck_1588_ == 0)
{
v___x_1546_ = v___x_1543_;
v_isShared_1547_ = v_isSharedCheck_1588_;
goto v_resetjp_1545_;
}
else
{
lean_inc(v_a_1544_);
lean_dec(v___x_1543_);
v___x_1546_ = lean_box(0);
v_isShared_1547_ = v_isSharedCheck_1588_;
goto v_resetjp_1545_;
}
v_resetjp_1545_:
{
if (lean_obj_tag(v_a_1544_) == 1)
{
lean_object* v_val_1548_; lean_object* v___x_1549_; 
lean_del_object(v___x_1546_);
v_val_1548_ = lean_ctor_get(v_a_1544_, 0);
lean_inc(v_val_1548_);
lean_dec_ref_known(v_a_1544_, 1);
lean_inc_ref(v_rhsExpr_1530_);
v___x_1549_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom(v_rhsExpr_1530_, v_a_1533_, v_a_1534_, v_a_1535_, v_a_1536_, v_a_1537_, v_a_1538_, v_a_1539_, v_a_1540_, v_a_1541_);
if (lean_obj_tag(v___x_1549_) == 0)
{
lean_object* v_a_1550_; lean_object* v___x_1552_; uint8_t v_isShared_1553_; uint8_t v_isSharedCheck_1583_; 
v_a_1550_ = lean_ctor_get(v___x_1549_, 0);
v_isSharedCheck_1583_ = !lean_is_exclusive(v___x_1549_);
if (v_isSharedCheck_1583_ == 0)
{
v___x_1552_ = v___x_1549_;
v_isShared_1553_ = v_isSharedCheck_1583_;
goto v_resetjp_1551_;
}
else
{
lean_inc(v_a_1550_);
lean_dec(v___x_1549_);
v___x_1552_ = lean_box(0);
v_isShared_1553_ = v_isSharedCheck_1583_;
goto v_resetjp_1551_;
}
v_resetjp_1551_:
{
if (lean_obj_tag(v_a_1550_) == 1)
{
lean_object* v_val_1554_; lean_object* v___x_1556_; uint8_t v_isShared_1557_; uint8_t v_isSharedCheck_1578_; 
lean_del_object(v___x_1552_);
v_val_1554_ = lean_ctor_get(v_a_1550_, 0);
v_isSharedCheck_1578_ = !lean_is_exclusive(v_a_1550_);
if (v_isSharedCheck_1578_ == 0)
{
v___x_1556_ = v_a_1550_;
v_isShared_1557_ = v_isSharedCheck_1578_;
goto v_resetjp_1555_;
}
else
{
lean_inc(v_val_1554_);
lean_dec(v_a_1550_);
v___x_1556_ = lean_box(0);
v_isShared_1557_ = v_isSharedCheck_1578_;
goto v_resetjp_1555_;
}
v_resetjp_1555_:
{
lean_object* v___x_1558_; 
v___x_1558_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg(v_val_1548_, v_val_1554_, v_lhsExpr_1529_, v_rhsExpr_1530_, v_gate_1531_, v_origExpr_1532_, v_a_1536_, v_a_1537_, v_a_1538_, v_a_1539_, v_a_1540_, v_a_1541_);
if (lean_obj_tag(v___x_1558_) == 0)
{
lean_object* v_a_1559_; lean_object* v___x_1561_; uint8_t v_isShared_1562_; uint8_t v_isSharedCheck_1569_; 
v_a_1559_ = lean_ctor_get(v___x_1558_, 0);
v_isSharedCheck_1569_ = !lean_is_exclusive(v___x_1558_);
if (v_isSharedCheck_1569_ == 0)
{
v___x_1561_ = v___x_1558_;
v_isShared_1562_ = v_isSharedCheck_1569_;
goto v_resetjp_1560_;
}
else
{
lean_inc(v_a_1559_);
lean_dec(v___x_1558_);
v___x_1561_ = lean_box(0);
v_isShared_1562_ = v_isSharedCheck_1569_;
goto v_resetjp_1560_;
}
v_resetjp_1560_:
{
lean_object* v___x_1564_; 
if (v_isShared_1557_ == 0)
{
lean_ctor_set(v___x_1556_, 0, v_a_1559_);
v___x_1564_ = v___x_1556_;
goto v_reusejp_1563_;
}
else
{
lean_object* v_reuseFailAlloc_1568_; 
v_reuseFailAlloc_1568_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1568_, 0, v_a_1559_);
v___x_1564_ = v_reuseFailAlloc_1568_;
goto v_reusejp_1563_;
}
v_reusejp_1563_:
{
lean_object* v___x_1566_; 
if (v_isShared_1562_ == 0)
{
lean_ctor_set(v___x_1561_, 0, v___x_1564_);
v___x_1566_ = v___x_1561_;
goto v_reusejp_1565_;
}
else
{
lean_object* v_reuseFailAlloc_1567_; 
v_reuseFailAlloc_1567_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1567_, 0, v___x_1564_);
v___x_1566_ = v_reuseFailAlloc_1567_;
goto v_reusejp_1565_;
}
v_reusejp_1565_:
{
return v___x_1566_;
}
}
}
}
else
{
lean_object* v_a_1570_; lean_object* v___x_1572_; uint8_t v_isShared_1573_; uint8_t v_isSharedCheck_1577_; 
lean_del_object(v___x_1556_);
v_a_1570_ = lean_ctor_get(v___x_1558_, 0);
v_isSharedCheck_1577_ = !lean_is_exclusive(v___x_1558_);
if (v_isSharedCheck_1577_ == 0)
{
v___x_1572_ = v___x_1558_;
v_isShared_1573_ = v_isSharedCheck_1577_;
goto v_resetjp_1571_;
}
else
{
lean_inc(v_a_1570_);
lean_dec(v___x_1558_);
v___x_1572_ = lean_box(0);
v_isShared_1573_ = v_isSharedCheck_1577_;
goto v_resetjp_1571_;
}
v_resetjp_1571_:
{
lean_object* v___x_1575_; 
if (v_isShared_1573_ == 0)
{
v___x_1575_ = v___x_1572_;
goto v_reusejp_1574_;
}
else
{
lean_object* v_reuseFailAlloc_1576_; 
v_reuseFailAlloc_1576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1576_, 0, v_a_1570_);
v___x_1575_ = v_reuseFailAlloc_1576_;
goto v_reusejp_1574_;
}
v_reusejp_1574_:
{
return v___x_1575_;
}
}
}
}
}
else
{
lean_object* v___x_1579_; lean_object* v___x_1581_; 
lean_dec(v_a_1550_);
lean_dec(v_val_1548_);
lean_dec_ref(v_origExpr_1532_);
lean_dec_ref(v_rhsExpr_1530_);
lean_dec_ref(v_lhsExpr_1529_);
v___x_1579_ = lean_box(0);
if (v_isShared_1553_ == 0)
{
lean_ctor_set(v___x_1552_, 0, v___x_1579_);
v___x_1581_ = v___x_1552_;
goto v_reusejp_1580_;
}
else
{
lean_object* v_reuseFailAlloc_1582_; 
v_reuseFailAlloc_1582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1582_, 0, v___x_1579_);
v___x_1581_ = v_reuseFailAlloc_1582_;
goto v_reusejp_1580_;
}
v_reusejp_1580_:
{
return v___x_1581_;
}
}
}
}
else
{
lean_dec(v_val_1548_);
lean_dec_ref(v_origExpr_1532_);
lean_dec_ref(v_rhsExpr_1530_);
lean_dec_ref(v_lhsExpr_1529_);
return v___x_1549_;
}
}
else
{
lean_object* v___x_1584_; lean_object* v___x_1586_; 
lean_dec(v_a_1544_);
lean_dec_ref(v_origExpr_1532_);
lean_dec_ref(v_rhsExpr_1530_);
lean_dec_ref(v_lhsExpr_1529_);
v___x_1584_ = lean_box(0);
if (v_isShared_1547_ == 0)
{
lean_ctor_set(v___x_1546_, 0, v___x_1584_);
v___x_1586_ = v___x_1546_;
goto v_reusejp_1585_;
}
else
{
lean_object* v_reuseFailAlloc_1587_; 
v_reuseFailAlloc_1587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1587_, 0, v___x_1584_);
v___x_1586_ = v_reuseFailAlloc_1587_;
goto v_reusejp_1585_;
}
v_reusejp_1585_:
{
return v___x_1586_;
}
}
}
}
else
{
lean_dec_ref(v_origExpr_1532_);
lean_dec_ref(v_rhsExpr_1530_);
lean_dec_ref(v_lhsExpr_1529_);
return v___x_1543_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go(lean_object* v_origExpr_1589_, lean_object* v_a_1590_, lean_object* v_a_1591_, lean_object* v_a_1592_, lean_object* v_a_1593_, lean_object* v_a_1594_, lean_object* v_a_1595_, lean_object* v_a_1596_, lean_object* v_a_1597_, lean_object* v_a_1598_){
_start:
{
lean_object* v___x_1603_; lean_object* v___x_1604_; 
v___x_1603_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__0));
v___x_1604_ = l_Lean_Core_checkSystem(v___x_1603_, v_a_1597_, v_a_1598_);
if (lean_obj_tag(v___x_1604_) == 0)
{
lean_object* v___x_1605_; 
lean_dec_ref_known(v___x_1604_, 1);
lean_inc_ref(v_origExpr_1589_);
v___x_1605_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_origExpr_1589_, v_a_1596_);
if (lean_obj_tag(v___x_1605_) == 0)
{
lean_object* v_a_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; uint8_t v___x_1609_; 
v_a_1606_ = lean_ctor_get(v___x_1605_, 0);
lean_inc(v_a_1606_);
lean_dec_ref_known(v___x_1605_, 1);
v___x_1607_ = l_Lean_Expr_cleanupAnnotations(v_a_1606_);
v___x_1608_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__3));
v___x_1609_ = l_Lean_Expr_isConstOf(v___x_1607_, v___x_1608_);
if (v___x_1609_ == 0)
{
lean_object* v___x_1610_; uint8_t v___x_1611_; 
v___x_1610_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__5));
v___x_1611_ = l_Lean_Expr_isConstOf(v___x_1607_, v___x_1610_);
if (v___x_1611_ == 0)
{
uint8_t v___x_1612_; 
v___x_1612_ = l_Lean_Expr_isApp(v___x_1607_);
if (v___x_1612_ == 0)
{
lean_object* v___x_1613_; 
lean_dec_ref(v___x_1607_);
v___x_1613_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goPred(v_origExpr_1589_, v_a_1590_, v_a_1591_, v_a_1592_, v_a_1593_, v_a_1594_, v_a_1595_, v_a_1596_, v_a_1597_, v_a_1598_);
return v___x_1613_;
}
else
{
lean_object* v_arg_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; uint8_t v___x_1617_; 
v_arg_1614_ = lean_ctor_get(v___x_1607_, 1);
lean_inc_ref(v_arg_1614_);
v___x_1615_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1607_);
v___x_1616_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__6));
v___x_1617_ = l_Lean_Expr_isConstOf(v___x_1615_, v___x_1616_);
if (v___x_1617_ == 0)
{
uint8_t v___x_1618_; 
v___x_1618_ = l_Lean_Expr_isApp(v___x_1615_);
if (v___x_1618_ == 0)
{
lean_object* v___x_1619_; 
lean_dec_ref(v___x_1615_);
lean_dec_ref(v_arg_1614_);
v___x_1619_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goPred(v_origExpr_1589_, v_a_1590_, v_a_1591_, v_a_1592_, v_a_1593_, v_a_1594_, v_a_1595_, v_a_1596_, v_a_1597_, v_a_1598_);
return v___x_1619_;
}
else
{
lean_object* v_arg_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; uint8_t v___x_1623_; 
v_arg_1620_ = lean_ctor_get(v___x_1615_, 1);
lean_inc_ref(v_arg_1620_);
v___x_1621_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1615_);
v___x_1622_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__7));
v___x_1623_ = l_Lean_Expr_isConstOf(v___x_1621_, v___x_1622_);
if (v___x_1623_ == 0)
{
lean_object* v___x_1624_; uint8_t v___x_1625_; 
v___x_1624_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__8));
v___x_1625_ = l_Lean_Expr_isConstOf(v___x_1621_, v___x_1624_);
if (v___x_1625_ == 0)
{
uint8_t v___x_1626_; 
v___x_1626_ = l_Lean_Expr_isApp(v___x_1621_);
if (v___x_1626_ == 0)
{
lean_object* v___x_1627_; 
lean_dec_ref(v___x_1621_);
lean_dec_ref(v_arg_1620_);
lean_dec_ref(v_arg_1614_);
v___x_1627_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goPred(v_origExpr_1589_, v_a_1590_, v_a_1591_, v_a_1592_, v_a_1593_, v_a_1594_, v_a_1595_, v_a_1596_, v_a_1597_, v_a_1598_);
return v___x_1627_;
}
else
{
lean_object* v_arg_1628_; lean_object* v___x_1629_; uint8_t v___x_1630_; 
v_arg_1628_ = lean_ctor_get(v___x_1621_, 1);
lean_inc_ref(v_arg_1628_);
v___x_1629_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1621_);
v___x_1630_ = l_Lean_Expr_isApp(v___x_1629_);
if (v___x_1630_ == 0)
{
lean_object* v___x_1631_; 
lean_dec_ref(v___x_1629_);
lean_dec_ref(v_arg_1628_);
lean_dec_ref(v_arg_1620_);
lean_dec_ref(v_arg_1614_);
v___x_1631_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goPred(v_origExpr_1589_, v_a_1590_, v_a_1591_, v_a_1592_, v_a_1593_, v_a_1594_, v_a_1595_, v_a_1596_, v_a_1597_, v_a_1598_);
return v___x_1631_;
}
else
{
lean_object* v_arg_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; uint8_t v___x_1635_; 
v_arg_1632_ = lean_ctor_get(v___x_1629_, 1);
lean_inc_ref(v_arg_1632_);
v___x_1633_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1629_);
v___x_1634_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__10));
v___x_1635_ = l_Lean_Expr_isConstOf(v___x_1633_, v___x_1634_);
if (v___x_1635_ == 0)
{
lean_object* v___x_1636_; uint8_t v___x_1637_; 
lean_dec_ref(v_arg_1628_);
v___x_1636_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__7));
v___x_1637_ = l_Lean_Expr_isConstOf(v___x_1633_, v___x_1636_);
lean_dec_ref(v___x_1633_);
if (v___x_1637_ == 0)
{
lean_object* v___x_1638_; 
lean_dec_ref(v_arg_1632_);
lean_dec_ref(v_arg_1620_);
lean_dec_ref(v_arg_1614_);
v___x_1638_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goPred(v_origExpr_1589_, v_a_1590_, v_a_1591_, v_a_1592_, v_a_1593_, v_a_1594_, v_a_1595_, v_a_1596_, v_a_1597_, v_a_1598_);
return v___x_1638_;
}
else
{
lean_object* v___x_1639_; 
v___x_1639_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_arg_1632_, v_a_1596_);
if (lean_obj_tag(v___x_1639_) == 0)
{
lean_object* v_a_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; uint8_t v___x_1643_; 
v_a_1640_ = lean_ctor_get(v___x_1639_, 0);
lean_inc(v_a_1640_);
lean_dec_ref_known(v___x_1639_, 1);
v___x_1641_ = l_Lean_Expr_cleanupAnnotations(v_a_1640_);
v___x_1642_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__11));
v___x_1643_ = l_Lean_Expr_isConstOf(v___x_1641_, v___x_1642_);
if (v___x_1643_ == 0)
{
uint8_t v___x_1644_; 
lean_dec_ref(v_arg_1620_);
lean_dec_ref(v_arg_1614_);
v___x_1644_ = l_Lean_Expr_isApp(v___x_1641_);
if (v___x_1644_ == 0)
{
lean_dec_ref(v___x_1641_);
lean_dec_ref(v_origExpr_1589_);
goto v___jp_1600_;
}
else
{
lean_object* v___x_1645_; lean_object* v___x_1646_; uint8_t v___x_1647_; 
v___x_1645_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1641_);
v___x_1646_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__8));
v___x_1647_ = l_Lean_Expr_isConstOf(v___x_1645_, v___x_1646_);
lean_dec_ref(v___x_1645_);
if (v___x_1647_ == 0)
{
lean_dec_ref(v_origExpr_1589_);
goto v___jp_1600_;
}
else
{
lean_object* v___x_1648_; 
v___x_1648_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goPred(v_origExpr_1589_, v_a_1590_, v_a_1591_, v_a_1592_, v_a_1593_, v_a_1594_, v_a_1595_, v_a_1596_, v_a_1597_, v_a_1598_);
return v___x_1648_;
}
}
}
else
{
uint8_t v___x_1649_; lean_object* v___x_1650_; 
lean_dec_ref(v___x_1641_);
v___x_1649_ = 2;
v___x_1650_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_gateReflection(v_arg_1620_, v_arg_1614_, v___x_1649_, v_origExpr_1589_, v_a_1590_, v_a_1591_, v_a_1592_, v_a_1593_, v_a_1594_, v_a_1595_, v_a_1596_, v_a_1597_, v_a_1598_);
return v___x_1650_;
}
}
else
{
lean_object* v_a_1651_; lean_object* v___x_1653_; uint8_t v_isShared_1654_; uint8_t v_isSharedCheck_1658_; 
lean_dec_ref(v_arg_1620_);
lean_dec_ref(v_arg_1614_);
lean_dec_ref(v_origExpr_1589_);
v_a_1651_ = lean_ctor_get(v___x_1639_, 0);
v_isSharedCheck_1658_ = !lean_is_exclusive(v___x_1639_);
if (v_isSharedCheck_1658_ == 0)
{
v___x_1653_ = v___x_1639_;
v_isShared_1654_ = v_isSharedCheck_1658_;
goto v_resetjp_1652_;
}
else
{
lean_inc(v_a_1651_);
lean_dec(v___x_1639_);
v___x_1653_ = lean_box(0);
v_isShared_1654_ = v_isSharedCheck_1658_;
goto v_resetjp_1652_;
}
v_resetjp_1652_:
{
lean_object* v___x_1656_; 
if (v_isShared_1654_ == 0)
{
v___x_1656_ = v___x_1653_;
goto v_reusejp_1655_;
}
else
{
lean_object* v_reuseFailAlloc_1657_; 
v_reuseFailAlloc_1657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1657_, 0, v_a_1651_);
v___x_1656_ = v_reuseFailAlloc_1657_;
goto v_reusejp_1655_;
}
v_reusejp_1655_:
{
return v___x_1656_;
}
}
}
}
}
else
{
lean_object* v___x_1659_; 
lean_dec_ref(v___x_1633_);
lean_dec_ref(v_arg_1632_);
lean_inc_ref(v_arg_1628_);
v___x_1659_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom(v_arg_1628_, v_a_1590_, v_a_1591_, v_a_1592_, v_a_1593_, v_a_1594_, v_a_1595_, v_a_1596_, v_a_1597_, v_a_1598_);
if (lean_obj_tag(v___x_1659_) == 0)
{
lean_object* v_a_1660_; lean_object* v___x_1662_; uint8_t v_isShared_1663_; uint8_t v_isSharedCheck_1715_; 
v_a_1660_ = lean_ctor_get(v___x_1659_, 0);
v_isSharedCheck_1715_ = !lean_is_exclusive(v___x_1659_);
if (v_isSharedCheck_1715_ == 0)
{
v___x_1662_ = v___x_1659_;
v_isShared_1663_ = v_isSharedCheck_1715_;
goto v_resetjp_1661_;
}
else
{
lean_inc(v_a_1660_);
lean_dec(v___x_1659_);
v___x_1662_ = lean_box(0);
v_isShared_1663_ = v_isSharedCheck_1715_;
goto v_resetjp_1661_;
}
v_resetjp_1661_:
{
if (lean_obj_tag(v_a_1660_) == 1)
{
lean_object* v_val_1664_; lean_object* v___x_1665_; 
lean_del_object(v___x_1662_);
v_val_1664_ = lean_ctor_get(v_a_1660_, 0);
lean_inc(v_val_1664_);
lean_dec_ref_known(v_a_1660_, 1);
lean_inc_ref(v_arg_1620_);
v___x_1665_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom(v_arg_1620_, v_a_1590_, v_a_1591_, v_a_1592_, v_a_1593_, v_a_1594_, v_a_1595_, v_a_1596_, v_a_1597_, v_a_1598_);
if (lean_obj_tag(v___x_1665_) == 0)
{
lean_object* v_a_1666_; lean_object* v___x_1668_; uint8_t v_isShared_1669_; uint8_t v_isSharedCheck_1710_; 
v_a_1666_ = lean_ctor_get(v___x_1665_, 0);
v_isSharedCheck_1710_ = !lean_is_exclusive(v___x_1665_);
if (v_isSharedCheck_1710_ == 0)
{
v___x_1668_ = v___x_1665_;
v_isShared_1669_ = v_isSharedCheck_1710_;
goto v_resetjp_1667_;
}
else
{
lean_inc(v_a_1666_);
lean_dec(v___x_1665_);
v___x_1668_ = lean_box(0);
v_isShared_1669_ = v_isSharedCheck_1710_;
goto v_resetjp_1667_;
}
v_resetjp_1667_:
{
if (lean_obj_tag(v_a_1666_) == 1)
{
lean_object* v_val_1670_; lean_object* v___x_1671_; 
lean_del_object(v___x_1668_);
v_val_1670_ = lean_ctor_get(v_a_1666_, 0);
lean_inc(v_val_1670_);
lean_dec_ref_known(v_a_1666_, 1);
lean_inc_ref(v_arg_1614_);
v___x_1671_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom(v_arg_1614_, v_a_1590_, v_a_1591_, v_a_1592_, v_a_1593_, v_a_1594_, v_a_1595_, v_a_1596_, v_a_1597_, v_a_1598_);
if (lean_obj_tag(v___x_1671_) == 0)
{
lean_object* v_a_1672_; lean_object* v___x_1674_; uint8_t v_isShared_1675_; uint8_t v_isSharedCheck_1705_; 
v_a_1672_ = lean_ctor_get(v___x_1671_, 0);
v_isSharedCheck_1705_ = !lean_is_exclusive(v___x_1671_);
if (v_isSharedCheck_1705_ == 0)
{
v___x_1674_ = v___x_1671_;
v_isShared_1675_ = v_isSharedCheck_1705_;
goto v_resetjp_1673_;
}
else
{
lean_inc(v_a_1672_);
lean_dec(v___x_1671_);
v___x_1674_ = lean_box(0);
v_isShared_1675_ = v_isSharedCheck_1705_;
goto v_resetjp_1673_;
}
v_resetjp_1673_:
{
if (lean_obj_tag(v_a_1672_) == 1)
{
lean_object* v_val_1676_; lean_object* v___x_1678_; uint8_t v_isShared_1679_; uint8_t v_isSharedCheck_1700_; 
lean_del_object(v___x_1674_);
v_val_1676_ = lean_ctor_get(v_a_1672_, 0);
v_isSharedCheck_1700_ = !lean_is_exclusive(v_a_1672_);
if (v_isSharedCheck_1700_ == 0)
{
v___x_1678_ = v_a_1672_;
v_isShared_1679_ = v_isSharedCheck_1700_;
goto v_resetjp_1677_;
}
else
{
lean_inc(v_val_1676_);
lean_dec(v_a_1672_);
v___x_1678_ = lean_box(0);
v_isShared_1679_ = v_isSharedCheck_1700_;
goto v_resetjp_1677_;
}
v_resetjp_1677_:
{
lean_object* v___x_1680_; 
v___x_1680_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkIte___redArg(v_val_1664_, v_val_1670_, v_val_1676_, v_arg_1628_, v_arg_1620_, v_arg_1614_, v_origExpr_1589_, v_a_1593_, v_a_1594_, v_a_1595_, v_a_1596_, v_a_1597_, v_a_1598_);
if (lean_obj_tag(v___x_1680_) == 0)
{
lean_object* v_a_1681_; lean_object* v___x_1683_; uint8_t v_isShared_1684_; uint8_t v_isSharedCheck_1691_; 
v_a_1681_ = lean_ctor_get(v___x_1680_, 0);
v_isSharedCheck_1691_ = !lean_is_exclusive(v___x_1680_);
if (v_isSharedCheck_1691_ == 0)
{
v___x_1683_ = v___x_1680_;
v_isShared_1684_ = v_isSharedCheck_1691_;
goto v_resetjp_1682_;
}
else
{
lean_inc(v_a_1681_);
lean_dec(v___x_1680_);
v___x_1683_ = lean_box(0);
v_isShared_1684_ = v_isSharedCheck_1691_;
goto v_resetjp_1682_;
}
v_resetjp_1682_:
{
lean_object* v___x_1686_; 
if (v_isShared_1679_ == 0)
{
lean_ctor_set(v___x_1678_, 0, v_a_1681_);
v___x_1686_ = v___x_1678_;
goto v_reusejp_1685_;
}
else
{
lean_object* v_reuseFailAlloc_1690_; 
v_reuseFailAlloc_1690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1690_, 0, v_a_1681_);
v___x_1686_ = v_reuseFailAlloc_1690_;
goto v_reusejp_1685_;
}
v_reusejp_1685_:
{
lean_object* v___x_1688_; 
if (v_isShared_1684_ == 0)
{
lean_ctor_set(v___x_1683_, 0, v___x_1686_);
v___x_1688_ = v___x_1683_;
goto v_reusejp_1687_;
}
else
{
lean_object* v_reuseFailAlloc_1689_; 
v_reuseFailAlloc_1689_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1689_, 0, v___x_1686_);
v___x_1688_ = v_reuseFailAlloc_1689_;
goto v_reusejp_1687_;
}
v_reusejp_1687_:
{
return v___x_1688_;
}
}
}
}
else
{
lean_object* v_a_1692_; lean_object* v___x_1694_; uint8_t v_isShared_1695_; uint8_t v_isSharedCheck_1699_; 
lean_del_object(v___x_1678_);
v_a_1692_ = lean_ctor_get(v___x_1680_, 0);
v_isSharedCheck_1699_ = !lean_is_exclusive(v___x_1680_);
if (v_isSharedCheck_1699_ == 0)
{
v___x_1694_ = v___x_1680_;
v_isShared_1695_ = v_isSharedCheck_1699_;
goto v_resetjp_1693_;
}
else
{
lean_inc(v_a_1692_);
lean_dec(v___x_1680_);
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
}
else
{
lean_object* v___x_1701_; lean_object* v___x_1703_; 
lean_dec(v_a_1672_);
lean_dec(v_val_1670_);
lean_dec(v_val_1664_);
lean_dec_ref(v_arg_1628_);
lean_dec_ref(v_arg_1620_);
lean_dec_ref(v_arg_1614_);
lean_dec_ref(v_origExpr_1589_);
v___x_1701_ = lean_box(0);
if (v_isShared_1675_ == 0)
{
lean_ctor_set(v___x_1674_, 0, v___x_1701_);
v___x_1703_ = v___x_1674_;
goto v_reusejp_1702_;
}
else
{
lean_object* v_reuseFailAlloc_1704_; 
v_reuseFailAlloc_1704_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1704_, 0, v___x_1701_);
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
else
{
lean_dec(v_val_1670_);
lean_dec(v_val_1664_);
lean_dec_ref(v_arg_1628_);
lean_dec_ref(v_arg_1620_);
lean_dec_ref(v_arg_1614_);
lean_dec_ref(v_origExpr_1589_);
return v___x_1671_;
}
}
else
{
lean_object* v___x_1706_; lean_object* v___x_1708_; 
lean_dec(v_a_1666_);
lean_dec(v_val_1664_);
lean_dec_ref(v_arg_1628_);
lean_dec_ref(v_arg_1620_);
lean_dec_ref(v_arg_1614_);
lean_dec_ref(v_origExpr_1589_);
v___x_1706_ = lean_box(0);
if (v_isShared_1669_ == 0)
{
lean_ctor_set(v___x_1668_, 0, v___x_1706_);
v___x_1708_ = v___x_1668_;
goto v_reusejp_1707_;
}
else
{
lean_object* v_reuseFailAlloc_1709_; 
v_reuseFailAlloc_1709_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1709_, 0, v___x_1706_);
v___x_1708_ = v_reuseFailAlloc_1709_;
goto v_reusejp_1707_;
}
v_reusejp_1707_:
{
return v___x_1708_;
}
}
}
}
else
{
lean_dec(v_val_1664_);
lean_dec_ref(v_arg_1628_);
lean_dec_ref(v_arg_1620_);
lean_dec_ref(v_arg_1614_);
lean_dec_ref(v_origExpr_1589_);
return v___x_1665_;
}
}
else
{
lean_object* v___x_1711_; lean_object* v___x_1713_; 
lean_dec(v_a_1660_);
lean_dec_ref(v_arg_1628_);
lean_dec_ref(v_arg_1620_);
lean_dec_ref(v_arg_1614_);
lean_dec_ref(v_origExpr_1589_);
v___x_1711_ = lean_box(0);
if (v_isShared_1663_ == 0)
{
lean_ctor_set(v___x_1662_, 0, v___x_1711_);
v___x_1713_ = v___x_1662_;
goto v_reusejp_1712_;
}
else
{
lean_object* v_reuseFailAlloc_1714_; 
v_reuseFailAlloc_1714_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1714_, 0, v___x_1711_);
v___x_1713_ = v_reuseFailAlloc_1714_;
goto v_reusejp_1712_;
}
v_reusejp_1712_:
{
return v___x_1713_;
}
}
}
}
else
{
lean_dec_ref(v_arg_1628_);
lean_dec_ref(v_arg_1620_);
lean_dec_ref(v_arg_1614_);
lean_dec_ref(v_origExpr_1589_);
return v___x_1659_;
}
}
}
}
}
else
{
uint8_t v___x_1716_; lean_object* v___x_1717_; 
lean_dec_ref(v___x_1621_);
v___x_1716_ = 0;
v___x_1717_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_gateReflection(v_arg_1620_, v_arg_1614_, v___x_1716_, v_origExpr_1589_, v_a_1590_, v_a_1591_, v_a_1592_, v_a_1593_, v_a_1594_, v_a_1595_, v_a_1596_, v_a_1597_, v_a_1598_);
return v___x_1717_;
}
}
else
{
uint8_t v___x_1718_; lean_object* v___x_1719_; 
lean_dec_ref(v___x_1621_);
v___x_1718_ = 1;
v___x_1719_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_gateReflection(v_arg_1620_, v_arg_1614_, v___x_1718_, v_origExpr_1589_, v_a_1590_, v_a_1591_, v_a_1592_, v_a_1593_, v_a_1594_, v_a_1595_, v_a_1596_, v_a_1597_, v_a_1598_);
return v___x_1719_;
}
}
}
else
{
lean_object* v___x_1720_; 
lean_dec_ref(v___x_1615_);
lean_inc_ref(v_arg_1614_);
v___x_1720_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom(v_arg_1614_, v_a_1590_, v_a_1591_, v_a_1592_, v_a_1593_, v_a_1594_, v_a_1595_, v_a_1596_, v_a_1597_, v_a_1598_);
if (lean_obj_tag(v___x_1720_) == 0)
{
lean_object* v_a_1721_; lean_object* v___x_1723_; uint8_t v_isShared_1724_; uint8_t v_isSharedCheck_1754_; 
v_a_1721_ = lean_ctor_get(v___x_1720_, 0);
v_isSharedCheck_1754_ = !lean_is_exclusive(v___x_1720_);
if (v_isSharedCheck_1754_ == 0)
{
v___x_1723_ = v___x_1720_;
v_isShared_1724_ = v_isSharedCheck_1754_;
goto v_resetjp_1722_;
}
else
{
lean_inc(v_a_1721_);
lean_dec(v___x_1720_);
v___x_1723_ = lean_box(0);
v_isShared_1724_ = v_isSharedCheck_1754_;
goto v_resetjp_1722_;
}
v_resetjp_1722_:
{
if (lean_obj_tag(v_a_1721_) == 1)
{
lean_object* v_val_1725_; lean_object* v___x_1727_; uint8_t v_isShared_1728_; uint8_t v_isSharedCheck_1749_; 
lean_del_object(v___x_1723_);
v_val_1725_ = lean_ctor_get(v_a_1721_, 0);
v_isSharedCheck_1749_ = !lean_is_exclusive(v_a_1721_);
if (v_isSharedCheck_1749_ == 0)
{
v___x_1727_ = v_a_1721_;
v_isShared_1728_ = v_isSharedCheck_1749_;
goto v_resetjp_1726_;
}
else
{
lean_inc(v_val_1725_);
lean_dec(v_a_1721_);
v___x_1727_ = lean_box(0);
v_isShared_1728_ = v_isSharedCheck_1749_;
goto v_resetjp_1726_;
}
v_resetjp_1726_:
{
lean_object* v___x_1729_; 
v___x_1729_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkNot___redArg(v_val_1725_, v_arg_1614_, v_origExpr_1589_, v_a_1593_, v_a_1594_, v_a_1595_, v_a_1596_, v_a_1597_, v_a_1598_);
if (lean_obj_tag(v___x_1729_) == 0)
{
lean_object* v_a_1730_; lean_object* v___x_1732_; uint8_t v_isShared_1733_; uint8_t v_isSharedCheck_1740_; 
v_a_1730_ = lean_ctor_get(v___x_1729_, 0);
v_isSharedCheck_1740_ = !lean_is_exclusive(v___x_1729_);
if (v_isSharedCheck_1740_ == 0)
{
v___x_1732_ = v___x_1729_;
v_isShared_1733_ = v_isSharedCheck_1740_;
goto v_resetjp_1731_;
}
else
{
lean_inc(v_a_1730_);
lean_dec(v___x_1729_);
v___x_1732_ = lean_box(0);
v_isShared_1733_ = v_isSharedCheck_1740_;
goto v_resetjp_1731_;
}
v_resetjp_1731_:
{
lean_object* v___x_1735_; 
if (v_isShared_1728_ == 0)
{
lean_ctor_set(v___x_1727_, 0, v_a_1730_);
v___x_1735_ = v___x_1727_;
goto v_reusejp_1734_;
}
else
{
lean_object* v_reuseFailAlloc_1739_; 
v_reuseFailAlloc_1739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1739_, 0, v_a_1730_);
v___x_1735_ = v_reuseFailAlloc_1739_;
goto v_reusejp_1734_;
}
v_reusejp_1734_:
{
lean_object* v___x_1737_; 
if (v_isShared_1733_ == 0)
{
lean_ctor_set(v___x_1732_, 0, v___x_1735_);
v___x_1737_ = v___x_1732_;
goto v_reusejp_1736_;
}
else
{
lean_object* v_reuseFailAlloc_1738_; 
v_reuseFailAlloc_1738_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1738_, 0, v___x_1735_);
v___x_1737_ = v_reuseFailAlloc_1738_;
goto v_reusejp_1736_;
}
v_reusejp_1736_:
{
return v___x_1737_;
}
}
}
}
else
{
lean_object* v_a_1741_; lean_object* v___x_1743_; uint8_t v_isShared_1744_; uint8_t v_isSharedCheck_1748_; 
lean_del_object(v___x_1727_);
v_a_1741_ = lean_ctor_get(v___x_1729_, 0);
v_isSharedCheck_1748_ = !lean_is_exclusive(v___x_1729_);
if (v_isSharedCheck_1748_ == 0)
{
v___x_1743_ = v___x_1729_;
v_isShared_1744_ = v_isSharedCheck_1748_;
goto v_resetjp_1742_;
}
else
{
lean_inc(v_a_1741_);
lean_dec(v___x_1729_);
v___x_1743_ = lean_box(0);
v_isShared_1744_ = v_isSharedCheck_1748_;
goto v_resetjp_1742_;
}
v_resetjp_1742_:
{
lean_object* v___x_1746_; 
if (v_isShared_1744_ == 0)
{
v___x_1746_ = v___x_1743_;
goto v_reusejp_1745_;
}
else
{
lean_object* v_reuseFailAlloc_1747_; 
v_reuseFailAlloc_1747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1747_, 0, v_a_1741_);
v___x_1746_ = v_reuseFailAlloc_1747_;
goto v_reusejp_1745_;
}
v_reusejp_1745_:
{
return v___x_1746_;
}
}
}
}
}
else
{
lean_object* v___x_1750_; lean_object* v___x_1752_; 
lean_dec(v_a_1721_);
lean_dec_ref(v_arg_1614_);
lean_dec_ref(v_origExpr_1589_);
v___x_1750_ = lean_box(0);
if (v_isShared_1724_ == 0)
{
lean_ctor_set(v___x_1723_, 0, v___x_1750_);
v___x_1752_ = v___x_1723_;
goto v_reusejp_1751_;
}
else
{
lean_object* v_reuseFailAlloc_1753_; 
v_reuseFailAlloc_1753_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1753_, 0, v___x_1750_);
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
else
{
lean_dec_ref(v_arg_1614_);
lean_dec_ref(v_origExpr_1589_);
return v___x_1720_;
}
}
}
}
else
{
lean_object* v___x_1755_; 
lean_dec_ref(v___x_1607_);
lean_dec_ref(v_origExpr_1589_);
v___x_1755_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg(v___x_1611_, v_a_1593_, v_a_1594_, v_a_1595_, v_a_1596_, v_a_1597_, v_a_1598_);
if (lean_obj_tag(v___x_1755_) == 0)
{
lean_object* v_a_1756_; lean_object* v___x_1758_; uint8_t v_isShared_1759_; uint8_t v_isSharedCheck_1764_; 
v_a_1756_ = lean_ctor_get(v___x_1755_, 0);
v_isSharedCheck_1764_ = !lean_is_exclusive(v___x_1755_);
if (v_isSharedCheck_1764_ == 0)
{
v___x_1758_ = v___x_1755_;
v_isShared_1759_ = v_isSharedCheck_1764_;
goto v_resetjp_1757_;
}
else
{
lean_inc(v_a_1756_);
lean_dec(v___x_1755_);
v___x_1758_ = lean_box(0);
v_isShared_1759_ = v_isSharedCheck_1764_;
goto v_resetjp_1757_;
}
v_resetjp_1757_:
{
lean_object* v___x_1760_; lean_object* v___x_1762_; 
v___x_1760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1760_, 0, v_a_1756_);
if (v_isShared_1759_ == 0)
{
lean_ctor_set(v___x_1758_, 0, v___x_1760_);
v___x_1762_ = v___x_1758_;
goto v_reusejp_1761_;
}
else
{
lean_object* v_reuseFailAlloc_1763_; 
v_reuseFailAlloc_1763_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1763_, 0, v___x_1760_);
v___x_1762_ = v_reuseFailAlloc_1763_;
goto v_reusejp_1761_;
}
v_reusejp_1761_:
{
return v___x_1762_;
}
}
}
else
{
lean_object* v_a_1765_; lean_object* v___x_1767_; uint8_t v_isShared_1768_; uint8_t v_isSharedCheck_1772_; 
v_a_1765_ = lean_ctor_get(v___x_1755_, 0);
v_isSharedCheck_1772_ = !lean_is_exclusive(v___x_1755_);
if (v_isSharedCheck_1772_ == 0)
{
v___x_1767_ = v___x_1755_;
v_isShared_1768_ = v_isSharedCheck_1772_;
goto v_resetjp_1766_;
}
else
{
lean_inc(v_a_1765_);
lean_dec(v___x_1755_);
v___x_1767_ = lean_box(0);
v_isShared_1768_ = v_isSharedCheck_1772_;
goto v_resetjp_1766_;
}
v_resetjp_1766_:
{
lean_object* v___x_1770_; 
if (v_isShared_1768_ == 0)
{
v___x_1770_ = v___x_1767_;
goto v_reusejp_1769_;
}
else
{
lean_object* v_reuseFailAlloc_1771_; 
v_reuseFailAlloc_1771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1771_, 0, v_a_1765_);
v___x_1770_ = v_reuseFailAlloc_1771_;
goto v_reusejp_1769_;
}
v_reusejp_1769_:
{
return v___x_1770_;
}
}
}
}
}
else
{
uint8_t v___x_1773_; lean_object* v___x_1774_; 
lean_dec_ref(v___x_1607_);
lean_dec_ref(v_origExpr_1589_);
v___x_1773_ = 0;
v___x_1774_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg(v___x_1773_, v_a_1593_, v_a_1594_, v_a_1595_, v_a_1596_, v_a_1597_, v_a_1598_);
if (lean_obj_tag(v___x_1774_) == 0)
{
lean_object* v_a_1775_; lean_object* v___x_1777_; uint8_t v_isShared_1778_; uint8_t v_isSharedCheck_1783_; 
v_a_1775_ = lean_ctor_get(v___x_1774_, 0);
v_isSharedCheck_1783_ = !lean_is_exclusive(v___x_1774_);
if (v_isSharedCheck_1783_ == 0)
{
v___x_1777_ = v___x_1774_;
v_isShared_1778_ = v_isSharedCheck_1783_;
goto v_resetjp_1776_;
}
else
{
lean_inc(v_a_1775_);
lean_dec(v___x_1774_);
v___x_1777_ = lean_box(0);
v_isShared_1778_ = v_isSharedCheck_1783_;
goto v_resetjp_1776_;
}
v_resetjp_1776_:
{
lean_object* v___x_1779_; lean_object* v___x_1781_; 
v___x_1779_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1779_, 0, v_a_1775_);
if (v_isShared_1778_ == 0)
{
lean_ctor_set(v___x_1777_, 0, v___x_1779_);
v___x_1781_ = v___x_1777_;
goto v_reusejp_1780_;
}
else
{
lean_object* v_reuseFailAlloc_1782_; 
v_reuseFailAlloc_1782_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1782_, 0, v___x_1779_);
v___x_1781_ = v_reuseFailAlloc_1782_;
goto v_reusejp_1780_;
}
v_reusejp_1780_:
{
return v___x_1781_;
}
}
}
else
{
lean_object* v_a_1784_; lean_object* v___x_1786_; uint8_t v_isShared_1787_; uint8_t v_isSharedCheck_1791_; 
v_a_1784_ = lean_ctor_get(v___x_1774_, 0);
v_isSharedCheck_1791_ = !lean_is_exclusive(v___x_1774_);
if (v_isSharedCheck_1791_ == 0)
{
v___x_1786_ = v___x_1774_;
v_isShared_1787_ = v_isSharedCheck_1791_;
goto v_resetjp_1785_;
}
else
{
lean_inc(v_a_1784_);
lean_dec(v___x_1774_);
v___x_1786_ = lean_box(0);
v_isShared_1787_ = v_isSharedCheck_1791_;
goto v_resetjp_1785_;
}
v_resetjp_1785_:
{
lean_object* v___x_1789_; 
if (v_isShared_1787_ == 0)
{
v___x_1789_ = v___x_1786_;
goto v_reusejp_1788_;
}
else
{
lean_object* v_reuseFailAlloc_1790_; 
v_reuseFailAlloc_1790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1790_, 0, v_a_1784_);
v___x_1789_ = v_reuseFailAlloc_1790_;
goto v_reusejp_1788_;
}
v_reusejp_1788_:
{
return v___x_1789_;
}
}
}
}
}
else
{
lean_object* v_a_1792_; lean_object* v___x_1794_; uint8_t v_isShared_1795_; uint8_t v_isSharedCheck_1799_; 
lean_dec_ref(v_origExpr_1589_);
v_a_1792_ = lean_ctor_get(v___x_1605_, 0);
v_isSharedCheck_1799_ = !lean_is_exclusive(v___x_1605_);
if (v_isSharedCheck_1799_ == 0)
{
v___x_1794_ = v___x_1605_;
v_isShared_1795_ = v_isSharedCheck_1799_;
goto v_resetjp_1793_;
}
else
{
lean_inc(v_a_1792_);
lean_dec(v___x_1605_);
v___x_1794_ = lean_box(0);
v_isShared_1795_ = v_isSharedCheck_1799_;
goto v_resetjp_1793_;
}
v_resetjp_1793_:
{
lean_object* v___x_1797_; 
if (v_isShared_1795_ == 0)
{
v___x_1797_ = v___x_1794_;
goto v_reusejp_1796_;
}
else
{
lean_object* v_reuseFailAlloc_1798_; 
v_reuseFailAlloc_1798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1798_, 0, v_a_1792_);
v___x_1797_ = v_reuseFailAlloc_1798_;
goto v_reusejp_1796_;
}
v_reusejp_1796_:
{
return v___x_1797_;
}
}
}
}
else
{
lean_object* v_a_1800_; lean_object* v___x_1802_; uint8_t v_isShared_1803_; uint8_t v_isSharedCheck_1807_; 
lean_dec_ref(v_origExpr_1589_);
v_a_1800_ = lean_ctor_get(v___x_1604_, 0);
v_isSharedCheck_1807_ = !lean_is_exclusive(v___x_1604_);
if (v_isSharedCheck_1807_ == 0)
{
v___x_1802_ = v___x_1604_;
v_isShared_1803_ = v_isSharedCheck_1807_;
goto v_resetjp_1801_;
}
else
{
lean_inc(v_a_1800_);
lean_dec(v___x_1604_);
v___x_1802_ = lean_box(0);
v_isShared_1803_ = v_isSharedCheck_1807_;
goto v_resetjp_1801_;
}
v_resetjp_1801_:
{
lean_object* v___x_1805_; 
if (v_isShared_1803_ == 0)
{
v___x_1805_ = v___x_1802_;
goto v_reusejp_1804_;
}
else
{
lean_object* v_reuseFailAlloc_1806_; 
v_reuseFailAlloc_1806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1806_, 0, v_a_1800_);
v___x_1805_ = v_reuseFailAlloc_1806_;
goto v_reusejp_1804_;
}
v_reusejp_1804_:
{
return v___x_1805_;
}
}
}
v___jp_1600_:
{
lean_object* v___x_1601_; lean_object* v___x_1602_; 
v___x_1601_ = lean_box(0);
v___x_1602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1602_, 0, v___x_1601_);
return v___x_1602_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2(lean_object* v_e_1808_, lean_object* v_a_1809_, lean_object* v_a_1810_, lean_object* v_a_1811_, lean_object* v_a_1812_, lean_object* v_a_1813_, lean_object* v_a_1814_, lean_object* v_a_1815_, lean_object* v_a_1816_, lean_object* v_a_1817_){
_start:
{
lean_object* v___y_1820_; lean_object* v___x_1843_; lean_object* v_bvLogicalCache_1844_; lean_object* v___x_1845_; 
v___x_1843_ = lean_st_ref_get(v_a_1809_);
v_bvLogicalCache_1844_ = lean_ctor_get(v___x_1843_, 3);
lean_inc_ref(v_bvLogicalCache_1844_);
lean_dec(v___x_1843_);
v___x_1845_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__12___redArg(v_bvLogicalCache_1844_, v_e_1808_);
lean_dec_ref(v_bvLogicalCache_1844_);
if (lean_obj_tag(v___x_1845_) == 0)
{
lean_object* v___x_1846_; 
lean_inc_ref(v_e_1808_);
v___x_1846_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go(v_e_1808_, v_a_1809_, v_a_1810_, v_a_1811_, v_a_1812_, v_a_1813_, v_a_1814_, v_a_1815_, v_a_1816_, v_a_1817_);
if (lean_obj_tag(v___x_1846_) == 0)
{
lean_object* v_a_1847_; 
v_a_1847_ = lean_ctor_get(v___x_1846_, 0);
lean_inc(v_a_1847_);
if (lean_obj_tag(v_a_1847_) == 0)
{
lean_object* v___x_1848_; 
lean_dec_ref_known(v___x_1846_, 1);
lean_inc_ref(v_e_1808_);
v___x_1848_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_boolAtom(v_e_1808_, v_a_1810_, v_a_1811_, v_a_1812_, v_a_1813_, v_a_1814_, v_a_1815_, v_a_1816_, v_a_1817_);
v___y_1820_ = v___x_1848_;
goto v___jp_1819_;
}
else
{
lean_dec_ref_known(v_a_1847_, 1);
v___y_1820_ = v___x_1846_;
goto v___jp_1819_;
}
}
else
{
v___y_1820_ = v___x_1846_;
goto v___jp_1819_;
}
}
else
{
lean_object* v_val_1849_; lean_object* v___x_1851_; uint8_t v_isShared_1852_; uint8_t v_isSharedCheck_1856_; 
lean_dec_ref(v_e_1808_);
v_val_1849_ = lean_ctor_get(v___x_1845_, 0);
v_isSharedCheck_1856_ = !lean_is_exclusive(v___x_1845_);
if (v_isSharedCheck_1856_ == 0)
{
v___x_1851_ = v___x_1845_;
v_isShared_1852_ = v_isSharedCheck_1856_;
goto v_resetjp_1850_;
}
else
{
lean_inc(v_val_1849_);
lean_dec(v___x_1845_);
v___x_1851_ = lean_box(0);
v_isShared_1852_ = v_isSharedCheck_1856_;
goto v_resetjp_1850_;
}
v_resetjp_1850_:
{
lean_object* v___x_1854_; 
if (v_isShared_1852_ == 0)
{
lean_ctor_set_tag(v___x_1851_, 0);
v___x_1854_ = v___x_1851_;
goto v_reusejp_1853_;
}
else
{
lean_object* v_reuseFailAlloc_1855_; 
v_reuseFailAlloc_1855_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1855_, 0, v_val_1849_);
v___x_1854_ = v_reuseFailAlloc_1855_;
goto v_reusejp_1853_;
}
v_reusejp_1853_:
{
return v___x_1854_;
}
}
}
v___jp_1819_:
{
if (lean_obj_tag(v___y_1820_) == 0)
{
lean_object* v_a_1821_; lean_object* v___x_1823_; uint8_t v_isShared_1824_; uint8_t v_isSharedCheck_1842_; 
v_a_1821_ = lean_ctor_get(v___y_1820_, 0);
v_isSharedCheck_1842_ = !lean_is_exclusive(v___y_1820_);
if (v_isSharedCheck_1842_ == 0)
{
v___x_1823_ = v___y_1820_;
v_isShared_1824_ = v_isSharedCheck_1842_;
goto v_resetjp_1822_;
}
else
{
lean_inc(v_a_1821_);
lean_dec(v___y_1820_);
v___x_1823_ = lean_box(0);
v_isShared_1824_ = v_isSharedCheck_1842_;
goto v_resetjp_1822_;
}
v_resetjp_1822_:
{
lean_object* v___x_1825_; lean_object* v_lemmas_1826_; lean_object* v_bvExprCache_1827_; lean_object* v_bvPredCache_1828_; lean_object* v_bvLogicalCache_1829_; lean_object* v___x_1831_; uint8_t v_isShared_1832_; uint8_t v_isSharedCheck_1841_; 
v___x_1825_ = lean_st_ref_take(v_a_1809_);
v_lemmas_1826_ = lean_ctor_get(v___x_1825_, 0);
v_bvExprCache_1827_ = lean_ctor_get(v___x_1825_, 1);
v_bvPredCache_1828_ = lean_ctor_get(v___x_1825_, 2);
v_bvLogicalCache_1829_ = lean_ctor_get(v___x_1825_, 3);
v_isSharedCheck_1841_ = !lean_is_exclusive(v___x_1825_);
if (v_isSharedCheck_1841_ == 0)
{
v___x_1831_ = v___x_1825_;
v_isShared_1832_ = v_isSharedCheck_1841_;
goto v_resetjp_1830_;
}
else
{
lean_inc(v_bvLogicalCache_1829_);
lean_inc(v_bvPredCache_1828_);
lean_inc(v_bvExprCache_1827_);
lean_inc(v_lemmas_1826_);
lean_dec(v___x_1825_);
v___x_1831_ = lean_box(0);
v_isShared_1832_ = v_isSharedCheck_1841_;
goto v_resetjp_1830_;
}
v_resetjp_1830_:
{
lean_object* v___x_1833_; lean_object* v___x_1835_; 
lean_inc(v_a_1821_);
v___x_1833_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13___redArg(v_bvLogicalCache_1829_, v_e_1808_, v_a_1821_);
if (v_isShared_1832_ == 0)
{
lean_ctor_set(v___x_1831_, 3, v___x_1833_);
v___x_1835_ = v___x_1831_;
goto v_reusejp_1834_;
}
else
{
lean_object* v_reuseFailAlloc_1840_; 
v_reuseFailAlloc_1840_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1840_, 0, v_lemmas_1826_);
lean_ctor_set(v_reuseFailAlloc_1840_, 1, v_bvExprCache_1827_);
lean_ctor_set(v_reuseFailAlloc_1840_, 2, v_bvPredCache_1828_);
lean_ctor_set(v_reuseFailAlloc_1840_, 3, v___x_1833_);
v___x_1835_ = v_reuseFailAlloc_1840_;
goto v_reusejp_1834_;
}
v_reusejp_1834_:
{
lean_object* v___x_1836_; lean_object* v___x_1838_; 
v___x_1836_ = lean_st_ref_put(v_a_1809_, v___x_1835_);
if (v_isShared_1824_ == 0)
{
v___x_1838_ = v___x_1823_;
goto v_reusejp_1837_;
}
else
{
lean_object* v_reuseFailAlloc_1839_; 
v_reuseFailAlloc_1839_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1839_, 0, v_a_1821_);
v___x_1838_ = v_reuseFailAlloc_1839_;
goto v_reusejp_1837_;
}
v_reusejp_1837_:
{
return v___x_1838_;
}
}
}
}
}
else
{
lean_dec_ref(v_e_1808_);
return v___y_1820_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom(lean_object* v_origExpr_1857_, lean_object* v_a_1858_, lean_object* v_a_1859_, lean_object* v_a_1860_, lean_object* v_a_1861_, lean_object* v_a_1862_, lean_object* v_a_1863_, lean_object* v_a_1864_, lean_object* v_a_1865_, lean_object* v_a_1866_){
_start:
{
lean_object* v___x_1868_; 
v___x_1868_ = l_Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2(v_origExpr_1857_, v_a_1858_, v_a_1859_, v_a_1860_, v_a_1861_, v_a_1862_, v_a_1863_, v_a_1864_, v_a_1865_, v_a_1866_);
return v___x_1868_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of(lean_object* v_origExpr_1869_, lean_object* v_a_1870_, lean_object* v_a_1871_, lean_object* v_a_1872_, lean_object* v_a_1873_, lean_object* v_a_1874_, lean_object* v_a_1875_, lean_object* v_a_1876_, lean_object* v_a_1877_, lean_object* v_a_1878_){
_start:
{
lean_object* v___x_1880_; 
v___x_1880_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom(v_origExpr_1869_, v_a_1870_, v_a_1871_, v_a_1872_, v_a_1873_, v_a_1874_, v_a_1875_, v_a_1876_, v_a_1877_, v_a_1878_);
return v___x_1880_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__6(void){
_start:
{
lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; 
v___x_1896_ = lean_box(0);
v___x_1897_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__5));
v___x_1898_ = l_Lean_mkConst(v___x_1897_, v___x_1896_);
return v___x_1898_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__3(void){
_start:
{
lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; 
v___x_1906_ = lean_box(0);
v___x_1907_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__2));
v___x_1908_ = l_Lean_mkConst(v___x_1907_, v___x_1906_);
return v___x_1908_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__6(void){
_start:
{
lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; 
v___x_1915_ = lean_box(0);
v___x_1916_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__5));
v___x_1917_ = l_Lean_mkConst(v___x_1916_, v___x_1915_);
return v___x_1917_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__9(void){
_start:
{
lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; 
v___x_1924_ = lean_box(0);
v___x_1925_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__8));
v___x_1926_ = l_Lean_mkConst(v___x_1925_, v___x_1924_);
return v___x_1926_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__12(void){
_start:
{
lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; 
v___x_1934_ = lean_box(0);
v___x_1935_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__11));
v___x_1936_ = l_Lean_mkConst(v___x_1935_, v___x_1934_);
return v___x_1936_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__15(void){
_start:
{
lean_object* v___x_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; 
v___x_1943_ = lean_box(0);
v___x_1944_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__14));
v___x_1945_ = l_Lean_mkConst(v___x_1944_, v___x_1943_);
return v___x_1945_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__18(void){
_start:
{
lean_object* v___x_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; 
v___x_1952_ = lean_box(0);
v___x_1953_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__17));
v___x_1954_ = l_Lean_mkConst(v___x_1953_, v___x_1952_);
return v___x_1954_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__21(void){
_start:
{
lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; 
v___x_1961_ = lean_box(0);
v___x_1962_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__20));
v___x_1963_ = l_Lean_mkConst(v___x_1962_, v___x_1961_);
return v___x_1963_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection(lean_object* v_innerExpr_1964_, lean_object* v_op_1965_, lean_object* v_congrThm_1966_, lean_object* v_origExpr_1967_, lean_object* v_a_1968_, lean_object* v_a_1969_, lean_object* v_a_1970_, lean_object* v_a_1971_, lean_object* v_a_1972_, lean_object* v_a_1973_, lean_object* v_a_1974_, lean_object* v_a_1975_, lean_object* v_a_1976_){
_start:
{
lean_object* v___x_1978_; 
lean_inc_ref(v_innerExpr_1964_);
v___x_1978_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_goOrAtom(v_innerExpr_1964_, v_a_1968_, v_a_1969_, v_a_1970_, v_a_1971_, v_a_1972_, v_a_1973_, v_a_1974_, v_a_1975_, v_a_1976_);
if (lean_obj_tag(v___x_1978_) == 0)
{
lean_object* v_a_1979_; lean_object* v___x_1981_; uint8_t v_isShared_1982_; uint8_t v_isSharedCheck_2041_; 
v_a_1979_ = lean_ctor_get(v___x_1978_, 0);
v_isSharedCheck_2041_ = !lean_is_exclusive(v___x_1978_);
if (v_isSharedCheck_2041_ == 0)
{
v___x_1981_ = v___x_1978_;
v_isShared_1982_ = v_isSharedCheck_2041_;
goto v_resetjp_1980_;
}
else
{
lean_inc(v_a_1979_);
lean_dec(v___x_1978_);
v___x_1981_ = lean_box(0);
v_isShared_1982_ = v_isSharedCheck_2041_;
goto v_resetjp_1980_;
}
v_resetjp_1980_:
{
if (lean_obj_tag(v_a_1979_) == 1)
{
lean_object* v_val_1983_; lean_object* v___x_1985_; uint8_t v_isShared_1986_; uint8_t v_isSharedCheck_2036_; 
lean_del_object(v___x_1981_);
v_val_1983_ = lean_ctor_get(v_a_1979_, 0);
v_isSharedCheck_2036_ = !lean_is_exclusive(v_a_1979_);
if (v_isSharedCheck_2036_ == 0)
{
v___x_1985_ = v_a_1979_;
v_isShared_1986_ = v_isSharedCheck_2036_;
goto v_resetjp_1984_;
}
else
{
lean_inc(v_val_1983_);
lean_dec(v_a_1979_);
v___x_1985_ = lean_box(0);
v_isShared_1986_ = v_isSharedCheck_2036_;
goto v_resetjp_1984_;
}
v_resetjp_1984_:
{
lean_object* v_width_1987_; lean_object* v_bvExpr_1988_; lean_object* v_expr_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___y_1995_; 
v_width_1987_ = lean_ctor_get(v_val_1983_, 0);
lean_inc_n(v_width_1987_, 3);
v_bvExpr_1988_ = lean_ctor_get(v_val_1983_, 1);
v_expr_1989_ = lean_ctor_get(v_val_1983_, 4);
lean_inc_ref(v_bvExpr_1988_);
lean_inc(v_op_1965_);
v___x_1990_ = l_Std_Tactic_BVDecide_BVExpr_un___override(v_width_1987_, v_op_1965_, v_bvExpr_1988_);
v___x_1991_ = lean_box(0);
v___x_1992_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__6, &l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__6_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__6);
v___x_1993_ = l_Lean_mkNatLit(v_width_1987_);
switch(lean_obj_tag(v_op_1965_))
{
case 0:
{
lean_object* v___x_2020_; 
v___x_2020_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__3, &l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__3_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__3);
v___y_1995_ = v___x_2020_;
goto v___jp_1994_;
}
case 1:
{
lean_object* v_n_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; 
v_n_2021_ = lean_ctor_get(v_op_1965_, 0);
lean_inc(v_n_2021_);
lean_dec_ref_known(v_op_1965_, 1);
v___x_2022_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__6, &l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__6_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__6);
v___x_2023_ = l_Lean_mkNatLit(v_n_2021_);
v___x_2024_ = l_Lean_Expr_app___override(v___x_2022_, v___x_2023_);
v___y_1995_ = v___x_2024_;
goto v___jp_1994_;
}
case 2:
{
lean_object* v_n_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; 
v_n_2025_ = lean_ctor_get(v_op_1965_, 0);
lean_inc(v_n_2025_);
lean_dec_ref_known(v_op_1965_, 1);
v___x_2026_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__9, &l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__9_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__9);
v___x_2027_ = l_Lean_mkNatLit(v_n_2025_);
v___x_2028_ = l_Lean_Expr_app___override(v___x_2026_, v___x_2027_);
v___y_1995_ = v___x_2028_;
goto v___jp_1994_;
}
case 3:
{
lean_object* v_n_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; 
v_n_2029_ = lean_ctor_get(v_op_1965_, 0);
lean_inc(v_n_2029_);
lean_dec_ref_known(v_op_1965_, 1);
v___x_2030_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__12);
v___x_2031_ = l_Lean_mkNatLit(v_n_2029_);
v___x_2032_ = l_Lean_Expr_app___override(v___x_2030_, v___x_2031_);
v___y_1995_ = v___x_2032_;
goto v___jp_1994_;
}
case 4:
{
lean_object* v___x_2033_; 
v___x_2033_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__15, &l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__15_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__15);
v___y_1995_ = v___x_2033_;
goto v___jp_1994_;
}
case 5:
{
lean_object* v___x_2034_; 
v___x_2034_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__18, &l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__18_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__18);
v___y_1995_ = v___x_2034_;
goto v___jp_1994_;
}
default: 
{
lean_object* v___x_2035_; 
v___x_2035_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__21, &l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__21_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__21);
v___y_1995_ = v___x_2035_;
goto v___jp_1994_;
}
}
v___jp_1994_:
{
lean_object* v___x_1996_; lean_object* v___x_1997_; 
lean_inc_ref(v_expr_1989_);
v___x_1996_ = l_Lean_mkApp3(v___x_1992_, v___x_1993_, v___y_1995_, v_expr_1989_);
v___x_1997_ = l_Lean_Meta_Sym_shareCommonInc(v___x_1996_, v_a_1971_, v_a_1972_, v_a_1973_, v_a_1974_, v_a_1975_, v_a_1976_);
if (lean_obj_tag(v___x_1997_) == 0)
{
lean_object* v_a_1998_; lean_object* v___x_2000_; uint8_t v_isShared_2001_; uint8_t v_isSharedCheck_2011_; 
v_a_1998_ = lean_ctor_get(v___x_1997_, 0);
v_isSharedCheck_2011_ = !lean_is_exclusive(v___x_1997_);
if (v_isSharedCheck_2011_ == 0)
{
v___x_2000_ = v___x_1997_;
v_isShared_2001_ = v_isSharedCheck_2011_;
goto v_resetjp_1999_;
}
else
{
lean_inc(v_a_1998_);
lean_dec(v___x_1997_);
v___x_2000_ = lean_box(0);
v_isShared_2001_ = v_isSharedCheck_2011_;
goto v_resetjp_1999_;
}
v_resetjp_1999_:
{
lean_object* v___x_2002_; lean_object* v___x_2003_; lean_object* v___x_2004_; lean_object* v___x_2006_; 
v___x_2002_ = l_Lean_mkConst(v_congrThm_1966_, v___x_1991_);
v___x_2003_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryCongrProof___boxed), 12, 3);
lean_closure_set(v___x_2003_, 0, v_val_1983_);
lean_closure_set(v___x_2003_, 1, v_innerExpr_1964_);
lean_closure_set(v___x_2003_, 2, v___x_2002_);
v___x_2004_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2004_, 0, v_width_1987_);
lean_ctor_set(v___x_2004_, 1, v___x_1990_);
lean_ctor_set(v___x_2004_, 2, v_origExpr_1967_);
lean_ctor_set(v___x_2004_, 3, v___x_2003_);
lean_ctor_set(v___x_2004_, 4, v_a_1998_);
if (v_isShared_1986_ == 0)
{
lean_ctor_set(v___x_1985_, 0, v___x_2004_);
v___x_2006_ = v___x_1985_;
goto v_reusejp_2005_;
}
else
{
lean_object* v_reuseFailAlloc_2010_; 
v_reuseFailAlloc_2010_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2010_, 0, v___x_2004_);
v___x_2006_ = v_reuseFailAlloc_2010_;
goto v_reusejp_2005_;
}
v_reusejp_2005_:
{
lean_object* v___x_2008_; 
if (v_isShared_2001_ == 0)
{
lean_ctor_set(v___x_2000_, 0, v___x_2006_);
v___x_2008_ = v___x_2000_;
goto v_reusejp_2007_;
}
else
{
lean_object* v_reuseFailAlloc_2009_; 
v_reuseFailAlloc_2009_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2009_, 0, v___x_2006_);
v___x_2008_ = v_reuseFailAlloc_2009_;
goto v_reusejp_2007_;
}
v_reusejp_2007_:
{
return v___x_2008_;
}
}
}
}
else
{
lean_object* v_a_2012_; lean_object* v___x_2014_; uint8_t v_isShared_2015_; uint8_t v_isSharedCheck_2019_; 
lean_dec_ref(v___x_1990_);
lean_dec(v_width_1987_);
lean_del_object(v___x_1985_);
lean_dec(v_val_1983_);
lean_dec_ref(v_origExpr_1967_);
lean_dec(v_congrThm_1966_);
lean_dec_ref(v_innerExpr_1964_);
v_a_2012_ = lean_ctor_get(v___x_1997_, 0);
v_isSharedCheck_2019_ = !lean_is_exclusive(v___x_1997_);
if (v_isSharedCheck_2019_ == 0)
{
v___x_2014_ = v___x_1997_;
v_isShared_2015_ = v_isSharedCheck_2019_;
goto v_resetjp_2013_;
}
else
{
lean_inc(v_a_2012_);
lean_dec(v___x_1997_);
v___x_2014_ = lean_box(0);
v_isShared_2015_ = v_isSharedCheck_2019_;
goto v_resetjp_2013_;
}
v_resetjp_2013_:
{
lean_object* v___x_2017_; 
if (v_isShared_2015_ == 0)
{
v___x_2017_ = v___x_2014_;
goto v_reusejp_2016_;
}
else
{
lean_object* v_reuseFailAlloc_2018_; 
v_reuseFailAlloc_2018_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2018_, 0, v_a_2012_);
v___x_2017_ = v_reuseFailAlloc_2018_;
goto v_reusejp_2016_;
}
v_reusejp_2016_:
{
return v___x_2017_;
}
}
}
}
}
}
else
{
lean_object* v___x_2037_; lean_object* v___x_2039_; 
lean_dec(v_a_1979_);
lean_dec_ref(v_origExpr_1967_);
lean_dec(v_congrThm_1966_);
lean_dec(v_op_1965_);
lean_dec_ref(v_innerExpr_1964_);
v___x_2037_ = lean_box(0);
if (v_isShared_1982_ == 0)
{
lean_ctor_set(v___x_1981_, 0, v___x_2037_);
v___x_2039_ = v___x_1981_;
goto v_reusejp_2038_;
}
else
{
lean_object* v_reuseFailAlloc_2040_; 
v_reuseFailAlloc_2040_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2040_, 0, v___x_2037_);
v___x_2039_ = v_reuseFailAlloc_2040_;
goto v_reusejp_2038_;
}
v_reusejp_2038_:
{
return v___x_2039_;
}
}
}
}
else
{
lean_dec_ref(v_origExpr_1967_);
lean_dec(v_congrThm_1966_);
lean_dec(v_op_1965_);
lean_dec_ref(v_innerExpr_1964_);
return v___x_1978_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection(lean_object* v_distance_2050_, lean_object* v_innerExpr_2051_, lean_object* v_shiftOp_2052_, lean_object* v_shiftOpName_2053_, lean_object* v_congrThm_2054_, lean_object* v_origExpr_2055_, lean_object* v_a_2056_, lean_object* v_a_2057_, lean_object* v_a_2058_, lean_object* v_a_2059_, lean_object* v_a_2060_, lean_object* v_a_2061_, lean_object* v_a_2062_, lean_object* v_a_2063_, lean_object* v_a_2064_){
_start:
{
lean_object* v___x_2066_; 
lean_inc_ref(v_innerExpr_2051_);
v___x_2066_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_goOrAtom(v_innerExpr_2051_, v_a_2056_, v_a_2057_, v_a_2058_, v_a_2059_, v_a_2060_, v_a_2061_, v_a_2062_, v_a_2063_, v_a_2064_);
if (lean_obj_tag(v___x_2066_) == 0)
{
lean_object* v_a_2067_; lean_object* v___x_2069_; uint8_t v_isShared_2070_; uint8_t v_isSharedCheck_2116_; 
v_a_2067_ = lean_ctor_get(v___x_2066_, 0);
v_isSharedCheck_2116_ = !lean_is_exclusive(v___x_2066_);
if (v_isSharedCheck_2116_ == 0)
{
v___x_2069_ = v___x_2066_;
v_isShared_2070_ = v_isSharedCheck_2116_;
goto v_resetjp_2068_;
}
else
{
lean_inc(v_a_2067_);
lean_dec(v___x_2066_);
v___x_2069_ = lean_box(0);
v_isShared_2070_ = v_isSharedCheck_2116_;
goto v_resetjp_2068_;
}
v_resetjp_2068_:
{
if (lean_obj_tag(v_a_2067_) == 1)
{
lean_object* v_val_2071_; lean_object* v___x_2073_; uint8_t v_isShared_2074_; uint8_t v_isSharedCheck_2111_; 
lean_del_object(v___x_2069_);
v_val_2071_ = lean_ctor_get(v_a_2067_, 0);
v_isSharedCheck_2111_ = !lean_is_exclusive(v_a_2067_);
if (v_isSharedCheck_2111_ == 0)
{
v___x_2073_ = v_a_2067_;
v_isShared_2074_ = v_isSharedCheck_2111_;
goto v_resetjp_2072_;
}
else
{
lean_inc(v_val_2071_);
lean_dec(v_a_2067_);
v___x_2073_ = lean_box(0);
v_isShared_2074_ = v_isSharedCheck_2111_;
goto v_resetjp_2072_;
}
v_resetjp_2072_:
{
lean_object* v_width_2075_; lean_object* v_bvExpr_2076_; lean_object* v_expr_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; 
v_width_2075_ = lean_ctor_get(v_val_2071_, 0);
lean_inc_n(v_width_2075_, 3);
v_bvExpr_2076_ = lean_ctor_get(v_val_2071_, 1);
v_expr_2077_ = lean_ctor_get(v_val_2071_, 4);
lean_inc(v_distance_2050_);
v___x_2078_ = lean_apply_1(v_shiftOp_2052_, v_distance_2050_);
lean_inc_ref(v_bvExpr_2076_);
v___x_2079_ = l_Std_Tactic_BVDecide_BVExpr_un___override(v_width_2075_, v___x_2078_, v_bvExpr_2076_);
v___x_2080_ = lean_box(0);
v___x_2081_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__6, &l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__6_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__6);
v___x_2082_ = l_Lean_mkNatLit(v_width_2075_);
v___x_2083_ = l_Lean_mkConst(v_shiftOpName_2053_, v___x_2080_);
v___x_2084_ = l_Lean_mkNatLit(v_distance_2050_);
lean_inc_ref(v___x_2084_);
v___x_2085_ = l_Lean_Expr_app___override(v___x_2083_, v___x_2084_);
lean_inc_ref(v_expr_2077_);
v___x_2086_ = l_Lean_mkApp3(v___x_2081_, v___x_2082_, v___x_2085_, v_expr_2077_);
v___x_2087_ = l_Lean_Meta_Sym_shareCommonInc(v___x_2086_, v_a_2059_, v_a_2060_, v_a_2061_, v_a_2062_, v_a_2063_, v_a_2064_);
if (lean_obj_tag(v___x_2087_) == 0)
{
lean_object* v_a_2088_; lean_object* v___x_2090_; uint8_t v_isShared_2091_; uint8_t v_isSharedCheck_2102_; 
v_a_2088_ = lean_ctor_get(v___x_2087_, 0);
v_isSharedCheck_2102_ = !lean_is_exclusive(v___x_2087_);
if (v_isSharedCheck_2102_ == 0)
{
v___x_2090_ = v___x_2087_;
v_isShared_2091_ = v_isSharedCheck_2102_;
goto v_resetjp_2089_;
}
else
{
lean_inc(v_a_2088_);
lean_dec(v___x_2087_);
v___x_2090_ = lean_box(0);
v_isShared_2091_ = v_isSharedCheck_2102_;
goto v_resetjp_2089_;
}
v_resetjp_2089_:
{
lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2097_; 
v___x_2092_ = l_Lean_mkConst(v_congrThm_2054_, v___x_2080_);
v___x_2093_ = l_Lean_Expr_app___override(v___x_2092_, v___x_2084_);
v___x_2094_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryCongrProof___boxed), 12, 3);
lean_closure_set(v___x_2094_, 0, v_val_2071_);
lean_closure_set(v___x_2094_, 1, v_innerExpr_2051_);
lean_closure_set(v___x_2094_, 2, v___x_2093_);
v___x_2095_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2095_, 0, v_width_2075_);
lean_ctor_set(v___x_2095_, 1, v___x_2079_);
lean_ctor_set(v___x_2095_, 2, v_origExpr_2055_);
lean_ctor_set(v___x_2095_, 3, v___x_2094_);
lean_ctor_set(v___x_2095_, 4, v_a_2088_);
if (v_isShared_2074_ == 0)
{
lean_ctor_set(v___x_2073_, 0, v___x_2095_);
v___x_2097_ = v___x_2073_;
goto v_reusejp_2096_;
}
else
{
lean_object* v_reuseFailAlloc_2101_; 
v_reuseFailAlloc_2101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2101_, 0, v___x_2095_);
v___x_2097_ = v_reuseFailAlloc_2101_;
goto v_reusejp_2096_;
}
v_reusejp_2096_:
{
lean_object* v___x_2099_; 
if (v_isShared_2091_ == 0)
{
lean_ctor_set(v___x_2090_, 0, v___x_2097_);
v___x_2099_ = v___x_2090_;
goto v_reusejp_2098_;
}
else
{
lean_object* v_reuseFailAlloc_2100_; 
v_reuseFailAlloc_2100_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2100_, 0, v___x_2097_);
v___x_2099_ = v_reuseFailAlloc_2100_;
goto v_reusejp_2098_;
}
v_reusejp_2098_:
{
return v___x_2099_;
}
}
}
}
else
{
lean_object* v_a_2103_; lean_object* v___x_2105_; uint8_t v_isShared_2106_; uint8_t v_isSharedCheck_2110_; 
lean_dec_ref(v___x_2084_);
lean_dec_ref(v___x_2079_);
lean_dec(v_width_2075_);
lean_del_object(v___x_2073_);
lean_dec(v_val_2071_);
lean_dec_ref(v_origExpr_2055_);
lean_dec(v_congrThm_2054_);
lean_dec_ref(v_innerExpr_2051_);
v_a_2103_ = lean_ctor_get(v___x_2087_, 0);
v_isSharedCheck_2110_ = !lean_is_exclusive(v___x_2087_);
if (v_isSharedCheck_2110_ == 0)
{
v___x_2105_ = v___x_2087_;
v_isShared_2106_ = v_isSharedCheck_2110_;
goto v_resetjp_2104_;
}
else
{
lean_inc(v_a_2103_);
lean_dec(v___x_2087_);
v___x_2105_ = lean_box(0);
v_isShared_2106_ = v_isSharedCheck_2110_;
goto v_resetjp_2104_;
}
v_resetjp_2104_:
{
lean_object* v___x_2108_; 
if (v_isShared_2106_ == 0)
{
v___x_2108_ = v___x_2105_;
goto v_reusejp_2107_;
}
else
{
lean_object* v_reuseFailAlloc_2109_; 
v_reuseFailAlloc_2109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2109_, 0, v_a_2103_);
v___x_2108_ = v_reuseFailAlloc_2109_;
goto v_reusejp_2107_;
}
v_reusejp_2107_:
{
return v___x_2108_;
}
}
}
}
}
else
{
lean_object* v___x_2112_; lean_object* v___x_2114_; 
lean_dec(v_a_2067_);
lean_dec_ref(v_origExpr_2055_);
lean_dec(v_congrThm_2054_);
lean_dec(v_shiftOpName_2053_);
lean_dec_ref(v_shiftOp_2052_);
lean_dec_ref(v_innerExpr_2051_);
lean_dec(v_distance_2050_);
v___x_2112_ = lean_box(0);
if (v_isShared_2070_ == 0)
{
lean_ctor_set(v___x_2069_, 0, v___x_2112_);
v___x_2114_ = v___x_2069_;
goto v_reusejp_2113_;
}
else
{
lean_object* v_reuseFailAlloc_2115_; 
v_reuseFailAlloc_2115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2115_, 0, v___x_2112_);
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
lean_dec_ref(v_origExpr_2055_);
lean_dec(v_congrThm_2054_);
lean_dec(v_shiftOpName_2053_);
lean_dec_ref(v_shiftOp_2052_);
lean_dec_ref(v_innerExpr_2051_);
lean_dec(v_distance_2050_);
return v___x_2066_;
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__88(void){
_start:
{
lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; 
v___x_2123_ = lean_box(0);
v___x_2124_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__87));
v___x_2125_ = l_Lean_mkConst(v___x_2124_, v___x_2123_);
return v___x_2125_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_rotateReflection(lean_object* v_distanceExpr_2134_, lean_object* v_innerExpr_2135_, lean_object* v_rotateOp_2136_, lean_object* v_rotateOpName_2137_, lean_object* v_congrThm_2138_, lean_object* v_origExpr_2139_, lean_object* v_a_2140_, lean_object* v_a_2141_, lean_object* v_a_2142_, lean_object* v_a_2143_, lean_object* v_a_2144_, lean_object* v_a_2145_, lean_object* v_a_2146_, lean_object* v_a_2147_, lean_object* v_a_2148_){
_start:
{
lean_object* v___x_2150_; 
v___x_2150_ = l_Lean_Meta_Sym_getNatValue_x3f(v_distanceExpr_2134_);
if (lean_obj_tag(v___x_2150_) == 1)
{
lean_object* v_val_2151_; lean_object* v___x_2152_; 
v_val_2151_ = lean_ctor_get(v___x_2150_, 0);
lean_inc(v_val_2151_);
lean_dec_ref_known(v___x_2150_, 1);
v___x_2152_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection(v_val_2151_, v_innerExpr_2135_, v_rotateOp_2136_, v_rotateOpName_2137_, v_congrThm_2138_, v_origExpr_2139_, v_a_2140_, v_a_2141_, v_a_2142_, v_a_2143_, v_a_2144_, v_a_2145_, v_a_2146_, v_a_2147_, v_a_2148_);
return v___x_2152_;
}
else
{
lean_object* v___x_2153_; lean_object* v___x_2154_; 
lean_dec(v___x_2150_);
lean_dec_ref(v_origExpr_2139_);
lean_dec(v_congrThm_2138_);
lean_dec(v_rotateOpName_2137_);
lean_dec_ref(v_rotateOp_2136_);
lean_dec_ref(v_innerExpr_2135_);
v___x_2153_ = lean_box(0);
v___x_2154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2154_, 0, v___x_2153_);
return v___x_2154_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go(lean_object* v_origExpr_2187_, lean_object* v_a_2188_, lean_object* v_a_2189_, lean_object* v_a_2190_, lean_object* v_a_2191_, lean_object* v_a_2192_, lean_object* v_a_2193_, lean_object* v_a_2194_, lean_object* v_a_2195_, lean_object* v_a_2196_){
_start:
{
lean_object* v___f_2213_; lean_object* v___f_2214_; lean_object* v___f_2215_; lean_object* v___f_2216_; lean_object* v___f_2217_; lean_object* v___f_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; 
v___f_2213_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__0));
v___f_2214_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__1));
v___f_2215_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__2));
v___f_2216_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__3));
v___f_2217_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__4));
v___f_2218_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__5));
v___x_2219_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__0));
v___x_2220_ = l_Lean_Core_checkSystem(v___x_2219_, v_a_2195_, v_a_2196_);
if (lean_obj_tag(v___x_2220_) == 0)
{
lean_object* v___x_2221_; 
lean_dec_ref_known(v___x_2220_, 1);
lean_inc_ref(v_origExpr_2187_);
v___x_2221_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_origExpr_2187_, v_a_2194_);
if (lean_obj_tag(v___x_2221_) == 0)
{
lean_object* v_a_2222_; lean_object* v___x_2224_; uint8_t v_isShared_2225_; uint8_t v_isSharedCheck_2703_; 
v_a_2222_ = lean_ctor_get(v___x_2221_, 0);
v_isSharedCheck_2703_ = !lean_is_exclusive(v___x_2221_);
if (v_isSharedCheck_2703_ == 0)
{
v___x_2224_ = v___x_2221_;
v_isShared_2225_ = v_isSharedCheck_2703_;
goto v_resetjp_2223_;
}
else
{
lean_inc(v_a_2222_);
lean_dec(v___x_2221_);
v___x_2224_ = lean_box(0);
v_isShared_2225_ = v_isSharedCheck_2703_;
goto v_resetjp_2223_;
}
v_resetjp_2223_:
{
lean_object* v___x_2226_; uint8_t v___x_2227_; 
v___x_2226_ = l_Lean_Expr_cleanupAnnotations(v_a_2222_);
v___x_2227_ = l_Lean_Expr_isApp(v___x_2226_);
if (v___x_2227_ == 0)
{
lean_dec_ref(v___x_2226_);
lean_del_object(v___x_2224_);
lean_dec_ref(v_origExpr_2187_);
goto v___jp_2210_;
}
else
{
lean_object* v_arg_2228_; lean_object* v___x_2229_; uint8_t v___x_2230_; 
v_arg_2228_ = lean_ctor_get(v___x_2226_, 1);
lean_inc_ref(v_arg_2228_);
v___x_2229_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2226_);
v___x_2230_ = l_Lean_Expr_isApp(v___x_2229_);
if (v___x_2230_ == 0)
{
lean_dec_ref(v___x_2229_);
lean_dec_ref(v_arg_2228_);
lean_del_object(v___x_2224_);
lean_dec_ref(v_origExpr_2187_);
goto v___jp_2210_;
}
else
{
lean_object* v_arg_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; uint8_t v___x_2235_; 
v_arg_2231_ = lean_ctor_get(v___x_2229_, 1);
lean_inc_ref(v_arg_2231_);
v___x_2232_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2229_);
v___x_2233_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__0));
v___x_2234_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__6));
v___x_2235_ = l_Lean_Expr_isConstOf(v___x_2232_, v___x_2234_);
if (v___x_2235_ == 0)
{
lean_object* v___x_2236_; uint8_t v___x_2237_; 
v___x_2236_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__7));
v___x_2237_ = l_Lean_Expr_isConstOf(v___x_2232_, v___x_2236_);
if (v___x_2237_ == 0)
{
lean_object* v___x_2238_; uint8_t v___x_2239_; 
v___x_2238_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__8));
v___x_2239_ = l_Lean_Expr_isConstOf(v___x_2232_, v___x_2238_);
if (v___x_2239_ == 0)
{
lean_object* v___x_2240_; uint8_t v___x_2241_; 
v___x_2240_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__10));
v___x_2241_ = l_Lean_Expr_isConstOf(v___x_2232_, v___x_2240_);
if (v___x_2241_ == 0)
{
uint8_t v___x_2242_; 
v___x_2242_ = l_Lean_Expr_isApp(v___x_2232_);
if (v___x_2242_ == 0)
{
lean_dec_ref(v___x_2232_);
lean_dec_ref(v_arg_2231_);
lean_dec_ref(v_arg_2228_);
lean_del_object(v___x_2224_);
lean_dec_ref(v_origExpr_2187_);
goto v___jp_2210_;
}
else
{
lean_object* v_arg_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; uint8_t v___x_2246_; 
v_arg_2243_ = lean_ctor_get(v___x_2232_, 1);
lean_inc_ref(v_arg_2243_);
v___x_2244_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2232_);
v___x_2245_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__11));
v___x_2246_ = l_Lean_Expr_isConstOf(v___x_2244_, v___x_2245_);
if (v___x_2246_ == 0)
{
lean_object* v___x_2247_; uint8_t v___x_2248_; 
v___x_2247_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__12));
v___x_2248_ = l_Lean_Expr_isConstOf(v___x_2244_, v___x_2247_);
if (v___x_2248_ == 0)
{
lean_object* v___x_2249_; uint8_t v___x_2250_; 
v___x_2249_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__14));
v___x_2250_ = l_Lean_Expr_isConstOf(v___x_2244_, v___x_2249_);
if (v___x_2250_ == 0)
{
lean_object* v___x_2251_; uint8_t v___x_2252_; 
v___x_2251_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__16));
v___x_2252_ = l_Lean_Expr_isConstOf(v___x_2244_, v___x_2251_);
if (v___x_2252_ == 0)
{
lean_object* v___x_2253_; uint8_t v___x_2254_; 
v___x_2253_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__19));
v___x_2254_ = l_Lean_Expr_isConstOf(v___x_2244_, v___x_2253_);
if (v___x_2254_ == 0)
{
uint8_t v___x_2255_; 
v___x_2255_ = l_Lean_Expr_isApp(v___x_2244_);
if (v___x_2255_ == 0)
{
lean_dec_ref(v___x_2244_);
lean_dec_ref(v_arg_2243_);
lean_dec_ref(v_arg_2231_);
lean_dec_ref(v_arg_2228_);
lean_del_object(v___x_2224_);
lean_dec_ref(v_origExpr_2187_);
goto v___jp_2210_;
}
else
{
lean_object* v___x_2256_; lean_object* v___x_2257_; uint8_t v___x_2258_; 
v___x_2256_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2244_);
v___x_2257_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___closed__10));
v___x_2258_ = l_Lean_Expr_isConstOf(v___x_2256_, v___x_2257_);
if (v___x_2258_ == 0)
{
lean_object* v___x_2259_; uint8_t v___x_2260_; 
v___x_2259_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__21));
v___x_2260_ = l_Lean_Expr_isConstOf(v___x_2256_, v___x_2259_);
if (v___x_2260_ == 0)
{
lean_object* v___x_2261_; uint8_t v___x_2262_; 
lean_dec_ref(v_arg_2243_);
lean_del_object(v___x_2224_);
v___x_2261_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__23));
v___x_2262_ = l_Lean_Expr_isConstOf(v___x_2256_, v___x_2261_);
if (v___x_2262_ == 0)
{
uint8_t v___x_2263_; 
v___x_2263_ = l_Lean_Expr_isApp(v___x_2256_);
if (v___x_2263_ == 0)
{
lean_dec_ref(v___x_2256_);
lean_dec_ref(v_arg_2231_);
lean_dec_ref(v_arg_2228_);
lean_dec_ref(v_origExpr_2187_);
goto v___jp_2210_;
}
else
{
lean_object* v_arg_2264_; lean_object* v___y_2266_; lean_object* v___y_2267_; lean_object* v___y_2268_; lean_object* v___y_2269_; lean_object* v___y_2270_; lean_object* v___y_2271_; lean_object* v___y_2272_; lean_object* v___y_2273_; lean_object* v___y_2274_; lean_object* v___y_2284_; lean_object* v___y_2285_; lean_object* v___y_2286_; lean_object* v___y_2287_; lean_object* v___y_2288_; lean_object* v___y_2289_; lean_object* v___y_2290_; lean_object* v___y_2291_; lean_object* v___y_2292_; lean_object* v___x_2301_; uint8_t v___x_2302_; 
v_arg_2264_ = lean_ctor_get(v___x_2256_, 1);
lean_inc_ref(v_arg_2264_);
v___x_2301_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2256_);
v___x_2302_ = l_Lean_Expr_isApp(v___x_2301_);
if (v___x_2302_ == 0)
{
lean_dec_ref(v___x_2301_);
lean_dec_ref(v_arg_2264_);
lean_dec_ref(v_arg_2231_);
lean_dec_ref(v_arg_2228_);
lean_dec_ref(v_origExpr_2187_);
goto v___jp_2210_;
}
else
{
lean_object* v_arg_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; uint8_t v___x_2306_; 
v_arg_2303_ = lean_ctor_get(v___x_2301_, 1);
lean_inc_ref(v_arg_2303_);
v___x_2304_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2301_);
v___x_2305_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__34));
v___x_2306_ = l_Lean_Expr_isConstOf(v___x_2304_, v___x_2305_);
if (v___x_2306_ == 0)
{
lean_object* v___x_2307_; uint8_t v___x_2308_; 
v___x_2307_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__37));
v___x_2308_ = l_Lean_Expr_isConstOf(v___x_2304_, v___x_2307_);
if (v___x_2308_ == 0)
{
lean_object* v___x_2309_; uint8_t v___x_2310_; 
v___x_2309_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__40));
v___x_2310_ = l_Lean_Expr_isConstOf(v___x_2304_, v___x_2309_);
if (v___x_2310_ == 0)
{
lean_object* v___x_2311_; uint8_t v___x_2312_; 
lean_dec_ref(v_arg_2303_);
lean_dec_ref(v_arg_2264_);
v___x_2311_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__43));
v___x_2312_ = l_Lean_Expr_isConstOf(v___x_2304_, v___x_2311_);
if (v___x_2312_ == 0)
{
lean_object* v___x_2313_; uint8_t v___x_2314_; 
v___x_2313_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__46));
v___x_2314_ = l_Lean_Expr_isConstOf(v___x_2304_, v___x_2313_);
if (v___x_2314_ == 0)
{
lean_object* v___x_2315_; uint8_t v___x_2316_; 
v___x_2315_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__49));
v___x_2316_ = l_Lean_Expr_isConstOf(v___x_2304_, v___x_2315_);
if (v___x_2316_ == 0)
{
lean_object* v___x_2317_; uint8_t v___x_2318_; 
v___x_2317_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__52));
v___x_2318_ = l_Lean_Expr_isConstOf(v___x_2304_, v___x_2317_);
if (v___x_2318_ == 0)
{
lean_object* v___x_2319_; uint8_t v___x_2320_; 
v___x_2319_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__55));
v___x_2320_ = l_Lean_Expr_isConstOf(v___x_2304_, v___x_2319_);
if (v___x_2320_ == 0)
{
lean_object* v___x_2321_; uint8_t v___x_2322_; 
v___x_2321_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__58));
v___x_2322_ = l_Lean_Expr_isConstOf(v___x_2304_, v___x_2321_);
lean_dec_ref(v___x_2304_);
if (v___x_2322_ == 0)
{
lean_dec_ref(v_arg_2231_);
lean_dec_ref(v_arg_2228_);
lean_dec_ref(v_origExpr_2187_);
goto v___jp_2210_;
}
else
{
uint8_t v___x_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; 
v___x_2323_ = 0;
v___x_2324_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__60));
v___x_2325_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection(v_arg_2231_, v_arg_2228_, v___x_2323_, v___x_2324_, v_origExpr_2187_, v_a_2188_, v_a_2189_, v_a_2190_, v_a_2191_, v_a_2192_, v_a_2193_, v_a_2194_, v_a_2195_, v_a_2196_);
return v___x_2325_;
}
}
else
{
uint8_t v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; 
lean_dec_ref(v___x_2304_);
v___x_2326_ = 2;
v___x_2327_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__62));
v___x_2328_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection(v_arg_2231_, v_arg_2228_, v___x_2326_, v___x_2327_, v_origExpr_2187_, v_a_2188_, v_a_2189_, v_a_2190_, v_a_2191_, v_a_2192_, v_a_2193_, v_a_2194_, v_a_2195_, v_a_2196_);
return v___x_2328_;
}
}
else
{
uint8_t v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; 
lean_dec_ref(v___x_2304_);
v___x_2329_ = 3;
v___x_2330_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__64));
v___x_2331_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection(v_arg_2231_, v_arg_2228_, v___x_2329_, v___x_2330_, v_origExpr_2187_, v_a_2188_, v_a_2189_, v_a_2190_, v_a_2191_, v_a_2192_, v_a_2193_, v_a_2194_, v_a_2195_, v_a_2196_);
return v___x_2331_;
}
}
else
{
uint8_t v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; 
lean_dec_ref(v___x_2304_);
v___x_2332_ = 4;
v___x_2333_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__66));
v___x_2334_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection(v_arg_2231_, v_arg_2228_, v___x_2332_, v___x_2333_, v_origExpr_2187_, v_a_2188_, v_a_2189_, v_a_2190_, v_a_2191_, v_a_2192_, v_a_2193_, v_a_2194_, v_a_2195_, v_a_2196_);
return v___x_2334_;
}
}
else
{
uint8_t v___x_2335_; lean_object* v___x_2336_; lean_object* v___x_2337_; 
lean_dec_ref(v___x_2304_);
v___x_2335_ = 5;
v___x_2336_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__68));
v___x_2337_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection(v_arg_2231_, v_arg_2228_, v___x_2335_, v___x_2336_, v_origExpr_2187_, v_a_2188_, v_a_2189_, v_a_2190_, v_a_2191_, v_a_2192_, v_a_2193_, v_a_2194_, v_a_2195_, v_a_2196_);
return v___x_2337_;
}
}
else
{
uint8_t v___x_2338_; lean_object* v___x_2339_; lean_object* v___x_2340_; 
lean_dec_ref(v___x_2304_);
v___x_2338_ = 6;
v___x_2339_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__70));
v___x_2340_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection(v_arg_2231_, v_arg_2228_, v___x_2338_, v___x_2339_, v_origExpr_2187_, v_a_2188_, v_a_2189_, v_a_2190_, v_a_2191_, v_a_2192_, v_a_2193_, v_a_2194_, v_a_2195_, v_a_2196_);
return v___x_2340_;
}
}
else
{
lean_object* v___x_2341_; 
lean_dec_ref(v___x_2304_);
lean_inc_ref(v_arg_2228_);
lean_inc_ref(v_arg_2264_);
v___x_2341_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_getNatOrBvValue_x3f___redArg(v_arg_2264_, v_arg_2228_, v_a_2194_);
if (lean_obj_tag(v___x_2341_) == 0)
{
lean_object* v_a_2342_; uint8_t v___y_2355_; lean_object* v___x_2356_; uint8_t v___x_2357_; 
v_a_2342_ = lean_ctor_get(v___x_2341_, 0);
lean_inc(v_a_2342_);
lean_dec_ref_known(v___x_2341_, 1);
v___x_2356_ = l_Lean_Expr_cleanupAnnotations(v_arg_2303_);
v___x_2357_ = l_Lean_Expr_isApp(v___x_2356_);
if (v___x_2357_ == 0)
{
lean_dec_ref(v___x_2356_);
lean_dec(v_a_2342_);
lean_dec_ref(v_arg_2264_);
lean_dec_ref(v_arg_2231_);
lean_dec_ref(v_arg_2228_);
lean_dec_ref(v_origExpr_2187_);
goto v___jp_2207_;
}
else
{
lean_object* v_arg_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; uint8_t v___x_2361_; 
v_arg_2358_ = lean_ctor_get(v___x_2356_, 1);
lean_inc_ref(v_arg_2358_);
v___x_2359_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2356_);
v___x_2360_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__8));
v___x_2361_ = l_Lean_Expr_isConstOf(v___x_2359_, v___x_2360_);
lean_dec_ref(v___x_2359_);
if (v___x_2361_ == 0)
{
lean_dec_ref(v_arg_2358_);
lean_dec(v_a_2342_);
lean_dec_ref(v_arg_2264_);
lean_dec_ref(v_arg_2231_);
lean_dec_ref(v_arg_2228_);
lean_dec_ref(v_origExpr_2187_);
goto v___jp_2207_;
}
else
{
lean_object* v___x_2362_; 
v___x_2362_ = l_Lean_Meta_Sym_getNatValue_x3f(v_arg_2358_);
if (lean_obj_tag(v___x_2362_) == 0)
{
v___y_2355_ = v___x_2308_;
goto v___jp_2354_;
}
else
{
lean_dec_ref_known(v___x_2362_, 1);
v___y_2355_ = v___x_2361_;
goto v___jp_2354_;
}
}
}
v___jp_2343_:
{
lean_object* v___x_2344_; lean_object* v___x_2345_; 
v___x_2344_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__72, &l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__72_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__72);
v___x_2345_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go_spec__12___redArg(v___x_2344_, v_a_2193_, v_a_2194_, v_a_2195_, v_a_2196_);
if (lean_obj_tag(v___x_2345_) == 0)
{
lean_dec_ref_known(v___x_2345_, 1);
v___y_2284_ = v_a_2188_;
v___y_2285_ = v_a_2189_;
v___y_2286_ = v_a_2190_;
v___y_2287_ = v_a_2191_;
v___y_2288_ = v_a_2192_;
v___y_2289_ = v_a_2193_;
v___y_2290_ = v_a_2194_;
v___y_2291_ = v_a_2195_;
v___y_2292_ = v_a_2196_;
goto v___jp_2283_;
}
else
{
lean_object* v_a_2346_; lean_object* v___x_2348_; uint8_t v_isShared_2349_; uint8_t v_isSharedCheck_2353_; 
lean_dec_ref(v_arg_2264_);
lean_dec_ref(v_arg_2231_);
lean_dec_ref(v_arg_2228_);
lean_dec_ref(v_origExpr_2187_);
v_a_2346_ = lean_ctor_get(v___x_2345_, 0);
v_isSharedCheck_2353_ = !lean_is_exclusive(v___x_2345_);
if (v_isSharedCheck_2353_ == 0)
{
v___x_2348_ = v___x_2345_;
v_isShared_2349_ = v_isSharedCheck_2353_;
goto v_resetjp_2347_;
}
else
{
lean_inc(v_a_2346_);
lean_dec(v___x_2345_);
v___x_2348_ = lean_box(0);
v_isShared_2349_ = v_isSharedCheck_2353_;
goto v_resetjp_2347_;
}
v_resetjp_2347_:
{
lean_object* v___x_2351_; 
if (v_isShared_2349_ == 0)
{
v___x_2351_ = v___x_2348_;
goto v_reusejp_2350_;
}
else
{
lean_object* v_reuseFailAlloc_2352_; 
v_reuseFailAlloc_2352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2352_, 0, v_a_2346_);
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
v___jp_2354_:
{
if (v___y_2355_ == 0)
{
lean_dec(v_a_2342_);
v___y_2284_ = v_a_2188_;
v___y_2285_ = v_a_2189_;
v___y_2286_ = v_a_2190_;
v___y_2287_ = v_a_2191_;
v___y_2288_ = v_a_2192_;
v___y_2289_ = v_a_2193_;
v___y_2290_ = v_a_2194_;
v___y_2291_ = v_a_2195_;
v___y_2292_ = v_a_2196_;
goto v___jp_2283_;
}
else
{
if (lean_obj_tag(v_a_2342_) == 0)
{
if (v___x_2308_ == 0)
{
v___y_2284_ = v_a_2188_;
v___y_2285_ = v_a_2189_;
v___y_2286_ = v_a_2190_;
v___y_2287_ = v_a_2191_;
v___y_2288_ = v_a_2192_;
v___y_2289_ = v_a_2193_;
v___y_2290_ = v_a_2194_;
v___y_2291_ = v_a_2195_;
v___y_2292_ = v_a_2196_;
goto v___jp_2283_;
}
else
{
goto v___jp_2343_;
}
}
else
{
lean_dec_ref_known(v_a_2342_, 1);
goto v___jp_2343_;
}
}
}
}
else
{
lean_object* v_a_2363_; lean_object* v___x_2365_; uint8_t v_isShared_2366_; uint8_t v_isSharedCheck_2370_; 
lean_dec_ref(v_arg_2303_);
lean_dec_ref(v_arg_2264_);
lean_dec_ref(v_arg_2231_);
lean_dec_ref(v_arg_2228_);
lean_dec_ref(v_origExpr_2187_);
v_a_2363_ = lean_ctor_get(v___x_2341_, 0);
v_isSharedCheck_2370_ = !lean_is_exclusive(v___x_2341_);
if (v_isSharedCheck_2370_ == 0)
{
v___x_2365_ = v___x_2341_;
v_isShared_2366_ = v_isSharedCheck_2370_;
goto v_resetjp_2364_;
}
else
{
lean_inc(v_a_2363_);
lean_dec(v___x_2341_);
v___x_2365_ = lean_box(0);
v_isShared_2366_ = v_isSharedCheck_2370_;
goto v_resetjp_2364_;
}
v_resetjp_2364_:
{
lean_object* v___x_2368_; 
if (v_isShared_2366_ == 0)
{
v___x_2368_ = v___x_2365_;
goto v_reusejp_2367_;
}
else
{
lean_object* v_reuseFailAlloc_2369_; 
v_reuseFailAlloc_2369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2369_, 0, v_a_2363_);
v___x_2368_ = v_reuseFailAlloc_2369_;
goto v_reusejp_2367_;
}
v_reusejp_2367_:
{
return v___x_2368_;
}
}
}
}
}
else
{
lean_object* v___x_2371_; 
lean_dec_ref(v___x_2304_);
lean_inc_ref(v_arg_2228_);
lean_inc_ref(v_arg_2264_);
v___x_2371_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_getNatOrBvValue_x3f___redArg(v_arg_2264_, v_arg_2228_, v_a_2194_);
if (lean_obj_tag(v___x_2371_) == 0)
{
lean_object* v_a_2372_; uint8_t v___y_2385_; lean_object* v___x_2386_; uint8_t v___x_2387_; 
v_a_2372_ = lean_ctor_get(v___x_2371_, 0);
lean_inc(v_a_2372_);
lean_dec_ref_known(v___x_2371_, 1);
v___x_2386_ = l_Lean_Expr_cleanupAnnotations(v_arg_2303_);
v___x_2387_ = l_Lean_Expr_isApp(v___x_2386_);
if (v___x_2387_ == 0)
{
lean_dec_ref(v___x_2386_);
lean_dec(v_a_2372_);
lean_dec_ref(v_arg_2264_);
lean_dec_ref(v_arg_2231_);
lean_dec_ref(v_arg_2228_);
lean_dec_ref(v_origExpr_2187_);
goto v___jp_2201_;
}
else
{
lean_object* v_arg_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; uint8_t v___x_2391_; 
v_arg_2388_ = lean_ctor_get(v___x_2386_, 1);
lean_inc_ref(v_arg_2388_);
v___x_2389_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2386_);
v___x_2390_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__8));
v___x_2391_ = l_Lean_Expr_isConstOf(v___x_2389_, v___x_2390_);
lean_dec_ref(v___x_2389_);
if (v___x_2391_ == 0)
{
lean_dec_ref(v_arg_2388_);
lean_dec(v_a_2372_);
lean_dec_ref(v_arg_2264_);
lean_dec_ref(v_arg_2231_);
lean_dec_ref(v_arg_2228_);
lean_dec_ref(v_origExpr_2187_);
goto v___jp_2201_;
}
else
{
lean_object* v___x_2392_; 
v___x_2392_ = l_Lean_Meta_Sym_getNatValue_x3f(v_arg_2388_);
if (lean_obj_tag(v___x_2392_) == 0)
{
v___y_2385_ = v___x_2306_;
goto v___jp_2384_;
}
else
{
lean_dec_ref_known(v___x_2392_, 1);
v___y_2385_ = v___x_2391_;
goto v___jp_2384_;
}
}
}
v___jp_2373_:
{
lean_object* v___x_2374_; lean_object* v___x_2375_; 
v___x_2374_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__72, &l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__72_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__72);
v___x_2375_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go_spec__12___redArg(v___x_2374_, v_a_2193_, v_a_2194_, v_a_2195_, v_a_2196_);
if (lean_obj_tag(v___x_2375_) == 0)
{
lean_dec_ref_known(v___x_2375_, 1);
v___y_2266_ = v_a_2188_;
v___y_2267_ = v_a_2189_;
v___y_2268_ = v_a_2190_;
v___y_2269_ = v_a_2191_;
v___y_2270_ = v_a_2192_;
v___y_2271_ = v_a_2193_;
v___y_2272_ = v_a_2194_;
v___y_2273_ = v_a_2195_;
v___y_2274_ = v_a_2196_;
goto v___jp_2265_;
}
else
{
lean_object* v_a_2376_; lean_object* v___x_2378_; uint8_t v_isShared_2379_; uint8_t v_isSharedCheck_2383_; 
lean_dec_ref(v_arg_2264_);
lean_dec_ref(v_arg_2231_);
lean_dec_ref(v_arg_2228_);
lean_dec_ref(v_origExpr_2187_);
v_a_2376_ = lean_ctor_get(v___x_2375_, 0);
v_isSharedCheck_2383_ = !lean_is_exclusive(v___x_2375_);
if (v_isSharedCheck_2383_ == 0)
{
v___x_2378_ = v___x_2375_;
v_isShared_2379_ = v_isSharedCheck_2383_;
goto v_resetjp_2377_;
}
else
{
lean_inc(v_a_2376_);
lean_dec(v___x_2375_);
v___x_2378_ = lean_box(0);
v_isShared_2379_ = v_isSharedCheck_2383_;
goto v_resetjp_2377_;
}
v_resetjp_2377_:
{
lean_object* v___x_2381_; 
if (v_isShared_2379_ == 0)
{
v___x_2381_ = v___x_2378_;
goto v_reusejp_2380_;
}
else
{
lean_object* v_reuseFailAlloc_2382_; 
v_reuseFailAlloc_2382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2382_, 0, v_a_2376_);
v___x_2381_ = v_reuseFailAlloc_2382_;
goto v_reusejp_2380_;
}
v_reusejp_2380_:
{
return v___x_2381_;
}
}
}
}
v___jp_2384_:
{
if (v___y_2385_ == 0)
{
lean_dec(v_a_2372_);
v___y_2266_ = v_a_2188_;
v___y_2267_ = v_a_2189_;
v___y_2268_ = v_a_2190_;
v___y_2269_ = v_a_2191_;
v___y_2270_ = v_a_2192_;
v___y_2271_ = v_a_2193_;
v___y_2272_ = v_a_2194_;
v___y_2273_ = v_a_2195_;
v___y_2274_ = v_a_2196_;
goto v___jp_2265_;
}
else
{
if (lean_obj_tag(v_a_2372_) == 0)
{
if (v___x_2306_ == 0)
{
v___y_2266_ = v_a_2188_;
v___y_2267_ = v_a_2189_;
v___y_2268_ = v_a_2190_;
v___y_2269_ = v_a_2191_;
v___y_2270_ = v_a_2192_;
v___y_2271_ = v_a_2193_;
v___y_2272_ = v_a_2194_;
v___y_2273_ = v_a_2195_;
v___y_2274_ = v_a_2196_;
goto v___jp_2265_;
}
else
{
goto v___jp_2373_;
}
}
else
{
lean_dec_ref_known(v_a_2372_, 1);
goto v___jp_2373_;
}
}
}
}
else
{
lean_object* v_a_2393_; lean_object* v___x_2395_; uint8_t v_isShared_2396_; uint8_t v_isSharedCheck_2400_; 
lean_dec_ref(v_arg_2303_);
lean_dec_ref(v_arg_2264_);
lean_dec_ref(v_arg_2231_);
lean_dec_ref(v_arg_2228_);
lean_dec_ref(v_origExpr_2187_);
v_a_2393_ = lean_ctor_get(v___x_2371_, 0);
v_isSharedCheck_2400_ = !lean_is_exclusive(v___x_2371_);
if (v_isSharedCheck_2400_ == 0)
{
v___x_2395_ = v___x_2371_;
v_isShared_2396_ = v_isSharedCheck_2400_;
goto v_resetjp_2394_;
}
else
{
lean_inc(v_a_2393_);
lean_dec(v___x_2371_);
v___x_2395_ = lean_box(0);
v_isShared_2396_ = v_isSharedCheck_2400_;
goto v_resetjp_2394_;
}
v_resetjp_2394_:
{
lean_object* v___x_2398_; 
if (v_isShared_2396_ == 0)
{
v___x_2398_ = v___x_2395_;
goto v_reusejp_2397_;
}
else
{
lean_object* v_reuseFailAlloc_2399_; 
v_reuseFailAlloc_2399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2399_, 0, v_a_2393_);
v___x_2398_ = v_reuseFailAlloc_2399_;
goto v_reusejp_2397_;
}
v_reusejp_2397_:
{
return v___x_2398_;
}
}
}
}
}
else
{
lean_object* v___x_2401_; 
lean_dec_ref(v___x_2304_);
lean_dec_ref(v_arg_2303_);
lean_dec_ref(v_arg_2264_);
lean_inc_ref(v_arg_2231_);
v___x_2401_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_goOrAtom(v_arg_2231_, v_a_2188_, v_a_2189_, v_a_2190_, v_a_2191_, v_a_2192_, v_a_2193_, v_a_2194_, v_a_2195_, v_a_2196_);
if (lean_obj_tag(v___x_2401_) == 0)
{
lean_object* v_a_2402_; lean_object* v___x_2404_; uint8_t v_isShared_2405_; uint8_t v_isSharedCheck_2475_; 
v_a_2402_ = lean_ctor_get(v___x_2401_, 0);
v_isSharedCheck_2475_ = !lean_is_exclusive(v___x_2401_);
if (v_isSharedCheck_2475_ == 0)
{
v___x_2404_ = v___x_2401_;
v_isShared_2405_ = v_isSharedCheck_2475_;
goto v_resetjp_2403_;
}
else
{
lean_inc(v_a_2402_);
lean_dec(v___x_2401_);
v___x_2404_ = lean_box(0);
v_isShared_2405_ = v_isSharedCheck_2475_;
goto v_resetjp_2403_;
}
v_resetjp_2403_:
{
if (lean_obj_tag(v_a_2402_) == 1)
{
lean_object* v_val_2406_; lean_object* v___x_2407_; 
lean_del_object(v___x_2404_);
v_val_2406_ = lean_ctor_get(v_a_2402_, 0);
lean_inc(v_val_2406_);
lean_dec_ref_known(v_a_2402_, 1);
lean_inc_ref(v_arg_2228_);
v___x_2407_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_goOrAtom(v_arg_2228_, v_a_2188_, v_a_2189_, v_a_2190_, v_a_2191_, v_a_2192_, v_a_2193_, v_a_2194_, v_a_2195_, v_a_2196_);
if (lean_obj_tag(v___x_2407_) == 0)
{
lean_object* v_a_2408_; lean_object* v___x_2410_; uint8_t v_isShared_2411_; uint8_t v_isSharedCheck_2470_; 
v_a_2408_ = lean_ctor_get(v___x_2407_, 0);
v_isSharedCheck_2470_ = !lean_is_exclusive(v___x_2407_);
if (v_isSharedCheck_2470_ == 0)
{
v___x_2410_ = v___x_2407_;
v_isShared_2411_ = v_isSharedCheck_2470_;
goto v_resetjp_2409_;
}
else
{
lean_inc(v_a_2408_);
lean_dec(v___x_2407_);
v___x_2410_ = lean_box(0);
v_isShared_2411_ = v_isSharedCheck_2470_;
goto v_resetjp_2409_;
}
v_resetjp_2409_:
{
if (lean_obj_tag(v_a_2408_) == 1)
{
lean_object* v_val_2412_; lean_object* v___x_2414_; uint8_t v_isShared_2415_; uint8_t v_isSharedCheck_2465_; 
lean_del_object(v___x_2410_);
v_val_2412_ = lean_ctor_get(v_a_2408_, 0);
v_isSharedCheck_2465_ = !lean_is_exclusive(v_a_2408_);
if (v_isSharedCheck_2465_ == 0)
{
v___x_2414_ = v_a_2408_;
v_isShared_2415_ = v_isSharedCheck_2465_;
goto v_resetjp_2413_;
}
else
{
lean_inc(v_val_2412_);
lean_dec(v_a_2408_);
v___x_2414_ = lean_box(0);
v_isShared_2415_ = v_isSharedCheck_2465_;
goto v_resetjp_2413_;
}
v_resetjp_2413_:
{
lean_object* v_width_2416_; lean_object* v_bvExpr_2417_; lean_object* v_expr_2418_; lean_object* v_width_2419_; lean_object* v_bvExpr_2420_; lean_object* v_expr_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; lean_object* v___x_2425_; 
v_width_2416_ = lean_ctor_get(v_val_2406_, 0);
lean_inc_n(v_width_2416_, 2);
v_bvExpr_2417_ = lean_ctor_get(v_val_2406_, 1);
v_expr_2418_ = lean_ctor_get(v_val_2406_, 4);
lean_inc_ref(v_expr_2418_);
v_width_2419_ = lean_ctor_get(v_val_2412_, 0);
lean_inc_n(v_width_2419_, 2);
v_bvExpr_2420_ = lean_ctor_get(v_val_2412_, 1);
v_expr_2421_ = lean_ctor_get(v_val_2412_, 4);
lean_inc_ref(v_expr_2421_);
v___x_2422_ = lean_nat_add(v_width_2416_, v_width_2419_);
lean_inc_ref(v_bvExpr_2420_);
lean_inc_ref(v_bvExpr_2417_);
lean_inc_n(v___x_2422_, 2);
v___x_2423_ = l_Std_Tactic_BVDecide_BVExpr_append___override___redArg(v_width_2416_, v_width_2419_, v___x_2422_, v_bvExpr_2417_, v_bvExpr_2420_);
v___x_2424_ = l_Lean_mkNatLit(v___x_2422_);
lean_inc_ref(v___x_2424_);
v___x_2425_ = l_Lean_Meta_mkEqRefl(v___x_2424_, v_a_2193_, v_a_2194_, v_a_2195_, v_a_2196_);
if (lean_obj_tag(v___x_2425_) == 0)
{
lean_object* v_a_2426_; lean_object* v___x_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; lean_object* v___x_2433_; lean_object* v___f_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; 
v_a_2426_ = lean_ctor_get(v___x_2425_, 0);
lean_inc(v_a_2426_);
lean_dec_ref_known(v___x_2425_, 1);
v___x_2427_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0));
v___x_2428_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1));
v___x_2429_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2));
v___x_2430_ = lean_box(0);
v___x_2431_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__75, &l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__75_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__75);
lean_inc(v_width_2416_);
v___x_2432_ = l_Lean_mkNatLit(v_width_2416_);
lean_inc(v_width_2419_);
v___x_2433_ = l_Lean_mkNatLit(v_width_2419_);
lean_inc_ref(v___x_2433_);
lean_inc_ref(v___x_2432_);
lean_inc_ref(v_expr_2421_);
lean_inc_ref(v_expr_2418_);
v___f_2434_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__3___boxed), 24, 15);
lean_closure_set(v___f_2434_, 0, v_width_2416_);
lean_closure_set(v___f_2434_, 1, v_expr_2418_);
lean_closure_set(v___f_2434_, 2, v_width_2419_);
lean_closure_set(v___f_2434_, 3, v_expr_2421_);
lean_closure_set(v___f_2434_, 4, v_val_2406_);
lean_closure_set(v___f_2434_, 5, v_val_2412_);
lean_closure_set(v___f_2434_, 6, v___x_2427_);
lean_closure_set(v___f_2434_, 7, v___x_2428_);
lean_closure_set(v___f_2434_, 8, v___x_2429_);
lean_closure_set(v___f_2434_, 9, v___x_2233_);
lean_closure_set(v___f_2434_, 10, v___x_2430_);
lean_closure_set(v___f_2434_, 11, v___x_2432_);
lean_closure_set(v___f_2434_, 12, v___x_2433_);
lean_closure_set(v___f_2434_, 13, v_arg_2231_);
lean_closure_set(v___f_2434_, 14, v_arg_2228_);
v___x_2435_ = l_Lean_mkApp6(v___x_2431_, v___x_2432_, v___x_2433_, v___x_2424_, v_expr_2418_, v_expr_2421_, v_a_2426_);
v___x_2436_ = l_Lean_Meta_Sym_shareCommonInc(v___x_2435_, v_a_2191_, v_a_2192_, v_a_2193_, v_a_2194_, v_a_2195_, v_a_2196_);
if (lean_obj_tag(v___x_2436_) == 0)
{
lean_object* v_a_2437_; lean_object* v___x_2439_; uint8_t v_isShared_2440_; uint8_t v_isSharedCheck_2448_; 
v_a_2437_ = lean_ctor_get(v___x_2436_, 0);
v_isSharedCheck_2448_ = !lean_is_exclusive(v___x_2436_);
if (v_isSharedCheck_2448_ == 0)
{
v___x_2439_ = v___x_2436_;
v_isShared_2440_ = v_isSharedCheck_2448_;
goto v_resetjp_2438_;
}
else
{
lean_inc(v_a_2437_);
lean_dec(v___x_2436_);
v___x_2439_ = lean_box(0);
v_isShared_2440_ = v_isSharedCheck_2448_;
goto v_resetjp_2438_;
}
v_resetjp_2438_:
{
lean_object* v___x_2441_; lean_object* v___x_2443_; 
v___x_2441_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2441_, 0, v___x_2422_);
lean_ctor_set(v___x_2441_, 1, v___x_2423_);
lean_ctor_set(v___x_2441_, 2, v_origExpr_2187_);
lean_ctor_set(v___x_2441_, 3, v___f_2434_);
lean_ctor_set(v___x_2441_, 4, v_a_2437_);
if (v_isShared_2415_ == 0)
{
lean_ctor_set(v___x_2414_, 0, v___x_2441_);
v___x_2443_ = v___x_2414_;
goto v_reusejp_2442_;
}
else
{
lean_object* v_reuseFailAlloc_2447_; 
v_reuseFailAlloc_2447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2447_, 0, v___x_2441_);
v___x_2443_ = v_reuseFailAlloc_2447_;
goto v_reusejp_2442_;
}
v_reusejp_2442_:
{
lean_object* v___x_2445_; 
if (v_isShared_2440_ == 0)
{
lean_ctor_set(v___x_2439_, 0, v___x_2443_);
v___x_2445_ = v___x_2439_;
goto v_reusejp_2444_;
}
else
{
lean_object* v_reuseFailAlloc_2446_; 
v_reuseFailAlloc_2446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2446_, 0, v___x_2443_);
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
else
{
lean_object* v_a_2449_; lean_object* v___x_2451_; uint8_t v_isShared_2452_; uint8_t v_isSharedCheck_2456_; 
lean_dec_ref(v___f_2434_);
lean_dec_ref(v___x_2423_);
lean_dec(v___x_2422_);
lean_del_object(v___x_2414_);
lean_dec_ref(v_origExpr_2187_);
v_a_2449_ = lean_ctor_get(v___x_2436_, 0);
v_isSharedCheck_2456_ = !lean_is_exclusive(v___x_2436_);
if (v_isSharedCheck_2456_ == 0)
{
v___x_2451_ = v___x_2436_;
v_isShared_2452_ = v_isSharedCheck_2456_;
goto v_resetjp_2450_;
}
else
{
lean_inc(v_a_2449_);
lean_dec(v___x_2436_);
v___x_2451_ = lean_box(0);
v_isShared_2452_ = v_isSharedCheck_2456_;
goto v_resetjp_2450_;
}
v_resetjp_2450_:
{
lean_object* v___x_2454_; 
if (v_isShared_2452_ == 0)
{
v___x_2454_ = v___x_2451_;
goto v_reusejp_2453_;
}
else
{
lean_object* v_reuseFailAlloc_2455_; 
v_reuseFailAlloc_2455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2455_, 0, v_a_2449_);
v___x_2454_ = v_reuseFailAlloc_2455_;
goto v_reusejp_2453_;
}
v_reusejp_2453_:
{
return v___x_2454_;
}
}
}
}
else
{
lean_object* v_a_2457_; lean_object* v___x_2459_; uint8_t v_isShared_2460_; uint8_t v_isSharedCheck_2464_; 
lean_dec_ref(v___x_2424_);
lean_dec_ref(v___x_2423_);
lean_dec(v___x_2422_);
lean_dec_ref(v_expr_2421_);
lean_dec(v_width_2419_);
lean_dec_ref(v_expr_2418_);
lean_dec(v_width_2416_);
lean_del_object(v___x_2414_);
lean_dec(v_val_2412_);
lean_dec(v_val_2406_);
lean_dec_ref(v_arg_2231_);
lean_dec_ref(v_arg_2228_);
lean_dec_ref(v_origExpr_2187_);
v_a_2457_ = lean_ctor_get(v___x_2425_, 0);
v_isSharedCheck_2464_ = !lean_is_exclusive(v___x_2425_);
if (v_isSharedCheck_2464_ == 0)
{
v___x_2459_ = v___x_2425_;
v_isShared_2460_ = v_isSharedCheck_2464_;
goto v_resetjp_2458_;
}
else
{
lean_inc(v_a_2457_);
lean_dec(v___x_2425_);
v___x_2459_ = lean_box(0);
v_isShared_2460_ = v_isSharedCheck_2464_;
goto v_resetjp_2458_;
}
v_resetjp_2458_:
{
lean_object* v___x_2462_; 
if (v_isShared_2460_ == 0)
{
v___x_2462_ = v___x_2459_;
goto v_reusejp_2461_;
}
else
{
lean_object* v_reuseFailAlloc_2463_; 
v_reuseFailAlloc_2463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2463_, 0, v_a_2457_);
v___x_2462_ = v_reuseFailAlloc_2463_;
goto v_reusejp_2461_;
}
v_reusejp_2461_:
{
return v___x_2462_;
}
}
}
}
}
else
{
lean_object* v___x_2466_; lean_object* v___x_2468_; 
lean_dec(v_a_2408_);
lean_dec(v_val_2406_);
lean_dec_ref(v_arg_2231_);
lean_dec_ref(v_arg_2228_);
lean_dec_ref(v_origExpr_2187_);
v___x_2466_ = lean_box(0);
if (v_isShared_2411_ == 0)
{
lean_ctor_set(v___x_2410_, 0, v___x_2466_);
v___x_2468_ = v___x_2410_;
goto v_reusejp_2467_;
}
else
{
lean_object* v_reuseFailAlloc_2469_; 
v_reuseFailAlloc_2469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2469_, 0, v___x_2466_);
v___x_2468_ = v_reuseFailAlloc_2469_;
goto v_reusejp_2467_;
}
v_reusejp_2467_:
{
return v___x_2468_;
}
}
}
}
else
{
lean_dec(v_val_2406_);
lean_dec_ref(v_arg_2231_);
lean_dec_ref(v_arg_2228_);
lean_dec_ref(v_origExpr_2187_);
return v___x_2407_;
}
}
else
{
lean_object* v___x_2471_; lean_object* v___x_2473_; 
lean_dec(v_a_2402_);
lean_dec_ref(v_arg_2231_);
lean_dec_ref(v_arg_2228_);
lean_dec_ref(v_origExpr_2187_);
v___x_2471_ = lean_box(0);
if (v_isShared_2405_ == 0)
{
lean_ctor_set(v___x_2404_, 0, v___x_2471_);
v___x_2473_ = v___x_2404_;
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
else
{
lean_dec_ref(v_arg_2231_);
lean_dec_ref(v_arg_2228_);
lean_dec_ref(v_origExpr_2187_);
return v___x_2401_;
}
}
}
v___jp_2265_:
{
lean_object* v___x_2275_; uint8_t v___x_2276_; 
v___x_2275_ = l_Lean_Expr_cleanupAnnotations(v_arg_2264_);
v___x_2276_ = l_Lean_Expr_isApp(v___x_2275_);
if (v___x_2276_ == 0)
{
lean_dec_ref(v___x_2275_);
lean_dec_ref(v_arg_2231_);
lean_dec_ref(v_arg_2228_);
lean_dec_ref(v_origExpr_2187_);
goto v___jp_2198_;
}
else
{
lean_object* v___x_2277_; lean_object* v___x_2278_; uint8_t v___x_2279_; 
v___x_2277_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2275_);
v___x_2278_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__8));
v___x_2279_ = l_Lean_Expr_isConstOf(v___x_2277_, v___x_2278_);
lean_dec_ref(v___x_2277_);
if (v___x_2279_ == 0)
{
lean_dec_ref(v_arg_2231_);
lean_dec_ref(v_arg_2228_);
lean_dec_ref(v_origExpr_2187_);
goto v___jp_2198_;
}
else
{
lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; 
v___x_2280_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__25));
v___x_2281_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__27));
v___x_2282_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftReflection(v_arg_2228_, v_arg_2231_, v___f_2215_, v___x_2280_, v___x_2281_, v_origExpr_2187_, v___y_2266_, v___y_2267_, v___y_2268_, v___y_2269_, v___y_2270_, v___y_2271_, v___y_2272_, v___y_2273_, v___y_2274_);
return v___x_2282_;
}
}
}
v___jp_2283_:
{
lean_object* v___x_2293_; uint8_t v___x_2294_; 
v___x_2293_ = l_Lean_Expr_cleanupAnnotations(v_arg_2264_);
v___x_2294_ = l_Lean_Expr_isApp(v___x_2293_);
if (v___x_2294_ == 0)
{
lean_dec_ref(v___x_2293_);
lean_dec_ref(v_arg_2231_);
lean_dec_ref(v_arg_2228_);
lean_dec_ref(v_origExpr_2187_);
goto v___jp_2204_;
}
else
{
lean_object* v___x_2295_; lean_object* v___x_2296_; uint8_t v___x_2297_; 
v___x_2295_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2293_);
v___x_2296_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___closed__8));
v___x_2297_ = l_Lean_Expr_isConstOf(v___x_2295_, v___x_2296_);
lean_dec_ref(v___x_2295_);
if (v___x_2297_ == 0)
{
lean_dec_ref(v_arg_2231_);
lean_dec_ref(v_arg_2228_);
lean_dec_ref(v_origExpr_2187_);
goto v___jp_2204_;
}
else
{
lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; 
v___x_2298_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__29));
v___x_2299_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__31));
v___x_2300_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftReflection(v_arg_2228_, v_arg_2231_, v___f_2214_, v___x_2298_, v___x_2299_, v_origExpr_2187_, v___y_2284_, v___y_2285_, v___y_2286_, v___y_2287_, v___y_2288_, v___y_2289_, v___y_2290_, v___y_2291_, v___y_2292_);
return v___x_2300_;
}
}
}
}
}
else
{
lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; 
lean_dec_ref(v___x_2256_);
v___x_2476_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__77));
v___x_2477_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__79));
v___x_2478_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftReflection(v_arg_2228_, v_arg_2231_, v___f_2216_, v___x_2476_, v___x_2477_, v_origExpr_2187_, v_a_2188_, v_a_2189_, v_a_2190_, v_a_2191_, v_a_2192_, v_a_2193_, v_a_2194_, v_a_2195_, v_a_2196_);
return v___x_2478_;
}
}
else
{
lean_object* v___x_2479_; 
lean_dec_ref(v___x_2256_);
lean_inc_ref(v_arg_2243_);
v___x_2479_ = l_Lean_Meta_Sym_getNatValue_x3f(v_arg_2243_);
if (lean_obj_tag(v___x_2479_) == 1)
{
lean_object* v_val_2480_; lean_object* v___x_2481_; 
v_val_2480_ = lean_ctor_get(v___x_2479_, 0);
lean_inc(v_val_2480_);
lean_dec_ref_known(v___x_2479_, 1);
lean_inc_ref(v_arg_2231_);
v___x_2481_ = l_Lean_Meta_Sym_getNatValue_x3f(v_arg_2231_);
if (lean_obj_tag(v___x_2481_) == 1)
{
lean_object* v_val_2482_; lean_object* v___x_2483_; 
lean_del_object(v___x_2224_);
v_val_2482_ = lean_ctor_get(v___x_2481_, 0);
lean_inc(v_val_2482_);
lean_dec_ref_known(v___x_2481_, 1);
lean_inc_ref(v_arg_2228_);
v___x_2483_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_goOrAtom(v_arg_2228_, v_a_2188_, v_a_2189_, v_a_2190_, v_a_2191_, v_a_2192_, v_a_2193_, v_a_2194_, v_a_2195_, v_a_2196_);
if (lean_obj_tag(v___x_2483_) == 0)
{
lean_object* v_a_2484_; lean_object* v___x_2486_; uint8_t v_isShared_2487_; uint8_t v_isSharedCheck_2530_; 
v_a_2484_ = lean_ctor_get(v___x_2483_, 0);
v_isSharedCheck_2530_ = !lean_is_exclusive(v___x_2483_);
if (v_isSharedCheck_2530_ == 0)
{
v___x_2486_ = v___x_2483_;
v_isShared_2487_ = v_isSharedCheck_2530_;
goto v_resetjp_2485_;
}
else
{
lean_inc(v_a_2484_);
lean_dec(v___x_2483_);
v___x_2486_ = lean_box(0);
v_isShared_2487_ = v_isSharedCheck_2530_;
goto v_resetjp_2485_;
}
v_resetjp_2485_:
{
if (lean_obj_tag(v_a_2484_) == 1)
{
lean_object* v_val_2488_; lean_object* v___x_2490_; uint8_t v_isShared_2491_; uint8_t v_isSharedCheck_2525_; 
lean_del_object(v___x_2486_);
v_val_2488_ = lean_ctor_get(v_a_2484_, 0);
v_isSharedCheck_2525_ = !lean_is_exclusive(v_a_2484_);
if (v_isSharedCheck_2525_ == 0)
{
v___x_2490_ = v_a_2484_;
v_isShared_2491_ = v_isSharedCheck_2525_;
goto v_resetjp_2489_;
}
else
{
lean_inc(v_val_2488_);
lean_dec(v_a_2484_);
v___x_2490_ = lean_box(0);
v_isShared_2491_ = v_isSharedCheck_2525_;
goto v_resetjp_2489_;
}
v_resetjp_2489_:
{
lean_object* v_width_2492_; lean_object* v_bvExpr_2493_; lean_object* v_expr_2494_; lean_object* v___x_2495_; lean_object* v___x_2496_; lean_object* v___x_2497_; lean_object* v___x_2498_; lean_object* v___x_2499_; lean_object* v___x_2500_; lean_object* v___x_2501_; lean_object* v___f_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; 
v_width_2492_ = lean_ctor_get(v_val_2488_, 0);
lean_inc_n(v_width_2492_, 3);
v_bvExpr_2493_ = lean_ctor_get(v_val_2488_, 1);
v_expr_2494_ = lean_ctor_get(v_val_2488_, 4);
lean_inc_ref_n(v_expr_2494_, 2);
lean_inc_ref(v_bvExpr_2493_);
lean_inc(v_val_2482_);
v___x_2495_ = l_Std_Tactic_BVDecide_BVExpr_extract___override(v_width_2492_, v_val_2480_, v_val_2482_, v_bvExpr_2493_);
v___x_2496_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0));
v___x_2497_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1));
v___x_2498_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2));
v___x_2499_ = lean_box(0);
v___x_2500_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__82, &l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__82_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__82);
v___x_2501_ = l_Lean_mkNatLit(v_width_2492_);
lean_inc_ref(v___x_2501_);
lean_inc_ref(v_arg_2231_);
lean_inc_ref(v_arg_2243_);
v___f_2502_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__4___boxed), 21, 12);
lean_closure_set(v___f_2502_, 0, v_width_2492_);
lean_closure_set(v___f_2502_, 1, v_expr_2494_);
lean_closure_set(v___f_2502_, 2, v_val_2488_);
lean_closure_set(v___f_2502_, 3, v___x_2496_);
lean_closure_set(v___f_2502_, 4, v___x_2497_);
lean_closure_set(v___f_2502_, 5, v___x_2498_);
lean_closure_set(v___f_2502_, 6, v___x_2233_);
lean_closure_set(v___f_2502_, 7, v___x_2499_);
lean_closure_set(v___f_2502_, 8, v_arg_2243_);
lean_closure_set(v___f_2502_, 9, v_arg_2231_);
lean_closure_set(v___f_2502_, 10, v___x_2501_);
lean_closure_set(v___f_2502_, 11, v_arg_2228_);
v___x_2503_ = l_Lean_mkApp4(v___x_2500_, v___x_2501_, v_arg_2243_, v_arg_2231_, v_expr_2494_);
v___x_2504_ = l_Lean_Meta_Sym_shareCommonInc(v___x_2503_, v_a_2191_, v_a_2192_, v_a_2193_, v_a_2194_, v_a_2195_, v_a_2196_);
if (lean_obj_tag(v___x_2504_) == 0)
{
lean_object* v_a_2505_; lean_object* v___x_2507_; uint8_t v_isShared_2508_; uint8_t v_isSharedCheck_2516_; 
v_a_2505_ = lean_ctor_get(v___x_2504_, 0);
v_isSharedCheck_2516_ = !lean_is_exclusive(v___x_2504_);
if (v_isSharedCheck_2516_ == 0)
{
v___x_2507_ = v___x_2504_;
v_isShared_2508_ = v_isSharedCheck_2516_;
goto v_resetjp_2506_;
}
else
{
lean_inc(v_a_2505_);
lean_dec(v___x_2504_);
v___x_2507_ = lean_box(0);
v_isShared_2508_ = v_isSharedCheck_2516_;
goto v_resetjp_2506_;
}
v_resetjp_2506_:
{
lean_object* v___x_2509_; lean_object* v___x_2511_; 
v___x_2509_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2509_, 0, v_val_2482_);
lean_ctor_set(v___x_2509_, 1, v___x_2495_);
lean_ctor_set(v___x_2509_, 2, v_origExpr_2187_);
lean_ctor_set(v___x_2509_, 3, v___f_2502_);
lean_ctor_set(v___x_2509_, 4, v_a_2505_);
if (v_isShared_2491_ == 0)
{
lean_ctor_set(v___x_2490_, 0, v___x_2509_);
v___x_2511_ = v___x_2490_;
goto v_reusejp_2510_;
}
else
{
lean_object* v_reuseFailAlloc_2515_; 
v_reuseFailAlloc_2515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2515_, 0, v___x_2509_);
v___x_2511_ = v_reuseFailAlloc_2515_;
goto v_reusejp_2510_;
}
v_reusejp_2510_:
{
lean_object* v___x_2513_; 
if (v_isShared_2508_ == 0)
{
lean_ctor_set(v___x_2507_, 0, v___x_2511_);
v___x_2513_ = v___x_2507_;
goto v_reusejp_2512_;
}
else
{
lean_object* v_reuseFailAlloc_2514_; 
v_reuseFailAlloc_2514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2514_, 0, v___x_2511_);
v___x_2513_ = v_reuseFailAlloc_2514_;
goto v_reusejp_2512_;
}
v_reusejp_2512_:
{
return v___x_2513_;
}
}
}
}
else
{
lean_object* v_a_2517_; lean_object* v___x_2519_; uint8_t v_isShared_2520_; uint8_t v_isSharedCheck_2524_; 
lean_dec_ref(v___f_2502_);
lean_dec_ref(v___x_2495_);
lean_del_object(v___x_2490_);
lean_dec(v_val_2482_);
lean_dec_ref(v_origExpr_2187_);
v_a_2517_ = lean_ctor_get(v___x_2504_, 0);
v_isSharedCheck_2524_ = !lean_is_exclusive(v___x_2504_);
if (v_isSharedCheck_2524_ == 0)
{
v___x_2519_ = v___x_2504_;
v_isShared_2520_ = v_isSharedCheck_2524_;
goto v_resetjp_2518_;
}
else
{
lean_inc(v_a_2517_);
lean_dec(v___x_2504_);
v___x_2519_ = lean_box(0);
v_isShared_2520_ = v_isSharedCheck_2524_;
goto v_resetjp_2518_;
}
v_resetjp_2518_:
{
lean_object* v___x_2522_; 
if (v_isShared_2520_ == 0)
{
v___x_2522_ = v___x_2519_;
goto v_reusejp_2521_;
}
else
{
lean_object* v_reuseFailAlloc_2523_; 
v_reuseFailAlloc_2523_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2523_, 0, v_a_2517_);
v___x_2522_ = v_reuseFailAlloc_2523_;
goto v_reusejp_2521_;
}
v_reusejp_2521_:
{
return v___x_2522_;
}
}
}
}
}
else
{
lean_object* v___x_2526_; lean_object* v___x_2528_; 
lean_dec(v_a_2484_);
lean_dec(v_val_2482_);
lean_dec(v_val_2480_);
lean_dec_ref(v_arg_2243_);
lean_dec_ref(v_arg_2231_);
lean_dec_ref(v_arg_2228_);
lean_dec_ref(v_origExpr_2187_);
v___x_2526_ = lean_box(0);
if (v_isShared_2487_ == 0)
{
lean_ctor_set(v___x_2486_, 0, v___x_2526_);
v___x_2528_ = v___x_2486_;
goto v_reusejp_2527_;
}
else
{
lean_object* v_reuseFailAlloc_2529_; 
v_reuseFailAlloc_2529_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2529_, 0, v___x_2526_);
v___x_2528_ = v_reuseFailAlloc_2529_;
goto v_reusejp_2527_;
}
v_reusejp_2527_:
{
return v___x_2528_;
}
}
}
}
else
{
lean_dec(v_val_2482_);
lean_dec(v_val_2480_);
lean_dec_ref(v_arg_2243_);
lean_dec_ref(v_arg_2231_);
lean_dec_ref(v_arg_2228_);
lean_dec_ref(v_origExpr_2187_);
return v___x_2483_;
}
}
else
{
lean_object* v___x_2531_; lean_object* v___x_2533_; 
lean_dec(v___x_2481_);
lean_dec(v_val_2480_);
lean_dec_ref(v_arg_2243_);
lean_dec_ref(v_arg_2231_);
lean_dec_ref(v_arg_2228_);
lean_dec_ref(v_origExpr_2187_);
v___x_2531_ = lean_box(0);
if (v_isShared_2225_ == 0)
{
lean_ctor_set(v___x_2224_, 0, v___x_2531_);
v___x_2533_ = v___x_2224_;
goto v_reusejp_2532_;
}
else
{
lean_object* v_reuseFailAlloc_2534_; 
v_reuseFailAlloc_2534_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2534_, 0, v___x_2531_);
v___x_2533_ = v_reuseFailAlloc_2534_;
goto v_reusejp_2532_;
}
v_reusejp_2532_:
{
return v___x_2533_;
}
}
}
else
{
lean_object* v___x_2535_; lean_object* v___x_2537_; 
lean_dec(v___x_2479_);
lean_dec_ref(v_arg_2243_);
lean_dec_ref(v_arg_2231_);
lean_dec_ref(v_arg_2228_);
lean_dec_ref(v_origExpr_2187_);
v___x_2535_ = lean_box(0);
if (v_isShared_2225_ == 0)
{
lean_ctor_set(v___x_2224_, 0, v___x_2535_);
v___x_2537_ = v___x_2224_;
goto v_reusejp_2536_;
}
else
{
lean_object* v_reuseFailAlloc_2538_; 
v_reuseFailAlloc_2538_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2538_, 0, v___x_2535_);
v___x_2537_ = v_reuseFailAlloc_2538_;
goto v_reusejp_2536_;
}
v_reusejp_2536_:
{
return v___x_2537_;
}
}
}
}
else
{
lean_object* v___x_2539_; 
lean_dec_ref(v___x_2256_);
lean_del_object(v___x_2224_);
lean_inc_ref(v_origExpr_2187_);
v___x_2539_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_bitVecAtom(v_origExpr_2187_, v___x_2258_, v_a_2189_, v_a_2190_, v_a_2191_, v_a_2192_, v_a_2193_, v_a_2194_, v_a_2195_, v_a_2196_);
if (lean_obj_tag(v___x_2539_) == 0)
{
lean_object* v_a_2540_; lean_object* v___x_2542_; uint8_t v_isShared_2543_; uint8_t v_isSharedCheck_2607_; 
v_a_2540_ = lean_ctor_get(v___x_2539_, 0);
v_isSharedCheck_2607_ = !lean_is_exclusive(v___x_2539_);
if (v_isSharedCheck_2607_ == 0)
{
v___x_2542_ = v___x_2539_;
v_isShared_2543_ = v_isSharedCheck_2607_;
goto v_resetjp_2541_;
}
else
{
lean_inc(v_a_2540_);
lean_dec(v___x_2539_);
v___x_2542_ = lean_box(0);
v_isShared_2543_ = v_isSharedCheck_2607_;
goto v_resetjp_2541_;
}
v_resetjp_2541_:
{
if (lean_obj_tag(v_a_2540_) == 1)
{
lean_object* v_val_2544_; lean_object* v___x_2545_; 
lean_del_object(v___x_2542_);
v_val_2544_ = lean_ctor_get(v_a_2540_, 0);
lean_inc_ref(v_arg_2243_);
v___x_2545_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of(v_arg_2243_, v_a_2188_, v_a_2189_, v_a_2190_, v_a_2191_, v_a_2192_, v_a_2193_, v_a_2194_, v_a_2195_, v_a_2196_);
if (lean_obj_tag(v___x_2545_) == 0)
{
lean_object* v_a_2546_; lean_object* v___x_2548_; uint8_t v_isShared_2549_; uint8_t v_isSharedCheck_2594_; 
v_a_2546_ = lean_ctor_get(v___x_2545_, 0);
v_isSharedCheck_2594_ = !lean_is_exclusive(v___x_2545_);
if (v_isSharedCheck_2594_ == 0)
{
v___x_2548_ = v___x_2545_;
v_isShared_2549_ = v_isSharedCheck_2594_;
goto v_resetjp_2547_;
}
else
{
lean_inc(v_a_2546_);
lean_dec(v___x_2545_);
v___x_2548_ = lean_box(0);
v_isShared_2549_ = v_isSharedCheck_2594_;
goto v_resetjp_2547_;
}
v_resetjp_2547_:
{
if (lean_obj_tag(v_a_2546_) == 1)
{
lean_object* v_val_2550_; lean_object* v___x_2551_; 
lean_del_object(v___x_2548_);
v_val_2550_ = lean_ctor_get(v_a_2546_, 0);
lean_inc(v_val_2550_);
lean_dec_ref_known(v_a_2546_, 1);
lean_inc_ref(v_arg_2231_);
v___x_2551_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_goOrAtom(v_arg_2231_, v_a_2188_, v_a_2189_, v_a_2190_, v_a_2191_, v_a_2192_, v_a_2193_, v_a_2194_, v_a_2195_, v_a_2196_);
if (lean_obj_tag(v___x_2551_) == 0)
{
lean_object* v_a_2552_; lean_object* v___x_2554_; uint8_t v_isShared_2555_; uint8_t v_isSharedCheck_2589_; 
v_a_2552_ = lean_ctor_get(v___x_2551_, 0);
v_isSharedCheck_2589_ = !lean_is_exclusive(v___x_2551_);
if (v_isSharedCheck_2589_ == 0)
{
v___x_2554_ = v___x_2551_;
v_isShared_2555_ = v_isSharedCheck_2589_;
goto v_resetjp_2553_;
}
else
{
lean_inc(v_a_2552_);
lean_dec(v___x_2551_);
v___x_2554_ = lean_box(0);
v_isShared_2555_ = v_isSharedCheck_2589_;
goto v_resetjp_2553_;
}
v_resetjp_2553_:
{
if (lean_obj_tag(v_a_2552_) == 1)
{
lean_object* v_val_2556_; lean_object* v___x_2557_; 
lean_del_object(v___x_2554_);
v_val_2556_ = lean_ctor_get(v_a_2552_, 0);
lean_inc(v_val_2556_);
lean_dec_ref_known(v_a_2552_, 1);
lean_inc_ref(v_arg_2228_);
v___x_2557_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_goOrAtom(v_arg_2228_, v_a_2188_, v_a_2189_, v_a_2190_, v_a_2191_, v_a_2192_, v_a_2193_, v_a_2194_, v_a_2195_, v_a_2196_);
if (lean_obj_tag(v___x_2557_) == 0)
{
lean_object* v_a_2558_; lean_object* v___x_2560_; uint8_t v_isShared_2561_; uint8_t v_isSharedCheck_2584_; 
v_a_2558_ = lean_ctor_get(v___x_2557_, 0);
v_isSharedCheck_2584_ = !lean_is_exclusive(v___x_2557_);
if (v_isSharedCheck_2584_ == 0)
{
v___x_2560_ = v___x_2557_;
v_isShared_2561_ = v_isSharedCheck_2584_;
goto v_resetjp_2559_;
}
else
{
lean_inc(v_a_2558_);
lean_dec(v___x_2557_);
v___x_2560_ = lean_box(0);
v_isShared_2561_ = v_isSharedCheck_2584_;
goto v_resetjp_2559_;
}
v_resetjp_2559_:
{
if (lean_obj_tag(v_a_2558_) == 1)
{
lean_object* v_val_2562_; lean_object* v___x_2563_; 
lean_del_object(v___x_2560_);
v_val_2562_ = lean_ctor_get(v_a_2558_, 0);
lean_inc(v_val_2562_);
lean_dec_ref_known(v_a_2558_, 1);
lean_inc(v_val_2544_);
v___x_2563_ = l_Lean_Meta_Tactic_BVDecide_addCondLemmas___redArg(v_val_2550_, v_val_2544_, v_val_2556_, v_val_2562_, v_arg_2243_, v_origExpr_2187_, v_arg_2231_, v_arg_2228_, v_a_2188_, v_a_2191_, v_a_2192_, v_a_2193_, v_a_2194_, v_a_2195_, v_a_2196_);
if (lean_obj_tag(v___x_2563_) == 0)
{
lean_object* v___x_2565_; uint8_t v_isShared_2566_; uint8_t v_isSharedCheck_2570_; 
v_isSharedCheck_2570_ = !lean_is_exclusive(v___x_2563_);
if (v_isSharedCheck_2570_ == 0)
{
lean_object* v_unused_2571_; 
v_unused_2571_ = lean_ctor_get(v___x_2563_, 0);
lean_dec(v_unused_2571_);
v___x_2565_ = v___x_2563_;
v_isShared_2566_ = v_isSharedCheck_2570_;
goto v_resetjp_2564_;
}
else
{
lean_dec(v___x_2563_);
v___x_2565_ = lean_box(0);
v_isShared_2566_ = v_isSharedCheck_2570_;
goto v_resetjp_2564_;
}
v_resetjp_2564_:
{
lean_object* v___x_2568_; 
if (v_isShared_2566_ == 0)
{
lean_ctor_set(v___x_2565_, 0, v_a_2540_);
v___x_2568_ = v___x_2565_;
goto v_reusejp_2567_;
}
else
{
lean_object* v_reuseFailAlloc_2569_; 
v_reuseFailAlloc_2569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2569_, 0, v_a_2540_);
v___x_2568_ = v_reuseFailAlloc_2569_;
goto v_reusejp_2567_;
}
v_reusejp_2567_:
{
return v___x_2568_;
}
}
}
else
{
lean_object* v_a_2572_; lean_object* v___x_2574_; uint8_t v_isShared_2575_; uint8_t v_isSharedCheck_2579_; 
lean_dec_ref_known(v_a_2540_, 1);
v_a_2572_ = lean_ctor_get(v___x_2563_, 0);
v_isSharedCheck_2579_ = !lean_is_exclusive(v___x_2563_);
if (v_isSharedCheck_2579_ == 0)
{
v___x_2574_ = v___x_2563_;
v_isShared_2575_ = v_isSharedCheck_2579_;
goto v_resetjp_2573_;
}
else
{
lean_inc(v_a_2572_);
lean_dec(v___x_2563_);
v___x_2574_ = lean_box(0);
v_isShared_2575_ = v_isSharedCheck_2579_;
goto v_resetjp_2573_;
}
v_resetjp_2573_:
{
lean_object* v___x_2577_; 
if (v_isShared_2575_ == 0)
{
v___x_2577_ = v___x_2574_;
goto v_reusejp_2576_;
}
else
{
lean_object* v_reuseFailAlloc_2578_; 
v_reuseFailAlloc_2578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2578_, 0, v_a_2572_);
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
else
{
lean_object* v___x_2580_; lean_object* v___x_2582_; 
lean_dec(v_a_2558_);
lean_dec(v_val_2556_);
lean_dec(v_val_2550_);
lean_dec_ref_known(v_a_2540_, 1);
lean_dec_ref(v_arg_2243_);
lean_dec_ref(v_arg_2231_);
lean_dec_ref(v_arg_2228_);
lean_dec_ref(v_origExpr_2187_);
v___x_2580_ = lean_box(0);
if (v_isShared_2561_ == 0)
{
lean_ctor_set(v___x_2560_, 0, v___x_2580_);
v___x_2582_ = v___x_2560_;
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
lean_dec(v_val_2556_);
lean_dec(v_val_2550_);
lean_dec_ref_known(v_a_2540_, 1);
lean_dec_ref(v_arg_2243_);
lean_dec_ref(v_arg_2231_);
lean_dec_ref(v_arg_2228_);
lean_dec_ref(v_origExpr_2187_);
return v___x_2557_;
}
}
else
{
lean_object* v___x_2585_; lean_object* v___x_2587_; 
lean_dec(v_a_2552_);
lean_dec(v_val_2550_);
lean_dec_ref_known(v_a_2540_, 1);
lean_dec_ref(v_arg_2243_);
lean_dec_ref(v_arg_2231_);
lean_dec_ref(v_arg_2228_);
lean_dec_ref(v_origExpr_2187_);
v___x_2585_ = lean_box(0);
if (v_isShared_2555_ == 0)
{
lean_ctor_set(v___x_2554_, 0, v___x_2585_);
v___x_2587_ = v___x_2554_;
goto v_reusejp_2586_;
}
else
{
lean_object* v_reuseFailAlloc_2588_; 
v_reuseFailAlloc_2588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2588_, 0, v___x_2585_);
v___x_2587_ = v_reuseFailAlloc_2588_;
goto v_reusejp_2586_;
}
v_reusejp_2586_:
{
return v___x_2587_;
}
}
}
}
else
{
lean_dec(v_val_2550_);
lean_dec_ref_known(v_a_2540_, 1);
lean_dec_ref(v_arg_2243_);
lean_dec_ref(v_arg_2231_);
lean_dec_ref(v_arg_2228_);
lean_dec_ref(v_origExpr_2187_);
return v___x_2551_;
}
}
else
{
lean_object* v___x_2590_; lean_object* v___x_2592_; 
lean_dec(v_a_2546_);
lean_dec_ref_known(v_a_2540_, 1);
lean_dec_ref(v_arg_2243_);
lean_dec_ref(v_arg_2231_);
lean_dec_ref(v_arg_2228_);
lean_dec_ref(v_origExpr_2187_);
v___x_2590_ = lean_box(0);
if (v_isShared_2549_ == 0)
{
lean_ctor_set(v___x_2548_, 0, v___x_2590_);
v___x_2592_ = v___x_2548_;
goto v_reusejp_2591_;
}
else
{
lean_object* v_reuseFailAlloc_2593_; 
v_reuseFailAlloc_2593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2593_, 0, v___x_2590_);
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
lean_object* v_a_2595_; lean_object* v___x_2597_; uint8_t v_isShared_2598_; uint8_t v_isSharedCheck_2602_; 
lean_dec_ref_known(v_a_2540_, 1);
lean_dec_ref(v_arg_2243_);
lean_dec_ref(v_arg_2231_);
lean_dec_ref(v_arg_2228_);
lean_dec_ref(v_origExpr_2187_);
v_a_2595_ = lean_ctor_get(v___x_2545_, 0);
v_isSharedCheck_2602_ = !lean_is_exclusive(v___x_2545_);
if (v_isSharedCheck_2602_ == 0)
{
v___x_2597_ = v___x_2545_;
v_isShared_2598_ = v_isSharedCheck_2602_;
goto v_resetjp_2596_;
}
else
{
lean_inc(v_a_2595_);
lean_dec(v___x_2545_);
v___x_2597_ = lean_box(0);
v_isShared_2598_ = v_isSharedCheck_2602_;
goto v_resetjp_2596_;
}
v_resetjp_2596_:
{
lean_object* v___x_2600_; 
if (v_isShared_2598_ == 0)
{
v___x_2600_ = v___x_2597_;
goto v_reusejp_2599_;
}
else
{
lean_object* v_reuseFailAlloc_2601_; 
v_reuseFailAlloc_2601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2601_, 0, v_a_2595_);
v___x_2600_ = v_reuseFailAlloc_2601_;
goto v_reusejp_2599_;
}
v_reusejp_2599_:
{
return v___x_2600_;
}
}
}
}
else
{
lean_object* v___x_2603_; lean_object* v___x_2605_; 
lean_dec(v_a_2540_);
lean_dec_ref(v_arg_2243_);
lean_dec_ref(v_arg_2231_);
lean_dec_ref(v_arg_2228_);
lean_dec_ref(v_origExpr_2187_);
v___x_2603_ = lean_box(0);
if (v_isShared_2543_ == 0)
{
lean_ctor_set(v___x_2542_, 0, v___x_2603_);
v___x_2605_ = v___x_2542_;
goto v_reusejp_2604_;
}
else
{
lean_object* v_reuseFailAlloc_2606_; 
v_reuseFailAlloc_2606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2606_, 0, v___x_2603_);
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
lean_dec_ref(v_arg_2243_);
lean_dec_ref(v_arg_2231_);
lean_dec_ref(v_arg_2228_);
lean_dec_ref(v_origExpr_2187_);
return v___x_2539_;
}
}
}
}
else
{
lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; 
lean_dec_ref(v___x_2244_);
lean_dec_ref(v_arg_2243_);
lean_dec_ref(v_arg_2231_);
lean_del_object(v___x_2224_);
v___x_2608_ = lean_box(0);
v___x_2609_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__84));
v___x_2610_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection(v_arg_2228_, v___x_2608_, v___x_2609_, v_origExpr_2187_, v_a_2188_, v_a_2189_, v_a_2190_, v_a_2191_, v_a_2192_, v_a_2193_, v_a_2194_, v_a_2195_, v_a_2196_);
return v___x_2610_;
}
}
else
{
lean_object* v___x_2611_; 
lean_dec_ref(v___x_2244_);
lean_dec_ref(v_arg_2243_);
v___x_2611_ = l_Lean_Meta_Sym_getNatValue_x3f(v_arg_2228_);
if (lean_obj_tag(v___x_2611_) == 1)
{
lean_object* v_val_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; lean_object* v___x_2615_; 
lean_del_object(v___x_2224_);
v_val_2612_ = lean_ctor_get(v___x_2611_, 0);
lean_inc(v_val_2612_);
lean_dec_ref_known(v___x_2611_, 1);
v___x_2613_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__11));
v___x_2614_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__86));
v___x_2615_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection(v_val_2612_, v_arg_2231_, v___f_2213_, v___x_2613_, v___x_2614_, v_origExpr_2187_, v_a_2188_, v_a_2189_, v_a_2190_, v_a_2191_, v_a_2192_, v_a_2193_, v_a_2194_, v_a_2195_, v_a_2196_);
return v___x_2615_;
}
else
{
lean_object* v___x_2616_; lean_object* v___x_2618_; 
lean_dec(v___x_2611_);
lean_dec_ref(v_arg_2231_);
lean_dec_ref(v_origExpr_2187_);
v___x_2616_ = lean_box(0);
if (v_isShared_2225_ == 0)
{
lean_ctor_set(v___x_2224_, 0, v___x_2616_);
v___x_2618_ = v___x_2224_;
goto v_reusejp_2617_;
}
else
{
lean_object* v_reuseFailAlloc_2619_; 
v_reuseFailAlloc_2619_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2619_, 0, v___x_2616_);
v___x_2618_ = v_reuseFailAlloc_2619_;
goto v_reusejp_2617_;
}
v_reusejp_2617_:
{
return v___x_2618_;
}
}
}
}
else
{
lean_object* v___x_2620_; 
lean_dec_ref(v___x_2244_);
lean_dec_ref(v_arg_2243_);
lean_del_object(v___x_2224_);
lean_inc_ref(v_arg_2228_);
v___x_2620_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_goOrAtom(v_arg_2228_, v_a_2188_, v_a_2189_, v_a_2190_, v_a_2191_, v_a_2192_, v_a_2193_, v_a_2194_, v_a_2195_, v_a_2196_);
if (lean_obj_tag(v___x_2620_) == 0)
{
lean_object* v_a_2621_; lean_object* v___x_2623_; uint8_t v_isShared_2624_; uint8_t v_isSharedCheck_2686_; 
v_a_2621_ = lean_ctor_get(v___x_2620_, 0);
v_isSharedCheck_2686_ = !lean_is_exclusive(v___x_2620_);
if (v_isSharedCheck_2686_ == 0)
{
v___x_2623_ = v___x_2620_;
v_isShared_2624_ = v_isSharedCheck_2686_;
goto v_resetjp_2622_;
}
else
{
lean_inc(v_a_2621_);
lean_dec(v___x_2620_);
v___x_2623_ = lean_box(0);
v_isShared_2624_ = v_isSharedCheck_2686_;
goto v_resetjp_2622_;
}
v_resetjp_2622_:
{
if (lean_obj_tag(v_a_2621_) == 1)
{
lean_object* v_val_2625_; lean_object* v___x_2626_; 
v_val_2625_ = lean_ctor_get(v_a_2621_, 0);
lean_inc(v_val_2625_);
lean_dec_ref_known(v_a_2621_, 1);
v___x_2626_ = l_Lean_Meta_Sym_getNatValue_x3f(v_arg_2231_);
if (lean_obj_tag(v___x_2626_) == 1)
{
lean_object* v_val_2627_; lean_object* v___x_2629_; uint8_t v_isShared_2630_; uint8_t v_isSharedCheck_2677_; 
lean_del_object(v___x_2623_);
v_val_2627_ = lean_ctor_get(v___x_2626_, 0);
v_isSharedCheck_2677_ = !lean_is_exclusive(v___x_2626_);
if (v_isSharedCheck_2677_ == 0)
{
v___x_2629_ = v___x_2626_;
v_isShared_2630_ = v_isSharedCheck_2677_;
goto v_resetjp_2628_;
}
else
{
lean_inc(v_val_2627_);
lean_dec(v___x_2626_);
v___x_2629_ = lean_box(0);
v_isShared_2630_ = v_isSharedCheck_2677_;
goto v_resetjp_2628_;
}
v_resetjp_2628_:
{
lean_object* v_width_2631_; lean_object* v_bvExpr_2632_; lean_object* v_expr_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; lean_object* v___x_2637_; 
v_width_2631_ = lean_ctor_get(v_val_2625_, 0);
lean_inc_n(v_width_2631_, 2);
v_bvExpr_2632_ = lean_ctor_get(v_val_2625_, 1);
v_expr_2633_ = lean_ctor_get(v_val_2625_, 4);
lean_inc_ref(v_expr_2633_);
v___x_2634_ = lean_nat_mul(v_width_2631_, v_val_2627_);
lean_inc_ref(v_bvExpr_2632_);
lean_inc(v_val_2627_);
lean_inc_n(v___x_2634_, 2);
v___x_2635_ = l_Std_Tactic_BVDecide_BVExpr_replicate___override___redArg(v_width_2631_, v___x_2634_, v_val_2627_, v_bvExpr_2632_);
v___x_2636_ = l_Lean_mkNatLit(v___x_2634_);
lean_inc_ref(v___x_2636_);
v___x_2637_ = l_Lean_Meta_mkEqRefl(v___x_2636_, v_a_2193_, v_a_2194_, v_a_2195_, v_a_2196_);
if (lean_obj_tag(v___x_2637_) == 0)
{
lean_object* v_a_2638_; lean_object* v___x_2639_; lean_object* v___x_2640_; lean_object* v___x_2641_; lean_object* v___x_2642_; lean_object* v___x_2643_; lean_object* v___x_2644_; lean_object* v___x_2645_; lean_object* v___f_2646_; lean_object* v___x_2647_; lean_object* v___x_2648_; 
v_a_2638_ = lean_ctor_get(v___x_2637_, 0);
lean_inc(v_a_2638_);
lean_dec_ref_known(v___x_2637_, 1);
v___x_2639_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0));
v___x_2640_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1));
v___x_2641_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2));
v___x_2642_ = lean_box(0);
v___x_2643_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__88, &l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__88_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__88);
lean_inc(v_width_2631_);
v___x_2644_ = l_Lean_mkNatLit(v_width_2631_);
v___x_2645_ = l_Lean_mkNatLit(v_val_2627_);
lean_inc_ref(v___x_2644_);
lean_inc_ref(v___x_2645_);
lean_inc_ref(v_expr_2633_);
v___f_2646_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___lam__5___boxed), 20, 11);
lean_closure_set(v___f_2646_, 0, v_width_2631_);
lean_closure_set(v___f_2646_, 1, v_expr_2633_);
lean_closure_set(v___f_2646_, 2, v_val_2625_);
lean_closure_set(v___f_2646_, 3, v___x_2639_);
lean_closure_set(v___f_2646_, 4, v___x_2640_);
lean_closure_set(v___f_2646_, 5, v___x_2641_);
lean_closure_set(v___f_2646_, 6, v___x_2233_);
lean_closure_set(v___f_2646_, 7, v___x_2642_);
lean_closure_set(v___f_2646_, 8, v___x_2645_);
lean_closure_set(v___f_2646_, 9, v___x_2644_);
lean_closure_set(v___f_2646_, 10, v_arg_2228_);
v___x_2647_ = l_Lean_mkApp5(v___x_2643_, v___x_2644_, v___x_2636_, v___x_2645_, v_expr_2633_, v_a_2638_);
v___x_2648_ = l_Lean_Meta_Sym_shareCommonInc(v___x_2647_, v_a_2191_, v_a_2192_, v_a_2193_, v_a_2194_, v_a_2195_, v_a_2196_);
if (lean_obj_tag(v___x_2648_) == 0)
{
lean_object* v_a_2649_; lean_object* v___x_2651_; uint8_t v_isShared_2652_; uint8_t v_isSharedCheck_2660_; 
v_a_2649_ = lean_ctor_get(v___x_2648_, 0);
v_isSharedCheck_2660_ = !lean_is_exclusive(v___x_2648_);
if (v_isSharedCheck_2660_ == 0)
{
v___x_2651_ = v___x_2648_;
v_isShared_2652_ = v_isSharedCheck_2660_;
goto v_resetjp_2650_;
}
else
{
lean_inc(v_a_2649_);
lean_dec(v___x_2648_);
v___x_2651_ = lean_box(0);
v_isShared_2652_ = v_isSharedCheck_2660_;
goto v_resetjp_2650_;
}
v_resetjp_2650_:
{
lean_object* v___x_2653_; lean_object* v___x_2655_; 
v___x_2653_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2653_, 0, v___x_2634_);
lean_ctor_set(v___x_2653_, 1, v___x_2635_);
lean_ctor_set(v___x_2653_, 2, v_origExpr_2187_);
lean_ctor_set(v___x_2653_, 3, v___f_2646_);
lean_ctor_set(v___x_2653_, 4, v_a_2649_);
if (v_isShared_2630_ == 0)
{
lean_ctor_set(v___x_2629_, 0, v___x_2653_);
v___x_2655_ = v___x_2629_;
goto v_reusejp_2654_;
}
else
{
lean_object* v_reuseFailAlloc_2659_; 
v_reuseFailAlloc_2659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2659_, 0, v___x_2653_);
v___x_2655_ = v_reuseFailAlloc_2659_;
goto v_reusejp_2654_;
}
v_reusejp_2654_:
{
lean_object* v___x_2657_; 
if (v_isShared_2652_ == 0)
{
lean_ctor_set(v___x_2651_, 0, v___x_2655_);
v___x_2657_ = v___x_2651_;
goto v_reusejp_2656_;
}
else
{
lean_object* v_reuseFailAlloc_2658_; 
v_reuseFailAlloc_2658_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2658_, 0, v___x_2655_);
v___x_2657_ = v_reuseFailAlloc_2658_;
goto v_reusejp_2656_;
}
v_reusejp_2656_:
{
return v___x_2657_;
}
}
}
}
else
{
lean_object* v_a_2661_; lean_object* v___x_2663_; uint8_t v_isShared_2664_; uint8_t v_isSharedCheck_2668_; 
lean_dec_ref(v___f_2646_);
lean_dec_ref(v___x_2635_);
lean_dec(v___x_2634_);
lean_del_object(v___x_2629_);
lean_dec_ref(v_origExpr_2187_);
v_a_2661_ = lean_ctor_get(v___x_2648_, 0);
v_isSharedCheck_2668_ = !lean_is_exclusive(v___x_2648_);
if (v_isSharedCheck_2668_ == 0)
{
v___x_2663_ = v___x_2648_;
v_isShared_2664_ = v_isSharedCheck_2668_;
goto v_resetjp_2662_;
}
else
{
lean_inc(v_a_2661_);
lean_dec(v___x_2648_);
v___x_2663_ = lean_box(0);
v_isShared_2664_ = v_isSharedCheck_2668_;
goto v_resetjp_2662_;
}
v_resetjp_2662_:
{
lean_object* v___x_2666_; 
if (v_isShared_2664_ == 0)
{
v___x_2666_ = v___x_2663_;
goto v_reusejp_2665_;
}
else
{
lean_object* v_reuseFailAlloc_2667_; 
v_reuseFailAlloc_2667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2667_, 0, v_a_2661_);
v___x_2666_ = v_reuseFailAlloc_2667_;
goto v_reusejp_2665_;
}
v_reusejp_2665_:
{
return v___x_2666_;
}
}
}
}
else
{
lean_object* v_a_2669_; lean_object* v___x_2671_; uint8_t v_isShared_2672_; uint8_t v_isSharedCheck_2676_; 
lean_dec_ref(v___x_2636_);
lean_dec_ref(v___x_2635_);
lean_dec(v___x_2634_);
lean_dec_ref(v_expr_2633_);
lean_dec(v_width_2631_);
lean_del_object(v___x_2629_);
lean_dec(v_val_2627_);
lean_dec(v_val_2625_);
lean_dec_ref(v_arg_2228_);
lean_dec_ref(v_origExpr_2187_);
v_a_2669_ = lean_ctor_get(v___x_2637_, 0);
v_isSharedCheck_2676_ = !lean_is_exclusive(v___x_2637_);
if (v_isSharedCheck_2676_ == 0)
{
v___x_2671_ = v___x_2637_;
v_isShared_2672_ = v_isSharedCheck_2676_;
goto v_resetjp_2670_;
}
else
{
lean_inc(v_a_2669_);
lean_dec(v___x_2637_);
v___x_2671_ = lean_box(0);
v_isShared_2672_ = v_isSharedCheck_2676_;
goto v_resetjp_2670_;
}
v_resetjp_2670_:
{
lean_object* v___x_2674_; 
if (v_isShared_2672_ == 0)
{
v___x_2674_ = v___x_2671_;
goto v_reusejp_2673_;
}
else
{
lean_object* v_reuseFailAlloc_2675_; 
v_reuseFailAlloc_2675_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2675_, 0, v_a_2669_);
v___x_2674_ = v_reuseFailAlloc_2675_;
goto v_reusejp_2673_;
}
v_reusejp_2673_:
{
return v___x_2674_;
}
}
}
}
}
else
{
lean_object* v___x_2678_; lean_object* v___x_2680_; 
lean_dec(v___x_2626_);
lean_dec(v_val_2625_);
lean_dec_ref(v_arg_2228_);
lean_dec_ref(v_origExpr_2187_);
v___x_2678_ = lean_box(0);
if (v_isShared_2624_ == 0)
{
lean_ctor_set(v___x_2623_, 0, v___x_2678_);
v___x_2680_ = v___x_2623_;
goto v_reusejp_2679_;
}
else
{
lean_object* v_reuseFailAlloc_2681_; 
v_reuseFailAlloc_2681_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2681_, 0, v___x_2678_);
v___x_2680_ = v_reuseFailAlloc_2681_;
goto v_reusejp_2679_;
}
v_reusejp_2679_:
{
return v___x_2680_;
}
}
}
else
{
lean_object* v___x_2682_; lean_object* v___x_2684_; 
lean_dec(v_a_2621_);
lean_dec_ref(v_arg_2231_);
lean_dec_ref(v_arg_2228_);
lean_dec_ref(v_origExpr_2187_);
v___x_2682_ = lean_box(0);
if (v_isShared_2624_ == 0)
{
lean_ctor_set(v___x_2623_, 0, v___x_2682_);
v___x_2684_ = v___x_2623_;
goto v_reusejp_2683_;
}
else
{
lean_object* v_reuseFailAlloc_2685_; 
v_reuseFailAlloc_2685_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2685_, 0, v___x_2682_);
v___x_2684_ = v_reuseFailAlloc_2685_;
goto v_reusejp_2683_;
}
v_reusejp_2683_:
{
return v___x_2684_;
}
}
}
}
else
{
lean_dec_ref(v_arg_2231_);
lean_dec_ref(v_arg_2228_);
lean_dec_ref(v_origExpr_2187_);
return v___x_2620_;
}
}
}
else
{
lean_object* v___x_2687_; lean_object* v___x_2688_; lean_object* v___x_2689_; 
lean_dec_ref(v___x_2244_);
lean_dec_ref(v_arg_2243_);
lean_del_object(v___x_2224_);
v___x_2687_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__5));
v___x_2688_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__90));
v___x_2689_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_rotateReflection(v_arg_2228_, v_arg_2231_, v___f_2217_, v___x_2687_, v___x_2688_, v_origExpr_2187_, v_a_2188_, v_a_2189_, v_a_2190_, v_a_2191_, v_a_2192_, v_a_2193_, v_a_2194_, v_a_2195_, v_a_2196_);
return v___x_2689_;
}
}
else
{
lean_object* v___x_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; 
lean_dec_ref(v___x_2244_);
lean_dec_ref(v_arg_2243_);
lean_del_object(v___x_2224_);
v___x_2690_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___closed__8));
v___x_2691_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__92));
v___x_2692_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_rotateReflection(v_arg_2228_, v_arg_2231_, v___f_2218_, v___x_2690_, v___x_2691_, v_origExpr_2187_, v_a_2188_, v_a_2189_, v_a_2190_, v_a_2191_, v_a_2192_, v_a_2193_, v_a_2194_, v_a_2195_, v_a_2196_);
return v___x_2692_;
}
}
}
else
{
lean_object* v___x_2693_; 
lean_dec_ref(v___x_2232_);
lean_dec_ref(v_arg_2231_);
lean_dec_ref(v_arg_2228_);
lean_del_object(v___x_2224_);
v___x_2693_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_goBvLit(v_origExpr_2187_, v_a_2189_, v_a_2190_, v_a_2191_, v_a_2192_, v_a_2193_, v_a_2194_, v_a_2195_, v_a_2196_);
return v___x_2693_;
}
}
else
{
lean_object* v___x_2694_; lean_object* v___x_2695_; lean_object* v___x_2696_; 
lean_dec_ref(v___x_2232_);
lean_dec_ref(v_arg_2231_);
lean_del_object(v___x_2224_);
v___x_2694_ = lean_box(4);
v___x_2695_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__94));
v___x_2696_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection(v_arg_2228_, v___x_2694_, v___x_2695_, v_origExpr_2187_, v_a_2188_, v_a_2189_, v_a_2190_, v_a_2191_, v_a_2192_, v_a_2193_, v_a_2194_, v_a_2195_, v_a_2196_);
return v___x_2696_;
}
}
else
{
lean_object* v___x_2697_; lean_object* v___x_2698_; lean_object* v___x_2699_; 
lean_dec_ref(v___x_2232_);
lean_dec_ref(v_arg_2231_);
lean_del_object(v___x_2224_);
v___x_2697_ = lean_box(5);
v___x_2698_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__96));
v___x_2699_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection(v_arg_2228_, v___x_2697_, v___x_2698_, v_origExpr_2187_, v_a_2188_, v_a_2189_, v_a_2190_, v_a_2191_, v_a_2192_, v_a_2193_, v_a_2194_, v_a_2195_, v_a_2196_);
return v___x_2699_;
}
}
else
{
lean_object* v___x_2700_; lean_object* v___x_2701_; lean_object* v___x_2702_; 
lean_dec_ref(v___x_2232_);
lean_dec_ref(v_arg_2231_);
lean_del_object(v___x_2224_);
v___x_2700_ = lean_box(6);
v___x_2701_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___closed__98));
v___x_2702_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection(v_arg_2228_, v___x_2700_, v___x_2701_, v_origExpr_2187_, v_a_2188_, v_a_2189_, v_a_2190_, v_a_2191_, v_a_2192_, v_a_2193_, v_a_2194_, v_a_2195_, v_a_2196_);
return v___x_2702_;
}
}
}
}
}
else
{
lean_object* v_a_2704_; lean_object* v___x_2706_; uint8_t v_isShared_2707_; uint8_t v_isSharedCheck_2711_; 
lean_dec_ref(v_origExpr_2187_);
v_a_2704_ = lean_ctor_get(v___x_2221_, 0);
v_isSharedCheck_2711_ = !lean_is_exclusive(v___x_2221_);
if (v_isSharedCheck_2711_ == 0)
{
v___x_2706_ = v___x_2221_;
v_isShared_2707_ = v_isSharedCheck_2711_;
goto v_resetjp_2705_;
}
else
{
lean_inc(v_a_2704_);
lean_dec(v___x_2221_);
v___x_2706_ = lean_box(0);
v_isShared_2707_ = v_isSharedCheck_2711_;
goto v_resetjp_2705_;
}
v_resetjp_2705_:
{
lean_object* v___x_2709_; 
if (v_isShared_2707_ == 0)
{
v___x_2709_ = v___x_2706_;
goto v_reusejp_2708_;
}
else
{
lean_object* v_reuseFailAlloc_2710_; 
v_reuseFailAlloc_2710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2710_, 0, v_a_2704_);
v___x_2709_ = v_reuseFailAlloc_2710_;
goto v_reusejp_2708_;
}
v_reusejp_2708_:
{
return v___x_2709_;
}
}
}
}
else
{
lean_object* v_a_2712_; lean_object* v___x_2714_; uint8_t v_isShared_2715_; uint8_t v_isSharedCheck_2719_; 
lean_dec_ref(v_origExpr_2187_);
v_a_2712_ = lean_ctor_get(v___x_2220_, 0);
v_isSharedCheck_2719_ = !lean_is_exclusive(v___x_2220_);
if (v_isSharedCheck_2719_ == 0)
{
v___x_2714_ = v___x_2220_;
v_isShared_2715_ = v_isSharedCheck_2719_;
goto v_resetjp_2713_;
}
else
{
lean_inc(v_a_2712_);
lean_dec(v___x_2220_);
v___x_2714_ = lean_box(0);
v_isShared_2715_ = v_isSharedCheck_2719_;
goto v_resetjp_2713_;
}
v_resetjp_2713_:
{
lean_object* v___x_2717_; 
if (v_isShared_2715_ == 0)
{
v___x_2717_ = v___x_2714_;
goto v_reusejp_2716_;
}
else
{
lean_object* v_reuseFailAlloc_2718_; 
v_reuseFailAlloc_2718_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2718_, 0, v_a_2712_);
v___x_2717_ = v_reuseFailAlloc_2718_;
goto v_reusejp_2716_;
}
v_reusejp_2716_:
{
return v___x_2717_;
}
}
}
v___jp_2198_:
{
lean_object* v___x_2199_; lean_object* v___x_2200_; 
v___x_2199_ = lean_box(0);
v___x_2200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2200_, 0, v___x_2199_);
return v___x_2200_;
}
v___jp_2201_:
{
lean_object* v___x_2202_; lean_object* v___x_2203_; 
v___x_2202_ = lean_box(0);
v___x_2203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2203_, 0, v___x_2202_);
return v___x_2203_;
}
v___jp_2204_:
{
lean_object* v___x_2205_; lean_object* v___x_2206_; 
v___x_2205_ = lean_box(0);
v___x_2206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2206_, 0, v___x_2205_);
return v___x_2206_;
}
v___jp_2207_:
{
lean_object* v___x_2208_; lean_object* v___x_2209_; 
v___x_2208_ = lean_box(0);
v___x_2209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2209_, 0, v___x_2208_);
return v___x_2209_;
}
v___jp_2210_:
{
lean_object* v___x_2211_; lean_object* v___x_2212_; 
v___x_2211_ = lean_box(0);
v___x_2212_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2212_, 0, v___x_2211_);
return v___x_2212_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_LemmaM_withBVExprCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_goOrAtom_spec__10(lean_object* v_e_2720_, lean_object* v_a_2721_, lean_object* v_a_2722_, lean_object* v_a_2723_, lean_object* v_a_2724_, lean_object* v_a_2725_, lean_object* v_a_2726_, lean_object* v_a_2727_, lean_object* v_a_2728_, lean_object* v_a_2729_){
_start:
{
lean_object* v___y_2732_; lean_object* v___x_2755_; lean_object* v_bvExprCache_2756_; lean_object* v___x_2757_; 
v___x_2755_ = lean_st_ref_get(v_a_2721_);
v_bvExprCache_2756_ = lean_ctor_get(v___x_2755_, 1);
lean_inc_ref(v_bvExprCache_2756_);
lean_dec(v___x_2755_);
v___x_2757_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__12___redArg(v_bvExprCache_2756_, v_e_2720_);
lean_dec_ref(v_bvExprCache_2756_);
if (lean_obj_tag(v___x_2757_) == 0)
{
lean_object* v___x_2758_; 
lean_inc_ref(v_e_2720_);
v___x_2758_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go(v_e_2720_, v_a_2721_, v_a_2722_, v_a_2723_, v_a_2724_, v_a_2725_, v_a_2726_, v_a_2727_, v_a_2728_, v_a_2729_);
if (lean_obj_tag(v___x_2758_) == 0)
{
lean_object* v_a_2759_; 
v_a_2759_ = lean_ctor_get(v___x_2758_, 0);
lean_inc(v_a_2759_);
if (lean_obj_tag(v_a_2759_) == 0)
{
uint8_t v___x_2760_; lean_object* v___x_2761_; 
lean_dec_ref_known(v___x_2758_, 1);
v___x_2760_ = 0;
lean_inc_ref(v_e_2720_);
v___x_2761_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_bitVecAtom(v_e_2720_, v___x_2760_, v_a_2722_, v_a_2723_, v_a_2724_, v_a_2725_, v_a_2726_, v_a_2727_, v_a_2728_, v_a_2729_);
v___y_2732_ = v___x_2761_;
goto v___jp_2731_;
}
else
{
lean_dec_ref_known(v_a_2759_, 1);
v___y_2732_ = v___x_2758_;
goto v___jp_2731_;
}
}
else
{
v___y_2732_ = v___x_2758_;
goto v___jp_2731_;
}
}
else
{
lean_object* v_val_2762_; lean_object* v___x_2764_; uint8_t v_isShared_2765_; uint8_t v_isSharedCheck_2769_; 
lean_dec_ref(v_e_2720_);
v_val_2762_ = lean_ctor_get(v___x_2757_, 0);
v_isSharedCheck_2769_ = !lean_is_exclusive(v___x_2757_);
if (v_isSharedCheck_2769_ == 0)
{
v___x_2764_ = v___x_2757_;
v_isShared_2765_ = v_isSharedCheck_2769_;
goto v_resetjp_2763_;
}
else
{
lean_inc(v_val_2762_);
lean_dec(v___x_2757_);
v___x_2764_ = lean_box(0);
v_isShared_2765_ = v_isSharedCheck_2769_;
goto v_resetjp_2763_;
}
v_resetjp_2763_:
{
lean_object* v___x_2767_; 
if (v_isShared_2765_ == 0)
{
lean_ctor_set_tag(v___x_2764_, 0);
v___x_2767_ = v___x_2764_;
goto v_reusejp_2766_;
}
else
{
lean_object* v_reuseFailAlloc_2768_; 
v_reuseFailAlloc_2768_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2768_, 0, v_val_2762_);
v___x_2767_ = v_reuseFailAlloc_2768_;
goto v_reusejp_2766_;
}
v_reusejp_2766_:
{
return v___x_2767_;
}
}
}
v___jp_2731_:
{
if (lean_obj_tag(v___y_2732_) == 0)
{
lean_object* v_a_2733_; lean_object* v___x_2735_; uint8_t v_isShared_2736_; uint8_t v_isSharedCheck_2754_; 
v_a_2733_ = lean_ctor_get(v___y_2732_, 0);
v_isSharedCheck_2754_ = !lean_is_exclusive(v___y_2732_);
if (v_isSharedCheck_2754_ == 0)
{
v___x_2735_ = v___y_2732_;
v_isShared_2736_ = v_isSharedCheck_2754_;
goto v_resetjp_2734_;
}
else
{
lean_inc(v_a_2733_);
lean_dec(v___y_2732_);
v___x_2735_ = lean_box(0);
v_isShared_2736_ = v_isSharedCheck_2754_;
goto v_resetjp_2734_;
}
v_resetjp_2734_:
{
lean_object* v___x_2737_; lean_object* v_lemmas_2738_; lean_object* v_bvExprCache_2739_; lean_object* v_bvPredCache_2740_; lean_object* v_bvLogicalCache_2741_; lean_object* v___x_2743_; uint8_t v_isShared_2744_; uint8_t v_isSharedCheck_2753_; 
v___x_2737_ = lean_st_ref_take(v_a_2721_);
v_lemmas_2738_ = lean_ctor_get(v___x_2737_, 0);
v_bvExprCache_2739_ = lean_ctor_get(v___x_2737_, 1);
v_bvPredCache_2740_ = lean_ctor_get(v___x_2737_, 2);
v_bvLogicalCache_2741_ = lean_ctor_get(v___x_2737_, 3);
v_isSharedCheck_2753_ = !lean_is_exclusive(v___x_2737_);
if (v_isSharedCheck_2753_ == 0)
{
v___x_2743_ = v___x_2737_;
v_isShared_2744_ = v_isSharedCheck_2753_;
goto v_resetjp_2742_;
}
else
{
lean_inc(v_bvLogicalCache_2741_);
lean_inc(v_bvPredCache_2740_);
lean_inc(v_bvExprCache_2739_);
lean_inc(v_lemmas_2738_);
lean_dec(v___x_2737_);
v___x_2743_ = lean_box(0);
v_isShared_2744_ = v_isSharedCheck_2753_;
goto v_resetjp_2742_;
}
v_resetjp_2742_:
{
lean_object* v___x_2745_; lean_object* v___x_2747_; 
lean_inc(v_a_2733_);
v___x_2745_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13___redArg(v_bvExprCache_2739_, v_e_2720_, v_a_2733_);
if (v_isShared_2744_ == 0)
{
lean_ctor_set(v___x_2743_, 1, v___x_2745_);
v___x_2747_ = v___x_2743_;
goto v_reusejp_2746_;
}
else
{
lean_object* v_reuseFailAlloc_2752_; 
v_reuseFailAlloc_2752_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2752_, 0, v_lemmas_2738_);
lean_ctor_set(v_reuseFailAlloc_2752_, 1, v___x_2745_);
lean_ctor_set(v_reuseFailAlloc_2752_, 2, v_bvPredCache_2740_);
lean_ctor_set(v_reuseFailAlloc_2752_, 3, v_bvLogicalCache_2741_);
v___x_2747_ = v_reuseFailAlloc_2752_;
goto v_reusejp_2746_;
}
v_reusejp_2746_:
{
lean_object* v___x_2748_; lean_object* v___x_2750_; 
v___x_2748_ = lean_st_ref_put(v_a_2721_, v___x_2747_);
if (v_isShared_2736_ == 0)
{
v___x_2750_ = v___x_2735_;
goto v_reusejp_2749_;
}
else
{
lean_object* v_reuseFailAlloc_2751_; 
v_reuseFailAlloc_2751_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2751_, 0, v_a_2733_);
v___x_2750_ = v_reuseFailAlloc_2751_;
goto v_reusejp_2749_;
}
v_reusejp_2749_:
{
return v___x_2750_;
}
}
}
}
}
else
{
lean_dec_ref(v_e_2720_);
return v___y_2732_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_goOrAtom(lean_object* v_origExpr_2770_, lean_object* v_a_2771_, lean_object* v_a_2772_, lean_object* v_a_2773_, lean_object* v_a_2774_, lean_object* v_a_2775_, lean_object* v_a_2776_, lean_object* v_a_2777_, lean_object* v_a_2778_, lean_object* v_a_2779_){
_start:
{
lean_object* v___x_2781_; 
v___x_2781_ = l_Lean_Meta_Tactic_BVDecide_LemmaM_withBVExprCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_goOrAtom_spec__10(v_origExpr_2770_, v_a_2771_, v_a_2772_, v_a_2773_, v_a_2774_, v_a_2775_, v_a_2776_, v_a_2777_, v_a_2778_, v_a_2779_);
return v___x_2781_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of(lean_object* v_origExpr_2782_, lean_object* v_a_2783_, lean_object* v_a_2784_, lean_object* v_a_2785_, lean_object* v_a_2786_, lean_object* v_a_2787_, lean_object* v_a_2788_, lean_object* v_a_2789_, lean_object* v_a_2790_, lean_object* v_a_2791_){
_start:
{
lean_object* v___x_2793_; 
v___x_2793_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_goOrAtom(v_origExpr_2782_, v_a_2783_, v_a_2784_, v_a_2785_, v_a_2786_, v_a_2787_, v_a_2788_, v_a_2789_, v_a_2790_, v_a_2791_);
return v___x_2793_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of___boxed(lean_object* v_origExpr_2794_, lean_object* v_a_2795_, lean_object* v_a_2796_, lean_object* v_a_2797_, lean_object* v_a_2798_, lean_object* v_a_2799_, lean_object* v_a_2800_, lean_object* v_a_2801_, lean_object* v_a_2802_, lean_object* v_a_2803_, lean_object* v_a_2804_){
_start:
{
lean_object* v_res_2805_; 
v_res_2805_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of(v_origExpr_2794_, v_a_2795_, v_a_2796_, v_a_2797_, v_a_2798_, v_a_2799_, v_a_2800_, v_a_2801_, v_a_2802_, v_a_2803_);
lean_dec(v_a_2803_);
lean_dec_ref(v_a_2802_);
lean_dec(v_a_2801_);
lean_dec_ref(v_a_2800_);
lean_dec(v_a_2799_);
lean_dec_ref(v_a_2798_);
lean_dec(v_a_2797_);
lean_dec_ref(v_a_2796_);
lean_dec(v_a_2795_);
return v_res_2805_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of___boxed(lean_object* v_origExpr_2806_, lean_object* v_a_2807_, lean_object* v_a_2808_, lean_object* v_a_2809_, lean_object* v_a_2810_, lean_object* v_a_2811_, lean_object* v_a_2812_, lean_object* v_a_2813_, lean_object* v_a_2814_, lean_object* v_a_2815_, lean_object* v_a_2816_){
_start:
{
lean_object* v_res_2817_; 
v_res_2817_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of(v_origExpr_2806_, v_a_2807_, v_a_2808_, v_a_2809_, v_a_2810_, v_a_2811_, v_a_2812_, v_a_2813_, v_a_2814_, v_a_2815_);
lean_dec(v_a_2815_);
lean_dec_ref(v_a_2814_);
lean_dec(v_a_2813_);
lean_dec_ref(v_a_2812_);
lean_dec(v_a_2811_);
lean_dec_ref(v_a_2810_);
lean_dec(v_a_2809_);
lean_dec_ref(v_a_2808_);
lean_dec(v_a_2807_);
return v_res_2817_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of___boxed(lean_object* v_origExpr_2818_, lean_object* v_a_2819_, lean_object* v_a_2820_, lean_object* v_a_2821_, lean_object* v_a_2822_, lean_object* v_a_2823_, lean_object* v_a_2824_, lean_object* v_a_2825_, lean_object* v_a_2826_, lean_object* v_a_2827_, lean_object* v_a_2828_){
_start:
{
lean_object* v_res_2829_; 
v_res_2829_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of(v_origExpr_2818_, v_a_2819_, v_a_2820_, v_a_2821_, v_a_2822_, v_a_2823_, v_a_2824_, v_a_2825_, v_a_2826_, v_a_2827_);
lean_dec(v_a_2827_);
lean_dec_ref(v_a_2826_);
lean_dec(v_a_2825_);
lean_dec_ref(v_a_2824_);
lean_dec(v_a_2823_);
lean_dec_ref(v_a_2822_);
lean_dec(v_a_2821_);
lean_dec_ref(v_a_2820_);
lean_dec(v_a_2819_);
return v_res_2829_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_goOrAtom___boxed(lean_object* v_origExpr_2830_, lean_object* v_a_2831_, lean_object* v_a_2832_, lean_object* v_a_2833_, lean_object* v_a_2834_, lean_object* v_a_2835_, lean_object* v_a_2836_, lean_object* v_a_2837_, lean_object* v_a_2838_, lean_object* v_a_2839_, lean_object* v_a_2840_){
_start:
{
lean_object* v_res_2841_; 
v_res_2841_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_goOrAtom(v_origExpr_2830_, v_a_2831_, v_a_2832_, v_a_2833_, v_a_2834_, v_a_2835_, v_a_2836_, v_a_2837_, v_a_2838_, v_a_2839_);
lean_dec(v_a_2839_);
lean_dec_ref(v_a_2838_);
lean_dec(v_a_2837_);
lean_dec_ref(v_a_2836_);
lean_dec(v_a_2835_);
lean_dec_ref(v_a_2834_);
lean_dec(v_a_2833_);
lean_dec_ref(v_a_2832_);
lean_dec(v_a_2831_);
return v_res_2841_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom___boxed(lean_object* v_origExpr_2842_, lean_object* v_a_2843_, lean_object* v_a_2844_, lean_object* v_a_2845_, lean_object* v_a_2846_, lean_object* v_a_2847_, lean_object* v_a_2848_, lean_object* v_a_2849_, lean_object* v_a_2850_, lean_object* v_a_2851_, lean_object* v_a_2852_){
_start:
{
lean_object* v_res_2853_; 
v_res_2853_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom(v_origExpr_2842_, v_a_2843_, v_a_2844_, v_a_2845_, v_a_2846_, v_a_2847_, v_a_2848_, v_a_2849_, v_a_2850_, v_a_2851_);
lean_dec(v_a_2851_);
lean_dec_ref(v_a_2850_);
lean_dec(v_a_2849_);
lean_dec_ref(v_a_2848_);
lean_dec(v_a_2847_);
lean_dec_ref(v_a_2846_);
lean_dec(v_a_2845_);
lean_dec_ref(v_a_2844_);
lean_dec(v_a_2843_);
return v_res_2853_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_rotateReflection___boxed(lean_object* v_distanceExpr_2854_, lean_object* v_innerExpr_2855_, lean_object* v_rotateOp_2856_, lean_object* v_rotateOpName_2857_, lean_object* v_congrThm_2858_, lean_object* v_origExpr_2859_, lean_object* v_a_2860_, lean_object* v_a_2861_, lean_object* v_a_2862_, lean_object* v_a_2863_, lean_object* v_a_2864_, lean_object* v_a_2865_, lean_object* v_a_2866_, lean_object* v_a_2867_, lean_object* v_a_2868_, lean_object* v_a_2869_){
_start:
{
lean_object* v_res_2870_; 
v_res_2870_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_rotateReflection(v_distanceExpr_2854_, v_innerExpr_2855_, v_rotateOp_2856_, v_rotateOpName_2857_, v_congrThm_2858_, v_origExpr_2859_, v_a_2860_, v_a_2861_, v_a_2862_, v_a_2863_, v_a_2864_, v_a_2865_, v_a_2866_, v_a_2867_, v_a_2868_);
lean_dec(v_a_2868_);
lean_dec_ref(v_a_2867_);
lean_dec(v_a_2866_);
lean_dec_ref(v_a_2865_);
lean_dec(v_a_2864_);
lean_dec_ref(v_a_2863_);
lean_dec(v_a_2862_);
lean_dec_ref(v_a_2861_);
lean_dec(v_a_2860_);
return v_res_2870_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goPred___boxed(lean_object* v_origExpr_2871_, lean_object* v_a_2872_, lean_object* v_a_2873_, lean_object* v_a_2874_, lean_object* v_a_2875_, lean_object* v_a_2876_, lean_object* v_a_2877_, lean_object* v_a_2878_, lean_object* v_a_2879_, lean_object* v_a_2880_, lean_object* v_a_2881_){
_start:
{
lean_object* v_res_2882_; 
v_res_2882_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goPred(v_origExpr_2871_, v_a_2872_, v_a_2873_, v_a_2874_, v_a_2875_, v_a_2876_, v_a_2877_, v_a_2878_, v_a_2879_, v_a_2880_);
lean_dec(v_a_2880_);
lean_dec_ref(v_a_2879_);
lean_dec(v_a_2878_);
lean_dec_ref(v_a_2877_);
lean_dec(v_a_2876_);
lean_dec_ref(v_a_2875_);
lean_dec(v_a_2874_);
lean_dec_ref(v_a_2873_);
lean_dec(v_a_2872_);
return v_res_2882_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_binaryReflection___boxed(lean_object* v_lhsExpr_2883_, lean_object* v_rhsExpr_2884_, lean_object* v_pred_2885_, lean_object* v_origExpr_2886_, lean_object* v_a_2887_, lean_object* v_a_2888_, lean_object* v_a_2889_, lean_object* v_a_2890_, lean_object* v_a_2891_, lean_object* v_a_2892_, lean_object* v_a_2893_, lean_object* v_a_2894_, lean_object* v_a_2895_, lean_object* v_a_2896_){
_start:
{
uint8_t v_pred_boxed_2897_; lean_object* v_res_2898_; 
v_pred_boxed_2897_ = lean_unbox(v_pred_2885_);
v_res_2898_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_binaryReflection(v_lhsExpr_2883_, v_rhsExpr_2884_, v_pred_boxed_2897_, v_origExpr_2886_, v_a_2887_, v_a_2888_, v_a_2889_, v_a_2890_, v_a_2891_, v_a_2892_, v_a_2893_, v_a_2894_, v_a_2895_);
lean_dec(v_a_2895_);
lean_dec_ref(v_a_2894_);
lean_dec(v_a_2893_);
lean_dec_ref(v_a_2892_);
lean_dec(v_a_2891_);
lean_dec_ref(v_a_2890_);
lean_dec(v_a_2889_);
lean_dec_ref(v_a_2888_);
lean_dec(v_a_2887_);
return v_res_2898_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_gateReflection___boxed(lean_object* v_lhsExpr_2899_, lean_object* v_rhsExpr_2900_, lean_object* v_gate_2901_, lean_object* v_origExpr_2902_, lean_object* v_a_2903_, lean_object* v_a_2904_, lean_object* v_a_2905_, lean_object* v_a_2906_, lean_object* v_a_2907_, lean_object* v_a_2908_, lean_object* v_a_2909_, lean_object* v_a_2910_, lean_object* v_a_2911_, lean_object* v_a_2912_){
_start:
{
uint8_t v_gate_boxed_2913_; lean_object* v_res_2914_; 
v_gate_boxed_2913_ = lean_unbox(v_gate_2901_);
v_res_2914_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_gateReflection(v_lhsExpr_2899_, v_rhsExpr_2900_, v_gate_boxed_2913_, v_origExpr_2902_, v_a_2903_, v_a_2904_, v_a_2905_, v_a_2906_, v_a_2907_, v_a_2908_, v_a_2909_, v_a_2910_, v_a_2911_);
lean_dec(v_a_2911_);
lean_dec_ref(v_a_2910_);
lean_dec(v_a_2909_);
lean_dec_ref(v_a_2908_);
lean_dec(v_a_2907_);
lean_dec_ref(v_a_2906_);
lean_dec(v_a_2905_);
lean_dec_ref(v_a_2904_);
lean_dec(v_a_2903_);
return v_res_2914_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2___boxed(lean_object* v_e_2915_, lean_object* v_a_2916_, lean_object* v_a_2917_, lean_object* v_a_2918_, lean_object* v_a_2919_, lean_object* v_a_2920_, lean_object* v_a_2921_, lean_object* v_a_2922_, lean_object* v_a_2923_, lean_object* v_a_2924_, lean_object* v_a_2925_){
_start:
{
lean_object* v_res_2926_; 
v_res_2926_ = l_Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2(v_e_2915_, v_a_2916_, v_a_2917_, v_a_2918_, v_a_2919_, v_a_2920_, v_a_2921_, v_a_2922_, v_a_2923_, v_a_2924_);
lean_dec(v_a_2924_);
lean_dec_ref(v_a_2923_);
lean_dec(v_a_2922_);
lean_dec_ref(v_a_2921_);
lean_dec(v_a_2920_);
lean_dec_ref(v_a_2919_);
lean_dec(v_a_2918_);
lean_dec_ref(v_a_2917_);
lean_dec(v_a_2916_);
return v_res_2926_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_LemmaM_withBVPredCache___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_spec__5___boxed(lean_object* v_e_2927_, lean_object* v_a_2928_, lean_object* v_a_2929_, lean_object* v_a_2930_, lean_object* v_a_2931_, lean_object* v_a_2932_, lean_object* v_a_2933_, lean_object* v_a_2934_, lean_object* v_a_2935_, lean_object* v_a_2936_, lean_object* v_a_2937_){
_start:
{
lean_object* v_res_2938_; 
v_res_2938_ = l_Lean_Meta_Tactic_BVDecide_LemmaM_withBVPredCache___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_spec__5(v_e_2927_, v_a_2928_, v_a_2929_, v_a_2930_, v_a_2931_, v_a_2932_, v_a_2933_, v_a_2934_, v_a_2935_, v_a_2936_);
lean_dec(v_a_2936_);
lean_dec_ref(v_a_2935_);
lean_dec(v_a_2934_);
lean_dec_ref(v_a_2933_);
lean_dec(v_a_2932_);
lean_dec_ref(v_a_2931_);
lean_dec(v_a_2930_);
lean_dec_ref(v_a_2929_);
lean_dec(v_a_2928_);
return v_res_2938_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_LemmaM_withBVExprCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_goOrAtom_spec__10___boxed(lean_object* v_e_2939_, lean_object* v_a_2940_, lean_object* v_a_2941_, lean_object* v_a_2942_, lean_object* v_a_2943_, lean_object* v_a_2944_, lean_object* v_a_2945_, lean_object* v_a_2946_, lean_object* v_a_2947_, lean_object* v_a_2948_, lean_object* v_a_2949_){
_start:
{
lean_object* v_res_2950_; 
v_res_2950_ = l_Lean_Meta_Tactic_BVDecide_LemmaM_withBVExprCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_goOrAtom_spec__10(v_e_2939_, v_a_2940_, v_a_2941_, v_a_2942_, v_a_2943_, v_a_2944_, v_a_2945_, v_a_2946_, v_a_2947_, v_a_2948_);
lean_dec(v_a_2948_);
lean_dec_ref(v_a_2947_);
lean_dec(v_a_2946_);
lean_dec_ref(v_a_2945_);
lean_dec(v_a_2944_);
lean_dec_ref(v_a_2943_);
lean_dec(v_a_2942_);
lean_dec_ref(v_a_2941_);
lean_dec(v_a_2940_);
return v_res_2950_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection___boxed(lean_object* v_distance_2951_, lean_object* v_innerExpr_2952_, lean_object* v_shiftOp_2953_, lean_object* v_shiftOpName_2954_, lean_object* v_congrThm_2955_, lean_object* v_origExpr_2956_, lean_object* v_a_2957_, lean_object* v_a_2958_, lean_object* v_a_2959_, lean_object* v_a_2960_, lean_object* v_a_2961_, lean_object* v_a_2962_, lean_object* v_a_2963_, lean_object* v_a_2964_, lean_object* v_a_2965_, lean_object* v_a_2966_){
_start:
{
lean_object* v_res_2967_; 
v_res_2967_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftConstLikeReflection(v_distance_2951_, v_innerExpr_2952_, v_shiftOp_2953_, v_shiftOpName_2954_, v_congrThm_2955_, v_origExpr_2956_, v_a_2957_, v_a_2958_, v_a_2959_, v_a_2960_, v_a_2961_, v_a_2962_, v_a_2963_, v_a_2964_, v_a_2965_);
lean_dec(v_a_2965_);
lean_dec_ref(v_a_2964_);
lean_dec(v_a_2963_);
lean_dec_ref(v_a_2962_);
lean_dec(v_a_2961_);
lean_dec_ref(v_a_2960_);
lean_dec(v_a_2959_);
lean_dec_ref(v_a_2958_);
lean_dec(v_a_2957_);
return v_res_2967_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftReflection___boxed(lean_object* v_distanceExpr_2968_, lean_object* v_innerExpr_2969_, lean_object* v_shiftOp_2970_, lean_object* v_shiftOpName_2971_, lean_object* v_congrThm_2972_, lean_object* v_origExpr_2973_, lean_object* v_a_2974_, lean_object* v_a_2975_, lean_object* v_a_2976_, lean_object* v_a_2977_, lean_object* v_a_2978_, lean_object* v_a_2979_, lean_object* v_a_2980_, lean_object* v_a_2981_, lean_object* v_a_2982_, lean_object* v_a_2983_){
_start:
{
lean_object* v_res_2984_; 
v_res_2984_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_shiftReflection(v_distanceExpr_2968_, v_innerExpr_2969_, v_shiftOp_2970_, v_shiftOpName_2971_, v_congrThm_2972_, v_origExpr_2973_, v_a_2974_, v_a_2975_, v_a_2976_, v_a_2977_, v_a_2978_, v_a_2979_, v_a_2980_, v_a_2981_, v_a_2982_);
lean_dec(v_a_2982_);
lean_dec_ref(v_a_2981_);
lean_dec(v_a_2980_);
lean_dec_ref(v_a_2979_);
lean_dec(v_a_2978_);
lean_dec_ref(v_a_2977_);
lean_dec(v_a_2976_);
lean_dec_ref(v_a_2975_);
lean_dec(v_a_2974_);
return v_res_2984_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection___boxed(lean_object* v_innerExpr_2985_, lean_object* v_op_2986_, lean_object* v_congrThm_2987_, lean_object* v_origExpr_2988_, lean_object* v_a_2989_, lean_object* v_a_2990_, lean_object* v_a_2991_, lean_object* v_a_2992_, lean_object* v_a_2993_, lean_object* v_a_2994_, lean_object* v_a_2995_, lean_object* v_a_2996_, lean_object* v_a_2997_, lean_object* v_a_2998_){
_start:
{
lean_object* v_res_2999_; 
v_res_2999_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_unaryReflection(v_innerExpr_2985_, v_op_2986_, v_congrThm_2987_, v_origExpr_2988_, v_a_2989_, v_a_2990_, v_a_2991_, v_a_2992_, v_a_2993_, v_a_2994_, v_a_2995_, v_a_2996_, v_a_2997_);
lean_dec(v_a_2997_);
lean_dec_ref(v_a_2996_);
lean_dec(v_a_2995_);
lean_dec_ref(v_a_2994_);
lean_dec(v_a_2993_);
lean_dec_ref(v_a_2992_);
lean_dec(v_a_2991_);
lean_dec_ref(v_a_2990_);
lean_dec(v_a_2989_);
return v_res_2999_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection___boxed(lean_object* v_lhsExpr_3000_, lean_object* v_rhsExpr_3001_, lean_object* v_op_3002_, lean_object* v_congrThm_3003_, lean_object* v_origExpr_3004_, lean_object* v_a_3005_, lean_object* v_a_3006_, lean_object* v_a_3007_, lean_object* v_a_3008_, lean_object* v_a_3009_, lean_object* v_a_3010_, lean_object* v_a_3011_, lean_object* v_a_3012_, lean_object* v_a_3013_, lean_object* v_a_3014_){
_start:
{
uint8_t v_op_boxed_3015_; lean_object* v_res_3016_; 
v_op_boxed_3015_ = lean_unbox(v_op_3002_);
v_res_3016_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_binaryReflection(v_lhsExpr_3000_, v_rhsExpr_3001_, v_op_boxed_3015_, v_congrThm_3003_, v_origExpr_3004_, v_a_3005_, v_a_3006_, v_a_3007_, v_a_3008_, v_a_3009_, v_a_3010_, v_a_3011_, v_a_3012_, v_a_3013_);
lean_dec(v_a_3013_);
lean_dec_ref(v_a_3012_);
lean_dec(v_a_3011_);
lean_dec_ref(v_a_3010_);
lean_dec(v_a_3009_);
lean_dec_ref(v_a_3008_);
lean_dec(v_a_3007_);
lean_dec_ref(v_a_3006_);
lean_dec(v_a_3005_);
return v_res_3016_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go___boxed(lean_object* v_origExpr_3017_, lean_object* v_a_3018_, lean_object* v_a_3019_, lean_object* v_a_3020_, lean_object* v_a_3021_, lean_object* v_a_3022_, lean_object* v_a_3023_, lean_object* v_a_3024_, lean_object* v_a_3025_, lean_object* v_a_3026_, lean_object* v_a_3027_){
_start:
{
lean_object* v_res_3028_; 
v_res_3028_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_of_go(v_origExpr_3017_, v_a_3018_, v_a_3019_, v_a_3020_, v_a_3021_, v_a_3022_, v_a_3023_, v_a_3024_, v_a_3025_, v_a_3026_);
lean_dec(v_a_3026_);
lean_dec_ref(v_a_3025_);
lean_dec(v_a_3024_);
lean_dec_ref(v_a_3023_);
lean_dec(v_a_3022_);
lean_dec_ref(v_a_3021_);
lean_dec(v_a_3020_);
lean_dec_ref(v_a_3019_);
lean_dec(v_a_3018_);
return v_res_3028_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go___boxed(lean_object* v_origExpr_3029_, lean_object* v_a_3030_, lean_object* v_a_3031_, lean_object* v_a_3032_, lean_object* v_a_3033_, lean_object* v_a_3034_, lean_object* v_a_3035_, lean_object* v_a_3036_, lean_object* v_a_3037_, lean_object* v_a_3038_, lean_object* v_a_3039_){
_start:
{
lean_object* v_res_3040_; 
v_res_3040_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_go(v_origExpr_3029_, v_a_3030_, v_a_3031_, v_a_3032_, v_a_3033_, v_a_3034_, v_a_3035_, v_a_3036_, v_a_3037_, v_a_3038_);
lean_dec(v_a_3038_);
lean_dec_ref(v_a_3037_);
lean_dec(v_a_3036_);
lean_dec_ref(v_a_3035_);
lean_dec(v_a_3034_);
lean_dec_ref(v_a_3033_);
lean_dec(v_a_3032_);
lean_dec_ref(v_a_3031_);
lean_dec(v_a_3030_);
return v_res_3040_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go___boxed(lean_object* v_origExpr_3041_, lean_object* v_a_3042_, lean_object* v_a_3043_, lean_object* v_a_3044_, lean_object* v_a_3045_, lean_object* v_a_3046_, lean_object* v_a_3047_, lean_object* v_a_3048_, lean_object* v_a_3049_, lean_object* v_a_3050_, lean_object* v_a_3051_){
_start:
{
lean_object* v_res_3052_; 
v_res_3052_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go(v_origExpr_3041_, v_a_3042_, v_a_3043_, v_a_3044_, v_a_3045_, v_a_3046_, v_a_3047_, v_a_3048_, v_a_3049_, v_a_3050_);
lean_dec(v_a_3050_);
lean_dec_ref(v_a_3049_);
lean_dec(v_a_3048_);
lean_dec_ref(v_a_3047_);
lean_dec(v_a_3046_);
lean_dec_ref(v_a_3045_);
lean_dec(v_a_3044_);
lean_dec_ref(v_a_3043_);
lean_dec(v_a_3042_);
return v_res_3052_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go_spec__12(lean_object* v_00_u03b1_3053_, lean_object* v_msg_3054_, lean_object* v___y_3055_, lean_object* v___y_3056_, lean_object* v___y_3057_, lean_object* v___y_3058_, lean_object* v___y_3059_, lean_object* v___y_3060_, lean_object* v___y_3061_, lean_object* v___y_3062_, lean_object* v___y_3063_){
_start:
{
lean_object* v___x_3065_; 
v___x_3065_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go_spec__12___redArg(v_msg_3054_, v___y_3060_, v___y_3061_, v___y_3062_, v___y_3063_);
return v___x_3065_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go_spec__12___boxed(lean_object* v_00_u03b1_3066_, lean_object* v_msg_3067_, lean_object* v___y_3068_, lean_object* v___y_3069_, lean_object* v___y_3070_, lean_object* v___y_3071_, lean_object* v___y_3072_, lean_object* v___y_3073_, lean_object* v___y_3074_, lean_object* v___y_3075_, lean_object* v___y_3076_, lean_object* v___y_3077_){
_start:
{
lean_object* v_res_3078_; 
v_res_3078_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_of_go_spec__12(v_00_u03b1_3066_, v_msg_3067_, v___y_3068_, v___y_3069_, v___y_3070_, v___y_3071_, v___y_3072_, v___y_3073_, v___y_3074_, v___y_3075_, v___y_3076_);
lean_dec(v___y_3076_);
lean_dec_ref(v___y_3075_);
lean_dec(v___y_3074_);
lean_dec_ref(v___y_3073_);
lean_dec(v___y_3072_);
lean_dec_ref(v___y_3071_);
lean_dec(v___y_3070_);
lean_dec_ref(v___y_3069_);
lean_dec(v___y_3068_);
return v_res_3078_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__12(lean_object* v_00_u03b2_3079_, lean_object* v_m_3080_, lean_object* v_a_3081_){
_start:
{
lean_object* v___x_3082_; 
v___x_3082_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__12___redArg(v_m_3080_, v_a_3081_);
return v___x_3082_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__12___boxed(lean_object* v_00_u03b2_3083_, lean_object* v_m_3084_, lean_object* v_a_3085_){
_start:
{
lean_object* v_res_3086_; 
v_res_3086_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__12(v_00_u03b2_3083_, v_m_3084_, v_a_3085_);
lean_dec_ref(v_a_3085_);
lean_dec_ref(v_m_3084_);
return v_res_3086_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13(lean_object* v_00_u03b2_3087_, lean_object* v_m_3088_, lean_object* v_a_3089_, lean_object* v_b_3090_){
_start:
{
lean_object* v___x_3091_; 
v___x_3091_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13___redArg(v_m_3088_, v_a_3089_, v_b_3090_);
return v___x_3091_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__12_spec__17(lean_object* v_00_u03b2_3092_, lean_object* v_a_3093_, lean_object* v_x_3094_){
_start:
{
lean_object* v___x_3095_; 
v___x_3095_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__12_spec__17___redArg(v_a_3093_, v_x_3094_);
return v___x_3095_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__12_spec__17___boxed(lean_object* v_00_u03b2_3096_, lean_object* v_a_3097_, lean_object* v_x_3098_){
_start:
{
lean_object* v_res_3099_; 
v_res_3099_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__12_spec__17(v_00_u03b2_3096_, v_a_3097_, v_x_3098_);
lean_dec(v_x_3098_);
lean_dec_ref(v_a_3097_);
return v_res_3099_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13_spec__19(lean_object* v_00_u03b2_3100_, lean_object* v_a_3101_, lean_object* v_x_3102_){
_start:
{
uint8_t v___x_3103_; 
v___x_3103_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13_spec__19___redArg(v_a_3101_, v_x_3102_);
return v___x_3103_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13_spec__19___boxed(lean_object* v_00_u03b2_3104_, lean_object* v_a_3105_, lean_object* v_x_3106_){
_start:
{
uint8_t v_res_3107_; lean_object* v_r_3108_; 
v_res_3107_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13_spec__19(v_00_u03b2_3104_, v_a_3105_, v_x_3106_);
lean_dec(v_x_3106_);
lean_dec_ref(v_a_3105_);
v_r_3108_ = lean_box(v_res_3107_);
return v_r_3108_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13_spec__20(lean_object* v_00_u03b2_3109_, lean_object* v_data_3110_){
_start:
{
lean_object* v___x_3111_; 
v___x_3111_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13_spec__20___redArg(v_data_3110_);
return v___x_3111_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13_spec__21(lean_object* v_00_u03b2_3112_, lean_object* v_a_3113_, lean_object* v_b_3114_, lean_object* v_x_3115_){
_start:
{
lean_object* v___x_3116_; 
v___x_3116_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13_spec__21___redArg(v_a_3113_, v_b_3114_, v_x_3115_);
return v___x_3116_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13_spec__20_spec__25(lean_object* v_00_u03b2_3117_, lean_object* v_i_3118_, lean_object* v_source_3119_, lean_object* v_target_3120_){
_start:
{
lean_object* v___x_3121_; 
v___x_3121_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13_spec__20_spec__25___redArg(v_i_3118_, v_source_3119_, v_target_3120_);
return v___x_3121_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13_spec__20_spec__25_spec__26(lean_object* v_00_u03b2_3122_, lean_object* v_x_3123_, lean_object* v_x_3124_){
_start:
{
lean_object* v___x_3125_; 
v___x_3125_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Reify_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13_spec__20_spec__25_spec__26___redArg(v_x_3123_, v_x_3124_);
return v___x_3125_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Reflect_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVExpr(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_LitValues(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_AppBuilder(uint8_t builtin);
lean_object* runtime_initialize_Std_Tactic_BVDecide_Reflect(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Reflect_Reify(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Reflect_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVExpr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_LitValues(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_AppBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Tactic_BVDecide_Reflect(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_BVDecide_Reflect_Reify(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_BVDecide_Reflect_Basic(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVExpr(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_LitValues(uint8_t builtin);
lean_object* initialize_Lean_Meta_AppBuilder(uint8_t builtin);
lean_object* initialize_Std_Tactic_BVDecide_Reflect(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_BVDecide_Reflect_Reify(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_BVDecide_Reflect_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVExpr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_LitValues(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_AppBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Tactic_BVDecide_Reflect(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Reflect_Reify(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_BVDecide_Reflect_Reify(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_BVDecide_Reflect_Reify(builtin);
}
#ifdef __cplusplus
}
#endif
