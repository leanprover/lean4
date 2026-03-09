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
lean_object* l_Lean_Meta_getBitVecValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkBVConst___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_bitVecAtom(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_goBvLit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_goBvLit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkBVRefl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_M_simplifyBinaryProof_x27___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryCongrProof_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkEvalExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_evalsAtAtoms(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryCongrProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryCongrProof___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkNatLit(lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryCongrProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryCongrProof___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom_spec__2_spec__12_spec__17___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom_spec__2_spec__12_spec__17___redArg___boxed(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom_spec__2_spec__12___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom_spec__2_spec__12___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13_spec__19___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13_spec__19___redArg___boxed(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13_spec__20_spec__25_spec__26___redArg(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13_spec__20_spec__25___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13_spec__20___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13_spec__21___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go_spec__12_spec__20(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go_spec__12_spec__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go_spec__12___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_M_simplifyBinaryProof_x27___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Reflect"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___lam__0___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "append_congr"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___lam__0___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___lam__0___closed__1_value;
lean_object* l_Lean_Name_mkStr6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkApp8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_mkApp5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___lam__3___boxed(lean_object**);
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_of_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "BitVec"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_of_go___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_of_go___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "cpop"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__19 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__19_value;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
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
lean_object* l_Lean_Name_mkStr1(lean_object*);
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
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_goOrAtom(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_BVExpr_bin___override(lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
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
lean_object* l_Std_Tactic_BVDecide_BVExpr_shiftLeft___override(lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftReflection(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__62_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 60, .m_capacity = 60, .m_length = 59, .m_data = "internal error: constant shift should have been eliminated."};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__62 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__62_value;
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_once_cell_t l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__63_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__63;
lean_object* l_Std_Tactic_BVDecide_BVExpr_shiftRight___override(lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Std_Tactic_BVDecide_BVExpr_arithShiftRight___override(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_mkBinPred___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_of_binaryReflection(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getNatValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_mkGetLsbD___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_of_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_boolAtom(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVPredCache___at___00Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_of_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_of(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_ofPred___redArg(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_mkGate___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_gateReflection(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_mkIte___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_mkNot___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_mkBoolConst___redArg(uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_boolAtom(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Std_Tactic_BVDecide_BVExpr_un___override(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_getNatOrBvValue_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_BVExpr_append___override___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqRefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_BVExpr_extract___override(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_BVExpr_replicate___override___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVExprCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_goOrAtom_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_goBvLit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc_ref(x_1);
x_8 = l_Lean_Meta_getBitVecValue_x3f(x_1, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec_ref(x_8);
if (lean_obj_tag(x_9) == 1)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_36; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_10 = lean_ctor_get(x_9, 0);
x_36 = !lean_is_exclusive(x_9);
if (x_36 == 0)
{
x_11 = x_9;
x_12 = x_36;
goto block_35;
}
else
{
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_box(0);
x_12 = x_36;
goto block_35;
}
block_35:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_10, 1);
lean_inc(x_14);
lean_dec(x_10);
x_15 = l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkBVConst___redArg(x_13, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_26; 
x_16 = lean_ctor_get(x_15, 0);
x_26 = !lean_is_exclusive(x_15);
if (x_26 == 0)
{
x_17 = x_15;
x_18 = x_26;
goto block_25;
}
else
{
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_box(0);
x_18 = x_26;
goto block_25;
}
block_25:
{
lean_object* x_19; 
if (x_12 == 0)
{
lean_ctor_set(x_11, 0, x_16);
x_19 = x_11;
goto block_23;
}
else
{
lean_object* x_24; 
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_16);
x_19 = x_24;
goto block_23;
}
block_23:
{
lean_object* x_20; 
if (x_18 == 0)
{
lean_ctor_set(x_17, 0, x_19);
x_20 = x_17;
goto block_21;
}
else
{
lean_object* x_22; 
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_19);
x_20 = x_22;
goto block_21;
}
block_21:
{
return x_20;
}
}
}
}
else
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; uint8_t x_34; 
lean_del_object(x_11);
x_27 = lean_ctor_get(x_15, 0);
x_34 = !lean_is_exclusive(x_15);
if (x_34 == 0)
{
x_28 = x_15;
x_29 = x_34;
goto block_33;
}
else
{
lean_inc(x_27);
lean_dec(x_15);
x_28 = lean_box(0);
x_29 = x_34;
goto block_33;
}
block_33:
{
lean_object* x_30; 
if (x_29 == 0)
{
x_30 = x_28;
goto block_31;
}
else
{
lean_object* x_32; 
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_27);
x_30 = x_32;
goto block_31;
}
block_31:
{
return x_30;
}
}
}
}
}
else
{
uint8_t x_37; lean_object* x_38; 
lean_dec(x_9);
x_37 = 0;
x_38 = l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_bitVecAtom(x_1, x_37, x_2, x_3, x_4, x_5, x_6);
return x_38;
}
}
else
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; uint8_t x_46; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_39 = lean_ctor_get(x_8, 0);
x_46 = !lean_is_exclusive(x_8);
if (x_46 == 0)
{
x_40 = x_8;
x_41 = x_46;
goto block_45;
}
else
{
lean_inc(x_39);
lean_dec(x_8);
x_40 = lean_box(0);
x_41 = x_46;
goto block_45;
}
block_45:
{
lean_object* x_42; 
if (x_41 == 0)
{
x_42 = x_40;
goto block_43;
}
else
{
lean_object* x_44; 
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_39);
x_42 = x_44;
goto block_43;
}
block_43:
{
return x_42;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_goBvLit___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_goBvLit(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_M_simplifyBinaryProof_x27___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryCongrProof_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec_ref(x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; 
lean_dec_ref(x_2);
lean_dec(x_1);
x_6 = lean_box(0);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; uint8_t x_16; 
x_7 = lean_ctor_get(x_5, 0);
x_16 = !lean_is_exclusive(x_5);
if (x_16 == 0)
{
x_8 = x_5;
x_9 = x_16;
goto block_15;
}
else
{
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_box(0);
x_9 = x_16;
goto block_15;
}
block_15:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkBVRefl(x_1, x_2);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_7);
if (x_9 == 0)
{
lean_ctor_set(x_8, 0, x_11);
x_12 = x_8;
goto block_13;
}
else
{
lean_object* x_14; 
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_11);
x_12 = x_14;
goto block_13;
}
block_13:
{
return x_12;
}
}
}
}
else
{
lean_dec_ref(x_2);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_26; 
x_17 = lean_ctor_get(x_3, 0);
x_26 = !lean_is_exclusive(x_3);
if (x_26 == 0)
{
x_18 = x_3;
x_19 = x_26;
goto block_25;
}
else
{
lean_inc(x_17);
lean_dec(x_3);
x_18 = lean_box(0);
x_19 = x_26;
goto block_25;
}
block_25:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkBVRefl(x_1, x_4);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_17);
lean_ctor_set(x_21, 1, x_20);
if (x_19 == 0)
{
lean_ctor_set(x_18, 0, x_21);
x_22 = x_18;
goto block_23;
}
else
{
lean_object* x_24; 
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_21);
x_22 = x_24;
goto block_23;
}
block_23:
{
return x_22;
}
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; uint8_t x_36; 
lean_dec_ref(x_4);
lean_dec(x_1);
x_27 = lean_ctor_get(x_3, 0);
lean_inc(x_27);
lean_dec_ref(x_3);
x_28 = lean_ctor_get(x_5, 0);
x_36 = !lean_is_exclusive(x_5);
if (x_36 == 0)
{
x_29 = x_5;
x_30 = x_36;
goto block_35;
}
else
{
lean_inc(x_28);
lean_dec(x_5);
x_29 = lean_box(0);
x_30 = x_36;
goto block_35;
}
block_35:
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_27);
lean_ctor_set(x_31, 1, x_28);
if (x_30 == 0)
{
lean_ctor_set(x_29, 0, x_31);
x_32 = x_29;
goto block_33;
}
else
{
lean_object* x_34; 
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_31);
x_32 = x_34;
goto block_33;
}
block_33:
{
return x_32;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryCongrProof(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 4);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc_ref(x_13);
lean_inc(x_12);
x_14 = l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkEvalExpr(x_12, x_13, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec_ref(x_14);
x_16 = lean_ctor_get(x_2, 0);
x_17 = lean_ctor_get(x_2, 4);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc_ref(x_17);
lean_inc(x_16);
x_18 = l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkEvalExpr(x_16, x_17, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec_ref(x_18);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
x_20 = l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_evalsAtAtoms(x_1, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec_ref(x_20);
x_22 = l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_evalsAtAtoms(x_2, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; uint8_t x_46; 
x_23 = lean_ctor_get(x_22, 0);
x_46 = !lean_is_exclusive(x_22);
if (x_46 == 0)
{
x_24 = x_22;
x_25 = x_46;
goto block_45;
}
else
{
lean_inc(x_23);
lean_dec(x_22);
x_24 = lean_box(0);
x_25 = x_46;
goto block_45;
}
block_45:
{
lean_object* x_26; 
lean_inc(x_19);
lean_inc(x_15);
x_26 = l_Lean_Elab_Tactic_BVDecide_Frontend_M_simplifyBinaryProof_x27___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryCongrProof_spec__0(x_12, x_15, x_21, x_19, x_23);
if (lean_obj_tag(x_26) == 1)
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; uint8_t x_40; 
x_27 = lean_ctor_get(x_26, 0);
x_40 = !lean_is_exclusive(x_26);
if (x_40 == 0)
{
x_28 = x_26;
x_29 = x_40;
goto block_39;
}
else
{
lean_inc(x_27);
lean_dec(x_26);
x_28 = lean_box(0);
x_29 = x_40;
goto block_39;
}
block_39:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_27, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_27, 1);
lean_inc(x_31);
lean_dec(x_27);
x_32 = l_Lean_mkApp6(x_5, x_3, x_4, x_15, x_19, x_30, x_31);
if (x_29 == 0)
{
lean_ctor_set(x_28, 0, x_32);
x_33 = x_28;
goto block_37;
}
else
{
lean_object* x_38; 
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_32);
x_33 = x_38;
goto block_37;
}
block_37:
{
lean_object* x_34; 
if (x_25 == 0)
{
lean_ctor_set(x_24, 0, x_33);
x_34 = x_24;
goto block_35;
}
else
{
lean_object* x_36; 
x_36 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_36, 0, x_33);
x_34 = x_36;
goto block_35;
}
block_35:
{
return x_34;
}
}
}
}
else
{
lean_object* x_41; lean_object* x_42; 
lean_dec(x_26);
lean_dec(x_19);
lean_dec(x_15);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_41 = lean_box(0);
if (x_25 == 0)
{
lean_ctor_set(x_24, 0, x_41);
x_42 = x_24;
goto block_43;
}
else
{
lean_object* x_44; 
x_44 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_44, 0, x_41);
x_42 = x_44;
goto block_43;
}
block_43:
{
return x_42;
}
}
}
}
else
{
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_15);
lean_dec(x_12);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_22;
}
}
else
{
lean_dec(x_19);
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_20;
}
}
else
{
lean_object* x_47; lean_object* x_48; uint8_t x_49; uint8_t x_54; 
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_47 = lean_ctor_get(x_18, 0);
x_54 = !lean_is_exclusive(x_18);
if (x_54 == 0)
{
x_48 = x_18;
x_49 = x_54;
goto block_53;
}
else
{
lean_inc(x_47);
lean_dec(x_18);
x_48 = lean_box(0);
x_49 = x_54;
goto block_53;
}
block_53:
{
lean_object* x_50; 
if (x_49 == 0)
{
x_50 = x_48;
goto block_51;
}
else
{
lean_object* x_52; 
x_52 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_52, 0, x_47);
x_50 = x_52;
goto block_51;
}
block_51:
{
return x_50;
}
}
}
}
else
{
lean_object* x_55; lean_object* x_56; uint8_t x_57; uint8_t x_62; 
lean_dec(x_12);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_55 = lean_ctor_get(x_14, 0);
x_62 = !lean_is_exclusive(x_14);
if (x_62 == 0)
{
x_56 = x_14;
x_57 = x_62;
goto block_61;
}
else
{
lean_inc(x_55);
lean_dec(x_14);
x_56 = lean_box(0);
x_57 = x_62;
goto block_61;
}
block_61:
{
lean_object* x_58; 
if (x_57 == 0)
{
x_58 = x_56;
goto block_59;
}
else
{
lean_object* x_60; 
x_60 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_60, 0, x_55);
x_58 = x_60;
goto block_59;
}
block_59:
{
return x_58;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryCongrProof___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryCongrProof(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryCongrProof(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 4);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_11);
lean_inc(x_10);
x_12 = l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkEvalExpr(x_10, x_11, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec_ref(x_12);
x_14 = l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_evalsAtAtoms(x_1, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_36; 
x_15 = lean_ctor_get(x_14, 0);
x_36 = !lean_is_exclusive(x_14);
if (x_36 == 0)
{
x_16 = x_14;
x_17 = x_36;
goto block_35;
}
else
{
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_box(0);
x_17 = x_36;
goto block_35;
}
block_35:
{
if (lean_obj_tag(x_15) == 1)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_30; 
x_18 = lean_ctor_get(x_15, 0);
x_30 = !lean_is_exclusive(x_15);
if (x_30 == 0)
{
x_19 = x_15;
x_20 = x_30;
goto block_29;
}
else
{
lean_inc(x_18);
lean_dec(x_15);
x_19 = lean_box(0);
x_20 = x_30;
goto block_29;
}
block_29:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = l_Lean_mkNatLit(x_10);
x_22 = l_Lean_mkApp4(x_3, x_21, x_2, x_13, x_18);
if (x_20 == 0)
{
lean_ctor_set(x_19, 0, x_22);
x_23 = x_19;
goto block_27;
}
else
{
lean_object* x_28; 
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_22);
x_23 = x_28;
goto block_27;
}
block_27:
{
lean_object* x_24; 
if (x_17 == 0)
{
lean_ctor_set(x_16, 0, x_23);
x_24 = x_16;
goto block_25;
}
else
{
lean_object* x_26; 
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_23);
x_24 = x_26;
goto block_25;
}
block_25:
{
return x_24;
}
}
}
}
else
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_10);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_31 = lean_box(0);
if (x_17 == 0)
{
lean_ctor_set(x_16, 0, x_31);
x_32 = x_16;
goto block_33;
}
else
{
lean_object* x_34; 
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_31);
x_32 = x_34;
goto block_33;
}
block_33:
{
return x_32;
}
}
}
}
else
{
lean_dec(x_13);
lean_dec(x_10);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_14;
}
}
else
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; uint8_t x_44; 
lean_dec(x_10);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_37 = lean_ctor_get(x_12, 0);
x_44 = !lean_is_exclusive(x_12);
if (x_44 == 0)
{
x_38 = x_12;
x_39 = x_44;
goto block_43;
}
else
{
lean_inc(x_37);
lean_dec(x_12);
x_38 = lean_box(0);
x_39 = x_44;
goto block_43;
}
block_43:
{
lean_object* x_40; 
if (x_39 == 0)
{
x_40 = x_38;
goto block_41;
}
else
{
lean_object* x_42; 
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_37);
x_40 = x_42;
goto block_41;
}
block_41:
{
return x_40;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryCongrProof___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryCongrProof(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom_spec__2_spec__12_spec__17___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 2);
x_7 = lean_expr_eqv(x_4, x_1);
if (x_7 == 0)
{
x_2 = x_6;
goto _start;
}
else
{
lean_object* x_9; 
lean_inc(x_5);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_5);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom_spec__2_spec__12_spec__17___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom_spec__2_spec__12_spec__17___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom_spec__2_spec__12___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint64_t x_5; uint64_t x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; size_t x_12; size_t x_13; size_t x_14; size_t x_15; size_t x_16; lean_object* x_17; lean_object* x_18; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
x_5 = l_Lean_Expr_hash(x_2);
x_6 = 32;
x_7 = lean_uint64_shift_right(x_5, x_6);
x_8 = lean_uint64_xor(x_5, x_7);
x_9 = 16;
x_10 = lean_uint64_shift_right(x_8, x_9);
x_11 = lean_uint64_xor(x_8, x_10);
x_12 = lean_uint64_to_usize(x_11);
x_13 = lean_usize_of_nat(x_4);
x_14 = 1;
x_15 = lean_usize_sub(x_13, x_14);
x_16 = lean_usize_land(x_12, x_15);
x_17 = lean_array_uget_borrowed(x_3, x_16);
x_18 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom_spec__2_spec__12_spec__17___redArg(x_2, x_17);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom_spec__2_spec__12___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom_spec__2_spec__12___redArg(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13_spec__19___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_expr_eqv(x_4, x_1);
if (x_6 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
return x_6;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13_spec__19___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13_spec__19___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13_spec__20_spec__25_spec__26___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_28; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_2, 2);
x_28 = !lean_is_exclusive(x_2);
if (x_28 == 0)
{
x_6 = x_2;
x_7 = x_28;
goto block_27;
}
else
{
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_dec(x_2);
x_6 = lean_box(0);
x_7 = x_28;
goto block_27;
}
block_27:
{
lean_object* x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; size_t x_16; size_t x_17; size_t x_18; size_t x_19; size_t x_20; lean_object* x_21; lean_object* x_22; 
x_8 = lean_array_get_size(x_1);
x_9 = l_Lean_Expr_hash(x_3);
x_10 = 32;
x_11 = lean_uint64_shift_right(x_9, x_10);
x_12 = lean_uint64_xor(x_9, x_11);
x_13 = 16;
x_14 = lean_uint64_shift_right(x_12, x_13);
x_15 = lean_uint64_xor(x_12, x_14);
x_16 = lean_uint64_to_usize(x_15);
x_17 = lean_usize_of_nat(x_8);
x_18 = 1;
x_19 = lean_usize_sub(x_17, x_18);
x_20 = lean_usize_land(x_16, x_19);
x_21 = lean_array_uget_borrowed(x_1, x_20);
lean_inc(x_21);
if (x_7 == 0)
{
lean_ctor_set(x_6, 2, x_21);
x_22 = x_6;
goto block_25;
}
else
{
lean_object* x_26; 
x_26 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_26, 0, x_3);
lean_ctor_set(x_26, 1, x_4);
lean_ctor_set(x_26, 2, x_21);
x_22 = x_26;
goto block_25;
}
block_25:
{
lean_object* x_23; 
x_23 = lean_array_uset(x_1, x_20, x_22);
x_1 = x_23;
x_2 = x_5;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13_spec__20_spec__25___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_1, x_4);
if (x_5 == 0)
{
lean_dec_ref(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_array_fget(x_2, x_1);
x_7 = lean_box(0);
x_8 = lean_array_fset(x_2, x_1, x_7);
x_9 = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13_spec__20_spec__25_spec__26___redArg(x_3, x_6);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_1, x_10);
lean_dec(x_1);
x_1 = x_11;
x_2 = x_8;
x_3 = x_9;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13_spec__20___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(2u);
x_4 = lean_nat_mul(x_2, x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_box(0);
x_7 = lean_mk_array(x_4, x_6);
x_8 = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13_spec__20_spec__25___redArg(x_5, x_1, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13_spec__21___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_18; 
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_3, 1);
x_6 = lean_ctor_get(x_3, 2);
x_18 = !lean_is_exclusive(x_3);
if (x_18 == 0)
{
x_7 = x_3;
x_8 = x_18;
goto block_17;
}
else
{
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_dec(x_3);
x_7 = lean_box(0);
x_8 = x_18;
goto block_17;
}
block_17:
{
uint8_t x_9; 
x_9 = lean_expr_eqv(x_4, x_1);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13_spec__21___redArg(x_1, x_2, x_6);
if (x_8 == 0)
{
lean_ctor_set(x_7, 2, x_10);
x_11 = x_7;
goto block_12;
}
else
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_13, 0, x_4);
lean_ctor_set(x_13, 1, x_5);
lean_ctor_set(x_13, 2, x_10);
x_11 = x_13;
goto block_12;
}
block_12:
{
return x_11;
}
}
else
{
lean_object* x_14; 
lean_dec(x_5);
lean_dec(x_4);
if (x_8 == 0)
{
lean_ctor_set(x_7, 1, x_2);
lean_ctor_set(x_7, 0, x_1);
x_14 = x_7;
goto block_15;
}
else
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_2);
lean_ctor_set(x_16, 2, x_6);
x_14 = x_16;
goto block_15;
}
block_15:
{
return x_14;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_48; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_48 = !lean_is_exclusive(x_1);
if (x_48 == 0)
{
x_6 = x_1;
x_7 = x_48;
goto block_47;
}
else
{
lean_inc(x_5);
lean_inc(x_4);
lean_dec(x_1);
x_6 = lean_box(0);
x_7 = x_48;
goto block_47;
}
block_47:
{
lean_object* x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; size_t x_16; size_t x_17; size_t x_18; size_t x_19; size_t x_20; lean_object* x_21; uint8_t x_22; 
x_8 = lean_array_get_size(x_5);
x_9 = l_Lean_Expr_hash(x_2);
x_10 = 32;
x_11 = lean_uint64_shift_right(x_9, x_10);
x_12 = lean_uint64_xor(x_9, x_11);
x_13 = 16;
x_14 = lean_uint64_shift_right(x_12, x_13);
x_15 = lean_uint64_xor(x_12, x_14);
x_16 = lean_uint64_to_usize(x_15);
x_17 = lean_usize_of_nat(x_8);
x_18 = 1;
x_19 = lean_usize_sub(x_17, x_18);
x_20 = lean_usize_land(x_16, x_19);
x_21 = lean_array_uget_borrowed(x_5, x_20);
x_22 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13_spec__19___redArg(x_2, x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_add(x_4, x_23);
lean_dec(x_4);
lean_inc(x_21);
x_25 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_25, 0, x_2);
lean_ctor_set(x_25, 1, x_3);
lean_ctor_set(x_25, 2, x_21);
x_26 = lean_array_uset(x_5, x_20, x_25);
x_27 = lean_unsigned_to_nat(4u);
x_28 = lean_nat_mul(x_24, x_27);
x_29 = lean_unsigned_to_nat(3u);
x_30 = lean_nat_div(x_28, x_29);
lean_dec(x_28);
x_31 = lean_array_get_size(x_26);
x_32 = lean_nat_dec_le(x_30, x_31);
lean_dec(x_30);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13_spec__20___redArg(x_26);
if (x_7 == 0)
{
lean_ctor_set(x_6, 1, x_33);
lean_ctor_set(x_6, 0, x_24);
x_34 = x_6;
goto block_35;
}
else
{
lean_object* x_36; 
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_24);
lean_ctor_set(x_36, 1, x_33);
x_34 = x_36;
goto block_35;
}
block_35:
{
return x_34;
}
}
else
{
lean_object* x_37; 
if (x_7 == 0)
{
lean_ctor_set(x_6, 1, x_26);
lean_ctor_set(x_6, 0, x_24);
x_37 = x_6;
goto block_38;
}
else
{
lean_object* x_39; 
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_24);
lean_ctor_set(x_39, 1, x_26);
x_37 = x_39;
goto block_38;
}
block_38:
{
return x_37;
}
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_inc(x_21);
x_40 = lean_box(0);
x_41 = lean_array_uset(x_5, x_20, x_40);
x_42 = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13_spec__21___redArg(x_2, x_3, x_21);
x_43 = lean_array_uset(x_41, x_20, x_42);
if (x_7 == 0)
{
lean_ctor_set(x_6, 1, x_43);
x_44 = x_6;
goto block_45;
}
else
{
lean_object* x_46; 
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_4);
lean_ctor_set(x_46, 1, x_43);
x_44 = x_46;
goto block_45;
}
block_45:
{
return x_44;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go_spec__12_spec__20(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_st_ref_get(x_5);
x_8 = lean_ctor_get(x_7, 0);
lean_inc_ref(x_8);
lean_dec(x_7);
x_9 = lean_st_ref_get(x_3);
x_10 = lean_ctor_get(x_9, 0);
lean_inc_ref(x_10);
lean_dec(x_9);
x_11 = lean_ctor_get(x_2, 2);
x_12 = lean_ctor_get(x_4, 2);
lean_inc_ref(x_12);
lean_inc_ref(x_11);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_8);
lean_ctor_set(x_13, 1, x_10);
lean_ctor_set(x_13, 2, x_11);
lean_ctor_set(x_13, 3, x_12);
x_14 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_1);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go_spec__12_spec__20___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go_spec__12_spec__20(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go_spec__12___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_17; 
x_7 = lean_ctor_get(x_4, 5);
x_8 = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go_spec__12_spec__20(x_1, x_2, x_3, x_4, x_5);
x_9 = lean_ctor_get(x_8, 0);
x_17 = !lean_is_exclusive(x_8);
if (x_17 == 0)
{
x_10 = x_8;
x_11 = x_17;
goto block_16;
}
else
{
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_box(0);
x_11 = x_17;
goto block_16;
}
block_16:
{
lean_object* x_12; lean_object* x_13; 
lean_inc(x_7);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_7);
lean_ctor_set(x_12, 1, x_9);
if (x_11 == 0)
{
lean_ctor_set_tag(x_10, 1);
lean_ctor_set(x_10, 0, x_12);
x_13 = x_10;
goto block_14;
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_12);
x_13 = x_15;
goto block_14;
}
block_14:
{
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go_spec__12___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go_spec__12___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_M_simplifyBinaryProof_x27___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go_spec__13(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_dec_ref(x_5);
lean_dec(x_2);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
lean_dec_ref(x_3);
lean_dec(x_1);
x_7 = lean_box(0);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_17; 
x_8 = lean_ctor_get(x_6, 0);
x_17 = !lean_is_exclusive(x_6);
if (x_17 == 0)
{
x_9 = x_6;
x_10 = x_17;
goto block_16;
}
else
{
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_box(0);
x_10 = x_17;
goto block_16;
}
block_16:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkBVRefl(x_1, x_3);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_8);
if (x_10 == 0)
{
lean_ctor_set(x_9, 0, x_12);
x_13 = x_9;
goto block_14;
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_12);
x_13 = x_15;
goto block_14;
}
block_14:
{
return x_13;
}
}
}
}
else
{
lean_dec_ref(x_3);
lean_dec(x_1);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_27; 
x_18 = lean_ctor_get(x_4, 0);
x_27 = !lean_is_exclusive(x_4);
if (x_27 == 0)
{
x_19 = x_4;
x_20 = x_27;
goto block_26;
}
else
{
lean_inc(x_18);
lean_dec(x_4);
x_19 = lean_box(0);
x_20 = x_27;
goto block_26;
}
block_26:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkBVRefl(x_2, x_5);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_18);
lean_ctor_set(x_22, 1, x_21);
if (x_20 == 0)
{
lean_ctor_set(x_19, 0, x_22);
x_23 = x_19;
goto block_24;
}
else
{
lean_object* x_25; 
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_22);
x_23 = x_25;
goto block_24;
}
block_24:
{
return x_23;
}
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; uint8_t x_37; 
lean_dec_ref(x_5);
lean_dec(x_2);
x_28 = lean_ctor_get(x_4, 0);
lean_inc(x_28);
lean_dec_ref(x_4);
x_29 = lean_ctor_get(x_6, 0);
x_37 = !lean_is_exclusive(x_6);
if (x_37 == 0)
{
x_30 = x_6;
x_31 = x_37;
goto block_36;
}
else
{
lean_inc(x_29);
lean_dec(x_6);
x_30 = lean_box(0);
x_31 = x_37;
goto block_36;
}
block_36:
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_28);
lean_ctor_set(x_32, 1, x_29);
if (x_31 == 0)
{
lean_ctor_set(x_30, 0, x_32);
x_33 = x_30;
goto block_34;
}
else
{
lean_object* x_35; 
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_32);
x_33 = x_35;
goto block_34;
}
block_34:
{
return x_33;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20) {
_start:
{
lean_object* x_22; 
lean_inc(x_20);
lean_inc_ref(x_19);
lean_inc(x_18);
lean_inc_ref(x_17);
lean_inc(x_1);
x_22 = l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkEvalExpr(x_1, x_2, x_16, x_17, x_18, x_19, x_20);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec_ref(x_22);
lean_inc(x_20);
lean_inc_ref(x_19);
lean_inc(x_18);
lean_inc_ref(x_17);
lean_inc(x_3);
x_24 = l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkEvalExpr(x_3, x_4, x_16, x_17, x_18, x_19, x_20);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec_ref(x_24);
lean_inc(x_20);
lean_inc_ref(x_19);
lean_inc(x_18);
lean_inc_ref(x_17);
lean_inc(x_16);
x_26 = l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_evalsAtAtoms(x_5, x_16, x_17, x_18, x_19, x_20);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
lean_dec_ref(x_26);
x_28 = l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_evalsAtAtoms(x_6, x_16, x_17, x_18, x_19, x_20);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; uint8_t x_56; 
x_29 = lean_ctor_get(x_28, 0);
x_56 = !lean_is_exclusive(x_28);
if (x_56 == 0)
{
x_30 = x_28;
x_31 = x_56;
goto block_55;
}
else
{
lean_inc(x_29);
lean_dec(x_28);
x_30 = lean_box(0);
x_31 = x_56;
goto block_55;
}
block_55:
{
lean_object* x_32; 
lean_inc(x_25);
lean_inc(x_23);
x_32 = l_Lean_Elab_Tactic_BVDecide_Frontend_M_simplifyBinaryProof_x27___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go_spec__13(x_1, x_3, x_23, x_27, x_25, x_29);
if (lean_obj_tag(x_32) == 1)
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; uint8_t x_50; 
x_33 = lean_ctor_get(x_32, 0);
x_50 = !lean_is_exclusive(x_32);
if (x_50 == 0)
{
x_34 = x_32;
x_35 = x_50;
goto block_49;
}
else
{
lean_inc(x_33);
lean_dec(x_32);
x_34 = lean_box(0);
x_35 = x_50;
goto block_49;
}
block_49:
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_36 = lean_ctor_get(x_33, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_33, 1);
lean_inc(x_37);
lean_dec(x_33);
x_38 = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___lam__0___closed__0));
x_39 = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___lam__0___closed__1));
x_40 = l_Lean_Name_mkStr6(x_7, x_8, x_9, x_38, x_10, x_39);
x_41 = l_Lean_mkConst(x_40, x_11);
x_42 = l_Lean_mkApp8(x_41, x_12, x_13, x_14, x_23, x_15, x_25, x_36, x_37);
if (x_35 == 0)
{
lean_ctor_set(x_34, 0, x_42);
x_43 = x_34;
goto block_47;
}
else
{
lean_object* x_48; 
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_42);
x_43 = x_48;
goto block_47;
}
block_47:
{
lean_object* x_44; 
if (x_31 == 0)
{
lean_ctor_set(x_30, 0, x_43);
x_44 = x_30;
goto block_45;
}
else
{
lean_object* x_46; 
x_46 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_46, 0, x_43);
x_44 = x_46;
goto block_45;
}
block_45:
{
return x_44;
}
}
}
}
else
{
lean_object* x_51; lean_object* x_52; 
lean_dec(x_32);
lean_dec(x_25);
lean_dec(x_23);
lean_dec_ref(x_15);
lean_dec_ref(x_14);
lean_dec_ref(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
x_51 = lean_box(0);
if (x_31 == 0)
{
lean_ctor_set(x_30, 0, x_51);
x_52 = x_30;
goto block_53;
}
else
{
lean_object* x_54; 
x_54 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_54, 0, x_51);
x_52 = x_54;
goto block_53;
}
block_53:
{
return x_52;
}
}
}
}
else
{
lean_dec(x_27);
lean_dec(x_25);
lean_dec(x_23);
lean_dec_ref(x_15);
lean_dec_ref(x_14);
lean_dec_ref(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec(x_3);
lean_dec(x_1);
return x_28;
}
}
else
{
lean_dec(x_25);
lean_dec(x_23);
lean_dec(x_20);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec_ref(x_17);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec_ref(x_14);
lean_dec_ref(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec(x_3);
lean_dec(x_1);
return x_26;
}
}
else
{
lean_object* x_57; lean_object* x_58; uint8_t x_59; uint8_t x_64; 
lean_dec(x_23);
lean_dec(x_20);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec_ref(x_17);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec_ref(x_14);
lean_dec_ref(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_57 = lean_ctor_get(x_24, 0);
x_64 = !lean_is_exclusive(x_24);
if (x_64 == 0)
{
x_58 = x_24;
x_59 = x_64;
goto block_63;
}
else
{
lean_inc(x_57);
lean_dec(x_24);
x_58 = lean_box(0);
x_59 = x_64;
goto block_63;
}
block_63:
{
lean_object* x_60; 
if (x_59 == 0)
{
x_60 = x_58;
goto block_61;
}
else
{
lean_object* x_62; 
x_62 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_62, 0, x_57);
x_60 = x_62;
goto block_61;
}
block_61:
{
return x_60;
}
}
}
}
else
{
lean_object* x_65; lean_object* x_66; uint8_t x_67; uint8_t x_72; 
lean_dec(x_20);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec_ref(x_17);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec_ref(x_14);
lean_dec_ref(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_65 = lean_ctor_get(x_22, 0);
x_72 = !lean_is_exclusive(x_22);
if (x_72 == 0)
{
x_66 = x_22;
x_67 = x_72;
goto block_71;
}
else
{
lean_inc(x_65);
lean_dec(x_22);
x_66 = lean_box(0);
x_67 = x_72;
goto block_71;
}
block_71:
{
lean_object* x_68; 
if (x_67 == 0)
{
x_68 = x_66;
goto block_69;
}
else
{
lean_object* x_70; 
x_70 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_70, 0, x_65);
x_68 = x_70;
goto block_69;
}
block_69:
{
return x_68;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___lam__0___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
lean_object* x_19 = _args[18];
lean_object* x_20 = _args[19];
lean_object* x_21 = _args[20];
_start:
{
lean_object* x_22; 
x_22 = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20);
return x_22;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
lean_object* x_19; 
lean_inc(x_17);
lean_inc_ref(x_16);
lean_inc(x_15);
lean_inc_ref(x_14);
x_19 = l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkEvalExpr(x_1, x_2, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec_ref(x_19);
x_21 = l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_evalsAtAtoms(x_3, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_46; 
x_22 = lean_ctor_get(x_21, 0);
x_46 = !lean_is_exclusive(x_21);
if (x_46 == 0)
{
x_23 = x_21;
x_24 = x_46;
goto block_45;
}
else
{
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_box(0);
x_24 = x_46;
goto block_45;
}
block_45:
{
if (lean_obj_tag(x_22) == 1)
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; uint8_t x_40; 
x_25 = lean_ctor_get(x_22, 0);
x_40 = !lean_is_exclusive(x_22);
if (x_40 == 0)
{
x_26 = x_22;
x_27 = x_40;
goto block_39;
}
else
{
lean_inc(x_25);
lean_dec(x_22);
x_26 = lean_box(0);
x_27 = x_40;
goto block_39;
}
block_39:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_28 = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___lam__0___closed__0));
x_29 = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___lam__1___closed__0));
x_30 = l_Lean_Name_mkStr6(x_4, x_5, x_6, x_28, x_7, x_29);
x_31 = l_Lean_mkConst(x_30, x_8);
x_32 = l_Lean_mkApp6(x_31, x_9, x_10, x_11, x_12, x_20, x_25);
if (x_27 == 0)
{
lean_ctor_set(x_26, 0, x_32);
x_33 = x_26;
goto block_37;
}
else
{
lean_object* x_38; 
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_32);
x_33 = x_38;
goto block_37;
}
block_37:
{
lean_object* x_34; 
if (x_24 == 0)
{
lean_ctor_set(x_23, 0, x_33);
x_34 = x_23;
goto block_35;
}
else
{
lean_object* x_36; 
x_36 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_36, 0, x_33);
x_34 = x_36;
goto block_35;
}
block_35:
{
return x_34;
}
}
}
}
else
{
lean_object* x_41; lean_object* x_42; 
lean_dec(x_22);
lean_dec(x_20);
lean_dec_ref(x_12);
lean_dec_ref(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_41 = lean_box(0);
if (x_24 == 0)
{
lean_ctor_set(x_23, 0, x_41);
x_42 = x_23;
goto block_43;
}
else
{
lean_object* x_44; 
x_44 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_44, 0, x_41);
x_42 = x_44;
goto block_43;
}
block_43:
{
return x_42;
}
}
}
}
else
{
lean_dec(x_20);
lean_dec_ref(x_12);
lean_dec_ref(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
return x_21;
}
}
else
{
lean_object* x_47; lean_object* x_48; uint8_t x_49; uint8_t x_54; 
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec_ref(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_47 = lean_ctor_get(x_19, 0);
x_54 = !lean_is_exclusive(x_19);
if (x_54 == 0)
{
x_48 = x_19;
x_49 = x_54;
goto block_53;
}
else
{
lean_inc(x_47);
lean_dec(x_19);
x_48 = lean_box(0);
x_49 = x_54;
goto block_53;
}
block_53:
{
lean_object* x_50; 
if (x_49 == 0)
{
x_50 = x_48;
goto block_51;
}
else
{
lean_object* x_52; 
x_52 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_52, 0, x_47);
x_50 = x_52;
goto block_51;
}
block_51:
{
return x_50;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___lam__1___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
_start:
{
lean_object* x_19; 
x_19 = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
return x_19;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___lam__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___lam__5(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___lam__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_18; 
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc(x_14);
lean_inc_ref(x_13);
x_18 = l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkEvalExpr(x_1, x_2, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec_ref(x_18);
x_20 = l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_evalsAtAtoms(x_3, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_45; 
x_21 = lean_ctor_get(x_20, 0);
x_45 = !lean_is_exclusive(x_20);
if (x_45 == 0)
{
x_22 = x_20;
x_23 = x_45;
goto block_44;
}
else
{
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_box(0);
x_23 = x_45;
goto block_44;
}
block_44:
{
if (lean_obj_tag(x_21) == 1)
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_39; 
x_24 = lean_ctor_get(x_21, 0);
x_39 = !lean_is_exclusive(x_21);
if (x_39 == 0)
{
x_25 = x_21;
x_26 = x_39;
goto block_38;
}
else
{
lean_inc(x_24);
lean_dec(x_21);
x_25 = lean_box(0);
x_26 = x_39;
goto block_38;
}
block_38:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_27 = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___lam__0___closed__0));
x_28 = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___lam__3___closed__0));
x_29 = l_Lean_Name_mkStr6(x_4, x_5, x_6, x_27, x_7, x_28);
x_30 = l_Lean_mkConst(x_29, x_8);
x_31 = l_Lean_mkApp5(x_30, x_9, x_10, x_11, x_19, x_24);
if (x_26 == 0)
{
lean_ctor_set(x_25, 0, x_31);
x_32 = x_25;
goto block_36;
}
else
{
lean_object* x_37; 
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_31);
x_32 = x_37;
goto block_36;
}
block_36:
{
lean_object* x_33; 
if (x_23 == 0)
{
lean_ctor_set(x_22, 0, x_32);
x_33 = x_22;
goto block_34;
}
else
{
lean_object* x_35; 
x_35 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_35, 0, x_32);
x_33 = x_35;
goto block_34;
}
block_34:
{
return x_33;
}
}
}
}
else
{
lean_object* x_40; lean_object* x_41; 
lean_dec(x_21);
lean_dec(x_19);
lean_dec_ref(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_40 = lean_box(0);
if (x_23 == 0)
{
lean_ctor_set(x_22, 0, x_40);
x_41 = x_22;
goto block_42;
}
else
{
lean_object* x_43; 
x_43 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_43, 0, x_40);
x_41 = x_43;
goto block_42;
}
block_42:
{
return x_41;
}
}
}
}
else
{
lean_dec(x_19);
lean_dec_ref(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
return x_20;
}
}
else
{
lean_object* x_46; lean_object* x_47; uint8_t x_48; uint8_t x_53; 
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_46 = lean_ctor_get(x_18, 0);
x_53 = !lean_is_exclusive(x_18);
if (x_53 == 0)
{
x_47 = x_18;
x_48 = x_53;
goto block_52;
}
else
{
lean_inc(x_46);
lean_dec(x_18);
x_47 = lean_box(0);
x_48 = x_53;
goto block_52;
}
block_52:
{
lean_object* x_49; 
if (x_48 == 0)
{
x_49 = x_47;
goto block_50;
}
else
{
lean_object* x_51; 
x_51 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_51, 0, x_46);
x_49 = x_51;
goto block_50;
}
block_50:
{
return x_49;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___lam__3___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
_start:
{
lean_object* x_18; 
x_18 = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___lam__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
return x_18;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__1));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__6(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__5));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__9(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__8));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__12(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__11));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__15(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__14));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__18(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__17));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__21(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__20));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__24(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__23));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_1);
x_13 = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_goOrAtom(x_1, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_73; 
x_14 = lean_ctor_get(x_13, 0);
x_73 = !lean_is_exclusive(x_13);
if (x_73 == 0)
{
x_15 = x_13;
x_16 = x_73;
goto block_72;
}
else
{
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_box(0);
x_16 = x_73;
goto block_72;
}
block_72:
{
if (lean_obj_tag(x_14) == 1)
{
lean_object* x_17; lean_object* x_18; 
lean_del_object(x_15);
x_17 = lean_ctor_get(x_14, 0);
lean_inc(x_17);
lean_dec_ref(x_14);
lean_inc_ref(x_2);
x_18 = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_goOrAtom(x_2, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_67; 
x_19 = lean_ctor_get(x_18, 0);
x_67 = !lean_is_exclusive(x_18);
if (x_67 == 0)
{
x_20 = x_18;
x_21 = x_67;
goto block_66;
}
else
{
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_box(0);
x_21 = x_67;
goto block_66;
}
block_66:
{
if (lean_obj_tag(x_19) == 1)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_61; 
x_22 = lean_ctor_get(x_19, 0);
x_61 = !lean_is_exclusive(x_19);
if (x_61 == 0)
{
x_23 = x_19;
x_24 = x_61;
goto block_60;
}
else
{
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_box(0);
x_24 = x_61;
goto block_60;
}
block_60:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_25 = lean_ctor_get(x_22, 0);
x_26 = lean_ctor_get(x_22, 1);
x_27 = lean_ctor_get(x_22, 4);
x_28 = lean_ctor_get(x_17, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_17, 1);
x_30 = lean_ctor_get(x_17, 4);
x_31 = lean_nat_dec_eq(x_25, x_28);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_28);
lean_del_object(x_23);
lean_dec(x_22);
lean_dec(x_17);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_32 = lean_box(0);
if (x_21 == 0)
{
lean_ctor_set(x_20, 0, x_32);
x_33 = x_20;
goto block_34;
}
else
{
lean_object* x_35; 
x_35 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_35, 0, x_32);
x_33 = x_35;
goto block_34;
}
block_34:
{
return x_33;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_inc_ref(x_26);
lean_inc_ref(x_29);
lean_inc(x_28);
x_36 = l_Std_Tactic_BVDecide_BVExpr_bin___override(x_28, x_29, x_3, x_26);
x_37 = lean_box(0);
x_38 = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__2, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__2_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__2);
lean_inc(x_28);
x_39 = l_Lean_mkNatLit(x_28);
switch (x_3) {
case 0:
{
lean_object* x_53; 
x_53 = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__6, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__6_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__6);
x_40 = x_53;
goto block_52;
}
case 1:
{
lean_object* x_54; 
x_54 = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__9, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__9_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__9);
x_40 = x_54;
goto block_52;
}
case 2:
{
lean_object* x_55; 
x_55 = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__12, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__12_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__12);
x_40 = x_55;
goto block_52;
}
case 3:
{
lean_object* x_56; 
x_56 = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__15, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__15_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__15);
x_40 = x_56;
goto block_52;
}
case 4:
{
lean_object* x_57; 
x_57 = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__18, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__18_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__18);
x_40 = x_57;
goto block_52;
}
case 5:
{
lean_object* x_58; 
x_58 = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__21, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__21_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__21);
x_40 = x_58;
goto block_52;
}
default: 
{
lean_object* x_59; 
x_59 = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__24, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__24_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___closed__24);
x_40 = x_59;
goto block_52;
}
}
block_52:
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_inc_ref(x_27);
lean_inc_ref(x_30);
lean_inc_ref(x_39);
x_41 = l_Lean_mkApp4(x_38, x_39, x_30, x_40, x_27);
x_42 = l_Lean_mkConst(x_4, x_37);
x_43 = l_Lean_Expr_app___override(x_42, x_39);
x_44 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryCongrProof___boxed), 11, 5);
lean_closure_set(x_44, 0, x_17);
lean_closure_set(x_44, 1, x_22);
lean_closure_set(x_44, 2, x_1);
lean_closure_set(x_44, 3, x_2);
lean_closure_set(x_44, 4, x_43);
x_45 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_45, 0, x_28);
lean_ctor_set(x_45, 1, x_36);
lean_ctor_set(x_45, 2, x_5);
lean_ctor_set(x_45, 3, x_44);
lean_ctor_set(x_45, 4, x_41);
if (x_24 == 0)
{
lean_ctor_set(x_23, 0, x_45);
x_46 = x_23;
goto block_50;
}
else
{
lean_object* x_51; 
x_51 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_51, 0, x_45);
x_46 = x_51;
goto block_50;
}
block_50:
{
lean_object* x_47; 
if (x_21 == 0)
{
lean_ctor_set(x_20, 0, x_46);
x_47 = x_20;
goto block_48;
}
else
{
lean_object* x_49; 
x_49 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_49, 0, x_46);
x_47 = x_49;
goto block_48;
}
block_48:
{
return x_47;
}
}
}
}
}
}
else
{
lean_object* x_62; lean_object* x_63; 
lean_dec(x_19);
lean_dec(x_17);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_62 = lean_box(0);
if (x_21 == 0)
{
lean_ctor_set(x_20, 0, x_62);
x_63 = x_20;
goto block_64;
}
else
{
lean_object* x_65; 
x_65 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_65, 0, x_62);
x_63 = x_65;
goto block_64;
}
block_64:
{
return x_63;
}
}
}
}
else
{
lean_dec(x_17);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_18;
}
}
else
{
lean_object* x_68; lean_object* x_69; 
lean_dec(x_14);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_68 = lean_box(0);
if (x_16 == 0)
{
lean_ctor_set(x_15, 0, x_68);
x_69 = x_15;
goto block_70;
}
else
{
lean_object* x_71; 
x_71 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_71, 0, x_68);
x_69 = x_71;
goto block_70;
}
block_70:
{
return x_69;
}
}
}
}
else
{
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftReflection(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; 
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_2);
x_14 = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_goOrAtom(x_2, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_61; 
x_15 = lean_ctor_get(x_14, 0);
x_61 = !lean_is_exclusive(x_14);
if (x_61 == 0)
{
x_16 = x_14;
x_17 = x_61;
goto block_60;
}
else
{
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_box(0);
x_17 = x_61;
goto block_60;
}
block_60:
{
if (lean_obj_tag(x_15) == 1)
{
lean_object* x_18; lean_object* x_19; 
lean_del_object(x_16);
x_18 = lean_ctor_get(x_15, 0);
lean_inc(x_18);
lean_dec_ref(x_15);
lean_inc_ref(x_1);
x_19 = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_goOrAtom(x_1, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_55; 
x_20 = lean_ctor_get(x_19, 0);
x_55 = !lean_is_exclusive(x_19);
if (x_55 == 0)
{
x_21 = x_19;
x_22 = x_55;
goto block_54;
}
else
{
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_box(0);
x_22 = x_55;
goto block_54;
}
block_54:
{
if (lean_obj_tag(x_20) == 1)
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; uint8_t x_49; 
x_23 = lean_ctor_get(x_20, 0);
x_49 = !lean_is_exclusive(x_20);
if (x_49 == 0)
{
x_24 = x_20;
x_25 = x_49;
goto block_48;
}
else
{
lean_inc(x_23);
lean_dec(x_20);
x_24 = lean_box(0);
x_25 = x_49;
goto block_48;
}
block_48:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_26 = lean_ctor_get(x_18, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_18, 1);
x_28 = lean_ctor_get(x_18, 4);
x_29 = lean_ctor_get(x_23, 0);
x_30 = lean_ctor_get(x_23, 1);
x_31 = lean_ctor_get(x_23, 4);
lean_inc_ref(x_30);
lean_inc_ref(x_27);
lean_inc(x_29);
lean_inc(x_26);
x_32 = lean_apply_4(x_3, x_26, x_29, x_27, x_30);
x_33 = lean_box(0);
x_34 = l_Lean_mkConst(x_4, x_33);
lean_inc(x_26);
x_35 = l_Lean_mkNatLit(x_26);
lean_inc(x_29);
x_36 = l_Lean_mkNatLit(x_29);
lean_inc_ref(x_31);
lean_inc_ref(x_28);
lean_inc_ref(x_36);
lean_inc_ref(x_35);
x_37 = l_Lean_mkApp4(x_34, x_35, x_36, x_28, x_31);
x_38 = l_Lean_mkConst(x_5, x_33);
x_39 = l_Lean_mkAppB(x_38, x_35, x_36);
x_40 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryCongrProof___boxed), 11, 5);
lean_closure_set(x_40, 0, x_18);
lean_closure_set(x_40, 1, x_23);
lean_closure_set(x_40, 2, x_2);
lean_closure_set(x_40, 3, x_1);
lean_closure_set(x_40, 4, x_39);
x_41 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_41, 0, x_26);
lean_ctor_set(x_41, 1, x_32);
lean_ctor_set(x_41, 2, x_6);
lean_ctor_set(x_41, 3, x_40);
lean_ctor_set(x_41, 4, x_37);
if (x_25 == 0)
{
lean_ctor_set(x_24, 0, x_41);
x_42 = x_24;
goto block_46;
}
else
{
lean_object* x_47; 
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_41);
x_42 = x_47;
goto block_46;
}
block_46:
{
lean_object* x_43; 
if (x_22 == 0)
{
lean_ctor_set(x_21, 0, x_42);
x_43 = x_21;
goto block_44;
}
else
{
lean_object* x_45; 
x_45 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_45, 0, x_42);
x_43 = x_45;
goto block_44;
}
block_44:
{
return x_43;
}
}
}
}
else
{
lean_object* x_50; lean_object* x_51; 
lean_dec(x_20);
lean_dec(x_18);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_50 = lean_box(0);
if (x_22 == 0)
{
lean_ctor_set(x_21, 0, x_50);
x_51 = x_21;
goto block_52;
}
else
{
lean_object* x_53; 
x_53 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_53, 0, x_50);
x_51 = x_53;
goto block_52;
}
block_52:
{
return x_51;
}
}
}
}
else
{
lean_dec(x_18);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_19;
}
}
else
{
lean_object* x_56; lean_object* x_57; 
lean_dec(x_15);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_56 = lean_box(0);
if (x_17 == 0)
{
lean_ctor_set(x_16, 0, x_56);
x_57 = x_16;
goto block_58;
}
else
{
lean_object* x_59; 
x_59 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_59, 0, x_56);
x_57 = x_59;
goto block_58;
}
block_58:
{
return x_57;
}
}
}
}
else
{
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_14;
}
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__63(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__62));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__71(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__70));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__79(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__78));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_of_binaryReflection(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_1);
x_12 = l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of(x_1, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_42; 
x_13 = lean_ctor_get(x_12, 0);
x_42 = !lean_is_exclusive(x_12);
if (x_42 == 0)
{
x_14 = x_12;
x_15 = x_42;
goto block_41;
}
else
{
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_box(0);
x_15 = x_42;
goto block_41;
}
block_41:
{
if (lean_obj_tag(x_13) == 1)
{
lean_object* x_16; lean_object* x_17; 
lean_del_object(x_14);
x_16 = lean_ctor_get(x_13, 0);
lean_inc(x_16);
lean_dec_ref(x_13);
lean_inc_ref(x_2);
x_17 = l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of(x_2, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_28; 
x_18 = lean_ctor_get(x_17, 0);
x_28 = !lean_is_exclusive(x_17);
if (x_28 == 0)
{
x_19 = x_17;
x_20 = x_28;
goto block_27;
}
else
{
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_box(0);
x_20 = x_28;
goto block_27;
}
block_27:
{
if (lean_obj_tag(x_18) == 1)
{
lean_object* x_21; lean_object* x_22; 
lean_del_object(x_19);
x_21 = lean_ctor_get(x_18, 0);
lean_inc(x_21);
lean_dec_ref(x_18);
x_22 = l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_mkBinPred___redArg(x_16, x_21, x_1, x_2, x_3, x_4);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_18);
lean_dec(x_16);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_23 = lean_box(0);
if (x_20 == 0)
{
lean_ctor_set(x_19, 0, x_23);
x_24 = x_19;
goto block_25;
}
else
{
lean_object* x_26; 
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_23);
x_24 = x_26;
goto block_25;
}
block_25:
{
return x_24;
}
}
}
}
else
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; uint8_t x_36; 
lean_dec(x_16);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_29 = lean_ctor_get(x_17, 0);
x_36 = !lean_is_exclusive(x_17);
if (x_36 == 0)
{
x_30 = x_17;
x_31 = x_36;
goto block_35;
}
else
{
lean_inc(x_29);
lean_dec(x_17);
x_30 = lean_box(0);
x_31 = x_36;
goto block_35;
}
block_35:
{
lean_object* x_32; 
if (x_31 == 0)
{
x_32 = x_30;
goto block_33;
}
else
{
lean_object* x_34; 
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_29);
x_32 = x_34;
goto block_33;
}
block_33:
{
return x_32;
}
}
}
}
else
{
lean_object* x_37; lean_object* x_38; 
lean_dec(x_13);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_37 = lean_box(0);
if (x_15 == 0)
{
lean_ctor_set(x_14, 0, x_37);
x_38 = x_14;
goto block_39;
}
else
{
lean_object* x_40; 
x_40 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_40, 0, x_37);
x_38 = x_40;
goto block_39;
}
block_39:
{
return x_38;
}
}
}
}
else
{
lean_object* x_43; lean_object* x_44; uint8_t x_45; uint8_t x_50; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_43 = lean_ctor_get(x_12, 0);
x_50 = !lean_is_exclusive(x_12);
if (x_50 == 0)
{
x_44 = x_12;
x_45 = x_50;
goto block_49;
}
else
{
lean_inc(x_43);
lean_dec(x_12);
x_44 = lean_box(0);
x_45 = x_50;
goto block_49;
}
block_49:
{
lean_object* x_46; 
if (x_45 == 0)
{
x_46 = x_44;
goto block_47;
}
else
{
lean_object* x_48; 
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_43);
x_46 = x_48;
goto block_47;
}
block_47:
{
return x_46;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_of_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_12; 
lean_inc_ref(x_1);
x_12 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_1, x_5);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_111; 
x_13 = lean_ctor_get(x_12, 0);
x_111 = !lean_is_exclusive(x_12);
if (x_111 == 0)
{
x_14 = x_12;
x_15 = x_111;
goto block_110;
}
else
{
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_box(0);
x_15 = x_111;
goto block_110;
}
block_110:
{
lean_object* x_21; uint8_t x_22; 
x_21 = l_Lean_Expr_cleanupAnnotations(x_13);
x_22 = l_Lean_Expr_isApp(x_21);
if (x_22 == 0)
{
lean_dec_ref(x_21);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
goto block_20;
}
else
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = lean_ctor_get(x_21, 1);
lean_inc_ref(x_23);
x_24 = l_Lean_Expr_appFnCleanup___redArg(x_21);
x_25 = l_Lean_Expr_isApp(x_24);
if (x_25 == 0)
{
lean_dec_ref(x_24);
lean_dec_ref(x_23);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
goto block_20;
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_24, 1);
lean_inc_ref(x_26);
x_27 = l_Lean_Expr_appFnCleanup___redArg(x_24);
x_28 = l_Lean_Expr_isApp(x_27);
if (x_28 == 0)
{
lean_dec_ref(x_27);
lean_dec_ref(x_26);
lean_dec_ref(x_23);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
goto block_20;
}
else
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_29 = l_Lean_Expr_appFnCleanup___redArg(x_27);
x_30 = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_of_go___closed__2));
x_31 = l_Lean_Expr_isConstOf(x_29, x_30);
if (x_31 == 0)
{
lean_object* x_32; uint8_t x_33; 
x_32 = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_of_go___closed__4));
x_33 = l_Lean_Expr_isConstOf(x_29, x_32);
if (x_33 == 0)
{
uint8_t x_34; 
x_34 = l_Lean_Expr_isApp(x_29);
if (x_34 == 0)
{
lean_dec_ref(x_29);
lean_dec_ref(x_26);
lean_dec_ref(x_23);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
goto block_20;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_35 = lean_ctor_get(x_29, 1);
lean_inc_ref(x_35);
x_36 = l_Lean_Expr_appFnCleanup___redArg(x_29);
x_37 = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_of_go___closed__7));
x_38 = l_Lean_Expr_isConstOf(x_36, x_37);
lean_dec_ref(x_36);
if (x_38 == 0)
{
lean_dec_ref(x_35);
lean_dec_ref(x_26);
lean_dec_ref(x_23);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
goto block_20;
}
else
{
lean_object* x_39; uint8_t x_40; 
lean_del_object(x_14);
x_39 = l_Lean_Expr_cleanupAnnotations(x_35);
x_40 = l_Lean_Expr_isApp(x_39);
if (x_40 == 0)
{
lean_dec_ref(x_39);
lean_dec_ref(x_26);
lean_dec_ref(x_23);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
goto block_11;
}
else
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_41 = l_Lean_Expr_appFnCleanup___redArg(x_39);
x_42 = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_of_go___closed__8));
x_43 = l_Lean_Expr_isConstOf(x_41, x_42);
lean_dec_ref(x_41);
if (x_43 == 0)
{
lean_dec_ref(x_26);
lean_dec_ref(x_23);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
goto block_11;
}
else
{
uint8_t x_44; lean_object* x_45; 
x_44 = 0;
x_45 = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_of_binaryReflection(x_26, x_23, x_44, x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_45;
}
}
}
}
}
else
{
uint8_t x_46; lean_object* x_47; 
lean_dec_ref(x_29);
lean_del_object(x_14);
x_46 = 1;
x_47 = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_of_binaryReflection(x_26, x_23, x_46, x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_47;
}
}
else
{
lean_object* x_48; 
lean_dec_ref(x_29);
lean_del_object(x_14);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc_ref(x_26);
x_48 = l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of(x_26, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; uint8_t x_51; uint8_t x_101; 
x_49 = lean_ctor_get(x_48, 0);
x_101 = !lean_is_exclusive(x_48);
if (x_101 == 0)
{
x_50 = x_48;
x_51 = x_101;
goto block_100;
}
else
{
lean_inc(x_49);
lean_dec(x_48);
x_50 = lean_box(0);
x_51 = x_101;
goto block_100;
}
block_100:
{
if (lean_obj_tag(x_49) == 1)
{
lean_object* x_52; lean_object* x_53; 
lean_del_object(x_50);
x_52 = lean_ctor_get(x_49, 0);
lean_inc(x_52);
lean_dec_ref(x_49);
x_53 = l_Lean_Meta_getNatValue_x3f(x_23, x_4, x_5, x_6, x_7);
lean_dec_ref(x_23);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; uint8_t x_56; uint8_t x_87; 
x_54 = lean_ctor_get(x_53, 0);
x_87 = !lean_is_exclusive(x_53);
if (x_87 == 0)
{
x_55 = x_53;
x_56 = x_87;
goto block_86;
}
else
{
lean_inc(x_54);
lean_dec(x_53);
x_55 = lean_box(0);
x_56 = x_87;
goto block_86;
}
block_86:
{
if (lean_obj_tag(x_54) == 1)
{
lean_object* x_57; lean_object* x_58; uint8_t x_59; uint8_t x_81; 
lean_del_object(x_55);
x_57 = lean_ctor_get(x_54, 0);
x_81 = !lean_is_exclusive(x_54);
if (x_81 == 0)
{
x_58 = x_54;
x_59 = x_81;
goto block_80;
}
else
{
lean_inc(x_57);
lean_dec(x_54);
x_58 = lean_box(0);
x_59 = x_81;
goto block_80;
}
block_80:
{
lean_object* x_60; 
x_60 = l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_mkGetLsbD___redArg(x_52, x_26, x_57, x_1);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; uint8_t x_63; uint8_t x_71; 
x_61 = lean_ctor_get(x_60, 0);
x_71 = !lean_is_exclusive(x_60);
if (x_71 == 0)
{
x_62 = x_60;
x_63 = x_71;
goto block_70;
}
else
{
lean_inc(x_61);
lean_dec(x_60);
x_62 = lean_box(0);
x_63 = x_71;
goto block_70;
}
block_70:
{
lean_object* x_64; 
if (x_59 == 0)
{
lean_ctor_set(x_58, 0, x_61);
x_64 = x_58;
goto block_68;
}
else
{
lean_object* x_69; 
x_69 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_69, 0, x_61);
x_64 = x_69;
goto block_68;
}
block_68:
{
lean_object* x_65; 
if (x_63 == 0)
{
lean_ctor_set(x_62, 0, x_64);
x_65 = x_62;
goto block_66;
}
else
{
lean_object* x_67; 
x_67 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_67, 0, x_64);
x_65 = x_67;
goto block_66;
}
block_66:
{
return x_65;
}
}
}
}
else
{
lean_object* x_72; lean_object* x_73; uint8_t x_74; uint8_t x_79; 
lean_del_object(x_58);
x_72 = lean_ctor_get(x_60, 0);
x_79 = !lean_is_exclusive(x_60);
if (x_79 == 0)
{
x_73 = x_60;
x_74 = x_79;
goto block_78;
}
else
{
lean_inc(x_72);
lean_dec(x_60);
x_73 = lean_box(0);
x_74 = x_79;
goto block_78;
}
block_78:
{
lean_object* x_75; 
if (x_74 == 0)
{
x_75 = x_73;
goto block_76;
}
else
{
lean_object* x_77; 
x_77 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_77, 0, x_72);
x_75 = x_77;
goto block_76;
}
block_76:
{
return x_75;
}
}
}
}
}
else
{
lean_object* x_82; lean_object* x_83; 
lean_dec(x_54);
lean_dec(x_52);
lean_dec_ref(x_26);
lean_dec_ref(x_1);
x_82 = lean_box(0);
if (x_56 == 0)
{
lean_ctor_set(x_55, 0, x_82);
x_83 = x_55;
goto block_84;
}
else
{
lean_object* x_85; 
x_85 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_85, 0, x_82);
x_83 = x_85;
goto block_84;
}
block_84:
{
return x_83;
}
}
}
}
else
{
lean_object* x_88; lean_object* x_89; uint8_t x_90; uint8_t x_95; 
lean_dec(x_52);
lean_dec_ref(x_26);
lean_dec_ref(x_1);
x_88 = lean_ctor_get(x_53, 0);
x_95 = !lean_is_exclusive(x_53);
if (x_95 == 0)
{
x_89 = x_53;
x_90 = x_95;
goto block_94;
}
else
{
lean_inc(x_88);
lean_dec(x_53);
x_89 = lean_box(0);
x_90 = x_95;
goto block_94;
}
block_94:
{
lean_object* x_91; 
if (x_90 == 0)
{
x_91 = x_89;
goto block_92;
}
else
{
lean_object* x_93; 
x_93 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_93, 0, x_88);
x_91 = x_93;
goto block_92;
}
block_92:
{
return x_91;
}
}
}
}
else
{
lean_object* x_96; lean_object* x_97; 
lean_dec(x_49);
lean_dec_ref(x_26);
lean_dec_ref(x_23);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_96 = lean_box(0);
if (x_51 == 0)
{
lean_ctor_set(x_50, 0, x_96);
x_97 = x_50;
goto block_98;
}
else
{
lean_object* x_99; 
x_99 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_99, 0, x_96);
x_97 = x_99;
goto block_98;
}
block_98:
{
return x_97;
}
}
}
}
else
{
lean_object* x_102; lean_object* x_103; uint8_t x_104; uint8_t x_109; 
lean_dec_ref(x_26);
lean_dec_ref(x_23);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_102 = lean_ctor_get(x_48, 0);
x_109 = !lean_is_exclusive(x_48);
if (x_109 == 0)
{
x_103 = x_48;
x_104 = x_109;
goto block_108;
}
else
{
lean_inc(x_102);
lean_dec(x_48);
x_103 = lean_box(0);
x_104 = x_109;
goto block_108;
}
block_108:
{
lean_object* x_105; 
if (x_104 == 0)
{
x_105 = x_103;
goto block_106;
}
else
{
lean_object* x_107; 
x_107 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_107, 0, x_102);
x_105 = x_107;
goto block_106;
}
block_106:
{
return x_105;
}
}
}
}
}
}
}
block_20:
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_box(0);
if (x_15 == 0)
{
lean_ctor_set(x_14, 0, x_16);
x_17 = x_14;
goto block_18;
}
else
{
lean_object* x_19; 
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_16);
x_17 = x_19;
goto block_18;
}
block_18:
{
return x_17;
}
}
}
}
else
{
lean_object* x_112; lean_object* x_113; uint8_t x_114; uint8_t x_119; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_112 = lean_ctor_get(x_12, 0);
x_119 = !lean_is_exclusive(x_12);
if (x_119 == 0)
{
x_113 = x_12;
x_114 = x_119;
goto block_118;
}
else
{
lean_inc(x_112);
lean_dec(x_12);
x_113 = lean_box(0);
x_114 = x_119;
goto block_118;
}
block_118:
{
lean_object* x_115; 
if (x_114 == 0)
{
x_115 = x_113;
goto block_116;
}
else
{
lean_object* x_117; 
x_117 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_117, 0, x_112);
x_115 = x_117;
goto block_116;
}
block_116:
{
return x_115;
}
}
}
block_11:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVPredCache___at___00Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_of_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_st_ref_get(x_2);
x_34 = lean_ctor_get(x_33, 2);
lean_inc_ref(x_34);
lean_dec(x_33);
x_35 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom_spec__2_spec__12___redArg(x_34, x_1);
lean_dec_ref(x_34);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; 
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_1);
x_36 = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_of_go(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; 
lean_dec_ref(x_36);
lean_inc_ref(x_1);
x_38 = l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_boolAtom(x_1, x_3, x_4, x_5, x_6, x_7);
x_9 = x_38;
goto block_32;
}
else
{
lean_dec_ref(x_37);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_9 = x_36;
goto block_32;
}
}
else
{
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_9 = x_36;
goto block_32;
}
}
else
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; uint8_t x_46; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_39 = lean_ctor_get(x_35, 0);
x_46 = !lean_is_exclusive(x_35);
if (x_46 == 0)
{
x_40 = x_35;
x_41 = x_46;
goto block_45;
}
else
{
lean_inc(x_39);
lean_dec(x_35);
x_40 = lean_box(0);
x_41 = x_46;
goto block_45;
}
block_45:
{
lean_object* x_42; 
if (x_41 == 0)
{
lean_ctor_set_tag(x_40, 0);
x_42 = x_40;
goto block_43;
}
else
{
lean_object* x_44; 
x_44 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_44, 0, x_39);
x_42 = x_44;
goto block_43;
}
block_43:
{
return x_42;
}
}
}
block_32:
{
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_31; 
x_10 = lean_ctor_get(x_9, 0);
x_31 = !lean_is_exclusive(x_9);
if (x_31 == 0)
{
x_11 = x_9;
x_12 = x_31;
goto block_30;
}
else
{
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_box(0);
x_12 = x_31;
goto block_30;
}
block_30:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_29; 
x_13 = lean_st_ref_take(x_2);
x_14 = lean_ctor_get(x_13, 0);
x_15 = lean_ctor_get(x_13, 1);
x_16 = lean_ctor_get(x_13, 2);
x_17 = lean_ctor_get(x_13, 3);
x_29 = !lean_is_exclusive(x_13);
if (x_29 == 0)
{
x_18 = x_13;
x_19 = x_29;
goto block_28;
}
else
{
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_13);
x_18 = lean_box(0);
x_19 = x_29;
goto block_28;
}
block_28:
{
lean_object* x_20; lean_object* x_21; 
lean_inc(x_10);
x_20 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13___redArg(x_16, x_1, x_10);
if (x_19 == 0)
{
lean_ctor_set(x_18, 2, x_20);
x_21 = x_18;
goto block_26;
}
else
{
lean_object* x_27; 
x_27 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_27, 0, x_14);
lean_ctor_set(x_27, 1, x_15);
lean_ctor_set(x_27, 2, x_20);
lean_ctor_set(x_27, 3, x_17);
x_21 = x_27;
goto block_26;
}
block_26:
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_st_ref_set(x_2, x_21);
if (x_12 == 0)
{
x_23 = x_11;
goto block_24;
}
else
{
lean_object* x_25; 
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_10);
x_23 = x_25;
goto block_24;
}
block_24:
{
return x_23;
}
}
}
}
}
else
{
lean_dec_ref(x_1);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_of(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVPredCache___at___00Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_of_spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goPred(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_of(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_43; 
x_10 = lean_ctor_get(x_9, 0);
x_43 = !lean_is_exclusive(x_9);
if (x_43 == 0)
{
x_11 = x_9;
x_12 = x_43;
goto block_42;
}
else
{
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_box(0);
x_12 = x_43;
goto block_42;
}
block_42:
{
if (lean_obj_tag(x_10) == 1)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_37; 
lean_del_object(x_11);
x_13 = lean_ctor_get(x_10, 0);
x_37 = !lean_is_exclusive(x_10);
if (x_37 == 0)
{
x_14 = x_10;
x_15 = x_37;
goto block_36;
}
else
{
lean_inc(x_13);
lean_dec(x_10);
x_14 = lean_box(0);
x_15 = x_37;
goto block_36;
}
block_36:
{
lean_object* x_16; 
x_16 = l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_ofPred___redArg(x_13);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_27; 
x_17 = lean_ctor_get(x_16, 0);
x_27 = !lean_is_exclusive(x_16);
if (x_27 == 0)
{
x_18 = x_16;
x_19 = x_27;
goto block_26;
}
else
{
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_box(0);
x_19 = x_27;
goto block_26;
}
block_26:
{
lean_object* x_20; 
if (x_15 == 0)
{
lean_ctor_set(x_14, 0, x_17);
x_20 = x_14;
goto block_24;
}
else
{
lean_object* x_25; 
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_17);
x_20 = x_25;
goto block_24;
}
block_24:
{
lean_object* x_21; 
if (x_19 == 0)
{
lean_ctor_set(x_18, 0, x_20);
x_21 = x_18;
goto block_22;
}
else
{
lean_object* x_23; 
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_20);
x_21 = x_23;
goto block_22;
}
block_22:
{
return x_21;
}
}
}
}
else
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; uint8_t x_35; 
lean_del_object(x_14);
x_28 = lean_ctor_get(x_16, 0);
x_35 = !lean_is_exclusive(x_16);
if (x_35 == 0)
{
x_29 = x_16;
x_30 = x_35;
goto block_34;
}
else
{
lean_inc(x_28);
lean_dec(x_16);
x_29 = lean_box(0);
x_30 = x_35;
goto block_34;
}
block_34:
{
lean_object* x_31; 
if (x_30 == 0)
{
x_31 = x_29;
goto block_32;
}
else
{
lean_object* x_33; 
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_28);
x_31 = x_33;
goto block_32;
}
block_32:
{
return x_31;
}
}
}
}
}
else
{
lean_object* x_38; lean_object* x_39; 
lean_dec(x_10);
x_38 = lean_box(0);
if (x_12 == 0)
{
lean_ctor_set(x_11, 0, x_38);
x_39 = x_11;
goto block_40;
}
else
{
lean_object* x_41; 
x_41 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_41, 0, x_38);
x_39 = x_41;
goto block_40;
}
block_40:
{
return x_39;
}
}
}
}
else
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; uint8_t x_51; 
x_44 = lean_ctor_get(x_9, 0);
x_51 = !lean_is_exclusive(x_9);
if (x_51 == 0)
{
x_45 = x_9;
x_46 = x_51;
goto block_50;
}
else
{
lean_inc(x_44);
lean_dec(x_9);
x_45 = lean_box(0);
x_46 = x_51;
goto block_50;
}
block_50:
{
lean_object* x_47; 
if (x_46 == 0)
{
x_47 = x_45;
goto block_48;
}
else
{
lean_object* x_49; 
x_49 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_49, 0, x_44);
x_47 = x_49;
goto block_48;
}
block_48:
{
return x_47;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_gateReflection(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_1);
x_12 = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom(x_1, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_57; 
x_13 = lean_ctor_get(x_12, 0);
x_57 = !lean_is_exclusive(x_12);
if (x_57 == 0)
{
x_14 = x_12;
x_15 = x_57;
goto block_56;
}
else
{
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_box(0);
x_15 = x_57;
goto block_56;
}
block_56:
{
if (lean_obj_tag(x_13) == 1)
{
lean_object* x_16; lean_object* x_17; 
lean_del_object(x_14);
x_16 = lean_ctor_get(x_13, 0);
lean_inc(x_16);
lean_dec_ref(x_13);
lean_inc_ref(x_2);
x_17 = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom(x_2, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_51; 
x_18 = lean_ctor_get(x_17, 0);
x_51 = !lean_is_exclusive(x_17);
if (x_51 == 0)
{
x_19 = x_17;
x_20 = x_51;
goto block_50;
}
else
{
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_box(0);
x_20 = x_51;
goto block_50;
}
block_50:
{
if (lean_obj_tag(x_18) == 1)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_45; 
lean_del_object(x_19);
x_21 = lean_ctor_get(x_18, 0);
x_45 = !lean_is_exclusive(x_18);
if (x_45 == 0)
{
x_22 = x_18;
x_23 = x_45;
goto block_44;
}
else
{
lean_inc(x_21);
lean_dec(x_18);
x_22 = lean_box(0);
x_23 = x_45;
goto block_44;
}
block_44:
{
lean_object* x_24; 
x_24 = l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_mkGate___redArg(x_16, x_21, x_1, x_2, x_3, x_4);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; uint8_t x_35; 
x_25 = lean_ctor_get(x_24, 0);
x_35 = !lean_is_exclusive(x_24);
if (x_35 == 0)
{
x_26 = x_24;
x_27 = x_35;
goto block_34;
}
else
{
lean_inc(x_25);
lean_dec(x_24);
x_26 = lean_box(0);
x_27 = x_35;
goto block_34;
}
block_34:
{
lean_object* x_28; 
if (x_23 == 0)
{
lean_ctor_set(x_22, 0, x_25);
x_28 = x_22;
goto block_32;
}
else
{
lean_object* x_33; 
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_25);
x_28 = x_33;
goto block_32;
}
block_32:
{
lean_object* x_29; 
if (x_27 == 0)
{
lean_ctor_set(x_26, 0, x_28);
x_29 = x_26;
goto block_30;
}
else
{
lean_object* x_31; 
x_31 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_31, 0, x_28);
x_29 = x_31;
goto block_30;
}
block_30:
{
return x_29;
}
}
}
}
else
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; uint8_t x_43; 
lean_del_object(x_22);
x_36 = lean_ctor_get(x_24, 0);
x_43 = !lean_is_exclusive(x_24);
if (x_43 == 0)
{
x_37 = x_24;
x_38 = x_43;
goto block_42;
}
else
{
lean_inc(x_36);
lean_dec(x_24);
x_37 = lean_box(0);
x_38 = x_43;
goto block_42;
}
block_42:
{
lean_object* x_39; 
if (x_38 == 0)
{
x_39 = x_37;
goto block_40;
}
else
{
lean_object* x_41; 
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_36);
x_39 = x_41;
goto block_40;
}
block_40:
{
return x_39;
}
}
}
}
}
else
{
lean_object* x_46; lean_object* x_47; 
lean_dec(x_18);
lean_dec(x_16);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_46 = lean_box(0);
if (x_20 == 0)
{
lean_ctor_set(x_19, 0, x_46);
x_47 = x_19;
goto block_48;
}
else
{
lean_object* x_49; 
x_49 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_49, 0, x_46);
x_47 = x_49;
goto block_48;
}
block_48:
{
return x_47;
}
}
}
}
else
{
lean_dec(x_16);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_17;
}
}
else
{
lean_object* x_52; lean_object* x_53; 
lean_dec(x_13);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_52 = lean_box(0);
if (x_15 == 0)
{
lean_ctor_set(x_14, 0, x_52);
x_53 = x_14;
goto block_54;
}
else
{
lean_object* x_55; 
x_55 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_55, 0, x_52);
x_53 = x_55;
goto block_54;
}
block_54:
{
return x_53;
}
}
}
}
else
{
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_12; 
lean_inc_ref(x_1);
x_12 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_1, x_5);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec_ref(x_12);
x_14 = l_Lean_Expr_cleanupAnnotations(x_13);
x_15 = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_go___closed__2));
x_16 = l_Lean_Expr_isConstOf(x_14, x_15);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_go___closed__4));
x_18 = l_Lean_Expr_isConstOf(x_14, x_17);
if (x_18 == 0)
{
uint8_t x_19; 
x_19 = l_Lean_Expr_isApp(x_14);
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec_ref(x_14);
x_20 = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goPred(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_21 = lean_ctor_get(x_14, 1);
lean_inc_ref(x_21);
x_22 = l_Lean_Expr_appFnCleanup___redArg(x_14);
x_23 = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_go___closed__5));
x_24 = l_Lean_Expr_isConstOf(x_22, x_23);
if (x_24 == 0)
{
uint8_t x_25; 
x_25 = l_Lean_Expr_isApp(x_22);
if (x_25 == 0)
{
lean_object* x_26; 
lean_dec_ref(x_22);
lean_dec_ref(x_21);
x_26 = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goPred(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_27 = lean_ctor_get(x_22, 1);
lean_inc_ref(x_27);
x_28 = l_Lean_Expr_appFnCleanup___redArg(x_22);
x_29 = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_go___closed__6));
x_30 = l_Lean_Expr_isConstOf(x_28, x_29);
if (x_30 == 0)
{
lean_object* x_31; uint8_t x_32; 
x_31 = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_go___closed__7));
x_32 = l_Lean_Expr_isConstOf(x_28, x_31);
if (x_32 == 0)
{
uint8_t x_33; 
x_33 = l_Lean_Expr_isApp(x_28);
if (x_33 == 0)
{
lean_object* x_34; 
lean_dec_ref(x_28);
lean_dec_ref(x_27);
lean_dec_ref(x_21);
x_34 = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goPred(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_35 = lean_ctor_get(x_28, 1);
lean_inc_ref(x_35);
x_36 = l_Lean_Expr_appFnCleanup___redArg(x_28);
x_37 = l_Lean_Expr_isApp(x_36);
if (x_37 == 0)
{
lean_object* x_38; 
lean_dec_ref(x_36);
lean_dec_ref(x_35);
lean_dec_ref(x_27);
lean_dec_ref(x_21);
x_38 = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goPred(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_39 = lean_ctor_get(x_36, 1);
lean_inc_ref(x_39);
x_40 = l_Lean_Expr_appFnCleanup___redArg(x_36);
x_41 = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_go___closed__9));
x_42 = l_Lean_Expr_isConstOf(x_40, x_41);
if (x_42 == 0)
{
lean_object* x_43; uint8_t x_44; 
lean_dec_ref(x_35);
x_43 = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_of_go___closed__7));
x_44 = l_Lean_Expr_isConstOf(x_40, x_43);
lean_dec_ref(x_40);
if (x_44 == 0)
{
lean_object* x_45; 
lean_dec_ref(x_39);
lean_dec_ref(x_27);
lean_dec_ref(x_21);
x_45 = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goPred(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_45;
}
else
{
lean_object* x_46; 
x_46 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_39, x_5);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
lean_dec_ref(x_46);
x_48 = l_Lean_Expr_cleanupAnnotations(x_47);
x_49 = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_go___closed__10));
x_50 = l_Lean_Expr_isConstOf(x_48, x_49);
if (x_50 == 0)
{
uint8_t x_51; 
lean_dec_ref(x_27);
lean_dec_ref(x_21);
x_51 = l_Lean_Expr_isApp(x_48);
if (x_51 == 0)
{
lean_dec_ref(x_48);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
goto block_11;
}
else
{
lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_52 = l_Lean_Expr_appFnCleanup___redArg(x_48);
x_53 = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_of_go___closed__8));
x_54 = l_Lean_Expr_isConstOf(x_52, x_53);
lean_dec_ref(x_52);
if (x_54 == 0)
{
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
goto block_11;
}
else
{
lean_object* x_55; 
x_55 = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goPred(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_55;
}
}
}
else
{
uint8_t x_56; lean_object* x_57; 
lean_dec_ref(x_48);
x_56 = 2;
x_57 = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_gateReflection(x_27, x_21, x_56, x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_57;
}
}
else
{
lean_object* x_58; lean_object* x_59; uint8_t x_60; uint8_t x_65; 
lean_dec_ref(x_27);
lean_dec_ref(x_21);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_58 = lean_ctor_get(x_46, 0);
x_65 = !lean_is_exclusive(x_46);
if (x_65 == 0)
{
x_59 = x_46;
x_60 = x_65;
goto block_64;
}
else
{
lean_inc(x_58);
lean_dec(x_46);
x_59 = lean_box(0);
x_60 = x_65;
goto block_64;
}
block_64:
{
lean_object* x_61; 
if (x_60 == 0)
{
x_61 = x_59;
goto block_62;
}
else
{
lean_object* x_63; 
x_63 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_63, 0, x_58);
x_61 = x_63;
goto block_62;
}
block_62:
{
return x_61;
}
}
}
}
}
else
{
lean_object* x_66; 
lean_dec_ref(x_40);
lean_dec_ref(x_39);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_35);
x_66 = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom(x_35, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; uint8_t x_69; uint8_t x_122; 
x_67 = lean_ctor_get(x_66, 0);
x_122 = !lean_is_exclusive(x_66);
if (x_122 == 0)
{
x_68 = x_66;
x_69 = x_122;
goto block_121;
}
else
{
lean_inc(x_67);
lean_dec(x_66);
x_68 = lean_box(0);
x_69 = x_122;
goto block_121;
}
block_121:
{
if (lean_obj_tag(x_67) == 1)
{
lean_object* x_70; lean_object* x_71; 
lean_del_object(x_68);
x_70 = lean_ctor_get(x_67, 0);
lean_inc(x_70);
lean_dec_ref(x_67);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_27);
x_71 = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom(x_27, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; lean_object* x_73; uint8_t x_74; uint8_t x_116; 
x_72 = lean_ctor_get(x_71, 0);
x_116 = !lean_is_exclusive(x_71);
if (x_116 == 0)
{
x_73 = x_71;
x_74 = x_116;
goto block_115;
}
else
{
lean_inc(x_72);
lean_dec(x_71);
x_73 = lean_box(0);
x_74 = x_116;
goto block_115;
}
block_115:
{
if (lean_obj_tag(x_72) == 1)
{
lean_object* x_75; lean_object* x_76; 
lean_del_object(x_73);
x_75 = lean_ctor_get(x_72, 0);
lean_inc(x_75);
lean_dec_ref(x_72);
lean_inc_ref(x_21);
x_76 = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom(x_21, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; uint8_t x_79; uint8_t x_110; 
x_77 = lean_ctor_get(x_76, 0);
x_110 = !lean_is_exclusive(x_76);
if (x_110 == 0)
{
x_78 = x_76;
x_79 = x_110;
goto block_109;
}
else
{
lean_inc(x_77);
lean_dec(x_76);
x_78 = lean_box(0);
x_79 = x_110;
goto block_109;
}
block_109:
{
if (lean_obj_tag(x_77) == 1)
{
lean_object* x_80; lean_object* x_81; uint8_t x_82; uint8_t x_104; 
lean_del_object(x_78);
x_80 = lean_ctor_get(x_77, 0);
x_104 = !lean_is_exclusive(x_77);
if (x_104 == 0)
{
x_81 = x_77;
x_82 = x_104;
goto block_103;
}
else
{
lean_inc(x_80);
lean_dec(x_77);
x_81 = lean_box(0);
x_82 = x_104;
goto block_103;
}
block_103:
{
lean_object* x_83; 
x_83 = l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_mkIte___redArg(x_70, x_75, x_80, x_35, x_27, x_21, x_1);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; uint8_t x_86; uint8_t x_94; 
x_84 = lean_ctor_get(x_83, 0);
x_94 = !lean_is_exclusive(x_83);
if (x_94 == 0)
{
x_85 = x_83;
x_86 = x_94;
goto block_93;
}
else
{
lean_inc(x_84);
lean_dec(x_83);
x_85 = lean_box(0);
x_86 = x_94;
goto block_93;
}
block_93:
{
lean_object* x_87; 
if (x_82 == 0)
{
lean_ctor_set(x_81, 0, x_84);
x_87 = x_81;
goto block_91;
}
else
{
lean_object* x_92; 
x_92 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_92, 0, x_84);
x_87 = x_92;
goto block_91;
}
block_91:
{
lean_object* x_88; 
if (x_86 == 0)
{
lean_ctor_set(x_85, 0, x_87);
x_88 = x_85;
goto block_89;
}
else
{
lean_object* x_90; 
x_90 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_90, 0, x_87);
x_88 = x_90;
goto block_89;
}
block_89:
{
return x_88;
}
}
}
}
else
{
lean_object* x_95; lean_object* x_96; uint8_t x_97; uint8_t x_102; 
lean_del_object(x_81);
x_95 = lean_ctor_get(x_83, 0);
x_102 = !lean_is_exclusive(x_83);
if (x_102 == 0)
{
x_96 = x_83;
x_97 = x_102;
goto block_101;
}
else
{
lean_inc(x_95);
lean_dec(x_83);
x_96 = lean_box(0);
x_97 = x_102;
goto block_101;
}
block_101:
{
lean_object* x_98; 
if (x_97 == 0)
{
x_98 = x_96;
goto block_99;
}
else
{
lean_object* x_100; 
x_100 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_100, 0, x_95);
x_98 = x_100;
goto block_99;
}
block_99:
{
return x_98;
}
}
}
}
}
else
{
lean_object* x_105; lean_object* x_106; 
lean_dec(x_77);
lean_dec(x_75);
lean_dec(x_70);
lean_dec_ref(x_35);
lean_dec_ref(x_27);
lean_dec_ref(x_21);
lean_dec_ref(x_1);
x_105 = lean_box(0);
if (x_79 == 0)
{
lean_ctor_set(x_78, 0, x_105);
x_106 = x_78;
goto block_107;
}
else
{
lean_object* x_108; 
x_108 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_108, 0, x_105);
x_106 = x_108;
goto block_107;
}
block_107:
{
return x_106;
}
}
}
}
else
{
lean_dec(x_75);
lean_dec(x_70);
lean_dec_ref(x_35);
lean_dec_ref(x_27);
lean_dec_ref(x_21);
lean_dec_ref(x_1);
return x_76;
}
}
else
{
lean_object* x_111; lean_object* x_112; 
lean_dec(x_72);
lean_dec(x_70);
lean_dec_ref(x_35);
lean_dec_ref(x_27);
lean_dec_ref(x_21);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_111 = lean_box(0);
if (x_74 == 0)
{
lean_ctor_set(x_73, 0, x_111);
x_112 = x_73;
goto block_113;
}
else
{
lean_object* x_114; 
x_114 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_114, 0, x_111);
x_112 = x_114;
goto block_113;
}
block_113:
{
return x_112;
}
}
}
}
else
{
lean_dec(x_70);
lean_dec_ref(x_35);
lean_dec_ref(x_27);
lean_dec_ref(x_21);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
return x_71;
}
}
else
{
lean_object* x_117; lean_object* x_118; 
lean_dec(x_67);
lean_dec_ref(x_35);
lean_dec_ref(x_27);
lean_dec_ref(x_21);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_117 = lean_box(0);
if (x_69 == 0)
{
lean_ctor_set(x_68, 0, x_117);
x_118 = x_68;
goto block_119;
}
else
{
lean_object* x_120; 
x_120 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_120, 0, x_117);
x_118 = x_120;
goto block_119;
}
block_119:
{
return x_118;
}
}
}
}
else
{
lean_dec_ref(x_35);
lean_dec_ref(x_27);
lean_dec_ref(x_21);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
return x_66;
}
}
}
}
}
else
{
uint8_t x_123; lean_object* x_124; 
lean_dec_ref(x_28);
x_123 = 0;
x_124 = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_gateReflection(x_27, x_21, x_123, x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_124;
}
}
else
{
uint8_t x_125; lean_object* x_126; 
lean_dec_ref(x_28);
x_125 = 1;
x_126 = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_gateReflection(x_27, x_21, x_125, x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_126;
}
}
}
else
{
lean_object* x_127; 
lean_dec_ref(x_22);
lean_inc_ref(x_21);
x_127 = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom(x_21, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_127) == 0)
{
lean_object* x_128; lean_object* x_129; uint8_t x_130; uint8_t x_161; 
x_128 = lean_ctor_get(x_127, 0);
x_161 = !lean_is_exclusive(x_127);
if (x_161 == 0)
{
x_129 = x_127;
x_130 = x_161;
goto block_160;
}
else
{
lean_inc(x_128);
lean_dec(x_127);
x_129 = lean_box(0);
x_130 = x_161;
goto block_160;
}
block_160:
{
if (lean_obj_tag(x_128) == 1)
{
lean_object* x_131; lean_object* x_132; uint8_t x_133; uint8_t x_155; 
lean_del_object(x_129);
x_131 = lean_ctor_get(x_128, 0);
x_155 = !lean_is_exclusive(x_128);
if (x_155 == 0)
{
x_132 = x_128;
x_133 = x_155;
goto block_154;
}
else
{
lean_inc(x_131);
lean_dec(x_128);
x_132 = lean_box(0);
x_133 = x_155;
goto block_154;
}
block_154:
{
lean_object* x_134; 
x_134 = l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_mkNot___redArg(x_131, x_21, x_1);
if (lean_obj_tag(x_134) == 0)
{
lean_object* x_135; lean_object* x_136; uint8_t x_137; uint8_t x_145; 
x_135 = lean_ctor_get(x_134, 0);
x_145 = !lean_is_exclusive(x_134);
if (x_145 == 0)
{
x_136 = x_134;
x_137 = x_145;
goto block_144;
}
else
{
lean_inc(x_135);
lean_dec(x_134);
x_136 = lean_box(0);
x_137 = x_145;
goto block_144;
}
block_144:
{
lean_object* x_138; 
if (x_133 == 0)
{
lean_ctor_set(x_132, 0, x_135);
x_138 = x_132;
goto block_142;
}
else
{
lean_object* x_143; 
x_143 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_143, 0, x_135);
x_138 = x_143;
goto block_142;
}
block_142:
{
lean_object* x_139; 
if (x_137 == 0)
{
lean_ctor_set(x_136, 0, x_138);
x_139 = x_136;
goto block_140;
}
else
{
lean_object* x_141; 
x_141 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_141, 0, x_138);
x_139 = x_141;
goto block_140;
}
block_140:
{
return x_139;
}
}
}
}
else
{
lean_object* x_146; lean_object* x_147; uint8_t x_148; uint8_t x_153; 
lean_del_object(x_132);
x_146 = lean_ctor_get(x_134, 0);
x_153 = !lean_is_exclusive(x_134);
if (x_153 == 0)
{
x_147 = x_134;
x_148 = x_153;
goto block_152;
}
else
{
lean_inc(x_146);
lean_dec(x_134);
x_147 = lean_box(0);
x_148 = x_153;
goto block_152;
}
block_152:
{
lean_object* x_149; 
if (x_148 == 0)
{
x_149 = x_147;
goto block_150;
}
else
{
lean_object* x_151; 
x_151 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_151, 0, x_146);
x_149 = x_151;
goto block_150;
}
block_150:
{
return x_149;
}
}
}
}
}
else
{
lean_object* x_156; lean_object* x_157; 
lean_dec(x_128);
lean_dec_ref(x_21);
lean_dec_ref(x_1);
x_156 = lean_box(0);
if (x_130 == 0)
{
lean_ctor_set(x_129, 0, x_156);
x_157 = x_129;
goto block_158;
}
else
{
lean_object* x_159; 
x_159 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_159, 0, x_156);
x_157 = x_159;
goto block_158;
}
block_158:
{
return x_157;
}
}
}
}
else
{
lean_dec_ref(x_21);
lean_dec_ref(x_1);
return x_127;
}
}
}
}
else
{
lean_object* x_162; 
lean_dec_ref(x_14);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_162 = l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_mkBoolConst___redArg(x_18);
if (lean_obj_tag(x_162) == 0)
{
lean_object* x_163; lean_object* x_164; uint8_t x_165; uint8_t x_171; 
x_163 = lean_ctor_get(x_162, 0);
x_171 = !lean_is_exclusive(x_162);
if (x_171 == 0)
{
x_164 = x_162;
x_165 = x_171;
goto block_170;
}
else
{
lean_inc(x_163);
lean_dec(x_162);
x_164 = lean_box(0);
x_165 = x_171;
goto block_170;
}
block_170:
{
lean_object* x_166; lean_object* x_167; 
x_166 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_166, 0, x_163);
if (x_165 == 0)
{
lean_ctor_set(x_164, 0, x_166);
x_167 = x_164;
goto block_168;
}
else
{
lean_object* x_169; 
x_169 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_169, 0, x_166);
x_167 = x_169;
goto block_168;
}
block_168:
{
return x_167;
}
}
}
else
{
lean_object* x_172; lean_object* x_173; uint8_t x_174; uint8_t x_179; 
x_172 = lean_ctor_get(x_162, 0);
x_179 = !lean_is_exclusive(x_162);
if (x_179 == 0)
{
x_173 = x_162;
x_174 = x_179;
goto block_178;
}
else
{
lean_inc(x_172);
lean_dec(x_162);
x_173 = lean_box(0);
x_174 = x_179;
goto block_178;
}
block_178:
{
lean_object* x_175; 
if (x_174 == 0)
{
x_175 = x_173;
goto block_176;
}
else
{
lean_object* x_177; 
x_177 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_177, 0, x_172);
x_175 = x_177;
goto block_176;
}
block_176:
{
return x_175;
}
}
}
}
}
else
{
uint8_t x_180; lean_object* x_181; 
lean_dec_ref(x_14);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_180 = 0;
x_181 = l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_mkBoolConst___redArg(x_180);
if (lean_obj_tag(x_181) == 0)
{
lean_object* x_182; lean_object* x_183; uint8_t x_184; uint8_t x_190; 
x_182 = lean_ctor_get(x_181, 0);
x_190 = !lean_is_exclusive(x_181);
if (x_190 == 0)
{
x_183 = x_181;
x_184 = x_190;
goto block_189;
}
else
{
lean_inc(x_182);
lean_dec(x_181);
x_183 = lean_box(0);
x_184 = x_190;
goto block_189;
}
block_189:
{
lean_object* x_185; lean_object* x_186; 
x_185 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_185, 0, x_182);
if (x_184 == 0)
{
lean_ctor_set(x_183, 0, x_185);
x_186 = x_183;
goto block_187;
}
else
{
lean_object* x_188; 
x_188 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_188, 0, x_185);
x_186 = x_188;
goto block_187;
}
block_187:
{
return x_186;
}
}
}
else
{
lean_object* x_191; lean_object* x_192; uint8_t x_193; uint8_t x_198; 
x_191 = lean_ctor_get(x_181, 0);
x_198 = !lean_is_exclusive(x_181);
if (x_198 == 0)
{
x_192 = x_181;
x_193 = x_198;
goto block_197;
}
else
{
lean_inc(x_191);
lean_dec(x_181);
x_192 = lean_box(0);
x_193 = x_198;
goto block_197;
}
block_197:
{
lean_object* x_194; 
if (x_193 == 0)
{
x_194 = x_192;
goto block_195;
}
else
{
lean_object* x_196; 
x_196 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_196, 0, x_191);
x_194 = x_196;
goto block_195;
}
block_195:
{
return x_194;
}
}
}
}
}
else
{
lean_object* x_199; lean_object* x_200; uint8_t x_201; uint8_t x_206; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_199 = lean_ctor_get(x_12, 0);
x_206 = !lean_is_exclusive(x_12);
if (x_206 == 0)
{
x_200 = x_12;
x_201 = x_206;
goto block_205;
}
else
{
lean_inc(x_199);
lean_dec(x_12);
x_200 = lean_box(0);
x_201 = x_206;
goto block_205;
}
block_205:
{
lean_object* x_202; 
if (x_201 == 0)
{
x_202 = x_200;
goto block_203;
}
else
{
lean_object* x_204; 
x_204 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_204, 0, x_199);
x_202 = x_204;
goto block_203;
}
block_203:
{
return x_202;
}
}
}
block_11:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_st_ref_get(x_2);
x_34 = lean_ctor_get(x_33, 3);
lean_inc_ref(x_34);
lean_dec(x_33);
x_35 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom_spec__2_spec__12___redArg(x_34, x_1);
lean_dec_ref(x_34);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; 
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_1);
x_36 = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_go(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; 
lean_dec_ref(x_36);
lean_inc_ref(x_1);
x_38 = l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_boolAtom(x_1, x_3, x_4, x_5, x_6, x_7);
x_9 = x_38;
goto block_32;
}
else
{
lean_dec_ref(x_37);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_9 = x_36;
goto block_32;
}
}
else
{
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_9 = x_36;
goto block_32;
}
}
else
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; uint8_t x_46; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_39 = lean_ctor_get(x_35, 0);
x_46 = !lean_is_exclusive(x_35);
if (x_46 == 0)
{
x_40 = x_35;
x_41 = x_46;
goto block_45;
}
else
{
lean_inc(x_39);
lean_dec(x_35);
x_40 = lean_box(0);
x_41 = x_46;
goto block_45;
}
block_45:
{
lean_object* x_42; 
if (x_41 == 0)
{
lean_ctor_set_tag(x_40, 0);
x_42 = x_40;
goto block_43;
}
else
{
lean_object* x_44; 
x_44 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_44, 0, x_39);
x_42 = x_44;
goto block_43;
}
block_43:
{
return x_42;
}
}
}
block_32:
{
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_31; 
x_10 = lean_ctor_get(x_9, 0);
x_31 = !lean_is_exclusive(x_9);
if (x_31 == 0)
{
x_11 = x_9;
x_12 = x_31;
goto block_30;
}
else
{
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_box(0);
x_12 = x_31;
goto block_30;
}
block_30:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_29; 
x_13 = lean_st_ref_take(x_2);
x_14 = lean_ctor_get(x_13, 0);
x_15 = lean_ctor_get(x_13, 1);
x_16 = lean_ctor_get(x_13, 2);
x_17 = lean_ctor_get(x_13, 3);
x_29 = !lean_is_exclusive(x_13);
if (x_29 == 0)
{
x_18 = x_13;
x_19 = x_29;
goto block_28;
}
else
{
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_13);
x_18 = lean_box(0);
x_19 = x_29;
goto block_28;
}
block_28:
{
lean_object* x_20; lean_object* x_21; 
lean_inc(x_10);
x_20 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13___redArg(x_17, x_1, x_10);
if (x_19 == 0)
{
lean_ctor_set(x_18, 3, x_20);
x_21 = x_18;
goto block_26;
}
else
{
lean_object* x_27; 
x_27 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_27, 0, x_14);
lean_ctor_set(x_27, 1, x_15);
lean_ctor_set(x_27, 2, x_16);
lean_ctor_set(x_27, 3, x_20);
x_21 = x_27;
goto block_26;
}
block_26:
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_st_ref_set(x_2, x_21);
if (x_12 == 0)
{
x_23 = x_11;
goto block_24;
}
else
{
lean_object* x_25; 
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_10);
x_23 = x_25;
goto block_24;
}
block_24:
{
return x_23;
}
}
}
}
}
else
{
lean_dec_ref(x_1);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__6(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__5));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__2));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__6(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__5));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__9(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__8));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__12(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__11));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__15(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__14));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__18(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__17));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__21(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__20));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
lean_inc_ref(x_1);
x_12 = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_goOrAtom(x_1, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_61; 
x_13 = lean_ctor_get(x_12, 0);
x_61 = !lean_is_exclusive(x_12);
if (x_61 == 0)
{
x_14 = x_12;
x_15 = x_61;
goto block_60;
}
else
{
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_box(0);
x_15 = x_61;
goto block_60;
}
block_60:
{
if (lean_obj_tag(x_13) == 1)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_55; 
x_16 = lean_ctor_get(x_13, 0);
x_55 = !lean_is_exclusive(x_13);
if (x_55 == 0)
{
x_17 = x_13;
x_18 = x_55;
goto block_54;
}
else
{
lean_inc(x_16);
lean_dec(x_13);
x_17 = lean_box(0);
x_18 = x_55;
goto block_54;
}
block_54:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_19 = lean_ctor_get(x_16, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_16, 1);
x_21 = lean_ctor_get(x_16, 4);
lean_inc_ref(x_20);
lean_inc(x_2);
lean_inc(x_19);
x_22 = l_Std_Tactic_BVDecide_BVExpr_un___override(x_19, x_2, x_20);
x_23 = lean_box(0);
x_24 = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__6, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__6_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__6);
lean_inc(x_19);
x_25 = l_Lean_mkNatLit(x_19);
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_38; 
x_38 = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__3, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__3_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__3);
x_26 = x_38;
goto block_37;
}
case 1:
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_39 = lean_ctor_get(x_2, 0);
lean_inc(x_39);
lean_dec_ref(x_2);
x_40 = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__6, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__6_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__6);
x_41 = l_Lean_mkNatLit(x_39);
x_42 = l_Lean_Expr_app___override(x_40, x_41);
x_26 = x_42;
goto block_37;
}
case 2:
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_43 = lean_ctor_get(x_2, 0);
lean_inc(x_43);
lean_dec_ref(x_2);
x_44 = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__9, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__9_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__9);
x_45 = l_Lean_mkNatLit(x_43);
x_46 = l_Lean_Expr_app___override(x_44, x_45);
x_26 = x_46;
goto block_37;
}
case 3:
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_47 = lean_ctor_get(x_2, 0);
lean_inc(x_47);
lean_dec_ref(x_2);
x_48 = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__12, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__12_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__12);
x_49 = l_Lean_mkNatLit(x_47);
x_50 = l_Lean_Expr_app___override(x_48, x_49);
x_26 = x_50;
goto block_37;
}
case 4:
{
lean_object* x_51; 
x_51 = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__15, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__15_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__15);
x_26 = x_51;
goto block_37;
}
case 5:
{
lean_object* x_52; 
x_52 = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__18, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__18_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__18);
x_26 = x_52;
goto block_37;
}
default: 
{
lean_object* x_53; 
x_53 = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__21, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__21_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__21);
x_26 = x_53;
goto block_37;
}
}
block_37:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_inc_ref(x_21);
x_27 = l_Lean_mkApp3(x_24, x_25, x_26, x_21);
x_28 = l_Lean_mkConst(x_3, x_23);
x_29 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryCongrProof___boxed), 9, 3);
lean_closure_set(x_29, 0, x_16);
lean_closure_set(x_29, 1, x_1);
lean_closure_set(x_29, 2, x_28);
x_30 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_30, 0, x_19);
lean_ctor_set(x_30, 1, x_22);
lean_ctor_set(x_30, 2, x_4);
lean_ctor_set(x_30, 3, x_29);
lean_ctor_set(x_30, 4, x_27);
if (x_18 == 0)
{
lean_ctor_set(x_17, 0, x_30);
x_31 = x_17;
goto block_35;
}
else
{
lean_object* x_36; 
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_30);
x_31 = x_36;
goto block_35;
}
block_35:
{
lean_object* x_32; 
if (x_15 == 0)
{
lean_ctor_set(x_14, 0, x_31);
x_32 = x_14;
goto block_33;
}
else
{
lean_object* x_34; 
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_31);
x_32 = x_34;
goto block_33;
}
block_33:
{
return x_32;
}
}
}
}
}
else
{
lean_object* x_56; lean_object* x_57; 
lean_dec(x_13);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_56 = lean_box(0);
if (x_15 == 0)
{
lean_ctor_set(x_14, 0, x_56);
x_57 = x_14;
goto block_58;
}
else
{
lean_object* x_59; 
x_59 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_59, 0, x_56);
x_57 = x_59;
goto block_58;
}
block_58:
{
return x_57;
}
}
}
}
else
{
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; 
lean_inc_ref(x_2);
x_14 = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_goOrAtom(x_2, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_50; 
x_15 = lean_ctor_get(x_14, 0);
x_50 = !lean_is_exclusive(x_14);
if (x_50 == 0)
{
x_16 = x_14;
x_17 = x_50;
goto block_49;
}
else
{
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_box(0);
x_17 = x_50;
goto block_49;
}
block_49:
{
if (lean_obj_tag(x_15) == 1)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_44; 
x_18 = lean_ctor_get(x_15, 0);
x_44 = !lean_is_exclusive(x_15);
if (x_44 == 0)
{
x_19 = x_15;
x_20 = x_44;
goto block_43;
}
else
{
lean_inc(x_18);
lean_dec(x_15);
x_19 = lean_box(0);
x_20 = x_44;
goto block_43;
}
block_43:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_21 = lean_ctor_get(x_18, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_18, 1);
x_23 = lean_ctor_get(x_18, 4);
lean_inc(x_1);
x_24 = lean_apply_1(x_3, x_1);
lean_inc_ref(x_22);
lean_inc(x_21);
x_25 = l_Std_Tactic_BVDecide_BVExpr_un___override(x_21, x_24, x_22);
x_26 = lean_box(0);
x_27 = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__6, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__6_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__6);
lean_inc(x_21);
x_28 = l_Lean_mkNatLit(x_21);
x_29 = l_Lean_mkConst(x_4, x_26);
x_30 = l_Lean_mkNatLit(x_1);
lean_inc_ref(x_30);
x_31 = l_Lean_Expr_app___override(x_29, x_30);
lean_inc_ref(x_23);
x_32 = l_Lean_mkApp3(x_27, x_28, x_31, x_23);
x_33 = l_Lean_mkConst(x_5, x_26);
x_34 = l_Lean_Expr_app___override(x_33, x_30);
x_35 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryCongrProof___boxed), 9, 3);
lean_closure_set(x_35, 0, x_18);
lean_closure_set(x_35, 1, x_2);
lean_closure_set(x_35, 2, x_34);
x_36 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_36, 0, x_21);
lean_ctor_set(x_36, 1, x_25);
lean_ctor_set(x_36, 2, x_6);
lean_ctor_set(x_36, 3, x_35);
lean_ctor_set(x_36, 4, x_32);
if (x_20 == 0)
{
lean_ctor_set(x_19, 0, x_36);
x_37 = x_19;
goto block_41;
}
else
{
lean_object* x_42; 
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_36);
x_37 = x_42;
goto block_41;
}
block_41:
{
lean_object* x_38; 
if (x_17 == 0)
{
lean_ctor_set(x_16, 0, x_37);
x_38 = x_16;
goto block_39;
}
else
{
lean_object* x_40; 
x_40 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_40, 0, x_37);
x_38 = x_40;
goto block_39;
}
block_39:
{
return x_38;
}
}
}
}
else
{
lean_object* x_45; lean_object* x_46; 
lean_dec(x_15);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_45 = lean_box(0);
if (x_17 == 0)
{
lean_ctor_set(x_16, 0, x_45);
x_46 = x_16;
goto block_47;
}
else
{
lean_object* x_48; 
x_48 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_48, 0, x_45);
x_46 = x_48;
goto block_47;
}
block_47:
{
return x_46;
}
}
}
}
else
{
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_14;
}
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__86(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__85));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_rotateReflection(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; 
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
x_14 = l_Lean_Meta_getNatValue_x3f(x_1, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_25; 
x_15 = lean_ctor_get(x_14, 0);
x_25 = !lean_is_exclusive(x_14);
if (x_25 == 0)
{
x_16 = x_14;
x_17 = x_25;
goto block_24;
}
else
{
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_box(0);
x_17 = x_25;
goto block_24;
}
block_24:
{
if (lean_obj_tag(x_15) == 1)
{
lean_object* x_18; lean_object* x_19; 
lean_del_object(x_16);
x_18 = lean_ctor_get(x_15, 0);
lean_inc(x_18);
lean_dec_ref(x_15);
x_19 = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection(x_18, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_15);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_20 = lean_box(0);
if (x_17 == 0)
{
lean_ctor_set(x_16, 0, x_20);
x_21 = x_16;
goto block_22;
}
else
{
lean_object* x_23; 
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_20);
x_21 = x_23;
goto block_22;
}
block_22:
{
return x_21;
}
}
}
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_33; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_26 = lean_ctor_get(x_14, 0);
x_33 = !lean_is_exclusive(x_14);
if (x_33 == 0)
{
x_27 = x_14;
x_28 = x_33;
goto block_32;
}
else
{
lean_inc(x_26);
lean_dec(x_14);
x_27 = lean_box(0);
x_28 = x_33;
goto block_32;
}
block_32:
{
lean_object* x_29; 
if (x_28 == 0)
{
x_29 = x_27;
goto block_30;
}
else
{
lean_object* x_31; 
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_26);
x_29 = x_31;
goto block_30;
}
block_30:
{
return x_29;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_15; 
lean_inc_ref(x_1);
x_15 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_1, x_5);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_554; 
x_16 = lean_ctor_get(x_15, 0);
x_554 = !lean_is_exclusive(x_15);
if (x_554 == 0)
{
x_17 = x_15;
x_18 = x_554;
goto block_553;
}
else
{
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_box(0);
x_18 = x_554;
goto block_553;
}
block_553:
{
lean_object* x_24; uint8_t x_25; 
x_24 = l_Lean_Expr_cleanupAnnotations(x_16);
x_25 = l_Lean_Expr_isApp(x_24);
if (x_25 == 0)
{
lean_dec_ref(x_24);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
goto block_23;
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_24, 1);
lean_inc_ref(x_26);
x_27 = l_Lean_Expr_appFnCleanup___redArg(x_24);
x_28 = l_Lean_Expr_isApp(x_27);
if (x_28 == 0)
{
lean_dec_ref(x_27);
lean_dec_ref(x_26);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
goto block_23;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_29 = lean_ctor_get(x_27, 1);
lean_inc_ref(x_29);
x_30 = l_Lean_Expr_appFnCleanup___redArg(x_27);
x_31 = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_of_go___closed__0));
x_32 = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__0));
x_33 = l_Lean_Expr_isConstOf(x_30, x_32);
if (x_33 == 0)
{
lean_object* x_34; uint8_t x_35; 
x_34 = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__1));
x_35 = l_Lean_Expr_isConstOf(x_30, x_34);
if (x_35 == 0)
{
lean_object* x_36; uint8_t x_37; 
x_36 = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__2));
x_37 = l_Lean_Expr_isConstOf(x_30, x_36);
if (x_37 == 0)
{
lean_object* x_38; uint8_t x_39; 
x_38 = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__4));
x_39 = l_Lean_Expr_isConstOf(x_30, x_38);
if (x_39 == 0)
{
uint8_t x_40; 
x_40 = l_Lean_Expr_isApp(x_30);
if (x_40 == 0)
{
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
goto block_23;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_41 = lean_ctor_get(x_30, 1);
lean_inc_ref(x_41);
x_42 = l_Lean_Expr_appFnCleanup___redArg(x_30);
x_43 = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__5));
x_44 = l_Lean_Expr_isConstOf(x_42, x_43);
if (x_44 == 0)
{
lean_object* x_45; uint8_t x_46; 
x_45 = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__6));
x_46 = l_Lean_Expr_isConstOf(x_42, x_45);
if (x_46 == 0)
{
lean_object* x_47; uint8_t x_48; 
x_47 = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__8));
x_48 = l_Lean_Expr_isConstOf(x_42, x_47);
if (x_48 == 0)
{
lean_object* x_49; uint8_t x_50; 
x_49 = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__10));
x_50 = l_Lean_Expr_isConstOf(x_42, x_49);
if (x_50 == 0)
{
lean_object* x_51; uint8_t x_52; 
x_51 = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__13));
x_52 = l_Lean_Expr_isConstOf(x_42, x_51);
if (x_52 == 0)
{
uint8_t x_53; 
x_53 = l_Lean_Expr_isApp(x_42);
if (x_53 == 0)
{
lean_dec_ref(x_42);
lean_dec_ref(x_41);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
goto block_23;
}
else
{
lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_54 = l_Lean_Expr_appFnCleanup___redArg(x_42);
x_55 = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_go___closed__9));
x_56 = l_Lean_Expr_isConstOf(x_54, x_55);
if (x_56 == 0)
{
lean_object* x_57; uint8_t x_58; 
x_57 = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__15));
x_58 = l_Lean_Expr_isConstOf(x_54, x_57);
if (x_58 == 0)
{
lean_object* x_59; uint8_t x_60; 
lean_dec_ref(x_41);
x_59 = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__17));
x_60 = l_Lean_Expr_isConstOf(x_54, x_59);
if (x_60 == 0)
{
uint8_t x_61; 
x_61 = l_Lean_Expr_isApp(x_54);
if (x_61 == 0)
{
lean_dec_ref(x_54);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
goto block_23;
}
else
{
lean_object* x_62; lean_object* x_63; uint8_t x_64; 
x_62 = lean_ctor_get(x_54, 1);
lean_inc_ref(x_62);
x_63 = l_Lean_Expr_appFnCleanup___redArg(x_54);
x_64 = l_Lean_Expr_isApp(x_63);
if (x_64 == 0)
{
lean_dec_ref(x_63);
lean_dec_ref(x_62);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
goto block_23;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_65 = lean_ctor_get(x_63, 1);
lean_inc_ref(x_65);
x_66 = l_Lean_Expr_appFnCleanup___redArg(x_63);
x_67 = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__20));
x_68 = l_Lean_Expr_isConstOf(x_66, x_67);
if (x_68 == 0)
{
lean_object* x_69; uint8_t x_70; 
x_69 = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__23));
x_70 = l_Lean_Expr_isConstOf(x_66, x_69);
if (x_70 == 0)
{
lean_object* x_71; uint8_t x_72; 
x_71 = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__26));
x_72 = l_Lean_Expr_isConstOf(x_66, x_71);
if (x_72 == 0)
{
lean_object* x_73; uint8_t x_74; 
lean_dec_ref(x_65);
lean_dec_ref(x_62);
x_73 = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__29));
x_74 = l_Lean_Expr_isConstOf(x_66, x_73);
if (x_74 == 0)
{
lean_object* x_75; uint8_t x_76; 
x_75 = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__32));
x_76 = l_Lean_Expr_isConstOf(x_66, x_75);
if (x_76 == 0)
{
lean_object* x_77; uint8_t x_78; 
x_77 = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__35));
x_78 = l_Lean_Expr_isConstOf(x_66, x_77);
if (x_78 == 0)
{
lean_object* x_79; uint8_t x_80; 
x_79 = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__38));
x_80 = l_Lean_Expr_isConstOf(x_66, x_79);
if (x_80 == 0)
{
lean_object* x_81; uint8_t x_82; 
x_81 = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__41));
x_82 = l_Lean_Expr_isConstOf(x_66, x_81);
if (x_82 == 0)
{
lean_object* x_83; uint8_t x_84; 
x_83 = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__44));
x_84 = l_Lean_Expr_isConstOf(x_66, x_83);
lean_dec_ref(x_66);
if (x_84 == 0)
{
lean_dec_ref(x_29);
lean_dec_ref(x_26);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
goto block_23;
}
else
{
uint8_t x_85; lean_object* x_86; lean_object* x_87; 
lean_del_object(x_17);
x_85 = 0;
x_86 = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__46));
x_87 = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection(x_29, x_26, x_85, x_86, x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_87;
}
}
else
{
uint8_t x_88; lean_object* x_89; lean_object* x_90; 
lean_dec_ref(x_66);
lean_del_object(x_17);
x_88 = 2;
x_89 = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__48));
x_90 = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection(x_29, x_26, x_88, x_89, x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_90;
}
}
else
{
uint8_t x_91; lean_object* x_92; lean_object* x_93; 
lean_dec_ref(x_66);
lean_del_object(x_17);
x_91 = 3;
x_92 = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__50));
x_93 = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection(x_29, x_26, x_91, x_92, x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_93;
}
}
else
{
uint8_t x_94; lean_object* x_95; lean_object* x_96; 
lean_dec_ref(x_66);
lean_del_object(x_17);
x_94 = 4;
x_95 = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__52));
x_96 = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection(x_29, x_26, x_94, x_95, x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_96;
}
}
else
{
uint8_t x_97; lean_object* x_98; lean_object* x_99; 
lean_dec_ref(x_66);
lean_del_object(x_17);
x_97 = 5;
x_98 = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__54));
x_99 = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection(x_29, x_26, x_97, x_98, x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_99;
}
}
else
{
uint8_t x_100; lean_object* x_101; lean_object* x_102; 
lean_dec_ref(x_66);
lean_del_object(x_17);
x_100 = 6;
x_101 = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__56));
x_102 = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection(x_29, x_26, x_100, x_101, x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_102;
}
}
else
{
lean_object* x_103; 
lean_dec_ref(x_66);
lean_del_object(x_17);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc_ref(x_26);
lean_inc_ref(x_62);
x_103 = l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_getNatOrBvValue_x3f___redArg(x_62, x_26, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; lean_object* x_105; uint8_t x_106; uint8_t x_157; 
x_104 = lean_ctor_get(x_103, 0);
x_157 = !lean_is_exclusive(x_103);
if (x_157 == 0)
{
x_105 = x_103;
x_106 = x_157;
goto block_156;
}
else
{
lean_inc(x_104);
lean_dec(x_103);
x_105 = lean_box(0);
x_106 = x_157;
goto block_156;
}
block_156:
{
lean_object* x_112; uint8_t x_113; 
x_112 = l_Lean_Expr_cleanupAnnotations(x_65);
x_113 = l_Lean_Expr_isApp(x_112);
if (x_113 == 0)
{
lean_dec_ref(x_112);
lean_dec(x_104);
lean_dec_ref(x_62);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
goto block_111;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; uint8_t x_117; 
x_114 = lean_ctor_get(x_112, 1);
lean_inc_ref(x_114);
x_115 = l_Lean_Expr_appFnCleanup___redArg(x_112);
x_116 = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_of_go___closed__8));
x_117 = l_Lean_Expr_isConstOf(x_115, x_116);
lean_dec_ref(x_115);
if (x_117 == 0)
{
lean_dec_ref(x_114);
lean_dec(x_104);
lean_dec_ref(x_62);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
goto block_111;
}
else
{
lean_object* x_118; 
lean_del_object(x_105);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_118 = l_Lean_Meta_getNatValue_x3f(x_114, x_4, x_5, x_6, x_7);
lean_dec_ref(x_114);
if (lean_obj_tag(x_118) == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; uint8_t x_146; 
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
lean_dec_ref(x_118);
x_120 = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__57));
if (lean_obj_tag(x_119) == 0)
{
x_146 = x_70;
goto block_147;
}
else
{
lean_dec_ref(x_119);
x_146 = x_117;
goto block_147;
}
block_134:
{
lean_object* x_127; uint8_t x_128; 
x_127 = l_Lean_Expr_cleanupAnnotations(x_62);
x_128 = l_Lean_Expr_isApp(x_127);
if (x_128 == 0)
{
lean_dec_ref(x_127);
lean_dec(x_126);
lean_dec_ref(x_125);
lean_dec(x_124);
lean_dec_ref(x_123);
lean_dec(x_122);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
lean_dec_ref(x_1);
goto block_11;
}
else
{
lean_object* x_129; uint8_t x_130; 
x_129 = l_Lean_Expr_appFnCleanup___redArg(x_127);
x_130 = l_Lean_Expr_isConstOf(x_129, x_116);
lean_dec_ref(x_129);
if (x_130 == 0)
{
lean_dec(x_126);
lean_dec_ref(x_125);
lean_dec(x_124);
lean_dec_ref(x_123);
lean_dec(x_122);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
lean_dec_ref(x_1);
goto block_11;
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_131 = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__59));
x_132 = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__61));
x_133 = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftReflection(x_26, x_29, x_120, x_131, x_132, x_1, x_121, x_122, x_123, x_124, x_125, x_126);
return x_133;
}
}
}
block_145:
{
lean_object* x_135; lean_object* x_136; 
x_135 = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__63, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__63_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__63);
x_136 = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go_spec__12___redArg(x_135, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_136) == 0)
{
lean_dec_ref(x_136);
x_121 = x_2;
x_122 = x_3;
x_123 = x_4;
x_124 = x_5;
x_125 = x_6;
x_126 = x_7;
goto block_134;
}
else
{
lean_object* x_137; lean_object* x_138; uint8_t x_139; uint8_t x_144; 
lean_dec_ref(x_62);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_137 = lean_ctor_get(x_136, 0);
x_144 = !lean_is_exclusive(x_136);
if (x_144 == 0)
{
x_138 = x_136;
x_139 = x_144;
goto block_143;
}
else
{
lean_inc(x_137);
lean_dec(x_136);
x_138 = lean_box(0);
x_139 = x_144;
goto block_143;
}
block_143:
{
lean_object* x_140; 
if (x_139 == 0)
{
x_140 = x_138;
goto block_141;
}
else
{
lean_object* x_142; 
x_142 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_142, 0, x_137);
x_140 = x_142;
goto block_141;
}
block_141:
{
return x_140;
}
}
}
}
block_147:
{
if (x_146 == 0)
{
lean_dec(x_104);
x_121 = x_2;
x_122 = x_3;
x_123 = x_4;
x_124 = x_5;
x_125 = x_6;
x_126 = x_7;
goto block_134;
}
else
{
if (lean_obj_tag(x_104) == 0)
{
if (x_70 == 0)
{
x_121 = x_2;
x_122 = x_3;
x_123 = x_4;
x_124 = x_5;
x_125 = x_6;
x_126 = x_7;
goto block_134;
}
else
{
goto block_145;
}
}
else
{
lean_dec_ref(x_104);
goto block_145;
}
}
}
}
else
{
lean_object* x_148; lean_object* x_149; uint8_t x_150; uint8_t x_155; 
lean_dec(x_104);
lean_dec_ref(x_62);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_148 = lean_ctor_get(x_118, 0);
x_155 = !lean_is_exclusive(x_118);
if (x_155 == 0)
{
x_149 = x_118;
x_150 = x_155;
goto block_154;
}
else
{
lean_inc(x_148);
lean_dec(x_118);
x_149 = lean_box(0);
x_150 = x_155;
goto block_154;
}
block_154:
{
lean_object* x_151; 
if (x_150 == 0)
{
x_151 = x_149;
goto block_152;
}
else
{
lean_object* x_153; 
x_153 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_153, 0, x_148);
x_151 = x_153;
goto block_152;
}
block_152:
{
return x_151;
}
}
}
}
}
block_111:
{
lean_object* x_107; lean_object* x_108; 
x_107 = lean_box(0);
if (x_106 == 0)
{
lean_ctor_set(x_105, 0, x_107);
x_108 = x_105;
goto block_109;
}
else
{
lean_object* x_110; 
x_110 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_110, 0, x_107);
x_108 = x_110;
goto block_109;
}
block_109:
{
return x_108;
}
}
}
}
else
{
lean_object* x_158; lean_object* x_159; uint8_t x_160; uint8_t x_165; 
lean_dec_ref(x_65);
lean_dec_ref(x_62);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_158 = lean_ctor_get(x_103, 0);
x_165 = !lean_is_exclusive(x_103);
if (x_165 == 0)
{
x_159 = x_103;
x_160 = x_165;
goto block_164;
}
else
{
lean_inc(x_158);
lean_dec(x_103);
x_159 = lean_box(0);
x_160 = x_165;
goto block_164;
}
block_164:
{
lean_object* x_161; 
if (x_160 == 0)
{
x_161 = x_159;
goto block_162;
}
else
{
lean_object* x_163; 
x_163 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_163, 0, x_158);
x_161 = x_163;
goto block_162;
}
block_162:
{
return x_161;
}
}
}
}
}
else
{
lean_object* x_166; 
lean_dec_ref(x_66);
lean_del_object(x_17);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc_ref(x_26);
lean_inc_ref(x_62);
x_166 = l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_getNatOrBvValue_x3f___redArg(x_62, x_26, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_166) == 0)
{
lean_object* x_167; lean_object* x_168; uint8_t x_169; uint8_t x_220; 
x_167 = lean_ctor_get(x_166, 0);
x_220 = !lean_is_exclusive(x_166);
if (x_220 == 0)
{
x_168 = x_166;
x_169 = x_220;
goto block_219;
}
else
{
lean_inc(x_167);
lean_dec(x_166);
x_168 = lean_box(0);
x_169 = x_220;
goto block_219;
}
block_219:
{
lean_object* x_175; uint8_t x_176; 
x_175 = l_Lean_Expr_cleanupAnnotations(x_65);
x_176 = l_Lean_Expr_isApp(x_175);
if (x_176 == 0)
{
lean_dec_ref(x_175);
lean_dec(x_167);
lean_dec_ref(x_62);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
goto block_174;
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; uint8_t x_180; 
x_177 = lean_ctor_get(x_175, 1);
lean_inc_ref(x_177);
x_178 = l_Lean_Expr_appFnCleanup___redArg(x_175);
x_179 = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_of_go___closed__8));
x_180 = l_Lean_Expr_isConstOf(x_178, x_179);
lean_dec_ref(x_178);
if (x_180 == 0)
{
lean_dec_ref(x_177);
lean_dec(x_167);
lean_dec_ref(x_62);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
goto block_174;
}
else
{
lean_object* x_181; 
lean_del_object(x_168);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_181 = l_Lean_Meta_getNatValue_x3f(x_177, x_4, x_5, x_6, x_7);
lean_dec_ref(x_177);
if (lean_obj_tag(x_181) == 0)
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; uint8_t x_209; 
x_182 = lean_ctor_get(x_181, 0);
lean_inc(x_182);
lean_dec_ref(x_181);
x_183 = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__64));
if (lean_obj_tag(x_182) == 0)
{
x_209 = x_68;
goto block_210;
}
else
{
lean_dec_ref(x_182);
x_209 = x_180;
goto block_210;
}
block_197:
{
lean_object* x_190; uint8_t x_191; 
x_190 = l_Lean_Expr_cleanupAnnotations(x_62);
x_191 = l_Lean_Expr_isApp(x_190);
if (x_191 == 0)
{
lean_dec_ref(x_190);
lean_dec(x_189);
lean_dec_ref(x_188);
lean_dec(x_187);
lean_dec_ref(x_186);
lean_dec(x_185);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
lean_dec_ref(x_1);
goto block_14;
}
else
{
lean_object* x_192; uint8_t x_193; 
x_192 = l_Lean_Expr_appFnCleanup___redArg(x_190);
x_193 = l_Lean_Expr_isConstOf(x_192, x_179);
lean_dec_ref(x_192);
if (x_193 == 0)
{
lean_dec(x_189);
lean_dec_ref(x_188);
lean_dec(x_187);
lean_dec_ref(x_186);
lean_dec(x_185);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
lean_dec_ref(x_1);
goto block_14;
}
else
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; 
x_194 = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__66));
x_195 = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__68));
x_196 = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftReflection(x_26, x_29, x_183, x_194, x_195, x_1, x_184, x_185, x_186, x_187, x_188, x_189);
return x_196;
}
}
}
block_208:
{
lean_object* x_198; lean_object* x_199; 
x_198 = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__63, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__63_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__63);
x_199 = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go_spec__12___redArg(x_198, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_199) == 0)
{
lean_dec_ref(x_199);
x_184 = x_2;
x_185 = x_3;
x_186 = x_4;
x_187 = x_5;
x_188 = x_6;
x_189 = x_7;
goto block_197;
}
else
{
lean_object* x_200; lean_object* x_201; uint8_t x_202; uint8_t x_207; 
lean_dec_ref(x_62);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_200 = lean_ctor_get(x_199, 0);
x_207 = !lean_is_exclusive(x_199);
if (x_207 == 0)
{
x_201 = x_199;
x_202 = x_207;
goto block_206;
}
else
{
lean_inc(x_200);
lean_dec(x_199);
x_201 = lean_box(0);
x_202 = x_207;
goto block_206;
}
block_206:
{
lean_object* x_203; 
if (x_202 == 0)
{
x_203 = x_201;
goto block_204;
}
else
{
lean_object* x_205; 
x_205 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_205, 0, x_200);
x_203 = x_205;
goto block_204;
}
block_204:
{
return x_203;
}
}
}
}
block_210:
{
if (x_209 == 0)
{
lean_dec(x_167);
x_184 = x_2;
x_185 = x_3;
x_186 = x_4;
x_187 = x_5;
x_188 = x_6;
x_189 = x_7;
goto block_197;
}
else
{
if (lean_obj_tag(x_167) == 0)
{
if (x_68 == 0)
{
x_184 = x_2;
x_185 = x_3;
x_186 = x_4;
x_187 = x_5;
x_188 = x_6;
x_189 = x_7;
goto block_197;
}
else
{
goto block_208;
}
}
else
{
lean_dec_ref(x_167);
goto block_208;
}
}
}
}
else
{
lean_object* x_211; lean_object* x_212; uint8_t x_213; uint8_t x_218; 
lean_dec(x_167);
lean_dec_ref(x_62);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_211 = lean_ctor_get(x_181, 0);
x_218 = !lean_is_exclusive(x_181);
if (x_218 == 0)
{
x_212 = x_181;
x_213 = x_218;
goto block_217;
}
else
{
lean_inc(x_211);
lean_dec(x_181);
x_212 = lean_box(0);
x_213 = x_218;
goto block_217;
}
block_217:
{
lean_object* x_214; 
if (x_213 == 0)
{
x_214 = x_212;
goto block_215;
}
else
{
lean_object* x_216; 
x_216 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_216, 0, x_211);
x_214 = x_216;
goto block_215;
}
block_215:
{
return x_214;
}
}
}
}
}
block_174:
{
lean_object* x_170; lean_object* x_171; 
x_170 = lean_box(0);
if (x_169 == 0)
{
lean_ctor_set(x_168, 0, x_170);
x_171 = x_168;
goto block_172;
}
else
{
lean_object* x_173; 
x_173 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_173, 0, x_170);
x_171 = x_173;
goto block_172;
}
block_172:
{
return x_171;
}
}
}
}
else
{
lean_object* x_221; lean_object* x_222; uint8_t x_223; uint8_t x_228; 
lean_dec_ref(x_65);
lean_dec_ref(x_62);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_221 = lean_ctor_get(x_166, 0);
x_228 = !lean_is_exclusive(x_166);
if (x_228 == 0)
{
x_222 = x_166;
x_223 = x_228;
goto block_227;
}
else
{
lean_inc(x_221);
lean_dec(x_166);
x_222 = lean_box(0);
x_223 = x_228;
goto block_227;
}
block_227:
{
lean_object* x_224; 
if (x_223 == 0)
{
x_224 = x_222;
goto block_225;
}
else
{
lean_object* x_226; 
x_226 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_226, 0, x_221);
x_224 = x_226;
goto block_225;
}
block_225:
{
return x_224;
}
}
}
}
}
else
{
lean_object* x_229; 
lean_dec_ref(x_66);
lean_dec_ref(x_65);
lean_dec_ref(x_62);
lean_del_object(x_17);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_29);
x_229 = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_goOrAtom(x_29, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_229) == 0)
{
lean_object* x_230; lean_object* x_231; uint8_t x_232; uint8_t x_293; 
x_230 = lean_ctor_get(x_229, 0);
x_293 = !lean_is_exclusive(x_229);
if (x_293 == 0)
{
x_231 = x_229;
x_232 = x_293;
goto block_292;
}
else
{
lean_inc(x_230);
lean_dec(x_229);
x_231 = lean_box(0);
x_232 = x_293;
goto block_292;
}
block_292:
{
if (lean_obj_tag(x_230) == 1)
{
lean_object* x_233; lean_object* x_234; 
lean_del_object(x_231);
x_233 = lean_ctor_get(x_230, 0);
lean_inc(x_233);
lean_dec_ref(x_230);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc_ref(x_26);
x_234 = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_goOrAtom(x_26, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_234) == 0)
{
lean_object* x_235; lean_object* x_236; uint8_t x_237; uint8_t x_287; 
x_235 = lean_ctor_get(x_234, 0);
x_287 = !lean_is_exclusive(x_234);
if (x_287 == 0)
{
x_236 = x_234;
x_237 = x_287;
goto block_286;
}
else
{
lean_inc(x_235);
lean_dec(x_234);
x_236 = lean_box(0);
x_237 = x_287;
goto block_286;
}
block_286:
{
if (lean_obj_tag(x_235) == 1)
{
lean_object* x_238; lean_object* x_239; uint8_t x_240; uint8_t x_281; 
lean_del_object(x_236);
x_238 = lean_ctor_get(x_235, 0);
x_281 = !lean_is_exclusive(x_235);
if (x_281 == 0)
{
x_239 = x_235;
x_240 = x_281;
goto block_280;
}
else
{
lean_inc(x_238);
lean_dec(x_235);
x_239 = lean_box(0);
x_240 = x_281;
goto block_280;
}
block_280:
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; 
x_241 = lean_ctor_get(x_233, 0);
lean_inc(x_241);
x_242 = lean_ctor_get(x_233, 1);
x_243 = lean_ctor_get(x_233, 4);
lean_inc_ref(x_243);
x_244 = lean_ctor_get(x_238, 0);
lean_inc(x_244);
x_245 = lean_ctor_get(x_238, 1);
x_246 = lean_ctor_get(x_238, 4);
lean_inc_ref(x_246);
x_247 = lean_nat_add(x_241, x_244);
lean_inc_ref(x_245);
lean_inc_ref(x_242);
lean_inc(x_247);
lean_inc(x_244);
lean_inc(x_241);
x_248 = l_Std_Tactic_BVDecide_BVExpr_append___override___redArg(x_241, x_244, x_247, x_242, x_245);
lean_inc(x_247);
x_249 = l_Lean_mkNatLit(x_247);
lean_inc_ref(x_249);
x_250 = l_Lean_Meta_mkEqRefl(x_249, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_250) == 0)
{
lean_object* x_251; lean_object* x_252; uint8_t x_253; uint8_t x_271; 
x_251 = lean_ctor_get(x_250, 0);
x_271 = !lean_is_exclusive(x_250);
if (x_271 == 0)
{
x_252 = x_250;
x_253 = x_271;
goto block_270;
}
else
{
lean_inc(x_251);
lean_dec(x_250);
x_252 = lean_box(0);
x_253 = x_271;
goto block_270;
}
block_270:
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; 
x_254 = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0));
x_255 = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1));
x_256 = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2));
x_257 = lean_box(0);
x_258 = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__71, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__71_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__71);
lean_inc(x_241);
x_259 = l_Lean_mkNatLit(x_241);
lean_inc(x_244);
x_260 = l_Lean_mkNatLit(x_244);
lean_inc_ref(x_260);
lean_inc_ref(x_259);
lean_inc_ref(x_246);
lean_inc_ref(x_243);
x_261 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___lam__0___boxed), 21, 15);
lean_closure_set(x_261, 0, x_241);
lean_closure_set(x_261, 1, x_243);
lean_closure_set(x_261, 2, x_244);
lean_closure_set(x_261, 3, x_246);
lean_closure_set(x_261, 4, x_233);
lean_closure_set(x_261, 5, x_238);
lean_closure_set(x_261, 6, x_254);
lean_closure_set(x_261, 7, x_255);
lean_closure_set(x_261, 8, x_256);
lean_closure_set(x_261, 9, x_31);
lean_closure_set(x_261, 10, x_257);
lean_closure_set(x_261, 11, x_259);
lean_closure_set(x_261, 12, x_260);
lean_closure_set(x_261, 13, x_29);
lean_closure_set(x_261, 14, x_26);
x_262 = l_Lean_mkApp6(x_258, x_259, x_260, x_249, x_243, x_246, x_251);
x_263 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_263, 0, x_247);
lean_ctor_set(x_263, 1, x_248);
lean_ctor_set(x_263, 2, x_1);
lean_ctor_set(x_263, 3, x_261);
lean_ctor_set(x_263, 4, x_262);
if (x_240 == 0)
{
lean_ctor_set(x_239, 0, x_263);
x_264 = x_239;
goto block_268;
}
else
{
lean_object* x_269; 
x_269 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_269, 0, x_263);
x_264 = x_269;
goto block_268;
}
block_268:
{
lean_object* x_265; 
if (x_253 == 0)
{
lean_ctor_set(x_252, 0, x_264);
x_265 = x_252;
goto block_266;
}
else
{
lean_object* x_267; 
x_267 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_267, 0, x_264);
x_265 = x_267;
goto block_266;
}
block_266:
{
return x_265;
}
}
}
}
else
{
lean_object* x_272; lean_object* x_273; uint8_t x_274; uint8_t x_279; 
lean_dec_ref(x_249);
lean_dec_ref(x_248);
lean_dec(x_247);
lean_dec_ref(x_246);
lean_dec(x_244);
lean_dec_ref(x_243);
lean_dec(x_241);
lean_del_object(x_239);
lean_dec(x_238);
lean_dec(x_233);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
lean_dec_ref(x_1);
x_272 = lean_ctor_get(x_250, 0);
x_279 = !lean_is_exclusive(x_250);
if (x_279 == 0)
{
x_273 = x_250;
x_274 = x_279;
goto block_278;
}
else
{
lean_inc(x_272);
lean_dec(x_250);
x_273 = lean_box(0);
x_274 = x_279;
goto block_278;
}
block_278:
{
lean_object* x_275; 
if (x_274 == 0)
{
x_275 = x_273;
goto block_276;
}
else
{
lean_object* x_277; 
x_277 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_277, 0, x_272);
x_275 = x_277;
goto block_276;
}
block_276:
{
return x_275;
}
}
}
}
}
else
{
lean_object* x_282; lean_object* x_283; 
lean_dec(x_235);
lean_dec(x_233);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_282 = lean_box(0);
if (x_237 == 0)
{
lean_ctor_set(x_236, 0, x_282);
x_283 = x_236;
goto block_284;
}
else
{
lean_object* x_285; 
x_285 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_285, 0, x_282);
x_283 = x_285;
goto block_284;
}
block_284:
{
return x_283;
}
}
}
}
else
{
lean_dec(x_233);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
return x_234;
}
}
else
{
lean_object* x_288; lean_object* x_289; 
lean_dec(x_230);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_288 = lean_box(0);
if (x_232 == 0)
{
lean_ctor_set(x_231, 0, x_288);
x_289 = x_231;
goto block_290;
}
else
{
lean_object* x_291; 
x_291 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_291, 0, x_288);
x_289 = x_291;
goto block_290;
}
block_290:
{
return x_289;
}
}
}
}
else
{
lean_dec_ref(x_29);
lean_dec_ref(x_26);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
return x_229;
}
}
}
}
}
else
{
lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; 
lean_dec_ref(x_54);
lean_del_object(x_17);
x_294 = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__72));
x_295 = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__74));
x_296 = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__76));
x_297 = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftReflection(x_26, x_29, x_294, x_295, x_296, x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_297;
}
}
else
{
lean_object* x_298; 
lean_dec_ref(x_54);
lean_del_object(x_17);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_298 = l_Lean_Meta_getNatValue_x3f(x_41, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_298) == 0)
{
lean_object* x_299; lean_object* x_300; uint8_t x_301; uint8_t x_361; 
x_299 = lean_ctor_get(x_298, 0);
x_361 = !lean_is_exclusive(x_298);
if (x_361 == 0)
{
x_300 = x_298;
x_301 = x_361;
goto block_360;
}
else
{
lean_inc(x_299);
lean_dec(x_298);
x_300 = lean_box(0);
x_301 = x_361;
goto block_360;
}
block_360:
{
if (lean_obj_tag(x_299) == 1)
{
lean_object* x_302; lean_object* x_303; 
lean_del_object(x_300);
x_302 = lean_ctor_get(x_299, 0);
lean_inc(x_302);
lean_dec_ref(x_299);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_303 = l_Lean_Meta_getNatValue_x3f(x_29, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_303) == 0)
{
lean_object* x_304; lean_object* x_305; uint8_t x_306; uint8_t x_347; 
x_304 = lean_ctor_get(x_303, 0);
x_347 = !lean_is_exclusive(x_303);
if (x_347 == 0)
{
x_305 = x_303;
x_306 = x_347;
goto block_346;
}
else
{
lean_inc(x_304);
lean_dec(x_303);
x_305 = lean_box(0);
x_306 = x_347;
goto block_346;
}
block_346:
{
if (lean_obj_tag(x_304) == 1)
{
lean_object* x_307; lean_object* x_308; 
lean_del_object(x_305);
x_307 = lean_ctor_get(x_304, 0);
lean_inc(x_307);
lean_dec_ref(x_304);
lean_inc_ref(x_26);
x_308 = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_goOrAtom(x_26, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_308) == 0)
{
lean_object* x_309; lean_object* x_310; uint8_t x_311; uint8_t x_341; 
x_309 = lean_ctor_get(x_308, 0);
x_341 = !lean_is_exclusive(x_308);
if (x_341 == 0)
{
x_310 = x_308;
x_311 = x_341;
goto block_340;
}
else
{
lean_inc(x_309);
lean_dec(x_308);
x_310 = lean_box(0);
x_311 = x_341;
goto block_340;
}
block_340:
{
if (lean_obj_tag(x_309) == 1)
{
lean_object* x_312; lean_object* x_313; uint8_t x_314; uint8_t x_335; 
x_312 = lean_ctor_get(x_309, 0);
x_335 = !lean_is_exclusive(x_309);
if (x_335 == 0)
{
x_313 = x_309;
x_314 = x_335;
goto block_334;
}
else
{
lean_inc(x_312);
lean_dec(x_309);
x_313 = lean_box(0);
x_314 = x_335;
goto block_334;
}
block_334:
{
lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; 
x_315 = lean_ctor_get(x_312, 0);
lean_inc(x_315);
x_316 = lean_ctor_get(x_312, 1);
x_317 = lean_ctor_get(x_312, 4);
lean_inc_ref(x_317);
lean_inc_ref(x_316);
lean_inc(x_307);
lean_inc(x_315);
x_318 = l_Std_Tactic_BVDecide_BVExpr_extract___override(x_315, x_302, x_307, x_316);
x_319 = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0));
x_320 = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1));
x_321 = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2));
x_322 = lean_box(0);
x_323 = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__79, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__79_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__79);
lean_inc(x_315);
x_324 = l_Lean_mkNatLit(x_315);
lean_inc_ref(x_324);
lean_inc_ref(x_29);
lean_inc_ref(x_41);
lean_inc_ref(x_317);
x_325 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___lam__1___boxed), 18, 12);
lean_closure_set(x_325, 0, x_315);
lean_closure_set(x_325, 1, x_317);
lean_closure_set(x_325, 2, x_312);
lean_closure_set(x_325, 3, x_319);
lean_closure_set(x_325, 4, x_320);
lean_closure_set(x_325, 5, x_321);
lean_closure_set(x_325, 6, x_31);
lean_closure_set(x_325, 7, x_322);
lean_closure_set(x_325, 8, x_41);
lean_closure_set(x_325, 9, x_29);
lean_closure_set(x_325, 10, x_324);
lean_closure_set(x_325, 11, x_26);
x_326 = l_Lean_mkApp4(x_323, x_324, x_41, x_29, x_317);
x_327 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_327, 0, x_307);
lean_ctor_set(x_327, 1, x_318);
lean_ctor_set(x_327, 2, x_1);
lean_ctor_set(x_327, 3, x_325);
lean_ctor_set(x_327, 4, x_326);
if (x_314 == 0)
{
lean_ctor_set(x_313, 0, x_327);
x_328 = x_313;
goto block_332;
}
else
{
lean_object* x_333; 
x_333 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_333, 0, x_327);
x_328 = x_333;
goto block_332;
}
block_332:
{
lean_object* x_329; 
if (x_311 == 0)
{
lean_ctor_set(x_310, 0, x_328);
x_329 = x_310;
goto block_330;
}
else
{
lean_object* x_331; 
x_331 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_331, 0, x_328);
x_329 = x_331;
goto block_330;
}
block_330:
{
return x_329;
}
}
}
}
else
{
lean_object* x_336; lean_object* x_337; 
lean_dec(x_309);
lean_dec(x_307);
lean_dec(x_302);
lean_dec_ref(x_41);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
lean_dec_ref(x_1);
x_336 = lean_box(0);
if (x_311 == 0)
{
lean_ctor_set(x_310, 0, x_336);
x_337 = x_310;
goto block_338;
}
else
{
lean_object* x_339; 
x_339 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_339, 0, x_336);
x_337 = x_339;
goto block_338;
}
block_338:
{
return x_337;
}
}
}
}
else
{
lean_dec(x_307);
lean_dec(x_302);
lean_dec_ref(x_41);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
lean_dec_ref(x_1);
return x_308;
}
}
else
{
lean_object* x_342; lean_object* x_343; 
lean_dec(x_304);
lean_dec(x_302);
lean_dec_ref(x_41);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_342 = lean_box(0);
if (x_306 == 0)
{
lean_ctor_set(x_305, 0, x_342);
x_343 = x_305;
goto block_344;
}
else
{
lean_object* x_345; 
x_345 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_345, 0, x_342);
x_343 = x_345;
goto block_344;
}
block_344:
{
return x_343;
}
}
}
}
else
{
lean_object* x_348; lean_object* x_349; uint8_t x_350; uint8_t x_355; 
lean_dec(x_302);
lean_dec_ref(x_41);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_348 = lean_ctor_get(x_303, 0);
x_355 = !lean_is_exclusive(x_303);
if (x_355 == 0)
{
x_349 = x_303;
x_350 = x_355;
goto block_354;
}
else
{
lean_inc(x_348);
lean_dec(x_303);
x_349 = lean_box(0);
x_350 = x_355;
goto block_354;
}
block_354:
{
lean_object* x_351; 
if (x_350 == 0)
{
x_351 = x_349;
goto block_352;
}
else
{
lean_object* x_353; 
x_353 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_353, 0, x_348);
x_351 = x_353;
goto block_352;
}
block_352:
{
return x_351;
}
}
}
}
else
{
lean_object* x_356; lean_object* x_357; 
lean_dec(x_299);
lean_dec_ref(x_41);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_356 = lean_box(0);
if (x_301 == 0)
{
lean_ctor_set(x_300, 0, x_356);
x_357 = x_300;
goto block_358;
}
else
{
lean_object* x_359; 
x_359 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_359, 0, x_356);
x_357 = x_359;
goto block_358;
}
block_358:
{
return x_357;
}
}
}
}
else
{
lean_object* x_362; lean_object* x_363; uint8_t x_364; uint8_t x_369; 
lean_dec_ref(x_41);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_362 = lean_ctor_get(x_298, 0);
x_369 = !lean_is_exclusive(x_298);
if (x_369 == 0)
{
x_363 = x_298;
x_364 = x_369;
goto block_368;
}
else
{
lean_inc(x_362);
lean_dec(x_298);
x_363 = lean_box(0);
x_364 = x_369;
goto block_368;
}
block_368:
{
lean_object* x_365; 
if (x_364 == 0)
{
x_365 = x_363;
goto block_366;
}
else
{
lean_object* x_367; 
x_367 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_367, 0, x_362);
x_365 = x_367;
goto block_366;
}
block_366:
{
return x_365;
}
}
}
}
}
else
{
lean_object* x_370; 
lean_dec_ref(x_54);
lean_del_object(x_17);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_1);
x_370 = l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_bitVecAtom(x_1, x_56, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_370) == 0)
{
lean_object* x_371; lean_object* x_372; uint8_t x_373; uint8_t x_438; 
x_371 = lean_ctor_get(x_370, 0);
x_438 = !lean_is_exclusive(x_370);
if (x_438 == 0)
{
x_372 = x_370;
x_373 = x_438;
goto block_437;
}
else
{
lean_inc(x_371);
lean_dec(x_370);
x_372 = lean_box(0);
x_373 = x_438;
goto block_437;
}
block_437:
{
if (lean_obj_tag(x_371) == 1)
{
lean_object* x_374; lean_object* x_375; 
lean_del_object(x_372);
x_374 = lean_ctor_get(x_371, 0);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_41);
x_375 = l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of(x_41, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_375) == 0)
{
lean_object* x_376; lean_object* x_377; uint8_t x_378; uint8_t x_424; 
x_376 = lean_ctor_get(x_375, 0);
x_424 = !lean_is_exclusive(x_375);
if (x_424 == 0)
{
x_377 = x_375;
x_378 = x_424;
goto block_423;
}
else
{
lean_inc(x_376);
lean_dec(x_375);
x_377 = lean_box(0);
x_378 = x_424;
goto block_423;
}
block_423:
{
if (lean_obj_tag(x_376) == 1)
{
lean_object* x_379; lean_object* x_380; 
lean_del_object(x_377);
x_379 = lean_ctor_get(x_376, 0);
lean_inc(x_379);
lean_dec_ref(x_376);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_29);
x_380 = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_goOrAtom(x_29, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_380) == 0)
{
lean_object* x_381; lean_object* x_382; uint8_t x_383; uint8_t x_418; 
x_381 = lean_ctor_get(x_380, 0);
x_418 = !lean_is_exclusive(x_380);
if (x_418 == 0)
{
x_382 = x_380;
x_383 = x_418;
goto block_417;
}
else
{
lean_inc(x_381);
lean_dec(x_380);
x_382 = lean_box(0);
x_383 = x_418;
goto block_417;
}
block_417:
{
if (lean_obj_tag(x_381) == 1)
{
lean_object* x_384; lean_object* x_385; 
lean_del_object(x_382);
x_384 = lean_ctor_get(x_381, 0);
lean_inc(x_384);
lean_dec_ref(x_381);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc_ref(x_26);
x_385 = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_goOrAtom(x_26, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_385) == 0)
{
lean_object* x_386; lean_object* x_387; uint8_t x_388; uint8_t x_412; 
x_386 = lean_ctor_get(x_385, 0);
x_412 = !lean_is_exclusive(x_385);
if (x_412 == 0)
{
x_387 = x_385;
x_388 = x_412;
goto block_411;
}
else
{
lean_inc(x_386);
lean_dec(x_385);
x_387 = lean_box(0);
x_388 = x_412;
goto block_411;
}
block_411:
{
if (lean_obj_tag(x_386) == 1)
{
lean_object* x_389; lean_object* x_390; 
lean_del_object(x_387);
x_389 = lean_ctor_get(x_386, 0);
lean_inc(x_389);
lean_dec_ref(x_386);
lean_inc(x_374);
x_390 = l_Lean_Elab_Tactic_BVDecide_Frontend_addCondLemmas___redArg(x_379, x_374, x_384, x_389, x_41, x_1, x_29, x_26, x_2, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_390) == 0)
{
lean_object* x_391; uint8_t x_392; uint8_t x_397; 
x_397 = !lean_is_exclusive(x_390);
if (x_397 == 0)
{
lean_object* x_398; 
x_398 = lean_ctor_get(x_390, 0);
lean_dec(x_398);
x_391 = x_390;
x_392 = x_397;
goto block_396;
}
else
{
lean_dec(x_390);
x_391 = lean_box(0);
x_392 = x_397;
goto block_396;
}
block_396:
{
lean_object* x_393; 
if (x_392 == 0)
{
lean_ctor_set(x_391, 0, x_371);
x_393 = x_391;
goto block_394;
}
else
{
lean_object* x_395; 
x_395 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_395, 0, x_371);
x_393 = x_395;
goto block_394;
}
block_394:
{
return x_393;
}
}
}
else
{
lean_object* x_399; lean_object* x_400; uint8_t x_401; uint8_t x_406; 
lean_dec_ref(x_371);
x_399 = lean_ctor_get(x_390, 0);
x_406 = !lean_is_exclusive(x_390);
if (x_406 == 0)
{
x_400 = x_390;
x_401 = x_406;
goto block_405;
}
else
{
lean_inc(x_399);
lean_dec(x_390);
x_400 = lean_box(0);
x_401 = x_406;
goto block_405;
}
block_405:
{
lean_object* x_402; 
if (x_401 == 0)
{
x_402 = x_400;
goto block_403;
}
else
{
lean_object* x_404; 
x_404 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_404, 0, x_399);
x_402 = x_404;
goto block_403;
}
block_403:
{
return x_402;
}
}
}
}
else
{
lean_object* x_407; lean_object* x_408; 
lean_dec(x_386);
lean_dec(x_384);
lean_dec(x_379);
lean_dec_ref(x_371);
lean_dec_ref(x_41);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_407 = lean_box(0);
if (x_388 == 0)
{
lean_ctor_set(x_387, 0, x_407);
x_408 = x_387;
goto block_409;
}
else
{
lean_object* x_410; 
x_410 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_410, 0, x_407);
x_408 = x_410;
goto block_409;
}
block_409:
{
return x_408;
}
}
}
}
else
{
lean_dec(x_384);
lean_dec(x_379);
lean_dec_ref(x_371);
lean_dec_ref(x_41);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
return x_385;
}
}
else
{
lean_object* x_413; lean_object* x_414; 
lean_dec(x_381);
lean_dec(x_379);
lean_dec_ref(x_371);
lean_dec_ref(x_41);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_413 = lean_box(0);
if (x_383 == 0)
{
lean_ctor_set(x_382, 0, x_413);
x_414 = x_382;
goto block_415;
}
else
{
lean_object* x_416; 
x_416 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_416, 0, x_413);
x_414 = x_416;
goto block_415;
}
block_415:
{
return x_414;
}
}
}
}
else
{
lean_dec(x_379);
lean_dec_ref(x_371);
lean_dec_ref(x_41);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
return x_380;
}
}
else
{
lean_object* x_419; lean_object* x_420; 
lean_dec(x_376);
lean_dec_ref(x_371);
lean_dec_ref(x_41);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_419 = lean_box(0);
if (x_378 == 0)
{
lean_ctor_set(x_377, 0, x_419);
x_420 = x_377;
goto block_421;
}
else
{
lean_object* x_422; 
x_422 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_422, 0, x_419);
x_420 = x_422;
goto block_421;
}
block_421:
{
return x_420;
}
}
}
}
else
{
lean_object* x_425; lean_object* x_426; uint8_t x_427; uint8_t x_432; 
lean_dec_ref(x_371);
lean_dec_ref(x_41);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_425 = lean_ctor_get(x_375, 0);
x_432 = !lean_is_exclusive(x_375);
if (x_432 == 0)
{
x_426 = x_375;
x_427 = x_432;
goto block_431;
}
else
{
lean_inc(x_425);
lean_dec(x_375);
x_426 = lean_box(0);
x_427 = x_432;
goto block_431;
}
block_431:
{
lean_object* x_428; 
if (x_427 == 0)
{
x_428 = x_426;
goto block_429;
}
else
{
lean_object* x_430; 
x_430 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_430, 0, x_425);
x_428 = x_430;
goto block_429;
}
block_429:
{
return x_428;
}
}
}
}
else
{
lean_object* x_433; lean_object* x_434; 
lean_dec(x_371);
lean_dec_ref(x_41);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_433 = lean_box(0);
if (x_373 == 0)
{
lean_ctor_set(x_372, 0, x_433);
x_434 = x_372;
goto block_435;
}
else
{
lean_object* x_436; 
x_436 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_436, 0, x_433);
x_434 = x_436;
goto block_435;
}
block_435:
{
return x_434;
}
}
}
}
else
{
lean_dec_ref(x_41);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
return x_370;
}
}
}
}
else
{
lean_object* x_439; lean_object* x_440; lean_object* x_441; 
lean_dec_ref(x_42);
lean_dec_ref(x_41);
lean_dec_ref(x_29);
lean_del_object(x_17);
x_439 = lean_box(0);
x_440 = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__81));
x_441 = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection(x_26, x_439, x_440, x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_441;
}
}
else
{
lean_object* x_442; 
lean_dec_ref(x_42);
lean_dec_ref(x_41);
lean_del_object(x_17);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_442 = l_Lean_Meta_getNatValue_x3f(x_26, x_4, x_5, x_6, x_7);
lean_dec_ref(x_26);
if (lean_obj_tag(x_442) == 0)
{
lean_object* x_443; lean_object* x_444; uint8_t x_445; uint8_t x_456; 
x_443 = lean_ctor_get(x_442, 0);
x_456 = !lean_is_exclusive(x_442);
if (x_456 == 0)
{
x_444 = x_442;
x_445 = x_456;
goto block_455;
}
else
{
lean_inc(x_443);
lean_dec(x_442);
x_444 = lean_box(0);
x_445 = x_456;
goto block_455;
}
block_455:
{
if (lean_obj_tag(x_443) == 1)
{
lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; 
lean_del_object(x_444);
x_446 = lean_ctor_get(x_443, 0);
lean_inc(x_446);
lean_dec_ref(x_443);
x_447 = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__82));
x_448 = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__11));
x_449 = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__84));
x_450 = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection(x_446, x_29, x_447, x_448, x_449, x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_450;
}
else
{
lean_object* x_451; lean_object* x_452; 
lean_dec(x_443);
lean_dec_ref(x_29);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_451 = lean_box(0);
if (x_445 == 0)
{
lean_ctor_set(x_444, 0, x_451);
x_452 = x_444;
goto block_453;
}
else
{
lean_object* x_454; 
x_454 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_454, 0, x_451);
x_452 = x_454;
goto block_453;
}
block_453:
{
return x_452;
}
}
}
}
else
{
lean_object* x_457; lean_object* x_458; uint8_t x_459; uint8_t x_464; 
lean_dec_ref(x_29);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_457 = lean_ctor_get(x_442, 0);
x_464 = !lean_is_exclusive(x_442);
if (x_464 == 0)
{
x_458 = x_442;
x_459 = x_464;
goto block_463;
}
else
{
lean_inc(x_457);
lean_dec(x_442);
x_458 = lean_box(0);
x_459 = x_464;
goto block_463;
}
block_463:
{
lean_object* x_460; 
if (x_459 == 0)
{
x_460 = x_458;
goto block_461;
}
else
{
lean_object* x_462; 
x_462 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_462, 0, x_457);
x_460 = x_462;
goto block_461;
}
block_461:
{
return x_460;
}
}
}
}
}
else
{
lean_object* x_465; 
lean_dec_ref(x_42);
lean_dec_ref(x_41);
lean_del_object(x_17);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc_ref(x_26);
x_465 = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_goOrAtom(x_26, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_465) == 0)
{
lean_object* x_466; lean_object* x_467; uint8_t x_468; uint8_t x_534; 
x_466 = lean_ctor_get(x_465, 0);
x_534 = !lean_is_exclusive(x_465);
if (x_534 == 0)
{
x_467 = x_465;
x_468 = x_534;
goto block_533;
}
else
{
lean_inc(x_466);
lean_dec(x_465);
x_467 = lean_box(0);
x_468 = x_534;
goto block_533;
}
block_533:
{
if (lean_obj_tag(x_466) == 1)
{
lean_object* x_469; lean_object* x_470; 
lean_del_object(x_467);
x_469 = lean_ctor_get(x_466, 0);
lean_inc(x_469);
lean_dec_ref(x_466);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_470 = l_Lean_Meta_getNatValue_x3f(x_29, x_4, x_5, x_6, x_7);
lean_dec_ref(x_29);
if (lean_obj_tag(x_470) == 0)
{
lean_object* x_471; lean_object* x_472; uint8_t x_473; uint8_t x_520; 
x_471 = lean_ctor_get(x_470, 0);
x_520 = !lean_is_exclusive(x_470);
if (x_520 == 0)
{
x_472 = x_470;
x_473 = x_520;
goto block_519;
}
else
{
lean_inc(x_471);
lean_dec(x_470);
x_472 = lean_box(0);
x_473 = x_520;
goto block_519;
}
block_519:
{
if (lean_obj_tag(x_471) == 1)
{
lean_object* x_474; lean_object* x_475; uint8_t x_476; uint8_t x_514; 
lean_del_object(x_472);
x_474 = lean_ctor_get(x_471, 0);
x_514 = !lean_is_exclusive(x_471);
if (x_514 == 0)
{
x_475 = x_471;
x_476 = x_514;
goto block_513;
}
else
{
lean_inc(x_474);
lean_dec(x_471);
x_475 = lean_box(0);
x_476 = x_514;
goto block_513;
}
block_513:
{
lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; 
x_477 = lean_ctor_get(x_469, 0);
lean_inc(x_477);
x_478 = lean_ctor_get(x_469, 1);
x_479 = lean_ctor_get(x_469, 4);
lean_inc_ref(x_479);
x_480 = lean_nat_mul(x_477, x_474);
lean_inc_ref(x_478);
lean_inc(x_474);
lean_inc(x_480);
lean_inc(x_477);
x_481 = l_Std_Tactic_BVDecide_BVExpr_replicate___override___redArg(x_477, x_480, x_474, x_478);
lean_inc(x_480);
x_482 = l_Lean_mkNatLit(x_480);
lean_inc_ref(x_482);
x_483 = l_Lean_Meta_mkEqRefl(x_482, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_483) == 0)
{
lean_object* x_484; lean_object* x_485; uint8_t x_486; uint8_t x_504; 
x_484 = lean_ctor_get(x_483, 0);
x_504 = !lean_is_exclusive(x_483);
if (x_504 == 0)
{
x_485 = x_483;
x_486 = x_504;
goto block_503;
}
else
{
lean_inc(x_484);
lean_dec(x_483);
x_485 = lean_box(0);
x_486 = x_504;
goto block_503;
}
block_503:
{
lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; 
x_487 = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__0));
x_488 = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__1));
x_489 = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___closed__2));
x_490 = lean_box(0);
x_491 = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__86, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__86_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__86);
lean_inc(x_477);
x_492 = l_Lean_mkNatLit(x_477);
x_493 = l_Lean_mkNatLit(x_474);
lean_inc_ref(x_492);
lean_inc_ref(x_493);
lean_inc_ref(x_479);
x_494 = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___lam__3___boxed), 17, 11);
lean_closure_set(x_494, 0, x_477);
lean_closure_set(x_494, 1, x_479);
lean_closure_set(x_494, 2, x_469);
lean_closure_set(x_494, 3, x_487);
lean_closure_set(x_494, 4, x_488);
lean_closure_set(x_494, 5, x_489);
lean_closure_set(x_494, 6, x_31);
lean_closure_set(x_494, 7, x_490);
lean_closure_set(x_494, 8, x_493);
lean_closure_set(x_494, 9, x_492);
lean_closure_set(x_494, 10, x_26);
x_495 = l_Lean_mkApp5(x_491, x_492, x_482, x_493, x_479, x_484);
x_496 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_496, 0, x_480);
lean_ctor_set(x_496, 1, x_481);
lean_ctor_set(x_496, 2, x_1);
lean_ctor_set(x_496, 3, x_494);
lean_ctor_set(x_496, 4, x_495);
if (x_476 == 0)
{
lean_ctor_set(x_475, 0, x_496);
x_497 = x_475;
goto block_501;
}
else
{
lean_object* x_502; 
x_502 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_502, 0, x_496);
x_497 = x_502;
goto block_501;
}
block_501:
{
lean_object* x_498; 
if (x_486 == 0)
{
lean_ctor_set(x_485, 0, x_497);
x_498 = x_485;
goto block_499;
}
else
{
lean_object* x_500; 
x_500 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_500, 0, x_497);
x_498 = x_500;
goto block_499;
}
block_499:
{
return x_498;
}
}
}
}
else
{
lean_object* x_505; lean_object* x_506; uint8_t x_507; uint8_t x_512; 
lean_dec_ref(x_482);
lean_dec_ref(x_481);
lean_dec(x_480);
lean_dec_ref(x_479);
lean_dec(x_477);
lean_del_object(x_475);
lean_dec(x_474);
lean_dec(x_469);
lean_dec_ref(x_26);
lean_dec_ref(x_1);
x_505 = lean_ctor_get(x_483, 0);
x_512 = !lean_is_exclusive(x_483);
if (x_512 == 0)
{
x_506 = x_483;
x_507 = x_512;
goto block_511;
}
else
{
lean_inc(x_505);
lean_dec(x_483);
x_506 = lean_box(0);
x_507 = x_512;
goto block_511;
}
block_511:
{
lean_object* x_508; 
if (x_507 == 0)
{
x_508 = x_506;
goto block_509;
}
else
{
lean_object* x_510; 
x_510 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_510, 0, x_505);
x_508 = x_510;
goto block_509;
}
block_509:
{
return x_508;
}
}
}
}
}
else
{
lean_object* x_515; lean_object* x_516; 
lean_dec(x_471);
lean_dec(x_469);
lean_dec_ref(x_26);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_515 = lean_box(0);
if (x_473 == 0)
{
lean_ctor_set(x_472, 0, x_515);
x_516 = x_472;
goto block_517;
}
else
{
lean_object* x_518; 
x_518 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_518, 0, x_515);
x_516 = x_518;
goto block_517;
}
block_517:
{
return x_516;
}
}
}
}
else
{
lean_object* x_521; lean_object* x_522; uint8_t x_523; uint8_t x_528; 
lean_dec(x_469);
lean_dec_ref(x_26);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_521 = lean_ctor_get(x_470, 0);
x_528 = !lean_is_exclusive(x_470);
if (x_528 == 0)
{
x_522 = x_470;
x_523 = x_528;
goto block_527;
}
else
{
lean_inc(x_521);
lean_dec(x_470);
x_522 = lean_box(0);
x_523 = x_528;
goto block_527;
}
block_527:
{
lean_object* x_524; 
if (x_523 == 0)
{
x_524 = x_522;
goto block_525;
}
else
{
lean_object* x_526; 
x_526 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_526, 0, x_521);
x_524 = x_526;
goto block_525;
}
block_525:
{
return x_524;
}
}
}
}
else
{
lean_object* x_529; lean_object* x_530; 
lean_dec(x_466);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_529 = lean_box(0);
if (x_468 == 0)
{
lean_ctor_set(x_467, 0, x_529);
x_530 = x_467;
goto block_531;
}
else
{
lean_object* x_532; 
x_532 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_532, 0, x_529);
x_530 = x_532;
goto block_531;
}
block_531:
{
return x_530;
}
}
}
}
else
{
lean_dec_ref(x_29);
lean_dec_ref(x_26);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
return x_465;
}
}
}
else
{
lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; 
lean_dec_ref(x_42);
lean_dec_ref(x_41);
lean_del_object(x_17);
x_535 = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__87));
x_536 = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__5));
x_537 = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__89));
x_538 = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_rotateReflection(x_26, x_29, x_535, x_536, x_537, x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_26);
return x_538;
}
}
else
{
lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; 
lean_dec_ref(x_42);
lean_dec_ref(x_41);
lean_del_object(x_17);
x_539 = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__90));
x_540 = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___closed__8));
x_541 = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__92));
x_542 = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_rotateReflection(x_26, x_29, x_539, x_540, x_541, x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_26);
return x_542;
}
}
}
else
{
lean_object* x_543; 
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
lean_del_object(x_17);
x_543 = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_goBvLit(x_1, x_3, x_4, x_5, x_6, x_7);
return x_543;
}
}
else
{
lean_object* x_544; lean_object* x_545; lean_object* x_546; 
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_del_object(x_17);
x_544 = lean_box(4);
x_545 = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__94));
x_546 = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection(x_26, x_544, x_545, x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_546;
}
}
else
{
lean_object* x_547; lean_object* x_548; lean_object* x_549; 
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_del_object(x_17);
x_547 = lean_box(5);
x_548 = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__96));
x_549 = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection(x_26, x_547, x_548, x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_549;
}
}
else
{
lean_object* x_550; lean_object* x_551; lean_object* x_552; 
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_del_object(x_17);
x_550 = lean_box(6);
x_551 = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___closed__98));
x_552 = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection(x_26, x_550, x_551, x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_552;
}
}
}
block_23:
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_box(0);
if (x_18 == 0)
{
lean_ctor_set(x_17, 0, x_19);
x_20 = x_17;
goto block_21;
}
else
{
lean_object* x_22; 
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_19);
x_20 = x_22;
goto block_21;
}
block_21:
{
return x_20;
}
}
}
}
else
{
lean_object* x_555; lean_object* x_556; uint8_t x_557; uint8_t x_562; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_555 = lean_ctor_get(x_15, 0);
x_562 = !lean_is_exclusive(x_15);
if (x_562 == 0)
{
x_556 = x_15;
x_557 = x_562;
goto block_561;
}
else
{
lean_inc(x_555);
lean_dec(x_15);
x_556 = lean_box(0);
x_557 = x_562;
goto block_561;
}
block_561:
{
lean_object* x_558; 
if (x_557 == 0)
{
x_558 = x_556;
goto block_559;
}
else
{
lean_object* x_560; 
x_560 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_560, 0, x_555);
x_558 = x_560;
goto block_559;
}
block_559:
{
return x_558;
}
}
}
block_11:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
block_14:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVExprCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_goOrAtom_spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_st_ref_get(x_2);
x_34 = lean_ctor_get(x_33, 1);
lean_inc_ref(x_34);
lean_dec(x_33);
x_35 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom_spec__2_spec__12___redArg(x_34, x_1);
lean_dec_ref(x_34);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; 
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_1);
x_36 = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
if (lean_obj_tag(x_37) == 0)
{
uint8_t x_38; lean_object* x_39; 
lean_dec_ref(x_36);
x_38 = 0;
lean_inc_ref(x_1);
x_39 = l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_bitVecAtom(x_1, x_38, x_3, x_4, x_5, x_6, x_7);
x_9 = x_39;
goto block_32;
}
else
{
lean_dec_ref(x_37);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_9 = x_36;
goto block_32;
}
}
else
{
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_9 = x_36;
goto block_32;
}
}
else
{
lean_object* x_40; lean_object* x_41; uint8_t x_42; uint8_t x_47; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_40 = lean_ctor_get(x_35, 0);
x_47 = !lean_is_exclusive(x_35);
if (x_47 == 0)
{
x_41 = x_35;
x_42 = x_47;
goto block_46;
}
else
{
lean_inc(x_40);
lean_dec(x_35);
x_41 = lean_box(0);
x_42 = x_47;
goto block_46;
}
block_46:
{
lean_object* x_43; 
if (x_42 == 0)
{
lean_ctor_set_tag(x_41, 0);
x_43 = x_41;
goto block_44;
}
else
{
lean_object* x_45; 
x_45 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_45, 0, x_40);
x_43 = x_45;
goto block_44;
}
block_44:
{
return x_43;
}
}
}
block_32:
{
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_31; 
x_10 = lean_ctor_get(x_9, 0);
x_31 = !lean_is_exclusive(x_9);
if (x_31 == 0)
{
x_11 = x_9;
x_12 = x_31;
goto block_30;
}
else
{
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_box(0);
x_12 = x_31;
goto block_30;
}
block_30:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_29; 
x_13 = lean_st_ref_take(x_2);
x_14 = lean_ctor_get(x_13, 0);
x_15 = lean_ctor_get(x_13, 1);
x_16 = lean_ctor_get(x_13, 2);
x_17 = lean_ctor_get(x_13, 3);
x_29 = !lean_is_exclusive(x_13);
if (x_29 == 0)
{
x_18 = x_13;
x_19 = x_29;
goto block_28;
}
else
{
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_13);
x_18 = lean_box(0);
x_19 = x_29;
goto block_28;
}
block_28:
{
lean_object* x_20; lean_object* x_21; 
lean_inc(x_10);
x_20 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13___redArg(x_15, x_1, x_10);
if (x_19 == 0)
{
lean_ctor_set(x_18, 1, x_20);
x_21 = x_18;
goto block_26;
}
else
{
lean_object* x_27; 
x_27 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_27, 0, x_14);
lean_ctor_set(x_27, 1, x_20);
lean_ctor_set(x_27, 2, x_16);
lean_ctor_set(x_27, 3, x_17);
x_21 = x_27;
goto block_26;
}
block_26:
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_st_ref_set(x_2, x_21);
if (x_12 == 0)
{
x_23 = x_11;
goto block_24;
}
else
{
lean_object* x_25; 
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_10);
x_23 = x_25;
goto block_24;
}
block_24:
{
return x_23;
}
}
}
}
}
else
{
lean_dec_ref(x_1);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_goOrAtom(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVExprCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_goOrAtom_spec__10(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_goOrAtom(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_of___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_of(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_goOrAtom___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_goOrAtom(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_rotateReflection___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_rotateReflection(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_7);
lean_dec_ref(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goPred___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goPred(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_of_binaryReflection___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_3);
x_13 = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_of_binaryReflection(x_1, x_2, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_gateReflection___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_3);
x_13 = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_gateReflection(x_1, x_2, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftConstLikeReflection(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_7);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftReflection___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_shiftReflection(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_7);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVPredCache___at___00Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_of_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVPredCache___at___00Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_of_spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVExprCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_goOrAtom_spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVExprCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_goOrAtom_spec__10(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_unaryReflection(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_3);
x_14 = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_binaryReflection(x_1, x_2, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_of_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVPred_of_go(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_go(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go_spec__12(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go_spec__12___redArg(x_2, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go_spec__12___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_of_go_spec__12(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom_spec__2_spec__12(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom_spec__2_spec__12___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom_spec__2_spec__12___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom_spec__2_spec__12(x_1, x_2, x_3);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom_spec__2_spec__12_spec__17(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom_spec__2_spec__12_spec__17___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom_spec__2_spec__12_spec__17___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom_spec__2_spec__12_spec__17(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13_spec__19(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13_spec__19___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13_spec__19___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13_spec__19(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13_spec__20(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13_spec__20___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13_spec__21(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13_spec__21___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13_spec__20_spec__25(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13_spec__20_spec__25___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13_spec__20_spec__25_spec__26(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_BVDecide_Frontend_LemmaM_withBVLogicalCache___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify_0__Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of_goOrAtom_spec__2_spec__13_spec__20_spec__25_spec__26___redArg(x_2, x_3);
return x_4;
}
}
lean_object* runtime_initialize_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_LitValues(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_LitValues(builtin)
;
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
res = initialize_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedLemmas(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_LitValues(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify(builtin);
}
#ifdef __cplusplus
}
#endif
