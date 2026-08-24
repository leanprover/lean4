// Lean compiler output
// Module: Lean.Elab.Tactic.VCGen.RuleCache
// Imports: public import Lean.Elab.Tactic.Do.VCGen.Split public import Lean.Elab.Tactic.VCGen.Context public import Lean.Elab.Tactic.VCGen.RuleConstruction public import Lean.Elab.Tactic.VCGen.LatticeOp public import Lean.Elab.Tactic.VCGen.Util import Lean.Meta.Sym.InferType
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
lean_object* lean_array_get_size(lean_object*);
size_t lean_ptr_addr(lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
uint64_t lean_usize_to_uint64(size_t);
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Elab_Tactic_VCGen_WPApp_instWP(lean_object*);
lean_object* l_Lean_Elab_Tactic_VCGen_mkBackwardRuleForSplit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_BackwardRule_shareCommon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppPrefix(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* l_Lean_Elab_Tactic_VCGen_mkLatticeOpRule(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_VCGen_mkFrameBackwardRule(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_VCGen_SpecAttr_SpecProof_key(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Elab_Tactic_VCGen_tryMkBackwardRuleFromSpec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__1___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__4_spec__5_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__4___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg___boxed(lean_object*, lean_object*);
static const lean_array_object l_Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__4_spec__5_spec__6(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_VCGen_mkBackwardRuleForSplitCached___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "ite"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_mkBackwardRuleForSplitCached___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRuleForSplitCached___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_mkBackwardRuleForSplitCached___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRuleForSplitCached___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(15, 2, 151, 246, 61, 29, 192, 254)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_mkBackwardRuleForSplitCached___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRuleForSplitCached___redArg___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_mkBackwardRuleForSplitCached___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "dite"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_mkBackwardRuleForSplitCached___redArg___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRuleForSplitCached___redArg___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_mkBackwardRuleForSplitCached___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRuleForSplitCached___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(137, 166, 197, 161, 68, 218, 116, 116)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_mkBackwardRuleForSplitCached___redArg___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRuleForSplitCached___redArg___closed__3_value;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_mkBackwardRuleForSplitCached___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "cond"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_mkBackwardRuleForSplitCached___redArg___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRuleForSplitCached___redArg___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_mkBackwardRuleForSplitCached___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRuleForSplitCached___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(130, 140, 200, 235, 144, 197, 118, 1)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_mkBackwardRuleForSplitCached___redArg___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRuleForSplitCached___redArg___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_mkBackwardRuleForSplitCached___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_mkBackwardRuleForSplitCached___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_mkBackwardRuleForSplitCached(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_mkBackwardRuleForSplitCached___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1_spec__3_spec__4_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1_spec__3___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1_spec__3_spec__4_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_mkFrameBackwardRuleCached___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_mkFrameBackwardRuleCached___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_mkFrameBackwardRuleCached(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_mkFrameBackwardRuleCached___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__1___redArg___lam__0(lean_object* v_k_1_, lean_object* v___y_2_, lean_object* v___y_3_, lean_object* v___y_4_, lean_object* v___y_5_, lean_object* v___y_6_, lean_object* v___y_7_, lean_object* v___y_8_, lean_object* v___y_9_, lean_object* v___y_10_, lean_object* v___y_11_, lean_object* v___y_12_){
_start:
{
lean_object* v___x_14_; 
lean_inc(v___y_8_);
lean_inc_ref(v___y_7_);
lean_inc(v___y_6_);
lean_inc_ref(v___y_5_);
lean_inc(v___y_4_);
lean_inc(v___y_3_);
lean_inc_ref(v___y_2_);
v___x_14_ = lean_apply_12(v_k_1_, v___y_2_, v___y_3_, v___y_4_, v___y_5_, v___y_6_, v___y_7_, v___y_8_, v___y_9_, v___y_10_, v___y_11_, v___y_12_, lean_box(0));
return v___x_14_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__1___redArg___lam__0___boxed(lean_object* v_k_15_, lean_object* v___y_16_, lean_object* v___y_17_, lean_object* v___y_18_, lean_object* v___y_19_, lean_object* v___y_20_, lean_object* v___y_21_, lean_object* v___y_22_, lean_object* v___y_23_, lean_object* v___y_24_, lean_object* v___y_25_, lean_object* v___y_26_, lean_object* v___y_27_){
_start:
{
lean_object* v_res_28_; 
v_res_28_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__1___redArg___lam__0(v_k_15_, v___y_16_, v___y_17_, v___y_18_, v___y_19_, v___y_20_, v___y_21_, v___y_22_, v___y_23_, v___y_24_, v___y_25_, v___y_26_);
lean_dec(v___y_22_);
lean_dec_ref(v___y_21_);
lean_dec(v___y_20_);
lean_dec_ref(v___y_19_);
lean_dec(v___y_18_);
lean_dec(v___y_17_);
lean_dec_ref(v___y_16_);
return v_res_28_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__1___redArg(lean_object* v_k_29_, uint8_t v_allowLevelAssignments_30_, lean_object* v___y_31_, lean_object* v___y_32_, lean_object* v___y_33_, lean_object* v___y_34_, lean_object* v___y_35_, lean_object* v___y_36_, lean_object* v___y_37_, lean_object* v___y_38_, lean_object* v___y_39_, lean_object* v___y_40_, lean_object* v___y_41_){
_start:
{
lean_object* v___f_43_; lean_object* v___x_44_; 
lean_inc(v___y_37_);
lean_inc_ref(v___y_36_);
lean_inc(v___y_35_);
lean_inc_ref(v___y_34_);
lean_inc(v___y_33_);
lean_inc(v___y_32_);
lean_inc_ref(v___y_31_);
v___f_43_ = lean_alloc_closure((void*)(l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__1___redArg___lam__0___boxed), 13, 8);
lean_closure_set(v___f_43_, 0, v_k_29_);
lean_closure_set(v___f_43_, 1, v___y_31_);
lean_closure_set(v___f_43_, 2, v___y_32_);
lean_closure_set(v___f_43_, 3, v___y_33_);
lean_closure_set(v___f_43_, 4, v___y_34_);
lean_closure_set(v___f_43_, 5, v___y_35_);
lean_closure_set(v___f_43_, 6, v___y_36_);
lean_closure_set(v___f_43_, 7, v___y_37_);
v___x_44_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_box(0), v_allowLevelAssignments_30_, v___f_43_, v___y_38_, v___y_39_, v___y_40_, v___y_41_);
if (lean_obj_tag(v___x_44_) == 0)
{
return v___x_44_;
}
else
{
lean_object* v_a_45_; lean_object* v___x_47_; uint8_t v_isShared_48_; uint8_t v_isSharedCheck_52_; 
v_a_45_ = lean_ctor_get(v___x_44_, 0);
v_isSharedCheck_52_ = !lean_is_exclusive(v___x_44_);
if (v_isSharedCheck_52_ == 0)
{
v___x_47_ = v___x_44_;
v_isShared_48_ = v_isSharedCheck_52_;
goto v_resetjp_46_;
}
else
{
lean_inc(v_a_45_);
lean_dec(v___x_44_);
v___x_47_ = lean_box(0);
v_isShared_48_ = v_isSharedCheck_52_;
goto v_resetjp_46_;
}
v_resetjp_46_:
{
lean_object* v___x_50_; 
if (v_isShared_48_ == 0)
{
v___x_50_ = v___x_47_;
goto v_reusejp_49_;
}
else
{
lean_object* v_reuseFailAlloc_51_; 
v_reuseFailAlloc_51_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_51_, 0, v_a_45_);
v___x_50_ = v_reuseFailAlloc_51_;
goto v_reusejp_49_;
}
v_reusejp_49_:
{
return v___x_50_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__1___redArg___boxed(lean_object* v_k_53_, lean_object* v_allowLevelAssignments_54_, lean_object* v___y_55_, lean_object* v___y_56_, lean_object* v___y_57_, lean_object* v___y_58_, lean_object* v___y_59_, lean_object* v___y_60_, lean_object* v___y_61_, lean_object* v___y_62_, lean_object* v___y_63_, lean_object* v___y_64_, lean_object* v___y_65_, lean_object* v___y_66_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_67_; lean_object* v_res_68_; 
v_allowLevelAssignments_boxed_67_ = lean_unbox(v_allowLevelAssignments_54_);
v_res_68_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__1___redArg(v_k_53_, v_allowLevelAssignments_boxed_67_, v___y_55_, v___y_56_, v___y_57_, v___y_58_, v___y_59_, v___y_60_, v___y_61_, v___y_62_, v___y_63_, v___y_64_, v___y_65_);
lean_dec(v___y_65_);
lean_dec_ref(v___y_64_);
lean_dec(v___y_63_);
lean_dec_ref(v___y_62_);
lean_dec(v___y_61_);
lean_dec_ref(v___y_60_);
lean_dec(v___y_59_);
lean_dec_ref(v___y_58_);
lean_dec(v___y_57_);
lean_dec(v___y_56_);
lean_dec_ref(v___y_55_);
return v_res_68_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__1(lean_object* v_00_u03b1_69_, lean_object* v_k_70_, uint8_t v_allowLevelAssignments_71_, lean_object* v___y_72_, lean_object* v___y_73_, lean_object* v___y_74_, lean_object* v___y_75_, lean_object* v___y_76_, lean_object* v___y_77_, lean_object* v___y_78_, lean_object* v___y_79_, lean_object* v___y_80_, lean_object* v___y_81_, lean_object* v___y_82_){
_start:
{
lean_object* v___x_84_; 
v___x_84_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__1___redArg(v_k_70_, v_allowLevelAssignments_71_, v___y_72_, v___y_73_, v___y_74_, v___y_75_, v___y_76_, v___y_77_, v___y_78_, v___y_79_, v___y_80_, v___y_81_, v___y_82_);
return v___x_84_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__1___boxed(lean_object* v_00_u03b1_85_, lean_object* v_k_86_, lean_object* v_allowLevelAssignments_87_, lean_object* v___y_88_, lean_object* v___y_89_, lean_object* v___y_90_, lean_object* v___y_91_, lean_object* v___y_92_, lean_object* v___y_93_, lean_object* v___y_94_, lean_object* v___y_95_, lean_object* v___y_96_, lean_object* v___y_97_, lean_object* v___y_98_, lean_object* v___y_99_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_100_; lean_object* v_res_101_; 
v_allowLevelAssignments_boxed_100_ = lean_unbox(v_allowLevelAssignments_87_);
v_res_101_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__1(v_00_u03b1_85_, v_k_86_, v_allowLevelAssignments_boxed_100_, v___y_88_, v___y_89_, v___y_90_, v___y_91_, v___y_92_, v___y_93_, v___y_94_, v___y_95_, v___y_96_, v___y_97_, v___y_98_);
lean_dec(v___y_98_);
lean_dec_ref(v___y_97_);
lean_dec(v___y_96_);
lean_dec_ref(v___y_95_);
lean_dec(v___y_94_);
lean_dec_ref(v___y_93_);
lean_dec(v___y_92_);
lean_dec_ref(v___y_91_);
lean_dec(v___y_90_);
lean_dec(v___y_89_);
lean_dec_ref(v___y_88_);
return v_res_101_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached___lam__0(lean_object* v_specThm_102_, lean_object* v_info_103_, lean_object* v___x_104_, lean_object* v___y_105_, lean_object* v___y_106_, lean_object* v___y_107_, lean_object* v___y_108_, lean_object* v___y_109_, lean_object* v___y_110_, lean_object* v___y_111_, lean_object* v___y_112_, lean_object* v___y_113_, lean_object* v___y_114_, lean_object* v___y_115_){
_start:
{
lean_object* v___x_117_; 
v___x_117_ = l_Lean_Elab_Tactic_VCGen_tryMkBackwardRuleFromSpec(v_specThm_102_, v_info_103_, v___x_104_, v___y_112_, v___y_113_, v___y_114_, v___y_115_);
if (lean_obj_tag(v___x_117_) == 0)
{
lean_object* v_a_118_; lean_object* v___x_120_; uint8_t v_isShared_121_; uint8_t v_isSharedCheck_126_; 
v_a_118_ = lean_ctor_get(v___x_117_, 0);
v_isSharedCheck_126_ = !lean_is_exclusive(v___x_117_);
if (v_isSharedCheck_126_ == 0)
{
v___x_120_ = v___x_117_;
v_isShared_121_ = v_isSharedCheck_126_;
goto v_resetjp_119_;
}
else
{
lean_inc(v_a_118_);
lean_dec(v___x_117_);
v___x_120_ = lean_box(0);
v_isShared_121_ = v_isSharedCheck_126_;
goto v_resetjp_119_;
}
v_resetjp_119_:
{
lean_object* v___x_122_; lean_object* v___x_124_; 
v___x_122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_122_, 0, v_a_118_);
if (v_isShared_121_ == 0)
{
lean_ctor_set(v___x_120_, 0, v___x_122_);
v___x_124_ = v___x_120_;
goto v_reusejp_123_;
}
else
{
lean_object* v_reuseFailAlloc_125_; 
v_reuseFailAlloc_125_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_125_, 0, v___x_122_);
v___x_124_ = v_reuseFailAlloc_125_;
goto v_reusejp_123_;
}
v_reusejp_123_:
{
return v___x_124_;
}
}
}
else
{
lean_object* v_a_127_; lean_object* v___x_129_; uint8_t v_isShared_130_; uint8_t v_isSharedCheck_134_; 
v_a_127_ = lean_ctor_get(v___x_117_, 0);
v_isSharedCheck_134_ = !lean_is_exclusive(v___x_117_);
if (v_isSharedCheck_134_ == 0)
{
v___x_129_ = v___x_117_;
v_isShared_130_ = v_isSharedCheck_134_;
goto v_resetjp_128_;
}
else
{
lean_inc(v_a_127_);
lean_dec(v___x_117_);
v___x_129_ = lean_box(0);
v_isShared_130_ = v_isSharedCheck_134_;
goto v_resetjp_128_;
}
v_resetjp_128_:
{
lean_object* v___x_132_; 
if (v_isShared_130_ == 0)
{
v___x_132_ = v___x_129_;
goto v_reusejp_131_;
}
else
{
lean_object* v_reuseFailAlloc_133_; 
v_reuseFailAlloc_133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_133_, 0, v_a_127_);
v___x_132_ = v_reuseFailAlloc_133_;
goto v_reusejp_131_;
}
v_reusejp_131_:
{
return v___x_132_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached___lam__0___boxed(lean_object* v_specThm_135_, lean_object* v_info_136_, lean_object* v___x_137_, lean_object* v___y_138_, lean_object* v___y_139_, lean_object* v___y_140_, lean_object* v___y_141_, lean_object* v___y_142_, lean_object* v___y_143_, lean_object* v___y_144_, lean_object* v___y_145_, lean_object* v___y_146_, lean_object* v___y_147_, lean_object* v___y_148_, lean_object* v___y_149_){
_start:
{
lean_object* v_res_150_; 
v_res_150_ = l_Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached___lam__0(v_specThm_135_, v_info_136_, v___x_137_, v___y_138_, v___y_139_, v___y_140_, v___y_141_, v___y_142_, v___y_143_, v___y_144_, v___y_145_, v___y_146_, v___y_147_, v___y_148_);
lean_dec(v___y_148_);
lean_dec_ref(v___y_147_);
lean_dec(v___y_146_);
lean_dec_ref(v___y_145_);
lean_dec(v___y_144_);
lean_dec_ref(v___y_143_);
lean_dec(v___y_142_);
lean_dec_ref(v___y_141_);
lean_dec(v___y_140_);
lean_dec(v___y_139_);
lean_dec_ref(v___y_138_);
lean_dec_ref(v_info_136_);
return v_res_150_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__3___redArg(lean_object* v_a_151_, lean_object* v_x_152_){
_start:
{
if (lean_obj_tag(v_x_152_) == 0)
{
uint8_t v___x_153_; 
v___x_153_ = 0;
return v___x_153_;
}
else
{
lean_object* v_key_154_; lean_object* v_tail_155_; uint8_t v___y_157_; lean_object* v_fst_159_; lean_object* v_snd_160_; lean_object* v_fst_161_; lean_object* v_snd_162_; uint8_t v___x_163_; 
v_key_154_ = lean_ctor_get(v_x_152_, 0);
v_tail_155_ = lean_ctor_get(v_x_152_, 2);
v_fst_159_ = lean_ctor_get(v_key_154_, 0);
v_snd_160_ = lean_ctor_get(v_key_154_, 1);
v_fst_161_ = lean_ctor_get(v_a_151_, 0);
v_snd_162_ = lean_ctor_get(v_a_151_, 1);
v___x_163_ = lean_name_eq(v_fst_159_, v_fst_161_);
if (v___x_163_ == 0)
{
v___y_157_ = v___x_163_;
goto v___jp_156_;
}
else
{
lean_object* v_fst_164_; lean_object* v_snd_165_; lean_object* v_fst_166_; lean_object* v_snd_167_; size_t v___x_168_; size_t v___x_169_; uint8_t v___x_170_; 
v_fst_164_ = lean_ctor_get(v_snd_160_, 0);
v_snd_165_ = lean_ctor_get(v_snd_160_, 1);
v_fst_166_ = lean_ctor_get(v_snd_162_, 0);
v_snd_167_ = lean_ctor_get(v_snd_162_, 1);
v___x_168_ = lean_ptr_addr(v_fst_164_);
v___x_169_ = lean_ptr_addr(v_fst_166_);
v___x_170_ = lean_usize_dec_eq(v___x_168_, v___x_169_);
if (v___x_170_ == 0)
{
v_x_152_ = v_tail_155_;
goto _start;
}
else
{
uint8_t v___x_172_; 
v___x_172_ = lean_nat_dec_eq(v_snd_165_, v_snd_167_);
v___y_157_ = v___x_172_;
goto v___jp_156_;
}
}
v___jp_156_:
{
if (v___y_157_ == 0)
{
v_x_152_ = v_tail_155_;
goto _start;
}
else
{
return v___y_157_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__3___redArg___boxed(lean_object* v_a_173_, lean_object* v_x_174_){
_start:
{
uint8_t v_res_175_; lean_object* v_r_176_; 
v_res_175_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__3___redArg(v_a_173_, v_x_174_);
lean_dec(v_x_174_);
lean_dec_ref(v_a_173_);
v_r_176_ = lean_box(v_res_175_);
return v_r_176_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__4_spec__5_spec__6___redArg(lean_object* v_x_177_, lean_object* v_x_178_){
_start:
{
if (lean_obj_tag(v_x_178_) == 0)
{
return v_x_177_;
}
else
{
lean_object* v_key_179_; lean_object* v_value_180_; lean_object* v_tail_181_; lean_object* v___x_183_; uint8_t v_isShared_184_; uint8_t v_isSharedCheck_218_; 
v_key_179_ = lean_ctor_get(v_x_178_, 0);
v_value_180_ = lean_ctor_get(v_x_178_, 1);
v_tail_181_ = lean_ctor_get(v_x_178_, 2);
v_isSharedCheck_218_ = !lean_is_exclusive(v_x_178_);
if (v_isSharedCheck_218_ == 0)
{
v___x_183_ = v_x_178_;
v_isShared_184_ = v_isSharedCheck_218_;
goto v_resetjp_182_;
}
else
{
lean_inc(v_tail_181_);
lean_inc(v_value_180_);
lean_inc(v_key_179_);
lean_dec(v_x_178_);
v___x_183_ = lean_box(0);
v_isShared_184_ = v_isSharedCheck_218_;
goto v_resetjp_182_;
}
v_resetjp_182_:
{
lean_object* v_fst_185_; lean_object* v_snd_186_; lean_object* v___x_187_; uint64_t v___y_189_; 
v_fst_185_ = lean_ctor_get(v_key_179_, 0);
v_snd_186_ = lean_ctor_get(v_key_179_, 1);
v___x_187_ = lean_array_get_size(v_x_177_);
if (lean_obj_tag(v_fst_185_) == 0)
{
uint64_t v___x_216_; 
v___x_216_ = 1723ULL;
v___y_189_ = v___x_216_;
goto v___jp_188_;
}
else
{
uint64_t v_hash_217_; 
v_hash_217_ = lean_ctor_get_uint64(v_fst_185_, sizeof(void*)*2);
v___y_189_ = v_hash_217_;
goto v___jp_188_;
}
v___jp_188_:
{
lean_object* v_fst_190_; lean_object* v_snd_191_; size_t v___x_192_; size_t v___x_193_; size_t v___x_194_; uint64_t v___x_195_; uint64_t v___x_196_; uint64_t v___x_197_; uint64_t v___x_198_; uint64_t v___x_199_; uint64_t v___x_200_; uint64_t v_fold_201_; uint64_t v___x_202_; uint64_t v___x_203_; uint64_t v___x_204_; size_t v___x_205_; size_t v___x_206_; size_t v___x_207_; size_t v___x_208_; size_t v___x_209_; lean_object* v___x_210_; lean_object* v___x_212_; 
v_fst_190_ = lean_ctor_get(v_snd_186_, 0);
v_snd_191_ = lean_ctor_get(v_snd_186_, 1);
v___x_192_ = lean_ptr_addr(v_fst_190_);
v___x_193_ = ((size_t)3ULL);
v___x_194_ = lean_usize_shift_right(v___x_192_, v___x_193_);
v___x_195_ = lean_usize_to_uint64(v___x_194_);
v___x_196_ = lean_uint64_of_nat(v_snd_191_);
v___x_197_ = lean_uint64_mix_hash(v___x_195_, v___x_196_);
v___x_198_ = lean_uint64_mix_hash(v___y_189_, v___x_197_);
v___x_199_ = 32ULL;
v___x_200_ = lean_uint64_shift_right(v___x_198_, v___x_199_);
v_fold_201_ = lean_uint64_xor(v___x_198_, v___x_200_);
v___x_202_ = 16ULL;
v___x_203_ = lean_uint64_shift_right(v_fold_201_, v___x_202_);
v___x_204_ = lean_uint64_xor(v_fold_201_, v___x_203_);
v___x_205_ = lean_uint64_to_usize(v___x_204_);
v___x_206_ = lean_usize_of_nat(v___x_187_);
v___x_207_ = ((size_t)1ULL);
v___x_208_ = lean_usize_sub(v___x_206_, v___x_207_);
v___x_209_ = lean_usize_land(v___x_205_, v___x_208_);
v___x_210_ = lean_array_uget_borrowed(v_x_177_, v___x_209_);
lean_inc(v___x_210_);
if (v_isShared_184_ == 0)
{
lean_ctor_set(v___x_183_, 2, v___x_210_);
v___x_212_ = v___x_183_;
goto v_reusejp_211_;
}
else
{
lean_object* v_reuseFailAlloc_215_; 
v_reuseFailAlloc_215_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_215_, 0, v_key_179_);
lean_ctor_set(v_reuseFailAlloc_215_, 1, v_value_180_);
lean_ctor_set(v_reuseFailAlloc_215_, 2, v___x_210_);
v___x_212_ = v_reuseFailAlloc_215_;
goto v_reusejp_211_;
}
v_reusejp_211_:
{
lean_object* v___x_213_; 
v___x_213_ = lean_array_uset(v_x_177_, v___x_209_, v___x_212_);
v_x_177_ = v___x_213_;
v_x_178_ = v_tail_181_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__4_spec__5___redArg(lean_object* v_i_219_, lean_object* v_source_220_, lean_object* v_target_221_){
_start:
{
lean_object* v___x_222_; uint8_t v___x_223_; 
v___x_222_ = lean_array_get_size(v_source_220_);
v___x_223_ = lean_nat_dec_lt(v_i_219_, v___x_222_);
if (v___x_223_ == 0)
{
lean_dec_ref(v_source_220_);
lean_dec(v_i_219_);
return v_target_221_;
}
else
{
lean_object* v_es_224_; lean_object* v___x_225_; lean_object* v_source_226_; lean_object* v_target_227_; lean_object* v___x_228_; lean_object* v___x_229_; 
v_es_224_ = lean_array_fget(v_source_220_, v_i_219_);
v___x_225_ = lean_box(0);
v_source_226_ = lean_array_fset(v_source_220_, v_i_219_, v___x_225_);
v_target_227_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__4_spec__5_spec__6___redArg(v_target_221_, v_es_224_);
v___x_228_ = lean_unsigned_to_nat(1u);
v___x_229_ = lean_nat_add(v_i_219_, v___x_228_);
lean_dec(v_i_219_);
v_i_219_ = v___x_229_;
v_source_220_ = v_source_226_;
v_target_221_ = v_target_227_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__4___redArg(lean_object* v_data_231_){
_start:
{
lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v_nbuckets_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; 
v___x_232_ = lean_array_get_size(v_data_231_);
v___x_233_ = lean_unsigned_to_nat(2u);
v_nbuckets_234_ = lean_nat_mul(v___x_232_, v___x_233_);
v___x_235_ = lean_unsigned_to_nat(0u);
v___x_236_ = lean_box(0);
v___x_237_ = lean_mk_array(v_nbuckets_234_, v___x_236_);
v___x_238_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__4_spec__5___redArg(v___x_235_, v_data_231_, v___x_237_);
return v___x_238_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__5___redArg(lean_object* v_a_239_, lean_object* v_b_240_, lean_object* v_x_241_){
_start:
{
if (lean_obj_tag(v_x_241_) == 0)
{
lean_dec(v_b_240_);
lean_dec_ref(v_a_239_);
return v_x_241_;
}
else
{
lean_object* v_key_242_; lean_object* v_value_243_; lean_object* v_tail_244_; lean_object* v___x_246_; uint8_t v_isShared_247_; uint8_t v_isSharedCheck_269_; 
v_key_242_ = lean_ctor_get(v_x_241_, 0);
v_value_243_ = lean_ctor_get(v_x_241_, 1);
v_tail_244_ = lean_ctor_get(v_x_241_, 2);
v_isSharedCheck_269_ = !lean_is_exclusive(v_x_241_);
if (v_isSharedCheck_269_ == 0)
{
v___x_246_ = v_x_241_;
v_isShared_247_ = v_isSharedCheck_269_;
goto v_resetjp_245_;
}
else
{
lean_inc(v_tail_244_);
lean_inc(v_value_243_);
lean_inc(v_key_242_);
lean_dec(v_x_241_);
v___x_246_ = lean_box(0);
v_isShared_247_ = v_isSharedCheck_269_;
goto v_resetjp_245_;
}
v_resetjp_245_:
{
uint8_t v___y_254_; lean_object* v_fst_256_; lean_object* v_snd_257_; lean_object* v_fst_258_; lean_object* v_snd_259_; uint8_t v___x_260_; 
v_fst_256_ = lean_ctor_get(v_key_242_, 0);
v_snd_257_ = lean_ctor_get(v_key_242_, 1);
v_fst_258_ = lean_ctor_get(v_a_239_, 0);
v_snd_259_ = lean_ctor_get(v_a_239_, 1);
v___x_260_ = lean_name_eq(v_fst_256_, v_fst_258_);
if (v___x_260_ == 0)
{
v___y_254_ = v___x_260_;
goto v___jp_253_;
}
else
{
lean_object* v_fst_261_; lean_object* v_snd_262_; lean_object* v_fst_263_; lean_object* v_snd_264_; size_t v___x_265_; size_t v___x_266_; uint8_t v___x_267_; 
v_fst_261_ = lean_ctor_get(v_snd_257_, 0);
v_snd_262_ = lean_ctor_get(v_snd_257_, 1);
v_fst_263_ = lean_ctor_get(v_snd_259_, 0);
v_snd_264_ = lean_ctor_get(v_snd_259_, 1);
v___x_265_ = lean_ptr_addr(v_fst_261_);
v___x_266_ = lean_ptr_addr(v_fst_263_);
v___x_267_ = lean_usize_dec_eq(v___x_265_, v___x_266_);
if (v___x_267_ == 0)
{
goto v___jp_248_;
}
else
{
uint8_t v___x_268_; 
v___x_268_ = lean_nat_dec_eq(v_snd_262_, v_snd_264_);
v___y_254_ = v___x_268_;
goto v___jp_253_;
}
}
v___jp_248_:
{
lean_object* v___x_249_; lean_object* v___x_251_; 
v___x_249_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__5___redArg(v_a_239_, v_b_240_, v_tail_244_);
if (v_isShared_247_ == 0)
{
lean_ctor_set(v___x_246_, 2, v___x_249_);
v___x_251_ = v___x_246_;
goto v_reusejp_250_;
}
else
{
lean_object* v_reuseFailAlloc_252_; 
v_reuseFailAlloc_252_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_252_, 0, v_key_242_);
lean_ctor_set(v_reuseFailAlloc_252_, 1, v_value_243_);
lean_ctor_set(v_reuseFailAlloc_252_, 2, v___x_249_);
v___x_251_ = v_reuseFailAlloc_252_;
goto v_reusejp_250_;
}
v_reusejp_250_:
{
return v___x_251_;
}
}
v___jp_253_:
{
if (v___y_254_ == 0)
{
goto v___jp_248_;
}
else
{
lean_object* v___x_255_; 
lean_del_object(v___x_246_);
lean_dec(v_value_243_);
lean_dec(v_key_242_);
v___x_255_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_255_, 0, v_a_239_);
lean_ctor_set(v___x_255_, 1, v_b_240_);
lean_ctor_set(v___x_255_, 2, v_tail_244_);
return v___x_255_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2___redArg(lean_object* v_m_270_, lean_object* v_a_271_, lean_object* v_b_272_){
_start:
{
lean_object* v_size_273_; lean_object* v_buckets_274_; lean_object* v___x_276_; uint8_t v_isShared_277_; uint8_t v_isSharedCheck_331_; 
v_size_273_ = lean_ctor_get(v_m_270_, 0);
v_buckets_274_ = lean_ctor_get(v_m_270_, 1);
v_isSharedCheck_331_ = !lean_is_exclusive(v_m_270_);
if (v_isSharedCheck_331_ == 0)
{
v___x_276_ = v_m_270_;
v_isShared_277_ = v_isSharedCheck_331_;
goto v_resetjp_275_;
}
else
{
lean_inc(v_buckets_274_);
lean_inc(v_size_273_);
lean_dec(v_m_270_);
v___x_276_ = lean_box(0);
v_isShared_277_ = v_isSharedCheck_331_;
goto v_resetjp_275_;
}
v_resetjp_275_:
{
lean_object* v_fst_278_; lean_object* v_snd_279_; lean_object* v___x_280_; uint64_t v___y_282_; 
v_fst_278_ = lean_ctor_get(v_a_271_, 0);
v_snd_279_ = lean_ctor_get(v_a_271_, 1);
v___x_280_ = lean_array_get_size(v_buckets_274_);
if (lean_obj_tag(v_fst_278_) == 0)
{
uint64_t v___x_329_; 
v___x_329_ = 1723ULL;
v___y_282_ = v___x_329_;
goto v___jp_281_;
}
else
{
uint64_t v_hash_330_; 
v_hash_330_ = lean_ctor_get_uint64(v_fst_278_, sizeof(void*)*2);
v___y_282_ = v_hash_330_;
goto v___jp_281_;
}
v___jp_281_:
{
lean_object* v_fst_283_; lean_object* v_snd_284_; size_t v___x_285_; size_t v___x_286_; size_t v___x_287_; uint64_t v___x_288_; uint64_t v___x_289_; uint64_t v___x_290_; uint64_t v___x_291_; uint64_t v___x_292_; uint64_t v___x_293_; uint64_t v_fold_294_; uint64_t v___x_295_; uint64_t v___x_296_; uint64_t v___x_297_; size_t v___x_298_; size_t v___x_299_; size_t v___x_300_; size_t v___x_301_; size_t v___x_302_; lean_object* v_bkt_303_; uint8_t v___x_304_; 
v_fst_283_ = lean_ctor_get(v_snd_279_, 0);
v_snd_284_ = lean_ctor_get(v_snd_279_, 1);
v___x_285_ = lean_ptr_addr(v_fst_283_);
v___x_286_ = ((size_t)3ULL);
v___x_287_ = lean_usize_shift_right(v___x_285_, v___x_286_);
v___x_288_ = lean_usize_to_uint64(v___x_287_);
v___x_289_ = lean_uint64_of_nat(v_snd_284_);
v___x_290_ = lean_uint64_mix_hash(v___x_288_, v___x_289_);
v___x_291_ = lean_uint64_mix_hash(v___y_282_, v___x_290_);
v___x_292_ = 32ULL;
v___x_293_ = lean_uint64_shift_right(v___x_291_, v___x_292_);
v_fold_294_ = lean_uint64_xor(v___x_291_, v___x_293_);
v___x_295_ = 16ULL;
v___x_296_ = lean_uint64_shift_right(v_fold_294_, v___x_295_);
v___x_297_ = lean_uint64_xor(v_fold_294_, v___x_296_);
v___x_298_ = lean_uint64_to_usize(v___x_297_);
v___x_299_ = lean_usize_of_nat(v___x_280_);
v___x_300_ = ((size_t)1ULL);
v___x_301_ = lean_usize_sub(v___x_299_, v___x_300_);
v___x_302_ = lean_usize_land(v___x_298_, v___x_301_);
v_bkt_303_ = lean_array_uget_borrowed(v_buckets_274_, v___x_302_);
v___x_304_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__3___redArg(v_a_271_, v_bkt_303_);
if (v___x_304_ == 0)
{
lean_object* v___x_305_; lean_object* v_size_x27_306_; lean_object* v___x_307_; lean_object* v_buckets_x27_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; uint8_t v___x_314_; 
v___x_305_ = lean_unsigned_to_nat(1u);
v_size_x27_306_ = lean_nat_add(v_size_273_, v___x_305_);
lean_dec(v_size_273_);
lean_inc(v_bkt_303_);
v___x_307_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_307_, 0, v_a_271_);
lean_ctor_set(v___x_307_, 1, v_b_272_);
lean_ctor_set(v___x_307_, 2, v_bkt_303_);
v_buckets_x27_308_ = lean_array_uset(v_buckets_274_, v___x_302_, v___x_307_);
v___x_309_ = lean_unsigned_to_nat(4u);
v___x_310_ = lean_nat_mul(v_size_x27_306_, v___x_309_);
v___x_311_ = lean_unsigned_to_nat(3u);
v___x_312_ = lean_nat_div(v___x_310_, v___x_311_);
lean_dec(v___x_310_);
v___x_313_ = lean_array_get_size(v_buckets_x27_308_);
v___x_314_ = lean_nat_dec_le(v___x_312_, v___x_313_);
lean_dec(v___x_312_);
if (v___x_314_ == 0)
{
lean_object* v_val_315_; lean_object* v___x_317_; 
v_val_315_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__4___redArg(v_buckets_x27_308_);
if (v_isShared_277_ == 0)
{
lean_ctor_set(v___x_276_, 1, v_val_315_);
lean_ctor_set(v___x_276_, 0, v_size_x27_306_);
v___x_317_ = v___x_276_;
goto v_reusejp_316_;
}
else
{
lean_object* v_reuseFailAlloc_318_; 
v_reuseFailAlloc_318_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_318_, 0, v_size_x27_306_);
lean_ctor_set(v_reuseFailAlloc_318_, 1, v_val_315_);
v___x_317_ = v_reuseFailAlloc_318_;
goto v_reusejp_316_;
}
v_reusejp_316_:
{
return v___x_317_;
}
}
else
{
lean_object* v___x_320_; 
if (v_isShared_277_ == 0)
{
lean_ctor_set(v___x_276_, 1, v_buckets_x27_308_);
lean_ctor_set(v___x_276_, 0, v_size_x27_306_);
v___x_320_ = v___x_276_;
goto v_reusejp_319_;
}
else
{
lean_object* v_reuseFailAlloc_321_; 
v_reuseFailAlloc_321_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_321_, 0, v_size_x27_306_);
lean_ctor_set(v_reuseFailAlloc_321_, 1, v_buckets_x27_308_);
v___x_320_ = v_reuseFailAlloc_321_;
goto v_reusejp_319_;
}
v_reusejp_319_:
{
return v___x_320_;
}
}
}
else
{
lean_object* v___x_322_; lean_object* v_buckets_x27_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_327_; 
lean_inc(v_bkt_303_);
v___x_322_ = lean_box(0);
v_buckets_x27_323_ = lean_array_uset(v_buckets_274_, v___x_302_, v___x_322_);
v___x_324_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__5___redArg(v_a_271_, v_b_272_, v_bkt_303_);
v___x_325_ = lean_array_uset(v_buckets_x27_323_, v___x_302_, v___x_324_);
if (v_isShared_277_ == 0)
{
lean_ctor_set(v___x_276_, 1, v___x_325_);
v___x_327_ = v___x_276_;
goto v_reusejp_326_;
}
else
{
lean_object* v_reuseFailAlloc_328_; 
v_reuseFailAlloc_328_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_328_, 0, v_size_273_);
lean_ctor_set(v_reuseFailAlloc_328_, 1, v___x_325_);
v___x_327_ = v_reuseFailAlloc_328_;
goto v_reusejp_326_;
}
v_reusejp_326_:
{
return v___x_327_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__0_spec__0___redArg(lean_object* v_a_332_, lean_object* v_x_333_){
_start:
{
if (lean_obj_tag(v_x_333_) == 0)
{
lean_object* v___x_334_; 
v___x_334_ = lean_box(0);
return v___x_334_;
}
else
{
lean_object* v_key_335_; lean_object* v_value_336_; lean_object* v_tail_337_; uint8_t v___y_339_; lean_object* v_fst_342_; lean_object* v_snd_343_; lean_object* v_fst_344_; lean_object* v_snd_345_; uint8_t v___x_346_; 
v_key_335_ = lean_ctor_get(v_x_333_, 0);
v_value_336_ = lean_ctor_get(v_x_333_, 1);
v_tail_337_ = lean_ctor_get(v_x_333_, 2);
v_fst_342_ = lean_ctor_get(v_key_335_, 0);
v_snd_343_ = lean_ctor_get(v_key_335_, 1);
v_fst_344_ = lean_ctor_get(v_a_332_, 0);
v_snd_345_ = lean_ctor_get(v_a_332_, 1);
v___x_346_ = lean_name_eq(v_fst_342_, v_fst_344_);
if (v___x_346_ == 0)
{
v___y_339_ = v___x_346_;
goto v___jp_338_;
}
else
{
lean_object* v_fst_347_; lean_object* v_snd_348_; lean_object* v_fst_349_; lean_object* v_snd_350_; size_t v___x_351_; size_t v___x_352_; uint8_t v___x_353_; 
v_fst_347_ = lean_ctor_get(v_snd_343_, 0);
v_snd_348_ = lean_ctor_get(v_snd_343_, 1);
v_fst_349_ = lean_ctor_get(v_snd_345_, 0);
v_snd_350_ = lean_ctor_get(v_snd_345_, 1);
v___x_351_ = lean_ptr_addr(v_fst_347_);
v___x_352_ = lean_ptr_addr(v_fst_349_);
v___x_353_ = lean_usize_dec_eq(v___x_351_, v___x_352_);
if (v___x_353_ == 0)
{
v_x_333_ = v_tail_337_;
goto _start;
}
else
{
uint8_t v___x_355_; 
v___x_355_ = lean_nat_dec_eq(v_snd_348_, v_snd_350_);
v___y_339_ = v___x_355_;
goto v___jp_338_;
}
}
v___jp_338_:
{
if (v___y_339_ == 0)
{
v_x_333_ = v_tail_337_;
goto _start;
}
else
{
lean_object* v___x_341_; 
lean_inc(v_value_336_);
v___x_341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_341_, 0, v_value_336_);
return v___x_341_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__0_spec__0___redArg___boxed(lean_object* v_a_356_, lean_object* v_x_357_){
_start:
{
lean_object* v_res_358_; 
v_res_358_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__0_spec__0___redArg(v_a_356_, v_x_357_);
lean_dec(v_x_357_);
lean_dec_ref(v_a_356_);
return v_res_358_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg(lean_object* v_m_359_, lean_object* v_a_360_){
_start:
{
lean_object* v_buckets_361_; lean_object* v_fst_362_; lean_object* v_snd_363_; lean_object* v___x_364_; uint64_t v___y_366_; 
v_buckets_361_ = lean_ctor_get(v_m_359_, 1);
v_fst_362_ = lean_ctor_get(v_a_360_, 0);
v_snd_363_ = lean_ctor_get(v_a_360_, 1);
v___x_364_ = lean_array_get_size(v_buckets_361_);
if (lean_obj_tag(v_fst_362_) == 0)
{
uint64_t v___x_389_; 
v___x_389_ = 1723ULL;
v___y_366_ = v___x_389_;
goto v___jp_365_;
}
else
{
uint64_t v_hash_390_; 
v_hash_390_ = lean_ctor_get_uint64(v_fst_362_, sizeof(void*)*2);
v___y_366_ = v_hash_390_;
goto v___jp_365_;
}
v___jp_365_:
{
lean_object* v_fst_367_; lean_object* v_snd_368_; size_t v___x_369_; size_t v___x_370_; size_t v___x_371_; uint64_t v___x_372_; uint64_t v___x_373_; uint64_t v___x_374_; uint64_t v___x_375_; uint64_t v___x_376_; uint64_t v___x_377_; uint64_t v_fold_378_; uint64_t v___x_379_; uint64_t v___x_380_; uint64_t v___x_381_; size_t v___x_382_; size_t v___x_383_; size_t v___x_384_; size_t v___x_385_; size_t v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; 
v_fst_367_ = lean_ctor_get(v_snd_363_, 0);
v_snd_368_ = lean_ctor_get(v_snd_363_, 1);
v___x_369_ = lean_ptr_addr(v_fst_367_);
v___x_370_ = ((size_t)3ULL);
v___x_371_ = lean_usize_shift_right(v___x_369_, v___x_370_);
v___x_372_ = lean_usize_to_uint64(v___x_371_);
v___x_373_ = lean_uint64_of_nat(v_snd_368_);
v___x_374_ = lean_uint64_mix_hash(v___x_372_, v___x_373_);
v___x_375_ = lean_uint64_mix_hash(v___y_366_, v___x_374_);
v___x_376_ = 32ULL;
v___x_377_ = lean_uint64_shift_right(v___x_375_, v___x_376_);
v_fold_378_ = lean_uint64_xor(v___x_375_, v___x_377_);
v___x_379_ = 16ULL;
v___x_380_ = lean_uint64_shift_right(v_fold_378_, v___x_379_);
v___x_381_ = lean_uint64_xor(v_fold_378_, v___x_380_);
v___x_382_ = lean_uint64_to_usize(v___x_381_);
v___x_383_ = lean_usize_of_nat(v___x_364_);
v___x_384_ = ((size_t)1ULL);
v___x_385_ = lean_usize_sub(v___x_383_, v___x_384_);
v___x_386_ = lean_usize_land(v___x_382_, v___x_385_);
v___x_387_ = lean_array_uget_borrowed(v_buckets_361_, v___x_386_);
v___x_388_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__0_spec__0___redArg(v_a_360_, v___x_387_);
return v___x_388_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg___boxed(lean_object* v_m_391_, lean_object* v_a_392_){
_start:
{
lean_object* v_res_393_; 
v_res_393_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg(v_m_391_, v_a_392_);
lean_dec_ref(v_a_392_);
lean_dec_ref(v_m_391_);
return v_res_393_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached(lean_object* v_specThm_396_, lean_object* v_info_397_, lean_object* v_a_398_, lean_object* v_a_399_, lean_object* v_a_400_, lean_object* v_a_401_, lean_object* v_a_402_, lean_object* v_a_403_, lean_object* v_a_404_, lean_object* v_a_405_, lean_object* v_a_406_, lean_object* v_a_407_, lean_object* v_a_408_){
_start:
{
lean_object* v___x_410_; lean_object* v_proof_411_; lean_object* v_excessArgs_412_; lean_object* v_specBackwardRuleCache_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v_key_418_; lean_object* v___x_419_; 
v___x_410_ = lean_st_ref_get(v_a_399_);
v_proof_411_ = lean_ctor_get(v_specThm_396_, 1);
v_excessArgs_412_ = lean_ctor_get(v_info_397_, 3);
v_specBackwardRuleCache_413_ = lean_ctor_get(v___x_410_, 0);
lean_inc_ref(v_specBackwardRuleCache_413_);
lean_dec(v___x_410_);
v___x_414_ = l_Lean_Elab_Tactic_VCGen_SpecAttr_SpecProof_key(v_proof_411_);
v___x_415_ = l_Lean_Elab_Tactic_VCGen_WPApp_instWP(v_info_397_);
v___x_416_ = lean_array_get_size(v_excessArgs_412_);
v___x_417_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_417_, 0, v___x_415_);
lean_ctor_set(v___x_417_, 1, v___x_416_);
v_key_418_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_key_418_, 0, v___x_414_);
lean_ctor_set(v_key_418_, 1, v___x_417_);
v___x_419_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg(v_specBackwardRuleCache_413_, v_key_418_);
lean_dec_ref(v_specBackwardRuleCache_413_);
if (lean_obj_tag(v___x_419_) == 1)
{
lean_object* v___x_420_; 
lean_dec_ref_known(v_key_418_, 2);
lean_dec_ref(v_info_397_);
lean_dec_ref(v_specThm_396_);
v___x_420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_420_, 0, v___x_419_);
return v___x_420_;
}
else
{
lean_object* v___x_421_; lean_object* v___f_422_; uint8_t v___x_423_; lean_object* v___x_424_; 
lean_dec(v___x_419_);
v___x_421_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached___closed__0));
v___f_422_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached___lam__0___boxed), 15, 3);
lean_closure_set(v___f_422_, 0, v_specThm_396_);
lean_closure_set(v___f_422_, 1, v_info_397_);
lean_closure_set(v___f_422_, 2, v___x_421_);
v___x_423_ = 0;
v___x_424_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__1___redArg(v___f_422_, v___x_423_, v_a_398_, v_a_399_, v_a_400_, v_a_401_, v_a_402_, v_a_403_, v_a_404_, v_a_405_, v_a_406_, v_a_407_, v_a_408_);
if (lean_obj_tag(v___x_424_) == 0)
{
lean_object* v_a_425_; lean_object* v___x_427_; uint8_t v_isShared_428_; uint8_t v_isSharedCheck_483_; 
v_a_425_ = lean_ctor_get(v___x_424_, 0);
v_isSharedCheck_483_ = !lean_is_exclusive(v___x_424_);
if (v_isSharedCheck_483_ == 0)
{
v___x_427_ = v___x_424_;
v_isShared_428_ = v_isSharedCheck_483_;
goto v_resetjp_426_;
}
else
{
lean_inc(v_a_425_);
lean_dec(v___x_424_);
v___x_427_ = lean_box(0);
v_isShared_428_ = v_isSharedCheck_483_;
goto v_resetjp_426_;
}
v_resetjp_426_:
{
if (lean_obj_tag(v_a_425_) == 0)
{
lean_object* v___x_429_; lean_object* v___x_431_; 
lean_dec_ref_known(v_key_418_, 2);
v___x_429_ = lean_box(0);
if (v_isShared_428_ == 0)
{
lean_ctor_set(v___x_427_, 0, v___x_429_);
v___x_431_ = v___x_427_;
goto v_reusejp_430_;
}
else
{
lean_object* v_reuseFailAlloc_432_; 
v_reuseFailAlloc_432_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_432_, 0, v___x_429_);
v___x_431_ = v_reuseFailAlloc_432_;
goto v_reusejp_430_;
}
v_reusejp_430_:
{
return v___x_431_;
}
}
else
{
lean_object* v_val_433_; 
v_val_433_ = lean_ctor_get(v_a_425_, 0);
lean_inc(v_val_433_);
lean_dec_ref_known(v_a_425_, 1);
if (lean_obj_tag(v_val_433_) == 1)
{
lean_object* v_val_434_; lean_object* v___x_436_; uint8_t v_isShared_437_; uint8_t v_isSharedCheck_478_; 
lean_del_object(v___x_427_);
v_val_434_ = lean_ctor_get(v_val_433_, 0);
v_isSharedCheck_478_ = !lean_is_exclusive(v_val_433_);
if (v_isSharedCheck_478_ == 0)
{
v___x_436_ = v_val_433_;
v_isShared_437_ = v_isSharedCheck_478_;
goto v_resetjp_435_;
}
else
{
lean_inc(v_val_434_);
lean_dec(v_val_433_);
v___x_436_ = lean_box(0);
v_isShared_437_ = v_isSharedCheck_478_;
goto v_resetjp_435_;
}
v_resetjp_435_:
{
lean_object* v___x_438_; 
v___x_438_ = l_Lean_Meta_Sym_BackwardRule_shareCommon(v_val_434_, v_a_403_, v_a_404_, v_a_405_, v_a_406_, v_a_407_, v_a_408_);
if (lean_obj_tag(v___x_438_) == 0)
{
lean_object* v_a_439_; lean_object* v___x_441_; uint8_t v_isShared_442_; uint8_t v_isSharedCheck_469_; 
v_a_439_ = lean_ctor_get(v___x_438_, 0);
v_isSharedCheck_469_ = !lean_is_exclusive(v___x_438_);
if (v_isSharedCheck_469_ == 0)
{
v___x_441_ = v___x_438_;
v_isShared_442_ = v_isSharedCheck_469_;
goto v_resetjp_440_;
}
else
{
lean_inc(v_a_439_);
lean_dec(v___x_438_);
v___x_441_ = lean_box(0);
v_isShared_442_ = v_isSharedCheck_469_;
goto v_resetjp_440_;
}
v_resetjp_440_:
{
lean_object* v___x_443_; lean_object* v_specBackwardRuleCache_444_; lean_object* v_splitBackwardRuleCache_445_; lean_object* v_latticeBackwardRuleCache_446_; lean_object* v_frameBackwardRuleCache_447_; lean_object* v_frameDB_448_; lean_object* v_invariants_449_; lean_object* v_vcs_450_; lean_object* v_simpState_451_; lean_object* v_fuel_452_; lean_object* v_inlineHandledInvariants_453_; lean_object* v___x_455_; uint8_t v_isShared_456_; uint8_t v_isSharedCheck_468_; 
v___x_443_ = lean_st_ref_take(v_a_399_);
v_specBackwardRuleCache_444_ = lean_ctor_get(v___x_443_, 0);
v_splitBackwardRuleCache_445_ = lean_ctor_get(v___x_443_, 1);
v_latticeBackwardRuleCache_446_ = lean_ctor_get(v___x_443_, 2);
v_frameBackwardRuleCache_447_ = lean_ctor_get(v___x_443_, 3);
v_frameDB_448_ = lean_ctor_get(v___x_443_, 4);
v_invariants_449_ = lean_ctor_get(v___x_443_, 5);
v_vcs_450_ = lean_ctor_get(v___x_443_, 6);
v_simpState_451_ = lean_ctor_get(v___x_443_, 7);
v_fuel_452_ = lean_ctor_get(v___x_443_, 8);
v_inlineHandledInvariants_453_ = lean_ctor_get(v___x_443_, 9);
v_isSharedCheck_468_ = !lean_is_exclusive(v___x_443_);
if (v_isSharedCheck_468_ == 0)
{
v___x_455_ = v___x_443_;
v_isShared_456_ = v_isSharedCheck_468_;
goto v_resetjp_454_;
}
else
{
lean_inc(v_inlineHandledInvariants_453_);
lean_inc(v_fuel_452_);
lean_inc(v_simpState_451_);
lean_inc(v_vcs_450_);
lean_inc(v_invariants_449_);
lean_inc(v_frameDB_448_);
lean_inc(v_frameBackwardRuleCache_447_);
lean_inc(v_latticeBackwardRuleCache_446_);
lean_inc(v_splitBackwardRuleCache_445_);
lean_inc(v_specBackwardRuleCache_444_);
lean_dec(v___x_443_);
v___x_455_ = lean_box(0);
v_isShared_456_ = v_isSharedCheck_468_;
goto v_resetjp_454_;
}
v_resetjp_454_:
{
lean_object* v___x_458_; 
lean_inc(v_a_439_);
if (v_isShared_437_ == 0)
{
lean_ctor_set(v___x_436_, 0, v_a_439_);
v___x_458_ = v___x_436_;
goto v_reusejp_457_;
}
else
{
lean_object* v_reuseFailAlloc_467_; 
v_reuseFailAlloc_467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_467_, 0, v_a_439_);
v___x_458_ = v_reuseFailAlloc_467_;
goto v_reusejp_457_;
}
v_reusejp_457_:
{
lean_object* v___x_459_; lean_object* v___x_461_; 
v___x_459_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2___redArg(v_specBackwardRuleCache_444_, v_key_418_, v_a_439_);
if (v_isShared_456_ == 0)
{
lean_ctor_set(v___x_455_, 0, v___x_459_);
v___x_461_ = v___x_455_;
goto v_reusejp_460_;
}
else
{
lean_object* v_reuseFailAlloc_466_; 
v_reuseFailAlloc_466_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_466_, 0, v___x_459_);
lean_ctor_set(v_reuseFailAlloc_466_, 1, v_splitBackwardRuleCache_445_);
lean_ctor_set(v_reuseFailAlloc_466_, 2, v_latticeBackwardRuleCache_446_);
lean_ctor_set(v_reuseFailAlloc_466_, 3, v_frameBackwardRuleCache_447_);
lean_ctor_set(v_reuseFailAlloc_466_, 4, v_frameDB_448_);
lean_ctor_set(v_reuseFailAlloc_466_, 5, v_invariants_449_);
lean_ctor_set(v_reuseFailAlloc_466_, 6, v_vcs_450_);
lean_ctor_set(v_reuseFailAlloc_466_, 7, v_simpState_451_);
lean_ctor_set(v_reuseFailAlloc_466_, 8, v_fuel_452_);
lean_ctor_set(v_reuseFailAlloc_466_, 9, v_inlineHandledInvariants_453_);
v___x_461_ = v_reuseFailAlloc_466_;
goto v_reusejp_460_;
}
v_reusejp_460_:
{
lean_object* v___x_462_; lean_object* v___x_464_; 
v___x_462_ = lean_st_ref_put(v_a_399_, v___x_461_);
if (v_isShared_442_ == 0)
{
lean_ctor_set(v___x_441_, 0, v___x_458_);
v___x_464_ = v___x_441_;
goto v_reusejp_463_;
}
else
{
lean_object* v_reuseFailAlloc_465_; 
v_reuseFailAlloc_465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_465_, 0, v___x_458_);
v___x_464_ = v_reuseFailAlloc_465_;
goto v_reusejp_463_;
}
v_reusejp_463_:
{
return v___x_464_;
}
}
}
}
}
}
else
{
lean_object* v_a_470_; lean_object* v___x_472_; uint8_t v_isShared_473_; uint8_t v_isSharedCheck_477_; 
lean_del_object(v___x_436_);
lean_dec_ref_known(v_key_418_, 2);
v_a_470_ = lean_ctor_get(v___x_438_, 0);
v_isSharedCheck_477_ = !lean_is_exclusive(v___x_438_);
if (v_isSharedCheck_477_ == 0)
{
v___x_472_ = v___x_438_;
v_isShared_473_ = v_isSharedCheck_477_;
goto v_resetjp_471_;
}
else
{
lean_inc(v_a_470_);
lean_dec(v___x_438_);
v___x_472_ = lean_box(0);
v_isShared_473_ = v_isSharedCheck_477_;
goto v_resetjp_471_;
}
v_resetjp_471_:
{
lean_object* v___x_475_; 
if (v_isShared_473_ == 0)
{
v___x_475_ = v___x_472_;
goto v_reusejp_474_;
}
else
{
lean_object* v_reuseFailAlloc_476_; 
v_reuseFailAlloc_476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_476_, 0, v_a_470_);
v___x_475_ = v_reuseFailAlloc_476_;
goto v_reusejp_474_;
}
v_reusejp_474_:
{
return v___x_475_;
}
}
}
}
}
else
{
lean_object* v___x_479_; lean_object* v___x_481_; 
lean_dec(v_val_433_);
lean_dec_ref_known(v_key_418_, 2);
v___x_479_ = lean_box(0);
if (v_isShared_428_ == 0)
{
lean_ctor_set(v___x_427_, 0, v___x_479_);
v___x_481_ = v___x_427_;
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
}
}
else
{
lean_object* v_a_484_; lean_object* v___x_486_; uint8_t v_isShared_487_; uint8_t v_isSharedCheck_491_; 
lean_dec_ref_known(v_key_418_, 2);
v_a_484_ = lean_ctor_get(v___x_424_, 0);
v_isSharedCheck_491_ = !lean_is_exclusive(v___x_424_);
if (v_isSharedCheck_491_ == 0)
{
v___x_486_ = v___x_424_;
v_isShared_487_ = v_isSharedCheck_491_;
goto v_resetjp_485_;
}
else
{
lean_inc(v_a_484_);
lean_dec(v___x_424_);
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
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached___boxed(lean_object* v_specThm_492_, lean_object* v_info_493_, lean_object* v_a_494_, lean_object* v_a_495_, lean_object* v_a_496_, lean_object* v_a_497_, lean_object* v_a_498_, lean_object* v_a_499_, lean_object* v_a_500_, lean_object* v_a_501_, lean_object* v_a_502_, lean_object* v_a_503_, lean_object* v_a_504_, lean_object* v_a_505_){
_start:
{
lean_object* v_res_506_; 
v_res_506_ = l_Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached(v_specThm_492_, v_info_493_, v_a_494_, v_a_495_, v_a_496_, v_a_497_, v_a_498_, v_a_499_, v_a_500_, v_a_501_, v_a_502_, v_a_503_, v_a_504_);
lean_dec(v_a_504_);
lean_dec_ref(v_a_503_);
lean_dec(v_a_502_);
lean_dec_ref(v_a_501_);
lean_dec(v_a_500_);
lean_dec_ref(v_a_499_);
lean_dec(v_a_498_);
lean_dec_ref(v_a_497_);
lean_dec(v_a_496_);
lean_dec(v_a_495_);
lean_dec_ref(v_a_494_);
return v_res_506_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__0(lean_object* v_00_u03b2_507_, lean_object* v_m_508_, lean_object* v_a_509_){
_start:
{
lean_object* v___x_510_; 
v___x_510_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg(v_m_508_, v_a_509_);
return v___x_510_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__0___boxed(lean_object* v_00_u03b2_511_, lean_object* v_m_512_, lean_object* v_a_513_){
_start:
{
lean_object* v_res_514_; 
v_res_514_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__0(v_00_u03b2_511_, v_m_512_, v_a_513_);
lean_dec_ref(v_a_513_);
lean_dec_ref(v_m_512_);
return v_res_514_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2(lean_object* v_00_u03b2_515_, lean_object* v_m_516_, lean_object* v_a_517_, lean_object* v_b_518_){
_start:
{
lean_object* v___x_519_; 
v___x_519_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2___redArg(v_m_516_, v_a_517_, v_b_518_);
return v___x_519_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__0_spec__0(lean_object* v_00_u03b2_520_, lean_object* v_a_521_, lean_object* v_x_522_){
_start:
{
lean_object* v___x_523_; 
v___x_523_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__0_spec__0___redArg(v_a_521_, v_x_522_);
return v___x_523_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__0_spec__0___boxed(lean_object* v_00_u03b2_524_, lean_object* v_a_525_, lean_object* v_x_526_){
_start:
{
lean_object* v_res_527_; 
v_res_527_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__0_spec__0(v_00_u03b2_524_, v_a_525_, v_x_526_);
lean_dec(v_x_526_);
lean_dec_ref(v_a_525_);
return v_res_527_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__3(lean_object* v_00_u03b2_528_, lean_object* v_a_529_, lean_object* v_x_530_){
_start:
{
uint8_t v___x_531_; 
v___x_531_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__3___redArg(v_a_529_, v_x_530_);
return v___x_531_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__3___boxed(lean_object* v_00_u03b2_532_, lean_object* v_a_533_, lean_object* v_x_534_){
_start:
{
uint8_t v_res_535_; lean_object* v_r_536_; 
v_res_535_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__3(v_00_u03b2_532_, v_a_533_, v_x_534_);
lean_dec(v_x_534_);
lean_dec_ref(v_a_533_);
v_r_536_ = lean_box(v_res_535_);
return v_r_536_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__4(lean_object* v_00_u03b2_537_, lean_object* v_data_538_){
_start:
{
lean_object* v___x_539_; 
v___x_539_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__4___redArg(v_data_538_);
return v___x_539_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__5(lean_object* v_00_u03b2_540_, lean_object* v_a_541_, lean_object* v_b_542_, lean_object* v_x_543_){
_start:
{
lean_object* v___x_544_; 
v___x_544_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__5___redArg(v_a_541_, v_b_542_, v_x_543_);
return v___x_544_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_545_, lean_object* v_i_546_, lean_object* v_source_547_, lean_object* v_target_548_){
_start:
{
lean_object* v___x_549_; 
v___x_549_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__4_spec__5___redArg(v_i_546_, v_source_547_, v_target_548_);
return v___x_549_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__4_spec__5_spec__6(lean_object* v_00_u03b2_550_, lean_object* v_x_551_, lean_object* v_x_552_){
_start:
{
lean_object* v___x_553_; 
v___x_553_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__4_spec__5_spec__6___redArg(v_x_551_, v_x_552_);
return v___x_553_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_mkBackwardRuleForSplitCached___redArg(lean_object* v_splitInfo_563_, lean_object* v_info_564_, lean_object* v_a_565_, lean_object* v_a_566_, lean_object* v_a_567_, lean_object* v_a_568_, lean_object* v_a_569_, lean_object* v_a_570_, lean_object* v_a_571_){
_start:
{
lean_object* v___y_574_; 
switch(lean_obj_tag(v_splitInfo_563_))
{
case 0:
{
lean_object* v___x_622_; 
v___x_622_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_mkBackwardRuleForSplitCached___redArg___closed__1));
v___y_574_ = v___x_622_;
goto v___jp_573_;
}
case 1:
{
lean_object* v___x_623_; 
v___x_623_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_mkBackwardRuleForSplitCached___redArg___closed__3));
v___y_574_ = v___x_623_;
goto v___jp_573_;
}
case 2:
{
lean_object* v___x_624_; 
v___x_624_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_mkBackwardRuleForSplitCached___redArg___closed__5));
v___y_574_ = v___x_624_;
goto v___jp_573_;
}
default: 
{
lean_object* v_matcherApp_625_; lean_object* v_matcherName_626_; 
v_matcherApp_625_ = lean_ctor_get(v_splitInfo_563_, 0);
v_matcherName_626_ = lean_ctor_get(v_matcherApp_625_, 1);
lean_inc(v_matcherName_626_);
v___y_574_ = v_matcherName_626_;
goto v___jp_573_;
}
}
v___jp_573_:
{
lean_object* v___x_575_; lean_object* v_excessArgs_576_; lean_object* v_splitBackwardRuleCache_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v_key_581_; lean_object* v___x_582_; 
v___x_575_ = lean_st_ref_get(v_a_565_);
v_excessArgs_576_ = lean_ctor_get(v_info_564_, 3);
v_splitBackwardRuleCache_577_ = lean_ctor_get(v___x_575_, 1);
lean_inc_ref(v_splitBackwardRuleCache_577_);
lean_dec(v___x_575_);
v___x_578_ = l_Lean_Elab_Tactic_VCGen_WPApp_instWP(v_info_564_);
v___x_579_ = lean_array_get_size(v_excessArgs_576_);
v___x_580_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_580_, 0, v___x_578_);
lean_ctor_set(v___x_580_, 1, v___x_579_);
v_key_581_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_key_581_, 0, v___y_574_);
lean_ctor_set(v_key_581_, 1, v___x_580_);
v___x_582_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg(v_splitBackwardRuleCache_577_, v_key_581_);
lean_dec_ref(v_splitBackwardRuleCache_577_);
if (lean_obj_tag(v___x_582_) == 1)
{
lean_object* v_val_583_; lean_object* v___x_585_; uint8_t v_isShared_586_; uint8_t v_isSharedCheck_590_; 
lean_dec_ref_known(v_key_581_, 2);
lean_dec_ref(v_info_564_);
lean_dec_ref(v_splitInfo_563_);
v_val_583_ = lean_ctor_get(v___x_582_, 0);
v_isSharedCheck_590_ = !lean_is_exclusive(v___x_582_);
if (v_isSharedCheck_590_ == 0)
{
v___x_585_ = v___x_582_;
v_isShared_586_ = v_isSharedCheck_590_;
goto v_resetjp_584_;
}
else
{
lean_inc(v_val_583_);
lean_dec(v___x_582_);
v___x_585_ = lean_box(0);
v_isShared_586_ = v_isSharedCheck_590_;
goto v_resetjp_584_;
}
v_resetjp_584_:
{
lean_object* v___x_588_; 
if (v_isShared_586_ == 0)
{
lean_ctor_set_tag(v___x_585_, 0);
v___x_588_ = v___x_585_;
goto v_reusejp_587_;
}
else
{
lean_object* v_reuseFailAlloc_589_; 
v_reuseFailAlloc_589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_589_, 0, v_val_583_);
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
lean_object* v___x_591_; 
lean_dec(v___x_582_);
v___x_591_ = l_Lean_Elab_Tactic_VCGen_mkBackwardRuleForSplit(v_splitInfo_563_, v_info_564_, v_a_568_, v_a_569_, v_a_570_, v_a_571_);
if (lean_obj_tag(v___x_591_) == 0)
{
lean_object* v_a_592_; lean_object* v___x_593_; 
v_a_592_ = lean_ctor_get(v___x_591_, 0);
lean_inc(v_a_592_);
lean_dec_ref_known(v___x_591_, 1);
v___x_593_ = l_Lean_Meta_Sym_BackwardRule_shareCommon(v_a_592_, v_a_566_, v_a_567_, v_a_568_, v_a_569_, v_a_570_, v_a_571_);
if (lean_obj_tag(v___x_593_) == 0)
{
lean_object* v_a_594_; lean_object* v___x_596_; uint8_t v_isShared_597_; uint8_t v_isSharedCheck_621_; 
v_a_594_ = lean_ctor_get(v___x_593_, 0);
v_isSharedCheck_621_ = !lean_is_exclusive(v___x_593_);
if (v_isSharedCheck_621_ == 0)
{
v___x_596_ = v___x_593_;
v_isShared_597_ = v_isSharedCheck_621_;
goto v_resetjp_595_;
}
else
{
lean_inc(v_a_594_);
lean_dec(v___x_593_);
v___x_596_ = lean_box(0);
v_isShared_597_ = v_isSharedCheck_621_;
goto v_resetjp_595_;
}
v_resetjp_595_:
{
lean_object* v___x_598_; lean_object* v_specBackwardRuleCache_599_; lean_object* v_splitBackwardRuleCache_600_; lean_object* v_latticeBackwardRuleCache_601_; lean_object* v_frameBackwardRuleCache_602_; lean_object* v_frameDB_603_; lean_object* v_invariants_604_; lean_object* v_vcs_605_; lean_object* v_simpState_606_; lean_object* v_fuel_607_; lean_object* v_inlineHandledInvariants_608_; lean_object* v___x_610_; uint8_t v_isShared_611_; uint8_t v_isSharedCheck_620_; 
v___x_598_ = lean_st_ref_take(v_a_565_);
v_specBackwardRuleCache_599_ = lean_ctor_get(v___x_598_, 0);
v_splitBackwardRuleCache_600_ = lean_ctor_get(v___x_598_, 1);
v_latticeBackwardRuleCache_601_ = lean_ctor_get(v___x_598_, 2);
v_frameBackwardRuleCache_602_ = lean_ctor_get(v___x_598_, 3);
v_frameDB_603_ = lean_ctor_get(v___x_598_, 4);
v_invariants_604_ = lean_ctor_get(v___x_598_, 5);
v_vcs_605_ = lean_ctor_get(v___x_598_, 6);
v_simpState_606_ = lean_ctor_get(v___x_598_, 7);
v_fuel_607_ = lean_ctor_get(v___x_598_, 8);
v_inlineHandledInvariants_608_ = lean_ctor_get(v___x_598_, 9);
v_isSharedCheck_620_ = !lean_is_exclusive(v___x_598_);
if (v_isSharedCheck_620_ == 0)
{
v___x_610_ = v___x_598_;
v_isShared_611_ = v_isSharedCheck_620_;
goto v_resetjp_609_;
}
else
{
lean_inc(v_inlineHandledInvariants_608_);
lean_inc(v_fuel_607_);
lean_inc(v_simpState_606_);
lean_inc(v_vcs_605_);
lean_inc(v_invariants_604_);
lean_inc(v_frameDB_603_);
lean_inc(v_frameBackwardRuleCache_602_);
lean_inc(v_latticeBackwardRuleCache_601_);
lean_inc(v_splitBackwardRuleCache_600_);
lean_inc(v_specBackwardRuleCache_599_);
lean_dec(v___x_598_);
v___x_610_ = lean_box(0);
v_isShared_611_ = v_isSharedCheck_620_;
goto v_resetjp_609_;
}
v_resetjp_609_:
{
lean_object* v___x_612_; lean_object* v___x_614_; 
lean_inc(v_a_594_);
v___x_612_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2___redArg(v_splitBackwardRuleCache_600_, v_key_581_, v_a_594_);
if (v_isShared_611_ == 0)
{
lean_ctor_set(v___x_610_, 1, v___x_612_);
v___x_614_ = v___x_610_;
goto v_reusejp_613_;
}
else
{
lean_object* v_reuseFailAlloc_619_; 
v_reuseFailAlloc_619_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_619_, 0, v_specBackwardRuleCache_599_);
lean_ctor_set(v_reuseFailAlloc_619_, 1, v___x_612_);
lean_ctor_set(v_reuseFailAlloc_619_, 2, v_latticeBackwardRuleCache_601_);
lean_ctor_set(v_reuseFailAlloc_619_, 3, v_frameBackwardRuleCache_602_);
lean_ctor_set(v_reuseFailAlloc_619_, 4, v_frameDB_603_);
lean_ctor_set(v_reuseFailAlloc_619_, 5, v_invariants_604_);
lean_ctor_set(v_reuseFailAlloc_619_, 6, v_vcs_605_);
lean_ctor_set(v_reuseFailAlloc_619_, 7, v_simpState_606_);
lean_ctor_set(v_reuseFailAlloc_619_, 8, v_fuel_607_);
lean_ctor_set(v_reuseFailAlloc_619_, 9, v_inlineHandledInvariants_608_);
v___x_614_ = v_reuseFailAlloc_619_;
goto v_reusejp_613_;
}
v_reusejp_613_:
{
lean_object* v___x_615_; lean_object* v___x_617_; 
v___x_615_ = lean_st_ref_put(v_a_565_, v___x_614_);
if (v_isShared_597_ == 0)
{
v___x_617_ = v___x_596_;
goto v_reusejp_616_;
}
else
{
lean_object* v_reuseFailAlloc_618_; 
v_reuseFailAlloc_618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_618_, 0, v_a_594_);
v___x_617_ = v_reuseFailAlloc_618_;
goto v_reusejp_616_;
}
v_reusejp_616_:
{
return v___x_617_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_key_581_, 2);
return v___x_593_;
}
}
else
{
lean_dec_ref_known(v_key_581_, 2);
return v___x_591_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_mkBackwardRuleForSplitCached___redArg___boxed(lean_object* v_splitInfo_627_, lean_object* v_info_628_, lean_object* v_a_629_, lean_object* v_a_630_, lean_object* v_a_631_, lean_object* v_a_632_, lean_object* v_a_633_, lean_object* v_a_634_, lean_object* v_a_635_, lean_object* v_a_636_){
_start:
{
lean_object* v_res_637_; 
v_res_637_ = l_Lean_Elab_Tactic_VCGen_mkBackwardRuleForSplitCached___redArg(v_splitInfo_627_, v_info_628_, v_a_629_, v_a_630_, v_a_631_, v_a_632_, v_a_633_, v_a_634_, v_a_635_);
lean_dec(v_a_635_);
lean_dec_ref(v_a_634_);
lean_dec(v_a_633_);
lean_dec_ref(v_a_632_);
lean_dec(v_a_631_);
lean_dec_ref(v_a_630_);
lean_dec(v_a_629_);
return v_res_637_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_mkBackwardRuleForSplitCached(lean_object* v_splitInfo_638_, lean_object* v_info_639_, lean_object* v_a_640_, lean_object* v_a_641_, lean_object* v_a_642_, lean_object* v_a_643_, lean_object* v_a_644_, lean_object* v_a_645_, lean_object* v_a_646_, lean_object* v_a_647_, lean_object* v_a_648_, lean_object* v_a_649_, lean_object* v_a_650_){
_start:
{
lean_object* v___x_652_; 
v___x_652_ = l_Lean_Elab_Tactic_VCGen_mkBackwardRuleForSplitCached___redArg(v_splitInfo_638_, v_info_639_, v_a_641_, v_a_645_, v_a_646_, v_a_647_, v_a_648_, v_a_649_, v_a_650_);
return v___x_652_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_mkBackwardRuleForSplitCached___boxed(lean_object* v_splitInfo_653_, lean_object* v_info_654_, lean_object* v_a_655_, lean_object* v_a_656_, lean_object* v_a_657_, lean_object* v_a_658_, lean_object* v_a_659_, lean_object* v_a_660_, lean_object* v_a_661_, lean_object* v_a_662_, lean_object* v_a_663_, lean_object* v_a_664_, lean_object* v_a_665_, lean_object* v_a_666_){
_start:
{
lean_object* v_res_667_; 
v_res_667_ = l_Lean_Elab_Tactic_VCGen_mkBackwardRuleForSplitCached(v_splitInfo_653_, v_info_654_, v_a_655_, v_a_656_, v_a_657_, v_a_658_, v_a_659_, v_a_660_, v_a_661_, v_a_662_, v_a_663_, v_a_664_, v_a_665_);
lean_dec(v_a_665_);
lean_dec_ref(v_a_664_);
lean_dec(v_a_663_);
lean_dec_ref(v_a_662_);
lean_dec(v_a_661_);
lean_dec_ref(v_a_660_);
lean_dec(v_a_659_);
lean_dec_ref(v_a_658_);
lean_dec(v_a_657_);
lean_dec(v_a_656_);
lean_dec_ref(v_a_655_);
return v_res_667_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1_spec__2___redArg(lean_object* v_a_668_, lean_object* v_x_669_){
_start:
{
if (lean_obj_tag(v_x_669_) == 0)
{
uint8_t v___x_670_; 
v___x_670_ = 0;
return v___x_670_;
}
else
{
lean_object* v_key_671_; lean_object* v_tail_672_; lean_object* v_fst_673_; lean_object* v_snd_674_; lean_object* v_fst_675_; lean_object* v_snd_676_; size_t v___x_677_; size_t v___x_678_; uint8_t v___x_679_; 
v_key_671_ = lean_ctor_get(v_x_669_, 0);
v_tail_672_ = lean_ctor_get(v_x_669_, 2);
v_fst_673_ = lean_ctor_get(v_key_671_, 0);
v_snd_674_ = lean_ctor_get(v_key_671_, 1);
v_fst_675_ = lean_ctor_get(v_a_668_, 0);
v_snd_676_ = lean_ctor_get(v_a_668_, 1);
v___x_677_ = lean_ptr_addr(v_fst_673_);
v___x_678_ = lean_ptr_addr(v_fst_675_);
v___x_679_ = lean_usize_dec_eq(v___x_677_, v___x_678_);
if (v___x_679_ == 0)
{
v_x_669_ = v_tail_672_;
goto _start;
}
else
{
uint8_t v___x_681_; 
v___x_681_ = lean_nat_dec_eq(v_snd_674_, v_snd_676_);
if (v___x_681_ == 0)
{
v_x_669_ = v_tail_672_;
goto _start;
}
else
{
return v___x_681_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1_spec__2___redArg___boxed(lean_object* v_a_683_, lean_object* v_x_684_){
_start:
{
uint8_t v_res_685_; lean_object* v_r_686_; 
v_res_685_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1_spec__2___redArg(v_a_683_, v_x_684_);
lean_dec(v_x_684_);
lean_dec_ref(v_a_683_);
v_r_686_ = lean_box(v_res_685_);
return v_r_686_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1_spec__4___redArg(lean_object* v_a_687_, lean_object* v_b_688_, lean_object* v_x_689_){
_start:
{
if (lean_obj_tag(v_x_689_) == 0)
{
lean_dec(v_b_688_);
lean_dec_ref(v_a_687_);
return v_x_689_;
}
else
{
lean_object* v_key_690_; lean_object* v_value_691_; lean_object* v_tail_692_; lean_object* v___x_694_; uint8_t v_isShared_695_; uint8_t v_isSharedCheck_710_; 
v_key_690_ = lean_ctor_get(v_x_689_, 0);
v_value_691_ = lean_ctor_get(v_x_689_, 1);
v_tail_692_ = lean_ctor_get(v_x_689_, 2);
v_isSharedCheck_710_ = !lean_is_exclusive(v_x_689_);
if (v_isSharedCheck_710_ == 0)
{
v___x_694_ = v_x_689_;
v_isShared_695_ = v_isSharedCheck_710_;
goto v_resetjp_693_;
}
else
{
lean_inc(v_tail_692_);
lean_inc(v_value_691_);
lean_inc(v_key_690_);
lean_dec(v_x_689_);
v___x_694_ = lean_box(0);
v_isShared_695_ = v_isSharedCheck_710_;
goto v_resetjp_693_;
}
v_resetjp_693_:
{
lean_object* v_fst_701_; lean_object* v_snd_702_; lean_object* v_fst_703_; lean_object* v_snd_704_; size_t v___x_705_; size_t v___x_706_; uint8_t v___x_707_; 
v_fst_701_ = lean_ctor_get(v_key_690_, 0);
v_snd_702_ = lean_ctor_get(v_key_690_, 1);
v_fst_703_ = lean_ctor_get(v_a_687_, 0);
v_snd_704_ = lean_ctor_get(v_a_687_, 1);
v___x_705_ = lean_ptr_addr(v_fst_701_);
v___x_706_ = lean_ptr_addr(v_fst_703_);
v___x_707_ = lean_usize_dec_eq(v___x_705_, v___x_706_);
if (v___x_707_ == 0)
{
goto v___jp_696_;
}
else
{
uint8_t v___x_708_; 
v___x_708_ = lean_nat_dec_eq(v_snd_702_, v_snd_704_);
if (v___x_708_ == 0)
{
goto v___jp_696_;
}
else
{
lean_object* v___x_709_; 
lean_del_object(v___x_694_);
lean_dec(v_value_691_);
lean_dec(v_key_690_);
v___x_709_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_709_, 0, v_a_687_);
lean_ctor_set(v___x_709_, 1, v_b_688_);
lean_ctor_set(v___x_709_, 2, v_tail_692_);
return v___x_709_;
}
}
v___jp_696_:
{
lean_object* v___x_697_; lean_object* v___x_699_; 
v___x_697_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1_spec__4___redArg(v_a_687_, v_b_688_, v_tail_692_);
if (v_isShared_695_ == 0)
{
lean_ctor_set(v___x_694_, 2, v___x_697_);
v___x_699_ = v___x_694_;
goto v_reusejp_698_;
}
else
{
lean_object* v_reuseFailAlloc_700_; 
v_reuseFailAlloc_700_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_700_, 0, v_key_690_);
lean_ctor_set(v_reuseFailAlloc_700_, 1, v_value_691_);
lean_ctor_set(v_reuseFailAlloc_700_, 2, v___x_697_);
v___x_699_ = v_reuseFailAlloc_700_;
goto v_reusejp_698_;
}
v_reusejp_698_:
{
return v___x_699_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1_spec__3_spec__4_spec__5___redArg(lean_object* v_x_711_, lean_object* v_x_712_){
_start:
{
if (lean_obj_tag(v_x_712_) == 0)
{
return v_x_711_;
}
else
{
lean_object* v_key_713_; lean_object* v_value_714_; lean_object* v_tail_715_; lean_object* v___x_717_; uint8_t v_isShared_718_; uint8_t v_isSharedCheck_745_; 
v_key_713_ = lean_ctor_get(v_x_712_, 0);
v_value_714_ = lean_ctor_get(v_x_712_, 1);
v_tail_715_ = lean_ctor_get(v_x_712_, 2);
v_isSharedCheck_745_ = !lean_is_exclusive(v_x_712_);
if (v_isSharedCheck_745_ == 0)
{
v___x_717_ = v_x_712_;
v_isShared_718_ = v_isSharedCheck_745_;
goto v_resetjp_716_;
}
else
{
lean_inc(v_tail_715_);
lean_inc(v_value_714_);
lean_inc(v_key_713_);
lean_dec(v_x_712_);
v___x_717_ = lean_box(0);
v_isShared_718_ = v_isSharedCheck_745_;
goto v_resetjp_716_;
}
v_resetjp_716_:
{
lean_object* v_fst_719_; lean_object* v_snd_720_; lean_object* v___x_721_; size_t v___x_722_; size_t v___x_723_; size_t v___x_724_; uint64_t v___x_725_; uint64_t v___x_726_; uint64_t v___x_727_; uint64_t v___x_728_; uint64_t v___x_729_; uint64_t v_fold_730_; uint64_t v___x_731_; uint64_t v___x_732_; uint64_t v___x_733_; size_t v___x_734_; size_t v___x_735_; size_t v___x_736_; size_t v___x_737_; size_t v___x_738_; lean_object* v___x_739_; lean_object* v___x_741_; 
v_fst_719_ = lean_ctor_get(v_key_713_, 0);
v_snd_720_ = lean_ctor_get(v_key_713_, 1);
v___x_721_ = lean_array_get_size(v_x_711_);
v___x_722_ = lean_ptr_addr(v_fst_719_);
v___x_723_ = ((size_t)3ULL);
v___x_724_ = lean_usize_shift_right(v___x_722_, v___x_723_);
v___x_725_ = lean_usize_to_uint64(v___x_724_);
v___x_726_ = lean_uint64_of_nat(v_snd_720_);
v___x_727_ = lean_uint64_mix_hash(v___x_725_, v___x_726_);
v___x_728_ = 32ULL;
v___x_729_ = lean_uint64_shift_right(v___x_727_, v___x_728_);
v_fold_730_ = lean_uint64_xor(v___x_727_, v___x_729_);
v___x_731_ = 16ULL;
v___x_732_ = lean_uint64_shift_right(v_fold_730_, v___x_731_);
v___x_733_ = lean_uint64_xor(v_fold_730_, v___x_732_);
v___x_734_ = lean_uint64_to_usize(v___x_733_);
v___x_735_ = lean_usize_of_nat(v___x_721_);
v___x_736_ = ((size_t)1ULL);
v___x_737_ = lean_usize_sub(v___x_735_, v___x_736_);
v___x_738_ = lean_usize_land(v___x_734_, v___x_737_);
v___x_739_ = lean_array_uget_borrowed(v_x_711_, v___x_738_);
lean_inc(v___x_739_);
if (v_isShared_718_ == 0)
{
lean_ctor_set(v___x_717_, 2, v___x_739_);
v___x_741_ = v___x_717_;
goto v_reusejp_740_;
}
else
{
lean_object* v_reuseFailAlloc_744_; 
v_reuseFailAlloc_744_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_744_, 0, v_key_713_);
lean_ctor_set(v_reuseFailAlloc_744_, 1, v_value_714_);
lean_ctor_set(v_reuseFailAlloc_744_, 2, v___x_739_);
v___x_741_ = v_reuseFailAlloc_744_;
goto v_reusejp_740_;
}
v_reusejp_740_:
{
lean_object* v___x_742_; 
v___x_742_ = lean_array_uset(v_x_711_, v___x_738_, v___x_741_);
v_x_711_ = v___x_742_;
v_x_712_ = v_tail_715_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1_spec__3_spec__4___redArg(lean_object* v_i_746_, lean_object* v_source_747_, lean_object* v_target_748_){
_start:
{
lean_object* v___x_749_; uint8_t v___x_750_; 
v___x_749_ = lean_array_get_size(v_source_747_);
v___x_750_ = lean_nat_dec_lt(v_i_746_, v___x_749_);
if (v___x_750_ == 0)
{
lean_dec_ref(v_source_747_);
lean_dec(v_i_746_);
return v_target_748_;
}
else
{
lean_object* v_es_751_; lean_object* v___x_752_; lean_object* v_source_753_; lean_object* v_target_754_; lean_object* v___x_755_; lean_object* v___x_756_; 
v_es_751_ = lean_array_fget(v_source_747_, v_i_746_);
v___x_752_ = lean_box(0);
v_source_753_ = lean_array_fset(v_source_747_, v_i_746_, v___x_752_);
v_target_754_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1_spec__3_spec__4_spec__5___redArg(v_target_748_, v_es_751_);
v___x_755_ = lean_unsigned_to_nat(1u);
v___x_756_ = lean_nat_add(v_i_746_, v___x_755_);
lean_dec(v_i_746_);
v_i_746_ = v___x_756_;
v_source_747_ = v_source_753_;
v_target_748_ = v_target_754_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1_spec__3___redArg(lean_object* v_data_758_){
_start:
{
lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v_nbuckets_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; 
v___x_759_ = lean_array_get_size(v_data_758_);
v___x_760_ = lean_unsigned_to_nat(2u);
v_nbuckets_761_ = lean_nat_mul(v___x_759_, v___x_760_);
v___x_762_ = lean_unsigned_to_nat(0u);
v___x_763_ = lean_box(0);
v___x_764_ = lean_mk_array(v_nbuckets_761_, v___x_763_);
v___x_765_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1_spec__3_spec__4___redArg(v___x_762_, v_data_758_, v___x_764_);
return v___x_765_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1___redArg(lean_object* v_m_766_, lean_object* v_a_767_, lean_object* v_b_768_){
_start:
{
lean_object* v_size_769_; lean_object* v_buckets_770_; lean_object* v___x_772_; uint8_t v_isShared_773_; uint8_t v_isSharedCheck_820_; 
v_size_769_ = lean_ctor_get(v_m_766_, 0);
v_buckets_770_ = lean_ctor_get(v_m_766_, 1);
v_isSharedCheck_820_ = !lean_is_exclusive(v_m_766_);
if (v_isSharedCheck_820_ == 0)
{
v___x_772_ = v_m_766_;
v_isShared_773_ = v_isSharedCheck_820_;
goto v_resetjp_771_;
}
else
{
lean_inc(v_buckets_770_);
lean_inc(v_size_769_);
lean_dec(v_m_766_);
v___x_772_ = lean_box(0);
v_isShared_773_ = v_isSharedCheck_820_;
goto v_resetjp_771_;
}
v_resetjp_771_:
{
lean_object* v_fst_774_; lean_object* v_snd_775_; lean_object* v___x_776_; size_t v___x_777_; size_t v___x_778_; size_t v___x_779_; uint64_t v___x_780_; uint64_t v___x_781_; uint64_t v___x_782_; uint64_t v___x_783_; uint64_t v___x_784_; uint64_t v_fold_785_; uint64_t v___x_786_; uint64_t v___x_787_; uint64_t v___x_788_; size_t v___x_789_; size_t v___x_790_; size_t v___x_791_; size_t v___x_792_; size_t v___x_793_; lean_object* v_bkt_794_; uint8_t v___x_795_; 
v_fst_774_ = lean_ctor_get(v_a_767_, 0);
v_snd_775_ = lean_ctor_get(v_a_767_, 1);
v___x_776_ = lean_array_get_size(v_buckets_770_);
v___x_777_ = lean_ptr_addr(v_fst_774_);
v___x_778_ = ((size_t)3ULL);
v___x_779_ = lean_usize_shift_right(v___x_777_, v___x_778_);
v___x_780_ = lean_usize_to_uint64(v___x_779_);
v___x_781_ = lean_uint64_of_nat(v_snd_775_);
v___x_782_ = lean_uint64_mix_hash(v___x_780_, v___x_781_);
v___x_783_ = 32ULL;
v___x_784_ = lean_uint64_shift_right(v___x_782_, v___x_783_);
v_fold_785_ = lean_uint64_xor(v___x_782_, v___x_784_);
v___x_786_ = 16ULL;
v___x_787_ = lean_uint64_shift_right(v_fold_785_, v___x_786_);
v___x_788_ = lean_uint64_xor(v_fold_785_, v___x_787_);
v___x_789_ = lean_uint64_to_usize(v___x_788_);
v___x_790_ = lean_usize_of_nat(v___x_776_);
v___x_791_ = ((size_t)1ULL);
v___x_792_ = lean_usize_sub(v___x_790_, v___x_791_);
v___x_793_ = lean_usize_land(v___x_789_, v___x_792_);
v_bkt_794_ = lean_array_uget_borrowed(v_buckets_770_, v___x_793_);
v___x_795_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1_spec__2___redArg(v_a_767_, v_bkt_794_);
if (v___x_795_ == 0)
{
lean_object* v___x_796_; lean_object* v_size_x27_797_; lean_object* v___x_798_; lean_object* v_buckets_x27_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; uint8_t v___x_805_; 
v___x_796_ = lean_unsigned_to_nat(1u);
v_size_x27_797_ = lean_nat_add(v_size_769_, v___x_796_);
lean_dec(v_size_769_);
lean_inc(v_bkt_794_);
v___x_798_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_798_, 0, v_a_767_);
lean_ctor_set(v___x_798_, 1, v_b_768_);
lean_ctor_set(v___x_798_, 2, v_bkt_794_);
v_buckets_x27_799_ = lean_array_uset(v_buckets_770_, v___x_793_, v___x_798_);
v___x_800_ = lean_unsigned_to_nat(4u);
v___x_801_ = lean_nat_mul(v_size_x27_797_, v___x_800_);
v___x_802_ = lean_unsigned_to_nat(3u);
v___x_803_ = lean_nat_div(v___x_801_, v___x_802_);
lean_dec(v___x_801_);
v___x_804_ = lean_array_get_size(v_buckets_x27_799_);
v___x_805_ = lean_nat_dec_le(v___x_803_, v___x_804_);
lean_dec(v___x_803_);
if (v___x_805_ == 0)
{
lean_object* v_val_806_; lean_object* v___x_808_; 
v_val_806_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1_spec__3___redArg(v_buckets_x27_799_);
if (v_isShared_773_ == 0)
{
lean_ctor_set(v___x_772_, 1, v_val_806_);
lean_ctor_set(v___x_772_, 0, v_size_x27_797_);
v___x_808_ = v___x_772_;
goto v_reusejp_807_;
}
else
{
lean_object* v_reuseFailAlloc_809_; 
v_reuseFailAlloc_809_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_809_, 0, v_size_x27_797_);
lean_ctor_set(v_reuseFailAlloc_809_, 1, v_val_806_);
v___x_808_ = v_reuseFailAlloc_809_;
goto v_reusejp_807_;
}
v_reusejp_807_:
{
return v___x_808_;
}
}
else
{
lean_object* v___x_811_; 
if (v_isShared_773_ == 0)
{
lean_ctor_set(v___x_772_, 1, v_buckets_x27_799_);
lean_ctor_set(v___x_772_, 0, v_size_x27_797_);
v___x_811_ = v___x_772_;
goto v_reusejp_810_;
}
else
{
lean_object* v_reuseFailAlloc_812_; 
v_reuseFailAlloc_812_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_812_, 0, v_size_x27_797_);
lean_ctor_set(v_reuseFailAlloc_812_, 1, v_buckets_x27_799_);
v___x_811_ = v_reuseFailAlloc_812_;
goto v_reusejp_810_;
}
v_reusejp_810_:
{
return v___x_811_;
}
}
}
else
{
lean_object* v___x_813_; lean_object* v_buckets_x27_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_818_; 
lean_inc(v_bkt_794_);
v___x_813_ = lean_box(0);
v_buckets_x27_814_ = lean_array_uset(v_buckets_770_, v___x_793_, v___x_813_);
v___x_815_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1_spec__4___redArg(v_a_767_, v_b_768_, v_bkt_794_);
v___x_816_ = lean_array_uset(v_buckets_x27_814_, v___x_793_, v___x_815_);
if (v_isShared_773_ == 0)
{
lean_ctor_set(v___x_772_, 1, v___x_816_);
v___x_818_ = v___x_772_;
goto v_reusejp_817_;
}
else
{
lean_object* v_reuseFailAlloc_819_; 
v_reuseFailAlloc_819_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_819_, 0, v_size_769_);
lean_ctor_set(v_reuseFailAlloc_819_, 1, v___x_816_);
v___x_818_ = v_reuseFailAlloc_819_;
goto v_reusejp_817_;
}
v_reusejp_817_:
{
return v___x_818_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__0_spec__0___redArg(lean_object* v_a_821_, lean_object* v_x_822_){
_start:
{
if (lean_obj_tag(v_x_822_) == 0)
{
lean_object* v___x_823_; 
v___x_823_ = lean_box(0);
return v___x_823_;
}
else
{
lean_object* v_key_824_; lean_object* v_value_825_; lean_object* v_tail_826_; lean_object* v_fst_827_; lean_object* v_snd_828_; lean_object* v_fst_829_; lean_object* v_snd_830_; size_t v___x_831_; size_t v___x_832_; uint8_t v___x_833_; 
v_key_824_ = lean_ctor_get(v_x_822_, 0);
v_value_825_ = lean_ctor_get(v_x_822_, 1);
v_tail_826_ = lean_ctor_get(v_x_822_, 2);
v_fst_827_ = lean_ctor_get(v_key_824_, 0);
v_snd_828_ = lean_ctor_get(v_key_824_, 1);
v_fst_829_ = lean_ctor_get(v_a_821_, 0);
v_snd_830_ = lean_ctor_get(v_a_821_, 1);
v___x_831_ = lean_ptr_addr(v_fst_827_);
v___x_832_ = lean_ptr_addr(v_fst_829_);
v___x_833_ = lean_usize_dec_eq(v___x_831_, v___x_832_);
if (v___x_833_ == 0)
{
v_x_822_ = v_tail_826_;
goto _start;
}
else
{
uint8_t v___x_835_; 
v___x_835_ = lean_nat_dec_eq(v_snd_828_, v_snd_830_);
if (v___x_835_ == 0)
{
v_x_822_ = v_tail_826_;
goto _start;
}
else
{
lean_object* v___x_837_; 
lean_inc(v_value_825_);
v___x_837_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_837_, 0, v_value_825_);
return v___x_837_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__0_spec__0___redArg___boxed(lean_object* v_a_838_, lean_object* v_x_839_){
_start:
{
lean_object* v_res_840_; 
v_res_840_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__0_spec__0___redArg(v_a_838_, v_x_839_);
lean_dec(v_x_839_);
lean_dec_ref(v_a_838_);
return v_res_840_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__0___redArg(lean_object* v_m_841_, lean_object* v_a_842_){
_start:
{
lean_object* v_buckets_843_; lean_object* v_fst_844_; lean_object* v_snd_845_; lean_object* v___x_846_; size_t v___x_847_; size_t v___x_848_; size_t v___x_849_; uint64_t v___x_850_; uint64_t v___x_851_; uint64_t v___x_852_; uint64_t v___x_853_; uint64_t v___x_854_; uint64_t v_fold_855_; uint64_t v___x_856_; uint64_t v___x_857_; uint64_t v___x_858_; size_t v___x_859_; size_t v___x_860_; size_t v___x_861_; size_t v___x_862_; size_t v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; 
v_buckets_843_ = lean_ctor_get(v_m_841_, 1);
v_fst_844_ = lean_ctor_get(v_a_842_, 0);
v_snd_845_ = lean_ctor_get(v_a_842_, 1);
v___x_846_ = lean_array_get_size(v_buckets_843_);
v___x_847_ = lean_ptr_addr(v_fst_844_);
v___x_848_ = ((size_t)3ULL);
v___x_849_ = lean_usize_shift_right(v___x_847_, v___x_848_);
v___x_850_ = lean_usize_to_uint64(v___x_849_);
v___x_851_ = lean_uint64_of_nat(v_snd_845_);
v___x_852_ = lean_uint64_mix_hash(v___x_850_, v___x_851_);
v___x_853_ = 32ULL;
v___x_854_ = lean_uint64_shift_right(v___x_852_, v___x_853_);
v_fold_855_ = lean_uint64_xor(v___x_852_, v___x_854_);
v___x_856_ = 16ULL;
v___x_857_ = lean_uint64_shift_right(v_fold_855_, v___x_856_);
v___x_858_ = lean_uint64_xor(v_fold_855_, v___x_857_);
v___x_859_ = lean_uint64_to_usize(v___x_858_);
v___x_860_ = lean_usize_of_nat(v___x_846_);
v___x_861_ = ((size_t)1ULL);
v___x_862_ = lean_usize_sub(v___x_860_, v___x_861_);
v___x_863_ = lean_usize_land(v___x_859_, v___x_862_);
v___x_864_ = lean_array_uget_borrowed(v_buckets_843_, v___x_863_);
v___x_865_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__0_spec__0___redArg(v_a_842_, v___x_864_);
return v___x_865_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__0___redArg___boxed(lean_object* v_m_866_, lean_object* v_a_867_){
_start:
{
lean_object* v_res_868_; 
v_res_868_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__0___redArg(v_m_866_, v_a_867_);
lean_dec_ref(v_a_867_);
lean_dec_ref(v_m_866_);
return v_res_868_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached___redArg(lean_object* v_rhs_869_, lean_object* v_op_870_, lean_object* v_a_871_, lean_object* v_a_872_, lean_object* v_a_873_, lean_object* v_a_874_, lean_object* v_a_875_, lean_object* v_a_876_, lean_object* v_a_877_){
_start:
{
lean_object* v___x_879_; lean_object* v_numConst_880_; lean_object* v_latticeBackwardRuleCache_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v_key_884_; lean_object* v___x_885_; 
v___x_879_ = lean_st_ref_get(v_a_871_);
v_numConst_880_ = lean_ctor_get(v_op_870_, 1);
v_latticeBackwardRuleCache_881_ = lean_ctor_get(v___x_879_, 2);
lean_inc_ref(v_latticeBackwardRuleCache_881_);
lean_dec(v___x_879_);
v___x_882_ = l_Lean_Expr_getAppPrefix(v_rhs_869_, v_numConst_880_);
v___x_883_ = l_Lean_Expr_getAppNumArgs(v_rhs_869_);
v_key_884_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_key_884_, 0, v___x_882_);
lean_ctor_set(v_key_884_, 1, v___x_883_);
v___x_885_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__0___redArg(v_latticeBackwardRuleCache_881_, v_key_884_);
lean_dec_ref(v_latticeBackwardRuleCache_881_);
if (lean_obj_tag(v___x_885_) == 1)
{
lean_object* v_val_886_; lean_object* v___x_888_; uint8_t v_isShared_889_; uint8_t v_isSharedCheck_893_; 
lean_dec_ref_known(v_key_884_, 2);
lean_dec_ref(v_op_870_);
lean_dec_ref(v_rhs_869_);
v_val_886_ = lean_ctor_get(v___x_885_, 0);
v_isSharedCheck_893_ = !lean_is_exclusive(v___x_885_);
if (v_isSharedCheck_893_ == 0)
{
v___x_888_ = v___x_885_;
v_isShared_889_ = v_isSharedCheck_893_;
goto v_resetjp_887_;
}
else
{
lean_inc(v_val_886_);
lean_dec(v___x_885_);
v___x_888_ = lean_box(0);
v_isShared_889_ = v_isSharedCheck_893_;
goto v_resetjp_887_;
}
v_resetjp_887_:
{
lean_object* v___x_891_; 
if (v_isShared_889_ == 0)
{
lean_ctor_set_tag(v___x_888_, 0);
v___x_891_ = v___x_888_;
goto v_reusejp_890_;
}
else
{
lean_object* v_reuseFailAlloc_892_; 
v_reuseFailAlloc_892_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_892_, 0, v_val_886_);
v___x_891_ = v_reuseFailAlloc_892_;
goto v_reusejp_890_;
}
v_reusejp_890_:
{
return v___x_891_;
}
}
}
else
{
lean_object* v___x_894_; 
lean_dec(v___x_885_);
v___x_894_ = l_Lean_Elab_Tactic_VCGen_mkLatticeOpRule(v_rhs_869_, v_op_870_, v_a_872_, v_a_873_, v_a_874_, v_a_875_, v_a_876_, v_a_877_);
if (lean_obj_tag(v___x_894_) == 0)
{
lean_object* v_a_895_; lean_object* v___x_896_; 
v_a_895_ = lean_ctor_get(v___x_894_, 0);
lean_inc(v_a_895_);
lean_dec_ref_known(v___x_894_, 1);
v___x_896_ = l_Lean_Meta_Sym_BackwardRule_shareCommon(v_a_895_, v_a_872_, v_a_873_, v_a_874_, v_a_875_, v_a_876_, v_a_877_);
if (lean_obj_tag(v___x_896_) == 0)
{
lean_object* v_a_897_; lean_object* v___x_899_; uint8_t v_isShared_900_; uint8_t v_isSharedCheck_924_; 
v_a_897_ = lean_ctor_get(v___x_896_, 0);
v_isSharedCheck_924_ = !lean_is_exclusive(v___x_896_);
if (v_isSharedCheck_924_ == 0)
{
v___x_899_ = v___x_896_;
v_isShared_900_ = v_isSharedCheck_924_;
goto v_resetjp_898_;
}
else
{
lean_inc(v_a_897_);
lean_dec(v___x_896_);
v___x_899_ = lean_box(0);
v_isShared_900_ = v_isSharedCheck_924_;
goto v_resetjp_898_;
}
v_resetjp_898_:
{
lean_object* v___x_901_; lean_object* v_specBackwardRuleCache_902_; lean_object* v_splitBackwardRuleCache_903_; lean_object* v_latticeBackwardRuleCache_904_; lean_object* v_frameBackwardRuleCache_905_; lean_object* v_frameDB_906_; lean_object* v_invariants_907_; lean_object* v_vcs_908_; lean_object* v_simpState_909_; lean_object* v_fuel_910_; lean_object* v_inlineHandledInvariants_911_; lean_object* v___x_913_; uint8_t v_isShared_914_; uint8_t v_isSharedCheck_923_; 
v___x_901_ = lean_st_ref_take(v_a_871_);
v_specBackwardRuleCache_902_ = lean_ctor_get(v___x_901_, 0);
v_splitBackwardRuleCache_903_ = lean_ctor_get(v___x_901_, 1);
v_latticeBackwardRuleCache_904_ = lean_ctor_get(v___x_901_, 2);
v_frameBackwardRuleCache_905_ = lean_ctor_get(v___x_901_, 3);
v_frameDB_906_ = lean_ctor_get(v___x_901_, 4);
v_invariants_907_ = lean_ctor_get(v___x_901_, 5);
v_vcs_908_ = lean_ctor_get(v___x_901_, 6);
v_simpState_909_ = lean_ctor_get(v___x_901_, 7);
v_fuel_910_ = lean_ctor_get(v___x_901_, 8);
v_inlineHandledInvariants_911_ = lean_ctor_get(v___x_901_, 9);
v_isSharedCheck_923_ = !lean_is_exclusive(v___x_901_);
if (v_isSharedCheck_923_ == 0)
{
v___x_913_ = v___x_901_;
v_isShared_914_ = v_isSharedCheck_923_;
goto v_resetjp_912_;
}
else
{
lean_inc(v_inlineHandledInvariants_911_);
lean_inc(v_fuel_910_);
lean_inc(v_simpState_909_);
lean_inc(v_vcs_908_);
lean_inc(v_invariants_907_);
lean_inc(v_frameDB_906_);
lean_inc(v_frameBackwardRuleCache_905_);
lean_inc(v_latticeBackwardRuleCache_904_);
lean_inc(v_splitBackwardRuleCache_903_);
lean_inc(v_specBackwardRuleCache_902_);
lean_dec(v___x_901_);
v___x_913_ = lean_box(0);
v_isShared_914_ = v_isSharedCheck_923_;
goto v_resetjp_912_;
}
v_resetjp_912_:
{
lean_object* v___x_915_; lean_object* v___x_917_; 
lean_inc(v_a_897_);
v___x_915_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1___redArg(v_latticeBackwardRuleCache_904_, v_key_884_, v_a_897_);
if (v_isShared_914_ == 0)
{
lean_ctor_set(v___x_913_, 2, v___x_915_);
v___x_917_ = v___x_913_;
goto v_reusejp_916_;
}
else
{
lean_object* v_reuseFailAlloc_922_; 
v_reuseFailAlloc_922_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_922_, 0, v_specBackwardRuleCache_902_);
lean_ctor_set(v_reuseFailAlloc_922_, 1, v_splitBackwardRuleCache_903_);
lean_ctor_set(v_reuseFailAlloc_922_, 2, v___x_915_);
lean_ctor_set(v_reuseFailAlloc_922_, 3, v_frameBackwardRuleCache_905_);
lean_ctor_set(v_reuseFailAlloc_922_, 4, v_frameDB_906_);
lean_ctor_set(v_reuseFailAlloc_922_, 5, v_invariants_907_);
lean_ctor_set(v_reuseFailAlloc_922_, 6, v_vcs_908_);
lean_ctor_set(v_reuseFailAlloc_922_, 7, v_simpState_909_);
lean_ctor_set(v_reuseFailAlloc_922_, 8, v_fuel_910_);
lean_ctor_set(v_reuseFailAlloc_922_, 9, v_inlineHandledInvariants_911_);
v___x_917_ = v_reuseFailAlloc_922_;
goto v_reusejp_916_;
}
v_reusejp_916_:
{
lean_object* v___x_918_; lean_object* v___x_920_; 
v___x_918_ = lean_st_ref_put(v_a_871_, v___x_917_);
if (v_isShared_900_ == 0)
{
v___x_920_ = v___x_899_;
goto v_reusejp_919_;
}
else
{
lean_object* v_reuseFailAlloc_921_; 
v_reuseFailAlloc_921_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_921_, 0, v_a_897_);
v___x_920_ = v_reuseFailAlloc_921_;
goto v_reusejp_919_;
}
v_reusejp_919_:
{
return v___x_920_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_key_884_, 2);
return v___x_896_;
}
}
else
{
lean_dec_ref_known(v_key_884_, 2);
return v___x_894_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached___redArg___boxed(lean_object* v_rhs_925_, lean_object* v_op_926_, lean_object* v_a_927_, lean_object* v_a_928_, lean_object* v_a_929_, lean_object* v_a_930_, lean_object* v_a_931_, lean_object* v_a_932_, lean_object* v_a_933_, lean_object* v_a_934_){
_start:
{
lean_object* v_res_935_; 
v_res_935_ = l_Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached___redArg(v_rhs_925_, v_op_926_, v_a_927_, v_a_928_, v_a_929_, v_a_930_, v_a_931_, v_a_932_, v_a_933_);
lean_dec(v_a_933_);
lean_dec_ref(v_a_932_);
lean_dec(v_a_931_);
lean_dec_ref(v_a_930_);
lean_dec(v_a_929_);
lean_dec_ref(v_a_928_);
lean_dec(v_a_927_);
return v_res_935_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached(lean_object* v_rhs_936_, lean_object* v_op_937_, lean_object* v_a_938_, lean_object* v_a_939_, lean_object* v_a_940_, lean_object* v_a_941_, lean_object* v_a_942_, lean_object* v_a_943_, lean_object* v_a_944_, lean_object* v_a_945_, lean_object* v_a_946_, lean_object* v_a_947_, lean_object* v_a_948_){
_start:
{
lean_object* v___x_950_; 
v___x_950_ = l_Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached___redArg(v_rhs_936_, v_op_937_, v_a_939_, v_a_943_, v_a_944_, v_a_945_, v_a_946_, v_a_947_, v_a_948_);
return v___x_950_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached___boxed(lean_object* v_rhs_951_, lean_object* v_op_952_, lean_object* v_a_953_, lean_object* v_a_954_, lean_object* v_a_955_, lean_object* v_a_956_, lean_object* v_a_957_, lean_object* v_a_958_, lean_object* v_a_959_, lean_object* v_a_960_, lean_object* v_a_961_, lean_object* v_a_962_, lean_object* v_a_963_, lean_object* v_a_964_){
_start:
{
lean_object* v_res_965_; 
v_res_965_ = l_Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached(v_rhs_951_, v_op_952_, v_a_953_, v_a_954_, v_a_955_, v_a_956_, v_a_957_, v_a_958_, v_a_959_, v_a_960_, v_a_961_, v_a_962_, v_a_963_);
lean_dec(v_a_963_);
lean_dec_ref(v_a_962_);
lean_dec(v_a_961_);
lean_dec_ref(v_a_960_);
lean_dec(v_a_959_);
lean_dec_ref(v_a_958_);
lean_dec(v_a_957_);
lean_dec_ref(v_a_956_);
lean_dec(v_a_955_);
lean_dec(v_a_954_);
lean_dec_ref(v_a_953_);
return v_res_965_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__0(lean_object* v_00_u03b2_966_, lean_object* v_m_967_, lean_object* v_a_968_){
_start:
{
lean_object* v___x_969_; 
v___x_969_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__0___redArg(v_m_967_, v_a_968_);
return v___x_969_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__0___boxed(lean_object* v_00_u03b2_970_, lean_object* v_m_971_, lean_object* v_a_972_){
_start:
{
lean_object* v_res_973_; 
v_res_973_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__0(v_00_u03b2_970_, v_m_971_, v_a_972_);
lean_dec_ref(v_a_972_);
lean_dec_ref(v_m_971_);
return v_res_973_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1(lean_object* v_00_u03b2_974_, lean_object* v_m_975_, lean_object* v_a_976_, lean_object* v_b_977_){
_start:
{
lean_object* v___x_978_; 
v___x_978_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1___redArg(v_m_975_, v_a_976_, v_b_977_);
return v___x_978_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__0_spec__0(lean_object* v_00_u03b2_979_, lean_object* v_a_980_, lean_object* v_x_981_){
_start:
{
lean_object* v___x_982_; 
v___x_982_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__0_spec__0___redArg(v_a_980_, v_x_981_);
return v___x_982_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__0_spec__0___boxed(lean_object* v_00_u03b2_983_, lean_object* v_a_984_, lean_object* v_x_985_){
_start:
{
lean_object* v_res_986_; 
v_res_986_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__0_spec__0(v_00_u03b2_983_, v_a_984_, v_x_985_);
lean_dec(v_x_985_);
lean_dec_ref(v_a_984_);
return v_res_986_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1_spec__2(lean_object* v_00_u03b2_987_, lean_object* v_a_988_, lean_object* v_x_989_){
_start:
{
uint8_t v___x_990_; 
v___x_990_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1_spec__2___redArg(v_a_988_, v_x_989_);
return v___x_990_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1_spec__2___boxed(lean_object* v_00_u03b2_991_, lean_object* v_a_992_, lean_object* v_x_993_){
_start:
{
uint8_t v_res_994_; lean_object* v_r_995_; 
v_res_994_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1_spec__2(v_00_u03b2_991_, v_a_992_, v_x_993_);
lean_dec(v_x_993_);
lean_dec_ref(v_a_992_);
v_r_995_ = lean_box(v_res_994_);
return v_r_995_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1_spec__3(lean_object* v_00_u03b2_996_, lean_object* v_data_997_){
_start:
{
lean_object* v___x_998_; 
v___x_998_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1_spec__3___redArg(v_data_997_);
return v___x_998_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1_spec__4(lean_object* v_00_u03b2_999_, lean_object* v_a_1000_, lean_object* v_b_1001_, lean_object* v_x_1002_){
_start:
{
lean_object* v___x_1003_; 
v___x_1003_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1_spec__4___redArg(v_a_1000_, v_b_1001_, v_x_1002_);
return v___x_1003_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1_spec__3_spec__4(lean_object* v_00_u03b2_1004_, lean_object* v_i_1005_, lean_object* v_source_1006_, lean_object* v_target_1007_){
_start:
{
lean_object* v___x_1008_; 
v___x_1008_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1_spec__3_spec__4___redArg(v_i_1005_, v_source_1006_, v_target_1007_);
return v___x_1008_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1_spec__3_spec__4_spec__5(lean_object* v_00_u03b2_1009_, lean_object* v_x_1010_, lean_object* v_x_1011_){
_start:
{
lean_object* v___x_1012_; 
v___x_1012_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1_spec__3_spec__4_spec__5___redArg(v_x_1010_, v_x_1011_);
return v___x_1012_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_mkFrameBackwardRuleCached___redArg(lean_object* v_fp_1013_, lean_object* v_info_1014_, lean_object* v_a_1015_, lean_object* v_a_1016_, lean_object* v_a_1017_, lean_object* v_a_1018_, lean_object* v_a_1019_, lean_object* v_a_1020_, lean_object* v_a_1021_){
_start:
{
lean_object* v___x_1023_; lean_object* v_excessArgs_1024_; lean_object* v_frameBackwardRuleCache_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v_key_1028_; lean_object* v___x_1029_; 
v___x_1023_ = lean_st_ref_get(v_a_1015_);
v_excessArgs_1024_ = lean_ctor_get(v_info_1014_, 3);
v_frameBackwardRuleCache_1025_ = lean_ctor_get(v___x_1023_, 3);
lean_inc_ref(v_frameBackwardRuleCache_1025_);
lean_dec(v___x_1023_);
v___x_1026_ = l_Lean_Elab_Tactic_VCGen_WPApp_instWP(v_info_1014_);
v___x_1027_ = lean_array_get_size(v_excessArgs_1024_);
v_key_1028_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_key_1028_, 0, v___x_1026_);
lean_ctor_set(v_key_1028_, 1, v___x_1027_);
v___x_1029_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__0___redArg(v_frameBackwardRuleCache_1025_, v_key_1028_);
lean_dec_ref(v_frameBackwardRuleCache_1025_);
if (lean_obj_tag(v___x_1029_) == 1)
{
lean_object* v_val_1030_; lean_object* v___x_1032_; uint8_t v_isShared_1033_; uint8_t v_isSharedCheck_1037_; 
lean_dec_ref_known(v_key_1028_, 2);
lean_dec_ref(v_info_1014_);
lean_dec_ref(v_fp_1013_);
v_val_1030_ = lean_ctor_get(v___x_1029_, 0);
v_isSharedCheck_1037_ = !lean_is_exclusive(v___x_1029_);
if (v_isSharedCheck_1037_ == 0)
{
v___x_1032_ = v___x_1029_;
v_isShared_1033_ = v_isSharedCheck_1037_;
goto v_resetjp_1031_;
}
else
{
lean_inc(v_val_1030_);
lean_dec(v___x_1029_);
v___x_1032_ = lean_box(0);
v_isShared_1033_ = v_isSharedCheck_1037_;
goto v_resetjp_1031_;
}
v_resetjp_1031_:
{
lean_object* v___x_1035_; 
if (v_isShared_1033_ == 0)
{
lean_ctor_set_tag(v___x_1032_, 0);
v___x_1035_ = v___x_1032_;
goto v_reusejp_1034_;
}
else
{
lean_object* v_reuseFailAlloc_1036_; 
v_reuseFailAlloc_1036_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1036_, 0, v_val_1030_);
v___x_1035_ = v_reuseFailAlloc_1036_;
goto v_reusejp_1034_;
}
v_reusejp_1034_:
{
return v___x_1035_;
}
}
}
else
{
lean_object* v___x_1038_; 
lean_dec(v___x_1029_);
v___x_1038_ = l_Lean_Elab_Tactic_VCGen_mkFrameBackwardRule(v_fp_1013_, v_info_1014_, v_a_1018_, v_a_1019_, v_a_1020_, v_a_1021_);
if (lean_obj_tag(v___x_1038_) == 0)
{
lean_object* v_a_1039_; lean_object* v_rule_1040_; lean_object* v_splitVCIdx_1041_; lean_object* v_frameIdx_1042_; lean_object* v___x_1044_; uint8_t v_isShared_1045_; uint8_t v_isSharedCheck_1086_; 
v_a_1039_ = lean_ctor_get(v___x_1038_, 0);
lean_inc(v_a_1039_);
lean_dec_ref_known(v___x_1038_, 1);
v_rule_1040_ = lean_ctor_get(v_a_1039_, 0);
v_splitVCIdx_1041_ = lean_ctor_get(v_a_1039_, 1);
v_frameIdx_1042_ = lean_ctor_get(v_a_1039_, 2);
v_isSharedCheck_1086_ = !lean_is_exclusive(v_a_1039_);
if (v_isSharedCheck_1086_ == 0)
{
v___x_1044_ = v_a_1039_;
v_isShared_1045_ = v_isSharedCheck_1086_;
goto v_resetjp_1043_;
}
else
{
lean_inc(v_frameIdx_1042_);
lean_inc(v_splitVCIdx_1041_);
lean_inc(v_rule_1040_);
lean_dec(v_a_1039_);
v___x_1044_ = lean_box(0);
v_isShared_1045_ = v_isSharedCheck_1086_;
goto v_resetjp_1043_;
}
v_resetjp_1043_:
{
lean_object* v___x_1046_; 
v___x_1046_ = l_Lean_Meta_Sym_BackwardRule_shareCommon(v_rule_1040_, v_a_1016_, v_a_1017_, v_a_1018_, v_a_1019_, v_a_1020_, v_a_1021_);
if (lean_obj_tag(v___x_1046_) == 0)
{
lean_object* v_a_1047_; lean_object* v___x_1049_; uint8_t v_isShared_1050_; uint8_t v_isSharedCheck_1077_; 
v_a_1047_ = lean_ctor_get(v___x_1046_, 0);
v_isSharedCheck_1077_ = !lean_is_exclusive(v___x_1046_);
if (v_isSharedCheck_1077_ == 0)
{
v___x_1049_ = v___x_1046_;
v_isShared_1050_ = v_isSharedCheck_1077_;
goto v_resetjp_1048_;
}
else
{
lean_inc(v_a_1047_);
lean_dec(v___x_1046_);
v___x_1049_ = lean_box(0);
v_isShared_1050_ = v_isSharedCheck_1077_;
goto v_resetjp_1048_;
}
v_resetjp_1048_:
{
lean_object* v___x_1051_; lean_object* v_specBackwardRuleCache_1052_; lean_object* v_splitBackwardRuleCache_1053_; lean_object* v_latticeBackwardRuleCache_1054_; lean_object* v_frameBackwardRuleCache_1055_; lean_object* v_frameDB_1056_; lean_object* v_invariants_1057_; lean_object* v_vcs_1058_; lean_object* v_simpState_1059_; lean_object* v_fuel_1060_; lean_object* v_inlineHandledInvariants_1061_; lean_object* v___x_1063_; uint8_t v_isShared_1064_; uint8_t v_isSharedCheck_1076_; 
v___x_1051_ = lean_st_ref_take(v_a_1015_);
v_specBackwardRuleCache_1052_ = lean_ctor_get(v___x_1051_, 0);
v_splitBackwardRuleCache_1053_ = lean_ctor_get(v___x_1051_, 1);
v_latticeBackwardRuleCache_1054_ = lean_ctor_get(v___x_1051_, 2);
v_frameBackwardRuleCache_1055_ = lean_ctor_get(v___x_1051_, 3);
v_frameDB_1056_ = lean_ctor_get(v___x_1051_, 4);
v_invariants_1057_ = lean_ctor_get(v___x_1051_, 5);
v_vcs_1058_ = lean_ctor_get(v___x_1051_, 6);
v_simpState_1059_ = lean_ctor_get(v___x_1051_, 7);
v_fuel_1060_ = lean_ctor_get(v___x_1051_, 8);
v_inlineHandledInvariants_1061_ = lean_ctor_get(v___x_1051_, 9);
v_isSharedCheck_1076_ = !lean_is_exclusive(v___x_1051_);
if (v_isSharedCheck_1076_ == 0)
{
v___x_1063_ = v___x_1051_;
v_isShared_1064_ = v_isSharedCheck_1076_;
goto v_resetjp_1062_;
}
else
{
lean_inc(v_inlineHandledInvariants_1061_);
lean_inc(v_fuel_1060_);
lean_inc(v_simpState_1059_);
lean_inc(v_vcs_1058_);
lean_inc(v_invariants_1057_);
lean_inc(v_frameDB_1056_);
lean_inc(v_frameBackwardRuleCache_1055_);
lean_inc(v_latticeBackwardRuleCache_1054_);
lean_inc(v_splitBackwardRuleCache_1053_);
lean_inc(v_specBackwardRuleCache_1052_);
lean_dec(v___x_1051_);
v___x_1063_ = lean_box(0);
v_isShared_1064_ = v_isSharedCheck_1076_;
goto v_resetjp_1062_;
}
v_resetjp_1062_:
{
lean_object* v___x_1066_; 
if (v_isShared_1045_ == 0)
{
lean_ctor_set(v___x_1044_, 0, v_a_1047_);
v___x_1066_ = v___x_1044_;
goto v_reusejp_1065_;
}
else
{
lean_object* v_reuseFailAlloc_1075_; 
v_reuseFailAlloc_1075_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1075_, 0, v_a_1047_);
lean_ctor_set(v_reuseFailAlloc_1075_, 1, v_splitVCIdx_1041_);
lean_ctor_set(v_reuseFailAlloc_1075_, 2, v_frameIdx_1042_);
v___x_1066_ = v_reuseFailAlloc_1075_;
goto v_reusejp_1065_;
}
v_reusejp_1065_:
{
lean_object* v___x_1067_; lean_object* v___x_1069_; 
lean_inc_ref(v___x_1066_);
v___x_1067_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1___redArg(v_frameBackwardRuleCache_1055_, v_key_1028_, v___x_1066_);
if (v_isShared_1064_ == 0)
{
lean_ctor_set(v___x_1063_, 3, v___x_1067_);
v___x_1069_ = v___x_1063_;
goto v_reusejp_1068_;
}
else
{
lean_object* v_reuseFailAlloc_1074_; 
v_reuseFailAlloc_1074_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1074_, 0, v_specBackwardRuleCache_1052_);
lean_ctor_set(v_reuseFailAlloc_1074_, 1, v_splitBackwardRuleCache_1053_);
lean_ctor_set(v_reuseFailAlloc_1074_, 2, v_latticeBackwardRuleCache_1054_);
lean_ctor_set(v_reuseFailAlloc_1074_, 3, v___x_1067_);
lean_ctor_set(v_reuseFailAlloc_1074_, 4, v_frameDB_1056_);
lean_ctor_set(v_reuseFailAlloc_1074_, 5, v_invariants_1057_);
lean_ctor_set(v_reuseFailAlloc_1074_, 6, v_vcs_1058_);
lean_ctor_set(v_reuseFailAlloc_1074_, 7, v_simpState_1059_);
lean_ctor_set(v_reuseFailAlloc_1074_, 8, v_fuel_1060_);
lean_ctor_set(v_reuseFailAlloc_1074_, 9, v_inlineHandledInvariants_1061_);
v___x_1069_ = v_reuseFailAlloc_1074_;
goto v_reusejp_1068_;
}
v_reusejp_1068_:
{
lean_object* v___x_1070_; lean_object* v___x_1072_; 
v___x_1070_ = lean_st_ref_put(v_a_1015_, v___x_1069_);
if (v_isShared_1050_ == 0)
{
lean_ctor_set(v___x_1049_, 0, v___x_1066_);
v___x_1072_ = v___x_1049_;
goto v_reusejp_1071_;
}
else
{
lean_object* v_reuseFailAlloc_1073_; 
v_reuseFailAlloc_1073_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1073_, 0, v___x_1066_);
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
}
else
{
lean_object* v_a_1078_; lean_object* v___x_1080_; uint8_t v_isShared_1081_; uint8_t v_isSharedCheck_1085_; 
lean_del_object(v___x_1044_);
lean_dec(v_frameIdx_1042_);
lean_dec(v_splitVCIdx_1041_);
lean_dec_ref_known(v_key_1028_, 2);
v_a_1078_ = lean_ctor_get(v___x_1046_, 0);
v_isSharedCheck_1085_ = !lean_is_exclusive(v___x_1046_);
if (v_isSharedCheck_1085_ == 0)
{
v___x_1080_ = v___x_1046_;
v_isShared_1081_ = v_isSharedCheck_1085_;
goto v_resetjp_1079_;
}
else
{
lean_inc(v_a_1078_);
lean_dec(v___x_1046_);
v___x_1080_ = lean_box(0);
v_isShared_1081_ = v_isSharedCheck_1085_;
goto v_resetjp_1079_;
}
v_resetjp_1079_:
{
lean_object* v___x_1083_; 
if (v_isShared_1081_ == 0)
{
v___x_1083_ = v___x_1080_;
goto v_reusejp_1082_;
}
else
{
lean_object* v_reuseFailAlloc_1084_; 
v_reuseFailAlloc_1084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1084_, 0, v_a_1078_);
v___x_1083_ = v_reuseFailAlloc_1084_;
goto v_reusejp_1082_;
}
v_reusejp_1082_:
{
return v___x_1083_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_key_1028_, 2);
return v___x_1038_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_mkFrameBackwardRuleCached___redArg___boxed(lean_object* v_fp_1087_, lean_object* v_info_1088_, lean_object* v_a_1089_, lean_object* v_a_1090_, lean_object* v_a_1091_, lean_object* v_a_1092_, lean_object* v_a_1093_, lean_object* v_a_1094_, lean_object* v_a_1095_, lean_object* v_a_1096_){
_start:
{
lean_object* v_res_1097_; 
v_res_1097_ = l_Lean_Elab_Tactic_VCGen_mkFrameBackwardRuleCached___redArg(v_fp_1087_, v_info_1088_, v_a_1089_, v_a_1090_, v_a_1091_, v_a_1092_, v_a_1093_, v_a_1094_, v_a_1095_);
lean_dec(v_a_1095_);
lean_dec_ref(v_a_1094_);
lean_dec(v_a_1093_);
lean_dec_ref(v_a_1092_);
lean_dec(v_a_1091_);
lean_dec_ref(v_a_1090_);
lean_dec(v_a_1089_);
return v_res_1097_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_mkFrameBackwardRuleCached(lean_object* v_fp_1098_, lean_object* v_info_1099_, lean_object* v_a_1100_, lean_object* v_a_1101_, lean_object* v_a_1102_, lean_object* v_a_1103_, lean_object* v_a_1104_, lean_object* v_a_1105_, lean_object* v_a_1106_, lean_object* v_a_1107_, lean_object* v_a_1108_, lean_object* v_a_1109_, lean_object* v_a_1110_){
_start:
{
lean_object* v___x_1112_; 
v___x_1112_ = l_Lean_Elab_Tactic_VCGen_mkFrameBackwardRuleCached___redArg(v_fp_1098_, v_info_1099_, v_a_1101_, v_a_1105_, v_a_1106_, v_a_1107_, v_a_1108_, v_a_1109_, v_a_1110_);
return v___x_1112_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_mkFrameBackwardRuleCached___boxed(lean_object* v_fp_1113_, lean_object* v_info_1114_, lean_object* v_a_1115_, lean_object* v_a_1116_, lean_object* v_a_1117_, lean_object* v_a_1118_, lean_object* v_a_1119_, lean_object* v_a_1120_, lean_object* v_a_1121_, lean_object* v_a_1122_, lean_object* v_a_1123_, lean_object* v_a_1124_, lean_object* v_a_1125_, lean_object* v_a_1126_){
_start:
{
lean_object* v_res_1127_; 
v_res_1127_ = l_Lean_Elab_Tactic_VCGen_mkFrameBackwardRuleCached(v_fp_1113_, v_info_1114_, v_a_1115_, v_a_1116_, v_a_1117_, v_a_1118_, v_a_1119_, v_a_1120_, v_a_1121_, v_a_1122_, v_a_1123_, v_a_1124_, v_a_1125_);
lean_dec(v_a_1125_);
lean_dec_ref(v_a_1124_);
lean_dec(v_a_1123_);
lean_dec_ref(v_a_1122_);
lean_dec(v_a_1121_);
lean_dec_ref(v_a_1120_);
lean_dec(v_a_1119_);
lean_dec_ref(v_a_1118_);
lean_dec(v_a_1117_);
lean_dec(v_a_1116_);
lean_dec_ref(v_a_1115_);
return v_res_1127_;
}
}
lean_object* runtime_initialize_Lean_Elab_Tactic_Do_VCGen_Split(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_VCGen_Context(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_VCGen_RuleConstruction(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_VCGen_LatticeOp(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_VCGen_Util(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_InferType(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_VCGen_RuleCache(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Elab_Tactic_Do_VCGen_Split(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_VCGen_Context(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_VCGen_RuleConstruction(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_VCGen_LatticeOp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_VCGen_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_InferType(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_VCGen_RuleCache(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Tactic_Do_VCGen_Split(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_VCGen_Context(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_VCGen_RuleConstruction(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_VCGen_LatticeOp(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_VCGen_Util(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_InferType(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_VCGen_RuleCache(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Tactic_Do_VCGen_Split(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_VCGen_Context(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_VCGen_RuleConstruction(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_VCGen_LatticeOp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_VCGen_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_InferType(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_VCGen_RuleCache(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_VCGen_RuleCache(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_VCGen_RuleCache(builtin);
}
#ifdef __cplusplus
}
#endif
