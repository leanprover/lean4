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
v___y_157_ = v___x_170_;
goto v___jp_156_;
}
else
{
uint8_t v___x_171_; 
v___x_171_ = lean_nat_dec_eq(v_snd_165_, v_snd_167_);
v___y_157_ = v___x_171_;
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__3___redArg___boxed(lean_object* v_a_172_, lean_object* v_x_173_){
_start:
{
uint8_t v_res_174_; lean_object* v_r_175_; 
v_res_174_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__3___redArg(v_a_172_, v_x_173_);
lean_dec(v_x_173_);
lean_dec_ref(v_a_172_);
v_r_175_ = lean_box(v_res_174_);
return v_r_175_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__4_spec__5_spec__6___redArg(lean_object* v_x_176_, lean_object* v_x_177_){
_start:
{
if (lean_obj_tag(v_x_177_) == 0)
{
return v_x_176_;
}
else
{
lean_object* v_key_178_; lean_object* v_value_179_; lean_object* v_tail_180_; lean_object* v___x_182_; uint8_t v_isShared_183_; uint8_t v_isSharedCheck_217_; 
v_key_178_ = lean_ctor_get(v_x_177_, 0);
v_value_179_ = lean_ctor_get(v_x_177_, 1);
v_tail_180_ = lean_ctor_get(v_x_177_, 2);
v_isSharedCheck_217_ = !lean_is_exclusive(v_x_177_);
if (v_isSharedCheck_217_ == 0)
{
v___x_182_ = v_x_177_;
v_isShared_183_ = v_isSharedCheck_217_;
goto v_resetjp_181_;
}
else
{
lean_inc(v_tail_180_);
lean_inc(v_value_179_);
lean_inc(v_key_178_);
lean_dec(v_x_177_);
v___x_182_ = lean_box(0);
v_isShared_183_ = v_isSharedCheck_217_;
goto v_resetjp_181_;
}
v_resetjp_181_:
{
lean_object* v_fst_184_; lean_object* v_snd_185_; lean_object* v___x_186_; uint64_t v___y_188_; 
v_fst_184_ = lean_ctor_get(v_key_178_, 0);
v_snd_185_ = lean_ctor_get(v_key_178_, 1);
v___x_186_ = lean_array_get_size(v_x_176_);
if (lean_obj_tag(v_fst_184_) == 0)
{
uint64_t v___x_215_; 
v___x_215_ = 1723ULL;
v___y_188_ = v___x_215_;
goto v___jp_187_;
}
else
{
uint64_t v_hash_216_; 
v_hash_216_ = lean_ctor_get_uint64(v_fst_184_, sizeof(void*)*2);
v___y_188_ = v_hash_216_;
goto v___jp_187_;
}
v___jp_187_:
{
lean_object* v_fst_189_; lean_object* v_snd_190_; size_t v___x_191_; size_t v___x_192_; size_t v___x_193_; uint64_t v___x_194_; uint64_t v___x_195_; uint64_t v___x_196_; uint64_t v___x_197_; uint64_t v___x_198_; uint64_t v___x_199_; uint64_t v_fold_200_; uint64_t v___x_201_; uint64_t v___x_202_; uint64_t v___x_203_; size_t v___x_204_; size_t v___x_205_; size_t v___x_206_; size_t v___x_207_; size_t v___x_208_; lean_object* v___x_209_; lean_object* v___x_211_; 
v_fst_189_ = lean_ctor_get(v_snd_185_, 0);
v_snd_190_ = lean_ctor_get(v_snd_185_, 1);
v___x_191_ = lean_ptr_addr(v_fst_189_);
v___x_192_ = ((size_t)3ULL);
v___x_193_ = lean_usize_shift_right(v___x_191_, v___x_192_);
v___x_194_ = lean_usize_to_uint64(v___x_193_);
v___x_195_ = lean_uint64_of_nat(v_snd_190_);
v___x_196_ = lean_uint64_mix_hash(v___x_194_, v___x_195_);
v___x_197_ = lean_uint64_mix_hash(v___y_188_, v___x_196_);
v___x_198_ = 32ULL;
v___x_199_ = lean_uint64_shift_right(v___x_197_, v___x_198_);
v_fold_200_ = lean_uint64_xor(v___x_197_, v___x_199_);
v___x_201_ = 16ULL;
v___x_202_ = lean_uint64_shift_right(v_fold_200_, v___x_201_);
v___x_203_ = lean_uint64_xor(v_fold_200_, v___x_202_);
v___x_204_ = lean_uint64_to_usize(v___x_203_);
v___x_205_ = lean_usize_of_nat(v___x_186_);
v___x_206_ = ((size_t)1ULL);
v___x_207_ = lean_usize_sub(v___x_205_, v___x_206_);
v___x_208_ = lean_usize_land(v___x_204_, v___x_207_);
v___x_209_ = lean_array_uget_borrowed(v_x_176_, v___x_208_);
lean_inc(v___x_209_);
if (v_isShared_183_ == 0)
{
lean_ctor_set(v___x_182_, 2, v___x_209_);
v___x_211_ = v___x_182_;
goto v_reusejp_210_;
}
else
{
lean_object* v_reuseFailAlloc_214_; 
v_reuseFailAlloc_214_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_214_, 0, v_key_178_);
lean_ctor_set(v_reuseFailAlloc_214_, 1, v_value_179_);
lean_ctor_set(v_reuseFailAlloc_214_, 2, v___x_209_);
v___x_211_ = v_reuseFailAlloc_214_;
goto v_reusejp_210_;
}
v_reusejp_210_:
{
lean_object* v___x_212_; 
v___x_212_ = lean_array_uset(v_x_176_, v___x_208_, v___x_211_);
v_x_176_ = v___x_212_;
v_x_177_ = v_tail_180_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__4_spec__5___redArg(lean_object* v_i_218_, lean_object* v_source_219_, lean_object* v_target_220_){
_start:
{
lean_object* v___x_221_; uint8_t v___x_222_; 
v___x_221_ = lean_array_get_size(v_source_219_);
v___x_222_ = lean_nat_dec_lt(v_i_218_, v___x_221_);
if (v___x_222_ == 0)
{
lean_dec_ref(v_source_219_);
lean_dec(v_i_218_);
return v_target_220_;
}
else
{
lean_object* v_es_223_; lean_object* v___x_224_; lean_object* v_source_225_; lean_object* v_target_226_; lean_object* v___x_227_; lean_object* v___x_228_; 
v_es_223_ = lean_array_fget(v_source_219_, v_i_218_);
v___x_224_ = lean_box(0);
v_source_225_ = lean_array_fset(v_source_219_, v_i_218_, v___x_224_);
v_target_226_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__4_spec__5_spec__6___redArg(v_target_220_, v_es_223_);
v___x_227_ = lean_unsigned_to_nat(1u);
v___x_228_ = lean_nat_add(v_i_218_, v___x_227_);
lean_dec(v_i_218_);
v_i_218_ = v___x_228_;
v_source_219_ = v_source_225_;
v_target_220_ = v_target_226_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__4___redArg(lean_object* v_data_230_){
_start:
{
lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v_nbuckets_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; 
v___x_231_ = lean_array_get_size(v_data_230_);
v___x_232_ = lean_unsigned_to_nat(2u);
v_nbuckets_233_ = lean_nat_mul(v___x_231_, v___x_232_);
v___x_234_ = lean_unsigned_to_nat(0u);
v___x_235_ = lean_box(0);
v___x_236_ = lean_mk_array(v_nbuckets_233_, v___x_235_);
v___x_237_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__4_spec__5___redArg(v___x_234_, v_data_230_, v___x_236_);
return v___x_237_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__5___redArg(lean_object* v_a_238_, lean_object* v_b_239_, lean_object* v_x_240_){
_start:
{
if (lean_obj_tag(v_x_240_) == 0)
{
lean_dec(v_b_239_);
lean_dec_ref(v_a_238_);
return v_x_240_;
}
else
{
lean_object* v_key_241_; lean_object* v_value_242_; lean_object* v_tail_243_; lean_object* v___x_245_; uint8_t v_isShared_246_; uint8_t v_isSharedCheck_269_; 
v_key_241_ = lean_ctor_get(v_x_240_, 0);
v_value_242_ = lean_ctor_get(v_x_240_, 1);
v_tail_243_ = lean_ctor_get(v_x_240_, 2);
v_isSharedCheck_269_ = !lean_is_exclusive(v_x_240_);
if (v_isSharedCheck_269_ == 0)
{
v___x_245_ = v_x_240_;
v_isShared_246_ = v_isSharedCheck_269_;
goto v_resetjp_244_;
}
else
{
lean_inc(v_tail_243_);
lean_inc(v_value_242_);
lean_inc(v_key_241_);
lean_dec(v_x_240_);
v___x_245_ = lean_box(0);
v_isShared_246_ = v_isSharedCheck_269_;
goto v_resetjp_244_;
}
v_resetjp_244_:
{
uint8_t v___y_248_; lean_object* v_fst_256_; lean_object* v_snd_257_; lean_object* v_fst_258_; lean_object* v_snd_259_; uint8_t v___x_260_; 
v_fst_256_ = lean_ctor_get(v_key_241_, 0);
v_snd_257_ = lean_ctor_get(v_key_241_, 1);
v_fst_258_ = lean_ctor_get(v_a_238_, 0);
v_snd_259_ = lean_ctor_get(v_a_238_, 1);
v___x_260_ = lean_name_eq(v_fst_256_, v_fst_258_);
if (v___x_260_ == 0)
{
v___y_248_ = v___x_260_;
goto v___jp_247_;
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
v___y_248_ = v___x_267_;
goto v___jp_247_;
}
else
{
uint8_t v___x_268_; 
v___x_268_ = lean_nat_dec_eq(v_snd_262_, v_snd_264_);
v___y_248_ = v___x_268_;
goto v___jp_247_;
}
}
v___jp_247_:
{
if (v___y_248_ == 0)
{
lean_object* v___x_249_; lean_object* v___x_251_; 
v___x_249_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__5___redArg(v_a_238_, v_b_239_, v_tail_243_);
if (v_isShared_246_ == 0)
{
lean_ctor_set(v___x_245_, 2, v___x_249_);
v___x_251_ = v___x_245_;
goto v_reusejp_250_;
}
else
{
lean_object* v_reuseFailAlloc_252_; 
v_reuseFailAlloc_252_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_252_, 0, v_key_241_);
lean_ctor_set(v_reuseFailAlloc_252_, 1, v_value_242_);
lean_ctor_set(v_reuseFailAlloc_252_, 2, v___x_249_);
v___x_251_ = v_reuseFailAlloc_252_;
goto v_reusejp_250_;
}
v_reusejp_250_:
{
return v___x_251_;
}
}
else
{
lean_object* v___x_254_; 
lean_dec(v_value_242_);
lean_dec(v_key_241_);
if (v_isShared_246_ == 0)
{
lean_ctor_set(v___x_245_, 1, v_b_239_);
lean_ctor_set(v___x_245_, 0, v_a_238_);
v___x_254_ = v___x_245_;
goto v_reusejp_253_;
}
else
{
lean_object* v_reuseFailAlloc_255_; 
v_reuseFailAlloc_255_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_255_, 0, v_a_238_);
lean_ctor_set(v_reuseFailAlloc_255_, 1, v_b_239_);
lean_ctor_set(v_reuseFailAlloc_255_, 2, v_tail_243_);
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
v___y_339_ = v___x_353_;
goto v___jp_338_;
}
else
{
uint8_t v___x_354_; 
v___x_354_ = lean_nat_dec_eq(v_snd_348_, v_snd_350_);
v___y_339_ = v___x_354_;
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__0_spec__0___redArg___boxed(lean_object* v_a_355_, lean_object* v_x_356_){
_start:
{
lean_object* v_res_357_; 
v_res_357_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__0_spec__0___redArg(v_a_355_, v_x_356_);
lean_dec(v_x_356_);
lean_dec_ref(v_a_355_);
return v_res_357_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg(lean_object* v_m_358_, lean_object* v_a_359_){
_start:
{
lean_object* v_buckets_360_; lean_object* v_fst_361_; lean_object* v_snd_362_; lean_object* v___x_363_; uint64_t v___y_365_; 
v_buckets_360_ = lean_ctor_get(v_m_358_, 1);
v_fst_361_ = lean_ctor_get(v_a_359_, 0);
v_snd_362_ = lean_ctor_get(v_a_359_, 1);
v___x_363_ = lean_array_get_size(v_buckets_360_);
if (lean_obj_tag(v_fst_361_) == 0)
{
uint64_t v___x_388_; 
v___x_388_ = 1723ULL;
v___y_365_ = v___x_388_;
goto v___jp_364_;
}
else
{
uint64_t v_hash_389_; 
v_hash_389_ = lean_ctor_get_uint64(v_fst_361_, sizeof(void*)*2);
v___y_365_ = v_hash_389_;
goto v___jp_364_;
}
v___jp_364_:
{
lean_object* v_fst_366_; lean_object* v_snd_367_; size_t v___x_368_; size_t v___x_369_; size_t v___x_370_; uint64_t v___x_371_; uint64_t v___x_372_; uint64_t v___x_373_; uint64_t v___x_374_; uint64_t v___x_375_; uint64_t v___x_376_; uint64_t v_fold_377_; uint64_t v___x_378_; uint64_t v___x_379_; uint64_t v___x_380_; size_t v___x_381_; size_t v___x_382_; size_t v___x_383_; size_t v___x_384_; size_t v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; 
v_fst_366_ = lean_ctor_get(v_snd_362_, 0);
v_snd_367_ = lean_ctor_get(v_snd_362_, 1);
v___x_368_ = lean_ptr_addr(v_fst_366_);
v___x_369_ = ((size_t)3ULL);
v___x_370_ = lean_usize_shift_right(v___x_368_, v___x_369_);
v___x_371_ = lean_usize_to_uint64(v___x_370_);
v___x_372_ = lean_uint64_of_nat(v_snd_367_);
v___x_373_ = lean_uint64_mix_hash(v___x_371_, v___x_372_);
v___x_374_ = lean_uint64_mix_hash(v___y_365_, v___x_373_);
v___x_375_ = 32ULL;
v___x_376_ = lean_uint64_shift_right(v___x_374_, v___x_375_);
v_fold_377_ = lean_uint64_xor(v___x_374_, v___x_376_);
v___x_378_ = 16ULL;
v___x_379_ = lean_uint64_shift_right(v_fold_377_, v___x_378_);
v___x_380_ = lean_uint64_xor(v_fold_377_, v___x_379_);
v___x_381_ = lean_uint64_to_usize(v___x_380_);
v___x_382_ = lean_usize_of_nat(v___x_363_);
v___x_383_ = ((size_t)1ULL);
v___x_384_ = lean_usize_sub(v___x_382_, v___x_383_);
v___x_385_ = lean_usize_land(v___x_381_, v___x_384_);
v___x_386_ = lean_array_uget_borrowed(v_buckets_360_, v___x_385_);
v___x_387_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__0_spec__0___redArg(v_a_359_, v___x_386_);
return v___x_387_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg___boxed(lean_object* v_m_390_, lean_object* v_a_391_){
_start:
{
lean_object* v_res_392_; 
v_res_392_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg(v_m_390_, v_a_391_);
lean_dec_ref(v_a_391_);
lean_dec_ref(v_m_390_);
return v_res_392_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached(lean_object* v_specThm_395_, lean_object* v_info_396_, lean_object* v_a_397_, lean_object* v_a_398_, lean_object* v_a_399_, lean_object* v_a_400_, lean_object* v_a_401_, lean_object* v_a_402_, lean_object* v_a_403_, lean_object* v_a_404_, lean_object* v_a_405_, lean_object* v_a_406_, lean_object* v_a_407_){
_start:
{
lean_object* v___x_409_; lean_object* v_proof_410_; lean_object* v_excessArgs_411_; lean_object* v_specBackwardRuleCache_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v_key_417_; lean_object* v___x_418_; 
v___x_409_ = lean_st_ref_get(v_a_398_);
v_proof_410_ = lean_ctor_get(v_specThm_395_, 1);
v_excessArgs_411_ = lean_ctor_get(v_info_396_, 2);
v_specBackwardRuleCache_412_ = lean_ctor_get(v___x_409_, 0);
lean_inc_ref(v_specBackwardRuleCache_412_);
lean_dec(v___x_409_);
v___x_413_ = l_Lean_Elab_Tactic_VCGen_SpecAttr_SpecProof_key(v_proof_410_);
v___x_414_ = l_Lean_Elab_Tactic_VCGen_WPApp_instWP(v_info_396_);
v___x_415_ = lean_array_get_size(v_excessArgs_411_);
v___x_416_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_416_, 0, v___x_414_);
lean_ctor_set(v___x_416_, 1, v___x_415_);
v_key_417_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_key_417_, 0, v___x_413_);
lean_ctor_set(v_key_417_, 1, v___x_416_);
v___x_418_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg(v_specBackwardRuleCache_412_, v_key_417_);
lean_dec_ref(v_specBackwardRuleCache_412_);
if (lean_obj_tag(v___x_418_) == 1)
{
lean_object* v___x_419_; 
lean_dec_ref_known(v_key_417_, 2);
lean_dec_ref(v_info_396_);
lean_dec_ref(v_specThm_395_);
v___x_419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_419_, 0, v___x_418_);
return v___x_419_;
}
else
{
lean_object* v___x_420_; lean_object* v___f_421_; uint8_t v___x_422_; lean_object* v___x_423_; 
lean_dec(v___x_418_);
v___x_420_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached___closed__0));
v___f_421_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached___lam__0___boxed), 15, 3);
lean_closure_set(v___f_421_, 0, v_specThm_395_);
lean_closure_set(v___f_421_, 1, v_info_396_);
lean_closure_set(v___f_421_, 2, v___x_420_);
v___x_422_ = 0;
v___x_423_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__1___redArg(v___f_421_, v___x_422_, v_a_397_, v_a_398_, v_a_399_, v_a_400_, v_a_401_, v_a_402_, v_a_403_, v_a_404_, v_a_405_, v_a_406_, v_a_407_);
if (lean_obj_tag(v___x_423_) == 0)
{
lean_object* v_a_424_; lean_object* v___x_426_; uint8_t v_isShared_427_; uint8_t v_isSharedCheck_482_; 
v_a_424_ = lean_ctor_get(v___x_423_, 0);
v_isSharedCheck_482_ = !lean_is_exclusive(v___x_423_);
if (v_isSharedCheck_482_ == 0)
{
v___x_426_ = v___x_423_;
v_isShared_427_ = v_isSharedCheck_482_;
goto v_resetjp_425_;
}
else
{
lean_inc(v_a_424_);
lean_dec(v___x_423_);
v___x_426_ = lean_box(0);
v_isShared_427_ = v_isSharedCheck_482_;
goto v_resetjp_425_;
}
v_resetjp_425_:
{
if (lean_obj_tag(v_a_424_) == 0)
{
lean_object* v___x_428_; lean_object* v___x_430_; 
lean_dec_ref_known(v_key_417_, 2);
v___x_428_ = lean_box(0);
if (v_isShared_427_ == 0)
{
lean_ctor_set(v___x_426_, 0, v___x_428_);
v___x_430_ = v___x_426_;
goto v_reusejp_429_;
}
else
{
lean_object* v_reuseFailAlloc_431_; 
v_reuseFailAlloc_431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_431_, 0, v___x_428_);
v___x_430_ = v_reuseFailAlloc_431_;
goto v_reusejp_429_;
}
v_reusejp_429_:
{
return v___x_430_;
}
}
else
{
lean_object* v_val_432_; 
v_val_432_ = lean_ctor_get(v_a_424_, 0);
lean_inc(v_val_432_);
lean_dec_ref_known(v_a_424_, 1);
if (lean_obj_tag(v_val_432_) == 1)
{
lean_object* v_val_433_; lean_object* v___x_435_; uint8_t v_isShared_436_; uint8_t v_isSharedCheck_477_; 
lean_del_object(v___x_426_);
v_val_433_ = lean_ctor_get(v_val_432_, 0);
v_isSharedCheck_477_ = !lean_is_exclusive(v_val_432_);
if (v_isSharedCheck_477_ == 0)
{
v___x_435_ = v_val_432_;
v_isShared_436_ = v_isSharedCheck_477_;
goto v_resetjp_434_;
}
else
{
lean_inc(v_val_433_);
lean_dec(v_val_432_);
v___x_435_ = lean_box(0);
v_isShared_436_ = v_isSharedCheck_477_;
goto v_resetjp_434_;
}
v_resetjp_434_:
{
lean_object* v___x_437_; 
v___x_437_ = l_Lean_Meta_Sym_BackwardRule_shareCommon(v_val_433_, v_a_402_, v_a_403_, v_a_404_, v_a_405_, v_a_406_, v_a_407_);
if (lean_obj_tag(v___x_437_) == 0)
{
lean_object* v_a_438_; lean_object* v___x_440_; uint8_t v_isShared_441_; uint8_t v_isSharedCheck_468_; 
v_a_438_ = lean_ctor_get(v___x_437_, 0);
v_isSharedCheck_468_ = !lean_is_exclusive(v___x_437_);
if (v_isSharedCheck_468_ == 0)
{
v___x_440_ = v___x_437_;
v_isShared_441_ = v_isSharedCheck_468_;
goto v_resetjp_439_;
}
else
{
lean_inc(v_a_438_);
lean_dec(v___x_437_);
v___x_440_ = lean_box(0);
v_isShared_441_ = v_isSharedCheck_468_;
goto v_resetjp_439_;
}
v_resetjp_439_:
{
lean_object* v___x_442_; lean_object* v_specBackwardRuleCache_443_; lean_object* v_splitBackwardRuleCache_444_; lean_object* v_latticeBackwardRuleCache_445_; lean_object* v_frameBackwardRuleCache_446_; lean_object* v_frameDB_447_; lean_object* v_invariants_448_; lean_object* v_vcs_449_; lean_object* v_simpState_450_; lean_object* v_fuel_451_; lean_object* v_inlineHandledInvariants_452_; lean_object* v___x_454_; uint8_t v_isShared_455_; uint8_t v_isSharedCheck_467_; 
v___x_442_ = lean_st_ref_take(v_a_398_);
v_specBackwardRuleCache_443_ = lean_ctor_get(v___x_442_, 0);
v_splitBackwardRuleCache_444_ = lean_ctor_get(v___x_442_, 1);
v_latticeBackwardRuleCache_445_ = lean_ctor_get(v___x_442_, 2);
v_frameBackwardRuleCache_446_ = lean_ctor_get(v___x_442_, 3);
v_frameDB_447_ = lean_ctor_get(v___x_442_, 4);
v_invariants_448_ = lean_ctor_get(v___x_442_, 5);
v_vcs_449_ = lean_ctor_get(v___x_442_, 6);
v_simpState_450_ = lean_ctor_get(v___x_442_, 7);
v_fuel_451_ = lean_ctor_get(v___x_442_, 8);
v_inlineHandledInvariants_452_ = lean_ctor_get(v___x_442_, 9);
v_isSharedCheck_467_ = !lean_is_exclusive(v___x_442_);
if (v_isSharedCheck_467_ == 0)
{
v___x_454_ = v___x_442_;
v_isShared_455_ = v_isSharedCheck_467_;
goto v_resetjp_453_;
}
else
{
lean_inc(v_inlineHandledInvariants_452_);
lean_inc(v_fuel_451_);
lean_inc(v_simpState_450_);
lean_inc(v_vcs_449_);
lean_inc(v_invariants_448_);
lean_inc(v_frameDB_447_);
lean_inc(v_frameBackwardRuleCache_446_);
lean_inc(v_latticeBackwardRuleCache_445_);
lean_inc(v_splitBackwardRuleCache_444_);
lean_inc(v_specBackwardRuleCache_443_);
lean_dec(v___x_442_);
v___x_454_ = lean_box(0);
v_isShared_455_ = v_isSharedCheck_467_;
goto v_resetjp_453_;
}
v_resetjp_453_:
{
lean_object* v___x_457_; 
lean_inc(v_a_438_);
if (v_isShared_436_ == 0)
{
lean_ctor_set(v___x_435_, 0, v_a_438_);
v___x_457_ = v___x_435_;
goto v_reusejp_456_;
}
else
{
lean_object* v_reuseFailAlloc_466_; 
v_reuseFailAlloc_466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_466_, 0, v_a_438_);
v___x_457_ = v_reuseFailAlloc_466_;
goto v_reusejp_456_;
}
v_reusejp_456_:
{
lean_object* v___x_458_; lean_object* v___x_460_; 
v___x_458_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2___redArg(v_specBackwardRuleCache_443_, v_key_417_, v_a_438_);
if (v_isShared_455_ == 0)
{
lean_ctor_set(v___x_454_, 0, v___x_458_);
v___x_460_ = v___x_454_;
goto v_reusejp_459_;
}
else
{
lean_object* v_reuseFailAlloc_465_; 
v_reuseFailAlloc_465_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_465_, 0, v___x_458_);
lean_ctor_set(v_reuseFailAlloc_465_, 1, v_splitBackwardRuleCache_444_);
lean_ctor_set(v_reuseFailAlloc_465_, 2, v_latticeBackwardRuleCache_445_);
lean_ctor_set(v_reuseFailAlloc_465_, 3, v_frameBackwardRuleCache_446_);
lean_ctor_set(v_reuseFailAlloc_465_, 4, v_frameDB_447_);
lean_ctor_set(v_reuseFailAlloc_465_, 5, v_invariants_448_);
lean_ctor_set(v_reuseFailAlloc_465_, 6, v_vcs_449_);
lean_ctor_set(v_reuseFailAlloc_465_, 7, v_simpState_450_);
lean_ctor_set(v_reuseFailAlloc_465_, 8, v_fuel_451_);
lean_ctor_set(v_reuseFailAlloc_465_, 9, v_inlineHandledInvariants_452_);
v___x_460_ = v_reuseFailAlloc_465_;
goto v_reusejp_459_;
}
v_reusejp_459_:
{
lean_object* v___x_461_; lean_object* v___x_463_; 
v___x_461_ = lean_st_ref_put(v_a_398_, v___x_460_);
if (v_isShared_441_ == 0)
{
lean_ctor_set(v___x_440_, 0, v___x_457_);
v___x_463_ = v___x_440_;
goto v_reusejp_462_;
}
else
{
lean_object* v_reuseFailAlloc_464_; 
v_reuseFailAlloc_464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_464_, 0, v___x_457_);
v___x_463_ = v_reuseFailAlloc_464_;
goto v_reusejp_462_;
}
v_reusejp_462_:
{
return v___x_463_;
}
}
}
}
}
}
else
{
lean_object* v_a_469_; lean_object* v___x_471_; uint8_t v_isShared_472_; uint8_t v_isSharedCheck_476_; 
lean_del_object(v___x_435_);
lean_dec_ref_known(v_key_417_, 2);
v_a_469_ = lean_ctor_get(v___x_437_, 0);
v_isSharedCheck_476_ = !lean_is_exclusive(v___x_437_);
if (v_isSharedCheck_476_ == 0)
{
v___x_471_ = v___x_437_;
v_isShared_472_ = v_isSharedCheck_476_;
goto v_resetjp_470_;
}
else
{
lean_inc(v_a_469_);
lean_dec(v___x_437_);
v___x_471_ = lean_box(0);
v_isShared_472_ = v_isSharedCheck_476_;
goto v_resetjp_470_;
}
v_resetjp_470_:
{
lean_object* v___x_474_; 
if (v_isShared_472_ == 0)
{
v___x_474_ = v___x_471_;
goto v_reusejp_473_;
}
else
{
lean_object* v_reuseFailAlloc_475_; 
v_reuseFailAlloc_475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_475_, 0, v_a_469_);
v___x_474_ = v_reuseFailAlloc_475_;
goto v_reusejp_473_;
}
v_reusejp_473_:
{
return v___x_474_;
}
}
}
}
}
else
{
lean_object* v___x_478_; lean_object* v___x_480_; 
lean_dec(v_val_432_);
lean_dec_ref_known(v_key_417_, 2);
v___x_478_ = lean_box(0);
if (v_isShared_427_ == 0)
{
lean_ctor_set(v___x_426_, 0, v___x_478_);
v___x_480_ = v___x_426_;
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
}
}
else
{
lean_object* v_a_483_; lean_object* v___x_485_; uint8_t v_isShared_486_; uint8_t v_isSharedCheck_490_; 
lean_dec_ref_known(v_key_417_, 2);
v_a_483_ = lean_ctor_get(v___x_423_, 0);
v_isSharedCheck_490_ = !lean_is_exclusive(v___x_423_);
if (v_isSharedCheck_490_ == 0)
{
v___x_485_ = v___x_423_;
v_isShared_486_ = v_isSharedCheck_490_;
goto v_resetjp_484_;
}
else
{
lean_inc(v_a_483_);
lean_dec(v___x_423_);
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
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached___boxed(lean_object* v_specThm_491_, lean_object* v_info_492_, lean_object* v_a_493_, lean_object* v_a_494_, lean_object* v_a_495_, lean_object* v_a_496_, lean_object* v_a_497_, lean_object* v_a_498_, lean_object* v_a_499_, lean_object* v_a_500_, lean_object* v_a_501_, lean_object* v_a_502_, lean_object* v_a_503_, lean_object* v_a_504_){
_start:
{
lean_object* v_res_505_; 
v_res_505_ = l_Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached(v_specThm_491_, v_info_492_, v_a_493_, v_a_494_, v_a_495_, v_a_496_, v_a_497_, v_a_498_, v_a_499_, v_a_500_, v_a_501_, v_a_502_, v_a_503_);
lean_dec(v_a_503_);
lean_dec_ref(v_a_502_);
lean_dec(v_a_501_);
lean_dec_ref(v_a_500_);
lean_dec(v_a_499_);
lean_dec_ref(v_a_498_);
lean_dec(v_a_497_);
lean_dec_ref(v_a_496_);
lean_dec(v_a_495_);
lean_dec(v_a_494_);
lean_dec_ref(v_a_493_);
return v_res_505_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__0(lean_object* v_00_u03b2_506_, lean_object* v_m_507_, lean_object* v_a_508_){
_start:
{
lean_object* v___x_509_; 
v___x_509_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg(v_m_507_, v_a_508_);
return v___x_509_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__0___boxed(lean_object* v_00_u03b2_510_, lean_object* v_m_511_, lean_object* v_a_512_){
_start:
{
lean_object* v_res_513_; 
v_res_513_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__0(v_00_u03b2_510_, v_m_511_, v_a_512_);
lean_dec_ref(v_a_512_);
lean_dec_ref(v_m_511_);
return v_res_513_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2(lean_object* v_00_u03b2_514_, lean_object* v_m_515_, lean_object* v_a_516_, lean_object* v_b_517_){
_start:
{
lean_object* v___x_518_; 
v___x_518_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2___redArg(v_m_515_, v_a_516_, v_b_517_);
return v___x_518_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__0_spec__0(lean_object* v_00_u03b2_519_, lean_object* v_a_520_, lean_object* v_x_521_){
_start:
{
lean_object* v___x_522_; 
v___x_522_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__0_spec__0___redArg(v_a_520_, v_x_521_);
return v___x_522_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__0_spec__0___boxed(lean_object* v_00_u03b2_523_, lean_object* v_a_524_, lean_object* v_x_525_){
_start:
{
lean_object* v_res_526_; 
v_res_526_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__0_spec__0(v_00_u03b2_523_, v_a_524_, v_x_525_);
lean_dec(v_x_525_);
lean_dec_ref(v_a_524_);
return v_res_526_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__3(lean_object* v_00_u03b2_527_, lean_object* v_a_528_, lean_object* v_x_529_){
_start:
{
uint8_t v___x_530_; 
v___x_530_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__3___redArg(v_a_528_, v_x_529_);
return v___x_530_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__3___boxed(lean_object* v_00_u03b2_531_, lean_object* v_a_532_, lean_object* v_x_533_){
_start:
{
uint8_t v_res_534_; lean_object* v_r_535_; 
v_res_534_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__3(v_00_u03b2_531_, v_a_532_, v_x_533_);
lean_dec(v_x_533_);
lean_dec_ref(v_a_532_);
v_r_535_ = lean_box(v_res_534_);
return v_r_535_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__4(lean_object* v_00_u03b2_536_, lean_object* v_data_537_){
_start:
{
lean_object* v___x_538_; 
v___x_538_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__4___redArg(v_data_537_);
return v___x_538_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__5(lean_object* v_00_u03b2_539_, lean_object* v_a_540_, lean_object* v_b_541_, lean_object* v_x_542_){
_start:
{
lean_object* v___x_543_; 
v___x_543_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__5___redArg(v_a_540_, v_b_541_, v_x_542_);
return v___x_543_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_544_, lean_object* v_i_545_, lean_object* v_source_546_, lean_object* v_target_547_){
_start:
{
lean_object* v___x_548_; 
v___x_548_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__4_spec__5___redArg(v_i_545_, v_source_546_, v_target_547_);
return v___x_548_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__4_spec__5_spec__6(lean_object* v_00_u03b2_549_, lean_object* v_x_550_, lean_object* v_x_551_){
_start:
{
lean_object* v___x_552_; 
v___x_552_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__4_spec__5_spec__6___redArg(v_x_550_, v_x_551_);
return v___x_552_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_mkBackwardRuleForSplitCached___redArg(lean_object* v_splitInfo_562_, lean_object* v_info_563_, lean_object* v_a_564_, lean_object* v_a_565_, lean_object* v_a_566_, lean_object* v_a_567_, lean_object* v_a_568_, lean_object* v_a_569_, lean_object* v_a_570_){
_start:
{
lean_object* v___y_573_; 
switch(lean_obj_tag(v_splitInfo_562_))
{
case 0:
{
lean_object* v___x_621_; 
v___x_621_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_mkBackwardRuleForSplitCached___redArg___closed__1));
v___y_573_ = v___x_621_;
goto v___jp_572_;
}
case 1:
{
lean_object* v___x_622_; 
v___x_622_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_mkBackwardRuleForSplitCached___redArg___closed__3));
v___y_573_ = v___x_622_;
goto v___jp_572_;
}
case 2:
{
lean_object* v___x_623_; 
v___x_623_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_mkBackwardRuleForSplitCached___redArg___closed__5));
v___y_573_ = v___x_623_;
goto v___jp_572_;
}
default: 
{
lean_object* v_matcherApp_624_; lean_object* v_matcherName_625_; 
v_matcherApp_624_ = lean_ctor_get(v_splitInfo_562_, 0);
v_matcherName_625_ = lean_ctor_get(v_matcherApp_624_, 1);
lean_inc(v_matcherName_625_);
v___y_573_ = v_matcherName_625_;
goto v___jp_572_;
}
}
v___jp_572_:
{
lean_object* v___x_574_; lean_object* v_excessArgs_575_; lean_object* v_splitBackwardRuleCache_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v_key_580_; lean_object* v___x_581_; 
v___x_574_ = lean_st_ref_get(v_a_564_);
v_excessArgs_575_ = lean_ctor_get(v_info_563_, 2);
v_splitBackwardRuleCache_576_ = lean_ctor_get(v___x_574_, 1);
lean_inc_ref(v_splitBackwardRuleCache_576_);
lean_dec(v___x_574_);
v___x_577_ = l_Lean_Elab_Tactic_VCGen_WPApp_instWP(v_info_563_);
v___x_578_ = lean_array_get_size(v_excessArgs_575_);
v___x_579_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_579_, 0, v___x_577_);
lean_ctor_set(v___x_579_, 1, v___x_578_);
v_key_580_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_key_580_, 0, v___y_573_);
lean_ctor_set(v_key_580_, 1, v___x_579_);
v___x_581_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg(v_splitBackwardRuleCache_576_, v_key_580_);
lean_dec_ref(v_splitBackwardRuleCache_576_);
if (lean_obj_tag(v___x_581_) == 1)
{
lean_object* v_val_582_; lean_object* v___x_584_; uint8_t v_isShared_585_; uint8_t v_isSharedCheck_589_; 
lean_dec_ref_known(v_key_580_, 2);
lean_dec_ref(v_info_563_);
lean_dec_ref(v_splitInfo_562_);
v_val_582_ = lean_ctor_get(v___x_581_, 0);
v_isSharedCheck_589_ = !lean_is_exclusive(v___x_581_);
if (v_isSharedCheck_589_ == 0)
{
v___x_584_ = v___x_581_;
v_isShared_585_ = v_isSharedCheck_589_;
goto v_resetjp_583_;
}
else
{
lean_inc(v_val_582_);
lean_dec(v___x_581_);
v___x_584_ = lean_box(0);
v_isShared_585_ = v_isSharedCheck_589_;
goto v_resetjp_583_;
}
v_resetjp_583_:
{
lean_object* v___x_587_; 
if (v_isShared_585_ == 0)
{
lean_ctor_set_tag(v___x_584_, 0);
v___x_587_ = v___x_584_;
goto v_reusejp_586_;
}
else
{
lean_object* v_reuseFailAlloc_588_; 
v_reuseFailAlloc_588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_588_, 0, v_val_582_);
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
lean_object* v___x_590_; 
lean_dec(v___x_581_);
v___x_590_ = l_Lean_Elab_Tactic_VCGen_mkBackwardRuleForSplit(v_splitInfo_562_, v_info_563_, v_a_567_, v_a_568_, v_a_569_, v_a_570_);
if (lean_obj_tag(v___x_590_) == 0)
{
lean_object* v_a_591_; lean_object* v___x_592_; 
v_a_591_ = lean_ctor_get(v___x_590_, 0);
lean_inc(v_a_591_);
lean_dec_ref_known(v___x_590_, 1);
v___x_592_ = l_Lean_Meta_Sym_BackwardRule_shareCommon(v_a_591_, v_a_565_, v_a_566_, v_a_567_, v_a_568_, v_a_569_, v_a_570_);
if (lean_obj_tag(v___x_592_) == 0)
{
lean_object* v_a_593_; lean_object* v___x_595_; uint8_t v_isShared_596_; uint8_t v_isSharedCheck_620_; 
v_a_593_ = lean_ctor_get(v___x_592_, 0);
v_isSharedCheck_620_ = !lean_is_exclusive(v___x_592_);
if (v_isSharedCheck_620_ == 0)
{
v___x_595_ = v___x_592_;
v_isShared_596_ = v_isSharedCheck_620_;
goto v_resetjp_594_;
}
else
{
lean_inc(v_a_593_);
lean_dec(v___x_592_);
v___x_595_ = lean_box(0);
v_isShared_596_ = v_isSharedCheck_620_;
goto v_resetjp_594_;
}
v_resetjp_594_:
{
lean_object* v___x_597_; lean_object* v_specBackwardRuleCache_598_; lean_object* v_splitBackwardRuleCache_599_; lean_object* v_latticeBackwardRuleCache_600_; lean_object* v_frameBackwardRuleCache_601_; lean_object* v_frameDB_602_; lean_object* v_invariants_603_; lean_object* v_vcs_604_; lean_object* v_simpState_605_; lean_object* v_fuel_606_; lean_object* v_inlineHandledInvariants_607_; lean_object* v___x_609_; uint8_t v_isShared_610_; uint8_t v_isSharedCheck_619_; 
v___x_597_ = lean_st_ref_take(v_a_564_);
v_specBackwardRuleCache_598_ = lean_ctor_get(v___x_597_, 0);
v_splitBackwardRuleCache_599_ = lean_ctor_get(v___x_597_, 1);
v_latticeBackwardRuleCache_600_ = lean_ctor_get(v___x_597_, 2);
v_frameBackwardRuleCache_601_ = lean_ctor_get(v___x_597_, 3);
v_frameDB_602_ = lean_ctor_get(v___x_597_, 4);
v_invariants_603_ = lean_ctor_get(v___x_597_, 5);
v_vcs_604_ = lean_ctor_get(v___x_597_, 6);
v_simpState_605_ = lean_ctor_get(v___x_597_, 7);
v_fuel_606_ = lean_ctor_get(v___x_597_, 8);
v_inlineHandledInvariants_607_ = lean_ctor_get(v___x_597_, 9);
v_isSharedCheck_619_ = !lean_is_exclusive(v___x_597_);
if (v_isSharedCheck_619_ == 0)
{
v___x_609_ = v___x_597_;
v_isShared_610_ = v_isSharedCheck_619_;
goto v_resetjp_608_;
}
else
{
lean_inc(v_inlineHandledInvariants_607_);
lean_inc(v_fuel_606_);
lean_inc(v_simpState_605_);
lean_inc(v_vcs_604_);
lean_inc(v_invariants_603_);
lean_inc(v_frameDB_602_);
lean_inc(v_frameBackwardRuleCache_601_);
lean_inc(v_latticeBackwardRuleCache_600_);
lean_inc(v_splitBackwardRuleCache_599_);
lean_inc(v_specBackwardRuleCache_598_);
lean_dec(v___x_597_);
v___x_609_ = lean_box(0);
v_isShared_610_ = v_isSharedCheck_619_;
goto v_resetjp_608_;
}
v_resetjp_608_:
{
lean_object* v___x_611_; lean_object* v___x_613_; 
lean_inc(v_a_593_);
v___x_611_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2___redArg(v_splitBackwardRuleCache_599_, v_key_580_, v_a_593_);
if (v_isShared_610_ == 0)
{
lean_ctor_set(v___x_609_, 1, v___x_611_);
v___x_613_ = v___x_609_;
goto v_reusejp_612_;
}
else
{
lean_object* v_reuseFailAlloc_618_; 
v_reuseFailAlloc_618_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_618_, 0, v_specBackwardRuleCache_598_);
lean_ctor_set(v_reuseFailAlloc_618_, 1, v___x_611_);
lean_ctor_set(v_reuseFailAlloc_618_, 2, v_latticeBackwardRuleCache_600_);
lean_ctor_set(v_reuseFailAlloc_618_, 3, v_frameBackwardRuleCache_601_);
lean_ctor_set(v_reuseFailAlloc_618_, 4, v_frameDB_602_);
lean_ctor_set(v_reuseFailAlloc_618_, 5, v_invariants_603_);
lean_ctor_set(v_reuseFailAlloc_618_, 6, v_vcs_604_);
lean_ctor_set(v_reuseFailAlloc_618_, 7, v_simpState_605_);
lean_ctor_set(v_reuseFailAlloc_618_, 8, v_fuel_606_);
lean_ctor_set(v_reuseFailAlloc_618_, 9, v_inlineHandledInvariants_607_);
v___x_613_ = v_reuseFailAlloc_618_;
goto v_reusejp_612_;
}
v_reusejp_612_:
{
lean_object* v___x_614_; lean_object* v___x_616_; 
v___x_614_ = lean_st_ref_put(v_a_564_, v___x_613_);
if (v_isShared_596_ == 0)
{
v___x_616_ = v___x_595_;
goto v_reusejp_615_;
}
else
{
lean_object* v_reuseFailAlloc_617_; 
v_reuseFailAlloc_617_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_617_, 0, v_a_593_);
v___x_616_ = v_reuseFailAlloc_617_;
goto v_reusejp_615_;
}
v_reusejp_615_:
{
return v___x_616_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_key_580_, 2);
return v___x_592_;
}
}
else
{
lean_dec_ref_known(v_key_580_, 2);
return v___x_590_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_mkBackwardRuleForSplitCached___redArg___boxed(lean_object* v_splitInfo_626_, lean_object* v_info_627_, lean_object* v_a_628_, lean_object* v_a_629_, lean_object* v_a_630_, lean_object* v_a_631_, lean_object* v_a_632_, lean_object* v_a_633_, lean_object* v_a_634_, lean_object* v_a_635_){
_start:
{
lean_object* v_res_636_; 
v_res_636_ = l_Lean_Elab_Tactic_VCGen_mkBackwardRuleForSplitCached___redArg(v_splitInfo_626_, v_info_627_, v_a_628_, v_a_629_, v_a_630_, v_a_631_, v_a_632_, v_a_633_, v_a_634_);
lean_dec(v_a_634_);
lean_dec_ref(v_a_633_);
lean_dec(v_a_632_);
lean_dec_ref(v_a_631_);
lean_dec(v_a_630_);
lean_dec_ref(v_a_629_);
lean_dec(v_a_628_);
return v_res_636_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_mkBackwardRuleForSplitCached(lean_object* v_splitInfo_637_, lean_object* v_info_638_, lean_object* v_a_639_, lean_object* v_a_640_, lean_object* v_a_641_, lean_object* v_a_642_, lean_object* v_a_643_, lean_object* v_a_644_, lean_object* v_a_645_, lean_object* v_a_646_, lean_object* v_a_647_, lean_object* v_a_648_, lean_object* v_a_649_){
_start:
{
lean_object* v___x_651_; 
v___x_651_ = l_Lean_Elab_Tactic_VCGen_mkBackwardRuleForSplitCached___redArg(v_splitInfo_637_, v_info_638_, v_a_640_, v_a_644_, v_a_645_, v_a_646_, v_a_647_, v_a_648_, v_a_649_);
return v___x_651_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_mkBackwardRuleForSplitCached___boxed(lean_object* v_splitInfo_652_, lean_object* v_info_653_, lean_object* v_a_654_, lean_object* v_a_655_, lean_object* v_a_656_, lean_object* v_a_657_, lean_object* v_a_658_, lean_object* v_a_659_, lean_object* v_a_660_, lean_object* v_a_661_, lean_object* v_a_662_, lean_object* v_a_663_, lean_object* v_a_664_, lean_object* v_a_665_){
_start:
{
lean_object* v_res_666_; 
v_res_666_ = l_Lean_Elab_Tactic_VCGen_mkBackwardRuleForSplitCached(v_splitInfo_652_, v_info_653_, v_a_654_, v_a_655_, v_a_656_, v_a_657_, v_a_658_, v_a_659_, v_a_660_, v_a_661_, v_a_662_, v_a_663_, v_a_664_);
lean_dec(v_a_664_);
lean_dec_ref(v_a_663_);
lean_dec(v_a_662_);
lean_dec_ref(v_a_661_);
lean_dec(v_a_660_);
lean_dec_ref(v_a_659_);
lean_dec(v_a_658_);
lean_dec_ref(v_a_657_);
lean_dec(v_a_656_);
lean_dec(v_a_655_);
lean_dec_ref(v_a_654_);
return v_res_666_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1_spec__2___redArg(lean_object* v_a_667_, lean_object* v_x_668_){
_start:
{
if (lean_obj_tag(v_x_668_) == 0)
{
uint8_t v___x_669_; 
v___x_669_ = 0;
return v___x_669_;
}
else
{
lean_object* v_key_670_; lean_object* v_tail_671_; uint8_t v___y_673_; lean_object* v_fst_675_; lean_object* v_snd_676_; lean_object* v_fst_677_; lean_object* v_snd_678_; size_t v___x_679_; size_t v___x_680_; uint8_t v___x_681_; 
v_key_670_ = lean_ctor_get(v_x_668_, 0);
v_tail_671_ = lean_ctor_get(v_x_668_, 2);
v_fst_675_ = lean_ctor_get(v_key_670_, 0);
v_snd_676_ = lean_ctor_get(v_key_670_, 1);
v_fst_677_ = lean_ctor_get(v_a_667_, 0);
v_snd_678_ = lean_ctor_get(v_a_667_, 1);
v___x_679_ = lean_ptr_addr(v_fst_675_);
v___x_680_ = lean_ptr_addr(v_fst_677_);
v___x_681_ = lean_usize_dec_eq(v___x_679_, v___x_680_);
if (v___x_681_ == 0)
{
v___y_673_ = v___x_681_;
goto v___jp_672_;
}
else
{
uint8_t v___x_682_; 
v___x_682_ = lean_nat_dec_eq(v_snd_676_, v_snd_678_);
v___y_673_ = v___x_682_;
goto v___jp_672_;
}
v___jp_672_:
{
if (v___y_673_ == 0)
{
v_x_668_ = v_tail_671_;
goto _start;
}
else
{
return v___y_673_;
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
lean_object* v_key_690_; lean_object* v_value_691_; lean_object* v_tail_692_; lean_object* v___x_694_; uint8_t v_isShared_695_; uint8_t v_isSharedCheck_713_; 
v_key_690_ = lean_ctor_get(v_x_689_, 0);
v_value_691_ = lean_ctor_get(v_x_689_, 1);
v_tail_692_ = lean_ctor_get(v_x_689_, 2);
v_isSharedCheck_713_ = !lean_is_exclusive(v_x_689_);
if (v_isSharedCheck_713_ == 0)
{
v___x_694_ = v_x_689_;
v_isShared_695_ = v_isSharedCheck_713_;
goto v_resetjp_693_;
}
else
{
lean_inc(v_tail_692_);
lean_inc(v_value_691_);
lean_inc(v_key_690_);
lean_dec(v_x_689_);
v___x_694_ = lean_box(0);
v_isShared_695_ = v_isSharedCheck_713_;
goto v_resetjp_693_;
}
v_resetjp_693_:
{
uint8_t v___y_697_; lean_object* v_fst_705_; lean_object* v_snd_706_; lean_object* v_fst_707_; lean_object* v_snd_708_; size_t v___x_709_; size_t v___x_710_; uint8_t v___x_711_; 
v_fst_705_ = lean_ctor_get(v_key_690_, 0);
v_snd_706_ = lean_ctor_get(v_key_690_, 1);
v_fst_707_ = lean_ctor_get(v_a_687_, 0);
v_snd_708_ = lean_ctor_get(v_a_687_, 1);
v___x_709_ = lean_ptr_addr(v_fst_705_);
v___x_710_ = lean_ptr_addr(v_fst_707_);
v___x_711_ = lean_usize_dec_eq(v___x_709_, v___x_710_);
if (v___x_711_ == 0)
{
v___y_697_ = v___x_711_;
goto v___jp_696_;
}
else
{
uint8_t v___x_712_; 
v___x_712_ = lean_nat_dec_eq(v_snd_706_, v_snd_708_);
v___y_697_ = v___x_712_;
goto v___jp_696_;
}
v___jp_696_:
{
if (v___y_697_ == 0)
{
lean_object* v___x_698_; lean_object* v___x_700_; 
v___x_698_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1_spec__4___redArg(v_a_687_, v_b_688_, v_tail_692_);
if (v_isShared_695_ == 0)
{
lean_ctor_set(v___x_694_, 2, v___x_698_);
v___x_700_ = v___x_694_;
goto v_reusejp_699_;
}
else
{
lean_object* v_reuseFailAlloc_701_; 
v_reuseFailAlloc_701_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_701_, 0, v_key_690_);
lean_ctor_set(v_reuseFailAlloc_701_, 1, v_value_691_);
lean_ctor_set(v_reuseFailAlloc_701_, 2, v___x_698_);
v___x_700_ = v_reuseFailAlloc_701_;
goto v_reusejp_699_;
}
v_reusejp_699_:
{
return v___x_700_;
}
}
else
{
lean_object* v___x_703_; 
lean_dec(v_value_691_);
lean_dec(v_key_690_);
if (v_isShared_695_ == 0)
{
lean_ctor_set(v___x_694_, 1, v_b_688_);
lean_ctor_set(v___x_694_, 0, v_a_687_);
v___x_703_ = v___x_694_;
goto v_reusejp_702_;
}
else
{
lean_object* v_reuseFailAlloc_704_; 
v_reuseFailAlloc_704_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_704_, 0, v_a_687_);
lean_ctor_set(v_reuseFailAlloc_704_, 1, v_b_688_);
lean_ctor_set(v_reuseFailAlloc_704_, 2, v_tail_692_);
v___x_703_ = v_reuseFailAlloc_704_;
goto v_reusejp_702_;
}
v_reusejp_702_:
{
return v___x_703_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1_spec__3_spec__4_spec__5___redArg(lean_object* v_x_714_, lean_object* v_x_715_){
_start:
{
if (lean_obj_tag(v_x_715_) == 0)
{
return v_x_714_;
}
else
{
lean_object* v_key_716_; lean_object* v_value_717_; lean_object* v_tail_718_; lean_object* v___x_720_; uint8_t v_isShared_721_; uint8_t v_isSharedCheck_748_; 
v_key_716_ = lean_ctor_get(v_x_715_, 0);
v_value_717_ = lean_ctor_get(v_x_715_, 1);
v_tail_718_ = lean_ctor_get(v_x_715_, 2);
v_isSharedCheck_748_ = !lean_is_exclusive(v_x_715_);
if (v_isSharedCheck_748_ == 0)
{
v___x_720_ = v_x_715_;
v_isShared_721_ = v_isSharedCheck_748_;
goto v_resetjp_719_;
}
else
{
lean_inc(v_tail_718_);
lean_inc(v_value_717_);
lean_inc(v_key_716_);
lean_dec(v_x_715_);
v___x_720_ = lean_box(0);
v_isShared_721_ = v_isSharedCheck_748_;
goto v_resetjp_719_;
}
v_resetjp_719_:
{
lean_object* v_fst_722_; lean_object* v_snd_723_; lean_object* v___x_724_; size_t v___x_725_; size_t v___x_726_; size_t v___x_727_; uint64_t v___x_728_; uint64_t v___x_729_; uint64_t v___x_730_; uint64_t v___x_731_; uint64_t v___x_732_; uint64_t v_fold_733_; uint64_t v___x_734_; uint64_t v___x_735_; uint64_t v___x_736_; size_t v___x_737_; size_t v___x_738_; size_t v___x_739_; size_t v___x_740_; size_t v___x_741_; lean_object* v___x_742_; lean_object* v___x_744_; 
v_fst_722_ = lean_ctor_get(v_key_716_, 0);
v_snd_723_ = lean_ctor_get(v_key_716_, 1);
v___x_724_ = lean_array_get_size(v_x_714_);
v___x_725_ = lean_ptr_addr(v_fst_722_);
v___x_726_ = ((size_t)3ULL);
v___x_727_ = lean_usize_shift_right(v___x_725_, v___x_726_);
v___x_728_ = lean_usize_to_uint64(v___x_727_);
v___x_729_ = lean_uint64_of_nat(v_snd_723_);
v___x_730_ = lean_uint64_mix_hash(v___x_728_, v___x_729_);
v___x_731_ = 32ULL;
v___x_732_ = lean_uint64_shift_right(v___x_730_, v___x_731_);
v_fold_733_ = lean_uint64_xor(v___x_730_, v___x_732_);
v___x_734_ = 16ULL;
v___x_735_ = lean_uint64_shift_right(v_fold_733_, v___x_734_);
v___x_736_ = lean_uint64_xor(v_fold_733_, v___x_735_);
v___x_737_ = lean_uint64_to_usize(v___x_736_);
v___x_738_ = lean_usize_of_nat(v___x_724_);
v___x_739_ = ((size_t)1ULL);
v___x_740_ = lean_usize_sub(v___x_738_, v___x_739_);
v___x_741_ = lean_usize_land(v___x_737_, v___x_740_);
v___x_742_ = lean_array_uget_borrowed(v_x_714_, v___x_741_);
lean_inc(v___x_742_);
if (v_isShared_721_ == 0)
{
lean_ctor_set(v___x_720_, 2, v___x_742_);
v___x_744_ = v___x_720_;
goto v_reusejp_743_;
}
else
{
lean_object* v_reuseFailAlloc_747_; 
v_reuseFailAlloc_747_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_747_, 0, v_key_716_);
lean_ctor_set(v_reuseFailAlloc_747_, 1, v_value_717_);
lean_ctor_set(v_reuseFailAlloc_747_, 2, v___x_742_);
v___x_744_ = v_reuseFailAlloc_747_;
goto v_reusejp_743_;
}
v_reusejp_743_:
{
lean_object* v___x_745_; 
v___x_745_ = lean_array_uset(v_x_714_, v___x_741_, v___x_744_);
v_x_714_ = v___x_745_;
v_x_715_ = v_tail_718_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1_spec__3_spec__4___redArg(lean_object* v_i_749_, lean_object* v_source_750_, lean_object* v_target_751_){
_start:
{
lean_object* v___x_752_; uint8_t v___x_753_; 
v___x_752_ = lean_array_get_size(v_source_750_);
v___x_753_ = lean_nat_dec_lt(v_i_749_, v___x_752_);
if (v___x_753_ == 0)
{
lean_dec_ref(v_source_750_);
lean_dec(v_i_749_);
return v_target_751_;
}
else
{
lean_object* v_es_754_; lean_object* v___x_755_; lean_object* v_source_756_; lean_object* v_target_757_; lean_object* v___x_758_; lean_object* v___x_759_; 
v_es_754_ = lean_array_fget(v_source_750_, v_i_749_);
v___x_755_ = lean_box(0);
v_source_756_ = lean_array_fset(v_source_750_, v_i_749_, v___x_755_);
v_target_757_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1_spec__3_spec__4_spec__5___redArg(v_target_751_, v_es_754_);
v___x_758_ = lean_unsigned_to_nat(1u);
v___x_759_ = lean_nat_add(v_i_749_, v___x_758_);
lean_dec(v_i_749_);
v_i_749_ = v___x_759_;
v_source_750_ = v_source_756_;
v_target_751_ = v_target_757_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1_spec__3___redArg(lean_object* v_data_761_){
_start:
{
lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v_nbuckets_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; 
v___x_762_ = lean_array_get_size(v_data_761_);
v___x_763_ = lean_unsigned_to_nat(2u);
v_nbuckets_764_ = lean_nat_mul(v___x_762_, v___x_763_);
v___x_765_ = lean_unsigned_to_nat(0u);
v___x_766_ = lean_box(0);
v___x_767_ = lean_mk_array(v_nbuckets_764_, v___x_766_);
v___x_768_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1_spec__3_spec__4___redArg(v___x_765_, v_data_761_, v___x_767_);
return v___x_768_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1___redArg(lean_object* v_m_769_, lean_object* v_a_770_, lean_object* v_b_771_){
_start:
{
lean_object* v_size_772_; lean_object* v_buckets_773_; lean_object* v___x_775_; uint8_t v_isShared_776_; uint8_t v_isSharedCheck_823_; 
v_size_772_ = lean_ctor_get(v_m_769_, 0);
v_buckets_773_ = lean_ctor_get(v_m_769_, 1);
v_isSharedCheck_823_ = !lean_is_exclusive(v_m_769_);
if (v_isSharedCheck_823_ == 0)
{
v___x_775_ = v_m_769_;
v_isShared_776_ = v_isSharedCheck_823_;
goto v_resetjp_774_;
}
else
{
lean_inc(v_buckets_773_);
lean_inc(v_size_772_);
lean_dec(v_m_769_);
v___x_775_ = lean_box(0);
v_isShared_776_ = v_isSharedCheck_823_;
goto v_resetjp_774_;
}
v_resetjp_774_:
{
lean_object* v_fst_777_; lean_object* v_snd_778_; lean_object* v___x_779_; size_t v___x_780_; size_t v___x_781_; size_t v___x_782_; uint64_t v___x_783_; uint64_t v___x_784_; uint64_t v___x_785_; uint64_t v___x_786_; uint64_t v___x_787_; uint64_t v_fold_788_; uint64_t v___x_789_; uint64_t v___x_790_; uint64_t v___x_791_; size_t v___x_792_; size_t v___x_793_; size_t v___x_794_; size_t v___x_795_; size_t v___x_796_; lean_object* v_bkt_797_; uint8_t v___x_798_; 
v_fst_777_ = lean_ctor_get(v_a_770_, 0);
v_snd_778_ = lean_ctor_get(v_a_770_, 1);
v___x_779_ = lean_array_get_size(v_buckets_773_);
v___x_780_ = lean_ptr_addr(v_fst_777_);
v___x_781_ = ((size_t)3ULL);
v___x_782_ = lean_usize_shift_right(v___x_780_, v___x_781_);
v___x_783_ = lean_usize_to_uint64(v___x_782_);
v___x_784_ = lean_uint64_of_nat(v_snd_778_);
v___x_785_ = lean_uint64_mix_hash(v___x_783_, v___x_784_);
v___x_786_ = 32ULL;
v___x_787_ = lean_uint64_shift_right(v___x_785_, v___x_786_);
v_fold_788_ = lean_uint64_xor(v___x_785_, v___x_787_);
v___x_789_ = 16ULL;
v___x_790_ = lean_uint64_shift_right(v_fold_788_, v___x_789_);
v___x_791_ = lean_uint64_xor(v_fold_788_, v___x_790_);
v___x_792_ = lean_uint64_to_usize(v___x_791_);
v___x_793_ = lean_usize_of_nat(v___x_779_);
v___x_794_ = ((size_t)1ULL);
v___x_795_ = lean_usize_sub(v___x_793_, v___x_794_);
v___x_796_ = lean_usize_land(v___x_792_, v___x_795_);
v_bkt_797_ = lean_array_uget_borrowed(v_buckets_773_, v___x_796_);
v___x_798_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1_spec__2___redArg(v_a_770_, v_bkt_797_);
if (v___x_798_ == 0)
{
lean_object* v___x_799_; lean_object* v_size_x27_800_; lean_object* v___x_801_; lean_object* v_buckets_x27_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; uint8_t v___x_808_; 
v___x_799_ = lean_unsigned_to_nat(1u);
v_size_x27_800_ = lean_nat_add(v_size_772_, v___x_799_);
lean_dec(v_size_772_);
lean_inc(v_bkt_797_);
v___x_801_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_801_, 0, v_a_770_);
lean_ctor_set(v___x_801_, 1, v_b_771_);
lean_ctor_set(v___x_801_, 2, v_bkt_797_);
v_buckets_x27_802_ = lean_array_uset(v_buckets_773_, v___x_796_, v___x_801_);
v___x_803_ = lean_unsigned_to_nat(4u);
v___x_804_ = lean_nat_mul(v_size_x27_800_, v___x_803_);
v___x_805_ = lean_unsigned_to_nat(3u);
v___x_806_ = lean_nat_div(v___x_804_, v___x_805_);
lean_dec(v___x_804_);
v___x_807_ = lean_array_get_size(v_buckets_x27_802_);
v___x_808_ = lean_nat_dec_le(v___x_806_, v___x_807_);
lean_dec(v___x_806_);
if (v___x_808_ == 0)
{
lean_object* v_val_809_; lean_object* v___x_811_; 
v_val_809_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1_spec__3___redArg(v_buckets_x27_802_);
if (v_isShared_776_ == 0)
{
lean_ctor_set(v___x_775_, 1, v_val_809_);
lean_ctor_set(v___x_775_, 0, v_size_x27_800_);
v___x_811_ = v___x_775_;
goto v_reusejp_810_;
}
else
{
lean_object* v_reuseFailAlloc_812_; 
v_reuseFailAlloc_812_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_812_, 0, v_size_x27_800_);
lean_ctor_set(v_reuseFailAlloc_812_, 1, v_val_809_);
v___x_811_ = v_reuseFailAlloc_812_;
goto v_reusejp_810_;
}
v_reusejp_810_:
{
return v___x_811_;
}
}
else
{
lean_object* v___x_814_; 
if (v_isShared_776_ == 0)
{
lean_ctor_set(v___x_775_, 1, v_buckets_x27_802_);
lean_ctor_set(v___x_775_, 0, v_size_x27_800_);
v___x_814_ = v___x_775_;
goto v_reusejp_813_;
}
else
{
lean_object* v_reuseFailAlloc_815_; 
v_reuseFailAlloc_815_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_815_, 0, v_size_x27_800_);
lean_ctor_set(v_reuseFailAlloc_815_, 1, v_buckets_x27_802_);
v___x_814_ = v_reuseFailAlloc_815_;
goto v_reusejp_813_;
}
v_reusejp_813_:
{
return v___x_814_;
}
}
}
else
{
lean_object* v___x_816_; lean_object* v_buckets_x27_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_821_; 
lean_inc(v_bkt_797_);
v___x_816_ = lean_box(0);
v_buckets_x27_817_ = lean_array_uset(v_buckets_773_, v___x_796_, v___x_816_);
v___x_818_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1_spec__4___redArg(v_a_770_, v_b_771_, v_bkt_797_);
v___x_819_ = lean_array_uset(v_buckets_x27_817_, v___x_796_, v___x_818_);
if (v_isShared_776_ == 0)
{
lean_ctor_set(v___x_775_, 1, v___x_819_);
v___x_821_ = v___x_775_;
goto v_reusejp_820_;
}
else
{
lean_object* v_reuseFailAlloc_822_; 
v_reuseFailAlloc_822_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_822_, 0, v_size_772_);
lean_ctor_set(v_reuseFailAlloc_822_, 1, v___x_819_);
v___x_821_ = v_reuseFailAlloc_822_;
goto v_reusejp_820_;
}
v_reusejp_820_:
{
return v___x_821_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__0_spec__0___redArg(lean_object* v_a_824_, lean_object* v_x_825_){
_start:
{
if (lean_obj_tag(v_x_825_) == 0)
{
lean_object* v___x_826_; 
v___x_826_ = lean_box(0);
return v___x_826_;
}
else
{
lean_object* v_key_827_; lean_object* v_value_828_; lean_object* v_tail_829_; uint8_t v___y_831_; lean_object* v_fst_834_; lean_object* v_snd_835_; lean_object* v_fst_836_; lean_object* v_snd_837_; size_t v___x_838_; size_t v___x_839_; uint8_t v___x_840_; 
v_key_827_ = lean_ctor_get(v_x_825_, 0);
v_value_828_ = lean_ctor_get(v_x_825_, 1);
v_tail_829_ = lean_ctor_get(v_x_825_, 2);
v_fst_834_ = lean_ctor_get(v_key_827_, 0);
v_snd_835_ = lean_ctor_get(v_key_827_, 1);
v_fst_836_ = lean_ctor_get(v_a_824_, 0);
v_snd_837_ = lean_ctor_get(v_a_824_, 1);
v___x_838_ = lean_ptr_addr(v_fst_834_);
v___x_839_ = lean_ptr_addr(v_fst_836_);
v___x_840_ = lean_usize_dec_eq(v___x_838_, v___x_839_);
if (v___x_840_ == 0)
{
v___y_831_ = v___x_840_;
goto v___jp_830_;
}
else
{
uint8_t v___x_841_; 
v___x_841_ = lean_nat_dec_eq(v_snd_835_, v_snd_837_);
v___y_831_ = v___x_841_;
goto v___jp_830_;
}
v___jp_830_:
{
if (v___y_831_ == 0)
{
v_x_825_ = v_tail_829_;
goto _start;
}
else
{
lean_object* v___x_833_; 
lean_inc(v_value_828_);
v___x_833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_833_, 0, v_value_828_);
return v___x_833_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__0_spec__0___redArg___boxed(lean_object* v_a_842_, lean_object* v_x_843_){
_start:
{
lean_object* v_res_844_; 
v_res_844_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__0_spec__0___redArg(v_a_842_, v_x_843_);
lean_dec(v_x_843_);
lean_dec_ref(v_a_842_);
return v_res_844_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__0___redArg(lean_object* v_m_845_, lean_object* v_a_846_){
_start:
{
lean_object* v_buckets_847_; lean_object* v_fst_848_; lean_object* v_snd_849_; lean_object* v___x_850_; size_t v___x_851_; size_t v___x_852_; size_t v___x_853_; uint64_t v___x_854_; uint64_t v___x_855_; uint64_t v___x_856_; uint64_t v___x_857_; uint64_t v___x_858_; uint64_t v_fold_859_; uint64_t v___x_860_; uint64_t v___x_861_; uint64_t v___x_862_; size_t v___x_863_; size_t v___x_864_; size_t v___x_865_; size_t v___x_866_; size_t v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; 
v_buckets_847_ = lean_ctor_get(v_m_845_, 1);
v_fst_848_ = lean_ctor_get(v_a_846_, 0);
v_snd_849_ = lean_ctor_get(v_a_846_, 1);
v___x_850_ = lean_array_get_size(v_buckets_847_);
v___x_851_ = lean_ptr_addr(v_fst_848_);
v___x_852_ = ((size_t)3ULL);
v___x_853_ = lean_usize_shift_right(v___x_851_, v___x_852_);
v___x_854_ = lean_usize_to_uint64(v___x_853_);
v___x_855_ = lean_uint64_of_nat(v_snd_849_);
v___x_856_ = lean_uint64_mix_hash(v___x_854_, v___x_855_);
v___x_857_ = 32ULL;
v___x_858_ = lean_uint64_shift_right(v___x_856_, v___x_857_);
v_fold_859_ = lean_uint64_xor(v___x_856_, v___x_858_);
v___x_860_ = 16ULL;
v___x_861_ = lean_uint64_shift_right(v_fold_859_, v___x_860_);
v___x_862_ = lean_uint64_xor(v_fold_859_, v___x_861_);
v___x_863_ = lean_uint64_to_usize(v___x_862_);
v___x_864_ = lean_usize_of_nat(v___x_850_);
v___x_865_ = ((size_t)1ULL);
v___x_866_ = lean_usize_sub(v___x_864_, v___x_865_);
v___x_867_ = lean_usize_land(v___x_863_, v___x_866_);
v___x_868_ = lean_array_uget_borrowed(v_buckets_847_, v___x_867_);
v___x_869_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__0_spec__0___redArg(v_a_846_, v___x_868_);
return v___x_869_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__0___redArg___boxed(lean_object* v_m_870_, lean_object* v_a_871_){
_start:
{
lean_object* v_res_872_; 
v_res_872_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__0___redArg(v_m_870_, v_a_871_);
lean_dec_ref(v_a_871_);
lean_dec_ref(v_m_870_);
return v_res_872_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached___redArg(lean_object* v_rhs_873_, lean_object* v_op_874_, lean_object* v_a_875_, lean_object* v_a_876_, lean_object* v_a_877_, lean_object* v_a_878_, lean_object* v_a_879_, lean_object* v_a_880_, lean_object* v_a_881_){
_start:
{
lean_object* v___x_883_; lean_object* v_numConst_884_; lean_object* v_latticeBackwardRuleCache_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v_key_888_; lean_object* v___x_889_; 
v___x_883_ = lean_st_ref_get(v_a_875_);
v_numConst_884_ = lean_ctor_get(v_op_874_, 1);
v_latticeBackwardRuleCache_885_ = lean_ctor_get(v___x_883_, 2);
lean_inc_ref(v_latticeBackwardRuleCache_885_);
lean_dec(v___x_883_);
v___x_886_ = l_Lean_Expr_getAppPrefix(v_rhs_873_, v_numConst_884_);
v___x_887_ = l_Lean_Expr_getAppNumArgs(v_rhs_873_);
v_key_888_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_key_888_, 0, v___x_886_);
lean_ctor_set(v_key_888_, 1, v___x_887_);
v___x_889_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__0___redArg(v_latticeBackwardRuleCache_885_, v_key_888_);
lean_dec_ref(v_latticeBackwardRuleCache_885_);
if (lean_obj_tag(v___x_889_) == 1)
{
lean_object* v_val_890_; lean_object* v___x_892_; uint8_t v_isShared_893_; uint8_t v_isSharedCheck_897_; 
lean_dec_ref_known(v_key_888_, 2);
lean_dec_ref(v_op_874_);
lean_dec_ref(v_rhs_873_);
v_val_890_ = lean_ctor_get(v___x_889_, 0);
v_isSharedCheck_897_ = !lean_is_exclusive(v___x_889_);
if (v_isSharedCheck_897_ == 0)
{
v___x_892_ = v___x_889_;
v_isShared_893_ = v_isSharedCheck_897_;
goto v_resetjp_891_;
}
else
{
lean_inc(v_val_890_);
lean_dec(v___x_889_);
v___x_892_ = lean_box(0);
v_isShared_893_ = v_isSharedCheck_897_;
goto v_resetjp_891_;
}
v_resetjp_891_:
{
lean_object* v___x_895_; 
if (v_isShared_893_ == 0)
{
lean_ctor_set_tag(v___x_892_, 0);
v___x_895_ = v___x_892_;
goto v_reusejp_894_;
}
else
{
lean_object* v_reuseFailAlloc_896_; 
v_reuseFailAlloc_896_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_896_, 0, v_val_890_);
v___x_895_ = v_reuseFailAlloc_896_;
goto v_reusejp_894_;
}
v_reusejp_894_:
{
return v___x_895_;
}
}
}
else
{
lean_object* v___x_898_; 
lean_dec(v___x_889_);
v___x_898_ = l_Lean_Elab_Tactic_VCGen_mkLatticeOpRule(v_rhs_873_, v_op_874_, v_a_876_, v_a_877_, v_a_878_, v_a_879_, v_a_880_, v_a_881_);
if (lean_obj_tag(v___x_898_) == 0)
{
lean_object* v_a_899_; lean_object* v___x_900_; 
v_a_899_ = lean_ctor_get(v___x_898_, 0);
lean_inc(v_a_899_);
lean_dec_ref_known(v___x_898_, 1);
v___x_900_ = l_Lean_Meta_Sym_BackwardRule_shareCommon(v_a_899_, v_a_876_, v_a_877_, v_a_878_, v_a_879_, v_a_880_, v_a_881_);
if (lean_obj_tag(v___x_900_) == 0)
{
lean_object* v_a_901_; lean_object* v___x_903_; uint8_t v_isShared_904_; uint8_t v_isSharedCheck_928_; 
v_a_901_ = lean_ctor_get(v___x_900_, 0);
v_isSharedCheck_928_ = !lean_is_exclusive(v___x_900_);
if (v_isSharedCheck_928_ == 0)
{
v___x_903_ = v___x_900_;
v_isShared_904_ = v_isSharedCheck_928_;
goto v_resetjp_902_;
}
else
{
lean_inc(v_a_901_);
lean_dec(v___x_900_);
v___x_903_ = lean_box(0);
v_isShared_904_ = v_isSharedCheck_928_;
goto v_resetjp_902_;
}
v_resetjp_902_:
{
lean_object* v___x_905_; lean_object* v_specBackwardRuleCache_906_; lean_object* v_splitBackwardRuleCache_907_; lean_object* v_latticeBackwardRuleCache_908_; lean_object* v_frameBackwardRuleCache_909_; lean_object* v_frameDB_910_; lean_object* v_invariants_911_; lean_object* v_vcs_912_; lean_object* v_simpState_913_; lean_object* v_fuel_914_; lean_object* v_inlineHandledInvariants_915_; lean_object* v___x_917_; uint8_t v_isShared_918_; uint8_t v_isSharedCheck_927_; 
v___x_905_ = lean_st_ref_take(v_a_875_);
v_specBackwardRuleCache_906_ = lean_ctor_get(v___x_905_, 0);
v_splitBackwardRuleCache_907_ = lean_ctor_get(v___x_905_, 1);
v_latticeBackwardRuleCache_908_ = lean_ctor_get(v___x_905_, 2);
v_frameBackwardRuleCache_909_ = lean_ctor_get(v___x_905_, 3);
v_frameDB_910_ = lean_ctor_get(v___x_905_, 4);
v_invariants_911_ = lean_ctor_get(v___x_905_, 5);
v_vcs_912_ = lean_ctor_get(v___x_905_, 6);
v_simpState_913_ = lean_ctor_get(v___x_905_, 7);
v_fuel_914_ = lean_ctor_get(v___x_905_, 8);
v_inlineHandledInvariants_915_ = lean_ctor_get(v___x_905_, 9);
v_isSharedCheck_927_ = !lean_is_exclusive(v___x_905_);
if (v_isSharedCheck_927_ == 0)
{
v___x_917_ = v___x_905_;
v_isShared_918_ = v_isSharedCheck_927_;
goto v_resetjp_916_;
}
else
{
lean_inc(v_inlineHandledInvariants_915_);
lean_inc(v_fuel_914_);
lean_inc(v_simpState_913_);
lean_inc(v_vcs_912_);
lean_inc(v_invariants_911_);
lean_inc(v_frameDB_910_);
lean_inc(v_frameBackwardRuleCache_909_);
lean_inc(v_latticeBackwardRuleCache_908_);
lean_inc(v_splitBackwardRuleCache_907_);
lean_inc(v_specBackwardRuleCache_906_);
lean_dec(v___x_905_);
v___x_917_ = lean_box(0);
v_isShared_918_ = v_isSharedCheck_927_;
goto v_resetjp_916_;
}
v_resetjp_916_:
{
lean_object* v___x_919_; lean_object* v___x_921_; 
lean_inc(v_a_901_);
v___x_919_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1___redArg(v_latticeBackwardRuleCache_908_, v_key_888_, v_a_901_);
if (v_isShared_918_ == 0)
{
lean_ctor_set(v___x_917_, 2, v___x_919_);
v___x_921_ = v___x_917_;
goto v_reusejp_920_;
}
else
{
lean_object* v_reuseFailAlloc_926_; 
v_reuseFailAlloc_926_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_926_, 0, v_specBackwardRuleCache_906_);
lean_ctor_set(v_reuseFailAlloc_926_, 1, v_splitBackwardRuleCache_907_);
lean_ctor_set(v_reuseFailAlloc_926_, 2, v___x_919_);
lean_ctor_set(v_reuseFailAlloc_926_, 3, v_frameBackwardRuleCache_909_);
lean_ctor_set(v_reuseFailAlloc_926_, 4, v_frameDB_910_);
lean_ctor_set(v_reuseFailAlloc_926_, 5, v_invariants_911_);
lean_ctor_set(v_reuseFailAlloc_926_, 6, v_vcs_912_);
lean_ctor_set(v_reuseFailAlloc_926_, 7, v_simpState_913_);
lean_ctor_set(v_reuseFailAlloc_926_, 8, v_fuel_914_);
lean_ctor_set(v_reuseFailAlloc_926_, 9, v_inlineHandledInvariants_915_);
v___x_921_ = v_reuseFailAlloc_926_;
goto v_reusejp_920_;
}
v_reusejp_920_:
{
lean_object* v___x_922_; lean_object* v___x_924_; 
v___x_922_ = lean_st_ref_put(v_a_875_, v___x_921_);
if (v_isShared_904_ == 0)
{
v___x_924_ = v___x_903_;
goto v_reusejp_923_;
}
else
{
lean_object* v_reuseFailAlloc_925_; 
v_reuseFailAlloc_925_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_925_, 0, v_a_901_);
v___x_924_ = v_reuseFailAlloc_925_;
goto v_reusejp_923_;
}
v_reusejp_923_:
{
return v___x_924_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_key_888_, 2);
return v___x_900_;
}
}
else
{
lean_dec_ref_known(v_key_888_, 2);
return v___x_898_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached___redArg___boxed(lean_object* v_rhs_929_, lean_object* v_op_930_, lean_object* v_a_931_, lean_object* v_a_932_, lean_object* v_a_933_, lean_object* v_a_934_, lean_object* v_a_935_, lean_object* v_a_936_, lean_object* v_a_937_, lean_object* v_a_938_){
_start:
{
lean_object* v_res_939_; 
v_res_939_ = l_Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached___redArg(v_rhs_929_, v_op_930_, v_a_931_, v_a_932_, v_a_933_, v_a_934_, v_a_935_, v_a_936_, v_a_937_);
lean_dec(v_a_937_);
lean_dec_ref(v_a_936_);
lean_dec(v_a_935_);
lean_dec_ref(v_a_934_);
lean_dec(v_a_933_);
lean_dec_ref(v_a_932_);
lean_dec(v_a_931_);
return v_res_939_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached(lean_object* v_rhs_940_, lean_object* v_op_941_, lean_object* v_a_942_, lean_object* v_a_943_, lean_object* v_a_944_, lean_object* v_a_945_, lean_object* v_a_946_, lean_object* v_a_947_, lean_object* v_a_948_, lean_object* v_a_949_, lean_object* v_a_950_, lean_object* v_a_951_, lean_object* v_a_952_){
_start:
{
lean_object* v___x_954_; 
v___x_954_ = l_Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached___redArg(v_rhs_940_, v_op_941_, v_a_943_, v_a_947_, v_a_948_, v_a_949_, v_a_950_, v_a_951_, v_a_952_);
return v___x_954_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached___boxed(lean_object* v_rhs_955_, lean_object* v_op_956_, lean_object* v_a_957_, lean_object* v_a_958_, lean_object* v_a_959_, lean_object* v_a_960_, lean_object* v_a_961_, lean_object* v_a_962_, lean_object* v_a_963_, lean_object* v_a_964_, lean_object* v_a_965_, lean_object* v_a_966_, lean_object* v_a_967_, lean_object* v_a_968_){
_start:
{
lean_object* v_res_969_; 
v_res_969_ = l_Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached(v_rhs_955_, v_op_956_, v_a_957_, v_a_958_, v_a_959_, v_a_960_, v_a_961_, v_a_962_, v_a_963_, v_a_964_, v_a_965_, v_a_966_, v_a_967_);
lean_dec(v_a_967_);
lean_dec_ref(v_a_966_);
lean_dec(v_a_965_);
lean_dec_ref(v_a_964_);
lean_dec(v_a_963_);
lean_dec_ref(v_a_962_);
lean_dec(v_a_961_);
lean_dec_ref(v_a_960_);
lean_dec(v_a_959_);
lean_dec(v_a_958_);
lean_dec_ref(v_a_957_);
return v_res_969_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__0(lean_object* v_00_u03b2_970_, lean_object* v_m_971_, lean_object* v_a_972_){
_start:
{
lean_object* v___x_973_; 
v___x_973_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__0___redArg(v_m_971_, v_a_972_);
return v___x_973_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__0___boxed(lean_object* v_00_u03b2_974_, lean_object* v_m_975_, lean_object* v_a_976_){
_start:
{
lean_object* v_res_977_; 
v_res_977_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__0(v_00_u03b2_974_, v_m_975_, v_a_976_);
lean_dec_ref(v_a_976_);
lean_dec_ref(v_m_975_);
return v_res_977_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1(lean_object* v_00_u03b2_978_, lean_object* v_m_979_, lean_object* v_a_980_, lean_object* v_b_981_){
_start:
{
lean_object* v___x_982_; 
v___x_982_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1___redArg(v_m_979_, v_a_980_, v_b_981_);
return v___x_982_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__0_spec__0(lean_object* v_00_u03b2_983_, lean_object* v_a_984_, lean_object* v_x_985_){
_start:
{
lean_object* v___x_986_; 
v___x_986_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__0_spec__0___redArg(v_a_984_, v_x_985_);
return v___x_986_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__0_spec__0___boxed(lean_object* v_00_u03b2_987_, lean_object* v_a_988_, lean_object* v_x_989_){
_start:
{
lean_object* v_res_990_; 
v_res_990_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__0_spec__0(v_00_u03b2_987_, v_a_988_, v_x_989_);
lean_dec(v_x_989_);
lean_dec_ref(v_a_988_);
return v_res_990_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1_spec__2(lean_object* v_00_u03b2_991_, lean_object* v_a_992_, lean_object* v_x_993_){
_start:
{
uint8_t v___x_994_; 
v___x_994_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1_spec__2___redArg(v_a_992_, v_x_993_);
return v___x_994_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1_spec__2___boxed(lean_object* v_00_u03b2_995_, lean_object* v_a_996_, lean_object* v_x_997_){
_start:
{
uint8_t v_res_998_; lean_object* v_r_999_; 
v_res_998_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1_spec__2(v_00_u03b2_995_, v_a_996_, v_x_997_);
lean_dec(v_x_997_);
lean_dec_ref(v_a_996_);
v_r_999_ = lean_box(v_res_998_);
return v_r_999_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1_spec__3(lean_object* v_00_u03b2_1000_, lean_object* v_data_1001_){
_start:
{
lean_object* v___x_1002_; 
v___x_1002_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1_spec__3___redArg(v_data_1001_);
return v___x_1002_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1_spec__4(lean_object* v_00_u03b2_1003_, lean_object* v_a_1004_, lean_object* v_b_1005_, lean_object* v_x_1006_){
_start:
{
lean_object* v___x_1007_; 
v___x_1007_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1_spec__4___redArg(v_a_1004_, v_b_1005_, v_x_1006_);
return v___x_1007_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1_spec__3_spec__4(lean_object* v_00_u03b2_1008_, lean_object* v_i_1009_, lean_object* v_source_1010_, lean_object* v_target_1011_){
_start:
{
lean_object* v___x_1012_; 
v___x_1012_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1_spec__3_spec__4___redArg(v_i_1009_, v_source_1010_, v_target_1011_);
return v___x_1012_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1_spec__3_spec__4_spec__5(lean_object* v_00_u03b2_1013_, lean_object* v_x_1014_, lean_object* v_x_1015_){
_start:
{
lean_object* v___x_1016_; 
v___x_1016_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1_spec__3_spec__4_spec__5___redArg(v_x_1014_, v_x_1015_);
return v___x_1016_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_mkFrameBackwardRuleCached___redArg(lean_object* v_fp_1017_, lean_object* v_info_1018_, lean_object* v_a_1019_, lean_object* v_a_1020_, lean_object* v_a_1021_, lean_object* v_a_1022_, lean_object* v_a_1023_, lean_object* v_a_1024_, lean_object* v_a_1025_){
_start:
{
lean_object* v___x_1027_; lean_object* v_excessArgs_1028_; lean_object* v_frameBackwardRuleCache_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v_key_1032_; lean_object* v___x_1033_; 
v___x_1027_ = lean_st_ref_get(v_a_1019_);
v_excessArgs_1028_ = lean_ctor_get(v_info_1018_, 2);
v_frameBackwardRuleCache_1029_ = lean_ctor_get(v___x_1027_, 3);
lean_inc_ref(v_frameBackwardRuleCache_1029_);
lean_dec(v___x_1027_);
v___x_1030_ = l_Lean_Elab_Tactic_VCGen_WPApp_instWP(v_info_1018_);
v___x_1031_ = lean_array_get_size(v_excessArgs_1028_);
v_key_1032_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_key_1032_, 0, v___x_1030_);
lean_ctor_set(v_key_1032_, 1, v___x_1031_);
v___x_1033_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__0___redArg(v_frameBackwardRuleCache_1029_, v_key_1032_);
lean_dec_ref(v_frameBackwardRuleCache_1029_);
if (lean_obj_tag(v___x_1033_) == 1)
{
lean_object* v_val_1034_; lean_object* v___x_1036_; uint8_t v_isShared_1037_; uint8_t v_isSharedCheck_1041_; 
lean_dec_ref_known(v_key_1032_, 2);
lean_dec_ref(v_info_1018_);
lean_dec_ref(v_fp_1017_);
v_val_1034_ = lean_ctor_get(v___x_1033_, 0);
v_isSharedCheck_1041_ = !lean_is_exclusive(v___x_1033_);
if (v_isSharedCheck_1041_ == 0)
{
v___x_1036_ = v___x_1033_;
v_isShared_1037_ = v_isSharedCheck_1041_;
goto v_resetjp_1035_;
}
else
{
lean_inc(v_val_1034_);
lean_dec(v___x_1033_);
v___x_1036_ = lean_box(0);
v_isShared_1037_ = v_isSharedCheck_1041_;
goto v_resetjp_1035_;
}
v_resetjp_1035_:
{
lean_object* v___x_1039_; 
if (v_isShared_1037_ == 0)
{
lean_ctor_set_tag(v___x_1036_, 0);
v___x_1039_ = v___x_1036_;
goto v_reusejp_1038_;
}
else
{
lean_object* v_reuseFailAlloc_1040_; 
v_reuseFailAlloc_1040_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1040_, 0, v_val_1034_);
v___x_1039_ = v_reuseFailAlloc_1040_;
goto v_reusejp_1038_;
}
v_reusejp_1038_:
{
return v___x_1039_;
}
}
}
else
{
lean_object* v___x_1042_; 
lean_dec(v___x_1033_);
v___x_1042_ = l_Lean_Elab_Tactic_VCGen_mkFrameBackwardRule(v_fp_1017_, v_info_1018_, v_a_1022_, v_a_1023_, v_a_1024_, v_a_1025_);
if (lean_obj_tag(v___x_1042_) == 0)
{
lean_object* v_a_1043_; lean_object* v_rule_1044_; lean_object* v_splitVCIdx_1045_; lean_object* v_frameIdx_1046_; lean_object* v___x_1048_; uint8_t v_isShared_1049_; uint8_t v_isSharedCheck_1090_; 
v_a_1043_ = lean_ctor_get(v___x_1042_, 0);
lean_inc(v_a_1043_);
lean_dec_ref_known(v___x_1042_, 1);
v_rule_1044_ = lean_ctor_get(v_a_1043_, 0);
v_splitVCIdx_1045_ = lean_ctor_get(v_a_1043_, 1);
v_frameIdx_1046_ = lean_ctor_get(v_a_1043_, 2);
v_isSharedCheck_1090_ = !lean_is_exclusive(v_a_1043_);
if (v_isSharedCheck_1090_ == 0)
{
v___x_1048_ = v_a_1043_;
v_isShared_1049_ = v_isSharedCheck_1090_;
goto v_resetjp_1047_;
}
else
{
lean_inc(v_frameIdx_1046_);
lean_inc(v_splitVCIdx_1045_);
lean_inc(v_rule_1044_);
lean_dec(v_a_1043_);
v___x_1048_ = lean_box(0);
v_isShared_1049_ = v_isSharedCheck_1090_;
goto v_resetjp_1047_;
}
v_resetjp_1047_:
{
lean_object* v___x_1050_; 
v___x_1050_ = l_Lean_Meta_Sym_BackwardRule_shareCommon(v_rule_1044_, v_a_1020_, v_a_1021_, v_a_1022_, v_a_1023_, v_a_1024_, v_a_1025_);
if (lean_obj_tag(v___x_1050_) == 0)
{
lean_object* v_a_1051_; lean_object* v___x_1053_; uint8_t v_isShared_1054_; uint8_t v_isSharedCheck_1081_; 
v_a_1051_ = lean_ctor_get(v___x_1050_, 0);
v_isSharedCheck_1081_ = !lean_is_exclusive(v___x_1050_);
if (v_isSharedCheck_1081_ == 0)
{
v___x_1053_ = v___x_1050_;
v_isShared_1054_ = v_isSharedCheck_1081_;
goto v_resetjp_1052_;
}
else
{
lean_inc(v_a_1051_);
lean_dec(v___x_1050_);
v___x_1053_ = lean_box(0);
v_isShared_1054_ = v_isSharedCheck_1081_;
goto v_resetjp_1052_;
}
v_resetjp_1052_:
{
lean_object* v___x_1055_; lean_object* v_specBackwardRuleCache_1056_; lean_object* v_splitBackwardRuleCache_1057_; lean_object* v_latticeBackwardRuleCache_1058_; lean_object* v_frameBackwardRuleCache_1059_; lean_object* v_frameDB_1060_; lean_object* v_invariants_1061_; lean_object* v_vcs_1062_; lean_object* v_simpState_1063_; lean_object* v_fuel_1064_; lean_object* v_inlineHandledInvariants_1065_; lean_object* v___x_1067_; uint8_t v_isShared_1068_; uint8_t v_isSharedCheck_1080_; 
v___x_1055_ = lean_st_ref_take(v_a_1019_);
v_specBackwardRuleCache_1056_ = lean_ctor_get(v___x_1055_, 0);
v_splitBackwardRuleCache_1057_ = lean_ctor_get(v___x_1055_, 1);
v_latticeBackwardRuleCache_1058_ = lean_ctor_get(v___x_1055_, 2);
v_frameBackwardRuleCache_1059_ = lean_ctor_get(v___x_1055_, 3);
v_frameDB_1060_ = lean_ctor_get(v___x_1055_, 4);
v_invariants_1061_ = lean_ctor_get(v___x_1055_, 5);
v_vcs_1062_ = lean_ctor_get(v___x_1055_, 6);
v_simpState_1063_ = lean_ctor_get(v___x_1055_, 7);
v_fuel_1064_ = lean_ctor_get(v___x_1055_, 8);
v_inlineHandledInvariants_1065_ = lean_ctor_get(v___x_1055_, 9);
v_isSharedCheck_1080_ = !lean_is_exclusive(v___x_1055_);
if (v_isSharedCheck_1080_ == 0)
{
v___x_1067_ = v___x_1055_;
v_isShared_1068_ = v_isSharedCheck_1080_;
goto v_resetjp_1066_;
}
else
{
lean_inc(v_inlineHandledInvariants_1065_);
lean_inc(v_fuel_1064_);
lean_inc(v_simpState_1063_);
lean_inc(v_vcs_1062_);
lean_inc(v_invariants_1061_);
lean_inc(v_frameDB_1060_);
lean_inc(v_frameBackwardRuleCache_1059_);
lean_inc(v_latticeBackwardRuleCache_1058_);
lean_inc(v_splitBackwardRuleCache_1057_);
lean_inc(v_specBackwardRuleCache_1056_);
lean_dec(v___x_1055_);
v___x_1067_ = lean_box(0);
v_isShared_1068_ = v_isSharedCheck_1080_;
goto v_resetjp_1066_;
}
v_resetjp_1066_:
{
lean_object* v___x_1070_; 
if (v_isShared_1049_ == 0)
{
lean_ctor_set(v___x_1048_, 0, v_a_1051_);
v___x_1070_ = v___x_1048_;
goto v_reusejp_1069_;
}
else
{
lean_object* v_reuseFailAlloc_1079_; 
v_reuseFailAlloc_1079_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1079_, 0, v_a_1051_);
lean_ctor_set(v_reuseFailAlloc_1079_, 1, v_splitVCIdx_1045_);
lean_ctor_set(v_reuseFailAlloc_1079_, 2, v_frameIdx_1046_);
v___x_1070_ = v_reuseFailAlloc_1079_;
goto v_reusejp_1069_;
}
v_reusejp_1069_:
{
lean_object* v___x_1071_; lean_object* v___x_1073_; 
lean_inc_ref(v___x_1070_);
v___x_1071_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1___redArg(v_frameBackwardRuleCache_1059_, v_key_1032_, v___x_1070_);
if (v_isShared_1068_ == 0)
{
lean_ctor_set(v___x_1067_, 3, v___x_1071_);
v___x_1073_ = v___x_1067_;
goto v_reusejp_1072_;
}
else
{
lean_object* v_reuseFailAlloc_1078_; 
v_reuseFailAlloc_1078_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1078_, 0, v_specBackwardRuleCache_1056_);
lean_ctor_set(v_reuseFailAlloc_1078_, 1, v_splitBackwardRuleCache_1057_);
lean_ctor_set(v_reuseFailAlloc_1078_, 2, v_latticeBackwardRuleCache_1058_);
lean_ctor_set(v_reuseFailAlloc_1078_, 3, v___x_1071_);
lean_ctor_set(v_reuseFailAlloc_1078_, 4, v_frameDB_1060_);
lean_ctor_set(v_reuseFailAlloc_1078_, 5, v_invariants_1061_);
lean_ctor_set(v_reuseFailAlloc_1078_, 6, v_vcs_1062_);
lean_ctor_set(v_reuseFailAlloc_1078_, 7, v_simpState_1063_);
lean_ctor_set(v_reuseFailAlloc_1078_, 8, v_fuel_1064_);
lean_ctor_set(v_reuseFailAlloc_1078_, 9, v_inlineHandledInvariants_1065_);
v___x_1073_ = v_reuseFailAlloc_1078_;
goto v_reusejp_1072_;
}
v_reusejp_1072_:
{
lean_object* v___x_1074_; lean_object* v___x_1076_; 
v___x_1074_ = lean_st_ref_put(v_a_1019_, v___x_1073_);
if (v_isShared_1054_ == 0)
{
lean_ctor_set(v___x_1053_, 0, v___x_1070_);
v___x_1076_ = v___x_1053_;
goto v_reusejp_1075_;
}
else
{
lean_object* v_reuseFailAlloc_1077_; 
v_reuseFailAlloc_1077_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1077_, 0, v___x_1070_);
v___x_1076_ = v_reuseFailAlloc_1077_;
goto v_reusejp_1075_;
}
v_reusejp_1075_:
{
return v___x_1076_;
}
}
}
}
}
}
else
{
lean_object* v_a_1082_; lean_object* v___x_1084_; uint8_t v_isShared_1085_; uint8_t v_isSharedCheck_1089_; 
lean_del_object(v___x_1048_);
lean_dec(v_frameIdx_1046_);
lean_dec(v_splitVCIdx_1045_);
lean_dec_ref_known(v_key_1032_, 2);
v_a_1082_ = lean_ctor_get(v___x_1050_, 0);
v_isSharedCheck_1089_ = !lean_is_exclusive(v___x_1050_);
if (v_isSharedCheck_1089_ == 0)
{
v___x_1084_ = v___x_1050_;
v_isShared_1085_ = v_isSharedCheck_1089_;
goto v_resetjp_1083_;
}
else
{
lean_inc(v_a_1082_);
lean_dec(v___x_1050_);
v___x_1084_ = lean_box(0);
v_isShared_1085_ = v_isSharedCheck_1089_;
goto v_resetjp_1083_;
}
v_resetjp_1083_:
{
lean_object* v___x_1087_; 
if (v_isShared_1085_ == 0)
{
v___x_1087_ = v___x_1084_;
goto v_reusejp_1086_;
}
else
{
lean_object* v_reuseFailAlloc_1088_; 
v_reuseFailAlloc_1088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1088_, 0, v_a_1082_);
v___x_1087_ = v_reuseFailAlloc_1088_;
goto v_reusejp_1086_;
}
v_reusejp_1086_:
{
return v___x_1087_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_key_1032_, 2);
return v___x_1042_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_mkFrameBackwardRuleCached___redArg___boxed(lean_object* v_fp_1091_, lean_object* v_info_1092_, lean_object* v_a_1093_, lean_object* v_a_1094_, lean_object* v_a_1095_, lean_object* v_a_1096_, lean_object* v_a_1097_, lean_object* v_a_1098_, lean_object* v_a_1099_, lean_object* v_a_1100_){
_start:
{
lean_object* v_res_1101_; 
v_res_1101_ = l_Lean_Elab_Tactic_VCGen_mkFrameBackwardRuleCached___redArg(v_fp_1091_, v_info_1092_, v_a_1093_, v_a_1094_, v_a_1095_, v_a_1096_, v_a_1097_, v_a_1098_, v_a_1099_);
lean_dec(v_a_1099_);
lean_dec_ref(v_a_1098_);
lean_dec(v_a_1097_);
lean_dec_ref(v_a_1096_);
lean_dec(v_a_1095_);
lean_dec_ref(v_a_1094_);
lean_dec(v_a_1093_);
return v_res_1101_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_mkFrameBackwardRuleCached(lean_object* v_fp_1102_, lean_object* v_info_1103_, lean_object* v_a_1104_, lean_object* v_a_1105_, lean_object* v_a_1106_, lean_object* v_a_1107_, lean_object* v_a_1108_, lean_object* v_a_1109_, lean_object* v_a_1110_, lean_object* v_a_1111_, lean_object* v_a_1112_, lean_object* v_a_1113_, lean_object* v_a_1114_){
_start:
{
lean_object* v___x_1116_; 
v___x_1116_ = l_Lean_Elab_Tactic_VCGen_mkFrameBackwardRuleCached___redArg(v_fp_1102_, v_info_1103_, v_a_1105_, v_a_1109_, v_a_1110_, v_a_1111_, v_a_1112_, v_a_1113_, v_a_1114_);
return v___x_1116_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_mkFrameBackwardRuleCached___boxed(lean_object* v_fp_1117_, lean_object* v_info_1118_, lean_object* v_a_1119_, lean_object* v_a_1120_, lean_object* v_a_1121_, lean_object* v_a_1122_, lean_object* v_a_1123_, lean_object* v_a_1124_, lean_object* v_a_1125_, lean_object* v_a_1126_, lean_object* v_a_1127_, lean_object* v_a_1128_, lean_object* v_a_1129_, lean_object* v_a_1130_){
_start:
{
lean_object* v_res_1131_; 
v_res_1131_ = l_Lean_Elab_Tactic_VCGen_mkFrameBackwardRuleCached(v_fp_1117_, v_info_1118_, v_a_1119_, v_a_1120_, v_a_1121_, v_a_1122_, v_a_1123_, v_a_1124_, v_a_1125_, v_a_1126_, v_a_1127_, v_a_1128_, v_a_1129_);
lean_dec(v_a_1129_);
lean_dec_ref(v_a_1128_);
lean_dec(v_a_1127_);
lean_dec_ref(v_a_1126_);
lean_dec(v_a_1125_);
lean_dec_ref(v_a_1124_);
lean_dec(v_a_1123_);
lean_dec_ref(v_a_1122_);
lean_dec(v_a_1121_);
lean_dec(v_a_1120_);
lean_dec_ref(v_a_1119_);
return v_res_1131_;
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
