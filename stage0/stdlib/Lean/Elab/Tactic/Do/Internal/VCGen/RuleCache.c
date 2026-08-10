// Lean compiler output
// Module: Lean.Elab.Tactic.Do.Internal.VCGen.RuleCache
// Imports: public import Lean.Elab.Tactic.Do.VCGen.Split public import Lean.Elab.Tactic.Do.Internal.VCGen.Context public import Lean.Elab.Tactic.Do.Internal.VCGen.RuleConstruction public import Lean.Elab.Tactic.Do.Internal.VCGen.LatticeOp public import Lean.Elab.Tactic.Do.Internal.VCGen.Util import Lean.Meta.Sym.InferType
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
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Expr_getAppPrefix(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
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
uint8_t lean_usize_dec_eq(size_t, size_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecProof_key(lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_WPApp_instWP(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_tryMkBackwardRuleFromSpec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForSplit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkFrameBackwardRule(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__1___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__4_spec__5_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__4___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2___redArg(lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__4_spec__5_spec__6(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForSplitCached___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "ite"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForSplitCached___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForSplitCached___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForSplitCached___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForSplitCached___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(15, 2, 151, 246, 61, 29, 192, 254)}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForSplitCached___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForSplitCached___redArg___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForSplitCached___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "dite"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForSplitCached___redArg___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForSplitCached___redArg___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForSplitCached___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForSplitCached___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(137, 166, 197, 161, 68, 218, 116, 116)}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForSplitCached___redArg___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForSplitCached___redArg___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForSplitCached___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForSplitCached___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForSplitCached(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForSplitCached___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRuleCached_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRuleCached_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRuleCached_spec__1_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRuleCached_spec__1_spec__3_spec__4_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRuleCached_spec__1_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRuleCached_spec__1_spec__3___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRuleCached_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRuleCached_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRuleCached_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRuleCached_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRuleCached_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRuleCached___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRuleCached___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRuleCached(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRuleCached___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRuleCached_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRuleCached_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRuleCached_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRuleCached_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRuleCached_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRuleCached_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRuleCached_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRuleCached_spec__1_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRuleCached_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRuleCached_spec__1_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRuleCached_spec__1_spec__3_spec__4_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkFrameBackwardRuleCached___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkFrameBackwardRuleCached___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkFrameBackwardRuleCached(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkFrameBackwardRuleCached___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__1___redArg___lam__0(lean_object* v_k_1_, lean_object* v___y_2_, lean_object* v___y_3_, lean_object* v___y_4_, lean_object* v___y_5_, lean_object* v___y_6_, lean_object* v___y_7_, lean_object* v___y_8_, lean_object* v___y_9_, lean_object* v___y_10_, lean_object* v___y_11_, lean_object* v___y_12_){
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
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__1___redArg___lam__0___boxed(lean_object* v_k_15_, lean_object* v___y_16_, lean_object* v___y_17_, lean_object* v___y_18_, lean_object* v___y_19_, lean_object* v___y_20_, lean_object* v___y_21_, lean_object* v___y_22_, lean_object* v___y_23_, lean_object* v___y_24_, lean_object* v___y_25_, lean_object* v___y_26_, lean_object* v___y_27_){
_start:
{
lean_object* v_res_28_; 
v_res_28_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__1___redArg___lam__0(v_k_15_, v___y_16_, v___y_17_, v___y_18_, v___y_19_, v___y_20_, v___y_21_, v___y_22_, v___y_23_, v___y_24_, v___y_25_, v___y_26_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__1___redArg(lean_object* v_k_29_, uint8_t v_allowLevelAssignments_30_, lean_object* v___y_31_, lean_object* v___y_32_, lean_object* v___y_33_, lean_object* v___y_34_, lean_object* v___y_35_, lean_object* v___y_36_, lean_object* v___y_37_, lean_object* v___y_38_, lean_object* v___y_39_, lean_object* v___y_40_, lean_object* v___y_41_){
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
v___f_43_ = lean_alloc_closure((void*)(l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__1___redArg___lam__0___boxed), 13, 8);
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
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__1___redArg___boxed(lean_object* v_k_53_, lean_object* v_allowLevelAssignments_54_, lean_object* v___y_55_, lean_object* v___y_56_, lean_object* v___y_57_, lean_object* v___y_58_, lean_object* v___y_59_, lean_object* v___y_60_, lean_object* v___y_61_, lean_object* v___y_62_, lean_object* v___y_63_, lean_object* v___y_64_, lean_object* v___y_65_, lean_object* v___y_66_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_67_; lean_object* v_res_68_; 
v_allowLevelAssignments_boxed_67_ = lean_unbox(v_allowLevelAssignments_54_);
v_res_68_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__1___redArg(v_k_53_, v_allowLevelAssignments_boxed_67_, v___y_55_, v___y_56_, v___y_57_, v___y_58_, v___y_59_, v___y_60_, v___y_61_, v___y_62_, v___y_63_, v___y_64_, v___y_65_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__1(lean_object* v_00_u03b1_69_, lean_object* v_k_70_, uint8_t v_allowLevelAssignments_71_, lean_object* v___y_72_, lean_object* v___y_73_, lean_object* v___y_74_, lean_object* v___y_75_, lean_object* v___y_76_, lean_object* v___y_77_, lean_object* v___y_78_, lean_object* v___y_79_, lean_object* v___y_80_, lean_object* v___y_81_, lean_object* v___y_82_){
_start:
{
lean_object* v___x_84_; 
v___x_84_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__1___redArg(v_k_70_, v_allowLevelAssignments_71_, v___y_72_, v___y_73_, v___y_74_, v___y_75_, v___y_76_, v___y_77_, v___y_78_, v___y_79_, v___y_80_, v___y_81_, v___y_82_);
return v___x_84_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__1___boxed(lean_object* v_00_u03b1_85_, lean_object* v_k_86_, lean_object* v_allowLevelAssignments_87_, lean_object* v___y_88_, lean_object* v___y_89_, lean_object* v___y_90_, lean_object* v___y_91_, lean_object* v___y_92_, lean_object* v___y_93_, lean_object* v___y_94_, lean_object* v___y_95_, lean_object* v___y_96_, lean_object* v___y_97_, lean_object* v___y_98_, lean_object* v___y_99_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_100_; lean_object* v_res_101_; 
v_allowLevelAssignments_boxed_100_ = lean_unbox(v_allowLevelAssignments_87_);
v_res_101_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__1(v_00_u03b1_85_, v_k_86_, v_allowLevelAssignments_boxed_100_, v___y_88_, v___y_89_, v___y_90_, v___y_91_, v___y_92_, v___y_93_, v___y_94_, v___y_95_, v___y_96_, v___y_97_, v___y_98_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached___lam__0(lean_object* v_specThm_102_, lean_object* v_info_103_, lean_object* v___x_104_, lean_object* v___y_105_, lean_object* v___y_106_, lean_object* v___y_107_, lean_object* v___y_108_, lean_object* v___y_109_, lean_object* v___y_110_, lean_object* v___y_111_, lean_object* v___y_112_, lean_object* v___y_113_, lean_object* v___y_114_, lean_object* v___y_115_){
_start:
{
lean_object* v___x_117_; 
v___x_117_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_tryMkBackwardRuleFromSpec(v_specThm_102_, v_info_103_, v___x_104_, v___y_112_, v___y_113_, v___y_114_, v___y_115_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached___lam__0___boxed(lean_object* v_specThm_135_, lean_object* v_info_136_, lean_object* v___x_137_, lean_object* v___y_138_, lean_object* v___y_139_, lean_object* v___y_140_, lean_object* v___y_141_, lean_object* v___y_142_, lean_object* v___y_143_, lean_object* v___y_144_, lean_object* v___y_145_, lean_object* v___y_146_, lean_object* v___y_147_, lean_object* v___y_148_, lean_object* v___y_149_){
_start:
{
lean_object* v_res_150_; 
v_res_150_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached___lam__0(v_specThm_135_, v_info_136_, v___x_137_, v___y_138_, v___y_139_, v___y_140_, v___y_141_, v___y_142_, v___y_143_, v___y_144_, v___y_145_, v___y_146_, v___y_147_, v___y_148_);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0_spec__0___redArg(lean_object* v_a_151_, lean_object* v_x_152_){
_start:
{
if (lean_obj_tag(v_x_152_) == 0)
{
lean_object* v___x_153_; 
v___x_153_ = lean_box(0);
return v___x_153_;
}
else
{
lean_object* v_key_154_; lean_object* v_value_155_; lean_object* v_tail_156_; uint8_t v___y_158_; lean_object* v_fst_161_; lean_object* v_snd_162_; lean_object* v_fst_163_; lean_object* v_snd_164_; uint8_t v___x_165_; 
v_key_154_ = lean_ctor_get(v_x_152_, 0);
v_value_155_ = lean_ctor_get(v_x_152_, 1);
v_tail_156_ = lean_ctor_get(v_x_152_, 2);
v_fst_161_ = lean_ctor_get(v_key_154_, 0);
v_snd_162_ = lean_ctor_get(v_key_154_, 1);
v_fst_163_ = lean_ctor_get(v_a_151_, 0);
v_snd_164_ = lean_ctor_get(v_a_151_, 1);
v___x_165_ = lean_name_eq(v_fst_161_, v_fst_163_);
if (v___x_165_ == 0)
{
v___y_158_ = v___x_165_;
goto v___jp_157_;
}
else
{
lean_object* v_fst_166_; lean_object* v_snd_167_; lean_object* v_fst_168_; lean_object* v_snd_169_; size_t v___x_170_; size_t v___x_171_; uint8_t v___x_172_; 
v_fst_166_ = lean_ctor_get(v_snd_162_, 0);
v_snd_167_ = lean_ctor_get(v_snd_162_, 1);
v_fst_168_ = lean_ctor_get(v_snd_164_, 0);
v_snd_169_ = lean_ctor_get(v_snd_164_, 1);
v___x_170_ = lean_ptr_addr(v_fst_166_);
v___x_171_ = lean_ptr_addr(v_fst_168_);
v___x_172_ = lean_usize_dec_eq(v___x_170_, v___x_171_);
if (v___x_172_ == 0)
{
v___y_158_ = v___x_172_;
goto v___jp_157_;
}
else
{
uint8_t v___x_173_; 
v___x_173_ = lean_nat_dec_eq(v_snd_167_, v_snd_169_);
v___y_158_ = v___x_173_;
goto v___jp_157_;
}
}
v___jp_157_:
{
if (v___y_158_ == 0)
{
v_x_152_ = v_tail_156_;
goto _start;
}
else
{
lean_object* v___x_160_; 
lean_inc(v_value_155_);
v___x_160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_160_, 0, v_value_155_);
return v___x_160_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0_spec__0___redArg___boxed(lean_object* v_a_174_, lean_object* v_x_175_){
_start:
{
lean_object* v_res_176_; 
v_res_176_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0_spec__0___redArg(v_a_174_, v_x_175_);
lean_dec(v_x_175_);
lean_dec_ref(v_a_174_);
return v_res_176_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg(lean_object* v_m_177_, lean_object* v_a_178_){
_start:
{
lean_object* v_buckets_179_; lean_object* v_fst_180_; lean_object* v_snd_181_; lean_object* v___x_182_; uint64_t v___y_184_; 
v_buckets_179_ = lean_ctor_get(v_m_177_, 1);
v_fst_180_ = lean_ctor_get(v_a_178_, 0);
v_snd_181_ = lean_ctor_get(v_a_178_, 1);
v___x_182_ = lean_array_get_size(v_buckets_179_);
if (lean_obj_tag(v_fst_180_) == 0)
{
uint64_t v___x_207_; 
v___x_207_ = 1723ULL;
v___y_184_ = v___x_207_;
goto v___jp_183_;
}
else
{
uint64_t v_hash_208_; 
v_hash_208_ = lean_ctor_get_uint64(v_fst_180_, sizeof(void*)*2);
v___y_184_ = v_hash_208_;
goto v___jp_183_;
}
v___jp_183_:
{
lean_object* v_fst_185_; lean_object* v_snd_186_; size_t v___x_187_; size_t v___x_188_; size_t v___x_189_; uint64_t v___x_190_; uint64_t v___x_191_; uint64_t v___x_192_; uint64_t v___x_193_; uint64_t v___x_194_; uint64_t v___x_195_; uint64_t v_fold_196_; uint64_t v___x_197_; uint64_t v___x_198_; uint64_t v___x_199_; size_t v___x_200_; size_t v___x_201_; size_t v___x_202_; size_t v___x_203_; size_t v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; 
v_fst_185_ = lean_ctor_get(v_snd_181_, 0);
v_snd_186_ = lean_ctor_get(v_snd_181_, 1);
v___x_187_ = lean_ptr_addr(v_fst_185_);
v___x_188_ = ((size_t)3ULL);
v___x_189_ = lean_usize_shift_right(v___x_187_, v___x_188_);
v___x_190_ = lean_usize_to_uint64(v___x_189_);
v___x_191_ = lean_uint64_of_nat(v_snd_186_);
v___x_192_ = lean_uint64_mix_hash(v___x_190_, v___x_191_);
v___x_193_ = lean_uint64_mix_hash(v___y_184_, v___x_192_);
v___x_194_ = 32ULL;
v___x_195_ = lean_uint64_shift_right(v___x_193_, v___x_194_);
v_fold_196_ = lean_uint64_xor(v___x_193_, v___x_195_);
v___x_197_ = 16ULL;
v___x_198_ = lean_uint64_shift_right(v_fold_196_, v___x_197_);
v___x_199_ = lean_uint64_xor(v_fold_196_, v___x_198_);
v___x_200_ = lean_uint64_to_usize(v___x_199_);
v___x_201_ = lean_usize_of_nat(v___x_182_);
v___x_202_ = ((size_t)1ULL);
v___x_203_ = lean_usize_sub(v___x_201_, v___x_202_);
v___x_204_ = lean_usize_land(v___x_200_, v___x_203_);
v___x_205_ = lean_array_uget_borrowed(v_buckets_179_, v___x_204_);
v___x_206_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0_spec__0___redArg(v_a_178_, v___x_205_);
return v___x_206_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg___boxed(lean_object* v_m_209_, lean_object* v_a_210_){
_start:
{
lean_object* v_res_211_; 
v_res_211_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg(v_m_209_, v_a_210_);
lean_dec_ref(v_a_210_);
lean_dec_ref(v_m_209_);
return v_res_211_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__4_spec__5_spec__6___redArg(lean_object* v_x_212_, lean_object* v_x_213_){
_start:
{
if (lean_obj_tag(v_x_213_) == 0)
{
return v_x_212_;
}
else
{
lean_object* v_key_214_; lean_object* v_value_215_; lean_object* v_tail_216_; lean_object* v___x_218_; uint8_t v_isShared_219_; uint8_t v_isSharedCheck_253_; 
v_key_214_ = lean_ctor_get(v_x_213_, 0);
v_value_215_ = lean_ctor_get(v_x_213_, 1);
v_tail_216_ = lean_ctor_get(v_x_213_, 2);
v_isSharedCheck_253_ = !lean_is_exclusive(v_x_213_);
if (v_isSharedCheck_253_ == 0)
{
v___x_218_ = v_x_213_;
v_isShared_219_ = v_isSharedCheck_253_;
goto v_resetjp_217_;
}
else
{
lean_inc(v_tail_216_);
lean_inc(v_value_215_);
lean_inc(v_key_214_);
lean_dec(v_x_213_);
v___x_218_ = lean_box(0);
v_isShared_219_ = v_isSharedCheck_253_;
goto v_resetjp_217_;
}
v_resetjp_217_:
{
lean_object* v_fst_220_; lean_object* v_snd_221_; lean_object* v___x_222_; uint64_t v___y_224_; 
v_fst_220_ = lean_ctor_get(v_key_214_, 0);
v_snd_221_ = lean_ctor_get(v_key_214_, 1);
v___x_222_ = lean_array_get_size(v_x_212_);
if (lean_obj_tag(v_fst_220_) == 0)
{
uint64_t v___x_251_; 
v___x_251_ = 1723ULL;
v___y_224_ = v___x_251_;
goto v___jp_223_;
}
else
{
uint64_t v_hash_252_; 
v_hash_252_ = lean_ctor_get_uint64(v_fst_220_, sizeof(void*)*2);
v___y_224_ = v_hash_252_;
goto v___jp_223_;
}
v___jp_223_:
{
lean_object* v_fst_225_; lean_object* v_snd_226_; size_t v___x_227_; size_t v___x_228_; size_t v___x_229_; uint64_t v___x_230_; uint64_t v___x_231_; uint64_t v___x_232_; uint64_t v___x_233_; uint64_t v___x_234_; uint64_t v___x_235_; uint64_t v_fold_236_; uint64_t v___x_237_; uint64_t v___x_238_; uint64_t v___x_239_; size_t v___x_240_; size_t v___x_241_; size_t v___x_242_; size_t v___x_243_; size_t v___x_244_; lean_object* v___x_245_; lean_object* v___x_247_; 
v_fst_225_ = lean_ctor_get(v_snd_221_, 0);
v_snd_226_ = lean_ctor_get(v_snd_221_, 1);
v___x_227_ = lean_ptr_addr(v_fst_225_);
v___x_228_ = ((size_t)3ULL);
v___x_229_ = lean_usize_shift_right(v___x_227_, v___x_228_);
v___x_230_ = lean_usize_to_uint64(v___x_229_);
v___x_231_ = lean_uint64_of_nat(v_snd_226_);
v___x_232_ = lean_uint64_mix_hash(v___x_230_, v___x_231_);
v___x_233_ = lean_uint64_mix_hash(v___y_224_, v___x_232_);
v___x_234_ = 32ULL;
v___x_235_ = lean_uint64_shift_right(v___x_233_, v___x_234_);
v_fold_236_ = lean_uint64_xor(v___x_233_, v___x_235_);
v___x_237_ = 16ULL;
v___x_238_ = lean_uint64_shift_right(v_fold_236_, v___x_237_);
v___x_239_ = lean_uint64_xor(v_fold_236_, v___x_238_);
v___x_240_ = lean_uint64_to_usize(v___x_239_);
v___x_241_ = lean_usize_of_nat(v___x_222_);
v___x_242_ = ((size_t)1ULL);
v___x_243_ = lean_usize_sub(v___x_241_, v___x_242_);
v___x_244_ = lean_usize_land(v___x_240_, v___x_243_);
v___x_245_ = lean_array_uget_borrowed(v_x_212_, v___x_244_);
lean_inc(v___x_245_);
if (v_isShared_219_ == 0)
{
lean_ctor_set(v___x_218_, 2, v___x_245_);
v___x_247_ = v___x_218_;
goto v_reusejp_246_;
}
else
{
lean_object* v_reuseFailAlloc_250_; 
v_reuseFailAlloc_250_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_250_, 0, v_key_214_);
lean_ctor_set(v_reuseFailAlloc_250_, 1, v_value_215_);
lean_ctor_set(v_reuseFailAlloc_250_, 2, v___x_245_);
v___x_247_ = v_reuseFailAlloc_250_;
goto v_reusejp_246_;
}
v_reusejp_246_:
{
lean_object* v___x_248_; 
v___x_248_ = lean_array_uset(v_x_212_, v___x_244_, v___x_247_);
v_x_212_ = v___x_248_;
v_x_213_ = v_tail_216_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__4_spec__5___redArg(lean_object* v_i_254_, lean_object* v_source_255_, lean_object* v_target_256_){
_start:
{
lean_object* v___x_257_; uint8_t v___x_258_; 
v___x_257_ = lean_array_get_size(v_source_255_);
v___x_258_ = lean_nat_dec_lt(v_i_254_, v___x_257_);
if (v___x_258_ == 0)
{
lean_dec_ref(v_source_255_);
lean_dec(v_i_254_);
return v_target_256_;
}
else
{
lean_object* v_es_259_; lean_object* v___x_260_; lean_object* v_source_261_; lean_object* v_target_262_; lean_object* v___x_263_; lean_object* v___x_264_; 
v_es_259_ = lean_array_fget(v_source_255_, v_i_254_);
v___x_260_ = lean_box(0);
v_source_261_ = lean_array_fset(v_source_255_, v_i_254_, v___x_260_);
v_target_262_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__4_spec__5_spec__6___redArg(v_target_256_, v_es_259_);
v___x_263_ = lean_unsigned_to_nat(1u);
v___x_264_ = lean_nat_add(v_i_254_, v___x_263_);
lean_dec(v_i_254_);
v_i_254_ = v___x_264_;
v_source_255_ = v_source_261_;
v_target_256_ = v_target_262_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__4___redArg(lean_object* v_data_266_){
_start:
{
lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v_nbuckets_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; 
v___x_267_ = lean_array_get_size(v_data_266_);
v___x_268_ = lean_unsigned_to_nat(2u);
v_nbuckets_269_ = lean_nat_mul(v___x_267_, v___x_268_);
v___x_270_ = lean_unsigned_to_nat(0u);
v___x_271_ = lean_box(0);
v___x_272_ = lean_mk_array(v_nbuckets_269_, v___x_271_);
v___x_273_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__4_spec__5___redArg(v___x_270_, v_data_266_, v___x_272_);
return v___x_273_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__3___redArg(lean_object* v_a_274_, lean_object* v_x_275_){
_start:
{
if (lean_obj_tag(v_x_275_) == 0)
{
uint8_t v___x_276_; 
v___x_276_ = 0;
return v___x_276_;
}
else
{
lean_object* v_key_277_; lean_object* v_tail_278_; uint8_t v___y_280_; lean_object* v_fst_282_; lean_object* v_snd_283_; lean_object* v_fst_284_; lean_object* v_snd_285_; uint8_t v___x_286_; 
v_key_277_ = lean_ctor_get(v_x_275_, 0);
v_tail_278_ = lean_ctor_get(v_x_275_, 2);
v_fst_282_ = lean_ctor_get(v_key_277_, 0);
v_snd_283_ = lean_ctor_get(v_key_277_, 1);
v_fst_284_ = lean_ctor_get(v_a_274_, 0);
v_snd_285_ = lean_ctor_get(v_a_274_, 1);
v___x_286_ = lean_name_eq(v_fst_282_, v_fst_284_);
if (v___x_286_ == 0)
{
v___y_280_ = v___x_286_;
goto v___jp_279_;
}
else
{
lean_object* v_fst_287_; lean_object* v_snd_288_; lean_object* v_fst_289_; lean_object* v_snd_290_; size_t v___x_291_; size_t v___x_292_; uint8_t v___x_293_; 
v_fst_287_ = lean_ctor_get(v_snd_283_, 0);
v_snd_288_ = lean_ctor_get(v_snd_283_, 1);
v_fst_289_ = lean_ctor_get(v_snd_285_, 0);
v_snd_290_ = lean_ctor_get(v_snd_285_, 1);
v___x_291_ = lean_ptr_addr(v_fst_287_);
v___x_292_ = lean_ptr_addr(v_fst_289_);
v___x_293_ = lean_usize_dec_eq(v___x_291_, v___x_292_);
if (v___x_293_ == 0)
{
v___y_280_ = v___x_293_;
goto v___jp_279_;
}
else
{
uint8_t v___x_294_; 
v___x_294_ = lean_nat_dec_eq(v_snd_288_, v_snd_290_);
v___y_280_ = v___x_294_;
goto v___jp_279_;
}
}
v___jp_279_:
{
if (v___y_280_ == 0)
{
v_x_275_ = v_tail_278_;
goto _start;
}
else
{
return v___y_280_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__3___redArg___boxed(lean_object* v_a_295_, lean_object* v_x_296_){
_start:
{
uint8_t v_res_297_; lean_object* v_r_298_; 
v_res_297_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__3___redArg(v_a_295_, v_x_296_);
lean_dec(v_x_296_);
lean_dec_ref(v_a_295_);
v_r_298_ = lean_box(v_res_297_);
return v_r_298_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__5___redArg(lean_object* v_a_299_, lean_object* v_b_300_, lean_object* v_x_301_){
_start:
{
if (lean_obj_tag(v_x_301_) == 0)
{
lean_dec(v_b_300_);
lean_dec_ref(v_a_299_);
return v_x_301_;
}
else
{
lean_object* v_key_302_; lean_object* v_value_303_; lean_object* v_tail_304_; lean_object* v___x_306_; uint8_t v_isShared_307_; uint8_t v_isSharedCheck_330_; 
v_key_302_ = lean_ctor_get(v_x_301_, 0);
v_value_303_ = lean_ctor_get(v_x_301_, 1);
v_tail_304_ = lean_ctor_get(v_x_301_, 2);
v_isSharedCheck_330_ = !lean_is_exclusive(v_x_301_);
if (v_isSharedCheck_330_ == 0)
{
v___x_306_ = v_x_301_;
v_isShared_307_ = v_isSharedCheck_330_;
goto v_resetjp_305_;
}
else
{
lean_inc(v_tail_304_);
lean_inc(v_value_303_);
lean_inc(v_key_302_);
lean_dec(v_x_301_);
v___x_306_ = lean_box(0);
v_isShared_307_ = v_isSharedCheck_330_;
goto v_resetjp_305_;
}
v_resetjp_305_:
{
uint8_t v___y_309_; lean_object* v_fst_317_; lean_object* v_snd_318_; lean_object* v_fst_319_; lean_object* v_snd_320_; uint8_t v___x_321_; 
v_fst_317_ = lean_ctor_get(v_key_302_, 0);
v_snd_318_ = lean_ctor_get(v_key_302_, 1);
v_fst_319_ = lean_ctor_get(v_a_299_, 0);
v_snd_320_ = lean_ctor_get(v_a_299_, 1);
v___x_321_ = lean_name_eq(v_fst_317_, v_fst_319_);
if (v___x_321_ == 0)
{
v___y_309_ = v___x_321_;
goto v___jp_308_;
}
else
{
lean_object* v_fst_322_; lean_object* v_snd_323_; lean_object* v_fst_324_; lean_object* v_snd_325_; size_t v___x_326_; size_t v___x_327_; uint8_t v___x_328_; 
v_fst_322_ = lean_ctor_get(v_snd_318_, 0);
v_snd_323_ = lean_ctor_get(v_snd_318_, 1);
v_fst_324_ = lean_ctor_get(v_snd_320_, 0);
v_snd_325_ = lean_ctor_get(v_snd_320_, 1);
v___x_326_ = lean_ptr_addr(v_fst_322_);
v___x_327_ = lean_ptr_addr(v_fst_324_);
v___x_328_ = lean_usize_dec_eq(v___x_326_, v___x_327_);
if (v___x_328_ == 0)
{
v___y_309_ = v___x_328_;
goto v___jp_308_;
}
else
{
uint8_t v___x_329_; 
v___x_329_ = lean_nat_dec_eq(v_snd_323_, v_snd_325_);
v___y_309_ = v___x_329_;
goto v___jp_308_;
}
}
v___jp_308_:
{
if (v___y_309_ == 0)
{
lean_object* v___x_310_; lean_object* v___x_312_; 
v___x_310_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__5___redArg(v_a_299_, v_b_300_, v_tail_304_);
if (v_isShared_307_ == 0)
{
lean_ctor_set(v___x_306_, 2, v___x_310_);
v___x_312_ = v___x_306_;
goto v_reusejp_311_;
}
else
{
lean_object* v_reuseFailAlloc_313_; 
v_reuseFailAlloc_313_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_313_, 0, v_key_302_);
lean_ctor_set(v_reuseFailAlloc_313_, 1, v_value_303_);
lean_ctor_set(v_reuseFailAlloc_313_, 2, v___x_310_);
v___x_312_ = v_reuseFailAlloc_313_;
goto v_reusejp_311_;
}
v_reusejp_311_:
{
return v___x_312_;
}
}
else
{
lean_object* v___x_315_; 
lean_dec(v_value_303_);
lean_dec(v_key_302_);
if (v_isShared_307_ == 0)
{
lean_ctor_set(v___x_306_, 1, v_b_300_);
lean_ctor_set(v___x_306_, 0, v_a_299_);
v___x_315_ = v___x_306_;
goto v_reusejp_314_;
}
else
{
lean_object* v_reuseFailAlloc_316_; 
v_reuseFailAlloc_316_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_316_, 0, v_a_299_);
lean_ctor_set(v_reuseFailAlloc_316_, 1, v_b_300_);
lean_ctor_set(v_reuseFailAlloc_316_, 2, v_tail_304_);
v___x_315_ = v_reuseFailAlloc_316_;
goto v_reusejp_314_;
}
v_reusejp_314_:
{
return v___x_315_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2___redArg(lean_object* v_m_331_, lean_object* v_a_332_, lean_object* v_b_333_){
_start:
{
lean_object* v_size_334_; lean_object* v_buckets_335_; lean_object* v___x_337_; uint8_t v_isShared_338_; uint8_t v_isSharedCheck_392_; 
v_size_334_ = lean_ctor_get(v_m_331_, 0);
v_buckets_335_ = lean_ctor_get(v_m_331_, 1);
v_isSharedCheck_392_ = !lean_is_exclusive(v_m_331_);
if (v_isSharedCheck_392_ == 0)
{
v___x_337_ = v_m_331_;
v_isShared_338_ = v_isSharedCheck_392_;
goto v_resetjp_336_;
}
else
{
lean_inc(v_buckets_335_);
lean_inc(v_size_334_);
lean_dec(v_m_331_);
v___x_337_ = lean_box(0);
v_isShared_338_ = v_isSharedCheck_392_;
goto v_resetjp_336_;
}
v_resetjp_336_:
{
lean_object* v_fst_339_; lean_object* v_snd_340_; lean_object* v___x_341_; uint64_t v___y_343_; 
v_fst_339_ = lean_ctor_get(v_a_332_, 0);
v_snd_340_ = lean_ctor_get(v_a_332_, 1);
v___x_341_ = lean_array_get_size(v_buckets_335_);
if (lean_obj_tag(v_fst_339_) == 0)
{
uint64_t v___x_390_; 
v___x_390_ = 1723ULL;
v___y_343_ = v___x_390_;
goto v___jp_342_;
}
else
{
uint64_t v_hash_391_; 
v_hash_391_ = lean_ctor_get_uint64(v_fst_339_, sizeof(void*)*2);
v___y_343_ = v_hash_391_;
goto v___jp_342_;
}
v___jp_342_:
{
lean_object* v_fst_344_; lean_object* v_snd_345_; size_t v___x_346_; size_t v___x_347_; size_t v___x_348_; uint64_t v___x_349_; uint64_t v___x_350_; uint64_t v___x_351_; uint64_t v___x_352_; uint64_t v___x_353_; uint64_t v___x_354_; uint64_t v_fold_355_; uint64_t v___x_356_; uint64_t v___x_357_; uint64_t v___x_358_; size_t v___x_359_; size_t v___x_360_; size_t v___x_361_; size_t v___x_362_; size_t v___x_363_; lean_object* v_bkt_364_; uint8_t v___x_365_; 
v_fst_344_ = lean_ctor_get(v_snd_340_, 0);
v_snd_345_ = lean_ctor_get(v_snd_340_, 1);
v___x_346_ = lean_ptr_addr(v_fst_344_);
v___x_347_ = ((size_t)3ULL);
v___x_348_ = lean_usize_shift_right(v___x_346_, v___x_347_);
v___x_349_ = lean_usize_to_uint64(v___x_348_);
v___x_350_ = lean_uint64_of_nat(v_snd_345_);
v___x_351_ = lean_uint64_mix_hash(v___x_349_, v___x_350_);
v___x_352_ = lean_uint64_mix_hash(v___y_343_, v___x_351_);
v___x_353_ = 32ULL;
v___x_354_ = lean_uint64_shift_right(v___x_352_, v___x_353_);
v_fold_355_ = lean_uint64_xor(v___x_352_, v___x_354_);
v___x_356_ = 16ULL;
v___x_357_ = lean_uint64_shift_right(v_fold_355_, v___x_356_);
v___x_358_ = lean_uint64_xor(v_fold_355_, v___x_357_);
v___x_359_ = lean_uint64_to_usize(v___x_358_);
v___x_360_ = lean_usize_of_nat(v___x_341_);
v___x_361_ = ((size_t)1ULL);
v___x_362_ = lean_usize_sub(v___x_360_, v___x_361_);
v___x_363_ = lean_usize_land(v___x_359_, v___x_362_);
v_bkt_364_ = lean_array_uget_borrowed(v_buckets_335_, v___x_363_);
v___x_365_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__3___redArg(v_a_332_, v_bkt_364_);
if (v___x_365_ == 0)
{
lean_object* v___x_366_; lean_object* v_size_x27_367_; lean_object* v___x_368_; lean_object* v_buckets_x27_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; uint8_t v___x_375_; 
v___x_366_ = lean_unsigned_to_nat(1u);
v_size_x27_367_ = lean_nat_add(v_size_334_, v___x_366_);
lean_dec(v_size_334_);
lean_inc(v_bkt_364_);
v___x_368_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_368_, 0, v_a_332_);
lean_ctor_set(v___x_368_, 1, v_b_333_);
lean_ctor_set(v___x_368_, 2, v_bkt_364_);
v_buckets_x27_369_ = lean_array_uset(v_buckets_335_, v___x_363_, v___x_368_);
v___x_370_ = lean_unsigned_to_nat(4u);
v___x_371_ = lean_nat_mul(v_size_x27_367_, v___x_370_);
v___x_372_ = lean_unsigned_to_nat(3u);
v___x_373_ = lean_nat_div(v___x_371_, v___x_372_);
lean_dec(v___x_371_);
v___x_374_ = lean_array_get_size(v_buckets_x27_369_);
v___x_375_ = lean_nat_dec_le(v___x_373_, v___x_374_);
lean_dec(v___x_373_);
if (v___x_375_ == 0)
{
lean_object* v_val_376_; lean_object* v___x_378_; 
v_val_376_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__4___redArg(v_buckets_x27_369_);
if (v_isShared_338_ == 0)
{
lean_ctor_set(v___x_337_, 1, v_val_376_);
lean_ctor_set(v___x_337_, 0, v_size_x27_367_);
v___x_378_ = v___x_337_;
goto v_reusejp_377_;
}
else
{
lean_object* v_reuseFailAlloc_379_; 
v_reuseFailAlloc_379_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_379_, 0, v_size_x27_367_);
lean_ctor_set(v_reuseFailAlloc_379_, 1, v_val_376_);
v___x_378_ = v_reuseFailAlloc_379_;
goto v_reusejp_377_;
}
v_reusejp_377_:
{
return v___x_378_;
}
}
else
{
lean_object* v___x_381_; 
if (v_isShared_338_ == 0)
{
lean_ctor_set(v___x_337_, 1, v_buckets_x27_369_);
lean_ctor_set(v___x_337_, 0, v_size_x27_367_);
v___x_381_ = v___x_337_;
goto v_reusejp_380_;
}
else
{
lean_object* v_reuseFailAlloc_382_; 
v_reuseFailAlloc_382_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_382_, 0, v_size_x27_367_);
lean_ctor_set(v_reuseFailAlloc_382_, 1, v_buckets_x27_369_);
v___x_381_ = v_reuseFailAlloc_382_;
goto v_reusejp_380_;
}
v_reusejp_380_:
{
return v___x_381_;
}
}
}
else
{
lean_object* v___x_383_; lean_object* v_buckets_x27_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_388_; 
lean_inc(v_bkt_364_);
v___x_383_ = lean_box(0);
v_buckets_x27_384_ = lean_array_uset(v_buckets_335_, v___x_363_, v___x_383_);
v___x_385_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__5___redArg(v_a_332_, v_b_333_, v_bkt_364_);
v___x_386_ = lean_array_uset(v_buckets_x27_384_, v___x_363_, v___x_385_);
if (v_isShared_338_ == 0)
{
lean_ctor_set(v___x_337_, 1, v___x_386_);
v___x_388_ = v___x_337_;
goto v_reusejp_387_;
}
else
{
lean_object* v_reuseFailAlloc_389_; 
v_reuseFailAlloc_389_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_389_, 0, v_size_334_);
lean_ctor_set(v_reuseFailAlloc_389_, 1, v___x_386_);
v___x_388_ = v_reuseFailAlloc_389_;
goto v_reusejp_387_;
}
v_reusejp_387_:
{
return v___x_388_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached(lean_object* v_specThm_395_, lean_object* v_info_396_, lean_object* v_a_397_, lean_object* v_a_398_, lean_object* v_a_399_, lean_object* v_a_400_, lean_object* v_a_401_, lean_object* v_a_402_, lean_object* v_a_403_, lean_object* v_a_404_, lean_object* v_a_405_, lean_object* v_a_406_, lean_object* v_a_407_){
_start:
{
lean_object* v___x_409_; lean_object* v_proof_410_; lean_object* v_excessArgs_411_; lean_object* v_specBackwardRuleCache_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v_key_417_; lean_object* v___x_418_; 
v___x_409_ = lean_st_ref_get(v_a_398_);
v_proof_410_ = lean_ctor_get(v_specThm_395_, 1);
v_excessArgs_411_ = lean_ctor_get(v_info_396_, 2);
v_specBackwardRuleCache_412_ = lean_ctor_get(v___x_409_, 0);
lean_inc_ref(v_specBackwardRuleCache_412_);
lean_dec(v___x_409_);
v___x_413_ = l_Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecProof_key(v_proof_410_);
v___x_414_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_WPApp_instWP(v_info_396_);
v___x_415_ = lean_array_get_size(v_excessArgs_411_);
v___x_416_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_416_, 0, v___x_414_);
lean_ctor_set(v___x_416_, 1, v___x_415_);
v_key_417_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_key_417_, 0, v___x_413_);
lean_ctor_set(v_key_417_, 1, v___x_416_);
v___x_418_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg(v_specBackwardRuleCache_412_, v_key_417_);
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
v___x_420_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached___closed__0));
v___f_421_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached___lam__0___boxed), 15, 3);
lean_closure_set(v___f_421_, 0, v_specThm_395_);
lean_closure_set(v___f_421_, 1, v_info_396_);
lean_closure_set(v___f_421_, 2, v___x_420_);
v___x_422_ = 0;
v___x_423_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__1___redArg(v___f_421_, v___x_422_, v_a_397_, v_a_398_, v_a_399_, v_a_400_, v_a_401_, v_a_402_, v_a_403_, v_a_404_, v_a_405_, v_a_406_, v_a_407_);
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
v___x_458_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2___redArg(v_specBackwardRuleCache_443_, v_key_417_, v_a_438_);
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
v___x_461_ = lean_st_ref_set(v_a_398_, v___x_460_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached___boxed(lean_object* v_specThm_491_, lean_object* v_info_492_, lean_object* v_a_493_, lean_object* v_a_494_, lean_object* v_a_495_, lean_object* v_a_496_, lean_object* v_a_497_, lean_object* v_a_498_, lean_object* v_a_499_, lean_object* v_a_500_, lean_object* v_a_501_, lean_object* v_a_502_, lean_object* v_a_503_, lean_object* v_a_504_){
_start:
{
lean_object* v_res_505_; 
v_res_505_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached(v_specThm_491_, v_info_492_, v_a_493_, v_a_494_, v_a_495_, v_a_496_, v_a_497_, v_a_498_, v_a_499_, v_a_500_, v_a_501_, v_a_502_, v_a_503_);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0(lean_object* v_00_u03b2_506_, lean_object* v_m_507_, lean_object* v_a_508_){
_start:
{
lean_object* v___x_509_; 
v___x_509_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg(v_m_507_, v_a_508_);
return v___x_509_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___boxed(lean_object* v_00_u03b2_510_, lean_object* v_m_511_, lean_object* v_a_512_){
_start:
{
lean_object* v_res_513_; 
v_res_513_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0(v_00_u03b2_510_, v_m_511_, v_a_512_);
lean_dec_ref(v_a_512_);
lean_dec_ref(v_m_511_);
return v_res_513_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2(lean_object* v_00_u03b2_514_, lean_object* v_m_515_, lean_object* v_a_516_, lean_object* v_b_517_){
_start:
{
lean_object* v___x_518_; 
v___x_518_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2___redArg(v_m_515_, v_a_516_, v_b_517_);
return v___x_518_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0_spec__0(lean_object* v_00_u03b2_519_, lean_object* v_a_520_, lean_object* v_x_521_){
_start:
{
lean_object* v___x_522_; 
v___x_522_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0_spec__0___redArg(v_a_520_, v_x_521_);
return v___x_522_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0_spec__0___boxed(lean_object* v_00_u03b2_523_, lean_object* v_a_524_, lean_object* v_x_525_){
_start:
{
lean_object* v_res_526_; 
v_res_526_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0_spec__0(v_00_u03b2_523_, v_a_524_, v_x_525_);
lean_dec(v_x_525_);
lean_dec_ref(v_a_524_);
return v_res_526_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__3(lean_object* v_00_u03b2_527_, lean_object* v_a_528_, lean_object* v_x_529_){
_start:
{
uint8_t v___x_530_; 
v___x_530_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__3___redArg(v_a_528_, v_x_529_);
return v___x_530_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__3___boxed(lean_object* v_00_u03b2_531_, lean_object* v_a_532_, lean_object* v_x_533_){
_start:
{
uint8_t v_res_534_; lean_object* v_r_535_; 
v_res_534_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__3(v_00_u03b2_531_, v_a_532_, v_x_533_);
lean_dec(v_x_533_);
lean_dec_ref(v_a_532_);
v_r_535_ = lean_box(v_res_534_);
return v_r_535_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__4(lean_object* v_00_u03b2_536_, lean_object* v_data_537_){
_start:
{
lean_object* v___x_538_; 
v___x_538_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__4___redArg(v_data_537_);
return v___x_538_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__5(lean_object* v_00_u03b2_539_, lean_object* v_a_540_, lean_object* v_b_541_, lean_object* v_x_542_){
_start:
{
lean_object* v___x_543_; 
v___x_543_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__5___redArg(v_a_540_, v_b_541_, v_x_542_);
return v___x_543_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_544_, lean_object* v_i_545_, lean_object* v_source_546_, lean_object* v_target_547_){
_start:
{
lean_object* v___x_548_; 
v___x_548_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__4_spec__5___redArg(v_i_545_, v_source_546_, v_target_547_);
return v___x_548_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__4_spec__5_spec__6(lean_object* v_00_u03b2_549_, lean_object* v_x_550_, lean_object* v_x_551_){
_start:
{
lean_object* v___x_552_; 
v___x_552_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__4_spec__5_spec__6___redArg(v_x_550_, v_x_551_);
return v___x_552_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForSplitCached___redArg(lean_object* v_splitInfo_559_, lean_object* v_info_560_, lean_object* v_a_561_, lean_object* v_a_562_, lean_object* v_a_563_, lean_object* v_a_564_, lean_object* v_a_565_, lean_object* v_a_566_, lean_object* v_a_567_){
_start:
{
lean_object* v___y_570_; 
switch(lean_obj_tag(v_splitInfo_559_))
{
case 0:
{
lean_object* v___x_618_; 
v___x_618_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForSplitCached___redArg___closed__1));
v___y_570_ = v___x_618_;
goto v___jp_569_;
}
case 1:
{
lean_object* v___x_619_; 
v___x_619_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForSplitCached___redArg___closed__3));
v___y_570_ = v___x_619_;
goto v___jp_569_;
}
default: 
{
lean_object* v_matcherApp_620_; lean_object* v_matcherName_621_; 
v_matcherApp_620_ = lean_ctor_get(v_splitInfo_559_, 0);
v_matcherName_621_ = lean_ctor_get(v_matcherApp_620_, 1);
lean_inc(v_matcherName_621_);
v___y_570_ = v_matcherName_621_;
goto v___jp_569_;
}
}
v___jp_569_:
{
lean_object* v___x_571_; lean_object* v_excessArgs_572_; lean_object* v_splitBackwardRuleCache_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v_key_577_; lean_object* v___x_578_; 
v___x_571_ = lean_st_ref_get(v_a_561_);
v_excessArgs_572_ = lean_ctor_get(v_info_560_, 2);
v_splitBackwardRuleCache_573_ = lean_ctor_get(v___x_571_, 1);
lean_inc_ref(v_splitBackwardRuleCache_573_);
lean_dec(v___x_571_);
v___x_574_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_WPApp_instWP(v_info_560_);
v___x_575_ = lean_array_get_size(v_excessArgs_572_);
v___x_576_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_576_, 0, v___x_574_);
lean_ctor_set(v___x_576_, 1, v___x_575_);
v_key_577_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_key_577_, 0, v___y_570_);
lean_ctor_set(v_key_577_, 1, v___x_576_);
v___x_578_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg(v_splitBackwardRuleCache_573_, v_key_577_);
lean_dec_ref(v_splitBackwardRuleCache_573_);
if (lean_obj_tag(v___x_578_) == 1)
{
lean_object* v_val_579_; lean_object* v___x_581_; uint8_t v_isShared_582_; uint8_t v_isSharedCheck_586_; 
lean_dec_ref_known(v_key_577_, 2);
lean_dec_ref(v_info_560_);
lean_dec_ref(v_splitInfo_559_);
v_val_579_ = lean_ctor_get(v___x_578_, 0);
v_isSharedCheck_586_ = !lean_is_exclusive(v___x_578_);
if (v_isSharedCheck_586_ == 0)
{
v___x_581_ = v___x_578_;
v_isShared_582_ = v_isSharedCheck_586_;
goto v_resetjp_580_;
}
else
{
lean_inc(v_val_579_);
lean_dec(v___x_578_);
v___x_581_ = lean_box(0);
v_isShared_582_ = v_isSharedCheck_586_;
goto v_resetjp_580_;
}
v_resetjp_580_:
{
lean_object* v___x_584_; 
if (v_isShared_582_ == 0)
{
lean_ctor_set_tag(v___x_581_, 0);
v___x_584_ = v___x_581_;
goto v_reusejp_583_;
}
else
{
lean_object* v_reuseFailAlloc_585_; 
v_reuseFailAlloc_585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_585_, 0, v_val_579_);
v___x_584_ = v_reuseFailAlloc_585_;
goto v_reusejp_583_;
}
v_reusejp_583_:
{
return v___x_584_;
}
}
}
else
{
lean_object* v___x_587_; 
lean_dec(v___x_578_);
v___x_587_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForSplit(v_splitInfo_559_, v_info_560_, v_a_564_, v_a_565_, v_a_566_, v_a_567_);
if (lean_obj_tag(v___x_587_) == 0)
{
lean_object* v_a_588_; lean_object* v___x_589_; 
v_a_588_ = lean_ctor_get(v___x_587_, 0);
lean_inc(v_a_588_);
lean_dec_ref_known(v___x_587_, 1);
v___x_589_ = l_Lean_Meta_Sym_BackwardRule_shareCommon(v_a_588_, v_a_562_, v_a_563_, v_a_564_, v_a_565_, v_a_566_, v_a_567_);
if (lean_obj_tag(v___x_589_) == 0)
{
lean_object* v_a_590_; lean_object* v___x_592_; uint8_t v_isShared_593_; uint8_t v_isSharedCheck_617_; 
v_a_590_ = lean_ctor_get(v___x_589_, 0);
v_isSharedCheck_617_ = !lean_is_exclusive(v___x_589_);
if (v_isSharedCheck_617_ == 0)
{
v___x_592_ = v___x_589_;
v_isShared_593_ = v_isSharedCheck_617_;
goto v_resetjp_591_;
}
else
{
lean_inc(v_a_590_);
lean_dec(v___x_589_);
v___x_592_ = lean_box(0);
v_isShared_593_ = v_isSharedCheck_617_;
goto v_resetjp_591_;
}
v_resetjp_591_:
{
lean_object* v___x_594_; lean_object* v_specBackwardRuleCache_595_; lean_object* v_splitBackwardRuleCache_596_; lean_object* v_latticeBackwardRuleCache_597_; lean_object* v_frameBackwardRuleCache_598_; lean_object* v_frameDB_599_; lean_object* v_invariants_600_; lean_object* v_vcs_601_; lean_object* v_simpState_602_; lean_object* v_fuel_603_; lean_object* v_inlineHandledInvariants_604_; lean_object* v___x_606_; uint8_t v_isShared_607_; uint8_t v_isSharedCheck_616_; 
v___x_594_ = lean_st_ref_take(v_a_561_);
v_specBackwardRuleCache_595_ = lean_ctor_get(v___x_594_, 0);
v_splitBackwardRuleCache_596_ = lean_ctor_get(v___x_594_, 1);
v_latticeBackwardRuleCache_597_ = lean_ctor_get(v___x_594_, 2);
v_frameBackwardRuleCache_598_ = lean_ctor_get(v___x_594_, 3);
v_frameDB_599_ = lean_ctor_get(v___x_594_, 4);
v_invariants_600_ = lean_ctor_get(v___x_594_, 5);
v_vcs_601_ = lean_ctor_get(v___x_594_, 6);
v_simpState_602_ = lean_ctor_get(v___x_594_, 7);
v_fuel_603_ = lean_ctor_get(v___x_594_, 8);
v_inlineHandledInvariants_604_ = lean_ctor_get(v___x_594_, 9);
v_isSharedCheck_616_ = !lean_is_exclusive(v___x_594_);
if (v_isSharedCheck_616_ == 0)
{
v___x_606_ = v___x_594_;
v_isShared_607_ = v_isSharedCheck_616_;
goto v_resetjp_605_;
}
else
{
lean_inc(v_inlineHandledInvariants_604_);
lean_inc(v_fuel_603_);
lean_inc(v_simpState_602_);
lean_inc(v_vcs_601_);
lean_inc(v_invariants_600_);
lean_inc(v_frameDB_599_);
lean_inc(v_frameBackwardRuleCache_598_);
lean_inc(v_latticeBackwardRuleCache_597_);
lean_inc(v_splitBackwardRuleCache_596_);
lean_inc(v_specBackwardRuleCache_595_);
lean_dec(v___x_594_);
v___x_606_ = lean_box(0);
v_isShared_607_ = v_isSharedCheck_616_;
goto v_resetjp_605_;
}
v_resetjp_605_:
{
lean_object* v___x_608_; lean_object* v___x_610_; 
lean_inc(v_a_590_);
v___x_608_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2___redArg(v_splitBackwardRuleCache_596_, v_key_577_, v_a_590_);
if (v_isShared_607_ == 0)
{
lean_ctor_set(v___x_606_, 1, v___x_608_);
v___x_610_ = v___x_606_;
goto v_reusejp_609_;
}
else
{
lean_object* v_reuseFailAlloc_615_; 
v_reuseFailAlloc_615_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_615_, 0, v_specBackwardRuleCache_595_);
lean_ctor_set(v_reuseFailAlloc_615_, 1, v___x_608_);
lean_ctor_set(v_reuseFailAlloc_615_, 2, v_latticeBackwardRuleCache_597_);
lean_ctor_set(v_reuseFailAlloc_615_, 3, v_frameBackwardRuleCache_598_);
lean_ctor_set(v_reuseFailAlloc_615_, 4, v_frameDB_599_);
lean_ctor_set(v_reuseFailAlloc_615_, 5, v_invariants_600_);
lean_ctor_set(v_reuseFailAlloc_615_, 6, v_vcs_601_);
lean_ctor_set(v_reuseFailAlloc_615_, 7, v_simpState_602_);
lean_ctor_set(v_reuseFailAlloc_615_, 8, v_fuel_603_);
lean_ctor_set(v_reuseFailAlloc_615_, 9, v_inlineHandledInvariants_604_);
v___x_610_ = v_reuseFailAlloc_615_;
goto v_reusejp_609_;
}
v_reusejp_609_:
{
lean_object* v___x_611_; lean_object* v___x_613_; 
v___x_611_ = lean_st_ref_set(v_a_561_, v___x_610_);
if (v_isShared_593_ == 0)
{
v___x_613_ = v___x_592_;
goto v_reusejp_612_;
}
else
{
lean_object* v_reuseFailAlloc_614_; 
v_reuseFailAlloc_614_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_614_, 0, v_a_590_);
v___x_613_ = v_reuseFailAlloc_614_;
goto v_reusejp_612_;
}
v_reusejp_612_:
{
return v___x_613_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_key_577_, 2);
return v___x_589_;
}
}
else
{
lean_dec_ref_known(v_key_577_, 2);
return v___x_587_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForSplitCached___redArg___boxed(lean_object* v_splitInfo_622_, lean_object* v_info_623_, lean_object* v_a_624_, lean_object* v_a_625_, lean_object* v_a_626_, lean_object* v_a_627_, lean_object* v_a_628_, lean_object* v_a_629_, lean_object* v_a_630_, lean_object* v_a_631_){
_start:
{
lean_object* v_res_632_; 
v_res_632_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForSplitCached___redArg(v_splitInfo_622_, v_info_623_, v_a_624_, v_a_625_, v_a_626_, v_a_627_, v_a_628_, v_a_629_, v_a_630_);
lean_dec(v_a_630_);
lean_dec_ref(v_a_629_);
lean_dec(v_a_628_);
lean_dec_ref(v_a_627_);
lean_dec(v_a_626_);
lean_dec_ref(v_a_625_);
lean_dec(v_a_624_);
return v_res_632_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForSplitCached(lean_object* v_splitInfo_633_, lean_object* v_info_634_, lean_object* v_a_635_, lean_object* v_a_636_, lean_object* v_a_637_, lean_object* v_a_638_, lean_object* v_a_639_, lean_object* v_a_640_, lean_object* v_a_641_, lean_object* v_a_642_, lean_object* v_a_643_, lean_object* v_a_644_, lean_object* v_a_645_){
_start:
{
lean_object* v___x_647_; 
v___x_647_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForSplitCached___redArg(v_splitInfo_633_, v_info_634_, v_a_636_, v_a_640_, v_a_641_, v_a_642_, v_a_643_, v_a_644_, v_a_645_);
return v___x_647_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForSplitCached___boxed(lean_object* v_splitInfo_648_, lean_object* v_info_649_, lean_object* v_a_650_, lean_object* v_a_651_, lean_object* v_a_652_, lean_object* v_a_653_, lean_object* v_a_654_, lean_object* v_a_655_, lean_object* v_a_656_, lean_object* v_a_657_, lean_object* v_a_658_, lean_object* v_a_659_, lean_object* v_a_660_, lean_object* v_a_661_){
_start:
{
lean_object* v_res_662_; 
v_res_662_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForSplitCached(v_splitInfo_648_, v_info_649_, v_a_650_, v_a_651_, v_a_652_, v_a_653_, v_a_654_, v_a_655_, v_a_656_, v_a_657_, v_a_658_, v_a_659_, v_a_660_);
lean_dec(v_a_660_);
lean_dec_ref(v_a_659_);
lean_dec(v_a_658_);
lean_dec_ref(v_a_657_);
lean_dec(v_a_656_);
lean_dec_ref(v_a_655_);
lean_dec(v_a_654_);
lean_dec_ref(v_a_653_);
lean_dec(v_a_652_);
lean_dec(v_a_651_);
lean_dec_ref(v_a_650_);
return v_res_662_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRuleCached_spec__1_spec__2___redArg(lean_object* v_a_663_, lean_object* v_x_664_){
_start:
{
if (lean_obj_tag(v_x_664_) == 0)
{
uint8_t v___x_665_; 
v___x_665_ = 0;
return v___x_665_;
}
else
{
lean_object* v_key_666_; lean_object* v_tail_667_; uint8_t v___y_669_; lean_object* v_fst_671_; lean_object* v_snd_672_; lean_object* v_fst_673_; lean_object* v_snd_674_; size_t v___x_675_; size_t v___x_676_; uint8_t v___x_677_; 
v_key_666_ = lean_ctor_get(v_x_664_, 0);
v_tail_667_ = lean_ctor_get(v_x_664_, 2);
v_fst_671_ = lean_ctor_get(v_key_666_, 0);
v_snd_672_ = lean_ctor_get(v_key_666_, 1);
v_fst_673_ = lean_ctor_get(v_a_663_, 0);
v_snd_674_ = lean_ctor_get(v_a_663_, 1);
v___x_675_ = lean_ptr_addr(v_fst_671_);
v___x_676_ = lean_ptr_addr(v_fst_673_);
v___x_677_ = lean_usize_dec_eq(v___x_675_, v___x_676_);
if (v___x_677_ == 0)
{
v___y_669_ = v___x_677_;
goto v___jp_668_;
}
else
{
uint8_t v___x_678_; 
v___x_678_ = lean_nat_dec_eq(v_snd_672_, v_snd_674_);
v___y_669_ = v___x_678_;
goto v___jp_668_;
}
v___jp_668_:
{
if (v___y_669_ == 0)
{
v_x_664_ = v_tail_667_;
goto _start;
}
else
{
return v___y_669_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRuleCached_spec__1_spec__2___redArg___boxed(lean_object* v_a_679_, lean_object* v_x_680_){
_start:
{
uint8_t v_res_681_; lean_object* v_r_682_; 
v_res_681_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRuleCached_spec__1_spec__2___redArg(v_a_679_, v_x_680_);
lean_dec(v_x_680_);
lean_dec_ref(v_a_679_);
v_r_682_ = lean_box(v_res_681_);
return v_r_682_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRuleCached_spec__1_spec__4___redArg(lean_object* v_a_683_, lean_object* v_b_684_, lean_object* v_x_685_){
_start:
{
if (lean_obj_tag(v_x_685_) == 0)
{
lean_dec(v_b_684_);
lean_dec_ref(v_a_683_);
return v_x_685_;
}
else
{
lean_object* v_key_686_; lean_object* v_value_687_; lean_object* v_tail_688_; lean_object* v___x_690_; uint8_t v_isShared_691_; uint8_t v_isSharedCheck_709_; 
v_key_686_ = lean_ctor_get(v_x_685_, 0);
v_value_687_ = lean_ctor_get(v_x_685_, 1);
v_tail_688_ = lean_ctor_get(v_x_685_, 2);
v_isSharedCheck_709_ = !lean_is_exclusive(v_x_685_);
if (v_isSharedCheck_709_ == 0)
{
v___x_690_ = v_x_685_;
v_isShared_691_ = v_isSharedCheck_709_;
goto v_resetjp_689_;
}
else
{
lean_inc(v_tail_688_);
lean_inc(v_value_687_);
lean_inc(v_key_686_);
lean_dec(v_x_685_);
v___x_690_ = lean_box(0);
v_isShared_691_ = v_isSharedCheck_709_;
goto v_resetjp_689_;
}
v_resetjp_689_:
{
uint8_t v___y_693_; lean_object* v_fst_701_; lean_object* v_snd_702_; lean_object* v_fst_703_; lean_object* v_snd_704_; size_t v___x_705_; size_t v___x_706_; uint8_t v___x_707_; 
v_fst_701_ = lean_ctor_get(v_key_686_, 0);
v_snd_702_ = lean_ctor_get(v_key_686_, 1);
v_fst_703_ = lean_ctor_get(v_a_683_, 0);
v_snd_704_ = lean_ctor_get(v_a_683_, 1);
v___x_705_ = lean_ptr_addr(v_fst_701_);
v___x_706_ = lean_ptr_addr(v_fst_703_);
v___x_707_ = lean_usize_dec_eq(v___x_705_, v___x_706_);
if (v___x_707_ == 0)
{
v___y_693_ = v___x_707_;
goto v___jp_692_;
}
else
{
uint8_t v___x_708_; 
v___x_708_ = lean_nat_dec_eq(v_snd_702_, v_snd_704_);
v___y_693_ = v___x_708_;
goto v___jp_692_;
}
v___jp_692_:
{
if (v___y_693_ == 0)
{
lean_object* v___x_694_; lean_object* v___x_696_; 
v___x_694_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRuleCached_spec__1_spec__4___redArg(v_a_683_, v_b_684_, v_tail_688_);
if (v_isShared_691_ == 0)
{
lean_ctor_set(v___x_690_, 2, v___x_694_);
v___x_696_ = v___x_690_;
goto v_reusejp_695_;
}
else
{
lean_object* v_reuseFailAlloc_697_; 
v_reuseFailAlloc_697_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_697_, 0, v_key_686_);
lean_ctor_set(v_reuseFailAlloc_697_, 1, v_value_687_);
lean_ctor_set(v_reuseFailAlloc_697_, 2, v___x_694_);
v___x_696_ = v_reuseFailAlloc_697_;
goto v_reusejp_695_;
}
v_reusejp_695_:
{
return v___x_696_;
}
}
else
{
lean_object* v___x_699_; 
lean_dec(v_value_687_);
lean_dec(v_key_686_);
if (v_isShared_691_ == 0)
{
lean_ctor_set(v___x_690_, 1, v_b_684_);
lean_ctor_set(v___x_690_, 0, v_a_683_);
v___x_699_ = v___x_690_;
goto v_reusejp_698_;
}
else
{
lean_object* v_reuseFailAlloc_700_; 
v_reuseFailAlloc_700_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_700_, 0, v_a_683_);
lean_ctor_set(v_reuseFailAlloc_700_, 1, v_b_684_);
lean_ctor_set(v_reuseFailAlloc_700_, 2, v_tail_688_);
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
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRuleCached_spec__1_spec__3_spec__4_spec__5___redArg(lean_object* v_x_710_, lean_object* v_x_711_){
_start:
{
if (lean_obj_tag(v_x_711_) == 0)
{
return v_x_710_;
}
else
{
lean_object* v_key_712_; lean_object* v_value_713_; lean_object* v_tail_714_; lean_object* v___x_716_; uint8_t v_isShared_717_; uint8_t v_isSharedCheck_744_; 
v_key_712_ = lean_ctor_get(v_x_711_, 0);
v_value_713_ = lean_ctor_get(v_x_711_, 1);
v_tail_714_ = lean_ctor_get(v_x_711_, 2);
v_isSharedCheck_744_ = !lean_is_exclusive(v_x_711_);
if (v_isSharedCheck_744_ == 0)
{
v___x_716_ = v_x_711_;
v_isShared_717_ = v_isSharedCheck_744_;
goto v_resetjp_715_;
}
else
{
lean_inc(v_tail_714_);
lean_inc(v_value_713_);
lean_inc(v_key_712_);
lean_dec(v_x_711_);
v___x_716_ = lean_box(0);
v_isShared_717_ = v_isSharedCheck_744_;
goto v_resetjp_715_;
}
v_resetjp_715_:
{
lean_object* v_fst_718_; lean_object* v_snd_719_; lean_object* v___x_720_; size_t v___x_721_; size_t v___x_722_; size_t v___x_723_; uint64_t v___x_724_; uint64_t v___x_725_; uint64_t v___x_726_; uint64_t v___x_727_; uint64_t v___x_728_; uint64_t v_fold_729_; uint64_t v___x_730_; uint64_t v___x_731_; uint64_t v___x_732_; size_t v___x_733_; size_t v___x_734_; size_t v___x_735_; size_t v___x_736_; size_t v___x_737_; lean_object* v___x_738_; lean_object* v___x_740_; 
v_fst_718_ = lean_ctor_get(v_key_712_, 0);
v_snd_719_ = lean_ctor_get(v_key_712_, 1);
v___x_720_ = lean_array_get_size(v_x_710_);
v___x_721_ = lean_ptr_addr(v_fst_718_);
v___x_722_ = ((size_t)3ULL);
v___x_723_ = lean_usize_shift_right(v___x_721_, v___x_722_);
v___x_724_ = lean_usize_to_uint64(v___x_723_);
v___x_725_ = lean_uint64_of_nat(v_snd_719_);
v___x_726_ = lean_uint64_mix_hash(v___x_724_, v___x_725_);
v___x_727_ = 32ULL;
v___x_728_ = lean_uint64_shift_right(v___x_726_, v___x_727_);
v_fold_729_ = lean_uint64_xor(v___x_726_, v___x_728_);
v___x_730_ = 16ULL;
v___x_731_ = lean_uint64_shift_right(v_fold_729_, v___x_730_);
v___x_732_ = lean_uint64_xor(v_fold_729_, v___x_731_);
v___x_733_ = lean_uint64_to_usize(v___x_732_);
v___x_734_ = lean_usize_of_nat(v___x_720_);
v___x_735_ = ((size_t)1ULL);
v___x_736_ = lean_usize_sub(v___x_734_, v___x_735_);
v___x_737_ = lean_usize_land(v___x_733_, v___x_736_);
v___x_738_ = lean_array_uget_borrowed(v_x_710_, v___x_737_);
lean_inc(v___x_738_);
if (v_isShared_717_ == 0)
{
lean_ctor_set(v___x_716_, 2, v___x_738_);
v___x_740_ = v___x_716_;
goto v_reusejp_739_;
}
else
{
lean_object* v_reuseFailAlloc_743_; 
v_reuseFailAlloc_743_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_743_, 0, v_key_712_);
lean_ctor_set(v_reuseFailAlloc_743_, 1, v_value_713_);
lean_ctor_set(v_reuseFailAlloc_743_, 2, v___x_738_);
v___x_740_ = v_reuseFailAlloc_743_;
goto v_reusejp_739_;
}
v_reusejp_739_:
{
lean_object* v___x_741_; 
v___x_741_ = lean_array_uset(v_x_710_, v___x_737_, v___x_740_);
v_x_710_ = v___x_741_;
v_x_711_ = v_tail_714_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRuleCached_spec__1_spec__3_spec__4___redArg(lean_object* v_i_745_, lean_object* v_source_746_, lean_object* v_target_747_){
_start:
{
lean_object* v___x_748_; uint8_t v___x_749_; 
v___x_748_ = lean_array_get_size(v_source_746_);
v___x_749_ = lean_nat_dec_lt(v_i_745_, v___x_748_);
if (v___x_749_ == 0)
{
lean_dec_ref(v_source_746_);
lean_dec(v_i_745_);
return v_target_747_;
}
else
{
lean_object* v_es_750_; lean_object* v___x_751_; lean_object* v_source_752_; lean_object* v_target_753_; lean_object* v___x_754_; lean_object* v___x_755_; 
v_es_750_ = lean_array_fget(v_source_746_, v_i_745_);
v___x_751_ = lean_box(0);
v_source_752_ = lean_array_fset(v_source_746_, v_i_745_, v___x_751_);
v_target_753_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRuleCached_spec__1_spec__3_spec__4_spec__5___redArg(v_target_747_, v_es_750_);
v___x_754_ = lean_unsigned_to_nat(1u);
v___x_755_ = lean_nat_add(v_i_745_, v___x_754_);
lean_dec(v_i_745_);
v_i_745_ = v___x_755_;
v_source_746_ = v_source_752_;
v_target_747_ = v_target_753_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRuleCached_spec__1_spec__3___redArg(lean_object* v_data_757_){
_start:
{
lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v_nbuckets_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; 
v___x_758_ = lean_array_get_size(v_data_757_);
v___x_759_ = lean_unsigned_to_nat(2u);
v_nbuckets_760_ = lean_nat_mul(v___x_758_, v___x_759_);
v___x_761_ = lean_unsigned_to_nat(0u);
v___x_762_ = lean_box(0);
v___x_763_ = lean_mk_array(v_nbuckets_760_, v___x_762_);
v___x_764_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRuleCached_spec__1_spec__3_spec__4___redArg(v___x_761_, v_data_757_, v___x_763_);
return v___x_764_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRuleCached_spec__1___redArg(lean_object* v_m_765_, lean_object* v_a_766_, lean_object* v_b_767_){
_start:
{
lean_object* v_size_768_; lean_object* v_buckets_769_; lean_object* v___x_771_; uint8_t v_isShared_772_; uint8_t v_isSharedCheck_819_; 
v_size_768_ = lean_ctor_get(v_m_765_, 0);
v_buckets_769_ = lean_ctor_get(v_m_765_, 1);
v_isSharedCheck_819_ = !lean_is_exclusive(v_m_765_);
if (v_isSharedCheck_819_ == 0)
{
v___x_771_ = v_m_765_;
v_isShared_772_ = v_isSharedCheck_819_;
goto v_resetjp_770_;
}
else
{
lean_inc(v_buckets_769_);
lean_inc(v_size_768_);
lean_dec(v_m_765_);
v___x_771_ = lean_box(0);
v_isShared_772_ = v_isSharedCheck_819_;
goto v_resetjp_770_;
}
v_resetjp_770_:
{
lean_object* v_fst_773_; lean_object* v_snd_774_; lean_object* v___x_775_; size_t v___x_776_; size_t v___x_777_; size_t v___x_778_; uint64_t v___x_779_; uint64_t v___x_780_; uint64_t v___x_781_; uint64_t v___x_782_; uint64_t v___x_783_; uint64_t v_fold_784_; uint64_t v___x_785_; uint64_t v___x_786_; uint64_t v___x_787_; size_t v___x_788_; size_t v___x_789_; size_t v___x_790_; size_t v___x_791_; size_t v___x_792_; lean_object* v_bkt_793_; uint8_t v___x_794_; 
v_fst_773_ = lean_ctor_get(v_a_766_, 0);
v_snd_774_ = lean_ctor_get(v_a_766_, 1);
v___x_775_ = lean_array_get_size(v_buckets_769_);
v___x_776_ = lean_ptr_addr(v_fst_773_);
v___x_777_ = ((size_t)3ULL);
v___x_778_ = lean_usize_shift_right(v___x_776_, v___x_777_);
v___x_779_ = lean_usize_to_uint64(v___x_778_);
v___x_780_ = lean_uint64_of_nat(v_snd_774_);
v___x_781_ = lean_uint64_mix_hash(v___x_779_, v___x_780_);
v___x_782_ = 32ULL;
v___x_783_ = lean_uint64_shift_right(v___x_781_, v___x_782_);
v_fold_784_ = lean_uint64_xor(v___x_781_, v___x_783_);
v___x_785_ = 16ULL;
v___x_786_ = lean_uint64_shift_right(v_fold_784_, v___x_785_);
v___x_787_ = lean_uint64_xor(v_fold_784_, v___x_786_);
v___x_788_ = lean_uint64_to_usize(v___x_787_);
v___x_789_ = lean_usize_of_nat(v___x_775_);
v___x_790_ = ((size_t)1ULL);
v___x_791_ = lean_usize_sub(v___x_789_, v___x_790_);
v___x_792_ = lean_usize_land(v___x_788_, v___x_791_);
v_bkt_793_ = lean_array_uget_borrowed(v_buckets_769_, v___x_792_);
v___x_794_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRuleCached_spec__1_spec__2___redArg(v_a_766_, v_bkt_793_);
if (v___x_794_ == 0)
{
lean_object* v___x_795_; lean_object* v_size_x27_796_; lean_object* v___x_797_; lean_object* v_buckets_x27_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; uint8_t v___x_804_; 
v___x_795_ = lean_unsigned_to_nat(1u);
v_size_x27_796_ = lean_nat_add(v_size_768_, v___x_795_);
lean_dec(v_size_768_);
lean_inc(v_bkt_793_);
v___x_797_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_797_, 0, v_a_766_);
lean_ctor_set(v___x_797_, 1, v_b_767_);
lean_ctor_set(v___x_797_, 2, v_bkt_793_);
v_buckets_x27_798_ = lean_array_uset(v_buckets_769_, v___x_792_, v___x_797_);
v___x_799_ = lean_unsigned_to_nat(4u);
v___x_800_ = lean_nat_mul(v_size_x27_796_, v___x_799_);
v___x_801_ = lean_unsigned_to_nat(3u);
v___x_802_ = lean_nat_div(v___x_800_, v___x_801_);
lean_dec(v___x_800_);
v___x_803_ = lean_array_get_size(v_buckets_x27_798_);
v___x_804_ = lean_nat_dec_le(v___x_802_, v___x_803_);
lean_dec(v___x_802_);
if (v___x_804_ == 0)
{
lean_object* v_val_805_; lean_object* v___x_807_; 
v_val_805_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRuleCached_spec__1_spec__3___redArg(v_buckets_x27_798_);
if (v_isShared_772_ == 0)
{
lean_ctor_set(v___x_771_, 1, v_val_805_);
lean_ctor_set(v___x_771_, 0, v_size_x27_796_);
v___x_807_ = v___x_771_;
goto v_reusejp_806_;
}
else
{
lean_object* v_reuseFailAlloc_808_; 
v_reuseFailAlloc_808_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_808_, 0, v_size_x27_796_);
lean_ctor_set(v_reuseFailAlloc_808_, 1, v_val_805_);
v___x_807_ = v_reuseFailAlloc_808_;
goto v_reusejp_806_;
}
v_reusejp_806_:
{
return v___x_807_;
}
}
else
{
lean_object* v___x_810_; 
if (v_isShared_772_ == 0)
{
lean_ctor_set(v___x_771_, 1, v_buckets_x27_798_);
lean_ctor_set(v___x_771_, 0, v_size_x27_796_);
v___x_810_ = v___x_771_;
goto v_reusejp_809_;
}
else
{
lean_object* v_reuseFailAlloc_811_; 
v_reuseFailAlloc_811_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_811_, 0, v_size_x27_796_);
lean_ctor_set(v_reuseFailAlloc_811_, 1, v_buckets_x27_798_);
v___x_810_ = v_reuseFailAlloc_811_;
goto v_reusejp_809_;
}
v_reusejp_809_:
{
return v___x_810_;
}
}
}
else
{
lean_object* v___x_812_; lean_object* v_buckets_x27_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_817_; 
lean_inc(v_bkt_793_);
v___x_812_ = lean_box(0);
v_buckets_x27_813_ = lean_array_uset(v_buckets_769_, v___x_792_, v___x_812_);
v___x_814_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRuleCached_spec__1_spec__4___redArg(v_a_766_, v_b_767_, v_bkt_793_);
v___x_815_ = lean_array_uset(v_buckets_x27_813_, v___x_792_, v___x_814_);
if (v_isShared_772_ == 0)
{
lean_ctor_set(v___x_771_, 1, v___x_815_);
v___x_817_ = v___x_771_;
goto v_reusejp_816_;
}
else
{
lean_object* v_reuseFailAlloc_818_; 
v_reuseFailAlloc_818_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_818_, 0, v_size_768_);
lean_ctor_set(v_reuseFailAlloc_818_, 1, v___x_815_);
v___x_817_ = v_reuseFailAlloc_818_;
goto v_reusejp_816_;
}
v_reusejp_816_:
{
return v___x_817_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRuleCached_spec__0_spec__0___redArg(lean_object* v_a_820_, lean_object* v_x_821_){
_start:
{
if (lean_obj_tag(v_x_821_) == 0)
{
lean_object* v___x_822_; 
v___x_822_ = lean_box(0);
return v___x_822_;
}
else
{
lean_object* v_key_823_; lean_object* v_value_824_; lean_object* v_tail_825_; uint8_t v___y_827_; lean_object* v_fst_830_; lean_object* v_snd_831_; lean_object* v_fst_832_; lean_object* v_snd_833_; size_t v___x_834_; size_t v___x_835_; uint8_t v___x_836_; 
v_key_823_ = lean_ctor_get(v_x_821_, 0);
v_value_824_ = lean_ctor_get(v_x_821_, 1);
v_tail_825_ = lean_ctor_get(v_x_821_, 2);
v_fst_830_ = lean_ctor_get(v_key_823_, 0);
v_snd_831_ = lean_ctor_get(v_key_823_, 1);
v_fst_832_ = lean_ctor_get(v_a_820_, 0);
v_snd_833_ = lean_ctor_get(v_a_820_, 1);
v___x_834_ = lean_ptr_addr(v_fst_830_);
v___x_835_ = lean_ptr_addr(v_fst_832_);
v___x_836_ = lean_usize_dec_eq(v___x_834_, v___x_835_);
if (v___x_836_ == 0)
{
v___y_827_ = v___x_836_;
goto v___jp_826_;
}
else
{
uint8_t v___x_837_; 
v___x_837_ = lean_nat_dec_eq(v_snd_831_, v_snd_833_);
v___y_827_ = v___x_837_;
goto v___jp_826_;
}
v___jp_826_:
{
if (v___y_827_ == 0)
{
v_x_821_ = v_tail_825_;
goto _start;
}
else
{
lean_object* v___x_829_; 
lean_inc(v_value_824_);
v___x_829_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_829_, 0, v_value_824_);
return v___x_829_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRuleCached_spec__0_spec__0___redArg___boxed(lean_object* v_a_838_, lean_object* v_x_839_){
_start:
{
lean_object* v_res_840_; 
v_res_840_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRuleCached_spec__0_spec__0___redArg(v_a_838_, v_x_839_);
lean_dec(v_x_839_);
lean_dec_ref(v_a_838_);
return v_res_840_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRuleCached_spec__0___redArg(lean_object* v_m_841_, lean_object* v_a_842_){
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
v___x_865_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRuleCached_spec__0_spec__0___redArg(v_a_842_, v___x_864_);
return v___x_865_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRuleCached_spec__0___redArg___boxed(lean_object* v_m_866_, lean_object* v_a_867_){
_start:
{
lean_object* v_res_868_; 
v_res_868_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRuleCached_spec__0___redArg(v_m_866_, v_a_867_);
lean_dec_ref(v_a_867_);
lean_dec_ref(v_m_866_);
return v_res_868_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRuleCached___redArg(lean_object* v_rhs_869_, lean_object* v_op_870_, lean_object* v_a_871_, lean_object* v_a_872_, lean_object* v_a_873_, lean_object* v_a_874_, lean_object* v_a_875_, lean_object* v_a_876_, lean_object* v_a_877_){
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
v___x_885_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRuleCached_spec__0___redArg(v_latticeBackwardRuleCache_881_, v_key_884_);
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
v___x_894_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule(v_rhs_869_, v_op_870_, v_a_872_, v_a_873_, v_a_874_, v_a_875_, v_a_876_, v_a_877_);
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
v___x_915_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRuleCached_spec__1___redArg(v_latticeBackwardRuleCache_904_, v_key_884_, v_a_897_);
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
v___x_918_ = lean_st_ref_set(v_a_871_, v___x_917_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRuleCached___redArg___boxed(lean_object* v_rhs_925_, lean_object* v_op_926_, lean_object* v_a_927_, lean_object* v_a_928_, lean_object* v_a_929_, lean_object* v_a_930_, lean_object* v_a_931_, lean_object* v_a_932_, lean_object* v_a_933_, lean_object* v_a_934_){
_start:
{
lean_object* v_res_935_; 
v_res_935_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRuleCached___redArg(v_rhs_925_, v_op_926_, v_a_927_, v_a_928_, v_a_929_, v_a_930_, v_a_931_, v_a_932_, v_a_933_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRuleCached(lean_object* v_rhs_936_, lean_object* v_op_937_, lean_object* v_a_938_, lean_object* v_a_939_, lean_object* v_a_940_, lean_object* v_a_941_, lean_object* v_a_942_, lean_object* v_a_943_, lean_object* v_a_944_, lean_object* v_a_945_, lean_object* v_a_946_, lean_object* v_a_947_, lean_object* v_a_948_){
_start:
{
lean_object* v___x_950_; 
v___x_950_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRuleCached___redArg(v_rhs_936_, v_op_937_, v_a_939_, v_a_943_, v_a_944_, v_a_945_, v_a_946_, v_a_947_, v_a_948_);
return v___x_950_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRuleCached___boxed(lean_object* v_rhs_951_, lean_object* v_op_952_, lean_object* v_a_953_, lean_object* v_a_954_, lean_object* v_a_955_, lean_object* v_a_956_, lean_object* v_a_957_, lean_object* v_a_958_, lean_object* v_a_959_, lean_object* v_a_960_, lean_object* v_a_961_, lean_object* v_a_962_, lean_object* v_a_963_, lean_object* v_a_964_){
_start:
{
lean_object* v_res_965_; 
v_res_965_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRuleCached(v_rhs_951_, v_op_952_, v_a_953_, v_a_954_, v_a_955_, v_a_956_, v_a_957_, v_a_958_, v_a_959_, v_a_960_, v_a_961_, v_a_962_, v_a_963_);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRuleCached_spec__0(lean_object* v_00_u03b2_966_, lean_object* v_m_967_, lean_object* v_a_968_){
_start:
{
lean_object* v___x_969_; 
v___x_969_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRuleCached_spec__0___redArg(v_m_967_, v_a_968_);
return v___x_969_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRuleCached_spec__0___boxed(lean_object* v_00_u03b2_970_, lean_object* v_m_971_, lean_object* v_a_972_){
_start:
{
lean_object* v_res_973_; 
v_res_973_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRuleCached_spec__0(v_00_u03b2_970_, v_m_971_, v_a_972_);
lean_dec_ref(v_a_972_);
lean_dec_ref(v_m_971_);
return v_res_973_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRuleCached_spec__1(lean_object* v_00_u03b2_974_, lean_object* v_m_975_, lean_object* v_a_976_, lean_object* v_b_977_){
_start:
{
lean_object* v___x_978_; 
v___x_978_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRuleCached_spec__1___redArg(v_m_975_, v_a_976_, v_b_977_);
return v___x_978_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRuleCached_spec__0_spec__0(lean_object* v_00_u03b2_979_, lean_object* v_a_980_, lean_object* v_x_981_){
_start:
{
lean_object* v___x_982_; 
v___x_982_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRuleCached_spec__0_spec__0___redArg(v_a_980_, v_x_981_);
return v___x_982_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRuleCached_spec__0_spec__0___boxed(lean_object* v_00_u03b2_983_, lean_object* v_a_984_, lean_object* v_x_985_){
_start:
{
lean_object* v_res_986_; 
v_res_986_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRuleCached_spec__0_spec__0(v_00_u03b2_983_, v_a_984_, v_x_985_);
lean_dec(v_x_985_);
lean_dec_ref(v_a_984_);
return v_res_986_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRuleCached_spec__1_spec__2(lean_object* v_00_u03b2_987_, lean_object* v_a_988_, lean_object* v_x_989_){
_start:
{
uint8_t v___x_990_; 
v___x_990_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRuleCached_spec__1_spec__2___redArg(v_a_988_, v_x_989_);
return v___x_990_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRuleCached_spec__1_spec__2___boxed(lean_object* v_00_u03b2_991_, lean_object* v_a_992_, lean_object* v_x_993_){
_start:
{
uint8_t v_res_994_; lean_object* v_r_995_; 
v_res_994_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRuleCached_spec__1_spec__2(v_00_u03b2_991_, v_a_992_, v_x_993_);
lean_dec(v_x_993_);
lean_dec_ref(v_a_992_);
v_r_995_ = lean_box(v_res_994_);
return v_r_995_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRuleCached_spec__1_spec__3(lean_object* v_00_u03b2_996_, lean_object* v_data_997_){
_start:
{
lean_object* v___x_998_; 
v___x_998_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRuleCached_spec__1_spec__3___redArg(v_data_997_);
return v___x_998_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRuleCached_spec__1_spec__4(lean_object* v_00_u03b2_999_, lean_object* v_a_1000_, lean_object* v_b_1001_, lean_object* v_x_1002_){
_start:
{
lean_object* v___x_1003_; 
v___x_1003_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRuleCached_spec__1_spec__4___redArg(v_a_1000_, v_b_1001_, v_x_1002_);
return v___x_1003_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRuleCached_spec__1_spec__3_spec__4(lean_object* v_00_u03b2_1004_, lean_object* v_i_1005_, lean_object* v_source_1006_, lean_object* v_target_1007_){
_start:
{
lean_object* v___x_1008_; 
v___x_1008_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRuleCached_spec__1_spec__3_spec__4___redArg(v_i_1005_, v_source_1006_, v_target_1007_);
return v___x_1008_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRuleCached_spec__1_spec__3_spec__4_spec__5(lean_object* v_00_u03b2_1009_, lean_object* v_x_1010_, lean_object* v_x_1011_){
_start:
{
lean_object* v___x_1012_; 
v___x_1012_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRuleCached_spec__1_spec__3_spec__4_spec__5___redArg(v_x_1010_, v_x_1011_);
return v___x_1012_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkFrameBackwardRuleCached___redArg(lean_object* v_fp_1013_, lean_object* v_info_1014_, lean_object* v_a_1015_, lean_object* v_a_1016_, lean_object* v_a_1017_, lean_object* v_a_1018_, lean_object* v_a_1019_, lean_object* v_a_1020_, lean_object* v_a_1021_){
_start:
{
lean_object* v___x_1023_; lean_object* v_excessArgs_1024_; lean_object* v_frameBackwardRuleCache_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v_key_1028_; lean_object* v___x_1029_; 
v___x_1023_ = lean_st_ref_get(v_a_1015_);
v_excessArgs_1024_ = lean_ctor_get(v_info_1014_, 2);
v_frameBackwardRuleCache_1025_ = lean_ctor_get(v___x_1023_, 3);
lean_inc_ref(v_frameBackwardRuleCache_1025_);
lean_dec(v___x_1023_);
v___x_1026_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_WPApp_instWP(v_info_1014_);
v___x_1027_ = lean_array_get_size(v_excessArgs_1024_);
v_key_1028_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_key_1028_, 0, v___x_1026_);
lean_ctor_set(v_key_1028_, 1, v___x_1027_);
v___x_1029_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRuleCached_spec__0___redArg(v_frameBackwardRuleCache_1025_, v_key_1028_);
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
v___x_1038_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_mkFrameBackwardRule(v_fp_1013_, v_info_1014_, v_a_1018_, v_a_1019_, v_a_1020_, v_a_1021_);
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
v___x_1067_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRuleCached_spec__1___redArg(v_frameBackwardRuleCache_1055_, v_key_1028_, v___x_1066_);
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
v___x_1070_ = lean_st_ref_set(v_a_1015_, v___x_1069_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkFrameBackwardRuleCached___redArg___boxed(lean_object* v_fp_1087_, lean_object* v_info_1088_, lean_object* v_a_1089_, lean_object* v_a_1090_, lean_object* v_a_1091_, lean_object* v_a_1092_, lean_object* v_a_1093_, lean_object* v_a_1094_, lean_object* v_a_1095_, lean_object* v_a_1096_){
_start:
{
lean_object* v_res_1097_; 
v_res_1097_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_mkFrameBackwardRuleCached___redArg(v_fp_1087_, v_info_1088_, v_a_1089_, v_a_1090_, v_a_1091_, v_a_1092_, v_a_1093_, v_a_1094_, v_a_1095_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkFrameBackwardRuleCached(lean_object* v_fp_1098_, lean_object* v_info_1099_, lean_object* v_a_1100_, lean_object* v_a_1101_, lean_object* v_a_1102_, lean_object* v_a_1103_, lean_object* v_a_1104_, lean_object* v_a_1105_, lean_object* v_a_1106_, lean_object* v_a_1107_, lean_object* v_a_1108_, lean_object* v_a_1109_, lean_object* v_a_1110_){
_start:
{
lean_object* v___x_1112_; 
v___x_1112_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_mkFrameBackwardRuleCached___redArg(v_fp_1098_, v_info_1099_, v_a_1101_, v_a_1105_, v_a_1106_, v_a_1107_, v_a_1108_, v_a_1109_, v_a_1110_);
return v___x_1112_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkFrameBackwardRuleCached___boxed(lean_object* v_fp_1113_, lean_object* v_info_1114_, lean_object* v_a_1115_, lean_object* v_a_1116_, lean_object* v_a_1117_, lean_object* v_a_1118_, lean_object* v_a_1119_, lean_object* v_a_1120_, lean_object* v_a_1121_, lean_object* v_a_1122_, lean_object* v_a_1123_, lean_object* v_a_1124_, lean_object* v_a_1125_, lean_object* v_a_1126_){
_start:
{
lean_object* v_res_1127_; 
v_res_1127_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_mkFrameBackwardRuleCached(v_fp_1113_, v_info_1114_, v_a_1115_, v_a_1116_, v_a_1117_, v_a_1118_, v_a_1119_, v_a_1120_, v_a_1121_, v_a_1122_, v_a_1123_, v_a_1124_, v_a_1125_);
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
lean_object* runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Context(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_RuleConstruction(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Util(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_InferType(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_RuleCache(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Elab_Tactic_Do_VCGen_Split(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Context(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_RuleConstruction(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_InferType(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_RuleCache(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Tactic_Do_VCGen_Split(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Context(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_Do_Internal_VCGen_RuleConstruction(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Util(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_InferType(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_Do_Internal_VCGen_RuleCache(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Tactic_Do_VCGen_Split(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Context(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Do_Internal_VCGen_RuleConstruction(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_InferType(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_RuleCache(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_RuleCache(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_Do_Internal_VCGen_RuleCache(builtin);
}
#ifdef __cplusplus
}
#endif
