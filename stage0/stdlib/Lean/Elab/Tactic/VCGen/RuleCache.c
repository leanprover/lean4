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
lean_object* l_Lean_Elab_Tactic_VCGen_WPApp_instWP(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Elab_Tactic_VCGen_mkBackwardRuleForSplit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_BackwardRule_shareCommon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v_key_154_; lean_object* v_tail_155_; lean_object* v_fst_156_; lean_object* v_snd_157_; lean_object* v_fst_158_; lean_object* v_snd_159_; uint8_t v___x_160_; 
v_key_154_ = lean_ctor_get(v_x_152_, 0);
v_tail_155_ = lean_ctor_get(v_x_152_, 2);
v_fst_156_ = lean_ctor_get(v_key_154_, 0);
v_snd_157_ = lean_ctor_get(v_key_154_, 1);
v_fst_158_ = lean_ctor_get(v_a_151_, 0);
v_snd_159_ = lean_ctor_get(v_a_151_, 1);
v___x_160_ = lean_name_eq(v_fst_156_, v_fst_158_);
if (v___x_160_ == 0)
{
v_x_152_ = v_tail_155_;
goto _start;
}
else
{
lean_object* v_fst_162_; lean_object* v_snd_163_; lean_object* v_fst_164_; lean_object* v_snd_165_; size_t v___x_166_; size_t v___x_167_; uint8_t v___x_168_; 
v_fst_162_ = lean_ctor_get(v_snd_157_, 0);
v_snd_163_ = lean_ctor_get(v_snd_157_, 1);
v_fst_164_ = lean_ctor_get(v_snd_159_, 0);
v_snd_165_ = lean_ctor_get(v_snd_159_, 1);
v___x_166_ = lean_ptr_addr(v_fst_162_);
v___x_167_ = lean_ptr_addr(v_fst_164_);
v___x_168_ = lean_usize_dec_eq(v___x_166_, v___x_167_);
if (v___x_168_ == 0)
{
v_x_152_ = v_tail_155_;
goto _start;
}
else
{
uint8_t v___x_170_; 
v___x_170_ = lean_nat_dec_eq(v_snd_163_, v_snd_165_);
if (v___x_170_ == 0)
{
v_x_152_ = v_tail_155_;
goto _start;
}
else
{
return v___x_170_;
}
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
lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v_nbuckets_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; 
v___x_231_ = lean_array_get_size(v_data_230_);
v___x_232_ = lean_unsigned_to_nat(2u);
v_nbuckets_233_ = lean_nat_mul(v___x_231_, v___x_232_);
v___x_234_ = lean_unsigned_to_nat(0u);
v___x_235_ = lean_box(0);
v___x_236_ = lean_mk_array(v_nbuckets_233_, v___x_235_);
v___x_237_ = lean_array_propagate_mark(v_data_230_, v___x_236_);
v___x_238_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__4_spec__5___redArg(v___x_234_, v_data_230_, v___x_237_);
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
lean_object* v_key_242_; lean_object* v_value_243_; lean_object* v_tail_244_; lean_object* v___x_246_; uint8_t v_isShared_247_; uint8_t v_isSharedCheck_267_; 
v_key_242_ = lean_ctor_get(v_x_241_, 0);
v_value_243_ = lean_ctor_get(v_x_241_, 1);
v_tail_244_ = lean_ctor_get(v_x_241_, 2);
v_isSharedCheck_267_ = !lean_is_exclusive(v_x_241_);
if (v_isSharedCheck_267_ == 0)
{
v___x_246_ = v_x_241_;
v_isShared_247_ = v_isSharedCheck_267_;
goto v_resetjp_245_;
}
else
{
lean_inc(v_tail_244_);
lean_inc(v_value_243_);
lean_inc(v_key_242_);
lean_dec(v_x_241_);
v___x_246_ = lean_box(0);
v_isShared_247_ = v_isSharedCheck_267_;
goto v_resetjp_245_;
}
v_resetjp_245_:
{
lean_object* v_fst_253_; lean_object* v_snd_254_; lean_object* v_fst_255_; lean_object* v_snd_256_; uint8_t v___x_257_; 
v_fst_253_ = lean_ctor_get(v_key_242_, 0);
v_snd_254_ = lean_ctor_get(v_key_242_, 1);
v_fst_255_ = lean_ctor_get(v_a_239_, 0);
v_snd_256_ = lean_ctor_get(v_a_239_, 1);
v___x_257_ = lean_name_eq(v_fst_253_, v_fst_255_);
if (v___x_257_ == 0)
{
goto v___jp_248_;
}
else
{
lean_object* v_fst_258_; lean_object* v_snd_259_; lean_object* v_fst_260_; lean_object* v_snd_261_; size_t v___x_262_; size_t v___x_263_; uint8_t v___x_264_; 
v_fst_258_ = lean_ctor_get(v_snd_254_, 0);
v_snd_259_ = lean_ctor_get(v_snd_254_, 1);
v_fst_260_ = lean_ctor_get(v_snd_256_, 0);
v_snd_261_ = lean_ctor_get(v_snd_256_, 1);
v___x_262_ = lean_ptr_addr(v_fst_258_);
v___x_263_ = lean_ptr_addr(v_fst_260_);
v___x_264_ = lean_usize_dec_eq(v___x_262_, v___x_263_);
if (v___x_264_ == 0)
{
goto v___jp_248_;
}
else
{
uint8_t v___x_265_; 
v___x_265_ = lean_nat_dec_eq(v_snd_259_, v_snd_261_);
if (v___x_265_ == 0)
{
goto v___jp_248_;
}
else
{
lean_object* v___x_266_; 
lean_del_object(v___x_246_);
lean_dec(v_value_243_);
lean_dec(v_key_242_);
v___x_266_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_266_, 0, v_a_239_);
lean_ctor_set(v___x_266_, 1, v_b_240_);
lean_ctor_set(v___x_266_, 2, v_tail_244_);
return v___x_266_;
}
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
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2___redArg(lean_object* v_m_268_, lean_object* v_a_269_, lean_object* v_b_270_){
_start:
{
lean_object* v_size_271_; lean_object* v_buckets_272_; lean_object* v___x_274_; uint8_t v_isShared_275_; uint8_t v_isSharedCheck_329_; 
v_size_271_ = lean_ctor_get(v_m_268_, 0);
v_buckets_272_ = lean_ctor_get(v_m_268_, 1);
v_isSharedCheck_329_ = !lean_is_exclusive(v_m_268_);
if (v_isSharedCheck_329_ == 0)
{
v___x_274_ = v_m_268_;
v_isShared_275_ = v_isSharedCheck_329_;
goto v_resetjp_273_;
}
else
{
lean_inc(v_buckets_272_);
lean_inc(v_size_271_);
lean_dec(v_m_268_);
v___x_274_ = lean_box(0);
v_isShared_275_ = v_isSharedCheck_329_;
goto v_resetjp_273_;
}
v_resetjp_273_:
{
lean_object* v_fst_276_; lean_object* v_snd_277_; lean_object* v___x_278_; uint64_t v___y_280_; 
v_fst_276_ = lean_ctor_get(v_a_269_, 0);
v_snd_277_ = lean_ctor_get(v_a_269_, 1);
v___x_278_ = lean_array_get_size(v_buckets_272_);
if (lean_obj_tag(v_fst_276_) == 0)
{
uint64_t v___x_327_; 
v___x_327_ = 1723ULL;
v___y_280_ = v___x_327_;
goto v___jp_279_;
}
else
{
uint64_t v_hash_328_; 
v_hash_328_ = lean_ctor_get_uint64(v_fst_276_, sizeof(void*)*2);
v___y_280_ = v_hash_328_;
goto v___jp_279_;
}
v___jp_279_:
{
lean_object* v_fst_281_; lean_object* v_snd_282_; size_t v___x_283_; size_t v___x_284_; size_t v___x_285_; uint64_t v___x_286_; uint64_t v___x_287_; uint64_t v___x_288_; uint64_t v___x_289_; uint64_t v___x_290_; uint64_t v___x_291_; uint64_t v_fold_292_; uint64_t v___x_293_; uint64_t v___x_294_; uint64_t v___x_295_; size_t v___x_296_; size_t v___x_297_; size_t v___x_298_; size_t v___x_299_; size_t v___x_300_; lean_object* v_bkt_301_; uint8_t v___x_302_; 
v_fst_281_ = lean_ctor_get(v_snd_277_, 0);
v_snd_282_ = lean_ctor_get(v_snd_277_, 1);
v___x_283_ = lean_ptr_addr(v_fst_281_);
v___x_284_ = ((size_t)3ULL);
v___x_285_ = lean_usize_shift_right(v___x_283_, v___x_284_);
v___x_286_ = lean_usize_to_uint64(v___x_285_);
v___x_287_ = lean_uint64_of_nat(v_snd_282_);
v___x_288_ = lean_uint64_mix_hash(v___x_286_, v___x_287_);
v___x_289_ = lean_uint64_mix_hash(v___y_280_, v___x_288_);
v___x_290_ = 32ULL;
v___x_291_ = lean_uint64_shift_right(v___x_289_, v___x_290_);
v_fold_292_ = lean_uint64_xor(v___x_289_, v___x_291_);
v___x_293_ = 16ULL;
v___x_294_ = lean_uint64_shift_right(v_fold_292_, v___x_293_);
v___x_295_ = lean_uint64_xor(v_fold_292_, v___x_294_);
v___x_296_ = lean_uint64_to_usize(v___x_295_);
v___x_297_ = lean_usize_of_nat(v___x_278_);
v___x_298_ = ((size_t)1ULL);
v___x_299_ = lean_usize_sub(v___x_297_, v___x_298_);
v___x_300_ = lean_usize_land(v___x_296_, v___x_299_);
v_bkt_301_ = lean_array_uget_borrowed(v_buckets_272_, v___x_300_);
v___x_302_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__3___redArg(v_a_269_, v_bkt_301_);
if (v___x_302_ == 0)
{
lean_object* v___x_303_; lean_object* v_size_x27_304_; lean_object* v___x_305_; lean_object* v_buckets_x27_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; uint8_t v___x_312_; 
v___x_303_ = lean_unsigned_to_nat(1u);
v_size_x27_304_ = lean_nat_add(v_size_271_, v___x_303_);
lean_dec(v_size_271_);
lean_inc(v_bkt_301_);
v___x_305_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_305_, 0, v_a_269_);
lean_ctor_set(v___x_305_, 1, v_b_270_);
lean_ctor_set(v___x_305_, 2, v_bkt_301_);
v_buckets_x27_306_ = lean_array_uset(v_buckets_272_, v___x_300_, v___x_305_);
v___x_307_ = lean_unsigned_to_nat(4u);
v___x_308_ = lean_nat_mul(v_size_x27_304_, v___x_307_);
v___x_309_ = lean_unsigned_to_nat(3u);
v___x_310_ = lean_nat_div(v___x_308_, v___x_309_);
lean_dec(v___x_308_);
v___x_311_ = lean_array_get_size(v_buckets_x27_306_);
v___x_312_ = lean_nat_dec_le(v___x_310_, v___x_311_);
lean_dec(v___x_310_);
if (v___x_312_ == 0)
{
lean_object* v_val_313_; lean_object* v___x_315_; 
v_val_313_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__4___redArg(v_buckets_x27_306_);
if (v_isShared_275_ == 0)
{
lean_ctor_set(v___x_274_, 1, v_val_313_);
lean_ctor_set(v___x_274_, 0, v_size_x27_304_);
v___x_315_ = v___x_274_;
goto v_reusejp_314_;
}
else
{
lean_object* v_reuseFailAlloc_316_; 
v_reuseFailAlloc_316_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_316_, 0, v_size_x27_304_);
lean_ctor_set(v_reuseFailAlloc_316_, 1, v_val_313_);
v___x_315_ = v_reuseFailAlloc_316_;
goto v_reusejp_314_;
}
v_reusejp_314_:
{
return v___x_315_;
}
}
else
{
lean_object* v___x_318_; 
if (v_isShared_275_ == 0)
{
lean_ctor_set(v___x_274_, 1, v_buckets_x27_306_);
lean_ctor_set(v___x_274_, 0, v_size_x27_304_);
v___x_318_ = v___x_274_;
goto v_reusejp_317_;
}
else
{
lean_object* v_reuseFailAlloc_319_; 
v_reuseFailAlloc_319_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_319_, 0, v_size_x27_304_);
lean_ctor_set(v_reuseFailAlloc_319_, 1, v_buckets_x27_306_);
v___x_318_ = v_reuseFailAlloc_319_;
goto v_reusejp_317_;
}
v_reusejp_317_:
{
return v___x_318_;
}
}
}
else
{
lean_object* v___x_320_; lean_object* v_buckets_x27_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_325_; 
lean_inc(v_bkt_301_);
v___x_320_ = lean_box(0);
v_buckets_x27_321_ = lean_array_uset(v_buckets_272_, v___x_300_, v___x_320_);
v___x_322_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__5___redArg(v_a_269_, v_b_270_, v_bkt_301_);
v___x_323_ = lean_array_uset(v_buckets_x27_321_, v___x_300_, v___x_322_);
if (v_isShared_275_ == 0)
{
lean_ctor_set(v___x_274_, 1, v___x_323_);
v___x_325_ = v___x_274_;
goto v_reusejp_324_;
}
else
{
lean_object* v_reuseFailAlloc_326_; 
v_reuseFailAlloc_326_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_326_, 0, v_size_271_);
lean_ctor_set(v_reuseFailAlloc_326_, 1, v___x_323_);
v___x_325_ = v_reuseFailAlloc_326_;
goto v_reusejp_324_;
}
v_reusejp_324_:
{
return v___x_325_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__0_spec__0___redArg(lean_object* v_a_330_, lean_object* v_x_331_){
_start:
{
if (lean_obj_tag(v_x_331_) == 0)
{
lean_object* v___x_332_; 
v___x_332_ = lean_box(0);
return v___x_332_;
}
else
{
lean_object* v_key_333_; lean_object* v_value_334_; lean_object* v_tail_335_; lean_object* v_fst_336_; lean_object* v_snd_337_; lean_object* v_fst_338_; lean_object* v_snd_339_; uint8_t v___x_340_; 
v_key_333_ = lean_ctor_get(v_x_331_, 0);
v_value_334_ = lean_ctor_get(v_x_331_, 1);
v_tail_335_ = lean_ctor_get(v_x_331_, 2);
v_fst_336_ = lean_ctor_get(v_key_333_, 0);
v_snd_337_ = lean_ctor_get(v_key_333_, 1);
v_fst_338_ = lean_ctor_get(v_a_330_, 0);
v_snd_339_ = lean_ctor_get(v_a_330_, 1);
v___x_340_ = lean_name_eq(v_fst_336_, v_fst_338_);
if (v___x_340_ == 0)
{
v_x_331_ = v_tail_335_;
goto _start;
}
else
{
lean_object* v_fst_342_; lean_object* v_snd_343_; lean_object* v_fst_344_; lean_object* v_snd_345_; size_t v___x_346_; size_t v___x_347_; uint8_t v___x_348_; 
v_fst_342_ = lean_ctor_get(v_snd_337_, 0);
v_snd_343_ = lean_ctor_get(v_snd_337_, 1);
v_fst_344_ = lean_ctor_get(v_snd_339_, 0);
v_snd_345_ = lean_ctor_get(v_snd_339_, 1);
v___x_346_ = lean_ptr_addr(v_fst_342_);
v___x_347_ = lean_ptr_addr(v_fst_344_);
v___x_348_ = lean_usize_dec_eq(v___x_346_, v___x_347_);
if (v___x_348_ == 0)
{
v_x_331_ = v_tail_335_;
goto _start;
}
else
{
uint8_t v___x_350_; 
v___x_350_ = lean_nat_dec_eq(v_snd_343_, v_snd_345_);
if (v___x_350_ == 0)
{
v_x_331_ = v_tail_335_;
goto _start;
}
else
{
lean_object* v___x_352_; 
lean_inc(v_value_334_);
v___x_352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_352_, 0, v_value_334_);
return v___x_352_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__0_spec__0___redArg___boxed(lean_object* v_a_353_, lean_object* v_x_354_){
_start:
{
lean_object* v_res_355_; 
v_res_355_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__0_spec__0___redArg(v_a_353_, v_x_354_);
lean_dec(v_x_354_);
lean_dec_ref(v_a_353_);
return v_res_355_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg(lean_object* v_m_356_, lean_object* v_a_357_){
_start:
{
lean_object* v_buckets_358_; lean_object* v_fst_359_; lean_object* v_snd_360_; lean_object* v___x_361_; uint64_t v___y_363_; 
v_buckets_358_ = lean_ctor_get(v_m_356_, 1);
v_fst_359_ = lean_ctor_get(v_a_357_, 0);
v_snd_360_ = lean_ctor_get(v_a_357_, 1);
v___x_361_ = lean_array_get_size(v_buckets_358_);
if (lean_obj_tag(v_fst_359_) == 0)
{
uint64_t v___x_386_; 
v___x_386_ = 1723ULL;
v___y_363_ = v___x_386_;
goto v___jp_362_;
}
else
{
uint64_t v_hash_387_; 
v_hash_387_ = lean_ctor_get_uint64(v_fst_359_, sizeof(void*)*2);
v___y_363_ = v_hash_387_;
goto v___jp_362_;
}
v___jp_362_:
{
lean_object* v_fst_364_; lean_object* v_snd_365_; size_t v___x_366_; size_t v___x_367_; size_t v___x_368_; uint64_t v___x_369_; uint64_t v___x_370_; uint64_t v___x_371_; uint64_t v___x_372_; uint64_t v___x_373_; uint64_t v___x_374_; uint64_t v_fold_375_; uint64_t v___x_376_; uint64_t v___x_377_; uint64_t v___x_378_; size_t v___x_379_; size_t v___x_380_; size_t v___x_381_; size_t v___x_382_; size_t v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; 
v_fst_364_ = lean_ctor_get(v_snd_360_, 0);
v_snd_365_ = lean_ctor_get(v_snd_360_, 1);
v___x_366_ = lean_ptr_addr(v_fst_364_);
v___x_367_ = ((size_t)3ULL);
v___x_368_ = lean_usize_shift_right(v___x_366_, v___x_367_);
v___x_369_ = lean_usize_to_uint64(v___x_368_);
v___x_370_ = lean_uint64_of_nat(v_snd_365_);
v___x_371_ = lean_uint64_mix_hash(v___x_369_, v___x_370_);
v___x_372_ = lean_uint64_mix_hash(v___y_363_, v___x_371_);
v___x_373_ = 32ULL;
v___x_374_ = lean_uint64_shift_right(v___x_372_, v___x_373_);
v_fold_375_ = lean_uint64_xor(v___x_372_, v___x_374_);
v___x_376_ = 16ULL;
v___x_377_ = lean_uint64_shift_right(v_fold_375_, v___x_376_);
v___x_378_ = lean_uint64_xor(v_fold_375_, v___x_377_);
v___x_379_ = lean_uint64_to_usize(v___x_378_);
v___x_380_ = lean_usize_of_nat(v___x_361_);
v___x_381_ = ((size_t)1ULL);
v___x_382_ = lean_usize_sub(v___x_380_, v___x_381_);
v___x_383_ = lean_usize_land(v___x_379_, v___x_382_);
v___x_384_ = lean_array_uget_borrowed(v_buckets_358_, v___x_383_);
v___x_385_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__0_spec__0___redArg(v_a_357_, v___x_384_);
return v___x_385_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg___boxed(lean_object* v_m_388_, lean_object* v_a_389_){
_start:
{
lean_object* v_res_390_; 
v_res_390_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg(v_m_388_, v_a_389_);
lean_dec_ref(v_a_389_);
lean_dec_ref(v_m_388_);
return v_res_390_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached(lean_object* v_specThm_393_, lean_object* v_info_394_, lean_object* v_a_395_, lean_object* v_a_396_, lean_object* v_a_397_, lean_object* v_a_398_, lean_object* v_a_399_, lean_object* v_a_400_, lean_object* v_a_401_, lean_object* v_a_402_, lean_object* v_a_403_, lean_object* v_a_404_, lean_object* v_a_405_){
_start:
{
lean_object* v_proof_407_; lean_object* v_excessArgs_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v_key_413_; lean_object* v___x_414_; lean_object* v_specBackwardRuleCache_415_; lean_object* v___x_416_; 
v_proof_407_ = lean_ctor_get(v_specThm_393_, 1);
v_excessArgs_408_ = lean_ctor_get(v_info_394_, 3);
v___x_409_ = l_Lean_Elab_Tactic_VCGen_SpecAttr_SpecProof_key(v_proof_407_);
v___x_410_ = l_Lean_Elab_Tactic_VCGen_WPApp_instWP(v_info_394_);
v___x_411_ = lean_array_get_size(v_excessArgs_408_);
v___x_412_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_412_, 0, v___x_410_);
lean_ctor_set(v___x_412_, 1, v___x_411_);
v_key_413_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_key_413_, 0, v___x_409_);
lean_ctor_set(v_key_413_, 1, v___x_412_);
v___x_414_ = lean_st_ref_get(v_a_396_);
v_specBackwardRuleCache_415_ = lean_ctor_get(v___x_414_, 0);
lean_inc_ref(v_specBackwardRuleCache_415_);
lean_dec(v___x_414_);
v___x_416_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg(v_specBackwardRuleCache_415_, v_key_413_);
lean_dec_ref(v_specBackwardRuleCache_415_);
if (lean_obj_tag(v___x_416_) == 1)
{
lean_object* v___x_417_; 
lean_dec_ref_known(v_key_413_, 2);
lean_dec_ref(v_info_394_);
lean_dec_ref(v_specThm_393_);
v___x_417_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_417_, 0, v___x_416_);
return v___x_417_;
}
else
{
lean_object* v___x_418_; lean_object* v___f_419_; uint8_t v___x_420_; lean_object* v___x_421_; 
lean_dec(v___x_416_);
v___x_418_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached___closed__0));
v___f_419_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached___lam__0___boxed), 15, 3);
lean_closure_set(v___f_419_, 0, v_specThm_393_);
lean_closure_set(v___f_419_, 1, v_info_394_);
lean_closure_set(v___f_419_, 2, v___x_418_);
v___x_420_ = 0;
v___x_421_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__1___redArg(v___f_419_, v___x_420_, v_a_395_, v_a_396_, v_a_397_, v_a_398_, v_a_399_, v_a_400_, v_a_401_, v_a_402_, v_a_403_, v_a_404_, v_a_405_);
if (lean_obj_tag(v___x_421_) == 0)
{
lean_object* v_a_422_; lean_object* v___x_424_; uint8_t v_isShared_425_; uint8_t v_isSharedCheck_480_; 
v_a_422_ = lean_ctor_get(v___x_421_, 0);
v_isSharedCheck_480_ = !lean_is_exclusive(v___x_421_);
if (v_isSharedCheck_480_ == 0)
{
v___x_424_ = v___x_421_;
v_isShared_425_ = v_isSharedCheck_480_;
goto v_resetjp_423_;
}
else
{
lean_inc(v_a_422_);
lean_dec(v___x_421_);
v___x_424_ = lean_box(0);
v_isShared_425_ = v_isSharedCheck_480_;
goto v_resetjp_423_;
}
v_resetjp_423_:
{
if (lean_obj_tag(v_a_422_) == 0)
{
lean_object* v___x_426_; lean_object* v___x_428_; 
lean_dec_ref_known(v_key_413_, 2);
v___x_426_ = lean_box(0);
if (v_isShared_425_ == 0)
{
lean_ctor_set(v___x_424_, 0, v___x_426_);
v___x_428_ = v___x_424_;
goto v_reusejp_427_;
}
else
{
lean_object* v_reuseFailAlloc_429_; 
v_reuseFailAlloc_429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_429_, 0, v___x_426_);
v___x_428_ = v_reuseFailAlloc_429_;
goto v_reusejp_427_;
}
v_reusejp_427_:
{
return v___x_428_;
}
}
else
{
lean_object* v_val_430_; 
v_val_430_ = lean_ctor_get(v_a_422_, 0);
lean_inc(v_val_430_);
lean_dec_ref_known(v_a_422_, 1);
if (lean_obj_tag(v_val_430_) == 1)
{
lean_object* v_val_431_; lean_object* v___x_433_; uint8_t v_isShared_434_; uint8_t v_isSharedCheck_475_; 
lean_del_object(v___x_424_);
v_val_431_ = lean_ctor_get(v_val_430_, 0);
v_isSharedCheck_475_ = !lean_is_exclusive(v_val_430_);
if (v_isSharedCheck_475_ == 0)
{
v___x_433_ = v_val_430_;
v_isShared_434_ = v_isSharedCheck_475_;
goto v_resetjp_432_;
}
else
{
lean_inc(v_val_431_);
lean_dec(v_val_430_);
v___x_433_ = lean_box(0);
v_isShared_434_ = v_isSharedCheck_475_;
goto v_resetjp_432_;
}
v_resetjp_432_:
{
lean_object* v___x_435_; 
v___x_435_ = l_Lean_Meta_Sym_BackwardRule_shareCommon(v_val_431_, v_a_400_, v_a_401_, v_a_402_, v_a_403_, v_a_404_, v_a_405_);
if (lean_obj_tag(v___x_435_) == 0)
{
lean_object* v_a_436_; lean_object* v___x_438_; uint8_t v_isShared_439_; uint8_t v_isSharedCheck_466_; 
v_a_436_ = lean_ctor_get(v___x_435_, 0);
v_isSharedCheck_466_ = !lean_is_exclusive(v___x_435_);
if (v_isSharedCheck_466_ == 0)
{
v___x_438_ = v___x_435_;
v_isShared_439_ = v_isSharedCheck_466_;
goto v_resetjp_437_;
}
else
{
lean_inc(v_a_436_);
lean_dec(v___x_435_);
v___x_438_ = lean_box(0);
v_isShared_439_ = v_isSharedCheck_466_;
goto v_resetjp_437_;
}
v_resetjp_437_:
{
lean_object* v___x_441_; 
lean_inc(v_a_436_);
if (v_isShared_434_ == 0)
{
lean_ctor_set(v___x_433_, 0, v_a_436_);
v___x_441_ = v___x_433_;
goto v_reusejp_440_;
}
else
{
lean_object* v_reuseFailAlloc_465_; 
v_reuseFailAlloc_465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_465_, 0, v_a_436_);
v___x_441_ = v_reuseFailAlloc_465_;
goto v_reusejp_440_;
}
v_reusejp_440_:
{
lean_object* v___x_442_; lean_object* v_specBackwardRuleCache_443_; lean_object* v_splitBackwardRuleCache_444_; lean_object* v_latticeBackwardRuleCache_445_; lean_object* v_frameBackwardRuleCache_446_; lean_object* v_frameDB_447_; lean_object* v_invariants_448_; lean_object* v_vcs_449_; lean_object* v_simpState_450_; lean_object* v_fuel_451_; lean_object* v_inlineHandledInvariants_452_; lean_object* v___x_454_; uint8_t v_isShared_455_; uint8_t v_isSharedCheck_464_; 
v___x_442_ = lean_st_ref_take(v_a_396_);
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
v_isSharedCheck_464_ = !lean_is_exclusive(v___x_442_);
if (v_isSharedCheck_464_ == 0)
{
v___x_454_ = v___x_442_;
v_isShared_455_ = v_isSharedCheck_464_;
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
v_isShared_455_ = v_isSharedCheck_464_;
goto v_resetjp_453_;
}
v_resetjp_453_:
{
lean_object* v___x_456_; lean_object* v___x_458_; 
v___x_456_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2___redArg(v_specBackwardRuleCache_443_, v_key_413_, v_a_436_);
if (v_isShared_455_ == 0)
{
lean_ctor_set(v___x_454_, 0, v___x_456_);
v___x_458_ = v___x_454_;
goto v_reusejp_457_;
}
else
{
lean_object* v_reuseFailAlloc_463_; 
v_reuseFailAlloc_463_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_463_, 0, v___x_456_);
lean_ctor_set(v_reuseFailAlloc_463_, 1, v_splitBackwardRuleCache_444_);
lean_ctor_set(v_reuseFailAlloc_463_, 2, v_latticeBackwardRuleCache_445_);
lean_ctor_set(v_reuseFailAlloc_463_, 3, v_frameBackwardRuleCache_446_);
lean_ctor_set(v_reuseFailAlloc_463_, 4, v_frameDB_447_);
lean_ctor_set(v_reuseFailAlloc_463_, 5, v_invariants_448_);
lean_ctor_set(v_reuseFailAlloc_463_, 6, v_vcs_449_);
lean_ctor_set(v_reuseFailAlloc_463_, 7, v_simpState_450_);
lean_ctor_set(v_reuseFailAlloc_463_, 8, v_fuel_451_);
lean_ctor_set(v_reuseFailAlloc_463_, 9, v_inlineHandledInvariants_452_);
v___x_458_ = v_reuseFailAlloc_463_;
goto v_reusejp_457_;
}
v_reusejp_457_:
{
lean_object* v___x_459_; lean_object* v___x_461_; 
v___x_459_ = lean_st_ref_put(v_a_396_, v___x_458_);
if (v_isShared_439_ == 0)
{
lean_ctor_set(v___x_438_, 0, v___x_441_);
v___x_461_ = v___x_438_;
goto v_reusejp_460_;
}
else
{
lean_object* v_reuseFailAlloc_462_; 
v_reuseFailAlloc_462_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_462_, 0, v___x_441_);
v___x_461_ = v_reuseFailAlloc_462_;
goto v_reusejp_460_;
}
v_reusejp_460_:
{
return v___x_461_;
}
}
}
}
}
}
else
{
lean_object* v_a_467_; lean_object* v___x_469_; uint8_t v_isShared_470_; uint8_t v_isSharedCheck_474_; 
lean_del_object(v___x_433_);
lean_dec_ref_known(v_key_413_, 2);
v_a_467_ = lean_ctor_get(v___x_435_, 0);
v_isSharedCheck_474_ = !lean_is_exclusive(v___x_435_);
if (v_isSharedCheck_474_ == 0)
{
v___x_469_ = v___x_435_;
v_isShared_470_ = v_isSharedCheck_474_;
goto v_resetjp_468_;
}
else
{
lean_inc(v_a_467_);
lean_dec(v___x_435_);
v___x_469_ = lean_box(0);
v_isShared_470_ = v_isSharedCheck_474_;
goto v_resetjp_468_;
}
v_resetjp_468_:
{
lean_object* v___x_472_; 
if (v_isShared_470_ == 0)
{
v___x_472_ = v___x_469_;
goto v_reusejp_471_;
}
else
{
lean_object* v_reuseFailAlloc_473_; 
v_reuseFailAlloc_473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_473_, 0, v_a_467_);
v___x_472_ = v_reuseFailAlloc_473_;
goto v_reusejp_471_;
}
v_reusejp_471_:
{
return v___x_472_;
}
}
}
}
}
else
{
lean_object* v___x_476_; lean_object* v___x_478_; 
lean_dec(v_val_430_);
lean_dec_ref_known(v_key_413_, 2);
v___x_476_ = lean_box(0);
if (v_isShared_425_ == 0)
{
lean_ctor_set(v___x_424_, 0, v___x_476_);
v___x_478_ = v___x_424_;
goto v_reusejp_477_;
}
else
{
lean_object* v_reuseFailAlloc_479_; 
v_reuseFailAlloc_479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_479_, 0, v___x_476_);
v___x_478_ = v_reuseFailAlloc_479_;
goto v_reusejp_477_;
}
v_reusejp_477_:
{
return v___x_478_;
}
}
}
}
}
else
{
lean_object* v_a_481_; lean_object* v___x_483_; uint8_t v_isShared_484_; uint8_t v_isSharedCheck_488_; 
lean_dec_ref_known(v_key_413_, 2);
v_a_481_ = lean_ctor_get(v___x_421_, 0);
v_isSharedCheck_488_ = !lean_is_exclusive(v___x_421_);
if (v_isSharedCheck_488_ == 0)
{
v___x_483_ = v___x_421_;
v_isShared_484_ = v_isSharedCheck_488_;
goto v_resetjp_482_;
}
else
{
lean_inc(v_a_481_);
lean_dec(v___x_421_);
v___x_483_ = lean_box(0);
v_isShared_484_ = v_isSharedCheck_488_;
goto v_resetjp_482_;
}
v_resetjp_482_:
{
lean_object* v___x_486_; 
if (v_isShared_484_ == 0)
{
v___x_486_ = v___x_483_;
goto v_reusejp_485_;
}
else
{
lean_object* v_reuseFailAlloc_487_; 
v_reuseFailAlloc_487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_487_, 0, v_a_481_);
v___x_486_ = v_reuseFailAlloc_487_;
goto v_reusejp_485_;
}
v_reusejp_485_:
{
return v___x_486_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached___boxed(lean_object* v_specThm_489_, lean_object* v_info_490_, lean_object* v_a_491_, lean_object* v_a_492_, lean_object* v_a_493_, lean_object* v_a_494_, lean_object* v_a_495_, lean_object* v_a_496_, lean_object* v_a_497_, lean_object* v_a_498_, lean_object* v_a_499_, lean_object* v_a_500_, lean_object* v_a_501_, lean_object* v_a_502_){
_start:
{
lean_object* v_res_503_; 
v_res_503_ = l_Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached(v_specThm_489_, v_info_490_, v_a_491_, v_a_492_, v_a_493_, v_a_494_, v_a_495_, v_a_496_, v_a_497_, v_a_498_, v_a_499_, v_a_500_, v_a_501_);
lean_dec(v_a_501_);
lean_dec_ref(v_a_500_);
lean_dec(v_a_499_);
lean_dec_ref(v_a_498_);
lean_dec(v_a_497_);
lean_dec_ref(v_a_496_);
lean_dec(v_a_495_);
lean_dec_ref(v_a_494_);
lean_dec(v_a_493_);
lean_dec(v_a_492_);
lean_dec_ref(v_a_491_);
return v_res_503_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__0(lean_object* v_00_u03b2_504_, lean_object* v_m_505_, lean_object* v_a_506_){
_start:
{
lean_object* v___x_507_; 
v___x_507_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg(v_m_505_, v_a_506_);
return v___x_507_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__0___boxed(lean_object* v_00_u03b2_508_, lean_object* v_m_509_, lean_object* v_a_510_){
_start:
{
lean_object* v_res_511_; 
v_res_511_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__0(v_00_u03b2_508_, v_m_509_, v_a_510_);
lean_dec_ref(v_a_510_);
lean_dec_ref(v_m_509_);
return v_res_511_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2(lean_object* v_00_u03b2_512_, lean_object* v_m_513_, lean_object* v_a_514_, lean_object* v_b_515_){
_start:
{
lean_object* v___x_516_; 
v___x_516_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2___redArg(v_m_513_, v_a_514_, v_b_515_);
return v___x_516_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__0_spec__0(lean_object* v_00_u03b2_517_, lean_object* v_a_518_, lean_object* v_x_519_){
_start:
{
lean_object* v___x_520_; 
v___x_520_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__0_spec__0___redArg(v_a_518_, v_x_519_);
return v___x_520_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__0_spec__0___boxed(lean_object* v_00_u03b2_521_, lean_object* v_a_522_, lean_object* v_x_523_){
_start:
{
lean_object* v_res_524_; 
v_res_524_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__0_spec__0(v_00_u03b2_521_, v_a_522_, v_x_523_);
lean_dec(v_x_523_);
lean_dec_ref(v_a_522_);
return v_res_524_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__3(lean_object* v_00_u03b2_525_, lean_object* v_a_526_, lean_object* v_x_527_){
_start:
{
uint8_t v___x_528_; 
v___x_528_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__3___redArg(v_a_526_, v_x_527_);
return v___x_528_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__3___boxed(lean_object* v_00_u03b2_529_, lean_object* v_a_530_, lean_object* v_x_531_){
_start:
{
uint8_t v_res_532_; lean_object* v_r_533_; 
v_res_532_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__3(v_00_u03b2_529_, v_a_530_, v_x_531_);
lean_dec(v_x_531_);
lean_dec_ref(v_a_530_);
v_r_533_ = lean_box(v_res_532_);
return v_r_533_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__4(lean_object* v_00_u03b2_534_, lean_object* v_data_535_){
_start:
{
lean_object* v___x_536_; 
v___x_536_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__4___redArg(v_data_535_);
return v___x_536_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__5(lean_object* v_00_u03b2_537_, lean_object* v_a_538_, lean_object* v_b_539_, lean_object* v_x_540_){
_start:
{
lean_object* v___x_541_; 
v___x_541_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__5___redArg(v_a_538_, v_b_539_, v_x_540_);
return v___x_541_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_542_, lean_object* v_i_543_, lean_object* v_source_544_, lean_object* v_target_545_){
_start:
{
lean_object* v___x_546_; 
v___x_546_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__4_spec__5___redArg(v_i_543_, v_source_544_, v_target_545_);
return v___x_546_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__4_spec__5_spec__6(lean_object* v_00_u03b2_547_, lean_object* v_x_548_, lean_object* v_x_549_){
_start:
{
lean_object* v___x_550_; 
v___x_550_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__4_spec__5_spec__6___redArg(v_x_548_, v_x_549_);
return v___x_550_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_mkBackwardRuleForSplitCached___redArg(lean_object* v_splitInfo_560_, lean_object* v_info_561_, lean_object* v_a_562_, lean_object* v_a_563_, lean_object* v_a_564_, lean_object* v_a_565_, lean_object* v_a_566_, lean_object* v_a_567_, lean_object* v_a_568_){
_start:
{
lean_object* v___y_571_; 
switch(lean_obj_tag(v_splitInfo_560_))
{
case 0:
{
lean_object* v___x_619_; 
v___x_619_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_mkBackwardRuleForSplitCached___redArg___closed__1));
v___y_571_ = v___x_619_;
goto v___jp_570_;
}
case 1:
{
lean_object* v___x_620_; 
v___x_620_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_mkBackwardRuleForSplitCached___redArg___closed__3));
v___y_571_ = v___x_620_;
goto v___jp_570_;
}
case 2:
{
lean_object* v___x_621_; 
v___x_621_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_mkBackwardRuleForSplitCached___redArg___closed__5));
v___y_571_ = v___x_621_;
goto v___jp_570_;
}
default: 
{
lean_object* v_matcherApp_622_; lean_object* v_matcherName_623_; 
v_matcherApp_622_ = lean_ctor_get(v_splitInfo_560_, 0);
v_matcherName_623_ = lean_ctor_get(v_matcherApp_622_, 1);
lean_inc(v_matcherName_623_);
v___y_571_ = v_matcherName_623_;
goto v___jp_570_;
}
}
v___jp_570_:
{
lean_object* v_excessArgs_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v_key_576_; lean_object* v___x_577_; lean_object* v_splitBackwardRuleCache_578_; lean_object* v___x_579_; 
v_excessArgs_572_ = lean_ctor_get(v_info_561_, 3);
v___x_573_ = l_Lean_Elab_Tactic_VCGen_WPApp_instWP(v_info_561_);
v___x_574_ = lean_array_get_size(v_excessArgs_572_);
v___x_575_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_575_, 0, v___x_573_);
lean_ctor_set(v___x_575_, 1, v___x_574_);
v_key_576_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_key_576_, 0, v___y_571_);
lean_ctor_set(v_key_576_, 1, v___x_575_);
v___x_577_ = lean_st_ref_get(v_a_562_);
v_splitBackwardRuleCache_578_ = lean_ctor_get(v___x_577_, 1);
lean_inc_ref(v_splitBackwardRuleCache_578_);
lean_dec(v___x_577_);
v___x_579_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg(v_splitBackwardRuleCache_578_, v_key_576_);
lean_dec_ref(v_splitBackwardRuleCache_578_);
if (lean_obj_tag(v___x_579_) == 1)
{
lean_object* v_val_580_; lean_object* v___x_582_; uint8_t v_isShared_583_; uint8_t v_isSharedCheck_587_; 
lean_dec_ref_known(v_key_576_, 2);
lean_dec_ref(v_info_561_);
lean_dec_ref(v_splitInfo_560_);
v_val_580_ = lean_ctor_get(v___x_579_, 0);
v_isSharedCheck_587_ = !lean_is_exclusive(v___x_579_);
if (v_isSharedCheck_587_ == 0)
{
v___x_582_ = v___x_579_;
v_isShared_583_ = v_isSharedCheck_587_;
goto v_resetjp_581_;
}
else
{
lean_inc(v_val_580_);
lean_dec(v___x_579_);
v___x_582_ = lean_box(0);
v_isShared_583_ = v_isSharedCheck_587_;
goto v_resetjp_581_;
}
v_resetjp_581_:
{
lean_object* v___x_585_; 
if (v_isShared_583_ == 0)
{
lean_ctor_set_tag(v___x_582_, 0);
v___x_585_ = v___x_582_;
goto v_reusejp_584_;
}
else
{
lean_object* v_reuseFailAlloc_586_; 
v_reuseFailAlloc_586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_586_, 0, v_val_580_);
v___x_585_ = v_reuseFailAlloc_586_;
goto v_reusejp_584_;
}
v_reusejp_584_:
{
return v___x_585_;
}
}
}
else
{
lean_object* v___x_588_; 
lean_dec(v___x_579_);
v___x_588_ = l_Lean_Elab_Tactic_VCGen_mkBackwardRuleForSplit(v_splitInfo_560_, v_info_561_, v_a_565_, v_a_566_, v_a_567_, v_a_568_);
if (lean_obj_tag(v___x_588_) == 0)
{
lean_object* v_a_589_; lean_object* v___x_590_; 
v_a_589_ = lean_ctor_get(v___x_588_, 0);
lean_inc(v_a_589_);
lean_dec_ref_known(v___x_588_, 1);
v___x_590_ = l_Lean_Meta_Sym_BackwardRule_shareCommon(v_a_589_, v_a_563_, v_a_564_, v_a_565_, v_a_566_, v_a_567_, v_a_568_);
if (lean_obj_tag(v___x_590_) == 0)
{
lean_object* v_a_591_; lean_object* v___x_593_; uint8_t v_isShared_594_; uint8_t v_isSharedCheck_618_; 
v_a_591_ = lean_ctor_get(v___x_590_, 0);
v_isSharedCheck_618_ = !lean_is_exclusive(v___x_590_);
if (v_isSharedCheck_618_ == 0)
{
v___x_593_ = v___x_590_;
v_isShared_594_ = v_isSharedCheck_618_;
goto v_resetjp_592_;
}
else
{
lean_inc(v_a_591_);
lean_dec(v___x_590_);
v___x_593_ = lean_box(0);
v_isShared_594_ = v_isSharedCheck_618_;
goto v_resetjp_592_;
}
v_resetjp_592_:
{
lean_object* v___x_595_; lean_object* v_specBackwardRuleCache_596_; lean_object* v_splitBackwardRuleCache_597_; lean_object* v_latticeBackwardRuleCache_598_; lean_object* v_frameBackwardRuleCache_599_; lean_object* v_frameDB_600_; lean_object* v_invariants_601_; lean_object* v_vcs_602_; lean_object* v_simpState_603_; lean_object* v_fuel_604_; lean_object* v_inlineHandledInvariants_605_; lean_object* v___x_607_; uint8_t v_isShared_608_; uint8_t v_isSharedCheck_617_; 
v___x_595_ = lean_st_ref_take(v_a_562_);
v_specBackwardRuleCache_596_ = lean_ctor_get(v___x_595_, 0);
v_splitBackwardRuleCache_597_ = lean_ctor_get(v___x_595_, 1);
v_latticeBackwardRuleCache_598_ = lean_ctor_get(v___x_595_, 2);
v_frameBackwardRuleCache_599_ = lean_ctor_get(v___x_595_, 3);
v_frameDB_600_ = lean_ctor_get(v___x_595_, 4);
v_invariants_601_ = lean_ctor_get(v___x_595_, 5);
v_vcs_602_ = lean_ctor_get(v___x_595_, 6);
v_simpState_603_ = lean_ctor_get(v___x_595_, 7);
v_fuel_604_ = lean_ctor_get(v___x_595_, 8);
v_inlineHandledInvariants_605_ = lean_ctor_get(v___x_595_, 9);
v_isSharedCheck_617_ = !lean_is_exclusive(v___x_595_);
if (v_isSharedCheck_617_ == 0)
{
v___x_607_ = v___x_595_;
v_isShared_608_ = v_isSharedCheck_617_;
goto v_resetjp_606_;
}
else
{
lean_inc(v_inlineHandledInvariants_605_);
lean_inc(v_fuel_604_);
lean_inc(v_simpState_603_);
lean_inc(v_vcs_602_);
lean_inc(v_invariants_601_);
lean_inc(v_frameDB_600_);
lean_inc(v_frameBackwardRuleCache_599_);
lean_inc(v_latticeBackwardRuleCache_598_);
lean_inc(v_splitBackwardRuleCache_597_);
lean_inc(v_specBackwardRuleCache_596_);
lean_dec(v___x_595_);
v___x_607_ = lean_box(0);
v_isShared_608_ = v_isSharedCheck_617_;
goto v_resetjp_606_;
}
v_resetjp_606_:
{
lean_object* v___x_609_; lean_object* v___x_611_; 
lean_inc(v_a_591_);
v___x_609_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2___redArg(v_splitBackwardRuleCache_597_, v_key_576_, v_a_591_);
if (v_isShared_608_ == 0)
{
lean_ctor_set(v___x_607_, 1, v___x_609_);
v___x_611_ = v___x_607_;
goto v_reusejp_610_;
}
else
{
lean_object* v_reuseFailAlloc_616_; 
v_reuseFailAlloc_616_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_616_, 0, v_specBackwardRuleCache_596_);
lean_ctor_set(v_reuseFailAlloc_616_, 1, v___x_609_);
lean_ctor_set(v_reuseFailAlloc_616_, 2, v_latticeBackwardRuleCache_598_);
lean_ctor_set(v_reuseFailAlloc_616_, 3, v_frameBackwardRuleCache_599_);
lean_ctor_set(v_reuseFailAlloc_616_, 4, v_frameDB_600_);
lean_ctor_set(v_reuseFailAlloc_616_, 5, v_invariants_601_);
lean_ctor_set(v_reuseFailAlloc_616_, 6, v_vcs_602_);
lean_ctor_set(v_reuseFailAlloc_616_, 7, v_simpState_603_);
lean_ctor_set(v_reuseFailAlloc_616_, 8, v_fuel_604_);
lean_ctor_set(v_reuseFailAlloc_616_, 9, v_inlineHandledInvariants_605_);
v___x_611_ = v_reuseFailAlloc_616_;
goto v_reusejp_610_;
}
v_reusejp_610_:
{
lean_object* v___x_612_; lean_object* v___x_614_; 
v___x_612_ = lean_st_ref_put(v_a_562_, v___x_611_);
if (v_isShared_594_ == 0)
{
v___x_614_ = v___x_593_;
goto v_reusejp_613_;
}
else
{
lean_object* v_reuseFailAlloc_615_; 
v_reuseFailAlloc_615_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_615_, 0, v_a_591_);
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
lean_dec_ref_known(v_key_576_, 2);
return v___x_590_;
}
}
else
{
lean_dec_ref_known(v_key_576_, 2);
return v___x_588_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_mkBackwardRuleForSplitCached___redArg___boxed(lean_object* v_splitInfo_624_, lean_object* v_info_625_, lean_object* v_a_626_, lean_object* v_a_627_, lean_object* v_a_628_, lean_object* v_a_629_, lean_object* v_a_630_, lean_object* v_a_631_, lean_object* v_a_632_, lean_object* v_a_633_){
_start:
{
lean_object* v_res_634_; 
v_res_634_ = l_Lean_Elab_Tactic_VCGen_mkBackwardRuleForSplitCached___redArg(v_splitInfo_624_, v_info_625_, v_a_626_, v_a_627_, v_a_628_, v_a_629_, v_a_630_, v_a_631_, v_a_632_);
lean_dec(v_a_632_);
lean_dec_ref(v_a_631_);
lean_dec(v_a_630_);
lean_dec_ref(v_a_629_);
lean_dec(v_a_628_);
lean_dec_ref(v_a_627_);
lean_dec(v_a_626_);
return v_res_634_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_mkBackwardRuleForSplitCached(lean_object* v_splitInfo_635_, lean_object* v_info_636_, lean_object* v_a_637_, lean_object* v_a_638_, lean_object* v_a_639_, lean_object* v_a_640_, lean_object* v_a_641_, lean_object* v_a_642_, lean_object* v_a_643_, lean_object* v_a_644_, lean_object* v_a_645_, lean_object* v_a_646_, lean_object* v_a_647_){
_start:
{
lean_object* v___x_649_; 
v___x_649_ = l_Lean_Elab_Tactic_VCGen_mkBackwardRuleForSplitCached___redArg(v_splitInfo_635_, v_info_636_, v_a_638_, v_a_642_, v_a_643_, v_a_644_, v_a_645_, v_a_646_, v_a_647_);
return v___x_649_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_mkBackwardRuleForSplitCached___boxed(lean_object* v_splitInfo_650_, lean_object* v_info_651_, lean_object* v_a_652_, lean_object* v_a_653_, lean_object* v_a_654_, lean_object* v_a_655_, lean_object* v_a_656_, lean_object* v_a_657_, lean_object* v_a_658_, lean_object* v_a_659_, lean_object* v_a_660_, lean_object* v_a_661_, lean_object* v_a_662_, lean_object* v_a_663_){
_start:
{
lean_object* v_res_664_; 
v_res_664_ = l_Lean_Elab_Tactic_VCGen_mkBackwardRuleForSplitCached(v_splitInfo_650_, v_info_651_, v_a_652_, v_a_653_, v_a_654_, v_a_655_, v_a_656_, v_a_657_, v_a_658_, v_a_659_, v_a_660_, v_a_661_, v_a_662_);
lean_dec(v_a_662_);
lean_dec_ref(v_a_661_);
lean_dec(v_a_660_);
lean_dec_ref(v_a_659_);
lean_dec(v_a_658_);
lean_dec_ref(v_a_657_);
lean_dec(v_a_656_);
lean_dec_ref(v_a_655_);
lean_dec(v_a_654_);
lean_dec(v_a_653_);
lean_dec_ref(v_a_652_);
return v_res_664_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1_spec__2___redArg(lean_object* v_a_665_, lean_object* v_x_666_){
_start:
{
if (lean_obj_tag(v_x_666_) == 0)
{
uint8_t v___x_667_; 
v___x_667_ = 0;
return v___x_667_;
}
else
{
lean_object* v_key_668_; lean_object* v_tail_669_; lean_object* v_fst_670_; lean_object* v_snd_671_; lean_object* v_fst_672_; lean_object* v_snd_673_; size_t v___x_674_; size_t v___x_675_; uint8_t v___x_676_; 
v_key_668_ = lean_ctor_get(v_x_666_, 0);
v_tail_669_ = lean_ctor_get(v_x_666_, 2);
v_fst_670_ = lean_ctor_get(v_key_668_, 0);
v_snd_671_ = lean_ctor_get(v_key_668_, 1);
v_fst_672_ = lean_ctor_get(v_a_665_, 0);
v_snd_673_ = lean_ctor_get(v_a_665_, 1);
v___x_674_ = lean_ptr_addr(v_fst_670_);
v___x_675_ = lean_ptr_addr(v_fst_672_);
v___x_676_ = lean_usize_dec_eq(v___x_674_, v___x_675_);
if (v___x_676_ == 0)
{
v_x_666_ = v_tail_669_;
goto _start;
}
else
{
uint8_t v___x_678_; 
v___x_678_ = lean_nat_dec_eq(v_snd_671_, v_snd_673_);
if (v___x_678_ == 0)
{
v_x_666_ = v_tail_669_;
goto _start;
}
else
{
return v___x_678_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1_spec__2___redArg___boxed(lean_object* v_a_680_, lean_object* v_x_681_){
_start:
{
uint8_t v_res_682_; lean_object* v_r_683_; 
v_res_682_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1_spec__2___redArg(v_a_680_, v_x_681_);
lean_dec(v_x_681_);
lean_dec_ref(v_a_680_);
v_r_683_ = lean_box(v_res_682_);
return v_r_683_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1_spec__4___redArg(lean_object* v_a_684_, lean_object* v_b_685_, lean_object* v_x_686_){
_start:
{
if (lean_obj_tag(v_x_686_) == 0)
{
lean_dec(v_b_685_);
lean_dec_ref(v_a_684_);
return v_x_686_;
}
else
{
lean_object* v_key_687_; lean_object* v_value_688_; lean_object* v_tail_689_; lean_object* v___x_691_; uint8_t v_isShared_692_; uint8_t v_isSharedCheck_707_; 
v_key_687_ = lean_ctor_get(v_x_686_, 0);
v_value_688_ = lean_ctor_get(v_x_686_, 1);
v_tail_689_ = lean_ctor_get(v_x_686_, 2);
v_isSharedCheck_707_ = !lean_is_exclusive(v_x_686_);
if (v_isSharedCheck_707_ == 0)
{
v___x_691_ = v_x_686_;
v_isShared_692_ = v_isSharedCheck_707_;
goto v_resetjp_690_;
}
else
{
lean_inc(v_tail_689_);
lean_inc(v_value_688_);
lean_inc(v_key_687_);
lean_dec(v_x_686_);
v___x_691_ = lean_box(0);
v_isShared_692_ = v_isSharedCheck_707_;
goto v_resetjp_690_;
}
v_resetjp_690_:
{
lean_object* v_fst_698_; lean_object* v_snd_699_; lean_object* v_fst_700_; lean_object* v_snd_701_; size_t v___x_702_; size_t v___x_703_; uint8_t v___x_704_; 
v_fst_698_ = lean_ctor_get(v_key_687_, 0);
v_snd_699_ = lean_ctor_get(v_key_687_, 1);
v_fst_700_ = lean_ctor_get(v_a_684_, 0);
v_snd_701_ = lean_ctor_get(v_a_684_, 1);
v___x_702_ = lean_ptr_addr(v_fst_698_);
v___x_703_ = lean_ptr_addr(v_fst_700_);
v___x_704_ = lean_usize_dec_eq(v___x_702_, v___x_703_);
if (v___x_704_ == 0)
{
goto v___jp_693_;
}
else
{
uint8_t v___x_705_; 
v___x_705_ = lean_nat_dec_eq(v_snd_699_, v_snd_701_);
if (v___x_705_ == 0)
{
goto v___jp_693_;
}
else
{
lean_object* v___x_706_; 
lean_del_object(v___x_691_);
lean_dec(v_value_688_);
lean_dec(v_key_687_);
v___x_706_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_706_, 0, v_a_684_);
lean_ctor_set(v___x_706_, 1, v_b_685_);
lean_ctor_set(v___x_706_, 2, v_tail_689_);
return v___x_706_;
}
}
v___jp_693_:
{
lean_object* v___x_694_; lean_object* v___x_696_; 
v___x_694_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1_spec__4___redArg(v_a_684_, v_b_685_, v_tail_689_);
if (v_isShared_692_ == 0)
{
lean_ctor_set(v___x_691_, 2, v___x_694_);
v___x_696_ = v___x_691_;
goto v_reusejp_695_;
}
else
{
lean_object* v_reuseFailAlloc_697_; 
v_reuseFailAlloc_697_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_697_, 0, v_key_687_);
lean_ctor_set(v_reuseFailAlloc_697_, 1, v_value_688_);
lean_ctor_set(v_reuseFailAlloc_697_, 2, v___x_694_);
v___x_696_ = v_reuseFailAlloc_697_;
goto v_reusejp_695_;
}
v_reusejp_695_:
{
return v___x_696_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1_spec__3_spec__4_spec__5___redArg(lean_object* v_x_708_, lean_object* v_x_709_){
_start:
{
if (lean_obj_tag(v_x_709_) == 0)
{
return v_x_708_;
}
else
{
lean_object* v_key_710_; lean_object* v_value_711_; lean_object* v_tail_712_; lean_object* v___x_714_; uint8_t v_isShared_715_; uint8_t v_isSharedCheck_742_; 
v_key_710_ = lean_ctor_get(v_x_709_, 0);
v_value_711_ = lean_ctor_get(v_x_709_, 1);
v_tail_712_ = lean_ctor_get(v_x_709_, 2);
v_isSharedCheck_742_ = !lean_is_exclusive(v_x_709_);
if (v_isSharedCheck_742_ == 0)
{
v___x_714_ = v_x_709_;
v_isShared_715_ = v_isSharedCheck_742_;
goto v_resetjp_713_;
}
else
{
lean_inc(v_tail_712_);
lean_inc(v_value_711_);
lean_inc(v_key_710_);
lean_dec(v_x_709_);
v___x_714_ = lean_box(0);
v_isShared_715_ = v_isSharedCheck_742_;
goto v_resetjp_713_;
}
v_resetjp_713_:
{
lean_object* v_fst_716_; lean_object* v_snd_717_; lean_object* v___x_718_; size_t v___x_719_; size_t v___x_720_; size_t v___x_721_; uint64_t v___x_722_; uint64_t v___x_723_; uint64_t v___x_724_; uint64_t v___x_725_; uint64_t v___x_726_; uint64_t v_fold_727_; uint64_t v___x_728_; uint64_t v___x_729_; uint64_t v___x_730_; size_t v___x_731_; size_t v___x_732_; size_t v___x_733_; size_t v___x_734_; size_t v___x_735_; lean_object* v___x_736_; lean_object* v___x_738_; 
v_fst_716_ = lean_ctor_get(v_key_710_, 0);
v_snd_717_ = lean_ctor_get(v_key_710_, 1);
v___x_718_ = lean_array_get_size(v_x_708_);
v___x_719_ = lean_ptr_addr(v_fst_716_);
v___x_720_ = ((size_t)3ULL);
v___x_721_ = lean_usize_shift_right(v___x_719_, v___x_720_);
v___x_722_ = lean_usize_to_uint64(v___x_721_);
v___x_723_ = lean_uint64_of_nat(v_snd_717_);
v___x_724_ = lean_uint64_mix_hash(v___x_722_, v___x_723_);
v___x_725_ = 32ULL;
v___x_726_ = lean_uint64_shift_right(v___x_724_, v___x_725_);
v_fold_727_ = lean_uint64_xor(v___x_724_, v___x_726_);
v___x_728_ = 16ULL;
v___x_729_ = lean_uint64_shift_right(v_fold_727_, v___x_728_);
v___x_730_ = lean_uint64_xor(v_fold_727_, v___x_729_);
v___x_731_ = lean_uint64_to_usize(v___x_730_);
v___x_732_ = lean_usize_of_nat(v___x_718_);
v___x_733_ = ((size_t)1ULL);
v___x_734_ = lean_usize_sub(v___x_732_, v___x_733_);
v___x_735_ = lean_usize_land(v___x_731_, v___x_734_);
v___x_736_ = lean_array_uget_borrowed(v_x_708_, v___x_735_);
lean_inc(v___x_736_);
if (v_isShared_715_ == 0)
{
lean_ctor_set(v___x_714_, 2, v___x_736_);
v___x_738_ = v___x_714_;
goto v_reusejp_737_;
}
else
{
lean_object* v_reuseFailAlloc_741_; 
v_reuseFailAlloc_741_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_741_, 0, v_key_710_);
lean_ctor_set(v_reuseFailAlloc_741_, 1, v_value_711_);
lean_ctor_set(v_reuseFailAlloc_741_, 2, v___x_736_);
v___x_738_ = v_reuseFailAlloc_741_;
goto v_reusejp_737_;
}
v_reusejp_737_:
{
lean_object* v___x_739_; 
v___x_739_ = lean_array_uset(v_x_708_, v___x_735_, v___x_738_);
v_x_708_ = v___x_739_;
v_x_709_ = v_tail_712_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1_spec__3_spec__4___redArg(lean_object* v_i_743_, lean_object* v_source_744_, lean_object* v_target_745_){
_start:
{
lean_object* v___x_746_; uint8_t v___x_747_; 
v___x_746_ = lean_array_get_size(v_source_744_);
v___x_747_ = lean_nat_dec_lt(v_i_743_, v___x_746_);
if (v___x_747_ == 0)
{
lean_dec_ref(v_source_744_);
lean_dec(v_i_743_);
return v_target_745_;
}
else
{
lean_object* v_es_748_; lean_object* v___x_749_; lean_object* v_source_750_; lean_object* v_target_751_; lean_object* v___x_752_; lean_object* v___x_753_; 
v_es_748_ = lean_array_fget(v_source_744_, v_i_743_);
v___x_749_ = lean_box(0);
v_source_750_ = lean_array_fset(v_source_744_, v_i_743_, v___x_749_);
v_target_751_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1_spec__3_spec__4_spec__5___redArg(v_target_745_, v_es_748_);
v___x_752_ = lean_unsigned_to_nat(1u);
v___x_753_ = lean_nat_add(v_i_743_, v___x_752_);
lean_dec(v_i_743_);
v_i_743_ = v___x_753_;
v_source_744_ = v_source_750_;
v_target_745_ = v_target_751_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1_spec__3___redArg(lean_object* v_data_755_){
_start:
{
lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v_nbuckets_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; 
v___x_756_ = lean_array_get_size(v_data_755_);
v___x_757_ = lean_unsigned_to_nat(2u);
v_nbuckets_758_ = lean_nat_mul(v___x_756_, v___x_757_);
v___x_759_ = lean_unsigned_to_nat(0u);
v___x_760_ = lean_box(0);
v___x_761_ = lean_mk_array(v_nbuckets_758_, v___x_760_);
v___x_762_ = lean_array_propagate_mark(v_data_755_, v___x_761_);
v___x_763_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1_spec__3_spec__4___redArg(v___x_759_, v_data_755_, v___x_762_);
return v___x_763_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1___redArg(lean_object* v_m_764_, lean_object* v_a_765_, lean_object* v_b_766_){
_start:
{
lean_object* v_size_767_; lean_object* v_buckets_768_; lean_object* v___x_770_; uint8_t v_isShared_771_; uint8_t v_isSharedCheck_818_; 
v_size_767_ = lean_ctor_get(v_m_764_, 0);
v_buckets_768_ = lean_ctor_get(v_m_764_, 1);
v_isSharedCheck_818_ = !lean_is_exclusive(v_m_764_);
if (v_isSharedCheck_818_ == 0)
{
v___x_770_ = v_m_764_;
v_isShared_771_ = v_isSharedCheck_818_;
goto v_resetjp_769_;
}
else
{
lean_inc(v_buckets_768_);
lean_inc(v_size_767_);
lean_dec(v_m_764_);
v___x_770_ = lean_box(0);
v_isShared_771_ = v_isSharedCheck_818_;
goto v_resetjp_769_;
}
v_resetjp_769_:
{
lean_object* v_fst_772_; lean_object* v_snd_773_; lean_object* v___x_774_; size_t v___x_775_; size_t v___x_776_; size_t v___x_777_; uint64_t v___x_778_; uint64_t v___x_779_; uint64_t v___x_780_; uint64_t v___x_781_; uint64_t v___x_782_; uint64_t v_fold_783_; uint64_t v___x_784_; uint64_t v___x_785_; uint64_t v___x_786_; size_t v___x_787_; size_t v___x_788_; size_t v___x_789_; size_t v___x_790_; size_t v___x_791_; lean_object* v_bkt_792_; uint8_t v___x_793_; 
v_fst_772_ = lean_ctor_get(v_a_765_, 0);
v_snd_773_ = lean_ctor_get(v_a_765_, 1);
v___x_774_ = lean_array_get_size(v_buckets_768_);
v___x_775_ = lean_ptr_addr(v_fst_772_);
v___x_776_ = ((size_t)3ULL);
v___x_777_ = lean_usize_shift_right(v___x_775_, v___x_776_);
v___x_778_ = lean_usize_to_uint64(v___x_777_);
v___x_779_ = lean_uint64_of_nat(v_snd_773_);
v___x_780_ = lean_uint64_mix_hash(v___x_778_, v___x_779_);
v___x_781_ = 32ULL;
v___x_782_ = lean_uint64_shift_right(v___x_780_, v___x_781_);
v_fold_783_ = lean_uint64_xor(v___x_780_, v___x_782_);
v___x_784_ = 16ULL;
v___x_785_ = lean_uint64_shift_right(v_fold_783_, v___x_784_);
v___x_786_ = lean_uint64_xor(v_fold_783_, v___x_785_);
v___x_787_ = lean_uint64_to_usize(v___x_786_);
v___x_788_ = lean_usize_of_nat(v___x_774_);
v___x_789_ = ((size_t)1ULL);
v___x_790_ = lean_usize_sub(v___x_788_, v___x_789_);
v___x_791_ = lean_usize_land(v___x_787_, v___x_790_);
v_bkt_792_ = lean_array_uget_borrowed(v_buckets_768_, v___x_791_);
v___x_793_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1_spec__2___redArg(v_a_765_, v_bkt_792_);
if (v___x_793_ == 0)
{
lean_object* v___x_794_; lean_object* v_size_x27_795_; lean_object* v___x_796_; lean_object* v_buckets_x27_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; uint8_t v___x_803_; 
v___x_794_ = lean_unsigned_to_nat(1u);
v_size_x27_795_ = lean_nat_add(v_size_767_, v___x_794_);
lean_dec(v_size_767_);
lean_inc(v_bkt_792_);
v___x_796_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_796_, 0, v_a_765_);
lean_ctor_set(v___x_796_, 1, v_b_766_);
lean_ctor_set(v___x_796_, 2, v_bkt_792_);
v_buckets_x27_797_ = lean_array_uset(v_buckets_768_, v___x_791_, v___x_796_);
v___x_798_ = lean_unsigned_to_nat(4u);
v___x_799_ = lean_nat_mul(v_size_x27_795_, v___x_798_);
v___x_800_ = lean_unsigned_to_nat(3u);
v___x_801_ = lean_nat_div(v___x_799_, v___x_800_);
lean_dec(v___x_799_);
v___x_802_ = lean_array_get_size(v_buckets_x27_797_);
v___x_803_ = lean_nat_dec_le(v___x_801_, v___x_802_);
lean_dec(v___x_801_);
if (v___x_803_ == 0)
{
lean_object* v_val_804_; lean_object* v___x_806_; 
v_val_804_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1_spec__3___redArg(v_buckets_x27_797_);
if (v_isShared_771_ == 0)
{
lean_ctor_set(v___x_770_, 1, v_val_804_);
lean_ctor_set(v___x_770_, 0, v_size_x27_795_);
v___x_806_ = v___x_770_;
goto v_reusejp_805_;
}
else
{
lean_object* v_reuseFailAlloc_807_; 
v_reuseFailAlloc_807_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_807_, 0, v_size_x27_795_);
lean_ctor_set(v_reuseFailAlloc_807_, 1, v_val_804_);
v___x_806_ = v_reuseFailAlloc_807_;
goto v_reusejp_805_;
}
v_reusejp_805_:
{
return v___x_806_;
}
}
else
{
lean_object* v___x_809_; 
if (v_isShared_771_ == 0)
{
lean_ctor_set(v___x_770_, 1, v_buckets_x27_797_);
lean_ctor_set(v___x_770_, 0, v_size_x27_795_);
v___x_809_ = v___x_770_;
goto v_reusejp_808_;
}
else
{
lean_object* v_reuseFailAlloc_810_; 
v_reuseFailAlloc_810_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_810_, 0, v_size_x27_795_);
lean_ctor_set(v_reuseFailAlloc_810_, 1, v_buckets_x27_797_);
v___x_809_ = v_reuseFailAlloc_810_;
goto v_reusejp_808_;
}
v_reusejp_808_:
{
return v___x_809_;
}
}
}
else
{
lean_object* v___x_811_; lean_object* v_buckets_x27_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_816_; 
lean_inc(v_bkt_792_);
v___x_811_ = lean_box(0);
v_buckets_x27_812_ = lean_array_uset(v_buckets_768_, v___x_791_, v___x_811_);
v___x_813_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1_spec__4___redArg(v_a_765_, v_b_766_, v_bkt_792_);
v___x_814_ = lean_array_uset(v_buckets_x27_812_, v___x_791_, v___x_813_);
if (v_isShared_771_ == 0)
{
lean_ctor_set(v___x_770_, 1, v___x_814_);
v___x_816_ = v___x_770_;
goto v_reusejp_815_;
}
else
{
lean_object* v_reuseFailAlloc_817_; 
v_reuseFailAlloc_817_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_817_, 0, v_size_767_);
lean_ctor_set(v_reuseFailAlloc_817_, 1, v___x_814_);
v___x_816_ = v_reuseFailAlloc_817_;
goto v_reusejp_815_;
}
v_reusejp_815_:
{
return v___x_816_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__0_spec__0___redArg(lean_object* v_a_819_, lean_object* v_x_820_){
_start:
{
if (lean_obj_tag(v_x_820_) == 0)
{
lean_object* v___x_821_; 
v___x_821_ = lean_box(0);
return v___x_821_;
}
else
{
lean_object* v_key_822_; lean_object* v_value_823_; lean_object* v_tail_824_; lean_object* v_fst_825_; lean_object* v_snd_826_; lean_object* v_fst_827_; lean_object* v_snd_828_; size_t v___x_829_; size_t v___x_830_; uint8_t v___x_831_; 
v_key_822_ = lean_ctor_get(v_x_820_, 0);
v_value_823_ = lean_ctor_get(v_x_820_, 1);
v_tail_824_ = lean_ctor_get(v_x_820_, 2);
v_fst_825_ = lean_ctor_get(v_key_822_, 0);
v_snd_826_ = lean_ctor_get(v_key_822_, 1);
v_fst_827_ = lean_ctor_get(v_a_819_, 0);
v_snd_828_ = lean_ctor_get(v_a_819_, 1);
v___x_829_ = lean_ptr_addr(v_fst_825_);
v___x_830_ = lean_ptr_addr(v_fst_827_);
v___x_831_ = lean_usize_dec_eq(v___x_829_, v___x_830_);
if (v___x_831_ == 0)
{
v_x_820_ = v_tail_824_;
goto _start;
}
else
{
uint8_t v___x_833_; 
v___x_833_ = lean_nat_dec_eq(v_snd_826_, v_snd_828_);
if (v___x_833_ == 0)
{
v_x_820_ = v_tail_824_;
goto _start;
}
else
{
lean_object* v___x_835_; 
lean_inc(v_value_823_);
v___x_835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_835_, 0, v_value_823_);
return v___x_835_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__0_spec__0___redArg___boxed(lean_object* v_a_836_, lean_object* v_x_837_){
_start:
{
lean_object* v_res_838_; 
v_res_838_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__0_spec__0___redArg(v_a_836_, v_x_837_);
lean_dec(v_x_837_);
lean_dec_ref(v_a_836_);
return v_res_838_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__0___redArg(lean_object* v_m_839_, lean_object* v_a_840_){
_start:
{
lean_object* v_buckets_841_; lean_object* v_fst_842_; lean_object* v_snd_843_; lean_object* v___x_844_; size_t v___x_845_; size_t v___x_846_; size_t v___x_847_; uint64_t v___x_848_; uint64_t v___x_849_; uint64_t v___x_850_; uint64_t v___x_851_; uint64_t v___x_852_; uint64_t v_fold_853_; uint64_t v___x_854_; uint64_t v___x_855_; uint64_t v___x_856_; size_t v___x_857_; size_t v___x_858_; size_t v___x_859_; size_t v___x_860_; size_t v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; 
v_buckets_841_ = lean_ctor_get(v_m_839_, 1);
v_fst_842_ = lean_ctor_get(v_a_840_, 0);
v_snd_843_ = lean_ctor_get(v_a_840_, 1);
v___x_844_ = lean_array_get_size(v_buckets_841_);
v___x_845_ = lean_ptr_addr(v_fst_842_);
v___x_846_ = ((size_t)3ULL);
v___x_847_ = lean_usize_shift_right(v___x_845_, v___x_846_);
v___x_848_ = lean_usize_to_uint64(v___x_847_);
v___x_849_ = lean_uint64_of_nat(v_snd_843_);
v___x_850_ = lean_uint64_mix_hash(v___x_848_, v___x_849_);
v___x_851_ = 32ULL;
v___x_852_ = lean_uint64_shift_right(v___x_850_, v___x_851_);
v_fold_853_ = lean_uint64_xor(v___x_850_, v___x_852_);
v___x_854_ = 16ULL;
v___x_855_ = lean_uint64_shift_right(v_fold_853_, v___x_854_);
v___x_856_ = lean_uint64_xor(v_fold_853_, v___x_855_);
v___x_857_ = lean_uint64_to_usize(v___x_856_);
v___x_858_ = lean_usize_of_nat(v___x_844_);
v___x_859_ = ((size_t)1ULL);
v___x_860_ = lean_usize_sub(v___x_858_, v___x_859_);
v___x_861_ = lean_usize_land(v___x_857_, v___x_860_);
v___x_862_ = lean_array_uget_borrowed(v_buckets_841_, v___x_861_);
v___x_863_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__0_spec__0___redArg(v_a_840_, v___x_862_);
return v___x_863_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__0___redArg___boxed(lean_object* v_m_864_, lean_object* v_a_865_){
_start:
{
lean_object* v_res_866_; 
v_res_866_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__0___redArg(v_m_864_, v_a_865_);
lean_dec_ref(v_a_865_);
lean_dec_ref(v_m_864_);
return v_res_866_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached___redArg(lean_object* v_rhs_867_, lean_object* v_op_868_, lean_object* v_a_869_, lean_object* v_a_870_, lean_object* v_a_871_, lean_object* v_a_872_, lean_object* v_a_873_, lean_object* v_a_874_, lean_object* v_a_875_){
_start:
{
lean_object* v_numConst_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v_key_880_; lean_object* v___x_881_; lean_object* v_latticeBackwardRuleCache_882_; lean_object* v___x_883_; 
v_numConst_877_ = lean_ctor_get(v_op_868_, 1);
v___x_878_ = l_Lean_Expr_getAppPrefix(v_rhs_867_, v_numConst_877_);
v___x_879_ = l_Lean_Expr_getAppNumArgs(v_rhs_867_);
v_key_880_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_key_880_, 0, v___x_878_);
lean_ctor_set(v_key_880_, 1, v___x_879_);
v___x_881_ = lean_st_ref_get(v_a_869_);
v_latticeBackwardRuleCache_882_ = lean_ctor_get(v___x_881_, 2);
lean_inc_ref(v_latticeBackwardRuleCache_882_);
lean_dec(v___x_881_);
v___x_883_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__0___redArg(v_latticeBackwardRuleCache_882_, v_key_880_);
lean_dec_ref(v_latticeBackwardRuleCache_882_);
if (lean_obj_tag(v___x_883_) == 1)
{
lean_object* v_val_884_; lean_object* v___x_886_; uint8_t v_isShared_887_; uint8_t v_isSharedCheck_891_; 
lean_dec_ref_known(v_key_880_, 2);
lean_dec_ref(v_op_868_);
lean_dec_ref(v_rhs_867_);
v_val_884_ = lean_ctor_get(v___x_883_, 0);
v_isSharedCheck_891_ = !lean_is_exclusive(v___x_883_);
if (v_isSharedCheck_891_ == 0)
{
v___x_886_ = v___x_883_;
v_isShared_887_ = v_isSharedCheck_891_;
goto v_resetjp_885_;
}
else
{
lean_inc(v_val_884_);
lean_dec(v___x_883_);
v___x_886_ = lean_box(0);
v_isShared_887_ = v_isSharedCheck_891_;
goto v_resetjp_885_;
}
v_resetjp_885_:
{
lean_object* v___x_889_; 
if (v_isShared_887_ == 0)
{
lean_ctor_set_tag(v___x_886_, 0);
v___x_889_ = v___x_886_;
goto v_reusejp_888_;
}
else
{
lean_object* v_reuseFailAlloc_890_; 
v_reuseFailAlloc_890_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_890_, 0, v_val_884_);
v___x_889_ = v_reuseFailAlloc_890_;
goto v_reusejp_888_;
}
v_reusejp_888_:
{
return v___x_889_;
}
}
}
else
{
lean_object* v___x_892_; 
lean_dec(v___x_883_);
v___x_892_ = l_Lean_Elab_Tactic_VCGen_mkLatticeOpRule(v_rhs_867_, v_op_868_, v_a_870_, v_a_871_, v_a_872_, v_a_873_, v_a_874_, v_a_875_);
if (lean_obj_tag(v___x_892_) == 0)
{
lean_object* v_a_893_; lean_object* v___x_894_; 
v_a_893_ = lean_ctor_get(v___x_892_, 0);
lean_inc(v_a_893_);
lean_dec_ref_known(v___x_892_, 1);
v___x_894_ = l_Lean_Meta_Sym_BackwardRule_shareCommon(v_a_893_, v_a_870_, v_a_871_, v_a_872_, v_a_873_, v_a_874_, v_a_875_);
if (lean_obj_tag(v___x_894_) == 0)
{
lean_object* v_a_895_; lean_object* v___x_897_; uint8_t v_isShared_898_; uint8_t v_isSharedCheck_922_; 
v_a_895_ = lean_ctor_get(v___x_894_, 0);
v_isSharedCheck_922_ = !lean_is_exclusive(v___x_894_);
if (v_isSharedCheck_922_ == 0)
{
v___x_897_ = v___x_894_;
v_isShared_898_ = v_isSharedCheck_922_;
goto v_resetjp_896_;
}
else
{
lean_inc(v_a_895_);
lean_dec(v___x_894_);
v___x_897_ = lean_box(0);
v_isShared_898_ = v_isSharedCheck_922_;
goto v_resetjp_896_;
}
v_resetjp_896_:
{
lean_object* v___x_899_; lean_object* v_specBackwardRuleCache_900_; lean_object* v_splitBackwardRuleCache_901_; lean_object* v_latticeBackwardRuleCache_902_; lean_object* v_frameBackwardRuleCache_903_; lean_object* v_frameDB_904_; lean_object* v_invariants_905_; lean_object* v_vcs_906_; lean_object* v_simpState_907_; lean_object* v_fuel_908_; lean_object* v_inlineHandledInvariants_909_; lean_object* v___x_911_; uint8_t v_isShared_912_; uint8_t v_isSharedCheck_921_; 
v___x_899_ = lean_st_ref_take(v_a_869_);
v_specBackwardRuleCache_900_ = lean_ctor_get(v___x_899_, 0);
v_splitBackwardRuleCache_901_ = lean_ctor_get(v___x_899_, 1);
v_latticeBackwardRuleCache_902_ = lean_ctor_get(v___x_899_, 2);
v_frameBackwardRuleCache_903_ = lean_ctor_get(v___x_899_, 3);
v_frameDB_904_ = lean_ctor_get(v___x_899_, 4);
v_invariants_905_ = lean_ctor_get(v___x_899_, 5);
v_vcs_906_ = lean_ctor_get(v___x_899_, 6);
v_simpState_907_ = lean_ctor_get(v___x_899_, 7);
v_fuel_908_ = lean_ctor_get(v___x_899_, 8);
v_inlineHandledInvariants_909_ = lean_ctor_get(v___x_899_, 9);
v_isSharedCheck_921_ = !lean_is_exclusive(v___x_899_);
if (v_isSharedCheck_921_ == 0)
{
v___x_911_ = v___x_899_;
v_isShared_912_ = v_isSharedCheck_921_;
goto v_resetjp_910_;
}
else
{
lean_inc(v_inlineHandledInvariants_909_);
lean_inc(v_fuel_908_);
lean_inc(v_simpState_907_);
lean_inc(v_vcs_906_);
lean_inc(v_invariants_905_);
lean_inc(v_frameDB_904_);
lean_inc(v_frameBackwardRuleCache_903_);
lean_inc(v_latticeBackwardRuleCache_902_);
lean_inc(v_splitBackwardRuleCache_901_);
lean_inc(v_specBackwardRuleCache_900_);
lean_dec(v___x_899_);
v___x_911_ = lean_box(0);
v_isShared_912_ = v_isSharedCheck_921_;
goto v_resetjp_910_;
}
v_resetjp_910_:
{
lean_object* v___x_913_; lean_object* v___x_915_; 
lean_inc(v_a_895_);
v___x_913_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1___redArg(v_latticeBackwardRuleCache_902_, v_key_880_, v_a_895_);
if (v_isShared_912_ == 0)
{
lean_ctor_set(v___x_911_, 2, v___x_913_);
v___x_915_ = v___x_911_;
goto v_reusejp_914_;
}
else
{
lean_object* v_reuseFailAlloc_920_; 
v_reuseFailAlloc_920_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_920_, 0, v_specBackwardRuleCache_900_);
lean_ctor_set(v_reuseFailAlloc_920_, 1, v_splitBackwardRuleCache_901_);
lean_ctor_set(v_reuseFailAlloc_920_, 2, v___x_913_);
lean_ctor_set(v_reuseFailAlloc_920_, 3, v_frameBackwardRuleCache_903_);
lean_ctor_set(v_reuseFailAlloc_920_, 4, v_frameDB_904_);
lean_ctor_set(v_reuseFailAlloc_920_, 5, v_invariants_905_);
lean_ctor_set(v_reuseFailAlloc_920_, 6, v_vcs_906_);
lean_ctor_set(v_reuseFailAlloc_920_, 7, v_simpState_907_);
lean_ctor_set(v_reuseFailAlloc_920_, 8, v_fuel_908_);
lean_ctor_set(v_reuseFailAlloc_920_, 9, v_inlineHandledInvariants_909_);
v___x_915_ = v_reuseFailAlloc_920_;
goto v_reusejp_914_;
}
v_reusejp_914_:
{
lean_object* v___x_916_; lean_object* v___x_918_; 
v___x_916_ = lean_st_ref_put(v_a_869_, v___x_915_);
if (v_isShared_898_ == 0)
{
v___x_918_ = v___x_897_;
goto v_reusejp_917_;
}
else
{
lean_object* v_reuseFailAlloc_919_; 
v_reuseFailAlloc_919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_919_, 0, v_a_895_);
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
else
{
lean_dec_ref_known(v_key_880_, 2);
return v___x_894_;
}
}
else
{
lean_dec_ref_known(v_key_880_, 2);
return v___x_892_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached___redArg___boxed(lean_object* v_rhs_923_, lean_object* v_op_924_, lean_object* v_a_925_, lean_object* v_a_926_, lean_object* v_a_927_, lean_object* v_a_928_, lean_object* v_a_929_, lean_object* v_a_930_, lean_object* v_a_931_, lean_object* v_a_932_){
_start:
{
lean_object* v_res_933_; 
v_res_933_ = l_Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached___redArg(v_rhs_923_, v_op_924_, v_a_925_, v_a_926_, v_a_927_, v_a_928_, v_a_929_, v_a_930_, v_a_931_);
lean_dec(v_a_931_);
lean_dec_ref(v_a_930_);
lean_dec(v_a_929_);
lean_dec_ref(v_a_928_);
lean_dec(v_a_927_);
lean_dec_ref(v_a_926_);
lean_dec(v_a_925_);
return v_res_933_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached(lean_object* v_rhs_934_, lean_object* v_op_935_, lean_object* v_a_936_, lean_object* v_a_937_, lean_object* v_a_938_, lean_object* v_a_939_, lean_object* v_a_940_, lean_object* v_a_941_, lean_object* v_a_942_, lean_object* v_a_943_, lean_object* v_a_944_, lean_object* v_a_945_, lean_object* v_a_946_){
_start:
{
lean_object* v___x_948_; 
v___x_948_ = l_Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached___redArg(v_rhs_934_, v_op_935_, v_a_937_, v_a_941_, v_a_942_, v_a_943_, v_a_944_, v_a_945_, v_a_946_);
return v___x_948_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached___boxed(lean_object* v_rhs_949_, lean_object* v_op_950_, lean_object* v_a_951_, lean_object* v_a_952_, lean_object* v_a_953_, lean_object* v_a_954_, lean_object* v_a_955_, lean_object* v_a_956_, lean_object* v_a_957_, lean_object* v_a_958_, lean_object* v_a_959_, lean_object* v_a_960_, lean_object* v_a_961_, lean_object* v_a_962_){
_start:
{
lean_object* v_res_963_; 
v_res_963_ = l_Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached(v_rhs_949_, v_op_950_, v_a_951_, v_a_952_, v_a_953_, v_a_954_, v_a_955_, v_a_956_, v_a_957_, v_a_958_, v_a_959_, v_a_960_, v_a_961_);
lean_dec(v_a_961_);
lean_dec_ref(v_a_960_);
lean_dec(v_a_959_);
lean_dec_ref(v_a_958_);
lean_dec(v_a_957_);
lean_dec_ref(v_a_956_);
lean_dec(v_a_955_);
lean_dec_ref(v_a_954_);
lean_dec(v_a_953_);
lean_dec(v_a_952_);
lean_dec_ref(v_a_951_);
return v_res_963_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__0(lean_object* v_00_u03b2_964_, lean_object* v_m_965_, lean_object* v_a_966_){
_start:
{
lean_object* v___x_967_; 
v___x_967_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__0___redArg(v_m_965_, v_a_966_);
return v___x_967_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__0___boxed(lean_object* v_00_u03b2_968_, lean_object* v_m_969_, lean_object* v_a_970_){
_start:
{
lean_object* v_res_971_; 
v_res_971_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__0(v_00_u03b2_968_, v_m_969_, v_a_970_);
lean_dec_ref(v_a_970_);
lean_dec_ref(v_m_969_);
return v_res_971_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1(lean_object* v_00_u03b2_972_, lean_object* v_m_973_, lean_object* v_a_974_, lean_object* v_b_975_){
_start:
{
lean_object* v___x_976_; 
v___x_976_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1___redArg(v_m_973_, v_a_974_, v_b_975_);
return v___x_976_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__0_spec__0(lean_object* v_00_u03b2_977_, lean_object* v_a_978_, lean_object* v_x_979_){
_start:
{
lean_object* v___x_980_; 
v___x_980_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__0_spec__0___redArg(v_a_978_, v_x_979_);
return v___x_980_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__0_spec__0___boxed(lean_object* v_00_u03b2_981_, lean_object* v_a_982_, lean_object* v_x_983_){
_start:
{
lean_object* v_res_984_; 
v_res_984_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__0_spec__0(v_00_u03b2_981_, v_a_982_, v_x_983_);
lean_dec(v_x_983_);
lean_dec_ref(v_a_982_);
return v_res_984_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1_spec__2(lean_object* v_00_u03b2_985_, lean_object* v_a_986_, lean_object* v_x_987_){
_start:
{
uint8_t v___x_988_; 
v___x_988_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1_spec__2___redArg(v_a_986_, v_x_987_);
return v___x_988_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1_spec__2___boxed(lean_object* v_00_u03b2_989_, lean_object* v_a_990_, lean_object* v_x_991_){
_start:
{
uint8_t v_res_992_; lean_object* v_r_993_; 
v_res_992_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1_spec__2(v_00_u03b2_989_, v_a_990_, v_x_991_);
lean_dec(v_x_991_);
lean_dec_ref(v_a_990_);
v_r_993_ = lean_box(v_res_992_);
return v_r_993_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1_spec__3(lean_object* v_00_u03b2_994_, lean_object* v_data_995_){
_start:
{
lean_object* v___x_996_; 
v___x_996_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1_spec__3___redArg(v_data_995_);
return v___x_996_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1_spec__4(lean_object* v_00_u03b2_997_, lean_object* v_a_998_, lean_object* v_b_999_, lean_object* v_x_1000_){
_start:
{
lean_object* v___x_1001_; 
v___x_1001_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1_spec__4___redArg(v_a_998_, v_b_999_, v_x_1000_);
return v___x_1001_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1_spec__3_spec__4(lean_object* v_00_u03b2_1002_, lean_object* v_i_1003_, lean_object* v_source_1004_, lean_object* v_target_1005_){
_start:
{
lean_object* v___x_1006_; 
v___x_1006_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1_spec__3_spec__4___redArg(v_i_1003_, v_source_1004_, v_target_1005_);
return v___x_1006_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1_spec__3_spec__4_spec__5(lean_object* v_00_u03b2_1007_, lean_object* v_x_1008_, lean_object* v_x_1009_){
_start:
{
lean_object* v___x_1010_; 
v___x_1010_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1_spec__3_spec__4_spec__5___redArg(v_x_1008_, v_x_1009_);
return v___x_1010_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_mkFrameBackwardRuleCached___redArg(lean_object* v_fp_1011_, lean_object* v_info_1012_, lean_object* v_a_1013_, lean_object* v_a_1014_, lean_object* v_a_1015_, lean_object* v_a_1016_, lean_object* v_a_1017_, lean_object* v_a_1018_, lean_object* v_a_1019_){
_start:
{
lean_object* v_excessArgs_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v_key_1024_; lean_object* v___x_1025_; lean_object* v_frameBackwardRuleCache_1026_; lean_object* v___x_1027_; 
v_excessArgs_1021_ = lean_ctor_get(v_info_1012_, 3);
v___x_1022_ = l_Lean_Elab_Tactic_VCGen_WPApp_instWP(v_info_1012_);
v___x_1023_ = lean_array_get_size(v_excessArgs_1021_);
v_key_1024_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_key_1024_, 0, v___x_1022_);
lean_ctor_set(v_key_1024_, 1, v___x_1023_);
v___x_1025_ = lean_st_ref_get(v_a_1013_);
v_frameBackwardRuleCache_1026_ = lean_ctor_get(v___x_1025_, 3);
lean_inc_ref(v_frameBackwardRuleCache_1026_);
lean_dec(v___x_1025_);
v___x_1027_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__0___redArg(v_frameBackwardRuleCache_1026_, v_key_1024_);
lean_dec_ref(v_frameBackwardRuleCache_1026_);
if (lean_obj_tag(v___x_1027_) == 1)
{
lean_object* v_val_1028_; lean_object* v___x_1030_; uint8_t v_isShared_1031_; uint8_t v_isSharedCheck_1035_; 
lean_dec_ref_known(v_key_1024_, 2);
lean_dec_ref(v_info_1012_);
lean_dec_ref(v_fp_1011_);
v_val_1028_ = lean_ctor_get(v___x_1027_, 0);
v_isSharedCheck_1035_ = !lean_is_exclusive(v___x_1027_);
if (v_isSharedCheck_1035_ == 0)
{
v___x_1030_ = v___x_1027_;
v_isShared_1031_ = v_isSharedCheck_1035_;
goto v_resetjp_1029_;
}
else
{
lean_inc(v_val_1028_);
lean_dec(v___x_1027_);
v___x_1030_ = lean_box(0);
v_isShared_1031_ = v_isSharedCheck_1035_;
goto v_resetjp_1029_;
}
v_resetjp_1029_:
{
lean_object* v___x_1033_; 
if (v_isShared_1031_ == 0)
{
lean_ctor_set_tag(v___x_1030_, 0);
v___x_1033_ = v___x_1030_;
goto v_reusejp_1032_;
}
else
{
lean_object* v_reuseFailAlloc_1034_; 
v_reuseFailAlloc_1034_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1034_, 0, v_val_1028_);
v___x_1033_ = v_reuseFailAlloc_1034_;
goto v_reusejp_1032_;
}
v_reusejp_1032_:
{
return v___x_1033_;
}
}
}
else
{
lean_object* v___x_1036_; 
lean_dec(v___x_1027_);
v___x_1036_ = l_Lean_Elab_Tactic_VCGen_mkFrameBackwardRule(v_fp_1011_, v_info_1012_, v_a_1016_, v_a_1017_, v_a_1018_, v_a_1019_);
if (lean_obj_tag(v___x_1036_) == 0)
{
lean_object* v_a_1037_; lean_object* v_rule_1038_; lean_object* v_splitVCIdx_1039_; lean_object* v_frameIdx_1040_; lean_object* v___x_1042_; uint8_t v_isShared_1043_; uint8_t v_isSharedCheck_1084_; 
v_a_1037_ = lean_ctor_get(v___x_1036_, 0);
lean_inc(v_a_1037_);
lean_dec_ref_known(v___x_1036_, 1);
v_rule_1038_ = lean_ctor_get(v_a_1037_, 0);
v_splitVCIdx_1039_ = lean_ctor_get(v_a_1037_, 1);
v_frameIdx_1040_ = lean_ctor_get(v_a_1037_, 2);
v_isSharedCheck_1084_ = !lean_is_exclusive(v_a_1037_);
if (v_isSharedCheck_1084_ == 0)
{
v___x_1042_ = v_a_1037_;
v_isShared_1043_ = v_isSharedCheck_1084_;
goto v_resetjp_1041_;
}
else
{
lean_inc(v_frameIdx_1040_);
lean_inc(v_splitVCIdx_1039_);
lean_inc(v_rule_1038_);
lean_dec(v_a_1037_);
v___x_1042_ = lean_box(0);
v_isShared_1043_ = v_isSharedCheck_1084_;
goto v_resetjp_1041_;
}
v_resetjp_1041_:
{
lean_object* v___x_1044_; 
v___x_1044_ = l_Lean_Meta_Sym_BackwardRule_shareCommon(v_rule_1038_, v_a_1014_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_, v_a_1019_);
if (lean_obj_tag(v___x_1044_) == 0)
{
lean_object* v_a_1045_; lean_object* v___x_1047_; uint8_t v_isShared_1048_; uint8_t v_isSharedCheck_1075_; 
v_a_1045_ = lean_ctor_get(v___x_1044_, 0);
v_isSharedCheck_1075_ = !lean_is_exclusive(v___x_1044_);
if (v_isSharedCheck_1075_ == 0)
{
v___x_1047_ = v___x_1044_;
v_isShared_1048_ = v_isSharedCheck_1075_;
goto v_resetjp_1046_;
}
else
{
lean_inc(v_a_1045_);
lean_dec(v___x_1044_);
v___x_1047_ = lean_box(0);
v_isShared_1048_ = v_isSharedCheck_1075_;
goto v_resetjp_1046_;
}
v_resetjp_1046_:
{
lean_object* v___x_1050_; 
if (v_isShared_1043_ == 0)
{
lean_ctor_set(v___x_1042_, 0, v_a_1045_);
v___x_1050_ = v___x_1042_;
goto v_reusejp_1049_;
}
else
{
lean_object* v_reuseFailAlloc_1074_; 
v_reuseFailAlloc_1074_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1074_, 0, v_a_1045_);
lean_ctor_set(v_reuseFailAlloc_1074_, 1, v_splitVCIdx_1039_);
lean_ctor_set(v_reuseFailAlloc_1074_, 2, v_frameIdx_1040_);
v___x_1050_ = v_reuseFailAlloc_1074_;
goto v_reusejp_1049_;
}
v_reusejp_1049_:
{
lean_object* v___x_1051_; lean_object* v_specBackwardRuleCache_1052_; lean_object* v_splitBackwardRuleCache_1053_; lean_object* v_latticeBackwardRuleCache_1054_; lean_object* v_frameBackwardRuleCache_1055_; lean_object* v_frameDB_1056_; lean_object* v_invariants_1057_; lean_object* v_vcs_1058_; lean_object* v_simpState_1059_; lean_object* v_fuel_1060_; lean_object* v_inlineHandledInvariants_1061_; lean_object* v___x_1063_; uint8_t v_isShared_1064_; uint8_t v_isSharedCheck_1073_; 
v___x_1051_ = lean_st_ref_take(v_a_1013_);
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
v_isSharedCheck_1073_ = !lean_is_exclusive(v___x_1051_);
if (v_isSharedCheck_1073_ == 0)
{
v___x_1063_ = v___x_1051_;
v_isShared_1064_ = v_isSharedCheck_1073_;
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
v_isShared_1064_ = v_isSharedCheck_1073_;
goto v_resetjp_1062_;
}
v_resetjp_1062_:
{
lean_object* v___x_1065_; lean_object* v___x_1067_; 
lean_inc_ref(v___x_1050_);
v___x_1065_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1___redArg(v_frameBackwardRuleCache_1055_, v_key_1024_, v___x_1050_);
if (v_isShared_1064_ == 0)
{
lean_ctor_set(v___x_1063_, 3, v___x_1065_);
v___x_1067_ = v___x_1063_;
goto v_reusejp_1066_;
}
else
{
lean_object* v_reuseFailAlloc_1072_; 
v_reuseFailAlloc_1072_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1072_, 0, v_specBackwardRuleCache_1052_);
lean_ctor_set(v_reuseFailAlloc_1072_, 1, v_splitBackwardRuleCache_1053_);
lean_ctor_set(v_reuseFailAlloc_1072_, 2, v_latticeBackwardRuleCache_1054_);
lean_ctor_set(v_reuseFailAlloc_1072_, 3, v___x_1065_);
lean_ctor_set(v_reuseFailAlloc_1072_, 4, v_frameDB_1056_);
lean_ctor_set(v_reuseFailAlloc_1072_, 5, v_invariants_1057_);
lean_ctor_set(v_reuseFailAlloc_1072_, 6, v_vcs_1058_);
lean_ctor_set(v_reuseFailAlloc_1072_, 7, v_simpState_1059_);
lean_ctor_set(v_reuseFailAlloc_1072_, 8, v_fuel_1060_);
lean_ctor_set(v_reuseFailAlloc_1072_, 9, v_inlineHandledInvariants_1061_);
v___x_1067_ = v_reuseFailAlloc_1072_;
goto v_reusejp_1066_;
}
v_reusejp_1066_:
{
lean_object* v___x_1068_; lean_object* v___x_1070_; 
v___x_1068_ = lean_st_ref_put(v_a_1013_, v___x_1067_);
if (v_isShared_1048_ == 0)
{
lean_ctor_set(v___x_1047_, 0, v___x_1050_);
v___x_1070_ = v___x_1047_;
goto v_reusejp_1069_;
}
else
{
lean_object* v_reuseFailAlloc_1071_; 
v_reuseFailAlloc_1071_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1071_, 0, v___x_1050_);
v___x_1070_ = v_reuseFailAlloc_1071_;
goto v_reusejp_1069_;
}
v_reusejp_1069_:
{
return v___x_1070_;
}
}
}
}
}
}
else
{
lean_object* v_a_1076_; lean_object* v___x_1078_; uint8_t v_isShared_1079_; uint8_t v_isSharedCheck_1083_; 
lean_del_object(v___x_1042_);
lean_dec(v_frameIdx_1040_);
lean_dec(v_splitVCIdx_1039_);
lean_dec_ref_known(v_key_1024_, 2);
v_a_1076_ = lean_ctor_get(v___x_1044_, 0);
v_isSharedCheck_1083_ = !lean_is_exclusive(v___x_1044_);
if (v_isSharedCheck_1083_ == 0)
{
v___x_1078_ = v___x_1044_;
v_isShared_1079_ = v_isSharedCheck_1083_;
goto v_resetjp_1077_;
}
else
{
lean_inc(v_a_1076_);
lean_dec(v___x_1044_);
v___x_1078_ = lean_box(0);
v_isShared_1079_ = v_isSharedCheck_1083_;
goto v_resetjp_1077_;
}
v_resetjp_1077_:
{
lean_object* v___x_1081_; 
if (v_isShared_1079_ == 0)
{
v___x_1081_ = v___x_1078_;
goto v_reusejp_1080_;
}
else
{
lean_object* v_reuseFailAlloc_1082_; 
v_reuseFailAlloc_1082_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1082_, 0, v_a_1076_);
v___x_1081_ = v_reuseFailAlloc_1082_;
goto v_reusejp_1080_;
}
v_reusejp_1080_:
{
return v___x_1081_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_key_1024_, 2);
return v___x_1036_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_mkFrameBackwardRuleCached___redArg___boxed(lean_object* v_fp_1085_, lean_object* v_info_1086_, lean_object* v_a_1087_, lean_object* v_a_1088_, lean_object* v_a_1089_, lean_object* v_a_1090_, lean_object* v_a_1091_, lean_object* v_a_1092_, lean_object* v_a_1093_, lean_object* v_a_1094_){
_start:
{
lean_object* v_res_1095_; 
v_res_1095_ = l_Lean_Elab_Tactic_VCGen_mkFrameBackwardRuleCached___redArg(v_fp_1085_, v_info_1086_, v_a_1087_, v_a_1088_, v_a_1089_, v_a_1090_, v_a_1091_, v_a_1092_, v_a_1093_);
lean_dec(v_a_1093_);
lean_dec_ref(v_a_1092_);
lean_dec(v_a_1091_);
lean_dec_ref(v_a_1090_);
lean_dec(v_a_1089_);
lean_dec_ref(v_a_1088_);
lean_dec(v_a_1087_);
return v_res_1095_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_mkFrameBackwardRuleCached(lean_object* v_fp_1096_, lean_object* v_info_1097_, lean_object* v_a_1098_, lean_object* v_a_1099_, lean_object* v_a_1100_, lean_object* v_a_1101_, lean_object* v_a_1102_, lean_object* v_a_1103_, lean_object* v_a_1104_, lean_object* v_a_1105_, lean_object* v_a_1106_, lean_object* v_a_1107_, lean_object* v_a_1108_){
_start:
{
lean_object* v___x_1110_; 
v___x_1110_ = l_Lean_Elab_Tactic_VCGen_mkFrameBackwardRuleCached___redArg(v_fp_1096_, v_info_1097_, v_a_1099_, v_a_1103_, v_a_1104_, v_a_1105_, v_a_1106_, v_a_1107_, v_a_1108_);
return v___x_1110_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_mkFrameBackwardRuleCached___boxed(lean_object* v_fp_1111_, lean_object* v_info_1112_, lean_object* v_a_1113_, lean_object* v_a_1114_, lean_object* v_a_1115_, lean_object* v_a_1116_, lean_object* v_a_1117_, lean_object* v_a_1118_, lean_object* v_a_1119_, lean_object* v_a_1120_, lean_object* v_a_1121_, lean_object* v_a_1122_, lean_object* v_a_1123_, lean_object* v_a_1124_){
_start:
{
lean_object* v_res_1125_; 
v_res_1125_ = l_Lean_Elab_Tactic_VCGen_mkFrameBackwardRuleCached(v_fp_1111_, v_info_1112_, v_a_1113_, v_a_1114_, v_a_1115_, v_a_1116_, v_a_1117_, v_a_1118_, v_a_1119_, v_a_1120_, v_a_1121_, v_a_1122_, v_a_1123_);
lean_dec(v_a_1123_);
lean_dec_ref(v_a_1122_);
lean_dec(v_a_1121_);
lean_dec_ref(v_a_1120_);
lean_dec(v_a_1119_);
lean_dec_ref(v_a_1118_);
lean_dec(v_a_1117_);
lean_dec_ref(v_a_1116_);
lean_dec(v_a_1115_);
lean_dec(v_a_1114_);
lean_dec_ref(v_a_1113_);
return v_res_1125_;
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
