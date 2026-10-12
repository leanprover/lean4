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
lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__1___redArg___lam__0(lean_object* v_k_1_, lean_object* v___y_2_, lean_object* v___y_3_, lean_object* v___y_4_, lean_object* v___y_5_, lean_object* v___y_6_, lean_object* v___y_7_, lean_object* v___y_8_, lean_object* v___y_9_, lean_object* v___y_10_, lean_object* v___y_11_, lean_object* v___y_12_){
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
LEAN_EXPORT void l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__1___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_1_ = stack[0].m_obj;
lean_object* v___y_2_ = stack[1].m_obj;
lean_object* v___y_3_ = stack[2].m_obj;
lean_object* v___y_4_ = stack[3].m_obj;
lean_object* v___y_5_ = stack[4].m_obj;
lean_object* v___y_6_ = stack[5].m_obj;
lean_object* v___y_7_ = stack[6].m_obj;
lean_object* v___y_8_ = stack[7].m_obj;
lean_object* v___y_9_ = stack[8].m_obj;
lean_object* v___y_10_ = stack[9].m_obj;
lean_object* v___y_11_ = stack[10].m_obj;
lean_object* v___y_12_ = stack[11].m_obj;
lean_object* v_res_15_;
v_res_15_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__1___redArg___lam__0(v_k_1_, v___y_2_, v___y_3_, v___y_4_, v___y_5_, v___y_6_, v___y_7_, v___y_8_, v___y_9_, v___y_10_, v___y_11_, v___y_12_);
stack->m_obj
 = v_res_15_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__1___redArg___lam__0___boxed(lean_object* v_k_16_, lean_object* v___y_17_, lean_object* v___y_18_, lean_object* v___y_19_, lean_object* v___y_20_, lean_object* v___y_21_, lean_object* v___y_22_, lean_object* v___y_23_, lean_object* v___y_24_, lean_object* v___y_25_, lean_object* v___y_26_, lean_object* v___y_27_, lean_object* v___y_28_){
_start:
{
lean_object* v_res_29_; 
v_res_29_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__1___redArg___lam__0(v_k_16_, v___y_17_, v___y_18_, v___y_19_, v___y_20_, v___y_21_, v___y_22_, v___y_23_, v___y_24_, v___y_25_, v___y_26_, v___y_27_);
lean_dec(v___y_23_);
lean_dec_ref(v___y_22_);
lean_dec(v___y_21_);
lean_dec_ref(v___y_20_);
lean_dec(v___y_19_);
lean_dec(v___y_18_);
lean_dec_ref(v___y_17_);
return v_res_29_;
}
}
lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__1___redArg(lean_object* v_k_30_, uint8_t v_allowLevelAssignments_31_, lean_object* v___y_32_, lean_object* v___y_33_, lean_object* v___y_34_, lean_object* v___y_35_, lean_object* v___y_36_, lean_object* v___y_37_, lean_object* v___y_38_, lean_object* v___y_39_, lean_object* v___y_40_, lean_object* v___y_41_, lean_object* v___y_42_){
_start:
{
lean_object* v___f_44_; lean_object* v___x_45_; 
lean_inc(v___y_38_);
lean_inc_ref(v___y_37_);
lean_inc(v___y_36_);
lean_inc_ref(v___y_35_);
lean_inc(v___y_34_);
lean_inc(v___y_33_);
lean_inc_ref(v___y_32_);
v___f_44_ = lean_alloc_closure((void*)(l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__1___redArg___lam__0___boxed), 13, 8);
lean_closure_set(v___f_44_, 0, v_k_30_);
lean_closure_set(v___f_44_, 1, v___y_32_);
lean_closure_set(v___f_44_, 2, v___y_33_);
lean_closure_set(v___f_44_, 3, v___y_34_);
lean_closure_set(v___f_44_, 4, v___y_35_);
lean_closure_set(v___f_44_, 5, v___y_36_);
lean_closure_set(v___f_44_, 6, v___y_37_);
lean_closure_set(v___f_44_, 7, v___y_38_);
v___x_45_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_box(0), v_allowLevelAssignments_31_, v___f_44_, v___y_39_, v___y_40_, v___y_41_, v___y_42_);
if (lean_obj_tag(v___x_45_) == 0)
{
return v___x_45_;
}
else
{
lean_object* v_a_46_; lean_object* v___x_48_; uint8_t v_isShared_49_; uint8_t v_isSharedCheck_53_; 
v_a_46_ = lean_ctor_get(v___x_45_, 0);
v_isSharedCheck_53_ = !lean_is_exclusive(v___x_45_);
if (v_isSharedCheck_53_ == 0)
{
v___x_48_ = v___x_45_;
v_isShared_49_ = v_isSharedCheck_53_;
goto v_resetjp_47_;
}
else
{
lean_inc(v_a_46_);
lean_dec(v___x_45_);
v___x_48_ = lean_box(0);
v_isShared_49_ = v_isSharedCheck_53_;
goto v_resetjp_47_;
}
v_resetjp_47_:
{
lean_object* v___x_51_; 
if (v_isShared_49_ == 0)
{
v___x_51_ = v___x_48_;
goto v_reusejp_50_;
}
else
{
lean_object* v_reuseFailAlloc_52_; 
v_reuseFailAlloc_52_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_52_, 0, v_a_46_);
v___x_51_ = v_reuseFailAlloc_52_;
goto v_reusejp_50_;
}
v_reusejp_50_:
{
return v___x_51_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_30_ = stack[0].m_obj;
uint8_t v_allowLevelAssignments_31_ = stack[1].m_num;
lean_object* v___y_32_ = stack[2].m_obj;
lean_object* v___y_33_ = stack[3].m_obj;
lean_object* v___y_34_ = stack[4].m_obj;
lean_object* v___y_35_ = stack[5].m_obj;
lean_object* v___y_36_ = stack[6].m_obj;
lean_object* v___y_37_ = stack[7].m_obj;
lean_object* v___y_38_ = stack[8].m_obj;
lean_object* v___y_39_ = stack[9].m_obj;
lean_object* v___y_40_ = stack[10].m_obj;
lean_object* v___y_41_ = stack[11].m_obj;
lean_object* v___y_42_ = stack[12].m_obj;
lean_object* v_res_54_;
v_res_54_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__1___redArg(v_k_30_, v_allowLevelAssignments_31_, v___y_32_, v___y_33_, v___y_34_, v___y_35_, v___y_36_, v___y_37_, v___y_38_, v___y_39_, v___y_40_, v___y_41_, v___y_42_);
stack->m_obj
 = v_res_54_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__1___redArg___boxed(lean_object* v_k_55_, lean_object* v_allowLevelAssignments_56_, lean_object* v___y_57_, lean_object* v___y_58_, lean_object* v___y_59_, lean_object* v___y_60_, lean_object* v___y_61_, lean_object* v___y_62_, lean_object* v___y_63_, lean_object* v___y_64_, lean_object* v___y_65_, lean_object* v___y_66_, lean_object* v___y_67_, lean_object* v___y_68_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_69_; lean_object* v_res_70_; 
v_allowLevelAssignments_boxed_69_ = lean_unbox(v_allowLevelAssignments_56_);
v_res_70_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__1___redArg(v_k_55_, v_allowLevelAssignments_boxed_69_, v___y_57_, v___y_58_, v___y_59_, v___y_60_, v___y_61_, v___y_62_, v___y_63_, v___y_64_, v___y_65_, v___y_66_, v___y_67_);
lean_dec(v___y_67_);
lean_dec_ref(v___y_66_);
lean_dec(v___y_65_);
lean_dec_ref(v___y_64_);
lean_dec(v___y_63_);
lean_dec_ref(v___y_62_);
lean_dec(v___y_61_);
lean_dec_ref(v___y_60_);
lean_dec(v___y_59_);
lean_dec(v___y_58_);
lean_dec_ref(v___y_57_);
return v_res_70_;
}
}
lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__1(lean_object* v_00_u03b1_71_, lean_object* v_k_72_, uint8_t v_allowLevelAssignments_73_, lean_object* v___y_74_, lean_object* v___y_75_, lean_object* v___y_76_, lean_object* v___y_77_, lean_object* v___y_78_, lean_object* v___y_79_, lean_object* v___y_80_, lean_object* v___y_81_, lean_object* v___y_82_, lean_object* v___y_83_, lean_object* v___y_84_){
_start:
{
lean_object* v___x_86_; 
v___x_86_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__1___redArg(v_k_72_, v_allowLevelAssignments_73_, v___y_74_, v___y_75_, v___y_76_, v___y_77_, v___y_78_, v___y_79_, v___y_80_, v___y_81_, v___y_82_, v___y_83_, v___y_84_);
return v___x_86_;
}
}
LEAN_EXPORT void l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_72_ = stack[1].m_obj;
uint8_t v_allowLevelAssignments_73_ = stack[2].m_num;
lean_object* v___y_74_ = stack[3].m_obj;
lean_object* v___y_75_ = stack[4].m_obj;
lean_object* v___y_76_ = stack[5].m_obj;
lean_object* v___y_77_ = stack[6].m_obj;
lean_object* v___y_78_ = stack[7].m_obj;
lean_object* v___y_79_ = stack[8].m_obj;
lean_object* v___y_80_ = stack[9].m_obj;
lean_object* v___y_81_ = stack[10].m_obj;
lean_object* v___y_82_ = stack[11].m_obj;
lean_object* v___y_83_ = stack[12].m_obj;
lean_object* v___y_84_ = stack[13].m_obj;
lean_object* v_res_87_;
v_res_87_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__1(lean_box(0), v_k_72_, v_allowLevelAssignments_73_, v___y_74_, v___y_75_, v___y_76_, v___y_77_, v___y_78_, v___y_79_, v___y_80_, v___y_81_, v___y_82_, v___y_83_, v___y_84_);
stack->m_obj
 = v_res_87_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__1___boxed(lean_object* v_00_u03b1_88_, lean_object* v_k_89_, lean_object* v_allowLevelAssignments_90_, lean_object* v___y_91_, lean_object* v___y_92_, lean_object* v___y_93_, lean_object* v___y_94_, lean_object* v___y_95_, lean_object* v___y_96_, lean_object* v___y_97_, lean_object* v___y_98_, lean_object* v___y_99_, lean_object* v___y_100_, lean_object* v___y_101_, lean_object* v___y_102_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_103_; lean_object* v_res_104_; 
v_allowLevelAssignments_boxed_103_ = lean_unbox(v_allowLevelAssignments_90_);
v_res_104_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__1(v_00_u03b1_88_, v_k_89_, v_allowLevelAssignments_boxed_103_, v___y_91_, v___y_92_, v___y_93_, v___y_94_, v___y_95_, v___y_96_, v___y_97_, v___y_98_, v___y_99_, v___y_100_, v___y_101_);
lean_dec(v___y_101_);
lean_dec_ref(v___y_100_);
lean_dec(v___y_99_);
lean_dec_ref(v___y_98_);
lean_dec(v___y_97_);
lean_dec_ref(v___y_96_);
lean_dec(v___y_95_);
lean_dec_ref(v___y_94_);
lean_dec(v___y_93_);
lean_dec(v___y_92_);
lean_dec_ref(v___y_91_);
return v_res_104_;
}
}
lean_object* l_Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached___lam__0(lean_object* v_specThm_105_, lean_object* v_info_106_, lean_object* v___x_107_, lean_object* v___y_108_, lean_object* v___y_109_, lean_object* v___y_110_, lean_object* v___y_111_, lean_object* v___y_112_, lean_object* v___y_113_, lean_object* v___y_114_, lean_object* v___y_115_, lean_object* v___y_116_, lean_object* v___y_117_, lean_object* v___y_118_){
_start:
{
lean_object* v___x_120_; 
v___x_120_ = l_Lean_Elab_Tactic_VCGen_tryMkBackwardRuleFromSpec(v_specThm_105_, v_info_106_, v___x_107_, v___y_115_, v___y_116_, v___y_117_, v___y_118_);
if (lean_obj_tag(v___x_120_) == 0)
{
lean_object* v_a_121_; lean_object* v___x_123_; uint8_t v_isShared_124_; uint8_t v_isSharedCheck_129_; 
v_a_121_ = lean_ctor_get(v___x_120_, 0);
v_isSharedCheck_129_ = !lean_is_exclusive(v___x_120_);
if (v_isSharedCheck_129_ == 0)
{
v___x_123_ = v___x_120_;
v_isShared_124_ = v_isSharedCheck_129_;
goto v_resetjp_122_;
}
else
{
lean_inc(v_a_121_);
lean_dec(v___x_120_);
v___x_123_ = lean_box(0);
v_isShared_124_ = v_isSharedCheck_129_;
goto v_resetjp_122_;
}
v_resetjp_122_:
{
lean_object* v___x_125_; lean_object* v___x_127_; 
v___x_125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_125_, 0, v_a_121_);
if (v_isShared_124_ == 0)
{
lean_ctor_set(v___x_123_, 0, v___x_125_);
v___x_127_ = v___x_123_;
goto v_reusejp_126_;
}
else
{
lean_object* v_reuseFailAlloc_128_; 
v_reuseFailAlloc_128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_128_, 0, v___x_125_);
v___x_127_ = v_reuseFailAlloc_128_;
goto v_reusejp_126_;
}
v_reusejp_126_:
{
return v___x_127_;
}
}
}
else
{
lean_object* v_a_130_; lean_object* v___x_132_; uint8_t v_isShared_133_; uint8_t v_isSharedCheck_137_; 
v_a_130_ = lean_ctor_get(v___x_120_, 0);
v_isSharedCheck_137_ = !lean_is_exclusive(v___x_120_);
if (v_isSharedCheck_137_ == 0)
{
v___x_132_ = v___x_120_;
v_isShared_133_ = v_isSharedCheck_137_;
goto v_resetjp_131_;
}
else
{
lean_inc(v_a_130_);
lean_dec(v___x_120_);
v___x_132_ = lean_box(0);
v_isShared_133_ = v_isSharedCheck_137_;
goto v_resetjp_131_;
}
v_resetjp_131_:
{
lean_object* v___x_135_; 
if (v_isShared_133_ == 0)
{
v___x_135_ = v___x_132_;
goto v_reusejp_134_;
}
else
{
lean_object* v_reuseFailAlloc_136_; 
v_reuseFailAlloc_136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_136_, 0, v_a_130_);
v___x_135_ = v_reuseFailAlloc_136_;
goto v_reusejp_134_;
}
v_reusejp_134_:
{
return v___x_135_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_specThm_105_ = stack[0].m_obj;
lean_object* v_info_106_ = stack[1].m_obj;
lean_object* v___x_107_ = stack[2].m_obj;
lean_object* v___y_108_ = stack[3].m_obj;
lean_object* v___y_109_ = stack[4].m_obj;
lean_object* v___y_110_ = stack[5].m_obj;
lean_object* v___y_111_ = stack[6].m_obj;
lean_object* v___y_112_ = stack[7].m_obj;
lean_object* v___y_113_ = stack[8].m_obj;
lean_object* v___y_114_ = stack[9].m_obj;
lean_object* v___y_115_ = stack[10].m_obj;
lean_object* v___y_116_ = stack[11].m_obj;
lean_object* v___y_117_ = stack[12].m_obj;
lean_object* v___y_118_ = stack[13].m_obj;
lean_object* v_res_138_;
v_res_138_ = l_Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached___lam__0(v_specThm_105_, v_info_106_, v___x_107_, v___y_108_, v___y_109_, v___y_110_, v___y_111_, v___y_112_, v___y_113_, v___y_114_, v___y_115_, v___y_116_, v___y_117_, v___y_118_);
stack->m_obj
 = v_res_138_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached___lam__0___boxed(lean_object* v_specThm_139_, lean_object* v_info_140_, lean_object* v___x_141_, lean_object* v___y_142_, lean_object* v___y_143_, lean_object* v___y_144_, lean_object* v___y_145_, lean_object* v___y_146_, lean_object* v___y_147_, lean_object* v___y_148_, lean_object* v___y_149_, lean_object* v___y_150_, lean_object* v___y_151_, lean_object* v___y_152_, lean_object* v___y_153_){
_start:
{
lean_object* v_res_154_; 
v_res_154_ = l_Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached___lam__0(v_specThm_139_, v_info_140_, v___x_141_, v___y_142_, v___y_143_, v___y_144_, v___y_145_, v___y_146_, v___y_147_, v___y_148_, v___y_149_, v___y_150_, v___y_151_, v___y_152_);
lean_dec(v___y_152_);
lean_dec_ref(v___y_151_);
lean_dec(v___y_150_);
lean_dec_ref(v___y_149_);
lean_dec(v___y_148_);
lean_dec_ref(v___y_147_);
lean_dec(v___y_146_);
lean_dec_ref(v___y_145_);
lean_dec(v___y_144_);
lean_dec(v___y_143_);
lean_dec_ref(v___y_142_);
lean_dec_ref(v_info_140_);
return v_res_154_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__3___redArg(lean_object* v_a_155_, lean_object* v_x_156_){
_start:
{
if (lean_obj_tag(v_x_156_) == 0)
{
uint8_t v___x_157_; 
v___x_157_ = 0;
return v___x_157_;
}
else
{
lean_object* v_key_158_; lean_object* v_tail_159_; uint8_t v___y_161_; lean_object* v_fst_163_; lean_object* v_snd_164_; lean_object* v_fst_165_; lean_object* v_snd_166_; uint8_t v___x_167_; 
v_key_158_ = lean_ctor_get(v_x_156_, 0);
v_tail_159_ = lean_ctor_get(v_x_156_, 2);
v_fst_163_ = lean_ctor_get(v_key_158_, 0);
v_snd_164_ = lean_ctor_get(v_key_158_, 1);
v_fst_165_ = lean_ctor_get(v_a_155_, 0);
v_snd_166_ = lean_ctor_get(v_a_155_, 1);
v___x_167_ = lean_name_eq(v_fst_163_, v_fst_165_);
if (v___x_167_ == 0)
{
v___y_161_ = v___x_167_;
goto v___jp_160_;
}
else
{
lean_object* v_fst_168_; lean_object* v_snd_169_; lean_object* v_fst_170_; lean_object* v_snd_171_; size_t v___x_172_; size_t v___x_173_; uint8_t v___x_174_; 
v_fst_168_ = lean_ctor_get(v_snd_164_, 0);
v_snd_169_ = lean_ctor_get(v_snd_164_, 1);
v_fst_170_ = lean_ctor_get(v_snd_166_, 0);
v_snd_171_ = lean_ctor_get(v_snd_166_, 1);
v___x_172_ = lean_ptr_addr(v_fst_168_);
v___x_173_ = lean_ptr_addr(v_fst_170_);
v___x_174_ = lean_usize_dec_eq(v___x_172_, v___x_173_);
if (v___x_174_ == 0)
{
v_x_156_ = v_tail_159_;
goto _start;
}
else
{
uint8_t v___x_176_; 
v___x_176_ = lean_nat_dec_eq(v_snd_169_, v_snd_171_);
v___y_161_ = v___x_176_;
goto v___jp_160_;
}
}
v___jp_160_:
{
if (v___y_161_ == 0)
{
v_x_156_ = v_tail_159_;
goto _start;
}
else
{
return v___y_161_;
}
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_155_ = stack[0].m_obj;
lean_object* v_x_156_ = stack[1].m_obj;
uint8_t v_res_177_;
v_res_177_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__3___redArg(v_a_155_, v_x_156_);
stack->m_num = v_res_177_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__3___redArg___boxed(lean_object* v_a_178_, lean_object* v_x_179_){
_start:
{
uint8_t v_res_180_; lean_object* v_r_181_; 
v_res_180_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__3___redArg(v_a_178_, v_x_179_);
lean_dec(v_x_179_);
lean_dec_ref(v_a_178_);
v_r_181_ = lean_box(v_res_180_);
return v_r_181_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__4_spec__5_spec__6___redArg(lean_object* v_x_182_, lean_object* v_x_183_){
_start:
{
if (lean_obj_tag(v_x_183_) == 0)
{
return v_x_182_;
}
else
{
lean_object* v_key_184_; lean_object* v_value_185_; lean_object* v_tail_186_; lean_object* v___x_188_; uint8_t v_isShared_189_; uint8_t v_isSharedCheck_223_; 
v_key_184_ = lean_ctor_get(v_x_183_, 0);
v_value_185_ = lean_ctor_get(v_x_183_, 1);
v_tail_186_ = lean_ctor_get(v_x_183_, 2);
v_isSharedCheck_223_ = !lean_is_exclusive(v_x_183_);
if (v_isSharedCheck_223_ == 0)
{
v___x_188_ = v_x_183_;
v_isShared_189_ = v_isSharedCheck_223_;
goto v_resetjp_187_;
}
else
{
lean_inc(v_tail_186_);
lean_inc(v_value_185_);
lean_inc(v_key_184_);
lean_dec(v_x_183_);
v___x_188_ = lean_box(0);
v_isShared_189_ = v_isSharedCheck_223_;
goto v_resetjp_187_;
}
v_resetjp_187_:
{
lean_object* v_fst_190_; lean_object* v_snd_191_; lean_object* v___x_192_; uint64_t v___y_194_; 
v_fst_190_ = lean_ctor_get(v_key_184_, 0);
v_snd_191_ = lean_ctor_get(v_key_184_, 1);
v___x_192_ = lean_array_get_size(v_x_182_);
if (lean_obj_tag(v_fst_190_) == 0)
{
uint64_t v___x_221_; 
v___x_221_ = 1723ULL;
v___y_194_ = v___x_221_;
goto v___jp_193_;
}
else
{
uint64_t v_hash_222_; 
v_hash_222_ = lean_ctor_get_uint64(v_fst_190_, sizeof(void*)*2);
v___y_194_ = v_hash_222_;
goto v___jp_193_;
}
v___jp_193_:
{
lean_object* v_fst_195_; lean_object* v_snd_196_; size_t v___x_197_; size_t v___x_198_; size_t v___x_199_; uint64_t v___x_200_; uint64_t v___x_201_; uint64_t v___x_202_; uint64_t v___x_203_; uint64_t v___x_204_; uint64_t v___x_205_; uint64_t v_fold_206_; uint64_t v___x_207_; uint64_t v___x_208_; uint64_t v___x_209_; size_t v___x_210_; size_t v___x_211_; size_t v___x_212_; size_t v___x_213_; size_t v___x_214_; lean_object* v___x_215_; lean_object* v___x_217_; 
v_fst_195_ = lean_ctor_get(v_snd_191_, 0);
v_snd_196_ = lean_ctor_get(v_snd_191_, 1);
v___x_197_ = lean_ptr_addr(v_fst_195_);
v___x_198_ = ((size_t)3ULL);
v___x_199_ = lean_usize_shift_right(v___x_197_, v___x_198_);
v___x_200_ = lean_usize_to_uint64(v___x_199_);
v___x_201_ = lean_uint64_of_nat(v_snd_196_);
v___x_202_ = lean_uint64_mix_hash(v___x_200_, v___x_201_);
v___x_203_ = lean_uint64_mix_hash(v___y_194_, v___x_202_);
v___x_204_ = 32ULL;
v___x_205_ = lean_uint64_shift_right(v___x_203_, v___x_204_);
v_fold_206_ = lean_uint64_xor(v___x_203_, v___x_205_);
v___x_207_ = 16ULL;
v___x_208_ = lean_uint64_shift_right(v_fold_206_, v___x_207_);
v___x_209_ = lean_uint64_xor(v_fold_206_, v___x_208_);
v___x_210_ = lean_uint64_to_usize(v___x_209_);
v___x_211_ = lean_usize_of_nat(v___x_192_);
v___x_212_ = ((size_t)1ULL);
v___x_213_ = lean_usize_sub(v___x_211_, v___x_212_);
v___x_214_ = lean_usize_land(v___x_210_, v___x_213_);
v___x_215_ = lean_array_uget_borrowed(v_x_182_, v___x_214_);
lean_inc(v___x_215_);
if (v_isShared_189_ == 0)
{
lean_ctor_set(v___x_188_, 2, v___x_215_);
v___x_217_ = v___x_188_;
goto v_reusejp_216_;
}
else
{
lean_object* v_reuseFailAlloc_220_; 
v_reuseFailAlloc_220_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_220_, 0, v_key_184_);
lean_ctor_set(v_reuseFailAlloc_220_, 1, v_value_185_);
lean_ctor_set(v_reuseFailAlloc_220_, 2, v___x_215_);
v___x_217_ = v_reuseFailAlloc_220_;
goto v_reusejp_216_;
}
v_reusejp_216_:
{
lean_object* v___x_218_; 
v___x_218_ = lean_array_uset(v_x_182_, v___x_214_, v___x_217_);
v_x_182_ = v___x_218_;
v_x_183_ = v_tail_186_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__4_spec__5___redArg(lean_object* v_i_224_, lean_object* v_source_225_, lean_object* v_target_226_){
_start:
{
lean_object* v___x_227_; uint8_t v___x_228_; 
v___x_227_ = lean_array_get_size(v_source_225_);
v___x_228_ = lean_nat_dec_lt(v_i_224_, v___x_227_);
if (v___x_228_ == 0)
{
lean_dec_ref(v_source_225_);
lean_dec(v_i_224_);
return v_target_226_;
}
else
{
lean_object* v_es_229_; lean_object* v___x_230_; lean_object* v_source_231_; lean_object* v_target_232_; lean_object* v___x_233_; lean_object* v___x_234_; 
v_es_229_ = lean_array_fget(v_source_225_, v_i_224_);
v___x_230_ = lean_box(0);
v_source_231_ = lean_array_fset(v_source_225_, v_i_224_, v___x_230_);
v_target_232_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__4_spec__5_spec__6___redArg(v_target_226_, v_es_229_);
v___x_233_ = lean_unsigned_to_nat(1u);
v___x_234_ = lean_nat_add(v_i_224_, v___x_233_);
lean_dec(v_i_224_);
v_i_224_ = v___x_234_;
v_source_225_ = v_source_231_;
v_target_226_ = v_target_232_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__4___redArg(lean_object* v_data_236_){
_start:
{
lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v_nbuckets_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; 
v___x_237_ = lean_array_get_size(v_data_236_);
v___x_238_ = lean_unsigned_to_nat(2u);
v_nbuckets_239_ = lean_nat_mul(v___x_237_, v___x_238_);
v___x_240_ = lean_unsigned_to_nat(0u);
v___x_241_ = lean_box(0);
v___x_242_ = lean_mk_array(v_nbuckets_239_, v___x_241_);
v___x_243_ = lean_array_propagate_mark(v_data_236_, v___x_242_);
v___x_244_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__4_spec__5___redArg(v___x_240_, v_data_236_, v___x_243_);
return v___x_244_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__5___redArg(lean_object* v_a_245_, lean_object* v_b_246_, lean_object* v_x_247_){
_start:
{
if (lean_obj_tag(v_x_247_) == 0)
{
lean_dec(v_b_246_);
lean_dec_ref(v_a_245_);
return v_x_247_;
}
else
{
lean_object* v_key_248_; lean_object* v_value_249_; lean_object* v_tail_250_; lean_object* v___x_252_; uint8_t v_isShared_253_; uint8_t v_isSharedCheck_275_; 
v_key_248_ = lean_ctor_get(v_x_247_, 0);
v_value_249_ = lean_ctor_get(v_x_247_, 1);
v_tail_250_ = lean_ctor_get(v_x_247_, 2);
v_isSharedCheck_275_ = !lean_is_exclusive(v_x_247_);
if (v_isSharedCheck_275_ == 0)
{
v___x_252_ = v_x_247_;
v_isShared_253_ = v_isSharedCheck_275_;
goto v_resetjp_251_;
}
else
{
lean_inc(v_tail_250_);
lean_inc(v_value_249_);
lean_inc(v_key_248_);
lean_dec(v_x_247_);
v___x_252_ = lean_box(0);
v_isShared_253_ = v_isSharedCheck_275_;
goto v_resetjp_251_;
}
v_resetjp_251_:
{
uint8_t v___y_260_; lean_object* v_fst_262_; lean_object* v_snd_263_; lean_object* v_fst_264_; lean_object* v_snd_265_; uint8_t v___x_266_; 
v_fst_262_ = lean_ctor_get(v_key_248_, 0);
v_snd_263_ = lean_ctor_get(v_key_248_, 1);
v_fst_264_ = lean_ctor_get(v_a_245_, 0);
v_snd_265_ = lean_ctor_get(v_a_245_, 1);
v___x_266_ = lean_name_eq(v_fst_262_, v_fst_264_);
if (v___x_266_ == 0)
{
v___y_260_ = v___x_266_;
goto v___jp_259_;
}
else
{
lean_object* v_fst_267_; lean_object* v_snd_268_; lean_object* v_fst_269_; lean_object* v_snd_270_; size_t v___x_271_; size_t v___x_272_; uint8_t v___x_273_; 
v_fst_267_ = lean_ctor_get(v_snd_263_, 0);
v_snd_268_ = lean_ctor_get(v_snd_263_, 1);
v_fst_269_ = lean_ctor_get(v_snd_265_, 0);
v_snd_270_ = lean_ctor_get(v_snd_265_, 1);
v___x_271_ = lean_ptr_addr(v_fst_267_);
v___x_272_ = lean_ptr_addr(v_fst_269_);
v___x_273_ = lean_usize_dec_eq(v___x_271_, v___x_272_);
if (v___x_273_ == 0)
{
goto v___jp_254_;
}
else
{
uint8_t v___x_274_; 
v___x_274_ = lean_nat_dec_eq(v_snd_268_, v_snd_270_);
v___y_260_ = v___x_274_;
goto v___jp_259_;
}
}
v___jp_254_:
{
lean_object* v___x_255_; lean_object* v___x_257_; 
v___x_255_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__5___redArg(v_a_245_, v_b_246_, v_tail_250_);
if (v_isShared_253_ == 0)
{
lean_ctor_set(v___x_252_, 2, v___x_255_);
v___x_257_ = v___x_252_;
goto v_reusejp_256_;
}
else
{
lean_object* v_reuseFailAlloc_258_; 
v_reuseFailAlloc_258_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_258_, 0, v_key_248_);
lean_ctor_set(v_reuseFailAlloc_258_, 1, v_value_249_);
lean_ctor_set(v_reuseFailAlloc_258_, 2, v___x_255_);
v___x_257_ = v_reuseFailAlloc_258_;
goto v_reusejp_256_;
}
v_reusejp_256_:
{
return v___x_257_;
}
}
v___jp_259_:
{
if (v___y_260_ == 0)
{
goto v___jp_254_;
}
else
{
lean_object* v___x_261_; 
lean_del_object(v___x_252_);
lean_dec(v_value_249_);
lean_dec(v_key_248_);
v___x_261_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_261_, 0, v_a_245_);
lean_ctor_set(v___x_261_, 1, v_b_246_);
lean_ctor_set(v___x_261_, 2, v_tail_250_);
return v___x_261_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2___redArg(lean_object* v_m_276_, lean_object* v_a_277_, lean_object* v_b_278_){
_start:
{
lean_object* v_size_279_; lean_object* v_buckets_280_; lean_object* v___x_282_; uint8_t v_isShared_283_; uint8_t v_isSharedCheck_337_; 
v_size_279_ = lean_ctor_get(v_m_276_, 0);
v_buckets_280_ = lean_ctor_get(v_m_276_, 1);
v_isSharedCheck_337_ = !lean_is_exclusive(v_m_276_);
if (v_isSharedCheck_337_ == 0)
{
v___x_282_ = v_m_276_;
v_isShared_283_ = v_isSharedCheck_337_;
goto v_resetjp_281_;
}
else
{
lean_inc(v_buckets_280_);
lean_inc(v_size_279_);
lean_dec(v_m_276_);
v___x_282_ = lean_box(0);
v_isShared_283_ = v_isSharedCheck_337_;
goto v_resetjp_281_;
}
v_resetjp_281_:
{
lean_object* v_fst_284_; lean_object* v_snd_285_; lean_object* v___x_286_; uint64_t v___y_288_; 
v_fst_284_ = lean_ctor_get(v_a_277_, 0);
v_snd_285_ = lean_ctor_get(v_a_277_, 1);
v___x_286_ = lean_array_get_size(v_buckets_280_);
if (lean_obj_tag(v_fst_284_) == 0)
{
uint64_t v___x_335_; 
v___x_335_ = 1723ULL;
v___y_288_ = v___x_335_;
goto v___jp_287_;
}
else
{
uint64_t v_hash_336_; 
v_hash_336_ = lean_ctor_get_uint64(v_fst_284_, sizeof(void*)*2);
v___y_288_ = v_hash_336_;
goto v___jp_287_;
}
v___jp_287_:
{
lean_object* v_fst_289_; lean_object* v_snd_290_; size_t v___x_291_; size_t v___x_292_; size_t v___x_293_; uint64_t v___x_294_; uint64_t v___x_295_; uint64_t v___x_296_; uint64_t v___x_297_; uint64_t v___x_298_; uint64_t v___x_299_; uint64_t v_fold_300_; uint64_t v___x_301_; uint64_t v___x_302_; uint64_t v___x_303_; size_t v___x_304_; size_t v___x_305_; size_t v___x_306_; size_t v___x_307_; size_t v___x_308_; lean_object* v_bkt_309_; uint8_t v___x_310_; 
v_fst_289_ = lean_ctor_get(v_snd_285_, 0);
v_snd_290_ = lean_ctor_get(v_snd_285_, 1);
v___x_291_ = lean_ptr_addr(v_fst_289_);
v___x_292_ = ((size_t)3ULL);
v___x_293_ = lean_usize_shift_right(v___x_291_, v___x_292_);
v___x_294_ = lean_usize_to_uint64(v___x_293_);
v___x_295_ = lean_uint64_of_nat(v_snd_290_);
v___x_296_ = lean_uint64_mix_hash(v___x_294_, v___x_295_);
v___x_297_ = lean_uint64_mix_hash(v___y_288_, v___x_296_);
v___x_298_ = 32ULL;
v___x_299_ = lean_uint64_shift_right(v___x_297_, v___x_298_);
v_fold_300_ = lean_uint64_xor(v___x_297_, v___x_299_);
v___x_301_ = 16ULL;
v___x_302_ = lean_uint64_shift_right(v_fold_300_, v___x_301_);
v___x_303_ = lean_uint64_xor(v_fold_300_, v___x_302_);
v___x_304_ = lean_uint64_to_usize(v___x_303_);
v___x_305_ = lean_usize_of_nat(v___x_286_);
v___x_306_ = ((size_t)1ULL);
v___x_307_ = lean_usize_sub(v___x_305_, v___x_306_);
v___x_308_ = lean_usize_land(v___x_304_, v___x_307_);
v_bkt_309_ = lean_array_uget_borrowed(v_buckets_280_, v___x_308_);
v___x_310_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__3___redArg(v_a_277_, v_bkt_309_);
if (v___x_310_ == 0)
{
lean_object* v___x_311_; lean_object* v_size_x27_312_; lean_object* v___x_313_; lean_object* v_buckets_x27_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; uint8_t v___x_320_; 
v___x_311_ = lean_unsigned_to_nat(1u);
v_size_x27_312_ = lean_nat_add(v_size_279_, v___x_311_);
lean_dec(v_size_279_);
lean_inc(v_bkt_309_);
v___x_313_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_313_, 0, v_a_277_);
lean_ctor_set(v___x_313_, 1, v_b_278_);
lean_ctor_set(v___x_313_, 2, v_bkt_309_);
v_buckets_x27_314_ = lean_array_uset(v_buckets_280_, v___x_308_, v___x_313_);
v___x_315_ = lean_unsigned_to_nat(4u);
v___x_316_ = lean_nat_mul(v_size_x27_312_, v___x_315_);
v___x_317_ = lean_unsigned_to_nat(3u);
v___x_318_ = lean_nat_div(v___x_316_, v___x_317_);
lean_dec(v___x_316_);
v___x_319_ = lean_array_get_size(v_buckets_x27_314_);
v___x_320_ = lean_nat_dec_le(v___x_318_, v___x_319_);
lean_dec(v___x_318_);
if (v___x_320_ == 0)
{
lean_object* v_val_321_; lean_object* v___x_323_; 
v_val_321_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__4___redArg(v_buckets_x27_314_);
if (v_isShared_283_ == 0)
{
lean_ctor_set(v___x_282_, 1, v_val_321_);
lean_ctor_set(v___x_282_, 0, v_size_x27_312_);
v___x_323_ = v___x_282_;
goto v_reusejp_322_;
}
else
{
lean_object* v_reuseFailAlloc_324_; 
v_reuseFailAlloc_324_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_324_, 0, v_size_x27_312_);
lean_ctor_set(v_reuseFailAlloc_324_, 1, v_val_321_);
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
if (v_isShared_283_ == 0)
{
lean_ctor_set(v___x_282_, 1, v_buckets_x27_314_);
lean_ctor_set(v___x_282_, 0, v_size_x27_312_);
v___x_326_ = v___x_282_;
goto v_reusejp_325_;
}
else
{
lean_object* v_reuseFailAlloc_327_; 
v_reuseFailAlloc_327_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_327_, 0, v_size_x27_312_);
lean_ctor_set(v_reuseFailAlloc_327_, 1, v_buckets_x27_314_);
v___x_326_ = v_reuseFailAlloc_327_;
goto v_reusejp_325_;
}
v_reusejp_325_:
{
return v___x_326_;
}
}
}
else
{
lean_object* v___x_328_; lean_object* v_buckets_x27_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_333_; 
lean_inc(v_bkt_309_);
v___x_328_ = lean_box(0);
v_buckets_x27_329_ = lean_array_uset(v_buckets_280_, v___x_308_, v___x_328_);
v___x_330_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__5___redArg(v_a_277_, v_b_278_, v_bkt_309_);
v___x_331_ = lean_array_uset(v_buckets_x27_329_, v___x_308_, v___x_330_);
if (v_isShared_283_ == 0)
{
lean_ctor_set(v___x_282_, 1, v___x_331_);
v___x_333_ = v___x_282_;
goto v_reusejp_332_;
}
else
{
lean_object* v_reuseFailAlloc_334_; 
v_reuseFailAlloc_334_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_334_, 0, v_size_279_);
lean_ctor_set(v_reuseFailAlloc_334_, 1, v___x_331_);
v___x_333_ = v_reuseFailAlloc_334_;
goto v_reusejp_332_;
}
v_reusejp_332_:
{
return v___x_333_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__0_spec__0___redArg(lean_object* v_a_338_, lean_object* v_x_339_){
_start:
{
if (lean_obj_tag(v_x_339_) == 0)
{
lean_object* v___x_340_; 
v___x_340_ = lean_box(0);
return v___x_340_;
}
else
{
lean_object* v_key_341_; lean_object* v_value_342_; lean_object* v_tail_343_; uint8_t v___y_345_; lean_object* v_fst_348_; lean_object* v_snd_349_; lean_object* v_fst_350_; lean_object* v_snd_351_; uint8_t v___x_352_; 
v_key_341_ = lean_ctor_get(v_x_339_, 0);
v_value_342_ = lean_ctor_get(v_x_339_, 1);
v_tail_343_ = lean_ctor_get(v_x_339_, 2);
v_fst_348_ = lean_ctor_get(v_key_341_, 0);
v_snd_349_ = lean_ctor_get(v_key_341_, 1);
v_fst_350_ = lean_ctor_get(v_a_338_, 0);
v_snd_351_ = lean_ctor_get(v_a_338_, 1);
v___x_352_ = lean_name_eq(v_fst_348_, v_fst_350_);
if (v___x_352_ == 0)
{
v___y_345_ = v___x_352_;
goto v___jp_344_;
}
else
{
lean_object* v_fst_353_; lean_object* v_snd_354_; lean_object* v_fst_355_; lean_object* v_snd_356_; size_t v___x_357_; size_t v___x_358_; uint8_t v___x_359_; 
v_fst_353_ = lean_ctor_get(v_snd_349_, 0);
v_snd_354_ = lean_ctor_get(v_snd_349_, 1);
v_fst_355_ = lean_ctor_get(v_snd_351_, 0);
v_snd_356_ = lean_ctor_get(v_snd_351_, 1);
v___x_357_ = lean_ptr_addr(v_fst_353_);
v___x_358_ = lean_ptr_addr(v_fst_355_);
v___x_359_ = lean_usize_dec_eq(v___x_357_, v___x_358_);
if (v___x_359_ == 0)
{
v_x_339_ = v_tail_343_;
goto _start;
}
else
{
uint8_t v___x_361_; 
v___x_361_ = lean_nat_dec_eq(v_snd_354_, v_snd_356_);
v___y_345_ = v___x_361_;
goto v___jp_344_;
}
}
v___jp_344_:
{
if (v___y_345_ == 0)
{
v_x_339_ = v_tail_343_;
goto _start;
}
else
{
lean_object* v___x_347_; 
lean_inc(v_value_342_);
v___x_347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_347_, 0, v_value_342_);
return v___x_347_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__0_spec__0___redArg___boxed(lean_object* v_a_362_, lean_object* v_x_363_){
_start:
{
lean_object* v_res_364_; 
v_res_364_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__0_spec__0___redArg(v_a_362_, v_x_363_);
lean_dec(v_x_363_);
lean_dec_ref(v_a_362_);
return v_res_364_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg(lean_object* v_m_365_, lean_object* v_a_366_){
_start:
{
lean_object* v_buckets_367_; lean_object* v_fst_368_; lean_object* v_snd_369_; lean_object* v___x_370_; uint64_t v___y_372_; 
v_buckets_367_ = lean_ctor_get(v_m_365_, 1);
v_fst_368_ = lean_ctor_get(v_a_366_, 0);
v_snd_369_ = lean_ctor_get(v_a_366_, 1);
v___x_370_ = lean_array_get_size(v_buckets_367_);
if (lean_obj_tag(v_fst_368_) == 0)
{
uint64_t v___x_395_; 
v___x_395_ = 1723ULL;
v___y_372_ = v___x_395_;
goto v___jp_371_;
}
else
{
uint64_t v_hash_396_; 
v_hash_396_ = lean_ctor_get_uint64(v_fst_368_, sizeof(void*)*2);
v___y_372_ = v_hash_396_;
goto v___jp_371_;
}
v___jp_371_:
{
lean_object* v_fst_373_; lean_object* v_snd_374_; size_t v___x_375_; size_t v___x_376_; size_t v___x_377_; uint64_t v___x_378_; uint64_t v___x_379_; uint64_t v___x_380_; uint64_t v___x_381_; uint64_t v___x_382_; uint64_t v___x_383_; uint64_t v_fold_384_; uint64_t v___x_385_; uint64_t v___x_386_; uint64_t v___x_387_; size_t v___x_388_; size_t v___x_389_; size_t v___x_390_; size_t v___x_391_; size_t v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; 
v_fst_373_ = lean_ctor_get(v_snd_369_, 0);
v_snd_374_ = lean_ctor_get(v_snd_369_, 1);
v___x_375_ = lean_ptr_addr(v_fst_373_);
v___x_376_ = ((size_t)3ULL);
v___x_377_ = lean_usize_shift_right(v___x_375_, v___x_376_);
v___x_378_ = lean_usize_to_uint64(v___x_377_);
v___x_379_ = lean_uint64_of_nat(v_snd_374_);
v___x_380_ = lean_uint64_mix_hash(v___x_378_, v___x_379_);
v___x_381_ = lean_uint64_mix_hash(v___y_372_, v___x_380_);
v___x_382_ = 32ULL;
v___x_383_ = lean_uint64_shift_right(v___x_381_, v___x_382_);
v_fold_384_ = lean_uint64_xor(v___x_381_, v___x_383_);
v___x_385_ = 16ULL;
v___x_386_ = lean_uint64_shift_right(v_fold_384_, v___x_385_);
v___x_387_ = lean_uint64_xor(v_fold_384_, v___x_386_);
v___x_388_ = lean_uint64_to_usize(v___x_387_);
v___x_389_ = lean_usize_of_nat(v___x_370_);
v___x_390_ = ((size_t)1ULL);
v___x_391_ = lean_usize_sub(v___x_389_, v___x_390_);
v___x_392_ = lean_usize_land(v___x_388_, v___x_391_);
v___x_393_ = lean_array_uget_borrowed(v_buckets_367_, v___x_392_);
v___x_394_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__0_spec__0___redArg(v_a_366_, v___x_393_);
return v___x_394_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg___boxed(lean_object* v_m_397_, lean_object* v_a_398_){
_start:
{
lean_object* v_res_399_; 
v_res_399_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg(v_m_397_, v_a_398_);
lean_dec_ref(v_a_398_);
lean_dec_ref(v_m_397_);
return v_res_399_;
}
}
lean_object* l_Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached(lean_object* v_specThm_402_, lean_object* v_info_403_, lean_object* v_a_404_, lean_object* v_a_405_, lean_object* v_a_406_, lean_object* v_a_407_, lean_object* v_a_408_, lean_object* v_a_409_, lean_object* v_a_410_, lean_object* v_a_411_, lean_object* v_a_412_, lean_object* v_a_413_, lean_object* v_a_414_){
_start:
{
lean_object* v_proof_416_; lean_object* v_excessArgs_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v_key_422_; lean_object* v___x_423_; lean_object* v_specBackwardRuleCache_424_; lean_object* v___x_425_; 
v_proof_416_ = lean_ctor_get(v_specThm_402_, 1);
v_excessArgs_417_ = lean_ctor_get(v_info_403_, 3);
v___x_418_ = l_Lean_Elab_Tactic_VCGen_SpecAttr_SpecProof_key(v_proof_416_);
v___x_419_ = l_Lean_Elab_Tactic_VCGen_WPApp_instWP(v_info_403_);
v___x_420_ = lean_array_get_size(v_excessArgs_417_);
v___x_421_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_421_, 0, v___x_419_);
lean_ctor_set(v___x_421_, 1, v___x_420_);
v_key_422_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_key_422_, 0, v___x_418_);
lean_ctor_set(v_key_422_, 1, v___x_421_);
v___x_423_ = lean_st_ref_get(v_a_405_);
v_specBackwardRuleCache_424_ = lean_ctor_get(v___x_423_, 0);
lean_inc_ref(v_specBackwardRuleCache_424_);
lean_dec(v___x_423_);
v___x_425_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg(v_specBackwardRuleCache_424_, v_key_422_);
lean_dec_ref(v_specBackwardRuleCache_424_);
if (lean_obj_tag(v___x_425_) == 1)
{
lean_object* v___x_426_; 
lean_dec_ref_known(v_key_422_, 2);
lean_dec_ref(v_info_403_);
lean_dec_ref(v_specThm_402_);
v___x_426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_426_, 0, v___x_425_);
return v___x_426_;
}
else
{
lean_object* v___x_427_; lean_object* v___f_428_; uint8_t v___x_429_; lean_object* v___x_430_; 
lean_dec(v___x_425_);
v___x_427_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached___closed__0));
v___f_428_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached___lam__0___boxed), 15, 3);
lean_closure_set(v___f_428_, 0, v_specThm_402_);
lean_closure_set(v___f_428_, 1, v_info_403_);
lean_closure_set(v___f_428_, 2, v___x_427_);
v___x_429_ = 0;
v___x_430_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__1___redArg(v___f_428_, v___x_429_, v_a_404_, v_a_405_, v_a_406_, v_a_407_, v_a_408_, v_a_409_, v_a_410_, v_a_411_, v_a_412_, v_a_413_, v_a_414_);
if (lean_obj_tag(v___x_430_) == 0)
{
lean_object* v_a_431_; lean_object* v___x_433_; uint8_t v_isShared_434_; uint8_t v_isSharedCheck_489_; 
v_a_431_ = lean_ctor_get(v___x_430_, 0);
v_isSharedCheck_489_ = !lean_is_exclusive(v___x_430_);
if (v_isSharedCheck_489_ == 0)
{
v___x_433_ = v___x_430_;
v_isShared_434_ = v_isSharedCheck_489_;
goto v_resetjp_432_;
}
else
{
lean_inc(v_a_431_);
lean_dec(v___x_430_);
v___x_433_ = lean_box(0);
v_isShared_434_ = v_isSharedCheck_489_;
goto v_resetjp_432_;
}
v_resetjp_432_:
{
if (lean_obj_tag(v_a_431_) == 0)
{
lean_object* v___x_435_; lean_object* v___x_437_; 
lean_dec_ref_known(v_key_422_, 2);
v___x_435_ = lean_box(0);
if (v_isShared_434_ == 0)
{
lean_ctor_set(v___x_433_, 0, v___x_435_);
v___x_437_ = v___x_433_;
goto v_reusejp_436_;
}
else
{
lean_object* v_reuseFailAlloc_438_; 
v_reuseFailAlloc_438_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_438_, 0, v___x_435_);
v___x_437_ = v_reuseFailAlloc_438_;
goto v_reusejp_436_;
}
v_reusejp_436_:
{
return v___x_437_;
}
}
else
{
lean_object* v_val_439_; 
v_val_439_ = lean_ctor_get(v_a_431_, 0);
lean_inc(v_val_439_);
lean_dec_ref_known(v_a_431_, 1);
if (lean_obj_tag(v_val_439_) == 1)
{
lean_object* v_val_440_; lean_object* v___x_442_; uint8_t v_isShared_443_; uint8_t v_isSharedCheck_484_; 
lean_del_object(v___x_433_);
v_val_440_ = lean_ctor_get(v_val_439_, 0);
v_isSharedCheck_484_ = !lean_is_exclusive(v_val_439_);
if (v_isSharedCheck_484_ == 0)
{
v___x_442_ = v_val_439_;
v_isShared_443_ = v_isSharedCheck_484_;
goto v_resetjp_441_;
}
else
{
lean_inc(v_val_440_);
lean_dec(v_val_439_);
v___x_442_ = lean_box(0);
v_isShared_443_ = v_isSharedCheck_484_;
goto v_resetjp_441_;
}
v_resetjp_441_:
{
lean_object* v___x_444_; 
v___x_444_ = l_Lean_Meta_Sym_BackwardRule_shareCommon(v_val_440_, v_a_409_, v_a_410_, v_a_411_, v_a_412_, v_a_413_, v_a_414_);
if (lean_obj_tag(v___x_444_) == 0)
{
lean_object* v_a_445_; lean_object* v___x_447_; uint8_t v_isShared_448_; uint8_t v_isSharedCheck_475_; 
v_a_445_ = lean_ctor_get(v___x_444_, 0);
v_isSharedCheck_475_ = !lean_is_exclusive(v___x_444_);
if (v_isSharedCheck_475_ == 0)
{
v___x_447_ = v___x_444_;
v_isShared_448_ = v_isSharedCheck_475_;
goto v_resetjp_446_;
}
else
{
lean_inc(v_a_445_);
lean_dec(v___x_444_);
v___x_447_ = lean_box(0);
v_isShared_448_ = v_isSharedCheck_475_;
goto v_resetjp_446_;
}
v_resetjp_446_:
{
lean_object* v___x_450_; 
lean_inc(v_a_445_);
if (v_isShared_443_ == 0)
{
lean_ctor_set(v___x_442_, 0, v_a_445_);
v___x_450_ = v___x_442_;
goto v_reusejp_449_;
}
else
{
lean_object* v_reuseFailAlloc_474_; 
v_reuseFailAlloc_474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_474_, 0, v_a_445_);
v___x_450_ = v_reuseFailAlloc_474_;
goto v_reusejp_449_;
}
v_reusejp_449_:
{
lean_object* v___x_451_; lean_object* v_specBackwardRuleCache_452_; lean_object* v_splitBackwardRuleCache_453_; lean_object* v_latticeBackwardRuleCache_454_; lean_object* v_frameBackwardRuleCache_455_; lean_object* v_frameDB_456_; lean_object* v_invariants_457_; lean_object* v_vcs_458_; lean_object* v_simpState_459_; lean_object* v_fuel_460_; lean_object* v_inlineHandledInvariants_461_; lean_object* v___x_463_; uint8_t v_isShared_464_; uint8_t v_isSharedCheck_473_; 
v___x_451_ = lean_st_ref_take(v_a_405_);
v_specBackwardRuleCache_452_ = lean_ctor_get(v___x_451_, 0);
v_splitBackwardRuleCache_453_ = lean_ctor_get(v___x_451_, 1);
v_latticeBackwardRuleCache_454_ = lean_ctor_get(v___x_451_, 2);
v_frameBackwardRuleCache_455_ = lean_ctor_get(v___x_451_, 3);
v_frameDB_456_ = lean_ctor_get(v___x_451_, 4);
v_invariants_457_ = lean_ctor_get(v___x_451_, 5);
v_vcs_458_ = lean_ctor_get(v___x_451_, 6);
v_simpState_459_ = lean_ctor_get(v___x_451_, 7);
v_fuel_460_ = lean_ctor_get(v___x_451_, 8);
v_inlineHandledInvariants_461_ = lean_ctor_get(v___x_451_, 9);
v_isSharedCheck_473_ = !lean_is_exclusive(v___x_451_);
if (v_isSharedCheck_473_ == 0)
{
v___x_463_ = v___x_451_;
v_isShared_464_ = v_isSharedCheck_473_;
goto v_resetjp_462_;
}
else
{
lean_inc(v_inlineHandledInvariants_461_);
lean_inc(v_fuel_460_);
lean_inc(v_simpState_459_);
lean_inc(v_vcs_458_);
lean_inc(v_invariants_457_);
lean_inc(v_frameDB_456_);
lean_inc(v_frameBackwardRuleCache_455_);
lean_inc(v_latticeBackwardRuleCache_454_);
lean_inc(v_splitBackwardRuleCache_453_);
lean_inc(v_specBackwardRuleCache_452_);
lean_dec(v___x_451_);
v___x_463_ = lean_box(0);
v_isShared_464_ = v_isSharedCheck_473_;
goto v_resetjp_462_;
}
v_resetjp_462_:
{
lean_object* v___x_465_; lean_object* v___x_467_; 
v___x_465_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2___redArg(v_specBackwardRuleCache_452_, v_key_422_, v_a_445_);
if (v_isShared_464_ == 0)
{
lean_ctor_set(v___x_463_, 0, v___x_465_);
v___x_467_ = v___x_463_;
goto v_reusejp_466_;
}
else
{
lean_object* v_reuseFailAlloc_472_; 
v_reuseFailAlloc_472_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_472_, 0, v___x_465_);
lean_ctor_set(v_reuseFailAlloc_472_, 1, v_splitBackwardRuleCache_453_);
lean_ctor_set(v_reuseFailAlloc_472_, 2, v_latticeBackwardRuleCache_454_);
lean_ctor_set(v_reuseFailAlloc_472_, 3, v_frameBackwardRuleCache_455_);
lean_ctor_set(v_reuseFailAlloc_472_, 4, v_frameDB_456_);
lean_ctor_set(v_reuseFailAlloc_472_, 5, v_invariants_457_);
lean_ctor_set(v_reuseFailAlloc_472_, 6, v_vcs_458_);
lean_ctor_set(v_reuseFailAlloc_472_, 7, v_simpState_459_);
lean_ctor_set(v_reuseFailAlloc_472_, 8, v_fuel_460_);
lean_ctor_set(v_reuseFailAlloc_472_, 9, v_inlineHandledInvariants_461_);
v___x_467_ = v_reuseFailAlloc_472_;
goto v_reusejp_466_;
}
v_reusejp_466_:
{
lean_object* v___x_468_; lean_object* v___x_470_; 
v___x_468_ = lean_st_ref_put(v_a_405_, v___x_467_);
if (v_isShared_448_ == 0)
{
lean_ctor_set(v___x_447_, 0, v___x_450_);
v___x_470_ = v___x_447_;
goto v_reusejp_469_;
}
else
{
lean_object* v_reuseFailAlloc_471_; 
v_reuseFailAlloc_471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_471_, 0, v___x_450_);
v___x_470_ = v_reuseFailAlloc_471_;
goto v_reusejp_469_;
}
v_reusejp_469_:
{
return v___x_470_;
}
}
}
}
}
}
else
{
lean_object* v_a_476_; lean_object* v___x_478_; uint8_t v_isShared_479_; uint8_t v_isSharedCheck_483_; 
lean_del_object(v___x_442_);
lean_dec_ref_known(v_key_422_, 2);
v_a_476_ = lean_ctor_get(v___x_444_, 0);
v_isSharedCheck_483_ = !lean_is_exclusive(v___x_444_);
if (v_isSharedCheck_483_ == 0)
{
v___x_478_ = v___x_444_;
v_isShared_479_ = v_isSharedCheck_483_;
goto v_resetjp_477_;
}
else
{
lean_inc(v_a_476_);
lean_dec(v___x_444_);
v___x_478_ = lean_box(0);
v_isShared_479_ = v_isSharedCheck_483_;
goto v_resetjp_477_;
}
v_resetjp_477_:
{
lean_object* v___x_481_; 
if (v_isShared_479_ == 0)
{
v___x_481_ = v___x_478_;
goto v_reusejp_480_;
}
else
{
lean_object* v_reuseFailAlloc_482_; 
v_reuseFailAlloc_482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_482_, 0, v_a_476_);
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
lean_object* v___x_485_; lean_object* v___x_487_; 
lean_dec(v_val_439_);
lean_dec_ref_known(v_key_422_, 2);
v___x_485_ = lean_box(0);
if (v_isShared_434_ == 0)
{
lean_ctor_set(v___x_433_, 0, v___x_485_);
v___x_487_ = v___x_433_;
goto v_reusejp_486_;
}
else
{
lean_object* v_reuseFailAlloc_488_; 
v_reuseFailAlloc_488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_488_, 0, v___x_485_);
v___x_487_ = v_reuseFailAlloc_488_;
goto v_reusejp_486_;
}
v_reusejp_486_:
{
return v___x_487_;
}
}
}
}
}
else
{
lean_object* v_a_490_; lean_object* v___x_492_; uint8_t v_isShared_493_; uint8_t v_isSharedCheck_497_; 
lean_dec_ref_known(v_key_422_, 2);
v_a_490_ = lean_ctor_get(v___x_430_, 0);
v_isSharedCheck_497_ = !lean_is_exclusive(v___x_430_);
if (v_isSharedCheck_497_ == 0)
{
v___x_492_ = v___x_430_;
v_isShared_493_ = v_isSharedCheck_497_;
goto v_resetjp_491_;
}
else
{
lean_inc(v_a_490_);
lean_dec(v___x_430_);
v___x_492_ = lean_box(0);
v_isShared_493_ = v_isSharedCheck_497_;
goto v_resetjp_491_;
}
v_resetjp_491_:
{
lean_object* v___x_495_; 
if (v_isShared_493_ == 0)
{
v___x_495_ = v___x_492_;
goto v_reusejp_494_;
}
else
{
lean_object* v_reuseFailAlloc_496_; 
v_reuseFailAlloc_496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_496_, 0, v_a_490_);
v___x_495_ = v_reuseFailAlloc_496_;
goto v_reusejp_494_;
}
v_reusejp_494_:
{
return v___x_495_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_0interp(lean_interpreter_value* stack)
{
lean_object* v_specThm_402_ = stack[0].m_obj;
lean_object* v_info_403_ = stack[1].m_obj;
lean_object* v_a_404_ = stack[2].m_obj;
lean_object* v_a_405_ = stack[3].m_obj;
lean_object* v_a_406_ = stack[4].m_obj;
lean_object* v_a_407_ = stack[5].m_obj;
lean_object* v_a_408_ = stack[6].m_obj;
lean_object* v_a_409_ = stack[7].m_obj;
lean_object* v_a_410_ = stack[8].m_obj;
lean_object* v_a_411_ = stack[9].m_obj;
lean_object* v_a_412_ = stack[10].m_obj;
lean_object* v_a_413_ = stack[11].m_obj;
lean_object* v_a_414_ = stack[12].m_obj;
lean_object* v_res_498_;
v_res_498_ = l_Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached(v_specThm_402_, v_info_403_, v_a_404_, v_a_405_, v_a_406_, v_a_407_, v_a_408_, v_a_409_, v_a_410_, v_a_411_, v_a_412_, v_a_413_, v_a_414_);
stack->m_obj
 = v_res_498_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached___boxed(lean_object* v_specThm_499_, lean_object* v_info_500_, lean_object* v_a_501_, lean_object* v_a_502_, lean_object* v_a_503_, lean_object* v_a_504_, lean_object* v_a_505_, lean_object* v_a_506_, lean_object* v_a_507_, lean_object* v_a_508_, lean_object* v_a_509_, lean_object* v_a_510_, lean_object* v_a_511_, lean_object* v_a_512_){
_start:
{
lean_object* v_res_513_; 
v_res_513_ = l_Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached(v_specThm_499_, v_info_500_, v_a_501_, v_a_502_, v_a_503_, v_a_504_, v_a_505_, v_a_506_, v_a_507_, v_a_508_, v_a_509_, v_a_510_, v_a_511_);
lean_dec(v_a_511_);
lean_dec_ref(v_a_510_);
lean_dec(v_a_509_);
lean_dec_ref(v_a_508_);
lean_dec(v_a_507_);
lean_dec_ref(v_a_506_);
lean_dec(v_a_505_);
lean_dec_ref(v_a_504_);
lean_dec(v_a_503_);
lean_dec(v_a_502_);
lean_dec_ref(v_a_501_);
return v_res_513_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__0(lean_object* v_00_u03b2_514_, lean_object* v_m_515_, lean_object* v_a_516_){
_start:
{
lean_object* v___x_517_; 
v___x_517_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg(v_m_515_, v_a_516_);
return v___x_517_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__0___boxed(lean_object* v_00_u03b2_518_, lean_object* v_m_519_, lean_object* v_a_520_){
_start:
{
lean_object* v_res_521_; 
v_res_521_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__0(v_00_u03b2_518_, v_m_519_, v_a_520_);
lean_dec_ref(v_a_520_);
lean_dec_ref(v_m_519_);
return v_res_521_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2(lean_object* v_00_u03b2_522_, lean_object* v_m_523_, lean_object* v_a_524_, lean_object* v_b_525_){
_start:
{
lean_object* v___x_526_; 
v___x_526_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2___redArg(v_m_523_, v_a_524_, v_b_525_);
return v___x_526_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__0_spec__0(lean_object* v_00_u03b2_527_, lean_object* v_a_528_, lean_object* v_x_529_){
_start:
{
lean_object* v___x_530_; 
v___x_530_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__0_spec__0___redArg(v_a_528_, v_x_529_);
return v___x_530_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__0_spec__0___boxed(lean_object* v_00_u03b2_531_, lean_object* v_a_532_, lean_object* v_x_533_){
_start:
{
lean_object* v_res_534_; 
v_res_534_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__0_spec__0(v_00_u03b2_531_, v_a_532_, v_x_533_);
lean_dec(v_x_533_);
lean_dec_ref(v_a_532_);
return v_res_534_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__3(lean_object* v_00_u03b2_535_, lean_object* v_a_536_, lean_object* v_x_537_){
_start:
{
uint8_t v___x_538_; 
v___x_538_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__3___redArg(v_a_536_, v_x_537_);
return v___x_538_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_536_ = stack[1].m_obj;
lean_object* v_x_537_ = stack[2].m_obj;
uint8_t v_res_539_;
v_res_539_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__3(lean_box(0), v_a_536_, v_x_537_);
stack->m_num = v_res_539_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__3___boxed(lean_object* v_00_u03b2_540_, lean_object* v_a_541_, lean_object* v_x_542_){
_start:
{
uint8_t v_res_543_; lean_object* v_r_544_; 
v_res_543_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__3(v_00_u03b2_540_, v_a_541_, v_x_542_);
lean_dec(v_x_542_);
lean_dec_ref(v_a_541_);
v_r_544_ = lean_box(v_res_543_);
return v_r_544_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__4(lean_object* v_00_u03b2_545_, lean_object* v_data_546_){
_start:
{
lean_object* v___x_547_; 
v___x_547_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__4___redArg(v_data_546_);
return v___x_547_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__5(lean_object* v_00_u03b2_548_, lean_object* v_a_549_, lean_object* v_b_550_, lean_object* v_x_551_){
_start:
{
lean_object* v___x_552_; 
v___x_552_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__5___redArg(v_a_549_, v_b_550_, v_x_551_);
return v___x_552_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_553_, lean_object* v_i_554_, lean_object* v_source_555_, lean_object* v_target_556_){
_start:
{
lean_object* v___x_557_; 
v___x_557_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__4_spec__5___redArg(v_i_554_, v_source_555_, v_target_556_);
return v___x_557_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__4_spec__5_spec__6(lean_object* v_00_u03b2_558_, lean_object* v_x_559_, lean_object* v_x_560_){
_start:
{
lean_object* v___x_561_; 
v___x_561_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__4_spec__5_spec__6___redArg(v_x_559_, v_x_560_);
return v___x_561_;
}
}
lean_object* l_Lean_Elab_Tactic_VCGen_mkBackwardRuleForSplitCached___redArg(lean_object* v_splitInfo_571_, lean_object* v_info_572_, lean_object* v_a_573_, lean_object* v_a_574_, lean_object* v_a_575_, lean_object* v_a_576_, lean_object* v_a_577_, lean_object* v_a_578_, lean_object* v_a_579_){
_start:
{
lean_object* v___y_582_; 
switch(lean_obj_tag(v_splitInfo_571_))
{
case 0:
{
lean_object* v___x_630_; 
v___x_630_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_mkBackwardRuleForSplitCached___redArg___closed__1));
v___y_582_ = v___x_630_;
goto v___jp_581_;
}
case 1:
{
lean_object* v___x_631_; 
v___x_631_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_mkBackwardRuleForSplitCached___redArg___closed__3));
v___y_582_ = v___x_631_;
goto v___jp_581_;
}
case 2:
{
lean_object* v___x_632_; 
v___x_632_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_mkBackwardRuleForSplitCached___redArg___closed__5));
v___y_582_ = v___x_632_;
goto v___jp_581_;
}
default: 
{
lean_object* v_matcherApp_633_; lean_object* v_matcherName_634_; 
v_matcherApp_633_ = lean_ctor_get(v_splitInfo_571_, 0);
v_matcherName_634_ = lean_ctor_get(v_matcherApp_633_, 1);
lean_inc(v_matcherName_634_);
v___y_582_ = v_matcherName_634_;
goto v___jp_581_;
}
}
v___jp_581_:
{
lean_object* v_excessArgs_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v_key_587_; lean_object* v___x_588_; lean_object* v_splitBackwardRuleCache_589_; lean_object* v___x_590_; 
v_excessArgs_583_ = lean_ctor_get(v_info_572_, 3);
v___x_584_ = l_Lean_Elab_Tactic_VCGen_WPApp_instWP(v_info_572_);
v___x_585_ = lean_array_get_size(v_excessArgs_583_);
v___x_586_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_586_, 0, v___x_584_);
lean_ctor_set(v___x_586_, 1, v___x_585_);
v_key_587_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_key_587_, 0, v___y_582_);
lean_ctor_set(v_key_587_, 1, v___x_586_);
v___x_588_ = lean_st_ref_get(v_a_573_);
v_splitBackwardRuleCache_589_ = lean_ctor_get(v___x_588_, 1);
lean_inc_ref(v_splitBackwardRuleCache_589_);
lean_dec(v___x_588_);
v___x_590_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg(v_splitBackwardRuleCache_589_, v_key_587_);
lean_dec_ref(v_splitBackwardRuleCache_589_);
if (lean_obj_tag(v___x_590_) == 1)
{
lean_object* v_val_591_; lean_object* v___x_593_; uint8_t v_isShared_594_; uint8_t v_isSharedCheck_598_; 
lean_dec_ref_known(v_key_587_, 2);
lean_dec_ref(v_info_572_);
lean_dec_ref(v_splitInfo_571_);
v_val_591_ = lean_ctor_get(v___x_590_, 0);
v_isSharedCheck_598_ = !lean_is_exclusive(v___x_590_);
if (v_isSharedCheck_598_ == 0)
{
v___x_593_ = v___x_590_;
v_isShared_594_ = v_isSharedCheck_598_;
goto v_resetjp_592_;
}
else
{
lean_inc(v_val_591_);
lean_dec(v___x_590_);
v___x_593_ = lean_box(0);
v_isShared_594_ = v_isSharedCheck_598_;
goto v_resetjp_592_;
}
v_resetjp_592_:
{
lean_object* v___x_596_; 
if (v_isShared_594_ == 0)
{
lean_ctor_set_tag(v___x_593_, 0);
v___x_596_ = v___x_593_;
goto v_reusejp_595_;
}
else
{
lean_object* v_reuseFailAlloc_597_; 
v_reuseFailAlloc_597_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_597_, 0, v_val_591_);
v___x_596_ = v_reuseFailAlloc_597_;
goto v_reusejp_595_;
}
v_reusejp_595_:
{
return v___x_596_;
}
}
}
else
{
lean_object* v___x_599_; 
lean_dec(v___x_590_);
v___x_599_ = l_Lean_Elab_Tactic_VCGen_mkBackwardRuleForSplit(v_splitInfo_571_, v_info_572_, v_a_576_, v_a_577_, v_a_578_, v_a_579_);
if (lean_obj_tag(v___x_599_) == 0)
{
lean_object* v_a_600_; lean_object* v___x_601_; 
v_a_600_ = lean_ctor_get(v___x_599_, 0);
lean_inc(v_a_600_);
lean_dec_ref_known(v___x_599_, 1);
v___x_601_ = l_Lean_Meta_Sym_BackwardRule_shareCommon(v_a_600_, v_a_574_, v_a_575_, v_a_576_, v_a_577_, v_a_578_, v_a_579_);
if (lean_obj_tag(v___x_601_) == 0)
{
lean_object* v_a_602_; lean_object* v___x_604_; uint8_t v_isShared_605_; uint8_t v_isSharedCheck_629_; 
v_a_602_ = lean_ctor_get(v___x_601_, 0);
v_isSharedCheck_629_ = !lean_is_exclusive(v___x_601_);
if (v_isSharedCheck_629_ == 0)
{
v___x_604_ = v___x_601_;
v_isShared_605_ = v_isSharedCheck_629_;
goto v_resetjp_603_;
}
else
{
lean_inc(v_a_602_);
lean_dec(v___x_601_);
v___x_604_ = lean_box(0);
v_isShared_605_ = v_isSharedCheck_629_;
goto v_resetjp_603_;
}
v_resetjp_603_:
{
lean_object* v___x_606_; lean_object* v_specBackwardRuleCache_607_; lean_object* v_splitBackwardRuleCache_608_; lean_object* v_latticeBackwardRuleCache_609_; lean_object* v_frameBackwardRuleCache_610_; lean_object* v_frameDB_611_; lean_object* v_invariants_612_; lean_object* v_vcs_613_; lean_object* v_simpState_614_; lean_object* v_fuel_615_; lean_object* v_inlineHandledInvariants_616_; lean_object* v___x_618_; uint8_t v_isShared_619_; uint8_t v_isSharedCheck_628_; 
v___x_606_ = lean_st_ref_take(v_a_573_);
v_specBackwardRuleCache_607_ = lean_ctor_get(v___x_606_, 0);
v_splitBackwardRuleCache_608_ = lean_ctor_get(v___x_606_, 1);
v_latticeBackwardRuleCache_609_ = lean_ctor_get(v___x_606_, 2);
v_frameBackwardRuleCache_610_ = lean_ctor_get(v___x_606_, 3);
v_frameDB_611_ = lean_ctor_get(v___x_606_, 4);
v_invariants_612_ = lean_ctor_get(v___x_606_, 5);
v_vcs_613_ = lean_ctor_get(v___x_606_, 6);
v_simpState_614_ = lean_ctor_get(v___x_606_, 7);
v_fuel_615_ = lean_ctor_get(v___x_606_, 8);
v_inlineHandledInvariants_616_ = lean_ctor_get(v___x_606_, 9);
v_isSharedCheck_628_ = !lean_is_exclusive(v___x_606_);
if (v_isSharedCheck_628_ == 0)
{
v___x_618_ = v___x_606_;
v_isShared_619_ = v_isSharedCheck_628_;
goto v_resetjp_617_;
}
else
{
lean_inc(v_inlineHandledInvariants_616_);
lean_inc(v_fuel_615_);
lean_inc(v_simpState_614_);
lean_inc(v_vcs_613_);
lean_inc(v_invariants_612_);
lean_inc(v_frameDB_611_);
lean_inc(v_frameBackwardRuleCache_610_);
lean_inc(v_latticeBackwardRuleCache_609_);
lean_inc(v_splitBackwardRuleCache_608_);
lean_inc(v_specBackwardRuleCache_607_);
lean_dec(v___x_606_);
v___x_618_ = lean_box(0);
v_isShared_619_ = v_isSharedCheck_628_;
goto v_resetjp_617_;
}
v_resetjp_617_:
{
lean_object* v___x_620_; lean_object* v___x_622_; 
lean_inc(v_a_602_);
v___x_620_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2___redArg(v_splitBackwardRuleCache_608_, v_key_587_, v_a_602_);
if (v_isShared_619_ == 0)
{
lean_ctor_set(v___x_618_, 1, v___x_620_);
v___x_622_ = v___x_618_;
goto v_reusejp_621_;
}
else
{
lean_object* v_reuseFailAlloc_627_; 
v_reuseFailAlloc_627_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_627_, 0, v_specBackwardRuleCache_607_);
lean_ctor_set(v_reuseFailAlloc_627_, 1, v___x_620_);
lean_ctor_set(v_reuseFailAlloc_627_, 2, v_latticeBackwardRuleCache_609_);
lean_ctor_set(v_reuseFailAlloc_627_, 3, v_frameBackwardRuleCache_610_);
lean_ctor_set(v_reuseFailAlloc_627_, 4, v_frameDB_611_);
lean_ctor_set(v_reuseFailAlloc_627_, 5, v_invariants_612_);
lean_ctor_set(v_reuseFailAlloc_627_, 6, v_vcs_613_);
lean_ctor_set(v_reuseFailAlloc_627_, 7, v_simpState_614_);
lean_ctor_set(v_reuseFailAlloc_627_, 8, v_fuel_615_);
lean_ctor_set(v_reuseFailAlloc_627_, 9, v_inlineHandledInvariants_616_);
v___x_622_ = v_reuseFailAlloc_627_;
goto v_reusejp_621_;
}
v_reusejp_621_:
{
lean_object* v___x_623_; lean_object* v___x_625_; 
v___x_623_ = lean_st_ref_put(v_a_573_, v___x_622_);
if (v_isShared_605_ == 0)
{
v___x_625_ = v___x_604_;
goto v_reusejp_624_;
}
else
{
lean_object* v_reuseFailAlloc_626_; 
v_reuseFailAlloc_626_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_626_, 0, v_a_602_);
v___x_625_ = v_reuseFailAlloc_626_;
goto v_reusejp_624_;
}
v_reusejp_624_:
{
return v___x_625_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_key_587_, 2);
return v___x_601_;
}
}
else
{
lean_dec_ref_known(v_key_587_, 2);
return v___x_599_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_VCGen_mkBackwardRuleForSplitCached___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_splitInfo_571_ = stack[0].m_obj;
lean_object* v_info_572_ = stack[1].m_obj;
lean_object* v_a_573_ = stack[2].m_obj;
lean_object* v_a_574_ = stack[3].m_obj;
lean_object* v_a_575_ = stack[4].m_obj;
lean_object* v_a_576_ = stack[5].m_obj;
lean_object* v_a_577_ = stack[6].m_obj;
lean_object* v_a_578_ = stack[7].m_obj;
lean_object* v_a_579_ = stack[8].m_obj;
lean_object* v_res_635_;
v_res_635_ = l_Lean_Elab_Tactic_VCGen_mkBackwardRuleForSplitCached___redArg(v_splitInfo_571_, v_info_572_, v_a_573_, v_a_574_, v_a_575_, v_a_576_, v_a_577_, v_a_578_, v_a_579_);
stack->m_obj
 = v_res_635_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_mkBackwardRuleForSplitCached___redArg___boxed(lean_object* v_splitInfo_636_, lean_object* v_info_637_, lean_object* v_a_638_, lean_object* v_a_639_, lean_object* v_a_640_, lean_object* v_a_641_, lean_object* v_a_642_, lean_object* v_a_643_, lean_object* v_a_644_, lean_object* v_a_645_){
_start:
{
lean_object* v_res_646_; 
v_res_646_ = l_Lean_Elab_Tactic_VCGen_mkBackwardRuleForSplitCached___redArg(v_splitInfo_636_, v_info_637_, v_a_638_, v_a_639_, v_a_640_, v_a_641_, v_a_642_, v_a_643_, v_a_644_);
lean_dec(v_a_644_);
lean_dec_ref(v_a_643_);
lean_dec(v_a_642_);
lean_dec_ref(v_a_641_);
lean_dec(v_a_640_);
lean_dec_ref(v_a_639_);
lean_dec(v_a_638_);
return v_res_646_;
}
}
lean_object* l_Lean_Elab_Tactic_VCGen_mkBackwardRuleForSplitCached(lean_object* v_splitInfo_647_, lean_object* v_info_648_, lean_object* v_a_649_, lean_object* v_a_650_, lean_object* v_a_651_, lean_object* v_a_652_, lean_object* v_a_653_, lean_object* v_a_654_, lean_object* v_a_655_, lean_object* v_a_656_, lean_object* v_a_657_, lean_object* v_a_658_, lean_object* v_a_659_){
_start:
{
lean_object* v___x_661_; 
v___x_661_ = l_Lean_Elab_Tactic_VCGen_mkBackwardRuleForSplitCached___redArg(v_splitInfo_647_, v_info_648_, v_a_650_, v_a_654_, v_a_655_, v_a_656_, v_a_657_, v_a_658_, v_a_659_);
return v___x_661_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_VCGen_mkBackwardRuleForSplitCached_0interp(lean_interpreter_value* stack)
{
lean_object* v_splitInfo_647_ = stack[0].m_obj;
lean_object* v_info_648_ = stack[1].m_obj;
lean_object* v_a_649_ = stack[2].m_obj;
lean_object* v_a_650_ = stack[3].m_obj;
lean_object* v_a_651_ = stack[4].m_obj;
lean_object* v_a_652_ = stack[5].m_obj;
lean_object* v_a_653_ = stack[6].m_obj;
lean_object* v_a_654_ = stack[7].m_obj;
lean_object* v_a_655_ = stack[8].m_obj;
lean_object* v_a_656_ = stack[9].m_obj;
lean_object* v_a_657_ = stack[10].m_obj;
lean_object* v_a_658_ = stack[11].m_obj;
lean_object* v_a_659_ = stack[12].m_obj;
lean_object* v_res_662_;
v_res_662_ = l_Lean_Elab_Tactic_VCGen_mkBackwardRuleForSplitCached(v_splitInfo_647_, v_info_648_, v_a_649_, v_a_650_, v_a_651_, v_a_652_, v_a_653_, v_a_654_, v_a_655_, v_a_656_, v_a_657_, v_a_658_, v_a_659_);
stack->m_obj
 = v_res_662_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_mkBackwardRuleForSplitCached___boxed(lean_object* v_splitInfo_663_, lean_object* v_info_664_, lean_object* v_a_665_, lean_object* v_a_666_, lean_object* v_a_667_, lean_object* v_a_668_, lean_object* v_a_669_, lean_object* v_a_670_, lean_object* v_a_671_, lean_object* v_a_672_, lean_object* v_a_673_, lean_object* v_a_674_, lean_object* v_a_675_, lean_object* v_a_676_){
_start:
{
lean_object* v_res_677_; 
v_res_677_ = l_Lean_Elab_Tactic_VCGen_mkBackwardRuleForSplitCached(v_splitInfo_663_, v_info_664_, v_a_665_, v_a_666_, v_a_667_, v_a_668_, v_a_669_, v_a_670_, v_a_671_, v_a_672_, v_a_673_, v_a_674_, v_a_675_);
lean_dec(v_a_675_);
lean_dec_ref(v_a_674_);
lean_dec(v_a_673_);
lean_dec_ref(v_a_672_);
lean_dec(v_a_671_);
lean_dec_ref(v_a_670_);
lean_dec(v_a_669_);
lean_dec_ref(v_a_668_);
lean_dec(v_a_667_);
lean_dec(v_a_666_);
lean_dec_ref(v_a_665_);
return v_res_677_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1_spec__2___redArg(lean_object* v_a_678_, lean_object* v_x_679_){
_start:
{
if (lean_obj_tag(v_x_679_) == 0)
{
uint8_t v___x_680_; 
v___x_680_ = 0;
return v___x_680_;
}
else
{
lean_object* v_key_681_; lean_object* v_tail_682_; lean_object* v_fst_683_; lean_object* v_snd_684_; lean_object* v_fst_685_; lean_object* v_snd_686_; size_t v___x_687_; size_t v___x_688_; uint8_t v___x_689_; 
v_key_681_ = lean_ctor_get(v_x_679_, 0);
v_tail_682_ = lean_ctor_get(v_x_679_, 2);
v_fst_683_ = lean_ctor_get(v_key_681_, 0);
v_snd_684_ = lean_ctor_get(v_key_681_, 1);
v_fst_685_ = lean_ctor_get(v_a_678_, 0);
v_snd_686_ = lean_ctor_get(v_a_678_, 1);
v___x_687_ = lean_ptr_addr(v_fst_683_);
v___x_688_ = lean_ptr_addr(v_fst_685_);
v___x_689_ = lean_usize_dec_eq(v___x_687_, v___x_688_);
if (v___x_689_ == 0)
{
v_x_679_ = v_tail_682_;
goto _start;
}
else
{
uint8_t v___x_691_; 
v___x_691_ = lean_nat_dec_eq(v_snd_684_, v_snd_686_);
if (v___x_691_ == 0)
{
v_x_679_ = v_tail_682_;
goto _start;
}
else
{
return v___x_691_;
}
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_678_ = stack[0].m_obj;
lean_object* v_x_679_ = stack[1].m_obj;
uint8_t v_res_693_;
v_res_693_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1_spec__2___redArg(v_a_678_, v_x_679_);
stack->m_num = v_res_693_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1_spec__2___redArg___boxed(lean_object* v_a_694_, lean_object* v_x_695_){
_start:
{
uint8_t v_res_696_; lean_object* v_r_697_; 
v_res_696_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1_spec__2___redArg(v_a_694_, v_x_695_);
lean_dec(v_x_695_);
lean_dec_ref(v_a_694_);
v_r_697_ = lean_box(v_res_696_);
return v_r_697_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1_spec__4___redArg(lean_object* v_a_698_, lean_object* v_b_699_, lean_object* v_x_700_){
_start:
{
if (lean_obj_tag(v_x_700_) == 0)
{
lean_dec(v_b_699_);
lean_dec_ref(v_a_698_);
return v_x_700_;
}
else
{
lean_object* v_key_701_; lean_object* v_value_702_; lean_object* v_tail_703_; lean_object* v___x_705_; uint8_t v_isShared_706_; uint8_t v_isSharedCheck_721_; 
v_key_701_ = lean_ctor_get(v_x_700_, 0);
v_value_702_ = lean_ctor_get(v_x_700_, 1);
v_tail_703_ = lean_ctor_get(v_x_700_, 2);
v_isSharedCheck_721_ = !lean_is_exclusive(v_x_700_);
if (v_isSharedCheck_721_ == 0)
{
v___x_705_ = v_x_700_;
v_isShared_706_ = v_isSharedCheck_721_;
goto v_resetjp_704_;
}
else
{
lean_inc(v_tail_703_);
lean_inc(v_value_702_);
lean_inc(v_key_701_);
lean_dec(v_x_700_);
v___x_705_ = lean_box(0);
v_isShared_706_ = v_isSharedCheck_721_;
goto v_resetjp_704_;
}
v_resetjp_704_:
{
lean_object* v_fst_712_; lean_object* v_snd_713_; lean_object* v_fst_714_; lean_object* v_snd_715_; size_t v___x_716_; size_t v___x_717_; uint8_t v___x_718_; 
v_fst_712_ = lean_ctor_get(v_key_701_, 0);
v_snd_713_ = lean_ctor_get(v_key_701_, 1);
v_fst_714_ = lean_ctor_get(v_a_698_, 0);
v_snd_715_ = lean_ctor_get(v_a_698_, 1);
v___x_716_ = lean_ptr_addr(v_fst_712_);
v___x_717_ = lean_ptr_addr(v_fst_714_);
v___x_718_ = lean_usize_dec_eq(v___x_716_, v___x_717_);
if (v___x_718_ == 0)
{
goto v___jp_707_;
}
else
{
uint8_t v___x_719_; 
v___x_719_ = lean_nat_dec_eq(v_snd_713_, v_snd_715_);
if (v___x_719_ == 0)
{
goto v___jp_707_;
}
else
{
lean_object* v___x_720_; 
lean_del_object(v___x_705_);
lean_dec(v_value_702_);
lean_dec(v_key_701_);
v___x_720_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_720_, 0, v_a_698_);
lean_ctor_set(v___x_720_, 1, v_b_699_);
lean_ctor_set(v___x_720_, 2, v_tail_703_);
return v___x_720_;
}
}
v___jp_707_:
{
lean_object* v___x_708_; lean_object* v___x_710_; 
v___x_708_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1_spec__4___redArg(v_a_698_, v_b_699_, v_tail_703_);
if (v_isShared_706_ == 0)
{
lean_ctor_set(v___x_705_, 2, v___x_708_);
v___x_710_ = v___x_705_;
goto v_reusejp_709_;
}
else
{
lean_object* v_reuseFailAlloc_711_; 
v_reuseFailAlloc_711_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_711_, 0, v_key_701_);
lean_ctor_set(v_reuseFailAlloc_711_, 1, v_value_702_);
lean_ctor_set(v_reuseFailAlloc_711_, 2, v___x_708_);
v___x_710_ = v_reuseFailAlloc_711_;
goto v_reusejp_709_;
}
v_reusejp_709_:
{
return v___x_710_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1_spec__3_spec__4_spec__5___redArg(lean_object* v_x_722_, lean_object* v_x_723_){
_start:
{
if (lean_obj_tag(v_x_723_) == 0)
{
return v_x_722_;
}
else
{
lean_object* v_key_724_; lean_object* v_value_725_; lean_object* v_tail_726_; lean_object* v___x_728_; uint8_t v_isShared_729_; uint8_t v_isSharedCheck_756_; 
v_key_724_ = lean_ctor_get(v_x_723_, 0);
v_value_725_ = lean_ctor_get(v_x_723_, 1);
v_tail_726_ = lean_ctor_get(v_x_723_, 2);
v_isSharedCheck_756_ = !lean_is_exclusive(v_x_723_);
if (v_isSharedCheck_756_ == 0)
{
v___x_728_ = v_x_723_;
v_isShared_729_ = v_isSharedCheck_756_;
goto v_resetjp_727_;
}
else
{
lean_inc(v_tail_726_);
lean_inc(v_value_725_);
lean_inc(v_key_724_);
lean_dec(v_x_723_);
v___x_728_ = lean_box(0);
v_isShared_729_ = v_isSharedCheck_756_;
goto v_resetjp_727_;
}
v_resetjp_727_:
{
lean_object* v_fst_730_; lean_object* v_snd_731_; lean_object* v___x_732_; size_t v___x_733_; size_t v___x_734_; size_t v___x_735_; uint64_t v___x_736_; uint64_t v___x_737_; uint64_t v___x_738_; uint64_t v___x_739_; uint64_t v___x_740_; uint64_t v_fold_741_; uint64_t v___x_742_; uint64_t v___x_743_; uint64_t v___x_744_; size_t v___x_745_; size_t v___x_746_; size_t v___x_747_; size_t v___x_748_; size_t v___x_749_; lean_object* v___x_750_; lean_object* v___x_752_; 
v_fst_730_ = lean_ctor_get(v_key_724_, 0);
v_snd_731_ = lean_ctor_get(v_key_724_, 1);
v___x_732_ = lean_array_get_size(v_x_722_);
v___x_733_ = lean_ptr_addr(v_fst_730_);
v___x_734_ = ((size_t)3ULL);
v___x_735_ = lean_usize_shift_right(v___x_733_, v___x_734_);
v___x_736_ = lean_usize_to_uint64(v___x_735_);
v___x_737_ = lean_uint64_of_nat(v_snd_731_);
v___x_738_ = lean_uint64_mix_hash(v___x_736_, v___x_737_);
v___x_739_ = 32ULL;
v___x_740_ = lean_uint64_shift_right(v___x_738_, v___x_739_);
v_fold_741_ = lean_uint64_xor(v___x_738_, v___x_740_);
v___x_742_ = 16ULL;
v___x_743_ = lean_uint64_shift_right(v_fold_741_, v___x_742_);
v___x_744_ = lean_uint64_xor(v_fold_741_, v___x_743_);
v___x_745_ = lean_uint64_to_usize(v___x_744_);
v___x_746_ = lean_usize_of_nat(v___x_732_);
v___x_747_ = ((size_t)1ULL);
v___x_748_ = lean_usize_sub(v___x_746_, v___x_747_);
v___x_749_ = lean_usize_land(v___x_745_, v___x_748_);
v___x_750_ = lean_array_uget_borrowed(v_x_722_, v___x_749_);
lean_inc(v___x_750_);
if (v_isShared_729_ == 0)
{
lean_ctor_set(v___x_728_, 2, v___x_750_);
v___x_752_ = v___x_728_;
goto v_reusejp_751_;
}
else
{
lean_object* v_reuseFailAlloc_755_; 
v_reuseFailAlloc_755_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_755_, 0, v_key_724_);
lean_ctor_set(v_reuseFailAlloc_755_, 1, v_value_725_);
lean_ctor_set(v_reuseFailAlloc_755_, 2, v___x_750_);
v___x_752_ = v_reuseFailAlloc_755_;
goto v_reusejp_751_;
}
v_reusejp_751_:
{
lean_object* v___x_753_; 
v___x_753_ = lean_array_uset(v_x_722_, v___x_749_, v___x_752_);
v_x_722_ = v___x_753_;
v_x_723_ = v_tail_726_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1_spec__3_spec__4___redArg(lean_object* v_i_757_, lean_object* v_source_758_, lean_object* v_target_759_){
_start:
{
lean_object* v___x_760_; uint8_t v___x_761_; 
v___x_760_ = lean_array_get_size(v_source_758_);
v___x_761_ = lean_nat_dec_lt(v_i_757_, v___x_760_);
if (v___x_761_ == 0)
{
lean_dec_ref(v_source_758_);
lean_dec(v_i_757_);
return v_target_759_;
}
else
{
lean_object* v_es_762_; lean_object* v___x_763_; lean_object* v_source_764_; lean_object* v_target_765_; lean_object* v___x_766_; lean_object* v___x_767_; 
v_es_762_ = lean_array_fget(v_source_758_, v_i_757_);
v___x_763_ = lean_box(0);
v_source_764_ = lean_array_fset(v_source_758_, v_i_757_, v___x_763_);
v_target_765_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1_spec__3_spec__4_spec__5___redArg(v_target_759_, v_es_762_);
v___x_766_ = lean_unsigned_to_nat(1u);
v___x_767_ = lean_nat_add(v_i_757_, v___x_766_);
lean_dec(v_i_757_);
v_i_757_ = v___x_767_;
v_source_758_ = v_source_764_;
v_target_759_ = v_target_765_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1_spec__3___redArg(lean_object* v_data_769_){
_start:
{
lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v_nbuckets_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; 
v___x_770_ = lean_array_get_size(v_data_769_);
v___x_771_ = lean_unsigned_to_nat(2u);
v_nbuckets_772_ = lean_nat_mul(v___x_770_, v___x_771_);
v___x_773_ = lean_unsigned_to_nat(0u);
v___x_774_ = lean_box(0);
v___x_775_ = lean_mk_array(v_nbuckets_772_, v___x_774_);
v___x_776_ = lean_array_propagate_mark(v_data_769_, v___x_775_);
v___x_777_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1_spec__3_spec__4___redArg(v___x_773_, v_data_769_, v___x_776_);
return v___x_777_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1___redArg(lean_object* v_m_778_, lean_object* v_a_779_, lean_object* v_b_780_){
_start:
{
lean_object* v_size_781_; lean_object* v_buckets_782_; lean_object* v___x_784_; uint8_t v_isShared_785_; uint8_t v_isSharedCheck_832_; 
v_size_781_ = lean_ctor_get(v_m_778_, 0);
v_buckets_782_ = lean_ctor_get(v_m_778_, 1);
v_isSharedCheck_832_ = !lean_is_exclusive(v_m_778_);
if (v_isSharedCheck_832_ == 0)
{
v___x_784_ = v_m_778_;
v_isShared_785_ = v_isSharedCheck_832_;
goto v_resetjp_783_;
}
else
{
lean_inc(v_buckets_782_);
lean_inc(v_size_781_);
lean_dec(v_m_778_);
v___x_784_ = lean_box(0);
v_isShared_785_ = v_isSharedCheck_832_;
goto v_resetjp_783_;
}
v_resetjp_783_:
{
lean_object* v_fst_786_; lean_object* v_snd_787_; lean_object* v___x_788_; size_t v___x_789_; size_t v___x_790_; size_t v___x_791_; uint64_t v___x_792_; uint64_t v___x_793_; uint64_t v___x_794_; uint64_t v___x_795_; uint64_t v___x_796_; uint64_t v_fold_797_; uint64_t v___x_798_; uint64_t v___x_799_; uint64_t v___x_800_; size_t v___x_801_; size_t v___x_802_; size_t v___x_803_; size_t v___x_804_; size_t v___x_805_; lean_object* v_bkt_806_; uint8_t v___x_807_; 
v_fst_786_ = lean_ctor_get(v_a_779_, 0);
v_snd_787_ = lean_ctor_get(v_a_779_, 1);
v___x_788_ = lean_array_get_size(v_buckets_782_);
v___x_789_ = lean_ptr_addr(v_fst_786_);
v___x_790_ = ((size_t)3ULL);
v___x_791_ = lean_usize_shift_right(v___x_789_, v___x_790_);
v___x_792_ = lean_usize_to_uint64(v___x_791_);
v___x_793_ = lean_uint64_of_nat(v_snd_787_);
v___x_794_ = lean_uint64_mix_hash(v___x_792_, v___x_793_);
v___x_795_ = 32ULL;
v___x_796_ = lean_uint64_shift_right(v___x_794_, v___x_795_);
v_fold_797_ = lean_uint64_xor(v___x_794_, v___x_796_);
v___x_798_ = 16ULL;
v___x_799_ = lean_uint64_shift_right(v_fold_797_, v___x_798_);
v___x_800_ = lean_uint64_xor(v_fold_797_, v___x_799_);
v___x_801_ = lean_uint64_to_usize(v___x_800_);
v___x_802_ = lean_usize_of_nat(v___x_788_);
v___x_803_ = ((size_t)1ULL);
v___x_804_ = lean_usize_sub(v___x_802_, v___x_803_);
v___x_805_ = lean_usize_land(v___x_801_, v___x_804_);
v_bkt_806_ = lean_array_uget_borrowed(v_buckets_782_, v___x_805_);
v___x_807_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1_spec__2___redArg(v_a_779_, v_bkt_806_);
if (v___x_807_ == 0)
{
lean_object* v___x_808_; lean_object* v_size_x27_809_; lean_object* v___x_810_; lean_object* v_buckets_x27_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; uint8_t v___x_817_; 
v___x_808_ = lean_unsigned_to_nat(1u);
v_size_x27_809_ = lean_nat_add(v_size_781_, v___x_808_);
lean_dec(v_size_781_);
lean_inc(v_bkt_806_);
v___x_810_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_810_, 0, v_a_779_);
lean_ctor_set(v___x_810_, 1, v_b_780_);
lean_ctor_set(v___x_810_, 2, v_bkt_806_);
v_buckets_x27_811_ = lean_array_uset(v_buckets_782_, v___x_805_, v___x_810_);
v___x_812_ = lean_unsigned_to_nat(4u);
v___x_813_ = lean_nat_mul(v_size_x27_809_, v___x_812_);
v___x_814_ = lean_unsigned_to_nat(3u);
v___x_815_ = lean_nat_div(v___x_813_, v___x_814_);
lean_dec(v___x_813_);
v___x_816_ = lean_array_get_size(v_buckets_x27_811_);
v___x_817_ = lean_nat_dec_le(v___x_815_, v___x_816_);
lean_dec(v___x_815_);
if (v___x_817_ == 0)
{
lean_object* v_val_818_; lean_object* v___x_820_; 
v_val_818_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1_spec__3___redArg(v_buckets_x27_811_);
if (v_isShared_785_ == 0)
{
lean_ctor_set(v___x_784_, 1, v_val_818_);
lean_ctor_set(v___x_784_, 0, v_size_x27_809_);
v___x_820_ = v___x_784_;
goto v_reusejp_819_;
}
else
{
lean_object* v_reuseFailAlloc_821_; 
v_reuseFailAlloc_821_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_821_, 0, v_size_x27_809_);
lean_ctor_set(v_reuseFailAlloc_821_, 1, v_val_818_);
v___x_820_ = v_reuseFailAlloc_821_;
goto v_reusejp_819_;
}
v_reusejp_819_:
{
return v___x_820_;
}
}
else
{
lean_object* v___x_823_; 
if (v_isShared_785_ == 0)
{
lean_ctor_set(v___x_784_, 1, v_buckets_x27_811_);
lean_ctor_set(v___x_784_, 0, v_size_x27_809_);
v___x_823_ = v___x_784_;
goto v_reusejp_822_;
}
else
{
lean_object* v_reuseFailAlloc_824_; 
v_reuseFailAlloc_824_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_824_, 0, v_size_x27_809_);
lean_ctor_set(v_reuseFailAlloc_824_, 1, v_buckets_x27_811_);
v___x_823_ = v_reuseFailAlloc_824_;
goto v_reusejp_822_;
}
v_reusejp_822_:
{
return v___x_823_;
}
}
}
else
{
lean_object* v___x_825_; lean_object* v_buckets_x27_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_830_; 
lean_inc(v_bkt_806_);
v___x_825_ = lean_box(0);
v_buckets_x27_826_ = lean_array_uset(v_buckets_782_, v___x_805_, v___x_825_);
v___x_827_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1_spec__4___redArg(v_a_779_, v_b_780_, v_bkt_806_);
v___x_828_ = lean_array_uset(v_buckets_x27_826_, v___x_805_, v___x_827_);
if (v_isShared_785_ == 0)
{
lean_ctor_set(v___x_784_, 1, v___x_828_);
v___x_830_ = v___x_784_;
goto v_reusejp_829_;
}
else
{
lean_object* v_reuseFailAlloc_831_; 
v_reuseFailAlloc_831_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_831_, 0, v_size_781_);
lean_ctor_set(v_reuseFailAlloc_831_, 1, v___x_828_);
v___x_830_ = v_reuseFailAlloc_831_;
goto v_reusejp_829_;
}
v_reusejp_829_:
{
return v___x_830_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__0_spec__0___redArg(lean_object* v_a_833_, lean_object* v_x_834_){
_start:
{
if (lean_obj_tag(v_x_834_) == 0)
{
lean_object* v___x_835_; 
v___x_835_ = lean_box(0);
return v___x_835_;
}
else
{
lean_object* v_key_836_; lean_object* v_value_837_; lean_object* v_tail_838_; lean_object* v_fst_839_; lean_object* v_snd_840_; lean_object* v_fst_841_; lean_object* v_snd_842_; size_t v___x_843_; size_t v___x_844_; uint8_t v___x_845_; 
v_key_836_ = lean_ctor_get(v_x_834_, 0);
v_value_837_ = lean_ctor_get(v_x_834_, 1);
v_tail_838_ = lean_ctor_get(v_x_834_, 2);
v_fst_839_ = lean_ctor_get(v_key_836_, 0);
v_snd_840_ = lean_ctor_get(v_key_836_, 1);
v_fst_841_ = lean_ctor_get(v_a_833_, 0);
v_snd_842_ = lean_ctor_get(v_a_833_, 1);
v___x_843_ = lean_ptr_addr(v_fst_839_);
v___x_844_ = lean_ptr_addr(v_fst_841_);
v___x_845_ = lean_usize_dec_eq(v___x_843_, v___x_844_);
if (v___x_845_ == 0)
{
v_x_834_ = v_tail_838_;
goto _start;
}
else
{
uint8_t v___x_847_; 
v___x_847_ = lean_nat_dec_eq(v_snd_840_, v_snd_842_);
if (v___x_847_ == 0)
{
v_x_834_ = v_tail_838_;
goto _start;
}
else
{
lean_object* v___x_849_; 
lean_inc(v_value_837_);
v___x_849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_849_, 0, v_value_837_);
return v___x_849_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__0_spec__0___redArg___boxed(lean_object* v_a_850_, lean_object* v_x_851_){
_start:
{
lean_object* v_res_852_; 
v_res_852_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__0_spec__0___redArg(v_a_850_, v_x_851_);
lean_dec(v_x_851_);
lean_dec_ref(v_a_850_);
return v_res_852_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__0___redArg(lean_object* v_m_853_, lean_object* v_a_854_){
_start:
{
lean_object* v_buckets_855_; lean_object* v_fst_856_; lean_object* v_snd_857_; lean_object* v___x_858_; size_t v___x_859_; size_t v___x_860_; size_t v___x_861_; uint64_t v___x_862_; uint64_t v___x_863_; uint64_t v___x_864_; uint64_t v___x_865_; uint64_t v___x_866_; uint64_t v_fold_867_; uint64_t v___x_868_; uint64_t v___x_869_; uint64_t v___x_870_; size_t v___x_871_; size_t v___x_872_; size_t v___x_873_; size_t v___x_874_; size_t v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; 
v_buckets_855_ = lean_ctor_get(v_m_853_, 1);
v_fst_856_ = lean_ctor_get(v_a_854_, 0);
v_snd_857_ = lean_ctor_get(v_a_854_, 1);
v___x_858_ = lean_array_get_size(v_buckets_855_);
v___x_859_ = lean_ptr_addr(v_fst_856_);
v___x_860_ = ((size_t)3ULL);
v___x_861_ = lean_usize_shift_right(v___x_859_, v___x_860_);
v___x_862_ = lean_usize_to_uint64(v___x_861_);
v___x_863_ = lean_uint64_of_nat(v_snd_857_);
v___x_864_ = lean_uint64_mix_hash(v___x_862_, v___x_863_);
v___x_865_ = 32ULL;
v___x_866_ = lean_uint64_shift_right(v___x_864_, v___x_865_);
v_fold_867_ = lean_uint64_xor(v___x_864_, v___x_866_);
v___x_868_ = 16ULL;
v___x_869_ = lean_uint64_shift_right(v_fold_867_, v___x_868_);
v___x_870_ = lean_uint64_xor(v_fold_867_, v___x_869_);
v___x_871_ = lean_uint64_to_usize(v___x_870_);
v___x_872_ = lean_usize_of_nat(v___x_858_);
v___x_873_ = ((size_t)1ULL);
v___x_874_ = lean_usize_sub(v___x_872_, v___x_873_);
v___x_875_ = lean_usize_land(v___x_871_, v___x_874_);
v___x_876_ = lean_array_uget_borrowed(v_buckets_855_, v___x_875_);
v___x_877_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__0_spec__0___redArg(v_a_854_, v___x_876_);
return v___x_877_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__0___redArg___boxed(lean_object* v_m_878_, lean_object* v_a_879_){
_start:
{
lean_object* v_res_880_; 
v_res_880_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__0___redArg(v_m_878_, v_a_879_);
lean_dec_ref(v_a_879_);
lean_dec_ref(v_m_878_);
return v_res_880_;
}
}
lean_object* l_Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached___redArg(lean_object* v_rhs_881_, lean_object* v_op_882_, lean_object* v_a_883_, lean_object* v_a_884_, lean_object* v_a_885_, lean_object* v_a_886_, lean_object* v_a_887_, lean_object* v_a_888_, lean_object* v_a_889_){
_start:
{
lean_object* v_numConst_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v_key_894_; lean_object* v___x_895_; lean_object* v_latticeBackwardRuleCache_896_; lean_object* v___x_897_; 
v_numConst_891_ = lean_ctor_get(v_op_882_, 1);
v___x_892_ = l_Lean_Expr_getAppPrefix(v_rhs_881_, v_numConst_891_);
v___x_893_ = l_Lean_Expr_getAppNumArgs(v_rhs_881_);
v_key_894_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_key_894_, 0, v___x_892_);
lean_ctor_set(v_key_894_, 1, v___x_893_);
v___x_895_ = lean_st_ref_get(v_a_883_);
v_latticeBackwardRuleCache_896_ = lean_ctor_get(v___x_895_, 2);
lean_inc_ref(v_latticeBackwardRuleCache_896_);
lean_dec(v___x_895_);
v___x_897_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__0___redArg(v_latticeBackwardRuleCache_896_, v_key_894_);
lean_dec_ref(v_latticeBackwardRuleCache_896_);
if (lean_obj_tag(v___x_897_) == 1)
{
lean_object* v_val_898_; lean_object* v___x_900_; uint8_t v_isShared_901_; uint8_t v_isSharedCheck_905_; 
lean_dec_ref_known(v_key_894_, 2);
lean_dec_ref(v_op_882_);
lean_dec_ref(v_rhs_881_);
v_val_898_ = lean_ctor_get(v___x_897_, 0);
v_isSharedCheck_905_ = !lean_is_exclusive(v___x_897_);
if (v_isSharedCheck_905_ == 0)
{
v___x_900_ = v___x_897_;
v_isShared_901_ = v_isSharedCheck_905_;
goto v_resetjp_899_;
}
else
{
lean_inc(v_val_898_);
lean_dec(v___x_897_);
v___x_900_ = lean_box(0);
v_isShared_901_ = v_isSharedCheck_905_;
goto v_resetjp_899_;
}
v_resetjp_899_:
{
lean_object* v___x_903_; 
if (v_isShared_901_ == 0)
{
lean_ctor_set_tag(v___x_900_, 0);
v___x_903_ = v___x_900_;
goto v_reusejp_902_;
}
else
{
lean_object* v_reuseFailAlloc_904_; 
v_reuseFailAlloc_904_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_904_, 0, v_val_898_);
v___x_903_ = v_reuseFailAlloc_904_;
goto v_reusejp_902_;
}
v_reusejp_902_:
{
return v___x_903_;
}
}
}
else
{
lean_object* v___x_906_; 
lean_dec(v___x_897_);
v___x_906_ = l_Lean_Elab_Tactic_VCGen_mkLatticeOpRule(v_rhs_881_, v_op_882_, v_a_884_, v_a_885_, v_a_886_, v_a_887_, v_a_888_, v_a_889_);
if (lean_obj_tag(v___x_906_) == 0)
{
lean_object* v_a_907_; lean_object* v___x_908_; 
v_a_907_ = lean_ctor_get(v___x_906_, 0);
lean_inc(v_a_907_);
lean_dec_ref_known(v___x_906_, 1);
v___x_908_ = l_Lean_Meta_Sym_BackwardRule_shareCommon(v_a_907_, v_a_884_, v_a_885_, v_a_886_, v_a_887_, v_a_888_, v_a_889_);
if (lean_obj_tag(v___x_908_) == 0)
{
lean_object* v_a_909_; lean_object* v___x_911_; uint8_t v_isShared_912_; uint8_t v_isSharedCheck_936_; 
v_a_909_ = lean_ctor_get(v___x_908_, 0);
v_isSharedCheck_936_ = !lean_is_exclusive(v___x_908_);
if (v_isSharedCheck_936_ == 0)
{
v___x_911_ = v___x_908_;
v_isShared_912_ = v_isSharedCheck_936_;
goto v_resetjp_910_;
}
else
{
lean_inc(v_a_909_);
lean_dec(v___x_908_);
v___x_911_ = lean_box(0);
v_isShared_912_ = v_isSharedCheck_936_;
goto v_resetjp_910_;
}
v_resetjp_910_:
{
lean_object* v___x_913_; lean_object* v_specBackwardRuleCache_914_; lean_object* v_splitBackwardRuleCache_915_; lean_object* v_latticeBackwardRuleCache_916_; lean_object* v_frameBackwardRuleCache_917_; lean_object* v_frameDB_918_; lean_object* v_invariants_919_; lean_object* v_vcs_920_; lean_object* v_simpState_921_; lean_object* v_fuel_922_; lean_object* v_inlineHandledInvariants_923_; lean_object* v___x_925_; uint8_t v_isShared_926_; uint8_t v_isSharedCheck_935_; 
v___x_913_ = lean_st_ref_take(v_a_883_);
v_specBackwardRuleCache_914_ = lean_ctor_get(v___x_913_, 0);
v_splitBackwardRuleCache_915_ = lean_ctor_get(v___x_913_, 1);
v_latticeBackwardRuleCache_916_ = lean_ctor_get(v___x_913_, 2);
v_frameBackwardRuleCache_917_ = lean_ctor_get(v___x_913_, 3);
v_frameDB_918_ = lean_ctor_get(v___x_913_, 4);
v_invariants_919_ = lean_ctor_get(v___x_913_, 5);
v_vcs_920_ = lean_ctor_get(v___x_913_, 6);
v_simpState_921_ = lean_ctor_get(v___x_913_, 7);
v_fuel_922_ = lean_ctor_get(v___x_913_, 8);
v_inlineHandledInvariants_923_ = lean_ctor_get(v___x_913_, 9);
v_isSharedCheck_935_ = !lean_is_exclusive(v___x_913_);
if (v_isSharedCheck_935_ == 0)
{
v___x_925_ = v___x_913_;
v_isShared_926_ = v_isSharedCheck_935_;
goto v_resetjp_924_;
}
else
{
lean_inc(v_inlineHandledInvariants_923_);
lean_inc(v_fuel_922_);
lean_inc(v_simpState_921_);
lean_inc(v_vcs_920_);
lean_inc(v_invariants_919_);
lean_inc(v_frameDB_918_);
lean_inc(v_frameBackwardRuleCache_917_);
lean_inc(v_latticeBackwardRuleCache_916_);
lean_inc(v_splitBackwardRuleCache_915_);
lean_inc(v_specBackwardRuleCache_914_);
lean_dec(v___x_913_);
v___x_925_ = lean_box(0);
v_isShared_926_ = v_isSharedCheck_935_;
goto v_resetjp_924_;
}
v_resetjp_924_:
{
lean_object* v___x_927_; lean_object* v___x_929_; 
lean_inc(v_a_909_);
v___x_927_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1___redArg(v_latticeBackwardRuleCache_916_, v_key_894_, v_a_909_);
if (v_isShared_926_ == 0)
{
lean_ctor_set(v___x_925_, 2, v___x_927_);
v___x_929_ = v___x_925_;
goto v_reusejp_928_;
}
else
{
lean_object* v_reuseFailAlloc_934_; 
v_reuseFailAlloc_934_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_934_, 0, v_specBackwardRuleCache_914_);
lean_ctor_set(v_reuseFailAlloc_934_, 1, v_splitBackwardRuleCache_915_);
lean_ctor_set(v_reuseFailAlloc_934_, 2, v___x_927_);
lean_ctor_set(v_reuseFailAlloc_934_, 3, v_frameBackwardRuleCache_917_);
lean_ctor_set(v_reuseFailAlloc_934_, 4, v_frameDB_918_);
lean_ctor_set(v_reuseFailAlloc_934_, 5, v_invariants_919_);
lean_ctor_set(v_reuseFailAlloc_934_, 6, v_vcs_920_);
lean_ctor_set(v_reuseFailAlloc_934_, 7, v_simpState_921_);
lean_ctor_set(v_reuseFailAlloc_934_, 8, v_fuel_922_);
lean_ctor_set(v_reuseFailAlloc_934_, 9, v_inlineHandledInvariants_923_);
v___x_929_ = v_reuseFailAlloc_934_;
goto v_reusejp_928_;
}
v_reusejp_928_:
{
lean_object* v___x_930_; lean_object* v___x_932_; 
v___x_930_ = lean_st_ref_put(v_a_883_, v___x_929_);
if (v_isShared_912_ == 0)
{
v___x_932_ = v___x_911_;
goto v_reusejp_931_;
}
else
{
lean_object* v_reuseFailAlloc_933_; 
v_reuseFailAlloc_933_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_933_, 0, v_a_909_);
v___x_932_ = v_reuseFailAlloc_933_;
goto v_reusejp_931_;
}
v_reusejp_931_:
{
return v___x_932_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_key_894_, 2);
return v___x_908_;
}
}
else
{
lean_dec_ref_known(v_key_894_, 2);
return v___x_906_;
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_rhs_881_ = stack[0].m_obj;
lean_object* v_op_882_ = stack[1].m_obj;
lean_object* v_a_883_ = stack[2].m_obj;
lean_object* v_a_884_ = stack[3].m_obj;
lean_object* v_a_885_ = stack[4].m_obj;
lean_object* v_a_886_ = stack[5].m_obj;
lean_object* v_a_887_ = stack[6].m_obj;
lean_object* v_a_888_ = stack[7].m_obj;
lean_object* v_a_889_ = stack[8].m_obj;
lean_object* v_res_937_;
v_res_937_ = l_Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached___redArg(v_rhs_881_, v_op_882_, v_a_883_, v_a_884_, v_a_885_, v_a_886_, v_a_887_, v_a_888_, v_a_889_);
stack->m_obj
 = v_res_937_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached___redArg___boxed(lean_object* v_rhs_938_, lean_object* v_op_939_, lean_object* v_a_940_, lean_object* v_a_941_, lean_object* v_a_942_, lean_object* v_a_943_, lean_object* v_a_944_, lean_object* v_a_945_, lean_object* v_a_946_, lean_object* v_a_947_){
_start:
{
lean_object* v_res_948_; 
v_res_948_ = l_Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached___redArg(v_rhs_938_, v_op_939_, v_a_940_, v_a_941_, v_a_942_, v_a_943_, v_a_944_, v_a_945_, v_a_946_);
lean_dec(v_a_946_);
lean_dec_ref(v_a_945_);
lean_dec(v_a_944_);
lean_dec_ref(v_a_943_);
lean_dec(v_a_942_);
lean_dec_ref(v_a_941_);
lean_dec(v_a_940_);
return v_res_948_;
}
}
lean_object* l_Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached(lean_object* v_rhs_949_, lean_object* v_op_950_, lean_object* v_a_951_, lean_object* v_a_952_, lean_object* v_a_953_, lean_object* v_a_954_, lean_object* v_a_955_, lean_object* v_a_956_, lean_object* v_a_957_, lean_object* v_a_958_, lean_object* v_a_959_, lean_object* v_a_960_, lean_object* v_a_961_){
_start:
{
lean_object* v___x_963_; 
v___x_963_ = l_Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached___redArg(v_rhs_949_, v_op_950_, v_a_952_, v_a_956_, v_a_957_, v_a_958_, v_a_959_, v_a_960_, v_a_961_);
return v___x_963_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_0interp(lean_interpreter_value* stack)
{
lean_object* v_rhs_949_ = stack[0].m_obj;
lean_object* v_op_950_ = stack[1].m_obj;
lean_object* v_a_951_ = stack[2].m_obj;
lean_object* v_a_952_ = stack[3].m_obj;
lean_object* v_a_953_ = stack[4].m_obj;
lean_object* v_a_954_ = stack[5].m_obj;
lean_object* v_a_955_ = stack[6].m_obj;
lean_object* v_a_956_ = stack[7].m_obj;
lean_object* v_a_957_ = stack[8].m_obj;
lean_object* v_a_958_ = stack[9].m_obj;
lean_object* v_a_959_ = stack[10].m_obj;
lean_object* v_a_960_ = stack[11].m_obj;
lean_object* v_a_961_ = stack[12].m_obj;
lean_object* v_res_964_;
v_res_964_ = l_Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached(v_rhs_949_, v_op_950_, v_a_951_, v_a_952_, v_a_953_, v_a_954_, v_a_955_, v_a_956_, v_a_957_, v_a_958_, v_a_959_, v_a_960_, v_a_961_);
stack->m_obj
 = v_res_964_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached___boxed(lean_object* v_rhs_965_, lean_object* v_op_966_, lean_object* v_a_967_, lean_object* v_a_968_, lean_object* v_a_969_, lean_object* v_a_970_, lean_object* v_a_971_, lean_object* v_a_972_, lean_object* v_a_973_, lean_object* v_a_974_, lean_object* v_a_975_, lean_object* v_a_976_, lean_object* v_a_977_, lean_object* v_a_978_){
_start:
{
lean_object* v_res_979_; 
v_res_979_ = l_Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached(v_rhs_965_, v_op_966_, v_a_967_, v_a_968_, v_a_969_, v_a_970_, v_a_971_, v_a_972_, v_a_973_, v_a_974_, v_a_975_, v_a_976_, v_a_977_);
lean_dec(v_a_977_);
lean_dec_ref(v_a_976_);
lean_dec(v_a_975_);
lean_dec_ref(v_a_974_);
lean_dec(v_a_973_);
lean_dec_ref(v_a_972_);
lean_dec(v_a_971_);
lean_dec_ref(v_a_970_);
lean_dec(v_a_969_);
lean_dec(v_a_968_);
lean_dec_ref(v_a_967_);
return v_res_979_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__0(lean_object* v_00_u03b2_980_, lean_object* v_m_981_, lean_object* v_a_982_){
_start:
{
lean_object* v___x_983_; 
v___x_983_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__0___redArg(v_m_981_, v_a_982_);
return v___x_983_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__0___boxed(lean_object* v_00_u03b2_984_, lean_object* v_m_985_, lean_object* v_a_986_){
_start:
{
lean_object* v_res_987_; 
v_res_987_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__0(v_00_u03b2_984_, v_m_985_, v_a_986_);
lean_dec_ref(v_a_986_);
lean_dec_ref(v_m_985_);
return v_res_987_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1(lean_object* v_00_u03b2_988_, lean_object* v_m_989_, lean_object* v_a_990_, lean_object* v_b_991_){
_start:
{
lean_object* v___x_992_; 
v___x_992_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1___redArg(v_m_989_, v_a_990_, v_b_991_);
return v___x_992_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__0_spec__0(lean_object* v_00_u03b2_993_, lean_object* v_a_994_, lean_object* v_x_995_){
_start:
{
lean_object* v___x_996_; 
v___x_996_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__0_spec__0___redArg(v_a_994_, v_x_995_);
return v___x_996_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__0_spec__0___boxed(lean_object* v_00_u03b2_997_, lean_object* v_a_998_, lean_object* v_x_999_){
_start:
{
lean_object* v_res_1000_; 
v_res_1000_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__0_spec__0(v_00_u03b2_997_, v_a_998_, v_x_999_);
lean_dec(v_x_999_);
lean_dec_ref(v_a_998_);
return v_res_1000_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1_spec__2(lean_object* v_00_u03b2_1001_, lean_object* v_a_1002_, lean_object* v_x_1003_){
_start:
{
uint8_t v___x_1004_; 
v___x_1004_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1_spec__2___redArg(v_a_1002_, v_x_1003_);
return v___x_1004_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1002_ = stack[1].m_obj;
lean_object* v_x_1003_ = stack[2].m_obj;
uint8_t v_res_1005_;
v_res_1005_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1_spec__2(lean_box(0), v_a_1002_, v_x_1003_);
stack->m_num = v_res_1005_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1006_, lean_object* v_a_1007_, lean_object* v_x_1008_){
_start:
{
uint8_t v_res_1009_; lean_object* v_r_1010_; 
v_res_1009_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1_spec__2(v_00_u03b2_1006_, v_a_1007_, v_x_1008_);
lean_dec(v_x_1008_);
lean_dec_ref(v_a_1007_);
v_r_1010_ = lean_box(v_res_1009_);
return v_r_1010_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1_spec__3(lean_object* v_00_u03b2_1011_, lean_object* v_data_1012_){
_start:
{
lean_object* v___x_1013_; 
v___x_1013_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1_spec__3___redArg(v_data_1012_);
return v___x_1013_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1_spec__4(lean_object* v_00_u03b2_1014_, lean_object* v_a_1015_, lean_object* v_b_1016_, lean_object* v_x_1017_){
_start:
{
lean_object* v___x_1018_; 
v___x_1018_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1_spec__4___redArg(v_a_1015_, v_b_1016_, v_x_1017_);
return v___x_1018_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1_spec__3_spec__4(lean_object* v_00_u03b2_1019_, lean_object* v_i_1020_, lean_object* v_source_1021_, lean_object* v_target_1022_){
_start:
{
lean_object* v___x_1023_; 
v___x_1023_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1_spec__3_spec__4___redArg(v_i_1020_, v_source_1021_, v_target_1022_);
return v___x_1023_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1_spec__3_spec__4_spec__5(lean_object* v_00_u03b2_1024_, lean_object* v_x_1025_, lean_object* v_x_1026_){
_start:
{
lean_object* v___x_1027_; 
v___x_1027_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1_spec__3_spec__4_spec__5___redArg(v_x_1025_, v_x_1026_);
return v___x_1027_;
}
}
lean_object* l_Lean_Elab_Tactic_VCGen_mkFrameBackwardRuleCached___redArg(lean_object* v_fp_1028_, lean_object* v_info_1029_, lean_object* v_a_1030_, lean_object* v_a_1031_, lean_object* v_a_1032_, lean_object* v_a_1033_, lean_object* v_a_1034_, lean_object* v_a_1035_, lean_object* v_a_1036_){
_start:
{
lean_object* v_excessArgs_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v_key_1041_; lean_object* v___x_1042_; lean_object* v_frameBackwardRuleCache_1043_; lean_object* v___x_1044_; 
v_excessArgs_1038_ = lean_ctor_get(v_info_1029_, 3);
v___x_1039_ = l_Lean_Elab_Tactic_VCGen_WPApp_instWP(v_info_1029_);
v___x_1040_ = lean_array_get_size(v_excessArgs_1038_);
v_key_1041_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_key_1041_, 0, v___x_1039_);
lean_ctor_set(v_key_1041_, 1, v___x_1040_);
v___x_1042_ = lean_st_ref_get(v_a_1030_);
v_frameBackwardRuleCache_1043_ = lean_ctor_get(v___x_1042_, 3);
lean_inc_ref(v_frameBackwardRuleCache_1043_);
lean_dec(v___x_1042_);
v___x_1044_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__0___redArg(v_frameBackwardRuleCache_1043_, v_key_1041_);
lean_dec_ref(v_frameBackwardRuleCache_1043_);
if (lean_obj_tag(v___x_1044_) == 1)
{
lean_object* v_val_1045_; lean_object* v___x_1047_; uint8_t v_isShared_1048_; uint8_t v_isSharedCheck_1052_; 
lean_dec_ref_known(v_key_1041_, 2);
lean_dec_ref(v_info_1029_);
lean_dec_ref(v_fp_1028_);
v_val_1045_ = lean_ctor_get(v___x_1044_, 0);
v_isSharedCheck_1052_ = !lean_is_exclusive(v___x_1044_);
if (v_isSharedCheck_1052_ == 0)
{
v___x_1047_ = v___x_1044_;
v_isShared_1048_ = v_isSharedCheck_1052_;
goto v_resetjp_1046_;
}
else
{
lean_inc(v_val_1045_);
lean_dec(v___x_1044_);
v___x_1047_ = lean_box(0);
v_isShared_1048_ = v_isSharedCheck_1052_;
goto v_resetjp_1046_;
}
v_resetjp_1046_:
{
lean_object* v___x_1050_; 
if (v_isShared_1048_ == 0)
{
lean_ctor_set_tag(v___x_1047_, 0);
v___x_1050_ = v___x_1047_;
goto v_reusejp_1049_;
}
else
{
lean_object* v_reuseFailAlloc_1051_; 
v_reuseFailAlloc_1051_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1051_, 0, v_val_1045_);
v___x_1050_ = v_reuseFailAlloc_1051_;
goto v_reusejp_1049_;
}
v_reusejp_1049_:
{
return v___x_1050_;
}
}
}
else
{
lean_object* v___x_1053_; 
lean_dec(v___x_1044_);
v___x_1053_ = l_Lean_Elab_Tactic_VCGen_mkFrameBackwardRule(v_fp_1028_, v_info_1029_, v_a_1033_, v_a_1034_, v_a_1035_, v_a_1036_);
if (lean_obj_tag(v___x_1053_) == 0)
{
lean_object* v_a_1054_; lean_object* v_rule_1055_; lean_object* v_splitVCIdx_1056_; lean_object* v_frameIdx_1057_; lean_object* v___x_1059_; uint8_t v_isShared_1060_; uint8_t v_isSharedCheck_1101_; 
v_a_1054_ = lean_ctor_get(v___x_1053_, 0);
lean_inc(v_a_1054_);
lean_dec_ref_known(v___x_1053_, 1);
v_rule_1055_ = lean_ctor_get(v_a_1054_, 0);
v_splitVCIdx_1056_ = lean_ctor_get(v_a_1054_, 1);
v_frameIdx_1057_ = lean_ctor_get(v_a_1054_, 2);
v_isSharedCheck_1101_ = !lean_is_exclusive(v_a_1054_);
if (v_isSharedCheck_1101_ == 0)
{
v___x_1059_ = v_a_1054_;
v_isShared_1060_ = v_isSharedCheck_1101_;
goto v_resetjp_1058_;
}
else
{
lean_inc(v_frameIdx_1057_);
lean_inc(v_splitVCIdx_1056_);
lean_inc(v_rule_1055_);
lean_dec(v_a_1054_);
v___x_1059_ = lean_box(0);
v_isShared_1060_ = v_isSharedCheck_1101_;
goto v_resetjp_1058_;
}
v_resetjp_1058_:
{
lean_object* v___x_1061_; 
v___x_1061_ = l_Lean_Meta_Sym_BackwardRule_shareCommon(v_rule_1055_, v_a_1031_, v_a_1032_, v_a_1033_, v_a_1034_, v_a_1035_, v_a_1036_);
if (lean_obj_tag(v___x_1061_) == 0)
{
lean_object* v_a_1062_; lean_object* v___x_1064_; uint8_t v_isShared_1065_; uint8_t v_isSharedCheck_1092_; 
v_a_1062_ = lean_ctor_get(v___x_1061_, 0);
v_isSharedCheck_1092_ = !lean_is_exclusive(v___x_1061_);
if (v_isSharedCheck_1092_ == 0)
{
v___x_1064_ = v___x_1061_;
v_isShared_1065_ = v_isSharedCheck_1092_;
goto v_resetjp_1063_;
}
else
{
lean_inc(v_a_1062_);
lean_dec(v___x_1061_);
v___x_1064_ = lean_box(0);
v_isShared_1065_ = v_isSharedCheck_1092_;
goto v_resetjp_1063_;
}
v_resetjp_1063_:
{
lean_object* v___x_1067_; 
if (v_isShared_1060_ == 0)
{
lean_ctor_set(v___x_1059_, 0, v_a_1062_);
v___x_1067_ = v___x_1059_;
goto v_reusejp_1066_;
}
else
{
lean_object* v_reuseFailAlloc_1091_; 
v_reuseFailAlloc_1091_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1091_, 0, v_a_1062_);
lean_ctor_set(v_reuseFailAlloc_1091_, 1, v_splitVCIdx_1056_);
lean_ctor_set(v_reuseFailAlloc_1091_, 2, v_frameIdx_1057_);
v___x_1067_ = v_reuseFailAlloc_1091_;
goto v_reusejp_1066_;
}
v_reusejp_1066_:
{
lean_object* v___x_1068_; lean_object* v_specBackwardRuleCache_1069_; lean_object* v_splitBackwardRuleCache_1070_; lean_object* v_latticeBackwardRuleCache_1071_; lean_object* v_frameBackwardRuleCache_1072_; lean_object* v_frameDB_1073_; lean_object* v_invariants_1074_; lean_object* v_vcs_1075_; lean_object* v_simpState_1076_; lean_object* v_fuel_1077_; lean_object* v_inlineHandledInvariants_1078_; lean_object* v___x_1080_; uint8_t v_isShared_1081_; uint8_t v_isSharedCheck_1090_; 
v___x_1068_ = lean_st_ref_take(v_a_1030_);
v_specBackwardRuleCache_1069_ = lean_ctor_get(v___x_1068_, 0);
v_splitBackwardRuleCache_1070_ = lean_ctor_get(v___x_1068_, 1);
v_latticeBackwardRuleCache_1071_ = lean_ctor_get(v___x_1068_, 2);
v_frameBackwardRuleCache_1072_ = lean_ctor_get(v___x_1068_, 3);
v_frameDB_1073_ = lean_ctor_get(v___x_1068_, 4);
v_invariants_1074_ = lean_ctor_get(v___x_1068_, 5);
v_vcs_1075_ = lean_ctor_get(v___x_1068_, 6);
v_simpState_1076_ = lean_ctor_get(v___x_1068_, 7);
v_fuel_1077_ = lean_ctor_get(v___x_1068_, 8);
v_inlineHandledInvariants_1078_ = lean_ctor_get(v___x_1068_, 9);
v_isSharedCheck_1090_ = !lean_is_exclusive(v___x_1068_);
if (v_isSharedCheck_1090_ == 0)
{
v___x_1080_ = v___x_1068_;
v_isShared_1081_ = v_isSharedCheck_1090_;
goto v_resetjp_1079_;
}
else
{
lean_inc(v_inlineHandledInvariants_1078_);
lean_inc(v_fuel_1077_);
lean_inc(v_simpState_1076_);
lean_inc(v_vcs_1075_);
lean_inc(v_invariants_1074_);
lean_inc(v_frameDB_1073_);
lean_inc(v_frameBackwardRuleCache_1072_);
lean_inc(v_latticeBackwardRuleCache_1071_);
lean_inc(v_splitBackwardRuleCache_1070_);
lean_inc(v_specBackwardRuleCache_1069_);
lean_dec(v___x_1068_);
v___x_1080_ = lean_box(0);
v_isShared_1081_ = v_isSharedCheck_1090_;
goto v_resetjp_1079_;
}
v_resetjp_1079_:
{
lean_object* v___x_1082_; lean_object* v___x_1084_; 
lean_inc_ref(v___x_1067_);
v___x_1082_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1___redArg(v_frameBackwardRuleCache_1072_, v_key_1041_, v___x_1067_);
if (v_isShared_1081_ == 0)
{
lean_ctor_set(v___x_1080_, 3, v___x_1082_);
v___x_1084_ = v___x_1080_;
goto v_reusejp_1083_;
}
else
{
lean_object* v_reuseFailAlloc_1089_; 
v_reuseFailAlloc_1089_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1089_, 0, v_specBackwardRuleCache_1069_);
lean_ctor_set(v_reuseFailAlloc_1089_, 1, v_splitBackwardRuleCache_1070_);
lean_ctor_set(v_reuseFailAlloc_1089_, 2, v_latticeBackwardRuleCache_1071_);
lean_ctor_set(v_reuseFailAlloc_1089_, 3, v___x_1082_);
lean_ctor_set(v_reuseFailAlloc_1089_, 4, v_frameDB_1073_);
lean_ctor_set(v_reuseFailAlloc_1089_, 5, v_invariants_1074_);
lean_ctor_set(v_reuseFailAlloc_1089_, 6, v_vcs_1075_);
lean_ctor_set(v_reuseFailAlloc_1089_, 7, v_simpState_1076_);
lean_ctor_set(v_reuseFailAlloc_1089_, 8, v_fuel_1077_);
lean_ctor_set(v_reuseFailAlloc_1089_, 9, v_inlineHandledInvariants_1078_);
v___x_1084_ = v_reuseFailAlloc_1089_;
goto v_reusejp_1083_;
}
v_reusejp_1083_:
{
lean_object* v___x_1085_; lean_object* v___x_1087_; 
v___x_1085_ = lean_st_ref_put(v_a_1030_, v___x_1084_);
if (v_isShared_1065_ == 0)
{
lean_ctor_set(v___x_1064_, 0, v___x_1067_);
v___x_1087_ = v___x_1064_;
goto v_reusejp_1086_;
}
else
{
lean_object* v_reuseFailAlloc_1088_; 
v_reuseFailAlloc_1088_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1088_, 0, v___x_1067_);
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
}
else
{
lean_object* v_a_1093_; lean_object* v___x_1095_; uint8_t v_isShared_1096_; uint8_t v_isSharedCheck_1100_; 
lean_del_object(v___x_1059_);
lean_dec(v_frameIdx_1057_);
lean_dec(v_splitVCIdx_1056_);
lean_dec_ref_known(v_key_1041_, 2);
v_a_1093_ = lean_ctor_get(v___x_1061_, 0);
v_isSharedCheck_1100_ = !lean_is_exclusive(v___x_1061_);
if (v_isSharedCheck_1100_ == 0)
{
v___x_1095_ = v___x_1061_;
v_isShared_1096_ = v_isSharedCheck_1100_;
goto v_resetjp_1094_;
}
else
{
lean_inc(v_a_1093_);
lean_dec(v___x_1061_);
v___x_1095_ = lean_box(0);
v_isShared_1096_ = v_isSharedCheck_1100_;
goto v_resetjp_1094_;
}
v_resetjp_1094_:
{
lean_object* v___x_1098_; 
if (v_isShared_1096_ == 0)
{
v___x_1098_ = v___x_1095_;
goto v_reusejp_1097_;
}
else
{
lean_object* v_reuseFailAlloc_1099_; 
v_reuseFailAlloc_1099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1099_, 0, v_a_1093_);
v___x_1098_ = v_reuseFailAlloc_1099_;
goto v_reusejp_1097_;
}
v_reusejp_1097_:
{
return v___x_1098_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_key_1041_, 2);
return v___x_1053_;
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_VCGen_mkFrameBackwardRuleCached___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_fp_1028_ = stack[0].m_obj;
lean_object* v_info_1029_ = stack[1].m_obj;
lean_object* v_a_1030_ = stack[2].m_obj;
lean_object* v_a_1031_ = stack[3].m_obj;
lean_object* v_a_1032_ = stack[4].m_obj;
lean_object* v_a_1033_ = stack[5].m_obj;
lean_object* v_a_1034_ = stack[6].m_obj;
lean_object* v_a_1035_ = stack[7].m_obj;
lean_object* v_a_1036_ = stack[8].m_obj;
lean_object* v_res_1102_;
v_res_1102_ = l_Lean_Elab_Tactic_VCGen_mkFrameBackwardRuleCached___redArg(v_fp_1028_, v_info_1029_, v_a_1030_, v_a_1031_, v_a_1032_, v_a_1033_, v_a_1034_, v_a_1035_, v_a_1036_);
stack->m_obj
 = v_res_1102_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_mkFrameBackwardRuleCached___redArg___boxed(lean_object* v_fp_1103_, lean_object* v_info_1104_, lean_object* v_a_1105_, lean_object* v_a_1106_, lean_object* v_a_1107_, lean_object* v_a_1108_, lean_object* v_a_1109_, lean_object* v_a_1110_, lean_object* v_a_1111_, lean_object* v_a_1112_){
_start:
{
lean_object* v_res_1113_; 
v_res_1113_ = l_Lean_Elab_Tactic_VCGen_mkFrameBackwardRuleCached___redArg(v_fp_1103_, v_info_1104_, v_a_1105_, v_a_1106_, v_a_1107_, v_a_1108_, v_a_1109_, v_a_1110_, v_a_1111_);
lean_dec(v_a_1111_);
lean_dec_ref(v_a_1110_);
lean_dec(v_a_1109_);
lean_dec_ref(v_a_1108_);
lean_dec(v_a_1107_);
lean_dec_ref(v_a_1106_);
lean_dec(v_a_1105_);
return v_res_1113_;
}
}
lean_object* l_Lean_Elab_Tactic_VCGen_mkFrameBackwardRuleCached(lean_object* v_fp_1114_, lean_object* v_info_1115_, lean_object* v_a_1116_, lean_object* v_a_1117_, lean_object* v_a_1118_, lean_object* v_a_1119_, lean_object* v_a_1120_, lean_object* v_a_1121_, lean_object* v_a_1122_, lean_object* v_a_1123_, lean_object* v_a_1124_, lean_object* v_a_1125_, lean_object* v_a_1126_){
_start:
{
lean_object* v___x_1128_; 
v___x_1128_ = l_Lean_Elab_Tactic_VCGen_mkFrameBackwardRuleCached___redArg(v_fp_1114_, v_info_1115_, v_a_1117_, v_a_1121_, v_a_1122_, v_a_1123_, v_a_1124_, v_a_1125_, v_a_1126_);
return v___x_1128_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_VCGen_mkFrameBackwardRuleCached_0interp(lean_interpreter_value* stack)
{
lean_object* v_fp_1114_ = stack[0].m_obj;
lean_object* v_info_1115_ = stack[1].m_obj;
lean_object* v_a_1116_ = stack[2].m_obj;
lean_object* v_a_1117_ = stack[3].m_obj;
lean_object* v_a_1118_ = stack[4].m_obj;
lean_object* v_a_1119_ = stack[5].m_obj;
lean_object* v_a_1120_ = stack[6].m_obj;
lean_object* v_a_1121_ = stack[7].m_obj;
lean_object* v_a_1122_ = stack[8].m_obj;
lean_object* v_a_1123_ = stack[9].m_obj;
lean_object* v_a_1124_ = stack[10].m_obj;
lean_object* v_a_1125_ = stack[11].m_obj;
lean_object* v_a_1126_ = stack[12].m_obj;
lean_object* v_res_1129_;
v_res_1129_ = l_Lean_Elab_Tactic_VCGen_mkFrameBackwardRuleCached(v_fp_1114_, v_info_1115_, v_a_1116_, v_a_1117_, v_a_1118_, v_a_1119_, v_a_1120_, v_a_1121_, v_a_1122_, v_a_1123_, v_a_1124_, v_a_1125_, v_a_1126_);
stack->m_obj
 = v_res_1129_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_mkFrameBackwardRuleCached___boxed(lean_object* v_fp_1130_, lean_object* v_info_1131_, lean_object* v_a_1132_, lean_object* v_a_1133_, lean_object* v_a_1134_, lean_object* v_a_1135_, lean_object* v_a_1136_, lean_object* v_a_1137_, lean_object* v_a_1138_, lean_object* v_a_1139_, lean_object* v_a_1140_, lean_object* v_a_1141_, lean_object* v_a_1142_, lean_object* v_a_1143_){
_start:
{
lean_object* v_res_1144_; 
v_res_1144_ = l_Lean_Elab_Tactic_VCGen_mkFrameBackwardRuleCached(v_fp_1130_, v_info_1131_, v_a_1132_, v_a_1133_, v_a_1134_, v_a_1135_, v_a_1136_, v_a_1137_, v_a_1138_, v_a_1139_, v_a_1140_, v_a_1141_, v_a_1142_);
lean_dec(v_a_1142_);
lean_dec_ref(v_a_1141_);
lean_dec(v_a_1140_);
lean_dec_ref(v_a_1139_);
lean_dec(v_a_1138_);
lean_dec_ref(v_a_1137_);
lean_dec(v_a_1136_);
lean_dec_ref(v_a_1135_);
lean_dec(v_a_1134_);
lean_dec(v_a_1133_);
lean_dec_ref(v_a_1132_);
return v_res_1144_;
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
