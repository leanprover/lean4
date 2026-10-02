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
lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v_nbuckets_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; 
v___x_232_ = lean_array_get_size(v_data_231_);
v___x_233_ = lean_unsigned_to_nat(2u);
v_nbuckets_234_ = lean_nat_mul(v___x_232_, v___x_233_);
v___x_235_ = lean_unsigned_to_nat(0u);
v___x_236_ = lean_box(0);
v___x_237_ = lean_mk_array(v_nbuckets_234_, v___x_236_);
v___x_238_ = lean_array_propagate_mark(v_data_231_, v___x_237_);
v___x_239_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__4_spec__5___redArg(v___x_235_, v_data_231_, v___x_238_);
return v___x_239_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__5___redArg(lean_object* v_a_240_, lean_object* v_b_241_, lean_object* v_x_242_){
_start:
{
if (lean_obj_tag(v_x_242_) == 0)
{
lean_dec(v_b_241_);
lean_dec_ref(v_a_240_);
return v_x_242_;
}
else
{
lean_object* v_key_243_; lean_object* v_value_244_; lean_object* v_tail_245_; lean_object* v___x_247_; uint8_t v_isShared_248_; uint8_t v_isSharedCheck_270_; 
v_key_243_ = lean_ctor_get(v_x_242_, 0);
v_value_244_ = lean_ctor_get(v_x_242_, 1);
v_tail_245_ = lean_ctor_get(v_x_242_, 2);
v_isSharedCheck_270_ = !lean_is_exclusive(v_x_242_);
if (v_isSharedCheck_270_ == 0)
{
v___x_247_ = v_x_242_;
v_isShared_248_ = v_isSharedCheck_270_;
goto v_resetjp_246_;
}
else
{
lean_inc(v_tail_245_);
lean_inc(v_value_244_);
lean_inc(v_key_243_);
lean_dec(v_x_242_);
v___x_247_ = lean_box(0);
v_isShared_248_ = v_isSharedCheck_270_;
goto v_resetjp_246_;
}
v_resetjp_246_:
{
uint8_t v___y_255_; lean_object* v_fst_257_; lean_object* v_snd_258_; lean_object* v_fst_259_; lean_object* v_snd_260_; uint8_t v___x_261_; 
v_fst_257_ = lean_ctor_get(v_key_243_, 0);
v_snd_258_ = lean_ctor_get(v_key_243_, 1);
v_fst_259_ = lean_ctor_get(v_a_240_, 0);
v_snd_260_ = lean_ctor_get(v_a_240_, 1);
v___x_261_ = lean_name_eq(v_fst_257_, v_fst_259_);
if (v___x_261_ == 0)
{
v___y_255_ = v___x_261_;
goto v___jp_254_;
}
else
{
lean_object* v_fst_262_; lean_object* v_snd_263_; lean_object* v_fst_264_; lean_object* v_snd_265_; size_t v___x_266_; size_t v___x_267_; uint8_t v___x_268_; 
v_fst_262_ = lean_ctor_get(v_snd_258_, 0);
v_snd_263_ = lean_ctor_get(v_snd_258_, 1);
v_fst_264_ = lean_ctor_get(v_snd_260_, 0);
v_snd_265_ = lean_ctor_get(v_snd_260_, 1);
v___x_266_ = lean_ptr_addr(v_fst_262_);
v___x_267_ = lean_ptr_addr(v_fst_264_);
v___x_268_ = lean_usize_dec_eq(v___x_266_, v___x_267_);
if (v___x_268_ == 0)
{
goto v___jp_249_;
}
else
{
uint8_t v___x_269_; 
v___x_269_ = lean_nat_dec_eq(v_snd_263_, v_snd_265_);
v___y_255_ = v___x_269_;
goto v___jp_254_;
}
}
v___jp_249_:
{
lean_object* v___x_250_; lean_object* v___x_252_; 
v___x_250_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__5___redArg(v_a_240_, v_b_241_, v_tail_245_);
if (v_isShared_248_ == 0)
{
lean_ctor_set(v___x_247_, 2, v___x_250_);
v___x_252_ = v___x_247_;
goto v_reusejp_251_;
}
else
{
lean_object* v_reuseFailAlloc_253_; 
v_reuseFailAlloc_253_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_253_, 0, v_key_243_);
lean_ctor_set(v_reuseFailAlloc_253_, 1, v_value_244_);
lean_ctor_set(v_reuseFailAlloc_253_, 2, v___x_250_);
v___x_252_ = v_reuseFailAlloc_253_;
goto v_reusejp_251_;
}
v_reusejp_251_:
{
return v___x_252_;
}
}
v___jp_254_:
{
if (v___y_255_ == 0)
{
goto v___jp_249_;
}
else
{
lean_object* v___x_256_; 
lean_del_object(v___x_247_);
lean_dec(v_value_244_);
lean_dec(v_key_243_);
v___x_256_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_256_, 0, v_a_240_);
lean_ctor_set(v___x_256_, 1, v_b_241_);
lean_ctor_set(v___x_256_, 2, v_tail_245_);
return v___x_256_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2___redArg(lean_object* v_m_271_, lean_object* v_a_272_, lean_object* v_b_273_){
_start:
{
lean_object* v_size_274_; lean_object* v_buckets_275_; lean_object* v___x_277_; uint8_t v_isShared_278_; uint8_t v_isSharedCheck_332_; 
v_size_274_ = lean_ctor_get(v_m_271_, 0);
v_buckets_275_ = lean_ctor_get(v_m_271_, 1);
v_isSharedCheck_332_ = !lean_is_exclusive(v_m_271_);
if (v_isSharedCheck_332_ == 0)
{
v___x_277_ = v_m_271_;
v_isShared_278_ = v_isSharedCheck_332_;
goto v_resetjp_276_;
}
else
{
lean_inc(v_buckets_275_);
lean_inc(v_size_274_);
lean_dec(v_m_271_);
v___x_277_ = lean_box(0);
v_isShared_278_ = v_isSharedCheck_332_;
goto v_resetjp_276_;
}
v_resetjp_276_:
{
lean_object* v_fst_279_; lean_object* v_snd_280_; lean_object* v___x_281_; uint64_t v___y_283_; 
v_fst_279_ = lean_ctor_get(v_a_272_, 0);
v_snd_280_ = lean_ctor_get(v_a_272_, 1);
v___x_281_ = lean_array_get_size(v_buckets_275_);
if (lean_obj_tag(v_fst_279_) == 0)
{
uint64_t v___x_330_; 
v___x_330_ = 1723ULL;
v___y_283_ = v___x_330_;
goto v___jp_282_;
}
else
{
uint64_t v_hash_331_; 
v_hash_331_ = lean_ctor_get_uint64(v_fst_279_, sizeof(void*)*2);
v___y_283_ = v_hash_331_;
goto v___jp_282_;
}
v___jp_282_:
{
lean_object* v_fst_284_; lean_object* v_snd_285_; size_t v___x_286_; size_t v___x_287_; size_t v___x_288_; uint64_t v___x_289_; uint64_t v___x_290_; uint64_t v___x_291_; uint64_t v___x_292_; uint64_t v___x_293_; uint64_t v___x_294_; uint64_t v_fold_295_; uint64_t v___x_296_; uint64_t v___x_297_; uint64_t v___x_298_; size_t v___x_299_; size_t v___x_300_; size_t v___x_301_; size_t v___x_302_; size_t v___x_303_; lean_object* v_bkt_304_; uint8_t v___x_305_; 
v_fst_284_ = lean_ctor_get(v_snd_280_, 0);
v_snd_285_ = lean_ctor_get(v_snd_280_, 1);
v___x_286_ = lean_ptr_addr(v_fst_284_);
v___x_287_ = ((size_t)3ULL);
v___x_288_ = lean_usize_shift_right(v___x_286_, v___x_287_);
v___x_289_ = lean_usize_to_uint64(v___x_288_);
v___x_290_ = lean_uint64_of_nat(v_snd_285_);
v___x_291_ = lean_uint64_mix_hash(v___x_289_, v___x_290_);
v___x_292_ = lean_uint64_mix_hash(v___y_283_, v___x_291_);
v___x_293_ = 32ULL;
v___x_294_ = lean_uint64_shift_right(v___x_292_, v___x_293_);
v_fold_295_ = lean_uint64_xor(v___x_292_, v___x_294_);
v___x_296_ = 16ULL;
v___x_297_ = lean_uint64_shift_right(v_fold_295_, v___x_296_);
v___x_298_ = lean_uint64_xor(v_fold_295_, v___x_297_);
v___x_299_ = lean_uint64_to_usize(v___x_298_);
v___x_300_ = lean_usize_of_nat(v___x_281_);
v___x_301_ = ((size_t)1ULL);
v___x_302_ = lean_usize_sub(v___x_300_, v___x_301_);
v___x_303_ = lean_usize_land(v___x_299_, v___x_302_);
v_bkt_304_ = lean_array_uget_borrowed(v_buckets_275_, v___x_303_);
v___x_305_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__3___redArg(v_a_272_, v_bkt_304_);
if (v___x_305_ == 0)
{
lean_object* v___x_306_; lean_object* v_size_x27_307_; lean_object* v___x_308_; lean_object* v_buckets_x27_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; uint8_t v___x_315_; 
v___x_306_ = lean_unsigned_to_nat(1u);
v_size_x27_307_ = lean_nat_add(v_size_274_, v___x_306_);
lean_dec(v_size_274_);
lean_inc(v_bkt_304_);
v___x_308_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_308_, 0, v_a_272_);
lean_ctor_set(v___x_308_, 1, v_b_273_);
lean_ctor_set(v___x_308_, 2, v_bkt_304_);
v_buckets_x27_309_ = lean_array_uset(v_buckets_275_, v___x_303_, v___x_308_);
v___x_310_ = lean_unsigned_to_nat(4u);
v___x_311_ = lean_nat_mul(v_size_x27_307_, v___x_310_);
v___x_312_ = lean_unsigned_to_nat(3u);
v___x_313_ = lean_nat_div(v___x_311_, v___x_312_);
lean_dec(v___x_311_);
v___x_314_ = lean_array_get_size(v_buckets_x27_309_);
v___x_315_ = lean_nat_dec_le(v___x_313_, v___x_314_);
lean_dec(v___x_313_);
if (v___x_315_ == 0)
{
lean_object* v_val_316_; lean_object* v___x_318_; 
v_val_316_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__4___redArg(v_buckets_x27_309_);
if (v_isShared_278_ == 0)
{
lean_ctor_set(v___x_277_, 1, v_val_316_);
lean_ctor_set(v___x_277_, 0, v_size_x27_307_);
v___x_318_ = v___x_277_;
goto v_reusejp_317_;
}
else
{
lean_object* v_reuseFailAlloc_319_; 
v_reuseFailAlloc_319_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_319_, 0, v_size_x27_307_);
lean_ctor_set(v_reuseFailAlloc_319_, 1, v_val_316_);
v___x_318_ = v_reuseFailAlloc_319_;
goto v_reusejp_317_;
}
v_reusejp_317_:
{
return v___x_318_;
}
}
else
{
lean_object* v___x_321_; 
if (v_isShared_278_ == 0)
{
lean_ctor_set(v___x_277_, 1, v_buckets_x27_309_);
lean_ctor_set(v___x_277_, 0, v_size_x27_307_);
v___x_321_ = v___x_277_;
goto v_reusejp_320_;
}
else
{
lean_object* v_reuseFailAlloc_322_; 
v_reuseFailAlloc_322_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_322_, 0, v_size_x27_307_);
lean_ctor_set(v_reuseFailAlloc_322_, 1, v_buckets_x27_309_);
v___x_321_ = v_reuseFailAlloc_322_;
goto v_reusejp_320_;
}
v_reusejp_320_:
{
return v___x_321_;
}
}
}
else
{
lean_object* v___x_323_; lean_object* v_buckets_x27_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_328_; 
lean_inc(v_bkt_304_);
v___x_323_ = lean_box(0);
v_buckets_x27_324_ = lean_array_uset(v_buckets_275_, v___x_303_, v___x_323_);
v___x_325_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__5___redArg(v_a_272_, v_b_273_, v_bkt_304_);
v___x_326_ = lean_array_uset(v_buckets_x27_324_, v___x_303_, v___x_325_);
if (v_isShared_278_ == 0)
{
lean_ctor_set(v___x_277_, 1, v___x_326_);
v___x_328_ = v___x_277_;
goto v_reusejp_327_;
}
else
{
lean_object* v_reuseFailAlloc_329_; 
v_reuseFailAlloc_329_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_329_, 0, v_size_274_);
lean_ctor_set(v_reuseFailAlloc_329_, 1, v___x_326_);
v___x_328_ = v_reuseFailAlloc_329_;
goto v_reusejp_327_;
}
v_reusejp_327_:
{
return v___x_328_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__0_spec__0___redArg(lean_object* v_a_333_, lean_object* v_x_334_){
_start:
{
if (lean_obj_tag(v_x_334_) == 0)
{
lean_object* v___x_335_; 
v___x_335_ = lean_box(0);
return v___x_335_;
}
else
{
lean_object* v_key_336_; lean_object* v_value_337_; lean_object* v_tail_338_; uint8_t v___y_340_; lean_object* v_fst_343_; lean_object* v_snd_344_; lean_object* v_fst_345_; lean_object* v_snd_346_; uint8_t v___x_347_; 
v_key_336_ = lean_ctor_get(v_x_334_, 0);
v_value_337_ = lean_ctor_get(v_x_334_, 1);
v_tail_338_ = lean_ctor_get(v_x_334_, 2);
v_fst_343_ = lean_ctor_get(v_key_336_, 0);
v_snd_344_ = lean_ctor_get(v_key_336_, 1);
v_fst_345_ = lean_ctor_get(v_a_333_, 0);
v_snd_346_ = lean_ctor_get(v_a_333_, 1);
v___x_347_ = lean_name_eq(v_fst_343_, v_fst_345_);
if (v___x_347_ == 0)
{
v___y_340_ = v___x_347_;
goto v___jp_339_;
}
else
{
lean_object* v_fst_348_; lean_object* v_snd_349_; lean_object* v_fst_350_; lean_object* v_snd_351_; size_t v___x_352_; size_t v___x_353_; uint8_t v___x_354_; 
v_fst_348_ = lean_ctor_get(v_snd_344_, 0);
v_snd_349_ = lean_ctor_get(v_snd_344_, 1);
v_fst_350_ = lean_ctor_get(v_snd_346_, 0);
v_snd_351_ = lean_ctor_get(v_snd_346_, 1);
v___x_352_ = lean_ptr_addr(v_fst_348_);
v___x_353_ = lean_ptr_addr(v_fst_350_);
v___x_354_ = lean_usize_dec_eq(v___x_352_, v___x_353_);
if (v___x_354_ == 0)
{
v_x_334_ = v_tail_338_;
goto _start;
}
else
{
uint8_t v___x_356_; 
v___x_356_ = lean_nat_dec_eq(v_snd_349_, v_snd_351_);
v___y_340_ = v___x_356_;
goto v___jp_339_;
}
}
v___jp_339_:
{
if (v___y_340_ == 0)
{
v_x_334_ = v_tail_338_;
goto _start;
}
else
{
lean_object* v___x_342_; 
lean_inc(v_value_337_);
v___x_342_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_342_, 0, v_value_337_);
return v___x_342_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__0_spec__0___redArg___boxed(lean_object* v_a_357_, lean_object* v_x_358_){
_start:
{
lean_object* v_res_359_; 
v_res_359_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__0_spec__0___redArg(v_a_357_, v_x_358_);
lean_dec(v_x_358_);
lean_dec_ref(v_a_357_);
return v_res_359_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg(lean_object* v_m_360_, lean_object* v_a_361_){
_start:
{
lean_object* v_buckets_362_; lean_object* v_fst_363_; lean_object* v_snd_364_; lean_object* v___x_365_; uint64_t v___y_367_; 
v_buckets_362_ = lean_ctor_get(v_m_360_, 1);
v_fst_363_ = lean_ctor_get(v_a_361_, 0);
v_snd_364_ = lean_ctor_get(v_a_361_, 1);
v___x_365_ = lean_array_get_size(v_buckets_362_);
if (lean_obj_tag(v_fst_363_) == 0)
{
uint64_t v___x_390_; 
v___x_390_ = 1723ULL;
v___y_367_ = v___x_390_;
goto v___jp_366_;
}
else
{
uint64_t v_hash_391_; 
v_hash_391_ = lean_ctor_get_uint64(v_fst_363_, sizeof(void*)*2);
v___y_367_ = v_hash_391_;
goto v___jp_366_;
}
v___jp_366_:
{
lean_object* v_fst_368_; lean_object* v_snd_369_; size_t v___x_370_; size_t v___x_371_; size_t v___x_372_; uint64_t v___x_373_; uint64_t v___x_374_; uint64_t v___x_375_; uint64_t v___x_376_; uint64_t v___x_377_; uint64_t v___x_378_; uint64_t v_fold_379_; uint64_t v___x_380_; uint64_t v___x_381_; uint64_t v___x_382_; size_t v___x_383_; size_t v___x_384_; size_t v___x_385_; size_t v___x_386_; size_t v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; 
v_fst_368_ = lean_ctor_get(v_snd_364_, 0);
v_snd_369_ = lean_ctor_get(v_snd_364_, 1);
v___x_370_ = lean_ptr_addr(v_fst_368_);
v___x_371_ = ((size_t)3ULL);
v___x_372_ = lean_usize_shift_right(v___x_370_, v___x_371_);
v___x_373_ = lean_usize_to_uint64(v___x_372_);
v___x_374_ = lean_uint64_of_nat(v_snd_369_);
v___x_375_ = lean_uint64_mix_hash(v___x_373_, v___x_374_);
v___x_376_ = lean_uint64_mix_hash(v___y_367_, v___x_375_);
v___x_377_ = 32ULL;
v___x_378_ = lean_uint64_shift_right(v___x_376_, v___x_377_);
v_fold_379_ = lean_uint64_xor(v___x_376_, v___x_378_);
v___x_380_ = 16ULL;
v___x_381_ = lean_uint64_shift_right(v_fold_379_, v___x_380_);
v___x_382_ = lean_uint64_xor(v_fold_379_, v___x_381_);
v___x_383_ = lean_uint64_to_usize(v___x_382_);
v___x_384_ = lean_usize_of_nat(v___x_365_);
v___x_385_ = ((size_t)1ULL);
v___x_386_ = lean_usize_sub(v___x_384_, v___x_385_);
v___x_387_ = lean_usize_land(v___x_383_, v___x_386_);
v___x_388_ = lean_array_uget_borrowed(v_buckets_362_, v___x_387_);
v___x_389_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__0_spec__0___redArg(v_a_361_, v___x_388_);
return v___x_389_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg___boxed(lean_object* v_m_392_, lean_object* v_a_393_){
_start:
{
lean_object* v_res_394_; 
v_res_394_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg(v_m_392_, v_a_393_);
lean_dec_ref(v_a_393_);
lean_dec_ref(v_m_392_);
return v_res_394_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached(lean_object* v_specThm_397_, lean_object* v_info_398_, lean_object* v_a_399_, lean_object* v_a_400_, lean_object* v_a_401_, lean_object* v_a_402_, lean_object* v_a_403_, lean_object* v_a_404_, lean_object* v_a_405_, lean_object* v_a_406_, lean_object* v_a_407_, lean_object* v_a_408_, lean_object* v_a_409_){
_start:
{
lean_object* v_proof_411_; lean_object* v_excessArgs_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v_key_417_; lean_object* v___x_418_; lean_object* v_specBackwardRuleCache_419_; lean_object* v___x_420_; 
v_proof_411_ = lean_ctor_get(v_specThm_397_, 1);
v_excessArgs_412_ = lean_ctor_get(v_info_398_, 3);
v___x_413_ = l_Lean_Elab_Tactic_VCGen_SpecAttr_SpecProof_key(v_proof_411_);
v___x_414_ = l_Lean_Elab_Tactic_VCGen_WPApp_instWP(v_info_398_);
v___x_415_ = lean_array_get_size(v_excessArgs_412_);
v___x_416_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_416_, 0, v___x_414_);
lean_ctor_set(v___x_416_, 1, v___x_415_);
v_key_417_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_key_417_, 0, v___x_413_);
lean_ctor_set(v_key_417_, 1, v___x_416_);
v___x_418_ = lean_st_ref_get(v_a_400_);
v_specBackwardRuleCache_419_ = lean_ctor_get(v___x_418_, 0);
lean_inc_ref(v_specBackwardRuleCache_419_);
lean_dec(v___x_418_);
v___x_420_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg(v_specBackwardRuleCache_419_, v_key_417_);
lean_dec_ref(v_specBackwardRuleCache_419_);
if (lean_obj_tag(v___x_420_) == 1)
{
lean_object* v___x_421_; 
lean_dec_ref_known(v_key_417_, 2);
lean_dec_ref(v_info_398_);
lean_dec_ref(v_specThm_397_);
v___x_421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_421_, 0, v___x_420_);
return v___x_421_;
}
else
{
lean_object* v___x_422_; lean_object* v___f_423_; uint8_t v___x_424_; lean_object* v___x_425_; 
lean_dec(v___x_420_);
v___x_422_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached___closed__0));
v___f_423_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached___lam__0___boxed), 15, 3);
lean_closure_set(v___f_423_, 0, v_specThm_397_);
lean_closure_set(v___f_423_, 1, v_info_398_);
lean_closure_set(v___f_423_, 2, v___x_422_);
v___x_424_ = 0;
v___x_425_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__1___redArg(v___f_423_, v___x_424_, v_a_399_, v_a_400_, v_a_401_, v_a_402_, v_a_403_, v_a_404_, v_a_405_, v_a_406_, v_a_407_, v_a_408_, v_a_409_);
if (lean_obj_tag(v___x_425_) == 0)
{
lean_object* v_a_426_; lean_object* v___x_428_; uint8_t v_isShared_429_; uint8_t v_isSharedCheck_484_; 
v_a_426_ = lean_ctor_get(v___x_425_, 0);
v_isSharedCheck_484_ = !lean_is_exclusive(v___x_425_);
if (v_isSharedCheck_484_ == 0)
{
v___x_428_ = v___x_425_;
v_isShared_429_ = v_isSharedCheck_484_;
goto v_resetjp_427_;
}
else
{
lean_inc(v_a_426_);
lean_dec(v___x_425_);
v___x_428_ = lean_box(0);
v_isShared_429_ = v_isSharedCheck_484_;
goto v_resetjp_427_;
}
v_resetjp_427_:
{
if (lean_obj_tag(v_a_426_) == 0)
{
lean_object* v___x_430_; lean_object* v___x_432_; 
lean_dec_ref_known(v_key_417_, 2);
v___x_430_ = lean_box(0);
if (v_isShared_429_ == 0)
{
lean_ctor_set(v___x_428_, 0, v___x_430_);
v___x_432_ = v___x_428_;
goto v_reusejp_431_;
}
else
{
lean_object* v_reuseFailAlloc_433_; 
v_reuseFailAlloc_433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_433_, 0, v___x_430_);
v___x_432_ = v_reuseFailAlloc_433_;
goto v_reusejp_431_;
}
v_reusejp_431_:
{
return v___x_432_;
}
}
else
{
lean_object* v_val_434_; 
v_val_434_ = lean_ctor_get(v_a_426_, 0);
lean_inc(v_val_434_);
lean_dec_ref_known(v_a_426_, 1);
if (lean_obj_tag(v_val_434_) == 1)
{
lean_object* v_val_435_; lean_object* v___x_437_; uint8_t v_isShared_438_; uint8_t v_isSharedCheck_479_; 
lean_del_object(v___x_428_);
v_val_435_ = lean_ctor_get(v_val_434_, 0);
v_isSharedCheck_479_ = !lean_is_exclusive(v_val_434_);
if (v_isSharedCheck_479_ == 0)
{
v___x_437_ = v_val_434_;
v_isShared_438_ = v_isSharedCheck_479_;
goto v_resetjp_436_;
}
else
{
lean_inc(v_val_435_);
lean_dec(v_val_434_);
v___x_437_ = lean_box(0);
v_isShared_438_ = v_isSharedCheck_479_;
goto v_resetjp_436_;
}
v_resetjp_436_:
{
lean_object* v___x_439_; 
v___x_439_ = l_Lean_Meta_Sym_BackwardRule_shareCommon(v_val_435_, v_a_404_, v_a_405_, v_a_406_, v_a_407_, v_a_408_, v_a_409_);
if (lean_obj_tag(v___x_439_) == 0)
{
lean_object* v_a_440_; lean_object* v___x_442_; uint8_t v_isShared_443_; uint8_t v_isSharedCheck_470_; 
v_a_440_ = lean_ctor_get(v___x_439_, 0);
v_isSharedCheck_470_ = !lean_is_exclusive(v___x_439_);
if (v_isSharedCheck_470_ == 0)
{
v___x_442_ = v___x_439_;
v_isShared_443_ = v_isSharedCheck_470_;
goto v_resetjp_441_;
}
else
{
lean_inc(v_a_440_);
lean_dec(v___x_439_);
v___x_442_ = lean_box(0);
v_isShared_443_ = v_isSharedCheck_470_;
goto v_resetjp_441_;
}
v_resetjp_441_:
{
lean_object* v___x_445_; 
lean_inc(v_a_440_);
if (v_isShared_438_ == 0)
{
lean_ctor_set(v___x_437_, 0, v_a_440_);
v___x_445_ = v___x_437_;
goto v_reusejp_444_;
}
else
{
lean_object* v_reuseFailAlloc_469_; 
v_reuseFailAlloc_469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_469_, 0, v_a_440_);
v___x_445_ = v_reuseFailAlloc_469_;
goto v_reusejp_444_;
}
v_reusejp_444_:
{
lean_object* v___x_446_; lean_object* v_specBackwardRuleCache_447_; lean_object* v_splitBackwardRuleCache_448_; lean_object* v_latticeBackwardRuleCache_449_; lean_object* v_frameBackwardRuleCache_450_; lean_object* v_frameDB_451_; lean_object* v_invariants_452_; lean_object* v_vcs_453_; lean_object* v_simpState_454_; lean_object* v_fuel_455_; lean_object* v_inlineHandledInvariants_456_; lean_object* v___x_458_; uint8_t v_isShared_459_; uint8_t v_isSharedCheck_468_; 
v___x_446_ = lean_st_ref_take(v_a_400_);
v_specBackwardRuleCache_447_ = lean_ctor_get(v___x_446_, 0);
v_splitBackwardRuleCache_448_ = lean_ctor_get(v___x_446_, 1);
v_latticeBackwardRuleCache_449_ = lean_ctor_get(v___x_446_, 2);
v_frameBackwardRuleCache_450_ = lean_ctor_get(v___x_446_, 3);
v_frameDB_451_ = lean_ctor_get(v___x_446_, 4);
v_invariants_452_ = lean_ctor_get(v___x_446_, 5);
v_vcs_453_ = lean_ctor_get(v___x_446_, 6);
v_simpState_454_ = lean_ctor_get(v___x_446_, 7);
v_fuel_455_ = lean_ctor_get(v___x_446_, 8);
v_inlineHandledInvariants_456_ = lean_ctor_get(v___x_446_, 9);
v_isSharedCheck_468_ = !lean_is_exclusive(v___x_446_);
if (v_isSharedCheck_468_ == 0)
{
v___x_458_ = v___x_446_;
v_isShared_459_ = v_isSharedCheck_468_;
goto v_resetjp_457_;
}
else
{
lean_inc(v_inlineHandledInvariants_456_);
lean_inc(v_fuel_455_);
lean_inc(v_simpState_454_);
lean_inc(v_vcs_453_);
lean_inc(v_invariants_452_);
lean_inc(v_frameDB_451_);
lean_inc(v_frameBackwardRuleCache_450_);
lean_inc(v_latticeBackwardRuleCache_449_);
lean_inc(v_splitBackwardRuleCache_448_);
lean_inc(v_specBackwardRuleCache_447_);
lean_dec(v___x_446_);
v___x_458_ = lean_box(0);
v_isShared_459_ = v_isSharedCheck_468_;
goto v_resetjp_457_;
}
v_resetjp_457_:
{
lean_object* v___x_460_; lean_object* v___x_462_; 
v___x_460_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2___redArg(v_specBackwardRuleCache_447_, v_key_417_, v_a_440_);
if (v_isShared_459_ == 0)
{
lean_ctor_set(v___x_458_, 0, v___x_460_);
v___x_462_ = v___x_458_;
goto v_reusejp_461_;
}
else
{
lean_object* v_reuseFailAlloc_467_; 
v_reuseFailAlloc_467_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_467_, 0, v___x_460_);
lean_ctor_set(v_reuseFailAlloc_467_, 1, v_splitBackwardRuleCache_448_);
lean_ctor_set(v_reuseFailAlloc_467_, 2, v_latticeBackwardRuleCache_449_);
lean_ctor_set(v_reuseFailAlloc_467_, 3, v_frameBackwardRuleCache_450_);
lean_ctor_set(v_reuseFailAlloc_467_, 4, v_frameDB_451_);
lean_ctor_set(v_reuseFailAlloc_467_, 5, v_invariants_452_);
lean_ctor_set(v_reuseFailAlloc_467_, 6, v_vcs_453_);
lean_ctor_set(v_reuseFailAlloc_467_, 7, v_simpState_454_);
lean_ctor_set(v_reuseFailAlloc_467_, 8, v_fuel_455_);
lean_ctor_set(v_reuseFailAlloc_467_, 9, v_inlineHandledInvariants_456_);
v___x_462_ = v_reuseFailAlloc_467_;
goto v_reusejp_461_;
}
v_reusejp_461_:
{
lean_object* v___x_463_; lean_object* v___x_465_; 
v___x_463_ = lean_st_ref_put(v_a_400_, v___x_462_);
if (v_isShared_443_ == 0)
{
lean_ctor_set(v___x_442_, 0, v___x_445_);
v___x_465_ = v___x_442_;
goto v_reusejp_464_;
}
else
{
lean_object* v_reuseFailAlloc_466_; 
v_reuseFailAlloc_466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_466_, 0, v___x_445_);
v___x_465_ = v_reuseFailAlloc_466_;
goto v_reusejp_464_;
}
v_reusejp_464_:
{
return v___x_465_;
}
}
}
}
}
}
else
{
lean_object* v_a_471_; lean_object* v___x_473_; uint8_t v_isShared_474_; uint8_t v_isSharedCheck_478_; 
lean_del_object(v___x_437_);
lean_dec_ref_known(v_key_417_, 2);
v_a_471_ = lean_ctor_get(v___x_439_, 0);
v_isSharedCheck_478_ = !lean_is_exclusive(v___x_439_);
if (v_isSharedCheck_478_ == 0)
{
v___x_473_ = v___x_439_;
v_isShared_474_ = v_isSharedCheck_478_;
goto v_resetjp_472_;
}
else
{
lean_inc(v_a_471_);
lean_dec(v___x_439_);
v___x_473_ = lean_box(0);
v_isShared_474_ = v_isSharedCheck_478_;
goto v_resetjp_472_;
}
v_resetjp_472_:
{
lean_object* v___x_476_; 
if (v_isShared_474_ == 0)
{
v___x_476_ = v___x_473_;
goto v_reusejp_475_;
}
else
{
lean_object* v_reuseFailAlloc_477_; 
v_reuseFailAlloc_477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_477_, 0, v_a_471_);
v___x_476_ = v_reuseFailAlloc_477_;
goto v_reusejp_475_;
}
v_reusejp_475_:
{
return v___x_476_;
}
}
}
}
}
else
{
lean_object* v___x_480_; lean_object* v___x_482_; 
lean_dec(v_val_434_);
lean_dec_ref_known(v_key_417_, 2);
v___x_480_ = lean_box(0);
if (v_isShared_429_ == 0)
{
lean_ctor_set(v___x_428_, 0, v___x_480_);
v___x_482_ = v___x_428_;
goto v_reusejp_481_;
}
else
{
lean_object* v_reuseFailAlloc_483_; 
v_reuseFailAlloc_483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_483_, 0, v___x_480_);
v___x_482_ = v_reuseFailAlloc_483_;
goto v_reusejp_481_;
}
v_reusejp_481_:
{
return v___x_482_;
}
}
}
}
}
else
{
lean_object* v_a_485_; lean_object* v___x_487_; uint8_t v_isShared_488_; uint8_t v_isSharedCheck_492_; 
lean_dec_ref_known(v_key_417_, 2);
v_a_485_ = lean_ctor_get(v___x_425_, 0);
v_isSharedCheck_492_ = !lean_is_exclusive(v___x_425_);
if (v_isSharedCheck_492_ == 0)
{
v___x_487_ = v___x_425_;
v_isShared_488_ = v_isSharedCheck_492_;
goto v_resetjp_486_;
}
else
{
lean_inc(v_a_485_);
lean_dec(v___x_425_);
v___x_487_ = lean_box(0);
v_isShared_488_ = v_isSharedCheck_492_;
goto v_resetjp_486_;
}
v_resetjp_486_:
{
lean_object* v___x_490_; 
if (v_isShared_488_ == 0)
{
v___x_490_ = v___x_487_;
goto v_reusejp_489_;
}
else
{
lean_object* v_reuseFailAlloc_491_; 
v_reuseFailAlloc_491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_491_, 0, v_a_485_);
v___x_490_ = v_reuseFailAlloc_491_;
goto v_reusejp_489_;
}
v_reusejp_489_:
{
return v___x_490_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached___boxed(lean_object* v_specThm_493_, lean_object* v_info_494_, lean_object* v_a_495_, lean_object* v_a_496_, lean_object* v_a_497_, lean_object* v_a_498_, lean_object* v_a_499_, lean_object* v_a_500_, lean_object* v_a_501_, lean_object* v_a_502_, lean_object* v_a_503_, lean_object* v_a_504_, lean_object* v_a_505_, lean_object* v_a_506_){
_start:
{
lean_object* v_res_507_; 
v_res_507_ = l_Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached(v_specThm_493_, v_info_494_, v_a_495_, v_a_496_, v_a_497_, v_a_498_, v_a_499_, v_a_500_, v_a_501_, v_a_502_, v_a_503_, v_a_504_, v_a_505_);
lean_dec(v_a_505_);
lean_dec_ref(v_a_504_);
lean_dec(v_a_503_);
lean_dec_ref(v_a_502_);
lean_dec(v_a_501_);
lean_dec_ref(v_a_500_);
lean_dec(v_a_499_);
lean_dec_ref(v_a_498_);
lean_dec(v_a_497_);
lean_dec(v_a_496_);
lean_dec_ref(v_a_495_);
return v_res_507_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__0(lean_object* v_00_u03b2_508_, lean_object* v_m_509_, lean_object* v_a_510_){
_start:
{
lean_object* v___x_511_; 
v___x_511_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg(v_m_509_, v_a_510_);
return v___x_511_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__0___boxed(lean_object* v_00_u03b2_512_, lean_object* v_m_513_, lean_object* v_a_514_){
_start:
{
lean_object* v_res_515_; 
v_res_515_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__0(v_00_u03b2_512_, v_m_513_, v_a_514_);
lean_dec_ref(v_a_514_);
lean_dec_ref(v_m_513_);
return v_res_515_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2(lean_object* v_00_u03b2_516_, lean_object* v_m_517_, lean_object* v_a_518_, lean_object* v_b_519_){
_start:
{
lean_object* v___x_520_; 
v___x_520_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2___redArg(v_m_517_, v_a_518_, v_b_519_);
return v___x_520_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__0_spec__0(lean_object* v_00_u03b2_521_, lean_object* v_a_522_, lean_object* v_x_523_){
_start:
{
lean_object* v___x_524_; 
v___x_524_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__0_spec__0___redArg(v_a_522_, v_x_523_);
return v___x_524_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__0_spec__0___boxed(lean_object* v_00_u03b2_525_, lean_object* v_a_526_, lean_object* v_x_527_){
_start:
{
lean_object* v_res_528_; 
v_res_528_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__0_spec__0(v_00_u03b2_525_, v_a_526_, v_x_527_);
lean_dec(v_x_527_);
lean_dec_ref(v_a_526_);
return v_res_528_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__3(lean_object* v_00_u03b2_529_, lean_object* v_a_530_, lean_object* v_x_531_){
_start:
{
uint8_t v___x_532_; 
v___x_532_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__3___redArg(v_a_530_, v_x_531_);
return v___x_532_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__3___boxed(lean_object* v_00_u03b2_533_, lean_object* v_a_534_, lean_object* v_x_535_){
_start:
{
uint8_t v_res_536_; lean_object* v_r_537_; 
v_res_536_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__3(v_00_u03b2_533_, v_a_534_, v_x_535_);
lean_dec(v_x_535_);
lean_dec_ref(v_a_534_);
v_r_537_ = lean_box(v_res_536_);
return v_r_537_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__4(lean_object* v_00_u03b2_538_, lean_object* v_data_539_){
_start:
{
lean_object* v___x_540_; 
v___x_540_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__4___redArg(v_data_539_);
return v___x_540_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__5(lean_object* v_00_u03b2_541_, lean_object* v_a_542_, lean_object* v_b_543_, lean_object* v_x_544_){
_start:
{
lean_object* v___x_545_; 
v___x_545_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__5___redArg(v_a_542_, v_b_543_, v_x_544_);
return v___x_545_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_546_, lean_object* v_i_547_, lean_object* v_source_548_, lean_object* v_target_549_){
_start:
{
lean_object* v___x_550_; 
v___x_550_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__4_spec__5___redArg(v_i_547_, v_source_548_, v_target_549_);
return v___x_550_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__4_spec__5_spec__6(lean_object* v_00_u03b2_551_, lean_object* v_x_552_, lean_object* v_x_553_){
_start:
{
lean_object* v___x_554_; 
v___x_554_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__4_spec__5_spec__6___redArg(v_x_552_, v_x_553_);
return v___x_554_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_mkBackwardRuleForSplitCached___redArg(lean_object* v_splitInfo_564_, lean_object* v_info_565_, lean_object* v_a_566_, lean_object* v_a_567_, lean_object* v_a_568_, lean_object* v_a_569_, lean_object* v_a_570_, lean_object* v_a_571_, lean_object* v_a_572_){
_start:
{
lean_object* v___y_575_; 
switch(lean_obj_tag(v_splitInfo_564_))
{
case 0:
{
lean_object* v___x_623_; 
v___x_623_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_mkBackwardRuleForSplitCached___redArg___closed__1));
v___y_575_ = v___x_623_;
goto v___jp_574_;
}
case 1:
{
lean_object* v___x_624_; 
v___x_624_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_mkBackwardRuleForSplitCached___redArg___closed__3));
v___y_575_ = v___x_624_;
goto v___jp_574_;
}
case 2:
{
lean_object* v___x_625_; 
v___x_625_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_mkBackwardRuleForSplitCached___redArg___closed__5));
v___y_575_ = v___x_625_;
goto v___jp_574_;
}
default: 
{
lean_object* v_matcherApp_626_; lean_object* v_matcherName_627_; 
v_matcherApp_626_ = lean_ctor_get(v_splitInfo_564_, 0);
v_matcherName_627_ = lean_ctor_get(v_matcherApp_626_, 1);
lean_inc(v_matcherName_627_);
v___y_575_ = v_matcherName_627_;
goto v___jp_574_;
}
}
v___jp_574_:
{
lean_object* v_excessArgs_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v_key_580_; lean_object* v___x_581_; lean_object* v_splitBackwardRuleCache_582_; lean_object* v___x_583_; 
v_excessArgs_576_ = lean_ctor_get(v_info_565_, 3);
v___x_577_ = l_Lean_Elab_Tactic_VCGen_WPApp_instWP(v_info_565_);
v___x_578_ = lean_array_get_size(v_excessArgs_576_);
v___x_579_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_579_, 0, v___x_577_);
lean_ctor_set(v___x_579_, 1, v___x_578_);
v_key_580_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_key_580_, 0, v___y_575_);
lean_ctor_set(v_key_580_, 1, v___x_579_);
v___x_581_ = lean_st_ref_get(v_a_566_);
v_splitBackwardRuleCache_582_ = lean_ctor_get(v___x_581_, 1);
lean_inc_ref(v_splitBackwardRuleCache_582_);
lean_dec(v___x_581_);
v___x_583_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg(v_splitBackwardRuleCache_582_, v_key_580_);
lean_dec_ref(v_splitBackwardRuleCache_582_);
if (lean_obj_tag(v___x_583_) == 1)
{
lean_object* v_val_584_; lean_object* v___x_586_; uint8_t v_isShared_587_; uint8_t v_isSharedCheck_591_; 
lean_dec_ref_known(v_key_580_, 2);
lean_dec_ref(v_info_565_);
lean_dec_ref(v_splitInfo_564_);
v_val_584_ = lean_ctor_get(v___x_583_, 0);
v_isSharedCheck_591_ = !lean_is_exclusive(v___x_583_);
if (v_isSharedCheck_591_ == 0)
{
v___x_586_ = v___x_583_;
v_isShared_587_ = v_isSharedCheck_591_;
goto v_resetjp_585_;
}
else
{
lean_inc(v_val_584_);
lean_dec(v___x_583_);
v___x_586_ = lean_box(0);
v_isShared_587_ = v_isSharedCheck_591_;
goto v_resetjp_585_;
}
v_resetjp_585_:
{
lean_object* v___x_589_; 
if (v_isShared_587_ == 0)
{
lean_ctor_set_tag(v___x_586_, 0);
v___x_589_ = v___x_586_;
goto v_reusejp_588_;
}
else
{
lean_object* v_reuseFailAlloc_590_; 
v_reuseFailAlloc_590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_590_, 0, v_val_584_);
v___x_589_ = v_reuseFailAlloc_590_;
goto v_reusejp_588_;
}
v_reusejp_588_:
{
return v___x_589_;
}
}
}
else
{
lean_object* v___x_592_; 
lean_dec(v___x_583_);
v___x_592_ = l_Lean_Elab_Tactic_VCGen_mkBackwardRuleForSplit(v_splitInfo_564_, v_info_565_, v_a_569_, v_a_570_, v_a_571_, v_a_572_);
if (lean_obj_tag(v___x_592_) == 0)
{
lean_object* v_a_593_; lean_object* v___x_594_; 
v_a_593_ = lean_ctor_get(v___x_592_, 0);
lean_inc(v_a_593_);
lean_dec_ref_known(v___x_592_, 1);
v___x_594_ = l_Lean_Meta_Sym_BackwardRule_shareCommon(v_a_593_, v_a_567_, v_a_568_, v_a_569_, v_a_570_, v_a_571_, v_a_572_);
if (lean_obj_tag(v___x_594_) == 0)
{
lean_object* v_a_595_; lean_object* v___x_597_; uint8_t v_isShared_598_; uint8_t v_isSharedCheck_622_; 
v_a_595_ = lean_ctor_get(v___x_594_, 0);
v_isSharedCheck_622_ = !lean_is_exclusive(v___x_594_);
if (v_isSharedCheck_622_ == 0)
{
v___x_597_ = v___x_594_;
v_isShared_598_ = v_isSharedCheck_622_;
goto v_resetjp_596_;
}
else
{
lean_inc(v_a_595_);
lean_dec(v___x_594_);
v___x_597_ = lean_box(0);
v_isShared_598_ = v_isSharedCheck_622_;
goto v_resetjp_596_;
}
v_resetjp_596_:
{
lean_object* v___x_599_; lean_object* v_specBackwardRuleCache_600_; lean_object* v_splitBackwardRuleCache_601_; lean_object* v_latticeBackwardRuleCache_602_; lean_object* v_frameBackwardRuleCache_603_; lean_object* v_frameDB_604_; lean_object* v_invariants_605_; lean_object* v_vcs_606_; lean_object* v_simpState_607_; lean_object* v_fuel_608_; lean_object* v_inlineHandledInvariants_609_; lean_object* v___x_611_; uint8_t v_isShared_612_; uint8_t v_isSharedCheck_621_; 
v___x_599_ = lean_st_ref_take(v_a_566_);
v_specBackwardRuleCache_600_ = lean_ctor_get(v___x_599_, 0);
v_splitBackwardRuleCache_601_ = lean_ctor_get(v___x_599_, 1);
v_latticeBackwardRuleCache_602_ = lean_ctor_get(v___x_599_, 2);
v_frameBackwardRuleCache_603_ = lean_ctor_get(v___x_599_, 3);
v_frameDB_604_ = lean_ctor_get(v___x_599_, 4);
v_invariants_605_ = lean_ctor_get(v___x_599_, 5);
v_vcs_606_ = lean_ctor_get(v___x_599_, 6);
v_simpState_607_ = lean_ctor_get(v___x_599_, 7);
v_fuel_608_ = lean_ctor_get(v___x_599_, 8);
v_inlineHandledInvariants_609_ = lean_ctor_get(v___x_599_, 9);
v_isSharedCheck_621_ = !lean_is_exclusive(v___x_599_);
if (v_isSharedCheck_621_ == 0)
{
v___x_611_ = v___x_599_;
v_isShared_612_ = v_isSharedCheck_621_;
goto v_resetjp_610_;
}
else
{
lean_inc(v_inlineHandledInvariants_609_);
lean_inc(v_fuel_608_);
lean_inc(v_simpState_607_);
lean_inc(v_vcs_606_);
lean_inc(v_invariants_605_);
lean_inc(v_frameDB_604_);
lean_inc(v_frameBackwardRuleCache_603_);
lean_inc(v_latticeBackwardRuleCache_602_);
lean_inc(v_splitBackwardRuleCache_601_);
lean_inc(v_specBackwardRuleCache_600_);
lean_dec(v___x_599_);
v___x_611_ = lean_box(0);
v_isShared_612_ = v_isSharedCheck_621_;
goto v_resetjp_610_;
}
v_resetjp_610_:
{
lean_object* v___x_613_; lean_object* v___x_615_; 
lean_inc(v_a_595_);
v___x_613_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2___redArg(v_splitBackwardRuleCache_601_, v_key_580_, v_a_595_);
if (v_isShared_612_ == 0)
{
lean_ctor_set(v___x_611_, 1, v___x_613_);
v___x_615_ = v___x_611_;
goto v_reusejp_614_;
}
else
{
lean_object* v_reuseFailAlloc_620_; 
v_reuseFailAlloc_620_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_620_, 0, v_specBackwardRuleCache_600_);
lean_ctor_set(v_reuseFailAlloc_620_, 1, v___x_613_);
lean_ctor_set(v_reuseFailAlloc_620_, 2, v_latticeBackwardRuleCache_602_);
lean_ctor_set(v_reuseFailAlloc_620_, 3, v_frameBackwardRuleCache_603_);
lean_ctor_set(v_reuseFailAlloc_620_, 4, v_frameDB_604_);
lean_ctor_set(v_reuseFailAlloc_620_, 5, v_invariants_605_);
lean_ctor_set(v_reuseFailAlloc_620_, 6, v_vcs_606_);
lean_ctor_set(v_reuseFailAlloc_620_, 7, v_simpState_607_);
lean_ctor_set(v_reuseFailAlloc_620_, 8, v_fuel_608_);
lean_ctor_set(v_reuseFailAlloc_620_, 9, v_inlineHandledInvariants_609_);
v___x_615_ = v_reuseFailAlloc_620_;
goto v_reusejp_614_;
}
v_reusejp_614_:
{
lean_object* v___x_616_; lean_object* v___x_618_; 
v___x_616_ = lean_st_ref_put(v_a_566_, v___x_615_);
if (v_isShared_598_ == 0)
{
v___x_618_ = v___x_597_;
goto v_reusejp_617_;
}
else
{
lean_object* v_reuseFailAlloc_619_; 
v_reuseFailAlloc_619_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_619_, 0, v_a_595_);
v___x_618_ = v_reuseFailAlloc_619_;
goto v_reusejp_617_;
}
v_reusejp_617_:
{
return v___x_618_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_key_580_, 2);
return v___x_594_;
}
}
else
{
lean_dec_ref_known(v_key_580_, 2);
return v___x_592_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_mkBackwardRuleForSplitCached___redArg___boxed(lean_object* v_splitInfo_628_, lean_object* v_info_629_, lean_object* v_a_630_, lean_object* v_a_631_, lean_object* v_a_632_, lean_object* v_a_633_, lean_object* v_a_634_, lean_object* v_a_635_, lean_object* v_a_636_, lean_object* v_a_637_){
_start:
{
lean_object* v_res_638_; 
v_res_638_ = l_Lean_Elab_Tactic_VCGen_mkBackwardRuleForSplitCached___redArg(v_splitInfo_628_, v_info_629_, v_a_630_, v_a_631_, v_a_632_, v_a_633_, v_a_634_, v_a_635_, v_a_636_);
lean_dec(v_a_636_);
lean_dec_ref(v_a_635_);
lean_dec(v_a_634_);
lean_dec_ref(v_a_633_);
lean_dec(v_a_632_);
lean_dec_ref(v_a_631_);
lean_dec(v_a_630_);
return v_res_638_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_mkBackwardRuleForSplitCached(lean_object* v_splitInfo_639_, lean_object* v_info_640_, lean_object* v_a_641_, lean_object* v_a_642_, lean_object* v_a_643_, lean_object* v_a_644_, lean_object* v_a_645_, lean_object* v_a_646_, lean_object* v_a_647_, lean_object* v_a_648_, lean_object* v_a_649_, lean_object* v_a_650_, lean_object* v_a_651_){
_start:
{
lean_object* v___x_653_; 
v___x_653_ = l_Lean_Elab_Tactic_VCGen_mkBackwardRuleForSplitCached___redArg(v_splitInfo_639_, v_info_640_, v_a_642_, v_a_646_, v_a_647_, v_a_648_, v_a_649_, v_a_650_, v_a_651_);
return v___x_653_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_mkBackwardRuleForSplitCached___boxed(lean_object* v_splitInfo_654_, lean_object* v_info_655_, lean_object* v_a_656_, lean_object* v_a_657_, lean_object* v_a_658_, lean_object* v_a_659_, lean_object* v_a_660_, lean_object* v_a_661_, lean_object* v_a_662_, lean_object* v_a_663_, lean_object* v_a_664_, lean_object* v_a_665_, lean_object* v_a_666_, lean_object* v_a_667_){
_start:
{
lean_object* v_res_668_; 
v_res_668_ = l_Lean_Elab_Tactic_VCGen_mkBackwardRuleForSplitCached(v_splitInfo_654_, v_info_655_, v_a_656_, v_a_657_, v_a_658_, v_a_659_, v_a_660_, v_a_661_, v_a_662_, v_a_663_, v_a_664_, v_a_665_, v_a_666_);
lean_dec(v_a_666_);
lean_dec_ref(v_a_665_);
lean_dec(v_a_664_);
lean_dec_ref(v_a_663_);
lean_dec(v_a_662_);
lean_dec_ref(v_a_661_);
lean_dec(v_a_660_);
lean_dec_ref(v_a_659_);
lean_dec(v_a_658_);
lean_dec(v_a_657_);
lean_dec_ref(v_a_656_);
return v_res_668_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1_spec__2___redArg(lean_object* v_a_669_, lean_object* v_x_670_){
_start:
{
if (lean_obj_tag(v_x_670_) == 0)
{
uint8_t v___x_671_; 
v___x_671_ = 0;
return v___x_671_;
}
else
{
lean_object* v_key_672_; lean_object* v_tail_673_; lean_object* v_fst_674_; lean_object* v_snd_675_; lean_object* v_fst_676_; lean_object* v_snd_677_; size_t v___x_678_; size_t v___x_679_; uint8_t v___x_680_; 
v_key_672_ = lean_ctor_get(v_x_670_, 0);
v_tail_673_ = lean_ctor_get(v_x_670_, 2);
v_fst_674_ = lean_ctor_get(v_key_672_, 0);
v_snd_675_ = lean_ctor_get(v_key_672_, 1);
v_fst_676_ = lean_ctor_get(v_a_669_, 0);
v_snd_677_ = lean_ctor_get(v_a_669_, 1);
v___x_678_ = lean_ptr_addr(v_fst_674_);
v___x_679_ = lean_ptr_addr(v_fst_676_);
v___x_680_ = lean_usize_dec_eq(v___x_678_, v___x_679_);
if (v___x_680_ == 0)
{
v_x_670_ = v_tail_673_;
goto _start;
}
else
{
uint8_t v___x_682_; 
v___x_682_ = lean_nat_dec_eq(v_snd_675_, v_snd_677_);
if (v___x_682_ == 0)
{
v_x_670_ = v_tail_673_;
goto _start;
}
else
{
return v___x_682_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1_spec__2___redArg___boxed(lean_object* v_a_684_, lean_object* v_x_685_){
_start:
{
uint8_t v_res_686_; lean_object* v_r_687_; 
v_res_686_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1_spec__2___redArg(v_a_684_, v_x_685_);
lean_dec(v_x_685_);
lean_dec_ref(v_a_684_);
v_r_687_ = lean_box(v_res_686_);
return v_r_687_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1_spec__4___redArg(lean_object* v_a_688_, lean_object* v_b_689_, lean_object* v_x_690_){
_start:
{
if (lean_obj_tag(v_x_690_) == 0)
{
lean_dec(v_b_689_);
lean_dec_ref(v_a_688_);
return v_x_690_;
}
else
{
lean_object* v_key_691_; lean_object* v_value_692_; lean_object* v_tail_693_; lean_object* v___x_695_; uint8_t v_isShared_696_; uint8_t v_isSharedCheck_711_; 
v_key_691_ = lean_ctor_get(v_x_690_, 0);
v_value_692_ = lean_ctor_get(v_x_690_, 1);
v_tail_693_ = lean_ctor_get(v_x_690_, 2);
v_isSharedCheck_711_ = !lean_is_exclusive(v_x_690_);
if (v_isSharedCheck_711_ == 0)
{
v___x_695_ = v_x_690_;
v_isShared_696_ = v_isSharedCheck_711_;
goto v_resetjp_694_;
}
else
{
lean_inc(v_tail_693_);
lean_inc(v_value_692_);
lean_inc(v_key_691_);
lean_dec(v_x_690_);
v___x_695_ = lean_box(0);
v_isShared_696_ = v_isSharedCheck_711_;
goto v_resetjp_694_;
}
v_resetjp_694_:
{
lean_object* v_fst_702_; lean_object* v_snd_703_; lean_object* v_fst_704_; lean_object* v_snd_705_; size_t v___x_706_; size_t v___x_707_; uint8_t v___x_708_; 
v_fst_702_ = lean_ctor_get(v_key_691_, 0);
v_snd_703_ = lean_ctor_get(v_key_691_, 1);
v_fst_704_ = lean_ctor_get(v_a_688_, 0);
v_snd_705_ = lean_ctor_get(v_a_688_, 1);
v___x_706_ = lean_ptr_addr(v_fst_702_);
v___x_707_ = lean_ptr_addr(v_fst_704_);
v___x_708_ = lean_usize_dec_eq(v___x_706_, v___x_707_);
if (v___x_708_ == 0)
{
goto v___jp_697_;
}
else
{
uint8_t v___x_709_; 
v___x_709_ = lean_nat_dec_eq(v_snd_703_, v_snd_705_);
if (v___x_709_ == 0)
{
goto v___jp_697_;
}
else
{
lean_object* v___x_710_; 
lean_del_object(v___x_695_);
lean_dec(v_value_692_);
lean_dec(v_key_691_);
v___x_710_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_710_, 0, v_a_688_);
lean_ctor_set(v___x_710_, 1, v_b_689_);
lean_ctor_set(v___x_710_, 2, v_tail_693_);
return v___x_710_;
}
}
v___jp_697_:
{
lean_object* v___x_698_; lean_object* v___x_700_; 
v___x_698_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1_spec__4___redArg(v_a_688_, v_b_689_, v_tail_693_);
if (v_isShared_696_ == 0)
{
lean_ctor_set(v___x_695_, 2, v___x_698_);
v___x_700_ = v___x_695_;
goto v_reusejp_699_;
}
else
{
lean_object* v_reuseFailAlloc_701_; 
v_reuseFailAlloc_701_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_701_, 0, v_key_691_);
lean_ctor_set(v_reuseFailAlloc_701_, 1, v_value_692_);
lean_ctor_set(v_reuseFailAlloc_701_, 2, v___x_698_);
v___x_700_ = v_reuseFailAlloc_701_;
goto v_reusejp_699_;
}
v_reusejp_699_:
{
return v___x_700_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1_spec__3_spec__4_spec__5___redArg(lean_object* v_x_712_, lean_object* v_x_713_){
_start:
{
if (lean_obj_tag(v_x_713_) == 0)
{
return v_x_712_;
}
else
{
lean_object* v_key_714_; lean_object* v_value_715_; lean_object* v_tail_716_; lean_object* v___x_718_; uint8_t v_isShared_719_; uint8_t v_isSharedCheck_746_; 
v_key_714_ = lean_ctor_get(v_x_713_, 0);
v_value_715_ = lean_ctor_get(v_x_713_, 1);
v_tail_716_ = lean_ctor_get(v_x_713_, 2);
v_isSharedCheck_746_ = !lean_is_exclusive(v_x_713_);
if (v_isSharedCheck_746_ == 0)
{
v___x_718_ = v_x_713_;
v_isShared_719_ = v_isSharedCheck_746_;
goto v_resetjp_717_;
}
else
{
lean_inc(v_tail_716_);
lean_inc(v_value_715_);
lean_inc(v_key_714_);
lean_dec(v_x_713_);
v___x_718_ = lean_box(0);
v_isShared_719_ = v_isSharedCheck_746_;
goto v_resetjp_717_;
}
v_resetjp_717_:
{
lean_object* v_fst_720_; lean_object* v_snd_721_; lean_object* v___x_722_; size_t v___x_723_; size_t v___x_724_; size_t v___x_725_; uint64_t v___x_726_; uint64_t v___x_727_; uint64_t v___x_728_; uint64_t v___x_729_; uint64_t v___x_730_; uint64_t v_fold_731_; uint64_t v___x_732_; uint64_t v___x_733_; uint64_t v___x_734_; size_t v___x_735_; size_t v___x_736_; size_t v___x_737_; size_t v___x_738_; size_t v___x_739_; lean_object* v___x_740_; lean_object* v___x_742_; 
v_fst_720_ = lean_ctor_get(v_key_714_, 0);
v_snd_721_ = lean_ctor_get(v_key_714_, 1);
v___x_722_ = lean_array_get_size(v_x_712_);
v___x_723_ = lean_ptr_addr(v_fst_720_);
v___x_724_ = ((size_t)3ULL);
v___x_725_ = lean_usize_shift_right(v___x_723_, v___x_724_);
v___x_726_ = lean_usize_to_uint64(v___x_725_);
v___x_727_ = lean_uint64_of_nat(v_snd_721_);
v___x_728_ = lean_uint64_mix_hash(v___x_726_, v___x_727_);
v___x_729_ = 32ULL;
v___x_730_ = lean_uint64_shift_right(v___x_728_, v___x_729_);
v_fold_731_ = lean_uint64_xor(v___x_728_, v___x_730_);
v___x_732_ = 16ULL;
v___x_733_ = lean_uint64_shift_right(v_fold_731_, v___x_732_);
v___x_734_ = lean_uint64_xor(v_fold_731_, v___x_733_);
v___x_735_ = lean_uint64_to_usize(v___x_734_);
v___x_736_ = lean_usize_of_nat(v___x_722_);
v___x_737_ = ((size_t)1ULL);
v___x_738_ = lean_usize_sub(v___x_736_, v___x_737_);
v___x_739_ = lean_usize_land(v___x_735_, v___x_738_);
v___x_740_ = lean_array_uget_borrowed(v_x_712_, v___x_739_);
lean_inc(v___x_740_);
if (v_isShared_719_ == 0)
{
lean_ctor_set(v___x_718_, 2, v___x_740_);
v___x_742_ = v___x_718_;
goto v_reusejp_741_;
}
else
{
lean_object* v_reuseFailAlloc_745_; 
v_reuseFailAlloc_745_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_745_, 0, v_key_714_);
lean_ctor_set(v_reuseFailAlloc_745_, 1, v_value_715_);
lean_ctor_set(v_reuseFailAlloc_745_, 2, v___x_740_);
v___x_742_ = v_reuseFailAlloc_745_;
goto v_reusejp_741_;
}
v_reusejp_741_:
{
lean_object* v___x_743_; 
v___x_743_ = lean_array_uset(v_x_712_, v___x_739_, v___x_742_);
v_x_712_ = v___x_743_;
v_x_713_ = v_tail_716_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1_spec__3_spec__4___redArg(lean_object* v_i_747_, lean_object* v_source_748_, lean_object* v_target_749_){
_start:
{
lean_object* v___x_750_; uint8_t v___x_751_; 
v___x_750_ = lean_array_get_size(v_source_748_);
v___x_751_ = lean_nat_dec_lt(v_i_747_, v___x_750_);
if (v___x_751_ == 0)
{
lean_dec_ref(v_source_748_);
lean_dec(v_i_747_);
return v_target_749_;
}
else
{
lean_object* v_es_752_; lean_object* v___x_753_; lean_object* v_source_754_; lean_object* v_target_755_; lean_object* v___x_756_; lean_object* v___x_757_; 
v_es_752_ = lean_array_fget(v_source_748_, v_i_747_);
v___x_753_ = lean_box(0);
v_source_754_ = lean_array_fset(v_source_748_, v_i_747_, v___x_753_);
v_target_755_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1_spec__3_spec__4_spec__5___redArg(v_target_749_, v_es_752_);
v___x_756_ = lean_unsigned_to_nat(1u);
v___x_757_ = lean_nat_add(v_i_747_, v___x_756_);
lean_dec(v_i_747_);
v_i_747_ = v___x_757_;
v_source_748_ = v_source_754_;
v_target_749_ = v_target_755_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1_spec__3___redArg(lean_object* v_data_759_){
_start:
{
lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v_nbuckets_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; 
v___x_760_ = lean_array_get_size(v_data_759_);
v___x_761_ = lean_unsigned_to_nat(2u);
v_nbuckets_762_ = lean_nat_mul(v___x_760_, v___x_761_);
v___x_763_ = lean_unsigned_to_nat(0u);
v___x_764_ = lean_box(0);
v___x_765_ = lean_mk_array(v_nbuckets_762_, v___x_764_);
v___x_766_ = lean_array_propagate_mark(v_data_759_, v___x_765_);
v___x_767_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1_spec__3_spec__4___redArg(v___x_763_, v_data_759_, v___x_766_);
return v___x_767_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1___redArg(lean_object* v_m_768_, lean_object* v_a_769_, lean_object* v_b_770_){
_start:
{
lean_object* v_size_771_; lean_object* v_buckets_772_; lean_object* v___x_774_; uint8_t v_isShared_775_; uint8_t v_isSharedCheck_822_; 
v_size_771_ = lean_ctor_get(v_m_768_, 0);
v_buckets_772_ = lean_ctor_get(v_m_768_, 1);
v_isSharedCheck_822_ = !lean_is_exclusive(v_m_768_);
if (v_isSharedCheck_822_ == 0)
{
v___x_774_ = v_m_768_;
v_isShared_775_ = v_isSharedCheck_822_;
goto v_resetjp_773_;
}
else
{
lean_inc(v_buckets_772_);
lean_inc(v_size_771_);
lean_dec(v_m_768_);
v___x_774_ = lean_box(0);
v_isShared_775_ = v_isSharedCheck_822_;
goto v_resetjp_773_;
}
v_resetjp_773_:
{
lean_object* v_fst_776_; lean_object* v_snd_777_; lean_object* v___x_778_; size_t v___x_779_; size_t v___x_780_; size_t v___x_781_; uint64_t v___x_782_; uint64_t v___x_783_; uint64_t v___x_784_; uint64_t v___x_785_; uint64_t v___x_786_; uint64_t v_fold_787_; uint64_t v___x_788_; uint64_t v___x_789_; uint64_t v___x_790_; size_t v___x_791_; size_t v___x_792_; size_t v___x_793_; size_t v___x_794_; size_t v___x_795_; lean_object* v_bkt_796_; uint8_t v___x_797_; 
v_fst_776_ = lean_ctor_get(v_a_769_, 0);
v_snd_777_ = lean_ctor_get(v_a_769_, 1);
v___x_778_ = lean_array_get_size(v_buckets_772_);
v___x_779_ = lean_ptr_addr(v_fst_776_);
v___x_780_ = ((size_t)3ULL);
v___x_781_ = lean_usize_shift_right(v___x_779_, v___x_780_);
v___x_782_ = lean_usize_to_uint64(v___x_781_);
v___x_783_ = lean_uint64_of_nat(v_snd_777_);
v___x_784_ = lean_uint64_mix_hash(v___x_782_, v___x_783_);
v___x_785_ = 32ULL;
v___x_786_ = lean_uint64_shift_right(v___x_784_, v___x_785_);
v_fold_787_ = lean_uint64_xor(v___x_784_, v___x_786_);
v___x_788_ = 16ULL;
v___x_789_ = lean_uint64_shift_right(v_fold_787_, v___x_788_);
v___x_790_ = lean_uint64_xor(v_fold_787_, v___x_789_);
v___x_791_ = lean_uint64_to_usize(v___x_790_);
v___x_792_ = lean_usize_of_nat(v___x_778_);
v___x_793_ = ((size_t)1ULL);
v___x_794_ = lean_usize_sub(v___x_792_, v___x_793_);
v___x_795_ = lean_usize_land(v___x_791_, v___x_794_);
v_bkt_796_ = lean_array_uget_borrowed(v_buckets_772_, v___x_795_);
v___x_797_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1_spec__2___redArg(v_a_769_, v_bkt_796_);
if (v___x_797_ == 0)
{
lean_object* v___x_798_; lean_object* v_size_x27_799_; lean_object* v___x_800_; lean_object* v_buckets_x27_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; uint8_t v___x_807_; 
v___x_798_ = lean_unsigned_to_nat(1u);
v_size_x27_799_ = lean_nat_add(v_size_771_, v___x_798_);
lean_dec(v_size_771_);
lean_inc(v_bkt_796_);
v___x_800_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_800_, 0, v_a_769_);
lean_ctor_set(v___x_800_, 1, v_b_770_);
lean_ctor_set(v___x_800_, 2, v_bkt_796_);
v_buckets_x27_801_ = lean_array_uset(v_buckets_772_, v___x_795_, v___x_800_);
v___x_802_ = lean_unsigned_to_nat(4u);
v___x_803_ = lean_nat_mul(v_size_x27_799_, v___x_802_);
v___x_804_ = lean_unsigned_to_nat(3u);
v___x_805_ = lean_nat_div(v___x_803_, v___x_804_);
lean_dec(v___x_803_);
v___x_806_ = lean_array_get_size(v_buckets_x27_801_);
v___x_807_ = lean_nat_dec_le(v___x_805_, v___x_806_);
lean_dec(v___x_805_);
if (v___x_807_ == 0)
{
lean_object* v_val_808_; lean_object* v___x_810_; 
v_val_808_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1_spec__3___redArg(v_buckets_x27_801_);
if (v_isShared_775_ == 0)
{
lean_ctor_set(v___x_774_, 1, v_val_808_);
lean_ctor_set(v___x_774_, 0, v_size_x27_799_);
v___x_810_ = v___x_774_;
goto v_reusejp_809_;
}
else
{
lean_object* v_reuseFailAlloc_811_; 
v_reuseFailAlloc_811_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_811_, 0, v_size_x27_799_);
lean_ctor_set(v_reuseFailAlloc_811_, 1, v_val_808_);
v___x_810_ = v_reuseFailAlloc_811_;
goto v_reusejp_809_;
}
v_reusejp_809_:
{
return v___x_810_;
}
}
else
{
lean_object* v___x_813_; 
if (v_isShared_775_ == 0)
{
lean_ctor_set(v___x_774_, 1, v_buckets_x27_801_);
lean_ctor_set(v___x_774_, 0, v_size_x27_799_);
v___x_813_ = v___x_774_;
goto v_reusejp_812_;
}
else
{
lean_object* v_reuseFailAlloc_814_; 
v_reuseFailAlloc_814_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_814_, 0, v_size_x27_799_);
lean_ctor_set(v_reuseFailAlloc_814_, 1, v_buckets_x27_801_);
v___x_813_ = v_reuseFailAlloc_814_;
goto v_reusejp_812_;
}
v_reusejp_812_:
{
return v___x_813_;
}
}
}
else
{
lean_object* v___x_815_; lean_object* v_buckets_x27_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_820_; 
lean_inc(v_bkt_796_);
v___x_815_ = lean_box(0);
v_buckets_x27_816_ = lean_array_uset(v_buckets_772_, v___x_795_, v___x_815_);
v___x_817_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1_spec__4___redArg(v_a_769_, v_b_770_, v_bkt_796_);
v___x_818_ = lean_array_uset(v_buckets_x27_816_, v___x_795_, v___x_817_);
if (v_isShared_775_ == 0)
{
lean_ctor_set(v___x_774_, 1, v___x_818_);
v___x_820_ = v___x_774_;
goto v_reusejp_819_;
}
else
{
lean_object* v_reuseFailAlloc_821_; 
v_reuseFailAlloc_821_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_821_, 0, v_size_771_);
lean_ctor_set(v_reuseFailAlloc_821_, 1, v___x_818_);
v___x_820_ = v_reuseFailAlloc_821_;
goto v_reusejp_819_;
}
v_reusejp_819_:
{
return v___x_820_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__0_spec__0___redArg(lean_object* v_a_823_, lean_object* v_x_824_){
_start:
{
if (lean_obj_tag(v_x_824_) == 0)
{
lean_object* v___x_825_; 
v___x_825_ = lean_box(0);
return v___x_825_;
}
else
{
lean_object* v_key_826_; lean_object* v_value_827_; lean_object* v_tail_828_; lean_object* v_fst_829_; lean_object* v_snd_830_; lean_object* v_fst_831_; lean_object* v_snd_832_; size_t v___x_833_; size_t v___x_834_; uint8_t v___x_835_; 
v_key_826_ = lean_ctor_get(v_x_824_, 0);
v_value_827_ = lean_ctor_get(v_x_824_, 1);
v_tail_828_ = lean_ctor_get(v_x_824_, 2);
v_fst_829_ = lean_ctor_get(v_key_826_, 0);
v_snd_830_ = lean_ctor_get(v_key_826_, 1);
v_fst_831_ = lean_ctor_get(v_a_823_, 0);
v_snd_832_ = lean_ctor_get(v_a_823_, 1);
v___x_833_ = lean_ptr_addr(v_fst_829_);
v___x_834_ = lean_ptr_addr(v_fst_831_);
v___x_835_ = lean_usize_dec_eq(v___x_833_, v___x_834_);
if (v___x_835_ == 0)
{
v_x_824_ = v_tail_828_;
goto _start;
}
else
{
uint8_t v___x_837_; 
v___x_837_ = lean_nat_dec_eq(v_snd_830_, v_snd_832_);
if (v___x_837_ == 0)
{
v_x_824_ = v_tail_828_;
goto _start;
}
else
{
lean_object* v___x_839_; 
lean_inc(v_value_827_);
v___x_839_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_839_, 0, v_value_827_);
return v___x_839_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__0_spec__0___redArg___boxed(lean_object* v_a_840_, lean_object* v_x_841_){
_start:
{
lean_object* v_res_842_; 
v_res_842_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__0_spec__0___redArg(v_a_840_, v_x_841_);
lean_dec(v_x_841_);
lean_dec_ref(v_a_840_);
return v_res_842_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__0___redArg(lean_object* v_m_843_, lean_object* v_a_844_){
_start:
{
lean_object* v_buckets_845_; lean_object* v_fst_846_; lean_object* v_snd_847_; lean_object* v___x_848_; size_t v___x_849_; size_t v___x_850_; size_t v___x_851_; uint64_t v___x_852_; uint64_t v___x_853_; uint64_t v___x_854_; uint64_t v___x_855_; uint64_t v___x_856_; uint64_t v_fold_857_; uint64_t v___x_858_; uint64_t v___x_859_; uint64_t v___x_860_; size_t v___x_861_; size_t v___x_862_; size_t v___x_863_; size_t v___x_864_; size_t v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; 
v_buckets_845_ = lean_ctor_get(v_m_843_, 1);
v_fst_846_ = lean_ctor_get(v_a_844_, 0);
v_snd_847_ = lean_ctor_get(v_a_844_, 1);
v___x_848_ = lean_array_get_size(v_buckets_845_);
v___x_849_ = lean_ptr_addr(v_fst_846_);
v___x_850_ = ((size_t)3ULL);
v___x_851_ = lean_usize_shift_right(v___x_849_, v___x_850_);
v___x_852_ = lean_usize_to_uint64(v___x_851_);
v___x_853_ = lean_uint64_of_nat(v_snd_847_);
v___x_854_ = lean_uint64_mix_hash(v___x_852_, v___x_853_);
v___x_855_ = 32ULL;
v___x_856_ = lean_uint64_shift_right(v___x_854_, v___x_855_);
v_fold_857_ = lean_uint64_xor(v___x_854_, v___x_856_);
v___x_858_ = 16ULL;
v___x_859_ = lean_uint64_shift_right(v_fold_857_, v___x_858_);
v___x_860_ = lean_uint64_xor(v_fold_857_, v___x_859_);
v___x_861_ = lean_uint64_to_usize(v___x_860_);
v___x_862_ = lean_usize_of_nat(v___x_848_);
v___x_863_ = ((size_t)1ULL);
v___x_864_ = lean_usize_sub(v___x_862_, v___x_863_);
v___x_865_ = lean_usize_land(v___x_861_, v___x_864_);
v___x_866_ = lean_array_uget_borrowed(v_buckets_845_, v___x_865_);
v___x_867_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__0_spec__0___redArg(v_a_844_, v___x_866_);
return v___x_867_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__0___redArg___boxed(lean_object* v_m_868_, lean_object* v_a_869_){
_start:
{
lean_object* v_res_870_; 
v_res_870_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__0___redArg(v_m_868_, v_a_869_);
lean_dec_ref(v_a_869_);
lean_dec_ref(v_m_868_);
return v_res_870_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached___redArg(lean_object* v_rhs_871_, lean_object* v_op_872_, lean_object* v_a_873_, lean_object* v_a_874_, lean_object* v_a_875_, lean_object* v_a_876_, lean_object* v_a_877_, lean_object* v_a_878_, lean_object* v_a_879_){
_start:
{
lean_object* v_numConst_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v_key_884_; lean_object* v___x_885_; lean_object* v_latticeBackwardRuleCache_886_; lean_object* v___x_887_; 
v_numConst_881_ = lean_ctor_get(v_op_872_, 1);
v___x_882_ = l_Lean_Expr_getAppPrefix(v_rhs_871_, v_numConst_881_);
v___x_883_ = l_Lean_Expr_getAppNumArgs(v_rhs_871_);
v_key_884_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_key_884_, 0, v___x_882_);
lean_ctor_set(v_key_884_, 1, v___x_883_);
v___x_885_ = lean_st_ref_get(v_a_873_);
v_latticeBackwardRuleCache_886_ = lean_ctor_get(v___x_885_, 2);
lean_inc_ref(v_latticeBackwardRuleCache_886_);
lean_dec(v___x_885_);
v___x_887_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__0___redArg(v_latticeBackwardRuleCache_886_, v_key_884_);
lean_dec_ref(v_latticeBackwardRuleCache_886_);
if (lean_obj_tag(v___x_887_) == 1)
{
lean_object* v_val_888_; lean_object* v___x_890_; uint8_t v_isShared_891_; uint8_t v_isSharedCheck_895_; 
lean_dec_ref_known(v_key_884_, 2);
lean_dec_ref(v_op_872_);
lean_dec_ref(v_rhs_871_);
v_val_888_ = lean_ctor_get(v___x_887_, 0);
v_isSharedCheck_895_ = !lean_is_exclusive(v___x_887_);
if (v_isSharedCheck_895_ == 0)
{
v___x_890_ = v___x_887_;
v_isShared_891_ = v_isSharedCheck_895_;
goto v_resetjp_889_;
}
else
{
lean_inc(v_val_888_);
lean_dec(v___x_887_);
v___x_890_ = lean_box(0);
v_isShared_891_ = v_isSharedCheck_895_;
goto v_resetjp_889_;
}
v_resetjp_889_:
{
lean_object* v___x_893_; 
if (v_isShared_891_ == 0)
{
lean_ctor_set_tag(v___x_890_, 0);
v___x_893_ = v___x_890_;
goto v_reusejp_892_;
}
else
{
lean_object* v_reuseFailAlloc_894_; 
v_reuseFailAlloc_894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_894_, 0, v_val_888_);
v___x_893_ = v_reuseFailAlloc_894_;
goto v_reusejp_892_;
}
v_reusejp_892_:
{
return v___x_893_;
}
}
}
else
{
lean_object* v___x_896_; 
lean_dec(v___x_887_);
v___x_896_ = l_Lean_Elab_Tactic_VCGen_mkLatticeOpRule(v_rhs_871_, v_op_872_, v_a_874_, v_a_875_, v_a_876_, v_a_877_, v_a_878_, v_a_879_);
if (lean_obj_tag(v___x_896_) == 0)
{
lean_object* v_a_897_; lean_object* v___x_898_; 
v_a_897_ = lean_ctor_get(v___x_896_, 0);
lean_inc(v_a_897_);
lean_dec_ref_known(v___x_896_, 1);
v___x_898_ = l_Lean_Meta_Sym_BackwardRule_shareCommon(v_a_897_, v_a_874_, v_a_875_, v_a_876_, v_a_877_, v_a_878_, v_a_879_);
if (lean_obj_tag(v___x_898_) == 0)
{
lean_object* v_a_899_; lean_object* v___x_901_; uint8_t v_isShared_902_; uint8_t v_isSharedCheck_926_; 
v_a_899_ = lean_ctor_get(v___x_898_, 0);
v_isSharedCheck_926_ = !lean_is_exclusive(v___x_898_);
if (v_isSharedCheck_926_ == 0)
{
v___x_901_ = v___x_898_;
v_isShared_902_ = v_isSharedCheck_926_;
goto v_resetjp_900_;
}
else
{
lean_inc(v_a_899_);
lean_dec(v___x_898_);
v___x_901_ = lean_box(0);
v_isShared_902_ = v_isSharedCheck_926_;
goto v_resetjp_900_;
}
v_resetjp_900_:
{
lean_object* v___x_903_; lean_object* v_specBackwardRuleCache_904_; lean_object* v_splitBackwardRuleCache_905_; lean_object* v_latticeBackwardRuleCache_906_; lean_object* v_frameBackwardRuleCache_907_; lean_object* v_frameDB_908_; lean_object* v_invariants_909_; lean_object* v_vcs_910_; lean_object* v_simpState_911_; lean_object* v_fuel_912_; lean_object* v_inlineHandledInvariants_913_; lean_object* v___x_915_; uint8_t v_isShared_916_; uint8_t v_isSharedCheck_925_; 
v___x_903_ = lean_st_ref_take(v_a_873_);
v_specBackwardRuleCache_904_ = lean_ctor_get(v___x_903_, 0);
v_splitBackwardRuleCache_905_ = lean_ctor_get(v___x_903_, 1);
v_latticeBackwardRuleCache_906_ = lean_ctor_get(v___x_903_, 2);
v_frameBackwardRuleCache_907_ = lean_ctor_get(v___x_903_, 3);
v_frameDB_908_ = lean_ctor_get(v___x_903_, 4);
v_invariants_909_ = lean_ctor_get(v___x_903_, 5);
v_vcs_910_ = lean_ctor_get(v___x_903_, 6);
v_simpState_911_ = lean_ctor_get(v___x_903_, 7);
v_fuel_912_ = lean_ctor_get(v___x_903_, 8);
v_inlineHandledInvariants_913_ = lean_ctor_get(v___x_903_, 9);
v_isSharedCheck_925_ = !lean_is_exclusive(v___x_903_);
if (v_isSharedCheck_925_ == 0)
{
v___x_915_ = v___x_903_;
v_isShared_916_ = v_isSharedCheck_925_;
goto v_resetjp_914_;
}
else
{
lean_inc(v_inlineHandledInvariants_913_);
lean_inc(v_fuel_912_);
lean_inc(v_simpState_911_);
lean_inc(v_vcs_910_);
lean_inc(v_invariants_909_);
lean_inc(v_frameDB_908_);
lean_inc(v_frameBackwardRuleCache_907_);
lean_inc(v_latticeBackwardRuleCache_906_);
lean_inc(v_splitBackwardRuleCache_905_);
lean_inc(v_specBackwardRuleCache_904_);
lean_dec(v___x_903_);
v___x_915_ = lean_box(0);
v_isShared_916_ = v_isSharedCheck_925_;
goto v_resetjp_914_;
}
v_resetjp_914_:
{
lean_object* v___x_917_; lean_object* v___x_919_; 
lean_inc(v_a_899_);
v___x_917_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1___redArg(v_latticeBackwardRuleCache_906_, v_key_884_, v_a_899_);
if (v_isShared_916_ == 0)
{
lean_ctor_set(v___x_915_, 2, v___x_917_);
v___x_919_ = v___x_915_;
goto v_reusejp_918_;
}
else
{
lean_object* v_reuseFailAlloc_924_; 
v_reuseFailAlloc_924_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_924_, 0, v_specBackwardRuleCache_904_);
lean_ctor_set(v_reuseFailAlloc_924_, 1, v_splitBackwardRuleCache_905_);
lean_ctor_set(v_reuseFailAlloc_924_, 2, v___x_917_);
lean_ctor_set(v_reuseFailAlloc_924_, 3, v_frameBackwardRuleCache_907_);
lean_ctor_set(v_reuseFailAlloc_924_, 4, v_frameDB_908_);
lean_ctor_set(v_reuseFailAlloc_924_, 5, v_invariants_909_);
lean_ctor_set(v_reuseFailAlloc_924_, 6, v_vcs_910_);
lean_ctor_set(v_reuseFailAlloc_924_, 7, v_simpState_911_);
lean_ctor_set(v_reuseFailAlloc_924_, 8, v_fuel_912_);
lean_ctor_set(v_reuseFailAlloc_924_, 9, v_inlineHandledInvariants_913_);
v___x_919_ = v_reuseFailAlloc_924_;
goto v_reusejp_918_;
}
v_reusejp_918_:
{
lean_object* v___x_920_; lean_object* v___x_922_; 
v___x_920_ = lean_st_ref_put(v_a_873_, v___x_919_);
if (v_isShared_902_ == 0)
{
v___x_922_ = v___x_901_;
goto v_reusejp_921_;
}
else
{
lean_object* v_reuseFailAlloc_923_; 
v_reuseFailAlloc_923_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_923_, 0, v_a_899_);
v___x_922_ = v_reuseFailAlloc_923_;
goto v_reusejp_921_;
}
v_reusejp_921_:
{
return v___x_922_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_key_884_, 2);
return v___x_898_;
}
}
else
{
lean_dec_ref_known(v_key_884_, 2);
return v___x_896_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached___redArg___boxed(lean_object* v_rhs_927_, lean_object* v_op_928_, lean_object* v_a_929_, lean_object* v_a_930_, lean_object* v_a_931_, lean_object* v_a_932_, lean_object* v_a_933_, lean_object* v_a_934_, lean_object* v_a_935_, lean_object* v_a_936_){
_start:
{
lean_object* v_res_937_; 
v_res_937_ = l_Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached___redArg(v_rhs_927_, v_op_928_, v_a_929_, v_a_930_, v_a_931_, v_a_932_, v_a_933_, v_a_934_, v_a_935_);
lean_dec(v_a_935_);
lean_dec_ref(v_a_934_);
lean_dec(v_a_933_);
lean_dec_ref(v_a_932_);
lean_dec(v_a_931_);
lean_dec_ref(v_a_930_);
lean_dec(v_a_929_);
return v_res_937_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached(lean_object* v_rhs_938_, lean_object* v_op_939_, lean_object* v_a_940_, lean_object* v_a_941_, lean_object* v_a_942_, lean_object* v_a_943_, lean_object* v_a_944_, lean_object* v_a_945_, lean_object* v_a_946_, lean_object* v_a_947_, lean_object* v_a_948_, lean_object* v_a_949_, lean_object* v_a_950_){
_start:
{
lean_object* v___x_952_; 
v___x_952_ = l_Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached___redArg(v_rhs_938_, v_op_939_, v_a_941_, v_a_945_, v_a_946_, v_a_947_, v_a_948_, v_a_949_, v_a_950_);
return v___x_952_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached___boxed(lean_object* v_rhs_953_, lean_object* v_op_954_, lean_object* v_a_955_, lean_object* v_a_956_, lean_object* v_a_957_, lean_object* v_a_958_, lean_object* v_a_959_, lean_object* v_a_960_, lean_object* v_a_961_, lean_object* v_a_962_, lean_object* v_a_963_, lean_object* v_a_964_, lean_object* v_a_965_, lean_object* v_a_966_){
_start:
{
lean_object* v_res_967_; 
v_res_967_ = l_Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached(v_rhs_953_, v_op_954_, v_a_955_, v_a_956_, v_a_957_, v_a_958_, v_a_959_, v_a_960_, v_a_961_, v_a_962_, v_a_963_, v_a_964_, v_a_965_);
lean_dec(v_a_965_);
lean_dec_ref(v_a_964_);
lean_dec(v_a_963_);
lean_dec_ref(v_a_962_);
lean_dec(v_a_961_);
lean_dec_ref(v_a_960_);
lean_dec(v_a_959_);
lean_dec_ref(v_a_958_);
lean_dec(v_a_957_);
lean_dec(v_a_956_);
lean_dec_ref(v_a_955_);
return v_res_967_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__0(lean_object* v_00_u03b2_968_, lean_object* v_m_969_, lean_object* v_a_970_){
_start:
{
lean_object* v___x_971_; 
v___x_971_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__0___redArg(v_m_969_, v_a_970_);
return v___x_971_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__0___boxed(lean_object* v_00_u03b2_972_, lean_object* v_m_973_, lean_object* v_a_974_){
_start:
{
lean_object* v_res_975_; 
v_res_975_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__0(v_00_u03b2_972_, v_m_973_, v_a_974_);
lean_dec_ref(v_a_974_);
lean_dec_ref(v_m_973_);
return v_res_975_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1(lean_object* v_00_u03b2_976_, lean_object* v_m_977_, lean_object* v_a_978_, lean_object* v_b_979_){
_start:
{
lean_object* v___x_980_; 
v___x_980_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1___redArg(v_m_977_, v_a_978_, v_b_979_);
return v___x_980_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__0_spec__0(lean_object* v_00_u03b2_981_, lean_object* v_a_982_, lean_object* v_x_983_){
_start:
{
lean_object* v___x_984_; 
v___x_984_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__0_spec__0___redArg(v_a_982_, v_x_983_);
return v___x_984_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__0_spec__0___boxed(lean_object* v_00_u03b2_985_, lean_object* v_a_986_, lean_object* v_x_987_){
_start:
{
lean_object* v_res_988_; 
v_res_988_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__0_spec__0(v_00_u03b2_985_, v_a_986_, v_x_987_);
lean_dec(v_x_987_);
lean_dec_ref(v_a_986_);
return v_res_988_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1_spec__2(lean_object* v_00_u03b2_989_, lean_object* v_a_990_, lean_object* v_x_991_){
_start:
{
uint8_t v___x_992_; 
v___x_992_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1_spec__2___redArg(v_a_990_, v_x_991_);
return v___x_992_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1_spec__2___boxed(lean_object* v_00_u03b2_993_, lean_object* v_a_994_, lean_object* v_x_995_){
_start:
{
uint8_t v_res_996_; lean_object* v_r_997_; 
v_res_996_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1_spec__2(v_00_u03b2_993_, v_a_994_, v_x_995_);
lean_dec(v_x_995_);
lean_dec_ref(v_a_994_);
v_r_997_ = lean_box(v_res_996_);
return v_r_997_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1_spec__3(lean_object* v_00_u03b2_998_, lean_object* v_data_999_){
_start:
{
lean_object* v___x_1000_; 
v___x_1000_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1_spec__3___redArg(v_data_999_);
return v___x_1000_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1_spec__4(lean_object* v_00_u03b2_1001_, lean_object* v_a_1002_, lean_object* v_b_1003_, lean_object* v_x_1004_){
_start:
{
lean_object* v___x_1005_; 
v___x_1005_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1_spec__4___redArg(v_a_1002_, v_b_1003_, v_x_1004_);
return v___x_1005_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1_spec__3_spec__4(lean_object* v_00_u03b2_1006_, lean_object* v_i_1007_, lean_object* v_source_1008_, lean_object* v_target_1009_){
_start:
{
lean_object* v___x_1010_; 
v___x_1010_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1_spec__3_spec__4___redArg(v_i_1007_, v_source_1008_, v_target_1009_);
return v___x_1010_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1_spec__3_spec__4_spec__5(lean_object* v_00_u03b2_1011_, lean_object* v_x_1012_, lean_object* v_x_1013_){
_start:
{
lean_object* v___x_1014_; 
v___x_1014_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1_spec__3_spec__4_spec__5___redArg(v_x_1012_, v_x_1013_);
return v___x_1014_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_mkFrameBackwardRuleCached___redArg(lean_object* v_fp_1015_, lean_object* v_info_1016_, lean_object* v_a_1017_, lean_object* v_a_1018_, lean_object* v_a_1019_, lean_object* v_a_1020_, lean_object* v_a_1021_, lean_object* v_a_1022_, lean_object* v_a_1023_){
_start:
{
lean_object* v_excessArgs_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v_key_1028_; lean_object* v___x_1029_; lean_object* v_frameBackwardRuleCache_1030_; lean_object* v___x_1031_; 
v_excessArgs_1025_ = lean_ctor_get(v_info_1016_, 3);
v___x_1026_ = l_Lean_Elab_Tactic_VCGen_WPApp_instWP(v_info_1016_);
v___x_1027_ = lean_array_get_size(v_excessArgs_1025_);
v_key_1028_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_key_1028_, 0, v___x_1026_);
lean_ctor_set(v_key_1028_, 1, v___x_1027_);
v___x_1029_ = lean_st_ref_get(v_a_1017_);
v_frameBackwardRuleCache_1030_ = lean_ctor_get(v___x_1029_, 3);
lean_inc_ref(v_frameBackwardRuleCache_1030_);
lean_dec(v___x_1029_);
v___x_1031_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__0___redArg(v_frameBackwardRuleCache_1030_, v_key_1028_);
lean_dec_ref(v_frameBackwardRuleCache_1030_);
if (lean_obj_tag(v___x_1031_) == 1)
{
lean_object* v_val_1032_; lean_object* v___x_1034_; uint8_t v_isShared_1035_; uint8_t v_isSharedCheck_1039_; 
lean_dec_ref_known(v_key_1028_, 2);
lean_dec_ref(v_info_1016_);
lean_dec_ref(v_fp_1015_);
v_val_1032_ = lean_ctor_get(v___x_1031_, 0);
v_isSharedCheck_1039_ = !lean_is_exclusive(v___x_1031_);
if (v_isSharedCheck_1039_ == 0)
{
v___x_1034_ = v___x_1031_;
v_isShared_1035_ = v_isSharedCheck_1039_;
goto v_resetjp_1033_;
}
else
{
lean_inc(v_val_1032_);
lean_dec(v___x_1031_);
v___x_1034_ = lean_box(0);
v_isShared_1035_ = v_isSharedCheck_1039_;
goto v_resetjp_1033_;
}
v_resetjp_1033_:
{
lean_object* v___x_1037_; 
if (v_isShared_1035_ == 0)
{
lean_ctor_set_tag(v___x_1034_, 0);
v___x_1037_ = v___x_1034_;
goto v_reusejp_1036_;
}
else
{
lean_object* v_reuseFailAlloc_1038_; 
v_reuseFailAlloc_1038_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1038_, 0, v_val_1032_);
v___x_1037_ = v_reuseFailAlloc_1038_;
goto v_reusejp_1036_;
}
v_reusejp_1036_:
{
return v___x_1037_;
}
}
}
else
{
lean_object* v___x_1040_; 
lean_dec(v___x_1031_);
v___x_1040_ = l_Lean_Elab_Tactic_VCGen_mkFrameBackwardRule(v_fp_1015_, v_info_1016_, v_a_1020_, v_a_1021_, v_a_1022_, v_a_1023_);
if (lean_obj_tag(v___x_1040_) == 0)
{
lean_object* v_a_1041_; lean_object* v_rule_1042_; lean_object* v_splitVCIdx_1043_; lean_object* v_frameIdx_1044_; lean_object* v___x_1046_; uint8_t v_isShared_1047_; uint8_t v_isSharedCheck_1088_; 
v_a_1041_ = lean_ctor_get(v___x_1040_, 0);
lean_inc(v_a_1041_);
lean_dec_ref_known(v___x_1040_, 1);
v_rule_1042_ = lean_ctor_get(v_a_1041_, 0);
v_splitVCIdx_1043_ = lean_ctor_get(v_a_1041_, 1);
v_frameIdx_1044_ = lean_ctor_get(v_a_1041_, 2);
v_isSharedCheck_1088_ = !lean_is_exclusive(v_a_1041_);
if (v_isSharedCheck_1088_ == 0)
{
v___x_1046_ = v_a_1041_;
v_isShared_1047_ = v_isSharedCheck_1088_;
goto v_resetjp_1045_;
}
else
{
lean_inc(v_frameIdx_1044_);
lean_inc(v_splitVCIdx_1043_);
lean_inc(v_rule_1042_);
lean_dec(v_a_1041_);
v___x_1046_ = lean_box(0);
v_isShared_1047_ = v_isSharedCheck_1088_;
goto v_resetjp_1045_;
}
v_resetjp_1045_:
{
lean_object* v___x_1048_; 
v___x_1048_ = l_Lean_Meta_Sym_BackwardRule_shareCommon(v_rule_1042_, v_a_1018_, v_a_1019_, v_a_1020_, v_a_1021_, v_a_1022_, v_a_1023_);
if (lean_obj_tag(v___x_1048_) == 0)
{
lean_object* v_a_1049_; lean_object* v___x_1051_; uint8_t v_isShared_1052_; uint8_t v_isSharedCheck_1079_; 
v_a_1049_ = lean_ctor_get(v___x_1048_, 0);
v_isSharedCheck_1079_ = !lean_is_exclusive(v___x_1048_);
if (v_isSharedCheck_1079_ == 0)
{
v___x_1051_ = v___x_1048_;
v_isShared_1052_ = v_isSharedCheck_1079_;
goto v_resetjp_1050_;
}
else
{
lean_inc(v_a_1049_);
lean_dec(v___x_1048_);
v___x_1051_ = lean_box(0);
v_isShared_1052_ = v_isSharedCheck_1079_;
goto v_resetjp_1050_;
}
v_resetjp_1050_:
{
lean_object* v___x_1054_; 
if (v_isShared_1047_ == 0)
{
lean_ctor_set(v___x_1046_, 0, v_a_1049_);
v___x_1054_ = v___x_1046_;
goto v_reusejp_1053_;
}
else
{
lean_object* v_reuseFailAlloc_1078_; 
v_reuseFailAlloc_1078_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1078_, 0, v_a_1049_);
lean_ctor_set(v_reuseFailAlloc_1078_, 1, v_splitVCIdx_1043_);
lean_ctor_set(v_reuseFailAlloc_1078_, 2, v_frameIdx_1044_);
v___x_1054_ = v_reuseFailAlloc_1078_;
goto v_reusejp_1053_;
}
v_reusejp_1053_:
{
lean_object* v___x_1055_; lean_object* v_specBackwardRuleCache_1056_; lean_object* v_splitBackwardRuleCache_1057_; lean_object* v_latticeBackwardRuleCache_1058_; lean_object* v_frameBackwardRuleCache_1059_; lean_object* v_frameDB_1060_; lean_object* v_invariants_1061_; lean_object* v_vcs_1062_; lean_object* v_simpState_1063_; lean_object* v_fuel_1064_; lean_object* v_inlineHandledInvariants_1065_; lean_object* v___x_1067_; uint8_t v_isShared_1068_; uint8_t v_isSharedCheck_1077_; 
v___x_1055_ = lean_st_ref_take(v_a_1017_);
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
v_isSharedCheck_1077_ = !lean_is_exclusive(v___x_1055_);
if (v_isSharedCheck_1077_ == 0)
{
v___x_1067_ = v___x_1055_;
v_isShared_1068_ = v_isSharedCheck_1077_;
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
v_isShared_1068_ = v_isSharedCheck_1077_;
goto v_resetjp_1066_;
}
v_resetjp_1066_:
{
lean_object* v___x_1069_; lean_object* v___x_1071_; 
lean_inc_ref(v___x_1054_);
v___x_1069_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1___redArg(v_frameBackwardRuleCache_1059_, v_key_1028_, v___x_1054_);
if (v_isShared_1068_ == 0)
{
lean_ctor_set(v___x_1067_, 3, v___x_1069_);
v___x_1071_ = v___x_1067_;
goto v_reusejp_1070_;
}
else
{
lean_object* v_reuseFailAlloc_1076_; 
v_reuseFailAlloc_1076_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1076_, 0, v_specBackwardRuleCache_1056_);
lean_ctor_set(v_reuseFailAlloc_1076_, 1, v_splitBackwardRuleCache_1057_);
lean_ctor_set(v_reuseFailAlloc_1076_, 2, v_latticeBackwardRuleCache_1058_);
lean_ctor_set(v_reuseFailAlloc_1076_, 3, v___x_1069_);
lean_ctor_set(v_reuseFailAlloc_1076_, 4, v_frameDB_1060_);
lean_ctor_set(v_reuseFailAlloc_1076_, 5, v_invariants_1061_);
lean_ctor_set(v_reuseFailAlloc_1076_, 6, v_vcs_1062_);
lean_ctor_set(v_reuseFailAlloc_1076_, 7, v_simpState_1063_);
lean_ctor_set(v_reuseFailAlloc_1076_, 8, v_fuel_1064_);
lean_ctor_set(v_reuseFailAlloc_1076_, 9, v_inlineHandledInvariants_1065_);
v___x_1071_ = v_reuseFailAlloc_1076_;
goto v_reusejp_1070_;
}
v_reusejp_1070_:
{
lean_object* v___x_1072_; lean_object* v___x_1074_; 
v___x_1072_ = lean_st_ref_put(v_a_1017_, v___x_1071_);
if (v_isShared_1052_ == 0)
{
lean_ctor_set(v___x_1051_, 0, v___x_1054_);
v___x_1074_ = v___x_1051_;
goto v_reusejp_1073_;
}
else
{
lean_object* v_reuseFailAlloc_1075_; 
v_reuseFailAlloc_1075_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1075_, 0, v___x_1054_);
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
}
}
else
{
lean_object* v_a_1080_; lean_object* v___x_1082_; uint8_t v_isShared_1083_; uint8_t v_isSharedCheck_1087_; 
lean_del_object(v___x_1046_);
lean_dec(v_frameIdx_1044_);
lean_dec(v_splitVCIdx_1043_);
lean_dec_ref_known(v_key_1028_, 2);
v_a_1080_ = lean_ctor_get(v___x_1048_, 0);
v_isSharedCheck_1087_ = !lean_is_exclusive(v___x_1048_);
if (v_isSharedCheck_1087_ == 0)
{
v___x_1082_ = v___x_1048_;
v_isShared_1083_ = v_isSharedCheck_1087_;
goto v_resetjp_1081_;
}
else
{
lean_inc(v_a_1080_);
lean_dec(v___x_1048_);
v___x_1082_ = lean_box(0);
v_isShared_1083_ = v_isSharedCheck_1087_;
goto v_resetjp_1081_;
}
v_resetjp_1081_:
{
lean_object* v___x_1085_; 
if (v_isShared_1083_ == 0)
{
v___x_1085_ = v___x_1082_;
goto v_reusejp_1084_;
}
else
{
lean_object* v_reuseFailAlloc_1086_; 
v_reuseFailAlloc_1086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1086_, 0, v_a_1080_);
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
}
else
{
lean_dec_ref_known(v_key_1028_, 2);
return v___x_1040_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_mkFrameBackwardRuleCached___redArg___boxed(lean_object* v_fp_1089_, lean_object* v_info_1090_, lean_object* v_a_1091_, lean_object* v_a_1092_, lean_object* v_a_1093_, lean_object* v_a_1094_, lean_object* v_a_1095_, lean_object* v_a_1096_, lean_object* v_a_1097_, lean_object* v_a_1098_){
_start:
{
lean_object* v_res_1099_; 
v_res_1099_ = l_Lean_Elab_Tactic_VCGen_mkFrameBackwardRuleCached___redArg(v_fp_1089_, v_info_1090_, v_a_1091_, v_a_1092_, v_a_1093_, v_a_1094_, v_a_1095_, v_a_1096_, v_a_1097_);
lean_dec(v_a_1097_);
lean_dec_ref(v_a_1096_);
lean_dec(v_a_1095_);
lean_dec_ref(v_a_1094_);
lean_dec(v_a_1093_);
lean_dec_ref(v_a_1092_);
lean_dec(v_a_1091_);
return v_res_1099_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_mkFrameBackwardRuleCached(lean_object* v_fp_1100_, lean_object* v_info_1101_, lean_object* v_a_1102_, lean_object* v_a_1103_, lean_object* v_a_1104_, lean_object* v_a_1105_, lean_object* v_a_1106_, lean_object* v_a_1107_, lean_object* v_a_1108_, lean_object* v_a_1109_, lean_object* v_a_1110_, lean_object* v_a_1111_, lean_object* v_a_1112_){
_start:
{
lean_object* v___x_1114_; 
v___x_1114_ = l_Lean_Elab_Tactic_VCGen_mkFrameBackwardRuleCached___redArg(v_fp_1100_, v_info_1101_, v_a_1103_, v_a_1107_, v_a_1108_, v_a_1109_, v_a_1110_, v_a_1111_, v_a_1112_);
return v___x_1114_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_mkFrameBackwardRuleCached___boxed(lean_object* v_fp_1115_, lean_object* v_info_1116_, lean_object* v_a_1117_, lean_object* v_a_1118_, lean_object* v_a_1119_, lean_object* v_a_1120_, lean_object* v_a_1121_, lean_object* v_a_1122_, lean_object* v_a_1123_, lean_object* v_a_1124_, lean_object* v_a_1125_, lean_object* v_a_1126_, lean_object* v_a_1127_, lean_object* v_a_1128_){
_start:
{
lean_object* v_res_1129_; 
v_res_1129_ = l_Lean_Elab_Tactic_VCGen_mkFrameBackwardRuleCached(v_fp_1115_, v_info_1116_, v_a_1117_, v_a_1118_, v_a_1119_, v_a_1120_, v_a_1121_, v_a_1122_, v_a_1123_, v_a_1124_, v_a_1125_, v_a_1126_, v_a_1127_);
lean_dec(v_a_1127_);
lean_dec_ref(v_a_1126_);
lean_dec(v_a_1125_);
lean_dec_ref(v_a_1124_);
lean_dec(v_a_1123_);
lean_dec_ref(v_a_1122_);
lean_dec(v_a_1121_);
lean_dec_ref(v_a_1120_);
lean_dec(v_a_1119_);
lean_dec(v_a_1118_);
lean_dec_ref(v_a_1117_);
return v_res_1129_;
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
