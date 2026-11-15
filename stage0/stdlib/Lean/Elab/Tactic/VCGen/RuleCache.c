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
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
uint64_t lean_usize_to_uint64(size_t);
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_VCGen_WPApp_instWP(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Elab_Tactic_VCGen_mkBackwardRuleForSplit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_BackwardRule_shareCommon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppPrefix(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* l_Lean_Elab_Tactic_VCGen_mkLatticeOpRule(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_mkBackwardRuleFromDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleForRIntroCached_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleForRIntroCached_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleForRIntroCached_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleForRIntroCached_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleForRIntroCached_spec__1_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleForRIntroCached_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleForRIntroCached_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleForRIntroCached_spec__1_spec__3_spec__4_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleForRIntroCached_spec__1_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleForRIntroCached_spec__1_spec__3___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleForRIntroCached_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_mkBackwardRuleForRIntroCached___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_mkBackwardRuleForRIntroCached___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_mkBackwardRuleForRIntroCached(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_mkBackwardRuleForRIntroCached___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleForRIntroCached_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleForRIntroCached_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleForRIntroCached_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleForRIntroCached_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleForRIntroCached_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleForRIntroCached_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleForRIntroCached_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleForRIntroCached_spec__1_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleForRIntroCached_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleForRIntroCached_spec__1_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleForRIntroCached_spec__1_spec__3_spec__4_spec__5(lean_object*, lean_object*, lean_object*);
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
lean_object* v_a_422_; lean_object* v___x_424_; uint8_t v_isShared_425_; uint8_t v_isSharedCheck_482_; 
v_a_422_ = lean_ctor_get(v___x_421_, 0);
v_isSharedCheck_482_ = !lean_is_exclusive(v___x_421_);
if (v_isSharedCheck_482_ == 0)
{
v___x_424_ = v___x_421_;
v_isShared_425_ = v_isSharedCheck_482_;
goto v_resetjp_423_;
}
else
{
lean_inc(v_a_422_);
lean_dec(v___x_421_);
v___x_424_ = lean_box(0);
v_isShared_425_ = v_isSharedCheck_482_;
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
lean_object* v_val_431_; lean_object* v___x_433_; uint8_t v_isShared_434_; uint8_t v_isSharedCheck_477_; 
lean_del_object(v___x_424_);
v_val_431_ = lean_ctor_get(v_val_430_, 0);
v_isSharedCheck_477_ = !lean_is_exclusive(v_val_430_);
if (v_isSharedCheck_477_ == 0)
{
v___x_433_ = v_val_430_;
v_isShared_434_ = v_isSharedCheck_477_;
goto v_resetjp_432_;
}
else
{
lean_inc(v_val_431_);
lean_dec(v_val_430_);
v___x_433_ = lean_box(0);
v_isShared_434_ = v_isSharedCheck_477_;
goto v_resetjp_432_;
}
v_resetjp_432_:
{
lean_object* v___x_435_; 
v___x_435_ = l_Lean_Meta_Sym_BackwardRule_shareCommon(v_val_431_, v_a_400_, v_a_401_, v_a_402_, v_a_403_, v_a_404_, v_a_405_);
if (lean_obj_tag(v___x_435_) == 0)
{
lean_object* v_a_436_; lean_object* v___x_438_; uint8_t v_isShared_439_; uint8_t v_isSharedCheck_468_; 
v_a_436_ = lean_ctor_get(v___x_435_, 0);
v_isSharedCheck_468_ = !lean_is_exclusive(v___x_435_);
if (v_isSharedCheck_468_ == 0)
{
v___x_438_ = v___x_435_;
v_isShared_439_ = v_isSharedCheck_468_;
goto v_resetjp_437_;
}
else
{
lean_inc(v_a_436_);
lean_dec(v___x_435_);
v___x_438_ = lean_box(0);
v_isShared_439_ = v_isSharedCheck_468_;
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
lean_object* v_reuseFailAlloc_467_; 
v_reuseFailAlloc_467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_467_, 0, v_a_436_);
v___x_441_ = v_reuseFailAlloc_467_;
goto v_reusejp_440_;
}
v_reusejp_440_:
{
lean_object* v___x_442_; lean_object* v_specBackwardRuleCache_443_; lean_object* v_splitBackwardRuleCache_444_; lean_object* v_latticeBackwardRuleCache_445_; lean_object* v_frameBackwardRuleCache_446_; lean_object* v_rintroBackwardRuleCache_447_; lean_object* v_frameDB_448_; lean_object* v_invariants_449_; lean_object* v_vcs_450_; lean_object* v_simpState_451_; lean_object* v_fuel_452_; lean_object* v_inlineHandledInvariants_453_; lean_object* v_pendingJoinPoints_454_; lean_object* v___x_456_; uint8_t v_isShared_457_; uint8_t v_isSharedCheck_466_; 
v___x_442_ = lean_st_ref_take(v_a_396_);
v_specBackwardRuleCache_443_ = lean_ctor_get(v___x_442_, 0);
v_splitBackwardRuleCache_444_ = lean_ctor_get(v___x_442_, 1);
v_latticeBackwardRuleCache_445_ = lean_ctor_get(v___x_442_, 2);
v_frameBackwardRuleCache_446_ = lean_ctor_get(v___x_442_, 3);
v_rintroBackwardRuleCache_447_ = lean_ctor_get(v___x_442_, 4);
v_frameDB_448_ = lean_ctor_get(v___x_442_, 5);
v_invariants_449_ = lean_ctor_get(v___x_442_, 6);
v_vcs_450_ = lean_ctor_get(v___x_442_, 7);
v_simpState_451_ = lean_ctor_get(v___x_442_, 8);
v_fuel_452_ = lean_ctor_get(v___x_442_, 9);
v_inlineHandledInvariants_453_ = lean_ctor_get(v___x_442_, 10);
v_pendingJoinPoints_454_ = lean_ctor_get(v___x_442_, 11);
v_isSharedCheck_466_ = !lean_is_exclusive(v___x_442_);
if (v_isSharedCheck_466_ == 0)
{
v___x_456_ = v___x_442_;
v_isShared_457_ = v_isSharedCheck_466_;
goto v_resetjp_455_;
}
else
{
lean_inc(v_pendingJoinPoints_454_);
lean_inc(v_inlineHandledInvariants_453_);
lean_inc(v_fuel_452_);
lean_inc(v_simpState_451_);
lean_inc(v_vcs_450_);
lean_inc(v_invariants_449_);
lean_inc(v_frameDB_448_);
lean_inc(v_rintroBackwardRuleCache_447_);
lean_inc(v_frameBackwardRuleCache_446_);
lean_inc(v_latticeBackwardRuleCache_445_);
lean_inc(v_splitBackwardRuleCache_444_);
lean_inc(v_specBackwardRuleCache_443_);
lean_dec(v___x_442_);
v___x_456_ = lean_box(0);
v_isShared_457_ = v_isSharedCheck_466_;
goto v_resetjp_455_;
}
v_resetjp_455_:
{
lean_object* v___x_458_; lean_object* v___x_460_; 
v___x_458_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2___redArg(v_specBackwardRuleCache_443_, v_key_413_, v_a_436_);
if (v_isShared_457_ == 0)
{
lean_ctor_set(v___x_456_, 0, v___x_458_);
v___x_460_ = v___x_456_;
goto v_reusejp_459_;
}
else
{
lean_object* v_reuseFailAlloc_465_; 
v_reuseFailAlloc_465_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_465_, 0, v___x_458_);
lean_ctor_set(v_reuseFailAlloc_465_, 1, v_splitBackwardRuleCache_444_);
lean_ctor_set(v_reuseFailAlloc_465_, 2, v_latticeBackwardRuleCache_445_);
lean_ctor_set(v_reuseFailAlloc_465_, 3, v_frameBackwardRuleCache_446_);
lean_ctor_set(v_reuseFailAlloc_465_, 4, v_rintroBackwardRuleCache_447_);
lean_ctor_set(v_reuseFailAlloc_465_, 5, v_frameDB_448_);
lean_ctor_set(v_reuseFailAlloc_465_, 6, v_invariants_449_);
lean_ctor_set(v_reuseFailAlloc_465_, 7, v_vcs_450_);
lean_ctor_set(v_reuseFailAlloc_465_, 8, v_simpState_451_);
lean_ctor_set(v_reuseFailAlloc_465_, 9, v_fuel_452_);
lean_ctor_set(v_reuseFailAlloc_465_, 10, v_inlineHandledInvariants_453_);
lean_ctor_set(v_reuseFailAlloc_465_, 11, v_pendingJoinPoints_454_);
v___x_460_ = v_reuseFailAlloc_465_;
goto v_reusejp_459_;
}
v_reusejp_459_:
{
lean_object* v___x_461_; lean_object* v___x_463_; 
v___x_461_ = lean_st_ref_put(v_a_396_, v___x_460_);
if (v_isShared_439_ == 0)
{
lean_ctor_set(v___x_438_, 0, v___x_441_);
v___x_463_ = v___x_438_;
goto v_reusejp_462_;
}
else
{
lean_object* v_reuseFailAlloc_464_; 
v_reuseFailAlloc_464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_464_, 0, v___x_441_);
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
lean_del_object(v___x_433_);
lean_dec_ref_known(v_key_413_, 2);
v_a_469_ = lean_ctor_get(v___x_435_, 0);
v_isSharedCheck_476_ = !lean_is_exclusive(v___x_435_);
if (v_isSharedCheck_476_ == 0)
{
v___x_471_ = v___x_435_;
v_isShared_472_ = v_isSharedCheck_476_;
goto v_resetjp_470_;
}
else
{
lean_inc(v_a_469_);
lean_dec(v___x_435_);
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
lean_dec(v_val_430_);
lean_dec_ref_known(v_key_413_, 2);
v___x_478_ = lean_box(0);
if (v_isShared_425_ == 0)
{
lean_ctor_set(v___x_424_, 0, v___x_478_);
v___x_480_ = v___x_424_;
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
lean_dec_ref_known(v_key_413_, 2);
v_a_483_ = lean_ctor_get(v___x_421_, 0);
v_isSharedCheck_490_ = !lean_is_exclusive(v___x_421_);
if (v_isSharedCheck_490_ == 0)
{
v___x_485_ = v___x_421_;
v_isShared_486_ = v_isSharedCheck_490_;
goto v_resetjp_484_;
}
else
{
lean_inc(v_a_483_);
lean_dec(v___x_421_);
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
lean_object* v___x_623_; 
v___x_623_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_mkBackwardRuleForSplitCached___redArg___closed__1));
v___y_573_ = v___x_623_;
goto v___jp_572_;
}
case 1:
{
lean_object* v___x_624_; 
v___x_624_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_mkBackwardRuleForSplitCached___redArg___closed__3));
v___y_573_ = v___x_624_;
goto v___jp_572_;
}
case 2:
{
lean_object* v___x_625_; 
v___x_625_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_mkBackwardRuleForSplitCached___redArg___closed__5));
v___y_573_ = v___x_625_;
goto v___jp_572_;
}
default: 
{
lean_object* v_matcherApp_626_; lean_object* v_matcherName_627_; 
v_matcherApp_626_ = lean_ctor_get(v_splitInfo_562_, 0);
v_matcherName_627_ = lean_ctor_get(v_matcherApp_626_, 1);
lean_inc(v_matcherName_627_);
v___y_573_ = v_matcherName_627_;
goto v___jp_572_;
}
}
v___jp_572_:
{
lean_object* v_excessArgs_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v_key_578_; lean_object* v___x_579_; lean_object* v_splitBackwardRuleCache_580_; lean_object* v___x_581_; 
v_excessArgs_574_ = lean_ctor_get(v_info_563_, 3);
v___x_575_ = l_Lean_Elab_Tactic_VCGen_WPApp_instWP(v_info_563_);
v___x_576_ = lean_array_get_size(v_excessArgs_574_);
v___x_577_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_577_, 0, v___x_575_);
lean_ctor_set(v___x_577_, 1, v___x_576_);
v_key_578_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_key_578_, 0, v___y_573_);
lean_ctor_set(v_key_578_, 1, v___x_577_);
v___x_579_ = lean_st_ref_get(v_a_564_);
v_splitBackwardRuleCache_580_ = lean_ctor_get(v___x_579_, 1);
lean_inc_ref(v_splitBackwardRuleCache_580_);
lean_dec(v___x_579_);
v___x_581_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg(v_splitBackwardRuleCache_580_, v_key_578_);
lean_dec_ref(v_splitBackwardRuleCache_580_);
if (lean_obj_tag(v___x_581_) == 1)
{
lean_object* v_val_582_; lean_object* v___x_584_; uint8_t v_isShared_585_; uint8_t v_isSharedCheck_589_; 
lean_dec_ref_known(v_key_578_, 2);
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
lean_object* v_a_593_; lean_object* v___x_595_; uint8_t v_isShared_596_; uint8_t v_isSharedCheck_622_; 
v_a_593_ = lean_ctor_get(v___x_592_, 0);
v_isSharedCheck_622_ = !lean_is_exclusive(v___x_592_);
if (v_isSharedCheck_622_ == 0)
{
v___x_595_ = v___x_592_;
v_isShared_596_ = v_isSharedCheck_622_;
goto v_resetjp_594_;
}
else
{
lean_inc(v_a_593_);
lean_dec(v___x_592_);
v___x_595_ = lean_box(0);
v_isShared_596_ = v_isSharedCheck_622_;
goto v_resetjp_594_;
}
v_resetjp_594_:
{
lean_object* v___x_597_; lean_object* v_specBackwardRuleCache_598_; lean_object* v_splitBackwardRuleCache_599_; lean_object* v_latticeBackwardRuleCache_600_; lean_object* v_frameBackwardRuleCache_601_; lean_object* v_rintroBackwardRuleCache_602_; lean_object* v_frameDB_603_; lean_object* v_invariants_604_; lean_object* v_vcs_605_; lean_object* v_simpState_606_; lean_object* v_fuel_607_; lean_object* v_inlineHandledInvariants_608_; lean_object* v_pendingJoinPoints_609_; lean_object* v___x_611_; uint8_t v_isShared_612_; uint8_t v_isSharedCheck_621_; 
v___x_597_ = lean_st_ref_take(v_a_564_);
v_specBackwardRuleCache_598_ = lean_ctor_get(v___x_597_, 0);
v_splitBackwardRuleCache_599_ = lean_ctor_get(v___x_597_, 1);
v_latticeBackwardRuleCache_600_ = lean_ctor_get(v___x_597_, 2);
v_frameBackwardRuleCache_601_ = lean_ctor_get(v___x_597_, 3);
v_rintroBackwardRuleCache_602_ = lean_ctor_get(v___x_597_, 4);
v_frameDB_603_ = lean_ctor_get(v___x_597_, 5);
v_invariants_604_ = lean_ctor_get(v___x_597_, 6);
v_vcs_605_ = lean_ctor_get(v___x_597_, 7);
v_simpState_606_ = lean_ctor_get(v___x_597_, 8);
v_fuel_607_ = lean_ctor_get(v___x_597_, 9);
v_inlineHandledInvariants_608_ = lean_ctor_get(v___x_597_, 10);
v_pendingJoinPoints_609_ = lean_ctor_get(v___x_597_, 11);
v_isSharedCheck_621_ = !lean_is_exclusive(v___x_597_);
if (v_isSharedCheck_621_ == 0)
{
v___x_611_ = v___x_597_;
v_isShared_612_ = v_isSharedCheck_621_;
goto v_resetjp_610_;
}
else
{
lean_inc(v_pendingJoinPoints_609_);
lean_inc(v_inlineHandledInvariants_608_);
lean_inc(v_fuel_607_);
lean_inc(v_simpState_606_);
lean_inc(v_vcs_605_);
lean_inc(v_invariants_604_);
lean_inc(v_frameDB_603_);
lean_inc(v_rintroBackwardRuleCache_602_);
lean_inc(v_frameBackwardRuleCache_601_);
lean_inc(v_latticeBackwardRuleCache_600_);
lean_inc(v_splitBackwardRuleCache_599_);
lean_inc(v_specBackwardRuleCache_598_);
lean_dec(v___x_597_);
v___x_611_ = lean_box(0);
v_isShared_612_ = v_isSharedCheck_621_;
goto v_resetjp_610_;
}
v_resetjp_610_:
{
lean_object* v___x_613_; lean_object* v___x_615_; 
lean_inc(v_a_593_);
v___x_613_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2___redArg(v_splitBackwardRuleCache_599_, v_key_578_, v_a_593_);
if (v_isShared_612_ == 0)
{
lean_ctor_set(v___x_611_, 1, v___x_613_);
v___x_615_ = v___x_611_;
goto v_reusejp_614_;
}
else
{
lean_object* v_reuseFailAlloc_620_; 
v_reuseFailAlloc_620_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_620_, 0, v_specBackwardRuleCache_598_);
lean_ctor_set(v_reuseFailAlloc_620_, 1, v___x_613_);
lean_ctor_set(v_reuseFailAlloc_620_, 2, v_latticeBackwardRuleCache_600_);
lean_ctor_set(v_reuseFailAlloc_620_, 3, v_frameBackwardRuleCache_601_);
lean_ctor_set(v_reuseFailAlloc_620_, 4, v_rintroBackwardRuleCache_602_);
lean_ctor_set(v_reuseFailAlloc_620_, 5, v_frameDB_603_);
lean_ctor_set(v_reuseFailAlloc_620_, 6, v_invariants_604_);
lean_ctor_set(v_reuseFailAlloc_620_, 7, v_vcs_605_);
lean_ctor_set(v_reuseFailAlloc_620_, 8, v_simpState_606_);
lean_ctor_set(v_reuseFailAlloc_620_, 9, v_fuel_607_);
lean_ctor_set(v_reuseFailAlloc_620_, 10, v_inlineHandledInvariants_608_);
lean_ctor_set(v_reuseFailAlloc_620_, 11, v_pendingJoinPoints_609_);
v___x_615_ = v_reuseFailAlloc_620_;
goto v_reusejp_614_;
}
v_reusejp_614_:
{
lean_object* v___x_616_; lean_object* v___x_618_; 
v___x_616_ = lean_st_ref_put(v_a_564_, v___x_615_);
if (v_isShared_596_ == 0)
{
v___x_618_ = v___x_595_;
goto v_reusejp_617_;
}
else
{
lean_object* v_reuseFailAlloc_619_; 
v_reuseFailAlloc_619_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_619_, 0, v_a_593_);
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
lean_dec_ref_known(v_key_578_, 2);
return v___x_592_;
}
}
else
{
lean_dec_ref_known(v_key_578_, 2);
return v___x_590_;
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
lean_object* v_a_899_; lean_object* v___x_901_; uint8_t v_isShared_902_; uint8_t v_isSharedCheck_928_; 
v_a_899_ = lean_ctor_get(v___x_898_, 0);
v_isSharedCheck_928_ = !lean_is_exclusive(v___x_898_);
if (v_isSharedCheck_928_ == 0)
{
v___x_901_ = v___x_898_;
v_isShared_902_ = v_isSharedCheck_928_;
goto v_resetjp_900_;
}
else
{
lean_inc(v_a_899_);
lean_dec(v___x_898_);
v___x_901_ = lean_box(0);
v_isShared_902_ = v_isSharedCheck_928_;
goto v_resetjp_900_;
}
v_resetjp_900_:
{
lean_object* v___x_903_; lean_object* v_specBackwardRuleCache_904_; lean_object* v_splitBackwardRuleCache_905_; lean_object* v_latticeBackwardRuleCache_906_; lean_object* v_frameBackwardRuleCache_907_; lean_object* v_rintroBackwardRuleCache_908_; lean_object* v_frameDB_909_; lean_object* v_invariants_910_; lean_object* v_vcs_911_; lean_object* v_simpState_912_; lean_object* v_fuel_913_; lean_object* v_inlineHandledInvariants_914_; lean_object* v_pendingJoinPoints_915_; lean_object* v___x_917_; uint8_t v_isShared_918_; uint8_t v_isSharedCheck_927_; 
v___x_903_ = lean_st_ref_take(v_a_873_);
v_specBackwardRuleCache_904_ = lean_ctor_get(v___x_903_, 0);
v_splitBackwardRuleCache_905_ = lean_ctor_get(v___x_903_, 1);
v_latticeBackwardRuleCache_906_ = lean_ctor_get(v___x_903_, 2);
v_frameBackwardRuleCache_907_ = lean_ctor_get(v___x_903_, 3);
v_rintroBackwardRuleCache_908_ = lean_ctor_get(v___x_903_, 4);
v_frameDB_909_ = lean_ctor_get(v___x_903_, 5);
v_invariants_910_ = lean_ctor_get(v___x_903_, 6);
v_vcs_911_ = lean_ctor_get(v___x_903_, 7);
v_simpState_912_ = lean_ctor_get(v___x_903_, 8);
v_fuel_913_ = lean_ctor_get(v___x_903_, 9);
v_inlineHandledInvariants_914_ = lean_ctor_get(v___x_903_, 10);
v_pendingJoinPoints_915_ = lean_ctor_get(v___x_903_, 11);
v_isSharedCheck_927_ = !lean_is_exclusive(v___x_903_);
if (v_isSharedCheck_927_ == 0)
{
v___x_917_ = v___x_903_;
v_isShared_918_ = v_isSharedCheck_927_;
goto v_resetjp_916_;
}
else
{
lean_inc(v_pendingJoinPoints_915_);
lean_inc(v_inlineHandledInvariants_914_);
lean_inc(v_fuel_913_);
lean_inc(v_simpState_912_);
lean_inc(v_vcs_911_);
lean_inc(v_invariants_910_);
lean_inc(v_frameDB_909_);
lean_inc(v_rintroBackwardRuleCache_908_);
lean_inc(v_frameBackwardRuleCache_907_);
lean_inc(v_latticeBackwardRuleCache_906_);
lean_inc(v_splitBackwardRuleCache_905_);
lean_inc(v_specBackwardRuleCache_904_);
lean_dec(v___x_903_);
v___x_917_ = lean_box(0);
v_isShared_918_ = v_isSharedCheck_927_;
goto v_resetjp_916_;
}
v_resetjp_916_:
{
lean_object* v___x_919_; lean_object* v___x_921_; 
lean_inc(v_a_899_);
v___x_919_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1___redArg(v_latticeBackwardRuleCache_906_, v_key_884_, v_a_899_);
if (v_isShared_918_ == 0)
{
lean_ctor_set(v___x_917_, 2, v___x_919_);
v___x_921_ = v___x_917_;
goto v_reusejp_920_;
}
else
{
lean_object* v_reuseFailAlloc_926_; 
v_reuseFailAlloc_926_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_926_, 0, v_specBackwardRuleCache_904_);
lean_ctor_set(v_reuseFailAlloc_926_, 1, v_splitBackwardRuleCache_905_);
lean_ctor_set(v_reuseFailAlloc_926_, 2, v___x_919_);
lean_ctor_set(v_reuseFailAlloc_926_, 3, v_frameBackwardRuleCache_907_);
lean_ctor_set(v_reuseFailAlloc_926_, 4, v_rintroBackwardRuleCache_908_);
lean_ctor_set(v_reuseFailAlloc_926_, 5, v_frameDB_909_);
lean_ctor_set(v_reuseFailAlloc_926_, 6, v_invariants_910_);
lean_ctor_set(v_reuseFailAlloc_926_, 7, v_vcs_911_);
lean_ctor_set(v_reuseFailAlloc_926_, 8, v_simpState_912_);
lean_ctor_set(v_reuseFailAlloc_926_, 9, v_fuel_913_);
lean_ctor_set(v_reuseFailAlloc_926_, 10, v_inlineHandledInvariants_914_);
lean_ctor_set(v_reuseFailAlloc_926_, 11, v_pendingJoinPoints_915_);
v___x_921_ = v_reuseFailAlloc_926_;
goto v_reusejp_920_;
}
v_reusejp_920_:
{
lean_object* v___x_922_; lean_object* v___x_924_; 
v___x_922_ = lean_st_ref_put(v_a_873_, v___x_921_);
if (v_isShared_902_ == 0)
{
v___x_924_ = v___x_901_;
goto v_reusejp_923_;
}
else
{
lean_object* v_reuseFailAlloc_925_; 
v_reuseFailAlloc_925_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_925_, 0, v_a_899_);
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
lean_object* v_excessArgs_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v_key_1030_; lean_object* v___x_1031_; lean_object* v_frameBackwardRuleCache_1032_; lean_object* v___x_1033_; 
v_excessArgs_1027_ = lean_ctor_get(v_info_1018_, 3);
v___x_1028_ = l_Lean_Elab_Tactic_VCGen_WPApp_instWP(v_info_1018_);
v___x_1029_ = lean_array_get_size(v_excessArgs_1027_);
v_key_1030_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_key_1030_, 0, v___x_1028_);
lean_ctor_set(v_key_1030_, 1, v___x_1029_);
v___x_1031_ = lean_st_ref_get(v_a_1019_);
v_frameBackwardRuleCache_1032_ = lean_ctor_get(v___x_1031_, 3);
lean_inc_ref(v_frameBackwardRuleCache_1032_);
lean_dec(v___x_1031_);
v___x_1033_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__0___redArg(v_frameBackwardRuleCache_1032_, v_key_1030_);
lean_dec_ref(v_frameBackwardRuleCache_1032_);
if (lean_obj_tag(v___x_1033_) == 1)
{
lean_object* v_val_1034_; lean_object* v___x_1036_; uint8_t v_isShared_1037_; uint8_t v_isSharedCheck_1041_; 
lean_dec_ref_known(v_key_1030_, 2);
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
lean_object* v_a_1043_; lean_object* v_rule_1044_; lean_object* v_splitVCIdx_1045_; lean_object* v_frameIdx_1046_; lean_object* v___x_1048_; uint8_t v_isShared_1049_; uint8_t v_isSharedCheck_1092_; 
v_a_1043_ = lean_ctor_get(v___x_1042_, 0);
lean_inc(v_a_1043_);
lean_dec_ref_known(v___x_1042_, 1);
v_rule_1044_ = lean_ctor_get(v_a_1043_, 0);
v_splitVCIdx_1045_ = lean_ctor_get(v_a_1043_, 1);
v_frameIdx_1046_ = lean_ctor_get(v_a_1043_, 2);
v_isSharedCheck_1092_ = !lean_is_exclusive(v_a_1043_);
if (v_isSharedCheck_1092_ == 0)
{
v___x_1048_ = v_a_1043_;
v_isShared_1049_ = v_isSharedCheck_1092_;
goto v_resetjp_1047_;
}
else
{
lean_inc(v_frameIdx_1046_);
lean_inc(v_splitVCIdx_1045_);
lean_inc(v_rule_1044_);
lean_dec(v_a_1043_);
v___x_1048_ = lean_box(0);
v_isShared_1049_ = v_isSharedCheck_1092_;
goto v_resetjp_1047_;
}
v_resetjp_1047_:
{
lean_object* v___x_1050_; 
v___x_1050_ = l_Lean_Meta_Sym_BackwardRule_shareCommon(v_rule_1044_, v_a_1020_, v_a_1021_, v_a_1022_, v_a_1023_, v_a_1024_, v_a_1025_);
if (lean_obj_tag(v___x_1050_) == 0)
{
lean_object* v_a_1051_; lean_object* v___x_1053_; uint8_t v_isShared_1054_; uint8_t v_isSharedCheck_1083_; 
v_a_1051_ = lean_ctor_get(v___x_1050_, 0);
v_isSharedCheck_1083_ = !lean_is_exclusive(v___x_1050_);
if (v_isSharedCheck_1083_ == 0)
{
v___x_1053_ = v___x_1050_;
v_isShared_1054_ = v_isSharedCheck_1083_;
goto v_resetjp_1052_;
}
else
{
lean_inc(v_a_1051_);
lean_dec(v___x_1050_);
v___x_1053_ = lean_box(0);
v_isShared_1054_ = v_isSharedCheck_1083_;
goto v_resetjp_1052_;
}
v_resetjp_1052_:
{
lean_object* v___x_1056_; 
if (v_isShared_1049_ == 0)
{
lean_ctor_set(v___x_1048_, 0, v_a_1051_);
v___x_1056_ = v___x_1048_;
goto v_reusejp_1055_;
}
else
{
lean_object* v_reuseFailAlloc_1082_; 
v_reuseFailAlloc_1082_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1082_, 0, v_a_1051_);
lean_ctor_set(v_reuseFailAlloc_1082_, 1, v_splitVCIdx_1045_);
lean_ctor_set(v_reuseFailAlloc_1082_, 2, v_frameIdx_1046_);
v___x_1056_ = v_reuseFailAlloc_1082_;
goto v_reusejp_1055_;
}
v_reusejp_1055_:
{
lean_object* v___x_1057_; lean_object* v_specBackwardRuleCache_1058_; lean_object* v_splitBackwardRuleCache_1059_; lean_object* v_latticeBackwardRuleCache_1060_; lean_object* v_frameBackwardRuleCache_1061_; lean_object* v_rintroBackwardRuleCache_1062_; lean_object* v_frameDB_1063_; lean_object* v_invariants_1064_; lean_object* v_vcs_1065_; lean_object* v_simpState_1066_; lean_object* v_fuel_1067_; lean_object* v_inlineHandledInvariants_1068_; lean_object* v_pendingJoinPoints_1069_; lean_object* v___x_1071_; uint8_t v_isShared_1072_; uint8_t v_isSharedCheck_1081_; 
v___x_1057_ = lean_st_ref_take(v_a_1019_);
v_specBackwardRuleCache_1058_ = lean_ctor_get(v___x_1057_, 0);
v_splitBackwardRuleCache_1059_ = lean_ctor_get(v___x_1057_, 1);
v_latticeBackwardRuleCache_1060_ = lean_ctor_get(v___x_1057_, 2);
v_frameBackwardRuleCache_1061_ = lean_ctor_get(v___x_1057_, 3);
v_rintroBackwardRuleCache_1062_ = lean_ctor_get(v___x_1057_, 4);
v_frameDB_1063_ = lean_ctor_get(v___x_1057_, 5);
v_invariants_1064_ = lean_ctor_get(v___x_1057_, 6);
v_vcs_1065_ = lean_ctor_get(v___x_1057_, 7);
v_simpState_1066_ = lean_ctor_get(v___x_1057_, 8);
v_fuel_1067_ = lean_ctor_get(v___x_1057_, 9);
v_inlineHandledInvariants_1068_ = lean_ctor_get(v___x_1057_, 10);
v_pendingJoinPoints_1069_ = lean_ctor_get(v___x_1057_, 11);
v_isSharedCheck_1081_ = !lean_is_exclusive(v___x_1057_);
if (v_isSharedCheck_1081_ == 0)
{
v___x_1071_ = v___x_1057_;
v_isShared_1072_ = v_isSharedCheck_1081_;
goto v_resetjp_1070_;
}
else
{
lean_inc(v_pendingJoinPoints_1069_);
lean_inc(v_inlineHandledInvariants_1068_);
lean_inc(v_fuel_1067_);
lean_inc(v_simpState_1066_);
lean_inc(v_vcs_1065_);
lean_inc(v_invariants_1064_);
lean_inc(v_frameDB_1063_);
lean_inc(v_rintroBackwardRuleCache_1062_);
lean_inc(v_frameBackwardRuleCache_1061_);
lean_inc(v_latticeBackwardRuleCache_1060_);
lean_inc(v_splitBackwardRuleCache_1059_);
lean_inc(v_specBackwardRuleCache_1058_);
lean_dec(v___x_1057_);
v___x_1071_ = lean_box(0);
v_isShared_1072_ = v_isSharedCheck_1081_;
goto v_resetjp_1070_;
}
v_resetjp_1070_:
{
lean_object* v___x_1073_; lean_object* v___x_1075_; 
lean_inc_ref(v___x_1056_);
v___x_1073_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1___redArg(v_frameBackwardRuleCache_1061_, v_key_1030_, v___x_1056_);
if (v_isShared_1072_ == 0)
{
lean_ctor_set(v___x_1071_, 3, v___x_1073_);
v___x_1075_ = v___x_1071_;
goto v_reusejp_1074_;
}
else
{
lean_object* v_reuseFailAlloc_1080_; 
v_reuseFailAlloc_1080_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_1080_, 0, v_specBackwardRuleCache_1058_);
lean_ctor_set(v_reuseFailAlloc_1080_, 1, v_splitBackwardRuleCache_1059_);
lean_ctor_set(v_reuseFailAlloc_1080_, 2, v_latticeBackwardRuleCache_1060_);
lean_ctor_set(v_reuseFailAlloc_1080_, 3, v___x_1073_);
lean_ctor_set(v_reuseFailAlloc_1080_, 4, v_rintroBackwardRuleCache_1062_);
lean_ctor_set(v_reuseFailAlloc_1080_, 5, v_frameDB_1063_);
lean_ctor_set(v_reuseFailAlloc_1080_, 6, v_invariants_1064_);
lean_ctor_set(v_reuseFailAlloc_1080_, 7, v_vcs_1065_);
lean_ctor_set(v_reuseFailAlloc_1080_, 8, v_simpState_1066_);
lean_ctor_set(v_reuseFailAlloc_1080_, 9, v_fuel_1067_);
lean_ctor_set(v_reuseFailAlloc_1080_, 10, v_inlineHandledInvariants_1068_);
lean_ctor_set(v_reuseFailAlloc_1080_, 11, v_pendingJoinPoints_1069_);
v___x_1075_ = v_reuseFailAlloc_1080_;
goto v_reusejp_1074_;
}
v_reusejp_1074_:
{
lean_object* v___x_1076_; lean_object* v___x_1078_; 
v___x_1076_ = lean_st_ref_put(v_a_1019_, v___x_1075_);
if (v_isShared_1054_ == 0)
{
lean_ctor_set(v___x_1053_, 0, v___x_1056_);
v___x_1078_ = v___x_1053_;
goto v_reusejp_1077_;
}
else
{
lean_object* v_reuseFailAlloc_1079_; 
v_reuseFailAlloc_1079_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1079_, 0, v___x_1056_);
v___x_1078_ = v_reuseFailAlloc_1079_;
goto v_reusejp_1077_;
}
v_reusejp_1077_:
{
return v___x_1078_;
}
}
}
}
}
}
else
{
lean_object* v_a_1084_; lean_object* v___x_1086_; uint8_t v_isShared_1087_; uint8_t v_isSharedCheck_1091_; 
lean_del_object(v___x_1048_);
lean_dec(v_frameIdx_1046_);
lean_dec(v_splitVCIdx_1045_);
lean_dec_ref_known(v_key_1030_, 2);
v_a_1084_ = lean_ctor_get(v___x_1050_, 0);
v_isSharedCheck_1091_ = !lean_is_exclusive(v___x_1050_);
if (v_isSharedCheck_1091_ == 0)
{
v___x_1086_ = v___x_1050_;
v_isShared_1087_ = v_isSharedCheck_1091_;
goto v_resetjp_1085_;
}
else
{
lean_inc(v_a_1084_);
lean_dec(v___x_1050_);
v___x_1086_ = lean_box(0);
v_isShared_1087_ = v_isSharedCheck_1091_;
goto v_resetjp_1085_;
}
v_resetjp_1085_:
{
lean_object* v___x_1089_; 
if (v_isShared_1087_ == 0)
{
v___x_1089_ = v___x_1086_;
goto v_reusejp_1088_;
}
else
{
lean_object* v_reuseFailAlloc_1090_; 
v_reuseFailAlloc_1090_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1090_, 0, v_a_1084_);
v___x_1089_ = v_reuseFailAlloc_1090_;
goto v_reusejp_1088_;
}
v_reusejp_1088_:
{
return v___x_1089_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_key_1030_, 2);
return v___x_1042_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_mkFrameBackwardRuleCached___redArg___boxed(lean_object* v_fp_1093_, lean_object* v_info_1094_, lean_object* v_a_1095_, lean_object* v_a_1096_, lean_object* v_a_1097_, lean_object* v_a_1098_, lean_object* v_a_1099_, lean_object* v_a_1100_, lean_object* v_a_1101_, lean_object* v_a_1102_){
_start:
{
lean_object* v_res_1103_; 
v_res_1103_ = l_Lean_Elab_Tactic_VCGen_mkFrameBackwardRuleCached___redArg(v_fp_1093_, v_info_1094_, v_a_1095_, v_a_1096_, v_a_1097_, v_a_1098_, v_a_1099_, v_a_1100_, v_a_1101_);
lean_dec(v_a_1101_);
lean_dec_ref(v_a_1100_);
lean_dec(v_a_1099_);
lean_dec_ref(v_a_1098_);
lean_dec(v_a_1097_);
lean_dec_ref(v_a_1096_);
lean_dec(v_a_1095_);
return v_res_1103_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_mkFrameBackwardRuleCached(lean_object* v_fp_1104_, lean_object* v_info_1105_, lean_object* v_a_1106_, lean_object* v_a_1107_, lean_object* v_a_1108_, lean_object* v_a_1109_, lean_object* v_a_1110_, lean_object* v_a_1111_, lean_object* v_a_1112_, lean_object* v_a_1113_, lean_object* v_a_1114_, lean_object* v_a_1115_, lean_object* v_a_1116_){
_start:
{
lean_object* v___x_1118_; 
v___x_1118_ = l_Lean_Elab_Tactic_VCGen_mkFrameBackwardRuleCached___redArg(v_fp_1104_, v_info_1105_, v_a_1107_, v_a_1111_, v_a_1112_, v_a_1113_, v_a_1114_, v_a_1115_, v_a_1116_);
return v___x_1118_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_mkFrameBackwardRuleCached___boxed(lean_object* v_fp_1119_, lean_object* v_info_1120_, lean_object* v_a_1121_, lean_object* v_a_1122_, lean_object* v_a_1123_, lean_object* v_a_1124_, lean_object* v_a_1125_, lean_object* v_a_1126_, lean_object* v_a_1127_, lean_object* v_a_1128_, lean_object* v_a_1129_, lean_object* v_a_1130_, lean_object* v_a_1131_, lean_object* v_a_1132_){
_start:
{
lean_object* v_res_1133_; 
v_res_1133_ = l_Lean_Elab_Tactic_VCGen_mkFrameBackwardRuleCached(v_fp_1119_, v_info_1120_, v_a_1121_, v_a_1122_, v_a_1123_, v_a_1124_, v_a_1125_, v_a_1126_, v_a_1127_, v_a_1128_, v_a_1129_, v_a_1130_, v_a_1131_);
lean_dec(v_a_1131_);
lean_dec_ref(v_a_1130_);
lean_dec(v_a_1129_);
lean_dec_ref(v_a_1128_);
lean_dec(v_a_1127_);
lean_dec_ref(v_a_1126_);
lean_dec(v_a_1125_);
lean_dec_ref(v_a_1124_);
lean_dec(v_a_1123_);
lean_dec(v_a_1122_);
lean_dec_ref(v_a_1121_);
return v_res_1133_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleForRIntroCached_spec__0_spec__0___redArg(lean_object* v_a_1134_, lean_object* v_x_1135_){
_start:
{
if (lean_obj_tag(v_x_1135_) == 0)
{
lean_object* v___x_1136_; 
v___x_1136_ = lean_box(0);
return v___x_1136_;
}
else
{
lean_object* v_key_1137_; lean_object* v_value_1138_; lean_object* v_tail_1139_; uint8_t v___x_1140_; 
v_key_1137_ = lean_ctor_get(v_x_1135_, 0);
v_value_1138_ = lean_ctor_get(v_x_1135_, 1);
v_tail_1139_ = lean_ctor_get(v_x_1135_, 2);
v___x_1140_ = lean_name_eq(v_key_1137_, v_a_1134_);
if (v___x_1140_ == 0)
{
v_x_1135_ = v_tail_1139_;
goto _start;
}
else
{
lean_object* v___x_1142_; 
lean_inc(v_value_1138_);
v___x_1142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1142_, 0, v_value_1138_);
return v___x_1142_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleForRIntroCached_spec__0_spec__0___redArg___boxed(lean_object* v_a_1143_, lean_object* v_x_1144_){
_start:
{
lean_object* v_res_1145_; 
v_res_1145_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleForRIntroCached_spec__0_spec__0___redArg(v_a_1143_, v_x_1144_);
lean_dec(v_x_1144_);
lean_dec(v_a_1143_);
return v_res_1145_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleForRIntroCached_spec__0___redArg(lean_object* v_m_1146_, lean_object* v_a_1147_){
_start:
{
lean_object* v_buckets_1148_; lean_object* v___x_1149_; uint64_t v___y_1151_; 
v_buckets_1148_ = lean_ctor_get(v_m_1146_, 1);
v___x_1149_ = lean_array_get_size(v_buckets_1148_);
if (lean_obj_tag(v_a_1147_) == 0)
{
uint64_t v___x_1165_; 
v___x_1165_ = 1723ULL;
v___y_1151_ = v___x_1165_;
goto v___jp_1150_;
}
else
{
uint64_t v_hash_1166_; 
v_hash_1166_ = lean_ctor_get_uint64(v_a_1147_, sizeof(void*)*2);
v___y_1151_ = v_hash_1166_;
goto v___jp_1150_;
}
v___jp_1150_:
{
uint64_t v___x_1152_; uint64_t v___x_1153_; uint64_t v_fold_1154_; uint64_t v___x_1155_; uint64_t v___x_1156_; uint64_t v___x_1157_; size_t v___x_1158_; size_t v___x_1159_; size_t v___x_1160_; size_t v___x_1161_; size_t v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; 
v___x_1152_ = 32ULL;
v___x_1153_ = lean_uint64_shift_right(v___y_1151_, v___x_1152_);
v_fold_1154_ = lean_uint64_xor(v___y_1151_, v___x_1153_);
v___x_1155_ = 16ULL;
v___x_1156_ = lean_uint64_shift_right(v_fold_1154_, v___x_1155_);
v___x_1157_ = lean_uint64_xor(v_fold_1154_, v___x_1156_);
v___x_1158_ = lean_uint64_to_usize(v___x_1157_);
v___x_1159_ = lean_usize_of_nat(v___x_1149_);
v___x_1160_ = ((size_t)1ULL);
v___x_1161_ = lean_usize_sub(v___x_1159_, v___x_1160_);
v___x_1162_ = lean_usize_land(v___x_1158_, v___x_1161_);
v___x_1163_ = lean_array_uget_borrowed(v_buckets_1148_, v___x_1162_);
v___x_1164_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleForRIntroCached_spec__0_spec__0___redArg(v_a_1147_, v___x_1163_);
return v___x_1164_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleForRIntroCached_spec__0___redArg___boxed(lean_object* v_m_1167_, lean_object* v_a_1168_){
_start:
{
lean_object* v_res_1169_; 
v_res_1169_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleForRIntroCached_spec__0___redArg(v_m_1167_, v_a_1168_);
lean_dec(v_a_1168_);
lean_dec_ref(v_m_1167_);
return v_res_1169_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleForRIntroCached_spec__1_spec__4___redArg(lean_object* v_a_1170_, lean_object* v_b_1171_, lean_object* v_x_1172_){
_start:
{
if (lean_obj_tag(v_x_1172_) == 0)
{
lean_dec(v_b_1171_);
lean_dec(v_a_1170_);
return v_x_1172_;
}
else
{
lean_object* v_key_1173_; lean_object* v_value_1174_; lean_object* v_tail_1175_; lean_object* v___x_1177_; uint8_t v_isShared_1178_; uint8_t v_isSharedCheck_1187_; 
v_key_1173_ = lean_ctor_get(v_x_1172_, 0);
v_value_1174_ = lean_ctor_get(v_x_1172_, 1);
v_tail_1175_ = lean_ctor_get(v_x_1172_, 2);
v_isSharedCheck_1187_ = !lean_is_exclusive(v_x_1172_);
if (v_isSharedCheck_1187_ == 0)
{
v___x_1177_ = v_x_1172_;
v_isShared_1178_ = v_isSharedCheck_1187_;
goto v_resetjp_1176_;
}
else
{
lean_inc(v_tail_1175_);
lean_inc(v_value_1174_);
lean_inc(v_key_1173_);
lean_dec(v_x_1172_);
v___x_1177_ = lean_box(0);
v_isShared_1178_ = v_isSharedCheck_1187_;
goto v_resetjp_1176_;
}
v_resetjp_1176_:
{
uint8_t v___x_1179_; 
v___x_1179_ = lean_name_eq(v_key_1173_, v_a_1170_);
if (v___x_1179_ == 0)
{
lean_object* v___x_1180_; lean_object* v___x_1182_; 
v___x_1180_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleForRIntroCached_spec__1_spec__4___redArg(v_a_1170_, v_b_1171_, v_tail_1175_);
if (v_isShared_1178_ == 0)
{
lean_ctor_set(v___x_1177_, 2, v___x_1180_);
v___x_1182_ = v___x_1177_;
goto v_reusejp_1181_;
}
else
{
lean_object* v_reuseFailAlloc_1183_; 
v_reuseFailAlloc_1183_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1183_, 0, v_key_1173_);
lean_ctor_set(v_reuseFailAlloc_1183_, 1, v_value_1174_);
lean_ctor_set(v_reuseFailAlloc_1183_, 2, v___x_1180_);
v___x_1182_ = v_reuseFailAlloc_1183_;
goto v_reusejp_1181_;
}
v_reusejp_1181_:
{
return v___x_1182_;
}
}
else
{
lean_object* v___x_1185_; 
lean_dec(v_value_1174_);
lean_dec(v_key_1173_);
if (v_isShared_1178_ == 0)
{
lean_ctor_set(v___x_1177_, 1, v_b_1171_);
lean_ctor_set(v___x_1177_, 0, v_a_1170_);
v___x_1185_ = v___x_1177_;
goto v_reusejp_1184_;
}
else
{
lean_object* v_reuseFailAlloc_1186_; 
v_reuseFailAlloc_1186_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1186_, 0, v_a_1170_);
lean_ctor_set(v_reuseFailAlloc_1186_, 1, v_b_1171_);
lean_ctor_set(v_reuseFailAlloc_1186_, 2, v_tail_1175_);
v___x_1185_ = v_reuseFailAlloc_1186_;
goto v_reusejp_1184_;
}
v_reusejp_1184_:
{
return v___x_1185_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleForRIntroCached_spec__1_spec__2___redArg(lean_object* v_a_1188_, lean_object* v_x_1189_){
_start:
{
if (lean_obj_tag(v_x_1189_) == 0)
{
uint8_t v___x_1190_; 
v___x_1190_ = 0;
return v___x_1190_;
}
else
{
lean_object* v_key_1191_; lean_object* v_tail_1192_; uint8_t v___x_1193_; 
v_key_1191_ = lean_ctor_get(v_x_1189_, 0);
v_tail_1192_ = lean_ctor_get(v_x_1189_, 2);
v___x_1193_ = lean_name_eq(v_key_1191_, v_a_1188_);
if (v___x_1193_ == 0)
{
v_x_1189_ = v_tail_1192_;
goto _start;
}
else
{
return v___x_1193_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleForRIntroCached_spec__1_spec__2___redArg___boxed(lean_object* v_a_1195_, lean_object* v_x_1196_){
_start:
{
uint8_t v_res_1197_; lean_object* v_r_1198_; 
v_res_1197_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleForRIntroCached_spec__1_spec__2___redArg(v_a_1195_, v_x_1196_);
lean_dec(v_x_1196_);
lean_dec(v_a_1195_);
v_r_1198_ = lean_box(v_res_1197_);
return v_r_1198_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleForRIntroCached_spec__1_spec__3_spec__4_spec__5___redArg(lean_object* v_x_1199_, lean_object* v_x_1200_){
_start:
{
if (lean_obj_tag(v_x_1200_) == 0)
{
return v_x_1199_;
}
else
{
lean_object* v_key_1201_; lean_object* v_value_1202_; lean_object* v_tail_1203_; lean_object* v___x_1205_; uint8_t v_isShared_1206_; uint8_t v_isSharedCheck_1229_; 
v_key_1201_ = lean_ctor_get(v_x_1200_, 0);
v_value_1202_ = lean_ctor_get(v_x_1200_, 1);
v_tail_1203_ = lean_ctor_get(v_x_1200_, 2);
v_isSharedCheck_1229_ = !lean_is_exclusive(v_x_1200_);
if (v_isSharedCheck_1229_ == 0)
{
v___x_1205_ = v_x_1200_;
v_isShared_1206_ = v_isSharedCheck_1229_;
goto v_resetjp_1204_;
}
else
{
lean_inc(v_tail_1203_);
lean_inc(v_value_1202_);
lean_inc(v_key_1201_);
lean_dec(v_x_1200_);
v___x_1205_ = lean_box(0);
v_isShared_1206_ = v_isSharedCheck_1229_;
goto v_resetjp_1204_;
}
v_resetjp_1204_:
{
lean_object* v___x_1207_; uint64_t v___y_1209_; 
v___x_1207_ = lean_array_get_size(v_x_1199_);
if (lean_obj_tag(v_key_1201_) == 0)
{
uint64_t v___x_1227_; 
v___x_1227_ = 1723ULL;
v___y_1209_ = v___x_1227_;
goto v___jp_1208_;
}
else
{
uint64_t v_hash_1228_; 
v_hash_1228_ = lean_ctor_get_uint64(v_key_1201_, sizeof(void*)*2);
v___y_1209_ = v_hash_1228_;
goto v___jp_1208_;
}
v___jp_1208_:
{
uint64_t v___x_1210_; uint64_t v___x_1211_; uint64_t v_fold_1212_; uint64_t v___x_1213_; uint64_t v___x_1214_; uint64_t v___x_1215_; size_t v___x_1216_; size_t v___x_1217_; size_t v___x_1218_; size_t v___x_1219_; size_t v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1223_; 
v___x_1210_ = 32ULL;
v___x_1211_ = lean_uint64_shift_right(v___y_1209_, v___x_1210_);
v_fold_1212_ = lean_uint64_xor(v___y_1209_, v___x_1211_);
v___x_1213_ = 16ULL;
v___x_1214_ = lean_uint64_shift_right(v_fold_1212_, v___x_1213_);
v___x_1215_ = lean_uint64_xor(v_fold_1212_, v___x_1214_);
v___x_1216_ = lean_uint64_to_usize(v___x_1215_);
v___x_1217_ = lean_usize_of_nat(v___x_1207_);
v___x_1218_ = ((size_t)1ULL);
v___x_1219_ = lean_usize_sub(v___x_1217_, v___x_1218_);
v___x_1220_ = lean_usize_land(v___x_1216_, v___x_1219_);
v___x_1221_ = lean_array_uget_borrowed(v_x_1199_, v___x_1220_);
lean_inc(v___x_1221_);
if (v_isShared_1206_ == 0)
{
lean_ctor_set(v___x_1205_, 2, v___x_1221_);
v___x_1223_ = v___x_1205_;
goto v_reusejp_1222_;
}
else
{
lean_object* v_reuseFailAlloc_1226_; 
v_reuseFailAlloc_1226_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1226_, 0, v_key_1201_);
lean_ctor_set(v_reuseFailAlloc_1226_, 1, v_value_1202_);
lean_ctor_set(v_reuseFailAlloc_1226_, 2, v___x_1221_);
v___x_1223_ = v_reuseFailAlloc_1226_;
goto v_reusejp_1222_;
}
v_reusejp_1222_:
{
lean_object* v___x_1224_; 
v___x_1224_ = lean_array_uset(v_x_1199_, v___x_1220_, v___x_1223_);
v_x_1199_ = v___x_1224_;
v_x_1200_ = v_tail_1203_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleForRIntroCached_spec__1_spec__3_spec__4___redArg(lean_object* v_i_1230_, lean_object* v_source_1231_, lean_object* v_target_1232_){
_start:
{
lean_object* v___x_1233_; uint8_t v___x_1234_; 
v___x_1233_ = lean_array_get_size(v_source_1231_);
v___x_1234_ = lean_nat_dec_lt(v_i_1230_, v___x_1233_);
if (v___x_1234_ == 0)
{
lean_dec_ref(v_source_1231_);
lean_dec(v_i_1230_);
return v_target_1232_;
}
else
{
lean_object* v_es_1235_; lean_object* v___x_1236_; lean_object* v_source_1237_; lean_object* v_target_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; 
v_es_1235_ = lean_array_fget(v_source_1231_, v_i_1230_);
v___x_1236_ = lean_box(0);
v_source_1237_ = lean_array_fset(v_source_1231_, v_i_1230_, v___x_1236_);
v_target_1238_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleForRIntroCached_spec__1_spec__3_spec__4_spec__5___redArg(v_target_1232_, v_es_1235_);
v___x_1239_ = lean_unsigned_to_nat(1u);
v___x_1240_ = lean_nat_add(v_i_1230_, v___x_1239_);
lean_dec(v_i_1230_);
v_i_1230_ = v___x_1240_;
v_source_1231_ = v_source_1237_;
v_target_1232_ = v_target_1238_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleForRIntroCached_spec__1_spec__3___redArg(lean_object* v_data_1242_){
_start:
{
lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v_nbuckets_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; 
v___x_1243_ = lean_array_get_size(v_data_1242_);
v___x_1244_ = lean_unsigned_to_nat(2u);
v_nbuckets_1245_ = lean_nat_mul(v___x_1243_, v___x_1244_);
v___x_1246_ = lean_unsigned_to_nat(0u);
v___x_1247_ = lean_box(0);
v___x_1248_ = lean_mk_array(v_nbuckets_1245_, v___x_1247_);
v___x_1249_ = lean_array_propagate_mark(v_data_1242_, v___x_1248_);
v___x_1250_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleForRIntroCached_spec__1_spec__3_spec__4___redArg(v___x_1246_, v_data_1242_, v___x_1249_);
return v___x_1250_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleForRIntroCached_spec__1___redArg(lean_object* v_m_1251_, lean_object* v_a_1252_, lean_object* v_b_1253_){
_start:
{
lean_object* v_size_1254_; lean_object* v_buckets_1255_; lean_object* v___x_1257_; uint8_t v_isShared_1258_; uint8_t v_isSharedCheck_1301_; 
v_size_1254_ = lean_ctor_get(v_m_1251_, 0);
v_buckets_1255_ = lean_ctor_get(v_m_1251_, 1);
v_isSharedCheck_1301_ = !lean_is_exclusive(v_m_1251_);
if (v_isSharedCheck_1301_ == 0)
{
v___x_1257_ = v_m_1251_;
v_isShared_1258_ = v_isSharedCheck_1301_;
goto v_resetjp_1256_;
}
else
{
lean_inc(v_buckets_1255_);
lean_inc(v_size_1254_);
lean_dec(v_m_1251_);
v___x_1257_ = lean_box(0);
v_isShared_1258_ = v_isSharedCheck_1301_;
goto v_resetjp_1256_;
}
v_resetjp_1256_:
{
lean_object* v___x_1259_; uint64_t v___y_1261_; 
v___x_1259_ = lean_array_get_size(v_buckets_1255_);
if (lean_obj_tag(v_a_1252_) == 0)
{
uint64_t v___x_1299_; 
v___x_1299_ = 1723ULL;
v___y_1261_ = v___x_1299_;
goto v___jp_1260_;
}
else
{
uint64_t v_hash_1300_; 
v_hash_1300_ = lean_ctor_get_uint64(v_a_1252_, sizeof(void*)*2);
v___y_1261_ = v_hash_1300_;
goto v___jp_1260_;
}
v___jp_1260_:
{
uint64_t v___x_1262_; uint64_t v___x_1263_; uint64_t v_fold_1264_; uint64_t v___x_1265_; uint64_t v___x_1266_; uint64_t v___x_1267_; size_t v___x_1268_; size_t v___x_1269_; size_t v___x_1270_; size_t v___x_1271_; size_t v___x_1272_; lean_object* v_bkt_1273_; uint8_t v___x_1274_; 
v___x_1262_ = 32ULL;
v___x_1263_ = lean_uint64_shift_right(v___y_1261_, v___x_1262_);
v_fold_1264_ = lean_uint64_xor(v___y_1261_, v___x_1263_);
v___x_1265_ = 16ULL;
v___x_1266_ = lean_uint64_shift_right(v_fold_1264_, v___x_1265_);
v___x_1267_ = lean_uint64_xor(v_fold_1264_, v___x_1266_);
v___x_1268_ = lean_uint64_to_usize(v___x_1267_);
v___x_1269_ = lean_usize_of_nat(v___x_1259_);
v___x_1270_ = ((size_t)1ULL);
v___x_1271_ = lean_usize_sub(v___x_1269_, v___x_1270_);
v___x_1272_ = lean_usize_land(v___x_1268_, v___x_1271_);
v_bkt_1273_ = lean_array_uget_borrowed(v_buckets_1255_, v___x_1272_);
v___x_1274_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleForRIntroCached_spec__1_spec__2___redArg(v_a_1252_, v_bkt_1273_);
if (v___x_1274_ == 0)
{
lean_object* v___x_1275_; lean_object* v_size_x27_1276_; lean_object* v___x_1277_; lean_object* v_buckets_x27_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; uint8_t v___x_1284_; 
v___x_1275_ = lean_unsigned_to_nat(1u);
v_size_x27_1276_ = lean_nat_add(v_size_1254_, v___x_1275_);
lean_dec(v_size_1254_);
lean_inc(v_bkt_1273_);
v___x_1277_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1277_, 0, v_a_1252_);
lean_ctor_set(v___x_1277_, 1, v_b_1253_);
lean_ctor_set(v___x_1277_, 2, v_bkt_1273_);
v_buckets_x27_1278_ = lean_array_uset(v_buckets_1255_, v___x_1272_, v___x_1277_);
v___x_1279_ = lean_unsigned_to_nat(4u);
v___x_1280_ = lean_nat_mul(v_size_x27_1276_, v___x_1279_);
v___x_1281_ = lean_unsigned_to_nat(3u);
v___x_1282_ = lean_nat_div(v___x_1280_, v___x_1281_);
lean_dec(v___x_1280_);
v___x_1283_ = lean_array_get_size(v_buckets_x27_1278_);
v___x_1284_ = lean_nat_dec_le(v___x_1282_, v___x_1283_);
lean_dec(v___x_1282_);
if (v___x_1284_ == 0)
{
lean_object* v_val_1285_; lean_object* v___x_1287_; 
v_val_1285_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleForRIntroCached_spec__1_spec__3___redArg(v_buckets_x27_1278_);
if (v_isShared_1258_ == 0)
{
lean_ctor_set(v___x_1257_, 1, v_val_1285_);
lean_ctor_set(v___x_1257_, 0, v_size_x27_1276_);
v___x_1287_ = v___x_1257_;
goto v_reusejp_1286_;
}
else
{
lean_object* v_reuseFailAlloc_1288_; 
v_reuseFailAlloc_1288_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1288_, 0, v_size_x27_1276_);
lean_ctor_set(v_reuseFailAlloc_1288_, 1, v_val_1285_);
v___x_1287_ = v_reuseFailAlloc_1288_;
goto v_reusejp_1286_;
}
v_reusejp_1286_:
{
return v___x_1287_;
}
}
else
{
lean_object* v___x_1290_; 
if (v_isShared_1258_ == 0)
{
lean_ctor_set(v___x_1257_, 1, v_buckets_x27_1278_);
lean_ctor_set(v___x_1257_, 0, v_size_x27_1276_);
v___x_1290_ = v___x_1257_;
goto v_reusejp_1289_;
}
else
{
lean_object* v_reuseFailAlloc_1291_; 
v_reuseFailAlloc_1291_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1291_, 0, v_size_x27_1276_);
lean_ctor_set(v_reuseFailAlloc_1291_, 1, v_buckets_x27_1278_);
v___x_1290_ = v_reuseFailAlloc_1291_;
goto v_reusejp_1289_;
}
v_reusejp_1289_:
{
return v___x_1290_;
}
}
}
else
{
lean_object* v___x_1292_; lean_object* v_buckets_x27_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1297_; 
lean_inc(v_bkt_1273_);
v___x_1292_ = lean_box(0);
v_buckets_x27_1293_ = lean_array_uset(v_buckets_1255_, v___x_1272_, v___x_1292_);
v___x_1294_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleForRIntroCached_spec__1_spec__4___redArg(v_a_1252_, v_b_1253_, v_bkt_1273_);
v___x_1295_ = lean_array_uset(v_buckets_x27_1293_, v___x_1272_, v___x_1294_);
if (v_isShared_1258_ == 0)
{
lean_ctor_set(v___x_1257_, 1, v___x_1295_);
v___x_1297_ = v___x_1257_;
goto v_reusejp_1296_;
}
else
{
lean_object* v_reuseFailAlloc_1298_; 
v_reuseFailAlloc_1298_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1298_, 0, v_size_1254_);
lean_ctor_set(v_reuseFailAlloc_1298_, 1, v___x_1295_);
v___x_1297_ = v_reuseFailAlloc_1298_;
goto v_reusejp_1296_;
}
v_reusejp_1296_:
{
return v___x_1297_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_mkBackwardRuleForRIntroCached___redArg(lean_object* v_e_1302_, lean_object* v_a_1303_, lean_object* v_a_1304_, lean_object* v_a_1305_, lean_object* v_a_1306_, lean_object* v_a_1307_, lean_object* v_a_1308_, lean_object* v_a_1309_){
_start:
{
lean_object* v___x_1311_; lean_object* v_rintroBackwardRuleCache_1312_; lean_object* v_declName_1313_; lean_object* v_numPremises_1314_; lean_object* v___x_1315_; 
v___x_1311_ = lean_st_ref_get(v_a_1303_);
v_rintroBackwardRuleCache_1312_ = lean_ctor_get(v___x_1311_, 4);
lean_inc_ref(v_rintroBackwardRuleCache_1312_);
lean_dec(v___x_1311_);
v_declName_1313_ = lean_ctor_get(v_e_1302_, 0);
lean_inc(v_declName_1313_);
v_numPremises_1314_ = lean_ctor_get(v_e_1302_, 1);
lean_inc(v_numPremises_1314_);
lean_dec_ref(v_e_1302_);
v___x_1315_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleForRIntroCached_spec__0___redArg(v_rintroBackwardRuleCache_1312_, v_declName_1313_);
lean_dec_ref(v_rintroBackwardRuleCache_1312_);
if (lean_obj_tag(v___x_1315_) == 1)
{
lean_object* v_val_1316_; lean_object* v___x_1318_; uint8_t v_isShared_1319_; uint8_t v_isSharedCheck_1323_; 
lean_dec(v_numPremises_1314_);
lean_dec(v_declName_1313_);
v_val_1316_ = lean_ctor_get(v___x_1315_, 0);
v_isSharedCheck_1323_ = !lean_is_exclusive(v___x_1315_);
if (v_isSharedCheck_1323_ == 0)
{
v___x_1318_ = v___x_1315_;
v_isShared_1319_ = v_isSharedCheck_1323_;
goto v_resetjp_1317_;
}
else
{
lean_inc(v_val_1316_);
lean_dec(v___x_1315_);
v___x_1318_ = lean_box(0);
v_isShared_1319_ = v_isSharedCheck_1323_;
goto v_resetjp_1317_;
}
v_resetjp_1317_:
{
lean_object* v___x_1321_; 
if (v_isShared_1319_ == 0)
{
lean_ctor_set_tag(v___x_1318_, 0);
v___x_1321_ = v___x_1318_;
goto v_reusejp_1320_;
}
else
{
lean_object* v_reuseFailAlloc_1322_; 
v_reuseFailAlloc_1322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1322_, 0, v_val_1316_);
v___x_1321_ = v_reuseFailAlloc_1322_;
goto v_reusejp_1320_;
}
v_reusejp_1320_:
{
return v___x_1321_;
}
}
}
else
{
lean_object* v___x_1324_; lean_object* v___x_1325_; 
lean_dec(v___x_1315_);
v___x_1324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1324_, 0, v_numPremises_1314_);
lean_inc(v_declName_1313_);
v___x_1325_ = l_Lean_Meta_Sym_mkBackwardRuleFromDecl(v_declName_1313_, v___x_1324_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
if (lean_obj_tag(v___x_1325_) == 0)
{
lean_object* v_a_1326_; lean_object* v___x_1327_; 
v_a_1326_ = lean_ctor_get(v___x_1325_, 0);
lean_inc(v_a_1326_);
lean_dec_ref_known(v___x_1325_, 1);
v___x_1327_ = l_Lean_Meta_Sym_BackwardRule_shareCommon(v_a_1326_, v_a_1304_, v_a_1305_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
if (lean_obj_tag(v___x_1327_) == 0)
{
lean_object* v_a_1328_; lean_object* v___x_1330_; uint8_t v_isShared_1331_; uint8_t v_isSharedCheck_1357_; 
v_a_1328_ = lean_ctor_get(v___x_1327_, 0);
v_isSharedCheck_1357_ = !lean_is_exclusive(v___x_1327_);
if (v_isSharedCheck_1357_ == 0)
{
v___x_1330_ = v___x_1327_;
v_isShared_1331_ = v_isSharedCheck_1357_;
goto v_resetjp_1329_;
}
else
{
lean_inc(v_a_1328_);
lean_dec(v___x_1327_);
v___x_1330_ = lean_box(0);
v_isShared_1331_ = v_isSharedCheck_1357_;
goto v_resetjp_1329_;
}
v_resetjp_1329_:
{
lean_object* v___x_1332_; lean_object* v_specBackwardRuleCache_1333_; lean_object* v_splitBackwardRuleCache_1334_; lean_object* v_latticeBackwardRuleCache_1335_; lean_object* v_frameBackwardRuleCache_1336_; lean_object* v_rintroBackwardRuleCache_1337_; lean_object* v_frameDB_1338_; lean_object* v_invariants_1339_; lean_object* v_vcs_1340_; lean_object* v_simpState_1341_; lean_object* v_fuel_1342_; lean_object* v_inlineHandledInvariants_1343_; lean_object* v_pendingJoinPoints_1344_; lean_object* v___x_1346_; uint8_t v_isShared_1347_; uint8_t v_isSharedCheck_1356_; 
v___x_1332_ = lean_st_ref_take(v_a_1303_);
v_specBackwardRuleCache_1333_ = lean_ctor_get(v___x_1332_, 0);
v_splitBackwardRuleCache_1334_ = lean_ctor_get(v___x_1332_, 1);
v_latticeBackwardRuleCache_1335_ = lean_ctor_get(v___x_1332_, 2);
v_frameBackwardRuleCache_1336_ = lean_ctor_get(v___x_1332_, 3);
v_rintroBackwardRuleCache_1337_ = lean_ctor_get(v___x_1332_, 4);
v_frameDB_1338_ = lean_ctor_get(v___x_1332_, 5);
v_invariants_1339_ = lean_ctor_get(v___x_1332_, 6);
v_vcs_1340_ = lean_ctor_get(v___x_1332_, 7);
v_simpState_1341_ = lean_ctor_get(v___x_1332_, 8);
v_fuel_1342_ = lean_ctor_get(v___x_1332_, 9);
v_inlineHandledInvariants_1343_ = lean_ctor_get(v___x_1332_, 10);
v_pendingJoinPoints_1344_ = lean_ctor_get(v___x_1332_, 11);
v_isSharedCheck_1356_ = !lean_is_exclusive(v___x_1332_);
if (v_isSharedCheck_1356_ == 0)
{
v___x_1346_ = v___x_1332_;
v_isShared_1347_ = v_isSharedCheck_1356_;
goto v_resetjp_1345_;
}
else
{
lean_inc(v_pendingJoinPoints_1344_);
lean_inc(v_inlineHandledInvariants_1343_);
lean_inc(v_fuel_1342_);
lean_inc(v_simpState_1341_);
lean_inc(v_vcs_1340_);
lean_inc(v_invariants_1339_);
lean_inc(v_frameDB_1338_);
lean_inc(v_rintroBackwardRuleCache_1337_);
lean_inc(v_frameBackwardRuleCache_1336_);
lean_inc(v_latticeBackwardRuleCache_1335_);
lean_inc(v_splitBackwardRuleCache_1334_);
lean_inc(v_specBackwardRuleCache_1333_);
lean_dec(v___x_1332_);
v___x_1346_ = lean_box(0);
v_isShared_1347_ = v_isSharedCheck_1356_;
goto v_resetjp_1345_;
}
v_resetjp_1345_:
{
lean_object* v___x_1348_; lean_object* v___x_1350_; 
lean_inc(v_a_1328_);
v___x_1348_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleForRIntroCached_spec__1___redArg(v_rintroBackwardRuleCache_1337_, v_declName_1313_, v_a_1328_);
if (v_isShared_1347_ == 0)
{
lean_ctor_set(v___x_1346_, 4, v___x_1348_);
v___x_1350_ = v___x_1346_;
goto v_reusejp_1349_;
}
else
{
lean_object* v_reuseFailAlloc_1355_; 
v_reuseFailAlloc_1355_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_1355_, 0, v_specBackwardRuleCache_1333_);
lean_ctor_set(v_reuseFailAlloc_1355_, 1, v_splitBackwardRuleCache_1334_);
lean_ctor_set(v_reuseFailAlloc_1355_, 2, v_latticeBackwardRuleCache_1335_);
lean_ctor_set(v_reuseFailAlloc_1355_, 3, v_frameBackwardRuleCache_1336_);
lean_ctor_set(v_reuseFailAlloc_1355_, 4, v___x_1348_);
lean_ctor_set(v_reuseFailAlloc_1355_, 5, v_frameDB_1338_);
lean_ctor_set(v_reuseFailAlloc_1355_, 6, v_invariants_1339_);
lean_ctor_set(v_reuseFailAlloc_1355_, 7, v_vcs_1340_);
lean_ctor_set(v_reuseFailAlloc_1355_, 8, v_simpState_1341_);
lean_ctor_set(v_reuseFailAlloc_1355_, 9, v_fuel_1342_);
lean_ctor_set(v_reuseFailAlloc_1355_, 10, v_inlineHandledInvariants_1343_);
lean_ctor_set(v_reuseFailAlloc_1355_, 11, v_pendingJoinPoints_1344_);
v___x_1350_ = v_reuseFailAlloc_1355_;
goto v_reusejp_1349_;
}
v_reusejp_1349_:
{
lean_object* v___x_1351_; lean_object* v___x_1353_; 
v___x_1351_ = lean_st_ref_put(v_a_1303_, v___x_1350_);
if (v_isShared_1331_ == 0)
{
v___x_1353_ = v___x_1330_;
goto v_reusejp_1352_;
}
else
{
lean_object* v_reuseFailAlloc_1354_; 
v_reuseFailAlloc_1354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1354_, 0, v_a_1328_);
v___x_1353_ = v_reuseFailAlloc_1354_;
goto v_reusejp_1352_;
}
v_reusejp_1352_:
{
return v___x_1353_;
}
}
}
}
}
else
{
lean_dec(v_declName_1313_);
return v___x_1327_;
}
}
else
{
lean_dec(v_declName_1313_);
return v___x_1325_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_mkBackwardRuleForRIntroCached___redArg___boxed(lean_object* v_e_1358_, lean_object* v_a_1359_, lean_object* v_a_1360_, lean_object* v_a_1361_, lean_object* v_a_1362_, lean_object* v_a_1363_, lean_object* v_a_1364_, lean_object* v_a_1365_, lean_object* v_a_1366_){
_start:
{
lean_object* v_res_1367_; 
v_res_1367_ = l_Lean_Elab_Tactic_VCGen_mkBackwardRuleForRIntroCached___redArg(v_e_1358_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_, v_a_1363_, v_a_1364_, v_a_1365_);
lean_dec(v_a_1365_);
lean_dec_ref(v_a_1364_);
lean_dec(v_a_1363_);
lean_dec_ref(v_a_1362_);
lean_dec(v_a_1361_);
lean_dec_ref(v_a_1360_);
lean_dec(v_a_1359_);
return v_res_1367_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_mkBackwardRuleForRIntroCached(lean_object* v_e_1368_, lean_object* v_a_1369_, lean_object* v_a_1370_, lean_object* v_a_1371_, lean_object* v_a_1372_, lean_object* v_a_1373_, lean_object* v_a_1374_, lean_object* v_a_1375_, lean_object* v_a_1376_, lean_object* v_a_1377_, lean_object* v_a_1378_, lean_object* v_a_1379_){
_start:
{
lean_object* v___x_1381_; 
v___x_1381_ = l_Lean_Elab_Tactic_VCGen_mkBackwardRuleForRIntroCached___redArg(v_e_1368_, v_a_1370_, v_a_1374_, v_a_1375_, v_a_1376_, v_a_1377_, v_a_1378_, v_a_1379_);
return v___x_1381_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_mkBackwardRuleForRIntroCached___boxed(lean_object* v_e_1382_, lean_object* v_a_1383_, lean_object* v_a_1384_, lean_object* v_a_1385_, lean_object* v_a_1386_, lean_object* v_a_1387_, lean_object* v_a_1388_, lean_object* v_a_1389_, lean_object* v_a_1390_, lean_object* v_a_1391_, lean_object* v_a_1392_, lean_object* v_a_1393_, lean_object* v_a_1394_){
_start:
{
lean_object* v_res_1395_; 
v_res_1395_ = l_Lean_Elab_Tactic_VCGen_mkBackwardRuleForRIntroCached(v_e_1382_, v_a_1383_, v_a_1384_, v_a_1385_, v_a_1386_, v_a_1387_, v_a_1388_, v_a_1389_, v_a_1390_, v_a_1391_, v_a_1392_, v_a_1393_);
lean_dec(v_a_1393_);
lean_dec_ref(v_a_1392_);
lean_dec(v_a_1391_);
lean_dec_ref(v_a_1390_);
lean_dec(v_a_1389_);
lean_dec_ref(v_a_1388_);
lean_dec(v_a_1387_);
lean_dec_ref(v_a_1386_);
lean_dec(v_a_1385_);
lean_dec(v_a_1384_);
lean_dec_ref(v_a_1383_);
return v_res_1395_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleForRIntroCached_spec__0(lean_object* v_00_u03b2_1396_, lean_object* v_m_1397_, lean_object* v_a_1398_){
_start:
{
lean_object* v___x_1399_; 
v___x_1399_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleForRIntroCached_spec__0___redArg(v_m_1397_, v_a_1398_);
return v___x_1399_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleForRIntroCached_spec__0___boxed(lean_object* v_00_u03b2_1400_, lean_object* v_m_1401_, lean_object* v_a_1402_){
_start:
{
lean_object* v_res_1403_; 
v_res_1403_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleForRIntroCached_spec__0(v_00_u03b2_1400_, v_m_1401_, v_a_1402_);
lean_dec(v_a_1402_);
lean_dec_ref(v_m_1401_);
return v_res_1403_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleForRIntroCached_spec__1(lean_object* v_00_u03b2_1404_, lean_object* v_m_1405_, lean_object* v_a_1406_, lean_object* v_b_1407_){
_start:
{
lean_object* v___x_1408_; 
v___x_1408_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleForRIntroCached_spec__1___redArg(v_m_1405_, v_a_1406_, v_b_1407_);
return v___x_1408_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleForRIntroCached_spec__0_spec__0(lean_object* v_00_u03b2_1409_, lean_object* v_a_1410_, lean_object* v_x_1411_){
_start:
{
lean_object* v___x_1412_; 
v___x_1412_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleForRIntroCached_spec__0_spec__0___redArg(v_a_1410_, v_x_1411_);
return v___x_1412_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleForRIntroCached_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1413_, lean_object* v_a_1414_, lean_object* v_x_1415_){
_start:
{
lean_object* v_res_1416_; 
v_res_1416_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleForRIntroCached_spec__0_spec__0(v_00_u03b2_1413_, v_a_1414_, v_x_1415_);
lean_dec(v_x_1415_);
lean_dec(v_a_1414_);
return v_res_1416_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleForRIntroCached_spec__1_spec__2(lean_object* v_00_u03b2_1417_, lean_object* v_a_1418_, lean_object* v_x_1419_){
_start:
{
uint8_t v___x_1420_; 
v___x_1420_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleForRIntroCached_spec__1_spec__2___redArg(v_a_1418_, v_x_1419_);
return v___x_1420_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleForRIntroCached_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1421_, lean_object* v_a_1422_, lean_object* v_x_1423_){
_start:
{
uint8_t v_res_1424_; lean_object* v_r_1425_; 
v_res_1424_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleForRIntroCached_spec__1_spec__2(v_00_u03b2_1421_, v_a_1422_, v_x_1423_);
lean_dec(v_x_1423_);
lean_dec(v_a_1422_);
v_r_1425_ = lean_box(v_res_1424_);
return v_r_1425_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleForRIntroCached_spec__1_spec__3(lean_object* v_00_u03b2_1426_, lean_object* v_data_1427_){
_start:
{
lean_object* v___x_1428_; 
v___x_1428_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleForRIntroCached_spec__1_spec__3___redArg(v_data_1427_);
return v___x_1428_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleForRIntroCached_spec__1_spec__4(lean_object* v_00_u03b2_1429_, lean_object* v_a_1430_, lean_object* v_b_1431_, lean_object* v_x_1432_){
_start:
{
lean_object* v___x_1433_; 
v___x_1433_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleForRIntroCached_spec__1_spec__4___redArg(v_a_1430_, v_b_1431_, v_x_1432_);
return v___x_1433_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleForRIntroCached_spec__1_spec__3_spec__4(lean_object* v_00_u03b2_1434_, lean_object* v_i_1435_, lean_object* v_source_1436_, lean_object* v_target_1437_){
_start:
{
lean_object* v___x_1438_; 
v___x_1438_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleForRIntroCached_spec__1_spec__3_spec__4___redArg(v_i_1435_, v_source_1436_, v_target_1437_);
return v___x_1438_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleForRIntroCached_spec__1_spec__3_spec__4_spec__5(lean_object* v_00_u03b2_1439_, lean_object* v_x_1440_, lean_object* v_x_1441_){
_start:
{
lean_object* v___x_1442_; 
v___x_1442_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleForRIntroCached_spec__1_spec__3_spec__4_spec__5___redArg(v_x_1440_, v_x_1441_);
return v___x_1442_;
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
