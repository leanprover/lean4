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
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_noption_is_some(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_noption_get(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
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
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Raw_setEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Elab_Tactic_VCGen_WPApp_instWP(lean_object*);
lean_object* l_Lean_Elab_Tactic_VCGen_mkBackwardRuleForSplit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_BackwardRule_shareCommon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__3_spec__5_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__3_spec__5_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__3_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__3_spec__5___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__3___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__3___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg___boxed(lean_object*, lean_object*);
static const lean_array_object l_Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__3_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__3_spec__5_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__3_spec__5_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__2_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__2_spec__4_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__2_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__2___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__2_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__2_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__2_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__3___redArg(lean_object* v_m_151_, lean_object* v_query_152_, lean_object* v_x_153_, lean_object* v_x_154_, lean_object* v_x_155_){
_start:
{
lean_object* v_zero_156_; uint8_t v_isZero_157_; 
v_zero_156_ = lean_unsigned_to_nat(0u);
v_isZero_157_ = lean_nat_dec_eq(v_x_154_, v_zero_156_);
if (v_isZero_157_ == 1)
{
lean_dec(v_x_155_);
lean_dec(v_x_154_);
if (lean_obj_tag(v_x_153_) == 0)
{
lean_object* v___x_158_; 
v___x_158_ = lean_box(2);
return v___x_158_;
}
else
{
lean_object* v_val_159_; lean_object* v___x_161_; uint8_t v_isShared_162_; uint8_t v_isSharedCheck_166_; 
v_val_159_ = lean_ctor_get(v_x_153_, 0);
v_isSharedCheck_166_ = !lean_is_exclusive(v_x_153_);
if (v_isSharedCheck_166_ == 0)
{
v___x_161_ = v_x_153_;
v_isShared_162_ = v_isSharedCheck_166_;
goto v_resetjp_160_;
}
else
{
lean_inc(v_val_159_);
lean_dec(v_x_153_);
v___x_161_ = lean_box(0);
v_isShared_162_ = v_isSharedCheck_166_;
goto v_resetjp_160_;
}
v_resetjp_160_:
{
lean_object* v___x_164_; 
if (v_isShared_162_ == 0)
{
v___x_164_ = v___x_161_;
goto v_reusejp_163_;
}
else
{
lean_object* v_reuseFailAlloc_165_; 
v_reuseFailAlloc_165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_165_, 0, v_val_159_);
v___x_164_ = v_reuseFailAlloc_165_;
goto v_reusejp_163_;
}
v_reusejp_163_:
{
return v___x_164_;
}
}
}
}
else
{
lean_object* v_keyArray_167_; lean_object* v_valueArray_168_; lean_object* v___x_169_; uint8_t v_isSome_170_; 
v_keyArray_167_ = lean_ctor_get(v_m_151_, 1);
v_valueArray_168_ = lean_ctor_get(v_m_151_, 2);
v___x_169_ = lean_array_fget_borrowed(v_keyArray_167_, v_x_155_);
v_isSome_170_ = lean_noption_is_some(v___x_169_);
if (v_isSome_170_ == 0)
{
lean_dec(v_x_154_);
if (lean_obj_tag(v_x_153_) == 0)
{
lean_object* v___x_171_; 
v___x_171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_171_, 0, v_x_155_);
return v___x_171_;
}
else
{
lean_object* v_val_172_; lean_object* v___x_174_; uint8_t v_isShared_175_; uint8_t v_isSharedCheck_179_; 
lean_dec(v_x_155_);
v_val_172_ = lean_ctor_get(v_x_153_, 0);
v_isSharedCheck_179_ = !lean_is_exclusive(v_x_153_);
if (v_isSharedCheck_179_ == 0)
{
v___x_174_ = v_x_153_;
v_isShared_175_ = v_isSharedCheck_179_;
goto v_resetjp_173_;
}
else
{
lean_inc(v_val_172_);
lean_dec(v_x_153_);
v___x_174_ = lean_box(0);
v_isShared_175_ = v_isSharedCheck_179_;
goto v_resetjp_173_;
}
v_resetjp_173_:
{
lean_object* v___x_177_; 
if (v_isShared_175_ == 0)
{
v___x_177_ = v___x_174_;
goto v_reusejp_176_;
}
else
{
lean_object* v_reuseFailAlloc_178_; 
v_reuseFailAlloc_178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_178_, 0, v_val_172_);
v___x_177_ = v_reuseFailAlloc_178_;
goto v_reusejp_176_;
}
v_reusejp_176_:
{
return v___x_177_;
}
}
}
}
else
{
lean_object* v_one_180_; lean_object* v_n_181_; lean_object* v___y_183_; 
v_one_180_ = lean_unsigned_to_nat(1u);
v_n_181_ = lean_nat_sub(v_x_154_, v_one_180_);
lean_dec(v_x_154_);
if (v_isSome_170_ == 0)
{
goto v___jp_189_;
}
else
{
lean_object* v___x_191_; uint8_t v_isSome_192_; 
v___x_191_ = lean_array_fget_borrowed(v_valueArray_168_, v_x_155_);
v_isSome_192_ = lean_noption_is_some(v___x_191_);
if (v_isSome_192_ == 0)
{
goto v___jp_189_;
}
else
{
lean_object* v_val_193_; lean_object* v_fst_194_; lean_object* v_snd_195_; lean_object* v_fst_196_; lean_object* v_snd_197_; lean_object* v_val_198_; uint8_t v___y_200_; uint8_t v___x_207_; 
lean_inc(v___x_169_);
v_val_193_ = lean_noption_get(v___x_169_);
v_fst_194_ = lean_ctor_get(v_val_193_, 0);
lean_inc(v_fst_194_);
v_snd_195_ = lean_ctor_get(v_val_193_, 1);
lean_inc(v_snd_195_);
v_fst_196_ = lean_ctor_get(v_query_152_, 0);
v_snd_197_ = lean_ctor_get(v_query_152_, 1);
lean_inc(v___x_191_);
v_val_198_ = lean_noption_get(v___x_191_);
v___x_207_ = lean_name_eq(v_fst_194_, v_fst_196_);
lean_dec(v_fst_194_);
if (v___x_207_ == 0)
{
lean_dec(v_snd_195_);
v___y_200_ = v___x_207_;
goto v___jp_199_;
}
else
{
lean_object* v_fst_208_; lean_object* v_snd_209_; lean_object* v_fst_210_; lean_object* v_snd_211_; size_t v___x_212_; size_t v___x_213_; uint8_t v___x_214_; 
v_fst_208_ = lean_ctor_get(v_snd_195_, 0);
lean_inc(v_fst_208_);
v_snd_209_ = lean_ctor_get(v_snd_195_, 1);
lean_inc(v_snd_209_);
lean_dec(v_snd_195_);
v_fst_210_ = lean_ctor_get(v_snd_197_, 0);
v_snd_211_ = lean_ctor_get(v_snd_197_, 1);
v___x_212_ = lean_ptr_addr(v_fst_208_);
lean_dec(v_fst_208_);
v___x_213_ = lean_ptr_addr(v_fst_210_);
v___x_214_ = lean_usize_dec_eq(v___x_212_, v___x_213_);
if (v___x_214_ == 0)
{
lean_dec(v_snd_209_);
v___y_200_ = v___x_214_;
goto v___jp_199_;
}
else
{
uint8_t v___x_215_; 
v___x_215_ = lean_nat_dec_eq(v_snd_209_, v_snd_211_);
lean_dec(v_snd_209_);
v___y_200_ = v___x_215_;
goto v___jp_199_;
}
}
v___jp_199_:
{
if (v___y_200_ == 0)
{
lean_object* v___x_201_; lean_object* v___x_202_; uint8_t v___x_203_; 
lean_dec(v_val_198_);
lean_dec(v_val_193_);
v___x_201_ = lean_array_get_size(v_keyArray_167_);
v___x_202_ = lean_nat_add(v_x_155_, v_one_180_);
lean_dec(v_x_155_);
v___x_203_ = lean_nat_dec_lt(v___x_202_, v___x_201_);
if (v___x_203_ == 0)
{
lean_dec(v___x_202_);
v_x_154_ = v_n_181_;
v_x_155_ = v_zero_156_;
goto _start;
}
else
{
v_x_154_ = v_n_181_;
v_x_155_ = v___x_202_;
goto _start;
}
}
else
{
lean_object* v___x_206_; 
lean_dec(v_n_181_);
lean_dec(v_x_153_);
v___x_206_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_206_, 0, v_x_155_);
lean_ctor_set(v___x_206_, 1, v_val_193_);
lean_ctor_set(v___x_206_, 2, v_val_198_);
return v___x_206_;
}
}
}
}
v___jp_182_:
{
lean_object* v___x_184_; lean_object* v___x_185_; uint8_t v___x_186_; 
v___x_184_ = lean_array_get_size(v_keyArray_167_);
v___x_185_ = lean_nat_add(v_x_155_, v_one_180_);
lean_dec(v_x_155_);
v___x_186_ = lean_nat_dec_lt(v___x_185_, v___x_184_);
if (v___x_186_ == 0)
{
lean_dec(v___x_185_);
v_x_153_ = v___y_183_;
v_x_154_ = v_n_181_;
v_x_155_ = v_zero_156_;
goto _start;
}
else
{
v_x_153_ = v___y_183_;
v_x_154_ = v_n_181_;
v_x_155_ = v___x_185_;
goto _start;
}
}
v___jp_189_:
{
if (lean_obj_tag(v_x_153_) == 0)
{
lean_object* v___x_190_; 
lean_inc(v_x_155_);
v___x_190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_190_, 0, v_x_155_);
v___y_183_ = v___x_190_;
goto v___jp_182_;
}
else
{
v___y_183_ = v_x_153_;
goto v___jp_182_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__3___redArg___boxed(lean_object* v_m_216_, lean_object* v_query_217_, lean_object* v_x_218_, lean_object* v_x_219_, lean_object* v_x_220_){
_start:
{
lean_object* v_res_221_; 
v_res_221_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__3___redArg(v_m_216_, v_query_217_, v_x_218_, v_x_219_, v_x_220_);
lean_dec_ref(v_query_217_);
lean_dec_ref(v_m_216_);
return v_res_221_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2___redArg(lean_object* v_m_222_, lean_object* v_query_223_){
_start:
{
lean_object* v_keyArray_224_; lean_object* v_fst_225_; lean_object* v_snd_226_; lean_object* v___x_227_; uint64_t v___y_229_; 
v_keyArray_224_ = lean_ctor_get(v_m_222_, 1);
v_fst_225_ = lean_ctor_get(v_query_223_, 0);
v_snd_226_ = lean_ctor_get(v_query_223_, 1);
v___x_227_ = lean_array_get_size(v_keyArray_224_);
if (lean_obj_tag(v_fst_225_) == 0)
{
uint64_t v___x_253_; 
v___x_253_ = 1723ULL;
v___y_229_ = v___x_253_;
goto v___jp_228_;
}
else
{
uint64_t v_hash_254_; 
v_hash_254_ = lean_ctor_get_uint64(v_fst_225_, sizeof(void*)*2);
v___y_229_ = v_hash_254_;
goto v___jp_228_;
}
v___jp_228_:
{
lean_object* v_fst_230_; lean_object* v_snd_231_; size_t v___x_232_; size_t v___x_233_; size_t v___x_234_; uint64_t v___x_235_; uint64_t v___x_236_; uint64_t v___x_237_; uint64_t v___x_238_; uint64_t v___x_239_; uint64_t v___x_240_; uint64_t v_fold_241_; uint64_t v___x_242_; uint64_t v___x_243_; uint64_t v___x_244_; size_t v___x_245_; size_t v___x_246_; size_t v___x_247_; size_t v___x_248_; size_t v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; 
v_fst_230_ = lean_ctor_get(v_snd_226_, 0);
v_snd_231_ = lean_ctor_get(v_snd_226_, 1);
v___x_232_ = lean_ptr_addr(v_fst_230_);
v___x_233_ = ((size_t)3ULL);
v___x_234_ = lean_usize_shift_right(v___x_232_, v___x_233_);
v___x_235_ = lean_usize_to_uint64(v___x_234_);
v___x_236_ = lean_uint64_of_nat(v_snd_231_);
v___x_237_ = lean_uint64_mix_hash(v___x_235_, v___x_236_);
v___x_238_ = lean_uint64_mix_hash(v___y_229_, v___x_237_);
v___x_239_ = 32ULL;
v___x_240_ = lean_uint64_shift_right(v___x_238_, v___x_239_);
v_fold_241_ = lean_uint64_xor(v___x_238_, v___x_240_);
v___x_242_ = 16ULL;
v___x_243_ = lean_uint64_shift_right(v_fold_241_, v___x_242_);
v___x_244_ = lean_uint64_xor(v_fold_241_, v___x_243_);
v___x_245_ = lean_uint64_to_usize(v___x_244_);
v___x_246_ = lean_usize_of_nat(v___x_227_);
v___x_247_ = ((size_t)1ULL);
v___x_248_ = lean_usize_sub(v___x_246_, v___x_247_);
v___x_249_ = lean_usize_land(v___x_245_, v___x_248_);
v___x_250_ = lean_usize_to_nat(v___x_249_);
v___x_251_ = lean_box(0);
v___x_252_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__3___redArg(v_m_222_, v_query_223_, v___x_251_, v___x_227_, v___x_250_);
return v___x_252_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2___redArg___boxed(lean_object* v_m_255_, lean_object* v_query_256_){
_start:
{
lean_object* v_res_257_; 
v_res_257_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2___redArg(v_m_255_, v_query_256_);
lean_dec_ref(v_query_256_);
lean_dec_ref(v_m_255_);
return v_res_257_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__3_spec__5_spec__6___redArg(lean_object* v_b_258_, lean_object* v_acc_259_, lean_object* v_i_260_){
_start:
{
lean_object* v___y_262_; lean_object* v_keyArray_270_; lean_object* v_valueArray_271_; lean_object* v___x_272_; uint8_t v___x_273_; 
v_keyArray_270_ = lean_ctor_get(v_b_258_, 1);
v_valueArray_271_ = lean_ctor_get(v_b_258_, 2);
v___x_272_ = lean_array_get_size(v_keyArray_270_);
v___x_273_ = lean_nat_dec_lt(v_i_260_, v___x_272_);
if (v___x_273_ == 0)
{
lean_dec(v_i_260_);
return v_acc_259_;
}
else
{
lean_object* v___x_274_; uint8_t v_isSome_275_; 
v___x_274_ = lean_array_fget_borrowed(v_keyArray_270_, v_i_260_);
v_isSome_275_ = lean_noption_is_some(v___x_274_);
if (v_isSome_275_ == 0)
{
goto v___jp_266_;
}
else
{
lean_object* v___x_276_; uint8_t v_isSome_277_; 
v___x_276_ = lean_array_fget_borrowed(v_valueArray_271_, v_i_260_);
v_isSome_277_ = lean_noption_is_some(v___x_276_);
if (v_isSome_277_ == 0)
{
goto v___jp_266_;
}
else
{
lean_object* v_val_278_; lean_object* v_val_279_; lean_object* v_i_281_; lean_object* v___x_286_; 
lean_inc(v___x_274_);
v_val_278_ = lean_noption_get(v___x_274_);
lean_inc(v___x_276_);
v_val_279_ = lean_noption_get(v___x_276_);
v___x_286_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2___redArg(v_acc_259_, v_val_278_);
switch(lean_obj_tag(v___x_286_))
{
case 0:
{
lean_object* v_index_287_; lean_object* v_size_288_; lean_object* v___x_289_; 
v_index_287_ = lean_ctor_get(v___x_286_, 0);
lean_inc(v_index_287_);
lean_dec_ref_known(v___x_286_, 3);
v_size_288_ = lean_ctor_get(v_acc_259_, 0);
lean_inc(v_size_288_);
v___x_289_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_259_, v_size_288_, v_index_287_, v_val_278_, v_val_279_);
lean_dec(v_index_287_);
v___y_262_ = v___x_289_;
goto v___jp_261_;
}
case 1:
{
lean_object* v_index_290_; 
v_index_290_ = lean_ctor_get(v___x_286_, 0);
lean_inc(v_index_290_);
lean_dec_ref_known(v___x_286_, 1);
v_i_281_ = v_index_290_;
goto v___jp_280_;
}
default: 
{
lean_object* v___x_291_; lean_object* v___x_292_; 
v___x_291_ = lean_unsigned_to_nat(0u);
v___x_292_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v_acc_259_, v___x_291_);
if (lean_obj_tag(v___x_292_) == 0)
{
lean_object* v_index_293_; 
v_index_293_ = lean_ctor_get(v___x_292_, 0);
lean_inc(v_index_293_);
lean_dec_ref_known(v___x_292_, 1);
v_i_281_ = v_index_293_;
goto v___jp_280_;
}
else
{
lean_dec(v_val_279_);
lean_dec(v_val_278_);
v___y_262_ = v_acc_259_;
goto v___jp_261_;
}
}
}
v___jp_280_:
{
lean_object* v_size_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; 
v_size_282_ = lean_ctor_get(v_acc_259_, 0);
v___x_283_ = lean_unsigned_to_nat(1u);
v___x_284_ = lean_nat_add(v_size_282_, v___x_283_);
v___x_285_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_259_, v___x_284_, v_i_281_, v_val_278_, v_val_279_);
lean_dec(v_i_281_);
v___y_262_ = v___x_285_;
goto v___jp_261_;
}
}
}
}
v___jp_261_:
{
lean_object* v___x_263_; lean_object* v___x_264_; 
v___x_263_ = lean_unsigned_to_nat(1u);
v___x_264_ = lean_nat_add(v_i_260_, v___x_263_);
lean_dec(v_i_260_);
v_acc_259_ = v___y_262_;
v_i_260_ = v___x_264_;
goto _start;
}
v___jp_266_:
{
lean_object* v___x_267_; lean_object* v___x_268_; 
v___x_267_ = lean_unsigned_to_nat(1u);
v___x_268_ = lean_nat_add(v_i_260_, v___x_267_);
lean_dec(v_i_260_);
v_i_260_ = v___x_268_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__3_spec__5_spec__6___redArg___boxed(lean_object* v_b_294_, lean_object* v_acc_295_, lean_object* v_i_296_){
_start:
{
lean_object* v_res_297_; 
v_res_297_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__3_spec__5_spec__6___redArg(v_b_294_, v_acc_295_, v_i_296_);
lean_dec_ref(v_b_294_);
return v_res_297_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__3_spec__5___redArg(lean_object* v_init_298_, lean_object* v_b_299_){
_start:
{
lean_object* v___x_300_; lean_object* v___x_301_; 
v___x_300_ = lean_unsigned_to_nat(0u);
v___x_301_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__3_spec__5_spec__6___redArg(v_b_299_, v_init_298_, v___x_300_);
return v___x_301_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__3_spec__5___redArg___boxed(lean_object* v_init_302_, lean_object* v_b_303_){
_start:
{
lean_object* v_res_304_; 
v_res_304_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__3_spec__5___redArg(v_init_302_, v_b_303_);
lean_dec_ref(v_b_303_);
return v_res_304_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__3___redArg(lean_object* v_m_305_){
_start:
{
lean_object* v_keyArray_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v_cellCount_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v_target_313_; lean_object* v___x_314_; 
v_keyArray_306_ = lean_ctor_get(v_m_305_, 1);
v___x_307_ = lean_array_get_size(v_keyArray_306_);
v___x_308_ = lean_unsigned_to_nat(2u);
v_cellCount_309_ = lean_nat_mul(v___x_307_, v___x_308_);
v___x_310_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_309_);
v___x_311_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_309_);
v___x_312_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_309_);
v_target_313_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_target_313_, 0, v___x_310_);
lean_ctor_set(v_target_313_, 1, v___x_311_);
lean_ctor_set(v_target_313_, 2, v___x_312_);
v___x_314_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__3_spec__5___redArg(v_target_313_, v_m_305_);
return v___x_314_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__3___redArg___boxed(lean_object* v_m_315_){
_start:
{
lean_object* v_res_316_; 
v_res_316_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__3___redArg(v_m_315_);
lean_dec_ref(v_m_315_);
return v_res_316_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__0_spec__0___redArg(lean_object* v_m_317_, lean_object* v_query_318_){
_start:
{
lean_object* v___x_319_; 
v___x_319_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2___redArg(v_m_317_, v_query_318_);
if (lean_obj_tag(v___x_319_) == 0)
{
lean_object* v_index_320_; lean_object* v_key_321_; lean_object* v_value_322_; lean_object* v___x_324_; uint8_t v_isShared_325_; uint8_t v_isSharedCheck_329_; 
v_index_320_ = lean_ctor_get(v___x_319_, 0);
v_key_321_ = lean_ctor_get(v___x_319_, 1);
v_value_322_ = lean_ctor_get(v___x_319_, 2);
v_isSharedCheck_329_ = !lean_is_exclusive(v___x_319_);
if (v_isSharedCheck_329_ == 0)
{
v___x_324_ = v___x_319_;
v_isShared_325_ = v_isSharedCheck_329_;
goto v_resetjp_323_;
}
else
{
lean_inc(v_value_322_);
lean_inc(v_key_321_);
lean_inc(v_index_320_);
lean_dec(v___x_319_);
v___x_324_ = lean_box(0);
v_isShared_325_ = v_isSharedCheck_329_;
goto v_resetjp_323_;
}
v_resetjp_323_:
{
lean_object* v___x_327_; 
if (v_isShared_325_ == 0)
{
v___x_327_ = v___x_324_;
goto v_reusejp_326_;
}
else
{
lean_object* v_reuseFailAlloc_328_; 
v_reuseFailAlloc_328_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_328_, 0, v_index_320_);
lean_ctor_set(v_reuseFailAlloc_328_, 1, v_key_321_);
lean_ctor_set(v_reuseFailAlloc_328_, 2, v_value_322_);
v___x_327_ = v_reuseFailAlloc_328_;
goto v_reusejp_326_;
}
v_reusejp_326_:
{
return v___x_327_;
}
}
}
else
{
lean_object* v___x_330_; 
lean_dec(v___x_319_);
v___x_330_ = lean_box(1);
return v___x_330_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__0_spec__0___redArg___boxed(lean_object* v_m_331_, lean_object* v_query_332_){
_start:
{
lean_object* v_res_333_; 
v_res_333_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__0_spec__0___redArg(v_m_331_, v_query_332_);
lean_dec_ref(v_query_332_);
lean_dec_ref(v_m_331_);
return v_res_333_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg(lean_object* v_m_334_, lean_object* v_a_335_){
_start:
{
lean_object* v___x_336_; 
v___x_336_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__0_spec__0___redArg(v_m_334_, v_a_335_);
if (lean_obj_tag(v___x_336_) == 0)
{
lean_object* v_value_337_; lean_object* v___x_338_; 
v_value_337_ = lean_ctor_get(v___x_336_, 2);
lean_inc(v_value_337_);
lean_dec_ref_known(v___x_336_, 3);
v___x_338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_338_, 0, v_value_337_);
return v___x_338_;
}
else
{
lean_object* v___x_339_; 
v___x_339_ = lean_box(0);
return v___x_339_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg___boxed(lean_object* v_m_340_, lean_object* v_a_341_){
_start:
{
lean_object* v_res_342_; 
v_res_342_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg(v_m_340_, v_a_341_);
lean_dec_ref(v_a_341_);
lean_dec_ref(v_m_340_);
return v_res_342_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached(lean_object* v_specThm_345_, lean_object* v_info_346_, lean_object* v_a_347_, lean_object* v_a_348_, lean_object* v_a_349_, lean_object* v_a_350_, lean_object* v_a_351_, lean_object* v_a_352_, lean_object* v_a_353_, lean_object* v_a_354_, lean_object* v_a_355_, lean_object* v_a_356_, lean_object* v_a_357_){
_start:
{
lean_object* v___x_359_; lean_object* v_proof_360_; lean_object* v_excessArgs_361_; lean_object* v_specBackwardRuleCache_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v_key_367_; lean_object* v___x_368_; 
v___x_359_ = lean_st_ref_get(v_a_348_);
v_proof_360_ = lean_ctor_get(v_specThm_345_, 1);
v_excessArgs_361_ = lean_ctor_get(v_info_346_, 2);
v_specBackwardRuleCache_362_ = lean_ctor_get(v___x_359_, 0);
lean_inc_ref(v_specBackwardRuleCache_362_);
lean_dec(v___x_359_);
v___x_363_ = l_Lean_Elab_Tactic_VCGen_SpecAttr_SpecProof_key(v_proof_360_);
v___x_364_ = l_Lean_Elab_Tactic_VCGen_WPApp_instWP(v_info_346_);
v___x_365_ = lean_array_get_size(v_excessArgs_361_);
v___x_366_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_366_, 0, v___x_364_);
lean_ctor_set(v___x_366_, 1, v___x_365_);
v_key_367_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_key_367_, 0, v___x_363_);
lean_ctor_set(v_key_367_, 1, v___x_366_);
v___x_368_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg(v_specBackwardRuleCache_362_, v_key_367_);
lean_dec_ref(v_specBackwardRuleCache_362_);
if (lean_obj_tag(v___x_368_) == 1)
{
lean_object* v___x_369_; 
lean_dec_ref_known(v_key_367_, 2);
lean_dec_ref(v_info_346_);
lean_dec_ref(v_specThm_345_);
v___x_369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_369_, 0, v___x_368_);
return v___x_369_;
}
else
{
lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___f_372_; uint8_t v___x_373_; lean_object* v___x_374_; 
lean_dec(v___x_368_);
v___x_370_ = lean_unsigned_to_nat(0u);
v___x_371_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached___closed__0));
v___f_372_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached___lam__0___boxed), 15, 3);
lean_closure_set(v___f_372_, 0, v_specThm_345_);
lean_closure_set(v___f_372_, 1, v_info_346_);
lean_closure_set(v___f_372_, 2, v___x_371_);
v___x_373_ = 0;
v___x_374_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__1___redArg(v___f_372_, v___x_373_, v_a_347_, v_a_348_, v_a_349_, v_a_350_, v_a_351_, v_a_352_, v_a_353_, v_a_354_, v_a_355_, v_a_356_, v_a_357_);
if (lean_obj_tag(v___x_374_) == 0)
{
lean_object* v_a_375_; lean_object* v___x_377_; uint8_t v_isShared_378_; uint8_t v_isSharedCheck_496_; 
v_a_375_ = lean_ctor_get(v___x_374_, 0);
v_isSharedCheck_496_ = !lean_is_exclusive(v___x_374_);
if (v_isSharedCheck_496_ == 0)
{
v___x_377_ = v___x_374_;
v_isShared_378_ = v_isSharedCheck_496_;
goto v_resetjp_376_;
}
else
{
lean_inc(v_a_375_);
lean_dec(v___x_374_);
v___x_377_ = lean_box(0);
v_isShared_378_ = v_isSharedCheck_496_;
goto v_resetjp_376_;
}
v_resetjp_376_:
{
if (lean_obj_tag(v_a_375_) == 0)
{
lean_object* v___x_379_; lean_object* v___x_381_; 
lean_dec_ref_known(v_key_367_, 2);
v___x_379_ = lean_box(0);
if (v_isShared_378_ == 0)
{
lean_ctor_set(v___x_377_, 0, v___x_379_);
v___x_381_ = v___x_377_;
goto v_reusejp_380_;
}
else
{
lean_object* v_reuseFailAlloc_382_; 
v_reuseFailAlloc_382_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_382_, 0, v___x_379_);
v___x_381_ = v_reuseFailAlloc_382_;
goto v_reusejp_380_;
}
v_reusejp_380_:
{
return v___x_381_;
}
}
else
{
lean_object* v_val_383_; 
v_val_383_ = lean_ctor_get(v_a_375_, 0);
lean_inc(v_val_383_);
lean_dec_ref_known(v_a_375_, 1);
if (lean_obj_tag(v_val_383_) == 1)
{
lean_object* v_val_384_; lean_object* v___x_386_; uint8_t v_isShared_387_; uint8_t v_isSharedCheck_491_; 
lean_del_object(v___x_377_);
v_val_384_ = lean_ctor_get(v_val_383_, 0);
v_isSharedCheck_491_ = !lean_is_exclusive(v_val_383_);
if (v_isSharedCheck_491_ == 0)
{
v___x_386_ = v_val_383_;
v_isShared_387_ = v_isSharedCheck_491_;
goto v_resetjp_385_;
}
else
{
lean_inc(v_val_384_);
lean_dec(v_val_383_);
v___x_386_ = lean_box(0);
v_isShared_387_ = v_isSharedCheck_491_;
goto v_resetjp_385_;
}
v_resetjp_385_:
{
lean_object* v___x_388_; 
v___x_388_ = l_Lean_Meta_Sym_BackwardRule_shareCommon(v_val_384_, v_a_352_, v_a_353_, v_a_354_, v_a_355_, v_a_356_, v_a_357_);
if (lean_obj_tag(v___x_388_) == 0)
{
lean_object* v_a_389_; lean_object* v___x_391_; uint8_t v_isShared_392_; uint8_t v_isSharedCheck_482_; 
v_a_389_ = lean_ctor_get(v___x_388_, 0);
v_isSharedCheck_482_ = !lean_is_exclusive(v___x_388_);
if (v_isSharedCheck_482_ == 0)
{
v___x_391_ = v___x_388_;
v_isShared_392_ = v_isSharedCheck_482_;
goto v_resetjp_390_;
}
else
{
lean_inc(v_a_389_);
lean_dec(v___x_388_);
v___x_391_ = lean_box(0);
v_isShared_392_ = v_isSharedCheck_482_;
goto v_resetjp_390_;
}
v_resetjp_390_:
{
lean_object* v___x_393_; lean_object* v_specBackwardRuleCache_394_; lean_object* v_splitBackwardRuleCache_395_; lean_object* v_latticeBackwardRuleCache_396_; lean_object* v_frameBackwardRuleCache_397_; lean_object* v_frameDB_398_; lean_object* v_invariants_399_; lean_object* v_vcs_400_; lean_object* v_simpState_401_; lean_object* v_fuel_402_; lean_object* v_inlineHandledInvariants_403_; lean_object* v___x_405_; uint8_t v_isShared_406_; uint8_t v_isSharedCheck_481_; 
v___x_393_ = lean_st_ref_take(v_a_348_);
v_specBackwardRuleCache_394_ = lean_ctor_get(v___x_393_, 0);
v_splitBackwardRuleCache_395_ = lean_ctor_get(v___x_393_, 1);
v_latticeBackwardRuleCache_396_ = lean_ctor_get(v___x_393_, 2);
v_frameBackwardRuleCache_397_ = lean_ctor_get(v___x_393_, 3);
v_frameDB_398_ = lean_ctor_get(v___x_393_, 4);
v_invariants_399_ = lean_ctor_get(v___x_393_, 5);
v_vcs_400_ = lean_ctor_get(v___x_393_, 6);
v_simpState_401_ = lean_ctor_get(v___x_393_, 7);
v_fuel_402_ = lean_ctor_get(v___x_393_, 8);
v_inlineHandledInvariants_403_ = lean_ctor_get(v___x_393_, 9);
v_isSharedCheck_481_ = !lean_is_exclusive(v___x_393_);
if (v_isSharedCheck_481_ == 0)
{
v___x_405_ = v___x_393_;
v_isShared_406_ = v_isSharedCheck_481_;
goto v_resetjp_404_;
}
else
{
lean_inc(v_inlineHandledInvariants_403_);
lean_inc(v_fuel_402_);
lean_inc(v_simpState_401_);
lean_inc(v_vcs_400_);
lean_inc(v_invariants_399_);
lean_inc(v_frameDB_398_);
lean_inc(v_frameBackwardRuleCache_397_);
lean_inc(v_latticeBackwardRuleCache_396_);
lean_inc(v_splitBackwardRuleCache_395_);
lean_inc(v_specBackwardRuleCache_394_);
lean_dec(v___x_393_);
v___x_405_ = lean_box(0);
v_isShared_406_ = v_isSharedCheck_481_;
goto v_resetjp_404_;
}
v_resetjp_404_:
{
lean_object* v___x_408_; 
lean_inc(v_a_389_);
if (v_isShared_387_ == 0)
{
lean_ctor_set(v___x_386_, 0, v_a_389_);
v___x_408_ = v___x_386_;
goto v_reusejp_407_;
}
else
{
lean_object* v_reuseFailAlloc_480_; 
v_reuseFailAlloc_480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_480_, 0, v_a_389_);
v___x_408_ = v_reuseFailAlloc_480_;
goto v_reusejp_407_;
}
v_reusejp_407_:
{
lean_object* v___y_410_; lean_object* v___y_419_; lean_object* v_i_420_; lean_object* v___y_435_; lean_object* v_i_436_; lean_object* v___y_442_; lean_object* v___x_450_; 
v___x_450_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2___redArg(v_specBackwardRuleCache_394_, v_key_367_);
switch(lean_obj_tag(v___x_450_))
{
case 0:
{
lean_object* v_index_451_; lean_object* v_size_452_; lean_object* v___x_453_; 
v_index_451_ = lean_ctor_get(v___x_450_, 0);
lean_inc(v_index_451_);
lean_dec_ref_known(v___x_450_, 3);
v_size_452_ = lean_ctor_get(v_specBackwardRuleCache_394_, 0);
lean_inc(v_size_452_);
v___x_453_ = l_Std_DHashMap_Raw_setEntry___redArg(v_specBackwardRuleCache_394_, v_size_452_, v_index_451_, v_key_367_, v_a_389_);
lean_dec(v_index_451_);
v___y_410_ = v___x_453_;
goto v___jp_409_;
}
case 1:
{
lean_object* v_index_454_; lean_object* v_size_455_; lean_object* v_keyArray_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; uint8_t v___x_460_; 
v_index_454_ = lean_ctor_get(v___x_450_, 0);
lean_inc(v_index_454_);
lean_dec_ref_known(v___x_450_, 1);
v_size_455_ = lean_ctor_get(v_specBackwardRuleCache_394_, 0);
v_keyArray_456_ = lean_ctor_get(v_specBackwardRuleCache_394_, 1);
v___x_457_ = lean_unsigned_to_nat(1u);
v___x_458_ = lean_nat_add(v_size_455_, v___x_457_);
v___x_459_ = lean_array_get_size(v_keyArray_456_);
v___x_460_ = lean_nat_dec_lt(v___x_458_, v___x_459_);
if (v___x_460_ == 0)
{
lean_dec(v___x_458_);
lean_dec(v_index_454_);
goto v___jp_425_;
}
else
{
lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; uint8_t v___x_465_; 
v___x_461_ = lean_unsigned_to_nat(4u);
v___x_462_ = lean_nat_mul(v___x_458_, v___x_461_);
v___x_463_ = lean_unsigned_to_nat(3u);
v___x_464_ = lean_nat_mul(v___x_459_, v___x_463_);
v___x_465_ = lean_nat_dec_le(v___x_462_, v___x_464_);
lean_dec(v___x_464_);
lean_dec(v___x_462_);
if (v___x_465_ == 0)
{
lean_dec(v___x_458_);
lean_dec(v_index_454_);
goto v___jp_425_;
}
else
{
lean_object* v___x_466_; 
v___x_466_ = l_Std_DHashMap_Raw_setEntry___redArg(v_specBackwardRuleCache_394_, v___x_458_, v_index_454_, v_key_367_, v_a_389_);
lean_dec(v_index_454_);
v___y_410_ = v___x_466_;
goto v___jp_409_;
}
}
}
default: 
{
lean_object* v_size_467_; lean_object* v_keyArray_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; uint8_t v___x_472_; 
v_size_467_ = lean_ctor_get(v_specBackwardRuleCache_394_, 0);
v_keyArray_468_ = lean_ctor_get(v_specBackwardRuleCache_394_, 1);
v___x_469_ = lean_unsigned_to_nat(1u);
v___x_470_ = lean_nat_add(v_size_467_, v___x_469_);
v___x_471_ = lean_array_get_size(v_keyArray_468_);
v___x_472_ = lean_nat_dec_lt(v___x_470_, v___x_471_);
if (v___x_472_ == 0)
{
lean_object* v___x_473_; 
lean_dec(v___x_470_);
v___x_473_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__3___redArg(v_specBackwardRuleCache_394_);
lean_dec_ref(v_specBackwardRuleCache_394_);
v___y_442_ = v___x_473_;
goto v___jp_441_;
}
else
{
lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; uint8_t v___x_478_; 
v___x_474_ = lean_unsigned_to_nat(4u);
v___x_475_ = lean_nat_mul(v___x_470_, v___x_474_);
lean_dec(v___x_470_);
v___x_476_ = lean_unsigned_to_nat(3u);
v___x_477_ = lean_nat_mul(v___x_471_, v___x_476_);
v___x_478_ = lean_nat_dec_le(v___x_475_, v___x_477_);
lean_dec(v___x_477_);
lean_dec(v___x_475_);
if (v___x_478_ == 0)
{
lean_object* v___x_479_; 
v___x_479_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__3___redArg(v_specBackwardRuleCache_394_);
lean_dec_ref(v_specBackwardRuleCache_394_);
v___y_442_ = v___x_479_;
goto v___jp_441_;
}
else
{
v___y_442_ = v_specBackwardRuleCache_394_;
goto v___jp_441_;
}
}
}
}
v___jp_409_:
{
lean_object* v___x_412_; 
if (v_isShared_406_ == 0)
{
lean_ctor_set(v___x_405_, 0, v___y_410_);
v___x_412_ = v___x_405_;
goto v_reusejp_411_;
}
else
{
lean_object* v_reuseFailAlloc_417_; 
v_reuseFailAlloc_417_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_417_, 0, v___y_410_);
lean_ctor_set(v_reuseFailAlloc_417_, 1, v_splitBackwardRuleCache_395_);
lean_ctor_set(v_reuseFailAlloc_417_, 2, v_latticeBackwardRuleCache_396_);
lean_ctor_set(v_reuseFailAlloc_417_, 3, v_frameBackwardRuleCache_397_);
lean_ctor_set(v_reuseFailAlloc_417_, 4, v_frameDB_398_);
lean_ctor_set(v_reuseFailAlloc_417_, 5, v_invariants_399_);
lean_ctor_set(v_reuseFailAlloc_417_, 6, v_vcs_400_);
lean_ctor_set(v_reuseFailAlloc_417_, 7, v_simpState_401_);
lean_ctor_set(v_reuseFailAlloc_417_, 8, v_fuel_402_);
lean_ctor_set(v_reuseFailAlloc_417_, 9, v_inlineHandledInvariants_403_);
v___x_412_ = v_reuseFailAlloc_417_;
goto v_reusejp_411_;
}
v_reusejp_411_:
{
lean_object* v___x_413_; lean_object* v___x_415_; 
v___x_413_ = lean_st_ref_put(v_a_348_, v___x_412_);
if (v_isShared_392_ == 0)
{
lean_ctor_set(v___x_391_, 0, v___x_408_);
v___x_415_ = v___x_391_;
goto v_reusejp_414_;
}
else
{
lean_object* v_reuseFailAlloc_416_; 
v_reuseFailAlloc_416_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_416_, 0, v___x_408_);
v___x_415_ = v_reuseFailAlloc_416_;
goto v_reusejp_414_;
}
v_reusejp_414_:
{
return v___x_415_;
}
}
}
v___jp_418_:
{
lean_object* v_size_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; 
v_size_421_ = lean_ctor_get(v___y_419_, 0);
v___x_422_ = lean_unsigned_to_nat(1u);
v___x_423_ = lean_nat_add(v_size_421_, v___x_422_);
v___x_424_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_419_, v___x_423_, v_i_420_, v_key_367_, v_a_389_);
lean_dec(v_i_420_);
v___y_410_ = v___x_424_;
goto v___jp_409_;
}
v___jp_425_:
{
lean_object* v___x_426_; lean_object* v___x_427_; 
v___x_426_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__3___redArg(v_specBackwardRuleCache_394_);
lean_dec_ref(v_specBackwardRuleCache_394_);
v___x_427_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2___redArg(v___x_426_, v_key_367_);
switch(lean_obj_tag(v___x_427_))
{
case 0:
{
lean_object* v_index_428_; lean_object* v_size_429_; lean_object* v___x_430_; 
v_index_428_ = lean_ctor_get(v___x_427_, 0);
lean_inc(v_index_428_);
lean_dec_ref_known(v___x_427_, 3);
v_size_429_ = lean_ctor_get(v___x_426_, 0);
lean_inc(v_size_429_);
v___x_430_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_426_, v_size_429_, v_index_428_, v_key_367_, v_a_389_);
lean_dec(v_index_428_);
v___y_410_ = v___x_430_;
goto v___jp_409_;
}
case 1:
{
lean_object* v_index_431_; 
v_index_431_ = lean_ctor_get(v___x_427_, 0);
lean_inc(v_index_431_);
lean_dec_ref_known(v___x_427_, 1);
v___y_419_ = v___x_426_;
v_i_420_ = v_index_431_;
goto v___jp_418_;
}
default: 
{
lean_object* v___x_432_; 
v___x_432_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_426_, v___x_370_);
if (lean_obj_tag(v___x_432_) == 0)
{
lean_object* v_index_433_; 
v_index_433_ = lean_ctor_get(v___x_432_, 0);
lean_inc(v_index_433_);
lean_dec_ref_known(v___x_432_, 1);
v___y_419_ = v___x_426_;
v_i_420_ = v_index_433_;
goto v___jp_418_;
}
else
{
lean_dec(v_a_389_);
lean_dec_ref_known(v_key_367_, 2);
v___y_410_ = v___x_426_;
goto v___jp_409_;
}
}
}
}
v___jp_434_:
{
lean_object* v_size_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; 
v_size_437_ = lean_ctor_get(v___y_435_, 0);
v___x_438_ = lean_unsigned_to_nat(1u);
v___x_439_ = lean_nat_add(v_size_437_, v___x_438_);
v___x_440_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_435_, v___x_439_, v_i_436_, v_key_367_, v_a_389_);
lean_dec(v_i_436_);
v___y_410_ = v___x_440_;
goto v___jp_409_;
}
v___jp_441_:
{
lean_object* v___x_443_; 
v___x_443_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2___redArg(v___y_442_, v_key_367_);
switch(lean_obj_tag(v___x_443_))
{
case 0:
{
lean_object* v_index_444_; lean_object* v_size_445_; lean_object* v___x_446_; 
v_index_444_ = lean_ctor_get(v___x_443_, 0);
lean_inc(v_index_444_);
lean_dec_ref_known(v___x_443_, 3);
v_size_445_ = lean_ctor_get(v___y_442_, 0);
lean_inc(v_size_445_);
v___x_446_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_442_, v_size_445_, v_index_444_, v_key_367_, v_a_389_);
lean_dec(v_index_444_);
v___y_410_ = v___x_446_;
goto v___jp_409_;
}
case 1:
{
lean_object* v_index_447_; 
v_index_447_ = lean_ctor_get(v___x_443_, 0);
lean_inc(v_index_447_);
lean_dec_ref_known(v___x_443_, 1);
v___y_435_ = v___y_442_;
v_i_436_ = v_index_447_;
goto v___jp_434_;
}
default: 
{
lean_object* v___x_448_; 
v___x_448_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_442_, v___x_370_);
if (lean_obj_tag(v___x_448_) == 0)
{
lean_object* v_index_449_; 
v_index_449_ = lean_ctor_get(v___x_448_, 0);
lean_inc(v_index_449_);
lean_dec_ref_known(v___x_448_, 1);
v___y_435_ = v___y_442_;
v_i_436_ = v_index_449_;
goto v___jp_434_;
}
else
{
lean_dec(v_a_389_);
lean_dec_ref_known(v_key_367_, 2);
v___y_410_ = v___y_442_;
goto v___jp_409_;
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
lean_object* v_a_483_; lean_object* v___x_485_; uint8_t v_isShared_486_; uint8_t v_isSharedCheck_490_; 
lean_del_object(v___x_386_);
lean_dec_ref_known(v_key_367_, 2);
v_a_483_ = lean_ctor_get(v___x_388_, 0);
v_isSharedCheck_490_ = !lean_is_exclusive(v___x_388_);
if (v_isSharedCheck_490_ == 0)
{
v___x_485_ = v___x_388_;
v_isShared_486_ = v_isSharedCheck_490_;
goto v_resetjp_484_;
}
else
{
lean_inc(v_a_483_);
lean_dec(v___x_388_);
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
else
{
lean_object* v___x_492_; lean_object* v___x_494_; 
lean_dec(v_val_383_);
lean_dec_ref_known(v_key_367_, 2);
v___x_492_ = lean_box(0);
if (v_isShared_378_ == 0)
{
lean_ctor_set(v___x_377_, 0, v___x_492_);
v___x_494_ = v___x_377_;
goto v_reusejp_493_;
}
else
{
lean_object* v_reuseFailAlloc_495_; 
v_reuseFailAlloc_495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_495_, 0, v___x_492_);
v___x_494_ = v_reuseFailAlloc_495_;
goto v_reusejp_493_;
}
v_reusejp_493_:
{
return v___x_494_;
}
}
}
}
}
else
{
lean_object* v_a_497_; lean_object* v___x_499_; uint8_t v_isShared_500_; uint8_t v_isSharedCheck_504_; 
lean_dec_ref_known(v_key_367_, 2);
v_a_497_ = lean_ctor_get(v___x_374_, 0);
v_isSharedCheck_504_ = !lean_is_exclusive(v___x_374_);
if (v_isSharedCheck_504_ == 0)
{
v___x_499_ = v___x_374_;
v_isShared_500_ = v_isSharedCheck_504_;
goto v_resetjp_498_;
}
else
{
lean_inc(v_a_497_);
lean_dec(v___x_374_);
v___x_499_ = lean_box(0);
v_isShared_500_ = v_isSharedCheck_504_;
goto v_resetjp_498_;
}
v_resetjp_498_:
{
lean_object* v___x_502_; 
if (v_isShared_500_ == 0)
{
v___x_502_ = v___x_499_;
goto v_reusejp_501_;
}
else
{
lean_object* v_reuseFailAlloc_503_; 
v_reuseFailAlloc_503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_503_, 0, v_a_497_);
v___x_502_ = v_reuseFailAlloc_503_;
goto v_reusejp_501_;
}
v_reusejp_501_:
{
return v___x_502_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached___boxed(lean_object* v_specThm_505_, lean_object* v_info_506_, lean_object* v_a_507_, lean_object* v_a_508_, lean_object* v_a_509_, lean_object* v_a_510_, lean_object* v_a_511_, lean_object* v_a_512_, lean_object* v_a_513_, lean_object* v_a_514_, lean_object* v_a_515_, lean_object* v_a_516_, lean_object* v_a_517_, lean_object* v_a_518_){
_start:
{
lean_object* v_res_519_; 
v_res_519_ = l_Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached(v_specThm_505_, v_info_506_, v_a_507_, v_a_508_, v_a_509_, v_a_510_, v_a_511_, v_a_512_, v_a_513_, v_a_514_, v_a_515_, v_a_516_, v_a_517_);
lean_dec(v_a_517_);
lean_dec_ref(v_a_516_);
lean_dec(v_a_515_);
lean_dec_ref(v_a_514_);
lean_dec(v_a_513_);
lean_dec_ref(v_a_512_);
lean_dec(v_a_511_);
lean_dec_ref(v_a_510_);
lean_dec(v_a_509_);
lean_dec(v_a_508_);
lean_dec_ref(v_a_507_);
return v_res_519_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__0(lean_object* v_00_u03b2_520_, lean_object* v_m_521_, lean_object* v_a_522_){
_start:
{
lean_object* v___x_523_; 
v___x_523_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg(v_m_521_, v_a_522_);
return v___x_523_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__0___boxed(lean_object* v_00_u03b2_524_, lean_object* v_m_525_, lean_object* v_a_526_){
_start:
{
lean_object* v_res_527_; 
v_res_527_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__0(v_00_u03b2_524_, v_m_525_, v_a_526_);
lean_dec_ref(v_a_526_);
lean_dec_ref(v_m_525_);
return v_res_527_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2(lean_object* v_00_u03b2_528_, lean_object* v_m_529_, lean_object* v_query_530_){
_start:
{
lean_object* v___x_531_; 
v___x_531_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2___redArg(v_m_529_, v_query_530_);
return v___x_531_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2___boxed(lean_object* v_00_u03b2_532_, lean_object* v_m_533_, lean_object* v_query_534_){
_start:
{
lean_object* v_res_535_; 
v_res_535_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2(v_00_u03b2_532_, v_m_533_, v_query_534_);
lean_dec_ref(v_query_534_);
lean_dec_ref(v_m_533_);
return v_res_535_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__3(lean_object* v_00_u03b2_536_, lean_object* v_m_537_){
_start:
{
lean_object* v___x_538_; 
v___x_538_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__3___redArg(v_m_537_);
return v___x_538_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__3___boxed(lean_object* v_00_u03b2_539_, lean_object* v_m_540_){
_start:
{
lean_object* v_res_541_; 
v_res_541_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__3(v_00_u03b2_539_, v_m_540_);
lean_dec_ref(v_m_540_);
return v_res_541_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__0_spec__0(lean_object* v_00_u03b2_542_, lean_object* v_m_543_, lean_object* v_query_544_){
_start:
{
lean_object* v___x_545_; 
v___x_545_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__0_spec__0___redArg(v_m_543_, v_query_544_);
return v___x_545_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__0_spec__0___boxed(lean_object* v_00_u03b2_546_, lean_object* v_m_547_, lean_object* v_query_548_){
_start:
{
lean_object* v_res_549_; 
v_res_549_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__0_spec__0(v_00_u03b2_546_, v_m_547_, v_query_548_);
lean_dec_ref(v_query_548_);
lean_dec_ref(v_m_547_);
return v_res_549_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__3(lean_object* v_00_u03b2_550_, lean_object* v_m_551_, lean_object* v_query_552_, lean_object* v_x_553_, lean_object* v_x_554_, lean_object* v_x_555_, lean_object* v_x_556_){
_start:
{
lean_object* v___x_557_; 
v___x_557_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__3___redArg(v_m_551_, v_query_552_, v_x_553_, v_x_554_, v_x_555_);
return v___x_557_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__3___boxed(lean_object* v_00_u03b2_558_, lean_object* v_m_559_, lean_object* v_query_560_, lean_object* v_x_561_, lean_object* v_x_562_, lean_object* v_x_563_, lean_object* v_x_564_){
_start:
{
lean_object* v_res_565_; 
v_res_565_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__3(v_00_u03b2_558_, v_m_559_, v_query_560_, v_x_561_, v_x_562_, v_x_563_, v_x_564_);
lean_dec_ref(v_query_560_);
lean_dec_ref(v_m_559_);
return v_res_565_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__3_spec__5(lean_object* v_00_u03b2_566_, lean_object* v_init_567_, lean_object* v_b_568_){
_start:
{
lean_object* v___x_569_; 
v___x_569_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__3_spec__5___redArg(v_init_567_, v_b_568_);
return v___x_569_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__3_spec__5___boxed(lean_object* v_00_u03b2_570_, lean_object* v_init_571_, lean_object* v_b_572_){
_start:
{
lean_object* v_res_573_; 
v_res_573_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__3_spec__5(v_00_u03b2_570_, v_init_571_, v_b_572_);
lean_dec_ref(v_b_572_);
return v_res_573_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__3_spec__5_spec__6(lean_object* v_00_u03b2_574_, lean_object* v_b_575_, lean_object* v_acc_576_, lean_object* v_i_577_){
_start:
{
lean_object* v___x_578_; 
v___x_578_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__3_spec__5_spec__6___redArg(v_b_575_, v_acc_576_, v_i_577_);
return v___x_578_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__3_spec__5_spec__6___boxed(lean_object* v_00_u03b2_579_, lean_object* v_b_580_, lean_object* v_acc_581_, lean_object* v_i_582_){
_start:
{
lean_object* v_res_583_; 
v_res_583_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__3_spec__5_spec__6(v_00_u03b2_579_, v_b_580_, v_acc_581_, v_i_582_);
lean_dec_ref(v_b_580_);
return v_res_583_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_mkBackwardRuleForSplitCached___redArg(lean_object* v_splitInfo_593_, lean_object* v_info_594_, lean_object* v_a_595_, lean_object* v_a_596_, lean_object* v_a_597_, lean_object* v_a_598_, lean_object* v_a_599_, lean_object* v_a_600_, lean_object* v_a_601_){
_start:
{
lean_object* v___y_604_; lean_object* v___y_605_; lean_object* v___y_606_; lean_object* v___y_607_; lean_object* v___y_608_; lean_object* v___y_609_; lean_object* v___y_610_; lean_object* v___y_611_; lean_object* v___y_612_; lean_object* v___y_613_; lean_object* v___y_614_; lean_object* v___y_619_; lean_object* v___y_620_; lean_object* v___y_621_; lean_object* v___y_622_; lean_object* v___y_623_; lean_object* v___y_624_; lean_object* v___y_625_; lean_object* v___y_626_; lean_object* v___y_627_; lean_object* v___y_628_; lean_object* v___y_629_; lean_object* v___y_630_; lean_object* v_i_631_; lean_object* v___y_637_; lean_object* v___y_638_; lean_object* v___y_639_; lean_object* v___y_640_; lean_object* v___y_641_; lean_object* v___y_642_; lean_object* v___y_643_; lean_object* v___y_644_; lean_object* v___y_645_; lean_object* v___y_646_; lean_object* v___y_647_; lean_object* v___y_648_; lean_object* v___y_658_; lean_object* v___y_659_; lean_object* v___y_660_; lean_object* v___y_661_; lean_object* v___y_662_; lean_object* v___y_663_; lean_object* v___y_664_; lean_object* v___y_665_; lean_object* v___y_666_; lean_object* v___y_667_; lean_object* v___y_668_; lean_object* v___y_669_; lean_object* v_i_670_; lean_object* v___y_676_; lean_object* v___y_677_; lean_object* v___y_678_; lean_object* v___y_679_; lean_object* v___y_680_; lean_object* v___y_681_; lean_object* v___y_682_; lean_object* v___y_683_; lean_object* v___y_684_; lean_object* v___y_685_; lean_object* v___y_686_; lean_object* v___y_687_; lean_object* v___y_698_; 
switch(lean_obj_tag(v_splitInfo_593_))
{
case 0:
{
lean_object* v___x_760_; 
v___x_760_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_mkBackwardRuleForSplitCached___redArg___closed__1));
v___y_698_ = v___x_760_;
goto v___jp_697_;
}
case 1:
{
lean_object* v___x_761_; 
v___x_761_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_mkBackwardRuleForSplitCached___redArg___closed__3));
v___y_698_ = v___x_761_;
goto v___jp_697_;
}
case 2:
{
lean_object* v___x_762_; 
v___x_762_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_mkBackwardRuleForSplitCached___redArg___closed__5));
v___y_698_ = v___x_762_;
goto v___jp_697_;
}
default: 
{
lean_object* v_matcherApp_763_; lean_object* v_matcherName_764_; 
v_matcherApp_763_ = lean_ctor_get(v_splitInfo_593_, 0);
v_matcherName_764_ = lean_ctor_get(v_matcherApp_763_, 1);
lean_inc(v_matcherName_764_);
v___y_698_ = v_matcherName_764_;
goto v___jp_697_;
}
}
v___jp_603_:
{
lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; 
v___x_615_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_615_, 0, v___y_607_);
lean_ctor_set(v___x_615_, 1, v___y_614_);
lean_ctor_set(v___x_615_, 2, v___y_608_);
lean_ctor_set(v___x_615_, 3, v___y_609_);
lean_ctor_set(v___x_615_, 4, v___y_606_);
lean_ctor_set(v___x_615_, 5, v___y_604_);
lean_ctor_set(v___x_615_, 6, v___y_605_);
lean_ctor_set(v___x_615_, 7, v___y_612_);
lean_ctor_set(v___x_615_, 8, v___y_613_);
lean_ctor_set(v___x_615_, 9, v___y_611_);
v___x_616_ = lean_st_ref_put(v_a_595_, v___x_615_);
v___x_617_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_617_, 0, v___y_610_);
return v___x_617_;
}
v___jp_618_:
{
lean_object* v_size_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; 
v_size_632_ = lean_ctor_get(v___y_626_, 0);
v___x_633_ = lean_unsigned_to_nat(1u);
v___x_634_ = lean_nat_add(v_size_632_, v___x_633_);
lean_inc_ref(v___y_623_);
v___x_635_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_626_, v___x_634_, v_i_631_, v___y_620_, v___y_623_);
lean_dec(v_i_631_);
v___y_604_ = v___y_619_;
v___y_605_ = v___y_624_;
v___y_606_ = v___y_625_;
v___y_607_ = v___y_621_;
v___y_608_ = v___y_622_;
v___y_609_ = v___y_627_;
v___y_610_ = v___y_623_;
v___y_611_ = v___y_628_;
v___y_612_ = v___y_629_;
v___y_613_ = v___y_630_;
v___y_614_ = v___x_635_;
goto v___jp_603_;
}
v___jp_636_:
{
lean_object* v___x_649_; 
v___x_649_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2___redArg(v___y_648_, v___y_639_);
switch(lean_obj_tag(v___x_649_))
{
case 0:
{
lean_object* v_index_650_; lean_object* v_size_651_; lean_object* v___x_652_; 
v_index_650_ = lean_ctor_get(v___x_649_, 0);
lean_inc(v_index_650_);
lean_dec_ref_known(v___x_649_, 3);
v_size_651_ = lean_ctor_get(v___y_648_, 0);
lean_inc(v_size_651_);
lean_inc_ref(v___y_643_);
v___x_652_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_648_, v_size_651_, v_index_650_, v___y_639_, v___y_643_);
lean_dec(v_index_650_);
v___y_604_ = v___y_637_;
v___y_605_ = v___y_638_;
v___y_606_ = v___y_640_;
v___y_607_ = v___y_641_;
v___y_608_ = v___y_642_;
v___y_609_ = v___y_644_;
v___y_610_ = v___y_643_;
v___y_611_ = v___y_645_;
v___y_612_ = v___y_646_;
v___y_613_ = v___y_647_;
v___y_614_ = v___x_652_;
goto v___jp_603_;
}
case 1:
{
lean_object* v_index_653_; 
v_index_653_ = lean_ctor_get(v___x_649_, 0);
lean_inc(v_index_653_);
lean_dec_ref_known(v___x_649_, 1);
v___y_619_ = v___y_637_;
v___y_620_ = v___y_639_;
v___y_621_ = v___y_641_;
v___y_622_ = v___y_642_;
v___y_623_ = v___y_643_;
v___y_624_ = v___y_638_;
v___y_625_ = v___y_640_;
v___y_626_ = v___y_648_;
v___y_627_ = v___y_644_;
v___y_628_ = v___y_645_;
v___y_629_ = v___y_646_;
v___y_630_ = v___y_647_;
v_i_631_ = v_index_653_;
goto v___jp_618_;
}
default: 
{
lean_object* v___x_654_; lean_object* v___x_655_; 
v___x_654_ = lean_unsigned_to_nat(0u);
v___x_655_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_648_, v___x_654_);
if (lean_obj_tag(v___x_655_) == 0)
{
lean_object* v_index_656_; 
v_index_656_ = lean_ctor_get(v___x_655_, 0);
lean_inc(v_index_656_);
lean_dec_ref_known(v___x_655_, 1);
v___y_619_ = v___y_637_;
v___y_620_ = v___y_639_;
v___y_621_ = v___y_641_;
v___y_622_ = v___y_642_;
v___y_623_ = v___y_643_;
v___y_624_ = v___y_638_;
v___y_625_ = v___y_640_;
v___y_626_ = v___y_648_;
v___y_627_ = v___y_644_;
v___y_628_ = v___y_645_;
v___y_629_ = v___y_646_;
v___y_630_ = v___y_647_;
v_i_631_ = v_index_656_;
goto v___jp_618_;
}
else
{
lean_dec_ref(v___y_639_);
v___y_604_ = v___y_637_;
v___y_605_ = v___y_638_;
v___y_606_ = v___y_640_;
v___y_607_ = v___y_641_;
v___y_608_ = v___y_642_;
v___y_609_ = v___y_644_;
v___y_610_ = v___y_643_;
v___y_611_ = v___y_645_;
v___y_612_ = v___y_646_;
v___y_613_ = v___y_647_;
v___y_614_ = v___y_648_;
goto v___jp_603_;
}
}
}
}
v___jp_657_:
{
lean_object* v_size_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; 
v_size_671_ = lean_ctor_get(v___y_663_, 0);
v___x_672_ = lean_unsigned_to_nat(1u);
v___x_673_ = lean_nat_add(v_size_671_, v___x_672_);
lean_inc_ref(v___y_662_);
v___x_674_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_663_, v___x_673_, v_i_670_, v___y_659_, v___y_662_);
lean_dec(v_i_670_);
v___y_604_ = v___y_658_;
v___y_605_ = v___y_664_;
v___y_606_ = v___y_665_;
v___y_607_ = v___y_660_;
v___y_608_ = v___y_661_;
v___y_609_ = v___y_666_;
v___y_610_ = v___y_662_;
v___y_611_ = v___y_667_;
v___y_612_ = v___y_668_;
v___y_613_ = v___y_669_;
v___y_614_ = v___x_674_;
goto v___jp_603_;
}
v___jp_675_:
{
lean_object* v___x_688_; lean_object* v___x_689_; 
v___x_688_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__3___redArg(v___y_678_);
lean_dec_ref(v___y_678_);
v___x_689_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2___redArg(v___x_688_, v___y_677_);
switch(lean_obj_tag(v___x_689_))
{
case 0:
{
lean_object* v_index_690_; lean_object* v_size_691_; lean_object* v___x_692_; 
v_index_690_ = lean_ctor_get(v___x_689_, 0);
lean_inc(v_index_690_);
lean_dec_ref_known(v___x_689_, 3);
v_size_691_ = lean_ctor_get(v___x_688_, 0);
lean_inc(v_size_691_);
lean_inc_ref(v___y_681_);
v___x_692_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_688_, v_size_691_, v_index_690_, v___y_677_, v___y_681_);
lean_dec(v_index_690_);
v___y_604_ = v___y_676_;
v___y_605_ = v___y_682_;
v___y_606_ = v___y_683_;
v___y_607_ = v___y_679_;
v___y_608_ = v___y_680_;
v___y_609_ = v___y_684_;
v___y_610_ = v___y_681_;
v___y_611_ = v___y_685_;
v___y_612_ = v___y_686_;
v___y_613_ = v___y_687_;
v___y_614_ = v___x_692_;
goto v___jp_603_;
}
case 1:
{
lean_object* v_index_693_; 
v_index_693_ = lean_ctor_get(v___x_689_, 0);
lean_inc(v_index_693_);
lean_dec_ref_known(v___x_689_, 1);
v___y_658_ = v___y_676_;
v___y_659_ = v___y_677_;
v___y_660_ = v___y_679_;
v___y_661_ = v___y_680_;
v___y_662_ = v___y_681_;
v___y_663_ = v___x_688_;
v___y_664_ = v___y_682_;
v___y_665_ = v___y_683_;
v___y_666_ = v___y_684_;
v___y_667_ = v___y_685_;
v___y_668_ = v___y_686_;
v___y_669_ = v___y_687_;
v_i_670_ = v_index_693_;
goto v___jp_657_;
}
default: 
{
lean_object* v___x_694_; lean_object* v___x_695_; 
v___x_694_ = lean_unsigned_to_nat(0u);
v___x_695_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_688_, v___x_694_);
if (lean_obj_tag(v___x_695_) == 0)
{
lean_object* v_index_696_; 
v_index_696_ = lean_ctor_get(v___x_695_, 0);
lean_inc(v_index_696_);
lean_dec_ref_known(v___x_695_, 1);
v___y_658_ = v___y_676_;
v___y_659_ = v___y_677_;
v___y_660_ = v___y_679_;
v___y_661_ = v___y_680_;
v___y_662_ = v___y_681_;
v___y_663_ = v___x_688_;
v___y_664_ = v___y_682_;
v___y_665_ = v___y_683_;
v___y_666_ = v___y_684_;
v___y_667_ = v___y_685_;
v___y_668_ = v___y_686_;
v___y_669_ = v___y_687_;
v_i_670_ = v_index_696_;
goto v___jp_657_;
}
else
{
lean_dec_ref(v___y_677_);
v___y_604_ = v___y_676_;
v___y_605_ = v___y_682_;
v___y_606_ = v___y_683_;
v___y_607_ = v___y_679_;
v___y_608_ = v___y_680_;
v___y_609_ = v___y_684_;
v___y_610_ = v___y_681_;
v___y_611_ = v___y_685_;
v___y_612_ = v___y_686_;
v___y_613_ = v___y_687_;
v___y_614_ = v___x_688_;
goto v___jp_603_;
}
}
}
}
v___jp_697_:
{
lean_object* v___x_699_; lean_object* v_excessArgs_700_; lean_object* v_splitBackwardRuleCache_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v_key_705_; lean_object* v___x_706_; 
v___x_699_ = lean_st_ref_get(v_a_595_);
v_excessArgs_700_ = lean_ctor_get(v_info_594_, 2);
v_splitBackwardRuleCache_701_ = lean_ctor_get(v___x_699_, 1);
lean_inc_ref(v_splitBackwardRuleCache_701_);
lean_dec(v___x_699_);
v___x_702_ = l_Lean_Elab_Tactic_VCGen_WPApp_instWP(v_info_594_);
v___x_703_ = lean_array_get_size(v_excessArgs_700_);
v___x_704_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_704_, 0, v___x_702_);
lean_ctor_set(v___x_704_, 1, v___x_703_);
v_key_705_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_key_705_, 0, v___y_698_);
lean_ctor_set(v_key_705_, 1, v___x_704_);
v___x_706_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg(v_splitBackwardRuleCache_701_, v_key_705_);
lean_dec_ref(v_splitBackwardRuleCache_701_);
if (lean_obj_tag(v___x_706_) == 1)
{
lean_object* v_val_707_; lean_object* v___x_709_; uint8_t v_isShared_710_; uint8_t v_isSharedCheck_714_; 
lean_dec_ref_known(v_key_705_, 2);
lean_dec_ref(v_info_594_);
lean_dec_ref(v_splitInfo_593_);
v_val_707_ = lean_ctor_get(v___x_706_, 0);
v_isSharedCheck_714_ = !lean_is_exclusive(v___x_706_);
if (v_isSharedCheck_714_ == 0)
{
v___x_709_ = v___x_706_;
v_isShared_710_ = v_isSharedCheck_714_;
goto v_resetjp_708_;
}
else
{
lean_inc(v_val_707_);
lean_dec(v___x_706_);
v___x_709_ = lean_box(0);
v_isShared_710_ = v_isSharedCheck_714_;
goto v_resetjp_708_;
}
v_resetjp_708_:
{
lean_object* v___x_712_; 
if (v_isShared_710_ == 0)
{
lean_ctor_set_tag(v___x_709_, 0);
v___x_712_ = v___x_709_;
goto v_reusejp_711_;
}
else
{
lean_object* v_reuseFailAlloc_713_; 
v_reuseFailAlloc_713_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_713_, 0, v_val_707_);
v___x_712_ = v_reuseFailAlloc_713_;
goto v_reusejp_711_;
}
v_reusejp_711_:
{
return v___x_712_;
}
}
}
else
{
lean_object* v___x_715_; 
lean_dec(v___x_706_);
v___x_715_ = l_Lean_Elab_Tactic_VCGen_mkBackwardRuleForSplit(v_splitInfo_593_, v_info_594_, v_a_598_, v_a_599_, v_a_600_, v_a_601_);
if (lean_obj_tag(v___x_715_) == 0)
{
lean_object* v_a_716_; lean_object* v___x_717_; 
v_a_716_ = lean_ctor_get(v___x_715_, 0);
lean_inc(v_a_716_);
lean_dec_ref_known(v___x_715_, 1);
v___x_717_ = l_Lean_Meta_Sym_BackwardRule_shareCommon(v_a_716_, v_a_596_, v_a_597_, v_a_598_, v_a_599_, v_a_600_, v_a_601_);
if (lean_obj_tag(v___x_717_) == 0)
{
lean_object* v_a_718_; lean_object* v___x_719_; lean_object* v_specBackwardRuleCache_720_; lean_object* v_splitBackwardRuleCache_721_; lean_object* v_latticeBackwardRuleCache_722_; lean_object* v_frameBackwardRuleCache_723_; lean_object* v_frameDB_724_; lean_object* v_invariants_725_; lean_object* v_vcs_726_; lean_object* v_simpState_727_; lean_object* v_fuel_728_; lean_object* v_inlineHandledInvariants_729_; lean_object* v___x_730_; 
v_a_718_ = lean_ctor_get(v___x_717_, 0);
lean_inc(v_a_718_);
lean_dec_ref_known(v___x_717_, 1);
v___x_719_ = lean_st_ref_take(v_a_595_);
v_specBackwardRuleCache_720_ = lean_ctor_get(v___x_719_, 0);
lean_inc_ref(v_specBackwardRuleCache_720_);
v_splitBackwardRuleCache_721_ = lean_ctor_get(v___x_719_, 1);
lean_inc_ref(v_splitBackwardRuleCache_721_);
v_latticeBackwardRuleCache_722_ = lean_ctor_get(v___x_719_, 2);
lean_inc_ref(v_latticeBackwardRuleCache_722_);
v_frameBackwardRuleCache_723_ = lean_ctor_get(v___x_719_, 3);
lean_inc_ref(v_frameBackwardRuleCache_723_);
v_frameDB_724_ = lean_ctor_get(v___x_719_, 4);
lean_inc_ref(v_frameDB_724_);
v_invariants_725_ = lean_ctor_get(v___x_719_, 5);
lean_inc_ref(v_invariants_725_);
v_vcs_726_ = lean_ctor_get(v___x_719_, 6);
lean_inc_ref(v_vcs_726_);
v_simpState_727_ = lean_ctor_get(v___x_719_, 7);
lean_inc_ref(v_simpState_727_);
v_fuel_728_ = lean_ctor_get(v___x_719_, 8);
lean_inc(v_fuel_728_);
v_inlineHandledInvariants_729_ = lean_ctor_get(v___x_719_, 9);
lean_inc_ref(v_inlineHandledInvariants_729_);
lean_dec(v___x_719_);
v___x_730_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__2___redArg(v_splitBackwardRuleCache_721_, v_key_705_);
switch(lean_obj_tag(v___x_730_))
{
case 0:
{
lean_object* v_index_731_; lean_object* v_size_732_; lean_object* v___x_733_; 
v_index_731_ = lean_ctor_get(v___x_730_, 0);
lean_inc(v_index_731_);
lean_dec_ref_known(v___x_730_, 3);
v_size_732_ = lean_ctor_get(v_splitBackwardRuleCache_721_, 0);
lean_inc(v_size_732_);
lean_inc(v_a_718_);
v___x_733_ = l_Std_DHashMap_Raw_setEntry___redArg(v_splitBackwardRuleCache_721_, v_size_732_, v_index_731_, v_key_705_, v_a_718_);
lean_dec(v_index_731_);
v___y_604_ = v_invariants_725_;
v___y_605_ = v_vcs_726_;
v___y_606_ = v_frameDB_724_;
v___y_607_ = v_specBackwardRuleCache_720_;
v___y_608_ = v_latticeBackwardRuleCache_722_;
v___y_609_ = v_frameBackwardRuleCache_723_;
v___y_610_ = v_a_718_;
v___y_611_ = v_inlineHandledInvariants_729_;
v___y_612_ = v_simpState_727_;
v___y_613_ = v_fuel_728_;
v___y_614_ = v___x_733_;
goto v___jp_603_;
}
case 1:
{
lean_object* v_index_734_; lean_object* v_size_735_; lean_object* v_keyArray_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; uint8_t v___x_740_; 
v_index_734_ = lean_ctor_get(v___x_730_, 0);
lean_inc(v_index_734_);
lean_dec_ref_known(v___x_730_, 1);
v_size_735_ = lean_ctor_get(v_splitBackwardRuleCache_721_, 0);
v_keyArray_736_ = lean_ctor_get(v_splitBackwardRuleCache_721_, 1);
v___x_737_ = lean_unsigned_to_nat(1u);
v___x_738_ = lean_nat_add(v_size_735_, v___x_737_);
v___x_739_ = lean_array_get_size(v_keyArray_736_);
v___x_740_ = lean_nat_dec_lt(v___x_738_, v___x_739_);
if (v___x_740_ == 0)
{
lean_dec(v___x_738_);
lean_dec(v_index_734_);
v___y_676_ = v_invariants_725_;
v___y_677_ = v_key_705_;
v___y_678_ = v_splitBackwardRuleCache_721_;
v___y_679_ = v_specBackwardRuleCache_720_;
v___y_680_ = v_latticeBackwardRuleCache_722_;
v___y_681_ = v_a_718_;
v___y_682_ = v_vcs_726_;
v___y_683_ = v_frameDB_724_;
v___y_684_ = v_frameBackwardRuleCache_723_;
v___y_685_ = v_inlineHandledInvariants_729_;
v___y_686_ = v_simpState_727_;
v___y_687_ = v_fuel_728_;
goto v___jp_675_;
}
else
{
lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; uint8_t v___x_745_; 
v___x_741_ = lean_unsigned_to_nat(4u);
v___x_742_ = lean_nat_mul(v___x_738_, v___x_741_);
v___x_743_ = lean_unsigned_to_nat(3u);
v___x_744_ = lean_nat_mul(v___x_739_, v___x_743_);
v___x_745_ = lean_nat_dec_le(v___x_742_, v___x_744_);
lean_dec(v___x_744_);
lean_dec(v___x_742_);
if (v___x_745_ == 0)
{
lean_dec(v___x_738_);
lean_dec(v_index_734_);
v___y_676_ = v_invariants_725_;
v___y_677_ = v_key_705_;
v___y_678_ = v_splitBackwardRuleCache_721_;
v___y_679_ = v_specBackwardRuleCache_720_;
v___y_680_ = v_latticeBackwardRuleCache_722_;
v___y_681_ = v_a_718_;
v___y_682_ = v_vcs_726_;
v___y_683_ = v_frameDB_724_;
v___y_684_ = v_frameBackwardRuleCache_723_;
v___y_685_ = v_inlineHandledInvariants_729_;
v___y_686_ = v_simpState_727_;
v___y_687_ = v_fuel_728_;
goto v___jp_675_;
}
else
{
lean_object* v___x_746_; 
lean_inc(v_a_718_);
v___x_746_ = l_Std_DHashMap_Raw_setEntry___redArg(v_splitBackwardRuleCache_721_, v___x_738_, v_index_734_, v_key_705_, v_a_718_);
lean_dec(v_index_734_);
v___y_604_ = v_invariants_725_;
v___y_605_ = v_vcs_726_;
v___y_606_ = v_frameDB_724_;
v___y_607_ = v_specBackwardRuleCache_720_;
v___y_608_ = v_latticeBackwardRuleCache_722_;
v___y_609_ = v_frameBackwardRuleCache_723_;
v___y_610_ = v_a_718_;
v___y_611_ = v_inlineHandledInvariants_729_;
v___y_612_ = v_simpState_727_;
v___y_613_ = v_fuel_728_;
v___y_614_ = v___x_746_;
goto v___jp_603_;
}
}
}
default: 
{
lean_object* v_size_747_; lean_object* v_keyArray_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; uint8_t v___x_752_; 
v_size_747_ = lean_ctor_get(v_splitBackwardRuleCache_721_, 0);
v_keyArray_748_ = lean_ctor_get(v_splitBackwardRuleCache_721_, 1);
v___x_749_ = lean_unsigned_to_nat(1u);
v___x_750_ = lean_nat_add(v_size_747_, v___x_749_);
v___x_751_ = lean_array_get_size(v_keyArray_748_);
v___x_752_ = lean_nat_dec_lt(v___x_750_, v___x_751_);
if (v___x_752_ == 0)
{
lean_object* v___x_753_; 
lean_dec(v___x_750_);
v___x_753_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__3___redArg(v_splitBackwardRuleCache_721_);
lean_dec_ref(v_splitBackwardRuleCache_721_);
v___y_637_ = v_invariants_725_;
v___y_638_ = v_vcs_726_;
v___y_639_ = v_key_705_;
v___y_640_ = v_frameDB_724_;
v___y_641_ = v_specBackwardRuleCache_720_;
v___y_642_ = v_latticeBackwardRuleCache_722_;
v___y_643_ = v_a_718_;
v___y_644_ = v_frameBackwardRuleCache_723_;
v___y_645_ = v_inlineHandledInvariants_729_;
v___y_646_ = v_simpState_727_;
v___y_647_ = v_fuel_728_;
v___y_648_ = v___x_753_;
goto v___jp_636_;
}
else
{
lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; uint8_t v___x_758_; 
v___x_754_ = lean_unsigned_to_nat(4u);
v___x_755_ = lean_nat_mul(v___x_750_, v___x_754_);
lean_dec(v___x_750_);
v___x_756_ = lean_unsigned_to_nat(3u);
v___x_757_ = lean_nat_mul(v___x_751_, v___x_756_);
v___x_758_ = lean_nat_dec_le(v___x_755_, v___x_757_);
lean_dec(v___x_757_);
lean_dec(v___x_755_);
if (v___x_758_ == 0)
{
lean_object* v___x_759_; 
v___x_759_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_VCGen_mkBackwardRuleFromSpecCached_spec__3___redArg(v_splitBackwardRuleCache_721_);
lean_dec_ref(v_splitBackwardRuleCache_721_);
v___y_637_ = v_invariants_725_;
v___y_638_ = v_vcs_726_;
v___y_639_ = v_key_705_;
v___y_640_ = v_frameDB_724_;
v___y_641_ = v_specBackwardRuleCache_720_;
v___y_642_ = v_latticeBackwardRuleCache_722_;
v___y_643_ = v_a_718_;
v___y_644_ = v_frameBackwardRuleCache_723_;
v___y_645_ = v_inlineHandledInvariants_729_;
v___y_646_ = v_simpState_727_;
v___y_647_ = v_fuel_728_;
v___y_648_ = v___x_759_;
goto v___jp_636_;
}
else
{
v___y_637_ = v_invariants_725_;
v___y_638_ = v_vcs_726_;
v___y_639_ = v_key_705_;
v___y_640_ = v_frameDB_724_;
v___y_641_ = v_specBackwardRuleCache_720_;
v___y_642_ = v_latticeBackwardRuleCache_722_;
v___y_643_ = v_a_718_;
v___y_644_ = v_frameBackwardRuleCache_723_;
v___y_645_ = v_inlineHandledInvariants_729_;
v___y_646_ = v_simpState_727_;
v___y_647_ = v_fuel_728_;
v___y_648_ = v_splitBackwardRuleCache_721_;
goto v___jp_636_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_key_705_, 2);
return v___x_717_;
}
}
else
{
lean_dec_ref_known(v_key_705_, 2);
return v___x_715_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_mkBackwardRuleForSplitCached___redArg___boxed(lean_object* v_splitInfo_765_, lean_object* v_info_766_, lean_object* v_a_767_, lean_object* v_a_768_, lean_object* v_a_769_, lean_object* v_a_770_, lean_object* v_a_771_, lean_object* v_a_772_, lean_object* v_a_773_, lean_object* v_a_774_){
_start:
{
lean_object* v_res_775_; 
v_res_775_ = l_Lean_Elab_Tactic_VCGen_mkBackwardRuleForSplitCached___redArg(v_splitInfo_765_, v_info_766_, v_a_767_, v_a_768_, v_a_769_, v_a_770_, v_a_771_, v_a_772_, v_a_773_);
lean_dec(v_a_773_);
lean_dec_ref(v_a_772_);
lean_dec(v_a_771_);
lean_dec_ref(v_a_770_);
lean_dec(v_a_769_);
lean_dec_ref(v_a_768_);
lean_dec(v_a_767_);
return v_res_775_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_mkBackwardRuleForSplitCached(lean_object* v_splitInfo_776_, lean_object* v_info_777_, lean_object* v_a_778_, lean_object* v_a_779_, lean_object* v_a_780_, lean_object* v_a_781_, lean_object* v_a_782_, lean_object* v_a_783_, lean_object* v_a_784_, lean_object* v_a_785_, lean_object* v_a_786_, lean_object* v_a_787_, lean_object* v_a_788_){
_start:
{
lean_object* v___x_790_; 
v___x_790_ = l_Lean_Elab_Tactic_VCGen_mkBackwardRuleForSplitCached___redArg(v_splitInfo_776_, v_info_777_, v_a_779_, v_a_783_, v_a_784_, v_a_785_, v_a_786_, v_a_787_, v_a_788_);
return v___x_790_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_mkBackwardRuleForSplitCached___boxed(lean_object* v_splitInfo_791_, lean_object* v_info_792_, lean_object* v_a_793_, lean_object* v_a_794_, lean_object* v_a_795_, lean_object* v_a_796_, lean_object* v_a_797_, lean_object* v_a_798_, lean_object* v_a_799_, lean_object* v_a_800_, lean_object* v_a_801_, lean_object* v_a_802_, lean_object* v_a_803_, lean_object* v_a_804_){
_start:
{
lean_object* v_res_805_; 
v_res_805_ = l_Lean_Elab_Tactic_VCGen_mkBackwardRuleForSplitCached(v_splitInfo_791_, v_info_792_, v_a_793_, v_a_794_, v_a_795_, v_a_796_, v_a_797_, v_a_798_, v_a_799_, v_a_800_, v_a_801_, v_a_802_, v_a_803_);
lean_dec(v_a_803_);
lean_dec_ref(v_a_802_);
lean_dec(v_a_801_);
lean_dec_ref(v_a_800_);
lean_dec(v_a_799_);
lean_dec_ref(v_a_798_);
lean_dec(v_a_797_);
lean_dec_ref(v_a_796_);
lean_dec(v_a_795_);
lean_dec(v_a_794_);
lean_dec_ref(v_a_793_);
return v_res_805_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1_spec__2___redArg(lean_object* v_m_806_, lean_object* v_query_807_, lean_object* v_x_808_, lean_object* v_x_809_, lean_object* v_x_810_){
_start:
{
lean_object* v_zero_811_; uint8_t v_isZero_812_; 
v_zero_811_ = lean_unsigned_to_nat(0u);
v_isZero_812_ = lean_nat_dec_eq(v_x_809_, v_zero_811_);
if (v_isZero_812_ == 1)
{
lean_dec(v_x_810_);
lean_dec(v_x_809_);
if (lean_obj_tag(v_x_808_) == 0)
{
lean_object* v___x_813_; 
v___x_813_ = lean_box(2);
return v___x_813_;
}
else
{
lean_object* v_val_814_; lean_object* v___x_816_; uint8_t v_isShared_817_; uint8_t v_isSharedCheck_821_; 
v_val_814_ = lean_ctor_get(v_x_808_, 0);
v_isSharedCheck_821_ = !lean_is_exclusive(v_x_808_);
if (v_isSharedCheck_821_ == 0)
{
v___x_816_ = v_x_808_;
v_isShared_817_ = v_isSharedCheck_821_;
goto v_resetjp_815_;
}
else
{
lean_inc(v_val_814_);
lean_dec(v_x_808_);
v___x_816_ = lean_box(0);
v_isShared_817_ = v_isSharedCheck_821_;
goto v_resetjp_815_;
}
v_resetjp_815_:
{
lean_object* v___x_819_; 
if (v_isShared_817_ == 0)
{
v___x_819_ = v___x_816_;
goto v_reusejp_818_;
}
else
{
lean_object* v_reuseFailAlloc_820_; 
v_reuseFailAlloc_820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_820_, 0, v_val_814_);
v___x_819_ = v_reuseFailAlloc_820_;
goto v_reusejp_818_;
}
v_reusejp_818_:
{
return v___x_819_;
}
}
}
}
else
{
lean_object* v_keyArray_822_; lean_object* v_valueArray_823_; lean_object* v___x_824_; uint8_t v_isSome_825_; 
v_keyArray_822_ = lean_ctor_get(v_m_806_, 1);
v_valueArray_823_ = lean_ctor_get(v_m_806_, 2);
v___x_824_ = lean_array_fget_borrowed(v_keyArray_822_, v_x_810_);
v_isSome_825_ = lean_noption_is_some(v___x_824_);
if (v_isSome_825_ == 0)
{
lean_dec(v_x_809_);
if (lean_obj_tag(v_x_808_) == 0)
{
lean_object* v___x_826_; 
v___x_826_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_826_, 0, v_x_810_);
return v___x_826_;
}
else
{
lean_object* v_val_827_; lean_object* v___x_829_; uint8_t v_isShared_830_; uint8_t v_isSharedCheck_834_; 
lean_dec(v_x_810_);
v_val_827_ = lean_ctor_get(v_x_808_, 0);
v_isSharedCheck_834_ = !lean_is_exclusive(v_x_808_);
if (v_isSharedCheck_834_ == 0)
{
v___x_829_ = v_x_808_;
v_isShared_830_ = v_isSharedCheck_834_;
goto v_resetjp_828_;
}
else
{
lean_inc(v_val_827_);
lean_dec(v_x_808_);
v___x_829_ = lean_box(0);
v_isShared_830_ = v_isSharedCheck_834_;
goto v_resetjp_828_;
}
v_resetjp_828_:
{
lean_object* v___x_832_; 
if (v_isShared_830_ == 0)
{
v___x_832_ = v___x_829_;
goto v_reusejp_831_;
}
else
{
lean_object* v_reuseFailAlloc_833_; 
v_reuseFailAlloc_833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_833_, 0, v_val_827_);
v___x_832_ = v_reuseFailAlloc_833_;
goto v_reusejp_831_;
}
v_reusejp_831_:
{
return v___x_832_;
}
}
}
}
else
{
lean_object* v_one_835_; lean_object* v_n_836_; lean_object* v___y_838_; 
v_one_835_ = lean_unsigned_to_nat(1u);
v_n_836_ = lean_nat_sub(v_x_809_, v_one_835_);
lean_dec(v_x_809_);
if (v_isSome_825_ == 0)
{
goto v___jp_844_;
}
else
{
lean_object* v___x_846_; uint8_t v_isSome_847_; 
v___x_846_ = lean_array_fget_borrowed(v_valueArray_823_, v_x_810_);
v_isSome_847_ = lean_noption_is_some(v___x_846_);
if (v_isSome_847_ == 0)
{
goto v___jp_844_;
}
else
{
lean_object* v_val_848_; lean_object* v_fst_849_; lean_object* v_snd_850_; lean_object* v_fst_851_; lean_object* v_snd_852_; lean_object* v_val_853_; uint8_t v___y_855_; size_t v___x_862_; size_t v___x_863_; uint8_t v___x_864_; 
lean_inc(v___x_824_);
v_val_848_ = lean_noption_get(v___x_824_);
v_fst_849_ = lean_ctor_get(v_val_848_, 0);
lean_inc(v_fst_849_);
v_snd_850_ = lean_ctor_get(v_val_848_, 1);
lean_inc(v_snd_850_);
v_fst_851_ = lean_ctor_get(v_query_807_, 0);
v_snd_852_ = lean_ctor_get(v_query_807_, 1);
lean_inc(v___x_846_);
v_val_853_ = lean_noption_get(v___x_846_);
v___x_862_ = lean_ptr_addr(v_fst_849_);
lean_dec(v_fst_849_);
v___x_863_ = lean_ptr_addr(v_fst_851_);
v___x_864_ = lean_usize_dec_eq(v___x_862_, v___x_863_);
if (v___x_864_ == 0)
{
lean_dec(v_snd_850_);
v___y_855_ = v___x_864_;
goto v___jp_854_;
}
else
{
uint8_t v___x_865_; 
v___x_865_ = lean_nat_dec_eq(v_snd_850_, v_snd_852_);
lean_dec(v_snd_850_);
v___y_855_ = v___x_865_;
goto v___jp_854_;
}
v___jp_854_:
{
if (v___y_855_ == 0)
{
lean_object* v___x_856_; lean_object* v___x_857_; uint8_t v___x_858_; 
lean_dec(v_val_853_);
lean_dec(v_val_848_);
v___x_856_ = lean_array_get_size(v_keyArray_822_);
v___x_857_ = lean_nat_add(v_x_810_, v_one_835_);
lean_dec(v_x_810_);
v___x_858_ = lean_nat_dec_lt(v___x_857_, v___x_856_);
if (v___x_858_ == 0)
{
lean_dec(v___x_857_);
v_x_809_ = v_n_836_;
v_x_810_ = v_zero_811_;
goto _start;
}
else
{
v_x_809_ = v_n_836_;
v_x_810_ = v___x_857_;
goto _start;
}
}
else
{
lean_object* v___x_861_; 
lean_dec(v_n_836_);
lean_dec(v_x_808_);
v___x_861_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_861_, 0, v_x_810_);
lean_ctor_set(v___x_861_, 1, v_val_848_);
lean_ctor_set(v___x_861_, 2, v_val_853_);
return v___x_861_;
}
}
}
}
v___jp_837_:
{
lean_object* v___x_839_; lean_object* v___x_840_; uint8_t v___x_841_; 
v___x_839_ = lean_array_get_size(v_keyArray_822_);
v___x_840_ = lean_nat_add(v_x_810_, v_one_835_);
lean_dec(v_x_810_);
v___x_841_ = lean_nat_dec_lt(v___x_840_, v___x_839_);
if (v___x_841_ == 0)
{
lean_dec(v___x_840_);
v_x_808_ = v___y_838_;
v_x_809_ = v_n_836_;
v_x_810_ = v_zero_811_;
goto _start;
}
else
{
v_x_808_ = v___y_838_;
v_x_809_ = v_n_836_;
v_x_810_ = v___x_840_;
goto _start;
}
}
v___jp_844_:
{
if (lean_obj_tag(v_x_808_) == 0)
{
lean_object* v___x_845_; 
lean_inc(v_x_810_);
v___x_845_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_845_, 0, v_x_810_);
v___y_838_ = v___x_845_;
goto v___jp_837_;
}
else
{
v___y_838_ = v_x_808_;
goto v___jp_837_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1_spec__2___redArg___boxed(lean_object* v_m_866_, lean_object* v_query_867_, lean_object* v_x_868_, lean_object* v_x_869_, lean_object* v_x_870_){
_start:
{
lean_object* v_res_871_; 
v_res_871_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1_spec__2___redArg(v_m_866_, v_query_867_, v_x_868_, v_x_869_, v_x_870_);
lean_dec_ref(v_query_867_);
lean_dec_ref(v_m_866_);
return v_res_871_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1___redArg(lean_object* v_m_872_, lean_object* v_query_873_){
_start:
{
lean_object* v_keyArray_874_; lean_object* v_fst_875_; lean_object* v_snd_876_; lean_object* v___x_877_; size_t v___x_878_; size_t v___x_879_; size_t v___x_880_; uint64_t v___x_881_; uint64_t v___x_882_; uint64_t v___x_883_; uint64_t v___x_884_; uint64_t v___x_885_; uint64_t v_fold_886_; uint64_t v___x_887_; uint64_t v___x_888_; uint64_t v___x_889_; size_t v___x_890_; size_t v___x_891_; size_t v___x_892_; size_t v___x_893_; size_t v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; 
v_keyArray_874_ = lean_ctor_get(v_m_872_, 1);
v_fst_875_ = lean_ctor_get(v_query_873_, 0);
v_snd_876_ = lean_ctor_get(v_query_873_, 1);
v___x_877_ = lean_array_get_size(v_keyArray_874_);
v___x_878_ = lean_ptr_addr(v_fst_875_);
v___x_879_ = ((size_t)3ULL);
v___x_880_ = lean_usize_shift_right(v___x_878_, v___x_879_);
v___x_881_ = lean_usize_to_uint64(v___x_880_);
v___x_882_ = lean_uint64_of_nat(v_snd_876_);
v___x_883_ = lean_uint64_mix_hash(v___x_881_, v___x_882_);
v___x_884_ = 32ULL;
v___x_885_ = lean_uint64_shift_right(v___x_883_, v___x_884_);
v_fold_886_ = lean_uint64_xor(v___x_883_, v___x_885_);
v___x_887_ = 16ULL;
v___x_888_ = lean_uint64_shift_right(v_fold_886_, v___x_887_);
v___x_889_ = lean_uint64_xor(v_fold_886_, v___x_888_);
v___x_890_ = lean_uint64_to_usize(v___x_889_);
v___x_891_ = lean_usize_of_nat(v___x_877_);
v___x_892_ = ((size_t)1ULL);
v___x_893_ = lean_usize_sub(v___x_891_, v___x_892_);
v___x_894_ = lean_usize_land(v___x_890_, v___x_893_);
v___x_895_ = lean_usize_to_nat(v___x_894_);
v___x_896_ = lean_box(0);
v___x_897_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1_spec__2___redArg(v_m_872_, v_query_873_, v___x_896_, v___x_877_, v___x_895_);
return v___x_897_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1___redArg___boxed(lean_object* v_m_898_, lean_object* v_query_899_){
_start:
{
lean_object* v_res_900_; 
v_res_900_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1___redArg(v_m_898_, v_query_899_);
lean_dec_ref(v_query_899_);
lean_dec_ref(v_m_898_);
return v_res_900_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__0_spec__0___redArg(lean_object* v_m_901_, lean_object* v_query_902_){
_start:
{
lean_object* v___x_903_; 
v___x_903_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1___redArg(v_m_901_, v_query_902_);
if (lean_obj_tag(v___x_903_) == 0)
{
lean_object* v_index_904_; lean_object* v_key_905_; lean_object* v_value_906_; lean_object* v___x_908_; uint8_t v_isShared_909_; uint8_t v_isSharedCheck_913_; 
v_index_904_ = lean_ctor_get(v___x_903_, 0);
v_key_905_ = lean_ctor_get(v___x_903_, 1);
v_value_906_ = lean_ctor_get(v___x_903_, 2);
v_isSharedCheck_913_ = !lean_is_exclusive(v___x_903_);
if (v_isSharedCheck_913_ == 0)
{
v___x_908_ = v___x_903_;
v_isShared_909_ = v_isSharedCheck_913_;
goto v_resetjp_907_;
}
else
{
lean_inc(v_value_906_);
lean_inc(v_key_905_);
lean_inc(v_index_904_);
lean_dec(v___x_903_);
v___x_908_ = lean_box(0);
v_isShared_909_ = v_isSharedCheck_913_;
goto v_resetjp_907_;
}
v_resetjp_907_:
{
lean_object* v___x_911_; 
if (v_isShared_909_ == 0)
{
v___x_911_ = v___x_908_;
goto v_reusejp_910_;
}
else
{
lean_object* v_reuseFailAlloc_912_; 
v_reuseFailAlloc_912_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_912_, 0, v_index_904_);
lean_ctor_set(v_reuseFailAlloc_912_, 1, v_key_905_);
lean_ctor_set(v_reuseFailAlloc_912_, 2, v_value_906_);
v___x_911_ = v_reuseFailAlloc_912_;
goto v_reusejp_910_;
}
v_reusejp_910_:
{
return v___x_911_;
}
}
}
else
{
lean_object* v___x_914_; 
lean_dec(v___x_903_);
v___x_914_ = lean_box(1);
return v___x_914_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__0_spec__0___redArg___boxed(lean_object* v_m_915_, lean_object* v_query_916_){
_start:
{
lean_object* v_res_917_; 
v_res_917_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__0_spec__0___redArg(v_m_915_, v_query_916_);
lean_dec_ref(v_query_916_);
lean_dec_ref(v_m_915_);
return v_res_917_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__0___redArg(lean_object* v_m_918_, lean_object* v_a_919_){
_start:
{
lean_object* v___x_920_; 
v___x_920_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__0_spec__0___redArg(v_m_918_, v_a_919_);
if (lean_obj_tag(v___x_920_) == 0)
{
lean_object* v_value_921_; lean_object* v___x_922_; 
v_value_921_ = lean_ctor_get(v___x_920_, 2);
lean_inc(v_value_921_);
lean_dec_ref_known(v___x_920_, 3);
v___x_922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_922_, 0, v_value_921_);
return v___x_922_;
}
else
{
lean_object* v___x_923_; 
v___x_923_ = lean_box(0);
return v___x_923_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__0___redArg___boxed(lean_object* v_m_924_, lean_object* v_a_925_){
_start:
{
lean_object* v_res_926_; 
v_res_926_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__0___redArg(v_m_924_, v_a_925_);
lean_dec_ref(v_a_925_);
lean_dec_ref(v_m_924_);
return v_res_926_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__2_spec__4_spec__5___redArg(lean_object* v_b_927_, lean_object* v_acc_928_, lean_object* v_i_929_){
_start:
{
lean_object* v___y_931_; lean_object* v_keyArray_939_; lean_object* v_valueArray_940_; lean_object* v___x_941_; uint8_t v___x_942_; 
v_keyArray_939_ = lean_ctor_get(v_b_927_, 1);
v_valueArray_940_ = lean_ctor_get(v_b_927_, 2);
v___x_941_ = lean_array_get_size(v_keyArray_939_);
v___x_942_ = lean_nat_dec_lt(v_i_929_, v___x_941_);
if (v___x_942_ == 0)
{
lean_dec(v_i_929_);
return v_acc_928_;
}
else
{
lean_object* v___x_943_; uint8_t v_isSome_944_; 
v___x_943_ = lean_array_fget_borrowed(v_keyArray_939_, v_i_929_);
v_isSome_944_ = lean_noption_is_some(v___x_943_);
if (v_isSome_944_ == 0)
{
goto v___jp_935_;
}
else
{
lean_object* v___x_945_; uint8_t v_isSome_946_; 
v___x_945_ = lean_array_fget_borrowed(v_valueArray_940_, v_i_929_);
v_isSome_946_ = lean_noption_is_some(v___x_945_);
if (v_isSome_946_ == 0)
{
goto v___jp_935_;
}
else
{
lean_object* v_val_947_; lean_object* v_val_948_; lean_object* v_i_950_; lean_object* v___x_955_; 
lean_inc(v___x_943_);
v_val_947_ = lean_noption_get(v___x_943_);
lean_inc(v___x_945_);
v_val_948_ = lean_noption_get(v___x_945_);
v___x_955_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1___redArg(v_acc_928_, v_val_947_);
switch(lean_obj_tag(v___x_955_))
{
case 0:
{
lean_object* v_index_956_; lean_object* v_size_957_; lean_object* v___x_958_; 
v_index_956_ = lean_ctor_get(v___x_955_, 0);
lean_inc(v_index_956_);
lean_dec_ref_known(v___x_955_, 3);
v_size_957_ = lean_ctor_get(v_acc_928_, 0);
lean_inc(v_size_957_);
v___x_958_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_928_, v_size_957_, v_index_956_, v_val_947_, v_val_948_);
lean_dec(v_index_956_);
v___y_931_ = v___x_958_;
goto v___jp_930_;
}
case 1:
{
lean_object* v_index_959_; 
v_index_959_ = lean_ctor_get(v___x_955_, 0);
lean_inc(v_index_959_);
lean_dec_ref_known(v___x_955_, 1);
v_i_950_ = v_index_959_;
goto v___jp_949_;
}
default: 
{
lean_object* v___x_960_; lean_object* v___x_961_; 
v___x_960_ = lean_unsigned_to_nat(0u);
v___x_961_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v_acc_928_, v___x_960_);
if (lean_obj_tag(v___x_961_) == 0)
{
lean_object* v_index_962_; 
v_index_962_ = lean_ctor_get(v___x_961_, 0);
lean_inc(v_index_962_);
lean_dec_ref_known(v___x_961_, 1);
v_i_950_ = v_index_962_;
goto v___jp_949_;
}
else
{
lean_dec(v_val_948_);
lean_dec(v_val_947_);
v___y_931_ = v_acc_928_;
goto v___jp_930_;
}
}
}
v___jp_949_:
{
lean_object* v_size_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; 
v_size_951_ = lean_ctor_get(v_acc_928_, 0);
v___x_952_ = lean_unsigned_to_nat(1u);
v___x_953_ = lean_nat_add(v_size_951_, v___x_952_);
v___x_954_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_928_, v___x_953_, v_i_950_, v_val_947_, v_val_948_);
lean_dec(v_i_950_);
v___y_931_ = v___x_954_;
goto v___jp_930_;
}
}
}
}
v___jp_930_:
{
lean_object* v___x_932_; lean_object* v___x_933_; 
v___x_932_ = lean_unsigned_to_nat(1u);
v___x_933_ = lean_nat_add(v_i_929_, v___x_932_);
lean_dec(v_i_929_);
v_acc_928_ = v___y_931_;
v_i_929_ = v___x_933_;
goto _start;
}
v___jp_935_:
{
lean_object* v___x_936_; lean_object* v___x_937_; 
v___x_936_ = lean_unsigned_to_nat(1u);
v___x_937_ = lean_nat_add(v_i_929_, v___x_936_);
lean_dec(v_i_929_);
v_i_929_ = v___x_937_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__2_spec__4_spec__5___redArg___boxed(lean_object* v_b_963_, lean_object* v_acc_964_, lean_object* v_i_965_){
_start:
{
lean_object* v_res_966_; 
v_res_966_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__2_spec__4_spec__5___redArg(v_b_963_, v_acc_964_, v_i_965_);
lean_dec_ref(v_b_963_);
return v_res_966_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__2_spec__4___redArg(lean_object* v_init_967_, lean_object* v_b_968_){
_start:
{
lean_object* v___x_969_; lean_object* v___x_970_; 
v___x_969_ = lean_unsigned_to_nat(0u);
v___x_970_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__2_spec__4_spec__5___redArg(v_b_968_, v_init_967_, v___x_969_);
return v___x_970_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__2_spec__4___redArg___boxed(lean_object* v_init_971_, lean_object* v_b_972_){
_start:
{
lean_object* v_res_973_; 
v_res_973_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__2_spec__4___redArg(v_init_971_, v_b_972_);
lean_dec_ref(v_b_972_);
return v_res_973_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__2___redArg(lean_object* v_m_974_){
_start:
{
lean_object* v_keyArray_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v_cellCount_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v_target_982_; lean_object* v___x_983_; 
v_keyArray_975_ = lean_ctor_get(v_m_974_, 1);
v___x_976_ = lean_array_get_size(v_keyArray_975_);
v___x_977_ = lean_unsigned_to_nat(2u);
v_cellCount_978_ = lean_nat_mul(v___x_976_, v___x_977_);
v___x_979_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_978_);
v___x_980_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_978_);
v___x_981_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_978_);
v_target_982_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_target_982_, 0, v___x_979_);
lean_ctor_set(v_target_982_, 1, v___x_980_);
lean_ctor_set(v_target_982_, 2, v___x_981_);
v___x_983_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__2_spec__4___redArg(v_target_982_, v_m_974_);
return v___x_983_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__2___redArg___boxed(lean_object* v_m_984_){
_start:
{
lean_object* v_res_985_; 
v_res_985_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__2___redArg(v_m_984_);
lean_dec_ref(v_m_984_);
return v_res_985_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached___redArg(lean_object* v_rhs_986_, lean_object* v_op_987_, lean_object* v_a_988_, lean_object* v_a_989_, lean_object* v_a_990_, lean_object* v_a_991_, lean_object* v_a_992_, lean_object* v_a_993_, lean_object* v_a_994_){
_start:
{
lean_object* v___x_996_; lean_object* v_numConst_997_; lean_object* v_latticeBackwardRuleCache_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v_key_1001_; lean_object* v___x_1002_; 
v___x_996_ = lean_st_ref_get(v_a_988_);
v_numConst_997_ = lean_ctor_get(v_op_987_, 1);
v_latticeBackwardRuleCache_998_ = lean_ctor_get(v___x_996_, 2);
lean_inc_ref(v_latticeBackwardRuleCache_998_);
lean_dec(v___x_996_);
v___x_999_ = l_Lean_Expr_getAppPrefix(v_rhs_986_, v_numConst_997_);
v___x_1000_ = l_Lean_Expr_getAppNumArgs(v_rhs_986_);
v_key_1001_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_key_1001_, 0, v___x_999_);
lean_ctor_set(v_key_1001_, 1, v___x_1000_);
v___x_1002_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__0___redArg(v_latticeBackwardRuleCache_998_, v_key_1001_);
lean_dec_ref(v_latticeBackwardRuleCache_998_);
if (lean_obj_tag(v___x_1002_) == 1)
{
lean_object* v_val_1003_; lean_object* v___x_1005_; uint8_t v_isShared_1006_; uint8_t v_isSharedCheck_1010_; 
lean_dec_ref_known(v_key_1001_, 2);
lean_dec_ref(v_op_987_);
lean_dec_ref(v_rhs_986_);
v_val_1003_ = lean_ctor_get(v___x_1002_, 0);
v_isSharedCheck_1010_ = !lean_is_exclusive(v___x_1002_);
if (v_isSharedCheck_1010_ == 0)
{
v___x_1005_ = v___x_1002_;
v_isShared_1006_ = v_isSharedCheck_1010_;
goto v_resetjp_1004_;
}
else
{
lean_inc(v_val_1003_);
lean_dec(v___x_1002_);
v___x_1005_ = lean_box(0);
v_isShared_1006_ = v_isSharedCheck_1010_;
goto v_resetjp_1004_;
}
v_resetjp_1004_:
{
lean_object* v___x_1008_; 
if (v_isShared_1006_ == 0)
{
lean_ctor_set_tag(v___x_1005_, 0);
v___x_1008_ = v___x_1005_;
goto v_reusejp_1007_;
}
else
{
lean_object* v_reuseFailAlloc_1009_; 
v_reuseFailAlloc_1009_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1009_, 0, v_val_1003_);
v___x_1008_ = v_reuseFailAlloc_1009_;
goto v_reusejp_1007_;
}
v_reusejp_1007_:
{
return v___x_1008_;
}
}
}
else
{
lean_object* v___x_1011_; 
lean_dec(v___x_1002_);
v___x_1011_ = l_Lean_Elab_Tactic_VCGen_mkLatticeOpRule(v_rhs_986_, v_op_987_, v_a_989_, v_a_990_, v_a_991_, v_a_992_, v_a_993_, v_a_994_);
if (lean_obj_tag(v___x_1011_) == 0)
{
lean_object* v_a_1012_; lean_object* v___x_1013_; 
v_a_1012_ = lean_ctor_get(v___x_1011_, 0);
lean_inc(v_a_1012_);
lean_dec_ref_known(v___x_1011_, 1);
v___x_1013_ = l_Lean_Meta_Sym_BackwardRule_shareCommon(v_a_1012_, v_a_989_, v_a_990_, v_a_991_, v_a_992_, v_a_993_, v_a_994_);
if (lean_obj_tag(v___x_1013_) == 0)
{
lean_object* v_a_1014_; lean_object* v___x_1016_; uint8_t v_isShared_1017_; uint8_t v_isSharedCheck_1106_; 
v_a_1014_ = lean_ctor_get(v___x_1013_, 0);
v_isSharedCheck_1106_ = !lean_is_exclusive(v___x_1013_);
if (v_isSharedCheck_1106_ == 0)
{
v___x_1016_ = v___x_1013_;
v_isShared_1017_ = v_isSharedCheck_1106_;
goto v_resetjp_1015_;
}
else
{
lean_inc(v_a_1014_);
lean_dec(v___x_1013_);
v___x_1016_ = lean_box(0);
v_isShared_1017_ = v_isSharedCheck_1106_;
goto v_resetjp_1015_;
}
v_resetjp_1015_:
{
lean_object* v___x_1018_; lean_object* v_specBackwardRuleCache_1019_; lean_object* v_splitBackwardRuleCache_1020_; lean_object* v_latticeBackwardRuleCache_1021_; lean_object* v_frameBackwardRuleCache_1022_; lean_object* v_frameDB_1023_; lean_object* v_invariants_1024_; lean_object* v_vcs_1025_; lean_object* v_simpState_1026_; lean_object* v_fuel_1027_; lean_object* v_inlineHandledInvariants_1028_; lean_object* v___x_1030_; uint8_t v_isShared_1031_; uint8_t v_isSharedCheck_1105_; 
v___x_1018_ = lean_st_ref_take(v_a_988_);
v_specBackwardRuleCache_1019_ = lean_ctor_get(v___x_1018_, 0);
v_splitBackwardRuleCache_1020_ = lean_ctor_get(v___x_1018_, 1);
v_latticeBackwardRuleCache_1021_ = lean_ctor_get(v___x_1018_, 2);
v_frameBackwardRuleCache_1022_ = lean_ctor_get(v___x_1018_, 3);
v_frameDB_1023_ = lean_ctor_get(v___x_1018_, 4);
v_invariants_1024_ = lean_ctor_get(v___x_1018_, 5);
v_vcs_1025_ = lean_ctor_get(v___x_1018_, 6);
v_simpState_1026_ = lean_ctor_get(v___x_1018_, 7);
v_fuel_1027_ = lean_ctor_get(v___x_1018_, 8);
v_inlineHandledInvariants_1028_ = lean_ctor_get(v___x_1018_, 9);
v_isSharedCheck_1105_ = !lean_is_exclusive(v___x_1018_);
if (v_isSharedCheck_1105_ == 0)
{
v___x_1030_ = v___x_1018_;
v_isShared_1031_ = v_isSharedCheck_1105_;
goto v_resetjp_1029_;
}
else
{
lean_inc(v_inlineHandledInvariants_1028_);
lean_inc(v_fuel_1027_);
lean_inc(v_simpState_1026_);
lean_inc(v_vcs_1025_);
lean_inc(v_invariants_1024_);
lean_inc(v_frameDB_1023_);
lean_inc(v_frameBackwardRuleCache_1022_);
lean_inc(v_latticeBackwardRuleCache_1021_);
lean_inc(v_splitBackwardRuleCache_1020_);
lean_inc(v_specBackwardRuleCache_1019_);
lean_dec(v___x_1018_);
v___x_1030_ = lean_box(0);
v_isShared_1031_ = v_isSharedCheck_1105_;
goto v_resetjp_1029_;
}
v_resetjp_1029_:
{
lean_object* v___y_1033_; lean_object* v___y_1042_; lean_object* v_i_1043_; lean_object* v___y_1059_; lean_object* v_i_1060_; lean_object* v___y_1066_; lean_object* v___x_1075_; 
v___x_1075_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1___redArg(v_latticeBackwardRuleCache_1021_, v_key_1001_);
switch(lean_obj_tag(v___x_1075_))
{
case 0:
{
lean_object* v_index_1076_; lean_object* v_size_1077_; lean_object* v___x_1078_; 
v_index_1076_ = lean_ctor_get(v___x_1075_, 0);
lean_inc(v_index_1076_);
lean_dec_ref_known(v___x_1075_, 3);
v_size_1077_ = lean_ctor_get(v_latticeBackwardRuleCache_1021_, 0);
lean_inc(v_size_1077_);
lean_inc(v_a_1014_);
v___x_1078_ = l_Std_DHashMap_Raw_setEntry___redArg(v_latticeBackwardRuleCache_1021_, v_size_1077_, v_index_1076_, v_key_1001_, v_a_1014_);
lean_dec(v_index_1076_);
v___y_1033_ = v___x_1078_;
goto v___jp_1032_;
}
case 1:
{
lean_object* v_index_1079_; lean_object* v_size_1080_; lean_object* v_keyArray_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; uint8_t v___x_1085_; 
v_index_1079_ = lean_ctor_get(v___x_1075_, 0);
lean_inc(v_index_1079_);
lean_dec_ref_known(v___x_1075_, 1);
v_size_1080_ = lean_ctor_get(v_latticeBackwardRuleCache_1021_, 0);
v_keyArray_1081_ = lean_ctor_get(v_latticeBackwardRuleCache_1021_, 1);
v___x_1082_ = lean_unsigned_to_nat(1u);
v___x_1083_ = lean_nat_add(v_size_1080_, v___x_1082_);
v___x_1084_ = lean_array_get_size(v_keyArray_1081_);
v___x_1085_ = lean_nat_dec_lt(v___x_1083_, v___x_1084_);
if (v___x_1085_ == 0)
{
lean_dec(v___x_1083_);
lean_dec(v_index_1079_);
goto v___jp_1048_;
}
else
{
lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; uint8_t v___x_1090_; 
v___x_1086_ = lean_unsigned_to_nat(4u);
v___x_1087_ = lean_nat_mul(v___x_1083_, v___x_1086_);
v___x_1088_ = lean_unsigned_to_nat(3u);
v___x_1089_ = lean_nat_mul(v___x_1084_, v___x_1088_);
v___x_1090_ = lean_nat_dec_le(v___x_1087_, v___x_1089_);
lean_dec(v___x_1089_);
lean_dec(v___x_1087_);
if (v___x_1090_ == 0)
{
lean_dec(v___x_1083_);
lean_dec(v_index_1079_);
goto v___jp_1048_;
}
else
{
lean_object* v___x_1091_; 
lean_inc(v_a_1014_);
v___x_1091_ = l_Std_DHashMap_Raw_setEntry___redArg(v_latticeBackwardRuleCache_1021_, v___x_1083_, v_index_1079_, v_key_1001_, v_a_1014_);
lean_dec(v_index_1079_);
v___y_1033_ = v___x_1091_;
goto v___jp_1032_;
}
}
}
default: 
{
lean_object* v_size_1092_; lean_object* v_keyArray_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; uint8_t v___x_1097_; 
v_size_1092_ = lean_ctor_get(v_latticeBackwardRuleCache_1021_, 0);
v_keyArray_1093_ = lean_ctor_get(v_latticeBackwardRuleCache_1021_, 1);
v___x_1094_ = lean_unsigned_to_nat(1u);
v___x_1095_ = lean_nat_add(v_size_1092_, v___x_1094_);
v___x_1096_ = lean_array_get_size(v_keyArray_1093_);
v___x_1097_ = lean_nat_dec_lt(v___x_1095_, v___x_1096_);
if (v___x_1097_ == 0)
{
lean_object* v___x_1098_; 
lean_dec(v___x_1095_);
v___x_1098_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__2___redArg(v_latticeBackwardRuleCache_1021_);
lean_dec_ref(v_latticeBackwardRuleCache_1021_);
v___y_1066_ = v___x_1098_;
goto v___jp_1065_;
}
else
{
lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; uint8_t v___x_1103_; 
v___x_1099_ = lean_unsigned_to_nat(4u);
v___x_1100_ = lean_nat_mul(v___x_1095_, v___x_1099_);
lean_dec(v___x_1095_);
v___x_1101_ = lean_unsigned_to_nat(3u);
v___x_1102_ = lean_nat_mul(v___x_1096_, v___x_1101_);
v___x_1103_ = lean_nat_dec_le(v___x_1100_, v___x_1102_);
lean_dec(v___x_1102_);
lean_dec(v___x_1100_);
if (v___x_1103_ == 0)
{
lean_object* v___x_1104_; 
v___x_1104_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__2___redArg(v_latticeBackwardRuleCache_1021_);
lean_dec_ref(v_latticeBackwardRuleCache_1021_);
v___y_1066_ = v___x_1104_;
goto v___jp_1065_;
}
else
{
v___y_1066_ = v_latticeBackwardRuleCache_1021_;
goto v___jp_1065_;
}
}
}
}
v___jp_1032_:
{
lean_object* v___x_1035_; 
if (v_isShared_1031_ == 0)
{
lean_ctor_set(v___x_1030_, 2, v___y_1033_);
v___x_1035_ = v___x_1030_;
goto v_reusejp_1034_;
}
else
{
lean_object* v_reuseFailAlloc_1040_; 
v_reuseFailAlloc_1040_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1040_, 0, v_specBackwardRuleCache_1019_);
lean_ctor_set(v_reuseFailAlloc_1040_, 1, v_splitBackwardRuleCache_1020_);
lean_ctor_set(v_reuseFailAlloc_1040_, 2, v___y_1033_);
lean_ctor_set(v_reuseFailAlloc_1040_, 3, v_frameBackwardRuleCache_1022_);
lean_ctor_set(v_reuseFailAlloc_1040_, 4, v_frameDB_1023_);
lean_ctor_set(v_reuseFailAlloc_1040_, 5, v_invariants_1024_);
lean_ctor_set(v_reuseFailAlloc_1040_, 6, v_vcs_1025_);
lean_ctor_set(v_reuseFailAlloc_1040_, 7, v_simpState_1026_);
lean_ctor_set(v_reuseFailAlloc_1040_, 8, v_fuel_1027_);
lean_ctor_set(v_reuseFailAlloc_1040_, 9, v_inlineHandledInvariants_1028_);
v___x_1035_ = v_reuseFailAlloc_1040_;
goto v_reusejp_1034_;
}
v_reusejp_1034_:
{
lean_object* v___x_1036_; lean_object* v___x_1038_; 
v___x_1036_ = lean_st_ref_put(v_a_988_, v___x_1035_);
if (v_isShared_1017_ == 0)
{
v___x_1038_ = v___x_1016_;
goto v_reusejp_1037_;
}
else
{
lean_object* v_reuseFailAlloc_1039_; 
v_reuseFailAlloc_1039_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1039_, 0, v_a_1014_);
v___x_1038_ = v_reuseFailAlloc_1039_;
goto v_reusejp_1037_;
}
v_reusejp_1037_:
{
return v___x_1038_;
}
}
}
v___jp_1041_:
{
lean_object* v_size_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; 
v_size_1044_ = lean_ctor_get(v___y_1042_, 0);
v___x_1045_ = lean_unsigned_to_nat(1u);
v___x_1046_ = lean_nat_add(v_size_1044_, v___x_1045_);
lean_inc(v_a_1014_);
v___x_1047_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1042_, v___x_1046_, v_i_1043_, v_key_1001_, v_a_1014_);
lean_dec(v_i_1043_);
v___y_1033_ = v___x_1047_;
goto v___jp_1032_;
}
v___jp_1048_:
{
lean_object* v___x_1049_; lean_object* v___x_1050_; 
v___x_1049_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__2___redArg(v_latticeBackwardRuleCache_1021_);
lean_dec_ref(v_latticeBackwardRuleCache_1021_);
v___x_1050_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1___redArg(v___x_1049_, v_key_1001_);
switch(lean_obj_tag(v___x_1050_))
{
case 0:
{
lean_object* v_index_1051_; lean_object* v_size_1052_; lean_object* v___x_1053_; 
v_index_1051_ = lean_ctor_get(v___x_1050_, 0);
lean_inc(v_index_1051_);
lean_dec_ref_known(v___x_1050_, 3);
v_size_1052_ = lean_ctor_get(v___x_1049_, 0);
lean_inc(v_size_1052_);
lean_inc(v_a_1014_);
v___x_1053_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_1049_, v_size_1052_, v_index_1051_, v_key_1001_, v_a_1014_);
lean_dec(v_index_1051_);
v___y_1033_ = v___x_1053_;
goto v___jp_1032_;
}
case 1:
{
lean_object* v_index_1054_; 
v_index_1054_ = lean_ctor_get(v___x_1050_, 0);
lean_inc(v_index_1054_);
lean_dec_ref_known(v___x_1050_, 1);
v___y_1042_ = v___x_1049_;
v_i_1043_ = v_index_1054_;
goto v___jp_1041_;
}
default: 
{
lean_object* v___x_1055_; lean_object* v___x_1056_; 
v___x_1055_ = lean_unsigned_to_nat(0u);
v___x_1056_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_1049_, v___x_1055_);
if (lean_obj_tag(v___x_1056_) == 0)
{
lean_object* v_index_1057_; 
v_index_1057_ = lean_ctor_get(v___x_1056_, 0);
lean_inc(v_index_1057_);
lean_dec_ref_known(v___x_1056_, 1);
v___y_1042_ = v___x_1049_;
v_i_1043_ = v_index_1057_;
goto v___jp_1041_;
}
else
{
lean_dec_ref_known(v_key_1001_, 2);
v___y_1033_ = v___x_1049_;
goto v___jp_1032_;
}
}
}
}
v___jp_1058_:
{
lean_object* v_size_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; 
v_size_1061_ = lean_ctor_get(v___y_1059_, 0);
v___x_1062_ = lean_unsigned_to_nat(1u);
v___x_1063_ = lean_nat_add(v_size_1061_, v___x_1062_);
lean_inc(v_a_1014_);
v___x_1064_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1059_, v___x_1063_, v_i_1060_, v_key_1001_, v_a_1014_);
lean_dec(v_i_1060_);
v___y_1033_ = v___x_1064_;
goto v___jp_1032_;
}
v___jp_1065_:
{
lean_object* v___x_1067_; 
v___x_1067_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1___redArg(v___y_1066_, v_key_1001_);
switch(lean_obj_tag(v___x_1067_))
{
case 0:
{
lean_object* v_index_1068_; lean_object* v_size_1069_; lean_object* v___x_1070_; 
v_index_1068_ = lean_ctor_get(v___x_1067_, 0);
lean_inc(v_index_1068_);
lean_dec_ref_known(v___x_1067_, 3);
v_size_1069_ = lean_ctor_get(v___y_1066_, 0);
lean_inc(v_size_1069_);
lean_inc(v_a_1014_);
v___x_1070_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1066_, v_size_1069_, v_index_1068_, v_key_1001_, v_a_1014_);
lean_dec(v_index_1068_);
v___y_1033_ = v___x_1070_;
goto v___jp_1032_;
}
case 1:
{
lean_object* v_index_1071_; 
v_index_1071_ = lean_ctor_get(v___x_1067_, 0);
lean_inc(v_index_1071_);
lean_dec_ref_known(v___x_1067_, 1);
v___y_1059_ = v___y_1066_;
v_i_1060_ = v_index_1071_;
goto v___jp_1058_;
}
default: 
{
lean_object* v___x_1072_; lean_object* v___x_1073_; 
v___x_1072_ = lean_unsigned_to_nat(0u);
v___x_1073_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_1066_, v___x_1072_);
if (lean_obj_tag(v___x_1073_) == 0)
{
lean_object* v_index_1074_; 
v_index_1074_ = lean_ctor_get(v___x_1073_, 0);
lean_inc(v_index_1074_);
lean_dec_ref_known(v___x_1073_, 1);
v___y_1059_ = v___y_1066_;
v_i_1060_ = v_index_1074_;
goto v___jp_1058_;
}
else
{
lean_dec_ref_known(v_key_1001_, 2);
v___y_1033_ = v___y_1066_;
goto v___jp_1032_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_key_1001_, 2);
return v___x_1013_;
}
}
else
{
lean_dec_ref_known(v_key_1001_, 2);
return v___x_1011_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached___redArg___boxed(lean_object* v_rhs_1107_, lean_object* v_op_1108_, lean_object* v_a_1109_, lean_object* v_a_1110_, lean_object* v_a_1111_, lean_object* v_a_1112_, lean_object* v_a_1113_, lean_object* v_a_1114_, lean_object* v_a_1115_, lean_object* v_a_1116_){
_start:
{
lean_object* v_res_1117_; 
v_res_1117_ = l_Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached___redArg(v_rhs_1107_, v_op_1108_, v_a_1109_, v_a_1110_, v_a_1111_, v_a_1112_, v_a_1113_, v_a_1114_, v_a_1115_);
lean_dec(v_a_1115_);
lean_dec_ref(v_a_1114_);
lean_dec(v_a_1113_);
lean_dec_ref(v_a_1112_);
lean_dec(v_a_1111_);
lean_dec_ref(v_a_1110_);
lean_dec(v_a_1109_);
return v_res_1117_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached(lean_object* v_rhs_1118_, lean_object* v_op_1119_, lean_object* v_a_1120_, lean_object* v_a_1121_, lean_object* v_a_1122_, lean_object* v_a_1123_, lean_object* v_a_1124_, lean_object* v_a_1125_, lean_object* v_a_1126_, lean_object* v_a_1127_, lean_object* v_a_1128_, lean_object* v_a_1129_, lean_object* v_a_1130_){
_start:
{
lean_object* v___x_1132_; 
v___x_1132_ = l_Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached___redArg(v_rhs_1118_, v_op_1119_, v_a_1121_, v_a_1125_, v_a_1126_, v_a_1127_, v_a_1128_, v_a_1129_, v_a_1130_);
return v___x_1132_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached___boxed(lean_object* v_rhs_1133_, lean_object* v_op_1134_, lean_object* v_a_1135_, lean_object* v_a_1136_, lean_object* v_a_1137_, lean_object* v_a_1138_, lean_object* v_a_1139_, lean_object* v_a_1140_, lean_object* v_a_1141_, lean_object* v_a_1142_, lean_object* v_a_1143_, lean_object* v_a_1144_, lean_object* v_a_1145_, lean_object* v_a_1146_){
_start:
{
lean_object* v_res_1147_; 
v_res_1147_ = l_Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached(v_rhs_1133_, v_op_1134_, v_a_1135_, v_a_1136_, v_a_1137_, v_a_1138_, v_a_1139_, v_a_1140_, v_a_1141_, v_a_1142_, v_a_1143_, v_a_1144_, v_a_1145_);
lean_dec(v_a_1145_);
lean_dec_ref(v_a_1144_);
lean_dec(v_a_1143_);
lean_dec_ref(v_a_1142_);
lean_dec(v_a_1141_);
lean_dec_ref(v_a_1140_);
lean_dec(v_a_1139_);
lean_dec_ref(v_a_1138_);
lean_dec(v_a_1137_);
lean_dec(v_a_1136_);
lean_dec_ref(v_a_1135_);
return v_res_1147_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__0(lean_object* v_00_u03b2_1148_, lean_object* v_m_1149_, lean_object* v_a_1150_){
_start:
{
lean_object* v___x_1151_; 
v___x_1151_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__0___redArg(v_m_1149_, v_a_1150_);
return v___x_1151_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__0___boxed(lean_object* v_00_u03b2_1152_, lean_object* v_m_1153_, lean_object* v_a_1154_){
_start:
{
lean_object* v_res_1155_; 
v_res_1155_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__0(v_00_u03b2_1152_, v_m_1153_, v_a_1154_);
lean_dec_ref(v_a_1154_);
lean_dec_ref(v_m_1153_);
return v_res_1155_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1(lean_object* v_00_u03b2_1156_, lean_object* v_m_1157_, lean_object* v_query_1158_){
_start:
{
lean_object* v___x_1159_; 
v___x_1159_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1___redArg(v_m_1157_, v_query_1158_);
return v___x_1159_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1___boxed(lean_object* v_00_u03b2_1160_, lean_object* v_m_1161_, lean_object* v_query_1162_){
_start:
{
lean_object* v_res_1163_; 
v_res_1163_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1(v_00_u03b2_1160_, v_m_1161_, v_query_1162_);
lean_dec_ref(v_query_1162_);
lean_dec_ref(v_m_1161_);
return v_res_1163_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__2(lean_object* v_00_u03b2_1164_, lean_object* v_m_1165_){
_start:
{
lean_object* v___x_1166_; 
v___x_1166_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__2___redArg(v_m_1165_);
return v___x_1166_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__2___boxed(lean_object* v_00_u03b2_1167_, lean_object* v_m_1168_){
_start:
{
lean_object* v_res_1169_; 
v_res_1169_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__2(v_00_u03b2_1167_, v_m_1168_);
lean_dec_ref(v_m_1168_);
return v_res_1169_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__0_spec__0(lean_object* v_00_u03b2_1170_, lean_object* v_m_1171_, lean_object* v_query_1172_){
_start:
{
lean_object* v___x_1173_; 
v___x_1173_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__0_spec__0___redArg(v_m_1171_, v_query_1172_);
return v___x_1173_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1174_, lean_object* v_m_1175_, lean_object* v_query_1176_){
_start:
{
lean_object* v_res_1177_; 
v_res_1177_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__0_spec__0(v_00_u03b2_1174_, v_m_1175_, v_query_1176_);
lean_dec_ref(v_query_1176_);
lean_dec_ref(v_m_1175_);
return v_res_1177_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1_spec__2(lean_object* v_00_u03b2_1178_, lean_object* v_m_1179_, lean_object* v_query_1180_, lean_object* v_x_1181_, lean_object* v_x_1182_, lean_object* v_x_1183_, lean_object* v_x_1184_){
_start:
{
lean_object* v___x_1185_; 
v___x_1185_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1_spec__2___redArg(v_m_1179_, v_query_1180_, v_x_1181_, v_x_1182_, v_x_1183_);
return v___x_1185_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1186_, lean_object* v_m_1187_, lean_object* v_query_1188_, lean_object* v_x_1189_, lean_object* v_x_1190_, lean_object* v_x_1191_, lean_object* v_x_1192_){
_start:
{
lean_object* v_res_1193_; 
v_res_1193_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1_spec__2(v_00_u03b2_1186_, v_m_1187_, v_query_1188_, v_x_1189_, v_x_1190_, v_x_1191_, v_x_1192_);
lean_dec_ref(v_query_1188_);
lean_dec_ref(v_m_1187_);
return v_res_1193_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__2_spec__4(lean_object* v_00_u03b2_1194_, lean_object* v_init_1195_, lean_object* v_b_1196_){
_start:
{
lean_object* v___x_1197_; 
v___x_1197_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__2_spec__4___redArg(v_init_1195_, v_b_1196_);
return v___x_1197_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__2_spec__4___boxed(lean_object* v_00_u03b2_1198_, lean_object* v_init_1199_, lean_object* v_b_1200_){
_start:
{
lean_object* v_res_1201_; 
v_res_1201_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__2_spec__4(v_00_u03b2_1198_, v_init_1199_, v_b_1200_);
lean_dec_ref(v_b_1200_);
return v_res_1201_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_1202_, lean_object* v_b_1203_, lean_object* v_acc_1204_, lean_object* v_i_1205_){
_start:
{
lean_object* v___x_1206_; 
v___x_1206_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__2_spec__4_spec__5___redArg(v_b_1203_, v_acc_1204_, v_i_1205_);
return v___x_1206_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__2_spec__4_spec__5___boxed(lean_object* v_00_u03b2_1207_, lean_object* v_b_1208_, lean_object* v_acc_1209_, lean_object* v_i_1210_){
_start:
{
lean_object* v_res_1211_; 
v_res_1211_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__2_spec__4_spec__5(v_00_u03b2_1207_, v_b_1208_, v_acc_1209_, v_i_1210_);
lean_dec_ref(v_b_1208_);
return v_res_1211_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_mkFrameBackwardRuleCached___redArg(lean_object* v_fp_1212_, lean_object* v_info_1213_, lean_object* v_a_1214_, lean_object* v_a_1215_, lean_object* v_a_1216_, lean_object* v_a_1217_, lean_object* v_a_1218_, lean_object* v_a_1219_, lean_object* v_a_1220_){
_start:
{
lean_object* v___x_1222_; lean_object* v_excessArgs_1223_; lean_object* v_frameBackwardRuleCache_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v_key_1227_; lean_object* v___x_1228_; 
v___x_1222_ = lean_st_ref_get(v_a_1214_);
v_excessArgs_1223_ = lean_ctor_get(v_info_1213_, 2);
v_frameBackwardRuleCache_1224_ = lean_ctor_get(v___x_1222_, 3);
lean_inc_ref(v_frameBackwardRuleCache_1224_);
lean_dec(v___x_1222_);
v___x_1225_ = l_Lean_Elab_Tactic_VCGen_WPApp_instWP(v_info_1213_);
v___x_1226_ = lean_array_get_size(v_excessArgs_1223_);
v_key_1227_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_key_1227_, 0, v___x_1225_);
lean_ctor_set(v_key_1227_, 1, v___x_1226_);
v___x_1228_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__0___redArg(v_frameBackwardRuleCache_1224_, v_key_1227_);
lean_dec_ref(v_frameBackwardRuleCache_1224_);
if (lean_obj_tag(v___x_1228_) == 1)
{
lean_object* v_val_1229_; lean_object* v___x_1231_; uint8_t v_isShared_1232_; uint8_t v_isSharedCheck_1236_; 
lean_dec_ref_known(v_key_1227_, 2);
lean_dec_ref(v_info_1213_);
lean_dec_ref(v_fp_1212_);
v_val_1229_ = lean_ctor_get(v___x_1228_, 0);
v_isSharedCheck_1236_ = !lean_is_exclusive(v___x_1228_);
if (v_isSharedCheck_1236_ == 0)
{
v___x_1231_ = v___x_1228_;
v_isShared_1232_ = v_isSharedCheck_1236_;
goto v_resetjp_1230_;
}
else
{
lean_inc(v_val_1229_);
lean_dec(v___x_1228_);
v___x_1231_ = lean_box(0);
v_isShared_1232_ = v_isSharedCheck_1236_;
goto v_resetjp_1230_;
}
v_resetjp_1230_:
{
lean_object* v___x_1234_; 
if (v_isShared_1232_ == 0)
{
lean_ctor_set_tag(v___x_1231_, 0);
v___x_1234_ = v___x_1231_;
goto v_reusejp_1233_;
}
else
{
lean_object* v_reuseFailAlloc_1235_; 
v_reuseFailAlloc_1235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1235_, 0, v_val_1229_);
v___x_1234_ = v_reuseFailAlloc_1235_;
goto v_reusejp_1233_;
}
v_reusejp_1233_:
{
return v___x_1234_;
}
}
}
else
{
lean_object* v___x_1237_; 
lean_dec(v___x_1228_);
v___x_1237_ = l_Lean_Elab_Tactic_VCGen_mkFrameBackwardRule(v_fp_1212_, v_info_1213_, v_a_1217_, v_a_1218_, v_a_1219_, v_a_1220_);
if (lean_obj_tag(v___x_1237_) == 0)
{
lean_object* v_a_1238_; lean_object* v_rule_1239_; lean_object* v_splitVCIdx_1240_; lean_object* v_frameIdx_1241_; lean_object* v___x_1243_; uint8_t v_isShared_1244_; uint8_t v_isSharedCheck_1350_; 
v_a_1238_ = lean_ctor_get(v___x_1237_, 0);
lean_inc(v_a_1238_);
lean_dec_ref_known(v___x_1237_, 1);
v_rule_1239_ = lean_ctor_get(v_a_1238_, 0);
v_splitVCIdx_1240_ = lean_ctor_get(v_a_1238_, 1);
v_frameIdx_1241_ = lean_ctor_get(v_a_1238_, 2);
v_isSharedCheck_1350_ = !lean_is_exclusive(v_a_1238_);
if (v_isSharedCheck_1350_ == 0)
{
v___x_1243_ = v_a_1238_;
v_isShared_1244_ = v_isSharedCheck_1350_;
goto v_resetjp_1242_;
}
else
{
lean_inc(v_frameIdx_1241_);
lean_inc(v_splitVCIdx_1240_);
lean_inc(v_rule_1239_);
lean_dec(v_a_1238_);
v___x_1243_ = lean_box(0);
v_isShared_1244_ = v_isSharedCheck_1350_;
goto v_resetjp_1242_;
}
v_resetjp_1242_:
{
lean_object* v___x_1245_; 
v___x_1245_ = l_Lean_Meta_Sym_BackwardRule_shareCommon(v_rule_1239_, v_a_1215_, v_a_1216_, v_a_1217_, v_a_1218_, v_a_1219_, v_a_1220_);
if (lean_obj_tag(v___x_1245_) == 0)
{
lean_object* v_a_1246_; lean_object* v___x_1248_; uint8_t v_isShared_1249_; uint8_t v_isSharedCheck_1341_; 
v_a_1246_ = lean_ctor_get(v___x_1245_, 0);
v_isSharedCheck_1341_ = !lean_is_exclusive(v___x_1245_);
if (v_isSharedCheck_1341_ == 0)
{
v___x_1248_ = v___x_1245_;
v_isShared_1249_ = v_isSharedCheck_1341_;
goto v_resetjp_1247_;
}
else
{
lean_inc(v_a_1246_);
lean_dec(v___x_1245_);
v___x_1248_ = lean_box(0);
v_isShared_1249_ = v_isSharedCheck_1341_;
goto v_resetjp_1247_;
}
v_resetjp_1247_:
{
lean_object* v___x_1250_; lean_object* v_specBackwardRuleCache_1251_; lean_object* v_splitBackwardRuleCache_1252_; lean_object* v_latticeBackwardRuleCache_1253_; lean_object* v_frameBackwardRuleCache_1254_; lean_object* v_frameDB_1255_; lean_object* v_invariants_1256_; lean_object* v_vcs_1257_; lean_object* v_simpState_1258_; lean_object* v_fuel_1259_; lean_object* v_inlineHandledInvariants_1260_; lean_object* v___x_1262_; uint8_t v_isShared_1263_; uint8_t v_isSharedCheck_1340_; 
v___x_1250_ = lean_st_ref_take(v_a_1214_);
v_specBackwardRuleCache_1251_ = lean_ctor_get(v___x_1250_, 0);
v_splitBackwardRuleCache_1252_ = lean_ctor_get(v___x_1250_, 1);
v_latticeBackwardRuleCache_1253_ = lean_ctor_get(v___x_1250_, 2);
v_frameBackwardRuleCache_1254_ = lean_ctor_get(v___x_1250_, 3);
v_frameDB_1255_ = lean_ctor_get(v___x_1250_, 4);
v_invariants_1256_ = lean_ctor_get(v___x_1250_, 5);
v_vcs_1257_ = lean_ctor_get(v___x_1250_, 6);
v_simpState_1258_ = lean_ctor_get(v___x_1250_, 7);
v_fuel_1259_ = lean_ctor_get(v___x_1250_, 8);
v_inlineHandledInvariants_1260_ = lean_ctor_get(v___x_1250_, 9);
v_isSharedCheck_1340_ = !lean_is_exclusive(v___x_1250_);
if (v_isSharedCheck_1340_ == 0)
{
v___x_1262_ = v___x_1250_;
v_isShared_1263_ = v_isSharedCheck_1340_;
goto v_resetjp_1261_;
}
else
{
lean_inc(v_inlineHandledInvariants_1260_);
lean_inc(v_fuel_1259_);
lean_inc(v_simpState_1258_);
lean_inc(v_vcs_1257_);
lean_inc(v_invariants_1256_);
lean_inc(v_frameDB_1255_);
lean_inc(v_frameBackwardRuleCache_1254_);
lean_inc(v_latticeBackwardRuleCache_1253_);
lean_inc(v_splitBackwardRuleCache_1252_);
lean_inc(v_specBackwardRuleCache_1251_);
lean_dec(v___x_1250_);
v___x_1262_ = lean_box(0);
v_isShared_1263_ = v_isSharedCheck_1340_;
goto v_resetjp_1261_;
}
v_resetjp_1261_:
{
lean_object* v___x_1265_; 
if (v_isShared_1244_ == 0)
{
lean_ctor_set(v___x_1243_, 0, v_a_1246_);
v___x_1265_ = v___x_1243_;
goto v_reusejp_1264_;
}
else
{
lean_object* v_reuseFailAlloc_1339_; 
v_reuseFailAlloc_1339_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1339_, 0, v_a_1246_);
lean_ctor_set(v_reuseFailAlloc_1339_, 1, v_splitVCIdx_1240_);
lean_ctor_set(v_reuseFailAlloc_1339_, 2, v_frameIdx_1241_);
v___x_1265_ = v_reuseFailAlloc_1339_;
goto v_reusejp_1264_;
}
v_reusejp_1264_:
{
lean_object* v___y_1267_; lean_object* v___y_1276_; lean_object* v_i_1277_; lean_object* v___y_1283_; lean_object* v___y_1293_; lean_object* v_i_1294_; lean_object* v___x_1309_; 
v___x_1309_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1___redArg(v_frameBackwardRuleCache_1254_, v_key_1227_);
switch(lean_obj_tag(v___x_1309_))
{
case 0:
{
lean_object* v_index_1310_; lean_object* v_size_1311_; lean_object* v___x_1312_; 
v_index_1310_ = lean_ctor_get(v___x_1309_, 0);
lean_inc(v_index_1310_);
lean_dec_ref_known(v___x_1309_, 3);
v_size_1311_ = lean_ctor_get(v_frameBackwardRuleCache_1254_, 0);
lean_inc(v_size_1311_);
lean_inc_ref(v___x_1265_);
v___x_1312_ = l_Std_DHashMap_Raw_setEntry___redArg(v_frameBackwardRuleCache_1254_, v_size_1311_, v_index_1310_, v_key_1227_, v___x_1265_);
lean_dec(v_index_1310_);
v___y_1267_ = v___x_1312_;
goto v___jp_1266_;
}
case 1:
{
lean_object* v_index_1313_; lean_object* v_size_1314_; lean_object* v_keyArray_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; uint8_t v___x_1319_; 
v_index_1313_ = lean_ctor_get(v___x_1309_, 0);
lean_inc(v_index_1313_);
lean_dec_ref_known(v___x_1309_, 1);
v_size_1314_ = lean_ctor_get(v_frameBackwardRuleCache_1254_, 0);
v_keyArray_1315_ = lean_ctor_get(v_frameBackwardRuleCache_1254_, 1);
v___x_1316_ = lean_unsigned_to_nat(1u);
v___x_1317_ = lean_nat_add(v_size_1314_, v___x_1316_);
v___x_1318_ = lean_array_get_size(v_keyArray_1315_);
v___x_1319_ = lean_nat_dec_lt(v___x_1317_, v___x_1318_);
if (v___x_1319_ == 0)
{
lean_dec(v___x_1317_);
lean_dec(v_index_1313_);
goto v___jp_1299_;
}
else
{
lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; uint8_t v___x_1324_; 
v___x_1320_ = lean_unsigned_to_nat(4u);
v___x_1321_ = lean_nat_mul(v___x_1317_, v___x_1320_);
v___x_1322_ = lean_unsigned_to_nat(3u);
v___x_1323_ = lean_nat_mul(v___x_1318_, v___x_1322_);
v___x_1324_ = lean_nat_dec_le(v___x_1321_, v___x_1323_);
lean_dec(v___x_1323_);
lean_dec(v___x_1321_);
if (v___x_1324_ == 0)
{
lean_dec(v___x_1317_);
lean_dec(v_index_1313_);
goto v___jp_1299_;
}
else
{
lean_object* v___x_1325_; 
lean_inc_ref(v___x_1265_);
v___x_1325_ = l_Std_DHashMap_Raw_setEntry___redArg(v_frameBackwardRuleCache_1254_, v___x_1317_, v_index_1313_, v_key_1227_, v___x_1265_);
lean_dec(v_index_1313_);
v___y_1267_ = v___x_1325_;
goto v___jp_1266_;
}
}
}
default: 
{
lean_object* v_size_1326_; lean_object* v_keyArray_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; uint8_t v___x_1331_; 
v_size_1326_ = lean_ctor_get(v_frameBackwardRuleCache_1254_, 0);
v_keyArray_1327_ = lean_ctor_get(v_frameBackwardRuleCache_1254_, 1);
v___x_1328_ = lean_unsigned_to_nat(1u);
v___x_1329_ = lean_nat_add(v_size_1326_, v___x_1328_);
v___x_1330_ = lean_array_get_size(v_keyArray_1327_);
v___x_1331_ = lean_nat_dec_lt(v___x_1329_, v___x_1330_);
if (v___x_1331_ == 0)
{
lean_object* v___x_1332_; 
lean_dec(v___x_1329_);
v___x_1332_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__2___redArg(v_frameBackwardRuleCache_1254_);
lean_dec_ref(v_frameBackwardRuleCache_1254_);
v___y_1283_ = v___x_1332_;
goto v___jp_1282_;
}
else
{
lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; uint8_t v___x_1337_; 
v___x_1333_ = lean_unsigned_to_nat(4u);
v___x_1334_ = lean_nat_mul(v___x_1329_, v___x_1333_);
lean_dec(v___x_1329_);
v___x_1335_ = lean_unsigned_to_nat(3u);
v___x_1336_ = lean_nat_mul(v___x_1330_, v___x_1335_);
v___x_1337_ = lean_nat_dec_le(v___x_1334_, v___x_1336_);
lean_dec(v___x_1336_);
lean_dec(v___x_1334_);
if (v___x_1337_ == 0)
{
lean_object* v___x_1338_; 
v___x_1338_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__2___redArg(v_frameBackwardRuleCache_1254_);
lean_dec_ref(v_frameBackwardRuleCache_1254_);
v___y_1283_ = v___x_1338_;
goto v___jp_1282_;
}
else
{
v___y_1283_ = v_frameBackwardRuleCache_1254_;
goto v___jp_1282_;
}
}
}
}
v___jp_1266_:
{
lean_object* v___x_1269_; 
if (v_isShared_1263_ == 0)
{
lean_ctor_set(v___x_1262_, 3, v___y_1267_);
v___x_1269_ = v___x_1262_;
goto v_reusejp_1268_;
}
else
{
lean_object* v_reuseFailAlloc_1274_; 
v_reuseFailAlloc_1274_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1274_, 0, v_specBackwardRuleCache_1251_);
lean_ctor_set(v_reuseFailAlloc_1274_, 1, v_splitBackwardRuleCache_1252_);
lean_ctor_set(v_reuseFailAlloc_1274_, 2, v_latticeBackwardRuleCache_1253_);
lean_ctor_set(v_reuseFailAlloc_1274_, 3, v___y_1267_);
lean_ctor_set(v_reuseFailAlloc_1274_, 4, v_frameDB_1255_);
lean_ctor_set(v_reuseFailAlloc_1274_, 5, v_invariants_1256_);
lean_ctor_set(v_reuseFailAlloc_1274_, 6, v_vcs_1257_);
lean_ctor_set(v_reuseFailAlloc_1274_, 7, v_simpState_1258_);
lean_ctor_set(v_reuseFailAlloc_1274_, 8, v_fuel_1259_);
lean_ctor_set(v_reuseFailAlloc_1274_, 9, v_inlineHandledInvariants_1260_);
v___x_1269_ = v_reuseFailAlloc_1274_;
goto v_reusejp_1268_;
}
v_reusejp_1268_:
{
lean_object* v___x_1270_; lean_object* v___x_1272_; 
v___x_1270_ = lean_st_ref_put(v_a_1214_, v___x_1269_);
if (v_isShared_1249_ == 0)
{
lean_ctor_set(v___x_1248_, 0, v___x_1265_);
v___x_1272_ = v___x_1248_;
goto v_reusejp_1271_;
}
else
{
lean_object* v_reuseFailAlloc_1273_; 
v_reuseFailAlloc_1273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1273_, 0, v___x_1265_);
v___x_1272_ = v_reuseFailAlloc_1273_;
goto v_reusejp_1271_;
}
v_reusejp_1271_:
{
return v___x_1272_;
}
}
}
v___jp_1275_:
{
lean_object* v_size_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; 
v_size_1278_ = lean_ctor_get(v___y_1276_, 0);
v___x_1279_ = lean_unsigned_to_nat(1u);
v___x_1280_ = lean_nat_add(v_size_1278_, v___x_1279_);
lean_inc_ref(v___x_1265_);
v___x_1281_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1276_, v___x_1280_, v_i_1277_, v_key_1227_, v___x_1265_);
lean_dec(v_i_1277_);
v___y_1267_ = v___x_1281_;
goto v___jp_1266_;
}
v___jp_1282_:
{
lean_object* v___x_1284_; 
v___x_1284_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1___redArg(v___y_1283_, v_key_1227_);
switch(lean_obj_tag(v___x_1284_))
{
case 0:
{
lean_object* v_index_1285_; lean_object* v_size_1286_; lean_object* v___x_1287_; 
v_index_1285_ = lean_ctor_get(v___x_1284_, 0);
lean_inc(v_index_1285_);
lean_dec_ref_known(v___x_1284_, 3);
v_size_1286_ = lean_ctor_get(v___y_1283_, 0);
lean_inc(v_size_1286_);
lean_inc_ref(v___x_1265_);
v___x_1287_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1283_, v_size_1286_, v_index_1285_, v_key_1227_, v___x_1265_);
lean_dec(v_index_1285_);
v___y_1267_ = v___x_1287_;
goto v___jp_1266_;
}
case 1:
{
lean_object* v_index_1288_; 
v_index_1288_ = lean_ctor_get(v___x_1284_, 0);
lean_inc(v_index_1288_);
lean_dec_ref_known(v___x_1284_, 1);
v___y_1276_ = v___y_1283_;
v_i_1277_ = v_index_1288_;
goto v___jp_1275_;
}
default: 
{
lean_object* v___x_1289_; lean_object* v___x_1290_; 
v___x_1289_ = lean_unsigned_to_nat(0u);
v___x_1290_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_1283_, v___x_1289_);
if (lean_obj_tag(v___x_1290_) == 0)
{
lean_object* v_index_1291_; 
v_index_1291_ = lean_ctor_get(v___x_1290_, 0);
lean_inc(v_index_1291_);
lean_dec_ref_known(v___x_1290_, 1);
v___y_1276_ = v___y_1283_;
v_i_1277_ = v_index_1291_;
goto v___jp_1275_;
}
else
{
lean_dec_ref_known(v_key_1227_, 2);
v___y_1267_ = v___y_1283_;
goto v___jp_1266_;
}
}
}
}
v___jp_1292_:
{
lean_object* v_size_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; 
v_size_1295_ = lean_ctor_get(v___y_1293_, 0);
v___x_1296_ = lean_unsigned_to_nat(1u);
v___x_1297_ = lean_nat_add(v_size_1295_, v___x_1296_);
lean_inc_ref(v___x_1265_);
v___x_1298_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1293_, v___x_1297_, v_i_1294_, v_key_1227_, v___x_1265_);
lean_dec(v_i_1294_);
v___y_1267_ = v___x_1298_;
goto v___jp_1266_;
}
v___jp_1299_:
{
lean_object* v___x_1300_; lean_object* v___x_1301_; 
v___x_1300_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__2___redArg(v_frameBackwardRuleCache_1254_);
lean_dec_ref(v_frameBackwardRuleCache_1254_);
v___x_1301_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Elab_Tactic_VCGen_mkLatticeOpRuleCached_spec__1___redArg(v___x_1300_, v_key_1227_);
switch(lean_obj_tag(v___x_1301_))
{
case 0:
{
lean_object* v_index_1302_; lean_object* v_size_1303_; lean_object* v___x_1304_; 
v_index_1302_ = lean_ctor_get(v___x_1301_, 0);
lean_inc(v_index_1302_);
lean_dec_ref_known(v___x_1301_, 3);
v_size_1303_ = lean_ctor_get(v___x_1300_, 0);
lean_inc(v_size_1303_);
lean_inc_ref(v___x_1265_);
v___x_1304_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_1300_, v_size_1303_, v_index_1302_, v_key_1227_, v___x_1265_);
lean_dec(v_index_1302_);
v___y_1267_ = v___x_1304_;
goto v___jp_1266_;
}
case 1:
{
lean_object* v_index_1305_; 
v_index_1305_ = lean_ctor_get(v___x_1301_, 0);
lean_inc(v_index_1305_);
lean_dec_ref_known(v___x_1301_, 1);
v___y_1293_ = v___x_1300_;
v_i_1294_ = v_index_1305_;
goto v___jp_1292_;
}
default: 
{
lean_object* v___x_1306_; lean_object* v___x_1307_; 
v___x_1306_ = lean_unsigned_to_nat(0u);
v___x_1307_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_1300_, v___x_1306_);
if (lean_obj_tag(v___x_1307_) == 0)
{
lean_object* v_index_1308_; 
v_index_1308_ = lean_ctor_get(v___x_1307_, 0);
lean_inc(v_index_1308_);
lean_dec_ref_known(v___x_1307_, 1);
v___y_1293_ = v___x_1300_;
v_i_1294_ = v_index_1308_;
goto v___jp_1292_;
}
else
{
lean_dec_ref_known(v_key_1227_, 2);
v___y_1267_ = v___x_1300_;
goto v___jp_1266_;
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
lean_object* v_a_1342_; lean_object* v___x_1344_; uint8_t v_isShared_1345_; uint8_t v_isSharedCheck_1349_; 
lean_del_object(v___x_1243_);
lean_dec(v_frameIdx_1241_);
lean_dec(v_splitVCIdx_1240_);
lean_dec_ref_known(v_key_1227_, 2);
v_a_1342_ = lean_ctor_get(v___x_1245_, 0);
v_isSharedCheck_1349_ = !lean_is_exclusive(v___x_1245_);
if (v_isSharedCheck_1349_ == 0)
{
v___x_1344_ = v___x_1245_;
v_isShared_1345_ = v_isSharedCheck_1349_;
goto v_resetjp_1343_;
}
else
{
lean_inc(v_a_1342_);
lean_dec(v___x_1245_);
v___x_1344_ = lean_box(0);
v_isShared_1345_ = v_isSharedCheck_1349_;
goto v_resetjp_1343_;
}
v_resetjp_1343_:
{
lean_object* v___x_1347_; 
if (v_isShared_1345_ == 0)
{
v___x_1347_ = v___x_1344_;
goto v_reusejp_1346_;
}
else
{
lean_object* v_reuseFailAlloc_1348_; 
v_reuseFailAlloc_1348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1348_, 0, v_a_1342_);
v___x_1347_ = v_reuseFailAlloc_1348_;
goto v_reusejp_1346_;
}
v_reusejp_1346_:
{
return v___x_1347_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_key_1227_, 2);
return v___x_1237_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_mkFrameBackwardRuleCached___redArg___boxed(lean_object* v_fp_1351_, lean_object* v_info_1352_, lean_object* v_a_1353_, lean_object* v_a_1354_, lean_object* v_a_1355_, lean_object* v_a_1356_, lean_object* v_a_1357_, lean_object* v_a_1358_, lean_object* v_a_1359_, lean_object* v_a_1360_){
_start:
{
lean_object* v_res_1361_; 
v_res_1361_ = l_Lean_Elab_Tactic_VCGen_mkFrameBackwardRuleCached___redArg(v_fp_1351_, v_info_1352_, v_a_1353_, v_a_1354_, v_a_1355_, v_a_1356_, v_a_1357_, v_a_1358_, v_a_1359_);
lean_dec(v_a_1359_);
lean_dec_ref(v_a_1358_);
lean_dec(v_a_1357_);
lean_dec_ref(v_a_1356_);
lean_dec(v_a_1355_);
lean_dec_ref(v_a_1354_);
lean_dec(v_a_1353_);
return v_res_1361_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_mkFrameBackwardRuleCached(lean_object* v_fp_1362_, lean_object* v_info_1363_, lean_object* v_a_1364_, lean_object* v_a_1365_, lean_object* v_a_1366_, lean_object* v_a_1367_, lean_object* v_a_1368_, lean_object* v_a_1369_, lean_object* v_a_1370_, lean_object* v_a_1371_, lean_object* v_a_1372_, lean_object* v_a_1373_, lean_object* v_a_1374_){
_start:
{
lean_object* v___x_1376_; 
v___x_1376_ = l_Lean_Elab_Tactic_VCGen_mkFrameBackwardRuleCached___redArg(v_fp_1362_, v_info_1363_, v_a_1365_, v_a_1369_, v_a_1370_, v_a_1371_, v_a_1372_, v_a_1373_, v_a_1374_);
return v___x_1376_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_mkFrameBackwardRuleCached___boxed(lean_object* v_fp_1377_, lean_object* v_info_1378_, lean_object* v_a_1379_, lean_object* v_a_1380_, lean_object* v_a_1381_, lean_object* v_a_1382_, lean_object* v_a_1383_, lean_object* v_a_1384_, lean_object* v_a_1385_, lean_object* v_a_1386_, lean_object* v_a_1387_, lean_object* v_a_1388_, lean_object* v_a_1389_, lean_object* v_a_1390_){
_start:
{
lean_object* v_res_1391_; 
v_res_1391_ = l_Lean_Elab_Tactic_VCGen_mkFrameBackwardRuleCached(v_fp_1377_, v_info_1378_, v_a_1379_, v_a_1380_, v_a_1381_, v_a_1382_, v_a_1383_, v_a_1384_, v_a_1385_, v_a_1386_, v_a_1387_, v_a_1388_, v_a_1389_);
lean_dec(v_a_1389_);
lean_dec_ref(v_a_1388_);
lean_dec(v_a_1387_);
lean_dec_ref(v_a_1386_);
lean_dec(v_a_1385_);
lean_dec_ref(v_a_1384_);
lean_dec(v_a_1383_);
lean_dec_ref(v_a_1382_);
lean_dec(v_a_1381_);
lean_dec(v_a_1380_);
lean_dec_ref(v_a_1379_);
return v_res_1391_;
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
