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
uint64_t lean_uint64_of_nat(lean_object*);
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
static lean_once_cell_t l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg___closed__0;
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
static uint64_t _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_177_; uint64_t v___x_178_; 
v___x_177_ = lean_unsigned_to_nat(1723u);
v___x_178_ = lean_uint64_of_nat(v___x_177_);
return v___x_178_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg(lean_object* v_m_179_, lean_object* v_a_180_){
_start:
{
lean_object* v_buckets_181_; lean_object* v_fst_182_; lean_object* v_snd_183_; lean_object* v___x_184_; uint64_t v___y_186_; 
v_buckets_181_ = lean_ctor_get(v_m_179_, 1);
v_fst_182_ = lean_ctor_get(v_a_180_, 0);
v_snd_183_ = lean_ctor_get(v_a_180_, 1);
v___x_184_ = lean_array_get_size(v_buckets_181_);
if (lean_obj_tag(v_fst_182_) == 0)
{
uint64_t v___x_209_; 
v___x_209_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg___closed__0);
v___y_186_ = v___x_209_;
goto v___jp_185_;
}
else
{
uint64_t v_hash_210_; 
v_hash_210_ = lean_ctor_get_uint64(v_fst_182_, sizeof(void*)*2);
v___y_186_ = v_hash_210_;
goto v___jp_185_;
}
v___jp_185_:
{
lean_object* v_fst_187_; lean_object* v_snd_188_; size_t v___x_189_; size_t v___x_190_; size_t v___x_191_; uint64_t v___x_192_; uint64_t v___x_193_; uint64_t v___x_194_; uint64_t v___x_195_; uint64_t v___x_196_; uint64_t v___x_197_; uint64_t v_fold_198_; uint64_t v___x_199_; uint64_t v___x_200_; uint64_t v___x_201_; size_t v___x_202_; size_t v___x_203_; size_t v___x_204_; size_t v___x_205_; size_t v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; 
v_fst_187_ = lean_ctor_get(v_snd_183_, 0);
v_snd_188_ = lean_ctor_get(v_snd_183_, 1);
v___x_189_ = lean_ptr_addr(v_fst_187_);
v___x_190_ = ((size_t)3ULL);
v___x_191_ = lean_usize_shift_right(v___x_189_, v___x_190_);
v___x_192_ = lean_usize_to_uint64(v___x_191_);
v___x_193_ = lean_uint64_of_nat(v_snd_188_);
v___x_194_ = lean_uint64_mix_hash(v___x_192_, v___x_193_);
v___x_195_ = lean_uint64_mix_hash(v___y_186_, v___x_194_);
v___x_196_ = 32ULL;
v___x_197_ = lean_uint64_shift_right(v___x_195_, v___x_196_);
v_fold_198_ = lean_uint64_xor(v___x_195_, v___x_197_);
v___x_199_ = 16ULL;
v___x_200_ = lean_uint64_shift_right(v_fold_198_, v___x_199_);
v___x_201_ = lean_uint64_xor(v_fold_198_, v___x_200_);
v___x_202_ = lean_uint64_to_usize(v___x_201_);
v___x_203_ = lean_usize_of_nat(v___x_184_);
v___x_204_ = ((size_t)1ULL);
v___x_205_ = lean_usize_sub(v___x_203_, v___x_204_);
v___x_206_ = lean_usize_land(v___x_202_, v___x_205_);
v___x_207_ = lean_array_uget_borrowed(v_buckets_181_, v___x_206_);
v___x_208_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0_spec__0___redArg(v_a_180_, v___x_207_);
return v___x_208_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg___boxed(lean_object* v_m_211_, lean_object* v_a_212_){
_start:
{
lean_object* v_res_213_; 
v_res_213_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg(v_m_211_, v_a_212_);
lean_dec_ref(v_a_212_);
lean_dec_ref(v_m_211_);
return v_res_213_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__4_spec__5_spec__6___redArg(lean_object* v_x_214_, lean_object* v_x_215_){
_start:
{
if (lean_obj_tag(v_x_215_) == 0)
{
return v_x_214_;
}
else
{
lean_object* v_key_216_; lean_object* v_value_217_; lean_object* v_tail_218_; lean_object* v___x_220_; uint8_t v_isShared_221_; uint8_t v_isSharedCheck_255_; 
v_key_216_ = lean_ctor_get(v_x_215_, 0);
v_value_217_ = lean_ctor_get(v_x_215_, 1);
v_tail_218_ = lean_ctor_get(v_x_215_, 2);
v_isSharedCheck_255_ = !lean_is_exclusive(v_x_215_);
if (v_isSharedCheck_255_ == 0)
{
v___x_220_ = v_x_215_;
v_isShared_221_ = v_isSharedCheck_255_;
goto v_resetjp_219_;
}
else
{
lean_inc(v_tail_218_);
lean_inc(v_value_217_);
lean_inc(v_key_216_);
lean_dec(v_x_215_);
v___x_220_ = lean_box(0);
v_isShared_221_ = v_isSharedCheck_255_;
goto v_resetjp_219_;
}
v_resetjp_219_:
{
lean_object* v_fst_222_; lean_object* v_snd_223_; lean_object* v___x_224_; uint64_t v___y_226_; 
v_fst_222_ = lean_ctor_get(v_key_216_, 0);
v_snd_223_ = lean_ctor_get(v_key_216_, 1);
v___x_224_ = lean_array_get_size(v_x_214_);
if (lean_obj_tag(v_fst_222_) == 0)
{
uint64_t v___x_253_; 
v___x_253_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg___closed__0);
v___y_226_ = v___x_253_;
goto v___jp_225_;
}
else
{
uint64_t v_hash_254_; 
v_hash_254_ = lean_ctor_get_uint64(v_fst_222_, sizeof(void*)*2);
v___y_226_ = v_hash_254_;
goto v___jp_225_;
}
v___jp_225_:
{
lean_object* v_fst_227_; lean_object* v_snd_228_; size_t v___x_229_; size_t v___x_230_; size_t v___x_231_; uint64_t v___x_232_; uint64_t v___x_233_; uint64_t v___x_234_; uint64_t v___x_235_; uint64_t v___x_236_; uint64_t v___x_237_; uint64_t v_fold_238_; uint64_t v___x_239_; uint64_t v___x_240_; uint64_t v___x_241_; size_t v___x_242_; size_t v___x_243_; size_t v___x_244_; size_t v___x_245_; size_t v___x_246_; lean_object* v___x_247_; lean_object* v___x_249_; 
v_fst_227_ = lean_ctor_get(v_snd_223_, 0);
v_snd_228_ = lean_ctor_get(v_snd_223_, 1);
v___x_229_ = lean_ptr_addr(v_fst_227_);
v___x_230_ = ((size_t)3ULL);
v___x_231_ = lean_usize_shift_right(v___x_229_, v___x_230_);
v___x_232_ = lean_usize_to_uint64(v___x_231_);
v___x_233_ = lean_uint64_of_nat(v_snd_228_);
v___x_234_ = lean_uint64_mix_hash(v___x_232_, v___x_233_);
v___x_235_ = lean_uint64_mix_hash(v___y_226_, v___x_234_);
v___x_236_ = 32ULL;
v___x_237_ = lean_uint64_shift_right(v___x_235_, v___x_236_);
v_fold_238_ = lean_uint64_xor(v___x_235_, v___x_237_);
v___x_239_ = 16ULL;
v___x_240_ = lean_uint64_shift_right(v_fold_238_, v___x_239_);
v___x_241_ = lean_uint64_xor(v_fold_238_, v___x_240_);
v___x_242_ = lean_uint64_to_usize(v___x_241_);
v___x_243_ = lean_usize_of_nat(v___x_224_);
v___x_244_ = ((size_t)1ULL);
v___x_245_ = lean_usize_sub(v___x_243_, v___x_244_);
v___x_246_ = lean_usize_land(v___x_242_, v___x_245_);
v___x_247_ = lean_array_uget_borrowed(v_x_214_, v___x_246_);
lean_inc(v___x_247_);
if (v_isShared_221_ == 0)
{
lean_ctor_set(v___x_220_, 2, v___x_247_);
v___x_249_ = v___x_220_;
goto v_reusejp_248_;
}
else
{
lean_object* v_reuseFailAlloc_252_; 
v_reuseFailAlloc_252_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_252_, 0, v_key_216_);
lean_ctor_set(v_reuseFailAlloc_252_, 1, v_value_217_);
lean_ctor_set(v_reuseFailAlloc_252_, 2, v___x_247_);
v___x_249_ = v_reuseFailAlloc_252_;
goto v_reusejp_248_;
}
v_reusejp_248_:
{
lean_object* v___x_250_; 
v___x_250_ = lean_array_uset(v_x_214_, v___x_246_, v___x_249_);
v_x_214_ = v___x_250_;
v_x_215_ = v_tail_218_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__4_spec__5___redArg(lean_object* v_i_256_, lean_object* v_source_257_, lean_object* v_target_258_){
_start:
{
lean_object* v___x_259_; uint8_t v___x_260_; 
v___x_259_ = lean_array_get_size(v_source_257_);
v___x_260_ = lean_nat_dec_lt(v_i_256_, v___x_259_);
if (v___x_260_ == 0)
{
lean_dec_ref(v_source_257_);
lean_dec(v_i_256_);
return v_target_258_;
}
else
{
lean_object* v_es_261_; lean_object* v___x_262_; lean_object* v_source_263_; lean_object* v_target_264_; lean_object* v___x_265_; lean_object* v___x_266_; 
v_es_261_ = lean_array_fget(v_source_257_, v_i_256_);
v___x_262_ = lean_box(0);
v_source_263_ = lean_array_fset(v_source_257_, v_i_256_, v___x_262_);
v_target_264_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__4_spec__5_spec__6___redArg(v_target_258_, v_es_261_);
v___x_265_ = lean_unsigned_to_nat(1u);
v___x_266_ = lean_nat_add(v_i_256_, v___x_265_);
lean_dec(v_i_256_);
v_i_256_ = v___x_266_;
v_source_257_ = v_source_263_;
v_target_258_ = v_target_264_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__4___redArg(lean_object* v_data_268_){
_start:
{
lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v_nbuckets_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; 
v___x_269_ = lean_array_get_size(v_data_268_);
v___x_270_ = lean_unsigned_to_nat(2u);
v_nbuckets_271_ = lean_nat_mul(v___x_269_, v___x_270_);
v___x_272_ = lean_unsigned_to_nat(0u);
v___x_273_ = lean_box(0);
v___x_274_ = lean_mk_array(v_nbuckets_271_, v___x_273_);
v___x_275_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__4_spec__5___redArg(v___x_272_, v_data_268_, v___x_274_);
return v___x_275_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__3___redArg(lean_object* v_a_276_, lean_object* v_x_277_){
_start:
{
if (lean_obj_tag(v_x_277_) == 0)
{
uint8_t v___x_278_; 
v___x_278_ = 0;
return v___x_278_;
}
else
{
lean_object* v_key_279_; lean_object* v_tail_280_; uint8_t v___y_282_; lean_object* v_fst_284_; lean_object* v_snd_285_; lean_object* v_fst_286_; lean_object* v_snd_287_; uint8_t v___x_288_; 
v_key_279_ = lean_ctor_get(v_x_277_, 0);
v_tail_280_ = lean_ctor_get(v_x_277_, 2);
v_fst_284_ = lean_ctor_get(v_key_279_, 0);
v_snd_285_ = lean_ctor_get(v_key_279_, 1);
v_fst_286_ = lean_ctor_get(v_a_276_, 0);
v_snd_287_ = lean_ctor_get(v_a_276_, 1);
v___x_288_ = lean_name_eq(v_fst_284_, v_fst_286_);
if (v___x_288_ == 0)
{
v___y_282_ = v___x_288_;
goto v___jp_281_;
}
else
{
lean_object* v_fst_289_; lean_object* v_snd_290_; lean_object* v_fst_291_; lean_object* v_snd_292_; size_t v___x_293_; size_t v___x_294_; uint8_t v___x_295_; 
v_fst_289_ = lean_ctor_get(v_snd_285_, 0);
v_snd_290_ = lean_ctor_get(v_snd_285_, 1);
v_fst_291_ = lean_ctor_get(v_snd_287_, 0);
v_snd_292_ = lean_ctor_get(v_snd_287_, 1);
v___x_293_ = lean_ptr_addr(v_fst_289_);
v___x_294_ = lean_ptr_addr(v_fst_291_);
v___x_295_ = lean_usize_dec_eq(v___x_293_, v___x_294_);
if (v___x_295_ == 0)
{
v___y_282_ = v___x_295_;
goto v___jp_281_;
}
else
{
uint8_t v___x_296_; 
v___x_296_ = lean_nat_dec_eq(v_snd_290_, v_snd_292_);
v___y_282_ = v___x_296_;
goto v___jp_281_;
}
}
v___jp_281_:
{
if (v___y_282_ == 0)
{
v_x_277_ = v_tail_280_;
goto _start;
}
else
{
return v___y_282_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__3___redArg___boxed(lean_object* v_a_297_, lean_object* v_x_298_){
_start:
{
uint8_t v_res_299_; lean_object* v_r_300_; 
v_res_299_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__3___redArg(v_a_297_, v_x_298_);
lean_dec(v_x_298_);
lean_dec_ref(v_a_297_);
v_r_300_ = lean_box(v_res_299_);
return v_r_300_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__5___redArg(lean_object* v_a_301_, lean_object* v_b_302_, lean_object* v_x_303_){
_start:
{
if (lean_obj_tag(v_x_303_) == 0)
{
lean_dec(v_b_302_);
lean_dec_ref(v_a_301_);
return v_x_303_;
}
else
{
lean_object* v_key_304_; lean_object* v_value_305_; lean_object* v_tail_306_; lean_object* v___x_308_; uint8_t v_isShared_309_; uint8_t v_isSharedCheck_332_; 
v_key_304_ = lean_ctor_get(v_x_303_, 0);
v_value_305_ = lean_ctor_get(v_x_303_, 1);
v_tail_306_ = lean_ctor_get(v_x_303_, 2);
v_isSharedCheck_332_ = !lean_is_exclusive(v_x_303_);
if (v_isSharedCheck_332_ == 0)
{
v___x_308_ = v_x_303_;
v_isShared_309_ = v_isSharedCheck_332_;
goto v_resetjp_307_;
}
else
{
lean_inc(v_tail_306_);
lean_inc(v_value_305_);
lean_inc(v_key_304_);
lean_dec(v_x_303_);
v___x_308_ = lean_box(0);
v_isShared_309_ = v_isSharedCheck_332_;
goto v_resetjp_307_;
}
v_resetjp_307_:
{
uint8_t v___y_311_; lean_object* v_fst_319_; lean_object* v_snd_320_; lean_object* v_fst_321_; lean_object* v_snd_322_; uint8_t v___x_323_; 
v_fst_319_ = lean_ctor_get(v_key_304_, 0);
v_snd_320_ = lean_ctor_get(v_key_304_, 1);
v_fst_321_ = lean_ctor_get(v_a_301_, 0);
v_snd_322_ = lean_ctor_get(v_a_301_, 1);
v___x_323_ = lean_name_eq(v_fst_319_, v_fst_321_);
if (v___x_323_ == 0)
{
v___y_311_ = v___x_323_;
goto v___jp_310_;
}
else
{
lean_object* v_fst_324_; lean_object* v_snd_325_; lean_object* v_fst_326_; lean_object* v_snd_327_; size_t v___x_328_; size_t v___x_329_; uint8_t v___x_330_; 
v_fst_324_ = lean_ctor_get(v_snd_320_, 0);
v_snd_325_ = lean_ctor_get(v_snd_320_, 1);
v_fst_326_ = lean_ctor_get(v_snd_322_, 0);
v_snd_327_ = lean_ctor_get(v_snd_322_, 1);
v___x_328_ = lean_ptr_addr(v_fst_324_);
v___x_329_ = lean_ptr_addr(v_fst_326_);
v___x_330_ = lean_usize_dec_eq(v___x_328_, v___x_329_);
if (v___x_330_ == 0)
{
v___y_311_ = v___x_330_;
goto v___jp_310_;
}
else
{
uint8_t v___x_331_; 
v___x_331_ = lean_nat_dec_eq(v_snd_325_, v_snd_327_);
v___y_311_ = v___x_331_;
goto v___jp_310_;
}
}
v___jp_310_:
{
if (v___y_311_ == 0)
{
lean_object* v___x_312_; lean_object* v___x_314_; 
v___x_312_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__5___redArg(v_a_301_, v_b_302_, v_tail_306_);
if (v_isShared_309_ == 0)
{
lean_ctor_set(v___x_308_, 2, v___x_312_);
v___x_314_ = v___x_308_;
goto v_reusejp_313_;
}
else
{
lean_object* v_reuseFailAlloc_315_; 
v_reuseFailAlloc_315_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_315_, 0, v_key_304_);
lean_ctor_set(v_reuseFailAlloc_315_, 1, v_value_305_);
lean_ctor_set(v_reuseFailAlloc_315_, 2, v___x_312_);
v___x_314_ = v_reuseFailAlloc_315_;
goto v_reusejp_313_;
}
v_reusejp_313_:
{
return v___x_314_;
}
}
else
{
lean_object* v___x_317_; 
lean_dec(v_value_305_);
lean_dec(v_key_304_);
if (v_isShared_309_ == 0)
{
lean_ctor_set(v___x_308_, 1, v_b_302_);
lean_ctor_set(v___x_308_, 0, v_a_301_);
v___x_317_ = v___x_308_;
goto v_reusejp_316_;
}
else
{
lean_object* v_reuseFailAlloc_318_; 
v_reuseFailAlloc_318_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_318_, 0, v_a_301_);
lean_ctor_set(v_reuseFailAlloc_318_, 1, v_b_302_);
lean_ctor_set(v_reuseFailAlloc_318_, 2, v_tail_306_);
v___x_317_ = v_reuseFailAlloc_318_;
goto v_reusejp_316_;
}
v_reusejp_316_:
{
return v___x_317_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2___redArg(lean_object* v_m_333_, lean_object* v_a_334_, lean_object* v_b_335_){
_start:
{
lean_object* v_size_336_; lean_object* v_buckets_337_; lean_object* v___x_339_; uint8_t v_isShared_340_; uint8_t v_isSharedCheck_394_; 
v_size_336_ = lean_ctor_get(v_m_333_, 0);
v_buckets_337_ = lean_ctor_get(v_m_333_, 1);
v_isSharedCheck_394_ = !lean_is_exclusive(v_m_333_);
if (v_isSharedCheck_394_ == 0)
{
v___x_339_ = v_m_333_;
v_isShared_340_ = v_isSharedCheck_394_;
goto v_resetjp_338_;
}
else
{
lean_inc(v_buckets_337_);
lean_inc(v_size_336_);
lean_dec(v_m_333_);
v___x_339_ = lean_box(0);
v_isShared_340_ = v_isSharedCheck_394_;
goto v_resetjp_338_;
}
v_resetjp_338_:
{
lean_object* v_fst_341_; lean_object* v_snd_342_; lean_object* v___x_343_; uint64_t v___y_345_; 
v_fst_341_ = lean_ctor_get(v_a_334_, 0);
v_snd_342_ = lean_ctor_get(v_a_334_, 1);
v___x_343_ = lean_array_get_size(v_buckets_337_);
if (lean_obj_tag(v_fst_341_) == 0)
{
uint64_t v___x_392_; 
v___x_392_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg___closed__0);
v___y_345_ = v___x_392_;
goto v___jp_344_;
}
else
{
uint64_t v_hash_393_; 
v_hash_393_ = lean_ctor_get_uint64(v_fst_341_, sizeof(void*)*2);
v___y_345_ = v_hash_393_;
goto v___jp_344_;
}
v___jp_344_:
{
lean_object* v_fst_346_; lean_object* v_snd_347_; size_t v___x_348_; size_t v___x_349_; size_t v___x_350_; uint64_t v___x_351_; uint64_t v___x_352_; uint64_t v___x_353_; uint64_t v___x_354_; uint64_t v___x_355_; uint64_t v___x_356_; uint64_t v_fold_357_; uint64_t v___x_358_; uint64_t v___x_359_; uint64_t v___x_360_; size_t v___x_361_; size_t v___x_362_; size_t v___x_363_; size_t v___x_364_; size_t v___x_365_; lean_object* v_bkt_366_; uint8_t v___x_367_; 
v_fst_346_ = lean_ctor_get(v_snd_342_, 0);
v_snd_347_ = lean_ctor_get(v_snd_342_, 1);
v___x_348_ = lean_ptr_addr(v_fst_346_);
v___x_349_ = ((size_t)3ULL);
v___x_350_ = lean_usize_shift_right(v___x_348_, v___x_349_);
v___x_351_ = lean_usize_to_uint64(v___x_350_);
v___x_352_ = lean_uint64_of_nat(v_snd_347_);
v___x_353_ = lean_uint64_mix_hash(v___x_351_, v___x_352_);
v___x_354_ = lean_uint64_mix_hash(v___y_345_, v___x_353_);
v___x_355_ = 32ULL;
v___x_356_ = lean_uint64_shift_right(v___x_354_, v___x_355_);
v_fold_357_ = lean_uint64_xor(v___x_354_, v___x_356_);
v___x_358_ = 16ULL;
v___x_359_ = lean_uint64_shift_right(v_fold_357_, v___x_358_);
v___x_360_ = lean_uint64_xor(v_fold_357_, v___x_359_);
v___x_361_ = lean_uint64_to_usize(v___x_360_);
v___x_362_ = lean_usize_of_nat(v___x_343_);
v___x_363_ = ((size_t)1ULL);
v___x_364_ = lean_usize_sub(v___x_362_, v___x_363_);
v___x_365_ = lean_usize_land(v___x_361_, v___x_364_);
v_bkt_366_ = lean_array_uget_borrowed(v_buckets_337_, v___x_365_);
v___x_367_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__3___redArg(v_a_334_, v_bkt_366_);
if (v___x_367_ == 0)
{
lean_object* v___x_368_; lean_object* v_size_x27_369_; lean_object* v___x_370_; lean_object* v_buckets_x27_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; uint8_t v___x_377_; 
v___x_368_ = lean_unsigned_to_nat(1u);
v_size_x27_369_ = lean_nat_add(v_size_336_, v___x_368_);
lean_dec(v_size_336_);
lean_inc(v_bkt_366_);
v___x_370_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_370_, 0, v_a_334_);
lean_ctor_set(v___x_370_, 1, v_b_335_);
lean_ctor_set(v___x_370_, 2, v_bkt_366_);
v_buckets_x27_371_ = lean_array_uset(v_buckets_337_, v___x_365_, v___x_370_);
v___x_372_ = lean_unsigned_to_nat(4u);
v___x_373_ = lean_nat_mul(v_size_x27_369_, v___x_372_);
v___x_374_ = lean_unsigned_to_nat(3u);
v___x_375_ = lean_nat_div(v___x_373_, v___x_374_);
lean_dec(v___x_373_);
v___x_376_ = lean_array_get_size(v_buckets_x27_371_);
v___x_377_ = lean_nat_dec_le(v___x_375_, v___x_376_);
lean_dec(v___x_375_);
if (v___x_377_ == 0)
{
lean_object* v_val_378_; lean_object* v___x_380_; 
v_val_378_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__4___redArg(v_buckets_x27_371_);
if (v_isShared_340_ == 0)
{
lean_ctor_set(v___x_339_, 1, v_val_378_);
lean_ctor_set(v___x_339_, 0, v_size_x27_369_);
v___x_380_ = v___x_339_;
goto v_reusejp_379_;
}
else
{
lean_object* v_reuseFailAlloc_381_; 
v_reuseFailAlloc_381_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_381_, 0, v_size_x27_369_);
lean_ctor_set(v_reuseFailAlloc_381_, 1, v_val_378_);
v___x_380_ = v_reuseFailAlloc_381_;
goto v_reusejp_379_;
}
v_reusejp_379_:
{
return v___x_380_;
}
}
else
{
lean_object* v___x_383_; 
if (v_isShared_340_ == 0)
{
lean_ctor_set(v___x_339_, 1, v_buckets_x27_371_);
lean_ctor_set(v___x_339_, 0, v_size_x27_369_);
v___x_383_ = v___x_339_;
goto v_reusejp_382_;
}
else
{
lean_object* v_reuseFailAlloc_384_; 
v_reuseFailAlloc_384_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_384_, 0, v_size_x27_369_);
lean_ctor_set(v_reuseFailAlloc_384_, 1, v_buckets_x27_371_);
v___x_383_ = v_reuseFailAlloc_384_;
goto v_reusejp_382_;
}
v_reusejp_382_:
{
return v___x_383_;
}
}
}
else
{
lean_object* v___x_385_; lean_object* v_buckets_x27_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_390_; 
lean_inc(v_bkt_366_);
v___x_385_ = lean_box(0);
v_buckets_x27_386_ = lean_array_uset(v_buckets_337_, v___x_365_, v___x_385_);
v___x_387_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__5___redArg(v_a_334_, v_b_335_, v_bkt_366_);
v___x_388_ = lean_array_uset(v_buckets_x27_386_, v___x_365_, v___x_387_);
if (v_isShared_340_ == 0)
{
lean_ctor_set(v___x_339_, 1, v___x_388_);
v___x_390_ = v___x_339_;
goto v_reusejp_389_;
}
else
{
lean_object* v_reuseFailAlloc_391_; 
v_reuseFailAlloc_391_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_391_, 0, v_size_336_);
lean_ctor_set(v_reuseFailAlloc_391_, 1, v___x_388_);
v___x_390_ = v_reuseFailAlloc_391_;
goto v_reusejp_389_;
}
v_reusejp_389_:
{
return v___x_390_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached(lean_object* v_specThm_397_, lean_object* v_info_398_, lean_object* v_a_399_, lean_object* v_a_400_, lean_object* v_a_401_, lean_object* v_a_402_, lean_object* v_a_403_, lean_object* v_a_404_, lean_object* v_a_405_, lean_object* v_a_406_, lean_object* v_a_407_, lean_object* v_a_408_, lean_object* v_a_409_){
_start:
{
lean_object* v___x_411_; lean_object* v_proof_412_; lean_object* v_excessArgs_413_; lean_object* v_specBackwardRuleCache_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v_key_419_; lean_object* v___x_420_; 
v___x_411_ = lean_st_ref_get(v_a_400_);
v_proof_412_ = lean_ctor_get(v_specThm_397_, 1);
v_excessArgs_413_ = lean_ctor_get(v_info_398_, 2);
v_specBackwardRuleCache_414_ = lean_ctor_get(v___x_411_, 0);
lean_inc_ref(v_specBackwardRuleCache_414_);
lean_dec(v___x_411_);
v___x_415_ = l_Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecProof_key(v_proof_412_);
v___x_416_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_WPApp_instWP(v_info_398_);
v___x_417_ = lean_array_get_size(v_excessArgs_413_);
v___x_418_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_418_, 0, v___x_416_);
lean_ctor_set(v___x_418_, 1, v___x_417_);
v_key_419_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_key_419_, 0, v___x_415_);
lean_ctor_set(v_key_419_, 1, v___x_418_);
v___x_420_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg(v_specBackwardRuleCache_414_, v_key_419_);
lean_dec_ref(v_specBackwardRuleCache_414_);
if (lean_obj_tag(v___x_420_) == 1)
{
lean_object* v___x_421_; 
lean_dec_ref_known(v_key_419_, 2);
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
v___x_422_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached___closed__0));
v___f_423_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached___lam__0___boxed), 15, 3);
lean_closure_set(v___f_423_, 0, v_specThm_397_);
lean_closure_set(v___f_423_, 1, v_info_398_);
lean_closure_set(v___f_423_, 2, v___x_422_);
v___x_424_ = 0;
v___x_425_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__1___redArg(v___f_423_, v___x_424_, v_a_399_, v_a_400_, v_a_401_, v_a_402_, v_a_403_, v_a_404_, v_a_405_, v_a_406_, v_a_407_, v_a_408_, v_a_409_);
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
lean_dec_ref_known(v_key_419_, 2);
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
lean_object* v___x_444_; lean_object* v_specBackwardRuleCache_445_; lean_object* v_splitBackwardRuleCache_446_; lean_object* v_latticeBackwardRuleCache_447_; lean_object* v_frameBackwardRuleCache_448_; lean_object* v_frameDB_449_; lean_object* v_invariants_450_; lean_object* v_vcs_451_; lean_object* v_simpState_452_; lean_object* v_fuel_453_; lean_object* v_inlineHandledInvariants_454_; lean_object* v___x_456_; uint8_t v_isShared_457_; uint8_t v_isSharedCheck_469_; 
v___x_444_ = lean_st_ref_take(v_a_400_);
v_specBackwardRuleCache_445_ = lean_ctor_get(v___x_444_, 0);
v_splitBackwardRuleCache_446_ = lean_ctor_get(v___x_444_, 1);
v_latticeBackwardRuleCache_447_ = lean_ctor_get(v___x_444_, 2);
v_frameBackwardRuleCache_448_ = lean_ctor_get(v___x_444_, 3);
v_frameDB_449_ = lean_ctor_get(v___x_444_, 4);
v_invariants_450_ = lean_ctor_get(v___x_444_, 5);
v_vcs_451_ = lean_ctor_get(v___x_444_, 6);
v_simpState_452_ = lean_ctor_get(v___x_444_, 7);
v_fuel_453_ = lean_ctor_get(v___x_444_, 8);
v_inlineHandledInvariants_454_ = lean_ctor_get(v___x_444_, 9);
v_isSharedCheck_469_ = !lean_is_exclusive(v___x_444_);
if (v_isSharedCheck_469_ == 0)
{
v___x_456_ = v___x_444_;
v_isShared_457_ = v_isSharedCheck_469_;
goto v_resetjp_455_;
}
else
{
lean_inc(v_inlineHandledInvariants_454_);
lean_inc(v_fuel_453_);
lean_inc(v_simpState_452_);
lean_inc(v_vcs_451_);
lean_inc(v_invariants_450_);
lean_inc(v_frameDB_449_);
lean_inc(v_frameBackwardRuleCache_448_);
lean_inc(v_latticeBackwardRuleCache_447_);
lean_inc(v_splitBackwardRuleCache_446_);
lean_inc(v_specBackwardRuleCache_445_);
lean_dec(v___x_444_);
v___x_456_ = lean_box(0);
v_isShared_457_ = v_isSharedCheck_469_;
goto v_resetjp_455_;
}
v_resetjp_455_:
{
lean_object* v___x_459_; 
lean_inc(v_a_440_);
if (v_isShared_438_ == 0)
{
lean_ctor_set(v___x_437_, 0, v_a_440_);
v___x_459_ = v___x_437_;
goto v_reusejp_458_;
}
else
{
lean_object* v_reuseFailAlloc_468_; 
v_reuseFailAlloc_468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_468_, 0, v_a_440_);
v___x_459_ = v_reuseFailAlloc_468_;
goto v_reusejp_458_;
}
v_reusejp_458_:
{
lean_object* v___x_460_; lean_object* v___x_462_; 
v___x_460_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2___redArg(v_specBackwardRuleCache_445_, v_key_419_, v_a_440_);
if (v_isShared_457_ == 0)
{
lean_ctor_set(v___x_456_, 0, v___x_460_);
v___x_462_ = v___x_456_;
goto v_reusejp_461_;
}
else
{
lean_object* v_reuseFailAlloc_467_; 
v_reuseFailAlloc_467_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_467_, 0, v___x_460_);
lean_ctor_set(v_reuseFailAlloc_467_, 1, v_splitBackwardRuleCache_446_);
lean_ctor_set(v_reuseFailAlloc_467_, 2, v_latticeBackwardRuleCache_447_);
lean_ctor_set(v_reuseFailAlloc_467_, 3, v_frameBackwardRuleCache_448_);
lean_ctor_set(v_reuseFailAlloc_467_, 4, v_frameDB_449_);
lean_ctor_set(v_reuseFailAlloc_467_, 5, v_invariants_450_);
lean_ctor_set(v_reuseFailAlloc_467_, 6, v_vcs_451_);
lean_ctor_set(v_reuseFailAlloc_467_, 7, v_simpState_452_);
lean_ctor_set(v_reuseFailAlloc_467_, 8, v_fuel_453_);
lean_ctor_set(v_reuseFailAlloc_467_, 9, v_inlineHandledInvariants_454_);
v___x_462_ = v_reuseFailAlloc_467_;
goto v_reusejp_461_;
}
v_reusejp_461_:
{
lean_object* v___x_463_; lean_object* v___x_465_; 
v___x_463_ = lean_st_ref_set(v_a_400_, v___x_462_);
if (v_isShared_443_ == 0)
{
lean_ctor_set(v___x_442_, 0, v___x_459_);
v___x_465_ = v___x_442_;
goto v_reusejp_464_;
}
else
{
lean_object* v_reuseFailAlloc_466_; 
v_reuseFailAlloc_466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_466_, 0, v___x_459_);
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
lean_dec_ref_known(v_key_419_, 2);
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
lean_dec_ref_known(v_key_419_, 2);
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
lean_dec_ref_known(v_key_419_, 2);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached___boxed(lean_object* v_specThm_493_, lean_object* v_info_494_, lean_object* v_a_495_, lean_object* v_a_496_, lean_object* v_a_497_, lean_object* v_a_498_, lean_object* v_a_499_, lean_object* v_a_500_, lean_object* v_a_501_, lean_object* v_a_502_, lean_object* v_a_503_, lean_object* v_a_504_, lean_object* v_a_505_, lean_object* v_a_506_){
_start:
{
lean_object* v_res_507_; 
v_res_507_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached(v_specThm_493_, v_info_494_, v_a_495_, v_a_496_, v_a_497_, v_a_498_, v_a_499_, v_a_500_, v_a_501_, v_a_502_, v_a_503_, v_a_504_, v_a_505_);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0(lean_object* v_00_u03b2_508_, lean_object* v_m_509_, lean_object* v_a_510_){
_start:
{
lean_object* v___x_511_; 
v___x_511_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg(v_m_509_, v_a_510_);
return v___x_511_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___boxed(lean_object* v_00_u03b2_512_, lean_object* v_m_513_, lean_object* v_a_514_){
_start:
{
lean_object* v_res_515_; 
v_res_515_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0(v_00_u03b2_512_, v_m_513_, v_a_514_);
lean_dec_ref(v_a_514_);
lean_dec_ref(v_m_513_);
return v_res_515_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2(lean_object* v_00_u03b2_516_, lean_object* v_m_517_, lean_object* v_a_518_, lean_object* v_b_519_){
_start:
{
lean_object* v___x_520_; 
v___x_520_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2___redArg(v_m_517_, v_a_518_, v_b_519_);
return v___x_520_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0_spec__0(lean_object* v_00_u03b2_521_, lean_object* v_a_522_, lean_object* v_x_523_){
_start:
{
lean_object* v___x_524_; 
v___x_524_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0_spec__0___redArg(v_a_522_, v_x_523_);
return v___x_524_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0_spec__0___boxed(lean_object* v_00_u03b2_525_, lean_object* v_a_526_, lean_object* v_x_527_){
_start:
{
lean_object* v_res_528_; 
v_res_528_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0_spec__0(v_00_u03b2_525_, v_a_526_, v_x_527_);
lean_dec(v_x_527_);
lean_dec_ref(v_a_526_);
return v_res_528_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__3(lean_object* v_00_u03b2_529_, lean_object* v_a_530_, lean_object* v_x_531_){
_start:
{
uint8_t v___x_532_; 
v___x_532_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__3___redArg(v_a_530_, v_x_531_);
return v___x_532_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__3___boxed(lean_object* v_00_u03b2_533_, lean_object* v_a_534_, lean_object* v_x_535_){
_start:
{
uint8_t v_res_536_; lean_object* v_r_537_; 
v_res_536_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__3(v_00_u03b2_533_, v_a_534_, v_x_535_);
lean_dec(v_x_535_);
lean_dec_ref(v_a_534_);
v_r_537_ = lean_box(v_res_536_);
return v_r_537_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__4(lean_object* v_00_u03b2_538_, lean_object* v_data_539_){
_start:
{
lean_object* v___x_540_; 
v___x_540_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__4___redArg(v_data_539_);
return v___x_540_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__5(lean_object* v_00_u03b2_541_, lean_object* v_a_542_, lean_object* v_b_543_, lean_object* v_x_544_){
_start:
{
lean_object* v___x_545_; 
v___x_545_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__5___redArg(v_a_542_, v_b_543_, v_x_544_);
return v___x_545_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_546_, lean_object* v_i_547_, lean_object* v_source_548_, lean_object* v_target_549_){
_start:
{
lean_object* v___x_550_; 
v___x_550_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__4_spec__5___redArg(v_i_547_, v_source_548_, v_target_549_);
return v___x_550_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__4_spec__5_spec__6(lean_object* v_00_u03b2_551_, lean_object* v_x_552_, lean_object* v_x_553_){
_start:
{
lean_object* v___x_554_; 
v___x_554_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__4_spec__5_spec__6___redArg(v_x_552_, v_x_553_);
return v___x_554_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForSplitCached___redArg(lean_object* v_splitInfo_561_, lean_object* v_info_562_, lean_object* v_a_563_, lean_object* v_a_564_, lean_object* v_a_565_, lean_object* v_a_566_, lean_object* v_a_567_, lean_object* v_a_568_, lean_object* v_a_569_){
_start:
{
lean_object* v___y_572_; 
switch(lean_obj_tag(v_splitInfo_561_))
{
case 0:
{
lean_object* v___x_620_; 
v___x_620_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForSplitCached___redArg___closed__1));
v___y_572_ = v___x_620_;
goto v___jp_571_;
}
case 1:
{
lean_object* v___x_621_; 
v___x_621_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForSplitCached___redArg___closed__3));
v___y_572_ = v___x_621_;
goto v___jp_571_;
}
default: 
{
lean_object* v_matcherApp_622_; lean_object* v_matcherName_623_; 
v_matcherApp_622_ = lean_ctor_get(v_splitInfo_561_, 0);
v_matcherName_623_ = lean_ctor_get(v_matcherApp_622_, 1);
lean_inc(v_matcherName_623_);
v___y_572_ = v_matcherName_623_;
goto v___jp_571_;
}
}
v___jp_571_:
{
lean_object* v___x_573_; lean_object* v_excessArgs_574_; lean_object* v_splitBackwardRuleCache_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v_key_579_; lean_object* v___x_580_; 
v___x_573_ = lean_st_ref_get(v_a_563_);
v_excessArgs_574_ = lean_ctor_get(v_info_562_, 2);
v_splitBackwardRuleCache_575_ = lean_ctor_get(v___x_573_, 1);
lean_inc_ref(v_splitBackwardRuleCache_575_);
lean_dec(v___x_573_);
v___x_576_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_WPApp_instWP(v_info_562_);
v___x_577_ = lean_array_get_size(v_excessArgs_574_);
v___x_578_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_578_, 0, v___x_576_);
lean_ctor_set(v___x_578_, 1, v___x_577_);
v_key_579_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_key_579_, 0, v___y_572_);
lean_ctor_set(v_key_579_, 1, v___x_578_);
v___x_580_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg(v_splitBackwardRuleCache_575_, v_key_579_);
lean_dec_ref(v_splitBackwardRuleCache_575_);
if (lean_obj_tag(v___x_580_) == 1)
{
lean_object* v_val_581_; lean_object* v___x_583_; uint8_t v_isShared_584_; uint8_t v_isSharedCheck_588_; 
lean_dec_ref_known(v_key_579_, 2);
lean_dec_ref(v_info_562_);
lean_dec_ref(v_splitInfo_561_);
v_val_581_ = lean_ctor_get(v___x_580_, 0);
v_isSharedCheck_588_ = !lean_is_exclusive(v___x_580_);
if (v_isSharedCheck_588_ == 0)
{
v___x_583_ = v___x_580_;
v_isShared_584_ = v_isSharedCheck_588_;
goto v_resetjp_582_;
}
else
{
lean_inc(v_val_581_);
lean_dec(v___x_580_);
v___x_583_ = lean_box(0);
v_isShared_584_ = v_isSharedCheck_588_;
goto v_resetjp_582_;
}
v_resetjp_582_:
{
lean_object* v___x_586_; 
if (v_isShared_584_ == 0)
{
lean_ctor_set_tag(v___x_583_, 0);
v___x_586_ = v___x_583_;
goto v_reusejp_585_;
}
else
{
lean_object* v_reuseFailAlloc_587_; 
v_reuseFailAlloc_587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_587_, 0, v_val_581_);
v___x_586_ = v_reuseFailAlloc_587_;
goto v_reusejp_585_;
}
v_reusejp_585_:
{
return v___x_586_;
}
}
}
else
{
lean_object* v___x_589_; 
lean_dec(v___x_580_);
v___x_589_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForSplit(v_splitInfo_561_, v_info_562_, v_a_566_, v_a_567_, v_a_568_, v_a_569_);
if (lean_obj_tag(v___x_589_) == 0)
{
lean_object* v_a_590_; lean_object* v___x_591_; 
v_a_590_ = lean_ctor_get(v___x_589_, 0);
lean_inc(v_a_590_);
lean_dec_ref_known(v___x_589_, 1);
v___x_591_ = l_Lean_Meta_Sym_BackwardRule_shareCommon(v_a_590_, v_a_564_, v_a_565_, v_a_566_, v_a_567_, v_a_568_, v_a_569_);
if (lean_obj_tag(v___x_591_) == 0)
{
lean_object* v_a_592_; lean_object* v___x_594_; uint8_t v_isShared_595_; uint8_t v_isSharedCheck_619_; 
v_a_592_ = lean_ctor_get(v___x_591_, 0);
v_isSharedCheck_619_ = !lean_is_exclusive(v___x_591_);
if (v_isSharedCheck_619_ == 0)
{
v___x_594_ = v___x_591_;
v_isShared_595_ = v_isSharedCheck_619_;
goto v_resetjp_593_;
}
else
{
lean_inc(v_a_592_);
lean_dec(v___x_591_);
v___x_594_ = lean_box(0);
v_isShared_595_ = v_isSharedCheck_619_;
goto v_resetjp_593_;
}
v_resetjp_593_:
{
lean_object* v___x_596_; lean_object* v_specBackwardRuleCache_597_; lean_object* v_splitBackwardRuleCache_598_; lean_object* v_latticeBackwardRuleCache_599_; lean_object* v_frameBackwardRuleCache_600_; lean_object* v_frameDB_601_; lean_object* v_invariants_602_; lean_object* v_vcs_603_; lean_object* v_simpState_604_; lean_object* v_fuel_605_; lean_object* v_inlineHandledInvariants_606_; lean_object* v___x_608_; uint8_t v_isShared_609_; uint8_t v_isSharedCheck_618_; 
v___x_596_ = lean_st_ref_take(v_a_563_);
v_specBackwardRuleCache_597_ = lean_ctor_get(v___x_596_, 0);
v_splitBackwardRuleCache_598_ = lean_ctor_get(v___x_596_, 1);
v_latticeBackwardRuleCache_599_ = lean_ctor_get(v___x_596_, 2);
v_frameBackwardRuleCache_600_ = lean_ctor_get(v___x_596_, 3);
v_frameDB_601_ = lean_ctor_get(v___x_596_, 4);
v_invariants_602_ = lean_ctor_get(v___x_596_, 5);
v_vcs_603_ = lean_ctor_get(v___x_596_, 6);
v_simpState_604_ = lean_ctor_get(v___x_596_, 7);
v_fuel_605_ = lean_ctor_get(v___x_596_, 8);
v_inlineHandledInvariants_606_ = lean_ctor_get(v___x_596_, 9);
v_isSharedCheck_618_ = !lean_is_exclusive(v___x_596_);
if (v_isSharedCheck_618_ == 0)
{
v___x_608_ = v___x_596_;
v_isShared_609_ = v_isSharedCheck_618_;
goto v_resetjp_607_;
}
else
{
lean_inc(v_inlineHandledInvariants_606_);
lean_inc(v_fuel_605_);
lean_inc(v_simpState_604_);
lean_inc(v_vcs_603_);
lean_inc(v_invariants_602_);
lean_inc(v_frameDB_601_);
lean_inc(v_frameBackwardRuleCache_600_);
lean_inc(v_latticeBackwardRuleCache_599_);
lean_inc(v_splitBackwardRuleCache_598_);
lean_inc(v_specBackwardRuleCache_597_);
lean_dec(v___x_596_);
v___x_608_ = lean_box(0);
v_isShared_609_ = v_isSharedCheck_618_;
goto v_resetjp_607_;
}
v_resetjp_607_:
{
lean_object* v___x_610_; lean_object* v___x_612_; 
lean_inc(v_a_592_);
v___x_610_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2___redArg(v_splitBackwardRuleCache_598_, v_key_579_, v_a_592_);
if (v_isShared_609_ == 0)
{
lean_ctor_set(v___x_608_, 1, v___x_610_);
v___x_612_ = v___x_608_;
goto v_reusejp_611_;
}
else
{
lean_object* v_reuseFailAlloc_617_; 
v_reuseFailAlloc_617_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_617_, 0, v_specBackwardRuleCache_597_);
lean_ctor_set(v_reuseFailAlloc_617_, 1, v___x_610_);
lean_ctor_set(v_reuseFailAlloc_617_, 2, v_latticeBackwardRuleCache_599_);
lean_ctor_set(v_reuseFailAlloc_617_, 3, v_frameBackwardRuleCache_600_);
lean_ctor_set(v_reuseFailAlloc_617_, 4, v_frameDB_601_);
lean_ctor_set(v_reuseFailAlloc_617_, 5, v_invariants_602_);
lean_ctor_set(v_reuseFailAlloc_617_, 6, v_vcs_603_);
lean_ctor_set(v_reuseFailAlloc_617_, 7, v_simpState_604_);
lean_ctor_set(v_reuseFailAlloc_617_, 8, v_fuel_605_);
lean_ctor_set(v_reuseFailAlloc_617_, 9, v_inlineHandledInvariants_606_);
v___x_612_ = v_reuseFailAlloc_617_;
goto v_reusejp_611_;
}
v_reusejp_611_:
{
lean_object* v___x_613_; lean_object* v___x_615_; 
v___x_613_ = lean_st_ref_set(v_a_563_, v___x_612_);
if (v_isShared_595_ == 0)
{
v___x_615_ = v___x_594_;
goto v_reusejp_614_;
}
else
{
lean_object* v_reuseFailAlloc_616_; 
v_reuseFailAlloc_616_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_616_, 0, v_a_592_);
v___x_615_ = v_reuseFailAlloc_616_;
goto v_reusejp_614_;
}
v_reusejp_614_:
{
return v___x_615_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_key_579_, 2);
return v___x_591_;
}
}
else
{
lean_dec_ref_known(v_key_579_, 2);
return v___x_589_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForSplitCached___redArg___boxed(lean_object* v_splitInfo_624_, lean_object* v_info_625_, lean_object* v_a_626_, lean_object* v_a_627_, lean_object* v_a_628_, lean_object* v_a_629_, lean_object* v_a_630_, lean_object* v_a_631_, lean_object* v_a_632_, lean_object* v_a_633_){
_start:
{
lean_object* v_res_634_; 
v_res_634_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForSplitCached___redArg(v_splitInfo_624_, v_info_625_, v_a_626_, v_a_627_, v_a_628_, v_a_629_, v_a_630_, v_a_631_, v_a_632_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForSplitCached(lean_object* v_splitInfo_635_, lean_object* v_info_636_, lean_object* v_a_637_, lean_object* v_a_638_, lean_object* v_a_639_, lean_object* v_a_640_, lean_object* v_a_641_, lean_object* v_a_642_, lean_object* v_a_643_, lean_object* v_a_644_, lean_object* v_a_645_, lean_object* v_a_646_, lean_object* v_a_647_){
_start:
{
lean_object* v___x_649_; 
v___x_649_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForSplitCached___redArg(v_splitInfo_635_, v_info_636_, v_a_638_, v_a_642_, v_a_643_, v_a_644_, v_a_645_, v_a_646_, v_a_647_);
return v___x_649_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForSplitCached___boxed(lean_object* v_splitInfo_650_, lean_object* v_info_651_, lean_object* v_a_652_, lean_object* v_a_653_, lean_object* v_a_654_, lean_object* v_a_655_, lean_object* v_a_656_, lean_object* v_a_657_, lean_object* v_a_658_, lean_object* v_a_659_, lean_object* v_a_660_, lean_object* v_a_661_, lean_object* v_a_662_, lean_object* v_a_663_){
_start:
{
lean_object* v_res_664_; 
v_res_664_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForSplitCached(v_splitInfo_650_, v_info_651_, v_a_652_, v_a_653_, v_a_654_, v_a_655_, v_a_656_, v_a_657_, v_a_658_, v_a_659_, v_a_660_, v_a_661_, v_a_662_);
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
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRuleCached_spec__1_spec__2___redArg(lean_object* v_a_665_, lean_object* v_x_666_){
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
lean_object* v_key_668_; lean_object* v_tail_669_; uint8_t v___y_671_; lean_object* v_fst_673_; lean_object* v_snd_674_; lean_object* v_fst_675_; lean_object* v_snd_676_; size_t v___x_677_; size_t v___x_678_; uint8_t v___x_679_; 
v_key_668_ = lean_ctor_get(v_x_666_, 0);
v_tail_669_ = lean_ctor_get(v_x_666_, 2);
v_fst_673_ = lean_ctor_get(v_key_668_, 0);
v_snd_674_ = lean_ctor_get(v_key_668_, 1);
v_fst_675_ = lean_ctor_get(v_a_665_, 0);
v_snd_676_ = lean_ctor_get(v_a_665_, 1);
v___x_677_ = lean_ptr_addr(v_fst_673_);
v___x_678_ = lean_ptr_addr(v_fst_675_);
v___x_679_ = lean_usize_dec_eq(v___x_677_, v___x_678_);
if (v___x_679_ == 0)
{
v___y_671_ = v___x_679_;
goto v___jp_670_;
}
else
{
uint8_t v___x_680_; 
v___x_680_ = lean_nat_dec_eq(v_snd_674_, v_snd_676_);
v___y_671_ = v___x_680_;
goto v___jp_670_;
}
v___jp_670_:
{
if (v___y_671_ == 0)
{
v_x_666_ = v_tail_669_;
goto _start;
}
else
{
return v___y_671_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRuleCached_spec__1_spec__2___redArg___boxed(lean_object* v_a_681_, lean_object* v_x_682_){
_start:
{
uint8_t v_res_683_; lean_object* v_r_684_; 
v_res_683_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRuleCached_spec__1_spec__2___redArg(v_a_681_, v_x_682_);
lean_dec(v_x_682_);
lean_dec_ref(v_a_681_);
v_r_684_ = lean_box(v_res_683_);
return v_r_684_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRuleCached_spec__1_spec__4___redArg(lean_object* v_a_685_, lean_object* v_b_686_, lean_object* v_x_687_){
_start:
{
if (lean_obj_tag(v_x_687_) == 0)
{
lean_dec(v_b_686_);
lean_dec_ref(v_a_685_);
return v_x_687_;
}
else
{
lean_object* v_key_688_; lean_object* v_value_689_; lean_object* v_tail_690_; lean_object* v___x_692_; uint8_t v_isShared_693_; uint8_t v_isSharedCheck_711_; 
v_key_688_ = lean_ctor_get(v_x_687_, 0);
v_value_689_ = lean_ctor_get(v_x_687_, 1);
v_tail_690_ = lean_ctor_get(v_x_687_, 2);
v_isSharedCheck_711_ = !lean_is_exclusive(v_x_687_);
if (v_isSharedCheck_711_ == 0)
{
v___x_692_ = v_x_687_;
v_isShared_693_ = v_isSharedCheck_711_;
goto v_resetjp_691_;
}
else
{
lean_inc(v_tail_690_);
lean_inc(v_value_689_);
lean_inc(v_key_688_);
lean_dec(v_x_687_);
v___x_692_ = lean_box(0);
v_isShared_693_ = v_isSharedCheck_711_;
goto v_resetjp_691_;
}
v_resetjp_691_:
{
uint8_t v___y_695_; lean_object* v_fst_703_; lean_object* v_snd_704_; lean_object* v_fst_705_; lean_object* v_snd_706_; size_t v___x_707_; size_t v___x_708_; uint8_t v___x_709_; 
v_fst_703_ = lean_ctor_get(v_key_688_, 0);
v_snd_704_ = lean_ctor_get(v_key_688_, 1);
v_fst_705_ = lean_ctor_get(v_a_685_, 0);
v_snd_706_ = lean_ctor_get(v_a_685_, 1);
v___x_707_ = lean_ptr_addr(v_fst_703_);
v___x_708_ = lean_ptr_addr(v_fst_705_);
v___x_709_ = lean_usize_dec_eq(v___x_707_, v___x_708_);
if (v___x_709_ == 0)
{
v___y_695_ = v___x_709_;
goto v___jp_694_;
}
else
{
uint8_t v___x_710_; 
v___x_710_ = lean_nat_dec_eq(v_snd_704_, v_snd_706_);
v___y_695_ = v___x_710_;
goto v___jp_694_;
}
v___jp_694_:
{
if (v___y_695_ == 0)
{
lean_object* v___x_696_; lean_object* v___x_698_; 
v___x_696_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRuleCached_spec__1_spec__4___redArg(v_a_685_, v_b_686_, v_tail_690_);
if (v_isShared_693_ == 0)
{
lean_ctor_set(v___x_692_, 2, v___x_696_);
v___x_698_ = v___x_692_;
goto v_reusejp_697_;
}
else
{
lean_object* v_reuseFailAlloc_699_; 
v_reuseFailAlloc_699_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_699_, 0, v_key_688_);
lean_ctor_set(v_reuseFailAlloc_699_, 1, v_value_689_);
lean_ctor_set(v_reuseFailAlloc_699_, 2, v___x_696_);
v___x_698_ = v_reuseFailAlloc_699_;
goto v_reusejp_697_;
}
v_reusejp_697_:
{
return v___x_698_;
}
}
else
{
lean_object* v___x_701_; 
lean_dec(v_value_689_);
lean_dec(v_key_688_);
if (v_isShared_693_ == 0)
{
lean_ctor_set(v___x_692_, 1, v_b_686_);
lean_ctor_set(v___x_692_, 0, v_a_685_);
v___x_701_ = v___x_692_;
goto v_reusejp_700_;
}
else
{
lean_object* v_reuseFailAlloc_702_; 
v_reuseFailAlloc_702_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_702_, 0, v_a_685_);
lean_ctor_set(v_reuseFailAlloc_702_, 1, v_b_686_);
lean_ctor_set(v_reuseFailAlloc_702_, 2, v_tail_690_);
v___x_701_ = v_reuseFailAlloc_702_;
goto v_reusejp_700_;
}
v_reusejp_700_:
{
return v___x_701_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRuleCached_spec__1_spec__3_spec__4_spec__5___redArg(lean_object* v_x_712_, lean_object* v_x_713_){
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
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRuleCached_spec__1_spec__3_spec__4___redArg(lean_object* v_i_747_, lean_object* v_source_748_, lean_object* v_target_749_){
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
v_target_755_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRuleCached_spec__1_spec__3_spec__4_spec__5___redArg(v_target_749_, v_es_752_);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRuleCached_spec__1_spec__3___redArg(lean_object* v_data_759_){
_start:
{
lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v_nbuckets_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; 
v___x_760_ = lean_array_get_size(v_data_759_);
v___x_761_ = lean_unsigned_to_nat(2u);
v_nbuckets_762_ = lean_nat_mul(v___x_760_, v___x_761_);
v___x_763_ = lean_unsigned_to_nat(0u);
v___x_764_ = lean_box(0);
v___x_765_ = lean_mk_array(v_nbuckets_762_, v___x_764_);
v___x_766_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRuleCached_spec__1_spec__3_spec__4___redArg(v___x_763_, v_data_759_, v___x_765_);
return v___x_766_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRuleCached_spec__1___redArg(lean_object* v_m_767_, lean_object* v_a_768_, lean_object* v_b_769_){
_start:
{
lean_object* v_size_770_; lean_object* v_buckets_771_; lean_object* v___x_773_; uint8_t v_isShared_774_; uint8_t v_isSharedCheck_821_; 
v_size_770_ = lean_ctor_get(v_m_767_, 0);
v_buckets_771_ = lean_ctor_get(v_m_767_, 1);
v_isSharedCheck_821_ = !lean_is_exclusive(v_m_767_);
if (v_isSharedCheck_821_ == 0)
{
v___x_773_ = v_m_767_;
v_isShared_774_ = v_isSharedCheck_821_;
goto v_resetjp_772_;
}
else
{
lean_inc(v_buckets_771_);
lean_inc(v_size_770_);
lean_dec(v_m_767_);
v___x_773_ = lean_box(0);
v_isShared_774_ = v_isSharedCheck_821_;
goto v_resetjp_772_;
}
v_resetjp_772_:
{
lean_object* v_fst_775_; lean_object* v_snd_776_; lean_object* v___x_777_; size_t v___x_778_; size_t v___x_779_; size_t v___x_780_; uint64_t v___x_781_; uint64_t v___x_782_; uint64_t v___x_783_; uint64_t v___x_784_; uint64_t v___x_785_; uint64_t v_fold_786_; uint64_t v___x_787_; uint64_t v___x_788_; uint64_t v___x_789_; size_t v___x_790_; size_t v___x_791_; size_t v___x_792_; size_t v___x_793_; size_t v___x_794_; lean_object* v_bkt_795_; uint8_t v___x_796_; 
v_fst_775_ = lean_ctor_get(v_a_768_, 0);
v_snd_776_ = lean_ctor_get(v_a_768_, 1);
v___x_777_ = lean_array_get_size(v_buckets_771_);
v___x_778_ = lean_ptr_addr(v_fst_775_);
v___x_779_ = ((size_t)3ULL);
v___x_780_ = lean_usize_shift_right(v___x_778_, v___x_779_);
v___x_781_ = lean_usize_to_uint64(v___x_780_);
v___x_782_ = lean_uint64_of_nat(v_snd_776_);
v___x_783_ = lean_uint64_mix_hash(v___x_781_, v___x_782_);
v___x_784_ = 32ULL;
v___x_785_ = lean_uint64_shift_right(v___x_783_, v___x_784_);
v_fold_786_ = lean_uint64_xor(v___x_783_, v___x_785_);
v___x_787_ = 16ULL;
v___x_788_ = lean_uint64_shift_right(v_fold_786_, v___x_787_);
v___x_789_ = lean_uint64_xor(v_fold_786_, v___x_788_);
v___x_790_ = lean_uint64_to_usize(v___x_789_);
v___x_791_ = lean_usize_of_nat(v___x_777_);
v___x_792_ = ((size_t)1ULL);
v___x_793_ = lean_usize_sub(v___x_791_, v___x_792_);
v___x_794_ = lean_usize_land(v___x_790_, v___x_793_);
v_bkt_795_ = lean_array_uget_borrowed(v_buckets_771_, v___x_794_);
v___x_796_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRuleCached_spec__1_spec__2___redArg(v_a_768_, v_bkt_795_);
if (v___x_796_ == 0)
{
lean_object* v___x_797_; lean_object* v_size_x27_798_; lean_object* v___x_799_; lean_object* v_buckets_x27_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; uint8_t v___x_806_; 
v___x_797_ = lean_unsigned_to_nat(1u);
v_size_x27_798_ = lean_nat_add(v_size_770_, v___x_797_);
lean_dec(v_size_770_);
lean_inc(v_bkt_795_);
v___x_799_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_799_, 0, v_a_768_);
lean_ctor_set(v___x_799_, 1, v_b_769_);
lean_ctor_set(v___x_799_, 2, v_bkt_795_);
v_buckets_x27_800_ = lean_array_uset(v_buckets_771_, v___x_794_, v___x_799_);
v___x_801_ = lean_unsigned_to_nat(4u);
v___x_802_ = lean_nat_mul(v_size_x27_798_, v___x_801_);
v___x_803_ = lean_unsigned_to_nat(3u);
v___x_804_ = lean_nat_div(v___x_802_, v___x_803_);
lean_dec(v___x_802_);
v___x_805_ = lean_array_get_size(v_buckets_x27_800_);
v___x_806_ = lean_nat_dec_le(v___x_804_, v___x_805_);
lean_dec(v___x_804_);
if (v___x_806_ == 0)
{
lean_object* v_val_807_; lean_object* v___x_809_; 
v_val_807_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRuleCached_spec__1_spec__3___redArg(v_buckets_x27_800_);
if (v_isShared_774_ == 0)
{
lean_ctor_set(v___x_773_, 1, v_val_807_);
lean_ctor_set(v___x_773_, 0, v_size_x27_798_);
v___x_809_ = v___x_773_;
goto v_reusejp_808_;
}
else
{
lean_object* v_reuseFailAlloc_810_; 
v_reuseFailAlloc_810_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_810_, 0, v_size_x27_798_);
lean_ctor_set(v_reuseFailAlloc_810_, 1, v_val_807_);
v___x_809_ = v_reuseFailAlloc_810_;
goto v_reusejp_808_;
}
v_reusejp_808_:
{
return v___x_809_;
}
}
else
{
lean_object* v___x_812_; 
if (v_isShared_774_ == 0)
{
lean_ctor_set(v___x_773_, 1, v_buckets_x27_800_);
lean_ctor_set(v___x_773_, 0, v_size_x27_798_);
v___x_812_ = v___x_773_;
goto v_reusejp_811_;
}
else
{
lean_object* v_reuseFailAlloc_813_; 
v_reuseFailAlloc_813_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_813_, 0, v_size_x27_798_);
lean_ctor_set(v_reuseFailAlloc_813_, 1, v_buckets_x27_800_);
v___x_812_ = v_reuseFailAlloc_813_;
goto v_reusejp_811_;
}
v_reusejp_811_:
{
return v___x_812_;
}
}
}
else
{
lean_object* v___x_814_; lean_object* v_buckets_x27_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_819_; 
lean_inc(v_bkt_795_);
v___x_814_ = lean_box(0);
v_buckets_x27_815_ = lean_array_uset(v_buckets_771_, v___x_794_, v___x_814_);
v___x_816_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRuleCached_spec__1_spec__4___redArg(v_a_768_, v_b_769_, v_bkt_795_);
v___x_817_ = lean_array_uset(v_buckets_x27_815_, v___x_794_, v___x_816_);
if (v_isShared_774_ == 0)
{
lean_ctor_set(v___x_773_, 1, v___x_817_);
v___x_819_ = v___x_773_;
goto v_reusejp_818_;
}
else
{
lean_object* v_reuseFailAlloc_820_; 
v_reuseFailAlloc_820_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_820_, 0, v_size_770_);
lean_ctor_set(v_reuseFailAlloc_820_, 1, v___x_817_);
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
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRuleCached_spec__0_spec__0___redArg(lean_object* v_a_822_, lean_object* v_x_823_){
_start:
{
if (lean_obj_tag(v_x_823_) == 0)
{
lean_object* v___x_824_; 
v___x_824_ = lean_box(0);
return v___x_824_;
}
else
{
lean_object* v_key_825_; lean_object* v_value_826_; lean_object* v_tail_827_; uint8_t v___y_829_; lean_object* v_fst_832_; lean_object* v_snd_833_; lean_object* v_fst_834_; lean_object* v_snd_835_; size_t v___x_836_; size_t v___x_837_; uint8_t v___x_838_; 
v_key_825_ = lean_ctor_get(v_x_823_, 0);
v_value_826_ = lean_ctor_get(v_x_823_, 1);
v_tail_827_ = lean_ctor_get(v_x_823_, 2);
v_fst_832_ = lean_ctor_get(v_key_825_, 0);
v_snd_833_ = lean_ctor_get(v_key_825_, 1);
v_fst_834_ = lean_ctor_get(v_a_822_, 0);
v_snd_835_ = lean_ctor_get(v_a_822_, 1);
v___x_836_ = lean_ptr_addr(v_fst_832_);
v___x_837_ = lean_ptr_addr(v_fst_834_);
v___x_838_ = lean_usize_dec_eq(v___x_836_, v___x_837_);
if (v___x_838_ == 0)
{
v___y_829_ = v___x_838_;
goto v___jp_828_;
}
else
{
uint8_t v___x_839_; 
v___x_839_ = lean_nat_dec_eq(v_snd_833_, v_snd_835_);
v___y_829_ = v___x_839_;
goto v___jp_828_;
}
v___jp_828_:
{
if (v___y_829_ == 0)
{
v_x_823_ = v_tail_827_;
goto _start;
}
else
{
lean_object* v___x_831_; 
lean_inc(v_value_826_);
v___x_831_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_831_, 0, v_value_826_);
return v___x_831_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRuleCached_spec__0_spec__0___redArg___boxed(lean_object* v_a_840_, lean_object* v_x_841_){
_start:
{
lean_object* v_res_842_; 
v_res_842_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRuleCached_spec__0_spec__0___redArg(v_a_840_, v_x_841_);
lean_dec(v_x_841_);
lean_dec_ref(v_a_840_);
return v_res_842_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRuleCached_spec__0___redArg(lean_object* v_m_843_, lean_object* v_a_844_){
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
v___x_867_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRuleCached_spec__0_spec__0___redArg(v_a_844_, v___x_866_);
return v___x_867_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRuleCached_spec__0___redArg___boxed(lean_object* v_m_868_, lean_object* v_a_869_){
_start:
{
lean_object* v_res_870_; 
v_res_870_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRuleCached_spec__0___redArg(v_m_868_, v_a_869_);
lean_dec_ref(v_a_869_);
lean_dec_ref(v_m_868_);
return v_res_870_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRuleCached___redArg(lean_object* v_rhs_871_, lean_object* v_op_872_, lean_object* v_a_873_, lean_object* v_a_874_, lean_object* v_a_875_, lean_object* v_a_876_, lean_object* v_a_877_, lean_object* v_a_878_, lean_object* v_a_879_){
_start:
{
lean_object* v___x_881_; lean_object* v_numConst_882_; lean_object* v_latticeBackwardRuleCache_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v_key_886_; lean_object* v___x_887_; 
v___x_881_ = lean_st_ref_get(v_a_873_);
v_numConst_882_ = lean_ctor_get(v_op_872_, 1);
v_latticeBackwardRuleCache_883_ = lean_ctor_get(v___x_881_, 2);
lean_inc_ref(v_latticeBackwardRuleCache_883_);
lean_dec(v___x_881_);
v___x_884_ = l_Lean_Expr_getAppPrefix(v_rhs_871_, v_numConst_882_);
v___x_885_ = l_Lean_Expr_getAppNumArgs(v_rhs_871_);
v_key_886_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_key_886_, 0, v___x_884_);
lean_ctor_set(v_key_886_, 1, v___x_885_);
v___x_887_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRuleCached_spec__0___redArg(v_latticeBackwardRuleCache_883_, v_key_886_);
lean_dec_ref(v_latticeBackwardRuleCache_883_);
if (lean_obj_tag(v___x_887_) == 1)
{
lean_object* v_val_888_; lean_object* v___x_890_; uint8_t v_isShared_891_; uint8_t v_isSharedCheck_895_; 
lean_dec_ref_known(v_key_886_, 2);
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
v___x_896_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRule(v_rhs_871_, v_op_872_, v_a_874_, v_a_875_, v_a_876_, v_a_877_, v_a_878_, v_a_879_);
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
v___x_917_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRuleCached_spec__1___redArg(v_latticeBackwardRuleCache_906_, v_key_886_, v_a_899_);
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
v___x_920_ = lean_st_ref_set(v_a_873_, v___x_919_);
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
lean_dec_ref_known(v_key_886_, 2);
return v___x_898_;
}
}
else
{
lean_dec_ref_known(v_key_886_, 2);
return v___x_896_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRuleCached___redArg___boxed(lean_object* v_rhs_927_, lean_object* v_op_928_, lean_object* v_a_929_, lean_object* v_a_930_, lean_object* v_a_931_, lean_object* v_a_932_, lean_object* v_a_933_, lean_object* v_a_934_, lean_object* v_a_935_, lean_object* v_a_936_){
_start:
{
lean_object* v_res_937_; 
v_res_937_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRuleCached___redArg(v_rhs_927_, v_op_928_, v_a_929_, v_a_930_, v_a_931_, v_a_932_, v_a_933_, v_a_934_, v_a_935_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRuleCached(lean_object* v_rhs_938_, lean_object* v_op_939_, lean_object* v_a_940_, lean_object* v_a_941_, lean_object* v_a_942_, lean_object* v_a_943_, lean_object* v_a_944_, lean_object* v_a_945_, lean_object* v_a_946_, lean_object* v_a_947_, lean_object* v_a_948_, lean_object* v_a_949_, lean_object* v_a_950_){
_start:
{
lean_object* v___x_952_; 
v___x_952_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRuleCached___redArg(v_rhs_938_, v_op_939_, v_a_941_, v_a_945_, v_a_946_, v_a_947_, v_a_948_, v_a_949_, v_a_950_);
return v___x_952_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRuleCached___boxed(lean_object* v_rhs_953_, lean_object* v_op_954_, lean_object* v_a_955_, lean_object* v_a_956_, lean_object* v_a_957_, lean_object* v_a_958_, lean_object* v_a_959_, lean_object* v_a_960_, lean_object* v_a_961_, lean_object* v_a_962_, lean_object* v_a_963_, lean_object* v_a_964_, lean_object* v_a_965_, lean_object* v_a_966_){
_start:
{
lean_object* v_res_967_; 
v_res_967_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRuleCached(v_rhs_953_, v_op_954_, v_a_955_, v_a_956_, v_a_957_, v_a_958_, v_a_959_, v_a_960_, v_a_961_, v_a_962_, v_a_963_, v_a_964_, v_a_965_);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRuleCached_spec__0(lean_object* v_00_u03b2_968_, lean_object* v_m_969_, lean_object* v_a_970_){
_start:
{
lean_object* v___x_971_; 
v___x_971_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRuleCached_spec__0___redArg(v_m_969_, v_a_970_);
return v___x_971_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRuleCached_spec__0___boxed(lean_object* v_00_u03b2_972_, lean_object* v_m_973_, lean_object* v_a_974_){
_start:
{
lean_object* v_res_975_; 
v_res_975_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRuleCached_spec__0(v_00_u03b2_972_, v_m_973_, v_a_974_);
lean_dec_ref(v_a_974_);
lean_dec_ref(v_m_973_);
return v_res_975_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRuleCached_spec__1(lean_object* v_00_u03b2_976_, lean_object* v_m_977_, lean_object* v_a_978_, lean_object* v_b_979_){
_start:
{
lean_object* v___x_980_; 
v___x_980_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRuleCached_spec__1___redArg(v_m_977_, v_a_978_, v_b_979_);
return v___x_980_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRuleCached_spec__0_spec__0(lean_object* v_00_u03b2_981_, lean_object* v_a_982_, lean_object* v_x_983_){
_start:
{
lean_object* v___x_984_; 
v___x_984_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRuleCached_spec__0_spec__0___redArg(v_a_982_, v_x_983_);
return v___x_984_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRuleCached_spec__0_spec__0___boxed(lean_object* v_00_u03b2_985_, lean_object* v_a_986_, lean_object* v_x_987_){
_start:
{
lean_object* v_res_988_; 
v_res_988_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRuleCached_spec__0_spec__0(v_00_u03b2_985_, v_a_986_, v_x_987_);
lean_dec(v_x_987_);
lean_dec_ref(v_a_986_);
return v_res_988_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRuleCached_spec__1_spec__2(lean_object* v_00_u03b2_989_, lean_object* v_a_990_, lean_object* v_x_991_){
_start:
{
uint8_t v___x_992_; 
v___x_992_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRuleCached_spec__1_spec__2___redArg(v_a_990_, v_x_991_);
return v___x_992_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRuleCached_spec__1_spec__2___boxed(lean_object* v_00_u03b2_993_, lean_object* v_a_994_, lean_object* v_x_995_){
_start:
{
uint8_t v_res_996_; lean_object* v_r_997_; 
v_res_996_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRuleCached_spec__1_spec__2(v_00_u03b2_993_, v_a_994_, v_x_995_);
lean_dec(v_x_995_);
lean_dec_ref(v_a_994_);
v_r_997_ = lean_box(v_res_996_);
return v_r_997_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRuleCached_spec__1_spec__3(lean_object* v_00_u03b2_998_, lean_object* v_data_999_){
_start:
{
lean_object* v___x_1000_; 
v___x_1000_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRuleCached_spec__1_spec__3___redArg(v_data_999_);
return v___x_1000_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRuleCached_spec__1_spec__4(lean_object* v_00_u03b2_1001_, lean_object* v_a_1002_, lean_object* v_b_1003_, lean_object* v_x_1004_){
_start:
{
lean_object* v___x_1005_; 
v___x_1005_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRuleCached_spec__1_spec__4___redArg(v_a_1002_, v_b_1003_, v_x_1004_);
return v___x_1005_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRuleCached_spec__1_spec__3_spec__4(lean_object* v_00_u03b2_1006_, lean_object* v_i_1007_, lean_object* v_source_1008_, lean_object* v_target_1009_){
_start:
{
lean_object* v___x_1010_; 
v___x_1010_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRuleCached_spec__1_spec__3_spec__4___redArg(v_i_1007_, v_source_1008_, v_target_1009_);
return v___x_1010_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRuleCached_spec__1_spec__3_spec__4_spec__5(lean_object* v_00_u03b2_1011_, lean_object* v_x_1012_, lean_object* v_x_1013_){
_start:
{
lean_object* v___x_1014_; 
v___x_1014_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRuleCached_spec__1_spec__3_spec__4_spec__5___redArg(v_x_1012_, v_x_1013_);
return v___x_1014_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkFrameBackwardRuleCached___redArg(lean_object* v_op_1015_, lean_object* v_info_1016_, lean_object* v_a_1017_, lean_object* v_a_1018_, lean_object* v_a_1019_, lean_object* v_a_1020_, lean_object* v_a_1021_, lean_object* v_a_1022_, lean_object* v_a_1023_){
_start:
{
lean_object* v___x_1025_; lean_object* v_excessArgs_1026_; lean_object* v_frameBackwardRuleCache_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v_key_1030_; lean_object* v___x_1031_; 
v___x_1025_ = lean_st_ref_get(v_a_1017_);
v_excessArgs_1026_ = lean_ctor_get(v_info_1016_, 2);
v_frameBackwardRuleCache_1027_ = lean_ctor_get(v___x_1025_, 3);
lean_inc_ref(v_frameBackwardRuleCache_1027_);
lean_dec(v___x_1025_);
v___x_1028_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_WPApp_instWP(v_info_1016_);
v___x_1029_ = lean_array_get_size(v_excessArgs_1026_);
v_key_1030_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_key_1030_, 0, v___x_1028_);
lean_ctor_set(v_key_1030_, 1, v___x_1029_);
v___x_1031_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRuleCached_spec__0___redArg(v_frameBackwardRuleCache_1027_, v_key_1030_);
lean_dec_ref(v_frameBackwardRuleCache_1027_);
if (lean_obj_tag(v___x_1031_) == 1)
{
lean_object* v_val_1032_; lean_object* v___x_1034_; uint8_t v_isShared_1035_; uint8_t v_isSharedCheck_1039_; 
lean_dec_ref_known(v_key_1030_, 2);
lean_dec_ref(v_op_1015_);
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
v___x_1040_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_mkFrameBackwardRule(v_op_1015_, v_info_1016_, v_a_1020_, v_a_1021_, v_a_1022_, v_a_1023_);
if (lean_obj_tag(v___x_1040_) == 0)
{
lean_object* v_a_1041_; lean_object* v___x_1042_; 
v_a_1041_ = lean_ctor_get(v___x_1040_, 0);
lean_inc(v_a_1041_);
lean_dec_ref_known(v___x_1040_, 1);
v___x_1042_ = l_Lean_Meta_Sym_BackwardRule_shareCommon(v_a_1041_, v_a_1018_, v_a_1019_, v_a_1020_, v_a_1021_, v_a_1022_, v_a_1023_);
if (lean_obj_tag(v___x_1042_) == 0)
{
lean_object* v_a_1043_; lean_object* v___x_1045_; uint8_t v_isShared_1046_; uint8_t v_isSharedCheck_1070_; 
v_a_1043_ = lean_ctor_get(v___x_1042_, 0);
v_isSharedCheck_1070_ = !lean_is_exclusive(v___x_1042_);
if (v_isSharedCheck_1070_ == 0)
{
v___x_1045_ = v___x_1042_;
v_isShared_1046_ = v_isSharedCheck_1070_;
goto v_resetjp_1044_;
}
else
{
lean_inc(v_a_1043_);
lean_dec(v___x_1042_);
v___x_1045_ = lean_box(0);
v_isShared_1046_ = v_isSharedCheck_1070_;
goto v_resetjp_1044_;
}
v_resetjp_1044_:
{
lean_object* v___x_1047_; lean_object* v_specBackwardRuleCache_1048_; lean_object* v_splitBackwardRuleCache_1049_; lean_object* v_latticeBackwardRuleCache_1050_; lean_object* v_frameBackwardRuleCache_1051_; lean_object* v_frameDB_1052_; lean_object* v_invariants_1053_; lean_object* v_vcs_1054_; lean_object* v_simpState_1055_; lean_object* v_fuel_1056_; lean_object* v_inlineHandledInvariants_1057_; lean_object* v___x_1059_; uint8_t v_isShared_1060_; uint8_t v_isSharedCheck_1069_; 
v___x_1047_ = lean_st_ref_take(v_a_1017_);
v_specBackwardRuleCache_1048_ = lean_ctor_get(v___x_1047_, 0);
v_splitBackwardRuleCache_1049_ = lean_ctor_get(v___x_1047_, 1);
v_latticeBackwardRuleCache_1050_ = lean_ctor_get(v___x_1047_, 2);
v_frameBackwardRuleCache_1051_ = lean_ctor_get(v___x_1047_, 3);
v_frameDB_1052_ = lean_ctor_get(v___x_1047_, 4);
v_invariants_1053_ = lean_ctor_get(v___x_1047_, 5);
v_vcs_1054_ = lean_ctor_get(v___x_1047_, 6);
v_simpState_1055_ = lean_ctor_get(v___x_1047_, 7);
v_fuel_1056_ = lean_ctor_get(v___x_1047_, 8);
v_inlineHandledInvariants_1057_ = lean_ctor_get(v___x_1047_, 9);
v_isSharedCheck_1069_ = !lean_is_exclusive(v___x_1047_);
if (v_isSharedCheck_1069_ == 0)
{
v___x_1059_ = v___x_1047_;
v_isShared_1060_ = v_isSharedCheck_1069_;
goto v_resetjp_1058_;
}
else
{
lean_inc(v_inlineHandledInvariants_1057_);
lean_inc(v_fuel_1056_);
lean_inc(v_simpState_1055_);
lean_inc(v_vcs_1054_);
lean_inc(v_invariants_1053_);
lean_inc(v_frameDB_1052_);
lean_inc(v_frameBackwardRuleCache_1051_);
lean_inc(v_latticeBackwardRuleCache_1050_);
lean_inc(v_splitBackwardRuleCache_1049_);
lean_inc(v_specBackwardRuleCache_1048_);
lean_dec(v___x_1047_);
v___x_1059_ = lean_box(0);
v_isShared_1060_ = v_isSharedCheck_1069_;
goto v_resetjp_1058_;
}
v_resetjp_1058_:
{
lean_object* v___x_1061_; lean_object* v___x_1063_; 
lean_inc(v_a_1043_);
v___x_1061_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkLatticeOpRuleCached_spec__1___redArg(v_frameBackwardRuleCache_1051_, v_key_1030_, v_a_1043_);
if (v_isShared_1060_ == 0)
{
lean_ctor_set(v___x_1059_, 3, v___x_1061_);
v___x_1063_ = v___x_1059_;
goto v_reusejp_1062_;
}
else
{
lean_object* v_reuseFailAlloc_1068_; 
v_reuseFailAlloc_1068_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1068_, 0, v_specBackwardRuleCache_1048_);
lean_ctor_set(v_reuseFailAlloc_1068_, 1, v_splitBackwardRuleCache_1049_);
lean_ctor_set(v_reuseFailAlloc_1068_, 2, v_latticeBackwardRuleCache_1050_);
lean_ctor_set(v_reuseFailAlloc_1068_, 3, v___x_1061_);
lean_ctor_set(v_reuseFailAlloc_1068_, 4, v_frameDB_1052_);
lean_ctor_set(v_reuseFailAlloc_1068_, 5, v_invariants_1053_);
lean_ctor_set(v_reuseFailAlloc_1068_, 6, v_vcs_1054_);
lean_ctor_set(v_reuseFailAlloc_1068_, 7, v_simpState_1055_);
lean_ctor_set(v_reuseFailAlloc_1068_, 8, v_fuel_1056_);
lean_ctor_set(v_reuseFailAlloc_1068_, 9, v_inlineHandledInvariants_1057_);
v___x_1063_ = v_reuseFailAlloc_1068_;
goto v_reusejp_1062_;
}
v_reusejp_1062_:
{
lean_object* v___x_1064_; lean_object* v___x_1066_; 
v___x_1064_ = lean_st_ref_set(v_a_1017_, v___x_1063_);
if (v_isShared_1046_ == 0)
{
v___x_1066_ = v___x_1045_;
goto v_reusejp_1065_;
}
else
{
lean_object* v_reuseFailAlloc_1067_; 
v_reuseFailAlloc_1067_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1067_, 0, v_a_1043_);
v___x_1066_ = v_reuseFailAlloc_1067_;
goto v_reusejp_1065_;
}
v_reusejp_1065_:
{
return v___x_1066_;
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
else
{
lean_dec_ref_known(v_key_1030_, 2);
return v___x_1040_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkFrameBackwardRuleCached___redArg___boxed(lean_object* v_op_1071_, lean_object* v_info_1072_, lean_object* v_a_1073_, lean_object* v_a_1074_, lean_object* v_a_1075_, lean_object* v_a_1076_, lean_object* v_a_1077_, lean_object* v_a_1078_, lean_object* v_a_1079_, lean_object* v_a_1080_){
_start:
{
lean_object* v_res_1081_; 
v_res_1081_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_mkFrameBackwardRuleCached___redArg(v_op_1071_, v_info_1072_, v_a_1073_, v_a_1074_, v_a_1075_, v_a_1076_, v_a_1077_, v_a_1078_, v_a_1079_);
lean_dec(v_a_1079_);
lean_dec_ref(v_a_1078_);
lean_dec(v_a_1077_);
lean_dec_ref(v_a_1076_);
lean_dec(v_a_1075_);
lean_dec_ref(v_a_1074_);
lean_dec(v_a_1073_);
lean_dec_ref(v_info_1072_);
return v_res_1081_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkFrameBackwardRuleCached(lean_object* v_op_1082_, lean_object* v_info_1083_, lean_object* v_a_1084_, lean_object* v_a_1085_, lean_object* v_a_1086_, lean_object* v_a_1087_, lean_object* v_a_1088_, lean_object* v_a_1089_, lean_object* v_a_1090_, lean_object* v_a_1091_, lean_object* v_a_1092_, lean_object* v_a_1093_, lean_object* v_a_1094_){
_start:
{
lean_object* v___x_1096_; 
v___x_1096_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_mkFrameBackwardRuleCached___redArg(v_op_1082_, v_info_1083_, v_a_1085_, v_a_1089_, v_a_1090_, v_a_1091_, v_a_1092_, v_a_1093_, v_a_1094_);
return v___x_1096_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkFrameBackwardRuleCached___boxed(lean_object* v_op_1097_, lean_object* v_info_1098_, lean_object* v_a_1099_, lean_object* v_a_1100_, lean_object* v_a_1101_, lean_object* v_a_1102_, lean_object* v_a_1103_, lean_object* v_a_1104_, lean_object* v_a_1105_, lean_object* v_a_1106_, lean_object* v_a_1107_, lean_object* v_a_1108_, lean_object* v_a_1109_, lean_object* v_a_1110_){
_start:
{
lean_object* v_res_1111_; 
v_res_1111_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_mkFrameBackwardRuleCached(v_op_1097_, v_info_1098_, v_a_1099_, v_a_1100_, v_a_1101_, v_a_1102_, v_a_1103_, v_a_1104_, v_a_1105_, v_a_1106_, v_a_1107_, v_a_1108_, v_a_1109_);
lean_dec(v_a_1109_);
lean_dec_ref(v_a_1108_);
lean_dec(v_a_1107_);
lean_dec_ref(v_a_1106_);
lean_dec(v_a_1105_);
lean_dec_ref(v_a_1104_);
lean_dec(v_a_1103_);
lean_dec_ref(v_a_1102_);
lean_dec(v_a_1101_);
lean_dec(v_a_1100_);
lean_dec_ref(v_a_1099_);
lean_dec_ref(v_info_1098_);
return v_res_1111_;
}
}
lean_object* runtime_initialize_Lean_Elab_Tactic_Do_VCGen_Split(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Context(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_RuleConstruction(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeOp(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Util(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_InferType(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_RuleCache(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
