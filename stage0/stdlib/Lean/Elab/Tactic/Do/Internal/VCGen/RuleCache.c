// Lean compiler output
// Module: Lean.Elab.Tactic.Do.Internal.VCGen.RuleCache
// Imports: public import Lean.Elab.Tactic.Do.VCGen.Split public import Lean.Elab.Tactic.Do.Internal.VCGen.Context public import Lean.Elab.Tactic.Do.Internal.VCGen.RuleConstruction public import Lean.Elab.Tactic.Do.Internal.VCGen.Util import Lean.Meta.Sym.InferType
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
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Meta_Sym_inferType___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_get_size(lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
uint64_t l_Lean_Expr_hash(lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeSplit_mkBackwardRuleForLattice(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecProof_key(lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_WPInfo_instWP(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_tryMkBackwardRuleFromSpec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForSplit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForSplitCached___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForSplitCached___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForSplitCached(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForSplitCached___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__1_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__1_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint64_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__1_spec__2(lean_object*, size_t, size_t, uint64_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2_spec__5_spec__7_spec__8___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2_spec__5_spec__7___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2_spec__5___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__1_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__0___redArg(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__0(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__1_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__1_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__1_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2_spec__5_spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2_spec__5_spec__7_spec__8(lean_object*, lean_object*, lean_object*);
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
lean_object* v_fst_166_; lean_object* v_snd_167_; lean_object* v_fst_168_; lean_object* v_snd_169_; uint8_t v___x_170_; 
v_fst_166_ = lean_ctor_get(v_snd_162_, 0);
v_snd_167_ = lean_ctor_get(v_snd_162_, 1);
v_fst_168_ = lean_ctor_get(v_snd_164_, 0);
v_snd_169_ = lean_ctor_get(v_snd_164_, 1);
v___x_170_ = lean_expr_eqv(v_fst_166_, v_fst_168_);
if (v___x_170_ == 0)
{
v___y_158_ = v___x_170_;
goto v___jp_157_;
}
else
{
uint8_t v___x_171_; 
v___x_171_ = lean_nat_dec_eq(v_snd_167_, v_snd_169_);
v___y_158_ = v___x_171_;
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0_spec__0___redArg___boxed(lean_object* v_a_172_, lean_object* v_x_173_){
_start:
{
lean_object* v_res_174_; 
v_res_174_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0_spec__0___redArg(v_a_172_, v_x_173_);
lean_dec(v_x_173_);
lean_dec_ref(v_a_172_);
return v_res_174_;
}
}
static uint64_t _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_175_; uint64_t v___x_176_; 
v___x_175_ = lean_unsigned_to_nat(1723u);
v___x_176_ = lean_uint64_of_nat(v___x_175_);
return v___x_176_;
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
uint64_t v___x_204_; 
v___x_204_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg___closed__0);
v___y_184_ = v___x_204_;
goto v___jp_183_;
}
else
{
uint64_t v_hash_205_; 
v_hash_205_ = lean_ctor_get_uint64(v_fst_180_, sizeof(void*)*2);
v___y_184_ = v_hash_205_;
goto v___jp_183_;
}
v___jp_183_:
{
lean_object* v_fst_185_; lean_object* v_snd_186_; uint64_t v___x_187_; uint64_t v___x_188_; uint64_t v___x_189_; uint64_t v___x_190_; uint64_t v___x_191_; uint64_t v___x_192_; uint64_t v_fold_193_; uint64_t v___x_194_; uint64_t v___x_195_; uint64_t v___x_196_; size_t v___x_197_; size_t v___x_198_; size_t v___x_199_; size_t v___x_200_; size_t v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; 
v_fst_185_ = lean_ctor_get(v_snd_181_, 0);
v_snd_186_ = lean_ctor_get(v_snd_181_, 1);
v___x_187_ = l_Lean_Expr_hash(v_fst_185_);
v___x_188_ = lean_uint64_of_nat(v_snd_186_);
v___x_189_ = lean_uint64_mix_hash(v___x_187_, v___x_188_);
v___x_190_ = lean_uint64_mix_hash(v___y_184_, v___x_189_);
v___x_191_ = 32ULL;
v___x_192_ = lean_uint64_shift_right(v___x_190_, v___x_191_);
v_fold_193_ = lean_uint64_xor(v___x_190_, v___x_192_);
v___x_194_ = 16ULL;
v___x_195_ = lean_uint64_shift_right(v_fold_193_, v___x_194_);
v___x_196_ = lean_uint64_xor(v_fold_193_, v___x_195_);
v___x_197_ = lean_uint64_to_usize(v___x_196_);
v___x_198_ = lean_usize_of_nat(v___x_182_);
v___x_199_ = ((size_t)1ULL);
v___x_200_ = lean_usize_sub(v___x_198_, v___x_199_);
v___x_201_ = lean_usize_land(v___x_197_, v___x_200_);
v___x_202_ = lean_array_uget_borrowed(v_buckets_179_, v___x_201_);
v___x_203_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0_spec__0___redArg(v_a_178_, v___x_202_);
return v___x_203_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg___boxed(lean_object* v_m_206_, lean_object* v_a_207_){
_start:
{
lean_object* v_res_208_; 
v_res_208_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg(v_m_206_, v_a_207_);
lean_dec_ref(v_a_207_);
lean_dec_ref(v_m_206_);
return v_res_208_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__4_spec__5_spec__6___redArg(lean_object* v_x_209_, lean_object* v_x_210_){
_start:
{
if (lean_obj_tag(v_x_210_) == 0)
{
return v_x_209_;
}
else
{
lean_object* v_key_211_; lean_object* v_value_212_; lean_object* v_tail_213_; lean_object* v___x_215_; uint8_t v_isShared_216_; uint8_t v_isSharedCheck_247_; 
v_key_211_ = lean_ctor_get(v_x_210_, 0);
v_value_212_ = lean_ctor_get(v_x_210_, 1);
v_tail_213_ = lean_ctor_get(v_x_210_, 2);
v_isSharedCheck_247_ = !lean_is_exclusive(v_x_210_);
if (v_isSharedCheck_247_ == 0)
{
v___x_215_ = v_x_210_;
v_isShared_216_ = v_isSharedCheck_247_;
goto v_resetjp_214_;
}
else
{
lean_inc(v_tail_213_);
lean_inc(v_value_212_);
lean_inc(v_key_211_);
lean_dec(v_x_210_);
v___x_215_ = lean_box(0);
v_isShared_216_ = v_isSharedCheck_247_;
goto v_resetjp_214_;
}
v_resetjp_214_:
{
lean_object* v_fst_217_; lean_object* v_snd_218_; lean_object* v___x_219_; uint64_t v___y_221_; 
v_fst_217_ = lean_ctor_get(v_key_211_, 0);
v_snd_218_ = lean_ctor_get(v_key_211_, 1);
v___x_219_ = lean_array_get_size(v_x_209_);
if (lean_obj_tag(v_fst_217_) == 0)
{
uint64_t v___x_245_; 
v___x_245_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg___closed__0);
v___y_221_ = v___x_245_;
goto v___jp_220_;
}
else
{
uint64_t v_hash_246_; 
v_hash_246_ = lean_ctor_get_uint64(v_fst_217_, sizeof(void*)*2);
v___y_221_ = v_hash_246_;
goto v___jp_220_;
}
v___jp_220_:
{
lean_object* v_fst_222_; lean_object* v_snd_223_; uint64_t v___x_224_; uint64_t v___x_225_; uint64_t v___x_226_; uint64_t v___x_227_; uint64_t v___x_228_; uint64_t v___x_229_; uint64_t v_fold_230_; uint64_t v___x_231_; uint64_t v___x_232_; uint64_t v___x_233_; size_t v___x_234_; size_t v___x_235_; size_t v___x_236_; size_t v___x_237_; size_t v___x_238_; lean_object* v___x_239_; lean_object* v___x_241_; 
v_fst_222_ = lean_ctor_get(v_snd_218_, 0);
v_snd_223_ = lean_ctor_get(v_snd_218_, 1);
v___x_224_ = l_Lean_Expr_hash(v_fst_222_);
v___x_225_ = lean_uint64_of_nat(v_snd_223_);
v___x_226_ = lean_uint64_mix_hash(v___x_224_, v___x_225_);
v___x_227_ = lean_uint64_mix_hash(v___y_221_, v___x_226_);
v___x_228_ = 32ULL;
v___x_229_ = lean_uint64_shift_right(v___x_227_, v___x_228_);
v_fold_230_ = lean_uint64_xor(v___x_227_, v___x_229_);
v___x_231_ = 16ULL;
v___x_232_ = lean_uint64_shift_right(v_fold_230_, v___x_231_);
v___x_233_ = lean_uint64_xor(v_fold_230_, v___x_232_);
v___x_234_ = lean_uint64_to_usize(v___x_233_);
v___x_235_ = lean_usize_of_nat(v___x_219_);
v___x_236_ = ((size_t)1ULL);
v___x_237_ = lean_usize_sub(v___x_235_, v___x_236_);
v___x_238_ = lean_usize_land(v___x_234_, v___x_237_);
v___x_239_ = lean_array_uget_borrowed(v_x_209_, v___x_238_);
lean_inc(v___x_239_);
if (v_isShared_216_ == 0)
{
lean_ctor_set(v___x_215_, 2, v___x_239_);
v___x_241_ = v___x_215_;
goto v_reusejp_240_;
}
else
{
lean_object* v_reuseFailAlloc_244_; 
v_reuseFailAlloc_244_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_244_, 0, v_key_211_);
lean_ctor_set(v_reuseFailAlloc_244_, 1, v_value_212_);
lean_ctor_set(v_reuseFailAlloc_244_, 2, v___x_239_);
v___x_241_ = v_reuseFailAlloc_244_;
goto v_reusejp_240_;
}
v_reusejp_240_:
{
lean_object* v___x_242_; 
v___x_242_ = lean_array_uset(v_x_209_, v___x_238_, v___x_241_);
v_x_209_ = v___x_242_;
v_x_210_ = v_tail_213_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__4_spec__5___redArg(lean_object* v_i_248_, lean_object* v_source_249_, lean_object* v_target_250_){
_start:
{
lean_object* v___x_251_; uint8_t v___x_252_; 
v___x_251_ = lean_array_get_size(v_source_249_);
v___x_252_ = lean_nat_dec_lt(v_i_248_, v___x_251_);
if (v___x_252_ == 0)
{
lean_dec_ref(v_source_249_);
lean_dec(v_i_248_);
return v_target_250_;
}
else
{
lean_object* v_es_253_; lean_object* v___x_254_; lean_object* v_source_255_; lean_object* v_target_256_; lean_object* v___x_257_; lean_object* v___x_258_; 
v_es_253_ = lean_array_fget(v_source_249_, v_i_248_);
v___x_254_ = lean_box(0);
v_source_255_ = lean_array_fset(v_source_249_, v_i_248_, v___x_254_);
v_target_256_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__4_spec__5_spec__6___redArg(v_target_250_, v_es_253_);
v___x_257_ = lean_unsigned_to_nat(1u);
v___x_258_ = lean_nat_add(v_i_248_, v___x_257_);
lean_dec(v_i_248_);
v_i_248_ = v___x_258_;
v_source_249_ = v_source_255_;
v_target_250_ = v_target_256_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__4___redArg(lean_object* v_data_260_){
_start:
{
lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v_nbuckets_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; 
v___x_261_ = lean_array_get_size(v_data_260_);
v___x_262_ = lean_unsigned_to_nat(2u);
v_nbuckets_263_ = lean_nat_mul(v___x_261_, v___x_262_);
v___x_264_ = lean_unsigned_to_nat(0u);
v___x_265_ = lean_box(0);
v___x_266_ = lean_mk_array(v_nbuckets_263_, v___x_265_);
v___x_267_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__4_spec__5___redArg(v___x_264_, v_data_260_, v___x_266_);
return v___x_267_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__3___redArg(lean_object* v_a_268_, lean_object* v_x_269_){
_start:
{
if (lean_obj_tag(v_x_269_) == 0)
{
uint8_t v___x_270_; 
v___x_270_ = 0;
return v___x_270_;
}
else
{
lean_object* v_key_271_; lean_object* v_tail_272_; uint8_t v___y_274_; lean_object* v_fst_276_; lean_object* v_snd_277_; lean_object* v_fst_278_; lean_object* v_snd_279_; uint8_t v___x_280_; 
v_key_271_ = lean_ctor_get(v_x_269_, 0);
v_tail_272_ = lean_ctor_get(v_x_269_, 2);
v_fst_276_ = lean_ctor_get(v_key_271_, 0);
v_snd_277_ = lean_ctor_get(v_key_271_, 1);
v_fst_278_ = lean_ctor_get(v_a_268_, 0);
v_snd_279_ = lean_ctor_get(v_a_268_, 1);
v___x_280_ = lean_name_eq(v_fst_276_, v_fst_278_);
if (v___x_280_ == 0)
{
v___y_274_ = v___x_280_;
goto v___jp_273_;
}
else
{
lean_object* v_fst_281_; lean_object* v_snd_282_; lean_object* v_fst_283_; lean_object* v_snd_284_; uint8_t v___x_285_; 
v_fst_281_ = lean_ctor_get(v_snd_277_, 0);
v_snd_282_ = lean_ctor_get(v_snd_277_, 1);
v_fst_283_ = lean_ctor_get(v_snd_279_, 0);
v_snd_284_ = lean_ctor_get(v_snd_279_, 1);
v___x_285_ = lean_expr_eqv(v_fst_281_, v_fst_283_);
if (v___x_285_ == 0)
{
v___y_274_ = v___x_285_;
goto v___jp_273_;
}
else
{
uint8_t v___x_286_; 
v___x_286_ = lean_nat_dec_eq(v_snd_282_, v_snd_284_);
v___y_274_ = v___x_286_;
goto v___jp_273_;
}
}
v___jp_273_:
{
if (v___y_274_ == 0)
{
v_x_269_ = v_tail_272_;
goto _start;
}
else
{
return v___y_274_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__3___redArg___boxed(lean_object* v_a_287_, lean_object* v_x_288_){
_start:
{
uint8_t v_res_289_; lean_object* v_r_290_; 
v_res_289_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__3___redArg(v_a_287_, v_x_288_);
lean_dec(v_x_288_);
lean_dec_ref(v_a_287_);
v_r_290_ = lean_box(v_res_289_);
return v_r_290_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__5___redArg(lean_object* v_a_291_, lean_object* v_b_292_, lean_object* v_x_293_){
_start:
{
if (lean_obj_tag(v_x_293_) == 0)
{
lean_dec(v_b_292_);
lean_dec_ref(v_a_291_);
return v_x_293_;
}
else
{
lean_object* v_key_294_; lean_object* v_value_295_; lean_object* v_tail_296_; lean_object* v___x_298_; uint8_t v_isShared_299_; uint8_t v_isSharedCheck_320_; 
v_key_294_ = lean_ctor_get(v_x_293_, 0);
v_value_295_ = lean_ctor_get(v_x_293_, 1);
v_tail_296_ = lean_ctor_get(v_x_293_, 2);
v_isSharedCheck_320_ = !lean_is_exclusive(v_x_293_);
if (v_isSharedCheck_320_ == 0)
{
v___x_298_ = v_x_293_;
v_isShared_299_ = v_isSharedCheck_320_;
goto v_resetjp_297_;
}
else
{
lean_inc(v_tail_296_);
lean_inc(v_value_295_);
lean_inc(v_key_294_);
lean_dec(v_x_293_);
v___x_298_ = lean_box(0);
v_isShared_299_ = v_isSharedCheck_320_;
goto v_resetjp_297_;
}
v_resetjp_297_:
{
uint8_t v___y_301_; lean_object* v_fst_309_; lean_object* v_snd_310_; lean_object* v_fst_311_; lean_object* v_snd_312_; uint8_t v___x_313_; 
v_fst_309_ = lean_ctor_get(v_key_294_, 0);
v_snd_310_ = lean_ctor_get(v_key_294_, 1);
v_fst_311_ = lean_ctor_get(v_a_291_, 0);
v_snd_312_ = lean_ctor_get(v_a_291_, 1);
v___x_313_ = lean_name_eq(v_fst_309_, v_fst_311_);
if (v___x_313_ == 0)
{
v___y_301_ = v___x_313_;
goto v___jp_300_;
}
else
{
lean_object* v_fst_314_; lean_object* v_snd_315_; lean_object* v_fst_316_; lean_object* v_snd_317_; uint8_t v___x_318_; 
v_fst_314_ = lean_ctor_get(v_snd_310_, 0);
v_snd_315_ = lean_ctor_get(v_snd_310_, 1);
v_fst_316_ = lean_ctor_get(v_snd_312_, 0);
v_snd_317_ = lean_ctor_get(v_snd_312_, 1);
v___x_318_ = lean_expr_eqv(v_fst_314_, v_fst_316_);
if (v___x_318_ == 0)
{
v___y_301_ = v___x_318_;
goto v___jp_300_;
}
else
{
uint8_t v___x_319_; 
v___x_319_ = lean_nat_dec_eq(v_snd_315_, v_snd_317_);
v___y_301_ = v___x_319_;
goto v___jp_300_;
}
}
v___jp_300_:
{
if (v___y_301_ == 0)
{
lean_object* v___x_302_; lean_object* v___x_304_; 
v___x_302_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__5___redArg(v_a_291_, v_b_292_, v_tail_296_);
if (v_isShared_299_ == 0)
{
lean_ctor_set(v___x_298_, 2, v___x_302_);
v___x_304_ = v___x_298_;
goto v_reusejp_303_;
}
else
{
lean_object* v_reuseFailAlloc_305_; 
v_reuseFailAlloc_305_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_305_, 0, v_key_294_);
lean_ctor_set(v_reuseFailAlloc_305_, 1, v_value_295_);
lean_ctor_set(v_reuseFailAlloc_305_, 2, v___x_302_);
v___x_304_ = v_reuseFailAlloc_305_;
goto v_reusejp_303_;
}
v_reusejp_303_:
{
return v___x_304_;
}
}
else
{
lean_object* v___x_307_; 
lean_dec(v_value_295_);
lean_dec(v_key_294_);
if (v_isShared_299_ == 0)
{
lean_ctor_set(v___x_298_, 1, v_b_292_);
lean_ctor_set(v___x_298_, 0, v_a_291_);
v___x_307_ = v___x_298_;
goto v_reusejp_306_;
}
else
{
lean_object* v_reuseFailAlloc_308_; 
v_reuseFailAlloc_308_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_308_, 0, v_a_291_);
lean_ctor_set(v_reuseFailAlloc_308_, 1, v_b_292_);
lean_ctor_set(v_reuseFailAlloc_308_, 2, v_tail_296_);
v___x_307_ = v_reuseFailAlloc_308_;
goto v_reusejp_306_;
}
v_reusejp_306_:
{
return v___x_307_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2___redArg(lean_object* v_m_321_, lean_object* v_a_322_, lean_object* v_b_323_){
_start:
{
lean_object* v_size_324_; lean_object* v_buckets_325_; lean_object* v___x_327_; uint8_t v_isShared_328_; uint8_t v_isSharedCheck_379_; 
v_size_324_ = lean_ctor_get(v_m_321_, 0);
v_buckets_325_ = lean_ctor_get(v_m_321_, 1);
v_isSharedCheck_379_ = !lean_is_exclusive(v_m_321_);
if (v_isSharedCheck_379_ == 0)
{
v___x_327_ = v_m_321_;
v_isShared_328_ = v_isSharedCheck_379_;
goto v_resetjp_326_;
}
else
{
lean_inc(v_buckets_325_);
lean_inc(v_size_324_);
lean_dec(v_m_321_);
v___x_327_ = lean_box(0);
v_isShared_328_ = v_isSharedCheck_379_;
goto v_resetjp_326_;
}
v_resetjp_326_:
{
lean_object* v_fst_329_; lean_object* v_snd_330_; lean_object* v___x_331_; uint64_t v___y_333_; 
v_fst_329_ = lean_ctor_get(v_a_322_, 0);
v_snd_330_ = lean_ctor_get(v_a_322_, 1);
v___x_331_ = lean_array_get_size(v_buckets_325_);
if (lean_obj_tag(v_fst_329_) == 0)
{
uint64_t v___x_377_; 
v___x_377_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg___closed__0);
v___y_333_ = v___x_377_;
goto v___jp_332_;
}
else
{
uint64_t v_hash_378_; 
v_hash_378_ = lean_ctor_get_uint64(v_fst_329_, sizeof(void*)*2);
v___y_333_ = v_hash_378_;
goto v___jp_332_;
}
v___jp_332_:
{
lean_object* v_fst_334_; lean_object* v_snd_335_; uint64_t v___x_336_; uint64_t v___x_337_; uint64_t v___x_338_; uint64_t v___x_339_; uint64_t v___x_340_; uint64_t v___x_341_; uint64_t v_fold_342_; uint64_t v___x_343_; uint64_t v___x_344_; uint64_t v___x_345_; size_t v___x_346_; size_t v___x_347_; size_t v___x_348_; size_t v___x_349_; size_t v___x_350_; lean_object* v_bkt_351_; uint8_t v___x_352_; 
v_fst_334_ = lean_ctor_get(v_snd_330_, 0);
v_snd_335_ = lean_ctor_get(v_snd_330_, 1);
v___x_336_ = l_Lean_Expr_hash(v_fst_334_);
v___x_337_ = lean_uint64_of_nat(v_snd_335_);
v___x_338_ = lean_uint64_mix_hash(v___x_336_, v___x_337_);
v___x_339_ = lean_uint64_mix_hash(v___y_333_, v___x_338_);
v___x_340_ = 32ULL;
v___x_341_ = lean_uint64_shift_right(v___x_339_, v___x_340_);
v_fold_342_ = lean_uint64_xor(v___x_339_, v___x_341_);
v___x_343_ = 16ULL;
v___x_344_ = lean_uint64_shift_right(v_fold_342_, v___x_343_);
v___x_345_ = lean_uint64_xor(v_fold_342_, v___x_344_);
v___x_346_ = lean_uint64_to_usize(v___x_345_);
v___x_347_ = lean_usize_of_nat(v___x_331_);
v___x_348_ = ((size_t)1ULL);
v___x_349_ = lean_usize_sub(v___x_347_, v___x_348_);
v___x_350_ = lean_usize_land(v___x_346_, v___x_349_);
v_bkt_351_ = lean_array_uget_borrowed(v_buckets_325_, v___x_350_);
v___x_352_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__3___redArg(v_a_322_, v_bkt_351_);
if (v___x_352_ == 0)
{
lean_object* v___x_353_; lean_object* v_size_x27_354_; lean_object* v___x_355_; lean_object* v_buckets_x27_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; uint8_t v___x_362_; 
v___x_353_ = lean_unsigned_to_nat(1u);
v_size_x27_354_ = lean_nat_add(v_size_324_, v___x_353_);
lean_dec(v_size_324_);
lean_inc(v_bkt_351_);
v___x_355_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_355_, 0, v_a_322_);
lean_ctor_set(v___x_355_, 1, v_b_323_);
lean_ctor_set(v___x_355_, 2, v_bkt_351_);
v_buckets_x27_356_ = lean_array_uset(v_buckets_325_, v___x_350_, v___x_355_);
v___x_357_ = lean_unsigned_to_nat(4u);
v___x_358_ = lean_nat_mul(v_size_x27_354_, v___x_357_);
v___x_359_ = lean_unsigned_to_nat(3u);
v___x_360_ = lean_nat_div(v___x_358_, v___x_359_);
lean_dec(v___x_358_);
v___x_361_ = lean_array_get_size(v_buckets_x27_356_);
v___x_362_ = lean_nat_dec_le(v___x_360_, v___x_361_);
lean_dec(v___x_360_);
if (v___x_362_ == 0)
{
lean_object* v_val_363_; lean_object* v___x_365_; 
v_val_363_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__4___redArg(v_buckets_x27_356_);
if (v_isShared_328_ == 0)
{
lean_ctor_set(v___x_327_, 1, v_val_363_);
lean_ctor_set(v___x_327_, 0, v_size_x27_354_);
v___x_365_ = v___x_327_;
goto v_reusejp_364_;
}
else
{
lean_object* v_reuseFailAlloc_366_; 
v_reuseFailAlloc_366_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_366_, 0, v_size_x27_354_);
lean_ctor_set(v_reuseFailAlloc_366_, 1, v_val_363_);
v___x_365_ = v_reuseFailAlloc_366_;
goto v_reusejp_364_;
}
v_reusejp_364_:
{
return v___x_365_;
}
}
else
{
lean_object* v___x_368_; 
if (v_isShared_328_ == 0)
{
lean_ctor_set(v___x_327_, 1, v_buckets_x27_356_);
lean_ctor_set(v___x_327_, 0, v_size_x27_354_);
v___x_368_ = v___x_327_;
goto v_reusejp_367_;
}
else
{
lean_object* v_reuseFailAlloc_369_; 
v_reuseFailAlloc_369_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_369_, 0, v_size_x27_354_);
lean_ctor_set(v_reuseFailAlloc_369_, 1, v_buckets_x27_356_);
v___x_368_ = v_reuseFailAlloc_369_;
goto v_reusejp_367_;
}
v_reusejp_367_:
{
return v___x_368_;
}
}
}
else
{
lean_object* v___x_370_; lean_object* v_buckets_x27_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_375_; 
lean_inc(v_bkt_351_);
v___x_370_ = lean_box(0);
v_buckets_x27_371_ = lean_array_uset(v_buckets_325_, v___x_350_, v___x_370_);
v___x_372_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__5___redArg(v_a_322_, v_b_323_, v_bkt_351_);
v___x_373_ = lean_array_uset(v_buckets_x27_371_, v___x_350_, v___x_372_);
if (v_isShared_328_ == 0)
{
lean_ctor_set(v___x_327_, 1, v___x_373_);
v___x_375_ = v___x_327_;
goto v_reusejp_374_;
}
else
{
lean_object* v_reuseFailAlloc_376_; 
v_reuseFailAlloc_376_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_376_, 0, v_size_324_);
lean_ctor_set(v_reuseFailAlloc_376_, 1, v___x_373_);
v___x_375_ = v_reuseFailAlloc_376_;
goto v_reusejp_374_;
}
v_reusejp_374_:
{
return v___x_375_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached(lean_object* v_specThm_382_, lean_object* v_info_383_, lean_object* v_a_384_, lean_object* v_a_385_, lean_object* v_a_386_, lean_object* v_a_387_, lean_object* v_a_388_, lean_object* v_a_389_, lean_object* v_a_390_, lean_object* v_a_391_, lean_object* v_a_392_, lean_object* v_a_393_, lean_object* v_a_394_){
_start:
{
lean_object* v___x_396_; lean_object* v_proof_397_; lean_object* v_excessArgs_398_; lean_object* v_specBackwardRuleCache_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v_key_404_; lean_object* v___x_405_; 
v___x_396_ = lean_st_ref_get(v_a_385_);
v_proof_397_ = lean_ctor_get(v_specThm_382_, 1);
v_excessArgs_398_ = lean_ctor_get(v_info_383_, 2);
v_specBackwardRuleCache_399_ = lean_ctor_get(v___x_396_, 0);
lean_inc_ref(v_specBackwardRuleCache_399_);
lean_dec(v___x_396_);
v___x_400_ = l_Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecProof_key(v_proof_397_);
v___x_401_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_WPInfo_instWP(v_info_383_);
v___x_402_ = lean_array_get_size(v_excessArgs_398_);
v___x_403_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_403_, 0, v___x_401_);
lean_ctor_set(v___x_403_, 1, v___x_402_);
v_key_404_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_key_404_, 0, v___x_400_);
lean_ctor_set(v_key_404_, 1, v___x_403_);
v___x_405_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg(v_specBackwardRuleCache_399_, v_key_404_);
lean_dec_ref(v_specBackwardRuleCache_399_);
if (lean_obj_tag(v___x_405_) == 1)
{
lean_object* v___x_406_; 
lean_dec_ref_known(v_key_404_, 2);
lean_dec_ref(v_info_383_);
lean_dec_ref(v_specThm_382_);
v___x_406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_406_, 0, v___x_405_);
return v___x_406_;
}
else
{
lean_object* v___x_407_; lean_object* v___f_408_; uint8_t v___x_409_; lean_object* v___x_410_; 
lean_dec(v___x_405_);
v___x_407_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached___closed__0));
v___f_408_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached___lam__0___boxed), 15, 3);
lean_closure_set(v___f_408_, 0, v_specThm_382_);
lean_closure_set(v___f_408_, 1, v_info_383_);
lean_closure_set(v___f_408_, 2, v___x_407_);
v___x_409_ = 0;
v___x_410_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__1___redArg(v___f_408_, v___x_409_, v_a_384_, v_a_385_, v_a_386_, v_a_387_, v_a_388_, v_a_389_, v_a_390_, v_a_391_, v_a_392_, v_a_393_, v_a_394_);
if (lean_obj_tag(v___x_410_) == 0)
{
lean_object* v_a_411_; lean_object* v___x_413_; uint8_t v_isShared_414_; uint8_t v_isSharedCheck_446_; 
v_a_411_ = lean_ctor_get(v___x_410_, 0);
v_isSharedCheck_446_ = !lean_is_exclusive(v___x_410_);
if (v_isSharedCheck_446_ == 0)
{
v___x_413_ = v___x_410_;
v_isShared_414_ = v_isSharedCheck_446_;
goto v_resetjp_412_;
}
else
{
lean_inc(v_a_411_);
lean_dec(v___x_410_);
v___x_413_ = lean_box(0);
v_isShared_414_ = v_isSharedCheck_446_;
goto v_resetjp_412_;
}
v_resetjp_412_:
{
if (lean_obj_tag(v_a_411_) == 0)
{
lean_object* v___x_415_; lean_object* v___x_417_; 
lean_dec_ref_known(v_key_404_, 2);
v___x_415_ = lean_box(0);
if (v_isShared_414_ == 0)
{
lean_ctor_set(v___x_413_, 0, v___x_415_);
v___x_417_ = v___x_413_;
goto v_reusejp_416_;
}
else
{
lean_object* v_reuseFailAlloc_418_; 
v_reuseFailAlloc_418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_418_, 0, v___x_415_);
v___x_417_ = v_reuseFailAlloc_418_;
goto v_reusejp_416_;
}
v_reusejp_416_:
{
return v___x_417_;
}
}
else
{
lean_object* v_val_419_; 
v_val_419_ = lean_ctor_get(v_a_411_, 0);
lean_inc(v_val_419_);
lean_dec_ref_known(v_a_411_, 1);
if (lean_obj_tag(v_val_419_) == 1)
{
lean_object* v_val_420_; lean_object* v___x_421_; lean_object* v_specBackwardRuleCache_422_; lean_object* v_splitBackwardRuleCache_423_; lean_object* v_latticeBackwardRuleCache_424_; lean_object* v_invariants_425_; lean_object* v_vcs_426_; lean_object* v_simpState_427_; lean_object* v_fuel_428_; lean_object* v_inlineHandledInvariants_429_; lean_object* v___x_431_; uint8_t v_isShared_432_; uint8_t v_isSharedCheck_441_; 
v_val_420_ = lean_ctor_get(v_val_419_, 0);
v___x_421_ = lean_st_ref_take(v_a_385_);
v_specBackwardRuleCache_422_ = lean_ctor_get(v___x_421_, 0);
v_splitBackwardRuleCache_423_ = lean_ctor_get(v___x_421_, 1);
v_latticeBackwardRuleCache_424_ = lean_ctor_get(v___x_421_, 2);
v_invariants_425_ = lean_ctor_get(v___x_421_, 3);
v_vcs_426_ = lean_ctor_get(v___x_421_, 4);
v_simpState_427_ = lean_ctor_get(v___x_421_, 5);
v_fuel_428_ = lean_ctor_get(v___x_421_, 6);
v_inlineHandledInvariants_429_ = lean_ctor_get(v___x_421_, 7);
v_isSharedCheck_441_ = !lean_is_exclusive(v___x_421_);
if (v_isSharedCheck_441_ == 0)
{
v___x_431_ = v___x_421_;
v_isShared_432_ = v_isSharedCheck_441_;
goto v_resetjp_430_;
}
else
{
lean_inc(v_inlineHandledInvariants_429_);
lean_inc(v_fuel_428_);
lean_inc(v_simpState_427_);
lean_inc(v_vcs_426_);
lean_inc(v_invariants_425_);
lean_inc(v_latticeBackwardRuleCache_424_);
lean_inc(v_splitBackwardRuleCache_423_);
lean_inc(v_specBackwardRuleCache_422_);
lean_dec(v___x_421_);
v___x_431_ = lean_box(0);
v_isShared_432_ = v_isSharedCheck_441_;
goto v_resetjp_430_;
}
v_resetjp_430_:
{
lean_object* v___x_433_; lean_object* v___x_435_; 
lean_inc(v_val_420_);
v___x_433_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2___redArg(v_specBackwardRuleCache_422_, v_key_404_, v_val_420_);
if (v_isShared_432_ == 0)
{
lean_ctor_set(v___x_431_, 0, v___x_433_);
v___x_435_ = v___x_431_;
goto v_reusejp_434_;
}
else
{
lean_object* v_reuseFailAlloc_440_; 
v_reuseFailAlloc_440_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_440_, 0, v___x_433_);
lean_ctor_set(v_reuseFailAlloc_440_, 1, v_splitBackwardRuleCache_423_);
lean_ctor_set(v_reuseFailAlloc_440_, 2, v_latticeBackwardRuleCache_424_);
lean_ctor_set(v_reuseFailAlloc_440_, 3, v_invariants_425_);
lean_ctor_set(v_reuseFailAlloc_440_, 4, v_vcs_426_);
lean_ctor_set(v_reuseFailAlloc_440_, 5, v_simpState_427_);
lean_ctor_set(v_reuseFailAlloc_440_, 6, v_fuel_428_);
lean_ctor_set(v_reuseFailAlloc_440_, 7, v_inlineHandledInvariants_429_);
v___x_435_ = v_reuseFailAlloc_440_;
goto v_reusejp_434_;
}
v_reusejp_434_:
{
lean_object* v___x_436_; lean_object* v___x_438_; 
v___x_436_ = lean_st_ref_set(v_a_385_, v___x_435_);
if (v_isShared_414_ == 0)
{
lean_ctor_set(v___x_413_, 0, v_val_419_);
v___x_438_ = v___x_413_;
goto v_reusejp_437_;
}
else
{
lean_object* v_reuseFailAlloc_439_; 
v_reuseFailAlloc_439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_439_, 0, v_val_419_);
v___x_438_ = v_reuseFailAlloc_439_;
goto v_reusejp_437_;
}
v_reusejp_437_:
{
return v___x_438_;
}
}
}
}
else
{
lean_object* v___x_442_; lean_object* v___x_444_; 
lean_dec(v_val_419_);
lean_dec_ref_known(v_key_404_, 2);
v___x_442_ = lean_box(0);
if (v_isShared_414_ == 0)
{
lean_ctor_set(v___x_413_, 0, v___x_442_);
v___x_444_ = v___x_413_;
goto v_reusejp_443_;
}
else
{
lean_object* v_reuseFailAlloc_445_; 
v_reuseFailAlloc_445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_445_, 0, v___x_442_);
v___x_444_ = v_reuseFailAlloc_445_;
goto v_reusejp_443_;
}
v_reusejp_443_:
{
return v___x_444_;
}
}
}
}
}
else
{
lean_object* v_a_447_; lean_object* v___x_449_; uint8_t v_isShared_450_; uint8_t v_isSharedCheck_454_; 
lean_dec_ref_known(v_key_404_, 2);
v_a_447_ = lean_ctor_get(v___x_410_, 0);
v_isSharedCheck_454_ = !lean_is_exclusive(v___x_410_);
if (v_isSharedCheck_454_ == 0)
{
v___x_449_ = v___x_410_;
v_isShared_450_ = v_isSharedCheck_454_;
goto v_resetjp_448_;
}
else
{
lean_inc(v_a_447_);
lean_dec(v___x_410_);
v___x_449_ = lean_box(0);
v_isShared_450_ = v_isSharedCheck_454_;
goto v_resetjp_448_;
}
v_resetjp_448_:
{
lean_object* v___x_452_; 
if (v_isShared_450_ == 0)
{
v___x_452_ = v___x_449_;
goto v_reusejp_451_;
}
else
{
lean_object* v_reuseFailAlloc_453_; 
v_reuseFailAlloc_453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_453_, 0, v_a_447_);
v___x_452_ = v_reuseFailAlloc_453_;
goto v_reusejp_451_;
}
v_reusejp_451_:
{
return v___x_452_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached___boxed(lean_object* v_specThm_455_, lean_object* v_info_456_, lean_object* v_a_457_, lean_object* v_a_458_, lean_object* v_a_459_, lean_object* v_a_460_, lean_object* v_a_461_, lean_object* v_a_462_, lean_object* v_a_463_, lean_object* v_a_464_, lean_object* v_a_465_, lean_object* v_a_466_, lean_object* v_a_467_, lean_object* v_a_468_){
_start:
{
lean_object* v_res_469_; 
v_res_469_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached(v_specThm_455_, v_info_456_, v_a_457_, v_a_458_, v_a_459_, v_a_460_, v_a_461_, v_a_462_, v_a_463_, v_a_464_, v_a_465_, v_a_466_, v_a_467_);
lean_dec(v_a_467_);
lean_dec_ref(v_a_466_);
lean_dec(v_a_465_);
lean_dec_ref(v_a_464_);
lean_dec(v_a_463_);
lean_dec_ref(v_a_462_);
lean_dec(v_a_461_);
lean_dec_ref(v_a_460_);
lean_dec(v_a_459_);
lean_dec(v_a_458_);
lean_dec_ref(v_a_457_);
return v_res_469_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0(lean_object* v_00_u03b2_470_, lean_object* v_m_471_, lean_object* v_a_472_){
_start:
{
lean_object* v___x_473_; 
v___x_473_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg(v_m_471_, v_a_472_);
return v___x_473_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___boxed(lean_object* v_00_u03b2_474_, lean_object* v_m_475_, lean_object* v_a_476_){
_start:
{
lean_object* v_res_477_; 
v_res_477_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0(v_00_u03b2_474_, v_m_475_, v_a_476_);
lean_dec_ref(v_a_476_);
lean_dec_ref(v_m_475_);
return v_res_477_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2(lean_object* v_00_u03b2_478_, lean_object* v_m_479_, lean_object* v_a_480_, lean_object* v_b_481_){
_start:
{
lean_object* v___x_482_; 
v___x_482_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2___redArg(v_m_479_, v_a_480_, v_b_481_);
return v___x_482_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0_spec__0(lean_object* v_00_u03b2_483_, lean_object* v_a_484_, lean_object* v_x_485_){
_start:
{
lean_object* v___x_486_; 
v___x_486_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0_spec__0___redArg(v_a_484_, v_x_485_);
return v___x_486_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0_spec__0___boxed(lean_object* v_00_u03b2_487_, lean_object* v_a_488_, lean_object* v_x_489_){
_start:
{
lean_object* v_res_490_; 
v_res_490_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0_spec__0(v_00_u03b2_487_, v_a_488_, v_x_489_);
lean_dec(v_x_489_);
lean_dec_ref(v_a_488_);
return v_res_490_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__3(lean_object* v_00_u03b2_491_, lean_object* v_a_492_, lean_object* v_x_493_){
_start:
{
uint8_t v___x_494_; 
v___x_494_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__3___redArg(v_a_492_, v_x_493_);
return v___x_494_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__3___boxed(lean_object* v_00_u03b2_495_, lean_object* v_a_496_, lean_object* v_x_497_){
_start:
{
uint8_t v_res_498_; lean_object* v_r_499_; 
v_res_498_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__3(v_00_u03b2_495_, v_a_496_, v_x_497_);
lean_dec(v_x_497_);
lean_dec_ref(v_a_496_);
v_r_499_ = lean_box(v_res_498_);
return v_r_499_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__4(lean_object* v_00_u03b2_500_, lean_object* v_data_501_){
_start:
{
lean_object* v___x_502_; 
v___x_502_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__4___redArg(v_data_501_);
return v___x_502_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__5(lean_object* v_00_u03b2_503_, lean_object* v_a_504_, lean_object* v_b_505_, lean_object* v_x_506_){
_start:
{
lean_object* v___x_507_; 
v___x_507_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__5___redArg(v_a_504_, v_b_505_, v_x_506_);
return v___x_507_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_508_, lean_object* v_i_509_, lean_object* v_source_510_, lean_object* v_target_511_){
_start:
{
lean_object* v___x_512_; 
v___x_512_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__4_spec__5___redArg(v_i_509_, v_source_510_, v_target_511_);
return v___x_512_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__4_spec__5_spec__6(lean_object* v_00_u03b2_513_, lean_object* v_x_514_, lean_object* v_x_515_){
_start:
{
lean_object* v___x_516_; 
v___x_516_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__4_spec__5_spec__6___redArg(v_x_514_, v_x_515_);
return v___x_516_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForSplitCached___redArg(lean_object* v_splitInfo_523_, lean_object* v_info_524_, lean_object* v_a_525_, lean_object* v_a_526_, lean_object* v_a_527_, lean_object* v_a_528_, lean_object* v_a_529_){
_start:
{
lean_object* v___y_532_; 
switch(lean_obj_tag(v_splitInfo_523_))
{
case 0:
{
lean_object* v___x_576_; 
v___x_576_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForSplitCached___redArg___closed__1));
v___y_532_ = v___x_576_;
goto v___jp_531_;
}
case 1:
{
lean_object* v___x_577_; 
v___x_577_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForSplitCached___redArg___closed__3));
v___y_532_ = v___x_577_;
goto v___jp_531_;
}
default: 
{
lean_object* v_matcherApp_578_; lean_object* v_matcherName_579_; 
v_matcherApp_578_ = lean_ctor_get(v_splitInfo_523_, 0);
v_matcherName_579_ = lean_ctor_get(v_matcherApp_578_, 1);
lean_inc(v_matcherName_579_);
v___y_532_ = v_matcherName_579_;
goto v___jp_531_;
}
}
v___jp_531_:
{
lean_object* v___x_533_; lean_object* v_excessArgs_534_; lean_object* v_splitBackwardRuleCache_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v_key_539_; lean_object* v___x_540_; 
v___x_533_ = lean_st_ref_get(v_a_525_);
v_excessArgs_534_ = lean_ctor_get(v_info_524_, 2);
v_splitBackwardRuleCache_535_ = lean_ctor_get(v___x_533_, 1);
lean_inc_ref(v_splitBackwardRuleCache_535_);
lean_dec(v___x_533_);
v___x_536_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_WPInfo_instWP(v_info_524_);
v___x_537_ = lean_array_get_size(v_excessArgs_534_);
v___x_538_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_538_, 0, v___x_536_);
lean_ctor_set(v___x_538_, 1, v___x_537_);
v_key_539_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_key_539_, 0, v___y_532_);
lean_ctor_set(v_key_539_, 1, v___x_538_);
v___x_540_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg(v_splitBackwardRuleCache_535_, v_key_539_);
lean_dec_ref(v_splitBackwardRuleCache_535_);
if (lean_obj_tag(v___x_540_) == 1)
{
lean_object* v_val_541_; lean_object* v___x_543_; uint8_t v_isShared_544_; uint8_t v_isSharedCheck_548_; 
lean_dec_ref_known(v_key_539_, 2);
lean_dec_ref(v_info_524_);
lean_dec_ref(v_splitInfo_523_);
v_val_541_ = lean_ctor_get(v___x_540_, 0);
v_isSharedCheck_548_ = !lean_is_exclusive(v___x_540_);
if (v_isSharedCheck_548_ == 0)
{
v___x_543_ = v___x_540_;
v_isShared_544_ = v_isSharedCheck_548_;
goto v_resetjp_542_;
}
else
{
lean_inc(v_val_541_);
lean_dec(v___x_540_);
v___x_543_ = lean_box(0);
v_isShared_544_ = v_isSharedCheck_548_;
goto v_resetjp_542_;
}
v_resetjp_542_:
{
lean_object* v___x_546_; 
if (v_isShared_544_ == 0)
{
lean_ctor_set_tag(v___x_543_, 0);
v___x_546_ = v___x_543_;
goto v_reusejp_545_;
}
else
{
lean_object* v_reuseFailAlloc_547_; 
v_reuseFailAlloc_547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_547_, 0, v_val_541_);
v___x_546_ = v_reuseFailAlloc_547_;
goto v_reusejp_545_;
}
v_reusejp_545_:
{
return v___x_546_;
}
}
}
else
{
lean_object* v___x_549_; 
lean_dec(v___x_540_);
v___x_549_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForSplit(v_splitInfo_523_, v_info_524_, v_a_526_, v_a_527_, v_a_528_, v_a_529_);
if (lean_obj_tag(v___x_549_) == 0)
{
lean_object* v_a_550_; lean_object* v___x_552_; uint8_t v_isShared_553_; uint8_t v_isSharedCheck_575_; 
v_a_550_ = lean_ctor_get(v___x_549_, 0);
v_isSharedCheck_575_ = !lean_is_exclusive(v___x_549_);
if (v_isSharedCheck_575_ == 0)
{
v___x_552_ = v___x_549_;
v_isShared_553_ = v_isSharedCheck_575_;
goto v_resetjp_551_;
}
else
{
lean_inc(v_a_550_);
lean_dec(v___x_549_);
v___x_552_ = lean_box(0);
v_isShared_553_ = v_isSharedCheck_575_;
goto v_resetjp_551_;
}
v_resetjp_551_:
{
lean_object* v___x_554_; lean_object* v_specBackwardRuleCache_555_; lean_object* v_splitBackwardRuleCache_556_; lean_object* v_latticeBackwardRuleCache_557_; lean_object* v_invariants_558_; lean_object* v_vcs_559_; lean_object* v_simpState_560_; lean_object* v_fuel_561_; lean_object* v_inlineHandledInvariants_562_; lean_object* v___x_564_; uint8_t v_isShared_565_; uint8_t v_isSharedCheck_574_; 
v___x_554_ = lean_st_ref_take(v_a_525_);
v_specBackwardRuleCache_555_ = lean_ctor_get(v___x_554_, 0);
v_splitBackwardRuleCache_556_ = lean_ctor_get(v___x_554_, 1);
v_latticeBackwardRuleCache_557_ = lean_ctor_get(v___x_554_, 2);
v_invariants_558_ = lean_ctor_get(v___x_554_, 3);
v_vcs_559_ = lean_ctor_get(v___x_554_, 4);
v_simpState_560_ = lean_ctor_get(v___x_554_, 5);
v_fuel_561_ = lean_ctor_get(v___x_554_, 6);
v_inlineHandledInvariants_562_ = lean_ctor_get(v___x_554_, 7);
v_isSharedCheck_574_ = !lean_is_exclusive(v___x_554_);
if (v_isSharedCheck_574_ == 0)
{
v___x_564_ = v___x_554_;
v_isShared_565_ = v_isSharedCheck_574_;
goto v_resetjp_563_;
}
else
{
lean_inc(v_inlineHandledInvariants_562_);
lean_inc(v_fuel_561_);
lean_inc(v_simpState_560_);
lean_inc(v_vcs_559_);
lean_inc(v_invariants_558_);
lean_inc(v_latticeBackwardRuleCache_557_);
lean_inc(v_splitBackwardRuleCache_556_);
lean_inc(v_specBackwardRuleCache_555_);
lean_dec(v___x_554_);
v___x_564_ = lean_box(0);
v_isShared_565_ = v_isSharedCheck_574_;
goto v_resetjp_563_;
}
v_resetjp_563_:
{
lean_object* v___x_566_; lean_object* v___x_568_; 
lean_inc(v_a_550_);
v___x_566_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2___redArg(v_splitBackwardRuleCache_556_, v_key_539_, v_a_550_);
if (v_isShared_565_ == 0)
{
lean_ctor_set(v___x_564_, 1, v___x_566_);
v___x_568_ = v___x_564_;
goto v_reusejp_567_;
}
else
{
lean_object* v_reuseFailAlloc_573_; 
v_reuseFailAlloc_573_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_573_, 0, v_specBackwardRuleCache_555_);
lean_ctor_set(v_reuseFailAlloc_573_, 1, v___x_566_);
lean_ctor_set(v_reuseFailAlloc_573_, 2, v_latticeBackwardRuleCache_557_);
lean_ctor_set(v_reuseFailAlloc_573_, 3, v_invariants_558_);
lean_ctor_set(v_reuseFailAlloc_573_, 4, v_vcs_559_);
lean_ctor_set(v_reuseFailAlloc_573_, 5, v_simpState_560_);
lean_ctor_set(v_reuseFailAlloc_573_, 6, v_fuel_561_);
lean_ctor_set(v_reuseFailAlloc_573_, 7, v_inlineHandledInvariants_562_);
v___x_568_ = v_reuseFailAlloc_573_;
goto v_reusejp_567_;
}
v_reusejp_567_:
{
lean_object* v___x_569_; lean_object* v___x_571_; 
v___x_569_ = lean_st_ref_set(v_a_525_, v___x_568_);
if (v_isShared_553_ == 0)
{
v___x_571_ = v___x_552_;
goto v_reusejp_570_;
}
else
{
lean_object* v_reuseFailAlloc_572_; 
v_reuseFailAlloc_572_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_572_, 0, v_a_550_);
v___x_571_ = v_reuseFailAlloc_572_;
goto v_reusejp_570_;
}
v_reusejp_570_:
{
return v___x_571_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_key_539_, 2);
return v___x_549_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForSplitCached___redArg___boxed(lean_object* v_splitInfo_580_, lean_object* v_info_581_, lean_object* v_a_582_, lean_object* v_a_583_, lean_object* v_a_584_, lean_object* v_a_585_, lean_object* v_a_586_, lean_object* v_a_587_){
_start:
{
lean_object* v_res_588_; 
v_res_588_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForSplitCached___redArg(v_splitInfo_580_, v_info_581_, v_a_582_, v_a_583_, v_a_584_, v_a_585_, v_a_586_);
lean_dec(v_a_586_);
lean_dec_ref(v_a_585_);
lean_dec(v_a_584_);
lean_dec_ref(v_a_583_);
lean_dec(v_a_582_);
return v_res_588_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForSplitCached(lean_object* v_splitInfo_589_, lean_object* v_info_590_, lean_object* v_a_591_, lean_object* v_a_592_, lean_object* v_a_593_, lean_object* v_a_594_, lean_object* v_a_595_, lean_object* v_a_596_, lean_object* v_a_597_, lean_object* v_a_598_, lean_object* v_a_599_, lean_object* v_a_600_, lean_object* v_a_601_){
_start:
{
lean_object* v___x_603_; 
v___x_603_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForSplitCached___redArg(v_splitInfo_589_, v_info_590_, v_a_592_, v_a_598_, v_a_599_, v_a_600_, v_a_601_);
return v___x_603_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForSplitCached___boxed(lean_object* v_splitInfo_604_, lean_object* v_info_605_, lean_object* v_a_606_, lean_object* v_a_607_, lean_object* v_a_608_, lean_object* v_a_609_, lean_object* v_a_610_, lean_object* v_a_611_, lean_object* v_a_612_, lean_object* v_a_613_, lean_object* v_a_614_, lean_object* v_a_615_, lean_object* v_a_616_, lean_object* v_a_617_){
_start:
{
lean_object* v_res_618_; 
v_res_618_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForSplitCached(v_splitInfo_604_, v_info_605_, v_a_606_, v_a_607_, v_a_608_, v_a_609_, v_a_610_, v_a_611_, v_a_612_, v_a_613_, v_a_614_, v_a_615_, v_a_616_);
lean_dec(v_a_616_);
lean_dec_ref(v_a_615_);
lean_dec(v_a_614_);
lean_dec_ref(v_a_613_);
lean_dec(v_a_612_);
lean_dec_ref(v_a_611_);
lean_dec(v_a_610_);
lean_dec_ref(v_a_609_);
lean_dec(v_a_608_);
lean_dec(v_a_607_);
lean_dec_ref(v_a_606_);
return v_res_618_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__1_spec__1_spec__2___redArg(lean_object* v_xs_619_, lean_object* v_ys_620_, lean_object* v_x_621_){
_start:
{
lean_object* v_zero_622_; uint8_t v_isZero_623_; 
v_zero_622_ = lean_unsigned_to_nat(0u);
v_isZero_623_ = lean_nat_dec_eq(v_x_621_, v_zero_622_);
if (v_isZero_623_ == 1)
{
lean_dec(v_x_621_);
return v_isZero_623_;
}
else
{
lean_object* v_one_624_; lean_object* v_n_625_; lean_object* v___x_626_; lean_object* v___x_627_; uint8_t v___x_628_; 
v_one_624_ = lean_unsigned_to_nat(1u);
v_n_625_ = lean_nat_sub(v_x_621_, v_one_624_);
lean_dec(v_x_621_);
v___x_626_ = lean_array_fget_borrowed(v_xs_619_, v_n_625_);
v___x_627_ = lean_array_fget_borrowed(v_ys_620_, v_n_625_);
v___x_628_ = lean_expr_eqv(v___x_626_, v___x_627_);
if (v___x_628_ == 0)
{
lean_dec(v_n_625_);
return v___x_628_;
}
else
{
v_x_621_ = v_n_625_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__1_spec__1_spec__2___redArg___boxed(lean_object* v_xs_630_, lean_object* v_ys_631_, lean_object* v_x_632_){
_start:
{
uint8_t v_res_633_; lean_object* v_r_634_; 
v_res_633_ = l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__1_spec__1_spec__2___redArg(v_xs_630_, v_ys_631_, v_x_632_);
lean_dec_ref(v_ys_631_);
lean_dec_ref(v_xs_630_);
v_r_634_ = lean_box(v_res_633_);
return v_r_634_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2_spec__4___redArg(lean_object* v_a_635_, lean_object* v_x_636_){
_start:
{
if (lean_obj_tag(v_x_636_) == 0)
{
uint8_t v___x_637_; 
v___x_637_ = 0;
return v___x_637_;
}
else
{
lean_object* v_key_638_; lean_object* v_tail_639_; uint8_t v___y_641_; lean_object* v_fst_643_; lean_object* v_snd_644_; lean_object* v_fst_645_; lean_object* v_snd_646_; uint8_t v___x_647_; 
v_key_638_ = lean_ctor_get(v_x_636_, 0);
v_tail_639_ = lean_ctor_get(v_x_636_, 2);
v_fst_643_ = lean_ctor_get(v_key_638_, 0);
v_snd_644_ = lean_ctor_get(v_key_638_, 1);
v_fst_645_ = lean_ctor_get(v_a_635_, 0);
v_snd_646_ = lean_ctor_get(v_a_635_, 1);
v___x_647_ = lean_name_eq(v_fst_643_, v_fst_645_);
if (v___x_647_ == 0)
{
v___y_641_ = v___x_647_;
goto v___jp_640_;
}
else
{
lean_object* v_fst_648_; lean_object* v_snd_649_; lean_object* v_fst_650_; lean_object* v_snd_651_; lean_object* v___x_652_; lean_object* v___x_653_; uint8_t v___x_654_; 
v_fst_648_ = lean_ctor_get(v_snd_644_, 0);
v_snd_649_ = lean_ctor_get(v_snd_644_, 1);
v_fst_650_ = lean_ctor_get(v_snd_646_, 0);
v_snd_651_ = lean_ctor_get(v_snd_646_, 1);
v___x_652_ = lean_array_get_size(v_fst_648_);
v___x_653_ = lean_array_get_size(v_fst_650_);
v___x_654_ = lean_nat_dec_eq(v___x_652_, v___x_653_);
if (v___x_654_ == 0)
{
v_x_636_ = v_tail_639_;
goto _start;
}
else
{
uint8_t v___x_656_; 
v___x_656_ = l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__1_spec__1_spec__2___redArg(v_fst_648_, v_fst_650_, v___x_652_);
if (v___x_656_ == 0)
{
v_x_636_ = v_tail_639_;
goto _start;
}
else
{
uint8_t v___x_658_; 
v___x_658_ = lean_nat_dec_eq(v_snd_649_, v_snd_651_);
v___y_641_ = v___x_658_;
goto v___jp_640_;
}
}
}
v___jp_640_:
{
if (v___y_641_ == 0)
{
v_x_636_ = v_tail_639_;
goto _start;
}
else
{
return v___y_641_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2_spec__4___redArg___boxed(lean_object* v_a_659_, lean_object* v_x_660_){
_start:
{
uint8_t v_res_661_; lean_object* v_r_662_; 
v_res_661_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2_spec__4___redArg(v_a_659_, v_x_660_);
lean_dec(v_x_660_);
lean_dec_ref(v_a_659_);
v_r_662_ = lean_box(v_res_661_);
return v_r_662_;
}
}
LEAN_EXPORT uint64_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__1_spec__2(lean_object* v_as_663_, size_t v_i_664_, size_t v_stop_665_, uint64_t v_b_666_){
_start:
{
uint8_t v___x_667_; 
v___x_667_ = lean_usize_dec_eq(v_i_664_, v_stop_665_);
if (v___x_667_ == 0)
{
lean_object* v___x_668_; uint64_t v___x_669_; uint64_t v___x_670_; size_t v___x_671_; size_t v___x_672_; 
v___x_668_ = lean_array_uget_borrowed(v_as_663_, v_i_664_);
v___x_669_ = l_Lean_Expr_hash(v___x_668_);
v___x_670_ = lean_uint64_mix_hash(v_b_666_, v___x_669_);
v___x_671_ = ((size_t)1ULL);
v___x_672_ = lean_usize_add(v_i_664_, v___x_671_);
v_i_664_ = v___x_672_;
v_b_666_ = v___x_670_;
goto _start;
}
else
{
return v_b_666_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__1_spec__2___boxed(lean_object* v_as_674_, lean_object* v_i_675_, lean_object* v_stop_676_, lean_object* v_b_677_){
_start:
{
size_t v_i_boxed_678_; size_t v_stop_boxed_679_; uint64_t v_b_boxed_680_; uint64_t v_res_681_; lean_object* v_r_682_; 
v_i_boxed_678_ = lean_unbox_usize(v_i_675_);
lean_dec(v_i_675_);
v_stop_boxed_679_ = lean_unbox_usize(v_stop_676_);
lean_dec(v_stop_676_);
v_b_boxed_680_ = lean_unbox_uint64(v_b_677_);
lean_dec_ref(v_b_677_);
v_res_681_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__1_spec__2(v_as_674_, v_i_boxed_678_, v_stop_boxed_679_, v_b_boxed_680_);
lean_dec_ref(v_as_674_);
v_r_682_ = lean_box_uint64(v_res_681_);
return v_r_682_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2_spec__5_spec__7_spec__8___redArg(lean_object* v_x_683_, lean_object* v_x_684_){
_start:
{
if (lean_obj_tag(v_x_684_) == 0)
{
return v_x_683_;
}
else
{
lean_object* v_key_685_; lean_object* v_value_686_; lean_object* v_tail_687_; lean_object* v___x_689_; uint8_t v_isShared_690_; uint8_t v_isSharedCheck_735_; 
v_key_685_ = lean_ctor_get(v_x_684_, 0);
v_value_686_ = lean_ctor_get(v_x_684_, 1);
v_tail_687_ = lean_ctor_get(v_x_684_, 2);
v_isSharedCheck_735_ = !lean_is_exclusive(v_x_684_);
if (v_isSharedCheck_735_ == 0)
{
v___x_689_ = v_x_684_;
v_isShared_690_ = v_isSharedCheck_735_;
goto v_resetjp_688_;
}
else
{
lean_inc(v_tail_687_);
lean_inc(v_value_686_);
lean_inc(v_key_685_);
lean_dec(v_x_684_);
v___x_689_ = lean_box(0);
v_isShared_690_ = v_isSharedCheck_735_;
goto v_resetjp_688_;
}
v_resetjp_688_:
{
lean_object* v_fst_691_; lean_object* v_snd_692_; lean_object* v___x_693_; uint64_t v___y_695_; lean_object* v___y_696_; uint64_t v___y_697_; uint64_t v___y_719_; 
v_fst_691_ = lean_ctor_get(v_key_685_, 0);
v_snd_692_ = lean_ctor_get(v_key_685_, 1);
v___x_693_ = lean_array_get_size(v_x_683_);
if (lean_obj_tag(v_fst_691_) == 0)
{
uint64_t v___x_733_; 
v___x_733_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg___closed__0);
v___y_719_ = v___x_733_;
goto v___jp_718_;
}
else
{
uint64_t v_hash_734_; 
v_hash_734_ = lean_ctor_get_uint64(v_fst_691_, sizeof(void*)*2);
v___y_719_ = v_hash_734_;
goto v___jp_718_;
}
v___jp_694_:
{
uint64_t v___x_698_; uint64_t v___x_699_; uint64_t v___x_700_; uint64_t v___x_701_; uint64_t v___x_702_; uint64_t v_fold_703_; uint64_t v___x_704_; uint64_t v___x_705_; uint64_t v___x_706_; size_t v___x_707_; size_t v___x_708_; size_t v___x_709_; size_t v___x_710_; size_t v___x_711_; lean_object* v___x_712_; lean_object* v___x_714_; 
v___x_698_ = lean_uint64_of_nat(v___y_696_);
lean_dec(v___y_696_);
v___x_699_ = lean_uint64_mix_hash(v___y_697_, v___x_698_);
v___x_700_ = lean_uint64_mix_hash(v___y_695_, v___x_699_);
v___x_701_ = 32ULL;
v___x_702_ = lean_uint64_shift_right(v___x_700_, v___x_701_);
v_fold_703_ = lean_uint64_xor(v___x_700_, v___x_702_);
v___x_704_ = 16ULL;
v___x_705_ = lean_uint64_shift_right(v_fold_703_, v___x_704_);
v___x_706_ = lean_uint64_xor(v_fold_703_, v___x_705_);
v___x_707_ = lean_uint64_to_usize(v___x_706_);
v___x_708_ = lean_usize_of_nat(v___x_693_);
v___x_709_ = ((size_t)1ULL);
v___x_710_ = lean_usize_sub(v___x_708_, v___x_709_);
v___x_711_ = lean_usize_land(v___x_707_, v___x_710_);
v___x_712_ = lean_array_uget_borrowed(v_x_683_, v___x_711_);
lean_inc(v___x_712_);
if (v_isShared_690_ == 0)
{
lean_ctor_set(v___x_689_, 2, v___x_712_);
v___x_714_ = v___x_689_;
goto v_reusejp_713_;
}
else
{
lean_object* v_reuseFailAlloc_717_; 
v_reuseFailAlloc_717_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_717_, 0, v_key_685_);
lean_ctor_set(v_reuseFailAlloc_717_, 1, v_value_686_);
lean_ctor_set(v_reuseFailAlloc_717_, 2, v___x_712_);
v___x_714_ = v_reuseFailAlloc_717_;
goto v_reusejp_713_;
}
v_reusejp_713_:
{
lean_object* v___x_715_; 
v___x_715_ = lean_array_uset(v_x_683_, v___x_711_, v___x_714_);
v_x_683_ = v___x_715_;
v_x_684_ = v_tail_687_;
goto _start;
}
}
v___jp_718_:
{
lean_object* v_fst_720_; lean_object* v_snd_721_; uint64_t v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; uint8_t v___x_725_; 
v_fst_720_ = lean_ctor_get(v_snd_692_, 0);
v_snd_721_ = lean_ctor_get(v_snd_692_, 1);
v___x_722_ = 7ULL;
v___x_723_ = lean_unsigned_to_nat(0u);
v___x_724_ = lean_array_get_size(v_fst_720_);
v___x_725_ = lean_nat_dec_lt(v___x_723_, v___x_724_);
if (v___x_725_ == 0)
{
lean_inc(v_snd_721_);
v___y_695_ = v___y_719_;
v___y_696_ = v_snd_721_;
v___y_697_ = v___x_722_;
goto v___jp_694_;
}
else
{
uint8_t v___x_726_; 
v___x_726_ = lean_nat_dec_le(v___x_724_, v___x_724_);
if (v___x_726_ == 0)
{
if (v___x_725_ == 0)
{
lean_inc(v_snd_721_);
v___y_695_ = v___y_719_;
v___y_696_ = v_snd_721_;
v___y_697_ = v___x_722_;
goto v___jp_694_;
}
else
{
size_t v___x_727_; size_t v___x_728_; uint64_t v___x_729_; 
v___x_727_ = ((size_t)0ULL);
v___x_728_ = lean_usize_of_nat(v___x_724_);
v___x_729_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__1_spec__2(v_fst_720_, v___x_727_, v___x_728_, v___x_722_);
lean_inc(v_snd_721_);
v___y_695_ = v___y_719_;
v___y_696_ = v_snd_721_;
v___y_697_ = v___x_729_;
goto v___jp_694_;
}
}
else
{
size_t v___x_730_; size_t v___x_731_; uint64_t v___x_732_; 
v___x_730_ = ((size_t)0ULL);
v___x_731_ = lean_usize_of_nat(v___x_724_);
v___x_732_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__1_spec__2(v_fst_720_, v___x_730_, v___x_731_, v___x_722_);
lean_inc(v_snd_721_);
v___y_695_ = v___y_719_;
v___y_696_ = v_snd_721_;
v___y_697_ = v___x_732_;
goto v___jp_694_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2_spec__5_spec__7___redArg(lean_object* v_i_736_, lean_object* v_source_737_, lean_object* v_target_738_){
_start:
{
lean_object* v___x_739_; uint8_t v___x_740_; 
v___x_739_ = lean_array_get_size(v_source_737_);
v___x_740_ = lean_nat_dec_lt(v_i_736_, v___x_739_);
if (v___x_740_ == 0)
{
lean_dec_ref(v_source_737_);
lean_dec(v_i_736_);
return v_target_738_;
}
else
{
lean_object* v_es_741_; lean_object* v___x_742_; lean_object* v_source_743_; lean_object* v_target_744_; lean_object* v___x_745_; lean_object* v___x_746_; 
v_es_741_ = lean_array_fget(v_source_737_, v_i_736_);
v___x_742_ = lean_box(0);
v_source_743_ = lean_array_fset(v_source_737_, v_i_736_, v___x_742_);
v_target_744_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2_spec__5_spec__7_spec__8___redArg(v_target_738_, v_es_741_);
v___x_745_ = lean_unsigned_to_nat(1u);
v___x_746_ = lean_nat_add(v_i_736_, v___x_745_);
lean_dec(v_i_736_);
v_i_736_ = v___x_746_;
v_source_737_ = v_source_743_;
v_target_738_ = v_target_744_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2_spec__5___redArg(lean_object* v_data_748_){
_start:
{
lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v_nbuckets_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; 
v___x_749_ = lean_array_get_size(v_data_748_);
v___x_750_ = lean_unsigned_to_nat(2u);
v_nbuckets_751_ = lean_nat_mul(v___x_749_, v___x_750_);
v___x_752_ = lean_unsigned_to_nat(0u);
v___x_753_ = lean_box(0);
v___x_754_ = lean_mk_array(v_nbuckets_751_, v___x_753_);
v___x_755_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2_spec__5_spec__7___redArg(v___x_752_, v_data_748_, v___x_754_);
return v___x_755_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2_spec__6___redArg(lean_object* v_a_756_, lean_object* v_b_757_, lean_object* v_x_758_){
_start:
{
if (lean_obj_tag(v_x_758_) == 0)
{
lean_dec(v_b_757_);
lean_dec_ref(v_a_756_);
return v_x_758_;
}
else
{
lean_object* v_key_759_; lean_object* v_value_760_; lean_object* v_tail_761_; lean_object* v___x_763_; uint8_t v_isShared_764_; uint8_t v_isSharedCheck_787_; 
v_key_759_ = lean_ctor_get(v_x_758_, 0);
v_value_760_ = lean_ctor_get(v_x_758_, 1);
v_tail_761_ = lean_ctor_get(v_x_758_, 2);
v_isSharedCheck_787_ = !lean_is_exclusive(v_x_758_);
if (v_isSharedCheck_787_ == 0)
{
v___x_763_ = v_x_758_;
v_isShared_764_ = v_isSharedCheck_787_;
goto v_resetjp_762_;
}
else
{
lean_inc(v_tail_761_);
lean_inc(v_value_760_);
lean_inc(v_key_759_);
lean_dec(v_x_758_);
v___x_763_ = lean_box(0);
v_isShared_764_ = v_isSharedCheck_787_;
goto v_resetjp_762_;
}
v_resetjp_762_:
{
uint8_t v___y_771_; lean_object* v_fst_773_; lean_object* v_snd_774_; lean_object* v_fst_775_; lean_object* v_snd_776_; uint8_t v___x_777_; 
v_fst_773_ = lean_ctor_get(v_key_759_, 0);
v_snd_774_ = lean_ctor_get(v_key_759_, 1);
v_fst_775_ = lean_ctor_get(v_a_756_, 0);
v_snd_776_ = lean_ctor_get(v_a_756_, 1);
v___x_777_ = lean_name_eq(v_fst_773_, v_fst_775_);
if (v___x_777_ == 0)
{
v___y_771_ = v___x_777_;
goto v___jp_770_;
}
else
{
lean_object* v_fst_778_; lean_object* v_snd_779_; lean_object* v_fst_780_; lean_object* v_snd_781_; lean_object* v___x_782_; lean_object* v___x_783_; uint8_t v___x_784_; 
v_fst_778_ = lean_ctor_get(v_snd_774_, 0);
v_snd_779_ = lean_ctor_get(v_snd_774_, 1);
v_fst_780_ = lean_ctor_get(v_snd_776_, 0);
v_snd_781_ = lean_ctor_get(v_snd_776_, 1);
v___x_782_ = lean_array_get_size(v_fst_778_);
v___x_783_ = lean_array_get_size(v_fst_780_);
v___x_784_ = lean_nat_dec_eq(v___x_782_, v___x_783_);
if (v___x_784_ == 0)
{
goto v___jp_765_;
}
else
{
uint8_t v___x_785_; 
v___x_785_ = l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__1_spec__1_spec__2___redArg(v_fst_778_, v_fst_780_, v___x_782_);
if (v___x_785_ == 0)
{
goto v___jp_765_;
}
else
{
uint8_t v___x_786_; 
v___x_786_ = lean_nat_dec_eq(v_snd_779_, v_snd_781_);
v___y_771_ = v___x_786_;
goto v___jp_770_;
}
}
}
v___jp_765_:
{
lean_object* v___x_766_; lean_object* v___x_768_; 
v___x_766_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2_spec__6___redArg(v_a_756_, v_b_757_, v_tail_761_);
if (v_isShared_764_ == 0)
{
lean_ctor_set(v___x_763_, 2, v___x_766_);
v___x_768_ = v___x_763_;
goto v_reusejp_767_;
}
else
{
lean_object* v_reuseFailAlloc_769_; 
v_reuseFailAlloc_769_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_769_, 0, v_key_759_);
lean_ctor_set(v_reuseFailAlloc_769_, 1, v_value_760_);
lean_ctor_set(v_reuseFailAlloc_769_, 2, v___x_766_);
v___x_768_ = v_reuseFailAlloc_769_;
goto v_reusejp_767_;
}
v_reusejp_767_:
{
return v___x_768_;
}
}
v___jp_770_:
{
if (v___y_771_ == 0)
{
goto v___jp_765_;
}
else
{
lean_object* v___x_772_; 
lean_del_object(v___x_763_);
lean_dec(v_value_760_);
lean_dec(v_key_759_);
v___x_772_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_772_, 0, v_a_756_);
lean_ctor_set(v___x_772_, 1, v_b_757_);
lean_ctor_set(v___x_772_, 2, v_tail_761_);
return v___x_772_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2___redArg(lean_object* v_m_788_, lean_object* v_a_789_, lean_object* v_b_790_){
_start:
{
lean_object* v_size_791_; lean_object* v_buckets_792_; lean_object* v___x_794_; uint8_t v_isShared_795_; uint8_t v_isSharedCheck_860_; 
v_size_791_ = lean_ctor_get(v_m_788_, 0);
v_buckets_792_ = lean_ctor_get(v_m_788_, 1);
v_isSharedCheck_860_ = !lean_is_exclusive(v_m_788_);
if (v_isSharedCheck_860_ == 0)
{
v___x_794_ = v_m_788_;
v_isShared_795_ = v_isSharedCheck_860_;
goto v_resetjp_793_;
}
else
{
lean_inc(v_buckets_792_);
lean_inc(v_size_791_);
lean_dec(v_m_788_);
v___x_794_ = lean_box(0);
v_isShared_795_ = v_isSharedCheck_860_;
goto v_resetjp_793_;
}
v_resetjp_793_:
{
lean_object* v_fst_796_; lean_object* v_snd_797_; lean_object* v___x_798_; lean_object* v___y_800_; uint64_t v___y_801_; uint64_t v___y_802_; uint64_t v___y_844_; 
v_fst_796_ = lean_ctor_get(v_a_789_, 0);
v_snd_797_ = lean_ctor_get(v_a_789_, 1);
v___x_798_ = lean_array_get_size(v_buckets_792_);
if (lean_obj_tag(v_fst_796_) == 0)
{
uint64_t v___x_858_; 
v___x_858_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg___closed__0);
v___y_844_ = v___x_858_;
goto v___jp_843_;
}
else
{
uint64_t v_hash_859_; 
v_hash_859_ = lean_ctor_get_uint64(v_fst_796_, sizeof(void*)*2);
v___y_844_ = v_hash_859_;
goto v___jp_843_;
}
v___jp_799_:
{
uint64_t v___x_803_; uint64_t v___x_804_; uint64_t v___x_805_; uint64_t v___x_806_; uint64_t v___x_807_; uint64_t v_fold_808_; uint64_t v___x_809_; uint64_t v___x_810_; uint64_t v___x_811_; size_t v___x_812_; size_t v___x_813_; size_t v___x_814_; size_t v___x_815_; size_t v___x_816_; lean_object* v_bkt_817_; uint8_t v___x_818_; 
v___x_803_ = lean_uint64_of_nat(v___y_800_);
lean_dec(v___y_800_);
v___x_804_ = lean_uint64_mix_hash(v___y_802_, v___x_803_);
v___x_805_ = lean_uint64_mix_hash(v___y_801_, v___x_804_);
v___x_806_ = 32ULL;
v___x_807_ = lean_uint64_shift_right(v___x_805_, v___x_806_);
v_fold_808_ = lean_uint64_xor(v___x_805_, v___x_807_);
v___x_809_ = 16ULL;
v___x_810_ = lean_uint64_shift_right(v_fold_808_, v___x_809_);
v___x_811_ = lean_uint64_xor(v_fold_808_, v___x_810_);
v___x_812_ = lean_uint64_to_usize(v___x_811_);
v___x_813_ = lean_usize_of_nat(v___x_798_);
v___x_814_ = ((size_t)1ULL);
v___x_815_ = lean_usize_sub(v___x_813_, v___x_814_);
v___x_816_ = lean_usize_land(v___x_812_, v___x_815_);
v_bkt_817_ = lean_array_uget_borrowed(v_buckets_792_, v___x_816_);
v___x_818_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2_spec__4___redArg(v_a_789_, v_bkt_817_);
if (v___x_818_ == 0)
{
lean_object* v___x_819_; lean_object* v_size_x27_820_; lean_object* v___x_821_; lean_object* v_buckets_x27_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; uint8_t v___x_828_; 
v___x_819_ = lean_unsigned_to_nat(1u);
v_size_x27_820_ = lean_nat_add(v_size_791_, v___x_819_);
lean_dec(v_size_791_);
lean_inc(v_bkt_817_);
v___x_821_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_821_, 0, v_a_789_);
lean_ctor_set(v___x_821_, 1, v_b_790_);
lean_ctor_set(v___x_821_, 2, v_bkt_817_);
v_buckets_x27_822_ = lean_array_uset(v_buckets_792_, v___x_816_, v___x_821_);
v___x_823_ = lean_unsigned_to_nat(4u);
v___x_824_ = lean_nat_mul(v_size_x27_820_, v___x_823_);
v___x_825_ = lean_unsigned_to_nat(3u);
v___x_826_ = lean_nat_div(v___x_824_, v___x_825_);
lean_dec(v___x_824_);
v___x_827_ = lean_array_get_size(v_buckets_x27_822_);
v___x_828_ = lean_nat_dec_le(v___x_826_, v___x_827_);
lean_dec(v___x_826_);
if (v___x_828_ == 0)
{
lean_object* v_val_829_; lean_object* v___x_831_; 
v_val_829_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2_spec__5___redArg(v_buckets_x27_822_);
if (v_isShared_795_ == 0)
{
lean_ctor_set(v___x_794_, 1, v_val_829_);
lean_ctor_set(v___x_794_, 0, v_size_x27_820_);
v___x_831_ = v___x_794_;
goto v_reusejp_830_;
}
else
{
lean_object* v_reuseFailAlloc_832_; 
v_reuseFailAlloc_832_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_832_, 0, v_size_x27_820_);
lean_ctor_set(v_reuseFailAlloc_832_, 1, v_val_829_);
v___x_831_ = v_reuseFailAlloc_832_;
goto v_reusejp_830_;
}
v_reusejp_830_:
{
return v___x_831_;
}
}
else
{
lean_object* v___x_834_; 
if (v_isShared_795_ == 0)
{
lean_ctor_set(v___x_794_, 1, v_buckets_x27_822_);
lean_ctor_set(v___x_794_, 0, v_size_x27_820_);
v___x_834_ = v___x_794_;
goto v_reusejp_833_;
}
else
{
lean_object* v_reuseFailAlloc_835_; 
v_reuseFailAlloc_835_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_835_, 0, v_size_x27_820_);
lean_ctor_set(v_reuseFailAlloc_835_, 1, v_buckets_x27_822_);
v___x_834_ = v_reuseFailAlloc_835_;
goto v_reusejp_833_;
}
v_reusejp_833_:
{
return v___x_834_;
}
}
}
else
{
lean_object* v___x_836_; lean_object* v_buckets_x27_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_841_; 
lean_inc(v_bkt_817_);
v___x_836_ = lean_box(0);
v_buckets_x27_837_ = lean_array_uset(v_buckets_792_, v___x_816_, v___x_836_);
v___x_838_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2_spec__6___redArg(v_a_789_, v_b_790_, v_bkt_817_);
v___x_839_ = lean_array_uset(v_buckets_x27_837_, v___x_816_, v___x_838_);
if (v_isShared_795_ == 0)
{
lean_ctor_set(v___x_794_, 1, v___x_839_);
v___x_841_ = v___x_794_;
goto v_reusejp_840_;
}
else
{
lean_object* v_reuseFailAlloc_842_; 
v_reuseFailAlloc_842_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_842_, 0, v_size_791_);
lean_ctor_set(v_reuseFailAlloc_842_, 1, v___x_839_);
v___x_841_ = v_reuseFailAlloc_842_;
goto v_reusejp_840_;
}
v_reusejp_840_:
{
return v___x_841_;
}
}
}
v___jp_843_:
{
lean_object* v_fst_845_; lean_object* v_snd_846_; uint64_t v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; uint8_t v___x_850_; 
v_fst_845_ = lean_ctor_get(v_snd_797_, 0);
v_snd_846_ = lean_ctor_get(v_snd_797_, 1);
v___x_847_ = 7ULL;
v___x_848_ = lean_unsigned_to_nat(0u);
v___x_849_ = lean_array_get_size(v_fst_845_);
v___x_850_ = lean_nat_dec_lt(v___x_848_, v___x_849_);
if (v___x_850_ == 0)
{
lean_inc(v_snd_846_);
v___y_800_ = v_snd_846_;
v___y_801_ = v___y_844_;
v___y_802_ = v___x_847_;
goto v___jp_799_;
}
else
{
uint8_t v___x_851_; 
v___x_851_ = lean_nat_dec_le(v___x_849_, v___x_849_);
if (v___x_851_ == 0)
{
if (v___x_850_ == 0)
{
lean_inc(v_snd_846_);
v___y_800_ = v_snd_846_;
v___y_801_ = v___y_844_;
v___y_802_ = v___x_847_;
goto v___jp_799_;
}
else
{
size_t v___x_852_; size_t v___x_853_; uint64_t v___x_854_; 
v___x_852_ = ((size_t)0ULL);
v___x_853_ = lean_usize_of_nat(v___x_849_);
v___x_854_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__1_spec__2(v_fst_845_, v___x_852_, v___x_853_, v___x_847_);
lean_inc(v_snd_846_);
v___y_800_ = v_snd_846_;
v___y_801_ = v___y_844_;
v___y_802_ = v___x_854_;
goto v___jp_799_;
}
}
else
{
size_t v___x_855_; size_t v___x_856_; uint64_t v___x_857_; 
v___x_855_ = ((size_t)0ULL);
v___x_856_ = lean_usize_of_nat(v___x_849_);
v___x_857_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__1_spec__2(v_fst_845_, v___x_855_, v___x_856_, v___x_847_);
lean_inc(v_snd_846_);
v___y_800_ = v_snd_846_;
v___y_801_ = v___y_844_;
v___y_802_ = v___x_857_;
goto v___jp_799_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__1_spec__1___redArg(lean_object* v_a_861_, lean_object* v_x_862_){
_start:
{
if (lean_obj_tag(v_x_862_) == 0)
{
lean_object* v___x_863_; 
v___x_863_ = lean_box(0);
return v___x_863_;
}
else
{
lean_object* v_key_864_; lean_object* v_value_865_; lean_object* v_tail_866_; uint8_t v___y_868_; lean_object* v_fst_871_; lean_object* v_snd_872_; lean_object* v_fst_873_; lean_object* v_snd_874_; uint8_t v___x_875_; 
v_key_864_ = lean_ctor_get(v_x_862_, 0);
v_value_865_ = lean_ctor_get(v_x_862_, 1);
v_tail_866_ = lean_ctor_get(v_x_862_, 2);
v_fst_871_ = lean_ctor_get(v_key_864_, 0);
v_snd_872_ = lean_ctor_get(v_key_864_, 1);
v_fst_873_ = lean_ctor_get(v_a_861_, 0);
v_snd_874_ = lean_ctor_get(v_a_861_, 1);
v___x_875_ = lean_name_eq(v_fst_871_, v_fst_873_);
if (v___x_875_ == 0)
{
v___y_868_ = v___x_875_;
goto v___jp_867_;
}
else
{
lean_object* v_fst_876_; lean_object* v_snd_877_; lean_object* v_fst_878_; lean_object* v_snd_879_; lean_object* v___x_880_; lean_object* v___x_881_; uint8_t v___x_882_; 
v_fst_876_ = lean_ctor_get(v_snd_872_, 0);
v_snd_877_ = lean_ctor_get(v_snd_872_, 1);
v_fst_878_ = lean_ctor_get(v_snd_874_, 0);
v_snd_879_ = lean_ctor_get(v_snd_874_, 1);
v___x_880_ = lean_array_get_size(v_fst_876_);
v___x_881_ = lean_array_get_size(v_fst_878_);
v___x_882_ = lean_nat_dec_eq(v___x_880_, v___x_881_);
if (v___x_882_ == 0)
{
v_x_862_ = v_tail_866_;
goto _start;
}
else
{
uint8_t v___x_884_; 
v___x_884_ = l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__1_spec__1_spec__2___redArg(v_fst_876_, v_fst_878_, v___x_880_);
if (v___x_884_ == 0)
{
v_x_862_ = v_tail_866_;
goto _start;
}
else
{
uint8_t v___x_886_; 
v___x_886_ = lean_nat_dec_eq(v_snd_877_, v_snd_879_);
v___y_868_ = v___x_886_;
goto v___jp_867_;
}
}
}
v___jp_867_:
{
if (v___y_868_ == 0)
{
v_x_862_ = v_tail_866_;
goto _start;
}
else
{
lean_object* v___x_870_; 
lean_inc(v_value_865_);
v___x_870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_870_, 0, v_value_865_);
return v___x_870_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__1_spec__1___redArg___boxed(lean_object* v_a_887_, lean_object* v_x_888_){
_start:
{
lean_object* v_res_889_; 
v_res_889_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__1_spec__1___redArg(v_a_887_, v_x_888_);
lean_dec(v_x_888_);
lean_dec_ref(v_a_887_);
return v_res_889_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__1___redArg(lean_object* v_m_890_, lean_object* v_a_891_){
_start:
{
lean_object* v_buckets_892_; lean_object* v_fst_893_; lean_object* v_snd_894_; lean_object* v___x_895_; lean_object* v___y_897_; uint64_t v___y_898_; uint64_t v___y_899_; uint64_t v___y_917_; 
v_buckets_892_ = lean_ctor_get(v_m_890_, 1);
v_fst_893_ = lean_ctor_get(v_a_891_, 0);
v_snd_894_ = lean_ctor_get(v_a_891_, 1);
v___x_895_ = lean_array_get_size(v_buckets_892_);
if (lean_obj_tag(v_fst_893_) == 0)
{
uint64_t v___x_931_; 
v___x_931_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg___closed__0);
v___y_917_ = v___x_931_;
goto v___jp_916_;
}
else
{
uint64_t v_hash_932_; 
v_hash_932_ = lean_ctor_get_uint64(v_fst_893_, sizeof(void*)*2);
v___y_917_ = v_hash_932_;
goto v___jp_916_;
}
v___jp_896_:
{
uint64_t v___x_900_; uint64_t v___x_901_; uint64_t v___x_902_; uint64_t v___x_903_; uint64_t v___x_904_; uint64_t v_fold_905_; uint64_t v___x_906_; uint64_t v___x_907_; uint64_t v___x_908_; size_t v___x_909_; size_t v___x_910_; size_t v___x_911_; size_t v___x_912_; size_t v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; 
v___x_900_ = lean_uint64_of_nat(v___y_897_);
v___x_901_ = lean_uint64_mix_hash(v___y_899_, v___x_900_);
v___x_902_ = lean_uint64_mix_hash(v___y_898_, v___x_901_);
v___x_903_ = 32ULL;
v___x_904_ = lean_uint64_shift_right(v___x_902_, v___x_903_);
v_fold_905_ = lean_uint64_xor(v___x_902_, v___x_904_);
v___x_906_ = 16ULL;
v___x_907_ = lean_uint64_shift_right(v_fold_905_, v___x_906_);
v___x_908_ = lean_uint64_xor(v_fold_905_, v___x_907_);
v___x_909_ = lean_uint64_to_usize(v___x_908_);
v___x_910_ = lean_usize_of_nat(v___x_895_);
v___x_911_ = ((size_t)1ULL);
v___x_912_ = lean_usize_sub(v___x_910_, v___x_911_);
v___x_913_ = lean_usize_land(v___x_909_, v___x_912_);
v___x_914_ = lean_array_uget_borrowed(v_buckets_892_, v___x_913_);
v___x_915_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__1_spec__1___redArg(v_a_891_, v___x_914_);
return v___x_915_;
}
v___jp_916_:
{
lean_object* v_fst_918_; lean_object* v_snd_919_; uint64_t v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; uint8_t v___x_923_; 
v_fst_918_ = lean_ctor_get(v_snd_894_, 0);
v_snd_919_ = lean_ctor_get(v_snd_894_, 1);
v___x_920_ = 7ULL;
v___x_921_ = lean_unsigned_to_nat(0u);
v___x_922_ = lean_array_get_size(v_fst_918_);
v___x_923_ = lean_nat_dec_lt(v___x_921_, v___x_922_);
if (v___x_923_ == 0)
{
v___y_897_ = v_snd_919_;
v___y_898_ = v___y_917_;
v___y_899_ = v___x_920_;
goto v___jp_896_;
}
else
{
uint8_t v___x_924_; 
v___x_924_ = lean_nat_dec_le(v___x_922_, v___x_922_);
if (v___x_924_ == 0)
{
if (v___x_923_ == 0)
{
v___y_897_ = v_snd_919_;
v___y_898_ = v___y_917_;
v___y_899_ = v___x_920_;
goto v___jp_896_;
}
else
{
size_t v___x_925_; size_t v___x_926_; uint64_t v___x_927_; 
v___x_925_ = ((size_t)0ULL);
v___x_926_ = lean_usize_of_nat(v___x_922_);
v___x_927_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__1_spec__2(v_fst_918_, v___x_925_, v___x_926_, v___x_920_);
v___y_897_ = v_snd_919_;
v___y_898_ = v___y_917_;
v___y_899_ = v___x_927_;
goto v___jp_896_;
}
}
else
{
size_t v___x_928_; size_t v___x_929_; uint64_t v___x_930_; 
v___x_928_ = ((size_t)0ULL);
v___x_929_ = lean_usize_of_nat(v___x_922_);
v___x_930_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__1_spec__2(v_fst_918_, v___x_928_, v___x_929_, v___x_920_);
v___y_897_ = v_snd_919_;
v___y_898_ = v___y_917_;
v___y_899_ = v___x_930_;
goto v___jp_896_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__1___redArg___boxed(lean_object* v_m_933_, lean_object* v_a_934_){
_start:
{
lean_object* v_res_935_; 
v_res_935_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__1___redArg(v_m_933_, v_a_934_);
lean_dec_ref(v_a_934_);
lean_dec_ref(v_m_933_);
return v_res_935_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__0___redArg(size_t v_sz_936_, size_t v_i_937_, lean_object* v_bs_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_){
_start:
{
uint8_t v___x_945_; 
v___x_945_ = lean_usize_dec_lt(v_i_937_, v_sz_936_);
if (v___x_945_ == 0)
{
lean_object* v___x_946_; 
v___x_946_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_946_, 0, v_bs_938_);
return v___x_946_;
}
else
{
lean_object* v_v_947_; lean_object* v___x_948_; 
v_v_947_ = lean_array_uget_borrowed(v_bs_938_, v_i_937_);
lean_inc(v_v_947_);
v___x_948_ = l_Lean_Meta_Sym_inferType___redArg(v_v_947_, v___y_939_, v___y_940_, v___y_941_, v___y_942_, v___y_943_);
if (lean_obj_tag(v___x_948_) == 0)
{
lean_object* v_a_949_; lean_object* v___x_950_; lean_object* v_bs_x27_951_; size_t v___x_952_; size_t v___x_953_; lean_object* v___x_954_; 
v_a_949_ = lean_ctor_get(v___x_948_, 0);
lean_inc(v_a_949_);
lean_dec_ref_known(v___x_948_, 1);
v___x_950_ = lean_unsigned_to_nat(0u);
v_bs_x27_951_ = lean_array_uset(v_bs_938_, v_i_937_, v___x_950_);
v___x_952_ = ((size_t)1ULL);
v___x_953_ = lean_usize_add(v_i_937_, v___x_952_);
v___x_954_ = lean_array_uset(v_bs_x27_951_, v_i_937_, v_a_949_);
v_i_937_ = v___x_953_;
v_bs_938_ = v___x_954_;
goto _start;
}
else
{
lean_object* v_a_956_; lean_object* v___x_958_; uint8_t v_isShared_959_; uint8_t v_isSharedCheck_963_; 
lean_dec_ref(v_bs_938_);
v_a_956_ = lean_ctor_get(v___x_948_, 0);
v_isSharedCheck_963_ = !lean_is_exclusive(v___x_948_);
if (v_isSharedCheck_963_ == 0)
{
v___x_958_ = v___x_948_;
v_isShared_959_ = v_isSharedCheck_963_;
goto v_resetjp_957_;
}
else
{
lean_inc(v_a_956_);
lean_dec(v___x_948_);
v___x_958_ = lean_box(0);
v_isShared_959_ = v_isSharedCheck_963_;
goto v_resetjp_957_;
}
v_resetjp_957_:
{
lean_object* v___x_961_; 
if (v_isShared_959_ == 0)
{
v___x_961_ = v___x_958_;
goto v_reusejp_960_;
}
else
{
lean_object* v_reuseFailAlloc_962_; 
v_reuseFailAlloc_962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_962_, 0, v_a_956_);
v___x_961_ = v_reuseFailAlloc_962_;
goto v_reusejp_960_;
}
v_reusejp_960_:
{
return v___x_961_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__0___redArg___boxed(lean_object* v_sz_964_, lean_object* v_i_965_, lean_object* v_bs_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_){
_start:
{
size_t v_sz_boxed_973_; size_t v_i_boxed_974_; lean_object* v_res_975_; 
v_sz_boxed_973_ = lean_unbox_usize(v_sz_964_);
lean_dec(v_sz_964_);
v_i_boxed_974_ = lean_unbox_usize(v_i_965_);
lean_dec(v_i_965_);
v_res_975_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__0___redArg(v_sz_boxed_973_, v_i_boxed_974_, v_bs_966_, v___y_967_, v___y_968_, v___y_969_, v___y_970_, v___y_971_);
lean_dec(v___y_971_);
lean_dec_ref(v___y_970_);
lean_dec(v___y_969_);
lean_dec_ref(v___y_968_);
lean_dec(v___y_967_);
return v_res_975_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached___redArg(lean_object* v_c_976_, lean_object* v_as_977_, lean_object* v_excessArgs_978_, lean_object* v_resultType_x3f_979_, lean_object* v_a_980_, lean_object* v_a_981_, lean_object* v_a_982_, lean_object* v_a_983_, lean_object* v_a_984_, lean_object* v_a_985_, lean_object* v_a_986_){
_start:
{
lean_object* v___x_988_; size_t v_sz_989_; size_t v___x_990_; lean_object* v___x_991_; 
v___x_988_ = lean_st_ref_get(v_a_980_);
v_sz_989_ = lean_array_size(v_as_977_);
v___x_990_ = ((size_t)0ULL);
lean_inc_ref(v_as_977_);
v___x_991_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__0___redArg(v_sz_989_, v___x_990_, v_as_977_, v_a_982_, v_a_983_, v_a_984_, v_a_985_, v_a_986_);
if (lean_obj_tag(v___x_991_) == 0)
{
lean_object* v_a_992_; lean_object* v___x_994_; uint8_t v_isShared_995_; uint8_t v_isSharedCheck_1033_; 
v_a_992_ = lean_ctor_get(v___x_991_, 0);
v_isSharedCheck_1033_ = !lean_is_exclusive(v___x_991_);
if (v_isSharedCheck_1033_ == 0)
{
v___x_994_ = v___x_991_;
v_isShared_995_ = v_isSharedCheck_1033_;
goto v_resetjp_993_;
}
else
{
lean_inc(v_a_992_);
lean_dec(v___x_991_);
v___x_994_ = lean_box(0);
v_isShared_995_ = v_isSharedCheck_1033_;
goto v_resetjp_993_;
}
v_resetjp_993_:
{
lean_object* v_latticeBackwardRuleCache_996_; lean_object* v_applyLemma_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; 
v_latticeBackwardRuleCache_996_ = lean_ctor_get(v___x_988_, 2);
lean_inc_ref(v_latticeBackwardRuleCache_996_);
lean_dec(v___x_988_);
v_applyLemma_997_ = lean_ctor_get(v_c_976_, 1);
v___x_998_ = lean_array_get_size(v_excessArgs_978_);
v___x_999_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_999_, 0, v_a_992_);
lean_ctor_set(v___x_999_, 1, v___x_998_);
lean_inc(v_applyLemma_997_);
v___x_1000_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1000_, 0, v_applyLemma_997_);
lean_ctor_set(v___x_1000_, 1, v___x_999_);
v___x_1001_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__1___redArg(v_latticeBackwardRuleCache_996_, v___x_1000_);
lean_dec_ref(v_latticeBackwardRuleCache_996_);
if (lean_obj_tag(v___x_1001_) == 1)
{
lean_object* v_val_1002_; lean_object* v___x_1004_; 
lean_dec_ref_known(v___x_1000_, 2);
lean_dec(v_resultType_x3f_979_);
lean_dec_ref(v_excessArgs_978_);
lean_dec_ref(v_as_977_);
lean_dec_ref(v_c_976_);
v_val_1002_ = lean_ctor_get(v___x_1001_, 0);
lean_inc(v_val_1002_);
lean_dec_ref_known(v___x_1001_, 1);
if (v_isShared_995_ == 0)
{
lean_ctor_set(v___x_994_, 0, v_val_1002_);
v___x_1004_ = v___x_994_;
goto v_reusejp_1003_;
}
else
{
lean_object* v_reuseFailAlloc_1005_; 
v_reuseFailAlloc_1005_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1005_, 0, v_val_1002_);
v___x_1004_ = v_reuseFailAlloc_1005_;
goto v_reusejp_1003_;
}
v_reusejp_1003_:
{
return v___x_1004_;
}
}
else
{
lean_object* v___x_1006_; 
lean_dec(v___x_1001_);
lean_del_object(v___x_994_);
v___x_1006_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeSplit_mkBackwardRuleForLattice(v_c_976_, v_as_977_, v_excessArgs_978_, v_resultType_x3f_979_, v_a_983_, v_a_984_, v_a_985_, v_a_986_);
if (lean_obj_tag(v___x_1006_) == 0)
{
lean_object* v_a_1007_; lean_object* v___x_1009_; uint8_t v_isShared_1010_; uint8_t v_isSharedCheck_1032_; 
v_a_1007_ = lean_ctor_get(v___x_1006_, 0);
v_isSharedCheck_1032_ = !lean_is_exclusive(v___x_1006_);
if (v_isSharedCheck_1032_ == 0)
{
v___x_1009_ = v___x_1006_;
v_isShared_1010_ = v_isSharedCheck_1032_;
goto v_resetjp_1008_;
}
else
{
lean_inc(v_a_1007_);
lean_dec(v___x_1006_);
v___x_1009_ = lean_box(0);
v_isShared_1010_ = v_isSharedCheck_1032_;
goto v_resetjp_1008_;
}
v_resetjp_1008_:
{
lean_object* v___x_1011_; lean_object* v_specBackwardRuleCache_1012_; lean_object* v_splitBackwardRuleCache_1013_; lean_object* v_latticeBackwardRuleCache_1014_; lean_object* v_invariants_1015_; lean_object* v_vcs_1016_; lean_object* v_simpState_1017_; lean_object* v_fuel_1018_; lean_object* v_inlineHandledInvariants_1019_; lean_object* v___x_1021_; uint8_t v_isShared_1022_; uint8_t v_isSharedCheck_1031_; 
v___x_1011_ = lean_st_ref_take(v_a_980_);
v_specBackwardRuleCache_1012_ = lean_ctor_get(v___x_1011_, 0);
v_splitBackwardRuleCache_1013_ = lean_ctor_get(v___x_1011_, 1);
v_latticeBackwardRuleCache_1014_ = lean_ctor_get(v___x_1011_, 2);
v_invariants_1015_ = lean_ctor_get(v___x_1011_, 3);
v_vcs_1016_ = lean_ctor_get(v___x_1011_, 4);
v_simpState_1017_ = lean_ctor_get(v___x_1011_, 5);
v_fuel_1018_ = lean_ctor_get(v___x_1011_, 6);
v_inlineHandledInvariants_1019_ = lean_ctor_get(v___x_1011_, 7);
v_isSharedCheck_1031_ = !lean_is_exclusive(v___x_1011_);
if (v_isSharedCheck_1031_ == 0)
{
v___x_1021_ = v___x_1011_;
v_isShared_1022_ = v_isSharedCheck_1031_;
goto v_resetjp_1020_;
}
else
{
lean_inc(v_inlineHandledInvariants_1019_);
lean_inc(v_fuel_1018_);
lean_inc(v_simpState_1017_);
lean_inc(v_vcs_1016_);
lean_inc(v_invariants_1015_);
lean_inc(v_latticeBackwardRuleCache_1014_);
lean_inc(v_splitBackwardRuleCache_1013_);
lean_inc(v_specBackwardRuleCache_1012_);
lean_dec(v___x_1011_);
v___x_1021_ = lean_box(0);
v_isShared_1022_ = v_isSharedCheck_1031_;
goto v_resetjp_1020_;
}
v_resetjp_1020_:
{
lean_object* v___x_1023_; lean_object* v___x_1025_; 
lean_inc(v_a_1007_);
v___x_1023_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2___redArg(v_latticeBackwardRuleCache_1014_, v___x_1000_, v_a_1007_);
if (v_isShared_1022_ == 0)
{
lean_ctor_set(v___x_1021_, 2, v___x_1023_);
v___x_1025_ = v___x_1021_;
goto v_reusejp_1024_;
}
else
{
lean_object* v_reuseFailAlloc_1030_; 
v_reuseFailAlloc_1030_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_1030_, 0, v_specBackwardRuleCache_1012_);
lean_ctor_set(v_reuseFailAlloc_1030_, 1, v_splitBackwardRuleCache_1013_);
lean_ctor_set(v_reuseFailAlloc_1030_, 2, v___x_1023_);
lean_ctor_set(v_reuseFailAlloc_1030_, 3, v_invariants_1015_);
lean_ctor_set(v_reuseFailAlloc_1030_, 4, v_vcs_1016_);
lean_ctor_set(v_reuseFailAlloc_1030_, 5, v_simpState_1017_);
lean_ctor_set(v_reuseFailAlloc_1030_, 6, v_fuel_1018_);
lean_ctor_set(v_reuseFailAlloc_1030_, 7, v_inlineHandledInvariants_1019_);
v___x_1025_ = v_reuseFailAlloc_1030_;
goto v_reusejp_1024_;
}
v_reusejp_1024_:
{
lean_object* v___x_1026_; lean_object* v___x_1028_; 
v___x_1026_ = lean_st_ref_set(v_a_980_, v___x_1025_);
if (v_isShared_1010_ == 0)
{
v___x_1028_ = v___x_1009_;
goto v_reusejp_1027_;
}
else
{
lean_object* v_reuseFailAlloc_1029_; 
v_reuseFailAlloc_1029_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1029_, 0, v_a_1007_);
v___x_1028_ = v_reuseFailAlloc_1029_;
goto v_reusejp_1027_;
}
v_reusejp_1027_:
{
return v___x_1028_;
}
}
}
}
}
else
{
lean_dec_ref_known(v___x_1000_, 2);
return v___x_1006_;
}
}
}
}
else
{
lean_object* v_a_1034_; lean_object* v___x_1036_; uint8_t v_isShared_1037_; uint8_t v_isSharedCheck_1041_; 
lean_dec(v___x_988_);
lean_dec(v_resultType_x3f_979_);
lean_dec_ref(v_excessArgs_978_);
lean_dec_ref(v_as_977_);
lean_dec_ref(v_c_976_);
v_a_1034_ = lean_ctor_get(v___x_991_, 0);
v_isSharedCheck_1041_ = !lean_is_exclusive(v___x_991_);
if (v_isSharedCheck_1041_ == 0)
{
v___x_1036_ = v___x_991_;
v_isShared_1037_ = v_isSharedCheck_1041_;
goto v_resetjp_1035_;
}
else
{
lean_inc(v_a_1034_);
lean_dec(v___x_991_);
v___x_1036_ = lean_box(0);
v_isShared_1037_ = v_isSharedCheck_1041_;
goto v_resetjp_1035_;
}
v_resetjp_1035_:
{
lean_object* v___x_1039_; 
if (v_isShared_1037_ == 0)
{
v___x_1039_ = v___x_1036_;
goto v_reusejp_1038_;
}
else
{
lean_object* v_reuseFailAlloc_1040_; 
v_reuseFailAlloc_1040_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1040_, 0, v_a_1034_);
v___x_1039_ = v_reuseFailAlloc_1040_;
goto v_reusejp_1038_;
}
v_reusejp_1038_:
{
return v___x_1039_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached___redArg___boxed(lean_object* v_c_1042_, lean_object* v_as_1043_, lean_object* v_excessArgs_1044_, lean_object* v_resultType_x3f_1045_, lean_object* v_a_1046_, lean_object* v_a_1047_, lean_object* v_a_1048_, lean_object* v_a_1049_, lean_object* v_a_1050_, lean_object* v_a_1051_, lean_object* v_a_1052_, lean_object* v_a_1053_){
_start:
{
lean_object* v_res_1054_; 
v_res_1054_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached___redArg(v_c_1042_, v_as_1043_, v_excessArgs_1044_, v_resultType_x3f_1045_, v_a_1046_, v_a_1047_, v_a_1048_, v_a_1049_, v_a_1050_, v_a_1051_, v_a_1052_);
lean_dec(v_a_1052_);
lean_dec_ref(v_a_1051_);
lean_dec(v_a_1050_);
lean_dec_ref(v_a_1049_);
lean_dec(v_a_1048_);
lean_dec_ref(v_a_1047_);
lean_dec(v_a_1046_);
return v_res_1054_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached(lean_object* v_c_1055_, lean_object* v_as_1056_, lean_object* v_excessArgs_1057_, lean_object* v_resultType_x3f_1058_, lean_object* v_a_1059_, lean_object* v_a_1060_, lean_object* v_a_1061_, lean_object* v_a_1062_, lean_object* v_a_1063_, lean_object* v_a_1064_, lean_object* v_a_1065_, lean_object* v_a_1066_, lean_object* v_a_1067_, lean_object* v_a_1068_, lean_object* v_a_1069_){
_start:
{
lean_object* v___x_1071_; 
v___x_1071_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached___redArg(v_c_1055_, v_as_1056_, v_excessArgs_1057_, v_resultType_x3f_1058_, v_a_1060_, v_a_1064_, v_a_1065_, v_a_1066_, v_a_1067_, v_a_1068_, v_a_1069_);
return v___x_1071_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached___boxed(lean_object* v_c_1072_, lean_object* v_as_1073_, lean_object* v_excessArgs_1074_, lean_object* v_resultType_x3f_1075_, lean_object* v_a_1076_, lean_object* v_a_1077_, lean_object* v_a_1078_, lean_object* v_a_1079_, lean_object* v_a_1080_, lean_object* v_a_1081_, lean_object* v_a_1082_, lean_object* v_a_1083_, lean_object* v_a_1084_, lean_object* v_a_1085_, lean_object* v_a_1086_, lean_object* v_a_1087_){
_start:
{
lean_object* v_res_1088_; 
v_res_1088_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached(v_c_1072_, v_as_1073_, v_excessArgs_1074_, v_resultType_x3f_1075_, v_a_1076_, v_a_1077_, v_a_1078_, v_a_1079_, v_a_1080_, v_a_1081_, v_a_1082_, v_a_1083_, v_a_1084_, v_a_1085_, v_a_1086_);
lean_dec(v_a_1086_);
lean_dec_ref(v_a_1085_);
lean_dec(v_a_1084_);
lean_dec_ref(v_a_1083_);
lean_dec(v_a_1082_);
lean_dec_ref(v_a_1081_);
lean_dec(v_a_1080_);
lean_dec_ref(v_a_1079_);
lean_dec(v_a_1078_);
lean_dec(v_a_1077_);
lean_dec_ref(v_a_1076_);
return v_res_1088_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__0(size_t v_sz_1089_, size_t v_i_1090_, lean_object* v_bs_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_){
_start:
{
lean_object* v___x_1099_; 
v___x_1099_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__0___redArg(v_sz_1089_, v_i_1090_, v_bs_1091_, v___y_1093_, v___y_1094_, v___y_1095_, v___y_1096_, v___y_1097_);
return v___x_1099_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__0___boxed(lean_object* v_sz_1100_, lean_object* v_i_1101_, lean_object* v_bs_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_){
_start:
{
size_t v_sz_boxed_1110_; size_t v_i_boxed_1111_; lean_object* v_res_1112_; 
v_sz_boxed_1110_ = lean_unbox_usize(v_sz_1100_);
lean_dec(v_sz_1100_);
v_i_boxed_1111_ = lean_unbox_usize(v_i_1101_);
lean_dec(v_i_1101_);
v_res_1112_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__0(v_sz_boxed_1110_, v_i_boxed_1111_, v_bs_1102_, v___y_1103_, v___y_1104_, v___y_1105_, v___y_1106_, v___y_1107_, v___y_1108_);
lean_dec(v___y_1108_);
lean_dec_ref(v___y_1107_);
lean_dec(v___y_1106_);
lean_dec_ref(v___y_1105_);
lean_dec(v___y_1104_);
lean_dec_ref(v___y_1103_);
return v_res_1112_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__1(lean_object* v_00_u03b2_1113_, lean_object* v_m_1114_, lean_object* v_a_1115_){
_start:
{
lean_object* v___x_1116_; 
v___x_1116_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__1___redArg(v_m_1114_, v_a_1115_);
return v___x_1116_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__1___boxed(lean_object* v_00_u03b2_1117_, lean_object* v_m_1118_, lean_object* v_a_1119_){
_start:
{
lean_object* v_res_1120_; 
v_res_1120_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__1(v_00_u03b2_1117_, v_m_1118_, v_a_1119_);
lean_dec_ref(v_a_1119_);
lean_dec_ref(v_m_1118_);
return v_res_1120_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2(lean_object* v_00_u03b2_1121_, lean_object* v_m_1122_, lean_object* v_a_1123_, lean_object* v_b_1124_){
_start:
{
lean_object* v___x_1125_; 
v___x_1125_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2___redArg(v_m_1122_, v_a_1123_, v_b_1124_);
return v___x_1125_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__1_spec__1(lean_object* v_00_u03b2_1126_, lean_object* v_a_1127_, lean_object* v_x_1128_){
_start:
{
lean_object* v___x_1129_; 
v___x_1129_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__1_spec__1___redArg(v_a_1127_, v_x_1128_);
return v___x_1129_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__1_spec__1___boxed(lean_object* v_00_u03b2_1130_, lean_object* v_a_1131_, lean_object* v_x_1132_){
_start:
{
lean_object* v_res_1133_; 
v_res_1133_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__1_spec__1(v_00_u03b2_1130_, v_a_1131_, v_x_1132_);
lean_dec(v_x_1132_);
lean_dec_ref(v_a_1131_);
return v_res_1133_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2_spec__4(lean_object* v_00_u03b2_1134_, lean_object* v_a_1135_, lean_object* v_x_1136_){
_start:
{
uint8_t v___x_1137_; 
v___x_1137_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2_spec__4___redArg(v_a_1135_, v_x_1136_);
return v___x_1137_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2_spec__4___boxed(lean_object* v_00_u03b2_1138_, lean_object* v_a_1139_, lean_object* v_x_1140_){
_start:
{
uint8_t v_res_1141_; lean_object* v_r_1142_; 
v_res_1141_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2_spec__4(v_00_u03b2_1138_, v_a_1139_, v_x_1140_);
lean_dec(v_x_1140_);
lean_dec_ref(v_a_1139_);
v_r_1142_ = lean_box(v_res_1141_);
return v_r_1142_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2_spec__5(lean_object* v_00_u03b2_1143_, lean_object* v_data_1144_){
_start:
{
lean_object* v___x_1145_; 
v___x_1145_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2_spec__5___redArg(v_data_1144_);
return v___x_1145_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2_spec__6(lean_object* v_00_u03b2_1146_, lean_object* v_a_1147_, lean_object* v_b_1148_, lean_object* v_x_1149_){
_start:
{
lean_object* v___x_1150_; 
v___x_1150_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2_spec__6___redArg(v_a_1147_, v_b_1148_, v_x_1149_);
return v___x_1150_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__1_spec__1_spec__2(lean_object* v_xs_1151_, lean_object* v_ys_1152_, lean_object* v_hsz_1153_, lean_object* v_x_1154_, lean_object* v_x_1155_){
_start:
{
uint8_t v___x_1156_; 
v___x_1156_ = l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__1_spec__1_spec__2___redArg(v_xs_1151_, v_ys_1152_, v_x_1154_);
return v___x_1156_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__1_spec__1_spec__2___boxed(lean_object* v_xs_1157_, lean_object* v_ys_1158_, lean_object* v_hsz_1159_, lean_object* v_x_1160_, lean_object* v_x_1161_){
_start:
{
uint8_t v_res_1162_; lean_object* v_r_1163_; 
v_res_1162_ = l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__1_spec__1_spec__2(v_xs_1157_, v_ys_1158_, v_hsz_1159_, v_x_1160_, v_x_1161_);
lean_dec_ref(v_ys_1158_);
lean_dec_ref(v_xs_1157_);
v_r_1163_ = lean_box(v_res_1162_);
return v_r_1163_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2_spec__5_spec__7(lean_object* v_00_u03b2_1164_, lean_object* v_i_1165_, lean_object* v_source_1166_, lean_object* v_target_1167_){
_start:
{
lean_object* v___x_1168_; 
v___x_1168_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2_spec__5_spec__7___redArg(v_i_1165_, v_source_1166_, v_target_1167_);
return v___x_1168_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2_spec__5_spec__7_spec__8(lean_object* v_00_u03b2_1169_, lean_object* v_x_1170_, lean_object* v_x_1171_){
_start:
{
lean_object* v___x_1172_; 
v___x_1172_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2_spec__5_spec__7_spec__8___redArg(v_x_1170_, v_x_1171_);
return v___x_1172_;
}
}
lean_object* runtime_initialize_Lean_Elab_Tactic_Do_VCGen_Split(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Context(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_RuleConstruction(uint8_t builtin);
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
