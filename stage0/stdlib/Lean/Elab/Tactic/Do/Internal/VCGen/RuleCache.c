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
lean_object* l_Lean_Meta_Sym_inferType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
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
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
uint64_t lean_usize_to_uint64(size_t);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeSplit_mkBackwardRuleForLattice(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_BackwardRule_shareCommon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForSplitCached___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForSplitCached___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForSplitCached(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForSplitCached___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__0(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint64_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2_spec__3(lean_object*, size_t, size_t, uint64_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__3_spec__6_spec__8_spec__9___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__3_spec__6_spec__8___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__3_spec__6___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__3_spec__7___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__3_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__3_spec__5___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__3_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__3_spec__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__3_spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__3_spec__6_spec__8(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__3_spec__6_spec__8_spec__9(lean_object*, lean_object*, lean_object*);
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
v___x_416_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_WPInfo_instWP(v_info_398_);
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
lean_object* v_a_426_; lean_object* v___x_428_; uint8_t v_isShared_429_; uint8_t v_isSharedCheck_483_; 
v_a_426_ = lean_ctor_get(v___x_425_, 0);
v_isSharedCheck_483_ = !lean_is_exclusive(v___x_425_);
if (v_isSharedCheck_483_ == 0)
{
v___x_428_ = v___x_425_;
v_isShared_429_ = v_isSharedCheck_483_;
goto v_resetjp_427_;
}
else
{
lean_inc(v_a_426_);
lean_dec(v___x_425_);
v___x_428_ = lean_box(0);
v_isShared_429_ = v_isSharedCheck_483_;
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
lean_object* v_val_435_; lean_object* v___x_437_; uint8_t v_isShared_438_; uint8_t v_isSharedCheck_478_; 
lean_del_object(v___x_428_);
v_val_435_ = lean_ctor_get(v_val_434_, 0);
v_isSharedCheck_478_ = !lean_is_exclusive(v_val_434_);
if (v_isSharedCheck_478_ == 0)
{
v___x_437_ = v_val_434_;
v_isShared_438_ = v_isSharedCheck_478_;
goto v_resetjp_436_;
}
else
{
lean_inc(v_val_435_);
lean_dec(v_val_434_);
v___x_437_ = lean_box(0);
v_isShared_438_ = v_isSharedCheck_478_;
goto v_resetjp_436_;
}
v_resetjp_436_:
{
lean_object* v___x_439_; 
v___x_439_ = l_Lean_Meta_Sym_BackwardRule_shareCommon(v_val_435_, v_a_404_, v_a_405_, v_a_406_, v_a_407_, v_a_408_, v_a_409_);
if (lean_obj_tag(v___x_439_) == 0)
{
lean_object* v_a_440_; lean_object* v___x_442_; uint8_t v_isShared_443_; uint8_t v_isSharedCheck_469_; 
v_a_440_ = lean_ctor_get(v___x_439_, 0);
v_isSharedCheck_469_ = !lean_is_exclusive(v___x_439_);
if (v_isSharedCheck_469_ == 0)
{
v___x_442_ = v___x_439_;
v_isShared_443_ = v_isSharedCheck_469_;
goto v_resetjp_441_;
}
else
{
lean_inc(v_a_440_);
lean_dec(v___x_439_);
v___x_442_ = lean_box(0);
v_isShared_443_ = v_isSharedCheck_469_;
goto v_resetjp_441_;
}
v_resetjp_441_:
{
lean_object* v___x_444_; lean_object* v_specBackwardRuleCache_445_; lean_object* v_splitBackwardRuleCache_446_; lean_object* v_latticeBackwardRuleCache_447_; lean_object* v_frameDB_x3f_448_; lean_object* v_invariants_449_; lean_object* v_vcs_450_; lean_object* v_simpState_451_; lean_object* v_fuel_452_; lean_object* v_inlineHandledInvariants_453_; lean_object* v___x_455_; uint8_t v_isShared_456_; uint8_t v_isSharedCheck_468_; 
v___x_444_ = lean_st_ref_take(v_a_400_);
v_specBackwardRuleCache_445_ = lean_ctor_get(v___x_444_, 0);
v_splitBackwardRuleCache_446_ = lean_ctor_get(v___x_444_, 1);
v_latticeBackwardRuleCache_447_ = lean_ctor_get(v___x_444_, 2);
v_frameDB_x3f_448_ = lean_ctor_get(v___x_444_, 3);
v_invariants_449_ = lean_ctor_get(v___x_444_, 4);
v_vcs_450_ = lean_ctor_get(v___x_444_, 5);
v_simpState_451_ = lean_ctor_get(v___x_444_, 6);
v_fuel_452_ = lean_ctor_get(v___x_444_, 7);
v_inlineHandledInvariants_453_ = lean_ctor_get(v___x_444_, 8);
v_isSharedCheck_468_ = !lean_is_exclusive(v___x_444_);
if (v_isSharedCheck_468_ == 0)
{
v___x_455_ = v___x_444_;
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
lean_inc(v_frameDB_x3f_448_);
lean_inc(v_latticeBackwardRuleCache_447_);
lean_inc(v_splitBackwardRuleCache_446_);
lean_inc(v_specBackwardRuleCache_445_);
lean_dec(v___x_444_);
v___x_455_ = lean_box(0);
v_isShared_456_ = v_isSharedCheck_468_;
goto v_resetjp_454_;
}
v_resetjp_454_:
{
lean_object* v___x_458_; 
lean_inc(v_a_440_);
if (v_isShared_438_ == 0)
{
lean_ctor_set(v___x_437_, 0, v_a_440_);
v___x_458_ = v___x_437_;
goto v_reusejp_457_;
}
else
{
lean_object* v_reuseFailAlloc_467_; 
v_reuseFailAlloc_467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_467_, 0, v_a_440_);
v___x_458_ = v_reuseFailAlloc_467_;
goto v_reusejp_457_;
}
v_reusejp_457_:
{
lean_object* v___x_459_; lean_object* v___x_461_; 
v___x_459_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2___redArg(v_specBackwardRuleCache_445_, v_key_419_, v_a_440_);
if (v_isShared_456_ == 0)
{
lean_ctor_set(v___x_455_, 0, v___x_459_);
v___x_461_ = v___x_455_;
goto v_reusejp_460_;
}
else
{
lean_object* v_reuseFailAlloc_466_; 
v_reuseFailAlloc_466_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_466_, 0, v___x_459_);
lean_ctor_set(v_reuseFailAlloc_466_, 1, v_splitBackwardRuleCache_446_);
lean_ctor_set(v_reuseFailAlloc_466_, 2, v_latticeBackwardRuleCache_447_);
lean_ctor_set(v_reuseFailAlloc_466_, 3, v_frameDB_x3f_448_);
lean_ctor_set(v_reuseFailAlloc_466_, 4, v_invariants_449_);
lean_ctor_set(v_reuseFailAlloc_466_, 5, v_vcs_450_);
lean_ctor_set(v_reuseFailAlloc_466_, 6, v_simpState_451_);
lean_ctor_set(v_reuseFailAlloc_466_, 7, v_fuel_452_);
lean_ctor_set(v_reuseFailAlloc_466_, 8, v_inlineHandledInvariants_453_);
v___x_461_ = v_reuseFailAlloc_466_;
goto v_reusejp_460_;
}
v_reusejp_460_:
{
lean_object* v___x_462_; lean_object* v___x_464_; 
v___x_462_ = lean_st_ref_set(v_a_400_, v___x_461_);
if (v_isShared_443_ == 0)
{
lean_ctor_set(v___x_442_, 0, v___x_458_);
v___x_464_ = v___x_442_;
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
lean_del_object(v___x_437_);
lean_dec_ref_known(v_key_419_, 2);
v_a_470_ = lean_ctor_get(v___x_439_, 0);
v_isSharedCheck_477_ = !lean_is_exclusive(v___x_439_);
if (v_isSharedCheck_477_ == 0)
{
v___x_472_ = v___x_439_;
v_isShared_473_ = v_isSharedCheck_477_;
goto v_resetjp_471_;
}
else
{
lean_inc(v_a_470_);
lean_dec(v___x_439_);
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
lean_dec(v_val_434_);
lean_dec_ref_known(v_key_419_, 2);
v___x_479_ = lean_box(0);
if (v_isShared_429_ == 0)
{
lean_ctor_set(v___x_428_, 0, v___x_479_);
v___x_481_ = v___x_428_;
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
lean_dec_ref_known(v_key_419_, 2);
v_a_484_ = lean_ctor_get(v___x_425_, 0);
v_isSharedCheck_491_ = !lean_is_exclusive(v___x_425_);
if (v_isSharedCheck_491_ == 0)
{
v___x_486_ = v___x_425_;
v_isShared_487_ = v_isSharedCheck_491_;
goto v_resetjp_485_;
}
else
{
lean_inc(v_a_484_);
lean_dec(v___x_425_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached___boxed(lean_object* v_specThm_492_, lean_object* v_info_493_, lean_object* v_a_494_, lean_object* v_a_495_, lean_object* v_a_496_, lean_object* v_a_497_, lean_object* v_a_498_, lean_object* v_a_499_, lean_object* v_a_500_, lean_object* v_a_501_, lean_object* v_a_502_, lean_object* v_a_503_, lean_object* v_a_504_, lean_object* v_a_505_){
_start:
{
lean_object* v_res_506_; 
v_res_506_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached(v_specThm_492_, v_info_493_, v_a_494_, v_a_495_, v_a_496_, v_a_497_, v_a_498_, v_a_499_, v_a_500_, v_a_501_, v_a_502_, v_a_503_, v_a_504_);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0(lean_object* v_00_u03b2_507_, lean_object* v_m_508_, lean_object* v_a_509_){
_start:
{
lean_object* v___x_510_; 
v___x_510_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg(v_m_508_, v_a_509_);
return v___x_510_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___boxed(lean_object* v_00_u03b2_511_, lean_object* v_m_512_, lean_object* v_a_513_){
_start:
{
lean_object* v_res_514_; 
v_res_514_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0(v_00_u03b2_511_, v_m_512_, v_a_513_);
lean_dec_ref(v_a_513_);
lean_dec_ref(v_m_512_);
return v_res_514_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2(lean_object* v_00_u03b2_515_, lean_object* v_m_516_, lean_object* v_a_517_, lean_object* v_b_518_){
_start:
{
lean_object* v___x_519_; 
v___x_519_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2___redArg(v_m_516_, v_a_517_, v_b_518_);
return v___x_519_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0_spec__0(lean_object* v_00_u03b2_520_, lean_object* v_a_521_, lean_object* v_x_522_){
_start:
{
lean_object* v___x_523_; 
v___x_523_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0_spec__0___redArg(v_a_521_, v_x_522_);
return v___x_523_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0_spec__0___boxed(lean_object* v_00_u03b2_524_, lean_object* v_a_525_, lean_object* v_x_526_){
_start:
{
lean_object* v_res_527_; 
v_res_527_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0_spec__0(v_00_u03b2_524_, v_a_525_, v_x_526_);
lean_dec(v_x_526_);
lean_dec_ref(v_a_525_);
return v_res_527_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__3(lean_object* v_00_u03b2_528_, lean_object* v_a_529_, lean_object* v_x_530_){
_start:
{
uint8_t v___x_531_; 
v___x_531_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__3___redArg(v_a_529_, v_x_530_);
return v___x_531_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__3___boxed(lean_object* v_00_u03b2_532_, lean_object* v_a_533_, lean_object* v_x_534_){
_start:
{
uint8_t v_res_535_; lean_object* v_r_536_; 
v_res_535_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__3(v_00_u03b2_532_, v_a_533_, v_x_534_);
lean_dec(v_x_534_);
lean_dec_ref(v_a_533_);
v_r_536_ = lean_box(v_res_535_);
return v_r_536_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__4(lean_object* v_00_u03b2_537_, lean_object* v_data_538_){
_start:
{
lean_object* v___x_539_; 
v___x_539_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__4___redArg(v_data_538_);
return v___x_539_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__5(lean_object* v_00_u03b2_540_, lean_object* v_a_541_, lean_object* v_b_542_, lean_object* v_x_543_){
_start:
{
lean_object* v___x_544_; 
v___x_544_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__5___redArg(v_a_541_, v_b_542_, v_x_543_);
return v___x_544_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_545_, lean_object* v_i_546_, lean_object* v_source_547_, lean_object* v_target_548_){
_start:
{
lean_object* v___x_549_; 
v___x_549_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__4_spec__5___redArg(v_i_546_, v_source_547_, v_target_548_);
return v___x_549_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__4_spec__5_spec__6(lean_object* v_00_u03b2_550_, lean_object* v_x_551_, lean_object* v_x_552_){
_start:
{
lean_object* v___x_553_; 
v___x_553_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__4_spec__5_spec__6___redArg(v_x_551_, v_x_552_);
return v___x_553_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForSplitCached___redArg(lean_object* v_splitInfo_560_, lean_object* v_info_561_, lean_object* v_a_562_, lean_object* v_a_563_, lean_object* v_a_564_, lean_object* v_a_565_, lean_object* v_a_566_, lean_object* v_a_567_, lean_object* v_a_568_){
_start:
{
lean_object* v___y_571_; 
switch(lean_obj_tag(v_splitInfo_560_))
{
case 0:
{
lean_object* v___x_618_; 
v___x_618_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForSplitCached___redArg___closed__1));
v___y_571_ = v___x_618_;
goto v___jp_570_;
}
case 1:
{
lean_object* v___x_619_; 
v___x_619_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForSplitCached___redArg___closed__3));
v___y_571_ = v___x_619_;
goto v___jp_570_;
}
default: 
{
lean_object* v_matcherApp_620_; lean_object* v_matcherName_621_; 
v_matcherApp_620_ = lean_ctor_get(v_splitInfo_560_, 0);
v_matcherName_621_ = lean_ctor_get(v_matcherApp_620_, 1);
lean_inc(v_matcherName_621_);
v___y_571_ = v_matcherName_621_;
goto v___jp_570_;
}
}
v___jp_570_:
{
lean_object* v___x_572_; lean_object* v_excessArgs_573_; lean_object* v_splitBackwardRuleCache_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v_key_578_; lean_object* v___x_579_; 
v___x_572_ = lean_st_ref_get(v_a_562_);
v_excessArgs_573_ = lean_ctor_get(v_info_561_, 2);
v_splitBackwardRuleCache_574_ = lean_ctor_get(v___x_572_, 1);
lean_inc_ref(v_splitBackwardRuleCache_574_);
lean_dec(v___x_572_);
v___x_575_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_WPInfo_instWP(v_info_561_);
v___x_576_ = lean_array_get_size(v_excessArgs_573_);
v___x_577_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_577_, 0, v___x_575_);
lean_ctor_set(v___x_577_, 1, v___x_576_);
v_key_578_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_key_578_, 0, v___y_571_);
lean_ctor_set(v_key_578_, 1, v___x_577_);
v___x_579_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg(v_splitBackwardRuleCache_574_, v_key_578_);
lean_dec_ref(v_splitBackwardRuleCache_574_);
if (lean_obj_tag(v___x_579_) == 1)
{
lean_object* v_val_580_; lean_object* v___x_582_; uint8_t v_isShared_583_; uint8_t v_isSharedCheck_587_; 
lean_dec_ref_known(v_key_578_, 2);
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
v___x_588_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForSplit(v_splitInfo_560_, v_info_561_, v_a_565_, v_a_566_, v_a_567_, v_a_568_);
if (lean_obj_tag(v___x_588_) == 0)
{
lean_object* v_a_589_; lean_object* v___x_590_; 
v_a_589_ = lean_ctor_get(v___x_588_, 0);
lean_inc(v_a_589_);
lean_dec_ref_known(v___x_588_, 1);
v___x_590_ = l_Lean_Meta_Sym_BackwardRule_shareCommon(v_a_589_, v_a_563_, v_a_564_, v_a_565_, v_a_566_, v_a_567_, v_a_568_);
if (lean_obj_tag(v___x_590_) == 0)
{
lean_object* v_a_591_; lean_object* v___x_593_; uint8_t v_isShared_594_; uint8_t v_isSharedCheck_617_; 
v_a_591_ = lean_ctor_get(v___x_590_, 0);
v_isSharedCheck_617_ = !lean_is_exclusive(v___x_590_);
if (v_isSharedCheck_617_ == 0)
{
v___x_593_ = v___x_590_;
v_isShared_594_ = v_isSharedCheck_617_;
goto v_resetjp_592_;
}
else
{
lean_inc(v_a_591_);
lean_dec(v___x_590_);
v___x_593_ = lean_box(0);
v_isShared_594_ = v_isSharedCheck_617_;
goto v_resetjp_592_;
}
v_resetjp_592_:
{
lean_object* v___x_595_; lean_object* v_specBackwardRuleCache_596_; lean_object* v_splitBackwardRuleCache_597_; lean_object* v_latticeBackwardRuleCache_598_; lean_object* v_frameDB_x3f_599_; lean_object* v_invariants_600_; lean_object* v_vcs_601_; lean_object* v_simpState_602_; lean_object* v_fuel_603_; lean_object* v_inlineHandledInvariants_604_; lean_object* v___x_606_; uint8_t v_isShared_607_; uint8_t v_isSharedCheck_616_; 
v___x_595_ = lean_st_ref_take(v_a_562_);
v_specBackwardRuleCache_596_ = lean_ctor_get(v___x_595_, 0);
v_splitBackwardRuleCache_597_ = lean_ctor_get(v___x_595_, 1);
v_latticeBackwardRuleCache_598_ = lean_ctor_get(v___x_595_, 2);
v_frameDB_x3f_599_ = lean_ctor_get(v___x_595_, 3);
v_invariants_600_ = lean_ctor_get(v___x_595_, 4);
v_vcs_601_ = lean_ctor_get(v___x_595_, 5);
v_simpState_602_ = lean_ctor_get(v___x_595_, 6);
v_fuel_603_ = lean_ctor_get(v___x_595_, 7);
v_inlineHandledInvariants_604_ = lean_ctor_get(v___x_595_, 8);
v_isSharedCheck_616_ = !lean_is_exclusive(v___x_595_);
if (v_isSharedCheck_616_ == 0)
{
v___x_606_ = v___x_595_;
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
lean_inc(v_frameDB_x3f_599_);
lean_inc(v_latticeBackwardRuleCache_598_);
lean_inc(v_splitBackwardRuleCache_597_);
lean_inc(v_specBackwardRuleCache_596_);
lean_dec(v___x_595_);
v___x_606_ = lean_box(0);
v_isShared_607_ = v_isSharedCheck_616_;
goto v_resetjp_605_;
}
v_resetjp_605_:
{
lean_object* v___x_608_; lean_object* v___x_610_; 
lean_inc(v_a_591_);
v___x_608_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2___redArg(v_splitBackwardRuleCache_597_, v_key_578_, v_a_591_);
if (v_isShared_607_ == 0)
{
lean_ctor_set(v___x_606_, 1, v___x_608_);
v___x_610_ = v___x_606_;
goto v_reusejp_609_;
}
else
{
lean_object* v_reuseFailAlloc_615_; 
v_reuseFailAlloc_615_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_615_, 0, v_specBackwardRuleCache_596_);
lean_ctor_set(v_reuseFailAlloc_615_, 1, v___x_608_);
lean_ctor_set(v_reuseFailAlloc_615_, 2, v_latticeBackwardRuleCache_598_);
lean_ctor_set(v_reuseFailAlloc_615_, 3, v_frameDB_x3f_599_);
lean_ctor_set(v_reuseFailAlloc_615_, 4, v_invariants_600_);
lean_ctor_set(v_reuseFailAlloc_615_, 5, v_vcs_601_);
lean_ctor_set(v_reuseFailAlloc_615_, 6, v_simpState_602_);
lean_ctor_set(v_reuseFailAlloc_615_, 7, v_fuel_603_);
lean_ctor_set(v_reuseFailAlloc_615_, 8, v_inlineHandledInvariants_604_);
v___x_610_ = v_reuseFailAlloc_615_;
goto v_reusejp_609_;
}
v_reusejp_609_:
{
lean_object* v___x_611_; lean_object* v___x_613_; 
v___x_611_ = lean_st_ref_set(v_a_562_, v___x_610_);
if (v_isShared_594_ == 0)
{
v___x_613_ = v___x_593_;
goto v_reusejp_612_;
}
else
{
lean_object* v_reuseFailAlloc_614_; 
v_reuseFailAlloc_614_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_614_, 0, v_a_591_);
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
lean_dec_ref_known(v_key_578_, 2);
return v___x_590_;
}
}
else
{
lean_dec_ref_known(v_key_578_, 2);
return v___x_588_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__0(size_t v_sz_663_, size_t v_i_664_, lean_object* v_bs_665_, lean_object* v___y_666_, lean_object* v___y_667_, lean_object* v___y_668_, lean_object* v___y_669_, lean_object* v___y_670_, lean_object* v___y_671_){
_start:
{
uint8_t v___x_673_; 
v___x_673_ = lean_usize_dec_lt(v_i_664_, v_sz_663_);
if (v___x_673_ == 0)
{
lean_object* v___x_674_; 
v___x_674_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_674_, 0, v_bs_665_);
return v___x_674_;
}
else
{
lean_object* v_v_675_; lean_object* v___x_676_; 
v_v_675_ = lean_array_uget_borrowed(v_bs_665_, v_i_664_);
lean_inc(v_v_675_);
v___x_676_ = l_Lean_Meta_Sym_inferType(v_v_675_, v___y_666_, v___y_667_, v___y_668_, v___y_669_, v___y_670_, v___y_671_);
if (lean_obj_tag(v___x_676_) == 0)
{
lean_object* v_a_677_; lean_object* v___x_678_; lean_object* v_bs_x27_679_; size_t v___x_680_; size_t v___x_681_; lean_object* v___x_682_; 
v_a_677_ = lean_ctor_get(v___x_676_, 0);
lean_inc(v_a_677_);
lean_dec_ref_known(v___x_676_, 1);
v___x_678_ = lean_unsigned_to_nat(0u);
v_bs_x27_679_ = lean_array_uset(v_bs_665_, v_i_664_, v___x_678_);
v___x_680_ = ((size_t)1ULL);
v___x_681_ = lean_usize_add(v_i_664_, v___x_680_);
v___x_682_ = lean_array_uset(v_bs_x27_679_, v_i_664_, v_a_677_);
v_i_664_ = v___x_681_;
v_bs_665_ = v___x_682_;
goto _start;
}
else
{
lean_object* v_a_684_; lean_object* v___x_686_; uint8_t v_isShared_687_; uint8_t v_isSharedCheck_691_; 
lean_dec_ref(v_bs_665_);
v_a_684_ = lean_ctor_get(v___x_676_, 0);
v_isSharedCheck_691_ = !lean_is_exclusive(v___x_676_);
if (v_isSharedCheck_691_ == 0)
{
v___x_686_ = v___x_676_;
v_isShared_687_ = v_isSharedCheck_691_;
goto v_resetjp_685_;
}
else
{
lean_inc(v_a_684_);
lean_dec(v___x_676_);
v___x_686_ = lean_box(0);
v_isShared_687_ = v_isSharedCheck_691_;
goto v_resetjp_685_;
}
v_resetjp_685_:
{
lean_object* v___x_689_; 
if (v_isShared_687_ == 0)
{
v___x_689_ = v___x_686_;
goto v_reusejp_688_;
}
else
{
lean_object* v_reuseFailAlloc_690_; 
v_reuseFailAlloc_690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_690_, 0, v_a_684_);
v___x_689_ = v_reuseFailAlloc_690_;
goto v_reusejp_688_;
}
v_reusejp_688_:
{
return v___x_689_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__0___boxed(lean_object* v_sz_692_, lean_object* v_i_693_, lean_object* v_bs_694_, lean_object* v___y_695_, lean_object* v___y_696_, lean_object* v___y_697_, lean_object* v___y_698_, lean_object* v___y_699_, lean_object* v___y_700_, lean_object* v___y_701_){
_start:
{
size_t v_sz_boxed_702_; size_t v_i_boxed_703_; lean_object* v_res_704_; 
v_sz_boxed_702_ = lean_unbox_usize(v_sz_692_);
lean_dec(v_sz_692_);
v_i_boxed_703_ = lean_unbox_usize(v_i_693_);
lean_dec(v_i_693_);
v_res_704_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__0(v_sz_boxed_702_, v_i_boxed_703_, v_bs_694_, v___y_695_, v___y_696_, v___y_697_, v___y_698_, v___y_699_, v___y_700_);
lean_dec(v___y_700_);
lean_dec_ref(v___y_699_);
lean_dec(v___y_698_);
lean_dec_ref(v___y_697_);
lean_dec(v___y_696_);
lean_dec_ref(v___y_695_);
return v_res_704_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2_spec__2_spec__3___redArg(lean_object* v_xs_705_, lean_object* v_ys_706_, lean_object* v_x_707_){
_start:
{
lean_object* v_zero_708_; uint8_t v_isZero_709_; 
v_zero_708_ = lean_unsigned_to_nat(0u);
v_isZero_709_ = lean_nat_dec_eq(v_x_707_, v_zero_708_);
if (v_isZero_709_ == 1)
{
lean_dec(v_x_707_);
return v_isZero_709_;
}
else
{
lean_object* v_one_710_; lean_object* v_n_711_; lean_object* v___x_712_; lean_object* v___x_713_; size_t v___x_714_; size_t v___x_715_; uint8_t v___x_716_; 
v_one_710_ = lean_unsigned_to_nat(1u);
v_n_711_ = lean_nat_sub(v_x_707_, v_one_710_);
lean_dec(v_x_707_);
v___x_712_ = lean_array_fget_borrowed(v_xs_705_, v_n_711_);
v___x_713_ = lean_array_fget_borrowed(v_ys_706_, v_n_711_);
v___x_714_ = lean_ptr_addr(v___x_712_);
v___x_715_ = lean_ptr_addr(v___x_713_);
v___x_716_ = lean_usize_dec_eq(v___x_714_, v___x_715_);
if (v___x_716_ == 0)
{
lean_dec(v_n_711_);
return v___x_716_;
}
else
{
v_x_707_ = v_n_711_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2_spec__2_spec__3___redArg___boxed(lean_object* v_xs_718_, lean_object* v_ys_719_, lean_object* v_x_720_){
_start:
{
uint8_t v_res_721_; lean_object* v_r_722_; 
v_res_721_ = l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2_spec__2_spec__3___redArg(v_xs_718_, v_ys_719_, v_x_720_);
lean_dec_ref(v_ys_719_);
lean_dec_ref(v_xs_718_);
v_r_722_ = lean_box(v_res_721_);
return v_r_722_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2_spec__2___redArg(lean_object* v_a_723_, lean_object* v_x_724_){
_start:
{
if (lean_obj_tag(v_x_724_) == 0)
{
lean_object* v___x_725_; 
v___x_725_ = lean_box(0);
return v___x_725_;
}
else
{
lean_object* v_key_726_; lean_object* v_value_727_; lean_object* v_tail_728_; uint8_t v___y_730_; lean_object* v_fst_733_; lean_object* v_snd_734_; lean_object* v_fst_735_; lean_object* v_snd_736_; uint8_t v___x_737_; 
v_key_726_ = lean_ctor_get(v_x_724_, 0);
v_value_727_ = lean_ctor_get(v_x_724_, 1);
v_tail_728_ = lean_ctor_get(v_x_724_, 2);
v_fst_733_ = lean_ctor_get(v_key_726_, 0);
v_snd_734_ = lean_ctor_get(v_key_726_, 1);
v_fst_735_ = lean_ctor_get(v_a_723_, 0);
v_snd_736_ = lean_ctor_get(v_a_723_, 1);
v___x_737_ = lean_name_eq(v_fst_733_, v_fst_735_);
if (v___x_737_ == 0)
{
v___y_730_ = v___x_737_;
goto v___jp_729_;
}
else
{
lean_object* v_fst_738_; lean_object* v_snd_739_; lean_object* v_fst_740_; lean_object* v_snd_741_; lean_object* v___x_742_; lean_object* v___x_743_; uint8_t v___x_744_; 
v_fst_738_ = lean_ctor_get(v_snd_734_, 0);
v_snd_739_ = lean_ctor_get(v_snd_734_, 1);
v_fst_740_ = lean_ctor_get(v_snd_736_, 0);
v_snd_741_ = lean_ctor_get(v_snd_736_, 1);
v___x_742_ = lean_array_get_size(v_fst_738_);
v___x_743_ = lean_array_get_size(v_fst_740_);
v___x_744_ = lean_nat_dec_eq(v___x_742_, v___x_743_);
if (v___x_744_ == 0)
{
v_x_724_ = v_tail_728_;
goto _start;
}
else
{
uint8_t v___x_746_; 
v___x_746_ = l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2_spec__2_spec__3___redArg(v_fst_738_, v_fst_740_, v___x_742_);
if (v___x_746_ == 0)
{
v_x_724_ = v_tail_728_;
goto _start;
}
else
{
uint8_t v___x_748_; 
v___x_748_ = lean_nat_dec_eq(v_snd_739_, v_snd_741_);
v___y_730_ = v___x_748_;
goto v___jp_729_;
}
}
}
v___jp_729_:
{
if (v___y_730_ == 0)
{
v_x_724_ = v_tail_728_;
goto _start;
}
else
{
lean_object* v___x_732_; 
lean_inc(v_value_727_);
v___x_732_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_732_, 0, v_value_727_);
return v___x_732_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2_spec__2___redArg___boxed(lean_object* v_a_749_, lean_object* v_x_750_){
_start:
{
lean_object* v_res_751_; 
v_res_751_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2_spec__2___redArg(v_a_749_, v_x_750_);
lean_dec(v_x_750_);
lean_dec_ref(v_a_749_);
return v_res_751_;
}
}
LEAN_EXPORT uint64_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2_spec__3(lean_object* v_as_752_, size_t v_i_753_, size_t v_stop_754_, uint64_t v_b_755_){
_start:
{
uint8_t v___x_756_; 
v___x_756_ = lean_usize_dec_eq(v_i_753_, v_stop_754_);
if (v___x_756_ == 0)
{
lean_object* v___x_757_; size_t v___x_758_; size_t v___x_759_; size_t v___x_760_; uint64_t v___x_761_; uint64_t v___x_762_; size_t v___x_763_; size_t v___x_764_; 
v___x_757_ = lean_array_uget_borrowed(v_as_752_, v_i_753_);
v___x_758_ = lean_ptr_addr(v___x_757_);
v___x_759_ = ((size_t)3ULL);
v___x_760_ = lean_usize_shift_right(v___x_758_, v___x_759_);
v___x_761_ = lean_usize_to_uint64(v___x_760_);
v___x_762_ = lean_uint64_mix_hash(v_b_755_, v___x_761_);
v___x_763_ = ((size_t)1ULL);
v___x_764_ = lean_usize_add(v_i_753_, v___x_763_);
v_i_753_ = v___x_764_;
v_b_755_ = v___x_762_;
goto _start;
}
else
{
return v_b_755_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2_spec__3___boxed(lean_object* v_as_766_, lean_object* v_i_767_, lean_object* v_stop_768_, lean_object* v_b_769_){
_start:
{
size_t v_i_boxed_770_; size_t v_stop_boxed_771_; uint64_t v_b_boxed_772_; uint64_t v_res_773_; lean_object* v_r_774_; 
v_i_boxed_770_ = lean_unbox_usize(v_i_767_);
lean_dec(v_i_767_);
v_stop_boxed_771_ = lean_unbox_usize(v_stop_768_);
lean_dec(v_stop_768_);
v_b_boxed_772_ = lean_unbox_uint64(v_b_769_);
lean_dec_ref(v_b_769_);
v_res_773_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2_spec__3(v_as_766_, v_i_boxed_770_, v_stop_boxed_771_, v_b_boxed_772_);
lean_dec_ref(v_as_766_);
v_r_774_ = lean_box_uint64(v_res_773_);
return v_r_774_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2___redArg(lean_object* v_m_775_, lean_object* v_a_776_){
_start:
{
lean_object* v_buckets_777_; lean_object* v_fst_778_; lean_object* v_snd_779_; lean_object* v___x_780_; lean_object* v___y_782_; uint64_t v___y_783_; uint64_t v___y_784_; uint64_t v___y_802_; 
v_buckets_777_ = lean_ctor_get(v_m_775_, 1);
v_fst_778_ = lean_ctor_get(v_a_776_, 0);
v_snd_779_ = lean_ctor_get(v_a_776_, 1);
v___x_780_ = lean_array_get_size(v_buckets_777_);
if (lean_obj_tag(v_fst_778_) == 0)
{
uint64_t v___x_816_; 
v___x_816_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg___closed__0);
v___y_802_ = v___x_816_;
goto v___jp_801_;
}
else
{
uint64_t v_hash_817_; 
v_hash_817_ = lean_ctor_get_uint64(v_fst_778_, sizeof(void*)*2);
v___y_802_ = v_hash_817_;
goto v___jp_801_;
}
v___jp_781_:
{
uint64_t v___x_785_; uint64_t v___x_786_; uint64_t v___x_787_; uint64_t v___x_788_; uint64_t v___x_789_; uint64_t v_fold_790_; uint64_t v___x_791_; uint64_t v___x_792_; uint64_t v___x_793_; size_t v___x_794_; size_t v___x_795_; size_t v___x_796_; size_t v___x_797_; size_t v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; 
v___x_785_ = lean_uint64_of_nat(v___y_782_);
v___x_786_ = lean_uint64_mix_hash(v___y_784_, v___x_785_);
v___x_787_ = lean_uint64_mix_hash(v___y_783_, v___x_786_);
v___x_788_ = 32ULL;
v___x_789_ = lean_uint64_shift_right(v___x_787_, v___x_788_);
v_fold_790_ = lean_uint64_xor(v___x_787_, v___x_789_);
v___x_791_ = 16ULL;
v___x_792_ = lean_uint64_shift_right(v_fold_790_, v___x_791_);
v___x_793_ = lean_uint64_xor(v_fold_790_, v___x_792_);
v___x_794_ = lean_uint64_to_usize(v___x_793_);
v___x_795_ = lean_usize_of_nat(v___x_780_);
v___x_796_ = ((size_t)1ULL);
v___x_797_ = lean_usize_sub(v___x_795_, v___x_796_);
v___x_798_ = lean_usize_land(v___x_794_, v___x_797_);
v___x_799_ = lean_array_uget_borrowed(v_buckets_777_, v___x_798_);
v___x_800_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2_spec__2___redArg(v_a_776_, v___x_799_);
return v___x_800_;
}
v___jp_801_:
{
lean_object* v_fst_803_; lean_object* v_snd_804_; uint64_t v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; uint8_t v___x_808_; 
v_fst_803_ = lean_ctor_get(v_snd_779_, 0);
v_snd_804_ = lean_ctor_get(v_snd_779_, 1);
v___x_805_ = 7ULL;
v___x_806_ = lean_unsigned_to_nat(0u);
v___x_807_ = lean_array_get_size(v_fst_803_);
v___x_808_ = lean_nat_dec_lt(v___x_806_, v___x_807_);
if (v___x_808_ == 0)
{
v___y_782_ = v_snd_804_;
v___y_783_ = v___y_802_;
v___y_784_ = v___x_805_;
goto v___jp_781_;
}
else
{
uint8_t v___x_809_; 
v___x_809_ = lean_nat_dec_le(v___x_807_, v___x_807_);
if (v___x_809_ == 0)
{
if (v___x_808_ == 0)
{
v___y_782_ = v_snd_804_;
v___y_783_ = v___y_802_;
v___y_784_ = v___x_805_;
goto v___jp_781_;
}
else
{
size_t v___x_810_; size_t v___x_811_; uint64_t v___x_812_; 
v___x_810_ = ((size_t)0ULL);
v___x_811_ = lean_usize_of_nat(v___x_807_);
v___x_812_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2_spec__3(v_fst_803_, v___x_810_, v___x_811_, v___x_805_);
v___y_782_ = v_snd_804_;
v___y_783_ = v___y_802_;
v___y_784_ = v___x_812_;
goto v___jp_781_;
}
}
else
{
size_t v___x_813_; size_t v___x_814_; uint64_t v___x_815_; 
v___x_813_ = ((size_t)0ULL);
v___x_814_ = lean_usize_of_nat(v___x_807_);
v___x_815_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2_spec__3(v_fst_803_, v___x_813_, v___x_814_, v___x_805_);
v___y_782_ = v_snd_804_;
v___y_783_ = v___y_802_;
v___y_784_ = v___x_815_;
goto v___jp_781_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2___redArg___boxed(lean_object* v_m_818_, lean_object* v_a_819_){
_start:
{
lean_object* v_res_820_; 
v_res_820_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2___redArg(v_m_818_, v_a_819_);
lean_dec_ref(v_a_819_);
lean_dec_ref(v_m_818_);
return v_res_820_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__1(size_t v_sz_821_, size_t v_i_822_, lean_object* v_bs_823_){
_start:
{
uint8_t v___x_824_; 
v___x_824_ = lean_usize_dec_lt(v_i_822_, v_sz_821_);
if (v___x_824_ == 0)
{
return v_bs_823_;
}
else
{
lean_object* v_v_825_; lean_object* v___x_826_; lean_object* v_bs_x27_827_; size_t v___x_828_; size_t v___x_829_; lean_object* v___x_830_; 
v_v_825_ = lean_array_uget(v_bs_823_, v_i_822_);
v___x_826_ = lean_unsigned_to_nat(0u);
v_bs_x27_827_ = lean_array_uset(v_bs_823_, v_i_822_, v___x_826_);
v___x_828_ = ((size_t)1ULL);
v___x_829_ = lean_usize_add(v_i_822_, v___x_828_);
v___x_830_ = lean_array_uset(v_bs_x27_827_, v_i_822_, v_v_825_);
v_i_822_ = v___x_829_;
v_bs_823_ = v___x_830_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__1___boxed(lean_object* v_sz_832_, lean_object* v_i_833_, lean_object* v_bs_834_){
_start:
{
size_t v_sz_boxed_835_; size_t v_i_boxed_836_; lean_object* v_res_837_; 
v_sz_boxed_835_ = lean_unbox_usize(v_sz_832_);
lean_dec(v_sz_832_);
v_i_boxed_836_ = lean_unbox_usize(v_i_833_);
lean_dec(v_i_833_);
v_res_837_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__1(v_sz_boxed_835_, v_i_boxed_836_, v_bs_834_);
return v_res_837_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__3_spec__6_spec__8_spec__9___redArg(lean_object* v_x_838_, lean_object* v_x_839_){
_start:
{
if (lean_obj_tag(v_x_839_) == 0)
{
return v_x_838_;
}
else
{
lean_object* v_key_840_; lean_object* v_value_841_; lean_object* v_tail_842_; lean_object* v___x_844_; uint8_t v_isShared_845_; uint8_t v_isSharedCheck_890_; 
v_key_840_ = lean_ctor_get(v_x_839_, 0);
v_value_841_ = lean_ctor_get(v_x_839_, 1);
v_tail_842_ = lean_ctor_get(v_x_839_, 2);
v_isSharedCheck_890_ = !lean_is_exclusive(v_x_839_);
if (v_isSharedCheck_890_ == 0)
{
v___x_844_ = v_x_839_;
v_isShared_845_ = v_isSharedCheck_890_;
goto v_resetjp_843_;
}
else
{
lean_inc(v_tail_842_);
lean_inc(v_value_841_);
lean_inc(v_key_840_);
lean_dec(v_x_839_);
v___x_844_ = lean_box(0);
v_isShared_845_ = v_isSharedCheck_890_;
goto v_resetjp_843_;
}
v_resetjp_843_:
{
lean_object* v_fst_846_; lean_object* v_snd_847_; lean_object* v___x_848_; lean_object* v___y_850_; uint64_t v___y_851_; uint64_t v___y_852_; uint64_t v___y_874_; 
v_fst_846_ = lean_ctor_get(v_key_840_, 0);
v_snd_847_ = lean_ctor_get(v_key_840_, 1);
v___x_848_ = lean_array_get_size(v_x_838_);
if (lean_obj_tag(v_fst_846_) == 0)
{
uint64_t v___x_888_; 
v___x_888_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg___closed__0);
v___y_874_ = v___x_888_;
goto v___jp_873_;
}
else
{
uint64_t v_hash_889_; 
v_hash_889_ = lean_ctor_get_uint64(v_fst_846_, sizeof(void*)*2);
v___y_874_ = v_hash_889_;
goto v___jp_873_;
}
v___jp_849_:
{
uint64_t v___x_853_; uint64_t v___x_854_; uint64_t v___x_855_; uint64_t v___x_856_; uint64_t v___x_857_; uint64_t v_fold_858_; uint64_t v___x_859_; uint64_t v___x_860_; uint64_t v___x_861_; size_t v___x_862_; size_t v___x_863_; size_t v___x_864_; size_t v___x_865_; size_t v___x_866_; lean_object* v___x_867_; lean_object* v___x_869_; 
v___x_853_ = lean_uint64_of_nat(v___y_850_);
lean_dec(v___y_850_);
v___x_854_ = lean_uint64_mix_hash(v___y_852_, v___x_853_);
v___x_855_ = lean_uint64_mix_hash(v___y_851_, v___x_854_);
v___x_856_ = 32ULL;
v___x_857_ = lean_uint64_shift_right(v___x_855_, v___x_856_);
v_fold_858_ = lean_uint64_xor(v___x_855_, v___x_857_);
v___x_859_ = 16ULL;
v___x_860_ = lean_uint64_shift_right(v_fold_858_, v___x_859_);
v___x_861_ = lean_uint64_xor(v_fold_858_, v___x_860_);
v___x_862_ = lean_uint64_to_usize(v___x_861_);
v___x_863_ = lean_usize_of_nat(v___x_848_);
v___x_864_ = ((size_t)1ULL);
v___x_865_ = lean_usize_sub(v___x_863_, v___x_864_);
v___x_866_ = lean_usize_land(v___x_862_, v___x_865_);
v___x_867_ = lean_array_uget_borrowed(v_x_838_, v___x_866_);
lean_inc(v___x_867_);
if (v_isShared_845_ == 0)
{
lean_ctor_set(v___x_844_, 2, v___x_867_);
v___x_869_ = v___x_844_;
goto v_reusejp_868_;
}
else
{
lean_object* v_reuseFailAlloc_872_; 
v_reuseFailAlloc_872_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_872_, 0, v_key_840_);
lean_ctor_set(v_reuseFailAlloc_872_, 1, v_value_841_);
lean_ctor_set(v_reuseFailAlloc_872_, 2, v___x_867_);
v___x_869_ = v_reuseFailAlloc_872_;
goto v_reusejp_868_;
}
v_reusejp_868_:
{
lean_object* v___x_870_; 
v___x_870_ = lean_array_uset(v_x_838_, v___x_866_, v___x_869_);
v_x_838_ = v___x_870_;
v_x_839_ = v_tail_842_;
goto _start;
}
}
v___jp_873_:
{
lean_object* v_fst_875_; lean_object* v_snd_876_; uint64_t v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; uint8_t v___x_880_; 
v_fst_875_ = lean_ctor_get(v_snd_847_, 0);
v_snd_876_ = lean_ctor_get(v_snd_847_, 1);
v___x_877_ = 7ULL;
v___x_878_ = lean_unsigned_to_nat(0u);
v___x_879_ = lean_array_get_size(v_fst_875_);
v___x_880_ = lean_nat_dec_lt(v___x_878_, v___x_879_);
if (v___x_880_ == 0)
{
lean_inc(v_snd_876_);
v___y_850_ = v_snd_876_;
v___y_851_ = v___y_874_;
v___y_852_ = v___x_877_;
goto v___jp_849_;
}
else
{
uint8_t v___x_881_; 
v___x_881_ = lean_nat_dec_le(v___x_879_, v___x_879_);
if (v___x_881_ == 0)
{
if (v___x_880_ == 0)
{
lean_inc(v_snd_876_);
v___y_850_ = v_snd_876_;
v___y_851_ = v___y_874_;
v___y_852_ = v___x_877_;
goto v___jp_849_;
}
else
{
size_t v___x_882_; size_t v___x_883_; uint64_t v___x_884_; 
v___x_882_ = ((size_t)0ULL);
v___x_883_ = lean_usize_of_nat(v___x_879_);
v___x_884_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2_spec__3(v_fst_875_, v___x_882_, v___x_883_, v___x_877_);
lean_inc(v_snd_876_);
v___y_850_ = v_snd_876_;
v___y_851_ = v___y_874_;
v___y_852_ = v___x_884_;
goto v___jp_849_;
}
}
else
{
size_t v___x_885_; size_t v___x_886_; uint64_t v___x_887_; 
v___x_885_ = ((size_t)0ULL);
v___x_886_ = lean_usize_of_nat(v___x_879_);
v___x_887_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2_spec__3(v_fst_875_, v___x_885_, v___x_886_, v___x_877_);
lean_inc(v_snd_876_);
v___y_850_ = v_snd_876_;
v___y_851_ = v___y_874_;
v___y_852_ = v___x_887_;
goto v___jp_849_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__3_spec__6_spec__8___redArg(lean_object* v_i_891_, lean_object* v_source_892_, lean_object* v_target_893_){
_start:
{
lean_object* v___x_894_; uint8_t v___x_895_; 
v___x_894_ = lean_array_get_size(v_source_892_);
v___x_895_ = lean_nat_dec_lt(v_i_891_, v___x_894_);
if (v___x_895_ == 0)
{
lean_dec_ref(v_source_892_);
lean_dec(v_i_891_);
return v_target_893_;
}
else
{
lean_object* v_es_896_; lean_object* v___x_897_; lean_object* v_source_898_; lean_object* v_target_899_; lean_object* v___x_900_; lean_object* v___x_901_; 
v_es_896_ = lean_array_fget(v_source_892_, v_i_891_);
v___x_897_ = lean_box(0);
v_source_898_ = lean_array_fset(v_source_892_, v_i_891_, v___x_897_);
v_target_899_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__3_spec__6_spec__8_spec__9___redArg(v_target_893_, v_es_896_);
v___x_900_ = lean_unsigned_to_nat(1u);
v___x_901_ = lean_nat_add(v_i_891_, v___x_900_);
lean_dec(v_i_891_);
v_i_891_ = v___x_901_;
v_source_892_ = v_source_898_;
v_target_893_ = v_target_899_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__3_spec__6___redArg(lean_object* v_data_903_){
_start:
{
lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v_nbuckets_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; 
v___x_904_ = lean_array_get_size(v_data_903_);
v___x_905_ = lean_unsigned_to_nat(2u);
v_nbuckets_906_ = lean_nat_mul(v___x_904_, v___x_905_);
v___x_907_ = lean_unsigned_to_nat(0u);
v___x_908_ = lean_box(0);
v___x_909_ = lean_mk_array(v_nbuckets_906_, v___x_908_);
v___x_910_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__3_spec__6_spec__8___redArg(v___x_907_, v_data_903_, v___x_909_);
return v___x_910_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__3_spec__7___redArg(lean_object* v_a_911_, lean_object* v_b_912_, lean_object* v_x_913_){
_start:
{
if (lean_obj_tag(v_x_913_) == 0)
{
lean_dec(v_b_912_);
lean_dec_ref(v_a_911_);
return v_x_913_;
}
else
{
lean_object* v_key_914_; lean_object* v_value_915_; lean_object* v_tail_916_; lean_object* v___x_918_; uint8_t v_isShared_919_; uint8_t v_isSharedCheck_942_; 
v_key_914_ = lean_ctor_get(v_x_913_, 0);
v_value_915_ = lean_ctor_get(v_x_913_, 1);
v_tail_916_ = lean_ctor_get(v_x_913_, 2);
v_isSharedCheck_942_ = !lean_is_exclusive(v_x_913_);
if (v_isSharedCheck_942_ == 0)
{
v___x_918_ = v_x_913_;
v_isShared_919_ = v_isSharedCheck_942_;
goto v_resetjp_917_;
}
else
{
lean_inc(v_tail_916_);
lean_inc(v_value_915_);
lean_inc(v_key_914_);
lean_dec(v_x_913_);
v___x_918_ = lean_box(0);
v_isShared_919_ = v_isSharedCheck_942_;
goto v_resetjp_917_;
}
v_resetjp_917_:
{
uint8_t v___y_926_; lean_object* v_fst_928_; lean_object* v_snd_929_; lean_object* v_fst_930_; lean_object* v_snd_931_; uint8_t v___x_932_; 
v_fst_928_ = lean_ctor_get(v_key_914_, 0);
v_snd_929_ = lean_ctor_get(v_key_914_, 1);
v_fst_930_ = lean_ctor_get(v_a_911_, 0);
v_snd_931_ = lean_ctor_get(v_a_911_, 1);
v___x_932_ = lean_name_eq(v_fst_928_, v_fst_930_);
if (v___x_932_ == 0)
{
v___y_926_ = v___x_932_;
goto v___jp_925_;
}
else
{
lean_object* v_fst_933_; lean_object* v_snd_934_; lean_object* v_fst_935_; lean_object* v_snd_936_; lean_object* v___x_937_; lean_object* v___x_938_; uint8_t v___x_939_; 
v_fst_933_ = lean_ctor_get(v_snd_929_, 0);
v_snd_934_ = lean_ctor_get(v_snd_929_, 1);
v_fst_935_ = lean_ctor_get(v_snd_931_, 0);
v_snd_936_ = lean_ctor_get(v_snd_931_, 1);
v___x_937_ = lean_array_get_size(v_fst_933_);
v___x_938_ = lean_array_get_size(v_fst_935_);
v___x_939_ = lean_nat_dec_eq(v___x_937_, v___x_938_);
if (v___x_939_ == 0)
{
goto v___jp_920_;
}
else
{
uint8_t v___x_940_; 
v___x_940_ = l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2_spec__2_spec__3___redArg(v_fst_933_, v_fst_935_, v___x_937_);
if (v___x_940_ == 0)
{
goto v___jp_920_;
}
else
{
uint8_t v___x_941_; 
v___x_941_ = lean_nat_dec_eq(v_snd_934_, v_snd_936_);
v___y_926_ = v___x_941_;
goto v___jp_925_;
}
}
}
v___jp_920_:
{
lean_object* v___x_921_; lean_object* v___x_923_; 
v___x_921_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__3_spec__7___redArg(v_a_911_, v_b_912_, v_tail_916_);
if (v_isShared_919_ == 0)
{
lean_ctor_set(v___x_918_, 2, v___x_921_);
v___x_923_ = v___x_918_;
goto v_reusejp_922_;
}
else
{
lean_object* v_reuseFailAlloc_924_; 
v_reuseFailAlloc_924_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_924_, 0, v_key_914_);
lean_ctor_set(v_reuseFailAlloc_924_, 1, v_value_915_);
lean_ctor_set(v_reuseFailAlloc_924_, 2, v___x_921_);
v___x_923_ = v_reuseFailAlloc_924_;
goto v_reusejp_922_;
}
v_reusejp_922_:
{
return v___x_923_;
}
}
v___jp_925_:
{
if (v___y_926_ == 0)
{
goto v___jp_920_;
}
else
{
lean_object* v___x_927_; 
lean_del_object(v___x_918_);
lean_dec(v_value_915_);
lean_dec(v_key_914_);
v___x_927_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_927_, 0, v_a_911_);
lean_ctor_set(v___x_927_, 1, v_b_912_);
lean_ctor_set(v___x_927_, 2, v_tail_916_);
return v___x_927_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__3_spec__5___redArg(lean_object* v_a_943_, lean_object* v_x_944_){
_start:
{
if (lean_obj_tag(v_x_944_) == 0)
{
uint8_t v___x_945_; 
v___x_945_ = 0;
return v___x_945_;
}
else
{
lean_object* v_key_946_; lean_object* v_tail_947_; uint8_t v___y_949_; lean_object* v_fst_951_; lean_object* v_snd_952_; lean_object* v_fst_953_; lean_object* v_snd_954_; uint8_t v___x_955_; 
v_key_946_ = lean_ctor_get(v_x_944_, 0);
v_tail_947_ = lean_ctor_get(v_x_944_, 2);
v_fst_951_ = lean_ctor_get(v_key_946_, 0);
v_snd_952_ = lean_ctor_get(v_key_946_, 1);
v_fst_953_ = lean_ctor_get(v_a_943_, 0);
v_snd_954_ = lean_ctor_get(v_a_943_, 1);
v___x_955_ = lean_name_eq(v_fst_951_, v_fst_953_);
if (v___x_955_ == 0)
{
v___y_949_ = v___x_955_;
goto v___jp_948_;
}
else
{
lean_object* v_fst_956_; lean_object* v_snd_957_; lean_object* v_fst_958_; lean_object* v_snd_959_; lean_object* v___x_960_; lean_object* v___x_961_; uint8_t v___x_962_; 
v_fst_956_ = lean_ctor_get(v_snd_952_, 0);
v_snd_957_ = lean_ctor_get(v_snd_952_, 1);
v_fst_958_ = lean_ctor_get(v_snd_954_, 0);
v_snd_959_ = lean_ctor_get(v_snd_954_, 1);
v___x_960_ = lean_array_get_size(v_fst_956_);
v___x_961_ = lean_array_get_size(v_fst_958_);
v___x_962_ = lean_nat_dec_eq(v___x_960_, v___x_961_);
if (v___x_962_ == 0)
{
v_x_944_ = v_tail_947_;
goto _start;
}
else
{
uint8_t v___x_964_; 
v___x_964_ = l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2_spec__2_spec__3___redArg(v_fst_956_, v_fst_958_, v___x_960_);
if (v___x_964_ == 0)
{
v_x_944_ = v_tail_947_;
goto _start;
}
else
{
uint8_t v___x_966_; 
v___x_966_ = lean_nat_dec_eq(v_snd_957_, v_snd_959_);
v___y_949_ = v___x_966_;
goto v___jp_948_;
}
}
}
v___jp_948_:
{
if (v___y_949_ == 0)
{
v_x_944_ = v_tail_947_;
goto _start;
}
else
{
return v___y_949_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__3_spec__5___redArg___boxed(lean_object* v_a_967_, lean_object* v_x_968_){
_start:
{
uint8_t v_res_969_; lean_object* v_r_970_; 
v_res_969_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__3_spec__5___redArg(v_a_967_, v_x_968_);
lean_dec(v_x_968_);
lean_dec_ref(v_a_967_);
v_r_970_ = lean_box(v_res_969_);
return v_r_970_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__3___redArg(lean_object* v_m_971_, lean_object* v_a_972_, lean_object* v_b_973_){
_start:
{
lean_object* v_size_974_; lean_object* v_buckets_975_; lean_object* v___x_977_; uint8_t v_isShared_978_; uint8_t v_isSharedCheck_1043_; 
v_size_974_ = lean_ctor_get(v_m_971_, 0);
v_buckets_975_ = lean_ctor_get(v_m_971_, 1);
v_isSharedCheck_1043_ = !lean_is_exclusive(v_m_971_);
if (v_isSharedCheck_1043_ == 0)
{
v___x_977_ = v_m_971_;
v_isShared_978_ = v_isSharedCheck_1043_;
goto v_resetjp_976_;
}
else
{
lean_inc(v_buckets_975_);
lean_inc(v_size_974_);
lean_dec(v_m_971_);
v___x_977_ = lean_box(0);
v_isShared_978_ = v_isSharedCheck_1043_;
goto v_resetjp_976_;
}
v_resetjp_976_:
{
lean_object* v_fst_979_; lean_object* v_snd_980_; lean_object* v___x_981_; lean_object* v___y_983_; uint64_t v___y_984_; uint64_t v___y_985_; uint64_t v___y_1027_; 
v_fst_979_ = lean_ctor_get(v_a_972_, 0);
v_snd_980_ = lean_ctor_get(v_a_972_, 1);
v___x_981_ = lean_array_get_size(v_buckets_975_);
if (lean_obj_tag(v_fst_979_) == 0)
{
uint64_t v___x_1041_; 
v___x_1041_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg___closed__0);
v___y_1027_ = v___x_1041_;
goto v___jp_1026_;
}
else
{
uint64_t v_hash_1042_; 
v_hash_1042_ = lean_ctor_get_uint64(v_fst_979_, sizeof(void*)*2);
v___y_1027_ = v_hash_1042_;
goto v___jp_1026_;
}
v___jp_982_:
{
uint64_t v___x_986_; uint64_t v___x_987_; uint64_t v___x_988_; uint64_t v___x_989_; uint64_t v___x_990_; uint64_t v_fold_991_; uint64_t v___x_992_; uint64_t v___x_993_; uint64_t v___x_994_; size_t v___x_995_; size_t v___x_996_; size_t v___x_997_; size_t v___x_998_; size_t v___x_999_; lean_object* v_bkt_1000_; uint8_t v___x_1001_; 
v___x_986_ = lean_uint64_of_nat(v___y_983_);
lean_dec(v___y_983_);
v___x_987_ = lean_uint64_mix_hash(v___y_985_, v___x_986_);
v___x_988_ = lean_uint64_mix_hash(v___y_984_, v___x_987_);
v___x_989_ = 32ULL;
v___x_990_ = lean_uint64_shift_right(v___x_988_, v___x_989_);
v_fold_991_ = lean_uint64_xor(v___x_988_, v___x_990_);
v___x_992_ = 16ULL;
v___x_993_ = lean_uint64_shift_right(v_fold_991_, v___x_992_);
v___x_994_ = lean_uint64_xor(v_fold_991_, v___x_993_);
v___x_995_ = lean_uint64_to_usize(v___x_994_);
v___x_996_ = lean_usize_of_nat(v___x_981_);
v___x_997_ = ((size_t)1ULL);
v___x_998_ = lean_usize_sub(v___x_996_, v___x_997_);
v___x_999_ = lean_usize_land(v___x_995_, v___x_998_);
v_bkt_1000_ = lean_array_uget_borrowed(v_buckets_975_, v___x_999_);
v___x_1001_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__3_spec__5___redArg(v_a_972_, v_bkt_1000_);
if (v___x_1001_ == 0)
{
lean_object* v___x_1002_; lean_object* v_size_x27_1003_; lean_object* v___x_1004_; lean_object* v_buckets_x27_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; uint8_t v___x_1011_; 
v___x_1002_ = lean_unsigned_to_nat(1u);
v_size_x27_1003_ = lean_nat_add(v_size_974_, v___x_1002_);
lean_dec(v_size_974_);
lean_inc(v_bkt_1000_);
v___x_1004_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1004_, 0, v_a_972_);
lean_ctor_set(v___x_1004_, 1, v_b_973_);
lean_ctor_set(v___x_1004_, 2, v_bkt_1000_);
v_buckets_x27_1005_ = lean_array_uset(v_buckets_975_, v___x_999_, v___x_1004_);
v___x_1006_ = lean_unsigned_to_nat(4u);
v___x_1007_ = lean_nat_mul(v_size_x27_1003_, v___x_1006_);
v___x_1008_ = lean_unsigned_to_nat(3u);
v___x_1009_ = lean_nat_div(v___x_1007_, v___x_1008_);
lean_dec(v___x_1007_);
v___x_1010_ = lean_array_get_size(v_buckets_x27_1005_);
v___x_1011_ = lean_nat_dec_le(v___x_1009_, v___x_1010_);
lean_dec(v___x_1009_);
if (v___x_1011_ == 0)
{
lean_object* v_val_1012_; lean_object* v___x_1014_; 
v_val_1012_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__3_spec__6___redArg(v_buckets_x27_1005_);
if (v_isShared_978_ == 0)
{
lean_ctor_set(v___x_977_, 1, v_val_1012_);
lean_ctor_set(v___x_977_, 0, v_size_x27_1003_);
v___x_1014_ = v___x_977_;
goto v_reusejp_1013_;
}
else
{
lean_object* v_reuseFailAlloc_1015_; 
v_reuseFailAlloc_1015_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1015_, 0, v_size_x27_1003_);
lean_ctor_set(v_reuseFailAlloc_1015_, 1, v_val_1012_);
v___x_1014_ = v_reuseFailAlloc_1015_;
goto v_reusejp_1013_;
}
v_reusejp_1013_:
{
return v___x_1014_;
}
}
else
{
lean_object* v___x_1017_; 
if (v_isShared_978_ == 0)
{
lean_ctor_set(v___x_977_, 1, v_buckets_x27_1005_);
lean_ctor_set(v___x_977_, 0, v_size_x27_1003_);
v___x_1017_ = v___x_977_;
goto v_reusejp_1016_;
}
else
{
lean_object* v_reuseFailAlloc_1018_; 
v_reuseFailAlloc_1018_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1018_, 0, v_size_x27_1003_);
lean_ctor_set(v_reuseFailAlloc_1018_, 1, v_buckets_x27_1005_);
v___x_1017_ = v_reuseFailAlloc_1018_;
goto v_reusejp_1016_;
}
v_reusejp_1016_:
{
return v___x_1017_;
}
}
}
else
{
lean_object* v___x_1019_; lean_object* v_buckets_x27_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1024_; 
lean_inc(v_bkt_1000_);
v___x_1019_ = lean_box(0);
v_buckets_x27_1020_ = lean_array_uset(v_buckets_975_, v___x_999_, v___x_1019_);
v___x_1021_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__3_spec__7___redArg(v_a_972_, v_b_973_, v_bkt_1000_);
v___x_1022_ = lean_array_uset(v_buckets_x27_1020_, v___x_999_, v___x_1021_);
if (v_isShared_978_ == 0)
{
lean_ctor_set(v___x_977_, 1, v___x_1022_);
v___x_1024_ = v___x_977_;
goto v_reusejp_1023_;
}
else
{
lean_object* v_reuseFailAlloc_1025_; 
v_reuseFailAlloc_1025_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1025_, 0, v_size_974_);
lean_ctor_set(v_reuseFailAlloc_1025_, 1, v___x_1022_);
v___x_1024_ = v_reuseFailAlloc_1025_;
goto v_reusejp_1023_;
}
v_reusejp_1023_:
{
return v___x_1024_;
}
}
}
v___jp_1026_:
{
lean_object* v_fst_1028_; lean_object* v_snd_1029_; uint64_t v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; uint8_t v___x_1033_; 
v_fst_1028_ = lean_ctor_get(v_snd_980_, 0);
v_snd_1029_ = lean_ctor_get(v_snd_980_, 1);
v___x_1030_ = 7ULL;
v___x_1031_ = lean_unsigned_to_nat(0u);
v___x_1032_ = lean_array_get_size(v_fst_1028_);
v___x_1033_ = lean_nat_dec_lt(v___x_1031_, v___x_1032_);
if (v___x_1033_ == 0)
{
lean_inc(v_snd_1029_);
v___y_983_ = v_snd_1029_;
v___y_984_ = v___y_1027_;
v___y_985_ = v___x_1030_;
goto v___jp_982_;
}
else
{
uint8_t v___x_1034_; 
v___x_1034_ = lean_nat_dec_le(v___x_1032_, v___x_1032_);
if (v___x_1034_ == 0)
{
if (v___x_1033_ == 0)
{
lean_inc(v_snd_1029_);
v___y_983_ = v_snd_1029_;
v___y_984_ = v___y_1027_;
v___y_985_ = v___x_1030_;
goto v___jp_982_;
}
else
{
size_t v___x_1035_; size_t v___x_1036_; uint64_t v___x_1037_; 
v___x_1035_ = ((size_t)0ULL);
v___x_1036_ = lean_usize_of_nat(v___x_1032_);
v___x_1037_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2_spec__3(v_fst_1028_, v___x_1035_, v___x_1036_, v___x_1030_);
lean_inc(v_snd_1029_);
v___y_983_ = v_snd_1029_;
v___y_984_ = v___y_1027_;
v___y_985_ = v___x_1037_;
goto v___jp_982_;
}
}
else
{
size_t v___x_1038_; size_t v___x_1039_; uint64_t v___x_1040_; 
v___x_1038_ = ((size_t)0ULL);
v___x_1039_ = lean_usize_of_nat(v___x_1032_);
v___x_1040_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2_spec__3(v_fst_1028_, v___x_1038_, v___x_1039_, v___x_1030_);
lean_inc(v_snd_1029_);
v___y_983_ = v_snd_1029_;
v___y_984_ = v___y_1027_;
v___y_985_ = v___x_1040_;
goto v___jp_982_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached___redArg(lean_object* v_c_1044_, lean_object* v_as_1045_, lean_object* v_excessArgs_1046_, lean_object* v_resultType_x3f_1047_, lean_object* v_a_1048_, lean_object* v_a_1049_, lean_object* v_a_1050_, lean_object* v_a_1051_, lean_object* v_a_1052_, lean_object* v_a_1053_, lean_object* v_a_1054_){
_start:
{
lean_object* v___x_1056_; size_t v_sz_1057_; size_t v___x_1058_; lean_object* v___x_1059_; 
v___x_1056_ = lean_st_ref_get(v_a_1048_);
v_sz_1057_ = lean_array_size(v_as_1045_);
v___x_1058_ = ((size_t)0ULL);
lean_inc_ref(v_as_1045_);
v___x_1059_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__0(v_sz_1057_, v___x_1058_, v_as_1045_, v_a_1049_, v_a_1050_, v_a_1051_, v_a_1052_, v_a_1053_, v_a_1054_);
if (lean_obj_tag(v___x_1059_) == 0)
{
lean_object* v_a_1060_; lean_object* v___x_1062_; uint8_t v_isShared_1063_; uint8_t v_isSharedCheck_1106_; 
v_a_1060_ = lean_ctor_get(v___x_1059_, 0);
v_isSharedCheck_1106_ = !lean_is_exclusive(v___x_1059_);
if (v_isSharedCheck_1106_ == 0)
{
v___x_1062_ = v___x_1059_;
v_isShared_1063_ = v_isSharedCheck_1106_;
goto v_resetjp_1061_;
}
else
{
lean_inc(v_a_1060_);
lean_dec(v___x_1059_);
v___x_1062_ = lean_box(0);
v_isShared_1063_ = v_isSharedCheck_1106_;
goto v_resetjp_1061_;
}
v_resetjp_1061_:
{
lean_object* v_latticeBackwardRuleCache_1064_; lean_object* v_applyLemma_1065_; size_t v_sz_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; 
v_latticeBackwardRuleCache_1064_ = lean_ctor_get(v___x_1056_, 2);
lean_inc_ref(v_latticeBackwardRuleCache_1064_);
lean_dec(v___x_1056_);
v_applyLemma_1065_ = lean_ctor_get(v_c_1044_, 1);
v_sz_1066_ = lean_array_size(v_a_1060_);
v___x_1067_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__1(v_sz_1066_, v___x_1058_, v_a_1060_);
v___x_1068_ = lean_array_get_size(v_excessArgs_1046_);
v___x_1069_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1069_, 0, v___x_1067_);
lean_ctor_set(v___x_1069_, 1, v___x_1068_);
lean_inc(v_applyLemma_1065_);
v___x_1070_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1070_, 0, v_applyLemma_1065_);
lean_ctor_set(v___x_1070_, 1, v___x_1069_);
v___x_1071_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2___redArg(v_latticeBackwardRuleCache_1064_, v___x_1070_);
lean_dec_ref(v_latticeBackwardRuleCache_1064_);
if (lean_obj_tag(v___x_1071_) == 1)
{
lean_object* v_val_1072_; lean_object* v___x_1074_; 
lean_dec_ref_known(v___x_1070_, 2);
lean_dec(v_resultType_x3f_1047_);
lean_dec_ref(v_excessArgs_1046_);
lean_dec_ref(v_as_1045_);
lean_dec_ref(v_c_1044_);
v_val_1072_ = lean_ctor_get(v___x_1071_, 0);
lean_inc(v_val_1072_);
lean_dec_ref_known(v___x_1071_, 1);
if (v_isShared_1063_ == 0)
{
lean_ctor_set(v___x_1062_, 0, v_val_1072_);
v___x_1074_ = v___x_1062_;
goto v_reusejp_1073_;
}
else
{
lean_object* v_reuseFailAlloc_1075_; 
v_reuseFailAlloc_1075_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1075_, 0, v_val_1072_);
v___x_1074_ = v_reuseFailAlloc_1075_;
goto v_reusejp_1073_;
}
v_reusejp_1073_:
{
return v___x_1074_;
}
}
else
{
lean_object* v___x_1076_; 
lean_dec(v___x_1071_);
lean_del_object(v___x_1062_);
v___x_1076_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeSplit_mkBackwardRuleForLattice(v_c_1044_, v_as_1045_, v_excessArgs_1046_, v_resultType_x3f_1047_, v_a_1051_, v_a_1052_, v_a_1053_, v_a_1054_);
if (lean_obj_tag(v___x_1076_) == 0)
{
lean_object* v_a_1077_; lean_object* v___x_1078_; 
v_a_1077_ = lean_ctor_get(v___x_1076_, 0);
lean_inc(v_a_1077_);
lean_dec_ref_known(v___x_1076_, 1);
v___x_1078_ = l_Lean_Meta_Sym_BackwardRule_shareCommon(v_a_1077_, v_a_1049_, v_a_1050_, v_a_1051_, v_a_1052_, v_a_1053_, v_a_1054_);
if (lean_obj_tag(v___x_1078_) == 0)
{
lean_object* v_a_1079_; lean_object* v___x_1081_; uint8_t v_isShared_1082_; uint8_t v_isSharedCheck_1105_; 
v_a_1079_ = lean_ctor_get(v___x_1078_, 0);
v_isSharedCheck_1105_ = !lean_is_exclusive(v___x_1078_);
if (v_isSharedCheck_1105_ == 0)
{
v___x_1081_ = v___x_1078_;
v_isShared_1082_ = v_isSharedCheck_1105_;
goto v_resetjp_1080_;
}
else
{
lean_inc(v_a_1079_);
lean_dec(v___x_1078_);
v___x_1081_ = lean_box(0);
v_isShared_1082_ = v_isSharedCheck_1105_;
goto v_resetjp_1080_;
}
v_resetjp_1080_:
{
lean_object* v___x_1083_; lean_object* v_specBackwardRuleCache_1084_; lean_object* v_splitBackwardRuleCache_1085_; lean_object* v_latticeBackwardRuleCache_1086_; lean_object* v_frameDB_x3f_1087_; lean_object* v_invariants_1088_; lean_object* v_vcs_1089_; lean_object* v_simpState_1090_; lean_object* v_fuel_1091_; lean_object* v_inlineHandledInvariants_1092_; lean_object* v___x_1094_; uint8_t v_isShared_1095_; uint8_t v_isSharedCheck_1104_; 
v___x_1083_ = lean_st_ref_take(v_a_1048_);
v_specBackwardRuleCache_1084_ = lean_ctor_get(v___x_1083_, 0);
v_splitBackwardRuleCache_1085_ = lean_ctor_get(v___x_1083_, 1);
v_latticeBackwardRuleCache_1086_ = lean_ctor_get(v___x_1083_, 2);
v_frameDB_x3f_1087_ = lean_ctor_get(v___x_1083_, 3);
v_invariants_1088_ = lean_ctor_get(v___x_1083_, 4);
v_vcs_1089_ = lean_ctor_get(v___x_1083_, 5);
v_simpState_1090_ = lean_ctor_get(v___x_1083_, 6);
v_fuel_1091_ = lean_ctor_get(v___x_1083_, 7);
v_inlineHandledInvariants_1092_ = lean_ctor_get(v___x_1083_, 8);
v_isSharedCheck_1104_ = !lean_is_exclusive(v___x_1083_);
if (v_isSharedCheck_1104_ == 0)
{
v___x_1094_ = v___x_1083_;
v_isShared_1095_ = v_isSharedCheck_1104_;
goto v_resetjp_1093_;
}
else
{
lean_inc(v_inlineHandledInvariants_1092_);
lean_inc(v_fuel_1091_);
lean_inc(v_simpState_1090_);
lean_inc(v_vcs_1089_);
lean_inc(v_invariants_1088_);
lean_inc(v_frameDB_x3f_1087_);
lean_inc(v_latticeBackwardRuleCache_1086_);
lean_inc(v_splitBackwardRuleCache_1085_);
lean_inc(v_specBackwardRuleCache_1084_);
lean_dec(v___x_1083_);
v___x_1094_ = lean_box(0);
v_isShared_1095_ = v_isSharedCheck_1104_;
goto v_resetjp_1093_;
}
v_resetjp_1093_:
{
lean_object* v___x_1096_; lean_object* v___x_1098_; 
lean_inc(v_a_1079_);
v___x_1096_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__3___redArg(v_latticeBackwardRuleCache_1086_, v___x_1070_, v_a_1079_);
if (v_isShared_1095_ == 0)
{
lean_ctor_set(v___x_1094_, 2, v___x_1096_);
v___x_1098_ = v___x_1094_;
goto v_reusejp_1097_;
}
else
{
lean_object* v_reuseFailAlloc_1103_; 
v_reuseFailAlloc_1103_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1103_, 0, v_specBackwardRuleCache_1084_);
lean_ctor_set(v_reuseFailAlloc_1103_, 1, v_splitBackwardRuleCache_1085_);
lean_ctor_set(v_reuseFailAlloc_1103_, 2, v___x_1096_);
lean_ctor_set(v_reuseFailAlloc_1103_, 3, v_frameDB_x3f_1087_);
lean_ctor_set(v_reuseFailAlloc_1103_, 4, v_invariants_1088_);
lean_ctor_set(v_reuseFailAlloc_1103_, 5, v_vcs_1089_);
lean_ctor_set(v_reuseFailAlloc_1103_, 6, v_simpState_1090_);
lean_ctor_set(v_reuseFailAlloc_1103_, 7, v_fuel_1091_);
lean_ctor_set(v_reuseFailAlloc_1103_, 8, v_inlineHandledInvariants_1092_);
v___x_1098_ = v_reuseFailAlloc_1103_;
goto v_reusejp_1097_;
}
v_reusejp_1097_:
{
lean_object* v___x_1099_; lean_object* v___x_1101_; 
v___x_1099_ = lean_st_ref_set(v_a_1048_, v___x_1098_);
if (v_isShared_1082_ == 0)
{
v___x_1101_ = v___x_1081_;
goto v_reusejp_1100_;
}
else
{
lean_object* v_reuseFailAlloc_1102_; 
v_reuseFailAlloc_1102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1102_, 0, v_a_1079_);
v___x_1101_ = v_reuseFailAlloc_1102_;
goto v_reusejp_1100_;
}
v_reusejp_1100_:
{
return v___x_1101_;
}
}
}
}
}
else
{
lean_dec_ref_known(v___x_1070_, 2);
return v___x_1078_;
}
}
else
{
lean_dec_ref_known(v___x_1070_, 2);
return v___x_1076_;
}
}
}
}
else
{
lean_object* v_a_1107_; lean_object* v___x_1109_; uint8_t v_isShared_1110_; uint8_t v_isSharedCheck_1114_; 
lean_dec(v___x_1056_);
lean_dec(v_resultType_x3f_1047_);
lean_dec_ref(v_excessArgs_1046_);
lean_dec_ref(v_as_1045_);
lean_dec_ref(v_c_1044_);
v_a_1107_ = lean_ctor_get(v___x_1059_, 0);
v_isSharedCheck_1114_ = !lean_is_exclusive(v___x_1059_);
if (v_isSharedCheck_1114_ == 0)
{
v___x_1109_ = v___x_1059_;
v_isShared_1110_ = v_isSharedCheck_1114_;
goto v_resetjp_1108_;
}
else
{
lean_inc(v_a_1107_);
lean_dec(v___x_1059_);
v___x_1109_ = lean_box(0);
v_isShared_1110_ = v_isSharedCheck_1114_;
goto v_resetjp_1108_;
}
v_resetjp_1108_:
{
lean_object* v___x_1112_; 
if (v_isShared_1110_ == 0)
{
v___x_1112_ = v___x_1109_;
goto v_reusejp_1111_;
}
else
{
lean_object* v_reuseFailAlloc_1113_; 
v_reuseFailAlloc_1113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1113_, 0, v_a_1107_);
v___x_1112_ = v_reuseFailAlloc_1113_;
goto v_reusejp_1111_;
}
v_reusejp_1111_:
{
return v___x_1112_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached___redArg___boxed(lean_object* v_c_1115_, lean_object* v_as_1116_, lean_object* v_excessArgs_1117_, lean_object* v_resultType_x3f_1118_, lean_object* v_a_1119_, lean_object* v_a_1120_, lean_object* v_a_1121_, lean_object* v_a_1122_, lean_object* v_a_1123_, lean_object* v_a_1124_, lean_object* v_a_1125_, lean_object* v_a_1126_){
_start:
{
lean_object* v_res_1127_; 
v_res_1127_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached___redArg(v_c_1115_, v_as_1116_, v_excessArgs_1117_, v_resultType_x3f_1118_, v_a_1119_, v_a_1120_, v_a_1121_, v_a_1122_, v_a_1123_, v_a_1124_, v_a_1125_);
lean_dec(v_a_1125_);
lean_dec_ref(v_a_1124_);
lean_dec(v_a_1123_);
lean_dec_ref(v_a_1122_);
lean_dec(v_a_1121_);
lean_dec_ref(v_a_1120_);
lean_dec(v_a_1119_);
return v_res_1127_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached(lean_object* v_c_1128_, lean_object* v_as_1129_, lean_object* v_excessArgs_1130_, lean_object* v_resultType_x3f_1131_, lean_object* v_a_1132_, lean_object* v_a_1133_, lean_object* v_a_1134_, lean_object* v_a_1135_, lean_object* v_a_1136_, lean_object* v_a_1137_, lean_object* v_a_1138_, lean_object* v_a_1139_, lean_object* v_a_1140_, lean_object* v_a_1141_, lean_object* v_a_1142_){
_start:
{
lean_object* v___x_1144_; 
v___x_1144_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached___redArg(v_c_1128_, v_as_1129_, v_excessArgs_1130_, v_resultType_x3f_1131_, v_a_1133_, v_a_1137_, v_a_1138_, v_a_1139_, v_a_1140_, v_a_1141_, v_a_1142_);
return v___x_1144_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached___boxed(lean_object* v_c_1145_, lean_object* v_as_1146_, lean_object* v_excessArgs_1147_, lean_object* v_resultType_x3f_1148_, lean_object* v_a_1149_, lean_object* v_a_1150_, lean_object* v_a_1151_, lean_object* v_a_1152_, lean_object* v_a_1153_, lean_object* v_a_1154_, lean_object* v_a_1155_, lean_object* v_a_1156_, lean_object* v_a_1157_, lean_object* v_a_1158_, lean_object* v_a_1159_, lean_object* v_a_1160_){
_start:
{
lean_object* v_res_1161_; 
v_res_1161_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached(v_c_1145_, v_as_1146_, v_excessArgs_1147_, v_resultType_x3f_1148_, v_a_1149_, v_a_1150_, v_a_1151_, v_a_1152_, v_a_1153_, v_a_1154_, v_a_1155_, v_a_1156_, v_a_1157_, v_a_1158_, v_a_1159_);
lean_dec(v_a_1159_);
lean_dec_ref(v_a_1158_);
lean_dec(v_a_1157_);
lean_dec_ref(v_a_1156_);
lean_dec(v_a_1155_);
lean_dec_ref(v_a_1154_);
lean_dec(v_a_1153_);
lean_dec_ref(v_a_1152_);
lean_dec(v_a_1151_);
lean_dec(v_a_1150_);
lean_dec_ref(v_a_1149_);
return v_res_1161_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2(lean_object* v_00_u03b2_1162_, lean_object* v_m_1163_, lean_object* v_a_1164_){
_start:
{
lean_object* v___x_1165_; 
v___x_1165_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2___redArg(v_m_1163_, v_a_1164_);
return v___x_1165_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2___boxed(lean_object* v_00_u03b2_1166_, lean_object* v_m_1167_, lean_object* v_a_1168_){
_start:
{
lean_object* v_res_1169_; 
v_res_1169_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2(v_00_u03b2_1166_, v_m_1167_, v_a_1168_);
lean_dec_ref(v_a_1168_);
lean_dec_ref(v_m_1167_);
return v_res_1169_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__3(lean_object* v_00_u03b2_1170_, lean_object* v_m_1171_, lean_object* v_a_1172_, lean_object* v_b_1173_){
_start:
{
lean_object* v___x_1174_; 
v___x_1174_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__3___redArg(v_m_1171_, v_a_1172_, v_b_1173_);
return v___x_1174_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2_spec__2(lean_object* v_00_u03b2_1175_, lean_object* v_a_1176_, lean_object* v_x_1177_){
_start:
{
lean_object* v___x_1178_; 
v___x_1178_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2_spec__2___redArg(v_a_1176_, v_x_1177_);
return v___x_1178_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2_spec__2___boxed(lean_object* v_00_u03b2_1179_, lean_object* v_a_1180_, lean_object* v_x_1181_){
_start:
{
lean_object* v_res_1182_; 
v_res_1182_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2_spec__2(v_00_u03b2_1179_, v_a_1180_, v_x_1181_);
lean_dec(v_x_1181_);
lean_dec_ref(v_a_1180_);
return v_res_1182_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__3_spec__5(lean_object* v_00_u03b2_1183_, lean_object* v_a_1184_, lean_object* v_x_1185_){
_start:
{
uint8_t v___x_1186_; 
v___x_1186_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__3_spec__5___redArg(v_a_1184_, v_x_1185_);
return v___x_1186_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__3_spec__5___boxed(lean_object* v_00_u03b2_1187_, lean_object* v_a_1188_, lean_object* v_x_1189_){
_start:
{
uint8_t v_res_1190_; lean_object* v_r_1191_; 
v_res_1190_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__3_spec__5(v_00_u03b2_1187_, v_a_1188_, v_x_1189_);
lean_dec(v_x_1189_);
lean_dec_ref(v_a_1188_);
v_r_1191_ = lean_box(v_res_1190_);
return v_r_1191_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__3_spec__6(lean_object* v_00_u03b2_1192_, lean_object* v_data_1193_){
_start:
{
lean_object* v___x_1194_; 
v___x_1194_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__3_spec__6___redArg(v_data_1193_);
return v___x_1194_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__3_spec__7(lean_object* v_00_u03b2_1195_, lean_object* v_a_1196_, lean_object* v_b_1197_, lean_object* v_x_1198_){
_start:
{
lean_object* v___x_1199_; 
v___x_1199_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__3_spec__7___redArg(v_a_1196_, v_b_1197_, v_x_1198_);
return v___x_1199_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2_spec__2_spec__3(lean_object* v_xs_1200_, lean_object* v_ys_1201_, lean_object* v_hsz_1202_, lean_object* v_x_1203_, lean_object* v_x_1204_){
_start:
{
uint8_t v___x_1205_; 
v___x_1205_ = l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2_spec__2_spec__3___redArg(v_xs_1200_, v_ys_1201_, v_x_1203_);
return v___x_1205_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2_spec__2_spec__3___boxed(lean_object* v_xs_1206_, lean_object* v_ys_1207_, lean_object* v_hsz_1208_, lean_object* v_x_1209_, lean_object* v_x_1210_){
_start:
{
uint8_t v_res_1211_; lean_object* v_r_1212_; 
v_res_1211_ = l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2_spec__2_spec__3(v_xs_1206_, v_ys_1207_, v_hsz_1208_, v_x_1209_, v_x_1210_);
lean_dec_ref(v_ys_1207_);
lean_dec_ref(v_xs_1206_);
v_r_1212_ = lean_box(v_res_1211_);
return v_r_1212_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__3_spec__6_spec__8(lean_object* v_00_u03b2_1213_, lean_object* v_i_1214_, lean_object* v_source_1215_, lean_object* v_target_1216_){
_start:
{
lean_object* v___x_1217_; 
v___x_1217_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__3_spec__6_spec__8___redArg(v_i_1214_, v_source_1215_, v_target_1216_);
return v___x_1217_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__3_spec__6_spec__8_spec__9(lean_object* v_00_u03b2_1218_, lean_object* v_x_1219_, lean_object* v_x_1220_){
_start:
{
lean_object* v___x_1221_; 
v___x_1221_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__3_spec__6_spec__8_spec__9___redArg(v_x_1219_, v_x_1220_);
return v___x_1221_;
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
