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
uint8_t l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
uint64_t l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(lean_object*);
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
lean_object* v_fst_166_; lean_object* v_snd_167_; lean_object* v_fst_168_; lean_object* v_snd_169_; uint8_t v___x_170_; 
v_fst_166_ = lean_ctor_get(v_snd_162_, 0);
v_snd_167_ = lean_ctor_get(v_snd_162_, 1);
v_fst_168_ = lean_ctor_get(v_snd_164_, 0);
v_snd_169_ = lean_ctor_get(v_snd_164_, 1);
v___x_170_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_fst_166_, v_fst_168_);
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
v___x_187_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_fst_185_);
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
v___x_224_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_fst_222_);
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
v___x_285_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_fst_281_, v_fst_283_);
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
v___x_318_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_fst_314_, v_fst_316_);
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
v___x_336_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_fst_334_);
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
lean_object* v_a_411_; lean_object* v___x_413_; uint8_t v_isShared_414_; uint8_t v_isSharedCheck_468_; 
v_a_411_ = lean_ctor_get(v___x_410_, 0);
v_isSharedCheck_468_ = !lean_is_exclusive(v___x_410_);
if (v_isSharedCheck_468_ == 0)
{
v___x_413_ = v___x_410_;
v_isShared_414_ = v_isSharedCheck_468_;
goto v_resetjp_412_;
}
else
{
lean_inc(v_a_411_);
lean_dec(v___x_410_);
v___x_413_ = lean_box(0);
v_isShared_414_ = v_isSharedCheck_468_;
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
lean_object* v_val_420_; lean_object* v___x_422_; uint8_t v_isShared_423_; uint8_t v_isSharedCheck_463_; 
lean_del_object(v___x_413_);
v_val_420_ = lean_ctor_get(v_val_419_, 0);
v_isSharedCheck_463_ = !lean_is_exclusive(v_val_419_);
if (v_isSharedCheck_463_ == 0)
{
v___x_422_ = v_val_419_;
v_isShared_423_ = v_isSharedCheck_463_;
goto v_resetjp_421_;
}
else
{
lean_inc(v_val_420_);
lean_dec(v_val_419_);
v___x_422_ = lean_box(0);
v_isShared_423_ = v_isSharedCheck_463_;
goto v_resetjp_421_;
}
v_resetjp_421_:
{
lean_object* v___x_424_; 
v___x_424_ = l_Lean_Meta_Sym_BackwardRule_shareCommon(v_val_420_, v_a_389_, v_a_390_, v_a_391_, v_a_392_, v_a_393_, v_a_394_);
if (lean_obj_tag(v___x_424_) == 0)
{
lean_object* v_a_425_; lean_object* v___x_427_; uint8_t v_isShared_428_; uint8_t v_isSharedCheck_454_; 
v_a_425_ = lean_ctor_get(v___x_424_, 0);
v_isSharedCheck_454_ = !lean_is_exclusive(v___x_424_);
if (v_isSharedCheck_454_ == 0)
{
v___x_427_ = v___x_424_;
v_isShared_428_ = v_isSharedCheck_454_;
goto v_resetjp_426_;
}
else
{
lean_inc(v_a_425_);
lean_dec(v___x_424_);
v___x_427_ = lean_box(0);
v_isShared_428_ = v_isSharedCheck_454_;
goto v_resetjp_426_;
}
v_resetjp_426_:
{
lean_object* v___x_429_; lean_object* v_specBackwardRuleCache_430_; lean_object* v_splitBackwardRuleCache_431_; lean_object* v_latticeBackwardRuleCache_432_; lean_object* v_frameDB_x3f_433_; lean_object* v_invariants_434_; lean_object* v_vcs_435_; lean_object* v_simpState_436_; lean_object* v_fuel_437_; lean_object* v_inlineHandledInvariants_438_; lean_object* v___x_440_; uint8_t v_isShared_441_; uint8_t v_isSharedCheck_453_; 
v___x_429_ = lean_st_ref_take(v_a_385_);
v_specBackwardRuleCache_430_ = lean_ctor_get(v___x_429_, 0);
v_splitBackwardRuleCache_431_ = lean_ctor_get(v___x_429_, 1);
v_latticeBackwardRuleCache_432_ = lean_ctor_get(v___x_429_, 2);
v_frameDB_x3f_433_ = lean_ctor_get(v___x_429_, 3);
v_invariants_434_ = lean_ctor_get(v___x_429_, 4);
v_vcs_435_ = lean_ctor_get(v___x_429_, 5);
v_simpState_436_ = lean_ctor_get(v___x_429_, 6);
v_fuel_437_ = lean_ctor_get(v___x_429_, 7);
v_inlineHandledInvariants_438_ = lean_ctor_get(v___x_429_, 8);
v_isSharedCheck_453_ = !lean_is_exclusive(v___x_429_);
if (v_isSharedCheck_453_ == 0)
{
v___x_440_ = v___x_429_;
v_isShared_441_ = v_isSharedCheck_453_;
goto v_resetjp_439_;
}
else
{
lean_inc(v_inlineHandledInvariants_438_);
lean_inc(v_fuel_437_);
lean_inc(v_simpState_436_);
lean_inc(v_vcs_435_);
lean_inc(v_invariants_434_);
lean_inc(v_frameDB_x3f_433_);
lean_inc(v_latticeBackwardRuleCache_432_);
lean_inc(v_splitBackwardRuleCache_431_);
lean_inc(v_specBackwardRuleCache_430_);
lean_dec(v___x_429_);
v___x_440_ = lean_box(0);
v_isShared_441_ = v_isSharedCheck_453_;
goto v_resetjp_439_;
}
v_resetjp_439_:
{
lean_object* v___x_443_; 
lean_inc(v_a_425_);
if (v_isShared_423_ == 0)
{
lean_ctor_set(v___x_422_, 0, v_a_425_);
v___x_443_ = v___x_422_;
goto v_reusejp_442_;
}
else
{
lean_object* v_reuseFailAlloc_452_; 
v_reuseFailAlloc_452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_452_, 0, v_a_425_);
v___x_443_ = v_reuseFailAlloc_452_;
goto v_reusejp_442_;
}
v_reusejp_442_:
{
lean_object* v___x_444_; lean_object* v___x_446_; 
v___x_444_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2___redArg(v_specBackwardRuleCache_430_, v_key_404_, v_a_425_);
if (v_isShared_441_ == 0)
{
lean_ctor_set(v___x_440_, 0, v___x_444_);
v___x_446_ = v___x_440_;
goto v_reusejp_445_;
}
else
{
lean_object* v_reuseFailAlloc_451_; 
v_reuseFailAlloc_451_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_451_, 0, v___x_444_);
lean_ctor_set(v_reuseFailAlloc_451_, 1, v_splitBackwardRuleCache_431_);
lean_ctor_set(v_reuseFailAlloc_451_, 2, v_latticeBackwardRuleCache_432_);
lean_ctor_set(v_reuseFailAlloc_451_, 3, v_frameDB_x3f_433_);
lean_ctor_set(v_reuseFailAlloc_451_, 4, v_invariants_434_);
lean_ctor_set(v_reuseFailAlloc_451_, 5, v_vcs_435_);
lean_ctor_set(v_reuseFailAlloc_451_, 6, v_simpState_436_);
lean_ctor_set(v_reuseFailAlloc_451_, 7, v_fuel_437_);
lean_ctor_set(v_reuseFailAlloc_451_, 8, v_inlineHandledInvariants_438_);
v___x_446_ = v_reuseFailAlloc_451_;
goto v_reusejp_445_;
}
v_reusejp_445_:
{
lean_object* v___x_447_; lean_object* v___x_449_; 
v___x_447_ = lean_st_ref_set(v_a_385_, v___x_446_);
if (v_isShared_428_ == 0)
{
lean_ctor_set(v___x_427_, 0, v___x_443_);
v___x_449_ = v___x_427_;
goto v_reusejp_448_;
}
else
{
lean_object* v_reuseFailAlloc_450_; 
v_reuseFailAlloc_450_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_450_, 0, v___x_443_);
v___x_449_ = v_reuseFailAlloc_450_;
goto v_reusejp_448_;
}
v_reusejp_448_:
{
return v___x_449_;
}
}
}
}
}
}
else
{
lean_object* v_a_455_; lean_object* v___x_457_; uint8_t v_isShared_458_; uint8_t v_isSharedCheck_462_; 
lean_del_object(v___x_422_);
lean_dec_ref_known(v_key_404_, 2);
v_a_455_ = lean_ctor_get(v___x_424_, 0);
v_isSharedCheck_462_ = !lean_is_exclusive(v___x_424_);
if (v_isSharedCheck_462_ == 0)
{
v___x_457_ = v___x_424_;
v_isShared_458_ = v_isSharedCheck_462_;
goto v_resetjp_456_;
}
else
{
lean_inc(v_a_455_);
lean_dec(v___x_424_);
v___x_457_ = lean_box(0);
v_isShared_458_ = v_isSharedCheck_462_;
goto v_resetjp_456_;
}
v_resetjp_456_:
{
lean_object* v___x_460_; 
if (v_isShared_458_ == 0)
{
v___x_460_ = v___x_457_;
goto v_reusejp_459_;
}
else
{
lean_object* v_reuseFailAlloc_461_; 
v_reuseFailAlloc_461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_461_, 0, v_a_455_);
v___x_460_ = v_reuseFailAlloc_461_;
goto v_reusejp_459_;
}
v_reusejp_459_:
{
return v___x_460_;
}
}
}
}
}
else
{
lean_object* v___x_464_; lean_object* v___x_466_; 
lean_dec(v_val_419_);
lean_dec_ref_known(v_key_404_, 2);
v___x_464_ = lean_box(0);
if (v_isShared_414_ == 0)
{
lean_ctor_set(v___x_413_, 0, v___x_464_);
v___x_466_ = v___x_413_;
goto v_reusejp_465_;
}
else
{
lean_object* v_reuseFailAlloc_467_; 
v_reuseFailAlloc_467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_467_, 0, v___x_464_);
v___x_466_ = v_reuseFailAlloc_467_;
goto v_reusejp_465_;
}
v_reusejp_465_:
{
return v___x_466_;
}
}
}
}
}
else
{
lean_object* v_a_469_; lean_object* v___x_471_; uint8_t v_isShared_472_; uint8_t v_isSharedCheck_476_; 
lean_dec_ref_known(v_key_404_, 2);
v_a_469_ = lean_ctor_get(v___x_410_, 0);
v_isSharedCheck_476_ = !lean_is_exclusive(v___x_410_);
if (v_isSharedCheck_476_ == 0)
{
v___x_471_ = v___x_410_;
v_isShared_472_ = v_isSharedCheck_476_;
goto v_resetjp_470_;
}
else
{
lean_inc(v_a_469_);
lean_dec(v___x_410_);
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
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached___boxed(lean_object* v_specThm_477_, lean_object* v_info_478_, lean_object* v_a_479_, lean_object* v_a_480_, lean_object* v_a_481_, lean_object* v_a_482_, lean_object* v_a_483_, lean_object* v_a_484_, lean_object* v_a_485_, lean_object* v_a_486_, lean_object* v_a_487_, lean_object* v_a_488_, lean_object* v_a_489_, lean_object* v_a_490_){
_start:
{
lean_object* v_res_491_; 
v_res_491_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached(v_specThm_477_, v_info_478_, v_a_479_, v_a_480_, v_a_481_, v_a_482_, v_a_483_, v_a_484_, v_a_485_, v_a_486_, v_a_487_, v_a_488_, v_a_489_);
lean_dec(v_a_489_);
lean_dec_ref(v_a_488_);
lean_dec(v_a_487_);
lean_dec_ref(v_a_486_);
lean_dec(v_a_485_);
lean_dec_ref(v_a_484_);
lean_dec(v_a_483_);
lean_dec_ref(v_a_482_);
lean_dec(v_a_481_);
lean_dec(v_a_480_);
lean_dec_ref(v_a_479_);
return v_res_491_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0(lean_object* v_00_u03b2_492_, lean_object* v_m_493_, lean_object* v_a_494_){
_start:
{
lean_object* v___x_495_; 
v___x_495_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg(v_m_493_, v_a_494_);
return v___x_495_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___boxed(lean_object* v_00_u03b2_496_, lean_object* v_m_497_, lean_object* v_a_498_){
_start:
{
lean_object* v_res_499_; 
v_res_499_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0(v_00_u03b2_496_, v_m_497_, v_a_498_);
lean_dec_ref(v_a_498_);
lean_dec_ref(v_m_497_);
return v_res_499_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2(lean_object* v_00_u03b2_500_, lean_object* v_m_501_, lean_object* v_a_502_, lean_object* v_b_503_){
_start:
{
lean_object* v___x_504_; 
v___x_504_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2___redArg(v_m_501_, v_a_502_, v_b_503_);
return v___x_504_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0_spec__0(lean_object* v_00_u03b2_505_, lean_object* v_a_506_, lean_object* v_x_507_){
_start:
{
lean_object* v___x_508_; 
v___x_508_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0_spec__0___redArg(v_a_506_, v_x_507_);
return v___x_508_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0_spec__0___boxed(lean_object* v_00_u03b2_509_, lean_object* v_a_510_, lean_object* v_x_511_){
_start:
{
lean_object* v_res_512_; 
v_res_512_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0_spec__0(v_00_u03b2_509_, v_a_510_, v_x_511_);
lean_dec(v_x_511_);
lean_dec_ref(v_a_510_);
return v_res_512_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__3(lean_object* v_00_u03b2_513_, lean_object* v_a_514_, lean_object* v_x_515_){
_start:
{
uint8_t v___x_516_; 
v___x_516_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__3___redArg(v_a_514_, v_x_515_);
return v___x_516_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__3___boxed(lean_object* v_00_u03b2_517_, lean_object* v_a_518_, lean_object* v_x_519_){
_start:
{
uint8_t v_res_520_; lean_object* v_r_521_; 
v_res_520_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__3(v_00_u03b2_517_, v_a_518_, v_x_519_);
lean_dec(v_x_519_);
lean_dec_ref(v_a_518_);
v_r_521_ = lean_box(v_res_520_);
return v_r_521_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__4(lean_object* v_00_u03b2_522_, lean_object* v_data_523_){
_start:
{
lean_object* v___x_524_; 
v___x_524_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__4___redArg(v_data_523_);
return v___x_524_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__5(lean_object* v_00_u03b2_525_, lean_object* v_a_526_, lean_object* v_b_527_, lean_object* v_x_528_){
_start:
{
lean_object* v___x_529_; 
v___x_529_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__5___redArg(v_a_526_, v_b_527_, v_x_528_);
return v___x_529_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_530_, lean_object* v_i_531_, lean_object* v_source_532_, lean_object* v_target_533_){
_start:
{
lean_object* v___x_534_; 
v___x_534_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__4_spec__5___redArg(v_i_531_, v_source_532_, v_target_533_);
return v___x_534_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__4_spec__5_spec__6(lean_object* v_00_u03b2_535_, lean_object* v_x_536_, lean_object* v_x_537_){
_start:
{
lean_object* v___x_538_; 
v___x_538_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2_spec__4_spec__5_spec__6___redArg(v_x_536_, v_x_537_);
return v___x_538_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForSplitCached___redArg(lean_object* v_splitInfo_545_, lean_object* v_info_546_, lean_object* v_a_547_, lean_object* v_a_548_, lean_object* v_a_549_, lean_object* v_a_550_, lean_object* v_a_551_, lean_object* v_a_552_, lean_object* v_a_553_){
_start:
{
lean_object* v___y_556_; 
switch(lean_obj_tag(v_splitInfo_545_))
{
case 0:
{
lean_object* v___x_603_; 
v___x_603_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForSplitCached___redArg___closed__1));
v___y_556_ = v___x_603_;
goto v___jp_555_;
}
case 1:
{
lean_object* v___x_604_; 
v___x_604_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForSplitCached___redArg___closed__3));
v___y_556_ = v___x_604_;
goto v___jp_555_;
}
default: 
{
lean_object* v_matcherApp_605_; lean_object* v_matcherName_606_; 
v_matcherApp_605_ = lean_ctor_get(v_splitInfo_545_, 0);
v_matcherName_606_ = lean_ctor_get(v_matcherApp_605_, 1);
lean_inc(v_matcherName_606_);
v___y_556_ = v_matcherName_606_;
goto v___jp_555_;
}
}
v___jp_555_:
{
lean_object* v___x_557_; lean_object* v_excessArgs_558_; lean_object* v_splitBackwardRuleCache_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v_key_563_; lean_object* v___x_564_; 
v___x_557_ = lean_st_ref_get(v_a_547_);
v_excessArgs_558_ = lean_ctor_get(v_info_546_, 2);
v_splitBackwardRuleCache_559_ = lean_ctor_get(v___x_557_, 1);
lean_inc_ref(v_splitBackwardRuleCache_559_);
lean_dec(v___x_557_);
v___x_560_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_WPInfo_instWP(v_info_546_);
v___x_561_ = lean_array_get_size(v_excessArgs_558_);
v___x_562_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_562_, 0, v___x_560_);
lean_ctor_set(v___x_562_, 1, v___x_561_);
v_key_563_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_key_563_, 0, v___y_556_);
lean_ctor_set(v_key_563_, 1, v___x_562_);
v___x_564_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg(v_splitBackwardRuleCache_559_, v_key_563_);
lean_dec_ref(v_splitBackwardRuleCache_559_);
if (lean_obj_tag(v___x_564_) == 1)
{
lean_object* v_val_565_; lean_object* v___x_567_; uint8_t v_isShared_568_; uint8_t v_isSharedCheck_572_; 
lean_dec_ref_known(v_key_563_, 2);
lean_dec_ref(v_info_546_);
lean_dec_ref(v_splitInfo_545_);
v_val_565_ = lean_ctor_get(v___x_564_, 0);
v_isSharedCheck_572_ = !lean_is_exclusive(v___x_564_);
if (v_isSharedCheck_572_ == 0)
{
v___x_567_ = v___x_564_;
v_isShared_568_ = v_isSharedCheck_572_;
goto v_resetjp_566_;
}
else
{
lean_inc(v_val_565_);
lean_dec(v___x_564_);
v___x_567_ = lean_box(0);
v_isShared_568_ = v_isSharedCheck_572_;
goto v_resetjp_566_;
}
v_resetjp_566_:
{
lean_object* v___x_570_; 
if (v_isShared_568_ == 0)
{
lean_ctor_set_tag(v___x_567_, 0);
v___x_570_ = v___x_567_;
goto v_reusejp_569_;
}
else
{
lean_object* v_reuseFailAlloc_571_; 
v_reuseFailAlloc_571_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_571_, 0, v_val_565_);
v___x_570_ = v_reuseFailAlloc_571_;
goto v_reusejp_569_;
}
v_reusejp_569_:
{
return v___x_570_;
}
}
}
else
{
lean_object* v___x_573_; 
lean_dec(v___x_564_);
v___x_573_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForSplit(v_splitInfo_545_, v_info_546_, v_a_550_, v_a_551_, v_a_552_, v_a_553_);
if (lean_obj_tag(v___x_573_) == 0)
{
lean_object* v_a_574_; lean_object* v___x_575_; 
v_a_574_ = lean_ctor_get(v___x_573_, 0);
lean_inc(v_a_574_);
lean_dec_ref_known(v___x_573_, 1);
v___x_575_ = l_Lean_Meta_Sym_BackwardRule_shareCommon(v_a_574_, v_a_548_, v_a_549_, v_a_550_, v_a_551_, v_a_552_, v_a_553_);
if (lean_obj_tag(v___x_575_) == 0)
{
lean_object* v_a_576_; lean_object* v___x_578_; uint8_t v_isShared_579_; uint8_t v_isSharedCheck_602_; 
v_a_576_ = lean_ctor_get(v___x_575_, 0);
v_isSharedCheck_602_ = !lean_is_exclusive(v___x_575_);
if (v_isSharedCheck_602_ == 0)
{
v___x_578_ = v___x_575_;
v_isShared_579_ = v_isSharedCheck_602_;
goto v_resetjp_577_;
}
else
{
lean_inc(v_a_576_);
lean_dec(v___x_575_);
v___x_578_ = lean_box(0);
v_isShared_579_ = v_isSharedCheck_602_;
goto v_resetjp_577_;
}
v_resetjp_577_:
{
lean_object* v___x_580_; lean_object* v_specBackwardRuleCache_581_; lean_object* v_splitBackwardRuleCache_582_; lean_object* v_latticeBackwardRuleCache_583_; lean_object* v_frameDB_x3f_584_; lean_object* v_invariants_585_; lean_object* v_vcs_586_; lean_object* v_simpState_587_; lean_object* v_fuel_588_; lean_object* v_inlineHandledInvariants_589_; lean_object* v___x_591_; uint8_t v_isShared_592_; uint8_t v_isSharedCheck_601_; 
v___x_580_ = lean_st_ref_take(v_a_547_);
v_specBackwardRuleCache_581_ = lean_ctor_get(v___x_580_, 0);
v_splitBackwardRuleCache_582_ = lean_ctor_get(v___x_580_, 1);
v_latticeBackwardRuleCache_583_ = lean_ctor_get(v___x_580_, 2);
v_frameDB_x3f_584_ = lean_ctor_get(v___x_580_, 3);
v_invariants_585_ = lean_ctor_get(v___x_580_, 4);
v_vcs_586_ = lean_ctor_get(v___x_580_, 5);
v_simpState_587_ = lean_ctor_get(v___x_580_, 6);
v_fuel_588_ = lean_ctor_get(v___x_580_, 7);
v_inlineHandledInvariants_589_ = lean_ctor_get(v___x_580_, 8);
v_isSharedCheck_601_ = !lean_is_exclusive(v___x_580_);
if (v_isSharedCheck_601_ == 0)
{
v___x_591_ = v___x_580_;
v_isShared_592_ = v_isSharedCheck_601_;
goto v_resetjp_590_;
}
else
{
lean_inc(v_inlineHandledInvariants_589_);
lean_inc(v_fuel_588_);
lean_inc(v_simpState_587_);
lean_inc(v_vcs_586_);
lean_inc(v_invariants_585_);
lean_inc(v_frameDB_x3f_584_);
lean_inc(v_latticeBackwardRuleCache_583_);
lean_inc(v_splitBackwardRuleCache_582_);
lean_inc(v_specBackwardRuleCache_581_);
lean_dec(v___x_580_);
v___x_591_ = lean_box(0);
v_isShared_592_ = v_isSharedCheck_601_;
goto v_resetjp_590_;
}
v_resetjp_590_:
{
lean_object* v___x_593_; lean_object* v___x_595_; 
lean_inc(v_a_576_);
v___x_593_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__2___redArg(v_splitBackwardRuleCache_582_, v_key_563_, v_a_576_);
if (v_isShared_592_ == 0)
{
lean_ctor_set(v___x_591_, 1, v___x_593_);
v___x_595_ = v___x_591_;
goto v_reusejp_594_;
}
else
{
lean_object* v_reuseFailAlloc_600_; 
v_reuseFailAlloc_600_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_600_, 0, v_specBackwardRuleCache_581_);
lean_ctor_set(v_reuseFailAlloc_600_, 1, v___x_593_);
lean_ctor_set(v_reuseFailAlloc_600_, 2, v_latticeBackwardRuleCache_583_);
lean_ctor_set(v_reuseFailAlloc_600_, 3, v_frameDB_x3f_584_);
lean_ctor_set(v_reuseFailAlloc_600_, 4, v_invariants_585_);
lean_ctor_set(v_reuseFailAlloc_600_, 5, v_vcs_586_);
lean_ctor_set(v_reuseFailAlloc_600_, 6, v_simpState_587_);
lean_ctor_set(v_reuseFailAlloc_600_, 7, v_fuel_588_);
lean_ctor_set(v_reuseFailAlloc_600_, 8, v_inlineHandledInvariants_589_);
v___x_595_ = v_reuseFailAlloc_600_;
goto v_reusejp_594_;
}
v_reusejp_594_:
{
lean_object* v___x_596_; lean_object* v___x_598_; 
v___x_596_ = lean_st_ref_set(v_a_547_, v___x_595_);
if (v_isShared_579_ == 0)
{
v___x_598_ = v___x_578_;
goto v_reusejp_597_;
}
else
{
lean_object* v_reuseFailAlloc_599_; 
v_reuseFailAlloc_599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_599_, 0, v_a_576_);
v___x_598_ = v_reuseFailAlloc_599_;
goto v_reusejp_597_;
}
v_reusejp_597_:
{
return v___x_598_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_key_563_, 2);
return v___x_575_;
}
}
else
{
lean_dec_ref_known(v_key_563_, 2);
return v___x_573_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForSplitCached___redArg___boxed(lean_object* v_splitInfo_607_, lean_object* v_info_608_, lean_object* v_a_609_, lean_object* v_a_610_, lean_object* v_a_611_, lean_object* v_a_612_, lean_object* v_a_613_, lean_object* v_a_614_, lean_object* v_a_615_, lean_object* v_a_616_){
_start:
{
lean_object* v_res_617_; 
v_res_617_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForSplitCached___redArg(v_splitInfo_607_, v_info_608_, v_a_609_, v_a_610_, v_a_611_, v_a_612_, v_a_613_, v_a_614_, v_a_615_);
lean_dec(v_a_615_);
lean_dec_ref(v_a_614_);
lean_dec(v_a_613_);
lean_dec_ref(v_a_612_);
lean_dec(v_a_611_);
lean_dec_ref(v_a_610_);
lean_dec(v_a_609_);
return v_res_617_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForSplitCached(lean_object* v_splitInfo_618_, lean_object* v_info_619_, lean_object* v_a_620_, lean_object* v_a_621_, lean_object* v_a_622_, lean_object* v_a_623_, lean_object* v_a_624_, lean_object* v_a_625_, lean_object* v_a_626_, lean_object* v_a_627_, lean_object* v_a_628_, lean_object* v_a_629_, lean_object* v_a_630_){
_start:
{
lean_object* v___x_632_; 
v___x_632_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForSplitCached___redArg(v_splitInfo_618_, v_info_619_, v_a_621_, v_a_625_, v_a_626_, v_a_627_, v_a_628_, v_a_629_, v_a_630_);
return v___x_632_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForSplitCached___boxed(lean_object* v_splitInfo_633_, lean_object* v_info_634_, lean_object* v_a_635_, lean_object* v_a_636_, lean_object* v_a_637_, lean_object* v_a_638_, lean_object* v_a_639_, lean_object* v_a_640_, lean_object* v_a_641_, lean_object* v_a_642_, lean_object* v_a_643_, lean_object* v_a_644_, lean_object* v_a_645_, lean_object* v_a_646_){
_start:
{
lean_object* v_res_647_; 
v_res_647_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForSplitCached(v_splitInfo_633_, v_info_634_, v_a_635_, v_a_636_, v_a_637_, v_a_638_, v_a_639_, v_a_640_, v_a_641_, v_a_642_, v_a_643_, v_a_644_, v_a_645_);
lean_dec(v_a_645_);
lean_dec_ref(v_a_644_);
lean_dec(v_a_643_);
lean_dec_ref(v_a_642_);
lean_dec(v_a_641_);
lean_dec_ref(v_a_640_);
lean_dec(v_a_639_);
lean_dec_ref(v_a_638_);
lean_dec(v_a_637_);
lean_dec(v_a_636_);
lean_dec_ref(v_a_635_);
return v_res_647_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__0(size_t v_sz_648_, size_t v_i_649_, lean_object* v_bs_650_, lean_object* v___y_651_, lean_object* v___y_652_, lean_object* v___y_653_, lean_object* v___y_654_, lean_object* v___y_655_, lean_object* v___y_656_){
_start:
{
uint8_t v___x_658_; 
v___x_658_ = lean_usize_dec_lt(v_i_649_, v_sz_648_);
if (v___x_658_ == 0)
{
lean_object* v___x_659_; 
v___x_659_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_659_, 0, v_bs_650_);
return v___x_659_;
}
else
{
lean_object* v_v_660_; lean_object* v___x_661_; 
v_v_660_ = lean_array_uget_borrowed(v_bs_650_, v_i_649_);
lean_inc(v_v_660_);
v___x_661_ = l_Lean_Meta_Sym_inferType(v_v_660_, v___y_651_, v___y_652_, v___y_653_, v___y_654_, v___y_655_, v___y_656_);
if (lean_obj_tag(v___x_661_) == 0)
{
lean_object* v_a_662_; lean_object* v___x_663_; lean_object* v_bs_x27_664_; size_t v___x_665_; size_t v___x_666_; lean_object* v___x_667_; 
v_a_662_ = lean_ctor_get(v___x_661_, 0);
lean_inc(v_a_662_);
lean_dec_ref_known(v___x_661_, 1);
v___x_663_ = lean_unsigned_to_nat(0u);
v_bs_x27_664_ = lean_array_uset(v_bs_650_, v_i_649_, v___x_663_);
v___x_665_ = ((size_t)1ULL);
v___x_666_ = lean_usize_add(v_i_649_, v___x_665_);
v___x_667_ = lean_array_uset(v_bs_x27_664_, v_i_649_, v_a_662_);
v_i_649_ = v___x_666_;
v_bs_650_ = v___x_667_;
goto _start;
}
else
{
lean_object* v_a_669_; lean_object* v___x_671_; uint8_t v_isShared_672_; uint8_t v_isSharedCheck_676_; 
lean_dec_ref(v_bs_650_);
v_a_669_ = lean_ctor_get(v___x_661_, 0);
v_isSharedCheck_676_ = !lean_is_exclusive(v___x_661_);
if (v_isSharedCheck_676_ == 0)
{
v___x_671_ = v___x_661_;
v_isShared_672_ = v_isSharedCheck_676_;
goto v_resetjp_670_;
}
else
{
lean_inc(v_a_669_);
lean_dec(v___x_661_);
v___x_671_ = lean_box(0);
v_isShared_672_ = v_isSharedCheck_676_;
goto v_resetjp_670_;
}
v_resetjp_670_:
{
lean_object* v___x_674_; 
if (v_isShared_672_ == 0)
{
v___x_674_ = v___x_671_;
goto v_reusejp_673_;
}
else
{
lean_object* v_reuseFailAlloc_675_; 
v_reuseFailAlloc_675_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_675_, 0, v_a_669_);
v___x_674_ = v_reuseFailAlloc_675_;
goto v_reusejp_673_;
}
v_reusejp_673_:
{
return v___x_674_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__0___boxed(lean_object* v_sz_677_, lean_object* v_i_678_, lean_object* v_bs_679_, lean_object* v___y_680_, lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_){
_start:
{
size_t v_sz_boxed_687_; size_t v_i_boxed_688_; lean_object* v_res_689_; 
v_sz_boxed_687_ = lean_unbox_usize(v_sz_677_);
lean_dec(v_sz_677_);
v_i_boxed_688_ = lean_unbox_usize(v_i_678_);
lean_dec(v_i_678_);
v_res_689_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__0(v_sz_boxed_687_, v_i_boxed_688_, v_bs_679_, v___y_680_, v___y_681_, v___y_682_, v___y_683_, v___y_684_, v___y_685_);
lean_dec(v___y_685_);
lean_dec_ref(v___y_684_);
lean_dec(v___y_683_);
lean_dec_ref(v___y_682_);
lean_dec(v___y_681_);
lean_dec_ref(v___y_680_);
return v_res_689_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2_spec__2_spec__3___redArg(lean_object* v_xs_690_, lean_object* v_ys_691_, lean_object* v_x_692_){
_start:
{
lean_object* v_zero_693_; uint8_t v_isZero_694_; 
v_zero_693_ = lean_unsigned_to_nat(0u);
v_isZero_694_ = lean_nat_dec_eq(v_x_692_, v_zero_693_);
if (v_isZero_694_ == 1)
{
lean_dec(v_x_692_);
return v_isZero_694_;
}
else
{
lean_object* v_one_695_; lean_object* v_n_696_; lean_object* v___x_697_; lean_object* v___x_698_; uint8_t v___x_699_; 
v_one_695_ = lean_unsigned_to_nat(1u);
v_n_696_ = lean_nat_sub(v_x_692_, v_one_695_);
lean_dec(v_x_692_);
v___x_697_ = lean_array_fget_borrowed(v_xs_690_, v_n_696_);
v___x_698_ = lean_array_fget_borrowed(v_ys_691_, v_n_696_);
v___x_699_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v___x_697_, v___x_698_);
if (v___x_699_ == 0)
{
lean_dec(v_n_696_);
return v___x_699_;
}
else
{
v_x_692_ = v_n_696_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2_spec__2_spec__3___redArg___boxed(lean_object* v_xs_701_, lean_object* v_ys_702_, lean_object* v_x_703_){
_start:
{
uint8_t v_res_704_; lean_object* v_r_705_; 
v_res_704_ = l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2_spec__2_spec__3___redArg(v_xs_701_, v_ys_702_, v_x_703_);
lean_dec_ref(v_ys_702_);
lean_dec_ref(v_xs_701_);
v_r_705_ = lean_box(v_res_704_);
return v_r_705_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2_spec__2___redArg(lean_object* v_a_706_, lean_object* v_x_707_){
_start:
{
if (lean_obj_tag(v_x_707_) == 0)
{
lean_object* v___x_708_; 
v___x_708_ = lean_box(0);
return v___x_708_;
}
else
{
lean_object* v_key_709_; lean_object* v_value_710_; lean_object* v_tail_711_; uint8_t v___y_713_; lean_object* v_fst_716_; lean_object* v_snd_717_; lean_object* v_fst_718_; lean_object* v_snd_719_; uint8_t v___x_720_; 
v_key_709_ = lean_ctor_get(v_x_707_, 0);
v_value_710_ = lean_ctor_get(v_x_707_, 1);
v_tail_711_ = lean_ctor_get(v_x_707_, 2);
v_fst_716_ = lean_ctor_get(v_key_709_, 0);
v_snd_717_ = lean_ctor_get(v_key_709_, 1);
v_fst_718_ = lean_ctor_get(v_a_706_, 0);
v_snd_719_ = lean_ctor_get(v_a_706_, 1);
v___x_720_ = lean_name_eq(v_fst_716_, v_fst_718_);
if (v___x_720_ == 0)
{
v___y_713_ = v___x_720_;
goto v___jp_712_;
}
else
{
lean_object* v_fst_721_; lean_object* v_snd_722_; lean_object* v_fst_723_; lean_object* v_snd_724_; lean_object* v___x_725_; lean_object* v___x_726_; uint8_t v___x_727_; 
v_fst_721_ = lean_ctor_get(v_snd_717_, 0);
v_snd_722_ = lean_ctor_get(v_snd_717_, 1);
v_fst_723_ = lean_ctor_get(v_snd_719_, 0);
v_snd_724_ = lean_ctor_get(v_snd_719_, 1);
v___x_725_ = lean_array_get_size(v_fst_721_);
v___x_726_ = lean_array_get_size(v_fst_723_);
v___x_727_ = lean_nat_dec_eq(v___x_725_, v___x_726_);
if (v___x_727_ == 0)
{
v_x_707_ = v_tail_711_;
goto _start;
}
else
{
uint8_t v___x_729_; 
v___x_729_ = l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2_spec__2_spec__3___redArg(v_fst_721_, v_fst_723_, v___x_725_);
if (v___x_729_ == 0)
{
v_x_707_ = v_tail_711_;
goto _start;
}
else
{
uint8_t v___x_731_; 
v___x_731_ = lean_nat_dec_eq(v_snd_722_, v_snd_724_);
v___y_713_ = v___x_731_;
goto v___jp_712_;
}
}
}
v___jp_712_:
{
if (v___y_713_ == 0)
{
v_x_707_ = v_tail_711_;
goto _start;
}
else
{
lean_object* v___x_715_; 
lean_inc(v_value_710_);
v___x_715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_715_, 0, v_value_710_);
return v___x_715_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2_spec__2___redArg___boxed(lean_object* v_a_732_, lean_object* v_x_733_){
_start:
{
lean_object* v_res_734_; 
v_res_734_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2_spec__2___redArg(v_a_732_, v_x_733_);
lean_dec(v_x_733_);
lean_dec_ref(v_a_732_);
return v_res_734_;
}
}
LEAN_EXPORT uint64_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2_spec__3(lean_object* v_as_735_, size_t v_i_736_, size_t v_stop_737_, uint64_t v_b_738_){
_start:
{
uint8_t v___x_739_; 
v___x_739_ = lean_usize_dec_eq(v_i_736_, v_stop_737_);
if (v___x_739_ == 0)
{
lean_object* v___x_740_; uint64_t v___x_741_; uint64_t v___x_742_; size_t v___x_743_; size_t v___x_744_; 
v___x_740_ = lean_array_uget_borrowed(v_as_735_, v_i_736_);
v___x_741_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v___x_740_);
v___x_742_ = lean_uint64_mix_hash(v_b_738_, v___x_741_);
v___x_743_ = ((size_t)1ULL);
v___x_744_ = lean_usize_add(v_i_736_, v___x_743_);
v_i_736_ = v___x_744_;
v_b_738_ = v___x_742_;
goto _start;
}
else
{
return v_b_738_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2_spec__3___boxed(lean_object* v_as_746_, lean_object* v_i_747_, lean_object* v_stop_748_, lean_object* v_b_749_){
_start:
{
size_t v_i_boxed_750_; size_t v_stop_boxed_751_; uint64_t v_b_boxed_752_; uint64_t v_res_753_; lean_object* v_r_754_; 
v_i_boxed_750_ = lean_unbox_usize(v_i_747_);
lean_dec(v_i_747_);
v_stop_boxed_751_ = lean_unbox_usize(v_stop_748_);
lean_dec(v_stop_748_);
v_b_boxed_752_ = lean_unbox_uint64(v_b_749_);
lean_dec_ref(v_b_749_);
v_res_753_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2_spec__3(v_as_746_, v_i_boxed_750_, v_stop_boxed_751_, v_b_boxed_752_);
lean_dec_ref(v_as_746_);
v_r_754_ = lean_box_uint64(v_res_753_);
return v_r_754_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2___redArg(lean_object* v_m_755_, lean_object* v_a_756_){
_start:
{
lean_object* v_buckets_757_; lean_object* v_fst_758_; lean_object* v_snd_759_; lean_object* v___x_760_; uint64_t v___y_762_; lean_object* v___y_763_; uint64_t v___y_764_; uint64_t v___y_782_; 
v_buckets_757_ = lean_ctor_get(v_m_755_, 1);
v_fst_758_ = lean_ctor_get(v_a_756_, 0);
v_snd_759_ = lean_ctor_get(v_a_756_, 1);
v___x_760_ = lean_array_get_size(v_buckets_757_);
if (lean_obj_tag(v_fst_758_) == 0)
{
uint64_t v___x_796_; 
v___x_796_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg___closed__0);
v___y_782_ = v___x_796_;
goto v___jp_781_;
}
else
{
uint64_t v_hash_797_; 
v_hash_797_ = lean_ctor_get_uint64(v_fst_758_, sizeof(void*)*2);
v___y_782_ = v_hash_797_;
goto v___jp_781_;
}
v___jp_761_:
{
uint64_t v___x_765_; uint64_t v___x_766_; uint64_t v___x_767_; uint64_t v___x_768_; uint64_t v___x_769_; uint64_t v_fold_770_; uint64_t v___x_771_; uint64_t v___x_772_; uint64_t v___x_773_; size_t v___x_774_; size_t v___x_775_; size_t v___x_776_; size_t v___x_777_; size_t v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; 
v___x_765_ = lean_uint64_of_nat(v___y_763_);
v___x_766_ = lean_uint64_mix_hash(v___y_764_, v___x_765_);
v___x_767_ = lean_uint64_mix_hash(v___y_762_, v___x_766_);
v___x_768_ = 32ULL;
v___x_769_ = lean_uint64_shift_right(v___x_767_, v___x_768_);
v_fold_770_ = lean_uint64_xor(v___x_767_, v___x_769_);
v___x_771_ = 16ULL;
v___x_772_ = lean_uint64_shift_right(v_fold_770_, v___x_771_);
v___x_773_ = lean_uint64_xor(v_fold_770_, v___x_772_);
v___x_774_ = lean_uint64_to_usize(v___x_773_);
v___x_775_ = lean_usize_of_nat(v___x_760_);
v___x_776_ = ((size_t)1ULL);
v___x_777_ = lean_usize_sub(v___x_775_, v___x_776_);
v___x_778_ = lean_usize_land(v___x_774_, v___x_777_);
v___x_779_ = lean_array_uget_borrowed(v_buckets_757_, v___x_778_);
v___x_780_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2_spec__2___redArg(v_a_756_, v___x_779_);
return v___x_780_;
}
v___jp_781_:
{
lean_object* v_fst_783_; lean_object* v_snd_784_; uint64_t v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; uint8_t v___x_788_; 
v_fst_783_ = lean_ctor_get(v_snd_759_, 0);
v_snd_784_ = lean_ctor_get(v_snd_759_, 1);
v___x_785_ = 7ULL;
v___x_786_ = lean_unsigned_to_nat(0u);
v___x_787_ = lean_array_get_size(v_fst_783_);
v___x_788_ = lean_nat_dec_lt(v___x_786_, v___x_787_);
if (v___x_788_ == 0)
{
v___y_762_ = v___y_782_;
v___y_763_ = v_snd_784_;
v___y_764_ = v___x_785_;
goto v___jp_761_;
}
else
{
uint8_t v___x_789_; 
v___x_789_ = lean_nat_dec_le(v___x_787_, v___x_787_);
if (v___x_789_ == 0)
{
if (v___x_788_ == 0)
{
v___y_762_ = v___y_782_;
v___y_763_ = v_snd_784_;
v___y_764_ = v___x_785_;
goto v___jp_761_;
}
else
{
size_t v___x_790_; size_t v___x_791_; uint64_t v___x_792_; 
v___x_790_ = ((size_t)0ULL);
v___x_791_ = lean_usize_of_nat(v___x_787_);
v___x_792_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2_spec__3(v_fst_783_, v___x_790_, v___x_791_, v___x_785_);
v___y_762_ = v___y_782_;
v___y_763_ = v_snd_784_;
v___y_764_ = v___x_792_;
goto v___jp_761_;
}
}
else
{
size_t v___x_793_; size_t v___x_794_; uint64_t v___x_795_; 
v___x_793_ = ((size_t)0ULL);
v___x_794_ = lean_usize_of_nat(v___x_787_);
v___x_795_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2_spec__3(v_fst_783_, v___x_793_, v___x_794_, v___x_785_);
v___y_762_ = v___y_782_;
v___y_763_ = v_snd_784_;
v___y_764_ = v___x_795_;
goto v___jp_761_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2___redArg___boxed(lean_object* v_m_798_, lean_object* v_a_799_){
_start:
{
lean_object* v_res_800_; 
v_res_800_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2___redArg(v_m_798_, v_a_799_);
lean_dec_ref(v_a_799_);
lean_dec_ref(v_m_798_);
return v_res_800_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__1(size_t v_sz_801_, size_t v_i_802_, lean_object* v_bs_803_){
_start:
{
uint8_t v___x_804_; 
v___x_804_ = lean_usize_dec_lt(v_i_802_, v_sz_801_);
if (v___x_804_ == 0)
{
return v_bs_803_;
}
else
{
lean_object* v_v_805_; lean_object* v___x_806_; lean_object* v_bs_x27_807_; size_t v___x_808_; size_t v___x_809_; lean_object* v___x_810_; 
v_v_805_ = lean_array_uget(v_bs_803_, v_i_802_);
v___x_806_ = lean_unsigned_to_nat(0u);
v_bs_x27_807_ = lean_array_uset(v_bs_803_, v_i_802_, v___x_806_);
v___x_808_ = ((size_t)1ULL);
v___x_809_ = lean_usize_add(v_i_802_, v___x_808_);
v___x_810_ = lean_array_uset(v_bs_x27_807_, v_i_802_, v_v_805_);
v_i_802_ = v___x_809_;
v_bs_803_ = v___x_810_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__1___boxed(lean_object* v_sz_812_, lean_object* v_i_813_, lean_object* v_bs_814_){
_start:
{
size_t v_sz_boxed_815_; size_t v_i_boxed_816_; lean_object* v_res_817_; 
v_sz_boxed_815_ = lean_unbox_usize(v_sz_812_);
lean_dec(v_sz_812_);
v_i_boxed_816_ = lean_unbox_usize(v_i_813_);
lean_dec(v_i_813_);
v_res_817_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__1(v_sz_boxed_815_, v_i_boxed_816_, v_bs_814_);
return v_res_817_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__3_spec__6_spec__8_spec__9___redArg(lean_object* v_x_818_, lean_object* v_x_819_){
_start:
{
if (lean_obj_tag(v_x_819_) == 0)
{
return v_x_818_;
}
else
{
lean_object* v_key_820_; lean_object* v_value_821_; lean_object* v_tail_822_; lean_object* v___x_824_; uint8_t v_isShared_825_; uint8_t v_isSharedCheck_870_; 
v_key_820_ = lean_ctor_get(v_x_819_, 0);
v_value_821_ = lean_ctor_get(v_x_819_, 1);
v_tail_822_ = lean_ctor_get(v_x_819_, 2);
v_isSharedCheck_870_ = !lean_is_exclusive(v_x_819_);
if (v_isSharedCheck_870_ == 0)
{
v___x_824_ = v_x_819_;
v_isShared_825_ = v_isSharedCheck_870_;
goto v_resetjp_823_;
}
else
{
lean_inc(v_tail_822_);
lean_inc(v_value_821_);
lean_inc(v_key_820_);
lean_dec(v_x_819_);
v___x_824_ = lean_box(0);
v_isShared_825_ = v_isSharedCheck_870_;
goto v_resetjp_823_;
}
v_resetjp_823_:
{
lean_object* v_fst_826_; lean_object* v_snd_827_; lean_object* v___x_828_; uint64_t v___y_830_; lean_object* v___y_831_; uint64_t v___y_832_; uint64_t v___y_854_; 
v_fst_826_ = lean_ctor_get(v_key_820_, 0);
v_snd_827_ = lean_ctor_get(v_key_820_, 1);
v___x_828_ = lean_array_get_size(v_x_818_);
if (lean_obj_tag(v_fst_826_) == 0)
{
uint64_t v___x_868_; 
v___x_868_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg___closed__0);
v___y_854_ = v___x_868_;
goto v___jp_853_;
}
else
{
uint64_t v_hash_869_; 
v_hash_869_ = lean_ctor_get_uint64(v_fst_826_, sizeof(void*)*2);
v___y_854_ = v_hash_869_;
goto v___jp_853_;
}
v___jp_829_:
{
uint64_t v___x_833_; uint64_t v___x_834_; uint64_t v___x_835_; uint64_t v___x_836_; uint64_t v___x_837_; uint64_t v_fold_838_; uint64_t v___x_839_; uint64_t v___x_840_; uint64_t v___x_841_; size_t v___x_842_; size_t v___x_843_; size_t v___x_844_; size_t v___x_845_; size_t v___x_846_; lean_object* v___x_847_; lean_object* v___x_849_; 
v___x_833_ = lean_uint64_of_nat(v___y_831_);
lean_dec(v___y_831_);
v___x_834_ = lean_uint64_mix_hash(v___y_832_, v___x_833_);
v___x_835_ = lean_uint64_mix_hash(v___y_830_, v___x_834_);
v___x_836_ = 32ULL;
v___x_837_ = lean_uint64_shift_right(v___x_835_, v___x_836_);
v_fold_838_ = lean_uint64_xor(v___x_835_, v___x_837_);
v___x_839_ = 16ULL;
v___x_840_ = lean_uint64_shift_right(v_fold_838_, v___x_839_);
v___x_841_ = lean_uint64_xor(v_fold_838_, v___x_840_);
v___x_842_ = lean_uint64_to_usize(v___x_841_);
v___x_843_ = lean_usize_of_nat(v___x_828_);
v___x_844_ = ((size_t)1ULL);
v___x_845_ = lean_usize_sub(v___x_843_, v___x_844_);
v___x_846_ = lean_usize_land(v___x_842_, v___x_845_);
v___x_847_ = lean_array_uget_borrowed(v_x_818_, v___x_846_);
lean_inc(v___x_847_);
if (v_isShared_825_ == 0)
{
lean_ctor_set(v___x_824_, 2, v___x_847_);
v___x_849_ = v___x_824_;
goto v_reusejp_848_;
}
else
{
lean_object* v_reuseFailAlloc_852_; 
v_reuseFailAlloc_852_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_852_, 0, v_key_820_);
lean_ctor_set(v_reuseFailAlloc_852_, 1, v_value_821_);
lean_ctor_set(v_reuseFailAlloc_852_, 2, v___x_847_);
v___x_849_ = v_reuseFailAlloc_852_;
goto v_reusejp_848_;
}
v_reusejp_848_:
{
lean_object* v___x_850_; 
v___x_850_ = lean_array_uset(v_x_818_, v___x_846_, v___x_849_);
v_x_818_ = v___x_850_;
v_x_819_ = v_tail_822_;
goto _start;
}
}
v___jp_853_:
{
lean_object* v_fst_855_; lean_object* v_snd_856_; uint64_t v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; uint8_t v___x_860_; 
v_fst_855_ = lean_ctor_get(v_snd_827_, 0);
v_snd_856_ = lean_ctor_get(v_snd_827_, 1);
v___x_857_ = 7ULL;
v___x_858_ = lean_unsigned_to_nat(0u);
v___x_859_ = lean_array_get_size(v_fst_855_);
v___x_860_ = lean_nat_dec_lt(v___x_858_, v___x_859_);
if (v___x_860_ == 0)
{
lean_inc(v_snd_856_);
v___y_830_ = v___y_854_;
v___y_831_ = v_snd_856_;
v___y_832_ = v___x_857_;
goto v___jp_829_;
}
else
{
uint8_t v___x_861_; 
v___x_861_ = lean_nat_dec_le(v___x_859_, v___x_859_);
if (v___x_861_ == 0)
{
if (v___x_860_ == 0)
{
lean_inc(v_snd_856_);
v___y_830_ = v___y_854_;
v___y_831_ = v_snd_856_;
v___y_832_ = v___x_857_;
goto v___jp_829_;
}
else
{
size_t v___x_862_; size_t v___x_863_; uint64_t v___x_864_; 
v___x_862_ = ((size_t)0ULL);
v___x_863_ = lean_usize_of_nat(v___x_859_);
v___x_864_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2_spec__3(v_fst_855_, v___x_862_, v___x_863_, v___x_857_);
lean_inc(v_snd_856_);
v___y_830_ = v___y_854_;
v___y_831_ = v_snd_856_;
v___y_832_ = v___x_864_;
goto v___jp_829_;
}
}
else
{
size_t v___x_865_; size_t v___x_866_; uint64_t v___x_867_; 
v___x_865_ = ((size_t)0ULL);
v___x_866_ = lean_usize_of_nat(v___x_859_);
v___x_867_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2_spec__3(v_fst_855_, v___x_865_, v___x_866_, v___x_857_);
lean_inc(v_snd_856_);
v___y_830_ = v___y_854_;
v___y_831_ = v_snd_856_;
v___y_832_ = v___x_867_;
goto v___jp_829_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__3_spec__6_spec__8___redArg(lean_object* v_i_871_, lean_object* v_source_872_, lean_object* v_target_873_){
_start:
{
lean_object* v___x_874_; uint8_t v___x_875_; 
v___x_874_ = lean_array_get_size(v_source_872_);
v___x_875_ = lean_nat_dec_lt(v_i_871_, v___x_874_);
if (v___x_875_ == 0)
{
lean_dec_ref(v_source_872_);
lean_dec(v_i_871_);
return v_target_873_;
}
else
{
lean_object* v_es_876_; lean_object* v___x_877_; lean_object* v_source_878_; lean_object* v_target_879_; lean_object* v___x_880_; lean_object* v___x_881_; 
v_es_876_ = lean_array_fget(v_source_872_, v_i_871_);
v___x_877_ = lean_box(0);
v_source_878_ = lean_array_fset(v_source_872_, v_i_871_, v___x_877_);
v_target_879_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__3_spec__6_spec__8_spec__9___redArg(v_target_873_, v_es_876_);
v___x_880_ = lean_unsigned_to_nat(1u);
v___x_881_ = lean_nat_add(v_i_871_, v___x_880_);
lean_dec(v_i_871_);
v_i_871_ = v___x_881_;
v_source_872_ = v_source_878_;
v_target_873_ = v_target_879_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__3_spec__6___redArg(lean_object* v_data_883_){
_start:
{
lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v_nbuckets_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; 
v___x_884_ = lean_array_get_size(v_data_883_);
v___x_885_ = lean_unsigned_to_nat(2u);
v_nbuckets_886_ = lean_nat_mul(v___x_884_, v___x_885_);
v___x_887_ = lean_unsigned_to_nat(0u);
v___x_888_ = lean_box(0);
v___x_889_ = lean_mk_array(v_nbuckets_886_, v___x_888_);
v___x_890_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__3_spec__6_spec__8___redArg(v___x_887_, v_data_883_, v___x_889_);
return v___x_890_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__3_spec__7___redArg(lean_object* v_a_891_, lean_object* v_b_892_, lean_object* v_x_893_){
_start:
{
if (lean_obj_tag(v_x_893_) == 0)
{
lean_dec(v_b_892_);
lean_dec_ref(v_a_891_);
return v_x_893_;
}
else
{
lean_object* v_key_894_; lean_object* v_value_895_; lean_object* v_tail_896_; lean_object* v___x_898_; uint8_t v_isShared_899_; uint8_t v_isSharedCheck_922_; 
v_key_894_ = lean_ctor_get(v_x_893_, 0);
v_value_895_ = lean_ctor_get(v_x_893_, 1);
v_tail_896_ = lean_ctor_get(v_x_893_, 2);
v_isSharedCheck_922_ = !lean_is_exclusive(v_x_893_);
if (v_isSharedCheck_922_ == 0)
{
v___x_898_ = v_x_893_;
v_isShared_899_ = v_isSharedCheck_922_;
goto v_resetjp_897_;
}
else
{
lean_inc(v_tail_896_);
lean_inc(v_value_895_);
lean_inc(v_key_894_);
lean_dec(v_x_893_);
v___x_898_ = lean_box(0);
v_isShared_899_ = v_isSharedCheck_922_;
goto v_resetjp_897_;
}
v_resetjp_897_:
{
uint8_t v___y_906_; lean_object* v_fst_908_; lean_object* v_snd_909_; lean_object* v_fst_910_; lean_object* v_snd_911_; uint8_t v___x_912_; 
v_fst_908_ = lean_ctor_get(v_key_894_, 0);
v_snd_909_ = lean_ctor_get(v_key_894_, 1);
v_fst_910_ = lean_ctor_get(v_a_891_, 0);
v_snd_911_ = lean_ctor_get(v_a_891_, 1);
v___x_912_ = lean_name_eq(v_fst_908_, v_fst_910_);
if (v___x_912_ == 0)
{
v___y_906_ = v___x_912_;
goto v___jp_905_;
}
else
{
lean_object* v_fst_913_; lean_object* v_snd_914_; lean_object* v_fst_915_; lean_object* v_snd_916_; lean_object* v___x_917_; lean_object* v___x_918_; uint8_t v___x_919_; 
v_fst_913_ = lean_ctor_get(v_snd_909_, 0);
v_snd_914_ = lean_ctor_get(v_snd_909_, 1);
v_fst_915_ = lean_ctor_get(v_snd_911_, 0);
v_snd_916_ = lean_ctor_get(v_snd_911_, 1);
v___x_917_ = lean_array_get_size(v_fst_913_);
v___x_918_ = lean_array_get_size(v_fst_915_);
v___x_919_ = lean_nat_dec_eq(v___x_917_, v___x_918_);
if (v___x_919_ == 0)
{
goto v___jp_900_;
}
else
{
uint8_t v___x_920_; 
v___x_920_ = l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2_spec__2_spec__3___redArg(v_fst_913_, v_fst_915_, v___x_917_);
if (v___x_920_ == 0)
{
goto v___jp_900_;
}
else
{
uint8_t v___x_921_; 
v___x_921_ = lean_nat_dec_eq(v_snd_914_, v_snd_916_);
v___y_906_ = v___x_921_;
goto v___jp_905_;
}
}
}
v___jp_900_:
{
lean_object* v___x_901_; lean_object* v___x_903_; 
v___x_901_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__3_spec__7___redArg(v_a_891_, v_b_892_, v_tail_896_);
if (v_isShared_899_ == 0)
{
lean_ctor_set(v___x_898_, 2, v___x_901_);
v___x_903_ = v___x_898_;
goto v_reusejp_902_;
}
else
{
lean_object* v_reuseFailAlloc_904_; 
v_reuseFailAlloc_904_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_904_, 0, v_key_894_);
lean_ctor_set(v_reuseFailAlloc_904_, 1, v_value_895_);
lean_ctor_set(v_reuseFailAlloc_904_, 2, v___x_901_);
v___x_903_ = v_reuseFailAlloc_904_;
goto v_reusejp_902_;
}
v_reusejp_902_:
{
return v___x_903_;
}
}
v___jp_905_:
{
if (v___y_906_ == 0)
{
goto v___jp_900_;
}
else
{
lean_object* v___x_907_; 
lean_del_object(v___x_898_);
lean_dec(v_value_895_);
lean_dec(v_key_894_);
v___x_907_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_907_, 0, v_a_891_);
lean_ctor_set(v___x_907_, 1, v_b_892_);
lean_ctor_set(v___x_907_, 2, v_tail_896_);
return v___x_907_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__3_spec__5___redArg(lean_object* v_a_923_, lean_object* v_x_924_){
_start:
{
if (lean_obj_tag(v_x_924_) == 0)
{
uint8_t v___x_925_; 
v___x_925_ = 0;
return v___x_925_;
}
else
{
lean_object* v_key_926_; lean_object* v_tail_927_; uint8_t v___y_929_; lean_object* v_fst_931_; lean_object* v_snd_932_; lean_object* v_fst_933_; lean_object* v_snd_934_; uint8_t v___x_935_; 
v_key_926_ = lean_ctor_get(v_x_924_, 0);
v_tail_927_ = lean_ctor_get(v_x_924_, 2);
v_fst_931_ = lean_ctor_get(v_key_926_, 0);
v_snd_932_ = lean_ctor_get(v_key_926_, 1);
v_fst_933_ = lean_ctor_get(v_a_923_, 0);
v_snd_934_ = lean_ctor_get(v_a_923_, 1);
v___x_935_ = lean_name_eq(v_fst_931_, v_fst_933_);
if (v___x_935_ == 0)
{
v___y_929_ = v___x_935_;
goto v___jp_928_;
}
else
{
lean_object* v_fst_936_; lean_object* v_snd_937_; lean_object* v_fst_938_; lean_object* v_snd_939_; lean_object* v___x_940_; lean_object* v___x_941_; uint8_t v___x_942_; 
v_fst_936_ = lean_ctor_get(v_snd_932_, 0);
v_snd_937_ = lean_ctor_get(v_snd_932_, 1);
v_fst_938_ = lean_ctor_get(v_snd_934_, 0);
v_snd_939_ = lean_ctor_get(v_snd_934_, 1);
v___x_940_ = lean_array_get_size(v_fst_936_);
v___x_941_ = lean_array_get_size(v_fst_938_);
v___x_942_ = lean_nat_dec_eq(v___x_940_, v___x_941_);
if (v___x_942_ == 0)
{
v_x_924_ = v_tail_927_;
goto _start;
}
else
{
uint8_t v___x_944_; 
v___x_944_ = l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2_spec__2_spec__3___redArg(v_fst_936_, v_fst_938_, v___x_940_);
if (v___x_944_ == 0)
{
v_x_924_ = v_tail_927_;
goto _start;
}
else
{
uint8_t v___x_946_; 
v___x_946_ = lean_nat_dec_eq(v_snd_937_, v_snd_939_);
v___y_929_ = v___x_946_;
goto v___jp_928_;
}
}
}
v___jp_928_:
{
if (v___y_929_ == 0)
{
v_x_924_ = v_tail_927_;
goto _start;
}
else
{
return v___y_929_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__3_spec__5___redArg___boxed(lean_object* v_a_947_, lean_object* v_x_948_){
_start:
{
uint8_t v_res_949_; lean_object* v_r_950_; 
v_res_949_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__3_spec__5___redArg(v_a_947_, v_x_948_);
lean_dec(v_x_948_);
lean_dec_ref(v_a_947_);
v_r_950_ = lean_box(v_res_949_);
return v_r_950_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__3___redArg(lean_object* v_m_951_, lean_object* v_a_952_, lean_object* v_b_953_){
_start:
{
lean_object* v_size_954_; lean_object* v_buckets_955_; lean_object* v___x_957_; uint8_t v_isShared_958_; uint8_t v_isSharedCheck_1023_; 
v_size_954_ = lean_ctor_get(v_m_951_, 0);
v_buckets_955_ = lean_ctor_get(v_m_951_, 1);
v_isSharedCheck_1023_ = !lean_is_exclusive(v_m_951_);
if (v_isSharedCheck_1023_ == 0)
{
v___x_957_ = v_m_951_;
v_isShared_958_ = v_isSharedCheck_1023_;
goto v_resetjp_956_;
}
else
{
lean_inc(v_buckets_955_);
lean_inc(v_size_954_);
lean_dec(v_m_951_);
v___x_957_ = lean_box(0);
v_isShared_958_ = v_isSharedCheck_1023_;
goto v_resetjp_956_;
}
v_resetjp_956_:
{
lean_object* v_fst_959_; lean_object* v_snd_960_; lean_object* v___x_961_; lean_object* v___y_963_; uint64_t v___y_964_; uint64_t v___y_965_; uint64_t v___y_1007_; 
v_fst_959_ = lean_ctor_get(v_a_952_, 0);
v_snd_960_ = lean_ctor_get(v_a_952_, 1);
v___x_961_ = lean_array_get_size(v_buckets_955_);
if (lean_obj_tag(v_fst_959_) == 0)
{
uint64_t v___x_1021_; 
v___x_1021_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached_spec__0___redArg___closed__0);
v___y_1007_ = v___x_1021_;
goto v___jp_1006_;
}
else
{
uint64_t v_hash_1022_; 
v_hash_1022_ = lean_ctor_get_uint64(v_fst_959_, sizeof(void*)*2);
v___y_1007_ = v_hash_1022_;
goto v___jp_1006_;
}
v___jp_962_:
{
uint64_t v___x_966_; uint64_t v___x_967_; uint64_t v___x_968_; uint64_t v___x_969_; uint64_t v___x_970_; uint64_t v_fold_971_; uint64_t v___x_972_; uint64_t v___x_973_; uint64_t v___x_974_; size_t v___x_975_; size_t v___x_976_; size_t v___x_977_; size_t v___x_978_; size_t v___x_979_; lean_object* v_bkt_980_; uint8_t v___x_981_; 
v___x_966_ = lean_uint64_of_nat(v___y_963_);
lean_dec(v___y_963_);
v___x_967_ = lean_uint64_mix_hash(v___y_965_, v___x_966_);
v___x_968_ = lean_uint64_mix_hash(v___y_964_, v___x_967_);
v___x_969_ = 32ULL;
v___x_970_ = lean_uint64_shift_right(v___x_968_, v___x_969_);
v_fold_971_ = lean_uint64_xor(v___x_968_, v___x_970_);
v___x_972_ = 16ULL;
v___x_973_ = lean_uint64_shift_right(v_fold_971_, v___x_972_);
v___x_974_ = lean_uint64_xor(v_fold_971_, v___x_973_);
v___x_975_ = lean_uint64_to_usize(v___x_974_);
v___x_976_ = lean_usize_of_nat(v___x_961_);
v___x_977_ = ((size_t)1ULL);
v___x_978_ = lean_usize_sub(v___x_976_, v___x_977_);
v___x_979_ = lean_usize_land(v___x_975_, v___x_978_);
v_bkt_980_ = lean_array_uget_borrowed(v_buckets_955_, v___x_979_);
v___x_981_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__3_spec__5___redArg(v_a_952_, v_bkt_980_);
if (v___x_981_ == 0)
{
lean_object* v___x_982_; lean_object* v_size_x27_983_; lean_object* v___x_984_; lean_object* v_buckets_x27_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; uint8_t v___x_991_; 
v___x_982_ = lean_unsigned_to_nat(1u);
v_size_x27_983_ = lean_nat_add(v_size_954_, v___x_982_);
lean_dec(v_size_954_);
lean_inc(v_bkt_980_);
v___x_984_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_984_, 0, v_a_952_);
lean_ctor_set(v___x_984_, 1, v_b_953_);
lean_ctor_set(v___x_984_, 2, v_bkt_980_);
v_buckets_x27_985_ = lean_array_uset(v_buckets_955_, v___x_979_, v___x_984_);
v___x_986_ = lean_unsigned_to_nat(4u);
v___x_987_ = lean_nat_mul(v_size_x27_983_, v___x_986_);
v___x_988_ = lean_unsigned_to_nat(3u);
v___x_989_ = lean_nat_div(v___x_987_, v___x_988_);
lean_dec(v___x_987_);
v___x_990_ = lean_array_get_size(v_buckets_x27_985_);
v___x_991_ = lean_nat_dec_le(v___x_989_, v___x_990_);
lean_dec(v___x_989_);
if (v___x_991_ == 0)
{
lean_object* v_val_992_; lean_object* v___x_994_; 
v_val_992_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__3_spec__6___redArg(v_buckets_x27_985_);
if (v_isShared_958_ == 0)
{
lean_ctor_set(v___x_957_, 1, v_val_992_);
lean_ctor_set(v___x_957_, 0, v_size_x27_983_);
v___x_994_ = v___x_957_;
goto v_reusejp_993_;
}
else
{
lean_object* v_reuseFailAlloc_995_; 
v_reuseFailAlloc_995_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_995_, 0, v_size_x27_983_);
lean_ctor_set(v_reuseFailAlloc_995_, 1, v_val_992_);
v___x_994_ = v_reuseFailAlloc_995_;
goto v_reusejp_993_;
}
v_reusejp_993_:
{
return v___x_994_;
}
}
else
{
lean_object* v___x_997_; 
if (v_isShared_958_ == 0)
{
lean_ctor_set(v___x_957_, 1, v_buckets_x27_985_);
lean_ctor_set(v___x_957_, 0, v_size_x27_983_);
v___x_997_ = v___x_957_;
goto v_reusejp_996_;
}
else
{
lean_object* v_reuseFailAlloc_998_; 
v_reuseFailAlloc_998_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_998_, 0, v_size_x27_983_);
lean_ctor_set(v_reuseFailAlloc_998_, 1, v_buckets_x27_985_);
v___x_997_ = v_reuseFailAlloc_998_;
goto v_reusejp_996_;
}
v_reusejp_996_:
{
return v___x_997_;
}
}
}
else
{
lean_object* v___x_999_; lean_object* v_buckets_x27_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1004_; 
lean_inc(v_bkt_980_);
v___x_999_ = lean_box(0);
v_buckets_x27_1000_ = lean_array_uset(v_buckets_955_, v___x_979_, v___x_999_);
v___x_1001_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__3_spec__7___redArg(v_a_952_, v_b_953_, v_bkt_980_);
v___x_1002_ = lean_array_uset(v_buckets_x27_1000_, v___x_979_, v___x_1001_);
if (v_isShared_958_ == 0)
{
lean_ctor_set(v___x_957_, 1, v___x_1002_);
v___x_1004_ = v___x_957_;
goto v_reusejp_1003_;
}
else
{
lean_object* v_reuseFailAlloc_1005_; 
v_reuseFailAlloc_1005_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1005_, 0, v_size_954_);
lean_ctor_set(v_reuseFailAlloc_1005_, 1, v___x_1002_);
v___x_1004_ = v_reuseFailAlloc_1005_;
goto v_reusejp_1003_;
}
v_reusejp_1003_:
{
return v___x_1004_;
}
}
}
v___jp_1006_:
{
lean_object* v_fst_1008_; lean_object* v_snd_1009_; uint64_t v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; uint8_t v___x_1013_; 
v_fst_1008_ = lean_ctor_get(v_snd_960_, 0);
v_snd_1009_ = lean_ctor_get(v_snd_960_, 1);
v___x_1010_ = 7ULL;
v___x_1011_ = lean_unsigned_to_nat(0u);
v___x_1012_ = lean_array_get_size(v_fst_1008_);
v___x_1013_ = lean_nat_dec_lt(v___x_1011_, v___x_1012_);
if (v___x_1013_ == 0)
{
lean_inc(v_snd_1009_);
v___y_963_ = v_snd_1009_;
v___y_964_ = v___y_1007_;
v___y_965_ = v___x_1010_;
goto v___jp_962_;
}
else
{
uint8_t v___x_1014_; 
v___x_1014_ = lean_nat_dec_le(v___x_1012_, v___x_1012_);
if (v___x_1014_ == 0)
{
if (v___x_1013_ == 0)
{
lean_inc(v_snd_1009_);
v___y_963_ = v_snd_1009_;
v___y_964_ = v___y_1007_;
v___y_965_ = v___x_1010_;
goto v___jp_962_;
}
else
{
size_t v___x_1015_; size_t v___x_1016_; uint64_t v___x_1017_; 
v___x_1015_ = ((size_t)0ULL);
v___x_1016_ = lean_usize_of_nat(v___x_1012_);
v___x_1017_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2_spec__3(v_fst_1008_, v___x_1015_, v___x_1016_, v___x_1010_);
lean_inc(v_snd_1009_);
v___y_963_ = v_snd_1009_;
v___y_964_ = v___y_1007_;
v___y_965_ = v___x_1017_;
goto v___jp_962_;
}
}
else
{
size_t v___x_1018_; size_t v___x_1019_; uint64_t v___x_1020_; 
v___x_1018_ = ((size_t)0ULL);
v___x_1019_ = lean_usize_of_nat(v___x_1012_);
v___x_1020_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2_spec__3(v_fst_1008_, v___x_1018_, v___x_1019_, v___x_1010_);
lean_inc(v_snd_1009_);
v___y_963_ = v_snd_1009_;
v___y_964_ = v___y_1007_;
v___y_965_ = v___x_1020_;
goto v___jp_962_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached___redArg(lean_object* v_c_1024_, lean_object* v_as_1025_, lean_object* v_excessArgs_1026_, lean_object* v_resultType_x3f_1027_, lean_object* v_a_1028_, lean_object* v_a_1029_, lean_object* v_a_1030_, lean_object* v_a_1031_, lean_object* v_a_1032_, lean_object* v_a_1033_, lean_object* v_a_1034_){
_start:
{
lean_object* v___x_1036_; size_t v_sz_1037_; size_t v___x_1038_; lean_object* v___x_1039_; 
v___x_1036_ = lean_st_ref_get(v_a_1028_);
v_sz_1037_ = lean_array_size(v_as_1025_);
v___x_1038_ = ((size_t)0ULL);
lean_inc_ref(v_as_1025_);
v___x_1039_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__0(v_sz_1037_, v___x_1038_, v_as_1025_, v_a_1029_, v_a_1030_, v_a_1031_, v_a_1032_, v_a_1033_, v_a_1034_);
if (lean_obj_tag(v___x_1039_) == 0)
{
lean_object* v_a_1040_; lean_object* v___x_1042_; uint8_t v_isShared_1043_; uint8_t v_isSharedCheck_1086_; 
v_a_1040_ = lean_ctor_get(v___x_1039_, 0);
v_isSharedCheck_1086_ = !lean_is_exclusive(v___x_1039_);
if (v_isSharedCheck_1086_ == 0)
{
v___x_1042_ = v___x_1039_;
v_isShared_1043_ = v_isSharedCheck_1086_;
goto v_resetjp_1041_;
}
else
{
lean_inc(v_a_1040_);
lean_dec(v___x_1039_);
v___x_1042_ = lean_box(0);
v_isShared_1043_ = v_isSharedCheck_1086_;
goto v_resetjp_1041_;
}
v_resetjp_1041_:
{
lean_object* v_latticeBackwardRuleCache_1044_; lean_object* v_applyLemma_1045_; size_t v_sz_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; 
v_latticeBackwardRuleCache_1044_ = lean_ctor_get(v___x_1036_, 2);
lean_inc_ref(v_latticeBackwardRuleCache_1044_);
lean_dec(v___x_1036_);
v_applyLemma_1045_ = lean_ctor_get(v_c_1024_, 1);
v_sz_1046_ = lean_array_size(v_a_1040_);
v___x_1047_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__1(v_sz_1046_, v___x_1038_, v_a_1040_);
v___x_1048_ = lean_array_get_size(v_excessArgs_1026_);
v___x_1049_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1049_, 0, v___x_1047_);
lean_ctor_set(v___x_1049_, 1, v___x_1048_);
lean_inc(v_applyLemma_1045_);
v___x_1050_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1050_, 0, v_applyLemma_1045_);
lean_ctor_set(v___x_1050_, 1, v___x_1049_);
v___x_1051_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2___redArg(v_latticeBackwardRuleCache_1044_, v___x_1050_);
lean_dec_ref(v_latticeBackwardRuleCache_1044_);
if (lean_obj_tag(v___x_1051_) == 1)
{
lean_object* v_val_1052_; lean_object* v___x_1054_; 
lean_dec_ref_known(v___x_1050_, 2);
lean_dec(v_resultType_x3f_1027_);
lean_dec_ref(v_excessArgs_1026_);
lean_dec_ref(v_as_1025_);
lean_dec_ref(v_c_1024_);
v_val_1052_ = lean_ctor_get(v___x_1051_, 0);
lean_inc(v_val_1052_);
lean_dec_ref_known(v___x_1051_, 1);
if (v_isShared_1043_ == 0)
{
lean_ctor_set(v___x_1042_, 0, v_val_1052_);
v___x_1054_ = v___x_1042_;
goto v_reusejp_1053_;
}
else
{
lean_object* v_reuseFailAlloc_1055_; 
v_reuseFailAlloc_1055_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1055_, 0, v_val_1052_);
v___x_1054_ = v_reuseFailAlloc_1055_;
goto v_reusejp_1053_;
}
v_reusejp_1053_:
{
return v___x_1054_;
}
}
else
{
lean_object* v___x_1056_; 
lean_dec(v___x_1051_);
lean_del_object(v___x_1042_);
v___x_1056_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_LatticeSplit_mkBackwardRuleForLattice(v_c_1024_, v_as_1025_, v_excessArgs_1026_, v_resultType_x3f_1027_, v_a_1031_, v_a_1032_, v_a_1033_, v_a_1034_);
if (lean_obj_tag(v___x_1056_) == 0)
{
lean_object* v_a_1057_; lean_object* v___x_1058_; 
v_a_1057_ = lean_ctor_get(v___x_1056_, 0);
lean_inc(v_a_1057_);
lean_dec_ref_known(v___x_1056_, 1);
v___x_1058_ = l_Lean_Meta_Sym_BackwardRule_shareCommon(v_a_1057_, v_a_1029_, v_a_1030_, v_a_1031_, v_a_1032_, v_a_1033_, v_a_1034_);
if (lean_obj_tag(v___x_1058_) == 0)
{
lean_object* v_a_1059_; lean_object* v___x_1061_; uint8_t v_isShared_1062_; uint8_t v_isSharedCheck_1085_; 
v_a_1059_ = lean_ctor_get(v___x_1058_, 0);
v_isSharedCheck_1085_ = !lean_is_exclusive(v___x_1058_);
if (v_isSharedCheck_1085_ == 0)
{
v___x_1061_ = v___x_1058_;
v_isShared_1062_ = v_isSharedCheck_1085_;
goto v_resetjp_1060_;
}
else
{
lean_inc(v_a_1059_);
lean_dec(v___x_1058_);
v___x_1061_ = lean_box(0);
v_isShared_1062_ = v_isSharedCheck_1085_;
goto v_resetjp_1060_;
}
v_resetjp_1060_:
{
lean_object* v___x_1063_; lean_object* v_specBackwardRuleCache_1064_; lean_object* v_splitBackwardRuleCache_1065_; lean_object* v_latticeBackwardRuleCache_1066_; lean_object* v_frameDB_x3f_1067_; lean_object* v_invariants_1068_; lean_object* v_vcs_1069_; lean_object* v_simpState_1070_; lean_object* v_fuel_1071_; lean_object* v_inlineHandledInvariants_1072_; lean_object* v___x_1074_; uint8_t v_isShared_1075_; uint8_t v_isSharedCheck_1084_; 
v___x_1063_ = lean_st_ref_take(v_a_1028_);
v_specBackwardRuleCache_1064_ = lean_ctor_get(v___x_1063_, 0);
v_splitBackwardRuleCache_1065_ = lean_ctor_get(v___x_1063_, 1);
v_latticeBackwardRuleCache_1066_ = lean_ctor_get(v___x_1063_, 2);
v_frameDB_x3f_1067_ = lean_ctor_get(v___x_1063_, 3);
v_invariants_1068_ = lean_ctor_get(v___x_1063_, 4);
v_vcs_1069_ = lean_ctor_get(v___x_1063_, 5);
v_simpState_1070_ = lean_ctor_get(v___x_1063_, 6);
v_fuel_1071_ = lean_ctor_get(v___x_1063_, 7);
v_inlineHandledInvariants_1072_ = lean_ctor_get(v___x_1063_, 8);
v_isSharedCheck_1084_ = !lean_is_exclusive(v___x_1063_);
if (v_isSharedCheck_1084_ == 0)
{
v___x_1074_ = v___x_1063_;
v_isShared_1075_ = v_isSharedCheck_1084_;
goto v_resetjp_1073_;
}
else
{
lean_inc(v_inlineHandledInvariants_1072_);
lean_inc(v_fuel_1071_);
lean_inc(v_simpState_1070_);
lean_inc(v_vcs_1069_);
lean_inc(v_invariants_1068_);
lean_inc(v_frameDB_x3f_1067_);
lean_inc(v_latticeBackwardRuleCache_1066_);
lean_inc(v_splitBackwardRuleCache_1065_);
lean_inc(v_specBackwardRuleCache_1064_);
lean_dec(v___x_1063_);
v___x_1074_ = lean_box(0);
v_isShared_1075_ = v_isSharedCheck_1084_;
goto v_resetjp_1073_;
}
v_resetjp_1073_:
{
lean_object* v___x_1076_; lean_object* v___x_1078_; 
lean_inc(v_a_1059_);
v___x_1076_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__3___redArg(v_latticeBackwardRuleCache_1066_, v___x_1050_, v_a_1059_);
if (v_isShared_1075_ == 0)
{
lean_ctor_set(v___x_1074_, 2, v___x_1076_);
v___x_1078_ = v___x_1074_;
goto v_reusejp_1077_;
}
else
{
lean_object* v_reuseFailAlloc_1083_; 
v_reuseFailAlloc_1083_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1083_, 0, v_specBackwardRuleCache_1064_);
lean_ctor_set(v_reuseFailAlloc_1083_, 1, v_splitBackwardRuleCache_1065_);
lean_ctor_set(v_reuseFailAlloc_1083_, 2, v___x_1076_);
lean_ctor_set(v_reuseFailAlloc_1083_, 3, v_frameDB_x3f_1067_);
lean_ctor_set(v_reuseFailAlloc_1083_, 4, v_invariants_1068_);
lean_ctor_set(v_reuseFailAlloc_1083_, 5, v_vcs_1069_);
lean_ctor_set(v_reuseFailAlloc_1083_, 6, v_simpState_1070_);
lean_ctor_set(v_reuseFailAlloc_1083_, 7, v_fuel_1071_);
lean_ctor_set(v_reuseFailAlloc_1083_, 8, v_inlineHandledInvariants_1072_);
v___x_1078_ = v_reuseFailAlloc_1083_;
goto v_reusejp_1077_;
}
v_reusejp_1077_:
{
lean_object* v___x_1079_; lean_object* v___x_1081_; 
v___x_1079_ = lean_st_ref_set(v_a_1028_, v___x_1078_);
if (v_isShared_1062_ == 0)
{
v___x_1081_ = v___x_1061_;
goto v_reusejp_1080_;
}
else
{
lean_object* v_reuseFailAlloc_1082_; 
v_reuseFailAlloc_1082_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1082_, 0, v_a_1059_);
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
lean_dec_ref_known(v___x_1050_, 2);
return v___x_1058_;
}
}
else
{
lean_dec_ref_known(v___x_1050_, 2);
return v___x_1056_;
}
}
}
}
else
{
lean_object* v_a_1087_; lean_object* v___x_1089_; uint8_t v_isShared_1090_; uint8_t v_isSharedCheck_1094_; 
lean_dec(v___x_1036_);
lean_dec(v_resultType_x3f_1027_);
lean_dec_ref(v_excessArgs_1026_);
lean_dec_ref(v_as_1025_);
lean_dec_ref(v_c_1024_);
v_a_1087_ = lean_ctor_get(v___x_1039_, 0);
v_isSharedCheck_1094_ = !lean_is_exclusive(v___x_1039_);
if (v_isSharedCheck_1094_ == 0)
{
v___x_1089_ = v___x_1039_;
v_isShared_1090_ = v_isSharedCheck_1094_;
goto v_resetjp_1088_;
}
else
{
lean_inc(v_a_1087_);
lean_dec(v___x_1039_);
v___x_1089_ = lean_box(0);
v_isShared_1090_ = v_isSharedCheck_1094_;
goto v_resetjp_1088_;
}
v_resetjp_1088_:
{
lean_object* v___x_1092_; 
if (v_isShared_1090_ == 0)
{
v___x_1092_ = v___x_1089_;
goto v_reusejp_1091_;
}
else
{
lean_object* v_reuseFailAlloc_1093_; 
v_reuseFailAlloc_1093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1093_, 0, v_a_1087_);
v___x_1092_ = v_reuseFailAlloc_1093_;
goto v_reusejp_1091_;
}
v_reusejp_1091_:
{
return v___x_1092_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached___redArg___boxed(lean_object* v_c_1095_, lean_object* v_as_1096_, lean_object* v_excessArgs_1097_, lean_object* v_resultType_x3f_1098_, lean_object* v_a_1099_, lean_object* v_a_1100_, lean_object* v_a_1101_, lean_object* v_a_1102_, lean_object* v_a_1103_, lean_object* v_a_1104_, lean_object* v_a_1105_, lean_object* v_a_1106_){
_start:
{
lean_object* v_res_1107_; 
v_res_1107_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached___redArg(v_c_1095_, v_as_1096_, v_excessArgs_1097_, v_resultType_x3f_1098_, v_a_1099_, v_a_1100_, v_a_1101_, v_a_1102_, v_a_1103_, v_a_1104_, v_a_1105_);
lean_dec(v_a_1105_);
lean_dec_ref(v_a_1104_);
lean_dec(v_a_1103_);
lean_dec_ref(v_a_1102_);
lean_dec(v_a_1101_);
lean_dec_ref(v_a_1100_);
lean_dec(v_a_1099_);
return v_res_1107_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached(lean_object* v_c_1108_, lean_object* v_as_1109_, lean_object* v_excessArgs_1110_, lean_object* v_resultType_x3f_1111_, lean_object* v_a_1112_, lean_object* v_a_1113_, lean_object* v_a_1114_, lean_object* v_a_1115_, lean_object* v_a_1116_, lean_object* v_a_1117_, lean_object* v_a_1118_, lean_object* v_a_1119_, lean_object* v_a_1120_, lean_object* v_a_1121_, lean_object* v_a_1122_){
_start:
{
lean_object* v___x_1124_; 
v___x_1124_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached___redArg(v_c_1108_, v_as_1109_, v_excessArgs_1110_, v_resultType_x3f_1111_, v_a_1113_, v_a_1117_, v_a_1118_, v_a_1119_, v_a_1120_, v_a_1121_, v_a_1122_);
return v___x_1124_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached___boxed(lean_object* v_c_1125_, lean_object* v_as_1126_, lean_object* v_excessArgs_1127_, lean_object* v_resultType_x3f_1128_, lean_object* v_a_1129_, lean_object* v_a_1130_, lean_object* v_a_1131_, lean_object* v_a_1132_, lean_object* v_a_1133_, lean_object* v_a_1134_, lean_object* v_a_1135_, lean_object* v_a_1136_, lean_object* v_a_1137_, lean_object* v_a_1138_, lean_object* v_a_1139_, lean_object* v_a_1140_){
_start:
{
lean_object* v_res_1141_; 
v_res_1141_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached(v_c_1125_, v_as_1126_, v_excessArgs_1127_, v_resultType_x3f_1128_, v_a_1129_, v_a_1130_, v_a_1131_, v_a_1132_, v_a_1133_, v_a_1134_, v_a_1135_, v_a_1136_, v_a_1137_, v_a_1138_, v_a_1139_);
lean_dec(v_a_1139_);
lean_dec_ref(v_a_1138_);
lean_dec(v_a_1137_);
lean_dec_ref(v_a_1136_);
lean_dec(v_a_1135_);
lean_dec_ref(v_a_1134_);
lean_dec(v_a_1133_);
lean_dec_ref(v_a_1132_);
lean_dec(v_a_1131_);
lean_dec(v_a_1130_);
lean_dec_ref(v_a_1129_);
return v_res_1141_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2(lean_object* v_00_u03b2_1142_, lean_object* v_m_1143_, lean_object* v_a_1144_){
_start:
{
lean_object* v___x_1145_; 
v___x_1145_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2___redArg(v_m_1143_, v_a_1144_);
return v___x_1145_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2___boxed(lean_object* v_00_u03b2_1146_, lean_object* v_m_1147_, lean_object* v_a_1148_){
_start:
{
lean_object* v_res_1149_; 
v_res_1149_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2(v_00_u03b2_1146_, v_m_1147_, v_a_1148_);
lean_dec_ref(v_a_1148_);
lean_dec_ref(v_m_1147_);
return v_res_1149_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__3(lean_object* v_00_u03b2_1150_, lean_object* v_m_1151_, lean_object* v_a_1152_, lean_object* v_b_1153_){
_start:
{
lean_object* v___x_1154_; 
v___x_1154_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__3___redArg(v_m_1151_, v_a_1152_, v_b_1153_);
return v___x_1154_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2_spec__2(lean_object* v_00_u03b2_1155_, lean_object* v_a_1156_, lean_object* v_x_1157_){
_start:
{
lean_object* v___x_1158_; 
v___x_1158_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2_spec__2___redArg(v_a_1156_, v_x_1157_);
return v___x_1158_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2_spec__2___boxed(lean_object* v_00_u03b2_1159_, lean_object* v_a_1160_, lean_object* v_x_1161_){
_start:
{
lean_object* v_res_1162_; 
v_res_1162_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2_spec__2(v_00_u03b2_1159_, v_a_1160_, v_x_1161_);
lean_dec(v_x_1161_);
lean_dec_ref(v_a_1160_);
return v_res_1162_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__3_spec__5(lean_object* v_00_u03b2_1163_, lean_object* v_a_1164_, lean_object* v_x_1165_){
_start:
{
uint8_t v___x_1166_; 
v___x_1166_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__3_spec__5___redArg(v_a_1164_, v_x_1165_);
return v___x_1166_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__3_spec__5___boxed(lean_object* v_00_u03b2_1167_, lean_object* v_a_1168_, lean_object* v_x_1169_){
_start:
{
uint8_t v_res_1170_; lean_object* v_r_1171_; 
v_res_1170_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__3_spec__5(v_00_u03b2_1167_, v_a_1168_, v_x_1169_);
lean_dec(v_x_1169_);
lean_dec_ref(v_a_1168_);
v_r_1171_ = lean_box(v_res_1170_);
return v_r_1171_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__3_spec__6(lean_object* v_00_u03b2_1172_, lean_object* v_data_1173_){
_start:
{
lean_object* v___x_1174_; 
v___x_1174_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__3_spec__6___redArg(v_data_1173_);
return v___x_1174_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__3_spec__7(lean_object* v_00_u03b2_1175_, lean_object* v_a_1176_, lean_object* v_b_1177_, lean_object* v_x_1178_){
_start:
{
lean_object* v___x_1179_; 
v___x_1179_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__3_spec__7___redArg(v_a_1176_, v_b_1177_, v_x_1178_);
return v___x_1179_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2_spec__2_spec__3(lean_object* v_xs_1180_, lean_object* v_ys_1181_, lean_object* v_hsz_1182_, lean_object* v_x_1183_, lean_object* v_x_1184_){
_start:
{
uint8_t v___x_1185_; 
v___x_1185_ = l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2_spec__2_spec__3___redArg(v_xs_1180_, v_ys_1181_, v_x_1183_);
return v___x_1185_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2_spec__2_spec__3___boxed(lean_object* v_xs_1186_, lean_object* v_ys_1187_, lean_object* v_hsz_1188_, lean_object* v_x_1189_, lean_object* v_x_1190_){
_start:
{
uint8_t v_res_1191_; lean_object* v_r_1192_; 
v_res_1191_ = l_Array_isEqvAux___at___00Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__2_spec__2_spec__3(v_xs_1186_, v_ys_1187_, v_hsz_1188_, v_x_1189_, v_x_1190_);
lean_dec_ref(v_ys_1187_);
lean_dec_ref(v_xs_1186_);
v_r_1192_ = lean_box(v_res_1191_);
return v_r_1192_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__3_spec__6_spec__8(lean_object* v_00_u03b2_1193_, lean_object* v_i_1194_, lean_object* v_source_1195_, lean_object* v_target_1196_){
_start:
{
lean_object* v___x_1197_; 
v___x_1197_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__3_spec__6_spec__8___redArg(v_i_1194_, v_source_1195_, v_target_1196_);
return v___x_1197_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__3_spec__6_spec__8_spec__9(lean_object* v_00_u03b2_1198_, lean_object* v_x_1199_, lean_object* v_x_1200_){
_start:
{
lean_object* v___x_1201_; 
v___x_1201_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForLatticeCached_spec__3_spec__6_spec__8_spec__9___redArg(v_x_1199_, v_x_1200_);
return v___x_1201_;
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
