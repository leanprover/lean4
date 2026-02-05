// Lean compiler output
// Module: Lean.LibrarySuggestions.Basic
// Imports: public import Lean.Elab.Command public import Lean.Meta.Eval public import Lean.Meta.CompletionName public import Lean.Linter.Deprecated public import Init.Data.Random public import Lean.Elab.Tactic.Grind.Annotated
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
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__0___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
uint8_t l_Lean_isInstanceReducibleCore(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isInstanceReducible___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isInstanceReducible___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isInstanceReducible___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isInstanceReducible___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
size_t lean_ptr_addr(lean_object*);
uint64_t lean_usize_to_uint64(size_t);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__2_spec__3_spec__6_spec__7___redArg(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__2_spec__3_spec__6___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__2_spec__3___redArg(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__1_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit___redArg___closed__0 = (const lean_object*)&l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit___redArg___closed__0_value;
lean_object* l_Lean_Meta_isProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getFunInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_instInhabitedParamInfo_default;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_ParamInfo_isInstImplicit(lean_object*);
uint8_t l_Lean_NameHashSet_contains(lean_object*, lean_object*);
lean_object* l_Lean_NameHashSet_insert(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__1_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__2_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__2_spec__3_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__2_spec__3_spec__6_spec__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkPtrSet___redArg(lean_object*);
static lean_object* l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_foldUnsafe___redArg___closed__0;
static lean_object* l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_foldUnsafe___redArg___closed__1;
static lean_object* l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_foldUnsafe___redArg___closed__2;
static lean_object* l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_foldUnsafe___redArg___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_foldUnsafe___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_foldUnsafe___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_foldUnsafe(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_foldUnsafe___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_relevantConstants___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_relevantConstants___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Expr_relevantConstants___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Expr_relevantConstants___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Expr_relevantConstants___closed__0 = (const lean_object*)&l_Lean_Expr_relevantConstants___closed__0_value;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lean_Expr_relevantConstants___closed__1;
LEAN_EXPORT lean_object* l_Lean_Expr_relevantConstants(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_relevantConstants___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_relevantConstantsAsSet___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_relevantConstantsAsSet___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Expr_relevantConstantsAsSet___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Expr_relevantConstantsAsSet___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Expr_relevantConstantsAsSet___closed__0 = (const lean_object*)&l_Lean_Expr_relevantConstantsAsSet___closed__0_value;
extern lean_object* l_Lean_NameSet_empty;
LEAN_EXPORT lean_object* l_Lean_Expr_relevantConstantsAsSet(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_relevantConstantsAsSet___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_getConstants_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_getConstants_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_getConstants_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_getConstants_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getUsedConstantsAsSet(lean_object*);
lean_object* l_Lean_NameSet_append(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_getConstants_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_getConstants_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_getConstants_spec__0_spec__0_spec__2_spec__5_spec__6___redArg(lean_object*, size_t, size_t, lean_object*);
uint8_t l_Lean_LocalDecl_isImplementationDetail(lean_object*);
lean_object* l_Lean_LocalDecl_toExpr(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_getConstants_spec__0_spec__0_spec__2_spec__5_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_getConstants_spec__0_spec__0_spec__2_spec__5(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_getConstants_spec__0_spec__0_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_getConstants_spec__0_spec__0_spec__2_spec__4(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_getConstants_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_getConstants_spec__0_spec__0_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_getConstants_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_getConstants_spec__0_spec__0_spec__3_spec__7___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_getConstants_spec__0_spec__0_spec__3_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_getConstants_spec__0_spec__0_spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_getConstants_spec__0_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_getConstants_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_getConstants_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_getLocalHyps___at___00Lean_MVarId_getConstants_spec__0___closed__0;
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___at___00Lean_MVarId_getConstants_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___at___00Lean_MVarId_getConstants_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_getConstants___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_getConstants___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_getConstants(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_getConstants___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_getConstants_spec__0_spec__0_spec__3_spec__7(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_getConstants_spec__0_spec__0_spec__3_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_getConstants_spec__0_spec__0_spec__2_spec__5_spec__6(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_getConstants_spec__0_spec__0_spec__2_spec__5_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_getRelevantConstants_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_getRelevantConstants_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_getRelevantConstants___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_getRelevantConstants___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_getRelevantConstants(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_getRelevantConstants___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_ppGoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Std_Format_defWidth;
lean_object* l_Std_Format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_ppSelector(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_ppSelector___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_Selector_postFilter___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_Selector_postFilter___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LibrarySuggestions_Selector_postFilter_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LibrarySuggestions_Selector_postFilter_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_LibrarySuggestions_Selector_postFilter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_LibrarySuggestions_Selector_postFilter___lam__0___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_LibrarySuggestions_Selector_postFilter___closed__0 = (const lean_object*)&l_Lean_LibrarySuggestions_Selector_postFilter___closed__0_value;
static lean_object* l_Lean_LibrarySuggestions_Selector_postFilter___closed__1;
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_Selector_postFilter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_Selector_postFilter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_extract___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_Selector_maxSuggestions(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_Selector_maxSuggestions___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_float_decLt(double, double);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LibrarySuggestions_Selector_combine_spec__2___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LibrarySuggestions_Selector_combine_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LibrarySuggestions_Selector_combine_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LibrarySuggestions_Selector_combine_spec__2___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LibrarySuggestions_Selector_combine_spec__2___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LibrarySuggestions_Selector_combine_spec__2___redArg___closed__0_value;
lean_object* l_Array_qpartition___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LibrarySuggestions_Selector_combine_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LibrarySuggestions_Selector_combine_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Name_hash___override(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_LibrarySuggestions_Selector_combine_spec__0_spec__1_spec__3_spec__8___redArg(lean_object*, lean_object*);
uint64_t lean_string_hash(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_LibrarySuggestions_Selector_combine_spec__0_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_LibrarySuggestions_Selector_combine_spec__0_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_LibrarySuggestions_Selector_combine_spec__0_spec__2___lam__0(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_LibrarySuggestions_Selector_combine_spec__0_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_LibrarySuggestions_Selector_combine_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_LibrarySuggestions_Selector_combine_spec__0_spec__2(lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_LibrarySuggestions_Selector_combine_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_LibrarySuggestions_Selector_combine_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_LibrarySuggestions_Selector_combine_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_LibrarySuggestions_Selector_combine_spec__1___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_LibrarySuggestions_Selector_combine_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_LibrarySuggestions_Selector_combine_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LibrarySuggestions_Selector_combine_spec__4(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LibrarySuggestions_Selector_combine_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_LibrarySuggestions_Selector_combine___closed__0;
static lean_object* l_Lean_LibrarySuggestions_Selector_combine___closed__1;
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_Selector_combine(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_Selector_combine___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_LibrarySuggestions_Selector_combine_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_LibrarySuggestions_Selector_combine_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LibrarySuggestions_Selector_combine_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LibrarySuggestions_Selector_combine_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_LibrarySuggestions_Selector_combine_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_LibrarySuggestions_Selector_combine_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_LibrarySuggestions_Selector_combine_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_LibrarySuggestions_Selector_combine_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_LibrarySuggestions_Selector_combine_spec__0_spec__1_spec__3_spec__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LibrarySuggestions_Selector_filterGrindAnnotated_spec__0___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
uint8_t l_Lean_Elab_Tactic_Grind_isGrindAnnotatedModule(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LibrarySuggestions_Selector_filterGrindAnnotated_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_LibrarySuggestions_Selector_filterGrindAnnotated___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "grind"};
static const lean_object* l_Lean_LibrarySuggestions_Selector_filterGrindAnnotated___closed__0 = (const lean_object*)&l_Lean_LibrarySuggestions_Selector_filterGrindAnnotated___closed__0_value;
static const lean_ctor_object l_Lean_LibrarySuggestions_Selector_filterGrindAnnotated___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_Selector_filterGrindAnnotated___closed__0_value)}};
static const lean_object* l_Lean_LibrarySuggestions_Selector_filterGrindAnnotated___closed__1 = (const lean_object*)&l_Lean_LibrarySuggestions_Selector_filterGrindAnnotated___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_Selector_filterGrindAnnotated(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_Selector_filterGrindAnnotated___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LibrarySuggestions_Selector_filterGrindAnnotated_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LibrarySuggestions_Selector_filterGrindAnnotated_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
static double l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_LibrarySuggestions_Selector_intersperse_spec__0___redArg___closed__0;
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
double lean_float_add(double, double);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_LibrarySuggestions_Selector_intersperse_spec__0___redArg(double, lean_object*, lean_object*, lean_object*, lean_object*);
double l_Float_ofScientific(lean_object*, uint8_t, lean_object*);
uint8_t lean_float_decLe(double, double);
double lean_float_div(double, double);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_LibrarySuggestions_Selector_intersperse_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_LibrarySuggestions_Selector_intersperse_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_LibrarySuggestions_Selector_intersperse_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static double l_Lean_LibrarySuggestions_Selector_intersperse___closed__0;
static lean_object* l_Lean_LibrarySuggestions_Selector_intersperse___closed__1;
static lean_object* l_Lean_LibrarySuggestions_Selector_intersperse___closed__2;
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_Selector_intersperse___closed__3___boxed__const__1;
static lean_object* l_Lean_LibrarySuggestions_Selector_intersperse___closed__3;
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_Selector_intersperse___closed__4___boxed__const__1;
static lean_object* l_Lean_LibrarySuggestions_Selector_intersperse___closed__4;
double lean_float_mul(double, double);
uint32_t lean_float_to_uint32(double);
lean_object* lean_uint32_to_nat(uint32_t);
double lean_float_sub(double, double);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_Selector_intersperse(lean_object*, lean_object*, double, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_Selector_intersperse___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_LibrarySuggestions_Selector_intersperse_spec__0(double, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_LibrarySuggestions_Selector_intersperse_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_LibrarySuggestions_Selector_intersperse_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_LibrarySuggestions_Selector_intersperse_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_initFn___lam__0_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2_(lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_initFn___lam__1_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__spec__0_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__spec__0_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_LibrarySuggestions_initFn___closed__0_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_LibrarySuggestions_initFn___lam__0_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2_, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_LibrarySuggestions_initFn___closed__0_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__0_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_LibrarySuggestions_initFn___closed__1_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_LibrarySuggestions_initFn___lam__1_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2_, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_LibrarySuggestions_initFn___closed__1_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__1_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_LibrarySuggestions_initFn___closed__2_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_LibrarySuggestions_initFn___closed__2_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__2_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_LibrarySuggestions_initFn___closed__3_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "LibrarySuggestions"};
static const lean_object* l_Lean_LibrarySuggestions_initFn___closed__3_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__3_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_LibrarySuggestions_initFn___closed__4_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "moduleDenyListExt"};
static const lean_object* l_Lean_LibrarySuggestions_initFn___closed__4_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__4_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__value;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_LibrarySuggestions_initFn___closed__5_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__2_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_LibrarySuggestions_initFn___closed__5_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__5_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__3_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(33, 7, 235, 60, 247, 182, 234, 218)}};
static const lean_ctor_object l_Lean_LibrarySuggestions_initFn___closed__5_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__5_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__value_aux_1),((lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__4_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(230, 123, 203, 142, 120, 156, 209, 106)}};
static const lean_object* l_Lean_LibrarySuggestions_initFn___closed__5_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__5_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_LibrarySuggestions_initFn___closed__6_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lake"};
static const lean_object* l_Lean_LibrarySuggestions_initFn___closed__6_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__6_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_LibrarySuggestions_initFn___closed__7_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Internal"};
static const lean_object* l_Lean_LibrarySuggestions_initFn___closed__7_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__7_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_LibrarySuggestions_initFn___closed__8_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_LibrarySuggestions_initFn___closed__8_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__8_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_LibrarySuggestions_initFn___closed__9_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__8_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_LibrarySuggestions_initFn___closed__9_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__9_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_LibrarySuggestions_initFn___closed__10_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__7_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__value),((lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__9_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__value)}};
static const lean_object* l_Lean_LibrarySuggestions_initFn___closed__10_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__10_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_LibrarySuggestions_initFn___closed__11_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__2_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__value),((lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__10_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__value)}};
static const lean_object* l_Lean_LibrarySuggestions_initFn___closed__11_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__11_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_LibrarySuggestions_initFn___closed__12_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__6_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__value),((lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__11_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__value)}};
static const lean_object* l_Lean_LibrarySuggestions_initFn___closed__12_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__12_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_LibrarySuggestions_initFn___closed__13_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_mkStateFromImportedEntries___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__spec__0___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__12_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__value)} };
static const lean_object* l_Lean_LibrarySuggestions_initFn___closed__13_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__13_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_LibrarySuggestions_initFn___closed__14_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*7 + 0, .m_other = 7, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__5_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__value),((lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__0_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__value),((lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__13_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__value),((lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__1_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_LibrarySuggestions_initFn___closed__14_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__14_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__value;
lean_object* l_Lean_registerSimplePersistentEnvExtension___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_moduleDenyListExt;
static const lean_string_object l_Lean_LibrarySuggestions_initFn___closed__0_00___x40_Lean_LibrarySuggestions_Basic_611429871____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "nameDenyListExt"};
static const lean_object* l_Lean_LibrarySuggestions_initFn___closed__0_00___x40_Lean_LibrarySuggestions_Basic_611429871____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__0_00___x40_Lean_LibrarySuggestions_Basic_611429871____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_LibrarySuggestions_initFn___closed__1_00___x40_Lean_LibrarySuggestions_Basic_611429871____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__2_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_LibrarySuggestions_initFn___closed__1_00___x40_Lean_LibrarySuggestions_Basic_611429871____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__1_00___x40_Lean_LibrarySuggestions_Basic_611429871____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__3_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(33, 7, 235, 60, 247, 182, 234, 218)}};
static const lean_ctor_object l_Lean_LibrarySuggestions_initFn___closed__1_00___x40_Lean_LibrarySuggestions_Basic_611429871____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__1_00___x40_Lean_LibrarySuggestions_Basic_611429871____hygCtx___hyg_2__value_aux_1),((lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__0_00___x40_Lean_LibrarySuggestions_Basic_611429871____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(231, 26, 152, 186, 195, 69, 163, 18)}};
static const lean_object* l_Lean_LibrarySuggestions_initFn___closed__1_00___x40_Lean_LibrarySuggestions_Basic_611429871____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__1_00___x40_Lean_LibrarySuggestions_Basic_611429871____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_LibrarySuggestions_initFn___closed__2_00___x40_Lean_LibrarySuggestions_Basic_611429871____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*7 + 0, .m_other = 7, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__1_00___x40_Lean_LibrarySuggestions_Basic_611429871____hygCtx___hyg_2__value),((lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__0_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__value),((lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__13_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__value),((lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__1_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_LibrarySuggestions_initFn___closed__2_00___x40_Lean_LibrarySuggestions_Basic_611429871____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__2_00___x40_Lean_LibrarySuggestions_Basic_611429871____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_611429871____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_611429871____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_nameDenyListExt;
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_initFn___lam__0_00___x40_Lean_LibrarySuggestions_Basic_3406067637____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_initFn___lam__1_00___x40_Lean_LibrarySuggestions_Basic_3406067637____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3406067637____hygCtx___hyg_2__spec__0_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3406067637____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3406067637____hygCtx___hyg_2__spec__0_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3406067637____hygCtx___hyg_2__spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3406067637____hygCtx___hyg_2__spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3406067637____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_LibrarySuggestions_initFn___closed__0_00___x40_Lean_LibrarySuggestions_Basic_3406067637____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_LibrarySuggestions_initFn___lam__0_00___x40_Lean_LibrarySuggestions_Basic_3406067637____hygCtx___hyg_2_, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_LibrarySuggestions_initFn___closed__0_00___x40_Lean_LibrarySuggestions_Basic_3406067637____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__0_00___x40_Lean_LibrarySuggestions_Basic_3406067637____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_LibrarySuggestions_initFn___closed__1_00___x40_Lean_LibrarySuggestions_Basic_3406067637____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_LibrarySuggestions_initFn___lam__1_00___x40_Lean_LibrarySuggestions_Basic_3406067637____hygCtx___hyg_2_, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_LibrarySuggestions_initFn___closed__1_00___x40_Lean_LibrarySuggestions_Basic_3406067637____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__1_00___x40_Lean_LibrarySuggestions_Basic_3406067637____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_LibrarySuggestions_initFn___closed__2_00___x40_Lean_LibrarySuggestions_Basic_3406067637____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "typePrefixDenyListExt"};
static const lean_object* l_Lean_LibrarySuggestions_initFn___closed__2_00___x40_Lean_LibrarySuggestions_Basic_3406067637____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__2_00___x40_Lean_LibrarySuggestions_Basic_3406067637____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_LibrarySuggestions_initFn___closed__3_00___x40_Lean_LibrarySuggestions_Basic_3406067637____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__2_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_LibrarySuggestions_initFn___closed__3_00___x40_Lean_LibrarySuggestions_Basic_3406067637____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__3_00___x40_Lean_LibrarySuggestions_Basic_3406067637____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__3_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(33, 7, 235, 60, 247, 182, 234, 218)}};
static const lean_ctor_object l_Lean_LibrarySuggestions_initFn___closed__3_00___x40_Lean_LibrarySuggestions_Basic_3406067637____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__3_00___x40_Lean_LibrarySuggestions_Basic_3406067637____hygCtx___hyg_2__value_aux_1),((lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__2_00___x40_Lean_LibrarySuggestions_Basic_3406067637____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(96, 199, 197, 114, 42, 156, 103, 187)}};
static const lean_object* l_Lean_LibrarySuggestions_initFn___closed__3_00___x40_Lean_LibrarySuggestions_Basic_3406067637____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__3_00___x40_Lean_LibrarySuggestions_Basic_3406067637____hygCtx___hyg_2__value;
lean_object* l_Lean_Name_mkStr1(lean_object*);
static const lean_ctor_object l_Lean_LibrarySuggestions_initFn___closed__4_00___x40_Lean_LibrarySuggestions_Basic_3406067637____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__6_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_object* l_Lean_LibrarySuggestions_initFn___closed__4_00___x40_Lean_LibrarySuggestions_Basic_3406067637____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__4_00___x40_Lean_LibrarySuggestions_Basic_3406067637____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_LibrarySuggestions_initFn___closed__5_00___x40_Lean_LibrarySuggestions_Basic_3406067637____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__2_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_object* l_Lean_LibrarySuggestions_initFn___closed__5_00___x40_Lean_LibrarySuggestions_Basic_3406067637____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__5_00___x40_Lean_LibrarySuggestions_Basic_3406067637____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_LibrarySuggestions_initFn___closed__6_00___x40_Lean_LibrarySuggestions_Basic_3406067637____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__5_00___x40_Lean_LibrarySuggestions_Basic_3406067637____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_LibrarySuggestions_initFn___closed__6_00___x40_Lean_LibrarySuggestions_Basic_3406067637____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__6_00___x40_Lean_LibrarySuggestions_Basic_3406067637____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_LibrarySuggestions_initFn___closed__7_00___x40_Lean_LibrarySuggestions_Basic_3406067637____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__4_00___x40_Lean_LibrarySuggestions_Basic_3406067637____hygCtx___hyg_2__value),((lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__6_00___x40_Lean_LibrarySuggestions_Basic_3406067637____hygCtx___hyg_2__value)}};
static const lean_object* l_Lean_LibrarySuggestions_initFn___closed__7_00___x40_Lean_LibrarySuggestions_Basic_3406067637____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__7_00___x40_Lean_LibrarySuggestions_Basic_3406067637____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_LibrarySuggestions_initFn___closed__8_00___x40_Lean_LibrarySuggestions_Basic_3406067637____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_mkStateFromImportedEntries___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3406067637____hygCtx___hyg_2__spec__0___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__7_00___x40_Lean_LibrarySuggestions_Basic_3406067637____hygCtx___hyg_2__value)} };
static const lean_object* l_Lean_LibrarySuggestions_initFn___closed__8_00___x40_Lean_LibrarySuggestions_Basic_3406067637____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__8_00___x40_Lean_LibrarySuggestions_Basic_3406067637____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_LibrarySuggestions_initFn___closed__9_00___x40_Lean_LibrarySuggestions_Basic_3406067637____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*7 + 0, .m_other = 7, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__3_00___x40_Lean_LibrarySuggestions_Basic_3406067637____hygCtx___hyg_2__value),((lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__0_00___x40_Lean_LibrarySuggestions_Basic_3406067637____hygCtx___hyg_2__value),((lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__8_00___x40_Lean_LibrarySuggestions_Basic_3406067637____hygCtx___hyg_2__value),((lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__1_00___x40_Lean_LibrarySuggestions_Basic_3406067637____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_LibrarySuggestions_initFn___closed__9_00___x40_Lean_LibrarySuggestions_Basic_3406067637____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__9_00___x40_Lean_LibrarySuggestions_Basic_3406067637____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3406067637____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3406067637____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_typePrefixDenyListExt;
LEAN_EXPORT uint8_t l_Lean_LibrarySuggestions_isDeniedModule___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_isDeniedModule___lam__0___boxed(lean_object*, lean_object*);
uint8_t l_Lean_Name_anyS(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_LibrarySuggestions_isDeniedModule___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_isDeniedModule___lam__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_List_any___redArg(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_LibrarySuggestions_isDeniedModule(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_isDeniedModule___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_LibrarySuggestions_isDeniedPremise___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_isDeniedPremise___lam__1___boxed(lean_object*, lean_object*);
uint8_t l_Lean_Name_isPrefixOf(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_LibrarySuggestions_isDeniedPremise___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_isDeniedPremise___lam__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_LibrarySuggestions_isDeniedPremise___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "sorryAx"};
static const lean_object* l_Lean_LibrarySuggestions_isDeniedPremise___closed__0 = (const lean_object*)&l_Lean_LibrarySuggestions_isDeniedPremise___closed__0_value;
static const lean_ctor_object l_Lean_LibrarySuggestions_isDeniedPremise___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_LibrarySuggestions_isDeniedPremise___closed__0_value),LEAN_SCALAR_PTR_LITERAL(196, 190, 164, 146, 38, 179, 69, 72)}};
static const lean_object* l_Lean_LibrarySuggestions_isDeniedPremise___closed__1 = (const lean_object*)&l_Lean_LibrarySuggestions_isDeniedPremise___closed__1_value;
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
lean_object* l_Lean_Expr_getForallBody(lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
uint8_t l_Lean_Linter_isDeprecated(lean_object*, lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_EnvironmentHeader_moduleNames(lean_object*);
uint8_t l_Lean_Name_isInternalDetail(lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
LEAN_EXPORT uint8_t l_Lean_LibrarySuggestions_isDeniedPremise(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_isDeniedPremise___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_empty___redArg();
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_empty___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_empty(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_empty___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_rand(lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_LibrarySuggestions_random_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_LibrarySuggestions_random_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_LibrarySuggestions_random_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LibrarySuggestions_random_spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LibrarySuggestions_random_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_IO_stdGenRef;
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Environment_const2ModIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_random___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_random___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_random(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_random___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_LibrarySuggestions_random_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_LibrarySuggestions_random_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_wasOriginallyTheorem(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_currentFile___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_currentFile___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_LibrarySuggestions_currentFile_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_LibrarySuggestions_currentFile_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_LibrarySuggestions_currentFile_spec__0_spec__0_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_LibrarySuggestions_currentFile_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_LibrarySuggestions_currentFile_spec__0_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_LibrarySuggestions_currentFile_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_LibrarySuggestions_currentFile_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_LibrarySuggestions_currentFile_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_LibrarySuggestions_currentFile_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_LibrarySuggestions_currentFile_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_constants(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_currentFile___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_currentFile___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_currentFile(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_currentFile___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_LibrarySuggestions_currentFile_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_LibrarySuggestions_currentFile_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_LibrarySuggestions_currentFile_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_LibrarySuggestions_currentFile_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_LibrarySuggestions_currentFile_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_LibrarySuggestions_currentFile_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_LibrarySuggestions_currentFile_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_LibrarySuggestions_currentFile_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_LibrarySuggestions_currentFile_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_LibrarySuggestions_currentFile_spec__0_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_LibrarySuggestions_currentFile_spec__0_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_LibrarySuggestions_currentFile_spec__0_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_initFn___lam__0_00___x40_Lean_LibrarySuggestions_Basic_2654663577____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_initFn___lam__0_00___x40_Lean_LibrarySuggestions_Basic_2654663577____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_2654663577____hygCtx___hyg_2__spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_2654663577____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_2654663577____hygCtx___hyg_2__spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_2654663577____hygCtx___hyg_2__spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_initFn___lam__1_00___x40_Lean_LibrarySuggestions_Basic_2654663577____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_initFn___lam__1_00___x40_Lean_LibrarySuggestions_Basic_2654663577____hygCtx___hyg_2____boxed(lean_object*);
static const lean_closure_object l_Lean_LibrarySuggestions_initFn___closed__0_00___x40_Lean_LibrarySuggestions_Basic_2654663577____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_LibrarySuggestions_initFn___lam__0_00___x40_Lean_LibrarySuggestions_Basic_2654663577____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_LibrarySuggestions_initFn___closed__0_00___x40_Lean_LibrarySuggestions_Basic_2654663577____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__0_00___x40_Lean_LibrarySuggestions_Basic_2654663577____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_LibrarySuggestions_initFn___closed__1_00___x40_Lean_LibrarySuggestions_Basic_2654663577____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_LibrarySuggestions_initFn___lam__1_00___x40_Lean_LibrarySuggestions_Basic_2654663577____hygCtx___hyg_2____boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_LibrarySuggestions_initFn___closed__1_00___x40_Lean_LibrarySuggestions_Basic_2654663577____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__1_00___x40_Lean_LibrarySuggestions_Basic_2654663577____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_LibrarySuggestions_initFn___closed__2_00___x40_Lean_LibrarySuggestions_Basic_2654663577____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "librarySuggestionsExt"};
static const lean_object* l_Lean_LibrarySuggestions_initFn___closed__2_00___x40_Lean_LibrarySuggestions_Basic_2654663577____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__2_00___x40_Lean_LibrarySuggestions_Basic_2654663577____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_LibrarySuggestions_initFn___closed__3_00___x40_Lean_LibrarySuggestions_Basic_2654663577____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__2_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_LibrarySuggestions_initFn___closed__3_00___x40_Lean_LibrarySuggestions_Basic_2654663577____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__3_00___x40_Lean_LibrarySuggestions_Basic_2654663577____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__3_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(33, 7, 235, 60, 247, 182, 234, 218)}};
static const lean_ctor_object l_Lean_LibrarySuggestions_initFn___closed__3_00___x40_Lean_LibrarySuggestions_Basic_2654663577____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__3_00___x40_Lean_LibrarySuggestions_Basic_2654663577____hygCtx___hyg_2__value_aux_1),((lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__2_00___x40_Lean_LibrarySuggestions_Basic_2654663577____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(99, 152, 201, 31, 243, 26, 178, 82)}};
static const lean_object* l_Lean_LibrarySuggestions_initFn___closed__3_00___x40_Lean_LibrarySuggestions_Basic_2654663577____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__3_00___x40_Lean_LibrarySuggestions_Basic_2654663577____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_LibrarySuggestions_initFn___closed__4_00___x40_Lean_LibrarySuggestions_Basic_2654663577____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*7 + 0, .m_other = 7, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__3_00___x40_Lean_LibrarySuggestions_Basic_2654663577____hygCtx___hyg_2__value),((lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__0_00___x40_Lean_LibrarySuggestions_Basic_2654663577____hygCtx___hyg_2__value),((lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__1_00___x40_Lean_LibrarySuggestions_Basic_2654663577____hygCtx___hyg_2__value),((lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__1_00___x40_Lean_LibrarySuggestions_Basic_3406067637____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_LibrarySuggestions_initFn___closed__4_00___x40_Lean_LibrarySuggestions_Basic_2654663577____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__4_00___x40_Lean_LibrarySuggestions_Basic_2654663577____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_2654663577____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_2654663577____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_librarySuggestionsExt;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__1_spec__2___closed__0;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__1_spec__2___closed__1;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__1_spec__2___closed__2;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__1_spec__2___closed__3;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__1_spec__2___closed__4;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__1_spec__2___closed__5;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__1_spec__2___closed__6;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0_value;
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2_value;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4_value;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__6 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__6_value;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__8 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__8_value;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__10_value;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__12_value;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13;
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__0_value;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__1;
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__2 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__2_value;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_LibrarySuggestions_initFn___lam__0___closed__0_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2_;
static lean_object* l_Lean_LibrarySuggestions_initFn___lam__0___closed__1_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2_;
static lean_object* l_Lean_LibrarySuggestions_initFn___lam__0___closed__2_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2_;
static const lean_string_object l_Lean_LibrarySuggestions_initFn___lam__0___closed__3_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Selector"};
static const lean_object* l_Lean_LibrarySuggestions_initFn___lam__0___closed__3_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_initFn___lam__0___closed__3_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_LibrarySuggestions_initFn___lam__0___closed__4_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__2_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_LibrarySuggestions_initFn___lam__0___closed__4_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_initFn___lam__0___closed__4_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__3_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(33, 7, 235, 60, 247, 182, 234, 218)}};
static const lean_ctor_object l_Lean_LibrarySuggestions_initFn___lam__0___closed__4_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_initFn___lam__0___closed__4_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__value_aux_1),((lean_object*)&l_Lean_LibrarySuggestions_initFn___lam__0___closed__3_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(124, 39, 7, 240, 9, 153, 37, 224)}};
static const lean_object* l_Lean_LibrarySuggestions_initFn___lam__0___closed__4_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_initFn___lam__0___closed__4_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__value;
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
static lean_object* l_Lean_LibrarySuggestions_initFn___lam__0___closed__5_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2_;
static const lean_string_object l_Lean_LibrarySuggestions_initFn___lam__0___closed__6_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "declaration '"};
static const lean_object* l_Lean_LibrarySuggestions_initFn___lam__0___closed__6_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_initFn___lam__0___closed__6_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__value;
static lean_object* l_Lean_LibrarySuggestions_initFn___lam__0___closed__7_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2_;
static const lean_string_object l_Lean_LibrarySuggestions_initFn___lam__0___closed__8_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "' must have type `Selector`"};
static const lean_object* l_Lean_LibrarySuggestions_initFn___lam__0___closed__8_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_initFn___lam__0___closed__8_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__value;
static lean_object* l_Lean_LibrarySuggestions_initFn___lam__0___closed__9_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2_;
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_initFn___lam__0_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_initFn___lam__0_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_LibrarySuggestions_initFn___closed__0_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_LibrarySuggestions_initFn___lam__0_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2____boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_LibrarySuggestions_initFn___closed__0_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__0_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_LibrarySuggestions_initFn___closed__1_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "library_suggestions"};
static const lean_object* l_Lean_LibrarySuggestions_initFn___closed__1_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__1_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_LibrarySuggestions_initFn___closed__2_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__1_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(112, 230, 242, 174, 112, 244, 220, 236)}};
static const lean_object* l_Lean_LibrarySuggestions_initFn___closed__2_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__2_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_LibrarySuggestions_initFn___closed__3_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "library suggestions selector"};
static const lean_object* l_Lean_LibrarySuggestions_initFn___closed__3_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__3_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_LibrarySuggestions_initFn___closed__4_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "librarySuggestionsAttr"};
static const lean_object* l_Lean_LibrarySuggestions_initFn___closed__4_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__4_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_LibrarySuggestions_initFn___closed__5_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__2_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_LibrarySuggestions_initFn___closed__5_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__5_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__3_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(33, 7, 235, 60, 247, 182, 234, 218)}};
static const lean_ctor_object l_Lean_LibrarySuggestions_initFn___closed__5_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__5_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__value_aux_1),((lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__4_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(126, 31, 118, 101, 75, 194, 175, 121)}};
static const lean_object* l_Lean_LibrarySuggestions_initFn___closed__5_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__5_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__value;
lean_object* l_Lean_registerTagAttribute(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_librarySuggestionsAttr;
extern lean_object* l_Lean_Elab_abortCommandExceptionId;
static lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00Lean_LibrarySuggestions_getSelectorImpl_spec__0_spec__1___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00Lean_LibrarySuggestions_getSelectorImpl_spec__0_spec__1___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00Lean_LibrarySuggestions_getSelectorImpl_spec__0_spec__1___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_LibrarySuggestions_getSelectorImpl_spec__0_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_LibrarySuggestions_getSelectorImpl_spec__0_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_LibrarySuggestions_getSelectorImpl_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_LibrarySuggestions_getSelectorImpl_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_LibrarySuggestions_getSelectorImpl_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_LibrarySuggestions_getSelectorImpl_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_has_compile_error(lean_object*, lean_object*);
lean_object* l_Lean_Environment_evalConstCheck___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_evalConstCheck___at___00Lean_LibrarySuggestions_getSelectorImpl_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_evalConstCheck___at___00Lean_LibrarySuggestions_getSelectorImpl_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_getSelectorImpl(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_getSelectorImpl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00Lean_LibrarySuggestions_getSelectorImpl_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00Lean_LibrarySuggestions_getSelectorImpl_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_evalConstCheck___at___00Lean_LibrarySuggestions_getSelectorImpl_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_evalConstCheck___at___00Lean_LibrarySuggestions_getSelectorImpl_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_LibrarySuggestions_getSelectorImpl_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_LibrarySuggestions_getSelectorImpl_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_LibrarySuggestions_getSelectorImpl_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_LibrarySuggestions_getSelectorImpl_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_LibrarySuggestions_select___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 180, .m_capacity = 180, .m_length = 179, .m_data = "No library suggestions engine registered. (Add `import Lean.LibrarySuggestions.Default` to use Lean's built-in engine, or use `set_library_suggestions` to configure a custom one.)"};
static const lean_object* l_Lean_LibrarySuggestions_select___closed__0 = (const lean_object*)&l_Lean_LibrarySuggestions_select___closed__0_value;
static lean_object* l_Lean_LibrarySuggestions_select___closed__1;
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_select(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_select___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__2___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Command_instInhabitedScope_default;
lean_object* l_List_head_x21___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__2_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__3_spec__11_spec__17___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__3_spec__11_spec__17___lam__0___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__3_spec__11_spec__17___lam__0___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__3_spec__11_spec__17___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__3_spec__11_spec__17___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__3_spec__11_spec__17_spec__21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__3_spec__11_spec__17_spec__21___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__3_spec__11_spec__17___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__3_spec__11_spec__17___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__3_spec__11_spec__17___closed__0_value;
lean_object* l_Lean_Elab_Command_getScope___redArg(lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Elab_Command_getRef___redArg(lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t, uint8_t);
extern lean_object* l_Lean_warningAsError;
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__3_spec__11_spec__17(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__3_spec__11_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__3_spec__11(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__3_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_expandMacroImpl_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ResolveName_resolveNamespace(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkPrivateName(lean_object*, lean_object*);
lean_object* l_Lean_privateToUserName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__9_spec__13___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__9_spec__13___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__9___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__9___redArg___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__3_spec__11_spec__17___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__1___redArg___closed__0 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__1___redArg___closed__0_value;
extern lean_object* l_Lean_inheritedTraceOptions;
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqExtraModUse_beq(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7_spec__10_spec__15_spec__21___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7_spec__10_spec__15_spec__21___redArg___boxed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7_spec__10_spec__15___redArg___closed__0;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7_spec__10_spec__15___redArg___closed__1;
lean_object* lean_usize_to_nat(size_t);
size_t lean_usize_shift_right(size_t, size_t);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7_spec__10_spec__15___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7_spec__10_spec__15___redArg___boxed(lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_instHashableExtraModUse_hash(lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7_spec__10___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7_spec__10___redArg___boxed(lean_object*, lean_object*);
static double l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__2___closed__0;
static lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__2___closed__1;
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instBEqExtraModUse_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instBEqExtraModUse_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___closed__0 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___closed__0_value;
lean_object* l_Lean_instHashableExtraModUse_hash___boxed(lean_object*);
static const lean_closure_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instHashableExtraModUse_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___closed__1 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___closed__1_value;
lean_object* l_Lean_PersistentHashMap_empty(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___closed__2;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "extraModUses"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___closed__3 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___closed__3_value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___closed__3_value),LEAN_SCALAR_PTR_LITERAL(27, 95, 70, 98, 97, 66, 56, 109)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___closed__4 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___closed__4_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = " extra mod use "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___closed__5 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___closed__5_value;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___closed__6;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " of "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___closed__7 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___closed__7_value;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___closed__8;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___closed__9;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "recording "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___closed__10 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___closed__10_value;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___closed__11;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___closed__12 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___closed__12_value;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___closed__13;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "regular"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___closed__14 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___closed__14_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "meta"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___closed__15 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___closed__15_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "private"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___closed__16 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___closed__16_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "public"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___closed__17 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___closed__17_value;
extern lean_object* l___private_Lean_ExtraModUses_0__Lean_extraModUses;
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedEffectiveImport_default;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__8(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4___closed__0 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4___closed__0_value;
lean_object* l_Lean_Name_hash___override___boxed(lean_object*);
static const lean_closure_object l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_hash___override___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4___closed__1 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4___closed__1_value;
lean_object* l_Std_HashMap_instInhabited(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4___closed__2;
static lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4___closed__3;
extern lean_object* l_Lean_indirectModUseExt;
uint8_t l_Lean_isMarkedMeta(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__6(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__8___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "runtime"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__8___redArg___closed__0 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__8___redArg___closed__0_value;
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__8___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "maxRecDepth"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__8___redArg___closed__1 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__8___redArg___closed__1_value;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__8___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__8___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(2, 128, 123, 132, 117, 90, 116, 101)}};
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__8___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__8___redArg___closed__2_value_aux_0),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__8___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(88, 230, 219, 180, 63, 89, 202, 3)}};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__8___redArg___closed__2 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__8___redArg___closed__2_value;
extern lean_object* l_Lean_maxRecDepthErrorMessage;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__8___redArg___closed__3;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__8___redArg___closed__4;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__8___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__8___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__8___redArg___boxed(lean_object*, lean_object*);
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__7_spec__13_spec__18_spec__21___closed__0;
static const lean_string_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__7_spec__13_spec__18_spec__21___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "while expanding"};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__7_spec__13_spec__18_spec__21___closed__1 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__7_spec__13_spec__18_spec__21___closed__1_value;
static const lean_ctor_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__7_spec__13_spec__18_spec__21___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__7_spec__13_spec__18_spec__21___closed__1_value)}};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__7_spec__13_spec__18_spec__21___closed__2 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__7_spec__13_spec__18_spec__21___closed__2_value;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__7_spec__13_spec__18_spec__21___closed__3;
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__7_spec__13_spec__18_spec__21(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__7_spec__13_spec__18___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "with resulting expansion"};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__7_spec__13_spec__18___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__7_spec__13_spec__18___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__7_spec__13_spec__18___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__7_spec__13_spec__18___redArg___closed__0_value)}};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__7_spec__13_spec__18___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__7_spec__13_spec__18___redArg___closed__1_value;
static lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__7_spec__13_spec__18___redArg___closed__2;
extern lean_object* l_Lean_Elab_pp_macroStack;
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__7_spec__13_spec__18___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__7_spec__13_spec__18___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__7_spec__13___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__7_spec__13___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ResolveName_resolveGlobalName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1___redArg___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 158, .m_capacity = 158, .m_length = 157, .m_data = "maximum recursion depth has been reached\nuse `set_option maxRecDepth <num>` to increase limit\nuse `set_option diagnostics true` to get diagnostic information"};
static const lean_object* l_Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1___redArg___closed__0_value;
lean_object* l_Lean_Elab_Command_getCurrMacroScope___redArg(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "setLibrarySuggestionsCmd"};
static const lean_object* l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__0 = (const lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__0_value;
static const lean_ctor_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__2_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__1_value_aux_0),((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__0_value),LEAN_SCALAR_PTR_LITERAL(101, 118, 147, 72, 144, 22, 225, 39)}};
static const lean_object* l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__1 = (const lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__1_value;
static const lean_string_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__2 = (const lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__2_value;
static const lean_string_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__3 = (const lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__3_value;
static const lean_string_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "declaration"};
static const lean_object* l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__4 = (const lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__4_value;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__2_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__5_value_aux_0),((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__5_value_aux_1),((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__3_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__5_value_aux_2),((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__4_value),LEAN_SCALAR_PTR_LITERAL(157, 246, 223, 221, 242, 35, 238, 117)}};
static const lean_object* l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__5 = (const lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__5_value;
static const lean_string_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "declModifiers"};
static const lean_object* l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__6 = (const lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__6_value;
static const lean_ctor_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__2_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__7_value_aux_0),((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__7_value_aux_1),((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__3_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__7_value_aux_2),((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__6_value),LEAN_SCALAR_PTR_LITERAL(0, 165, 146, 53, 36, 89, 7, 202)}};
static const lean_object* l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__7 = (const lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__7_value;
static const lean_string_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__8 = (const lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__8_value;
static const lean_ctor_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__8_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__9 = (const lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__9_value;
lean_object* l_Array_mkArray0(lean_object*);
static lean_object* l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__10;
static const lean_string_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__11 = (const lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__11_value;
static const lean_string_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "attributes"};
static const lean_object* l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__12 = (const lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__12_value;
static const lean_ctor_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__2_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__13_value_aux_0),((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__13_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__13_value_aux_1),((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__11_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__13_value_aux_2),((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__12_value),LEAN_SCALAR_PTR_LITERAL(66, 184, 196, 169, 25, 125, 40, 35)}};
static const lean_object* l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__13 = (const lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__13_value;
static const lean_string_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "@["};
static const lean_object* l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__14 = (const lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__14_value;
static const lean_string_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "attrInstance"};
static const lean_object* l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__15 = (const lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__15_value;
static const lean_ctor_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__2_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__16_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__16_value_aux_0),((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__16_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__16_value_aux_1),((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__11_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__16_value_aux_2),((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__15_value),LEAN_SCALAR_PTR_LITERAL(241, 75, 242, 110, 47, 5, 20, 104)}};
static const lean_object* l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__16 = (const lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__16_value;
static const lean_string_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "attrKind"};
static const lean_object* l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__17 = (const lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__17_value;
static const lean_ctor_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__18_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__2_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__18_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__18_value_aux_0),((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__18_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__18_value_aux_1),((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__11_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__18_value_aux_2),((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__17_value),LEAN_SCALAR_PTR_LITERAL(32, 164, 20, 104, 12, 221, 204, 110)}};
static const lean_object* l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__18 = (const lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__18_value;
static const lean_string_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Attr"};
static const lean_object* l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__19 = (const lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__19_value;
static const lean_string_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "simple"};
static const lean_object* l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__20 = (const lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__20_value;
static const lean_ctor_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__21_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__2_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__21_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__21_value_aux_0),((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__21_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__21_value_aux_1),((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__19_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__21_value_aux_2),((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__20_value),LEAN_SCALAR_PTR_LITERAL(107, 67, 254, 234, 65, 174, 209, 53)}};
static const lean_object* l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__21 = (const lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__21_value;
static const lean_string_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "expose"};
static const lean_object* l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__22 = (const lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__22_value;
lean_object* l_String_toRawSubstring_x27(lean_object*);
static lean_object* l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__23;
static const lean_ctor_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__22_value),LEAN_SCALAR_PTR_LITERAL(170, 113, 233, 77, 243, 78, 243, 129)}};
static const lean_object* l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__24 = (const lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__24_value;
static const lean_string_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__25 = (const lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__25_value;
static lean_object* l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__26;
static const lean_string_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__27 = (const lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__27_value;
static const lean_ctor_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__28_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__2_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__28_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__28_value_aux_0),((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__28_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__28_value_aux_1),((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__3_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__28_value_aux_2),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___closed__17_value),LEAN_SCALAR_PTR_LITERAL(99, 134, 241, 204, 211, 206, 124, 144)}};
static const lean_object* l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__28 = (const lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__28_value;
static const lean_string_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "definition"};
static const lean_object* l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__29 = (const lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__29_value;
static const lean_ctor_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__30_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__2_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__30_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__30_value_aux_0),((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__30_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__30_value_aux_1),((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__3_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__30_value_aux_2),((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__29_value),LEAN_SCALAR_PTR_LITERAL(248, 187, 217, 228, 39, 184, 218, 135)}};
static const lean_object* l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__30 = (const lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__30_value;
static const lean_string_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "def"};
static const lean_object* l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__31 = (const lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__31_value;
static const lean_string_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "declId"};
static const lean_object* l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__32 = (const lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__32_value;
static const lean_ctor_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__33_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__2_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__33_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__33_value_aux_0),((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__33_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__33_value_aux_1),((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__3_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__33_value_aux_2),((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__32_value),LEAN_SCALAR_PTR_LITERAL(243, 92, 136, 33, 216, 98, 92, 25)}};
static const lean_object* l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__33 = (const lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__33_value;
static lean_object* l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__34;
static lean_object* l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__35;
static lean_object* l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__36;
static const lean_string_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "optDeclSig"};
static const lean_object* l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__37 = (const lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__37_value;
static const lean_ctor_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__38_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__2_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__38_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__38_value_aux_0),((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__38_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__38_value_aux_1),((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__3_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__38_value_aux_2),((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__37_value),LEAN_SCALAR_PTR_LITERAL(26, 9, 103, 232, 183, 57, 246, 75)}};
static const lean_object* l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__38 = (const lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__38_value;
static const lean_string_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "typeSpec"};
static const lean_object* l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__39 = (const lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__39_value;
static const lean_ctor_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__40_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__2_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__40_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__40_value_aux_0),((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__40_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__40_value_aux_1),((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__11_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__40_value_aux_2),((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__39_value),LEAN_SCALAR_PTR_LITERAL(77, 126, 241, 117, 174, 189, 108, 62)}};
static const lean_object* l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__40 = (const lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__40_value;
static const lean_string_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__41 = (const lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__41_value;
static const lean_string_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "Lean.LibrarySuggestions.Selector"};
static const lean_object* l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__42 = (const lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__42_value;
static lean_object* l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__43;
static const lean_ctor_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_initFn___lam__0___closed__4_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__44 = (const lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__44_value;
static const lean_ctor_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_initFn___lam__0___closed__4_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__value)}};
static const lean_object* l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__45 = (const lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__45_value;
static const lean_ctor_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__45_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__46 = (const lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__46_value;
static const lean_ctor_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__44_value),((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__46_value)}};
static const lean_object* l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__47 = (const lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__47_value;
static const lean_string_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "declValSimple"};
static const lean_object* l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__48 = (const lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__48_value;
static const lean_ctor_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__49_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__2_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__49_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__49_value_aux_0),((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__49_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__49_value_aux_1),((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__3_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__49_value_aux_2),((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__48_value),LEAN_SCALAR_PTR_LITERAL(228, 117, 47, 248, 145, 185, 135, 188)}};
static const lean_object* l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__49 = (const lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__49_value;
static const lean_string_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ":="};
static const lean_object* l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__50 = (const lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__50_value;
static const lean_string_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Termination"};
static const lean_object* l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__51 = (const lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__51_value;
static const lean_string_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "suffix"};
static const lean_object* l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__52 = (const lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__52_value;
static const lean_ctor_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__53_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__2_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__53_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__53_value_aux_0),((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__53_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__53_value_aux_1),((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__51_value),LEAN_SCALAR_PTR_LITERAL(128, 225, 226, 49, 186, 161, 212, 105)}};
static const lean_ctor_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__53_value_aux_2),((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__52_value),LEAN_SCALAR_PTR_LITERAL(245, 187, 99, 45, 217, 244, 244, 120)}};
static const lean_object* l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__53 = (const lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__53_value;
static const lean_string_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__54_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "_librarySuggestions"};
static const lean_object* l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__54 = (const lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__54_value;
static const lean_ctor_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__55_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__54_value),LEAN_SCALAR_PTR_LITERAL(147, 241, 103, 239, 116, 245, 70, 103)}};
static const lean_object* l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__55 = (const lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__55_value;
lean_object* l_Lean_Macro_addMacroScope(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__56_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Macro_addMacroScope, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__55_value)} };
static const lean_object* l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__56 = (const lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__56_value;
static const lean_string_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__57_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Basic"};
static const lean_object* l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__57 = (const lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__57_value;
static const lean_ctor_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__58_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__2_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__58_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__58_value_aux_0),((lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__3_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(33, 7, 235, 60, 247, 182, 234, 218)}};
static const lean_ctor_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__58_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__58_value_aux_1),((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__57_value),LEAN_SCALAR_PTR_LITERAL(198, 90, 67, 198, 19, 167, 19, 166)}};
static const lean_object* l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__58 = (const lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__58_value;
static const lean_string_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__59_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 95, .m_capacity = 95, .m_length = 94, .m_data = "Add `import Lean.LibrarySuggestions.Basic` before using the `set_library_suggestions` command."};
static const lean_object* l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__59 = (const lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__59_value;
static const lean_ctor_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__60_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__59_value)}};
static const lean_object* l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__60 = (const lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__60_value;
static lean_object* l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__61;
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_syntax_ident(lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabCommand(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
uint8_t l_Array_contains___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_elabSetLibrarySuggestions(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__8(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__9(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__9___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__7_spec__13(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__7_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7_spec__10(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7_spec__10___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__9_spec__13(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__9_spec__13___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__7_spec__13_spec__18(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__7_spec__13_spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7_spec__10_spec__15(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7_spec__10_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7_spec__10_spec__15_spec__21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7_spec__10_spec__15_spec__21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___regBuiltin_Lean_LibrarySuggestions_elabSetLibrarySuggestions__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "elabSetLibrarySuggestions"};
static const lean_object* l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___regBuiltin_Lean_LibrarySuggestions_elabSetLibrarySuggestions__1___closed__0 = (const lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___regBuiltin_Lean_LibrarySuggestions_elabSetLibrarySuggestions__1___closed__0_value;
static const lean_ctor_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___regBuiltin_Lean_LibrarySuggestions_elabSetLibrarySuggestions__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__2_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___regBuiltin_Lean_LibrarySuggestions_elabSetLibrarySuggestions__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___regBuiltin_Lean_LibrarySuggestions_elabSetLibrarySuggestions__1___closed__1_value_aux_0),((lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__3_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(33, 7, 235, 60, 247, 182, 234, 218)}};
static const lean_ctor_object l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___regBuiltin_Lean_LibrarySuggestions_elabSetLibrarySuggestions__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___regBuiltin_Lean_LibrarySuggestions_elabSetLibrarySuggestions__1___closed__1_value_aux_1),((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___regBuiltin_Lean_LibrarySuggestions_elabSetLibrarySuggestions__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(8, 220, 99, 96, 165, 4, 120, 100)}};
static const lean_object* l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___regBuiltin_Lean_LibrarySuggestions_elabSetLibrarySuggestions__1___closed__1 = (const lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___regBuiltin_Lean_LibrarySuggestions_elabSetLibrarySuggestions__1___closed__1_value;
extern lean_object* l_Lean_Elab_Command_commandElabAttribute;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___regBuiltin_Lean_LibrarySuggestions_elabSetLibrarySuggestions__1();
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___regBuiltin_Lean_LibrarySuggestions_elabSetLibrarySuggestions__1___boxed(lean_object*);
static double l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_LibrarySuggestions_evalSuggestions_spec__2___closed__0;
uint8_t lean_float_beq(double, double);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_LibrarySuggestions_evalSuggestions_spec__2(lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_LibrarySuggestions_evalSuggestions_spec__2___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_LibrarySuggestions_evalSuggestions_spec__1_spec__1_spec__2___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_LibrarySuggestions_evalSuggestions_spec__1_spec__1_spec__2___lam__0___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_LibrarySuggestions_evalSuggestions_spec__1_spec__1_spec__2___lam__0___closed__0_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_LibrarySuggestions_evalSuggestions_spec__1_spec__1_spec__2___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "unsolvedGoals"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_LibrarySuggestions_evalSuggestions_spec__1_spec__1_spec__2___lam__0___closed__1 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_LibrarySuggestions_evalSuggestions_spec__1_spec__1_spec__2___lam__0___closed__1_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_LibrarySuggestions_evalSuggestions_spec__1_spec__1_spec__2___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "synthPlaceholder"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_LibrarySuggestions_evalSuggestions_spec__1_spec__1_spec__2___lam__0___closed__2 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_LibrarySuggestions_evalSuggestions_spec__1_spec__1_spec__2___lam__0___closed__2_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_LibrarySuggestions_evalSuggestions_spec__1_spec__1_spec__2___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lean"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_LibrarySuggestions_evalSuggestions_spec__1_spec__1_spec__2___lam__0___closed__3 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_LibrarySuggestions_evalSuggestions_spec__1_spec__1_spec__2___lam__0___closed__3_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_LibrarySuggestions_evalSuggestions_spec__1_spec__1_spec__2___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "inductionWithNoAlts"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_LibrarySuggestions_evalSuggestions_spec__1_spec__1_spec__2___lam__0___closed__4 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_LibrarySuggestions_evalSuggestions_spec__1_spec__1_spec__2___lam__0___closed__4_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_LibrarySuggestions_evalSuggestions_spec__1_spec__1_spec__2___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "_namedError"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_LibrarySuggestions_evalSuggestions_spec__1_spec__1_spec__2___lam__0___closed__5 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_LibrarySuggestions_evalSuggestions_spec__1_spec__1_spec__2___lam__0___closed__5_value;
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_LibrarySuggestions_evalSuggestions_spec__1_spec__1_spec__2___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_LibrarySuggestions_evalSuggestions_spec__1_spec__1_spec__2___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_LibrarySuggestions_evalSuggestions_spec__1_spec__1_spec__2(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_LibrarySuggestions_evalSuggestions_spec__1_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logInfo___at___00Lean_LibrarySuggestions_evalSuggestions_spec__1_spec__1(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logInfo___at___00Lean_LibrarySuggestions_evalSuggestions_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logInfo___at___00Lean_LibrarySuggestions_evalSuggestions_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logInfo___at___00Lean_LibrarySuggestions_evalSuggestions_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_LibrarySuggestions_evalSuggestions_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " ["};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_LibrarySuggestions_evalSuggestions_spec__0___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_LibrarySuggestions_evalSuggestions_spec__0___redArg___closed__0_value;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_LibrarySuggestions_evalSuggestions_spec__0___redArg___closed__1;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_LibrarySuggestions_evalSuggestions_spec__0___redArg___closed__2;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_LibrarySuggestions_evalSuggestions_spec__0___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "  "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_LibrarySuggestions_evalSuggestions_spec__0___redArg___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_LibrarySuggestions_evalSuggestions_spec__0___redArg___closed__3_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_LibrarySuggestions_evalSuggestions_spec__0___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_LibrarySuggestions_evalSuggestions_spec__0___redArg___closed__3_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_LibrarySuggestions_evalSuggestions_spec__0___redArg___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_LibrarySuggestions_evalSuggestions_spec__0___redArg___closed__4_value;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_LibrarySuggestions_evalSuggestions_spec__0___redArg___closed__5;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_LibrarySuggestions_evalSuggestions_spec__0___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = " (score: "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_LibrarySuggestions_evalSuggestions_spec__0___redArg___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_LibrarySuggestions_evalSuggestions_spec__0___redArg___closed__6_value;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_LibrarySuggestions_evalSuggestions_spec__0___redArg___closed__7;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_LibrarySuggestions_evalSuggestions_spec__0___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_LibrarySuggestions_evalSuggestions_spec__0___redArg___closed__8 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_LibrarySuggestions_evalSuggestions_spec__0___redArg___closed__8_value;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_LibrarySuggestions_evalSuggestions_spec__0___redArg___closed__9;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_LibrarySuggestions_evalSuggestions_spec__0___redArg(uint8_t, lean_object*, size_t, size_t, lean_object*);
lean_object* lean_float_to_string(double);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_LibrarySuggestions_evalSuggestions_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_LibrarySuggestions_evalSuggestions___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Library suggestions:"};
static const lean_object* l_Lean_LibrarySuggestions_evalSuggestions___redArg___lam__1___closed__0 = (const lean_object*)&l_Lean_LibrarySuggestions_evalSuggestions___redArg___lam__1___closed__0_value;
static const lean_ctor_object l_Lean_LibrarySuggestions_evalSuggestions___redArg___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_evalSuggestions___redArg___lam__1___closed__0_value)}};
static const lean_object* l_Lean_LibrarySuggestions_evalSuggestions___redArg___lam__1___closed__1 = (const lean_object*)&l_Lean_LibrarySuggestions_evalSuggestions___redArg___lam__1___closed__1_value;
static lean_object* l_Lean_LibrarySuggestions_evalSuggestions___redArg___lam__1___closed__2;
lean_object* l_Lean_Elab_Tactic_getMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_replaceMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_evalSuggestions___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_evalSuggestions___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_LibrarySuggestions_evalSuggestions___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_LibrarySuggestions_evalSuggestions___redArg___lam__1___boxed, .m_arity = 10, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_Selector_postFilter___closed__0_value)} };
static const lean_object* l_Lean_LibrarySuggestions_evalSuggestions___redArg___closed__0 = (const lean_object*)&l_Lean_LibrarySuggestions_evalSuggestions___redArg___closed__0_value;
lean_object* l_Lean_Elab_Tactic_withMainContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_evalSuggestions___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_evalSuggestions___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_evalSuggestions(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_evalSuggestions___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_LibrarySuggestions_evalSuggestions_spec__0(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_LibrarySuggestions_evalSuggestions_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_LibrarySuggestions_evalSuggestions___regBuiltin_Lean_LibrarySuggestions_evalSuggestions__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "suggestions"};
static const lean_object* l_Lean_LibrarySuggestions_evalSuggestions___regBuiltin_Lean_LibrarySuggestions_evalSuggestions__1___closed__0 = (const lean_object*)&l_Lean_LibrarySuggestions_evalSuggestions___regBuiltin_Lean_LibrarySuggestions_evalSuggestions__1___closed__0_value;
static const lean_ctor_object l_Lean_LibrarySuggestions_evalSuggestions___regBuiltin_Lean_LibrarySuggestions_evalSuggestions__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__2_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_LibrarySuggestions_evalSuggestions___regBuiltin_Lean_LibrarySuggestions_evalSuggestions__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_evalSuggestions___regBuiltin_Lean_LibrarySuggestions_evalSuggestions__1___closed__1_value_aux_0),((lean_object*)&l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_LibrarySuggestions_evalSuggestions___regBuiltin_Lean_LibrarySuggestions_evalSuggestions__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_evalSuggestions___regBuiltin_Lean_LibrarySuggestions_evalSuggestions__1___closed__1_value_aux_1),((lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__8_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_LibrarySuggestions_evalSuggestions___regBuiltin_Lean_LibrarySuggestions_evalSuggestions__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_evalSuggestions___regBuiltin_Lean_LibrarySuggestions_evalSuggestions__1___closed__1_value_aux_2),((lean_object*)&l_Lean_LibrarySuggestions_evalSuggestions___regBuiltin_Lean_LibrarySuggestions_evalSuggestions__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(33, 205, 204, 217, 194, 115, 0, 147)}};
static const lean_object* l_Lean_LibrarySuggestions_evalSuggestions___regBuiltin_Lean_LibrarySuggestions_evalSuggestions__1___closed__1 = (const lean_object*)&l_Lean_LibrarySuggestions_evalSuggestions___regBuiltin_Lean_LibrarySuggestions_evalSuggestions__1___closed__1_value;
static const lean_string_object l_Lean_LibrarySuggestions_evalSuggestions___regBuiltin_Lean_LibrarySuggestions_evalSuggestions__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "evalSuggestions"};
static const lean_object* l_Lean_LibrarySuggestions_evalSuggestions___regBuiltin_Lean_LibrarySuggestions_evalSuggestions__1___closed__2 = (const lean_object*)&l_Lean_LibrarySuggestions_evalSuggestions___regBuiltin_Lean_LibrarySuggestions_evalSuggestions__1___closed__2_value;
static const lean_ctor_object l_Lean_LibrarySuggestions_evalSuggestions___regBuiltin_Lean_LibrarySuggestions_evalSuggestions__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__2_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_LibrarySuggestions_evalSuggestions___regBuiltin_Lean_LibrarySuggestions_evalSuggestions__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_evalSuggestions___regBuiltin_Lean_LibrarySuggestions_evalSuggestions__1___closed__3_value_aux_0),((lean_object*)&l_Lean_LibrarySuggestions_initFn___closed__3_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(33, 7, 235, 60, 247, 182, 234, 218)}};
static const lean_ctor_object l_Lean_LibrarySuggestions_evalSuggestions___regBuiltin_Lean_LibrarySuggestions_evalSuggestions__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_LibrarySuggestions_evalSuggestions___regBuiltin_Lean_LibrarySuggestions_evalSuggestions__1___closed__3_value_aux_1),((lean_object*)&l_Lean_LibrarySuggestions_evalSuggestions___regBuiltin_Lean_LibrarySuggestions_evalSuggestions__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(189, 185, 91, 28, 225, 145, 246, 66)}};
static const lean_object* l_Lean_LibrarySuggestions_evalSuggestions___regBuiltin_Lean_LibrarySuggestions_evalSuggestions__1___closed__3 = (const lean_object*)&l_Lean_LibrarySuggestions_evalSuggestions___regBuiltin_Lean_LibrarySuggestions_evalSuggestions__1___closed__3_value;
extern lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_evalSuggestions___regBuiltin_Lean_LibrarySuggestions_evalSuggestions__1();
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_evalSuggestions___regBuiltin_Lean_LibrarySuggestions_evalSuggestions__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__0___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = lean_apply_7(x_1, x_3, x_2, x_4, x_5, x_6, x_7, lean_box(0));
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__0___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_withLocalDecl___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__0___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__0___redArg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__0___redArg___lam__0___boxed), 8, 2);
lean_closure_set(x_12, 0, x_4);
lean_closure_set(x_12, 1, x_6);
x_13 = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), x_1, x_2, x_3, x_12, x_5, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
return x_13;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_13);
if (x_17 == 0)
{
return x_13;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_13, 0);
lean_inc(x_18);
lean_dec(x_13);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; uint8_t x_13; lean_object* x_14; 
x_12 = lean_unbox(x_2);
x_13 = lean_unbox(x_5);
x_14 = l_Lean_Meta_withLocalDecl___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__0___redArg(x_1, x_12, x_3, x_4, x_13, x_6, x_7, x_8, x_9, x_10);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__0(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_withLocalDecl___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; uint8_t x_14; lean_object* x_15; 
x_13 = lean_unbox(x_3);
x_14 = lean_unbox(x_6);
x_15 = l_Lean_Meta_withLocalDecl___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__0(x_1, x_2, x_13, x_4, x_5, x_14, x_7, x_8, x_9, x_10, x_11);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__3___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__0___redArg___lam__0___boxed), 8, 2);
lean_closure_set(x_13, 0, x_4);
lean_closure_set(x_13, 1, x_7);
x_14 = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), x_1, x_2, x_3, x_13, x_5, x_6, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
return x_14;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_14);
if (x_18 == 0)
{
return x_14;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_14, 0);
lean_inc(x_19);
lean_dec(x_14);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; uint8_t x_14; lean_object* x_15; 
x_13 = lean_unbox(x_5);
x_14 = lean_unbox(x_6);
x_15 = l_Lean_Meta_withLetDecl___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__3___redArg(x_1, x_2, x_3, x_4, x_13, x_14, x_7, x_8, x_9, x_10, x_11);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_withLetDecl___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__3___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; uint8_t x_15; lean_object* x_16; 
x_14 = lean_unbox(x_6);
x_15 = lean_unbox(x_7);
x_16 = l_Lean_Meta_withLetDecl___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__3(x_1, x_2, x_3, x_4, x_5, x_14, x_15, x_8, x_9, x_10, x_11, x_12);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_isInstanceReducible___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__4___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_st_ref_get(x_3);
x_6 = lean_ctor_get(x_5, 0);
lean_inc_ref(x_6);
lean_dec(x_5);
x_7 = l_Lean_isInstanceReducibleCore(x_6, x_1);
x_8 = lean_box(x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_2);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_isInstanceReducible___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__4___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_isInstanceReducible___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__4___redArg(x_1, x_2, x_3);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_isInstanceReducible___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_isInstanceReducible___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__4___redArg(x_1, x_2, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_isInstanceReducible___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_isInstanceReducible___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__4(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__2_spec__3_spec__6_spec__7___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; size_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; uint64_t x_16; size_t x_17; size_t x_18; size_t x_19; size_t x_20; size_t x_21; lean_object* x_22; lean_object* x_23; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_array_get_size(x_1);
x_7 = lean_ptr_addr(x_4);
x_8 = lean_usize_to_uint64(x_7);
x_9 = 11;
x_10 = lean_uint64_mix_hash(x_8, x_9);
x_11 = 32;
x_12 = lean_uint64_shift_right(x_10, x_11);
x_13 = lean_uint64_xor(x_10, x_12);
x_14 = 16;
x_15 = lean_uint64_shift_right(x_13, x_14);
x_16 = lean_uint64_xor(x_13, x_15);
x_17 = lean_uint64_to_usize(x_16);
x_18 = lean_usize_of_nat(x_6);
x_19 = 1;
x_20 = lean_usize_sub(x_18, x_19);
x_21 = lean_usize_land(x_17, x_20);
x_22 = lean_array_uget(x_1, x_21);
lean_ctor_set(x_2, 2, x_22);
x_23 = lean_array_uset(x_1, x_21, x_2);
x_1 = x_23;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; size_t x_29; uint64_t x_30; uint64_t x_31; uint64_t x_32; uint64_t x_33; uint64_t x_34; uint64_t x_35; uint64_t x_36; uint64_t x_37; uint64_t x_38; size_t x_39; size_t x_40; size_t x_41; size_t x_42; size_t x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_25 = lean_ctor_get(x_2, 0);
x_26 = lean_ctor_get(x_2, 1);
x_27 = lean_ctor_get(x_2, 2);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_2);
x_28 = lean_array_get_size(x_1);
x_29 = lean_ptr_addr(x_25);
x_30 = lean_usize_to_uint64(x_29);
x_31 = 11;
x_32 = lean_uint64_mix_hash(x_30, x_31);
x_33 = 32;
x_34 = lean_uint64_shift_right(x_32, x_33);
x_35 = lean_uint64_xor(x_32, x_34);
x_36 = 16;
x_37 = lean_uint64_shift_right(x_35, x_36);
x_38 = lean_uint64_xor(x_35, x_37);
x_39 = lean_uint64_to_usize(x_38);
x_40 = lean_usize_of_nat(x_28);
x_41 = 1;
x_42 = lean_usize_sub(x_40, x_41);
x_43 = lean_usize_land(x_39, x_42);
x_44 = lean_array_uget(x_1, x_43);
x_45 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_45, 0, x_25);
lean_ctor_set(x_45, 1, x_26);
lean_ctor_set(x_45, 2, x_44);
x_46 = lean_array_uset(x_1, x_43, x_45);
x_1 = x_46;
x_2 = x_27;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__2_spec__3_spec__6___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_1, x_4);
if (x_5 == 0)
{
lean_dec_ref(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_array_fget(x_2, x_1);
x_7 = lean_box(0);
x_8 = lean_array_fset(x_2, x_1, x_7);
x_9 = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__2_spec__3_spec__6_spec__7___redArg(x_3, x_6);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_1, x_10);
lean_dec(x_1);
x_1 = x_11;
x_2 = x_8;
x_3 = x_9;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__2_spec__3___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(2u);
x_4 = lean_nat_mul(x_2, x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_box(0);
x_7 = lean_mk_array(x_4, x_6);
x_8 = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__2_spec__3_spec__6___redArg(x_5, x_1, x_7);
return x_8;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__1_spec__1___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; size_t x_6; size_t x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_ptr_addr(x_4);
x_7 = lean_ptr_addr(x_1);
x_8 = lean_usize_dec_eq(x_6, x_7);
if (x_8 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__1_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__1_spec__1___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; size_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; uint64_t x_16; size_t x_17; size_t x_18; size_t x_19; size_t x_20; size_t x_21; lean_object* x_22; uint8_t x_23; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_array_get_size(x_5);
x_7 = lean_ptr_addr(x_2);
x_8 = lean_usize_to_uint64(x_7);
x_9 = 11;
x_10 = lean_uint64_mix_hash(x_8, x_9);
x_11 = 32;
x_12 = lean_uint64_shift_right(x_10, x_11);
x_13 = lean_uint64_xor(x_10, x_12);
x_14 = 16;
x_15 = lean_uint64_shift_right(x_13, x_14);
x_16 = lean_uint64_xor(x_13, x_15);
x_17 = lean_uint64_to_usize(x_16);
x_18 = lean_usize_of_nat(x_6);
x_19 = 1;
x_20 = lean_usize_sub(x_18, x_19);
x_21 = lean_usize_land(x_17, x_20);
x_22 = lean_array_uget(x_5, x_21);
x_23 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__1_spec__1___redArg(x_2, x_22);
if (x_23 == 0)
{
uint8_t x_24; 
lean_inc_ref(x_5);
lean_inc(x_4);
x_24 = !lean_is_exclusive(x_1);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_25 = lean_ctor_get(x_1, 1);
lean_dec(x_25);
x_26 = lean_ctor_get(x_1, 0);
lean_dec(x_26);
x_27 = lean_unsigned_to_nat(1u);
x_28 = lean_nat_add(x_4, x_27);
lean_dec(x_4);
x_29 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_29, 0, x_2);
lean_ctor_set(x_29, 1, x_3);
lean_ctor_set(x_29, 2, x_22);
x_30 = lean_array_uset(x_5, x_21, x_29);
x_31 = lean_unsigned_to_nat(4u);
x_32 = lean_nat_mul(x_28, x_31);
x_33 = lean_unsigned_to_nat(3u);
x_34 = lean_nat_div(x_32, x_33);
lean_dec(x_32);
x_35 = lean_array_get_size(x_30);
x_36 = lean_nat_dec_le(x_34, x_35);
lean_dec(x_34);
if (x_36 == 0)
{
lean_object* x_37; 
x_37 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__2_spec__3___redArg(x_30);
lean_ctor_set(x_1, 1, x_37);
lean_ctor_set(x_1, 0, x_28);
return x_1;
}
else
{
lean_ctor_set(x_1, 1, x_30);
lean_ctor_set(x_1, 0, x_28);
return x_1;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
lean_dec(x_1);
x_38 = lean_unsigned_to_nat(1u);
x_39 = lean_nat_add(x_4, x_38);
lean_dec(x_4);
x_40 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_40, 0, x_2);
lean_ctor_set(x_40, 1, x_3);
lean_ctor_set(x_40, 2, x_22);
x_41 = lean_array_uset(x_5, x_21, x_40);
x_42 = lean_unsigned_to_nat(4u);
x_43 = lean_nat_mul(x_39, x_42);
x_44 = lean_unsigned_to_nat(3u);
x_45 = lean_nat_div(x_43, x_44);
lean_dec(x_43);
x_46 = lean_array_get_size(x_41);
x_47 = lean_nat_dec_le(x_45, x_46);
lean_dec(x_45);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__2_spec__3___redArg(x_41);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_39);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
else
{
lean_object* x_50; 
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_39);
lean_ctor_set(x_50, 1, x_41);
return x_50;
}
}
}
else
{
lean_dec(x_22);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_1;
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__1___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; size_t x_5; uint64_t x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; size_t x_15; size_t x_16; size_t x_17; size_t x_18; size_t x_19; lean_object* x_20; uint8_t x_21; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
x_5 = lean_ptr_addr(x_2);
x_6 = lean_usize_to_uint64(x_5);
x_7 = 11;
x_8 = lean_uint64_mix_hash(x_6, x_7);
x_9 = 32;
x_10 = lean_uint64_shift_right(x_8, x_9);
x_11 = lean_uint64_xor(x_8, x_10);
x_12 = 16;
x_13 = lean_uint64_shift_right(x_11, x_12);
x_14 = lean_uint64_xor(x_11, x_13);
x_15 = lean_uint64_to_usize(x_14);
x_16 = lean_usize_of_nat(x_4);
x_17 = 1;
x_18 = lean_usize_sub(x_16, x_17);
x_19 = lean_usize_land(x_15, x_18);
x_20 = lean_array_uget(x_3, x_19);
x_21 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__1_spec__1___redArg(x_2, x_20);
lean_dec(x_20);
return x_21;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__1___redArg(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_expr_instantiate1(x_1, x_4);
x_12 = l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit___redArg(x_2, x_11, x_3, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit___redArg___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_28 = lean_ctor_get(x_4, 0);
x_29 = lean_ctor_get(x_4, 1);
x_30 = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__1___redArg(x_28, x_2);
if (x_30 == 0)
{
uint8_t x_31; 
lean_inc_ref(x_29);
lean_inc_ref(x_28);
x_31 = !lean_is_exclusive(x_4);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_32 = lean_ctor_get(x_4, 1);
lean_dec(x_32);
x_33 = lean_ctor_get(x_4, 0);
lean_dec(x_33);
x_34 = lean_box(0);
lean_inc_ref(x_2);
x_35 = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__2___redArg(x_28, x_2, x_34);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_2);
x_36 = l_Lean_Meta_isProof(x_2, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_36) == 0)
{
uint8_t x_37; 
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
lean_object* x_38; uint8_t x_39; 
x_38 = lean_ctor_get(x_36, 0);
lean_inc_ref(x_29);
lean_inc_ref(x_35);
lean_ctor_set(x_4, 0, x_35);
x_39 = lean_unbox(x_38);
lean_dec(x_38);
if (x_39 == 0)
{
switch (lean_obj_tag(x_2)) {
case 7:
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
lean_free_object(x_36);
lean_dec_ref(x_35);
lean_dec_ref(x_29);
x_40 = lean_ctor_get(x_2, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_41);
x_42 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_42);
x_43 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
lean_dec_ref(x_2);
x_10 = x_40;
x_11 = x_41;
x_12 = x_42;
x_13 = x_43;
x_14 = x_4;
x_15 = x_5;
x_16 = x_6;
x_17 = x_7;
x_18 = x_8;
x_19 = lean_box(0);
goto block_27;
}
case 6:
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
lean_free_object(x_36);
lean_dec_ref(x_35);
lean_dec_ref(x_29);
x_44 = lean_ctor_get(x_2, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_45);
x_46 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_46);
x_47 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
lean_dec_ref(x_2);
x_10 = x_44;
x_11 = x_45;
x_12 = x_46;
x_13 = x_47;
x_14 = x_4;
x_15 = x_5;
x_16 = x_6;
x_17 = x_7;
x_18 = x_8;
x_19 = lean_box(0);
goto block_27;
}
case 10:
{
lean_object* x_48; 
lean_free_object(x_36);
lean_dec_ref(x_35);
lean_dec_ref(x_29);
x_48 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_48);
lean_dec_ref(x_2);
x_2 = x_48;
goto _start;
}
case 8:
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; 
lean_free_object(x_36);
lean_dec_ref(x_35);
lean_dec_ref(x_29);
x_50 = lean_ctor_get(x_2, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_51);
x_52 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_52);
x_53 = lean_ctor_get(x_2, 3);
lean_inc_ref(x_53);
x_54 = lean_ctor_get_uint8(x_2, sizeof(void*)*4 + 8);
lean_dec_ref(x_2);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_51);
lean_inc_ref(x_1);
x_55 = l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit___redArg(x_1, x_51, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
lean_dec_ref(x_55);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_52);
lean_inc_ref(x_1);
x_59 = l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit___redArg(x_1, x_52, x_57, x_58, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; lean_object* x_65; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
lean_dec_ref(x_59);
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
x_63 = lean_alloc_closure((void*)(l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit___redArg___lam__1___boxed), 10, 3);
lean_closure_set(x_63, 0, x_53);
lean_closure_set(x_63, 1, x_1);
lean_closure_set(x_63, 2, x_61);
x_64 = 0;
x_65 = l_Lean_Meta_withLetDecl___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__3___redArg(x_50, x_51, x_52, x_63, x_54, x_64, x_62, x_5, x_6, x_7, x_8);
return x_65;
}
else
{
lean_dec_ref(x_53);
lean_dec_ref(x_52);
lean_dec_ref(x_51);
lean_dec(x_50);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
return x_59;
}
}
else
{
lean_dec_ref(x_53);
lean_dec_ref(x_52);
lean_dec_ref(x_51);
lean_dec(x_50);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
return x_55;
}
}
case 5:
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
lean_free_object(x_36);
lean_dec_ref(x_35);
lean_dec_ref(x_29);
x_66 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_66);
x_67 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_67);
lean_dec_ref(x_2);
x_68 = ((lean_object*)(l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit___redArg___closed__0));
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_66);
x_69 = l_Lean_Meta_getFunInfo(x_66, x_68, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
lean_dec_ref(x_69);
x_71 = lean_ctor_get(x_70, 0);
lean_inc_ref(x_71);
lean_dec(x_70);
x_72 = l_Lean_Meta_instInhabitedParamInfo_default;
x_73 = lean_unsigned_to_nat(0u);
x_74 = lean_array_get(x_72, x_71, x_73);
lean_dec_ref(x_71);
x_75 = l_Lean_Meta_ParamInfo_isInstImplicit(x_74);
lean_dec(x_74);
if (x_75 == 0)
{
lean_object* x_76; 
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_1);
x_76 = l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit___redArg(x_1, x_66, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
lean_dec_ref(x_76);
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec(x_77);
x_2 = x_67;
x_3 = x_78;
x_4 = x_79;
goto _start;
}
else
{
lean_dec_ref(x_67);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
return x_76;
}
}
else
{
lean_dec_ref(x_67);
x_2 = x_66;
goto _start;
}
}
else
{
uint8_t x_82; 
lean_dec_ref(x_67);
lean_dec_ref(x_66);
lean_dec_ref(x_4);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_3);
lean_dec_ref(x_1);
x_82 = !lean_is_exclusive(x_69);
if (x_82 == 0)
{
return x_69;
}
else
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_ctor_get(x_69, 0);
lean_inc(x_83);
lean_dec(x_69);
x_84 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_84, 0, x_83);
return x_84;
}
}
}
case 11:
{
lean_object* x_85; 
lean_free_object(x_36);
lean_dec_ref(x_35);
lean_dec_ref(x_29);
x_85 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_85);
lean_dec_ref(x_2);
x_2 = x_85;
goto _start;
}
case 4:
{
lean_object* x_87; uint8_t x_88; 
x_87 = lean_ctor_get(x_2, 0);
lean_inc(x_87);
lean_dec_ref(x_2);
x_88 = l_Lean_NameHashSet_contains(x_29, x_87);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
lean_dec_ref(x_4);
lean_free_object(x_36);
lean_inc(x_87);
x_89 = l_Lean_NameHashSet_insert(x_29, x_87);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_35);
lean_ctor_set(x_90, 1, x_89);
lean_inc(x_87);
x_91 = l_Lean_isInstanceReducible___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__4___redArg(x_87, x_90, x_8);
if (lean_obj_tag(x_91) == 0)
{
uint8_t x_92; 
x_92 = !lean_is_exclusive(x_91);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; uint8_t x_95; 
x_93 = lean_ctor_get(x_91, 0);
x_94 = lean_ctor_get(x_93, 0);
x_95 = lean_unbox(x_94);
if (x_95 == 0)
{
uint8_t x_96; 
lean_free_object(x_91);
x_96 = !lean_is_exclusive(x_93);
if (x_96 == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_93, 1);
x_98 = lean_ctor_get(x_93, 0);
lean_dec(x_98);
x_99 = lean_apply_7(x_1, x_87, x_3, x_5, x_6, x_7, x_8, lean_box(0));
if (lean_obj_tag(x_99) == 0)
{
uint8_t x_100; 
x_100 = !lean_is_exclusive(x_99);
if (x_100 == 0)
{
lean_object* x_101; 
x_101 = lean_ctor_get(x_99, 0);
lean_ctor_set(x_93, 0, x_101);
lean_ctor_set(x_99, 0, x_93);
return x_99;
}
else
{
lean_object* x_102; lean_object* x_103; 
x_102 = lean_ctor_get(x_99, 0);
lean_inc(x_102);
lean_dec(x_99);
lean_ctor_set(x_93, 0, x_102);
x_103 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_103, 0, x_93);
return x_103;
}
}
else
{
uint8_t x_104; 
lean_free_object(x_93);
lean_dec(x_97);
x_104 = !lean_is_exclusive(x_99);
if (x_104 == 0)
{
return x_99;
}
else
{
lean_object* x_105; lean_object* x_106; 
x_105 = lean_ctor_get(x_99, 0);
lean_inc(x_105);
lean_dec(x_99);
x_106 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_106, 0, x_105);
return x_106;
}
}
}
else
{
lean_object* x_107; lean_object* x_108; 
x_107 = lean_ctor_get(x_93, 1);
lean_inc(x_107);
lean_dec(x_93);
x_108 = lean_apply_7(x_1, x_87, x_3, x_5, x_6, x_7, x_8, lean_box(0));
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
if (lean_is_exclusive(x_108)) {
 lean_ctor_release(x_108, 0);
 x_110 = x_108;
} else {
 lean_dec_ref(x_108);
 x_110 = lean_box(0);
}
x_111 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set(x_111, 1, x_107);
if (lean_is_scalar(x_110)) {
 x_112 = lean_alloc_ctor(0, 1, 0);
} else {
 x_112 = x_110;
}
lean_ctor_set(x_112, 0, x_111);
return x_112;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
lean_dec(x_107);
x_113 = lean_ctor_get(x_108, 0);
lean_inc(x_113);
if (lean_is_exclusive(x_108)) {
 lean_ctor_release(x_108, 0);
 x_114 = x_108;
} else {
 lean_dec_ref(x_108);
 x_114 = lean_box(0);
}
if (lean_is_scalar(x_114)) {
 x_115 = lean_alloc_ctor(1, 1, 0);
} else {
 x_115 = x_114;
}
lean_ctor_set(x_115, 0, x_113);
return x_115;
}
}
}
else
{
uint8_t x_116; 
lean_dec(x_87);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_116 = !lean_is_exclusive(x_93);
if (x_116 == 0)
{
lean_object* x_117; 
x_117 = lean_ctor_get(x_93, 0);
lean_dec(x_117);
lean_ctor_set(x_93, 0, x_3);
return x_91;
}
else
{
lean_object* x_118; lean_object* x_119; 
x_118 = lean_ctor_get(x_93, 1);
lean_inc(x_118);
lean_dec(x_93);
x_119 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_119, 0, x_3);
lean_ctor_set(x_119, 1, x_118);
lean_ctor_set(x_91, 0, x_119);
return x_91;
}
}
}
else
{
lean_object* x_120; lean_object* x_121; uint8_t x_122; 
x_120 = lean_ctor_get(x_91, 0);
lean_inc(x_120);
lean_dec(x_91);
x_121 = lean_ctor_get(x_120, 0);
x_122 = lean_unbox(x_121);
if (x_122 == 0)
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_123 = lean_ctor_get(x_120, 1);
lean_inc(x_123);
if (lean_is_exclusive(x_120)) {
 lean_ctor_release(x_120, 0);
 lean_ctor_release(x_120, 1);
 x_124 = x_120;
} else {
 lean_dec_ref(x_120);
 x_124 = lean_box(0);
}
x_125 = lean_apply_7(x_1, x_87, x_3, x_5, x_6, x_7, x_8, lean_box(0));
if (lean_obj_tag(x_125) == 0)
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
if (lean_is_exclusive(x_125)) {
 lean_ctor_release(x_125, 0);
 x_127 = x_125;
} else {
 lean_dec_ref(x_125);
 x_127 = lean_box(0);
}
if (lean_is_scalar(x_124)) {
 x_128 = lean_alloc_ctor(0, 2, 0);
} else {
 x_128 = x_124;
}
lean_ctor_set(x_128, 0, x_126);
lean_ctor_set(x_128, 1, x_123);
if (lean_is_scalar(x_127)) {
 x_129 = lean_alloc_ctor(0, 1, 0);
} else {
 x_129 = x_127;
}
lean_ctor_set(x_129, 0, x_128);
return x_129;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; 
lean_dec(x_124);
lean_dec(x_123);
x_130 = lean_ctor_get(x_125, 0);
lean_inc(x_130);
if (lean_is_exclusive(x_125)) {
 lean_ctor_release(x_125, 0);
 x_131 = x_125;
} else {
 lean_dec_ref(x_125);
 x_131 = lean_box(0);
}
if (lean_is_scalar(x_131)) {
 x_132 = lean_alloc_ctor(1, 1, 0);
} else {
 x_132 = x_131;
}
lean_ctor_set(x_132, 0, x_130);
return x_132;
}
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
lean_dec(x_87);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_133 = lean_ctor_get(x_120, 1);
lean_inc(x_133);
if (lean_is_exclusive(x_120)) {
 lean_ctor_release(x_120, 0);
 lean_ctor_release(x_120, 1);
 x_134 = x_120;
} else {
 lean_dec_ref(x_120);
 x_134 = lean_box(0);
}
if (lean_is_scalar(x_134)) {
 x_135 = lean_alloc_ctor(0, 2, 0);
} else {
 x_135 = x_134;
}
lean_ctor_set(x_135, 0, x_3);
lean_ctor_set(x_135, 1, x_133);
x_136 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_136, 0, x_135);
return x_136;
}
}
}
else
{
uint8_t x_137; 
lean_dec(x_87);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_3);
lean_dec_ref(x_1);
x_137 = !lean_is_exclusive(x_91);
if (x_137 == 0)
{
return x_91;
}
else
{
lean_object* x_138; lean_object* x_139; 
x_138 = lean_ctor_get(x_91, 0);
lean_inc(x_138);
lean_dec(x_91);
x_139 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_139, 0, x_138);
return x_139;
}
}
}
else
{
lean_object* x_140; 
lean_dec(x_87);
lean_dec_ref(x_35);
lean_dec_ref(x_29);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_140 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_140, 0, x_3);
lean_ctor_set(x_140, 1, x_4);
lean_ctor_set(x_36, 0, x_140);
return x_36;
}
}
default: 
{
lean_object* x_141; 
lean_dec_ref(x_35);
lean_dec_ref(x_29);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_141 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_141, 0, x_3);
lean_ctor_set(x_141, 1, x_4);
lean_ctor_set(x_36, 0, x_141);
return x_36;
}
}
}
else
{
lean_object* x_142; 
lean_dec_ref(x_35);
lean_dec_ref(x_29);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_142 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_142, 0, x_3);
lean_ctor_set(x_142, 1, x_4);
lean_ctor_set(x_36, 0, x_142);
return x_36;
}
}
else
{
lean_object* x_143; uint8_t x_144; 
x_143 = lean_ctor_get(x_36, 0);
lean_inc(x_143);
lean_dec(x_36);
lean_inc_ref(x_29);
lean_inc_ref(x_35);
lean_ctor_set(x_4, 0, x_35);
x_144 = lean_unbox(x_143);
lean_dec(x_143);
if (x_144 == 0)
{
switch (lean_obj_tag(x_2)) {
case 7:
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; uint8_t x_148; 
lean_dec_ref(x_35);
lean_dec_ref(x_29);
x_145 = lean_ctor_get(x_2, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_146);
x_147 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_147);
x_148 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
lean_dec_ref(x_2);
x_10 = x_145;
x_11 = x_146;
x_12 = x_147;
x_13 = x_148;
x_14 = x_4;
x_15 = x_5;
x_16 = x_6;
x_17 = x_7;
x_18 = x_8;
x_19 = lean_box(0);
goto block_27;
}
case 6:
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; uint8_t x_152; 
lean_dec_ref(x_35);
lean_dec_ref(x_29);
x_149 = lean_ctor_get(x_2, 0);
lean_inc(x_149);
x_150 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_150);
x_151 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_151);
x_152 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
lean_dec_ref(x_2);
x_10 = x_149;
x_11 = x_150;
x_12 = x_151;
x_13 = x_152;
x_14 = x_4;
x_15 = x_5;
x_16 = x_6;
x_17 = x_7;
x_18 = x_8;
x_19 = lean_box(0);
goto block_27;
}
case 10:
{
lean_object* x_153; 
lean_dec_ref(x_35);
lean_dec_ref(x_29);
x_153 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_153);
lean_dec_ref(x_2);
x_2 = x_153;
goto _start;
}
case 8:
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; uint8_t x_159; lean_object* x_160; 
lean_dec_ref(x_35);
lean_dec_ref(x_29);
x_155 = lean_ctor_get(x_2, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_156);
x_157 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_157);
x_158 = lean_ctor_get(x_2, 3);
lean_inc_ref(x_158);
x_159 = lean_ctor_get_uint8(x_2, sizeof(void*)*4 + 8);
lean_dec_ref(x_2);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_156);
lean_inc_ref(x_1);
x_160 = l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit___redArg(x_1, x_156, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_160) == 0)
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_161 = lean_ctor_get(x_160, 0);
lean_inc(x_161);
lean_dec_ref(x_160);
x_162 = lean_ctor_get(x_161, 0);
lean_inc(x_162);
x_163 = lean_ctor_get(x_161, 1);
lean_inc(x_163);
lean_dec(x_161);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_157);
lean_inc_ref(x_1);
x_164 = l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit___redArg(x_1, x_157, x_162, x_163, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_164) == 0)
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; uint8_t x_169; lean_object* x_170; 
x_165 = lean_ctor_get(x_164, 0);
lean_inc(x_165);
lean_dec_ref(x_164);
x_166 = lean_ctor_get(x_165, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_165, 1);
lean_inc(x_167);
lean_dec(x_165);
x_168 = lean_alloc_closure((void*)(l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit___redArg___lam__1___boxed), 10, 3);
lean_closure_set(x_168, 0, x_158);
lean_closure_set(x_168, 1, x_1);
lean_closure_set(x_168, 2, x_166);
x_169 = 0;
x_170 = l_Lean_Meta_withLetDecl___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__3___redArg(x_155, x_156, x_157, x_168, x_159, x_169, x_167, x_5, x_6, x_7, x_8);
return x_170;
}
else
{
lean_dec_ref(x_158);
lean_dec_ref(x_157);
lean_dec_ref(x_156);
lean_dec(x_155);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
return x_164;
}
}
else
{
lean_dec_ref(x_158);
lean_dec_ref(x_157);
lean_dec_ref(x_156);
lean_dec(x_155);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
return x_160;
}
}
case 5:
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
lean_dec_ref(x_35);
lean_dec_ref(x_29);
x_171 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_171);
x_172 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_172);
lean_dec_ref(x_2);
x_173 = ((lean_object*)(l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit___redArg___closed__0));
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_171);
x_174 = l_Lean_Meta_getFunInfo(x_171, x_173, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_174) == 0)
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; uint8_t x_180; 
x_175 = lean_ctor_get(x_174, 0);
lean_inc(x_175);
lean_dec_ref(x_174);
x_176 = lean_ctor_get(x_175, 0);
lean_inc_ref(x_176);
lean_dec(x_175);
x_177 = l_Lean_Meta_instInhabitedParamInfo_default;
x_178 = lean_unsigned_to_nat(0u);
x_179 = lean_array_get(x_177, x_176, x_178);
lean_dec_ref(x_176);
x_180 = l_Lean_Meta_ParamInfo_isInstImplicit(x_179);
lean_dec(x_179);
if (x_180 == 0)
{
lean_object* x_181; 
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_1);
x_181 = l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit___redArg(x_1, x_171, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_181) == 0)
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_182 = lean_ctor_get(x_181, 0);
lean_inc(x_182);
lean_dec_ref(x_181);
x_183 = lean_ctor_get(x_182, 0);
lean_inc(x_183);
x_184 = lean_ctor_get(x_182, 1);
lean_inc(x_184);
lean_dec(x_182);
x_2 = x_172;
x_3 = x_183;
x_4 = x_184;
goto _start;
}
else
{
lean_dec_ref(x_172);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
return x_181;
}
}
else
{
lean_dec_ref(x_172);
x_2 = x_171;
goto _start;
}
}
else
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; 
lean_dec_ref(x_172);
lean_dec_ref(x_171);
lean_dec_ref(x_4);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_3);
lean_dec_ref(x_1);
x_187 = lean_ctor_get(x_174, 0);
lean_inc(x_187);
if (lean_is_exclusive(x_174)) {
 lean_ctor_release(x_174, 0);
 x_188 = x_174;
} else {
 lean_dec_ref(x_174);
 x_188 = lean_box(0);
}
if (lean_is_scalar(x_188)) {
 x_189 = lean_alloc_ctor(1, 1, 0);
} else {
 x_189 = x_188;
}
lean_ctor_set(x_189, 0, x_187);
return x_189;
}
}
case 11:
{
lean_object* x_190; 
lean_dec_ref(x_35);
lean_dec_ref(x_29);
x_190 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_190);
lean_dec_ref(x_2);
x_2 = x_190;
goto _start;
}
case 4:
{
lean_object* x_192; uint8_t x_193; 
x_192 = lean_ctor_get(x_2, 0);
lean_inc(x_192);
lean_dec_ref(x_2);
x_193 = l_Lean_NameHashSet_contains(x_29, x_192);
if (x_193 == 0)
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; 
lean_dec_ref(x_4);
lean_inc(x_192);
x_194 = l_Lean_NameHashSet_insert(x_29, x_192);
x_195 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_195, 0, x_35);
lean_ctor_set(x_195, 1, x_194);
lean_inc(x_192);
x_196 = l_Lean_isInstanceReducible___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__4___redArg(x_192, x_195, x_8);
if (lean_obj_tag(x_196) == 0)
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; uint8_t x_200; 
x_197 = lean_ctor_get(x_196, 0);
lean_inc(x_197);
if (lean_is_exclusive(x_196)) {
 lean_ctor_release(x_196, 0);
 x_198 = x_196;
} else {
 lean_dec_ref(x_196);
 x_198 = lean_box(0);
}
x_199 = lean_ctor_get(x_197, 0);
x_200 = lean_unbox(x_199);
if (x_200 == 0)
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; 
lean_dec(x_198);
x_201 = lean_ctor_get(x_197, 1);
lean_inc(x_201);
if (lean_is_exclusive(x_197)) {
 lean_ctor_release(x_197, 0);
 lean_ctor_release(x_197, 1);
 x_202 = x_197;
} else {
 lean_dec_ref(x_197);
 x_202 = lean_box(0);
}
x_203 = lean_apply_7(x_1, x_192, x_3, x_5, x_6, x_7, x_8, lean_box(0));
if (lean_obj_tag(x_203) == 0)
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; 
x_204 = lean_ctor_get(x_203, 0);
lean_inc(x_204);
if (lean_is_exclusive(x_203)) {
 lean_ctor_release(x_203, 0);
 x_205 = x_203;
} else {
 lean_dec_ref(x_203);
 x_205 = lean_box(0);
}
if (lean_is_scalar(x_202)) {
 x_206 = lean_alloc_ctor(0, 2, 0);
} else {
 x_206 = x_202;
}
lean_ctor_set(x_206, 0, x_204);
lean_ctor_set(x_206, 1, x_201);
if (lean_is_scalar(x_205)) {
 x_207 = lean_alloc_ctor(0, 1, 0);
} else {
 x_207 = x_205;
}
lean_ctor_set(x_207, 0, x_206);
return x_207;
}
else
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; 
lean_dec(x_202);
lean_dec(x_201);
x_208 = lean_ctor_get(x_203, 0);
lean_inc(x_208);
if (lean_is_exclusive(x_203)) {
 lean_ctor_release(x_203, 0);
 x_209 = x_203;
} else {
 lean_dec_ref(x_203);
 x_209 = lean_box(0);
}
if (lean_is_scalar(x_209)) {
 x_210 = lean_alloc_ctor(1, 1, 0);
} else {
 x_210 = x_209;
}
lean_ctor_set(x_210, 0, x_208);
return x_210;
}
}
else
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; 
lean_dec(x_192);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_211 = lean_ctor_get(x_197, 1);
lean_inc(x_211);
if (lean_is_exclusive(x_197)) {
 lean_ctor_release(x_197, 0);
 lean_ctor_release(x_197, 1);
 x_212 = x_197;
} else {
 lean_dec_ref(x_197);
 x_212 = lean_box(0);
}
if (lean_is_scalar(x_212)) {
 x_213 = lean_alloc_ctor(0, 2, 0);
} else {
 x_213 = x_212;
}
lean_ctor_set(x_213, 0, x_3);
lean_ctor_set(x_213, 1, x_211);
if (lean_is_scalar(x_198)) {
 x_214 = lean_alloc_ctor(0, 1, 0);
} else {
 x_214 = x_198;
}
lean_ctor_set(x_214, 0, x_213);
return x_214;
}
}
else
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; 
lean_dec(x_192);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_3);
lean_dec_ref(x_1);
x_215 = lean_ctor_get(x_196, 0);
lean_inc(x_215);
if (lean_is_exclusive(x_196)) {
 lean_ctor_release(x_196, 0);
 x_216 = x_196;
} else {
 lean_dec_ref(x_196);
 x_216 = lean_box(0);
}
if (lean_is_scalar(x_216)) {
 x_217 = lean_alloc_ctor(1, 1, 0);
} else {
 x_217 = x_216;
}
lean_ctor_set(x_217, 0, x_215);
return x_217;
}
}
else
{
lean_object* x_218; lean_object* x_219; 
lean_dec(x_192);
lean_dec_ref(x_35);
lean_dec_ref(x_29);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_218 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_218, 0, x_3);
lean_ctor_set(x_218, 1, x_4);
x_219 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_219, 0, x_218);
return x_219;
}
}
default: 
{
lean_object* x_220; lean_object* x_221; 
lean_dec_ref(x_35);
lean_dec_ref(x_29);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_220 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_220, 0, x_3);
lean_ctor_set(x_220, 1, x_4);
x_221 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_221, 0, x_220);
return x_221;
}
}
}
else
{
lean_object* x_222; lean_object* x_223; 
lean_dec_ref(x_35);
lean_dec_ref(x_29);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_222 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_222, 0, x_3);
lean_ctor_set(x_222, 1, x_4);
x_223 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_223, 0, x_222);
return x_223;
}
}
}
else
{
uint8_t x_224; 
lean_dec_ref(x_35);
lean_free_object(x_4);
lean_dec_ref(x_29);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_224 = !lean_is_exclusive(x_36);
if (x_224 == 0)
{
return x_36;
}
else
{
lean_object* x_225; lean_object* x_226; 
x_225 = lean_ctor_get(x_36, 0);
lean_inc(x_225);
lean_dec(x_36);
x_226 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_226, 0, x_225);
return x_226;
}
}
}
else
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; 
lean_dec(x_4);
x_227 = lean_box(0);
lean_inc_ref(x_2);
x_228 = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__2___redArg(x_28, x_2, x_227);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_2);
x_229 = l_Lean_Meta_isProof(x_2, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_229) == 0)
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; uint8_t x_233; 
x_230 = lean_ctor_get(x_229, 0);
lean_inc(x_230);
if (lean_is_exclusive(x_229)) {
 lean_ctor_release(x_229, 0);
 x_231 = x_229;
} else {
 lean_dec_ref(x_229);
 x_231 = lean_box(0);
}
lean_inc_ref(x_29);
lean_inc_ref(x_228);
x_232 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_232, 0, x_228);
lean_ctor_set(x_232, 1, x_29);
x_233 = lean_unbox(x_230);
lean_dec(x_230);
if (x_233 == 0)
{
switch (lean_obj_tag(x_2)) {
case 7:
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; uint8_t x_237; 
lean_dec(x_231);
lean_dec_ref(x_228);
lean_dec_ref(x_29);
x_234 = lean_ctor_get(x_2, 0);
lean_inc(x_234);
x_235 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_235);
x_236 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_236);
x_237 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
lean_dec_ref(x_2);
x_10 = x_234;
x_11 = x_235;
x_12 = x_236;
x_13 = x_237;
x_14 = x_232;
x_15 = x_5;
x_16 = x_6;
x_17 = x_7;
x_18 = x_8;
x_19 = lean_box(0);
goto block_27;
}
case 6:
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; uint8_t x_241; 
lean_dec(x_231);
lean_dec_ref(x_228);
lean_dec_ref(x_29);
x_238 = lean_ctor_get(x_2, 0);
lean_inc(x_238);
x_239 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_239);
x_240 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_240);
x_241 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
lean_dec_ref(x_2);
x_10 = x_238;
x_11 = x_239;
x_12 = x_240;
x_13 = x_241;
x_14 = x_232;
x_15 = x_5;
x_16 = x_6;
x_17 = x_7;
x_18 = x_8;
x_19 = lean_box(0);
goto block_27;
}
case 10:
{
lean_object* x_242; 
lean_dec(x_231);
lean_dec_ref(x_228);
lean_dec_ref(x_29);
x_242 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_242);
lean_dec_ref(x_2);
x_2 = x_242;
x_4 = x_232;
goto _start;
}
case 8:
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; uint8_t x_248; lean_object* x_249; 
lean_dec(x_231);
lean_dec_ref(x_228);
lean_dec_ref(x_29);
x_244 = lean_ctor_get(x_2, 0);
lean_inc(x_244);
x_245 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_245);
x_246 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_246);
x_247 = lean_ctor_get(x_2, 3);
lean_inc_ref(x_247);
x_248 = lean_ctor_get_uint8(x_2, sizeof(void*)*4 + 8);
lean_dec_ref(x_2);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_245);
lean_inc_ref(x_1);
x_249 = l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit___redArg(x_1, x_245, x_3, x_232, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_249) == 0)
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; 
x_250 = lean_ctor_get(x_249, 0);
lean_inc(x_250);
lean_dec_ref(x_249);
x_251 = lean_ctor_get(x_250, 0);
lean_inc(x_251);
x_252 = lean_ctor_get(x_250, 1);
lean_inc(x_252);
lean_dec(x_250);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_246);
lean_inc_ref(x_1);
x_253 = l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit___redArg(x_1, x_246, x_251, x_252, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_253) == 0)
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; uint8_t x_258; lean_object* x_259; 
x_254 = lean_ctor_get(x_253, 0);
lean_inc(x_254);
lean_dec_ref(x_253);
x_255 = lean_ctor_get(x_254, 0);
lean_inc(x_255);
x_256 = lean_ctor_get(x_254, 1);
lean_inc(x_256);
lean_dec(x_254);
x_257 = lean_alloc_closure((void*)(l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit___redArg___lam__1___boxed), 10, 3);
lean_closure_set(x_257, 0, x_247);
lean_closure_set(x_257, 1, x_1);
lean_closure_set(x_257, 2, x_255);
x_258 = 0;
x_259 = l_Lean_Meta_withLetDecl___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__3___redArg(x_244, x_245, x_246, x_257, x_248, x_258, x_256, x_5, x_6, x_7, x_8);
return x_259;
}
else
{
lean_dec_ref(x_247);
lean_dec_ref(x_246);
lean_dec_ref(x_245);
lean_dec(x_244);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
return x_253;
}
}
else
{
lean_dec_ref(x_247);
lean_dec_ref(x_246);
lean_dec_ref(x_245);
lean_dec(x_244);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
return x_249;
}
}
case 5:
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; 
lean_dec(x_231);
lean_dec_ref(x_228);
lean_dec_ref(x_29);
x_260 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_260);
x_261 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_261);
lean_dec_ref(x_2);
x_262 = ((lean_object*)(l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit___redArg___closed__0));
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_260);
x_263 = l_Lean_Meta_getFunInfo(x_260, x_262, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_263) == 0)
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; uint8_t x_269; 
x_264 = lean_ctor_get(x_263, 0);
lean_inc(x_264);
lean_dec_ref(x_263);
x_265 = lean_ctor_get(x_264, 0);
lean_inc_ref(x_265);
lean_dec(x_264);
x_266 = l_Lean_Meta_instInhabitedParamInfo_default;
x_267 = lean_unsigned_to_nat(0u);
x_268 = lean_array_get(x_266, x_265, x_267);
lean_dec_ref(x_265);
x_269 = l_Lean_Meta_ParamInfo_isInstImplicit(x_268);
lean_dec(x_268);
if (x_269 == 0)
{
lean_object* x_270; 
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_1);
x_270 = l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit___redArg(x_1, x_260, x_3, x_232, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_270) == 0)
{
lean_object* x_271; lean_object* x_272; lean_object* x_273; 
x_271 = lean_ctor_get(x_270, 0);
lean_inc(x_271);
lean_dec_ref(x_270);
x_272 = lean_ctor_get(x_271, 0);
lean_inc(x_272);
x_273 = lean_ctor_get(x_271, 1);
lean_inc(x_273);
lean_dec(x_271);
x_2 = x_261;
x_3 = x_272;
x_4 = x_273;
goto _start;
}
else
{
lean_dec_ref(x_261);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
return x_270;
}
}
else
{
lean_dec_ref(x_261);
x_2 = x_260;
x_4 = x_232;
goto _start;
}
}
else
{
lean_object* x_276; lean_object* x_277; lean_object* x_278; 
lean_dec_ref(x_261);
lean_dec_ref(x_260);
lean_dec_ref(x_232);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_3);
lean_dec_ref(x_1);
x_276 = lean_ctor_get(x_263, 0);
lean_inc(x_276);
if (lean_is_exclusive(x_263)) {
 lean_ctor_release(x_263, 0);
 x_277 = x_263;
} else {
 lean_dec_ref(x_263);
 x_277 = lean_box(0);
}
if (lean_is_scalar(x_277)) {
 x_278 = lean_alloc_ctor(1, 1, 0);
} else {
 x_278 = x_277;
}
lean_ctor_set(x_278, 0, x_276);
return x_278;
}
}
case 11:
{
lean_object* x_279; 
lean_dec(x_231);
lean_dec_ref(x_228);
lean_dec_ref(x_29);
x_279 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_279);
lean_dec_ref(x_2);
x_2 = x_279;
x_4 = x_232;
goto _start;
}
case 4:
{
lean_object* x_281; uint8_t x_282; 
x_281 = lean_ctor_get(x_2, 0);
lean_inc(x_281);
lean_dec_ref(x_2);
x_282 = l_Lean_NameHashSet_contains(x_29, x_281);
if (x_282 == 0)
{
lean_object* x_283; lean_object* x_284; lean_object* x_285; 
lean_dec_ref(x_232);
lean_dec(x_231);
lean_inc(x_281);
x_283 = l_Lean_NameHashSet_insert(x_29, x_281);
x_284 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_284, 0, x_228);
lean_ctor_set(x_284, 1, x_283);
lean_inc(x_281);
x_285 = l_Lean_isInstanceReducible___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__4___redArg(x_281, x_284, x_8);
if (lean_obj_tag(x_285) == 0)
{
lean_object* x_286; lean_object* x_287; lean_object* x_288; uint8_t x_289; 
x_286 = lean_ctor_get(x_285, 0);
lean_inc(x_286);
if (lean_is_exclusive(x_285)) {
 lean_ctor_release(x_285, 0);
 x_287 = x_285;
} else {
 lean_dec_ref(x_285);
 x_287 = lean_box(0);
}
x_288 = lean_ctor_get(x_286, 0);
x_289 = lean_unbox(x_288);
if (x_289 == 0)
{
lean_object* x_290; lean_object* x_291; lean_object* x_292; 
lean_dec(x_287);
x_290 = lean_ctor_get(x_286, 1);
lean_inc(x_290);
if (lean_is_exclusive(x_286)) {
 lean_ctor_release(x_286, 0);
 lean_ctor_release(x_286, 1);
 x_291 = x_286;
} else {
 lean_dec_ref(x_286);
 x_291 = lean_box(0);
}
x_292 = lean_apply_7(x_1, x_281, x_3, x_5, x_6, x_7, x_8, lean_box(0));
if (lean_obj_tag(x_292) == 0)
{
lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; 
x_293 = lean_ctor_get(x_292, 0);
lean_inc(x_293);
if (lean_is_exclusive(x_292)) {
 lean_ctor_release(x_292, 0);
 x_294 = x_292;
} else {
 lean_dec_ref(x_292);
 x_294 = lean_box(0);
}
if (lean_is_scalar(x_291)) {
 x_295 = lean_alloc_ctor(0, 2, 0);
} else {
 x_295 = x_291;
}
lean_ctor_set(x_295, 0, x_293);
lean_ctor_set(x_295, 1, x_290);
if (lean_is_scalar(x_294)) {
 x_296 = lean_alloc_ctor(0, 1, 0);
} else {
 x_296 = x_294;
}
lean_ctor_set(x_296, 0, x_295);
return x_296;
}
else
{
lean_object* x_297; lean_object* x_298; lean_object* x_299; 
lean_dec(x_291);
lean_dec(x_290);
x_297 = lean_ctor_get(x_292, 0);
lean_inc(x_297);
if (lean_is_exclusive(x_292)) {
 lean_ctor_release(x_292, 0);
 x_298 = x_292;
} else {
 lean_dec_ref(x_292);
 x_298 = lean_box(0);
}
if (lean_is_scalar(x_298)) {
 x_299 = lean_alloc_ctor(1, 1, 0);
} else {
 x_299 = x_298;
}
lean_ctor_set(x_299, 0, x_297);
return x_299;
}
}
else
{
lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; 
lean_dec(x_281);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_300 = lean_ctor_get(x_286, 1);
lean_inc(x_300);
if (lean_is_exclusive(x_286)) {
 lean_ctor_release(x_286, 0);
 lean_ctor_release(x_286, 1);
 x_301 = x_286;
} else {
 lean_dec_ref(x_286);
 x_301 = lean_box(0);
}
if (lean_is_scalar(x_301)) {
 x_302 = lean_alloc_ctor(0, 2, 0);
} else {
 x_302 = x_301;
}
lean_ctor_set(x_302, 0, x_3);
lean_ctor_set(x_302, 1, x_300);
if (lean_is_scalar(x_287)) {
 x_303 = lean_alloc_ctor(0, 1, 0);
} else {
 x_303 = x_287;
}
lean_ctor_set(x_303, 0, x_302);
return x_303;
}
}
else
{
lean_object* x_304; lean_object* x_305; lean_object* x_306; 
lean_dec(x_281);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_3);
lean_dec_ref(x_1);
x_304 = lean_ctor_get(x_285, 0);
lean_inc(x_304);
if (lean_is_exclusive(x_285)) {
 lean_ctor_release(x_285, 0);
 x_305 = x_285;
} else {
 lean_dec_ref(x_285);
 x_305 = lean_box(0);
}
if (lean_is_scalar(x_305)) {
 x_306 = lean_alloc_ctor(1, 1, 0);
} else {
 x_306 = x_305;
}
lean_ctor_set(x_306, 0, x_304);
return x_306;
}
}
else
{
lean_object* x_307; lean_object* x_308; 
lean_dec(x_281);
lean_dec_ref(x_228);
lean_dec_ref(x_29);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_307 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_307, 0, x_3);
lean_ctor_set(x_307, 1, x_232);
if (lean_is_scalar(x_231)) {
 x_308 = lean_alloc_ctor(0, 1, 0);
} else {
 x_308 = x_231;
}
lean_ctor_set(x_308, 0, x_307);
return x_308;
}
}
default: 
{
lean_object* x_309; lean_object* x_310; 
lean_dec_ref(x_228);
lean_dec_ref(x_29);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_309 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_309, 0, x_3);
lean_ctor_set(x_309, 1, x_232);
if (lean_is_scalar(x_231)) {
 x_310 = lean_alloc_ctor(0, 1, 0);
} else {
 x_310 = x_231;
}
lean_ctor_set(x_310, 0, x_309);
return x_310;
}
}
}
else
{
lean_object* x_311; lean_object* x_312; 
lean_dec_ref(x_228);
lean_dec_ref(x_29);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_311 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_311, 0, x_3);
lean_ctor_set(x_311, 1, x_232);
if (lean_is_scalar(x_231)) {
 x_312 = lean_alloc_ctor(0, 1, 0);
} else {
 x_312 = x_231;
}
lean_ctor_set(x_312, 0, x_311);
return x_312;
}
}
else
{
lean_object* x_313; lean_object* x_314; lean_object* x_315; 
lean_dec_ref(x_228);
lean_dec_ref(x_29);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_313 = lean_ctor_get(x_229, 0);
lean_inc(x_313);
if (lean_is_exclusive(x_229)) {
 lean_ctor_release(x_229, 0);
 x_314 = x_229;
} else {
 lean_dec_ref(x_229);
 x_314 = lean_box(0);
}
if (lean_is_scalar(x_314)) {
 x_315 = lean_alloc_ctor(1, 1, 0);
} else {
 x_315 = x_314;
}
lean_ctor_set(x_315, 0, x_313);
return x_315;
}
}
}
else
{
lean_object* x_316; lean_object* x_317; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_316 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_316, 0, x_3);
lean_ctor_set(x_316, 1, x_4);
x_317 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_317, 0, x_316);
return x_317;
}
block_27:
{
lean_object* x_20; 
lean_inc(x_18);
lean_inc_ref(x_17);
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc_ref(x_11);
lean_inc_ref(x_1);
x_20 = l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit___redArg(x_1, x_11, x_3, x_14, x_15, x_16, x_17, x_18);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec_ref(x_20);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_alloc_closure((void*)(l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit___redArg___lam__0___boxed), 10, 3);
lean_closure_set(x_24, 0, x_12);
lean_closure_set(x_24, 1, x_1);
lean_closure_set(x_24, 2, x_22);
x_25 = 0;
x_26 = l_Lean_Meta_withLocalDecl___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__0___redArg(x_10, x_13, x_11, x_24, x_25, x_23, x_15, x_16, x_17, x_18);
return x_26;
}
else
{
lean_dec(x_18);
lean_dec_ref(x_17);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec_ref(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_1);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_expr_instantiate1(x_1, x_4);
x_12 = l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit___redArg(x_2, x_11, x_3, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__1___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__1(x_1, x_2, x_3);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__2___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__1_spec__1___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__1_spec__1(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__2_spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__2_spec__3___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__2_spec__3_spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__2_spec__3_spec__6___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__2_spec__3_spec__6_spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit_spec__2_spec__3_spec__6_spec__7___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
static lean_object* _init_l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_foldUnsafe___redArg___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(64u);
x_2 = l_Lean_mkPtrSet___redArg(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_foldUnsafe___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_unsigned_to_nat(16u);
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_foldUnsafe___redArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_foldUnsafe___redArg___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_foldUnsafe___redArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_foldUnsafe___redArg___closed__2;
x_2 = l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_foldUnsafe___redArg___closed__0;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_foldUnsafe___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_foldUnsafe___redArg___closed__3;
x_10 = l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit___redArg(x_3, x_1, x_2, x_9, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec(x_12);
lean_ctor_set(x_10, 0, x_13);
return x_10;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_10, 0);
lean_inc(x_14);
lean_dec(x_10);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_10);
if (x_17 == 0)
{
return x_10;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_10, 0);
lean_inc(x_18);
lean_dec(x_10);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_foldUnsafe___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_foldUnsafe___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_foldUnsafe(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_foldUnsafe___redArg___closed__3;
x_11 = l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit___redArg(x_4, x_2, x_3, x_10, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec(x_13);
lean_ctor_set(x_11, 0, x_14);
return x_11;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_11, 0);
lean_inc(x_15);
lean_dec(x_11);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_11);
if (x_18 == 0)
{
return x_11;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_11, 0);
lean_inc(x_19);
lean_dec(x_11);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_foldUnsafe___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_foldUnsafe(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_relevantConstants___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_array_push(x_2, x_1);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_relevantConstants___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Expr_relevantConstants___lam__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
static lean_object* _init_l_Lean_Expr_relevantConstants___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_relevantConstants(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = ((lean_object*)(l_Lean_Expr_relevantConstants___closed__0));
x_8 = l_Lean_Expr_relevantConstants___closed__1;
x_9 = l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_foldUnsafe___redArg___closed__3;
x_10 = l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit___redArg(x_7, x_1, x_8, x_9, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec(x_12);
lean_ctor_set(x_10, 0, x_13);
return x_10;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_10, 0);
lean_inc(x_14);
lean_dec(x_10);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_10);
if (x_17 == 0)
{
return x_10;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_10, 0);
lean_inc(x_18);
lean_dec(x_10);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_relevantConstants___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Expr_relevantConstants(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_relevantConstantsAsSet___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_NameSet_insert(x_2, x_1);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_relevantConstantsAsSet___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Expr_relevantConstantsAsSet___lam__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_relevantConstantsAsSet(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = ((lean_object*)(l_Lean_Expr_relevantConstantsAsSet___closed__0));
x_8 = l_Lean_NameSet_empty;
x_9 = l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_foldUnsafe___redArg___closed__3;
x_10 = l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_fold_visit___redArg(x_7, x_1, x_8, x_9, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec(x_12);
lean_ctor_set(x_10, 0, x_13);
return x_10;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_10, 0);
lean_inc(x_14);
lean_dec(x_10);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_10);
if (x_17 == 0)
{
return x_10;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_10, 0);
lean_inc(x_18);
lean_dec(x_10);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_relevantConstantsAsSet___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Expr_relevantConstantsAsSet(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_getConstants_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
return x_8;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_8);
if (x_12 == 0)
{
return x_8;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_8, 0);
lean_inc(x_13);
lean_dec(x_8);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_getConstants_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_MVarId_withContext___at___00Lean_MVarId_getConstants_spec__2___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_getConstants_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_MVarId_withContext___at___00Lean_MVarId_getConstants_spec__2___redArg(x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_getConstants_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_MVarId_withContext___at___00Lean_MVarId_getConstants_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_getConstants_spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_lt(x_3, x_2);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_4);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_array_uget(x_1, x_3);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_13 = lean_infer_type(x_12, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec_ref(x_13);
x_15 = l_Lean_Expr_getUsedConstantsAsSet(x_14);
x_16 = l_Lean_NameSet_append(x_4, x_15);
x_17 = 1;
x_18 = lean_usize_add(x_3, x_17);
x_3 = x_18;
x_4 = x_16;
goto _start;
}
else
{
uint8_t x_20; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
x_20 = !lean_is_exclusive(x_13);
if (x_20 == 0)
{
return x_13;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_13, 0);
lean_inc(x_21);
lean_dec(x_13);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_21);
return x_22;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_getConstants_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_getConstants_spec__1(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_getConstants_spec__0_spec__0_spec__2_spec__5_spec__6___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_lt(x_3, x_2);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_4);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_18; 
x_8 = lean_ctor_get(x_4, 1);
lean_inc(x_8);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 x_9 = x_4;
} else {
 lean_dec_ref(x_4);
 x_9 = lean_box(0);
}
x_10 = lean_box(0);
x_18 = lean_array_uget(x_1, x_3);
if (lean_obj_tag(x_18) == 0)
{
x_11 = x_8;
x_12 = lean_box(0);
goto block_17;
}
else
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec_ref(x_18);
x_20 = l_Lean_LocalDecl_isImplementationDetail(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = l_Lean_LocalDecl_toExpr(x_19);
x_22 = lean_array_push(x_8, x_21);
x_11 = x_22;
x_12 = lean_box(0);
goto block_17;
}
else
{
lean_dec(x_19);
x_11 = x_8;
x_12 = lean_box(0);
goto block_17;
}
}
block_17:
{
lean_object* x_13; size_t x_14; size_t x_15; 
if (lean_is_scalar(x_9)) {
 x_13 = lean_alloc_ctor(0, 2, 0);
} else {
 x_13 = x_9;
}
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_11);
x_14 = 1;
x_15 = lean_usize_add(x_3, x_14);
x_3 = x_15;
x_4 = x_13;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_getConstants_spec__0_spec__0_spec__2_spec__5_spec__6___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_getConstants_spec__0_spec__0_spec__2_spec__5_spec__6___redArg(x_1, x_6, x_7, x_4);
lean_dec_ref(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_getConstants_spec__0_spec__0_spec__2_spec__5(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_lt(x_3, x_2);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_4);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_22; 
x_12 = lean_ctor_get(x_4, 1);
lean_inc(x_12);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 x_13 = x_4;
} else {
 lean_dec_ref(x_4);
 x_13 = lean_box(0);
}
x_14 = lean_box(0);
x_22 = lean_array_uget(x_1, x_3);
if (lean_obj_tag(x_22) == 0)
{
x_15 = x_12;
x_16 = lean_box(0);
goto block_21;
}
else
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec_ref(x_22);
x_24 = l_Lean_LocalDecl_isImplementationDetail(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = l_Lean_LocalDecl_toExpr(x_23);
x_26 = lean_array_push(x_12, x_25);
x_15 = x_26;
x_16 = lean_box(0);
goto block_21;
}
else
{
lean_dec(x_23);
x_15 = x_12;
x_16 = lean_box(0);
goto block_21;
}
}
block_21:
{
lean_object* x_17; size_t x_18; size_t x_19; lean_object* x_20; 
if (lean_is_scalar(x_13)) {
 x_17 = lean_alloc_ctor(0, 2, 0);
} else {
 x_17 = x_13;
}
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_15);
x_18 = 1;
x_19 = lean_usize_add(x_3, x_18);
x_20 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_getConstants_spec__0_spec__0_spec__2_spec__5_spec__6___redArg(x_1, x_2, x_19, x_17);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_getConstants_spec__0_spec__0_spec__2_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_getConstants_spec__0_spec__0_spec__2_spec__5(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_getConstants_spec__0_spec__0_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_2);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; size_t x_13; size_t x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_3);
x_13 = lean_array_size(x_10);
x_14 = 0;
x_15 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_getConstants_spec__0_spec__0_spec__2_spec__4(x_1, x_10, x_13, x_14, x_12, x_4, x_5, x_6, x_7);
lean_dec_ref(x_10);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get(x_17, 0);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
lean_ctor_set_tag(x_2, 1);
lean_ctor_set(x_2, 0, x_19);
lean_ctor_set(x_15, 0, x_2);
return x_15;
}
else
{
lean_object* x_20; 
lean_inc_ref(x_18);
lean_dec(x_17);
lean_free_object(x_2);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
lean_dec_ref(x_18);
lean_ctor_set(x_15, 0, x_20);
return x_15;
}
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_15, 0);
lean_inc(x_21);
lean_dec(x_15);
x_22 = lean_ctor_get(x_21, 0);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
lean_ctor_set_tag(x_2, 1);
lean_ctor_set(x_2, 0, x_23);
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_2);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; 
lean_inc_ref(x_22);
lean_dec(x_21);
lean_free_object(x_2);
x_25 = lean_ctor_get(x_22, 0);
lean_inc(x_25);
lean_dec_ref(x_22);
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
}
}
else
{
uint8_t x_27; 
lean_free_object(x_2);
x_27 = !lean_is_exclusive(x_15);
if (x_27 == 0)
{
return x_15;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_15, 0);
lean_inc(x_28);
lean_dec(x_15);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_28);
return x_29;
}
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; size_t x_33; size_t x_34; lean_object* x_35; 
x_30 = lean_ctor_get(x_2, 0);
lean_inc(x_30);
lean_dec(x_2);
x_31 = lean_box(0);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_3);
x_33 = lean_array_size(x_30);
x_34 = 0;
x_35 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_getConstants_spec__0_spec__0_spec__2_spec__4(x_1, x_30, x_33, x_34, x_32, x_4, x_5, x_6, x_7);
lean_dec_ref(x_30);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 x_37 = x_35;
} else {
 lean_dec_ref(x_35);
 x_37 = lean_box(0);
}
x_38 = lean_ctor_get(x_36, 0);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
lean_dec(x_36);
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_39);
if (lean_is_scalar(x_37)) {
 x_41 = lean_alloc_ctor(0, 1, 0);
} else {
 x_41 = x_37;
}
lean_ctor_set(x_41, 0, x_40);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; 
lean_inc_ref(x_38);
lean_dec(x_36);
x_42 = lean_ctor_get(x_38, 0);
lean_inc(x_42);
lean_dec_ref(x_38);
if (lean_is_scalar(x_37)) {
 x_43 = lean_alloc_ctor(0, 1, 0);
} else {
 x_43 = x_37;
}
lean_ctor_set(x_43, 0, x_42);
return x_43;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_35, 0);
lean_inc(x_44);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 x_45 = x_35;
} else {
 lean_dec_ref(x_35);
 x_45 = lean_box(0);
}
if (lean_is_scalar(x_45)) {
 x_46 = lean_alloc_ctor(1, 1, 0);
} else {
 x_46 = x_45;
}
lean_ctor_set(x_46, 0, x_44);
return x_46;
}
}
}
else
{
uint8_t x_47; 
x_47 = !lean_is_exclusive(x_2);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; size_t x_51; size_t x_52; lean_object* x_53; 
x_48 = lean_ctor_get(x_2, 0);
x_49 = lean_box(0);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_3);
x_51 = lean_array_size(x_48);
x_52 = 0;
x_53 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_getConstants_spec__0_spec__0_spec__2_spec__5(x_48, x_51, x_52, x_50, x_4, x_5, x_6, x_7);
lean_dec_ref(x_48);
if (lean_obj_tag(x_53) == 0)
{
uint8_t x_54; 
x_54 = !lean_is_exclusive(x_53);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_53, 0);
x_56 = lean_ctor_get(x_55, 0);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; 
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
lean_ctor_set(x_2, 0, x_57);
lean_ctor_set(x_53, 0, x_2);
return x_53;
}
else
{
lean_object* x_58; 
lean_inc_ref(x_56);
lean_dec(x_55);
lean_free_object(x_2);
x_58 = lean_ctor_get(x_56, 0);
lean_inc(x_58);
lean_dec_ref(x_56);
lean_ctor_set(x_53, 0, x_58);
return x_53;
}
}
else
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_53, 0);
lean_inc(x_59);
lean_dec(x_53);
x_60 = lean_ctor_get(x_59, 0);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
lean_ctor_set(x_2, 0, x_61);
x_62 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_62, 0, x_2);
return x_62;
}
else
{
lean_object* x_63; lean_object* x_64; 
lean_inc_ref(x_60);
lean_dec(x_59);
lean_free_object(x_2);
x_63 = lean_ctor_get(x_60, 0);
lean_inc(x_63);
lean_dec_ref(x_60);
x_64 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_64, 0, x_63);
return x_64;
}
}
}
else
{
uint8_t x_65; 
lean_free_object(x_2);
x_65 = !lean_is_exclusive(x_53);
if (x_65 == 0)
{
return x_53;
}
else
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_ctor_get(x_53, 0);
lean_inc(x_66);
lean_dec(x_53);
x_67 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_67, 0, x_66);
return x_67;
}
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; size_t x_71; size_t x_72; lean_object* x_73; 
x_68 = lean_ctor_get(x_2, 0);
lean_inc(x_68);
lean_dec(x_2);
x_69 = lean_box(0);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_3);
x_71 = lean_array_size(x_68);
x_72 = 0;
x_73 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_getConstants_spec__0_spec__0_spec__2_spec__5(x_68, x_71, x_72, x_70, x_4, x_5, x_6, x_7);
lean_dec_ref(x_68);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 x_75 = x_73;
} else {
 lean_dec_ref(x_73);
 x_75 = lean_box(0);
}
x_76 = lean_ctor_get(x_74, 0);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_74, 1);
lean_inc(x_77);
lean_dec(x_74);
x_78 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_78, 0, x_77);
if (lean_is_scalar(x_75)) {
 x_79 = lean_alloc_ctor(0, 1, 0);
} else {
 x_79 = x_75;
}
lean_ctor_set(x_79, 0, x_78);
return x_79;
}
else
{
lean_object* x_80; lean_object* x_81; 
lean_inc_ref(x_76);
lean_dec(x_74);
x_80 = lean_ctor_get(x_76, 0);
lean_inc(x_80);
lean_dec_ref(x_76);
if (lean_is_scalar(x_75)) {
 x_81 = lean_alloc_ctor(0, 1, 0);
} else {
 x_81 = x_75;
}
lean_ctor_set(x_81, 0, x_80);
return x_81;
}
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_73, 0);
lean_inc(x_82);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 x_83 = x_73;
} else {
 lean_dec_ref(x_73);
 x_83 = lean_box(0);
}
if (lean_is_scalar(x_83)) {
 x_84 = lean_alloc_ctor(1, 1, 0);
} else {
 x_84 = x_83;
}
lean_ctor_set(x_84, 0, x_82);
return x_84;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_getConstants_spec__0_spec__0_spec__2_spec__4(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_lt(x_4, x_3);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_5);
return x_12;
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_5);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_5, 1);
x_15 = lean_ctor_get(x_5, 0);
lean_dec(x_15);
x_16 = lean_array_uget(x_2, x_4);
lean_inc(x_14);
x_17 = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_getConstants_spec__0_spec__0_spec__2(x_1, x_16, x_14, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_17, 0);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_5, 0, x_20);
lean_ctor_set(x_17, 0, x_5);
return x_17;
}
else
{
lean_object* x_21; lean_object* x_22; size_t x_23; size_t x_24; 
lean_free_object(x_17);
lean_dec(x_14);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
lean_dec_ref(x_19);
x_22 = lean_box(0);
lean_ctor_set(x_5, 1, x_21);
lean_ctor_set(x_5, 0, x_22);
x_23 = 1;
x_24 = lean_usize_add(x_4, x_23);
x_4 = x_24;
goto _start;
}
}
else
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_17, 0);
lean_inc(x_26);
lean_dec(x_17);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_5, 0, x_27);
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_5);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; size_t x_31; size_t x_32; 
lean_dec(x_14);
x_29 = lean_ctor_get(x_26, 0);
lean_inc(x_29);
lean_dec_ref(x_26);
x_30 = lean_box(0);
lean_ctor_set(x_5, 1, x_29);
lean_ctor_set(x_5, 0, x_30);
x_31 = 1;
x_32 = lean_usize_add(x_4, x_31);
x_4 = x_32;
goto _start;
}
}
}
else
{
uint8_t x_34; 
lean_free_object(x_5);
lean_dec(x_14);
x_34 = !lean_is_exclusive(x_17);
if (x_34 == 0)
{
return x_17;
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_17, 0);
lean_inc(x_35);
lean_dec(x_17);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_35);
return x_36;
}
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_5, 1);
lean_inc(x_37);
lean_dec(x_5);
x_38 = lean_array_uget(x_2, x_4);
lean_inc(x_37);
x_39 = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_getConstants_spec__0_spec__0_spec__2(x_1, x_38, x_37, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 x_41 = x_39;
} else {
 lean_dec_ref(x_39);
 x_41 = lean_box(0);
}
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_40);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_37);
if (lean_is_scalar(x_41)) {
 x_44 = lean_alloc_ctor(0, 1, 0);
} else {
 x_44 = x_41;
}
lean_ctor_set(x_44, 0, x_43);
return x_44;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; size_t x_48; size_t x_49; 
lean_dec(x_41);
lean_dec(x_37);
x_45 = lean_ctor_get(x_40, 0);
lean_inc(x_45);
lean_dec_ref(x_40);
x_46 = lean_box(0);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_45);
x_48 = 1;
x_49 = lean_usize_add(x_4, x_48);
x_4 = x_49;
x_5 = x_47;
goto _start;
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_37);
x_51 = lean_ctor_get(x_39, 0);
lean_inc(x_51);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 x_52 = x_39;
} else {
 lean_dec_ref(x_39);
 x_52 = lean_box(0);
}
if (lean_is_scalar(x_52)) {
 x_53 = lean_alloc_ctor(1, 1, 0);
} else {
 x_53 = x_52;
}
lean_ctor_set(x_53, 0, x_51);
return x_53;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_getConstants_spec__0_spec__0_spec__2_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_getConstants_spec__0_spec__0_spec__2_spec__4(x_1, x_2, x_11, x_12, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_getConstants_spec__0_spec__0_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_getConstants_spec__0_spec__0_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_getConstants_spec__0_spec__0_spec__3_spec__7___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_lt(x_3, x_2);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_4);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_18; 
x_8 = lean_ctor_get(x_4, 1);
lean_inc(x_8);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 x_9 = x_4;
} else {
 lean_dec_ref(x_4);
 x_9 = lean_box(0);
}
x_10 = lean_box(0);
x_18 = lean_array_uget(x_1, x_3);
if (lean_obj_tag(x_18) == 0)
{
x_11 = x_8;
x_12 = lean_box(0);
goto block_17;
}
else
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec_ref(x_18);
x_20 = l_Lean_LocalDecl_isImplementationDetail(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = l_Lean_LocalDecl_toExpr(x_19);
x_22 = lean_array_push(x_8, x_21);
x_11 = x_22;
x_12 = lean_box(0);
goto block_17;
}
else
{
lean_dec(x_19);
x_11 = x_8;
x_12 = lean_box(0);
goto block_17;
}
}
block_17:
{
lean_object* x_13; size_t x_14; size_t x_15; 
if (lean_is_scalar(x_9)) {
 x_13 = lean_alloc_ctor(0, 2, 0);
} else {
 x_13 = x_9;
}
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_11);
x_14 = 1;
x_15 = lean_usize_add(x_3, x_14);
x_3 = x_15;
x_4 = x_13;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_getConstants_spec__0_spec__0_spec__3_spec__7___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_getConstants_spec__0_spec__0_spec__3_spec__7___redArg(x_1, x_6, x_7, x_4);
lean_dec_ref(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_getConstants_spec__0_spec__0_spec__3(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_lt(x_3, x_2);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_4);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_22; 
x_12 = lean_ctor_get(x_4, 1);
lean_inc(x_12);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 x_13 = x_4;
} else {
 lean_dec_ref(x_4);
 x_13 = lean_box(0);
}
x_14 = lean_box(0);
x_22 = lean_array_uget(x_1, x_3);
if (lean_obj_tag(x_22) == 0)
{
x_15 = x_12;
x_16 = lean_box(0);
goto block_21;
}
else
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec_ref(x_22);
x_24 = l_Lean_LocalDecl_isImplementationDetail(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = l_Lean_LocalDecl_toExpr(x_23);
x_26 = lean_array_push(x_12, x_25);
x_15 = x_26;
x_16 = lean_box(0);
goto block_21;
}
else
{
lean_dec(x_23);
x_15 = x_12;
x_16 = lean_box(0);
goto block_21;
}
}
block_21:
{
lean_object* x_17; size_t x_18; size_t x_19; lean_object* x_20; 
if (lean_is_scalar(x_13)) {
 x_17 = lean_alloc_ctor(0, 2, 0);
} else {
 x_17 = x_13;
}
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_15);
x_18 = 1;
x_19 = lean_usize_add(x_3, x_18);
x_20 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_getConstants_spec__0_spec__0_spec__3_spec__7___redArg(x_1, x_2, x_19, x_17);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_getConstants_spec__0_spec__0_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_getConstants_spec__0_spec__0_spec__3(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_getConstants_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_8);
x_9 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_9);
lean_dec_ref(x_1);
lean_inc_ref(x_2);
x_10 = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_getConstants_spec__0_spec__0_spec__2(x_2, x_8, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_2);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_10, 0);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
lean_dec_ref(x_9);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec_ref(x_12);
lean_ctor_set(x_10, 0, x_13);
return x_10;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; 
lean_free_object(x_10);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec_ref(x_12);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
x_17 = lean_array_size(x_9);
x_18 = 0;
x_19 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_getConstants_spec__0_spec__0_spec__3(x_9, x_17, x_18, x_16, x_3, x_4, x_5, x_6);
lean_dec_ref(x_9);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = lean_ctor_get(x_21, 0);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
lean_ctor_set(x_19, 0, x_23);
return x_19;
}
else
{
lean_object* x_24; 
lean_inc_ref(x_22);
lean_dec(x_21);
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
lean_dec_ref(x_22);
lean_ctor_set(x_19, 0, x_24);
return x_19;
}
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_19, 0);
lean_inc(x_25);
lean_dec(x_19);
x_26 = lean_ctor_get(x_25, 0);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_27);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; 
lean_inc_ref(x_26);
lean_dec(x_25);
x_29 = lean_ctor_get(x_26, 0);
lean_inc(x_29);
lean_dec_ref(x_26);
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_29);
return x_30;
}
}
}
else
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_19);
if (x_31 == 0)
{
return x_19;
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_19, 0);
lean_inc(x_32);
lean_dec(x_19);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_32);
return x_33;
}
}
}
}
else
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_10, 0);
lean_inc(x_34);
lean_dec(x_10);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; 
lean_dec_ref(x_9);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
lean_dec_ref(x_34);
x_36 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_36, 0, x_35);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; size_t x_40; size_t x_41; lean_object* x_42; 
x_37 = lean_ctor_get(x_34, 0);
lean_inc(x_37);
lean_dec_ref(x_34);
x_38 = lean_box(0);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
x_40 = lean_array_size(x_9);
x_41 = 0;
x_42 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_getConstants_spec__0_spec__0_spec__3(x_9, x_40, x_41, x_39, x_3, x_4, x_5, x_6);
lean_dec_ref(x_9);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 x_44 = x_42;
} else {
 lean_dec_ref(x_42);
 x_44 = lean_box(0);
}
x_45 = lean_ctor_get(x_43, 0);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_43, 1);
lean_inc(x_46);
lean_dec(x_43);
if (lean_is_scalar(x_44)) {
 x_47 = lean_alloc_ctor(0, 1, 0);
} else {
 x_47 = x_44;
}
lean_ctor_set(x_47, 0, x_46);
return x_47;
}
else
{
lean_object* x_48; lean_object* x_49; 
lean_inc_ref(x_45);
lean_dec(x_43);
x_48 = lean_ctor_get(x_45, 0);
lean_inc(x_48);
lean_dec_ref(x_45);
if (lean_is_scalar(x_44)) {
 x_49 = lean_alloc_ctor(0, 1, 0);
} else {
 x_49 = x_44;
}
lean_ctor_set(x_49, 0, x_48);
return x_49;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_42, 0);
lean_inc(x_50);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 x_51 = x_42;
} else {
 lean_dec_ref(x_42);
 x_51 = lean_box(0);
}
if (lean_is_scalar(x_51)) {
 x_52 = lean_alloc_ctor(1, 1, 0);
} else {
 x_52 = x_51;
}
lean_ctor_set(x_52, 0, x_50);
return x_52;
}
}
}
}
else
{
uint8_t x_53; 
lean_dec_ref(x_9);
x_53 = !lean_is_exclusive(x_10);
if (x_53 == 0)
{
return x_10;
}
else
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_10, 0);
lean_inc(x_54);
lean_dec(x_10);
x_55 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_55, 0, x_54);
return x_55;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_getConstants_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_getConstants_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
static lean_object* _init_l_Lean_getLocalHyps___at___00Lean_MVarId_getConstants_spec__0___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___at___00Lean_MVarId_getConstants_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_1, 2);
x_7 = lean_ctor_get(x_6, 1);
lean_inc_ref(x_7);
x_8 = l_Lean_getLocalHyps___at___00Lean_MVarId_getConstants_spec__0___closed__0;
x_9 = l_Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_getConstants_spec__0_spec__0(x_7, x_8, x_1, x_2, x_3, x_4);
lean_dec_ref(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_getLocalHyps___at___00Lean_MVarId_getConstants_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_getLocalHyps___at___00Lean_MVarId_getConstants_spec__0(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_getConstants___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_MVarId_getType(x_1, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec_ref(x_7);
lean_inc_ref(x_2);
x_9 = l_Lean_getLocalHyps___at___00Lean_MVarId_getConstants_spec__0(x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec_ref(x_9);
x_11 = l_Lean_Expr_getUsedConstantsAsSet(x_8);
x_12 = lean_array_size(x_10);
x_13 = 0;
x_14 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_getConstants_spec__1(x_10, x_12, x_13, x_11, x_2, x_3, x_4, x_5);
lean_dec(x_10);
return x_14;
}
else
{
uint8_t x_15; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_15 = !lean_is_exclusive(x_9);
if (x_15 == 0)
{
return x_9;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_9, 0);
lean_inc(x_16);
lean_dec(x_9);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
}
}
else
{
uint8_t x_18; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_18 = !lean_is_exclusive(x_7);
if (x_18 == 0)
{
return x_7;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_7, 0);
lean_inc(x_19);
lean_dec(x_7);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_getConstants___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_MVarId_getConstants___lam__0(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_getConstants(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; 
lean_inc(x_1);
x_7 = lean_alloc_closure((void*)(l_Lean_MVarId_getConstants___lam__0___boxed), 6, 1);
lean_closure_set(x_7, 0, x_1);
x_8 = l_Lean_MVarId_withContext___at___00Lean_MVarId_getConstants_spec__2___redArg(x_1, x_7, x_2, x_3, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_getConstants___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_MVarId_getConstants(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_getConstants_spec__0_spec__0_spec__3_spec__7(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_getConstants_spec__0_spec__0_spec__3_spec__7___redArg(x_1, x_2, x_3, x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_getConstants_spec__0_spec__0_spec__3_spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_getConstants_spec__0_spec__0_spec__3_spec__7(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_getConstants_spec__0_spec__0_spec__2_spec__5_spec__6(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_getConstants_spec__0_spec__0_spec__2_spec__5_spec__6___redArg(x_1, x_2, x_3, x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_getConstants_spec__0_spec__0_spec__2_spec__5_spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_getLocalHyps___at___00Lean_MVarId_getConstants_spec__0_spec__0_spec__2_spec__5_spec__6(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_getRelevantConstants_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_lt(x_3, x_2);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_4);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_array_uget(x_1, x_3);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_13 = lean_infer_type(x_12, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec_ref(x_13);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_15 = l_Lean_Expr_relevantConstantsAsSet(x_14, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec_ref(x_15);
x_17 = l_Lean_NameSet_append(x_4, x_16);
x_18 = 1;
x_19 = lean_usize_add(x_3, x_18);
x_3 = x_19;
x_4 = x_17;
goto _start;
}
else
{
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
return x_15;
}
}
else
{
uint8_t x_21; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
x_21 = !lean_is_exclusive(x_13);
if (x_21 == 0)
{
return x_13;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_13, 0);
lean_inc(x_22);
lean_dec(x_13);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
return x_23;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_getRelevantConstants_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_getRelevantConstants_spec__0(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_getRelevantConstants___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_MVarId_getType(x_1, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec_ref(x_7);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_9 = l_Lean_Expr_relevantConstantsAsSet(x_8, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec_ref(x_9);
lean_inc_ref(x_2);
x_11 = l_Lean_getLocalHyps___at___00Lean_MVarId_getConstants_spec__0(x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; size_t x_13; size_t x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec_ref(x_11);
x_13 = lean_array_size(x_12);
x_14 = 0;
x_15 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_getRelevantConstants_spec__0(x_12, x_13, x_14, x_10, x_2, x_3, x_4, x_5);
lean_dec(x_12);
return x_15;
}
else
{
uint8_t x_16; 
lean_dec(x_10);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_16 = !lean_is_exclusive(x_11);
if (x_16 == 0)
{
return x_11;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_11, 0);
lean_inc(x_17);
lean_dec(x_11);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
}
}
else
{
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_9;
}
}
else
{
uint8_t x_19; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_19 = !lean_is_exclusive(x_7);
if (x_19 == 0)
{
return x_7;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_7, 0);
lean_inc(x_20);
lean_dec(x_7);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_20);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_getRelevantConstants___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_MVarId_getRelevantConstants___lam__0(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_getRelevantConstants(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; 
lean_inc(x_1);
x_7 = lean_alloc_closure((void*)(l_Lean_MVarId_getRelevantConstants___lam__0___boxed), 6, 1);
lean_closure_set(x_7, 0, x_1);
x_8 = l_Lean_MVarId_withContext___at___00Lean_MVarId_getConstants_spec__2___redArg(x_1, x_7, x_2, x_3, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_getRelevantConstants___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_MVarId_getRelevantConstants(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_ppSelector(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_9 = l_Lean_Meta_ppGoal(x_2, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec_ref(x_9);
x_11 = l_Std_Format_defWidth;
x_12 = lean_unsigned_to_nat(0u);
x_13 = l_Std_Format_pretty(x_10, x_11, x_12, x_12);
x_14 = lean_apply_7(x_1, x_13, x_3, x_4, x_5, x_6, x_7, lean_box(0));
return x_14;
}
else
{
uint8_t x_15; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_15 = !lean_is_exclusive(x_9);
if (x_15 == 0)
{
return x_9;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_9, 0);
lean_inc(x_16);
lean_dec(x_9);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_ppSelector___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_LibrarySuggestions_ppSelector(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_Selector_postFilter___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_7; lean_object* x_8; lean_object* x_9; 
x_7 = 1;
x_8 = lean_box(x_7);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_Selector_postFilter___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_LibrarySuggestions_Selector_postFilter___lam__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LibrarySuggestions_Selector_postFilter_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_eq(x_3, x_4);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_1, 2);
x_13 = lean_array_uget(x_2, x_3);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_inc_ref(x_12);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_15 = lean_apply_6(x_12, x_14, x_6, x_7, x_8, x_9, lean_box(0));
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_22; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec_ref(x_15);
x_22 = lean_unbox(x_16);
lean_dec(x_16);
if (x_22 == 0)
{
lean_dec(x_13);
x_17 = x_5;
goto block_21;
}
else
{
lean_object* x_23; 
x_23 = lean_array_push(x_5, x_13);
x_17 = x_23;
goto block_21;
}
block_21:
{
size_t x_18; size_t x_19; 
x_18 = 1;
x_19 = lean_usize_add(x_3, x_18);
x_3 = x_19;
x_5 = x_17;
goto _start;
}
}
else
{
uint8_t x_24; 
lean_dec(x_13);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_24 = !lean_is_exclusive(x_15);
if (x_24 == 0)
{
return x_15;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_15, 0);
lean_inc(x_25);
lean_dec(x_15);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
}
}
else
{
lean_object* x_27; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_1);
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_5);
return x_27;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LibrarySuggestions_Selector_postFilter_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LibrarySuggestions_Selector_postFilter_spec__0(x_1, x_2, x_11, x_12, x_5, x_6, x_7, x_8, x_9);
lean_dec_ref(x_2);
return x_13;
}
}
static lean_object* _init_l_Lean_LibrarySuggestions_Selector_postFilter___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_Selector_postFilter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_ctor_get(x_3, 0);
x_10 = lean_ctor_get(x_3, 1);
x_11 = lean_ctor_get(x_3, 3);
x_12 = ((lean_object*)(l_Lean_LibrarySuggestions_Selector_postFilter___closed__0));
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_10);
lean_ctor_set(x_13, 2, x_12);
lean_ctor_set(x_13, 3, x_11);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_14 = lean_apply_7(x_1, x_2, x_13, x_4, x_5, x_6, x_7, lean_box(0));
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_array_get_size(x_16);
x_19 = l_Lean_LibrarySuggestions_Selector_postFilter___closed__1;
x_20 = lean_nat_dec_lt(x_17, x_18);
if (x_20 == 0)
{
lean_dec(x_16);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_ctor_set(x_14, 0, x_19);
return x_14;
}
else
{
uint8_t x_21; 
x_21 = lean_nat_dec_le(x_18, x_18);
if (x_21 == 0)
{
if (x_20 == 0)
{
lean_dec(x_16);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_ctor_set(x_14, 0, x_19);
return x_14;
}
else
{
size_t x_22; size_t x_23; lean_object* x_24; 
lean_free_object(x_14);
x_22 = 0;
x_23 = lean_usize_of_nat(x_18);
x_24 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LibrarySuggestions_Selector_postFilter_spec__0(x_3, x_16, x_22, x_23, x_19, x_4, x_5, x_6, x_7);
lean_dec(x_16);
return x_24;
}
}
else
{
size_t x_25; size_t x_26; lean_object* x_27; 
lean_free_object(x_14);
x_25 = 0;
x_26 = lean_usize_of_nat(x_18);
x_27 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LibrarySuggestions_Selector_postFilter_spec__0(x_3, x_16, x_25, x_26, x_19, x_4, x_5, x_6, x_7);
lean_dec(x_16);
return x_27;
}
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_28 = lean_ctor_get(x_14, 0);
lean_inc(x_28);
lean_dec(x_14);
x_29 = lean_unsigned_to_nat(0u);
x_30 = lean_array_get_size(x_28);
x_31 = l_Lean_LibrarySuggestions_Selector_postFilter___closed__1;
x_32 = lean_nat_dec_lt(x_29, x_30);
if (x_32 == 0)
{
lean_object* x_33; 
lean_dec(x_28);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_33 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_33, 0, x_31);
return x_33;
}
else
{
uint8_t x_34; 
x_34 = lean_nat_dec_le(x_30, x_30);
if (x_34 == 0)
{
if (x_32 == 0)
{
lean_object* x_35; 
lean_dec(x_28);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_35 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_35, 0, x_31);
return x_35;
}
else
{
size_t x_36; size_t x_37; lean_object* x_38; 
x_36 = 0;
x_37 = lean_usize_of_nat(x_30);
x_38 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LibrarySuggestions_Selector_postFilter_spec__0(x_3, x_28, x_36, x_37, x_31, x_4, x_5, x_6, x_7);
lean_dec(x_28);
return x_38;
}
}
else
{
size_t x_39; size_t x_40; lean_object* x_41; 
x_39 = 0;
x_40 = lean_usize_of_nat(x_30);
x_41 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LibrarySuggestions_Selector_postFilter_spec__0(x_3, x_28, x_39, x_40, x_31, x_4, x_5, x_6, x_7);
lean_dec(x_28);
return x_41;
}
}
}
}
else
{
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_Selector_postFilter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_LibrarySuggestions_Selector_postFilter(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_Selector_maxSuggestions(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
lean_inc_ref(x_3);
x_9 = lean_apply_7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, lean_box(0));
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_3, 0);
lean_inc(x_12);
lean_dec_ref(x_3);
x_13 = lean_unsigned_to_nat(0u);
x_14 = l_Array_extract___redArg(x_11, x_13, x_12);
lean_dec(x_11);
lean_ctor_set(x_9, 0, x_14);
return x_9;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_9, 0);
lean_inc(x_15);
lean_dec(x_9);
x_16 = lean_ctor_get(x_3, 0);
lean_inc(x_16);
lean_dec_ref(x_3);
x_17 = lean_unsigned_to_nat(0u);
x_18 = l_Array_extract___redArg(x_15, x_17, x_16);
lean_dec(x_15);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
}
else
{
lean_dec_ref(x_3);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_Selector_maxSuggestions___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_LibrarySuggestions_Selector_maxSuggestions(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LibrarySuggestions_Selector_combine_spec__2___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
double x_3; double x_4; uint8_t x_5; 
x_3 = lean_ctor_get_float(x_2, sizeof(void*)*2);
x_4 = lean_ctor_get_float(x_1, sizeof(void*)*2);
x_5 = lean_float_decLt(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LibrarySuggestions_Selector_combine_spec__2___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LibrarySuggestions_Selector_combine_spec__2___redArg___lam__0(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LibrarySuggestions_Selector_combine_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_nat_dec_lt(x_2, x_3);
if (x_4 == 0)
{
lean_dec(x_2);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LibrarySuggestions_Selector_combine_spec__2___redArg___closed__0));
lean_inc(x_2);
x_6 = l_Array_qpartition___redArg(x_1, x_5, x_2, x_3);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec_ref(x_6);
x_9 = lean_nat_dec_le(x_3, x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LibrarySuggestions_Selector_combine_spec__2___redArg(x_8, x_2, x_7);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_7, x_11);
lean_dec(x_7);
x_1 = x_10;
x_2 = x_12;
goto _start;
}
else
{
lean_dec(x_7);
lean_dec(x_2);
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LibrarySuggestions_Selector_combine_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LibrarySuggestions_Selector_combine_spec__2___redArg(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_LibrarySuggestions_Selector_combine_spec__0_spec__1_spec__3_spec__8___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint64_t x_10; uint64_t x_11; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 2);
lean_inc(x_5);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 lean_ctor_release(x_2, 2);
 x_6 = x_2;
} else {
 lean_dec_ref(x_2);
 x_6 = lean_box(0);
}
x_7 = lean_ctor_get(x_3, 0);
x_8 = lean_ctor_get(x_3, 1);
x_9 = lean_array_get_size(x_1);
x_10 = l_Lean_Name_hash___override(x_7);
if (lean_obj_tag(x_8) == 0)
{
uint64_t x_29; 
x_29 = 11;
x_11 = x_29;
goto block_28;
}
else
{
lean_object* x_30; uint64_t x_31; uint64_t x_32; uint64_t x_33; 
x_30 = lean_ctor_get(x_8, 0);
x_31 = lean_string_hash(x_30);
x_32 = 13;
x_33 = lean_uint64_mix_hash(x_31, x_32);
x_11 = x_33;
goto block_28;
}
block_28:
{
uint64_t x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; uint64_t x_16; uint64_t x_17; uint64_t x_18; size_t x_19; size_t x_20; size_t x_21; size_t x_22; size_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_12 = lean_uint64_mix_hash(x_10, x_11);
x_13 = 32;
x_14 = lean_uint64_shift_right(x_12, x_13);
x_15 = lean_uint64_xor(x_12, x_14);
x_16 = 16;
x_17 = lean_uint64_shift_right(x_15, x_16);
x_18 = lean_uint64_xor(x_15, x_17);
x_19 = lean_uint64_to_usize(x_18);
x_20 = lean_usize_of_nat(x_9);
x_21 = 1;
x_22 = lean_usize_sub(x_20, x_21);
x_23 = lean_usize_land(x_19, x_22);
x_24 = lean_array_uget(x_1, x_23);
if (lean_is_scalar(x_6)) {
 x_25 = lean_alloc_ctor(1, 3, 0);
} else {
 x_25 = x_6;
}
lean_ctor_set(x_25, 0, x_3);
lean_ctor_set(x_25, 1, x_4);
lean_ctor_set(x_25, 2, x_24);
x_26 = lean_array_uset(x_1, x_23, x_25);
x_1 = x_26;
x_2 = x_5;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_LibrarySuggestions_Selector_combine_spec__0_spec__1_spec__3___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_1, x_4);
if (x_5 == 0)
{
lean_dec_ref(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_array_fget(x_2, x_1);
x_7 = lean_box(0);
x_8 = lean_array_fset(x_2, x_1, x_7);
x_9 = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_LibrarySuggestions_Selector_combine_spec__0_spec__1_spec__3_spec__8___redArg(x_3, x_6);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_1, x_10);
lean_dec(x_1);
x_1 = x_11;
x_2 = x_8;
x_3 = x_9;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_LibrarySuggestions_Selector_combine_spec__0_spec__1___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(2u);
x_4 = lean_nat_mul(x_2, x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_box(0);
x_7 = lean_mk_array(x_4, x_6);
x_8 = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_LibrarySuggestions_Selector_combine_spec__0_spec__1_spec__3___redArg(x_5, x_1, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_LibrarySuggestions_Selector_combine_spec__0_spec__2___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_1);
return x_3;
}
else
{
lean_object* x_4; double x_5; double x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get_float(x_4, sizeof(void*)*2);
x_6 = lean_ctor_get_float(x_1, sizeof(void*)*2);
x_7 = lean_float_decLt(x_5, x_6);
if (x_7 == 0)
{
lean_dec_ref(x_1);
return x_2;
}
else
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_2);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_2, 0);
lean_dec(x_9);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
else
{
lean_object* x_10; 
lean_dec(x_2);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_1);
return x_10;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_LibrarySuggestions_Selector_combine_spec__0_spec__0_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
else
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
}
else
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_string_dec_eq(x_6, x_7);
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_LibrarySuggestions_Selector_combine_spec__0_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Option_instBEq_beq___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_LibrarySuggestions_Selector_combine_spec__0_spec__0_spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_LibrarySuggestions_Selector_combine_spec__0_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_box(0);
x_5 = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_LibrarySuggestions_Selector_combine_spec__0_spec__2___lam__0(x_1, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_dec_ref(x_2);
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec_ref(x_5);
x_7 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_7, 0, x_2);
lean_ctor_set(x_7, 1, x_6);
lean_ctor_set(x_7, 2, x_3);
return x_7;
}
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_3, 2);
lean_inc(x_10);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 lean_ctor_release(x_3, 2);
 x_11 = x_3;
} else {
 lean_dec_ref(x_3);
 x_11 = lean_box(0);
}
x_20 = lean_ctor_get(x_8, 0);
x_21 = lean_ctor_get(x_8, 1);
x_22 = lean_ctor_get(x_2, 0);
x_23 = lean_ctor_get(x_2, 1);
x_24 = lean_name_eq(x_20, x_22);
if (x_24 == 0)
{
x_12 = x_24;
goto block_19;
}
else
{
uint8_t x_25; 
x_25 = l_Option_instBEq_beq___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_LibrarySuggestions_Selector_combine_spec__0_spec__0_spec__1(x_21, x_23);
x_12 = x_25;
goto block_19;
}
block_19:
{
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_LibrarySuggestions_Selector_combine_spec__0_spec__2(x_1, x_2, x_10);
if (lean_is_scalar(x_11)) {
 x_14 = lean_alloc_ctor(1, 3, 0);
} else {
 x_14 = x_11;
}
lean_ctor_set(x_14, 0, x_8);
lean_ctor_set(x_14, 1, x_9);
lean_ctor_set(x_14, 2, x_13);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_8);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_9);
x_16 = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_LibrarySuggestions_Selector_combine_spec__0_spec__2___lam__0(x_1, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_dec(x_11);
lean_dec_ref(x_2);
return x_10;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec_ref(x_16);
if (lean_is_scalar(x_11)) {
 x_18 = lean_alloc_ctor(1, 3, 0);
} else {
 x_18 = x_11;
}
lean_ctor_set(x_18, 0, x_2);
lean_ctor_set(x_18, 1, x_17);
lean_ctor_set(x_18, 2, x_10);
return x_18;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_LibrarySuggestions_Selector_combine_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_9 = lean_ctor_get(x_4, 0);
x_10 = lean_ctor_get(x_4, 1);
x_11 = lean_ctor_get(x_1, 0);
x_12 = lean_ctor_get(x_1, 1);
x_13 = lean_name_eq(x_9, x_11);
if (x_13 == 0)
{
x_6 = x_13;
goto block_8;
}
else
{
uint8_t x_14; 
x_14 = l_Option_instBEq_beq___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_LibrarySuggestions_Selector_combine_spec__0_spec__0_spec__1(x_10, x_12);
x_6 = x_14;
goto block_8;
}
block_8:
{
if (x_6 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
return x_6;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_LibrarySuggestions_Selector_combine_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_LibrarySuggestions_Selector_combine_spec__0_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_LibrarySuggestions_Selector_combine_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; size_t x_6; lean_object* x_7; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint64_t x_17; uint64_t x_18; 
x_11 = lean_ctor_get(x_2, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_12);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 x_13 = x_2;
} else {
 lean_dec_ref(x_2);
 x_13 = lean_box(0);
}
x_14 = lean_ctor_get(x_3, 0);
x_15 = lean_ctor_get(x_3, 1);
x_16 = lean_array_get_size(x_12);
x_17 = l_Lean_Name_hash___override(x_14);
if (lean_obj_tag(x_15) == 0)
{
uint64_t x_53; 
x_53 = 11;
x_18 = x_53;
goto block_52;
}
else
{
lean_object* x_54; uint64_t x_55; uint64_t x_56; uint64_t x_57; 
x_54 = lean_ctor_get(x_15, 0);
x_55 = lean_string_hash(x_54);
x_56 = 13;
x_57 = lean_uint64_mix_hash(x_55, x_56);
x_18 = x_57;
goto block_52;
}
block_10:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_array_uset(x_5, x_6, x_4);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
block_52:
{
uint64_t x_19; uint64_t x_20; uint64_t x_21; uint64_t x_22; uint64_t x_23; uint64_t x_24; uint64_t x_25; size_t x_26; size_t x_27; size_t x_28; size_t x_29; size_t x_30; lean_object* x_31; uint8_t x_32; 
x_19 = lean_uint64_mix_hash(x_17, x_18);
x_20 = 32;
x_21 = lean_uint64_shift_right(x_19, x_20);
x_22 = lean_uint64_xor(x_19, x_21);
x_23 = 16;
x_24 = lean_uint64_shift_right(x_22, x_23);
x_25 = lean_uint64_xor(x_22, x_24);
x_26 = lean_uint64_to_usize(x_25);
x_27 = lean_usize_of_nat(x_16);
x_28 = 1;
x_29 = lean_usize_sub(x_27, x_28);
x_30 = lean_usize_land(x_26, x_29);
x_31 = lean_array_uget(x_12, x_30);
x_32 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_LibrarySuggestions_Selector_combine_spec__0_spec__0___redArg(x_3, x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_33 = lean_unsigned_to_nat(1u);
x_34 = lean_nat_add(x_11, x_33);
lean_dec(x_11);
x_35 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_35, 0, x_3);
lean_ctor_set(x_35, 1, x_1);
lean_ctor_set(x_35, 2, x_31);
x_36 = lean_array_uset(x_12, x_30, x_35);
x_37 = lean_unsigned_to_nat(4u);
x_38 = lean_nat_mul(x_34, x_37);
x_39 = lean_unsigned_to_nat(3u);
x_40 = lean_nat_div(x_38, x_39);
lean_dec(x_38);
x_41 = lean_array_get_size(x_36);
x_42 = lean_nat_dec_le(x_40, x_41);
lean_dec(x_40);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_LibrarySuggestions_Selector_combine_spec__0_spec__1___redArg(x_36);
if (lean_is_scalar(x_13)) {
 x_44 = lean_alloc_ctor(0, 2, 0);
} else {
 x_44 = x_13;
}
lean_ctor_set(x_44, 0, x_34);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
else
{
lean_object* x_45; 
if (lean_is_scalar(x_13)) {
 x_45 = lean_alloc_ctor(0, 2, 0);
} else {
 x_45 = x_13;
}
lean_ctor_set(x_45, 0, x_34);
lean_ctor_set(x_45, 1, x_36);
return x_45;
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
lean_dec(x_13);
x_46 = lean_box(0);
x_47 = lean_array_uset(x_12, x_30, x_46);
lean_inc_ref(x_3);
x_48 = l_Std_DHashMap_Internal_AssocList_Const_alter___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_LibrarySuggestions_Selector_combine_spec__0_spec__2(x_1, x_3, x_31);
x_49 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_LibrarySuggestions_Selector_combine_spec__0_spec__0___redArg(x_3, x_48);
lean_dec_ref(x_3);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_unsigned_to_nat(1u);
x_51 = lean_nat_sub(x_11, x_50);
lean_dec(x_11);
x_4 = x_48;
x_5 = x_47;
x_6 = x_30;
x_7 = x_51;
goto block_10;
}
else
{
x_4 = x_48;
x_5 = x_47;
x_6 = x_30;
x_7 = x_11;
goto block_10;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_LibrarySuggestions_Selector_combine_spec__1___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_lt(x_3, x_2);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_4);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; size_t x_13; size_t x_14; 
x_8 = lean_array_uget(x_1, x_3);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
x_12 = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_LibrarySuggestions_Selector_combine_spec__0(x_8, x_4, x_11);
x_13 = 1;
x_14 = lean_usize_add(x_3, x_13);
x_3 = x_14;
x_4 = x_12;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_LibrarySuggestions_Selector_combine_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_LibrarySuggestions_Selector_combine_spec__1___redArg(x_1, x_6, x_7, x_4);
lean_dec_ref(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_LibrarySuggestions_Selector_combine_spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 2);
lean_inc(x_4);
lean_dec_ref(x_2);
x_5 = lean_array_push(x_1, x_3);
x_1 = x_5;
x_2 = x_4;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LibrarySuggestions_Selector_combine_spec__4(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_LibrarySuggestions_Selector_combine_spec__3(x_4, x_6);
x_8 = 1;
x_9 = lean_usize_add(x_2, x_8);
x_2 = x_9;
x_4 = x_7;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LibrarySuggestions_Selector_combine_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LibrarySuggestions_Selector_combine_spec__4(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
static lean_object* _init_l_Lean_LibrarySuggestions_Selector_combine___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_unsigned_to_nat(16u);
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_LibrarySuggestions_Selector_combine___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_LibrarySuggestions_Selector_combine___closed__0;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_Selector_combine(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
x_10 = lean_apply_7(x_1, x_3, x_4, x_5, x_6, x_7, x_8, lean_box(0));
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec_ref(x_10);
lean_inc_ref(x_4);
x_12 = lean_apply_7(x_2, x_3, x_4, x_5, x_6, x_7, x_8, lean_box(0));
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec_ref(x_12);
x_14 = lean_unsigned_to_nat(0u);
x_15 = l_Lean_LibrarySuggestions_Selector_combine___closed__1;
x_16 = l_Array_append___redArg(x_11, x_13);
lean_dec(x_13);
x_17 = lean_array_size(x_16);
x_18 = 0;
x_19 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_LibrarySuggestions_Selector_combine_spec__1___redArg(x_16, x_17, x_18, x_15);
lean_dec_ref(x_16);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_39; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 x_21 = x_19;
} else {
 lean_dec_ref(x_19);
 x_21 = lean_box(0);
}
x_46 = lean_ctor_get(x_20, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_20, 1);
lean_inc_ref(x_47);
lean_dec(x_20);
x_48 = lean_mk_empty_array_with_capacity(x_46);
lean_dec(x_46);
x_49 = lean_array_get_size(x_47);
x_50 = lean_nat_dec_lt(x_14, x_49);
if (x_50 == 0)
{
lean_dec_ref(x_47);
x_39 = x_48;
goto block_45;
}
else
{
uint8_t x_51; 
x_51 = lean_nat_dec_le(x_49, x_49);
if (x_51 == 0)
{
if (x_50 == 0)
{
lean_dec_ref(x_47);
x_39 = x_48;
goto block_45;
}
else
{
size_t x_52; lean_object* x_53; 
x_52 = lean_usize_of_nat(x_49);
x_53 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LibrarySuggestions_Selector_combine_spec__4(x_47, x_18, x_52, x_48);
lean_dec_ref(x_47);
x_39 = x_53;
goto block_45;
}
}
else
{
size_t x_54; lean_object* x_55; 
x_54 = lean_usize_of_nat(x_49);
x_55 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LibrarySuggestions_Selector_combine_spec__4(x_47, x_18, x_54, x_48);
lean_dec_ref(x_47);
x_39 = x_55;
goto block_45;
}
}
block_26:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_4, 0);
lean_inc(x_23);
lean_dec_ref(x_4);
x_24 = l_Array_extract___redArg(x_22, x_14, x_23);
lean_dec_ref(x_22);
if (lean_is_scalar(x_21)) {
 x_25 = lean_alloc_ctor(0, 1, 0);
} else {
 x_25 = x_21;
}
lean_ctor_set(x_25, 0, x_24);
return x_25;
}
block_32:
{
lean_object* x_31; 
lean_dec(x_27);
x_31 = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LibrarySuggestions_Selector_combine_spec__2___redArg(x_29, x_28, x_30);
lean_dec(x_30);
x_22 = x_31;
goto block_26;
}
block_38:
{
uint8_t x_37; 
x_37 = lean_nat_dec_le(x_36, x_35);
if (x_37 == 0)
{
lean_dec(x_35);
lean_inc(x_36);
x_27 = x_33;
x_28 = x_36;
x_29 = x_34;
x_30 = x_36;
goto block_32;
}
else
{
x_27 = x_33;
x_28 = x_36;
x_29 = x_34;
x_30 = x_35;
goto block_32;
}
}
block_45:
{
lean_object* x_40; uint8_t x_41; 
x_40 = lean_array_get_size(x_39);
x_41 = lean_nat_dec_eq(x_40, x_14);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_42 = lean_unsigned_to_nat(1u);
x_43 = lean_nat_sub(x_40, x_42);
x_44 = lean_nat_dec_le(x_14, x_43);
if (x_44 == 0)
{
lean_inc(x_43);
x_33 = x_40;
x_34 = x_39;
x_35 = x_43;
x_36 = x_43;
goto block_38;
}
else
{
x_33 = x_40;
x_34 = x_39;
x_35 = x_43;
x_36 = x_14;
goto block_38;
}
}
else
{
x_22 = x_39;
goto block_26;
}
}
}
else
{
uint8_t x_56; 
lean_dec_ref(x_4);
x_56 = !lean_is_exclusive(x_19);
if (x_56 == 0)
{
return x_19;
}
else
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_19, 0);
lean_inc(x_57);
lean_dec(x_19);
x_58 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_58, 0, x_57);
return x_58;
}
}
}
else
{
lean_dec(x_11);
lean_dec_ref(x_4);
return x_12;
}
}
else
{
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_Selector_combine___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_LibrarySuggestions_Selector_combine(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_LibrarySuggestions_Selector_combine_spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_LibrarySuggestions_Selector_combine_spec__1___redArg(x_1, x_2, x_3, x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_LibrarySuggestions_Selector_combine_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_LibrarySuggestions_Selector_combine_spec__1(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LibrarySuggestions_Selector_combine_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LibrarySuggestions_Selector_combine_spec__2___redArg(x_2, x_3, x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LibrarySuggestions_Selector_combine_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_LibrarySuggestions_Selector_combine_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_LibrarySuggestions_Selector_combine_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_LibrarySuggestions_Selector_combine_spec__0_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_LibrarySuggestions_Selector_combine_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_LibrarySuggestions_Selector_combine_spec__0_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_LibrarySuggestions_Selector_combine_spec__0_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_LibrarySuggestions_Selector_combine_spec__0_spec__1___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_LibrarySuggestions_Selector_combine_spec__0_spec__1_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_LibrarySuggestions_Selector_combine_spec__0_spec__1_spec__3___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_LibrarySuggestions_Selector_combine_spec__0_spec__1_spec__3_spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_LibrarySuggestions_Selector_combine_spec__0_spec__1_spec__3_spec__8___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LibrarySuggestions_Selector_filterGrindAnnotated_spec__0___redArg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_13; 
x_13 = lean_usize_dec_eq(x_3, x_4);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_18; lean_object* x_19; 
x_14 = lean_array_uget(x_2, x_3);
x_18 = lean_ctor_get(x_14, 0);
lean_inc(x_18);
x_19 = l_Lean_Environment_getModuleIdxFor_x3f(x_1, x_18);
lean_dec(x_18);
if (lean_obj_tag(x_19) == 0)
{
x_15 = lean_box(0);
goto block_17;
}
else
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec_ref(x_19);
lean_inc_ref(x_1);
x_21 = l_Lean_Elab_Tactic_Grind_isGrindAnnotatedModule(x_1, x_20);
lean_dec(x_20);
if (x_21 == 0)
{
x_15 = lean_box(0);
goto block_17;
}
else
{
lean_dec(x_14);
x_7 = x_5;
x_8 = lean_box(0);
goto block_12;
}
}
block_17:
{
lean_object* x_16; 
x_16 = lean_array_push(x_5, x_14);
x_7 = x_16;
x_8 = lean_box(0);
goto block_12;
}
}
else
{
lean_object* x_22; 
lean_dec_ref(x_1);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_5);
return x_22;
}
block_12:
{
size_t x_9; size_t x_10; 
x_9 = 1;
x_10 = lean_usize_add(x_3, x_9);
x_3 = x_10;
x_5 = x_7;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LibrarySuggestions_Selector_filterGrindAnnotated_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LibrarySuggestions_Selector_filterGrindAnnotated_spec__0___redArg(x_1, x_2, x_7, x_8, x_5);
lean_dec_ref(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_Selector_filterGrindAnnotated(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc_ref(x_3);
x_9 = lean_apply_7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, lean_box(0));
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_3, 1);
lean_inc(x_11);
lean_dec_ref(x_3);
x_12 = ((lean_object*)(l_Lean_LibrarySuggestions_Selector_filterGrindAnnotated___closed__1));
x_13 = l_Option_instBEq_beq___at___00Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_Const_alter___at___00Lean_LibrarySuggestions_Selector_combine_spec__0_spec__0_spec__1(x_11, x_12);
lean_dec(x_11);
if (x_13 == 0)
{
lean_dec(x_10);
lean_dec(x_7);
return x_9;
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_9);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_15 = lean_ctor_get(x_9, 0);
lean_dec(x_15);
x_16 = lean_st_ref_get(x_7);
lean_dec(x_7);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_array_get_size(x_10);
x_19 = l_Lean_LibrarySuggestions_Selector_postFilter___closed__1;
x_20 = lean_nat_dec_lt(x_17, x_18);
if (x_20 == 0)
{
lean_dec(x_16);
lean_dec(x_10);
lean_ctor_set(x_9, 0, x_19);
return x_9;
}
else
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_16, 0);
lean_inc_ref(x_21);
lean_dec(x_16);
x_22 = lean_nat_dec_le(x_18, x_18);
if (x_22 == 0)
{
if (x_20 == 0)
{
lean_dec_ref(x_21);
lean_dec(x_10);
lean_ctor_set(x_9, 0, x_19);
return x_9;
}
else
{
size_t x_23; size_t x_24; lean_object* x_25; 
lean_free_object(x_9);
x_23 = 0;
x_24 = lean_usize_of_nat(x_18);
x_25 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LibrarySuggestions_Selector_filterGrindAnnotated_spec__0___redArg(x_21, x_10, x_23, x_24, x_19);
lean_dec(x_10);
return x_25;
}
}
else
{
size_t x_26; size_t x_27; lean_object* x_28; 
lean_free_object(x_9);
x_26 = 0;
x_27 = lean_usize_of_nat(x_18);
x_28 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LibrarySuggestions_Selector_filterGrindAnnotated_spec__0___redArg(x_21, x_10, x_26, x_27, x_19);
lean_dec(x_10);
return x_28;
}
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
lean_dec(x_9);
x_29 = lean_st_ref_get(x_7);
lean_dec(x_7);
x_30 = lean_unsigned_to_nat(0u);
x_31 = lean_array_get_size(x_10);
x_32 = l_Lean_LibrarySuggestions_Selector_postFilter___closed__1;
x_33 = lean_nat_dec_lt(x_30, x_31);
if (x_33 == 0)
{
lean_object* x_34; 
lean_dec(x_29);
lean_dec(x_10);
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_32);
return x_34;
}
else
{
lean_object* x_35; uint8_t x_36; 
x_35 = lean_ctor_get(x_29, 0);
lean_inc_ref(x_35);
lean_dec(x_29);
x_36 = lean_nat_dec_le(x_31, x_31);
if (x_36 == 0)
{
if (x_33 == 0)
{
lean_object* x_37; 
lean_dec_ref(x_35);
lean_dec(x_10);
x_37 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_37, 0, x_32);
return x_37;
}
else
{
size_t x_38; size_t x_39; lean_object* x_40; 
x_38 = 0;
x_39 = lean_usize_of_nat(x_31);
x_40 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LibrarySuggestions_Selector_filterGrindAnnotated_spec__0___redArg(x_35, x_10, x_38, x_39, x_32);
lean_dec(x_10);
return x_40;
}
}
else
{
size_t x_41; size_t x_42; lean_object* x_43; 
x_41 = 0;
x_42 = lean_usize_of_nat(x_31);
x_43 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LibrarySuggestions_Selector_filterGrindAnnotated_spec__0___redArg(x_35, x_10, x_41, x_42, x_32);
lean_dec(x_10);
return x_43;
}
}
}
}
}
else
{
lean_dec(x_7);
lean_dec_ref(x_3);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_Selector_filterGrindAnnotated___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_LibrarySuggestions_Selector_filterGrindAnnotated(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LibrarySuggestions_Selector_filterGrindAnnotated_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LibrarySuggestions_Selector_filterGrindAnnotated_spec__0___redArg(x_1, x_2, x_3, x_4, x_5);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LibrarySuggestions_Selector_filterGrindAnnotated_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LibrarySuggestions_Selector_filterGrindAnnotated_spec__0(x_1, x_2, x_11, x_12, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
return x_13;
}
}
static double _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_LibrarySuggestions_Selector_intersperse_spec__0___redArg___closed__0() {
_start:
{
lean_object* x_1; double x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_float_of_nat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_LibrarySuggestions_Selector_intersperse_spec__0___redArg(double x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_25; uint8_t x_26; 
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_5, 0);
lean_inc(x_10);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_11 = x_5;
} else {
 lean_dec_ref(x_5);
 x_11 = lean_box(0);
}
x_12 = lean_ctor_get(x_7, 0);
lean_inc(x_12);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_13 = x_7;
} else {
 lean_dec_ref(x_7);
 x_13 = lean_box(0);
}
x_14 = lean_ctor_get(x_8, 0);
lean_inc(x_14);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 x_15 = x_8;
} else {
 lean_dec_ref(x_8);
 x_15 = lean_box(0);
}
x_16 = lean_ctor_get(x_9, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_9, 1);
lean_inc(x_17);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 lean_ctor_release(x_9, 1);
 x_18 = x_9;
} else {
 lean_dec_ref(x_9);
 x_18 = lean_box(0);
}
x_25 = lean_array_get_size(x_3);
x_26 = lean_nat_dec_lt(x_14, x_25);
if (x_26 == 0)
{
goto block_24;
}
else
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_array_get_size(x_2);
x_28 = lean_nat_dec_lt(x_16, x_27);
if (x_28 == 0)
{
goto block_24;
}
else
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_array_get_size(x_17);
x_30 = lean_nat_dec_lt(x_29, x_4);
if (x_30 == 0)
{
goto block_24;
}
else
{
lean_object* x_31; double x_32; double x_33; lean_object* x_58; double x_59; double x_60; double x_61; double x_62; uint8_t x_63; 
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_11);
x_31 = lean_unsigned_to_nat(1u);
x_32 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_LibrarySuggestions_Selector_intersperse_spec__0___redArg___closed__0;
x_58 = lean_unsigned_to_nat(0u);
x_59 = l_Float_ofScientific(x_58, x_30, x_31);
x_60 = lean_unbox_float(x_10);
x_61 = lean_unbox_float(x_12);
x_62 = lean_float_add(x_60, x_61);
x_63 = lean_float_decLe(x_62, x_59);
if (x_63 == 0)
{
double x_64; double x_65; 
x_64 = lean_unbox_float(x_10);
x_65 = lean_float_div(x_64, x_62);
x_33 = x_65;
goto block_57;
}
else
{
x_33 = x_59;
goto block_57;
}
block_57:
{
uint8_t x_34; 
x_34 = lean_float_decLt(x_33, x_1);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; double x_38; double x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_35 = lean_array_fget_borrowed(x_2, x_16);
lean_inc(x_35);
x_36 = lean_array_push(x_17, x_35);
x_37 = lean_nat_add(x_16, x_31);
lean_dec(x_16);
x_38 = lean_unbox_float(x_12);
lean_dec(x_12);
x_39 = lean_float_add(x_38, x_32);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_37);
lean_ctor_set(x_40, 1, x_36);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_14);
lean_ctor_set(x_41, 1, x_40);
x_42 = lean_box_float(x_39);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_41);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_10);
lean_ctor_set(x_44, 1, x_43);
x_5 = x_44;
goto _start;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; double x_49; double x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_46 = lean_array_fget_borrowed(x_3, x_14);
lean_inc(x_46);
x_47 = lean_array_push(x_17, x_46);
x_48 = lean_nat_add(x_14, x_31);
lean_dec(x_14);
x_49 = lean_unbox_float(x_10);
lean_dec(x_10);
x_50 = lean_float_add(x_49, x_32);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_16);
lean_ctor_set(x_51, 1, x_47);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_48);
lean_ctor_set(x_52, 1, x_51);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_12);
lean_ctor_set(x_53, 1, x_52);
x_54 = lean_box_float(x_50);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_53);
x_5 = x_55;
goto _start;
}
}
}
}
}
block_24:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
if (lean_is_scalar(x_18)) {
 x_19 = lean_alloc_ctor(0, 2, 0);
} else {
 x_19 = x_18;
}
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_17);
if (lean_is_scalar(x_15)) {
 x_20 = lean_alloc_ctor(0, 2, 0);
} else {
 x_20 = x_15;
}
lean_ctor_set(x_20, 0, x_14);
lean_ctor_set(x_20, 1, x_19);
if (lean_is_scalar(x_13)) {
 x_21 = lean_alloc_ctor(0, 2, 0);
} else {
 x_21 = x_13;
}
lean_ctor_set(x_21, 0, x_12);
lean_ctor_set(x_21, 1, x_20);
if (lean_is_scalar(x_11)) {
 x_22 = lean_alloc_ctor(0, 2, 0);
} else {
 x_22 = x_11;
}
lean_ctor_set(x_22, 0, x_10);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_22);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_LibrarySuggestions_Selector_intersperse_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
double x_7; lean_object* x_8; 
x_7 = lean_unbox_float(x_1);
lean_dec_ref(x_1);
x_8 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_LibrarySuggestions_Selector_intersperse_spec__0___redArg(x_7, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_LibrarySuggestions_Selector_intersperse_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_11; uint8_t x_12; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 x_7 = x_3;
} else {
 lean_dec_ref(x_3);
 x_7 = lean_box(0);
}
x_11 = lean_array_get_size(x_1);
x_12 = lean_nat_dec_lt(x_5, x_11);
if (x_12 == 0)
{
goto block_10;
}
else
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_array_get_size(x_6);
x_14 = lean_nat_dec_lt(x_13, x_2);
if (x_14 == 0)
{
goto block_10;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_7);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_array_fget_borrowed(x_1, x_5);
lean_inc(x_16);
x_17 = lean_array_push(x_6, x_16);
x_18 = lean_nat_add(x_5, x_15);
lean_dec(x_5);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
x_3 = x_19;
goto _start;
}
}
block_10:
{
lean_object* x_8; lean_object* x_9; 
if (lean_is_scalar(x_7)) {
 x_8 = lean_alloc_ctor(0, 2, 0);
} else {
 x_8 = x_7;
}
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_6);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_LibrarySuggestions_Selector_intersperse_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_LibrarySuggestions_Selector_intersperse_spec__1___redArg(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_5;
}
}
static double _init_l_Lean_LibrarySuggestions_Selector_intersperse___closed__0() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; double x_4; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = 1;
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Float_ofScientific(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_LibrarySuggestions_Selector_intersperse___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_LibrarySuggestions_Selector_postFilter___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_LibrarySuggestions_Selector_intersperse___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_LibrarySuggestions_Selector_intersperse___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_LibrarySuggestions_Selector_intersperse___closed__3___boxed__const__1() {
_start:
{
double x_1; lean_object* x_2; 
x_1 = l_Lean_LibrarySuggestions_Selector_intersperse___closed__0;
x_2 = lean_box_float(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_LibrarySuggestions_Selector_intersperse___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_LibrarySuggestions_Selector_intersperse___closed__2;
x_2 = l_Lean_LibrarySuggestions_Selector_intersperse___closed__3___boxed__const__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_LibrarySuggestions_Selector_intersperse___closed__4___boxed__const__1() {
_start:
{
double x_1; lean_object* x_2; 
x_1 = l_Lean_LibrarySuggestions_Selector_intersperse___closed__0;
x_2 = lean_box_float(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_LibrarySuggestions_Selector_intersperse___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_LibrarySuggestions_Selector_intersperse___closed__3;
x_2 = l_Lean_LibrarySuggestions_Selector_intersperse___closed__4___boxed__const__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_Selector_intersperse(lean_object* x_1, lean_object* x_2, double x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_5);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; double x_16; double x_17; uint32_t x_18; lean_object* x_19; lean_object* x_20; 
x_12 = lean_ctor_get(x_5, 0);
x_13 = lean_ctor_get(x_5, 1);
x_14 = lean_ctor_get(x_5, 2);
x_15 = lean_ctor_get(x_5, 3);
lean_inc(x_12);
x_16 = lean_float_of_nat(x_12);
x_17 = lean_float_mul(x_16, x_3);
x_18 = lean_float_to_uint32(x_17);
x_19 = lean_uint32_to_nat(x_18);
lean_inc(x_15);
lean_inc_ref(x_14);
lean_inc(x_13);
lean_ctor_set(x_5, 0, x_19);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_4);
x_20 = lean_apply_7(x_1, x_4, x_5, x_6, x_7, x_8, x_9, lean_box(0));
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; double x_22; double x_23; double x_24; uint32_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec_ref(x_20);
x_22 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_LibrarySuggestions_Selector_intersperse_spec__0___redArg___closed__0;
x_23 = lean_float_sub(x_22, x_3);
x_24 = lean_float_mul(x_16, x_23);
x_25 = lean_float_to_uint32(x_24);
x_26 = lean_uint32_to_nat(x_25);
x_27 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_13);
lean_ctor_set(x_27, 2, x_14);
lean_ctor_set(x_27, 3, x_15);
x_28 = lean_apply_7(x_2, x_4, x_27, x_6, x_7, x_8, x_9, lean_box(0));
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
lean_dec_ref(x_28);
x_30 = l_Lean_LibrarySuggestions_Selector_intersperse___closed__4;
x_31 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_LibrarySuggestions_Selector_intersperse_spec__0___redArg(x_3, x_29, x_21, x_12, x_30);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
lean_dec_ref(x_31);
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
lean_dec(x_32);
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
lean_dec(x_33);
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 0);
lean_inc(x_36);
lean_dec(x_34);
x_37 = !lean_is_exclusive(x_35);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_35, 0);
lean_ctor_set(x_35, 0, x_36);
x_39 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_LibrarySuggestions_Selector_intersperse_spec__1___redArg(x_21, x_12, x_35);
lean_dec(x_21);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; uint8_t x_41; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
lean_dec_ref(x_39);
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_40, 0);
lean_dec(x_42);
lean_ctor_set(x_40, 0, x_38);
x_43 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_LibrarySuggestions_Selector_intersperse_spec__1___redArg(x_29, x_12, x_40);
lean_dec(x_12);
lean_dec(x_29);
if (lean_obj_tag(x_43) == 0)
{
uint8_t x_44; 
x_44 = !lean_is_exclusive(x_43);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_43, 0);
x_46 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
lean_dec(x_45);
lean_ctor_set(x_43, 0, x_46);
return x_43;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_43, 0);
lean_inc(x_47);
lean_dec(x_43);
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
lean_dec(x_47);
x_49 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_49, 0, x_48);
return x_49;
}
}
else
{
uint8_t x_50; 
x_50 = !lean_is_exclusive(x_43);
if (x_50 == 0)
{
return x_43;
}
else
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_43, 0);
lean_inc(x_51);
lean_dec(x_43);
x_52 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_52, 0, x_51);
return x_52;
}
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_40, 1);
lean_inc(x_53);
lean_dec(x_40);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_38);
lean_ctor_set(x_54, 1, x_53);
x_55 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_LibrarySuggestions_Selector_intersperse_spec__1___redArg(x_29, x_12, x_54);
lean_dec(x_12);
lean_dec(x_29);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 x_57 = x_55;
} else {
 lean_dec_ref(x_55);
 x_57 = lean_box(0);
}
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
if (lean_is_scalar(x_57)) {
 x_59 = lean_alloc_ctor(0, 1, 0);
} else {
 x_59 = x_57;
}
lean_ctor_set(x_59, 0, x_58);
return x_59;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_55, 0);
lean_inc(x_60);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 x_61 = x_55;
} else {
 lean_dec_ref(x_55);
 x_61 = lean_box(0);
}
if (lean_is_scalar(x_61)) {
 x_62 = lean_alloc_ctor(1, 1, 0);
} else {
 x_62 = x_61;
}
lean_ctor_set(x_62, 0, x_60);
return x_62;
}
}
}
else
{
uint8_t x_63; 
lean_dec(x_38);
lean_dec(x_29);
lean_dec(x_12);
x_63 = !lean_is_exclusive(x_39);
if (x_63 == 0)
{
return x_39;
}
else
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_ctor_get(x_39, 0);
lean_inc(x_64);
lean_dec(x_39);
x_65 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_65, 0, x_64);
return x_65;
}
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_66 = lean_ctor_get(x_35, 0);
x_67 = lean_ctor_get(x_35, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_35);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_36);
lean_ctor_set(x_68, 1, x_67);
x_69 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_LibrarySuggestions_Selector_intersperse_spec__1___redArg(x_21, x_12, x_68);
lean_dec(x_21);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
lean_dec_ref(x_69);
x_71 = lean_ctor_get(x_70, 1);
lean_inc(x_71);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 lean_ctor_release(x_70, 1);
 x_72 = x_70;
} else {
 lean_dec_ref(x_70);
 x_72 = lean_box(0);
}
if (lean_is_scalar(x_72)) {
 x_73 = lean_alloc_ctor(0, 2, 0);
} else {
 x_73 = x_72;
}
lean_ctor_set(x_73, 0, x_66);
lean_ctor_set(x_73, 1, x_71);
x_74 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_LibrarySuggestions_Selector_intersperse_spec__1___redArg(x_29, x_12, x_73);
lean_dec(x_12);
lean_dec(x_29);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 x_76 = x_74;
} else {
 lean_dec_ref(x_74);
 x_76 = lean_box(0);
}
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
lean_dec(x_75);
if (lean_is_scalar(x_76)) {
 x_78 = lean_alloc_ctor(0, 1, 0);
} else {
 x_78 = x_76;
}
lean_ctor_set(x_78, 0, x_77);
return x_78;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_74, 0);
lean_inc(x_79);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 x_80 = x_74;
} else {
 lean_dec_ref(x_74);
 x_80 = lean_box(0);
}
if (lean_is_scalar(x_80)) {
 x_81 = lean_alloc_ctor(1, 1, 0);
} else {
 x_81 = x_80;
}
lean_ctor_set(x_81, 0, x_79);
return x_81;
}
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
lean_dec(x_66);
lean_dec(x_29);
lean_dec(x_12);
x_82 = lean_ctor_get(x_69, 0);
lean_inc(x_82);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 x_83 = x_69;
} else {
 lean_dec_ref(x_69);
 x_83 = lean_box(0);
}
if (lean_is_scalar(x_83)) {
 x_84 = lean_alloc_ctor(1, 1, 0);
} else {
 x_84 = x_83;
}
lean_ctor_set(x_84, 0, x_82);
return x_84;
}
}
}
else
{
uint8_t x_85; 
lean_dec(x_29);
lean_dec(x_21);
lean_dec(x_12);
x_85 = !lean_is_exclusive(x_31);
if (x_85 == 0)
{
return x_31;
}
else
{
lean_object* x_86; lean_object* x_87; 
x_86 = lean_ctor_get(x_31, 0);
lean_inc(x_86);
lean_dec(x_31);
x_87 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_87, 0, x_86);
return x_87;
}
}
}
else
{
lean_dec(x_21);
lean_dec(x_12);
return x_28;
}
}
else
{
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_4);
lean_dec_ref(x_2);
return x_20;
}
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; double x_92; double x_93; uint32_t x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_88 = lean_ctor_get(x_5, 0);
x_89 = lean_ctor_get(x_5, 1);
x_90 = lean_ctor_get(x_5, 2);
x_91 = lean_ctor_get(x_5, 3);
lean_inc(x_91);
lean_inc(x_90);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_5);
lean_inc(x_88);
x_92 = lean_float_of_nat(x_88);
x_93 = lean_float_mul(x_92, x_3);
x_94 = lean_float_to_uint32(x_93);
x_95 = lean_uint32_to_nat(x_94);
lean_inc(x_91);
lean_inc_ref(x_90);
lean_inc(x_89);
x_96 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_89);
lean_ctor_set(x_96, 2, x_90);
lean_ctor_set(x_96, 3, x_91);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_4);
x_97 = lean_apply_7(x_1, x_4, x_96, x_6, x_7, x_8, x_9, lean_box(0));
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_98; double x_99; double x_100; double x_101; uint32_t x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
lean_dec_ref(x_97);
x_99 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_LibrarySuggestions_Selector_intersperse_spec__0___redArg___closed__0;
x_100 = lean_float_sub(x_99, x_3);
x_101 = lean_float_mul(x_92, x_100);
x_102 = lean_float_to_uint32(x_101);
x_103 = lean_uint32_to_nat(x_102);
x_104 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_104, 1, x_89);
lean_ctor_set(x_104, 2, x_90);
lean_ctor_set(x_104, 3, x_91);
x_105 = lean_apply_7(x_2, x_4, x_104, x_6, x_7, x_8, x_9, lean_box(0));
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
lean_dec_ref(x_105);
x_107 = l_Lean_LibrarySuggestions_Selector_intersperse___closed__4;
x_108 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_LibrarySuggestions_Selector_intersperse_spec__0___redArg(x_3, x_106, x_98, x_88, x_107);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
lean_dec_ref(x_108);
x_110 = lean_ctor_get(x_109, 1);
lean_inc(x_110);
lean_dec(x_109);
x_111 = lean_ctor_get(x_110, 1);
lean_inc(x_111);
lean_dec(x_110);
x_112 = lean_ctor_get(x_111, 1);
lean_inc(x_112);
x_113 = lean_ctor_get(x_111, 0);
lean_inc(x_113);
lean_dec(x_111);
x_114 = lean_ctor_get(x_112, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_112, 1);
lean_inc(x_115);
if (lean_is_exclusive(x_112)) {
 lean_ctor_release(x_112, 0);
 lean_ctor_release(x_112, 1);
 x_116 = x_112;
} else {
 lean_dec_ref(x_112);
 x_116 = lean_box(0);
}
if (lean_is_scalar(x_116)) {
 x_117 = lean_alloc_ctor(0, 2, 0);
} else {
 x_117 = x_116;
}
lean_ctor_set(x_117, 0, x_113);
lean_ctor_set(x_117, 1, x_115);
x_118 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_LibrarySuggestions_Selector_intersperse_spec__1___redArg(x_98, x_88, x_117);
lean_dec(x_98);
if (lean_obj_tag(x_118) == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
lean_dec_ref(x_118);
x_120 = lean_ctor_get(x_119, 1);
lean_inc(x_120);
if (lean_is_exclusive(x_119)) {
 lean_ctor_release(x_119, 0);
 lean_ctor_release(x_119, 1);
 x_121 = x_119;
} else {
 lean_dec_ref(x_119);
 x_121 = lean_box(0);
}
if (lean_is_scalar(x_121)) {
 x_122 = lean_alloc_ctor(0, 2, 0);
} else {
 x_122 = x_121;
}
lean_ctor_set(x_122, 0, x_114);
lean_ctor_set(x_122, 1, x_120);
x_123 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_LibrarySuggestions_Selector_intersperse_spec__1___redArg(x_106, x_88, x_122);
lean_dec(x_88);
lean_dec(x_106);
if (lean_obj_tag(x_123) == 0)
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
if (lean_is_exclusive(x_123)) {
 lean_ctor_release(x_123, 0);
 x_125 = x_123;
} else {
 lean_dec_ref(x_123);
 x_125 = lean_box(0);
}
x_126 = lean_ctor_get(x_124, 1);
lean_inc(x_126);
lean_dec(x_124);
if (lean_is_scalar(x_125)) {
 x_127 = lean_alloc_ctor(0, 1, 0);
} else {
 x_127 = x_125;
}
lean_ctor_set(x_127, 0, x_126);
return x_127;
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_128 = lean_ctor_get(x_123, 0);
lean_inc(x_128);
if (lean_is_exclusive(x_123)) {
 lean_ctor_release(x_123, 0);
 x_129 = x_123;
} else {
 lean_dec_ref(x_123);
 x_129 = lean_box(0);
}
if (lean_is_scalar(x_129)) {
 x_130 = lean_alloc_ctor(1, 1, 0);
} else {
 x_130 = x_129;
}
lean_ctor_set(x_130, 0, x_128);
return x_130;
}
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; 
lean_dec(x_114);
lean_dec(x_106);
lean_dec(x_88);
x_131 = lean_ctor_get(x_118, 0);
lean_inc(x_131);
if (lean_is_exclusive(x_118)) {
 lean_ctor_release(x_118, 0);
 x_132 = x_118;
} else {
 lean_dec_ref(x_118);
 x_132 = lean_box(0);
}
if (lean_is_scalar(x_132)) {
 x_133 = lean_alloc_ctor(1, 1, 0);
} else {
 x_133 = x_132;
}
lean_ctor_set(x_133, 0, x_131);
return x_133;
}
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; 
lean_dec(x_106);
lean_dec(x_98);
lean_dec(x_88);
x_134 = lean_ctor_get(x_108, 0);
lean_inc(x_134);
if (lean_is_exclusive(x_108)) {
 lean_ctor_release(x_108, 0);
 x_135 = x_108;
} else {
 lean_dec_ref(x_108);
 x_135 = lean_box(0);
}
if (lean_is_scalar(x_135)) {
 x_136 = lean_alloc_ctor(1, 1, 0);
} else {
 x_136 = x_135;
}
lean_ctor_set(x_136, 0, x_134);
return x_136;
}
}
else
{
lean_dec(x_98);
lean_dec(x_88);
return x_105;
}
}
else
{
lean_dec(x_91);
lean_dec_ref(x_90);
lean_dec(x_89);
lean_dec(x_88);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_4);
lean_dec_ref(x_2);
return x_97;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_Selector_intersperse___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
double x_11; lean_object* x_12; 
x_11 = lean_unbox_float(x_3);
lean_dec_ref(x_3);
x_12 = l_Lean_LibrarySuggestions_Selector_intersperse(x_1, x_2, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_LibrarySuggestions_Selector_intersperse_spec__0(double x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_LibrarySuggestions_Selector_intersperse_spec__0___redArg(x_1, x_2, x_3, x_4, x_5);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_LibrarySuggestions_Selector_intersperse_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
double x_11; lean_object* x_12; 
x_11 = lean_unbox_float(x_1);
lean_dec_ref(x_1);
x_12 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_LibrarySuggestions_Selector_intersperse_spec__0(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_LibrarySuggestions_Selector_intersperse_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_LibrarySuggestions_Selector_intersperse_spec__1___redArg(x_1, x_2, x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_LibrarySuggestions_Selector_intersperse_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_LibrarySuggestions_Selector_intersperse_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_initFn___lam__0_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2_(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_initFn___lam__1_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2_(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_array_mk(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__spec__0_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_4);
x_8 = 1;
x_9 = lean_usize_add(x_2, x_8);
x_2 = x_9;
x_4 = x_7;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__spec__0_spec__0(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__spec__0_spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_10; 
x_10 = lean_usize_dec_eq(x_2, x_3);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_array_uget(x_1, x_2);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_array_get_size(x_11);
x_14 = lean_nat_dec_lt(x_12, x_13);
if (x_14 == 0)
{
lean_dec(x_11);
x_5 = x_4;
goto block_9;
}
else
{
uint8_t x_15; 
x_15 = lean_nat_dec_le(x_13, x_13);
if (x_15 == 0)
{
if (x_14 == 0)
{
lean_dec(x_11);
x_5 = x_4;
goto block_9;
}
else
{
size_t x_16; size_t x_17; lean_object* x_18; 
x_16 = 0;
x_17 = lean_usize_of_nat(x_13);
x_18 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__spec__0_spec__0(x_11, x_16, x_17, x_4);
lean_dec(x_11);
x_5 = x_18;
goto block_9;
}
}
else
{
size_t x_19; size_t x_20; lean_object* x_21; 
x_19 = 0;
x_20 = lean_usize_of_nat(x_13);
x_21 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__spec__0_spec__0(x_11, x_19, x_20, x_4);
lean_dec(x_11);
x_5 = x_21;
goto block_9;
}
}
}
else
{
return x_4;
}
block_9:
{
size_t x_6; size_t x_7; 
x_6 = 1;
x_7 = lean_usize_add(x_2, x_6);
x_2 = x_7;
x_4 = x_5;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__spec__0_spec__1(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_3, x_4);
if (x_5 == 0)
{
return x_1;
}
else
{
uint8_t x_6; 
x_6 = lean_nat_dec_le(x_4, x_4);
if (x_6 == 0)
{
if (x_5 == 0)
{
return x_1;
}
else
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = 0;
x_8 = lean_usize_of_nat(x_4);
x_9 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__spec__0_spec__1(x_2, x_7, x_8, x_1);
return x_9;
}
}
else
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = 0;
x_11 = lean_usize_of_nat(x_4);
x_12 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__spec__0_spec__1(x_2, x_10, x_11, x_1);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_mkStateFromImportedEntries___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2__spec__0(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2_() {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = ((lean_object*)(l_Lean_LibrarySuggestions_initFn___closed__14_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2_));
x_3 = l_Lean_registerSimplePersistentEnvExtension___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2_();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_611429871____hygCtx___hyg_2_() {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = ((lean_object*)(l_Lean_LibrarySuggestions_initFn___closed__2_00___x40_Lean_LibrarySuggestions_Basic_611429871____hygCtx___hyg_2_));
x_3 = l_Lean_registerSimplePersistentEnvExtension___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_611429871____hygCtx___hyg_2____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_611429871____hygCtx___hyg_2_();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_initFn___lam__0_00___x40_Lean_LibrarySuggestions_Basic_3406067637____hygCtx___hyg_2_(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_initFn___lam__1_00___x40_Lean_LibrarySuggestions_Basic_3406067637____hygCtx___hyg_2_(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_array_mk(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3406067637____hygCtx___hyg_2__spec__0_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_4);
x_8 = 1;
x_9 = lean_usize_add(x_2, x_8);
x_2 = x_9;
x_4 = x_7;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3406067637____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3406067637____hygCtx___hyg_2__spec__0_spec__0(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3406067637____hygCtx___hyg_2__spec__0_spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_10; 
x_10 = lean_usize_dec_eq(x_2, x_3);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_array_uget(x_1, x_2);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_array_get_size(x_11);
x_14 = lean_nat_dec_lt(x_12, x_13);
if (x_14 == 0)
{
lean_dec(x_11);
x_5 = x_4;
goto block_9;
}
else
{
uint8_t x_15; 
x_15 = lean_nat_dec_le(x_13, x_13);
if (x_15 == 0)
{
if (x_14 == 0)
{
lean_dec(x_11);
x_5 = x_4;
goto block_9;
}
else
{
size_t x_16; size_t x_17; lean_object* x_18; 
x_16 = 0;
x_17 = lean_usize_of_nat(x_13);
x_18 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3406067637____hygCtx___hyg_2__spec__0_spec__0(x_11, x_16, x_17, x_4);
lean_dec(x_11);
x_5 = x_18;
goto block_9;
}
}
else
{
size_t x_19; size_t x_20; lean_object* x_21; 
x_19 = 0;
x_20 = lean_usize_of_nat(x_13);
x_21 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3406067637____hygCtx___hyg_2__spec__0_spec__0(x_11, x_19, x_20, x_4);
lean_dec(x_11);
x_5 = x_21;
goto block_9;
}
}
}
else
{
return x_4;
}
block_9:
{
size_t x_6; size_t x_7; 
x_6 = 1;
x_7 = lean_usize_add(x_2, x_6);
x_2 = x_7;
x_4 = x_5;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3406067637____hygCtx___hyg_2__spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3406067637____hygCtx___hyg_2__spec__0_spec__1(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3406067637____hygCtx___hyg_2__spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_3, x_4);
if (x_5 == 0)
{
return x_1;
}
else
{
uint8_t x_6; 
x_6 = lean_nat_dec_le(x_4, x_4);
if (x_6 == 0)
{
if (x_5 == 0)
{
return x_1;
}
else
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = 0;
x_8 = lean_usize_of_nat(x_4);
x_9 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3406067637____hygCtx___hyg_2__spec__0_spec__1(x_2, x_7, x_8, x_1);
return x_9;
}
}
else
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = 0;
x_11 = lean_usize_of_nat(x_4);
x_12 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3406067637____hygCtx___hyg_2__spec__0_spec__1(x_2, x_10, x_11, x_1);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3406067637____hygCtx___hyg_2__spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_mkStateFromImportedEntries___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3406067637____hygCtx___hyg_2__spec__0(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3406067637____hygCtx___hyg_2_() {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = ((lean_object*)(l_Lean_LibrarySuggestions_initFn___closed__9_00___x40_Lean_LibrarySuggestions_Basic_3406067637____hygCtx___hyg_2_));
x_3 = l_Lean_registerSimplePersistentEnvExtension___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3406067637____hygCtx___hyg_2____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3406067637____hygCtx___hyg_2_();
return x_2;
}
}
LEAN_EXPORT uint8_t l_Lean_LibrarySuggestions_isDeniedModule___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_string_dec_eq(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_isDeniedModule___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_LibrarySuggestions_isDeniedModule___lam__0(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_LibrarySuggestions_isDeniedModule___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_alloc_closure((void*)(l_Lean_LibrarySuggestions_isDeniedModule___lam__0___boxed), 2, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = l_Lean_Name_anyS(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_isDeniedModule___lam__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_LibrarySuggestions_isDeniedModule___lam__1(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_LibrarySuggestions_isDeniedModule(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_3 = l_Lean_LibrarySuggestions_moduleDenyListExt;
x_4 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_4);
x_5 = lean_ctor_get(x_4, 2);
lean_inc(x_5);
lean_dec_ref(x_4);
x_6 = lean_alloc_closure((void*)(l_Lean_LibrarySuggestions_isDeniedModule___lam__1___boxed), 2, 1);
lean_closure_set(x_6, 0, x_2);
x_7 = lean_box(0);
x_8 = lean_box(0);
x_9 = l_Lean_SimplePersistentEnvExtension_getState___redArg(x_7, x_3, x_1, x_5, x_8);
lean_dec(x_5);
x_10 = l_List_any___redArg(x_9, x_6);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_isDeniedModule___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_LibrarySuggestions_isDeniedModule(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_LibrarySuggestions_isDeniedPremise___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_alloc_closure((void*)(l_Lean_LibrarySuggestions_isDeniedModule___lam__0___boxed), 2, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = l_Lean_Name_anyS(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_isDeniedPremise___lam__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_LibrarySuggestions_isDeniedPremise___lam__1(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_LibrarySuggestions_isDeniedPremise___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Lean_Name_isPrefixOf(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_isDeniedPremise___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_LibrarySuggestions_isDeniedPremise___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_LibrarySuggestions_isDeniedPremise(lean_object* x_1, lean_object* x_2, uint8_t x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = ((lean_object*)(l_Lean_LibrarySuggestions_isDeniedPremise___closed__1));
x_5 = lean_name_eq(x_2, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_24; uint8_t x_25; uint8_t x_40; 
lean_inc(x_2);
x_6 = lean_alloc_closure((void*)(l_Lean_LibrarySuggestions_isDeniedPremise___lam__1___boxed), 2, 1);
lean_closure_set(x_6, 0, x_2);
x_7 = lean_box(0);
x_24 = lean_box(0);
lean_inc(x_2);
x_40 = l_Lean_Name_isInternalDetail(x_2);
if (x_40 == 0)
{
x_25 = x_40;
goto block_39;
}
else
{
if (x_3 == 0)
{
x_25 = x_40;
goto block_39;
}
else
{
uint8_t x_41; 
x_41 = l_Lean_isPrivateName(x_2);
if (x_41 == 0)
{
x_25 = x_40;
goto block_39;
}
else
{
x_25 = x_5;
goto block_39;
}
}
}
block_23:
{
lean_object* x_10; 
lean_inc_ref(x_1);
x_10 = l_Lean_Environment_find_x3f(x_1, x_2, x_9);
if (lean_obj_tag(x_10) == 1)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec_ref(x_10);
x_12 = l_Lean_ConstantInfo_type(x_11);
lean_dec(x_11);
x_13 = l_Lean_Expr_getForallBody(x_12);
lean_dec_ref(x_12);
x_14 = l_Lean_Expr_getAppFn(x_13);
lean_dec_ref(x_13);
if (lean_obj_tag(x_14) == 4)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec_ref(x_14);
x_16 = l_Lean_LibrarySuggestions_typePrefixDenyListExt;
x_17 = lean_ctor_get(x_16, 0);
lean_inc_ref(x_17);
x_18 = lean_ctor_get(x_17, 2);
lean_inc(x_18);
lean_dec_ref(x_17);
x_19 = lean_alloc_closure((void*)(l_Lean_LibrarySuggestions_isDeniedPremise___lam__0___boxed), 2, 1);
lean_closure_set(x_19, 0, x_15);
x_20 = l_Lean_SimplePersistentEnvExtension_getState___redArg(x_7, x_16, x_1, x_18, x_8);
lean_dec(x_18);
x_21 = l_List_any___redArg(x_20, x_19);
return x_21;
}
else
{
lean_dec_ref(x_14);
lean_dec(x_8);
lean_dec_ref(x_1);
return x_9;
}
}
else
{
uint8_t x_22; 
lean_dec(x_10);
lean_dec(x_8);
lean_dec_ref(x_1);
x_22 = 1;
return x_22;
}
}
block_39:
{
if (x_25 == 0)
{
uint8_t x_26; 
lean_inc(x_2);
lean_inc_ref(x_1);
x_26 = l_Lean_isInstanceReducibleCore(x_1, x_2);
if (x_26 == 0)
{
uint8_t x_27; 
lean_inc(x_2);
lean_inc_ref(x_1);
x_27 = l_Lean_Linter_isDeprecated(x_1, x_2);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_28 = l_Lean_LibrarySuggestions_nameDenyListExt;
x_29 = lean_ctor_get(x_28, 0);
lean_inc_ref(x_29);
x_30 = lean_ctor_get(x_29, 2);
lean_inc(x_30);
lean_dec_ref(x_29);
lean_inc_ref(x_1);
x_31 = l_Lean_SimplePersistentEnvExtension_getState___redArg(x_7, x_28, x_1, x_30, x_24);
lean_dec(x_30);
x_32 = l_List_any___redArg(x_31, x_6);
if (x_32 == 0)
{
lean_object* x_33; 
x_33 = l_Lean_Environment_getModuleIdxFor_x3f(x_1, x_2);
if (lean_obj_tag(x_33) == 1)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
lean_dec_ref(x_33);
x_35 = l_Lean_Environment_header(x_1);
x_36 = l_Lean_EnvironmentHeader_moduleNames(x_35);
x_37 = lean_array_get(x_24, x_36, x_34);
lean_dec(x_34);
lean_dec_ref(x_36);
lean_inc_ref(x_1);
x_38 = l_Lean_LibrarySuggestions_isDeniedModule(x_1, x_37);
if (x_38 == 0)
{
x_8 = x_24;
x_9 = x_32;
goto block_23;
}
else
{
lean_dec(x_2);
lean_dec_ref(x_1);
return x_38;
}
}
else
{
lean_dec(x_33);
x_8 = x_24;
x_9 = x_32;
goto block_23;
}
}
else
{
lean_dec(x_2);
lean_dec_ref(x_1);
return x_32;
}
}
else
{
lean_dec_ref(x_6);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_27;
}
}
else
{
lean_dec_ref(x_6);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_26;
}
}
else
{
lean_dec_ref(x_6);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_25;
}
}
}
else
{
lean_dec(x_2);
lean_dec_ref(x_1);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_isDeniedPremise___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox(x_3);
x_5 = l_Lean_LibrarySuggestions_isDeniedPremise(x_1, x_2, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_empty___redArg() {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_LibrarySuggestions_Selector_postFilter___closed__1;
x_3 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_empty___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_LibrarySuggestions_empty___redArg();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_empty(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_LibrarySuggestions_empty___redArg();
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_empty___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_LibrarySuggestions_empty(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_LibrarySuggestions_random_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_4);
x_7 = lean_nat_dec_lt(x_6, x_1);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec_ref(x_3);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_4);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_15; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_array_get_size(x_2);
x_11 = l_IO_rand(x_9, x_10);
x_12 = lean_box(0);
x_13 = lean_array_get_borrowed(x_12, x_2, x_11);
lean_dec(x_11);
x_14 = 0;
lean_inc(x_13);
lean_inc_ref(x_3);
x_15 = l_Lean_LibrarySuggestions_isDeniedPremise(x_3, x_13, x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; double x_18; double x_19; double x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_16 = lean_unsigned_to_nat(10u);
x_17 = lean_unsigned_to_nat(1u);
x_18 = l_Float_ofScientific(x_16, x_7, x_17);
x_19 = lean_float_of_nat(x_10);
x_20 = lean_float_div(x_18, x_19);
x_21 = lean_box(0);
lean_inc(x_13);
x_22 = lean_alloc_ctor(0, 2, 8);
lean_ctor_set(x_22, 0, x_13);
lean_ctor_set(x_22, 1, x_21);
lean_ctor_set_float(x_22, sizeof(void*)*2, x_20);
x_23 = lean_array_push(x_4, x_22);
x_4 = x_23;
goto _start;
}
else
{
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_LibrarySuggestions_random_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_LibrarySuggestions_random_spec__0___redArg(x_1, x_2, x_3, x_4);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_LibrarySuggestions_random_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 2);
lean_inc(x_4);
lean_dec_ref(x_2);
x_5 = lean_array_push(x_1, x_3);
x_1 = x_5;
x_2 = x_4;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LibrarySuggestions_random_spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_LibrarySuggestions_random_spec__1(x_4, x_6);
x_8 = 1;
x_9 = lean_usize_add(x_2, x_8);
x_2 = x_9;
x_4 = x_7;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LibrarySuggestions_random_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LibrarySuggestions_random_spec__2(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_random___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_8 = l_IO_stdGenRef;
x_9 = lean_st_ref_set(x_8, x_1);
x_10 = lean_st_ref_get(x_6);
x_11 = lean_ctor_get(x_10, 0);
lean_inc_ref(x_11);
lean_dec(x_10);
x_12 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_11);
x_17 = l_Lean_Environment_const2ModIdx(x_11);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc_ref(x_19);
lean_dec_ref(x_17);
x_20 = lean_mk_empty_array_with_capacity(x_18);
lean_dec(x_18);
x_21 = lean_unsigned_to_nat(0u);
x_22 = lean_array_get_size(x_19);
x_23 = lean_nat_dec_lt(x_21, x_22);
if (x_23 == 0)
{
lean_dec_ref(x_19);
x_13 = x_20;
goto block_16;
}
else
{
uint8_t x_24; 
x_24 = lean_nat_dec_le(x_22, x_22);
if (x_24 == 0)
{
if (x_23 == 0)
{
lean_dec_ref(x_19);
x_13 = x_20;
goto block_16;
}
else
{
size_t x_25; size_t x_26; lean_object* x_27; 
x_25 = 0;
x_26 = lean_usize_of_nat(x_22);
x_27 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LibrarySuggestions_random_spec__2(x_19, x_25, x_26, x_20);
lean_dec_ref(x_19);
x_13 = x_27;
goto block_16;
}
}
else
{
size_t x_28; size_t x_29; lean_object* x_30; 
x_28 = 0;
x_29 = lean_usize_of_nat(x_22);
x_30 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LibrarySuggestions_random_spec__2(x_19, x_28, x_29, x_20);
lean_dec_ref(x_19);
x_13 = x_30;
goto block_16;
}
}
block_16:
{
lean_object* x_14; lean_object* x_15; 
x_14 = l_Lean_LibrarySuggestions_Selector_postFilter___closed__1;
x_15 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_LibrarySuggestions_random_spec__0___redArg(x_12, x_13, x_11, x_14);
lean_dec_ref(x_13);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_random___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_LibrarySuggestions_random___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_random(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_LibrarySuggestions_random___redArg(x_1, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_random___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_LibrarySuggestions_random(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_LibrarySuggestions_random_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_LibrarySuggestions_random_spec__0___redArg(x_1, x_2, x_3, x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_LibrarySuggestions_random_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_LibrarySuggestions_random_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_currentFile___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_3, 0);
lean_inc(x_10);
lean_dec_ref(x_3);
x_11 = lean_array_get_size(x_4);
x_12 = lean_nat_dec_le(x_1, x_11);
if (x_12 == 0)
{
uint8_t x_13; uint8_t x_14; 
x_13 = 1;
lean_inc(x_10);
lean_inc_ref(x_2);
x_14 = l_Lean_LibrarySuggestions_isDeniedPremise(x_2, x_10, x_13);
if (x_14 == 0)
{
uint8_t x_15; 
lean_inc(x_10);
x_15 = l_Lean_wasOriginallyTheorem(x_2, x_10);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_10);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_4);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; double x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_18 = lean_unsigned_to_nat(10u);
x_19 = lean_unsigned_to_nat(1u);
x_20 = l_Float_ofScientific(x_18, x_15, x_19);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 2, 8);
lean_ctor_set(x_22, 0, x_10);
lean_ctor_set(x_22, 1, x_21);
lean_ctor_set_float(x_22, sizeof(void*)*2, x_20);
x_23 = lean_array_push(x_4, x_22);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_24);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_10);
lean_dec_ref(x_2);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_4);
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_26);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_10);
lean_dec_ref(x_2);
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_4);
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_28);
return x_29;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_currentFile___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_LibrarySuggestions_currentFile___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_LibrarySuggestions_currentFile_spec__0___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_3);
lean_ctor_set(x_10, 1, x_4);
x_11 = lean_apply_7(x_1, x_10, x_2, x_5, x_6, x_7, x_8, lean_box(0));
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_11, 0);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
return x_11;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_11, 0, x_16);
return x_11;
}
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_13);
if (x_17 == 0)
{
return x_11;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_13, 0);
lean_inc(x_18);
lean_dec(x_13);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_11, 0, x_19);
return x_11;
}
}
}
else
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_11, 0);
lean_inc(x_20);
lean_dec(x_11);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 x_22 = x_20;
} else {
 lean_dec_ref(x_20);
 x_22 = lean_box(0);
}
if (lean_is_scalar(x_22)) {
 x_23 = lean_alloc_ctor(0, 1, 0);
} else {
 x_23 = x_22;
}
lean_ctor_set(x_23, 0, x_21);
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_23);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_20, 0);
lean_inc(x_25);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 x_26 = x_20;
} else {
 lean_dec_ref(x_20);
 x_26 = lean_box(0);
}
if (lean_is_scalar(x_26)) {
 x_27 = lean_alloc_ctor(1, 1, 0);
} else {
 x_27 = x_26;
}
lean_ctor_set(x_27, 0, x_25);
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_27);
return x_28;
}
}
}
else
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_11);
if (x_29 == 0)
{
return x_11;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_11, 0);
lean_inc(x_30);
lean_dec(x_11);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_30);
return x_31;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_LibrarySuggestions_currentFile_spec__0___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_PersistentHashMap_forIn___at___00Lean_LibrarySuggestions_currentFile_spec__0___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_LibrarySuggestions_currentFile_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_array_get_size(x_2);
x_12 = lean_nat_dec_lt(x_4, x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_4);
lean_dec_ref(x_1);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_5);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_array_fget_borrowed(x_2, x_4);
x_16 = lean_array_fget_borrowed(x_3, x_4);
lean_inc_ref(x_1);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_16);
lean_inc(x_15);
x_17 = lean_apply_8(x_1, x_5, x_15, x_16, x_6, x_7, x_8, x_9, lean_box(0));
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 0)
{
lean_dec_ref(x_18);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_4);
lean_dec_ref(x_1);
return x_17;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec_ref(x_17);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec_ref(x_18);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_add(x_4, x_20);
lean_dec(x_4);
x_4 = x_21;
x_5 = x_19;
goto _start;
}
}
else
{
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_4);
lean_dec_ref(x_1);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_LibrarySuggestions_currentFile_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_LibrarySuggestions_currentFile_spec__0_spec__0_spec__1_spec__3___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_LibrarySuggestions_currentFile_spec__0_spec__0_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_2);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_array_get_size(x_10);
x_13 = lean_nat_dec_lt(x_11, x_12);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec_ref(x_10);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
lean_ctor_set_tag(x_2, 1);
lean_ctor_set(x_2, 0, x_3);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_2);
return x_14;
}
else
{
uint8_t x_15; 
x_15 = lean_nat_dec_le(x_12, x_12);
if (x_15 == 0)
{
if (x_13 == 0)
{
lean_object* x_16; 
lean_dec_ref(x_10);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
lean_ctor_set_tag(x_2, 1);
lean_ctor_set(x_2, 0, x_3);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_2);
return x_16;
}
else
{
size_t x_17; size_t x_18; lean_object* x_19; 
lean_free_object(x_2);
x_17 = 0;
x_18 = lean_usize_of_nat(x_12);
x_19 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_LibrarySuggestions_currentFile_spec__0_spec__0_spec__1_spec__2___redArg(x_1, x_10, x_17, x_18, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_10);
return x_19;
}
}
else
{
size_t x_20; size_t x_21; lean_object* x_22; 
lean_free_object(x_2);
x_20 = 0;
x_21 = lean_usize_of_nat(x_12);
x_22 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_LibrarySuggestions_currentFile_spec__0_spec__0_spec__1_spec__2___redArg(x_1, x_10, x_20, x_21, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_10);
return x_22;
}
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_23 = lean_ctor_get(x_2, 0);
lean_inc(x_23);
lean_dec(x_2);
x_24 = lean_unsigned_to_nat(0u);
x_25 = lean_array_get_size(x_23);
x_26 = lean_nat_dec_lt(x_24, x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
lean_dec_ref(x_23);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_3);
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_27);
return x_28;
}
else
{
uint8_t x_29; 
x_29 = lean_nat_dec_le(x_25, x_25);
if (x_29 == 0)
{
if (x_26 == 0)
{
lean_object* x_30; lean_object* x_31; 
lean_dec_ref(x_23);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_3);
x_31 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_31, 0, x_30);
return x_31;
}
else
{
size_t x_32; size_t x_33; lean_object* x_34; 
x_32 = 0;
x_33 = lean_usize_of_nat(x_25);
x_34 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_LibrarySuggestions_currentFile_spec__0_spec__0_spec__1_spec__2___redArg(x_1, x_23, x_32, x_33, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_23);
return x_34;
}
}
else
{
size_t x_35; size_t x_36; lean_object* x_37; 
x_35 = 0;
x_36 = lean_usize_of_nat(x_25);
x_37 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_LibrarySuggestions_currentFile_spec__0_spec__0_spec__1_spec__2___redArg(x_1, x_23, x_35, x_36, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_23);
return x_37;
}
}
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_38 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_38);
x_39 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_39);
lean_dec_ref(x_2);
x_40 = lean_unsigned_to_nat(0u);
x_41 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_LibrarySuggestions_currentFile_spec__0_spec__0_spec__1_spec__3___redArg(x_1, x_38, x_39, x_40, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_39);
lean_dec_ref(x_38);
return x_41;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_LibrarySuggestions_currentFile_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_17; uint8_t x_21; 
x_21 = lean_usize_dec_eq(x_3, x_4);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_array_uget(x_2, x_3);
switch (lean_obj_tag(x_22)) {
case 0:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec_ref(x_22);
lean_inc_ref(x_1);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_25 = lean_apply_8(x_1, x_5, x_23, x_24, x_6, x_7, x_8, x_9, lean_box(0));
x_17 = x_25;
goto block_20;
}
case 1:
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_22, 0);
lean_inc(x_26);
lean_dec_ref(x_22);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc_ref(x_1);
x_27 = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_LibrarySuggestions_currentFile_spec__0_spec__0_spec__1___redArg(x_1, x_26, x_5, x_6, x_7, x_8, x_9);
x_17 = x_27;
goto block_20;
}
default: 
{
x_11 = x_5;
x_12 = lean_box(0);
goto block_16;
}
}
}
else
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_1);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_5);
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_28);
return x_29;
}
block_16:
{
size_t x_13; size_t x_14; 
x_13 = 1;
x_14 = lean_usize_add(x_3, x_13);
x_3 = x_14;
x_5 = x_11;
goto _start;
}
block_20:
{
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_17, 0);
if (lean_obj_tag(x_18) == 0)
{
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_1);
return x_17;
}
else
{
lean_object* x_19; 
lean_inc_ref(x_18);
lean_dec_ref(x_17);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec_ref(x_18);
x_11 = x_19;
x_12 = lean_box(0);
goto block_16;
}
}
else
{
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_1);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_LibrarySuggestions_currentFile_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_LibrarySuggestions_currentFile_spec__0_spec__0_spec__1_spec__2___redArg(x_1, x_2, x_11, x_12, x_5, x_6, x_7, x_8, x_9);
lean_dec_ref(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_LibrarySuggestions_currentFile_spec__0_spec__0_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_LibrarySuggestions_currentFile_spec__0_spec__0_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_LibrarySuggestions_currentFile_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_forIn___at___00Lean_LibrarySuggestions_currentFile_spec__0___redArg___lam__0___boxed), 9, 1);
lean_closure_set(x_9, 0, x_3);
x_10 = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_LibrarySuggestions_currentFile_spec__0_spec__0_spec__1___redArg(x_9, x_1, x_2, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec(x_12);
lean_ctor_set(x_10, 0, x_13);
return x_10;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_10, 0);
lean_inc(x_14);
lean_dec(x_10);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_10);
if (x_17 == 0)
{
return x_10;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_10, 0);
lean_inc(x_18);
lean_dec(x_10);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_LibrarySuggestions_currentFile_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_PersistentHashMap_forIn___at___00Lean_LibrarySuggestions_currentFile_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_currentFile___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_7 = lean_st_ref_get(x_5);
x_8 = lean_ctor_get(x_7, 0);
lean_inc_ref(x_8);
lean_dec(x_7);
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec_ref(x_1);
lean_inc_ref(x_8);
x_10 = l_Lean_Environment_constants(x_8);
x_11 = lean_ctor_get(x_10, 1);
lean_inc_ref(x_11);
lean_dec_ref(x_10);
x_12 = lean_alloc_closure((void*)(l_Lean_LibrarySuggestions_currentFile___redArg___lam__0___boxed), 9, 2);
lean_closure_set(x_12, 0, x_9);
lean_closure_set(x_12, 1, x_8);
x_13 = l_Lean_LibrarySuggestions_Selector_postFilter___closed__1;
x_14 = l_Lean_PersistentHashMap_forIn___at___00Lean_LibrarySuggestions_currentFile_spec__0___redArg(x_11, x_13, x_12, x_2, x_3, x_4, x_5);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_currentFile___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_LibrarySuggestions_currentFile___redArg(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_currentFile(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_LibrarySuggestions_currentFile___redArg(x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_currentFile___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_LibrarySuggestions_currentFile(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_LibrarySuggestions_currentFile_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_PersistentHashMap_forIn___at___00Lean_LibrarySuggestions_currentFile_spec__0___redArg(x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_LibrarySuggestions_currentFile_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_PersistentHashMap_forIn___at___00Lean_LibrarySuggestions_currentFile_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_LibrarySuggestions_currentFile_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_LibrarySuggestions_currentFile_spec__0_spec__0_spec__1___redArg(x_2, x_1, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_LibrarySuggestions_currentFile_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_LibrarySuggestions_currentFile_spec__0_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_LibrarySuggestions_currentFile_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_LibrarySuggestions_currentFile_spec__0_spec__0_spec__1___redArg(x_5, x_4, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_LibrarySuggestions_currentFile_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_LibrarySuggestions_currentFile_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_LibrarySuggestions_currentFile_spec__0_spec__0_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_LibrarySuggestions_currentFile_spec__0_spec__0_spec__1___redArg(x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_LibrarySuggestions_currentFile_spec__0_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_LibrarySuggestions_currentFile_spec__0_spec__0_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_LibrarySuggestions_currentFile_spec__0_spec__0_spec__1_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, size_t x_7, size_t x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_LibrarySuggestions_currentFile_spec__0_spec__0_spec__1_spec__2___redArg(x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_LibrarySuggestions_currentFile_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
size_t x_15; size_t x_16; lean_object* x_17; 
x_15 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_16 = lean_unbox_usize(x_8);
lean_dec(x_8);
x_17 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_LibrarySuggestions_currentFile_spec__0_spec__0_spec__1_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_15, x_16, x_9, x_10, x_11, x_12, x_13);
lean_dec_ref(x_6);
return x_17;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_LibrarySuggestions_currentFile_spec__0_spec__0_spec__1_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_16; 
x_16 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_LibrarySuggestions_currentFile_spec__0_spec__0_spec__1_spec__3___redArg(x_5, x_6, x_7, x_9, x_10, x_11, x_12, x_13, x_14);
return x_16;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_LibrarySuggestions_currentFile_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_LibrarySuggestions_currentFile_spec__0_spec__0_spec__1_spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_initFn___lam__0_00___x40_Lean_LibrarySuggestions_Basic_2654663577____hygCtx___hyg_2_(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_initFn___lam__0_00___x40_Lean_LibrarySuggestions_Basic_2654663577____hygCtx___hyg_2____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_LibrarySuggestions_initFn___lam__0_00___x40_Lean_LibrarySuggestions_Basic_2654663577____hygCtx___hyg_2_(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_2654663577____hygCtx___hyg_2__spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; 
lean_dec(x_4);
x_6 = lean_array_uget(x_1, x_2);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = 1;
x_9 = lean_usize_add(x_2, x_8);
x_2 = x_9;
x_4 = x_7;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_2654663577____hygCtx___hyg_2__spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_2654663577____hygCtx___hyg_2__spec__0(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_2654663577____hygCtx___hyg_2__spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_10; 
x_10 = lean_usize_dec_eq(x_2, x_3);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_array_uget(x_1, x_2);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_array_get_size(x_11);
x_14 = lean_nat_dec_lt(x_12, x_13);
if (x_14 == 0)
{
lean_dec(x_11);
x_5 = x_4;
goto block_9;
}
else
{
uint8_t x_15; 
x_15 = lean_nat_dec_le(x_13, x_13);
if (x_15 == 0)
{
if (x_14 == 0)
{
lean_dec(x_11);
x_5 = x_4;
goto block_9;
}
else
{
size_t x_16; size_t x_17; lean_object* x_18; 
x_16 = 0;
x_17 = lean_usize_of_nat(x_13);
x_18 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_2654663577____hygCtx___hyg_2__spec__0(x_11, x_16, x_17, x_4);
lean_dec(x_11);
x_5 = x_18;
goto block_9;
}
}
else
{
size_t x_19; size_t x_20; lean_object* x_21; 
x_19 = 0;
x_20 = lean_usize_of_nat(x_13);
x_21 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_2654663577____hygCtx___hyg_2__spec__0(x_11, x_19, x_20, x_4);
lean_dec(x_11);
x_5 = x_21;
goto block_9;
}
}
}
else
{
return x_4;
}
block_9:
{
size_t x_6; size_t x_7; 
x_6 = 1;
x_7 = lean_usize_add(x_2, x_6);
x_2 = x_7;
x_4 = x_5;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_2654663577____hygCtx___hyg_2__spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_2654663577____hygCtx___hyg_2__spec__1(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_initFn___lam__1_00___x40_Lean_LibrarySuggestions_Basic_2654663577____hygCtx___hyg_2_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_box(0);
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_array_get_size(x_1);
x_5 = lean_nat_dec_lt(x_3, x_4);
if (x_5 == 0)
{
return x_2;
}
else
{
uint8_t x_6; 
x_6 = lean_nat_dec_le(x_4, x_4);
if (x_6 == 0)
{
if (x_5 == 0)
{
return x_2;
}
else
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = 0;
x_8 = lean_usize_of_nat(x_4);
x_9 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_2654663577____hygCtx___hyg_2__spec__1(x_1, x_7, x_8, x_2);
return x_9;
}
}
else
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = 0;
x_11 = lean_usize_of_nat(x_4);
x_12 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_2654663577____hygCtx___hyg_2__spec__1(x_1, x_10, x_11, x_2);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_initFn___lam__1_00___x40_Lean_LibrarySuggestions_Basic_2654663577____hygCtx___hyg_2____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_LibrarySuggestions_initFn___lam__1_00___x40_Lean_LibrarySuggestions_Basic_2654663577____hygCtx___hyg_2_(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_2654663577____hygCtx___hyg_2_() {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = ((lean_object*)(l_Lean_LibrarySuggestions_initFn___closed__4_00___x40_Lean_LibrarySuggestions_Basic_2654663577____hygCtx___hyg_2_));
x_3 = l_Lean_registerSimplePersistentEnvExtension___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_2654663577____hygCtx___hyg_2____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_2654663577____hygCtx___hyg_2_();
return x_2;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__1_spec__2___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__1_spec__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__1_spec__2___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__1_spec__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__1_spec__2___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 2, x_2);
lean_ctor_set(x_3, 3, x_1);
lean_ctor_set(x_3, 4, x_1);
lean_ctor_set(x_3, 5, x_1);
lean_ctor_set(x_3, 6, x_1);
lean_ctor_set(x_3, 7, x_1);
lean_ctor_set(x_3, 8, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__1_spec__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__1_spec__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__1_spec__2___closed__3;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__1_spec__2___closed__5() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__1_spec__2___closed__3;
x_4 = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__1_spec__2___closed__4;
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_2);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__1_spec__2___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(1);
x_2 = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__1_spec__2___closed__5;
x_3 = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__1_spec__2___closed__1;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__1_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_5 = lean_st_ref_get(x_3);
x_6 = lean_ctor_get(x_5, 0);
lean_inc_ref(x_6);
lean_dec(x_5);
x_7 = lean_ctor_get(x_2, 2);
x_8 = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__1_spec__2___closed__2;
x_9 = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__1_spec__2___closed__6;
lean_inc_ref(x_7);
x_10 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_10, 0, x_6);
lean_ctor_set(x_10, 1, x_8);
lean_ctor_set(x_10, 2, x_9);
lean_ctor_set(x_10, 3, x_7);
x_11 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_1);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__1_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__1_spec__2(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_2, 5);
x_6 = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__1_spec__2(x_1, x_2, x_3);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_5);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_8);
lean_ctor_set_tag(x_6, 1);
lean_ctor_set(x_6, 0, x_9);
return x_6;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_6, 0);
lean_inc(x_10);
lean_dec(x_6);
lean_inc(x_5);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_5);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_throwError___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__1___redArg(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__6___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_3, 5);
x_8 = l_Lean_replaceRef(x_1, x_7);
lean_dec(x_7);
lean_ctor_set(x_3, 5, x_8);
x_9 = l_Lean_throwError___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__1___redArg(x_2, x_3, x_4);
lean_dec_ref(x_3);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_10 = lean_ctor_get(x_3, 0);
x_11 = lean_ctor_get(x_3, 1);
x_12 = lean_ctor_get(x_3, 2);
x_13 = lean_ctor_get(x_3, 3);
x_14 = lean_ctor_get(x_3, 4);
x_15 = lean_ctor_get(x_3, 5);
x_16 = lean_ctor_get(x_3, 6);
x_17 = lean_ctor_get(x_3, 7);
x_18 = lean_ctor_get(x_3, 8);
x_19 = lean_ctor_get(x_3, 9);
x_20 = lean_ctor_get(x_3, 10);
x_21 = lean_ctor_get(x_3, 11);
x_22 = lean_ctor_get_uint8(x_3, sizeof(void*)*14);
x_23 = lean_ctor_get(x_3, 12);
x_24 = lean_ctor_get_uint8(x_3, sizeof(void*)*14 + 1);
x_25 = lean_ctor_get(x_3, 13);
lean_inc(x_25);
lean_inc(x_23);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_3);
x_26 = l_Lean_replaceRef(x_1, x_15);
lean_dec(x_15);
x_27 = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(x_27, 0, x_10);
lean_ctor_set(x_27, 1, x_11);
lean_ctor_set(x_27, 2, x_12);
lean_ctor_set(x_27, 3, x_13);
lean_ctor_set(x_27, 4, x_14);
lean_ctor_set(x_27, 5, x_26);
lean_ctor_set(x_27, 6, x_16);
lean_ctor_set(x_27, 7, x_17);
lean_ctor_set(x_27, 8, x_18);
lean_ctor_set(x_27, 9, x_19);
lean_ctor_set(x_27, 10, x_20);
lean_ctor_set(x_27, 11, x_21);
lean_ctor_set(x_27, 12, x_23);
lean_ctor_set(x_27, 13, x_25);
lean_ctor_set_uint8(x_27, sizeof(void*)*14, x_22);
lean_ctor_set_uint8(x_27, sizeof(void*)*14 + 1, x_24);
x_28 = l_Lean_throwError___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__1___redArg(x_2, x_27, x_4);
lean_dec_ref(x_27);
return x_28;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__6___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__6___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__6));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__8));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__10));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__12));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_st_ref_get(x_3);
x_6 = lean_ctor_get(x_5, 0);
lean_inc_ref(x_6);
lean_dec(x_5);
x_7 = l_Lean_Name_isAnonymous(x_2);
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = lean_ctor_get_uint8(x_6, sizeof(void*)*8);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec_ref(x_6);
lean_dec(x_2);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_1);
return x_9;
}
else
{
lean_object* x_10; uint8_t x_11; 
lean_inc_ref(x_6);
x_10 = l_Lean_Environment_setExporting(x_6, x_7);
lean_inc(x_2);
lean_inc_ref(x_10);
x_11 = l_Lean_Environment_contains(x_10, x_2, x_8);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec_ref(x_10);
lean_dec_ref(x_6);
lean_dec(x_2);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_1);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_13 = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__1_spec__2___closed__2;
x_14 = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__1_spec__2___closed__6;
x_15 = l_Lean_Options_empty;
x_16 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_16, 0, x_10);
lean_ctor_set(x_16, 1, x_13);
lean_ctor_set(x_16, 2, x_14);
lean_ctor_set(x_16, 3, x_15);
lean_inc(x_2);
x_17 = l_Lean_MessageData_ofConstName(x_2, x_7);
x_18 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_Lean_Environment_getModuleIdxFor_x3f(x_6, x_2);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec_ref(x_6);
lean_dec(x_2);
x_20 = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1;
x_21 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_18);
x_22 = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3;
x_23 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = l_Lean_MessageData_note(x_23);
x_25 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_25, 0, x_1);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
else
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_19);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_28 = lean_ctor_get(x_19, 0);
x_29 = lean_box(0);
x_30 = l_Lean_Environment_header(x_6);
lean_dec_ref(x_6);
x_31 = l_Lean_EnvironmentHeader_moduleNames(x_30);
x_32 = lean_array_get(x_29, x_31, x_28);
lean_dec(x_28);
lean_dec_ref(x_31);
x_33 = l_Lean_isPrivateName(x_2);
lean_dec(x_2);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_34 = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5;
x_35 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_18);
x_36 = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7;
x_37 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
x_38 = l_Lean_MessageData_ofName(x_32);
x_39 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
x_40 = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9;
x_41 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
x_42 = l_Lean_MessageData_note(x_41);
x_43 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_43, 0, x_1);
lean_ctor_set(x_43, 1, x_42);
lean_ctor_set_tag(x_19, 0);
lean_ctor_set(x_19, 0, x_43);
return x_19;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_44 = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1;
x_45 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_18);
x_46 = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11;
x_47 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
x_48 = l_Lean_MessageData_ofName(x_32);
x_49 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
x_50 = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13;
x_51 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
x_52 = l_Lean_MessageData_note(x_51);
x_53 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_53, 0, x_1);
lean_ctor_set(x_53, 1, x_52);
lean_ctor_set_tag(x_19, 0);
lean_ctor_set(x_19, 0, x_53);
return x_19;
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_54 = lean_ctor_get(x_19, 0);
lean_inc(x_54);
lean_dec(x_19);
x_55 = lean_box(0);
x_56 = l_Lean_Environment_header(x_6);
lean_dec_ref(x_6);
x_57 = l_Lean_EnvironmentHeader_moduleNames(x_56);
x_58 = lean_array_get(x_55, x_57, x_54);
lean_dec(x_54);
lean_dec_ref(x_57);
x_59 = l_Lean_isPrivateName(x_2);
lean_dec(x_2);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_60 = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5;
x_61 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_18);
x_62 = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7;
x_63 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
x_64 = l_Lean_MessageData_ofName(x_58);
x_65 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
x_66 = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9;
x_67 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
x_68 = l_Lean_MessageData_note(x_67);
x_69 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_69, 0, x_1);
lean_ctor_set(x_69, 1, x_68);
x_70 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_70, 0, x_69);
return x_70;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_71 = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1;
x_72 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_18);
x_73 = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11;
x_74 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
x_75 = l_Lean_MessageData_ofName(x_58);
x_76 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
x_77 = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13;
x_78 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
x_79 = l_Lean_MessageData_note(x_78);
x_80 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_80, 0, x_1);
lean_ctor_set(x_80, 1, x_79);
x_81 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_81, 0, x_80);
return x_81;
}
}
}
}
}
}
else
{
lean_object* x_82; 
lean_dec_ref(x_6);
lean_dec(x_2);
x_82 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_82, 0, x_1);
return x_82;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(x_1, x_2, x_3);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(x_1, x_2, x_4);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = l_Lean_unknownIdentifierMessageTag;
x_10 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
lean_ctor_set(x_6, 0, x_10);
return x_6;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_6, 0);
lean_inc(x_11);
lean_dec(x_6);
x_12 = l_Lean_unknownIdentifierMessageTag;
x_13 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5(x_2, x_3, x_4, x_5);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec_ref(x_7);
x_9 = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__6___redArg(x_1, x_8, x_4, x_5);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_1);
return x_7;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__2));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__1;
x_7 = 0;
lean_inc(x_2);
x_8 = l_Lean_MessageData_ofConstName(x_2, x_7);
x_9 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_8);
x_10 = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__3;
x_11 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
x_12 = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___redArg(x_1, x_11, x_2, x_3, x_4);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_2, 5);
lean_inc(x_5);
x_6 = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(x_5, x_1, x_2, x_3);
lean_dec(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0___redArg(x_1, x_2, x_3);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_st_ref_get(x_3);
x_6 = lean_ctor_get(x_5, 0);
lean_inc_ref(x_6);
lean_dec(x_5);
x_7 = 0;
lean_inc(x_1);
x_8 = l_Lean_Environment_find_x3f(x_6, x_1, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
x_9 = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0___redArg(x_1, x_2, x_3);
return x_9;
}
else
{
uint8_t x_10; 
lean_dec_ref(x_2);
lean_dec(x_1);
x_10 = !lean_is_exclusive(x_8);
if (x_10 == 0)
{
lean_ctor_set_tag(x_8, 0);
return x_8;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_8, 0);
lean_inc(x_11);
lean_dec(x_8);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0(x_1, x_2, x_3);
lean_dec(x_3);
return x_5;
}
}
static lean_object* _init_l_Lean_LibrarySuggestions_initFn___lam__0___closed__0_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_LibrarySuggestions_initFn___lam__0___closed__1_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_LibrarySuggestions_initFn___lam__0___closed__0_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2_;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_LibrarySuggestions_initFn___lam__0___closed__2_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_LibrarySuggestions_initFn___lam__0___closed__1_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2_;
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_LibrarySuggestions_initFn___lam__0___closed__5_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_LibrarySuggestions_initFn___lam__0___closed__4_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2_));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_LibrarySuggestions_initFn___lam__0___closed__7_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_LibrarySuggestions_initFn___lam__0___closed__6_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2_));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_LibrarySuggestions_initFn___lam__0___closed__9_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_LibrarySuggestions_initFn___lam__0___closed__8_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2_));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_initFn___lam__0_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2_(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_39; 
lean_inc_ref(x_2);
lean_inc(x_1);
x_39 = l_Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0(x_1, x_2, x_3);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
lean_dec_ref(x_39);
x_41 = l_Lean_ConstantInfo_type(x_40);
lean_dec(x_40);
x_42 = l_Lean_LibrarySuggestions_initFn___lam__0___closed__5_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2_;
x_43 = lean_expr_eqv(x_41, x_42);
lean_dec_ref(x_41);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_44 = l_Lean_LibrarySuggestions_initFn___lam__0___closed__7_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2_;
x_45 = l_Lean_MessageData_ofName(x_1);
x_46 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
x_47 = l_Lean_LibrarySuggestions_initFn___lam__0___closed__9_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2_;
x_48 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
x_49 = l_Lean_throwError___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__1___redArg(x_48, x_2, x_3);
lean_dec_ref(x_2);
return x_49;
}
else
{
lean_dec_ref(x_2);
x_5 = x_3;
x_6 = lean_box(0);
goto block_38;
}
}
else
{
uint8_t x_50; 
lean_dec_ref(x_2);
lean_dec(x_1);
x_50 = !lean_is_exclusive(x_39);
if (x_50 == 0)
{
return x_39;
}
else
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_39, 0);
lean_inc(x_51);
lean_dec(x_39);
x_52 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_52, 0, x_51);
return x_52;
}
}
block_38:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_st_ref_take(x_5);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 5);
lean_dec(x_10);
x_11 = l_Lean_LibrarySuggestions_librarySuggestionsExt;
x_12 = lean_ctor_get(x_11, 0);
lean_inc_ref(x_12);
x_13 = lean_ctor_get(x_12, 2);
lean_inc(x_13);
lean_dec_ref(x_12);
x_14 = lean_box(0);
x_15 = l_Lean_PersistentEnvExtension_addEntry___redArg(x_11, x_9, x_1, x_13, x_14);
lean_dec(x_13);
x_16 = l_Lean_LibrarySuggestions_initFn___lam__0___closed__2_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2_;
lean_ctor_set(x_7, 5, x_16);
lean_ctor_set(x_7, 0, x_15);
x_17 = lean_st_ref_set(x_5, x_7);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_20 = lean_ctor_get(x_7, 0);
x_21 = lean_ctor_get(x_7, 1);
x_22 = lean_ctor_get(x_7, 2);
x_23 = lean_ctor_get(x_7, 3);
x_24 = lean_ctor_get(x_7, 4);
x_25 = lean_ctor_get(x_7, 6);
x_26 = lean_ctor_get(x_7, 7);
x_27 = lean_ctor_get(x_7, 8);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_7);
x_28 = l_Lean_LibrarySuggestions_librarySuggestionsExt;
x_29 = lean_ctor_get(x_28, 0);
lean_inc_ref(x_29);
x_30 = lean_ctor_get(x_29, 2);
lean_inc(x_30);
lean_dec_ref(x_29);
x_31 = lean_box(0);
x_32 = l_Lean_PersistentEnvExtension_addEntry___redArg(x_28, x_20, x_1, x_30, x_31);
lean_dec(x_30);
x_33 = l_Lean_LibrarySuggestions_initFn___lam__0___closed__2_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2_;
x_34 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_21);
lean_ctor_set(x_34, 2, x_22);
lean_ctor_set(x_34, 3, x_23);
lean_ctor_set(x_34, 4, x_24);
lean_ctor_set(x_34, 5, x_33);
lean_ctor_set(x_34, 6, x_25);
lean_ctor_set(x_34, 7, x_26);
lean_ctor_set(x_34, 8, x_27);
x_35 = lean_st_ref_set(x_5, x_34);
x_36 = lean_box(0);
x_37 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_37, 0, x_36);
return x_37;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_initFn___lam__0_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2____boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_LibrarySuggestions_initFn___lam__0_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2_(x_1, x_2, x_3);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2_() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; 
x_2 = ((lean_object*)(l_Lean_LibrarySuggestions_initFn___closed__0_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2_));
x_3 = ((lean_object*)(l_Lean_LibrarySuggestions_initFn___closed__2_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2_));
x_4 = ((lean_object*)(l_Lean_LibrarySuggestions_initFn___closed__3_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2_));
x_5 = ((lean_object*)(l_Lean_LibrarySuggestions_initFn___closed__5_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2_));
x_6 = 0;
x_7 = lean_box(2);
x_8 = l_Lean_registerTagAttribute(x_3, x_4, x_2, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2_();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_throwError___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__1___redArg(x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_throwError___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0___redArg(x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___redArg(x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(x_1, x_2, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__6___redArg(x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__6(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
return x_7;
}
}
static lean_object* _init_l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00Lean_LibrarySuggestions_getSelectorImpl_spec__0_spec__1___redArg___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_abortCommandExceptionId;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00Lean_LibrarySuggestions_getSelectorImpl_spec__0_spec__1___redArg() {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00Lean_LibrarySuggestions_getSelectorImpl_spec__0_spec__1___redArg___closed__0;
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00Lean_LibrarySuggestions_getSelectorImpl_spec__0_spec__1___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00Lean_LibrarySuggestions_getSelectorImpl_spec__0_spec__1___redArg();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_LibrarySuggestions_getSelectorImpl_spec__0_spec__0_spec__1_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_st_ref_get(x_5);
x_8 = lean_ctor_get(x_7, 0);
lean_inc_ref(x_8);
lean_dec(x_7);
x_9 = lean_st_ref_get(x_3);
x_10 = lean_ctor_get(x_9, 0);
lean_inc_ref(x_10);
lean_dec(x_9);
x_11 = lean_ctor_get(x_2, 2);
x_12 = lean_ctor_get(x_4, 2);
lean_inc_ref(x_12);
lean_inc_ref(x_11);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_8);
lean_ctor_set(x_13, 1, x_10);
lean_ctor_set(x_13, 2, x_11);
lean_ctor_set(x_13, 3, x_12);
x_14 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_1);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_LibrarySuggestions_getSelectorImpl_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_LibrarySuggestions_getSelectorImpl_spec__0_spec__0_spec__1_spec__3(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_LibrarySuggestions_getSelectorImpl_spec__0_spec__0_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_4, 5);
x_8 = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_LibrarySuggestions_getSelectorImpl_spec__0_spec__0_spec__1_spec__3(x_1, x_2, x_3, x_4, x_5);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_7);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_10);
lean_ctor_set_tag(x_8, 1);
lean_ctor_set(x_8, 0, x_11);
return x_8;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_8, 0);
lean_inc(x_12);
lean_dec(x_8);
lean_inc(x_7);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_7);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_LibrarySuggestions_getSelectorImpl_spec__0_spec__0_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_LibrarySuggestions_getSelectorImpl_spec__0_spec__0_spec__1___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_LibrarySuggestions_getSelectorImpl_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec_ref(x_1);
x_8 = l_Lean_stringToMessageData(x_7);
x_9 = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_LibrarySuggestions_getSelectorImpl_spec__0_spec__0_spec__1___redArg(x_8, x_2, x_3, x_4, x_5);
return x_9;
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_1);
if (x_10 == 0)
{
lean_ctor_set_tag(x_1, 0);
return x_1;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_LibrarySuggestions_getSelectorImpl_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_LibrarySuggestions_getSelectorImpl_spec__0_spec__0___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConstCheck___at___00Lean_LibrarySuggestions_getSelectorImpl_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_st_ref_get(x_6);
x_9 = lean_ctor_get(x_8, 0);
lean_inc_ref(x_9);
lean_dec(x_8);
lean_inc(x_2);
x_10 = lean_has_compile_error(x_9, x_2);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_st_ref_get(x_6);
x_12 = lean_ctor_get(x_11, 0);
lean_inc_ref(x_12);
lean_dec(x_11);
x_13 = lean_ctor_get(x_5, 2);
x_14 = l_Lean_Environment_evalConstCheck___redArg(x_12, x_13, x_1, x_2);
x_15 = l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_LibrarySuggestions_getSelectorImpl_spec__0_spec__0___redArg(x_14, x_3, x_4, x_5, x_6);
return x_15;
}
else
{
lean_object* x_16; 
x_16 = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00Lean_LibrarySuggestions_getSelectorImpl_spec__0_spec__1___redArg();
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec_ref(x_16);
x_17 = lean_st_ref_get(x_6);
x_18 = lean_ctor_get(x_17, 0);
lean_inc_ref(x_18);
lean_dec(x_17);
x_19 = lean_ctor_get(x_5, 2);
x_20 = l_Lean_Environment_evalConstCheck___redArg(x_18, x_19, x_1, x_2);
x_21 = l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_LibrarySuggestions_getSelectorImpl_spec__0_spec__0___redArg(x_20, x_3, x_4, x_5, x_6);
return x_21;
}
else
{
uint8_t x_22; 
lean_dec(x_2);
lean_dec(x_1);
x_22 = !lean_is_exclusive(x_16);
if (x_22 == 0)
{
return x_16;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_16, 0);
lean_inc(x_23);
lean_dec(x_16);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
return x_24;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_evalConstCheck___at___00Lean_LibrarySuggestions_getSelectorImpl_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_evalConstCheck___at___00Lean_LibrarySuggestions_getSelectorImpl_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_getSelectorImpl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_6 = lean_st_ref_get(x_4);
x_7 = lean_ctor_get(x_6, 0);
lean_inc_ref(x_7);
lean_dec(x_6);
x_8 = l_Lean_LibrarySuggestions_librarySuggestionsExt;
x_9 = lean_ctor_get(x_8, 0);
lean_inc_ref(x_9);
x_10 = lean_ctor_get(x_9, 2);
lean_inc(x_10);
lean_dec_ref(x_9);
x_11 = lean_box(0);
x_12 = lean_box(0);
x_13 = l_Lean_SimplePersistentEnvExtension_getState___redArg(x_11, x_8, x_7, x_10, x_12);
lean_dec(x_10);
if (lean_obj_tag(x_13) == 1)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = ((lean_object*)(l_Lean_LibrarySuggestions_initFn___lam__0___closed__4_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2_));
x_17 = l_Lean_evalConstCheck___at___00Lean_LibrarySuggestions_getSelectorImpl_spec__0___redArg(x_16, x_15, x_1, x_2, x_3, x_4);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_17, 0);
lean_ctor_set(x_13, 0, x_19);
lean_ctor_set(x_17, 0, x_13);
return x_17;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_17, 0);
lean_inc(x_20);
lean_dec(x_17);
lean_ctor_set(x_13, 0, x_20);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_13);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_28; 
lean_free_object(x_13);
x_22 = lean_ctor_get(x_17, 0);
lean_inc(x_22);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 x_23 = x_17;
} else {
 lean_dec_ref(x_17);
 x_23 = lean_box(0);
}
x_28 = l_Lean_Exception_isInterrupt(x_22);
if (x_28 == 0)
{
uint8_t x_29; 
lean_inc(x_22);
x_29 = l_Lean_Exception_isRuntime(x_22);
x_24 = x_29;
goto block_27;
}
else
{
x_24 = x_28;
goto block_27;
}
block_27:
{
if (x_24 == 0)
{
lean_object* x_25; 
lean_dec(x_22);
if (lean_is_scalar(x_23)) {
 x_25 = lean_alloc_ctor(0, 1, 0);
} else {
 x_25 = x_23;
 lean_ctor_set_tag(x_25, 0);
}
lean_ctor_set(x_25, 0, x_11);
return x_25;
}
else
{
lean_object* x_26; 
if (lean_is_scalar(x_23)) {
 x_26 = lean_alloc_ctor(1, 1, 0);
} else {
 x_26 = x_23;
}
lean_ctor_set(x_26, 0, x_22);
return x_26;
}
}
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_13, 0);
lean_inc(x_30);
lean_dec(x_13);
x_31 = ((lean_object*)(l_Lean_LibrarySuggestions_initFn___lam__0___closed__4_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2_));
x_32 = l_Lean_evalConstCheck___at___00Lean_LibrarySuggestions_getSelectorImpl_spec__0___redArg(x_31, x_30, x_1, x_2, x_3, x_4);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 x_34 = x_32;
} else {
 lean_dec_ref(x_32);
 x_34 = lean_box(0);
}
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_33);
if (lean_is_scalar(x_34)) {
 x_36 = lean_alloc_ctor(0, 1, 0);
} else {
 x_36 = x_34;
}
lean_ctor_set(x_36, 0, x_35);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; uint8_t x_43; 
x_37 = lean_ctor_get(x_32, 0);
lean_inc(x_37);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 x_38 = x_32;
} else {
 lean_dec_ref(x_32);
 x_38 = lean_box(0);
}
x_43 = l_Lean_Exception_isInterrupt(x_37);
if (x_43 == 0)
{
uint8_t x_44; 
lean_inc(x_37);
x_44 = l_Lean_Exception_isRuntime(x_37);
x_39 = x_44;
goto block_42;
}
else
{
x_39 = x_43;
goto block_42;
}
block_42:
{
if (x_39 == 0)
{
lean_object* x_40; 
lean_dec(x_37);
if (lean_is_scalar(x_38)) {
 x_40 = lean_alloc_ctor(0, 1, 0);
} else {
 x_40 = x_38;
 lean_ctor_set_tag(x_40, 0);
}
lean_ctor_set(x_40, 0, x_11);
return x_40;
}
else
{
lean_object* x_41; 
if (lean_is_scalar(x_38)) {
 x_41 = lean_alloc_ctor(1, 1, 0);
} else {
 x_41 = x_38;
}
lean_ctor_set(x_41, 0, x_37);
return x_41;
}
}
}
}
}
else
{
lean_object* x_45; 
lean_dec(x_13);
x_45 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_45, 0, x_11);
return x_45;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_getSelectorImpl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_LibrarySuggestions_getSelectorImpl(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00Lean_LibrarySuggestions_getSelectorImpl_spec__0_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00Lean_LibrarySuggestions_getSelectorImpl_spec__0_spec__1___redArg();
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00Lean_LibrarySuggestions_getSelectorImpl_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00Lean_LibrarySuggestions_getSelectorImpl_spec__0_spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConstCheck___at___00Lean_LibrarySuggestions_getSelectorImpl_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_evalConstCheck___at___00Lean_LibrarySuggestions_getSelectorImpl_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConstCheck___at___00Lean_LibrarySuggestions_getSelectorImpl_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_evalConstCheck___at___00Lean_LibrarySuggestions_getSelectorImpl_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_LibrarySuggestions_getSelectorImpl_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_LibrarySuggestions_getSelectorImpl_spec__0_spec__0___redArg(x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_LibrarySuggestions_getSelectorImpl_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_LibrarySuggestions_getSelectorImpl_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_LibrarySuggestions_getSelectorImpl_spec__0_spec__0_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_LibrarySuggestions_getSelectorImpl_spec__0_spec__0_spec__1___redArg(x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_LibrarySuggestions_getSelectorImpl_spec__0_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_LibrarySuggestions_getSelectorImpl_spec__0_spec__0_spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
static lean_object* _init_l_Lean_LibrarySuggestions_select___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_LibrarySuggestions_select___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_select(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_LibrarySuggestions_getSelectorImpl(x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec_ref(x_8);
if (lean_obj_tag(x_9) == 1)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec_ref(x_9);
x_11 = lean_apply_7(x_10, x_1, x_2, x_3, x_4, x_5, x_6, lean_box(0));
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_9);
lean_dec_ref(x_2);
lean_dec(x_1);
x_12 = l_Lean_LibrarySuggestions_select___closed__1;
x_13 = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_LibrarySuggestions_getSelectorImpl_spec__0_spec__0_spec__1___redArg(x_12, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_13;
}
}
else
{
uint8_t x_14; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_14 = !lean_is_exclusive(x_8);
if (x_14 == 0)
{
return x_8;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_8, 0);
lean_inc(x_15);
lean_dec(x_8);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_select___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_LibrarySuggestions_select(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__0___redArg___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_unsupportedSyntaxExceptionId;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__0___redArg() {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__0___redArg___closed__0;
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__0___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__0___redArg();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__0___redArg();
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__2___redArg(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_st_ref_get(x_1);
x_4 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_4);
lean_dec(x_3);
x_5 = l_Lean_Environment_header(x_4);
lean_dec_ref(x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec_ref(x_5);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_getMainModule___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__2___redArg(x_1);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_getMainModule___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__2___redArg(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_getMainModule___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__2_spec__4___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_4 = lean_st_ref_get(x_2);
x_5 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_5);
lean_dec(x_4);
x_6 = lean_st_ref_get(x_2);
x_7 = lean_ctor_get(x_6, 2);
lean_inc(x_7);
lean_dec(x_6);
x_8 = l_Lean_Elab_Command_instInhabitedScope_default;
x_9 = l_List_head_x21___redArg(x_8, x_7);
lean_dec(x_7);
x_10 = lean_ctor_get(x_9, 1);
lean_inc_ref(x_10);
lean_dec(x_9);
x_11 = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__1_spec__2___closed__2;
x_12 = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__1_spec__2___closed__6;
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_5);
lean_ctor_set(x_13, 1, x_11);
lean_ctor_set(x_13, 2, x_12);
lean_ctor_set(x_13, 3, x_10);
x_14 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_1);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__2_spec__4___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__2_spec__4___redArg(x_1, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__3_spec__11_spec__17___lam__0(uint8_t x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 1)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_3, 0);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_3, 1);
x_6 = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__3_spec__11_spec__17___lam__0___closed__0));
x_7 = lean_string_dec_eq(x_5, x_6);
if (x_7 == 0)
{
return x_1;
}
else
{
return x_2;
}
}
else
{
return x_1;
}
}
else
{
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__3_spec__11_spec__17___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_4 = lean_unbox(x_1);
x_5 = lean_unbox(x_2);
x_6 = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__3_spec__11_spec__17___lam__0(x_4, x_5, x_3);
lean_dec(x_3);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__3_spec__11_spec__17_spec__21(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_1, 0);
x_6 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(x_5, x_3);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = lean_unbox(x_4);
return x_7;
}
else
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec_ref(x_6);
if (lean_obj_tag(x_8) == 1)
{
uint8_t x_9; 
x_9 = lean_ctor_get_uint8(x_8, 0);
lean_dec_ref(x_8);
return x_9;
}
else
{
uint8_t x_10; 
lean_dec(x_8);
x_10 = lean_unbox(x_4);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__3_spec__11_spec__17_spec__21___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__3_spec__11_spec__17_spec__21(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__3_spec__11_spec__17(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_82; uint8_t x_83; lean_object* x_84; uint8_t x_85; lean_object* x_86; lean_object* x_87; uint8_t x_116; uint8_t x_117; lean_object* x_118; uint8_t x_119; lean_object* x_120; lean_object* x_121; uint8_t x_125; uint8_t x_126; lean_object* x_127; uint8_t x_128; uint8_t x_139; uint8_t x_140; uint8_t x_141; lean_object* x_142; uint8_t x_143; uint8_t x_145; uint8_t x_158; 
x_139 = 2;
x_158 = l_Lean_instBEqMessageSeverity_beq(x_3, x_139);
if (x_158 == 0)
{
x_145 = x_158;
goto block_157;
}
else
{
uint8_t x_159; 
lean_inc_ref(x_2);
x_159 = l_Lean_MessageData_hasSyntheticSorry(x_2);
x_145 = x_159;
goto block_157;
}
block_81:
{
lean_object* x_17; 
x_17 = l_Lean_Elab_Command_getScope___redArg(x_15);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec_ref(x_17);
x_19 = l_Lean_Elab_Command_getScope___redArg(x_15);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = lean_st_ref_take(x_15);
x_23 = lean_ctor_get(x_18, 2);
lean_inc(x_23);
lean_dec(x_18);
x_24 = lean_ctor_get(x_21, 3);
lean_inc(x_24);
lean_dec(x_21);
x_25 = !lean_is_exclusive(x_22);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_26 = lean_ctor_get(x_22, 1);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_23);
lean_ctor_set(x_27, 1, x_24);
x_28 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_11);
x_29 = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(x_29, 0, x_14);
lean_ctor_set(x_29, 1, x_10);
lean_ctor_set(x_29, 2, x_13);
lean_ctor_set(x_29, 3, x_8);
lean_ctor_set(x_29, 4, x_28);
lean_ctor_set_uint8(x_29, sizeof(void*)*5, x_12);
lean_ctor_set_uint8(x_29, sizeof(void*)*5 + 1, x_9);
lean_ctor_set_uint8(x_29, sizeof(void*)*5 + 2, x_4);
x_30 = l_Lean_MessageLog_add(x_29, x_26);
lean_ctor_set(x_22, 1, x_30);
x_31 = lean_st_ref_set(x_15, x_22);
x_32 = lean_box(0);
lean_ctor_set(x_19, 0, x_32);
return x_19;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_33 = lean_ctor_get(x_22, 0);
x_34 = lean_ctor_get(x_22, 1);
x_35 = lean_ctor_get(x_22, 2);
x_36 = lean_ctor_get(x_22, 3);
x_37 = lean_ctor_get(x_22, 4);
x_38 = lean_ctor_get(x_22, 5);
x_39 = lean_ctor_get(x_22, 6);
x_40 = lean_ctor_get(x_22, 7);
x_41 = lean_ctor_get(x_22, 8);
x_42 = lean_ctor_get(x_22, 9);
x_43 = lean_ctor_get(x_22, 10);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_22);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_23);
lean_ctor_set(x_44, 1, x_24);
x_45 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_11);
x_46 = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(x_46, 0, x_14);
lean_ctor_set(x_46, 1, x_10);
lean_ctor_set(x_46, 2, x_13);
lean_ctor_set(x_46, 3, x_8);
lean_ctor_set(x_46, 4, x_45);
lean_ctor_set_uint8(x_46, sizeof(void*)*5, x_12);
lean_ctor_set_uint8(x_46, sizeof(void*)*5 + 1, x_9);
lean_ctor_set_uint8(x_46, sizeof(void*)*5 + 2, x_4);
x_47 = l_Lean_MessageLog_add(x_46, x_34);
x_48 = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(x_48, 0, x_33);
lean_ctor_set(x_48, 1, x_47);
lean_ctor_set(x_48, 2, x_35);
lean_ctor_set(x_48, 3, x_36);
lean_ctor_set(x_48, 4, x_37);
lean_ctor_set(x_48, 5, x_38);
lean_ctor_set(x_48, 6, x_39);
lean_ctor_set(x_48, 7, x_40);
lean_ctor_set(x_48, 8, x_41);
lean_ctor_set(x_48, 9, x_42);
lean_ctor_set(x_48, 10, x_43);
x_49 = lean_st_ref_set(x_15, x_48);
x_50 = lean_box(0);
lean_ctor_set(x_19, 0, x_50);
return x_19;
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_51 = lean_ctor_get(x_19, 0);
lean_inc(x_51);
lean_dec(x_19);
x_52 = lean_st_ref_take(x_15);
x_53 = lean_ctor_get(x_18, 2);
lean_inc(x_53);
lean_dec(x_18);
x_54 = lean_ctor_get(x_51, 3);
lean_inc(x_54);
lean_dec(x_51);
x_55 = lean_ctor_get(x_52, 0);
lean_inc_ref(x_55);
x_56 = lean_ctor_get(x_52, 1);
lean_inc_ref(x_56);
x_57 = lean_ctor_get(x_52, 2);
lean_inc(x_57);
x_58 = lean_ctor_get(x_52, 3);
lean_inc(x_58);
x_59 = lean_ctor_get(x_52, 4);
lean_inc(x_59);
x_60 = lean_ctor_get(x_52, 5);
lean_inc(x_60);
x_61 = lean_ctor_get(x_52, 6);
lean_inc_ref(x_61);
x_62 = lean_ctor_get(x_52, 7);
lean_inc_ref(x_62);
x_63 = lean_ctor_get(x_52, 8);
lean_inc_ref(x_63);
x_64 = lean_ctor_get(x_52, 9);
lean_inc_ref(x_64);
x_65 = lean_ctor_get(x_52, 10);
lean_inc_ref(x_65);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 lean_ctor_release(x_52, 2);
 lean_ctor_release(x_52, 3);
 lean_ctor_release(x_52, 4);
 lean_ctor_release(x_52, 5);
 lean_ctor_release(x_52, 6);
 lean_ctor_release(x_52, 7);
 lean_ctor_release(x_52, 8);
 lean_ctor_release(x_52, 9);
 lean_ctor_release(x_52, 10);
 x_66 = x_52;
} else {
 lean_dec_ref(x_52);
 x_66 = lean_box(0);
}
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_53);
lean_ctor_set(x_67, 1, x_54);
x_68 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_11);
x_69 = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(x_69, 0, x_14);
lean_ctor_set(x_69, 1, x_10);
lean_ctor_set(x_69, 2, x_13);
lean_ctor_set(x_69, 3, x_8);
lean_ctor_set(x_69, 4, x_68);
lean_ctor_set_uint8(x_69, sizeof(void*)*5, x_12);
lean_ctor_set_uint8(x_69, sizeof(void*)*5 + 1, x_9);
lean_ctor_set_uint8(x_69, sizeof(void*)*5 + 2, x_4);
x_70 = l_Lean_MessageLog_add(x_69, x_56);
if (lean_is_scalar(x_66)) {
 x_71 = lean_alloc_ctor(0, 11, 0);
} else {
 x_71 = x_66;
}
lean_ctor_set(x_71, 0, x_55);
lean_ctor_set(x_71, 1, x_70);
lean_ctor_set(x_71, 2, x_57);
lean_ctor_set(x_71, 3, x_58);
lean_ctor_set(x_71, 4, x_59);
lean_ctor_set(x_71, 5, x_60);
lean_ctor_set(x_71, 6, x_61);
lean_ctor_set(x_71, 7, x_62);
lean_ctor_set(x_71, 8, x_63);
lean_ctor_set(x_71, 9, x_64);
lean_ctor_set(x_71, 10, x_65);
x_72 = lean_st_ref_set(x_15, x_71);
x_73 = lean_box(0);
x_74 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_74, 0, x_73);
return x_74;
}
}
else
{
uint8_t x_75; 
lean_dec(x_18);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_8);
x_75 = !lean_is_exclusive(x_19);
if (x_75 == 0)
{
return x_19;
}
else
{
lean_object* x_76; lean_object* x_77; 
x_76 = lean_ctor_get(x_19, 0);
lean_inc(x_76);
lean_dec(x_19);
x_77 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_77, 0, x_76);
return x_77;
}
}
}
else
{
uint8_t x_78; 
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_8);
x_78 = !lean_is_exclusive(x_17);
if (x_78 == 0)
{
return x_17;
}
else
{
lean_object* x_79; lean_object* x_80; 
x_79 = lean_ctor_get(x_17, 0);
lean_inc(x_79);
lean_dec(x_17);
x_80 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_80, 0, x_79);
return x_80;
}
}
}
block_115:
{
lean_object* x_88; lean_object* x_89; uint8_t x_90; lean_object* x_91; lean_object* x_92; uint8_t x_93; 
x_88 = lean_ctor_get(x_5, 0);
lean_inc_ref(x_88);
x_89 = lean_ctor_get(x_5, 1);
lean_inc_ref(x_89);
x_90 = lean_ctor_get_uint8(x_5, sizeof(void*)*10);
lean_dec_ref(x_5);
x_91 = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(x_2);
x_92 = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__2_spec__4___redArg(x_91, x_6);
x_93 = !lean_is_exclusive(x_92);
if (x_93 == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_94 = lean_ctor_get(x_92, 0);
lean_inc_ref(x_89);
x_95 = l_Lean_FileMap_toPosition(x_89, x_86);
lean_dec(x_86);
x_96 = l_Lean_FileMap_toPosition(x_89, x_87);
lean_dec(x_87);
x_97 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_97, 0, x_96);
x_98 = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__3_spec__11_spec__17___closed__0));
if (x_90 == 0)
{
lean_free_object(x_92);
x_8 = x_98;
x_9 = x_83;
x_10 = x_95;
x_11 = x_94;
x_12 = x_85;
x_13 = x_97;
x_14 = x_88;
x_15 = x_6;
x_16 = lean_box(0);
goto block_81;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; uint8_t x_102; 
x_99 = lean_box(x_82);
x_100 = lean_box(x_90);
x_101 = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__3_spec__11_spec__17___lam__0___boxed), 3, 2);
lean_closure_set(x_101, 0, x_99);
lean_closure_set(x_101, 1, x_100);
lean_inc(x_94);
x_102 = l_Lean_MessageData_hasTag(x_101, x_94);
if (x_102 == 0)
{
lean_object* x_103; 
lean_dec_ref(x_97);
lean_dec_ref(x_95);
lean_dec(x_94);
lean_dec_ref(x_88);
x_103 = lean_box(0);
lean_ctor_set(x_92, 0, x_103);
return x_92;
}
else
{
lean_free_object(x_92);
x_8 = x_98;
x_9 = x_83;
x_10 = x_95;
x_11 = x_94;
x_12 = x_85;
x_13 = x_97;
x_14 = x_88;
x_15 = x_6;
x_16 = lean_box(0);
goto block_81;
}
}
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_104 = lean_ctor_get(x_92, 0);
lean_inc(x_104);
lean_dec(x_92);
lean_inc_ref(x_89);
x_105 = l_Lean_FileMap_toPosition(x_89, x_86);
lean_dec(x_86);
x_106 = l_Lean_FileMap_toPosition(x_89, x_87);
lean_dec(x_87);
x_107 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_107, 0, x_106);
x_108 = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__3_spec__11_spec__17___closed__0));
if (x_90 == 0)
{
x_8 = x_108;
x_9 = x_83;
x_10 = x_105;
x_11 = x_104;
x_12 = x_85;
x_13 = x_107;
x_14 = x_88;
x_15 = x_6;
x_16 = lean_box(0);
goto block_81;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; uint8_t x_112; 
x_109 = lean_box(x_82);
x_110 = lean_box(x_90);
x_111 = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__3_spec__11_spec__17___lam__0___boxed), 3, 2);
lean_closure_set(x_111, 0, x_109);
lean_closure_set(x_111, 1, x_110);
lean_inc(x_104);
x_112 = l_Lean_MessageData_hasTag(x_111, x_104);
if (x_112 == 0)
{
lean_object* x_113; lean_object* x_114; 
lean_dec_ref(x_107);
lean_dec_ref(x_105);
lean_dec(x_104);
lean_dec_ref(x_88);
x_113 = lean_box(0);
x_114 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_114, 0, x_113);
return x_114;
}
else
{
x_8 = x_108;
x_9 = x_83;
x_10 = x_105;
x_11 = x_104;
x_12 = x_85;
x_13 = x_107;
x_14 = x_88;
x_15 = x_6;
x_16 = lean_box(0);
goto block_81;
}
}
}
}
block_124:
{
lean_object* x_122; 
x_122 = l_Lean_Syntax_getTailPos_x3f(x_120, x_119);
lean_dec(x_120);
if (lean_obj_tag(x_122) == 0)
{
lean_inc(x_121);
x_82 = x_116;
x_83 = x_117;
x_84 = lean_box(0);
x_85 = x_119;
x_86 = x_121;
x_87 = x_121;
goto block_115;
}
else
{
lean_object* x_123; 
x_123 = lean_ctor_get(x_122, 0);
lean_inc(x_123);
lean_dec_ref(x_122);
x_82 = x_116;
x_83 = x_117;
x_84 = lean_box(0);
x_85 = x_119;
x_86 = x_121;
x_87 = x_123;
goto block_115;
}
}
block_138:
{
lean_object* x_129; 
x_129 = l_Lean_Elab_Command_getRef___redArg(x_5);
if (lean_obj_tag(x_129) == 0)
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_130 = lean_ctor_get(x_129, 0);
lean_inc(x_130);
lean_dec_ref(x_129);
x_131 = l_Lean_replaceRef(x_1, x_130);
lean_dec(x_130);
x_132 = l_Lean_Syntax_getPos_x3f(x_131, x_126);
if (lean_obj_tag(x_132) == 0)
{
lean_object* x_133; 
x_133 = lean_unsigned_to_nat(0u);
x_116 = x_125;
x_117 = x_128;
x_118 = lean_box(0);
x_119 = x_126;
x_120 = x_131;
x_121 = x_133;
goto block_124;
}
else
{
lean_object* x_134; 
x_134 = lean_ctor_get(x_132, 0);
lean_inc(x_134);
lean_dec_ref(x_132);
x_116 = x_125;
x_117 = x_128;
x_118 = lean_box(0);
x_119 = x_126;
x_120 = x_131;
x_121 = x_134;
goto block_124;
}
}
else
{
uint8_t x_135; 
lean_dec_ref(x_5);
lean_dec_ref(x_2);
x_135 = !lean_is_exclusive(x_129);
if (x_135 == 0)
{
return x_129;
}
else
{
lean_object* x_136; lean_object* x_137; 
x_136 = lean_ctor_get(x_129, 0);
lean_inc(x_136);
lean_dec(x_129);
x_137 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_137, 0, x_136);
return x_137;
}
}
}
block_144:
{
if (x_143 == 0)
{
x_125 = x_140;
x_126 = x_141;
x_127 = lean_box(0);
x_128 = x_3;
goto block_138;
}
else
{
x_125 = x_140;
x_126 = x_141;
x_127 = lean_box(0);
x_128 = x_139;
goto block_138;
}
}
block_157:
{
if (x_145 == 0)
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; uint8_t x_151; uint8_t x_152; 
x_146 = lean_st_ref_get(x_6);
x_147 = lean_ctor_get(x_146, 2);
lean_inc(x_147);
lean_dec(x_146);
x_148 = l_Lean_Elab_Command_instInhabitedScope_default;
x_149 = l_List_head_x21___redArg(x_148, x_147);
lean_dec(x_147);
x_150 = lean_ctor_get(x_149, 1);
lean_inc_ref(x_150);
lean_dec(x_149);
x_151 = 1;
x_152 = l_Lean_instBEqMessageSeverity_beq(x_3, x_151);
if (x_152 == 0)
{
lean_dec_ref(x_150);
x_140 = x_145;
x_141 = x_145;
x_142 = lean_box(0);
x_143 = x_152;
goto block_144;
}
else
{
lean_object* x_153; uint8_t x_154; 
x_153 = l_Lean_warningAsError;
x_154 = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__3_spec__11_spec__17_spec__21(x_150, x_153);
lean_dec_ref(x_150);
x_140 = x_145;
x_141 = x_145;
x_142 = lean_box(0);
x_143 = x_154;
goto block_144;
}
}
else
{
lean_object* x_155; lean_object* x_156; 
lean_dec_ref(x_5);
lean_dec_ref(x_2);
x_155 = lean_box(0);
x_156 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_156, 0, x_155);
return x_156;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__3_spec__11_spec__17___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; uint8_t x_9; lean_object* x_10; 
x_8 = lean_unbox(x_3);
x_9 = lean_unbox(x_4);
x_10 = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__3_spec__11_spec__17(x_1, x_2, x_8, x_9, x_5, x_6);
lean_dec(x_6);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__3_spec__11(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_Command_getRef___redArg(x_4);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec_ref(x_7);
x_9 = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__3_spec__11_spec__17(x_8, x_1, x_2, x_3, x_4, x_5);
lean_dec(x_8);
return x_9;
}
else
{
uint8_t x_10; 
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_10 = !lean_is_exclusive(x_7);
if (x_10 == 0)
{
return x_7;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_7, 0);
lean_inc(x_11);
lean_dec(x_7);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__3_spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; uint8_t x_8; lean_object* x_9; 
x_7 = lean_unbox(x_2);
x_8 = lean_unbox(x_3);
x_9 = l_Lean_log___at___00Lean_logWarning___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__3_spec__11(x_1, x_7, x_8, x_4, x_5);
lean_dec(x_5);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = 1;
x_6 = 0;
x_7 = l_Lean_log___at___00Lean_logWarning___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__3_spec__11(x_1, x_5, x_6, x_2, x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_logWarning___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__3(x_1, x_2, x_3);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__3___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_2);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__3___redArg(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_expandMacroImpl_x3f(x_1, x_2, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_5, 0);
lean_dec(x_8);
x_9 = lean_box(0);
lean_ctor_set(x_5, 0, x_9);
return x_5;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_5, 1);
lean_inc(x_10);
lean_dec(x_5);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_6);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_6, 0);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; uint8_t x_17; 
lean_free_object(x_6);
x_16 = lean_ctor_get(x_5, 1);
lean_inc(x_16);
lean_dec_ref(x_5);
x_17 = !lean_is_exclusive(x_15);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__3___redArg(x_15, x_16);
lean_dec_ref(x_15);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_15, 0);
lean_inc(x_19);
lean_dec(x_15);
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__3___redArg(x_20, x_16);
lean_dec_ref(x_20);
return x_21;
}
}
else
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_5, 1);
lean_inc(x_22);
lean_dec_ref(x_5);
x_23 = !lean_is_exclusive(x_15);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_15, 0);
lean_ctor_set(x_6, 0, x_24);
lean_ctor_set(x_15, 0, x_6);
x_25 = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__3___redArg(x_15, x_22);
lean_dec_ref(x_15);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_15, 0);
lean_inc(x_26);
lean_dec(x_15);
lean_ctor_set(x_6, 0, x_26);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_6);
x_28 = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__3___redArg(x_27, x_22);
lean_dec_ref(x_27);
return x_28;
}
}
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_6, 0);
lean_inc(x_29);
lean_dec(x_6);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_31 = lean_ctor_get(x_5, 1);
lean_inc(x_31);
lean_dec_ref(x_5);
x_32 = lean_ctor_get(x_30, 0);
lean_inc(x_32);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 x_33 = x_30;
} else {
 lean_dec_ref(x_30);
 x_33 = lean_box(0);
}
if (lean_is_scalar(x_33)) {
 x_34 = lean_alloc_ctor(0, 1, 0);
} else {
 x_34 = x_33;
}
lean_ctor_set(x_34, 0, x_32);
x_35 = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__3___redArg(x_34, x_31);
lean_dec_ref(x_34);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_36 = lean_ctor_get(x_5, 1);
lean_inc(x_36);
lean_dec_ref(x_5);
x_37 = lean_ctor_get(x_30, 0);
lean_inc(x_37);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 x_38 = x_30;
} else {
 lean_dec_ref(x_30);
 x_38 = lean_box(0);
}
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_37);
if (lean_is_scalar(x_38)) {
 x_40 = lean_alloc_ctor(1, 1, 0);
} else {
 x_40 = x_38;
}
lean_ctor_set(x_40, 0, x_39);
x_41 = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__3___redArg(x_40, x_36);
lean_dec_ref(x_40);
return x_41;
}
}
}
}
else
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_5);
if (x_42 == 0)
{
return x_5;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_5, 0);
x_44 = lean_ctor_get(x_5, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_5);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1___redArg___lam__1(x_1, x_2, x_3, x_4);
lean_dec_ref(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1___redArg___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_ResolveName_resolveNamespace(x_1, x_2, x_3, x_4);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1___redArg___lam__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1___redArg___lam__3(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_9; 
x_5 = 0;
x_6 = l_Lean_Environment_setExporting(x_1, x_5);
lean_inc(x_2);
x_7 = l_Lean_mkPrivateName(x_6, x_2);
x_8 = 1;
lean_inc_ref(x_6);
x_9 = l_Lean_Environment_contains(x_6, x_7, x_8);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; 
x_10 = l_Lean_privateToUserName(x_2);
x_11 = l_Lean_Environment_contains(x_6, x_10, x_8);
x_12 = lean_box(x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_4);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
lean_dec_ref(x_6);
lean_dec(x_2);
x_14 = lean_box(x_9);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_4);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1___redArg___lam__0(x_1, x_2, x_3, x_4);
lean_dec_ref(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__9_spec__13___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 2);
x_7 = lean_name_eq(x_4, x_1);
if (x_7 == 0)
{
x_2 = x_6;
goto _start;
}
else
{
lean_object* x_9; 
lean_inc(x_5);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_5);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__9_spec__13___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__9_spec__13___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__9___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint64_t x_5; uint64_t x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; size_t x_12; size_t x_13; size_t x_14; size_t x_15; size_t x_16; lean_object* x_17; lean_object* x_18; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
x_5 = l_Lean_Name_hash___override(x_2);
x_6 = 32;
x_7 = lean_uint64_shift_right(x_5, x_6);
x_8 = lean_uint64_xor(x_5, x_7);
x_9 = 16;
x_10 = lean_uint64_shift_right(x_8, x_9);
x_11 = lean_uint64_xor(x_8, x_10);
x_12 = lean_uint64_to_usize(x_11);
x_13 = lean_usize_of_nat(x_4);
x_14 = 1;
x_15 = lean_usize_sub(x_13, x_14);
x_16 = lean_usize_land(x_12, x_15);
x_17 = lean_array_uget(x_3, x_16);
x_18 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__9_spec__13___redArg(x_2, x_17);
lean_dec(x_17);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__9___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__9___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__1___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_4 = l_Lean_inheritedTraceOptions;
x_5 = lean_st_ref_get(x_4);
x_6 = lean_st_ref_get(x_2);
x_7 = lean_ctor_get(x_6, 2);
lean_inc(x_7);
lean_dec(x_6);
x_8 = l_Lean_Elab_Command_instInhabitedScope_default;
x_9 = l_List_head_x21___redArg(x_8, x_7);
lean_dec(x_7);
x_10 = lean_ctor_get(x_9, 1);
lean_inc_ref(x_10);
lean_dec(x_9);
x_11 = lean_ctor_get_uint8(x_10, sizeof(void*)*1);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec_ref(x_10);
lean_dec(x_5);
lean_dec(x_1);
x_12 = lean_box(x_11);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; 
x_14 = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__1___redArg___closed__0));
x_15 = l_Lean_Name_append(x_14, x_1);
x_16 = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(x_5, x_10, x_15);
lean_dec(x_15);
lean_dec_ref(x_10);
lean_dec(x_5);
x_17 = lean_box(x_16);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__1___redArg(x_1, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7_spec__10_spec__15_spec__21___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_1);
x_5 = lean_nat_dec_lt(x_2, x_4);
if (x_5 == 0)
{
lean_dec(x_2);
return x_5;
}
else
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_fget_borrowed(x_1, x_2);
x_7 = l_Lean_instBEqExtraModUse_beq(x_3, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_add(x_2, x_8);
lean_dec(x_2);
x_2 = x_9;
goto _start;
}
else
{
lean_dec(x_2);
return x_7;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7_spec__10_spec__15_spec__21___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7_spec__10_spec__15_spec__21___redArg(x_1, x_2, x_3);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7_spec__10_spec__15___redArg___closed__0() {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 5;
x_2 = 1;
x_3 = lean_usize_shift_left(x_2, x_1);
return x_3;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7_spec__10_spec__15___redArg___closed__1() {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 1;
x_2 = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7_spec__10_spec__15___redArg___closed__0;
x_3 = lean_usize_sub(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7_spec__10_spec__15___redArg(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; size_t x_6; size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_4);
lean_dec_ref(x_1);
x_5 = lean_box(2);
x_6 = 5;
x_7 = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7_spec__10_spec__15___redArg___closed__1;
x_8 = lean_usize_land(x_2, x_7);
x_9 = lean_usize_to_nat(x_8);
x_10 = lean_array_get(x_5, x_4, x_9);
lean_dec(x_9);
lean_dec_ref(x_4);
switch (lean_obj_tag(x_10)) {
case 0:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec_ref(x_10);
x_12 = l_Lean_instBEqExtraModUse_beq(x_3, x_11);
lean_dec(x_11);
return x_12;
}
case 1:
{
lean_object* x_13; size_t x_14; 
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
lean_dec_ref(x_10);
x_14 = lean_usize_shift_right(x_2, x_6);
x_1 = x_13;
x_2 = x_14;
goto _start;
}
default: 
{
uint8_t x_16; 
x_16 = 0;
return x_16;
}
}
}
else
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_17);
lean_dec_ref(x_1);
x_18 = lean_unsigned_to_nat(0u);
x_19 = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7_spec__10_spec__15_spec__21___redArg(x_17, x_18, x_3);
lean_dec_ref(x_17);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7_spec__10_spec__15___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7_spec__10_spec__15___redArg(x_1, x_4, x_3);
lean_dec_ref(x_3);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7_spec__10___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; size_t x_4; uint8_t x_5; 
x_3 = l_Lean_instHashableExtraModUse_hash(x_2);
x_4 = lean_uint64_to_usize(x_3);
x_5 = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7_spec__10_spec__15___redArg(x_1, x_4, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7_spec__10___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7_spec__10___redArg(x_1, x_2);
lean_dec_ref(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__2___closed__0() {
_start:
{
lean_object* x_1; double x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_float_of_nat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_Command_getRef___redArg(x_3);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec_ref(x_6);
x_8 = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__2_spec__4___redArg(x_2, x_4);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_st_ref_take(x_4);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_11, 9);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; double x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__2___closed__0;
x_17 = 0;
x_18 = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__3_spec__11_spec__17___closed__0));
x_19 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_19, 0, x_1);
lean_ctor_set(x_19, 1, x_18);
lean_ctor_set_float(x_19, sizeof(void*)*2, x_16);
lean_ctor_set_float(x_19, sizeof(void*)*2 + 8, x_16);
lean_ctor_set_uint8(x_19, sizeof(void*)*2 + 16, x_17);
x_20 = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__2___closed__1;
x_21 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_10);
lean_ctor_set(x_21, 2, x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_7);
lean_ctor_set(x_22, 1, x_21);
x_23 = l_Lean_PersistentArray_push___redArg(x_15, x_22);
lean_ctor_set(x_13, 0, x_23);
x_24 = lean_st_ref_set(x_4, x_11);
x_25 = lean_box(0);
lean_ctor_set(x_8, 0, x_25);
return x_8;
}
else
{
uint64_t x_26; lean_object* x_27; double x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_26 = lean_ctor_get_uint64(x_13, sizeof(void*)*1);
x_27 = lean_ctor_get(x_13, 0);
lean_inc(x_27);
lean_dec(x_13);
x_28 = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__2___closed__0;
x_29 = 0;
x_30 = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__3_spec__11_spec__17___closed__0));
x_31 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_31, 0, x_1);
lean_ctor_set(x_31, 1, x_30);
lean_ctor_set_float(x_31, sizeof(void*)*2, x_28);
lean_ctor_set_float(x_31, sizeof(void*)*2 + 8, x_28);
lean_ctor_set_uint8(x_31, sizeof(void*)*2 + 16, x_29);
x_32 = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__2___closed__1;
x_33 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_10);
lean_ctor_set(x_33, 2, x_32);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_7);
lean_ctor_set(x_34, 1, x_33);
x_35 = l_Lean_PersistentArray_push___redArg(x_27, x_34);
x_36 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set_uint64(x_36, sizeof(void*)*1, x_26);
lean_ctor_set(x_11, 9, x_36);
x_37 = lean_st_ref_set(x_4, x_11);
x_38 = lean_box(0);
lean_ctor_set(x_8, 0, x_38);
return x_8;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint64_t x_50; lean_object* x_51; lean_object* x_52; double x_53; uint8_t x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_39 = lean_ctor_get(x_11, 9);
x_40 = lean_ctor_get(x_11, 0);
x_41 = lean_ctor_get(x_11, 1);
x_42 = lean_ctor_get(x_11, 2);
x_43 = lean_ctor_get(x_11, 3);
x_44 = lean_ctor_get(x_11, 4);
x_45 = lean_ctor_get(x_11, 5);
x_46 = lean_ctor_get(x_11, 6);
x_47 = lean_ctor_get(x_11, 7);
x_48 = lean_ctor_get(x_11, 8);
x_49 = lean_ctor_get(x_11, 10);
lean_inc(x_49);
lean_inc(x_39);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_11);
x_50 = lean_ctor_get_uint64(x_39, sizeof(void*)*1);
x_51 = lean_ctor_get(x_39, 0);
lean_inc_ref(x_51);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 x_52 = x_39;
} else {
 lean_dec_ref(x_39);
 x_52 = lean_box(0);
}
x_53 = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__2___closed__0;
x_54 = 0;
x_55 = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__3_spec__11_spec__17___closed__0));
x_56 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_56, 0, x_1);
lean_ctor_set(x_56, 1, x_55);
lean_ctor_set_float(x_56, sizeof(void*)*2, x_53);
lean_ctor_set_float(x_56, sizeof(void*)*2 + 8, x_53);
lean_ctor_set_uint8(x_56, sizeof(void*)*2 + 16, x_54);
x_57 = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__2___closed__1;
x_58 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_10);
lean_ctor_set(x_58, 2, x_57);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_7);
lean_ctor_set(x_59, 1, x_58);
x_60 = l_Lean_PersistentArray_push___redArg(x_51, x_59);
if (lean_is_scalar(x_52)) {
 x_61 = lean_alloc_ctor(0, 1, 8);
} else {
 x_61 = x_52;
}
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set_uint64(x_61, sizeof(void*)*1, x_50);
x_62 = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(x_62, 0, x_40);
lean_ctor_set(x_62, 1, x_41);
lean_ctor_set(x_62, 2, x_42);
lean_ctor_set(x_62, 3, x_43);
lean_ctor_set(x_62, 4, x_44);
lean_ctor_set(x_62, 5, x_45);
lean_ctor_set(x_62, 6, x_46);
lean_ctor_set(x_62, 7, x_47);
lean_ctor_set(x_62, 8, x_48);
lean_ctor_set(x_62, 9, x_61);
lean_ctor_set(x_62, 10, x_49);
x_63 = lean_st_ref_set(x_4, x_62);
x_64 = lean_box(0);
lean_ctor_set(x_8, 0, x_64);
return x_8;
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; uint64_t x_79; lean_object* x_80; lean_object* x_81; double x_82; uint8_t x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_65 = lean_ctor_get(x_8, 0);
lean_inc(x_65);
lean_dec(x_8);
x_66 = lean_st_ref_take(x_4);
x_67 = lean_ctor_get(x_66, 9);
lean_inc_ref(x_67);
x_68 = lean_ctor_get(x_66, 0);
lean_inc_ref(x_68);
x_69 = lean_ctor_get(x_66, 1);
lean_inc_ref(x_69);
x_70 = lean_ctor_get(x_66, 2);
lean_inc(x_70);
x_71 = lean_ctor_get(x_66, 3);
lean_inc(x_71);
x_72 = lean_ctor_get(x_66, 4);
lean_inc(x_72);
x_73 = lean_ctor_get(x_66, 5);
lean_inc(x_73);
x_74 = lean_ctor_get(x_66, 6);
lean_inc_ref(x_74);
x_75 = lean_ctor_get(x_66, 7);
lean_inc_ref(x_75);
x_76 = lean_ctor_get(x_66, 8);
lean_inc_ref(x_76);
x_77 = lean_ctor_get(x_66, 10);
lean_inc_ref(x_77);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 lean_ctor_release(x_66, 1);
 lean_ctor_release(x_66, 2);
 lean_ctor_release(x_66, 3);
 lean_ctor_release(x_66, 4);
 lean_ctor_release(x_66, 5);
 lean_ctor_release(x_66, 6);
 lean_ctor_release(x_66, 7);
 lean_ctor_release(x_66, 8);
 lean_ctor_release(x_66, 9);
 lean_ctor_release(x_66, 10);
 x_78 = x_66;
} else {
 lean_dec_ref(x_66);
 x_78 = lean_box(0);
}
x_79 = lean_ctor_get_uint64(x_67, sizeof(void*)*1);
x_80 = lean_ctor_get(x_67, 0);
lean_inc_ref(x_80);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 x_81 = x_67;
} else {
 lean_dec_ref(x_67);
 x_81 = lean_box(0);
}
x_82 = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__2___closed__0;
x_83 = 0;
x_84 = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__3_spec__11_spec__17___closed__0));
x_85 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_85, 0, x_1);
lean_ctor_set(x_85, 1, x_84);
lean_ctor_set_float(x_85, sizeof(void*)*2, x_82);
lean_ctor_set_float(x_85, sizeof(void*)*2 + 8, x_82);
lean_ctor_set_uint8(x_85, sizeof(void*)*2 + 16, x_83);
x_86 = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__2___closed__1;
x_87 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_65);
lean_ctor_set(x_87, 2, x_86);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_7);
lean_ctor_set(x_88, 1, x_87);
x_89 = l_Lean_PersistentArray_push___redArg(x_80, x_88);
if (lean_is_scalar(x_81)) {
 x_90 = lean_alloc_ctor(0, 1, 8);
} else {
 x_90 = x_81;
}
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set_uint64(x_90, sizeof(void*)*1, x_79);
if (lean_is_scalar(x_78)) {
 x_91 = lean_alloc_ctor(0, 11, 0);
} else {
 x_91 = x_78;
}
lean_ctor_set(x_91, 0, x_68);
lean_ctor_set(x_91, 1, x_69);
lean_ctor_set(x_91, 2, x_70);
lean_ctor_set(x_91, 3, x_71);
lean_ctor_set(x_91, 4, x_72);
lean_ctor_set(x_91, 5, x_73);
lean_ctor_set(x_91, 6, x_74);
lean_ctor_set(x_91, 7, x_75);
lean_ctor_set(x_91, 8, x_76);
lean_ctor_set(x_91, 9, x_90);
lean_ctor_set(x_91, 10, x_77);
x_92 = lean_st_ref_set(x_4, x_91);
x_93 = lean_box(0);
x_94 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_94, 0, x_93);
return x_94;
}
}
else
{
uint8_t x_95; 
lean_dec_ref(x_2);
lean_dec(x_1);
x_95 = !lean_is_exclusive(x_6);
if (x_95 == 0)
{
return x_6;
}
else
{
lean_object* x_96; lean_object* x_97; 
x_96 = lean_ctor_get(x_6, 0);
lean_inc(x_96);
lean_dec(x_6);
x_97 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_97, 0, x_96);
return x_97;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__2(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_6;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___closed__1));
x_2 = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___closed__0));
x_3 = l_Lean_PersistentHashMap_empty(lean_box(0), lean_box(0), x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___closed__5));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___closed__7));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__3_spec__11_spec__17___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___closed__10));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___closed__12));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_46; uint8_t x_47; 
x_7 = lean_st_ref_get(x_5);
x_8 = lean_ctor_get(x_7, 0);
lean_inc_ref(x_8);
lean_dec(x_7);
x_9 = lean_ctor_get_uint8(x_8, sizeof(void*)*8);
lean_dec_ref(x_8);
x_10 = lean_st_ref_get(x_5);
x_11 = lean_ctor_get(x_10, 0);
lean_inc_ref(x_11);
lean_dec(x_10);
x_12 = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___closed__2;
lean_inc(x_1);
x_13 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_13, 0, x_1);
lean_ctor_set_uint8(x_13, sizeof(void*)*1, x_9);
lean_ctor_set_uint8(x_13, sizeof(void*)*1 + 1, x_2);
x_14 = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
x_15 = lean_box(1);
x_16 = lean_box(0);
x_46 = l_Lean_SimplePersistentEnvExtension_getState___redArg(x_12, x_14, x_11, x_15, x_16);
x_47 = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7_spec__10___redArg(x_46, x_13);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_56; lean_object* x_57; uint8_t x_70; 
x_48 = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___closed__4));
x_49 = l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__1___redArg(x_48, x_5);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
lean_dec_ref(x_49);
x_70 = lean_unbox(x_50);
lean_dec(x_50);
if (x_70 == 0)
{
lean_dec(x_3);
lean_dec(x_1);
x_17 = x_5;
x_18 = lean_box(0);
goto block_45;
}
else
{
lean_object* x_71; lean_object* x_72; 
x_71 = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___closed__11;
if (x_9 == 0)
{
lean_object* x_80; 
x_80 = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___closed__16));
x_72 = x_80;
goto block_79;
}
else
{
lean_object* x_81; 
x_81 = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___closed__17));
x_72 = x_81;
goto block_79;
}
block_79:
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_73 = l_Lean_stringToMessageData(x_72);
x_74 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_74, 0, x_71);
lean_ctor_set(x_74, 1, x_73);
x_75 = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___closed__13;
x_76 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
if (x_2 == 0)
{
lean_object* x_77; 
x_77 = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___closed__14));
x_56 = x_76;
x_57 = x_77;
goto block_69;
}
else
{
lean_object* x_78; 
x_78 = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___closed__15));
x_56 = x_76;
x_57 = x_78;
goto block_69;
}
}
}
block_55:
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
x_54 = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__2(x_48, x_53, x_4, x_5);
if (lean_obj_tag(x_54) == 0)
{
lean_dec_ref(x_54);
x_17 = x_5;
x_18 = lean_box(0);
goto block_45;
}
else
{
lean_dec_ref(x_13);
return x_54;
}
}
block_69:
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; 
x_58 = l_Lean_stringToMessageData(x_57);
x_59 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_59, 0, x_56);
lean_ctor_set(x_59, 1, x_58);
x_60 = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___closed__6;
x_61 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
x_62 = l_Lean_MessageData_ofName(x_1);
x_63 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
x_64 = l_Lean_Name_isAnonymous(x_3);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___closed__8;
x_66 = l_Lean_MessageData_ofName(x_3);
x_67 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
x_51 = x_63;
x_52 = x_67;
goto block_55;
}
else
{
lean_object* x_68; 
lean_dec(x_3);
x_68 = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___closed__9;
x_51 = x_63;
x_52 = x_68;
goto block_55;
}
}
}
else
{
lean_object* x_82; lean_object* x_83; 
lean_dec_ref(x_13);
lean_dec(x_3);
lean_dec(x_1);
x_82 = lean_box(0);
x_83 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_83, 0, x_82);
return x_83;
}
block_45:
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_st_ref_take(x_17);
x_20 = lean_ctor_get(x_14, 0);
lean_inc_ref(x_20);
x_21 = !lean_is_exclusive(x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_22 = lean_ctor_get(x_19, 0);
x_23 = lean_ctor_get(x_20, 2);
lean_inc(x_23);
lean_dec_ref(x_20);
x_24 = l_Lean_PersistentEnvExtension_addEntry___redArg(x_14, x_22, x_13, x_23, x_16);
lean_dec(x_23);
lean_ctor_set(x_19, 0, x_24);
x_25 = lean_st_ref_set(x_17, x_19);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_26);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_28 = lean_ctor_get(x_19, 0);
x_29 = lean_ctor_get(x_19, 1);
x_30 = lean_ctor_get(x_19, 2);
x_31 = lean_ctor_get(x_19, 3);
x_32 = lean_ctor_get(x_19, 4);
x_33 = lean_ctor_get(x_19, 5);
x_34 = lean_ctor_get(x_19, 6);
x_35 = lean_ctor_get(x_19, 7);
x_36 = lean_ctor_get(x_19, 8);
x_37 = lean_ctor_get(x_19, 9);
x_38 = lean_ctor_get(x_19, 10);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_19);
x_39 = lean_ctor_get(x_20, 2);
lean_inc(x_39);
lean_dec_ref(x_20);
x_40 = l_Lean_PersistentEnvExtension_addEntry___redArg(x_14, x_28, x_13, x_39, x_16);
lean_dec(x_39);
x_41 = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_29);
lean_ctor_set(x_41, 2, x_30);
lean_ctor_set(x_41, 3, x_31);
lean_ctor_set(x_41, 4, x_32);
lean_ctor_set(x_41, 5, x_33);
lean_ctor_set(x_41, 6, x_34);
lean_ctor_set(x_41, 7, x_35);
lean_ctor_set(x_41, 8, x_36);
lean_ctor_set(x_41, 9, x_37);
lean_ctor_set(x_41, 10, x_38);
x_42 = lean_st_ref_set(x_17, x_41);
x_43 = lean_box(0);
x_44 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_44, 0, x_43);
return x_44;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_2);
x_8 = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7(x_1, x_7, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_lt(x_5, x_4);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_2);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_6);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; 
x_12 = l_Lean_Environment_header(x_1);
x_13 = lean_ctor_get(x_12, 3);
lean_inc_ref(x_13);
lean_dec_ref(x_12);
x_14 = l_Lean_instInhabitedEffectiveImport_default;
x_15 = lean_array_uget(x_3, x_5);
x_16 = lean_array_get(x_14, x_13, x_15);
lean_dec(x_15);
lean_dec_ref(x_13);
x_17 = lean_ctor_get(x_16, 0);
lean_inc_ref(x_17);
lean_dec(x_16);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec_ref(x_17);
x_19 = 0;
lean_inc(x_2);
x_20 = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7(x_18, x_19, x_2, x_7, x_8);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; size_t x_22; size_t x_23; 
lean_dec_ref(x_20);
x_21 = lean_box(0);
x_22 = 1;
x_23 = lean_usize_add(x_5, x_22);
x_5 = x_23;
x_6 = x_21;
goto _start;
}
else
{
lean_dec(x_2);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_11 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_12 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__8(x_1, x_2, x_3, x_10, x_11, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_12;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4___closed__1));
x_2 = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4___closed__0));
x_3 = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_21; 
x_6 = lean_st_ref_get(x_4);
x_10 = lean_ctor_get(x_6, 0);
lean_inc_ref(x_10);
lean_dec(x_6);
x_21 = l_Lean_Environment_getModuleIdxFor_x3f(x_10, x_1);
if (lean_obj_tag(x_21) == 0)
{
lean_dec_ref(x_10);
lean_dec(x_1);
goto block_9;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec_ref(x_21);
x_23 = l_Lean_Environment_header(x_10);
x_24 = lean_ctor_get(x_23, 3);
lean_inc_ref(x_24);
lean_dec_ref(x_23);
x_25 = lean_array_get_size(x_24);
x_26 = lean_nat_dec_lt(x_22, x_25);
if (x_26 == 0)
{
lean_dec_ref(x_24);
lean_dec(x_22);
lean_dec_ref(x_10);
lean_dec(x_1);
goto block_9;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_27 = lean_st_ref_get(x_4);
x_28 = lean_ctor_get(x_27, 0);
lean_inc_ref(x_28);
lean_dec(x_27);
x_29 = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4___closed__2;
x_30 = lean_array_fget(x_24, x_22);
lean_dec(x_22);
lean_dec_ref(x_24);
if (x_2 == 0)
{
lean_dec_ref(x_28);
x_31 = x_2;
goto block_42;
}
else
{
uint8_t x_43; 
lean_inc(x_1);
x_43 = l_Lean_isMarkedMeta(x_28, x_1);
if (x_43 == 0)
{
x_31 = x_2;
goto block_42;
}
else
{
uint8_t x_44; 
x_44 = 0;
x_31 = x_44;
goto block_42;
}
}
block_42:
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_30, 0);
lean_inc_ref(x_32);
lean_dec(x_30);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
lean_dec_ref(x_32);
lean_inc(x_1);
x_34 = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7(x_33, x_31, x_1, x_3, x_4);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec_ref(x_34);
x_35 = l_Lean_indirectModUseExt;
x_36 = lean_box(1);
x_37 = lean_box(0);
lean_inc_ref(x_10);
x_38 = l_Lean_SimplePersistentEnvExtension_getState___redArg(x_29, x_35, x_10, x_36, x_37);
x_39 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__9___redArg(x_38, x_1);
lean_dec(x_38);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; 
x_40 = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4___closed__3;
x_11 = lean_box(0);
x_12 = x_40;
goto block_20;
}
else
{
lean_object* x_41; 
x_41 = lean_ctor_get(x_39, 0);
lean_inc(x_41);
lean_dec_ref(x_39);
x_11 = lean_box(0);
x_12 = x_41;
goto block_20;
}
}
else
{
lean_dec_ref(x_10);
lean_dec(x_1);
return x_34;
}
}
}
}
block_9:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
block_20:
{
lean_object* x_13; size_t x_14; size_t x_15; lean_object* x_16; 
x_13 = lean_box(0);
x_14 = lean_array_size(x_12);
x_15 = 0;
x_16 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__8(x_10, x_1, x_12, x_14, x_15, x_13, x_3, x_4);
lean_dec_ref(x_12);
lean_dec_ref(x_10);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_16, 0);
lean_dec(x_18);
lean_ctor_set(x_16, 0, x_13);
return x_16;
}
else
{
lean_object* x_19; 
lean_dec(x_16);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_13);
return x_19;
}
}
else
{
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
x_7 = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4(x_1, x_6, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__5___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_6; 
x_6 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_6, 0, x_2);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_dec_ref(x_1);
x_9 = 1;
x_10 = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4(x_7, x_9, x_3, x_4);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
lean_dec_ref(x_10);
x_11 = lean_box(0);
x_1 = x_8;
x_2 = x_11;
goto _start;
}
else
{
lean_dec(x_8);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__5___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__5___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_dec_ref(x_1);
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
lean_dec(x_7);
lean_inc(x_9);
x_11 = l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__1___redArg(x_9, x_3);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_unbox(x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_free_object(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_1 = x_8;
goto _start;
}
else
{
lean_object* x_16; lean_object* x_17; 
lean_ctor_set_tag(x_11, 3);
lean_ctor_set(x_11, 0, x_10);
x_16 = l_Lean_MessageData_ofFormat(x_11);
x_17 = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__2(x_9, x_16, x_2, x_3);
if (lean_obj_tag(x_17) == 0)
{
lean_dec_ref(x_17);
x_1 = x_8;
goto _start;
}
else
{
lean_dec(x_8);
return x_17;
}
}
}
else
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_11, 0);
lean_inc(x_19);
lean_dec(x_11);
x_20 = lean_unbox(x_19);
lean_dec(x_19);
if (x_20 == 0)
{
lean_dec(x_10);
lean_dec(x_9);
x_1 = x_8;
goto _start;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_22, 0, x_10);
x_23 = l_Lean_MessageData_ofFormat(x_22);
x_24 = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__2(x_9, x_23, x_2, x_3);
if (lean_obj_tag(x_24) == 0)
{
lean_dec_ref(x_24);
x_1 = x_8;
goto _start;
}
else
{
lean_dec(x_8);
return x_24;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__6(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__8___redArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_maxRecDepthErrorMessage;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__8___redArg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__8___redArg___closed__3;
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__8___redArg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__8___redArg___closed__4;
x_2 = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__8___redArg___closed__2));
x_3 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__8___redArg(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__8___redArg___closed__5;
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__8___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__8___redArg(x_1);
return x_3;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__7_spec__13_spec__18_spec__21___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(1);
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__7_spec__13_spec__18_spec__21___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__7_spec__13_spec__18_spec__21___closed__2));
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__7_spec__13_spec__18_spec__21(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_6 = lean_ctor_get(x_2, 1);
x_7 = lean_ctor_get(x_4, 0);
x_8 = lean_ctor_get(x_4, 1);
lean_dec(x_8);
x_9 = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__7_spec__13_spec__18_spec__21___closed__0;
lean_ctor_set_tag(x_4, 7);
lean_ctor_set(x_4, 1, x_9);
lean_ctor_set(x_4, 0, x_1);
x_10 = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__7_spec__13_spec__18_spec__21___closed__3;
lean_ctor_set_tag(x_2, 7);
lean_ctor_set(x_2, 1, x_10);
x_11 = l_Lean_MessageData_ofSyntax(x_7);
x_12 = l_Lean_indentD(x_11);
x_13 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_13, 0, x_2);
lean_ctor_set(x_13, 1, x_12);
x_1 = x_13;
x_2 = x_6;
goto _start;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_15 = lean_ctor_get(x_2, 1);
x_16 = lean_ctor_get(x_4, 0);
lean_inc(x_16);
lean_dec(x_4);
x_17 = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__7_spec__13_spec__18_spec__21___closed__0;
x_18 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_18, 0, x_1);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__7_spec__13_spec__18_spec__21___closed__3;
lean_ctor_set_tag(x_2, 7);
lean_ctor_set(x_2, 1, x_19);
lean_ctor_set(x_2, 0, x_18);
x_20 = l_Lean_MessageData_ofSyntax(x_16);
x_21 = l_Lean_indentD(x_20);
x_22 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_22, 0, x_2);
lean_ctor_set(x_22, 1, x_21);
x_1 = x_22;
x_2 = x_15;
goto _start;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_24 = lean_ctor_get(x_2, 0);
x_25 = lean_ctor_get(x_2, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_2);
x_26 = lean_ctor_get(x_24, 0);
lean_inc(x_26);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 x_27 = x_24;
} else {
 lean_dec_ref(x_24);
 x_27 = lean_box(0);
}
x_28 = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__7_spec__13_spec__18_spec__21___closed__0;
if (lean_is_scalar(x_27)) {
 x_29 = lean_alloc_ctor(7, 2, 0);
} else {
 x_29 = x_27;
 lean_ctor_set_tag(x_29, 7);
}
lean_ctor_set(x_29, 0, x_1);
lean_ctor_set(x_29, 1, x_28);
x_30 = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__7_spec__13_spec__18_spec__21___closed__3;
x_31 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_32 = l_Lean_MessageData_ofSyntax(x_26);
x_33 = l_Lean_indentD(x_32);
x_34 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_34, 0, x_31);
lean_ctor_set(x_34, 1, x_33);
x_1 = x_34;
x_2 = x_25;
goto _start;
}
}
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__7_spec__13_spec__18___redArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__7_spec__13_spec__18___redArg___closed__1));
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__7_spec__13_spec__18___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_5 = lean_st_ref_get(x_3);
x_6 = lean_ctor_get(x_5, 2);
lean_inc(x_6);
lean_dec(x_5);
x_7 = l_Lean_Elab_Command_instInhabitedScope_default;
x_8 = l_List_head_x21___redArg(x_7, x_6);
lean_dec(x_6);
x_9 = lean_ctor_get(x_8, 1);
lean_inc_ref(x_9);
lean_dec(x_8);
x_10 = l_Lean_Elab_pp_macroStack;
x_11 = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__3_spec__11_spec__17_spec__21(x_9, x_10);
lean_dec_ref(x_9);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_2);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_1);
return x_12;
}
else
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_1);
return x_13;
}
else
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_2, 0);
lean_inc(x_14);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_16 = lean_ctor_get(x_14, 1);
x_17 = lean_ctor_get(x_14, 0);
lean_dec(x_17);
x_18 = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__7_spec__13_spec__18_spec__21___closed__0;
lean_ctor_set_tag(x_14, 7);
lean_ctor_set(x_14, 1, x_18);
lean_ctor_set(x_14, 0, x_1);
x_19 = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__7_spec__13_spec__18___redArg___closed__2;
x_20 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_20, 0, x_14);
lean_ctor_set(x_20, 1, x_19);
x_21 = l_Lean_MessageData_ofSyntax(x_16);
x_22 = l_Lean_indentD(x_21);
x_23 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_23, 0, x_20);
lean_ctor_set(x_23, 1, x_22);
x_24 = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__7_spec__13_spec__18_spec__21(x_23, x_2);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_24);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_26 = lean_ctor_get(x_14, 1);
lean_inc(x_26);
lean_dec(x_14);
x_27 = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__7_spec__13_spec__18_spec__21___closed__0;
x_28 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_28, 0, x_1);
lean_ctor_set(x_28, 1, x_27);
x_29 = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__7_spec__13_spec__18___redArg___closed__2;
x_30 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = l_Lean_MessageData_ofSyntax(x_26);
x_32 = l_Lean_indentD(x_31);
x_33 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_33, 0, x_30);
lean_ctor_set(x_33, 1, x_32);
x_34 = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__7_spec__13_spec__18_spec__21(x_33, x_2);
x_35 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_35, 0, x_34);
return x_35;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__7_spec__13_spec__18___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__7_spec__13_spec__18___redArg(x_1, x_2, x_3);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__7_spec__13___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_getRef___redArg(x_2);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec_ref(x_5);
x_7 = lean_ctor_get(x_2, 4);
lean_inc(x_7);
lean_dec_ref(x_2);
x_8 = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__2_spec__4___redArg(x_1, x_3);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec_ref(x_8);
lean_inc(x_7);
x_10 = l_Lean_Elab_getBetterRef(x_6, x_7);
lean_dec(x_6);
x_11 = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__7_spec__13_spec__18___redArg(x_9, x_7, x_3);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_10);
lean_ctor_set(x_14, 1, x_13);
lean_ctor_set_tag(x_11, 1);
lean_ctor_set(x_11, 0, x_14);
return x_11;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_11, 0);
lean_inc(x_15);
lean_dec(x_11);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_10);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
}
else
{
uint8_t x_18; 
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_18 = !lean_is_exclusive(x_5);
if (x_18 == 0)
{
return x_5;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_5, 0);
lean_inc(x_19);
lean_dec(x_5);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__7_spec__13___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__7_spec__13___redArg(x_1, x_2, x_3);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__7___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_Command_getRef___redArg(x_3);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec_ref(x_6);
x_8 = !lean_is_exclusive(x_3);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_3, 7);
lean_dec(x_9);
x_10 = l_Lean_replaceRef(x_1, x_7);
lean_dec(x_7);
lean_ctor_set(x_3, 7, x_10);
x_11 = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__7_spec__13___redArg(x_2, x_3, x_4);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_12 = lean_ctor_get(x_3, 0);
x_13 = lean_ctor_get(x_3, 1);
x_14 = lean_ctor_get(x_3, 2);
x_15 = lean_ctor_get(x_3, 3);
x_16 = lean_ctor_get(x_3, 4);
x_17 = lean_ctor_get(x_3, 5);
x_18 = lean_ctor_get(x_3, 6);
x_19 = lean_ctor_get(x_3, 8);
x_20 = lean_ctor_get(x_3, 9);
x_21 = lean_ctor_get_uint8(x_3, sizeof(void*)*10);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_3);
x_22 = l_Lean_replaceRef(x_1, x_7);
lean_dec(x_7);
x_23 = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(x_23, 0, x_12);
lean_ctor_set(x_23, 1, x_13);
lean_ctor_set(x_23, 2, x_14);
lean_ctor_set(x_23, 3, x_15);
lean_ctor_set(x_23, 4, x_16);
lean_ctor_set(x_23, 5, x_17);
lean_ctor_set(x_23, 6, x_18);
lean_ctor_set(x_23, 7, x_22);
lean_ctor_set(x_23, 8, x_19);
lean_ctor_set(x_23, 9, x_20);
lean_ctor_set_uint8(x_23, sizeof(void*)*10, x_21);
x_24 = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__7_spec__13___redArg(x_2, x_23, x_4);
return x_24;
}
}
else
{
uint8_t x_25; 
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_25 = !lean_is_exclusive(x_6);
if (x_25 == 0)
{
return x_6;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_6, 0);
lean_inc(x_26);
lean_dec(x_6);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_26);
return x_27;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__7___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__7___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1___redArg___lam__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_ResolveName_resolveGlobalName(x_1, x_2, x_3, x_4, x_5);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1___redArg___lam__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1___redArg___lam__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1___redArg___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1___redArg___lam__2(x_1, x_2, x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_5 = lean_st_ref_get(x_3);
x_6 = lean_ctor_get(x_5, 0);
lean_inc_ref(x_6);
lean_dec(x_5);
x_7 = lean_st_ref_get(x_3);
x_8 = lean_ctor_get(x_7, 2);
lean_inc(x_8);
lean_dec(x_7);
x_9 = l_Lean_Elab_Command_instInhabitedScope_default;
x_10 = l_List_head_x21___redArg(x_9, x_8);
lean_dec(x_8);
x_11 = lean_ctor_get(x_10, 1);
lean_inc_ref(x_11);
lean_dec(x_10);
x_12 = l_Lean_Elab_Command_getScope___redArg(x_3);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec_ref(x_12);
x_14 = lean_ctor_get(x_13, 2);
lean_inc(x_14);
lean_dec(x_13);
x_15 = l_Lean_Elab_Command_getScope___redArg(x_3);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec_ref(x_15);
x_17 = lean_ctor_get(x_16, 3);
lean_inc(x_17);
lean_dec(x_16);
x_18 = l_Lean_Elab_Command_getRef___redArg(x_2);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec_ref(x_18);
x_20 = l_Lean_Elab_Command_getCurrMacroScope___redArg(x_2);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec_ref(x_20);
x_22 = lean_ctor_get(x_2, 2);
x_23 = lean_ctor_get(x_2, 5);
lean_inc_ref(x_6);
x_24 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1___redArg___lam__0___boxed), 4, 1);
lean_closure_set(x_24, 0, x_6);
lean_inc_ref(x_6);
x_25 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1___redArg___lam__1___boxed), 4, 1);
lean_closure_set(x_25, 0, x_6);
lean_inc(x_14);
x_26 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1___redArg___lam__2___boxed), 3, 1);
lean_closure_set(x_26, 0, x_14);
lean_inc(x_17);
lean_inc(x_14);
lean_inc_ref(x_6);
x_27 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1___redArg___lam__3___boxed), 6, 3);
lean_closure_set(x_27, 0, x_6);
lean_closure_set(x_27, 1, x_14);
lean_closure_set(x_27, 2, x_17);
x_28 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1___redArg___lam__4___boxed), 7, 4);
lean_closure_set(x_28, 0, x_6);
lean_closure_set(x_28, 1, x_11);
lean_closure_set(x_28, 2, x_14);
lean_closure_set(x_28, 3, x_17);
x_29 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_29, 0, x_25);
lean_ctor_set(x_29, 1, x_26);
lean_ctor_set(x_29, 2, x_24);
lean_ctor_set(x_29, 3, x_27);
lean_ctor_set(x_29, 4, x_28);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_92; lean_object* x_93; 
x_92 = l_Lean_getMainModule___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__2___redArg(x_3);
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
lean_dec_ref(x_92);
x_30 = x_93;
x_31 = lean_box(0);
goto block_91;
}
else
{
lean_object* x_94; 
x_94 = lean_ctor_get(x_23, 0);
lean_inc(x_94);
x_30 = x_94;
x_31 = lean_box(0);
goto block_91;
}
block_91:
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_32 = lean_st_ref_get(x_3);
x_33 = lean_ctor_get(x_32, 5);
lean_inc(x_33);
lean_dec(x_32);
x_34 = lean_st_ref_get(x_3);
x_35 = lean_ctor_get(x_34, 4);
lean_inc(x_35);
lean_dec(x_34);
lean_inc(x_22);
x_36 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_36, 0, x_29);
lean_ctor_set(x_36, 1, x_30);
lean_ctor_set(x_36, 2, x_21);
lean_ctor_set(x_36, 3, x_22);
lean_ctor_set(x_36, 4, x_33);
lean_ctor_set(x_36, 5, x_19);
x_37 = lean_box(0);
x_38 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_38, 0, x_35);
lean_ctor_set(x_38, 1, x_37);
lean_ctor_set(x_38, 2, x_37);
x_39 = lean_apply_2(x_1, x_36, x_38);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 0);
lean_inc(x_41);
lean_dec_ref(x_39);
x_42 = lean_ctor_get(x_40, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_40, 1);
lean_inc(x_43);
x_44 = lean_ctor_get(x_40, 2);
lean_inc(x_44);
lean_dec(x_40);
x_45 = lean_box(0);
x_46 = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__5___redArg(x_44, x_45, x_2, x_3);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; uint8_t x_48; 
lean_dec_ref(x_46);
x_47 = lean_st_ref_take(x_3);
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_49 = lean_ctor_get(x_47, 4);
lean_dec(x_49);
lean_ctor_set(x_47, 4, x_42);
x_50 = lean_st_ref_set(x_3, x_47);
x_51 = l_List_reverse___redArg(x_43);
x_52 = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__6(x_51, x_2, x_3);
lean_dec_ref(x_2);
if (lean_obj_tag(x_52) == 0)
{
uint8_t x_53; 
x_53 = !lean_is_exclusive(x_52);
if (x_53 == 0)
{
lean_object* x_54; 
x_54 = lean_ctor_get(x_52, 0);
lean_dec(x_54);
lean_ctor_set(x_52, 0, x_41);
return x_52;
}
else
{
lean_object* x_55; 
lean_dec(x_52);
x_55 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_55, 0, x_41);
return x_55;
}
}
else
{
uint8_t x_56; 
lean_dec(x_41);
x_56 = !lean_is_exclusive(x_52);
if (x_56 == 0)
{
return x_52;
}
else
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_52, 0);
lean_inc(x_57);
lean_dec(x_52);
x_58 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_58, 0, x_57);
return x_58;
}
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_59 = lean_ctor_get(x_47, 0);
x_60 = lean_ctor_get(x_47, 1);
x_61 = lean_ctor_get(x_47, 2);
x_62 = lean_ctor_get(x_47, 3);
x_63 = lean_ctor_get(x_47, 5);
x_64 = lean_ctor_get(x_47, 6);
x_65 = lean_ctor_get(x_47, 7);
x_66 = lean_ctor_get(x_47, 8);
x_67 = lean_ctor_get(x_47, 9);
x_68 = lean_ctor_get(x_47, 10);
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_47);
x_69 = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(x_69, 0, x_59);
lean_ctor_set(x_69, 1, x_60);
lean_ctor_set(x_69, 2, x_61);
lean_ctor_set(x_69, 3, x_62);
lean_ctor_set(x_69, 4, x_42);
lean_ctor_set(x_69, 5, x_63);
lean_ctor_set(x_69, 6, x_64);
lean_ctor_set(x_69, 7, x_65);
lean_ctor_set(x_69, 8, x_66);
lean_ctor_set(x_69, 9, x_67);
lean_ctor_set(x_69, 10, x_68);
x_70 = lean_st_ref_set(x_3, x_69);
x_71 = l_List_reverse___redArg(x_43);
x_72 = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__6(x_71, x_2, x_3);
lean_dec_ref(x_2);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; 
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 x_73 = x_72;
} else {
 lean_dec_ref(x_72);
 x_73 = lean_box(0);
}
if (lean_is_scalar(x_73)) {
 x_74 = lean_alloc_ctor(0, 1, 0);
} else {
 x_74 = x_73;
}
lean_ctor_set(x_74, 0, x_41);
return x_74;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_dec(x_41);
x_75 = lean_ctor_get(x_72, 0);
lean_inc(x_75);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 x_76 = x_72;
} else {
 lean_dec_ref(x_72);
 x_76 = lean_box(0);
}
if (lean_is_scalar(x_76)) {
 x_77 = lean_alloc_ctor(1, 1, 0);
} else {
 x_77 = x_76;
}
lean_ctor_set(x_77, 0, x_75);
return x_77;
}
}
}
else
{
uint8_t x_78; 
lean_dec(x_43);
lean_dec(x_42);
lean_dec(x_41);
lean_dec_ref(x_2);
x_78 = !lean_is_exclusive(x_46);
if (x_78 == 0)
{
return x_46;
}
else
{
lean_object* x_79; lean_object* x_80; 
x_79 = lean_ctor_get(x_46, 0);
lean_inc(x_79);
lean_dec(x_46);
x_80 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_80, 0, x_79);
return x_80;
}
}
}
else
{
lean_object* x_81; 
x_81 = lean_ctor_get(x_39, 0);
lean_inc(x_81);
lean_dec_ref(x_39);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc_ref(x_83);
lean_dec_ref(x_81);
x_84 = ((lean_object*)(l_Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1___redArg___closed__0));
x_85 = lean_string_dec_eq(x_83, x_84);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_86, 0, x_83);
x_87 = l_Lean_MessageData_ofFormat(x_86);
x_88 = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__7___redArg(x_82, x_87, x_2, x_3);
lean_dec(x_82);
return x_88;
}
else
{
lean_object* x_89; 
lean_dec_ref(x_83);
lean_dec_ref(x_2);
x_89 = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__8___redArg(x_82);
return x_89;
}
}
else
{
lean_object* x_90; 
lean_dec_ref(x_2);
x_90 = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__0___redArg();
return x_90;
}
}
}
}
else
{
uint8_t x_95; 
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_14);
lean_dec_ref(x_11);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_95 = !lean_is_exclusive(x_20);
if (x_95 == 0)
{
return x_20;
}
else
{
lean_object* x_96; lean_object* x_97; 
x_96 = lean_ctor_get(x_20, 0);
lean_inc(x_96);
lean_dec(x_20);
x_97 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_97, 0, x_96);
return x_97;
}
}
}
else
{
uint8_t x_98; 
lean_dec(x_17);
lean_dec(x_14);
lean_dec_ref(x_11);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_98 = !lean_is_exclusive(x_18);
if (x_98 == 0)
{
return x_18;
}
else
{
lean_object* x_99; lean_object* x_100; 
x_99 = lean_ctor_get(x_18, 0);
lean_inc(x_99);
lean_dec(x_18);
x_100 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_100, 0, x_99);
return x_100;
}
}
}
else
{
uint8_t x_101; 
lean_dec(x_14);
lean_dec_ref(x_11);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_101 = !lean_is_exclusive(x_15);
if (x_101 == 0)
{
return x_15;
}
else
{
lean_object* x_102; lean_object* x_103; 
x_102 = lean_ctor_get(x_15, 0);
lean_inc(x_102);
lean_dec(x_15);
x_103 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_103, 0, x_102);
return x_103;
}
}
}
else
{
uint8_t x_104; 
lean_dec_ref(x_11);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_104 = !lean_is_exclusive(x_12);
if (x_104 == 0)
{
return x_12;
}
else
{
lean_object* x_105; lean_object* x_106; 
x_105 = lean_ctor_get(x_12, 0);
lean_inc(x_105);
lean_dec(x_12);
x_106 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_106, 0, x_105);
return x_106;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1___redArg(x_1, x_2, x_3);
lean_dec(x_3);
return x_5;
}
}
static lean_object* _init_l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = l_Array_mkArray0(lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__22));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__26() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_LibrarySuggestions_initFn___closed__1_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2_));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__34() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__35() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__34;
x_2 = ((lean_object*)(l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__9));
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__36() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__43() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__42));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__61() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__60));
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_elabSetLibrarySuggestions(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = ((lean_object*)(l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__1));
lean_inc(x_1);
x_6 = l_Lean_Syntax_isOfKind(x_1, x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_7 = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__0___redArg();
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; uint8_t x_120; 
x_8 = lean_st_ref_get(x_3);
x_9 = lean_ctor_get(x_8, 0);
lean_inc_ref(x_9);
lean_dec(x_8);
x_10 = lean_unsigned_to_nat(1u);
x_11 = l_Lean_Syntax_getArg(x_1, x_10);
lean_dec(x_1);
x_116 = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4___closed__0));
x_117 = ((lean_object*)(l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__58));
x_118 = l_Lean_Environment_header(x_9);
lean_dec_ref(x_9);
x_119 = l_Lean_EnvironmentHeader_moduleNames(x_118);
x_120 = l_Array_contains___redArg(x_116, x_119, x_117);
if (x_120 == 0)
{
if (x_6 == 0)
{
x_90 = x_2;
x_91 = x_3;
x_92 = lean_box(0);
goto block_115;
}
else
{
lean_object* x_121; lean_object* x_122; 
x_121 = l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__61;
lean_inc_ref(x_2);
x_122 = l_Lean_logWarning___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__3(x_121, x_2, x_3);
if (lean_obj_tag(x_122) == 0)
{
lean_dec_ref(x_122);
x_90 = x_2;
x_91 = x_3;
x_92 = lean_box(0);
goto block_115;
}
else
{
lean_dec(x_11);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_122;
}
}
}
else
{
x_90 = x_2;
x_91 = x_3;
x_92 = lean_box(0);
goto block_115;
}
block_89:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_19 = ((lean_object*)(l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__5));
x_20 = ((lean_object*)(l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__7));
x_21 = ((lean_object*)(l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__9));
x_22 = l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__10;
lean_inc(x_14);
x_23 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_23, 0, x_14);
lean_ctor_set(x_23, 1, x_21);
lean_ctor_set(x_23, 2, x_22);
x_24 = ((lean_object*)(l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__13));
x_25 = ((lean_object*)(l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__14));
lean_inc(x_14);
x_26 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_26, 0, x_14);
lean_ctor_set(x_26, 1, x_25);
x_27 = ((lean_object*)(l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__16));
x_28 = ((lean_object*)(l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__18));
lean_inc_ref(x_23);
lean_inc(x_14);
x_29 = l_Lean_Syntax_node1(x_14, x_28, x_23);
x_30 = ((lean_object*)(l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__21));
x_31 = l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__23;
x_32 = ((lean_object*)(l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__24));
lean_inc(x_13);
lean_inc(x_17);
x_33 = l_Lean_addMacroScope(x_17, x_32, x_13);
x_34 = lean_box(0);
lean_inc(x_14);
x_35 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_35, 0, x_14);
lean_ctor_set(x_35, 1, x_31);
lean_ctor_set(x_35, 2, x_33);
lean_ctor_set(x_35, 3, x_34);
lean_inc_ref(x_23);
lean_inc(x_14);
x_36 = l_Lean_Syntax_node2(x_14, x_30, x_35, x_23);
lean_inc(x_29);
lean_inc(x_14);
x_37 = l_Lean_Syntax_node2(x_14, x_27, x_29, x_36);
x_38 = ((lean_object*)(l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__25));
lean_inc(x_14);
x_39 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_39, 0, x_14);
lean_ctor_set(x_39, 1, x_38);
x_40 = l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__26;
x_41 = ((lean_object*)(l_Lean_LibrarySuggestions_initFn___closed__2_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2_));
lean_inc(x_13);
lean_inc(x_17);
x_42 = l_Lean_addMacroScope(x_17, x_41, x_13);
lean_inc(x_14);
x_43 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_43, 0, x_14);
lean_ctor_set(x_43, 1, x_40);
lean_ctor_set(x_43, 2, x_42);
lean_ctor_set(x_43, 3, x_34);
lean_inc_ref(x_23);
lean_inc(x_14);
x_44 = l_Lean_Syntax_node2(x_14, x_30, x_43, x_23);
lean_inc(x_14);
x_45 = l_Lean_Syntax_node2(x_14, x_27, x_29, x_44);
lean_inc(x_14);
x_46 = l_Lean_Syntax_node3(x_14, x_21, x_37, x_39, x_45);
x_47 = ((lean_object*)(l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__27));
lean_inc(x_14);
x_48 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_48, 0, x_14);
lean_ctor_set(x_48, 1, x_47);
lean_inc(x_14);
x_49 = l_Lean_Syntax_node3(x_14, x_24, x_26, x_46, x_48);
lean_inc(x_14);
x_50 = l_Lean_Syntax_node1(x_14, x_21, x_49);
x_51 = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___closed__17));
x_52 = ((lean_object*)(l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__28));
lean_inc(x_14);
x_53 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_53, 0, x_14);
lean_ctor_set(x_53, 1, x_51);
lean_inc(x_14);
x_54 = l_Lean_Syntax_node1(x_14, x_52, x_53);
lean_inc(x_14);
x_55 = l_Lean_Syntax_node1(x_14, x_21, x_54);
lean_inc_ref_n(x_23, 5);
lean_inc(x_14);
x_56 = l_Lean_Syntax_node7(x_14, x_20, x_23, x_50, x_55, x_23, x_23, x_23, x_23);
x_57 = ((lean_object*)(l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__30));
x_58 = ((lean_object*)(l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__31));
lean_inc(x_14);
x_59 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_59, 0, x_14);
lean_ctor_set(x_59, 1, x_58);
x_60 = ((lean_object*)(l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__33));
x_61 = lean_mk_syntax_ident(x_16);
x_62 = lean_box(2);
x_63 = l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__35;
x_64 = l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__36;
x_65 = lean_array_push(x_64, x_61);
x_66 = lean_array_push(x_65, x_63);
x_67 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_67, 0, x_62);
lean_ctor_set(x_67, 1, x_60);
lean_ctor_set(x_67, 2, x_66);
x_68 = ((lean_object*)(l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__38));
x_69 = ((lean_object*)(l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__40));
x_70 = ((lean_object*)(l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__41));
lean_inc(x_14);
x_71 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_71, 0, x_14);
lean_ctor_set(x_71, 1, x_70);
x_72 = l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__43;
x_73 = ((lean_object*)(l_Lean_LibrarySuggestions_initFn___lam__0___closed__4_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2_));
x_74 = l_Lean_addMacroScope(x_17, x_73, x_13);
x_75 = ((lean_object*)(l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__47));
lean_inc(x_14);
x_76 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_76, 0, x_14);
lean_ctor_set(x_76, 1, x_72);
lean_ctor_set(x_76, 2, x_74);
lean_ctor_set(x_76, 3, x_75);
lean_inc(x_14);
x_77 = l_Lean_Syntax_node2(x_14, x_69, x_71, x_76);
lean_inc(x_14);
x_78 = l_Lean_Syntax_node1(x_14, x_21, x_77);
lean_inc_ref(x_23);
lean_inc(x_14);
x_79 = l_Lean_Syntax_node2(x_14, x_68, x_23, x_78);
x_80 = ((lean_object*)(l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__49));
x_81 = ((lean_object*)(l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__50));
lean_inc(x_14);
x_82 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_82, 0, x_14);
lean_ctor_set(x_82, 1, x_81);
x_83 = ((lean_object*)(l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__53));
lean_inc_ref_n(x_23, 2);
lean_inc(x_14);
x_84 = l_Lean_Syntax_node2(x_14, x_83, x_23, x_23);
lean_inc_ref(x_23);
lean_inc(x_14);
x_85 = l_Lean_Syntax_node4(x_14, x_80, x_82, x_11, x_84, x_23);
lean_inc(x_14);
x_86 = l_Lean_Syntax_node5(x_14, x_57, x_59, x_67, x_79, x_85, x_23);
x_87 = l_Lean_Syntax_node2(x_14, x_19, x_56, x_86);
x_88 = l_Lean_Elab_Command_elabCommand(x_87, x_15, x_12);
return x_88;
}
block_115:
{
lean_object* x_93; lean_object* x_94; 
x_93 = ((lean_object*)(l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__56));
lean_inc_ref(x_90);
x_94 = l_Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1___redArg(x_93, x_90, x_91);
if (lean_obj_tag(x_94) == 0)
{
lean_object* x_95; lean_object* x_96; 
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
lean_dec_ref(x_94);
x_96 = l_Lean_Elab_Command_getRef___redArg(x_90);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_97; lean_object* x_98; 
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
lean_dec_ref(x_96);
x_98 = l_Lean_Elab_Command_getCurrMacroScope___redArg(x_90);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; lean_object* x_100; uint8_t x_101; lean_object* x_102; 
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
lean_dec_ref(x_98);
x_100 = lean_ctor_get(x_90, 5);
x_101 = 0;
x_102 = l_Lean_SourceInfo_fromRef(x_97, x_101);
lean_dec(x_97);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_103; lean_object* x_104; 
x_103 = l_Lean_getMainModule___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__2___redArg(x_91);
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
lean_dec_ref(x_103);
x_12 = x_91;
x_13 = x_99;
x_14 = x_102;
x_15 = x_90;
x_16 = x_95;
x_17 = x_104;
x_18 = lean_box(0);
goto block_89;
}
else
{
lean_object* x_105; 
x_105 = lean_ctor_get(x_100, 0);
lean_inc(x_105);
x_12 = x_91;
x_13 = x_99;
x_14 = x_102;
x_15 = x_90;
x_16 = x_95;
x_17 = x_105;
x_18 = lean_box(0);
goto block_89;
}
}
else
{
uint8_t x_106; 
lean_dec(x_97);
lean_dec(x_95);
lean_dec(x_91);
lean_dec_ref(x_90);
lean_dec(x_11);
x_106 = !lean_is_exclusive(x_98);
if (x_106 == 0)
{
return x_98;
}
else
{
lean_object* x_107; lean_object* x_108; 
x_107 = lean_ctor_get(x_98, 0);
lean_inc(x_107);
lean_dec(x_98);
x_108 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_108, 0, x_107);
return x_108;
}
}
}
else
{
uint8_t x_109; 
lean_dec(x_95);
lean_dec(x_91);
lean_dec_ref(x_90);
lean_dec(x_11);
x_109 = !lean_is_exclusive(x_96);
if (x_109 == 0)
{
return x_96;
}
else
{
lean_object* x_110; lean_object* x_111; 
x_110 = lean_ctor_get(x_96, 0);
lean_inc(x_110);
lean_dec(x_96);
x_111 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_111, 0, x_110);
return x_111;
}
}
}
else
{
uint8_t x_112; 
lean_dec(x_91);
lean_dec_ref(x_90);
lean_dec(x_11);
x_112 = !lean_is_exclusive(x_94);
if (x_112 == 0)
{
return x_94;
}
else
{
lean_object* x_113; lean_object* x_114; 
x_113 = lean_ctor_get(x_94, 0);
lean_inc(x_113);
lean_dec(x_94);
x_114 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_114, 0, x_113);
return x_114;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_LibrarySuggestions_elabSetLibrarySuggestions(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__1___redArg(x_1, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__1(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__3___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__3(x_1, x_2, x_3, x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__8___redArg(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__8(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1___redArg(x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__2_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__2_spec__4___redArg(x_1, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__2_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__2_spec__4(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__5___redArg(x_2, x_3, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__5(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__7___redArg(x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__7(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__9___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__9(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__7_spec__13(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__7_spec__13___redArg(x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__7_spec__13___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__7_spec__13(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7_spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7_spec__10___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7_spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7_spec__10(x_1, x_2, x_3);
lean_dec_ref(x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__9_spec__13(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__9_spec__13___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__9_spec__13___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__9_spec__13(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__7_spec__13_spec__18(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__7_spec__13_spec__18___redArg(x_1, x_2, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__7_spec__13_spec__18___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__7_spec__13_spec__18(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7_spec__10_spec__15(lean_object* x_1, lean_object* x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7_spec__10_spec__15___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7_spec__10_spec__15___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7_spec__10_spec__15(x_1, x_2, x_5, x_4);
lean_dec_ref(x_4);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7_spec__10_spec__15_spec__21(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7_spec__10_spec__15_spec__21___redArg(x_2, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7_spec__10_spec__15_spec__21___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7_spec__10_spec__15_spec__21(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___regBuiltin_Lean_LibrarySuggestions_elabSetLibrarySuggestions__1() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_Command_commandElabAttribute;
x_3 = ((lean_object*)(l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__1));
x_4 = ((lean_object*)(l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___regBuiltin_Lean_LibrarySuggestions_elabSetLibrarySuggestions__1___closed__1));
x_5 = lean_alloc_closure((void*)(l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___boxed), 4, 0);
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___regBuiltin_Lean_LibrarySuggestions_elabSetLibrarySuggestions__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___regBuiltin_Lean_LibrarySuggestions_elabSetLibrarySuggestions__1();
return x_2;
}
}
static double _init_l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_LibrarySuggestions_evalSuggestions_spec__2___closed__0() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; double x_4; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = 1;
x_3 = lean_unsigned_to_nat(10u);
x_4 = l_Float_ofScientific(x_3, x_2, x_1);
return x_4;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_LibrarySuggestions_evalSuggestions_spec__2(lean_object* x_1, size_t x_2, size_t x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_eq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; double x_6; uint8_t x_7; double x_8; uint8_t x_9; 
x_5 = lean_array_uget(x_1, x_2);
x_6 = lean_ctor_get_float(x_5, sizeof(void*)*2);
lean_dec(x_5);
x_7 = 1;
x_8 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_LibrarySuggestions_evalSuggestions_spec__2___closed__0;
x_9 = lean_float_beq(x_6, x_8);
if (x_9 == 0)
{
return x_7;
}
else
{
if (x_4 == 0)
{
size_t x_10; size_t x_11; 
x_10 = 1;
x_11 = lean_usize_add(x_2, x_10);
x_2 = x_11;
goto _start;
}
else
{
return x_7;
}
}
}
else
{
uint8_t x_13; 
x_13 = 0;
return x_13;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_LibrarySuggestions_evalSuggestions_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; uint8_t x_6; lean_object* x_7; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_LibrarySuggestions_evalSuggestions_spec__2(x_1, x_4, x_5);
lean_dec_ref(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_LibrarySuggestions_evalSuggestions_spec__1_spec__1_spec__2___lam__0(uint8_t x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 1)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_3, 0);
switch (lean_obj_tag(x_4)) {
case 1:
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_4, 0);
switch (lean_obj_tag(x_5)) {
case 0:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_ctor_get(x_4, 1);
x_8 = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_LibrarySuggestions_evalSuggestions_spec__1_spec__1_spec__2___lam__0___closed__0));
x_9 = lean_string_dec_eq(x_7, x_8);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = ((lean_object*)(l_Lean_LibrarySuggestions_initFn___closed__8_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2_));
x_11 = lean_string_dec_eq(x_7, x_10);
if (x_11 == 0)
{
return x_1;
}
else
{
lean_object* x_12; uint8_t x_13; 
x_12 = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_LibrarySuggestions_evalSuggestions_spec__1_spec__1_spec__2___lam__0___closed__1));
x_13 = lean_string_dec_eq(x_6, x_12);
if (x_13 == 0)
{
return x_1;
}
else
{
return x_2;
}
}
}
else
{
lean_object* x_14; uint8_t x_15; 
x_14 = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_LibrarySuggestions_evalSuggestions_spec__1_spec__1_spec__2___lam__0___closed__2));
x_15 = lean_string_dec_eq(x_6, x_14);
if (x_15 == 0)
{
return x_1;
}
else
{
return x_2;
}
}
}
case 1:
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_5, 0);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_17 = lean_ctor_get(x_3, 1);
x_18 = lean_ctor_get(x_4, 1);
x_19 = lean_ctor_get(x_5, 1);
x_20 = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_LibrarySuggestions_evalSuggestions_spec__1_spec__1_spec__2___lam__0___closed__3));
x_21 = lean_string_dec_eq(x_19, x_20);
if (x_21 == 0)
{
return x_1;
}
else
{
lean_object* x_22; uint8_t x_23; 
x_22 = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_LibrarySuggestions_evalSuggestions_spec__1_spec__1_spec__2___lam__0___closed__4));
x_23 = lean_string_dec_eq(x_18, x_22);
if (x_23 == 0)
{
return x_1;
}
else
{
lean_object* x_24; uint8_t x_25; 
x_24 = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_LibrarySuggestions_evalSuggestions_spec__1_spec__1_spec__2___lam__0___closed__5));
x_25 = lean_string_dec_eq(x_17, x_24);
if (x_25 == 0)
{
return x_1;
}
else
{
return x_2;
}
}
}
}
else
{
return x_1;
}
}
default: 
{
return x_1;
}
}
}
case 0:
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_3, 1);
x_27 = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__3_spec__11_spec__17___lam__0___closed__0));
x_28 = lean_string_dec_eq(x_26, x_27);
if (x_28 == 0)
{
return x_1;
}
else
{
return x_2;
}
}
default: 
{
return x_1;
}
}
}
else
{
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_LibrarySuggestions_evalSuggestions_spec__1_spec__1_spec__2___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_4 = lean_unbox(x_1);
x_5 = lean_unbox(x_2);
x_6 = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_LibrarySuggestions_evalSuggestions_spec__1_spec__1_spec__2___lam__0(x_4, x_5, x_3);
lean_dec(x_3);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_LibrarySuggestions_evalSuggestions_spec__1_spec__1_spec__2(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_50; uint8_t x_51; uint8_t x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; lean_object* x_56; lean_object* x_57; lean_object* x_77; uint8_t x_78; lean_object* x_79; uint8_t x_80; uint8_t x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_88; uint8_t x_89; lean_object* x_90; lean_object* x_91; uint8_t x_92; lean_object* x_93; uint8_t x_94; uint8_t x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; lean_object* x_104; lean_object* x_105; uint8_t x_106; uint8_t x_107; uint8_t x_109; uint8_t x_125; 
x_100 = 2;
x_125 = l_Lean_instBEqMessageSeverity_beq(x_3, x_100);
if (x_125 == 0)
{
x_109 = x_125;
goto block_124;
}
else
{
uint8_t x_126; 
lean_inc_ref(x_2);
x_126 = l_Lean_MessageData_hasSyntheticSorry(x_2);
x_109 = x_126;
goto block_124;
}
block_49:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_20 = lean_st_ref_take(x_18);
x_21 = lean_ctor_get(x_17, 6);
lean_inc(x_21);
x_22 = lean_ctor_get(x_17, 7);
lean_inc(x_22);
lean_dec_ref(x_17);
x_23 = !lean_is_exclusive(x_20);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_24 = lean_ctor_get(x_20, 6);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_21);
lean_ctor_set(x_25, 1, x_22);
x_26 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_16);
x_27 = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(x_27, 0, x_13);
lean_ctor_set(x_27, 1, x_15);
lean_ctor_set(x_27, 2, x_14);
lean_ctor_set(x_27, 3, x_11);
lean_ctor_set(x_27, 4, x_26);
lean_ctor_set_uint8(x_27, sizeof(void*)*5, x_12);
lean_ctor_set_uint8(x_27, sizeof(void*)*5 + 1, x_10);
lean_ctor_set_uint8(x_27, sizeof(void*)*5 + 2, x_4);
x_28 = l_Lean_MessageLog_add(x_27, x_24);
lean_ctor_set(x_20, 6, x_28);
x_29 = lean_st_ref_set(x_18, x_20);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_31, 0, x_30);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_32 = lean_ctor_get(x_20, 0);
x_33 = lean_ctor_get(x_20, 1);
x_34 = lean_ctor_get(x_20, 2);
x_35 = lean_ctor_get(x_20, 3);
x_36 = lean_ctor_get(x_20, 4);
x_37 = lean_ctor_get(x_20, 5);
x_38 = lean_ctor_get(x_20, 6);
x_39 = lean_ctor_get(x_20, 7);
x_40 = lean_ctor_get(x_20, 8);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_20);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_21);
lean_ctor_set(x_41, 1, x_22);
x_42 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_16);
x_43 = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(x_43, 0, x_13);
lean_ctor_set(x_43, 1, x_15);
lean_ctor_set(x_43, 2, x_14);
lean_ctor_set(x_43, 3, x_11);
lean_ctor_set(x_43, 4, x_42);
lean_ctor_set_uint8(x_43, sizeof(void*)*5, x_12);
lean_ctor_set_uint8(x_43, sizeof(void*)*5 + 1, x_10);
lean_ctor_set_uint8(x_43, sizeof(void*)*5 + 2, x_4);
x_44 = l_Lean_MessageLog_add(x_43, x_38);
x_45 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_45, 0, x_32);
lean_ctor_set(x_45, 1, x_33);
lean_ctor_set(x_45, 2, x_34);
lean_ctor_set(x_45, 3, x_35);
lean_ctor_set(x_45, 4, x_36);
lean_ctor_set(x_45, 5, x_37);
lean_ctor_set(x_45, 6, x_44);
lean_ctor_set(x_45, 7, x_39);
lean_ctor_set(x_45, 8, x_40);
x_46 = lean_st_ref_set(x_18, x_45);
x_47 = lean_box(0);
x_48 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_48, 0, x_47);
return x_48;
}
}
block_76:
{
lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_58 = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(x_2);
x_59 = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_LibrarySuggestions_getSelectorImpl_spec__0_spec__0_spec__1_spec__3(x_58, x_5, x_6, x_7, x_8);
x_60 = !lean_is_exclusive(x_59);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_61 = lean_ctor_get(x_59, 0);
lean_inc_ref(x_53);
x_62 = l_Lean_FileMap_toPosition(x_53, x_56);
lean_dec(x_56);
x_63 = l_Lean_FileMap_toPosition(x_53, x_57);
lean_dec(x_57);
x_64 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_64, 0, x_63);
x_65 = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__3_spec__11_spec__17___closed__0));
if (x_52 == 0)
{
lean_free_object(x_59);
lean_dec_ref(x_50);
x_10 = x_51;
x_11 = x_65;
x_12 = x_55;
x_13 = x_54;
x_14 = x_64;
x_15 = x_62;
x_16 = x_61;
x_17 = x_7;
x_18 = x_8;
x_19 = lean_box(0);
goto block_49;
}
else
{
uint8_t x_66; 
lean_inc(x_61);
x_66 = l_Lean_MessageData_hasTag(x_50, x_61);
if (x_66 == 0)
{
lean_object* x_67; 
lean_dec_ref(x_64);
lean_dec_ref(x_62);
lean_dec(x_61);
lean_dec_ref(x_54);
lean_dec_ref(x_7);
x_67 = lean_box(0);
lean_ctor_set(x_59, 0, x_67);
return x_59;
}
else
{
lean_free_object(x_59);
x_10 = x_51;
x_11 = x_65;
x_12 = x_55;
x_13 = x_54;
x_14 = x_64;
x_15 = x_62;
x_16 = x_61;
x_17 = x_7;
x_18 = x_8;
x_19 = lean_box(0);
goto block_49;
}
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_68 = lean_ctor_get(x_59, 0);
lean_inc(x_68);
lean_dec(x_59);
lean_inc_ref(x_53);
x_69 = l_Lean_FileMap_toPosition(x_53, x_56);
lean_dec(x_56);
x_70 = l_Lean_FileMap_toPosition(x_53, x_57);
lean_dec(x_57);
x_71 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_71, 0, x_70);
x_72 = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__3_spec__11_spec__17___closed__0));
if (x_52 == 0)
{
lean_dec_ref(x_50);
x_10 = x_51;
x_11 = x_72;
x_12 = x_55;
x_13 = x_54;
x_14 = x_71;
x_15 = x_69;
x_16 = x_68;
x_17 = x_7;
x_18 = x_8;
x_19 = lean_box(0);
goto block_49;
}
else
{
uint8_t x_73; 
lean_inc(x_68);
x_73 = l_Lean_MessageData_hasTag(x_50, x_68);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; 
lean_dec_ref(x_71);
lean_dec_ref(x_69);
lean_dec(x_68);
lean_dec_ref(x_54);
lean_dec_ref(x_7);
x_74 = lean_box(0);
x_75 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_75, 0, x_74);
return x_75;
}
else
{
x_10 = x_51;
x_11 = x_72;
x_12 = x_55;
x_13 = x_54;
x_14 = x_71;
x_15 = x_69;
x_16 = x_68;
x_17 = x_7;
x_18 = x_8;
x_19 = lean_box(0);
goto block_49;
}
}
}
}
block_87:
{
lean_object* x_85; 
x_85 = l_Lean_Syntax_getTailPos_x3f(x_83, x_81);
lean_dec(x_83);
if (lean_obj_tag(x_85) == 0)
{
lean_inc(x_84);
x_50 = x_77;
x_51 = x_78;
x_52 = x_80;
x_53 = x_79;
x_54 = x_82;
x_55 = x_81;
x_56 = x_84;
x_57 = x_84;
goto block_76;
}
else
{
lean_object* x_86; 
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
lean_dec_ref(x_85);
x_50 = x_77;
x_51 = x_78;
x_52 = x_80;
x_53 = x_79;
x_54 = x_82;
x_55 = x_81;
x_56 = x_84;
x_57 = x_86;
goto block_76;
}
}
block_99:
{
lean_object* x_95; lean_object* x_96; 
x_95 = l_Lean_replaceRef(x_1, x_93);
lean_dec(x_93);
x_96 = l_Lean_Syntax_getPos_x3f(x_95, x_92);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_97; 
x_97 = lean_unsigned_to_nat(0u);
x_77 = x_88;
x_78 = x_94;
x_79 = x_90;
x_80 = x_89;
x_81 = x_92;
x_82 = x_91;
x_83 = x_95;
x_84 = x_97;
goto block_87;
}
else
{
lean_object* x_98; 
x_98 = lean_ctor_get(x_96, 0);
lean_inc(x_98);
lean_dec_ref(x_96);
x_77 = x_88;
x_78 = x_94;
x_79 = x_90;
x_80 = x_89;
x_81 = x_92;
x_82 = x_91;
x_83 = x_95;
x_84 = x_98;
goto block_87;
}
}
block_108:
{
if (x_107 == 0)
{
x_88 = x_101;
x_89 = x_103;
x_90 = x_102;
x_91 = x_104;
x_92 = x_106;
x_93 = x_105;
x_94 = x_3;
goto block_99;
}
else
{
x_88 = x_101;
x_89 = x_103;
x_90 = x_102;
x_91 = x_104;
x_92 = x_106;
x_93 = x_105;
x_94 = x_100;
goto block_99;
}
}
block_124:
{
if (x_109 == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; uint8_t x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; uint8_t x_118; uint8_t x_119; 
x_110 = lean_ctor_get(x_7, 0);
x_111 = lean_ctor_get(x_7, 1);
x_112 = lean_ctor_get(x_7, 2);
x_113 = lean_ctor_get(x_7, 5);
x_114 = lean_ctor_get_uint8(x_7, sizeof(void*)*14 + 1);
x_115 = lean_box(x_109);
x_116 = lean_box(x_114);
x_117 = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_LibrarySuggestions_evalSuggestions_spec__1_spec__1_spec__2___lam__0___boxed), 3, 2);
lean_closure_set(x_117, 0, x_115);
lean_closure_set(x_117, 1, x_116);
x_118 = 1;
x_119 = l_Lean_instBEqMessageSeverity_beq(x_3, x_118);
if (x_119 == 0)
{
lean_inc(x_113);
lean_inc_ref(x_110);
lean_inc_ref(x_111);
x_101 = x_117;
x_102 = x_111;
x_103 = x_114;
x_104 = x_110;
x_105 = x_113;
x_106 = x_109;
x_107 = x_119;
goto block_108;
}
else
{
lean_object* x_120; uint8_t x_121; 
x_120 = l_Lean_warningAsError;
x_121 = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__3_spec__11_spec__17_spec__21(x_112, x_120);
lean_inc(x_113);
lean_inc_ref(x_110);
lean_inc_ref(x_111);
x_101 = x_117;
x_102 = x_111;
x_103 = x_114;
x_104 = x_110;
x_105 = x_113;
x_106 = x_109;
x_107 = x_121;
goto block_108;
}
}
else
{
lean_object* x_122; lean_object* x_123; 
lean_dec_ref(x_7);
lean_dec_ref(x_2);
x_122 = lean_box(0);
x_123 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_123, 0, x_122);
return x_123;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_LibrarySuggestions_evalSuggestions_spec__1_spec__1_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; uint8_t x_11; lean_object* x_12; 
x_10 = lean_unbox(x_3);
x_11 = lean_unbox(x_4);
x_12 = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_LibrarySuggestions_evalSuggestions_spec__1_spec__1_spec__2(x_1, x_2, x_10, x_11, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logInfo___at___00Lean_LibrarySuggestions_evalSuggestions_spec__1_spec__1(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_6, 5);
lean_inc(x_9);
x_10 = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_LibrarySuggestions_evalSuggestions_spec__1_spec__1_spec__2(x_9, x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logInfo___at___00Lean_LibrarySuggestions_evalSuggestions_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; uint8_t x_10; lean_object* x_11; 
x_9 = lean_unbox(x_2);
x_10 = lean_unbox(x_3);
x_11 = l_Lean_log___at___00Lean_logInfo___at___00Lean_LibrarySuggestions_evalSuggestions_spec__1_spec__1(x_1, x_9, x_10, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfo___at___00Lean_LibrarySuggestions_evalSuggestions_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_7; uint8_t x_8; lean_object* x_9; 
x_7 = 0;
x_8 = 0;
x_9 = l_Lean_log___at___00Lean_logInfo___at___00Lean_LibrarySuggestions_evalSuggestions_spec__1_spec__1(x_1, x_7, x_8, x_2, x_3, x_4, x_5);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfo___at___00Lean_LibrarySuggestions_evalSuggestions_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_logInfo___at___00Lean_LibrarySuggestions_evalSuggestions_spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_LibrarySuggestions_evalSuggestions_spec__0___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_LibrarySuggestions_evalSuggestions_spec__0___redArg___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_LibrarySuggestions_evalSuggestions_spec__0___redArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__27));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_LibrarySuggestions_evalSuggestions_spec__0___redArg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_LibrarySuggestions_evalSuggestions_spec__0___redArg___closed__4));
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_LibrarySuggestions_evalSuggestions_spec__0___redArg___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_LibrarySuggestions_evalSuggestions_spec__0___redArg___closed__6));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_LibrarySuggestions_evalSuggestions_spec__0___redArg___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_LibrarySuggestions_evalSuggestions_spec__0___redArg___closed__8));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_LibrarySuggestions_evalSuggestions_spec__0___redArg(uint8_t x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_13; 
x_13 = lean_usize_dec_lt(x_4, x_3);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_5);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_27; double x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; 
x_15 = lean_array_uget(x_2, x_4);
x_27 = lean_ctor_get(x_15, 0);
lean_inc(x_27);
x_28 = lean_ctor_get_float(x_15, sizeof(void*)*2);
x_29 = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__7_spec__13_spec__18_spec__21___closed__0;
x_30 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_30, 0, x_5);
lean_ctor_set(x_30, 1, x_29);
x_31 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_LibrarySuggestions_evalSuggestions_spec__0___redArg___closed__5;
x_32 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
x_33 = 0;
x_34 = l_Lean_MessageData_ofConstName(x_27, x_33);
x_35 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_35, 0, x_32);
lean_ctor_set(x_35, 1, x_34);
if (x_1 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_36 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_LibrarySuggestions_evalSuggestions_spec__0___redArg___closed__7;
x_37 = lean_float_to_string(x_28);
x_38 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_38, 0, x_37);
x_39 = l_Lean_MessageData_ofFormat(x_38);
x_40 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_40, 0, x_36);
lean_ctor_set(x_40, 1, x_39);
x_41 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_LibrarySuggestions_evalSuggestions_spec__0___redArg___closed__9;
x_42 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_43, 0, x_35);
lean_ctor_set(x_43, 1, x_42);
x_16 = x_43;
x_17 = lean_box(0);
goto block_26;
}
else
{
x_16 = x_35;
x_17 = lean_box(0);
goto block_26;
}
block_26:
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
if (lean_obj_tag(x_18) == 1)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec_ref(x_18);
x_20 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_LibrarySuggestions_evalSuggestions_spec__0___redArg___closed__1;
x_21 = l_Lean_stringToMessageData(x_19);
x_22 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_LibrarySuggestions_evalSuggestions_spec__0___redArg___closed__2;
x_24 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_25, 0, x_16);
lean_ctor_set(x_25, 1, x_24);
x_7 = x_25;
x_8 = lean_box(0);
goto block_12;
}
else
{
lean_dec(x_18);
x_7 = x_16;
x_8 = lean_box(0);
goto block_12;
}
}
}
block_12:
{
size_t x_9; size_t x_10; 
x_9 = 1;
x_10 = lean_usize_add(x_4, x_9);
x_4 = x_10;
x_5 = x_7;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_LibrarySuggestions_evalSuggestions_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; size_t x_8; size_t x_9; lean_object* x_10; 
x_7 = lean_unbox(x_1);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_10 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_LibrarySuggestions_evalSuggestions_spec__0___redArg(x_7, x_2, x_8, x_9, x_5);
lean_dec_ref(x_2);
return x_10;
}
}
static lean_object* _init_l_Lean_LibrarySuggestions_evalSuggestions___redArg___lam__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_LibrarySuggestions_evalSuggestions___redArg___lam__1___closed__1));
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_evalSuggestions___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_getMainGoal___redArg(x_3, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec_ref(x_11);
x_13 = lean_unsigned_to_nat(100u);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
lean_ctor_set(x_15, 2, x_1);
lean_ctor_set(x_15, 3, x_14);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_12);
x_16 = l_Lean_LibrarySuggestions_select(x_12, x_15, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec_ref(x_16);
x_18 = l_Lean_LibrarySuggestions_evalSuggestions___redArg___lam__1___closed__2;
x_32 = lean_unsigned_to_nat(0u);
x_33 = lean_array_get_size(x_17);
x_34 = lean_nat_dec_lt(x_32, x_33);
if (x_34 == 0)
{
uint8_t x_35; 
x_35 = 1;
x_19 = x_35;
goto block_31;
}
else
{
if (x_34 == 0)
{
x_19 = x_34;
goto block_31;
}
else
{
size_t x_36; size_t x_37; uint8_t x_38; 
x_36 = 0;
x_37 = lean_usize_of_nat(x_33);
x_38 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_LibrarySuggestions_evalSuggestions_spec__2(x_17, x_36, x_37);
if (x_38 == 0)
{
x_19 = x_34;
goto block_31;
}
else
{
uint8_t x_39; 
x_39 = 0;
x_19 = x_39;
goto block_31;
}
}
}
block_31:
{
size_t x_20; size_t x_21; lean_object* x_22; 
x_20 = lean_array_size(x_17);
x_21 = 0;
x_22 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_LibrarySuggestions_evalSuggestions_spec__0___redArg(x_19, x_17, x_20, x_21, x_18);
lean_dec(x_17);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec_ref(x_22);
lean_inc_ref(x_8);
x_24 = l_Lean_logInfo___at___00Lean_LibrarySuggestions_evalSuggestions_spec__1(x_23, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec_ref(x_24);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_12);
lean_ctor_set(x_26, 1, x_25);
x_27 = l_Lean_Elab_Tactic_replaceMainGoal___redArg(x_26, x_3, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
return x_27;
}
else
{
lean_dec(x_12);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
return x_24;
}
}
else
{
uint8_t x_28; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_28 = !lean_is_exclusive(x_22);
if (x_28 == 0)
{
return x_22;
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_22, 0);
lean_inc(x_29);
lean_dec(x_22);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_29);
return x_30;
}
}
}
}
else
{
uint8_t x_40; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_40 = !lean_is_exclusive(x_16);
if (x_40 == 0)
{
return x_16;
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_16, 0);
lean_inc(x_41);
lean_dec(x_16);
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_41);
return x_42;
}
}
}
else
{
uint8_t x_43; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_1);
x_43 = !lean_is_exclusive(x_11);
if (x_43 == 0)
{
return x_11;
}
else
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_11, 0);
lean_inc(x_44);
lean_dec(x_11);
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_44);
return x_45;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_evalSuggestions___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_LibrarySuggestions_evalSuggestions___redArg___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_evalSuggestions___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = ((lean_object*)(l_Lean_LibrarySuggestions_evalSuggestions___redArg___closed__0));
x_11 = l_Lean_Elab_Tactic_withMainContext___redArg(x_10, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_evalSuggestions___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_LibrarySuggestions_evalSuggestions___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_evalSuggestions(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_LibrarySuggestions_evalSuggestions___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_evalSuggestions___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_LibrarySuggestions_evalSuggestions(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_LibrarySuggestions_evalSuggestions_spec__0(uint8_t x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_LibrarySuggestions_evalSuggestions_spec__0___redArg(x_1, x_2, x_3, x_4, x_5);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_LibrarySuggestions_evalSuggestions_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; size_t x_12; size_t x_13; lean_object* x_14; 
x_11 = lean_unbox(x_1);
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_14 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_LibrarySuggestions_evalSuggestions_spec__0(x_11, x_2, x_12, x_13, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_evalSuggestions___regBuiltin_Lean_LibrarySuggestions_evalSuggestions__1() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_Tactic_tacticElabAttribute;
x_3 = ((lean_object*)(l_Lean_LibrarySuggestions_evalSuggestions___regBuiltin_Lean_LibrarySuggestions_evalSuggestions__1___closed__1));
x_4 = ((lean_object*)(l_Lean_LibrarySuggestions_evalSuggestions___regBuiltin_Lean_LibrarySuggestions_evalSuggestions__1___closed__3));
x_5 = lean_alloc_closure((void*)(l_Lean_LibrarySuggestions_evalSuggestions___boxed), 10, 0);
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_LibrarySuggestions_evalSuggestions___regBuiltin_Lean_LibrarySuggestions_evalSuggestions__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_LibrarySuggestions_evalSuggestions___regBuiltin_Lean_LibrarySuggestions_evalSuggestions__1();
return x_2;
}
}
lean_object* initialize_Lean_Elab_Command(uint8_t builtin);
lean_object* initialize_Lean_Meta_Eval(uint8_t builtin);
lean_object* initialize_Lean_Meta_CompletionName(uint8_t builtin);
lean_object* initialize_Lean_Linter_Deprecated(uint8_t builtin);
lean_object* initialize_Init_Data_Random(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_Grind_Annotated(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_LibrarySuggestions_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Command(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Eval(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_CompletionName(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Linter_Deprecated(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Random(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Grind_Annotated(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_foldUnsafe___redArg___closed__0 = _init_l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_foldUnsafe___redArg___closed__0();
lean_mark_persistent(l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_foldUnsafe___redArg___closed__0);
l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_foldUnsafe___redArg___closed__1 = _init_l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_foldUnsafe___redArg___closed__1();
lean_mark_persistent(l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_foldUnsafe___redArg___closed__1);
l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_foldUnsafe___redArg___closed__2 = _init_l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_foldUnsafe___redArg___closed__2();
lean_mark_persistent(l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_foldUnsafe___redArg___closed__2);
l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_foldUnsafe___redArg___closed__3 = _init_l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_foldUnsafe___redArg___closed__3();
lean_mark_persistent(l___private_Lean_LibrarySuggestions_Basic_0__Lean_Expr_FoldRelevantConstantsImpl_foldUnsafe___redArg___closed__3);
l_Lean_Expr_relevantConstants___closed__1 = _init_l_Lean_Expr_relevantConstants___closed__1();
lean_mark_persistent(l_Lean_Expr_relevantConstants___closed__1);
l_Lean_getLocalHyps___at___00Lean_MVarId_getConstants_spec__0___closed__0 = _init_l_Lean_getLocalHyps___at___00Lean_MVarId_getConstants_spec__0___closed__0();
lean_mark_persistent(l_Lean_getLocalHyps___at___00Lean_MVarId_getConstants_spec__0___closed__0);
l_Lean_LibrarySuggestions_Selector_postFilter___closed__1 = _init_l_Lean_LibrarySuggestions_Selector_postFilter___closed__1();
lean_mark_persistent(l_Lean_LibrarySuggestions_Selector_postFilter___closed__1);
l_Lean_LibrarySuggestions_Selector_combine___closed__0 = _init_l_Lean_LibrarySuggestions_Selector_combine___closed__0();
lean_mark_persistent(l_Lean_LibrarySuggestions_Selector_combine___closed__0);
l_Lean_LibrarySuggestions_Selector_combine___closed__1 = _init_l_Lean_LibrarySuggestions_Selector_combine___closed__1();
lean_mark_persistent(l_Lean_LibrarySuggestions_Selector_combine___closed__1);
l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_LibrarySuggestions_Selector_intersperse_spec__0___redArg___closed__0 = _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_LibrarySuggestions_Selector_intersperse_spec__0___redArg___closed__0();
l_Lean_LibrarySuggestions_Selector_intersperse___closed__0 = _init_l_Lean_LibrarySuggestions_Selector_intersperse___closed__0();
l_Lean_LibrarySuggestions_Selector_intersperse___closed__1 = _init_l_Lean_LibrarySuggestions_Selector_intersperse___closed__1();
lean_mark_persistent(l_Lean_LibrarySuggestions_Selector_intersperse___closed__1);
l_Lean_LibrarySuggestions_Selector_intersperse___closed__2 = _init_l_Lean_LibrarySuggestions_Selector_intersperse___closed__2();
lean_mark_persistent(l_Lean_LibrarySuggestions_Selector_intersperse___closed__2);
l_Lean_LibrarySuggestions_Selector_intersperse___closed__3___boxed__const__1 = _init_l_Lean_LibrarySuggestions_Selector_intersperse___closed__3___boxed__const__1();
lean_mark_persistent(l_Lean_LibrarySuggestions_Selector_intersperse___closed__3___boxed__const__1);
l_Lean_LibrarySuggestions_Selector_intersperse___closed__3 = _init_l_Lean_LibrarySuggestions_Selector_intersperse___closed__3();
lean_mark_persistent(l_Lean_LibrarySuggestions_Selector_intersperse___closed__3);
l_Lean_LibrarySuggestions_Selector_intersperse___closed__4___boxed__const__1 = _init_l_Lean_LibrarySuggestions_Selector_intersperse___closed__4___boxed__const__1();
lean_mark_persistent(l_Lean_LibrarySuggestions_Selector_intersperse___closed__4___boxed__const__1);
l_Lean_LibrarySuggestions_Selector_intersperse___closed__4 = _init_l_Lean_LibrarySuggestions_Selector_intersperse___closed__4();
lean_mark_persistent(l_Lean_LibrarySuggestions_Selector_intersperse___closed__4);
if (builtin) {res = l_Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_2108197918____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_LibrarySuggestions_moduleDenyListExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_LibrarySuggestions_moduleDenyListExt);
lean_dec_ref(res);
}if (builtin) {res = l_Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_611429871____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_LibrarySuggestions_nameDenyListExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_LibrarySuggestions_nameDenyListExt);
lean_dec_ref(res);
}if (builtin) {res = l_Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3406067637____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_LibrarySuggestions_typePrefixDenyListExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_LibrarySuggestions_typePrefixDenyListExt);
lean_dec_ref(res);
}if (builtin) {res = l_Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_2654663577____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_LibrarySuggestions_librarySuggestionsExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_LibrarySuggestions_librarySuggestionsExt);
lean_dec_ref(res);
}l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__1_spec__2___closed__0 = _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__1_spec__2___closed__0();
lean_mark_persistent(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__1_spec__2___closed__0);
l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__1_spec__2___closed__1 = _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__1_spec__2___closed__1();
lean_mark_persistent(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__1_spec__2___closed__1);
l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__1_spec__2___closed__2 = _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__1_spec__2___closed__2();
lean_mark_persistent(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__1_spec__2___closed__2);
l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__1_spec__2___closed__3 = _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__1_spec__2___closed__3();
lean_mark_persistent(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__1_spec__2___closed__3);
l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__1_spec__2___closed__4 = _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__1_spec__2___closed__4();
lean_mark_persistent(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__1_spec__2___closed__4);
l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__1_spec__2___closed__5 = _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__1_spec__2___closed__5();
lean_mark_persistent(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__1_spec__2___closed__5);
l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__1_spec__2___closed__6 = _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__1_spec__2___closed__6();
lean_mark_persistent(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__1_spec__2___closed__6);
l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1 = _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1();
lean_mark_persistent(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1);
l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3 = _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3();
lean_mark_persistent(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3);
l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5 = _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5();
lean_mark_persistent(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5);
l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7 = _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7();
lean_mark_persistent(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7);
l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9 = _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9();
lean_mark_persistent(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9);
l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11 = _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11();
lean_mark_persistent(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11);
l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13 = _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13();
lean_mark_persistent(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13);
l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__1 = _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__1();
lean_mark_persistent(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__1);
l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__3 = _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__3();
lean_mark_persistent(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__3);
l_Lean_LibrarySuggestions_initFn___lam__0___closed__0_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2_ = _init_l_Lean_LibrarySuggestions_initFn___lam__0___closed__0_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2_();
lean_mark_persistent(l_Lean_LibrarySuggestions_initFn___lam__0___closed__0_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2_);
l_Lean_LibrarySuggestions_initFn___lam__0___closed__1_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2_ = _init_l_Lean_LibrarySuggestions_initFn___lam__0___closed__1_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2_();
lean_mark_persistent(l_Lean_LibrarySuggestions_initFn___lam__0___closed__1_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2_);
l_Lean_LibrarySuggestions_initFn___lam__0___closed__2_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2_ = _init_l_Lean_LibrarySuggestions_initFn___lam__0___closed__2_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2_();
lean_mark_persistent(l_Lean_LibrarySuggestions_initFn___lam__0___closed__2_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2_);
l_Lean_LibrarySuggestions_initFn___lam__0___closed__5_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2_ = _init_l_Lean_LibrarySuggestions_initFn___lam__0___closed__5_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2_();
lean_mark_persistent(l_Lean_LibrarySuggestions_initFn___lam__0___closed__5_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2_);
l_Lean_LibrarySuggestions_initFn___lam__0___closed__7_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2_ = _init_l_Lean_LibrarySuggestions_initFn___lam__0___closed__7_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2_();
lean_mark_persistent(l_Lean_LibrarySuggestions_initFn___lam__0___closed__7_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2_);
l_Lean_LibrarySuggestions_initFn___lam__0___closed__9_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2_ = _init_l_Lean_LibrarySuggestions_initFn___lam__0___closed__9_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2_();
lean_mark_persistent(l_Lean_LibrarySuggestions_initFn___lam__0___closed__9_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2_);
if (builtin) {res = l_Lean_LibrarySuggestions_initFn_00___x40_Lean_LibrarySuggestions_Basic_3716816319____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_LibrarySuggestions_librarySuggestionsAttr = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_LibrarySuggestions_librarySuggestionsAttr);
lean_dec_ref(res);
}l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00Lean_LibrarySuggestions_getSelectorImpl_spec__0_spec__1___redArg___closed__0 = _init_l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00Lean_LibrarySuggestions_getSelectorImpl_spec__0_spec__1___redArg___closed__0();
lean_mark_persistent(l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00Lean_LibrarySuggestions_getSelectorImpl_spec__0_spec__1___redArg___closed__0);
l_Lean_LibrarySuggestions_select___closed__1 = _init_l_Lean_LibrarySuggestions_select___closed__1();
lean_mark_persistent(l_Lean_LibrarySuggestions_select___closed__1);
l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__0___redArg___closed__0 = _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__0___redArg___closed__0();
lean_mark_persistent(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__0___redArg___closed__0);
l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7_spec__10_spec__15___redArg___closed__0 = _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7_spec__10_spec__15___redArg___closed__0();
l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7_spec__10_spec__15___redArg___closed__1 = _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7_spec__10_spec__15___redArg___closed__1();
l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__2___closed__0 = _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__2___closed__0();
l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__2___closed__1 = _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__2___closed__1();
lean_mark_persistent(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__2___closed__1);
l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___closed__2 = _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___closed__2();
lean_mark_persistent(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___closed__2);
l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___closed__6 = _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___closed__6();
lean_mark_persistent(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___closed__6);
l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___closed__8 = _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___closed__8();
lean_mark_persistent(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___closed__8);
l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___closed__9 = _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___closed__9();
lean_mark_persistent(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___closed__9);
l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___closed__11 = _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___closed__11();
lean_mark_persistent(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___closed__11);
l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___closed__13 = _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___closed__13();
lean_mark_persistent(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4_spec__7___closed__13);
l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4___closed__2 = _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4___closed__2();
lean_mark_persistent(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4___closed__2);
l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4___closed__3 = _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4___closed__3();
lean_mark_persistent(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__4___closed__3);
l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__8___redArg___closed__3 = _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__8___redArg___closed__3();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__8___redArg___closed__3);
l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__8___redArg___closed__4 = _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__8___redArg___closed__4();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__8___redArg___closed__4);
l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__8___redArg___closed__5 = _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__8___redArg___closed__5();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__8___redArg___closed__5);
l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__7_spec__13_spec__18_spec__21___closed__0 = _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__7_spec__13_spec__18_spec__21___closed__0();
lean_mark_persistent(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__7_spec__13_spec__18_spec__21___closed__0);
l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__7_spec__13_spec__18_spec__21___closed__3 = _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__7_spec__13_spec__18_spec__21___closed__3();
lean_mark_persistent(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__7_spec__13_spec__18_spec__21___closed__3);
l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__7_spec__13_spec__18___redArg___closed__2 = _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__7_spec__13_spec__18___redArg___closed__2();
lean_mark_persistent(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_LibrarySuggestions_elabSetLibrarySuggestions_spec__1_spec__7_spec__13_spec__18___redArg___closed__2);
l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__10 = _init_l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__10();
lean_mark_persistent(l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__10);
l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__23 = _init_l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__23();
lean_mark_persistent(l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__23);
l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__26 = _init_l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__26();
lean_mark_persistent(l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__26);
l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__34 = _init_l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__34();
lean_mark_persistent(l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__34);
l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__35 = _init_l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__35();
lean_mark_persistent(l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__35);
l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__36 = _init_l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__36();
lean_mark_persistent(l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__36);
l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__43 = _init_l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__43();
lean_mark_persistent(l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__43);
l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__61 = _init_l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__61();
lean_mark_persistent(l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___closed__61);
if (builtin) {res = l_Lean_LibrarySuggestions_elabSetLibrarySuggestions___regBuiltin_Lean_LibrarySuggestions_elabSetLibrarySuggestions__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_LibrarySuggestions_evalSuggestions_spec__2___closed__0 = _init_l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_LibrarySuggestions_evalSuggestions_spec__2___closed__0();
l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_LibrarySuggestions_evalSuggestions_spec__0___redArg___closed__1 = _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_LibrarySuggestions_evalSuggestions_spec__0___redArg___closed__1();
lean_mark_persistent(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_LibrarySuggestions_evalSuggestions_spec__0___redArg___closed__1);
l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_LibrarySuggestions_evalSuggestions_spec__0___redArg___closed__2 = _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_LibrarySuggestions_evalSuggestions_spec__0___redArg___closed__2();
lean_mark_persistent(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_LibrarySuggestions_evalSuggestions_spec__0___redArg___closed__2);
l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_LibrarySuggestions_evalSuggestions_spec__0___redArg___closed__5 = _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_LibrarySuggestions_evalSuggestions_spec__0___redArg___closed__5();
lean_mark_persistent(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_LibrarySuggestions_evalSuggestions_spec__0___redArg___closed__5);
l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_LibrarySuggestions_evalSuggestions_spec__0___redArg___closed__7 = _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_LibrarySuggestions_evalSuggestions_spec__0___redArg___closed__7();
lean_mark_persistent(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_LibrarySuggestions_evalSuggestions_spec__0___redArg___closed__7);
l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_LibrarySuggestions_evalSuggestions_spec__0___redArg___closed__9 = _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_LibrarySuggestions_evalSuggestions_spec__0___redArg___closed__9();
lean_mark_persistent(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_LibrarySuggestions_evalSuggestions_spec__0___redArg___closed__9);
l_Lean_LibrarySuggestions_evalSuggestions___redArg___lam__1___closed__2 = _init_l_Lean_LibrarySuggestions_evalSuggestions___redArg___lam__1___closed__2();
lean_mark_persistent(l_Lean_LibrarySuggestions_evalSuggestions___redArg___lam__1___closed__2);
if (builtin) {res = l_Lean_LibrarySuggestions_evalSuggestions___regBuiltin_Lean_LibrarySuggestions_evalSuggestions__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
